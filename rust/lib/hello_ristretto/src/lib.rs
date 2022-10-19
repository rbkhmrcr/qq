extern crate bincode;
extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate libc;
extern crate rand;
#[macro_use]
extern crate arrayref;

use curve25519_dalek::{ristretto::RistrettoPoint,ristretto::CompressedRistretto, scalar::Scalar};
use libc::{size_t, uint64_t, uint8_t};
use rand::{OsRng, Rng};
use std::slice;

use bulletproofs::{Generators, PedersenGenerators, RangeProof, Transcript};

#[no_mangle]
pub extern "C" fn generate_ristretto_random(buf: *mut uint8_t, len: size_t) {
    let buffer = unsafe {
        assert!(!buf.is_null());
        slice::from_raw_parts_mut(buf, len as usize)
    };
    let mut rng = OsRng::new().unwrap();

    let point = RistrettoPoint::random(&mut rng);

    let point_bytes = point.compress().to_bytes();

    buffer.copy_from_slice(&point_bytes);
}

#[no_mangle]
pub extern "C" fn generate_ristretto_range_proof(
    vals:*const uint64_t,
    vals_len: size_t,
    blinding_factors: *const uint8_t,
    blinding_factors_len: size_t,
    proof_buf: *mut uint8_t,
    proof_buf_len: size_t,
    commitments: *mut uint8_t,
    commitments_len: size_t
) {
    let values = unsafe {
        assert!(!proof_buf.is_null());
        slice::from_raw_parts(vals, vals_len as usize)
    };

    let mut blindings: Vec<Scalar> = vec![];
    for i in 0..blinding_factors_len{
            let blind_p = unsafe{
                blinding_factors.offset((i * 32) as isize)
            };
            let blind_buffer = c_buf_to_32_bytes_array(blind_p, 32);
            blindings.push(Scalar::from_canonical_bytes(blind_buffer).unwrap());
    }




    // Both prover and verifier have access to the generators and the proof
    let generators = Generators::new(PedersenGenerators::default(), 64, vals_len);
    

    let proof_buffer = unsafe {
        assert!(!proof_buf.is_null());
        slice::from_raw_parts_mut(proof_buf, proof_buf_len as usize)
    };

    let mut rng = OsRng::new().unwrap();
    let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

    let (min, max) = (0u64, ((1u128 << 2) - 1) as u64);

    let proof = RangeProof::prove_multiple(
        &generators,
        &mut transcript,
        &mut rng,
        &values,
        &blindings,
        2,
    ).unwrap();

    // 2. Serialize
    let proof_bytes = bincode::serialize(&proof).unwrap();

    proof_buffer.copy_from_slice(proof_bytes.as_slice());

    let pg = &generators.pedersen_gens;

    // XXX would be nice to have some convenience API for this
    let value_commitments: Vec<RistrettoPoint> = values
        .iter()
        .zip(blindings.iter())
        .map(|(&v, &v_blinding)| pg.commit(Scalar::from(v), v_blinding))
        .collect();

    for i in 0..commitments_len{
        let mut buffer = unsafe {
        let mut commmitment_p = commitments.offset((i *32) as isize);
        slice::from_raw_parts_mut(commmitment_p, 32)
        };
        buffer.copy_from_slice(&value_commitments[i].compress().to_bytes());
    }

}

#[no_mangle]
pub extern "C" fn verify_ristretto_range_proof(
    proof_buf: *const uint8_t,
    proof_buf_len: size_t,
    commitments:*const uint8_t,
    commitments_len:size_t,
)-> bool{


    let generators = Generators::new(PedersenGenerators::default(), 2, 2);

    let proof_buffer = unsafe {
        assert!(!proof_buf.is_null());
        slice::from_raw_parts(proof_buf, proof_buf_len as usize)
    };

    let mut value_commitments:Vec<RistrettoPoint> = vec![];

    for i in 0..commitments_len{
        let commit_p = unsafe{
            commitments.offset((i * 32) as isize)
        };
        let point = CompressedRistretto(c_buf_to_32_bytes_array(commit_p,32));
        value_commitments.push(point.decompress().unwrap());
    } 

    let proof: RangeProof = bincode::deserialize(proof_buffer).unwrap();

    // 4. Verify with the same customization label as above
    let mut rng = OsRng::new().unwrap();
    let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

    proof.verify(
        &value_commitments,
        &generators,
        &mut transcript,
        &mut rng,
        2
    ).is_ok()

}

fn c_buf_to_32_bytes_array(buf: *const uint8_t,len: size_t)->[u8;32]{
    let buffer = unsafe {
        assert!(!buf.is_null());
        slice::from_raw_parts(buf, len as usize)
    };
    array_ref![buffer,0,32].clone()
}
