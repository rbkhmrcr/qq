package qq

import (
	"crypto/sha256"
	r "github.com/bwesterb/go-ristretto"
	"math/big"
)

// Witness contains the randomness to update v, the permutation pi,
// and the randomness for the encryptions rho
type shufflewitness struct {
	pi  [][]int       // size N -- permutation arranged in n x m matrix
	tau [][]*r.Scalar // size N - randomness st Ci' = C(pi(i)^vi (Ci = act[i][j].pk)
	rho *r.Scalar     // randomness st Di' = enc(1; rho).D(pi(i)) (Di = act[i][j].com)
}

// ShuffleArg contains all communications in the argument for
// correctness of a shuffle
type shufflearg struct {
	cA   []*r.Point // len(ca) = m
	ctau []*r.Point // len(cv) = m
	x    *r.Scalar
	cBo  []*r.Point // len(cb) = m
	cB1  []*r.Point // len(cb) = m
	ha   []*harg
	y    *r.Scalar
	z    *r.Scalar
	pa   *prodarg
	vua  *vuarg
	meao *multiexparg
	mea1 *multiexparg
}

// Prove proves the correctness of a shuffle
func (stmnt *Statement) shuffleprove(w *shufflewitness) *shufflearg {
	groupOrder, _ := new(big.Int).SetString("7237005577332262213973186563042994240857116359379907606001950938285454250989", 10)

	// generate the randomness needed for the commitments
	ro := make([]*r.Scalar, stmnt.m)
	r1 := make([]*r.Scalar, stmnt.m)
	so := make([]*r.Scalar, stmnt.m)
	s1 := make([]*r.Scalar, stmnt.m)

	for i := 0; i < stmnt.m; i++ {
		ro[i] = new(r.Scalar).Rand()
		r1[i] = new(r.Scalar).Rand()
		so[i] = new(r.Scalar).Rand()
		s1[i] = new(r.Scalar).Rand()
	}

	piscalar := make([][]*r.Scalar, stmnt.n)
	for i, _ := range piscalar {
		piscalar[i] = make([]*r.Scalar, stmnt.n)
	}
	for i, pii := range w.pi {
		for j, piij := range pii {
			piscalar[i][j] = inttoscalar(piij)
		}
	}

	// this will commit to n elements of pi, m times
	// what would 'for i, x := range w.pi' give?
	// a and v are of equal size
	ca := make([]*r.Point, stmnt.m)
	ctau := make([]*r.Point, stmnt.m)
	for i := 0; i < stmnt.m; i++ {
		// each compactcommit commits to n elements
		ca[i] = stmnt.CompactCommit(piscalar[i], ro[i])
		ctau[i] = stmnt.CompactCommit(w.tau[i], r1[i])
	}

	xx := sha256.Sum256(ca[0].Bytes())
	x := new(r.Scalar).SetBytes(&xx)

	// b[i] =  x*(pi(i)) is computed over the integers
	// (or mod groupOrder equivalently)
	// commit to n elements at a time (m times)
	bo := make([][]*r.Scalar, stmnt.m)
	b1 := make([][]*r.Scalar, stmnt.m)
	for i, _ := range bo {
		bo[i] = make([]*r.Scalar, stmnt.n)
		b1[i] = make([]*r.Scalar, stmnt.n)
	}

	tempo := new(r.Scalar).SetZero()
	temp1 := new(r.Scalar).SetZero()
	temp := new(r.Scalar).SetZero()
	// could use range i, b := range w.pi, j, c := range b
	for i := 0; i < stmnt.m; i++ {
		for j := 0; j < stmnt.n; j++ {
			// bo(i) = x^pi(i)
			bo[i][j] = new(r.Scalar).SetBigInt(new(big.Int).Exp(x.BigInt(), piscalar[i][j].BigInt(), groupOrder))
			// b1(i) = x^pi(i) / v(i)
			b1[i][j] = tempo.Mul(temp1.Inverse(w.tau[i][j]), bo[i][j])
		}
	}

	cBo := make([]*r.Point, stmnt.m)
	cB1 := make([]*r.Point, stmnt.m)
	ha := make([]*harg, stmnt.m)
	for i := range cBo {
		cBo[i] = stmnt.CompactCommit(bo[i], so[i])
		cB1[i] = stmnt.CompactCommit(b1[i], s1[i])
	}

	/*
		// bvec = sum (from i to m) of ai
		// cb = com(bvec; s)

		s := new(r.Scalar).Rand()
		bvec := make([]*r.Scalar, stmnt.n)
		sum := bigZero

		// ranges from a1, ..., am
		for i, ai := range w.pi {
			sum = bigZero
			// ranges a11, ..., a1n, a21, ..., a2n, ... amn
			for _, aij := range ai {
				sum.Add(sum, aij)
			}
			bvec[i] = sum
		}

		cb := stmnt.CompactCommit(bvec, s)
	*/

	// now make argument showing b'.v = b (in committed form :D)
	for i := range cBo {
		ha[i] = stmnt.hadamardarg(&hwitness{ca, cBo[i], piscalar, bo[i], ro, so[i]})
	}

	// These should be replaced with hashing everything above
	y := new(r.Scalar).Rand()
	z := new(r.Scalar).Rand()
	// verif can commute this cz := stmnt.CompactCommit(minuszvec, bigZero)

	temp = new(r.Scalar).SetZero()

	// t = y.ro + so
	t := make([]*r.Scalar, stmnt.m)
	for i := range t {
		temp = new(r.Scalar).Mul(y, ro[i])
		t[i] = new(r.Scalar).Add(temp, so[i])
	}

	// f = y.a + b
	// these seem redundant
	f := make([][]*r.Scalar, stmnt.n)
	for i := range f {
		f[i] = make([]*r.Scalar, stmnt.m)
	}

	// do we even need a commitment to f
	cf := make([]*r.Point, stmnt.n)
	for i, fi := range f {
		for j := range fi {
			temp = new(r.Scalar).Mul(y, piscalar[i][j])
			f[i][j] = new(r.Scalar).Add(temp, bo[i][j])
		}
	}
	for i := range f {
		cf[i] = stmnt.CompactCommit(f[i], t[i])
	}

	/*
		// this is how the verifier can compute cF
		cF := make([]*r.Point, stmnt.m)
		for i := range cF {
			a := ca[i].ScalarMult(y)
			cF[i] = a.Add(cBo[i])
		}
	*/

	// b := yi + x ^ i - z
	// product arg proves product of ei = product of yi + x^i - z
	// -z = (-z, ..., -z)

	/* this is for the verifier
	bigZero = new(r.Scalar).SetZero()
	minusz := new(r.Scalar).Sub(bigZero, z)
	mzv := make([][]*r.Scalar, stmnt.m)
	for i := range mzv {
		mzv[i] = make([]*r.Scalar, stmnt.n)
	}

	// cz = commitment to minus v (randomness zero)
	cz := make([]*r.Point, stmnt.n)
	for i, mi := range mzv {
		for j := range mi {
			mzv[i][j] = minusz
		}
		// fmt.Println("i, len(cz), len(mzv)", i, len(cz), len(mzv))
		cz[i] = stmnt.CompactCommit(mzv[i], bigZero)
	}
	*/

	// e = f - z
	e := make([][]*r.Scalar, stmnt.n)
	for i, _ := range e {
		e[i] = make([]*r.Scalar, stmnt.m)
	}
	for i, ei := range e {
		for j := range ei {
			e[i][j] = new(r.Scalar).Sub(f[i][j], z)
		}
	}

	ce := make([]*r.Point, stmnt.n)
	for i := range e {
		ce[i] = stmnt.CompactCommit(e[i], t[i])
	}

	/*
		// this is for verifier
		cE := make([]*r.Point, stmnt.n)
		for i := range cE {
			cE[i] = cF[i].Add(cz[i])
		}
	*/

	// G, H, G', H' = product (pki^(x^i), pki^((x^i).rho)

	xi := new(r.Scalar).SetOne()
	temp = new(r.Scalar).SetOne()
	xirho := new(r.Scalar).SetOne()

	tempgo := new(r.Point).SetZero()
	tempg1 := new(r.Point).SetZero()
	tempho := new(r.Point).SetZero()
	temph1 := new(r.Point).SetZero()
	sumgo := new(r.Point).SetZero()
	sumg1 := new(r.Point).SetZero()
	sumho := new(r.Point).SetZero()
	sumh1 := new(r.Point).SetZero()

	for i, ei := range e {
		xi = new(r.Scalar).SetBigInt(new(big.Int).Exp(x.BigInt(), big.NewInt(int64(i)), groupOrder))
		xirho = new(r.Scalar).Mul(xi, w.rho)
		for j, _ := range ei {
			// go = pk.gi^(x^i)
			tempgo = new(r.Point).ScalarMult(stmnt.acti[i][j].pk.gi, xi)
			// ho = pk.hi^(x^i)
			tempho = new(r.Point).ScalarMult(stmnt.acti[i][j].pk.hi, xi)
			sumgo.Add(tempgo, sumgo)
			sumho.Add(tempho, sumho)

			// g1 = pk.gi^(rho * x^i)
			tempg1 = new(r.Point).ScalarMult((stmnt.acti[i][j].pk).gi, xirho)
			// h1 = pk.hi^(rho * x^i)
			temph1 = new(r.Point).ScalarMult(stmnt.acti[i][j].pk.hi, xirho)
			sumg1.Add(tempg1, sumg1)
			sumh1.Add(temph1, sumh1)
		}
	}
	// (g, h), (g', h')
	sumo := &PublicKey{sumgo, sumho}
	sum1 := &PublicKey{sumg1, sumh1}

	vuarg := sumo.SigmaVUQQ(sum1, w.rho)

	// b = (i from 1 to n) yi + x ^ i - z = (i from 1 to n) ei
	b := new(r.Scalar).SetOne()
	for i, ei := range e {
		for j := range ei {
			b = new(r.Scalar).Mul(b, e[i][j])
		}
	}
	parg := stmnt.productarg(&prodwitness{e, t, b, ce})

	pk := make([][]*PublicKey, stmnt.m)
	upk := make([][]*PublicKey, stmnt.m)
	for i, _ := range pk {
		pk[i] = make([]*PublicKey, stmnt.n)
		upk[i] = make([]*PublicKey, stmnt.n)
	}

	// these should be commitments but the content is the same : gi = c and hi = d
	com := make([][]*PublicKey, stmnt.m)
	ucom := make([][]*PublicKey, stmnt.m)
	for i, _ := range com {
		com[i] = make([]*PublicKey, stmnt.n)
		ucom[i] = make([]*PublicKey, stmnt.n)
	}

	for i, acti := range stmnt.acti {
		for j, actij := range acti {
			pk[i][j] = &PublicKey{actij.pk.gi, actij.pk.hi}
			upk[i][j] = &PublicKey{stmnt.actpi[i][j].pk.gi, stmnt.actpi[i][j].pk.hi}
			com[i][j] = &PublicKey{stmnt.acti[i][j].com.c, stmnt.acti[i][j].com.d}
			ucom[i][j] = &PublicKey{stmnt.actpi[i][j].com.c, stmnt.actpi[i][j].com.d}
		}
	}

	// multiexp argument o shows sum( b'[i] . upk[i] ) = sum ( x^i . pk[i] )
	meargo := stmnt.multiexparg(&multiexpwitness{b1, s1, pk, upk, sum1, cB1})

	// multiexp argument 1 shows sum( b[i] . ucom[i] ) = sum ( x^i . com[i] ) + (G', H')
	mearg1 := stmnt.multiexparg(&multiexpwitness{bo, so, com, ucom, sumo, cB1})

	return &shufflearg{
		ca,
		ctau,
		x,
		cBo,
		cB1,
		ha,
		y,
		z,
		parg,
		vuarg,
		meargo,
		mearg1,
	}
}

func (s *Statement) shuffleverify(sa *shufflearg) bool {

	// CF
	cF := make([]*r.Point, s.m)
	for i := range cF {
		a := new(r.Point).ScalarMult(sa.cA[i], sa.y)
		cF[i] = new(r.Point).Add(a, sa.cBo[i])
	}

	bigZero := new(r.Scalar).SetZero()
	minusz := new(r.Scalar).Neg(sa.z)

	mzv := make([][]*r.Scalar, s.m)
	for i := range mzv {
		mzv[i] = make([]*r.Scalar, s.n)
	}

	cz := make([]*r.Point, s.m)
	for i, mi := range mzv {
		for j := range mi {
			mzv[i][j] = minusz
		}
		// fmt.Println("i, len(cz), len(mzv)", i, len(cz), len(mzv))
		cz[i] = s.CompactCommit(mzv[i], bigZero)
	}

	// CE
	cE := make([]*r.Point, s.m)
	for i := range cE {
		cE[i] = new(r.Point).Add(cF[i], cz[i])
	}

	// G, H

	// verify the hadamard argument
	for i := range sa.ha {
		if !s.hverify(sa.ha[i]) {
			return false
		}
	}

	// product arg is cb, ha (a hadamard argument) and svpa
	// ha = cA, cb, cB, x, y, cD, cDvec, za
	if !s.productverify(sa.pa) {
		return false
	}
	if !s.meverify(sa.meao) {
		return false
	}
	if !s.meverify(sa.mea1) {
		return false
	}
	return true
}
