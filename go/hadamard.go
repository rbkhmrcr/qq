package qq

import (
	r "github.com/bwesterb/go-ristretto"
	"math/big"
)

type hwitness struct {
	cA   []*r.Point    // cA = com(A; rvec)
	cb   *r.Point      // cb = com(bvec; s)
	A    [][]*r.Scalar // A = n x m matrix of shuffled ciphertexts
	bvec []*r.Scalar   // bvec = sum (from i to m) of ai
	rvec []*r.Scalar   // rvec = randomness for cA
	s    *r.Scalar     // s = randomness for cb
}

type harg struct {
	cA    []*r.Point
	cb    *r.Point
	cB    []*r.Point // cB = {com(b1 = a1; s1), ..., com(bm = b; sm = s)}
	x     *r.Scalar  // x = challenge
	y     *r.Scalar  // y = challenge
	cD    *r.Point   // cD = product cB_(i+1)^(x^i)
	cDvec []*r.Point // cDvec = {cB1^(x^1), ..., cBm^(x^m)}
	za    *zeroarg   // za = zeroarg that 0 = sum ( a(i+1) star di ) minmus ( 1 star d )
}

// ai, b, vectors of length n
// cA, cb, a1, ..., am, bvec, st bvec = product ai
// (with entrywise multiplication)
// cA = com(A;rvec); cb = com(bvec; s)
func (stmnt *Statement) hadamardarg(hw *hwitness) *harg {
	groupOrder, _ := new(big.Int).SetString("7237005577332262213973186563042994240857116359379907606001950938285454250989", 10)
	bigZero := new(r.Scalar).SetZero()
	bigOne := new(r.Scalar).SetOne()
	minusOne := new(r.Scalar).Sub(bigZero, bigOne)
	// make m slices (each length n)
	b := make([][]*r.Scalar, stmnt.m)
	for i := range b {
		b[i] = make([]*r.Scalar, stmnt.n)
	}

	temp := bigZero
	for i, bi := range b {
		// b1 = a1
		if i == 0 {
			b[0] = hw.A[0]
		} else if i == stmnt.m-1 {
			b[i] = hw.bvec
		} else {
			// b2 = a1a2, b3 = a1a2a3, ..., bm-1 = a1...am-1, bm = b
			for j := range bi {
				// b[i-1] for i = 0 will be 0 so can't use this.
				b[i][j] = temp.Mul(b[i-1][j], hw.A[i][j])
			}
		}
	}

	svec := make([]*r.Scalar, stmnt.m)
	cB := make([]*r.Point, stmnt.m)
	for i, _ := range svec {
		svec[i] = new(r.Scalar).Rand()
		cB[i] = stmnt.CompactCommit(b[i], svec[i])
	}
	svec[0] = hw.rvec[0]
	svec[stmnt.m-1] = hw.s
	cB[0] = hw.cA[0]
	cB[stmnt.m-1] = hw.cb

	x := new(r.Scalar).Rand()
	y := new(r.Scalar).Rand()
	cx := new(r.Scalar).SetZero()
	cD := &r.Point{}
	cDvec := make([]*r.Point, stmnt.m)

	for i := range cB {
		// x^i
		cx = new(r.Scalar).SetBigInt(new(big.Int).Exp(x.BigInt(), big.NewInt(int64(i)), groupOrder))
		// x^i . c_B(i)
		cDvec[i] = new(r.Point).ScalarMult(cB[i], cx)
		if i == 0 || i == len(cB)-1 {
			continue
		} else {
			// cD = sum( x^i . c_B(i+1)
			cD = new(r.Point).Add(cD, new(r.Point).ScalarMult(cB[i+1], cx))
		}
	}

	movec := make([]*r.Scalar, stmnt.n)
	for i := range movec {
		movec[i] = minusOne
	}

	// cmo := CompactCommit(ck, movec, bigZero)
	// zeroarg takes A, rvec, B, svec
	za := stmnt.zeroargument(&zerowitness{hw.A, hw.rvec, b, svec, hw.cA, cB, y})

	return &harg{
		hw.cA,
		hw.cb,
		cB,
		x,
		y,
		cD,
		cDvec,
		za}
}

func (s *Statement) hverify(ha *harg) bool {

	// check cB1 = cA1
	if ha.cB[0] != ha.cA[0] {
		return false
	}
	// check cBm = cb
	if ha.cB[s.m-1] != ha.cb {
		return false
	}

	var cD, temp *r.Point
	cx := new(r.Scalar)
	cDvec := make([]*r.Point, s.m)
	for i := range ha.cB {
		// x^i
		cx = new(r.Scalar).SetBigInt(new(big.Int).Exp(ha.x.BigInt(), big.NewInt(int64(i)), nil))
		// x^i . c_B(i)
		cDvec[i] = new(r.Point).ScalarMult(ha.cB[i], cx)
		// for i = 1 to i = m-1
		if i > 0 && i < s.m-1 {
			// x^i . c_B(i+1)
			temp = new(r.Point).ScalarMult(ha.cB[i+1], cx)
			if i == 1 {
				cD = temp
			} else {
				cD = new(r.Point).Add(cD, temp)
			}
		}
	}
	bigZero := new(r.Scalar).SetZero()
	bigOne := new(r.Scalar).SetOne()
	minusOne := new(r.Scalar).Sub(bigZero, bigOne)

	movec := make([]*r.Scalar, s.n)
	for i := range movec {
		movec[i] = minusOne
	}

	if s.zverify(ha.za) != true {
		return false
	}
	return true
}
