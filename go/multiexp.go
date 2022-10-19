package qq

import (
	r "github.com/bwesterb/go-ristretto"
	"math/big"
)

/*
statement:
commitments C1, ..., Cm (each n dimensional)
C a single commitment; c_A m dimensional commitment

witness:
A = aj for j = 1, ..., m, an n x m matrix
r in Zq^m; rho in Zq;
C = enc(1; rho) product of Ci^ai
cA = com(A; r)

parameters m, n defined elsewhere

*/

type multiexpwitness struct {
	A [][]*r.Scalar
	r []*r.Scalar
	// rho *r.Scalar
	C0 [][]*PublicKey // sometimes a commitment
	C1 [][]*PublicKey // sometimes a commmitment
	C  *PublicKey
	cA []*r.Point
}

type multiexparg struct {
	C0  [][]*PublicKey // sometimes com
	C1  [][]*PublicKey // sometimes com
	C   *PublicKey
	cA  []*r.Point
	cA0 *r.Point
	cBk []*r.Point
	ek  *PublicKey // type?? PublicKey?
	x   *r.Scalar
	a   []*r.Scalar
	r   *r.Scalar
	b   *r.Scalar
	s   *r.Scalar
	tau *r.Scalar
}

func (stmnt *Statement) multiexparg(w *multiexpwitness) *multiexparg {
	groupOrder, _ := new(big.Int).SetString("7237005577332262213973186563042994240857116359379907606001950938285454250989", 10)
	m := stmnt.m
	n := stmnt.n

	var cA0 *r.Point
	ek := &PublicKey{}
	a0 := make([]*r.Scalar, n)
	cBk := make([]*r.Point, 2*m)
	//Ek := make([]*PublicKey, 2*m)
	bvec := make([]*r.Scalar, 2*m)
	svec := make([]*r.Scalar, 2*m)
	tauvec := make([]*r.Scalar, 2*m)
	r0 := new(r.Scalar).Rand()

	// maybe i should make a fill rand function
	for i := 0; i < n; i++ {
		a0[i] = new(r.Scalar).Rand()
	}

	for i := 0; i < 2*m; i++ {
		bvec[i] = new(r.Scalar).Rand()
		svec[i] = new(r.Scalar).Rand()
		tauvec[i] = new(r.Scalar).Rand()
	}

	bvec[m] = new(r.Scalar).SetZero()
	svec[m] = new(r.Scalar).SetZero()

	cA0 = stmnt.CompactCommit(a0, r0)
	for k := 0; k < 2*m; k++ {
		cBk[k] = stmnt.Commit(bvec[k], svec[k], 0)
	}
	// 	Ek := E(G.ScalarBaseMult(bvec[k].Bytes()), tauvec[k])
	for k := 1; k < 2*m; k++ {
		for i := 1; i < m+1; i++ {
			for j := k - m + i; j < m+1; j++ {
			}
		}
	}

	x := new(r.Scalar).Rand()
	xvecext := make([]*r.Scalar, 2*m-2)
	for i := range xvecext {
		xvecext[i] = new(r.Scalar).SetBigInt(new(big.Int).Exp(x.BigInt(), big.NewInt(int64(i)), groupOrder))
	}

	xa := new(r.Scalar).SetOne()
	sum := new(r.Scalar).SetZero()

	// n x m . m x 1 = n x 1
	avec := make([]*r.Scalar, n)
	avec = a0
	for i, ai := range w.A {
		for j, aij := range ai {
			xa.Mul(aij, xvecext[j])
			sum.Add(sum, xa)
		}
		avec[i] = sum
	}

	xr := new(r.Scalar).SetOne()
	xs := new(r.Scalar).SetOne()
	xb := new(r.Scalar).SetOne()
	xtau := new(r.Scalar).SetOne()

	r := r0
	for i := range w.r {
		xr.Mul(xvecext[i], w.r[i])
		r.Add(r, xr)
	}

	b := bvec[0]
	s := svec[0]
	tau := tauvec[0]
	for i := range xvecext {
		xb.Mul(xvecext[i], bvec[i])
		b.Add(b, xb)
		xs.Mul(xvecext[i], svec[i])
		s.Add(s, xs)
		xtau.Mul(xvecext[i], tauvec[i])
		tau.Add(tau, xtau)
	}

	return &multiexparg{
		w.C0,
		w.C1,
		w.C,
		w.cA,
		cA0,
		cBk,
		ek,
		x,
		avec,
		r,
		b,
		s,
		tau}
}

func (s *Statement) meverify(mea *multiexparg) bool {
	bigZero := new(r.Scalar).SetZero()
	if mea.cBk[s.m-1] != s.Commit(bigZero, bigZero, 0) {
		return false
	}
	// check Em = C
	ax := new(r.Scalar).SetZero()
	bx := new(r.Scalar).SetZero()
	var suma, tempa, sumb, tempb *r.Point

	for i := range mea.cA {
		// x^i
		ax = new(r.Scalar).SetBigInt(new(big.Int).Exp(mea.x.BigInt(), big.NewInt(int64(i)), nil))
		// x^(m-i)
		bx = new(r.Scalar).SetBigInt(new(big.Int).Exp(mea.x.BigInt(), big.NewInt(int64(s.m-i)), nil))
		// x^i . c_A(i)
		tempa = new(r.Point).ScalarMult(mea.cA[i], ax)
		suma = new(r.Point).Add(suma, tempa)
		// temp e, sum e
		// x^(m-i) . c_B(i)
		tempb = new(r.Point).ScalarMult(mea.cBk[i], bx)
		sumb = new(r.Point).Add(sumb, tempb)
		// sume = sum e . Add(temp e)
	}
	if suma != s.CompactCommit(mea.a, mea.r) {
		return false
	}
	if sumb != s.Commit(mea.b, mea.s, 0) {
		return false
	}
	for i := s.m + 1; i < 2*s.m-2; i++ {
		ax = new(r.Scalar).SetBigInt(new(big.Int).Exp(mea.x.BigInt(), big.NewInt(int64(i)), nil))
		// sume = sume.Add(tempe)
	}
	if sumd != sume {
		return false
	}
	return true
}
