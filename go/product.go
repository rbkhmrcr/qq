package qq

import (
	r "github.com/bwesterb/go-ristretto"
	"math/big"
)

type prodarg struct {
	cb   *r.Point
	ha   *harg
	svpa []*svparg // size n
}

type prodwitness struct {
	A    [][]*r.Scalar
	rvec []*r.Scalar
	b    *r.Scalar
	cA   []*r.Point
}

// product arg is called on a witness a, b such that product product A[i][j] = b
// with statement as commitments to the values A
func (stmnt *Statement) productarg(pw *prodwitness) *prodarg {
	bigOne := new(r.Scalar).SetOne()
	s := new(r.Scalar).Rand()

	var cb *r.Point
	// cb = com(product (from 1 to m) a1j, ..., product (from 1 to m) anj; s)
	// does this loop m times?
	aprod := make([]*r.Scalar, stmnt.n)
	prod := new(r.Scalar).SetOne()
	for i, ai := range pw.A {
		for j := range ai {
			prod.Mul(prod, pw.A[i][j])
		}
		aprod[i] = prod
		prod = bigOne
	}
	cb = stmnt.CompactCommit(aprod, s)

	// hadamard argument convinces verifier you know
	// A and b st prod prod A = b :) with b a VECTOR
	ha := stmnt.hadamardarg(&hwitness{pw.cA, cb, pw.A, aprod, pw.rvec, s})

	// svp argument convinces verifier that prod a = b with b a SCALAR
	svpa := make([]*svparg, stmnt.m)
	// do the below for i in a(row/column), committing to each separately (i think this is to prove aprod is formed correctly?)
	for i := range svpa {
		svpa[i] = stmnt.svparg(&svpwitness{pw.A[i], pw.rvec[i], aprod[i], pw.cA[i]})
	}
	return &prodarg{cb, ha, svpa}
}

func bilinearmap(a []*r.Scalar, b []*r.Scalar, y *r.Scalar) *r.Scalar {
	groupOrder, _ := new(big.Int).SetString("7237005577332262213973186563042994240857116359379907606001950938285454250989", 10)
	sum := new(r.Scalar).SetZero()
	yj := new(r.Scalar).SetZero()
	tempo := new(r.Scalar).SetZero()
	for j := range a {
		// yj = y^j
		yj = new(r.Scalar).SetBigInt(new(big.Int).Exp(y.BigInt(), big.NewInt(int64(j)), groupOrder))
		// temp = aj . bj . y^j
		tempo = new(r.Scalar).Mul(new(r.Scalar).Mul(a[j], b[j]), yj)
		sum.Add(sum, tempo)
	}
	return sum
}

func (s *Statement) productverify(pa *prodarg) bool {
	if s.hverify(pa.ha) != true {
		return false
	}
	for i := range pa.svpa {
		if s.svpverify(pa.svpa[i]) != true {
			return false
		}
	}
	return true
}
