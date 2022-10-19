package qq

import (
	"crypto/sha256"
	r "github.com/bwesterb/go-ristretto"
)

// sp = single value product
type svparg struct {
	// svp statement
	ca *r.Point
	b  *r.Scalar
	// svp argument
	// (comm x or no?)
	cd     *r.Point
	cdelta *r.Point
	cDelta *r.Point
	x      *r.Scalar
	atvec  []*r.Scalar
	btvec  []*r.Scalar
	rt     *r.Scalar
	st     *r.Scalar
}

type svpwitness struct {
	a []*r.Scalar
	r *r.Scalar
	// svp statement
	b  *r.Scalar
	ca *r.Point
}

// product arg is called on a wintess a, b such that product(ai) = b
// with statement as b, and ca, a commitment to the values ai
func (stmnt *Statement) svparg(spw *svpwitness) *svparg {
	bigZero := new(r.Scalar).SetZero()
	bigOne := new(r.Scalar).SetOne()
	// n here is len a which isn't dependent on n, m in the statement
	// b1 = a1, b2 = a1a2, ..., bn = prod a1, ..., an
	n := len(spw.a)
	bvec := make([]*r.Scalar, n)
	prod := bigOne
	for i, ai := range spw.a {
		prod.Mul(prod, ai)
		bvec[i] = prod
	}

	d := make([]*r.Scalar, n)
	delta := make([]*r.Scalar, n)

	for i := range d {
		d[i] = new(r.Scalar).Rand()
		delta[i] = new(r.Scalar).Rand()
	}

	rd := new(r.Scalar).Rand()
	delta[0] = d[0]
	delta[len(delta)-1] = bigZero

	s1 := new(r.Scalar).Rand()
	sx := new(r.Scalar).Rand()

	cd := stmnt.CompactCommit(d, rd)
	// cdelta and cDelta are commitments to n-1 entries
	dd := make([]*r.Scalar, n-1)
	DD := make([]*r.Scalar, n-1)

	// dd[i] = - deltavec[i] * dvec[i+1]
	for i := range dd {
		dd[i] = new(r.Scalar).Sub(bigZero, new(r.Scalar).Mul(delta[i], d[i+1]))
	}
	// DD[i] = delta[i+1] - a[i+1]delta[i] - b[i]d[i+1]
	for i := range DD {
		// a[i+1]delta[i]
		ad := new(r.Scalar).Mul(spw.a[i+1], delta[i])
		// b[i]d[i+1]
		bd := new(r.Scalar).Mul(bvec[i], d[i+1])
		// delta[i+1] - ad - bd
		DD[i] = new(r.Scalar).Sub(new(r.Scalar).Sub(delta[i+1], ad), bd)
	}

	cdelta := stmnt.CompactCommit(dd, s1)
	cDelta := stmnt.CompactCommit(DD, sx)

	xx := sha256.Sum256(cdelta.Bytes())
	x := new(r.Scalar).SetBytes(&xx)
	atvec := make([]*r.Scalar, n)
	btvec := make([]*r.Scalar, n)

	for i := range atvec {
		tempo := new(r.Scalar).Mul(spw.a[i], x)
		atvec[i] = new(r.Scalar).Add(tempo, d[i])
		temp1 := new(r.Scalar).Mul(bvec[i], x)
		btvec[i] = new(r.Scalar).Add(temp1, delta[i])
	}
	rt := new(r.Scalar).Mul(spw.r, x)
	rt = new(r.Scalar).Add(rt, rd)
	st := new(r.Scalar).Mul(sx, x)
	st = new(r.Scalar).Add(st, s1)
	return &svparg{spw.ca, spw.b, cd, cdelta, cDelta, x, atvec, btvec, rt, st}
}

func (stmnt *Statement) svpverify(spa *svparg) bool {
	n := len(spa.atvec)
	// bt[n-1] = xb
	xb := new(r.Scalar).Mul(spa.x, spa.b)
	// fmt.Println("bt[n-1] = ", spa.btvec[n-1])
	// fmt.Println("xb", xb)
	if !spa.btvec[n-1].Equals(xb) {
		// fmt.Println("bt[n-1] != xb")
	}

	// bt[0] = at[0]
	if !spa.btvec[0].Equals(spa.atvec[0]) {
		// fmt.Println("bt[0] != at[0]")
	}

	// x.ca + cd = com(at[0], ..., at[n-1]; rt)
	xca := new(r.Point).ScalarMult(spa.ca, spa.x)
	xca = new(r.Point).Add(xca, spa.cd)
	como := stmnt.CompactCommit(spa.atvec, spa.rt)

	if !como.Equals(xca) {
		// 	fmt.Println("x.ca + cd != com(at; rt)")
	}

	// x.cDelta + cdelta = com(x.bt[i+1] - b[i]a[i+1]; st)
	xcd := new(r.Point).ScalarMult(spa.cDelta, spa.x)
	xcd = new(r.Point).Add(xcd, spa.cdelta)

	// these are all scalars in Zq
	comvec := make([]*r.Scalar, n-1)
	xbt := new(r.Scalar).SetZero()
	ba := new(r.Scalar).SetZero()
	for i := range comvec {
		// xbt = x.bt[i+1]
		xbt = xbt.Mul(spa.x, spa.btvec[i+1])
		// ba = bt[i]at[i+1]
		ba = ba.Mul(spa.btvec[i], spa.atvec[i+1])
		comvec[i] = new(r.Scalar).Sub(xbt, ba)
	}
	com1 := stmnt.CompactCommit(comvec, spa.st)
	if !com1.Equals(xcd) {
		//	fmt.Println("x.cDelta + cdelta != com(x.bt[i+1] - bt[i]at[i+1]; st)")
		return false
	}
	return true
}
