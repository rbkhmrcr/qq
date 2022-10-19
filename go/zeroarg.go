package qq

import (
	"crypto/sha256"
	r "github.com/bwesterb/go-ristretto"
	"math/big"
)

/*
witness
A = {a_i} for a_i vectors of length n, i runs from 1 to m
r = vector of length m
B = {b_i} for b_i vectors of length n, i runs from 1 to m
s = vector of length m

we're proving that, with statement cA, cB, star:
cA = com(A; r); cB = com(B; s);
0 = sum from i to m of a_i star b_i
*/

type zerowitness struct {
	// witness
	A    [][]*r.Scalar
	rvec []*r.Scalar // size m
	B    [][]*r.Scalar
	svec []*r.Scalar // size m
	// statement
	cA []*r.Point
	cB []*r.Point
	y  *r.Scalar // y = prod arg challenge
}

type zeroarg struct {
	// statement
	cA []*r.Point
	cB []*r.Point
	y  *r.Scalar
	// communication
	cAo *r.Point
	cBm *r.Point
	cD  []*r.Point // size 2m
	x   *r.Scalar
	a   []*r.Scalar // size n
	b   []*r.Scalar // size n
	r   *r.Scalar
	s   *r.Scalar
	t   *r.Scalar
}

func (stmnt *Statement) zeroargument(zw *zerowitness) *zeroarg {
	groupOrder, _ := new(big.Int).SetString("7237005577332262213973186563042994240857116359379907606001950938285454250989", 10)
	newa := make([][]*r.Scalar, stmnt.m+1)
	newb := make([][]*r.Scalar, stmnt.m+1)
	for i := range newa {
		newa[i] = make([]*r.Scalar, stmnt.n)
		newb[i] = make([]*r.Scalar, stmnt.n)
	}
	ao := make([]*r.Scalar, stmnt.n)
	bm := make([]*r.Scalar, stmnt.n)
	for i := range ao {
		ao[i] = new(r.Scalar).Rand()
		bm[i] = new(r.Scalar).Rand()
	}

	for i := range zw.B {
		newa[i+1] = zw.A[i]
		newb[i] = zw.B[i]
	}
	newa[0] = ao
	newb[len(newb)-1] = bm

	ro := new(r.Scalar).Rand()
	sm := new(r.Scalar).Rand()
	cAo := stmnt.CompactCommit(ao, ro)
	cBm := stmnt.CompactCommit(bm, sm)

	// do to d2m are computed as sum a_i star b_j
	temp := new(r.Scalar).SetZero()
	sum := new(r.Scalar).SetZero()
	dvec := make([]*r.Scalar, 2*(stmnt.m)+1)
	tvec := make([]*r.Scalar, 2*(stmnt.m)+1)
	cD := make([]*r.Point, 2*(stmnt.m)+1)

	for k := range cD {
		sum = sum.SetZero()
		for i, ai := range zw.A {
			for j, bj := range zw.B {
				if j == stmnt.m-k+i {
					sum = sum.Add(bilinearmap(ai, bj, zw.y), sum)
				} else {
					continue
				}
			}
		}
		dvec[k] = sum
		tvec[k] = new(r.Scalar).Rand()
	}

	tvec[stmnt.m+1] = new(r.Scalar).SetZero()

	// commit to dvec using tvec
	for i, di := range dvec {
		cD[i] = stmnt.Commit(di, tvec[i], 0)
	}

	xx := sha256.Sum256(cD[0].Bytes())
	x := new(r.Scalar).SetBytes(&xx)

	// 'answer' section of protocol
	a := make([]*r.Scalar, stmnt.n)
	b := make([]*r.Scalar, stmnt.n)
	suma := new(r.Scalar).SetZero()
	sumb := new(r.Scalar).SetZero()
	temp0 := new(r.Scalar).SetOne()
	temp1 := new(r.Scalar).SetOne()

	// we need to include these in the sums.
	// sum of x^i . A[i] (sum runs over m+1, meaning result has n entries)
	for i, ai := range newa {
		suma = suma.SetZero()
		sumb = sumb.SetZero()
		for j := range ai {
			// x^i
			temp0 = new(r.Scalar).SetBigInt(new(big.Int).Exp(x.BigInt(), big.NewInt(int64(i)), groupOrder))
			// aij . x^i
			temp1 = new(r.Scalar).Mul(temp0, ai[j])
			// sum (aij * x^i)
			suma = suma.Add(suma, temp1)
			// x^(m-i) (b starts from 0)
			temp0 = new(r.Scalar).SetBigInt(new(big.Int).Exp(x.BigInt(), big.NewInt(int64(stmnt.m-i)), groupOrder))
			// bij . x^(m-i)
			temp1 = new(r.Scalar).Mul(temp, newb[i][j])
			// sum(bij . x^(m-i))
			sumb = sumb.Add(sumb, temp1)
			a[j] = suma
			b[j] = sumb
		}
	}

	// these are done separately as we are summing values not arrays
	rand := new(r.Scalar).SetZero()
	s := new(r.Scalar).SetZero()
	t := new(r.Scalar).SetZero()

	for j := 0; j < stmnt.m; j++ {
		// x^j
		temp = new(r.Scalar).SetBigInt(new(big.Int).Exp(x.BigInt(), big.NewInt(int64(j)), groupOrder))
		// r[j] . x^j
		temp0 = new(r.Scalar).Mul(temp, zw.rvec[j])
		rand = new(r.Scalar).Add(rand, temp0)
		// x^(m-j)
		temp = new(r.Scalar).SetBigInt(new(big.Int).Exp(x.BigInt(), big.NewInt(int64(stmnt.m-j)), groupOrder))
		// s[j] . x^(m-j)
		temp0 = new(r.Scalar).Mul(temp, zw.svec[j])
		s = new(r.Scalar).Add(s, temp0)
	}
	for k := 0; k < 2*(stmnt.m); k++ {
		temp = new(r.Scalar).SetBigInt(new(big.Int).Exp(x.BigInt(), big.NewInt(int64(k)), groupOrder))
		temp0 = new(r.Scalar).Mul(temp, tvec[k])
		t = new(r.Scalar).Add(t, temp0)
	}

	return &zeroarg{
		zw.cA,
		zw.cB,
		zw.y,
		cAo,
		cBm,
		cD,
		x,
		a,
		b,
		rand,
		s,
		t,
	}
}

func (s *Statement) zverify(za *zeroarg) bool {

	groupOrder, _ := new(big.Int).SetString("7237005577332262213973186563042994240857116359379907606001950938285454250989", 10)

	// check cD is in G^2m+1
	if len(za.cD) != 2*s.m+1 {
		// fmt.Println("len(cD) != 2m+1")
	}

	zeroPoint := new(r.Point).SetZero()
	for _, cdi := range za.cD {
		if !cdi.Equals(zeroPoint) {
			// fmt.Println("cd[i] != (0, 0)")
		}
	}
	bigZero := new(r.Scalar).SetZero()
	zerocommit := s.Commit(bigZero, bigZero, 0)
	if !zerocommit.Equals(za.cD[s.m+1]) {
		// fmt.Println("cd[m+1] != com(0;0)")
	}

	ax := new(r.Scalar).SetZero()
	bx := new(r.Scalar).SetZero()

	suma := s.Commit(bigZero, bigZero, 0)
	tempa := s.Commit(bigZero, bigZero, 0)
	sumb := s.Commit(bigZero, bigZero, 0)
	tempb := s.Commit(bigZero, bigZero, 0)
	sumd := s.Commit(bigZero, bigZero, 0)
	tempd := s.Commit(bigZero, bigZero, 0)

	for i := range za.cA {
		// x^i
		ax = new(r.Scalar).SetBigInt(new(big.Int).Exp(za.x.BigInt(), big.NewInt(int64(i)), groupOrder))
		// x^(m-i)
		bx = new(r.Scalar).SetBigInt(new(big.Int).Exp(za.x.BigInt(), big.NewInt(int64(s.m-i)), groupOrder))
		// x^i . c_A(i)
		tempa = new(r.Point).ScalarMult(za.cA[i], ax)
		suma = new(r.Point).Add(suma, tempa)
		// x^(m-i) . c_B(i)
		tempb = new(r.Point).ScalarMult(za.cB[i], bx)
		sumb = new(r.Point).Add(sumb, tempb)
	}
	ar := s.CompactCommit(za.a, za.r)
	if !suma.Equals(ar) {
		// fmt.Println("suma != com(a;r)")
	}
	bs := s.CompactCommit(za.b, za.s)
	if !sumb.Equals(bs) {
		// fmt.Println("sumb != com(b;s)")
	}

	for i := range za.cD {
		ax = new(r.Scalar).SetBigInt(new(big.Int).Exp(za.x.BigInt(), big.NewInt(int64(i)), groupOrder))
		tempd = new(r.Point).ScalarMult(za.cD[i], ax)
		sumd = new(r.Point).Add(sumd, tempd)
	}
	abs := s.Commit(bilinearmap(za.a, za.b, za.y), za.s, 0)
	if !sumd.Equals(abs) {
		// fmt.Println("sumd", sumd.x, sumd.y)
		// fmt.Println("com(a.b;s)", abs.x, abs.y)
		// fmt.Println("sumd != com(a.b;s)")
	}
	return true
}
