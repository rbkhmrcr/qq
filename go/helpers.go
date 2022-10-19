package qq

import (
	r "github.com/bwesterb/go-ristretto"
	"math/big"
)

type QQParams struct {
	g *r.Point
	h *r.Point
}

// SecretKey is of form sk, value
type SecretKey struct {
	ski *r.Scalar
	vi  *r.Scalar
}

// PublicKey is of form gi^r, hi^r so two curvepoints
type PublicKey struct {
	gi *r.Point
	hi *r.Point
}

// Commitment is of form gi^s, gi^vi.hi^s so two curvepoints
type Commitment struct {
	c *r.Point
	d *r.Point
}

type Account struct {
	pk  *PublicKey
	com *Commitment
}

type Value struct {
	v *r.Scalar
}

type Statement struct {
	group    *QQParams
	acti     [][]*Account // 'inputs' will have size N
	actpi    [][]*Account // 'outputs'
	inputsp  [][]*Account
	outputsp [][]*Account
	acctd    [][]*Account
	accte    [][]*Account
	m        int
	n        int        // N = n x m
	ck       []*r.Point // will have size m
	t        int
}

func SampleParams() *QQParams {
	g := new(r.Point).Rand()
	h := new(r.Point).Rand()
	return &QQParams{g, h}
}

func (g *QQParams) SampleStatement(a int, b int, t int) (*Statement, *SecretKey, [][]*r.Scalar) {
	bigZero := new(r.Scalar).SetZero()
	act := make([][]*Account, a)
	actp := make([][]*Account, a)
	sk := make([][]*SecretKey, a)
	v := make([][]*r.Scalar, a)
	rvec := make([][]*r.Scalar, a)
	for i := range act {
		act[i] = make([]*Account, b)
		actp[i] = make([]*Account, b)
		sk[i] = make([]*SecretKey, b)
		v[i] = make([]*r.Scalar, b)
		rvec[i] = make([]*r.Scalar, b)
	}

	for i := 0; i < a; i++ {
		for j := 0; j < b; j++ {
			v[i][j] = new(r.Scalar).Rand()
			sk[i][j], act[i][j] = g.AccountGen(v[i][j])
			rvec[i][j] = new(r.Scalar).Rand()
			actp[i][j] = g.Update(act[i][j], bigZero, rvec[i][j], bigZero)

		}
	}
	ck := make([]*r.Point, a+2)
	for i := 0; i < a+2; i++ {
		ck[i] = new(r.Point).Rand()
	}

	return &Statement{g, act, actp, act, actp, act, act, a, b, ck, t}, sk[0][0], rvec
}

// Add returns the result of adding two points,
// with inputs and output of type *r.Point

// Commit produces Pedersen commitments (perfectly hiding)
func (s *Statement) Commit(msg, rand *r.Scalar, i int) *r.Point {
	gm := new(r.Point).ScalarMult(s.ck[i], msg)
	hr := new(r.Point).ScalarMult(s.ck[i+1], rand)
	hr = new(r.Point).Add(gm, hr)
	return hr
}

// CompactCommit takes a slice of curvepoints (the commitment key, used as generators)
// a slice of msgs to be committed to, and a single random element of Zq for blinding,
// and returns one perfectly blinding compact commitment to all of the messages in msgs.
func (s *Statement) CompactCommit(msgs []*r.Scalar, rand *r.Scalar) *r.Point {
	var a *r.Point
	if len(s.ck) < len(msgs)+1 {
		return nil
	}
	// msg[i].g[i], com = sum msg[i].g[i] + r.h with h = ck[0]
	// this means r.ck[0] + msgs[0]ck[1]
	sum := s.Commit(msgs[0], rand, 0)
	for i := 1; i < len(msgs); i++ {
		a = new(r.Point).ScalarMult(s.ck[i+1], msgs[i])
		sum = new(r.Point).Add(sum, a)
	}
	return sum
}

func int64toscalar(index int64) *r.Scalar {
	bigindex := big.NewInt(index)
	s := new(r.Scalar).SetBigInt(bigindex)
	return s
}

func inttoscalar(index int) *r.Scalar {
	bigindex := big.NewInt(int64(index))
	s := new(r.Scalar).SetBigInt(bigindex)
	return s
}

/*
	 // use calling the above
	sum := s.Commit(msgs[0], r, 0)
	for i := range msgs {
		temp = s.Commit(msgs[i], r, i)
		sum = sum.Add(temp)
	}
	return sum
}
*/

func SampleRand() *r.Scalar {
	s, err := rand.Int(rand.Reader, groupOrder)
	check(err)
	return &r.Scalar{s}
}

/* Try and increment
-- this isn't constant time so don't feed it private info
 for {
	x = u + i
	if x³ - 3x + b is quad res in Fp {
		return x, x³ - 3x + b
	}
 }

 n^((p-1)/2) = 1 mod p iff n in QR
 z^((p-1)/2) = -1 mod p iff z not in QR

 p = 3 mod 4 so we have residues defined
 +/- n^((p+1)/4) mod p
*/
// HashToP256 takes a bigint and returns x, y coordinates
// of a P256 element st the DL is unknown.
func (g *Curve) maptoP256(u *big.Int) *r.Point {
	// G is the elliptic curve group P256
	// y² = x³ - 3x + b
	params := g.Params()
	fieldOrder := params.P
	groupOrder := params.N
	b := params.B
	bigOne := big.NewInt(int64(1))
	bigThree := big.NewInt(int64(3))
	bigFour := big.NewInt(int64(4))
	pOneFour := new(big.Int).Div(new(big.Int).Add(fieldOrder, bigOne), bigFour)
	x := u
	x.Mod(x, groupOrder)

	// y² = x³ + B
	for {
		xx := new(big.Int).Mul(x, x) // x²
		xx.Mod(xx, fieldOrder)

		xxx := xx.Mul(xx, x) // x³
		xxx.Mod(xxx, fieldOrder)
		x3 := new(big.Int).Mul(x, bigThree)
		xx.Sub(xxx, x3)
		beta := new(big.Int).Add(xxx, b) // x³ + B
		beta.Mod(beta, fieldOrder)

		//y := new(big.Int).ModSqrt(t, P)		// y = √(x³+B)
		y := new(big.Int).Exp(beta, pOneFour, fieldOrder)

		if y != nil {
			// Then verify (√(x³+B)%P)² == (x³+B)%P
			z := new(big.Int).Mul(y, y)
			z.Mod(z, fieldOrder)
			if z.Cmp(beta) == 0 {
				curveout := &r.Point{g, x, y}
				if curveout != nil {
					return curveout
				}
			}
			x.Add(x, bigOne)
		}
	}
}

// we can divide here as p = 3 mod 4 => p+1/4 is a whole number
// y² = x³ - 3x + b
// p+1/4 to be used in inverting
// we can just divide as p = 3 mod 4 => p+1/4 is a whole number
// if xxx + b has a sqrt then (xxx + b)^((p-1)/2) = 1 mod p

func (g *Curve) commitmentKeyGen(n int) []*r.Point {
	var temp *big.Int
	ck := make([]*r.Point, n+1)
	for i := 0; i < n+1; i++ {
		temp = SampleRand()
		ck[i] = g.maptoP256(temp.k)
	}
	return ck
}

func (a *PublicKey) ModPK(ord *big.Int) *PublicKey {
	a.gi.x.Mod(a.gi.x, ord)
	a.gi.y.Mod(a.gi.y, ord)
	a.hi.x.Mod(a.hi.x, ord)
	a.hi.y.Mod(a.hi.y, ord)
	return a
}
