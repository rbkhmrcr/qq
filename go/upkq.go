package qq

import (
	r "github.com/bwesterb/go-ristretto"
)

/*
func InitialiseQ(spec string) *Curve {
	var g elliptic.Curve
	switch spec {
	case "P224":
		g = elliptic.P224()
	case "P256":
		g = elliptic.P256()
	case "P384":
		g = elliptic.P384()
	case "P521":
		g = elliptic.P521()
	}
	return &Curve{g}
}
*/

// GenQ takes the value v and returns sk, pk, and the commitment to the value
// new(r.Scalar). α, r, s ← Fp,
// set h = g^α,
// output pk = (g^r, h^r, g^s, g^v·h^s) and sk = (α, v).

func ParamGen() *QQParams {
	g := new(r.Point).Rand()
	h := new(r.Point).Rand()
	return &QQParams{g, h}
}

func (G *QQParams) AccountGen(v *r.Scalar) (*SecretKey, *Account) {

	// sample secret key
	sk := new(r.Scalar).Rand()
	// sample randomness for commitment
	s := new(r.Scalar).Rand()
	// sample randomness to blind public key
	rand := new(r.Scalar).Rand()

	// h = g^sk
	h := new(r.Point).ScalarMult(G.g, sk)
	// pko = g^r
	pko := new(r.Point).ScalarMult(G.g, rand)
	// pk1 = h^r
	pk1 := new(r.Point).ScalarMult(h, rand)

	// co = g^s
	co := new(r.Point).ScalarMult(G.g, s)
	// c1 = g^v·h^s
	gv := new(r.Point).ScalarMult(G.g, v)
	hs := new(r.Point).ScalarMult(G.h, s)
	c1 := new(r.Point).Add(gv, hs)

	return &SecretKey{sk, v}, &Account{&PublicKey{pko, pk1}, &Commitment{co, c1}}
}

// UpdateQ updates the key and value of a public key. v = 0 will just update the public key
// pki = (gi, hi), commitment = (ci, di).
// new(r.Scalar). r, s ← Fp
// output {pk′i = (gi^r, hi^r, gi^s . ci, g^vi . hi^s . di)}i.
func (G *QQParams) Update(act *Account, v *r.Scalar, rand *r.Scalar, s *r.Scalar) *Account {

	// gi^r
	pko := new(r.Point).ScalarMult(act.pk.gi, rand)
	// hi^r
	pk1 := new(r.Point).ScalarMult(act.pk.hi, rand)

	// gi^s
	gs := new(r.Point).ScalarMult(act.pk.gi, s)
	// gi^s . ci
	co := new(r.Point).Add(act.com.c, gs)
	// g^vi (global g!)
	gv := new(r.Point).ScalarMult(G.g, v)
	// hi^s
	hs := new(r.Point).ScalarMult(act.pk.hi, s)
	// g^vi . hi^s . di
	c1 := new(r.Point).Add(act.com.d, new(r.Point).Add(gv, hs))

	return &Account{&PublicKey{pko, pk1}, &Commitment{co, c1}}
}

func Derive(sk *SecretKey, v *r.Scalar) *SecretKey {
	return &SecretKey{sk.ski, new(r.Scalar).Add(v, sk.vi)}
}
