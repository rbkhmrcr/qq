package qq

import (
	"crypto/sha256"
	r "github.com/bwesterb/go-ristretto"
)

/* Prover(pki, pki', w)     Verifier(pki, pki')
s <- Zp
a = pk_i^s = g_i^s, h_i^s
          -----------a--------->
                                  c <- {0, 1}^k
          <----------c----------
r = cw + s
          -----------r--------->
                                  Check:
                                  pk_i^r =? a.pk_i'^c
pk and upk are both formed gix, giy, hix, hiy
*/

// SchnorrID produces the 3 msg Schnorr proof,
// given the original and updates group elements,
// and the witness st upk = pk^w
func (pk *PublicKey) SigmaVerifyKPQQ(w *r.Scalar) (*r.Point, *r.Scalar, *r.Scalar) {
	rand := new(r.Scalar).Rand()
	a := new(r.Point).ScalarMult(pk.gi, rand)
	// if we're parametrising the curve we should parameterise the hash fn too really
	cdigest := sha256.Sum256(a.Bytes())
	c := new(r.Scalar).SetBytes(&cdigest)
	z := new(r.Scalar).Mul(c, w)
	z.Add(z, rand)
	return a, c, z
}

func (pk *PublicKey) VerifyKPQQ(a *r.Point, c *r.Scalar, z *r.Scalar) bool {
	// check z.gi = c.hi + a
	zg := new(r.Point).ScalarMult(pk.gi, z)
	hic := new(r.Point).ScalarMult(pk.hi, c)
	hic.Add(hic, a)

	if !hic.Equals(zg) {
		return false
	}
	return true
}

type vuarg struct {
	a *PublicKey
	c *r.Scalar
	z *r.Scalar
}

// SchnorrUpdate produces the 3 msg Schnorr proof, given the original and updates group elements,
// and the witness st upk = pk^w
func (pk *PublicKey) SigmaVUQQ(upk *PublicKey, w *r.Scalar) *vuarg {
	s := new(r.Scalar).Rand()
	a := new(r.Point).ScalarMult(pk.gi, s)
	b := new(r.Point).ScalarMult(pk.hi, s)
	// if we're parametrising the curve we should parameterise the hash fn too really
	// we feed all information into here?
	cdigest := sha256.Sum256(a.Bytes())
	c := new(r.Scalar).SetBytes(&cdigest)
	z := new(r.Scalar).Mul(c, w)
	z.Add(z, s)

	return &vuarg{&PublicKey{a, b}, c, z}
}

func (pk *PublicKey) VerifyVUQQ(upk *PublicKey, vu *vuarg) bool {
	// check z.pk = c.upk + a
	zg := new(r.Point).ScalarMult(pk.gi, vu.z)
	zh := new(r.Point).ScalarMult(pk.hi, vu.z)

	cg := new(r.Point).ScalarMult(upk.gi, vu.c)
	ch := new(r.Point).ScalarMult(upk.hi, vu.c)

	gca := new(r.Point).Add(cg, vu.a.gi)
	hca := new(r.Point).Add(ch, vu.a.hi)

	if !gca.Equals(zg) || !hca.Equals(zh) {
		return false
	} else {
		return true
	}
}

func (pk *PublicKey) SimKPQQ(c *r.Scalar) (*r.Point, *r.Scalar, *r.Scalar) {
	z := new(r.Scalar).Rand()
	// gi^x . inv(hi^c)
	a := new(r.Point).ScalarMult(pk.gi, z)
	b := new(r.Point).ScalarMult(pk.hi, c)
	// set d = inv(b) by negating its y co ordinate
	// FIX MEEEEEEEEEEEEEEE
	d := new(r.Point).Neg(b)
	// set a = z.g - c.h
	a = new(r.Point).Add(a, d)
	return a, c, z
}

func (pk *PublicKey) SimVUQQ(upk *PublicKey, c *r.Scalar) (*PublicKey, *r.Scalar, *r.Scalar) {
	// pki^z . inv(upki^c)
	// z.pk
	z := new(r.Scalar).Rand()
	ag := new(r.Point).ScalarMult(pk.gi, z)
	ah := new(r.Point).ScalarMult(pk.hi, z)
	// c.upk
	bg := new(r.Point).ScalarMult(upk.gi, c)
	bh := new(r.Point).ScalarMult(upk.hi, c)
	a := &PublicKey{ag, ah}
	b := &PublicKey{bg, bh}
	// d = inv b = ( inv(bo), inv(b1) )
	dg := new(r.Point).Neg(b.gi)
	dh := new(r.Point).Neg(b.hi)

	// set a = z.pk - c.upk
	a.gi = new(r.Point).Add(a.gi, dg)
	a.hi = new(r.Point).Add(a.hi, dh)
	return a, c, z
}

func (pk *PublicKey) KPORProofQQ(upk *PublicKey, w *r.Scalar) (*r.Point, *PublicKey, [5]*r.Scalar) {
	// cnb = challenge not b :)
	cnb := new(r.Scalar).Rand()
	// b = 0 means you have witness for VKP
	a1, c1, z1 := pk.SimVUQQ(upk, cnb)
	s := new(r.Scalar).Rand()
	ao := new(r.Point).ScalarMult(pk.gi, s)

	// put ao and a1 in a byte slice then feed that to the hash algo.
	cdigest := sha256.Sum256(ao.Bytes())
	c := new(r.Scalar).SetBytes(&cdigest)
	// define cb = c sub cnb mod groupOrder
	co := new(r.Scalar).Sub(c, c1)
	zo := new(r.Scalar).Mul(co, w)
	zo.Add(zo, s)

	return ao, a1, [5]*r.Scalar{c, co, c1, zo, z1}
}

func (pk *PublicKey) UDORProofQQ(upk *PublicKey, w *r.Scalar) (*r.Point, *PublicKey, [5]*r.Scalar) {
	cnb := new(r.Scalar).Rand()
	ao, co, zo := pk.SimKPQQ(cnb)
	s := new(r.Scalar).Rand()
	a1g := new(r.Point).ScalarMult(pk.gi, s)
	a1h := new(r.Point).ScalarMult(pk.hi, s)

	// put ao and a1 in a byte slice then feed that to the hash algo.
	cdigest := sha256.Sum256(ao.Bytes())
	c := new(r.Scalar).SetBytes(&cdigest)
	// define cb = c sub cnb mod groupOrder
	c1 := new(r.Scalar).Sub(c, co)
	z1 := new(r.Scalar).Mul(c1, w)
	z1.Add(z1, s)
	return ao, &PublicKey{a1g, a1h}, [5]*r.Scalar{c, co, c1, zo, z1}
}

func (pk *PublicKey) ORVerifQQ(upk *PublicKey, ao *r.Point, a1 *PublicKey, fe [5]*r.Scalar) bool {
	// 	c, co, c1, zo, z1 = fe
	c := fe[0]
	co := fe[1]
	c1 := fe[2]
	zo := fe[3]
	z1 := fe[4]

	// check co + c1 = c
	cc := new(r.Scalar).Add(co, c1)
	if !c.Equals(cc) {
		return false
	}

	// check zo.gi = co.hi + ao
	gzo := new(r.Point).ScalarMult(pk.gi, zo)
	hco := new(r.Point).ScalarMult(pk.hi, co)
	hca := new(r.Point).Add(hco, ao)

	if !gzo.Equals(hca) {
		// fmt.Println("zo.gi != co.hi + ao")
		return false
	}

	// check z1.pki = c1.upki + a1
	pkz1 := &PublicKey{new(r.Point).ScalarMult(pk.gi, z1), new(r.Point).ScalarMult(pk.hi, z1)}
	upkc1 := &PublicKey{new(r.Point).ScalarMult(upk.gi, c1), new(r.Point).ScalarMult(upk.hi, c1)}
	upkca := &PublicKey{new(r.Point).Add(upkc1.gi, a1.gi), new(r.Point).Add(upkc1.hi, a1.hi)}

	if !pkz1.gi.Equals(upkca.gi) || !pkz1.hi.Equals(upkca.hi) {
		// fmt.Println("z1pk != c1.upk + a1")
		return false
	}

	return true
}

/* Prover(pk1, pk2, m, r1, r2)     Verifier(pk1, pk2)
 pk1 = g1, h1, c1, d1 ; pk2 = g2, h2, c2, d2
 m', r1', r2' <- Fp
 (e1, f1) = g1^r1', g1^m', h1^r1'
 (e2, f2) = g2^r2', g2^m', h2^r2'
              ----e1, f1, e2, f2---->
                                    x <- {0, 1}^k
              <----------x----------
(zm, zr1, zr2) <- x(m, r1, r2) + (m', r1', r2')
              -----zm, zr1, zr2----->
                                      Check, for i = 1, 2
                                      gi^zri  =? ci^x . ei
																			gi^zm . hi^zri =? di^x . fi
*/

type comarg struct {
	ef1 *Commitment
	ef2 *Commitment
	x   *r.Scalar
	zm  *r.Scalar
	zr1 *r.Scalar
	zr2 *r.Scalar
}

func (q *QQParams) SigmaComQQ(act1 *Account, act2 *Account, m *r.Scalar, r1 *r.Scalar, r2 *r.Scalar) *comarg {
	mp := new(r.Scalar).Rand()
	r1p := new(r.Scalar).Rand()
	r2p := new(r.Scalar).Rand()

	e1 := new(r.Point).ScalarMult(act1.pk.gi, r1p)
	f1 := new(r.Point).Add(new(r.Point).ScalarMult(q.g, mp), new(r.Point).ScalarMult(act1.pk.hi, r1p))
	e2 := new(r.Point).ScalarMult(act2.pk.gi, r2p)
	f2 := new(r.Point).Add(new(r.Point).ScalarMult(q.g, mp), new(r.Point).ScalarMult(act2.pk.hi, r2p))

	xx := sha256.Sum256(e1.Bytes())
	x := new(r.Scalar).SetBytes(&xx)

	zm := new(r.Scalar).Add(new(r.Scalar).Mul(x, m), mp)
	zr1 := new(r.Scalar).Add(new(r.Scalar).Mul(x, r1), r1p)
	zr2 := new(r.Scalar).Add(new(r.Scalar).Mul(x, r2), r2p)

	return &comarg{&Commitment{e1, f1}, &Commitment{e2, f2}, x, zm, zr1, zr2}
}

func (q *QQParams) VerifyComQQ(act1 *Account, act2 *Account, p *comarg) bool {

	// gi^zri  =? ci^x . ei

	// gi^zri
	g1zr1 := new(r.Point).ScalarMult(act1.pk.gi, p.zr1)
	g2zr2 := new(r.Point).ScalarMult(act2.pk.gi, p.zr2)

	// ci^x . ei
	c1x := new(r.Point).Add(new(r.Point).ScalarMult(act1.com.c, p.x), p.ef1.c)
	c2x := new(r.Point).Add(new(r.Point).ScalarMult(act2.com.c, p.x), p.ef2.c)

	// gi^zm . hi^zri =? di^x . fi

	gzm := new(r.Point).ScalarMult(q.g, p.zm)

	h1zr1 := new(r.Point).ScalarMult(act1.pk.hi, p.zr1)
	h2zr2 := new(r.Point).ScalarMult(act2.pk.hi, p.zr2)

	// di^x . fi

	dxf1 := new(r.Point).Add(new(r.Point).ScalarMult(act1.com.d, p.x), p.ef1.d)
	dxf2 := new(r.Point).Add(new(r.Point).ScalarMult(act2.com.d, p.x), p.ef2.d)

	if !g1zr1.Equals(c1x) || !g2zr2.Equals(c2x) {
		return false
	}
	if !dxf1.Equals(new(r.Point).Add(gzm, h1zr1)) || !dxf2.Equals(new(r.Point).Add(gzm, h2zr2)) {
		return false
	}
	return true
}

type comskarg struct {
	como *Commitment
	com1 *Commitment
	x    *r.Scalar
	zv   *r.Scalar
	zsk  *r.Scalar
	zr   *r.Scalar
}

func (G *QQParams) SigmaComSKQQ(act1 *Account, act2 *Account, sk *SecretKey, rand *r.Scalar) *comskarg {
	rv := new(r.Scalar).Rand()
	rsk := new(r.Scalar).Rand()
	rp := new(r.Scalar).Rand()

	// gi^rsk
	e1 := new(r.Point).ScalarMult(act1.pk.gi, rsk)
	// g^rv . c1^rsk
	f1 := new(r.Point).Add(new(r.Point).ScalarMult(G.g, rv), new(r.Point).ScalarMult(act1.com.c, rsk))
	// g^rp
	e2 := new(r.Point).ScalarMult(G.g, rp)
	// g^rv . h2^rp
	f2 := new(r.Point).Add(new(r.Point).ScalarMult(G.g, rv), new(r.Point).ScalarMult(act2.pk.hi, rp))

	xx := sha256.Sum256(e1.Bytes())
	x := new(r.Scalar).SetBytes(&xx)

	// zv, zsk, zr = x(v, sk, r) + (rv, rsk, r')
	zv := new(r.Scalar).Add(new(r.Scalar).Mul(x, sk.vi), rv)
	zsk := new(r.Scalar).Add(new(r.Scalar).Mul(x, sk.ski), rsk)
	zr := new(r.Scalar).Add(new(r.Scalar).Mul(x, rand), rp)

	return &comskarg{&Commitment{e1, f1}, &Commitment{e2, f2}, x, zv, zsk, zr}
}

func (G *QQParams) VerifyComSKQQ(act1 *Account, act2 *Account, p *comskarg) bool {

	// g1^zsk  =? h1^x . e1
	// g1^zsk
	g1zsk := new(r.Point).ScalarMult(act1.pk.gi, p.zsk)
	// h1^x . e1
	h1xe := new(r.Point).Add(new(r.Point).ScalarMult(act1.pk.hi, p.x), p.como.c)
	// g1^zv . c1^zsk =? d1^x . f1
	g1zv := new(r.Point).ScalarMult(act1.pk.gi, p.zv)
	c1zsk := new(r.Point).ScalarMult(act1.com.c, p.zsk)
	// d1^x . f1
	dxf1 := new(r.Point).Add(new(r.Point).ScalarMult(act1.com.d, p.x), p.como.d)

	// g^zr  =? c2^x . e2
	// g^zr
	gzr := new(r.Point).ScalarMult(G.g, p.zr)
	// c2^x . e2
	c2xe := new(r.Point).Add(new(r.Point).ScalarMult(act2.com.c, p.x), p.com1.c)
	// g^zv . h^zr =? d2^x . f2
	gzv := new(r.Point).ScalarMult(G.g, p.zv)
	hzr := new(r.Point).ScalarMult(G.h, p.zr)
	// d2^x . f2
	dxf2 := new(r.Point).Add(new(r.Point).ScalarMult(act2.com.d, p.x), p.com1.d)

	if !g1zsk.Equals(h1xe) || !dxf1.Equals(new(r.Point).Add(g1zv, c1zsk)) {
		return false
	}
	if !gzr.Equals(c2xe) || !dxf2.Equals(new(r.Point).Add(gzv, hzr)) {
		return false
	}
	return true
}
