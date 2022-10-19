package qq

import (
	r "github.com/bwesterb/go-ristretto"
)

// CreateDelta({pki}ni=1 , {vi}ni=1):
// Parse pki = (Li , Ri). Sample r1,r2,...,rn−1 ←$ Fp and set rn = −􏰀sum over [n−1] ri.
// Set pk_delta,i = (Li, g^ri, g^vi . h^ri). Set pk_epsilon,i = (g, h, g^ri, g^vi . h^ri).
// Output ({pk_δ,i}, {pk_ε,i}), rvec).
func (G *QQParams) CreateDelta(act [][]*Account, v [][]int64) ([][]*Account, [][]*Account, [][]*r.Scalar, [][]*r.Scalar) {
	n := len(act)
	rand := make([][]*r.Scalar, n)
	for i, _ := range rand {
		rand[i] = make([]*r.Scalar, n)
	}
	sum := new(r.Scalar).SetZero()
	for i, ai := range act {
		for j, _ := range ai {
			rand[i][j] = new(r.Scalar).Rand()
		}
	}

	for i, ri := range rand {
		for j, _ := range ri {
			sum = new(r.Scalar).Add(sum, rand[i][j])
		}
	}

	bigZero := new(r.Scalar).SetZero()
	rand[n-1][n-1] = new(r.Scalar).Sub(bigZero, sum)

	// pk_δ,i = Li, gri, g^vi . h^ri
	actd := make([][]*Account, n)
	// pk_ε,i = g, h, g^ri, g^vi . h^ri
	acte := make([][]*Account, n)
	for i, _ := range actd {
		actd[i] = make([]*Account, n)
		acte[i] = make([]*Account, n)
	}
	for i, ri := range rand {
		for j, rij := range ri {
			grd := new(r.Point).ScalarMult(act[i][j].pk.gi, rij)
			gv := new(r.Point).ScalarMult(G.g, int64toscalar(v[i][j]))
			hr := new(r.Point).ScalarMult(act[i][j].pk.hi, rij)
			gvhrd := new(r.Point).Add(gv, hr)
			gre := new(r.Point).ScalarMult(G.g, rij)
			gvhre := new(r.Point).Add(gv, new(r.Point).ScalarMult(G.h, rij))
			actd[i][j] = &Account{act[i][j].pk, &Commitment{grd, gvhrd}}
			acte[i][j] = &Account{&PublicKey{G.g, G.h}, &Commitment{gre, gvhre}}
		}
	}
	// proof := CreateDeltaZKP()
	return actd, acte, rand, rand
}

func VerifyDelta(actd [][]*Account, acte [][]*Account, v [][]*r.Scalar, rand [][]*r.Scalar) bool {

	var rsumo *r.Point
	var rsum1 *r.Point
	for i, ei := range acte {
		for j, _ := range ei {
			rsumo = rsumo.Add(rsumo, acte[i][j].com.c)
			rsum1 = rsum1.Add(rsum1, acte[i][j].com.d)
		}
	}
	if !rsumo.Equals(new(r.Point).SetZero()) || !rsum1.Equals(new(r.Point).SetZero()) {
		return false
	}
	return true
}

func UpdateDelta(act [][]*Account, actd [][]*Account) ([][]*Account, bool) {
	n := len(act)
	actc := make([][]*Account, n)
	for i, _ := range actc {
		actc[i] = make([]*Account, n)
	}
	for i, acti := range act {
		for j, actij := range acti {
			if !lCmp(actij, actd[i][j]) {
				return nil, false
			} else {
				uc := new(r.Point).Add(actij.com.c, actd[i][j].com.c)
				ud := new(r.Point).Add(actij.com.d, actd[i][j].com.d)
				actc[i][j] = &Account{actij.pk, &Commitment{uc, ud}}
			}
		}
	}
	return actc, true
}

func VerifyUD(act *Account, actp *Account, actd *Account) bool {
	comp := &Commitment{new(r.Point).Add(act.com.c, actd.com.c), new(r.Point).Add(act.com.d, actd.com.d)}
	if !lCmp(act, actp) || !lCmp(actp, actd) || !rCmp(actp, comp) {
		return false
	}
	return true
}

func rCmp(acto *Account, c *Commitment) bool {
	if acto.com.c.Equals(c.c) && acto.com.d.Equals(c.d) {
		return true
	}
	return false
}

func lCmp(acto *Account, act1 *Account) bool {
	if acto.pk.gi.Equals(act1.pk.gi) && acto.pk.hi.Equals(act1.pk.hi) {
		return true
	}
	return false
}
