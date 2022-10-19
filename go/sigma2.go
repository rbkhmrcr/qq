package qq

import (
	r "github.com/bwesterb/go-ristretto"
	gr "github.com/zmanian/go_to_rust_ristretto"
)

type starg struct {
	vu1  [][]*vuarg
	com1 [][]*comarg
	bp1  *bulletproof
	vu2  [][]*vuarg
	bp2  *bulletproof
	com2 *comskarg
}

type stwitness struct {
	sk       *SecretKey
	inputsp  [][]*Account
	outputsp [][]*Account
	acctd    [][]*Account
	rd       [][]*r.Scalar
	accte    [][]*Account
	re       [][]*r.Scalar
	rand     [][]*r.Scalar
	vprime   [][]int64
}

type bulletproof struct {
	proof []byte
	com   [][32]byte
}

// sigmaTwo = sigma_vud (for i = 1 to n) AND sigma_com AND sigma_nn
// sigma_nn = sigma_range (for i = 2 to t+1) AND sigma_zero (for i = t+2 to n)
// sigma_zero is just sigma_vu with input commitment = com2/com1
func (s *Statement) sigmaTwo(stw *stwitness) *starg {

	// 1. sigma_vu from i = 1 to i = n
	vuargs1 := make([][]*vuarg, s.n)
	for i, _ := range vuargs1 {
		vuargs1[i] = make([]*vuarg, s.n)
	}

	for i, acti := range s.acti {
		for j, actij := range acti {
			vuargs1[i][j] = actij.pk.SigmaVUQQ(s.actpi[i][j].pk, stw.rand[i][j])
		}
	}

	// 2. sigma_com
	// prover shows knowledge of v', r such that VerifyDelta({acctδ,i}),{acctε,i},v',r)=1
	comargs := make([][]*comarg, s.n)
	for i, _ := range comargs {
		comargs[i] = make([]*comarg, s.n)
	}
	for i, acctdi := range stw.acctd {
		for j, acctdij := range acctdi {
			comargs[i][j] = s.group.SigmaComQQ(acctdij, stw.accte[i][j], int64toscalar(stw.vprime[i][j]), stw.rd[i][j], stw.re[i][j])
		}
	}

	// 3. sigma_zero is sigma_vu with upk = com2/com1
	// 4. ΣNN: (Σrange(acctδ,i,vi',ri) for i = 2 to t + 1) ∧ (Σizero for i = t+2 to n)
	// sigma_vu from i = t + 2 to i = n
	// Σizero: prover shows knowledge of randi such that VerifyUpdateAcct(inputpi, outputspi, 0, (1, randi)) = 1

	vuargs2 := make([][]*vuarg, s.n)
	for i, _ := range vuargs2 {
		vuargs2[i] = make([]*vuarg, s.n)
	}
	for i, inpi := range stw.inputsp {
		for j, inpij := range inpi {
			if i == 0 && j < s.t+2 {
				continue
			} else {
				tempcom := &PublicKey{new(r.Point).Add(inpij.com.c, new(r.Point).Neg(stw.outputsp[i][j].com.c)),
					new(r.Point).Add(inpij.com.d, new(r.Point).Neg(stw.outputsp[i][j].com.d))}
				vuargs2[i][j] = inpij.pk.SigmaVUQQ(tempcom, stw.rand[i][j])
			}
		}
	}

	// (Σrange(acctδ,i,vi',ri) for i = 2 to t + 1)
	var flatvprime []int64
	var randbytes [][]byte
	/*
		for i, _ := range randbytes {
			randbytes[i] = make([]byte, s.n)
		}
	*/

	for _, vi := range stw.vprime {
		for _, vij := range vi {
			flatvprime = append(flatvprime, vij)
		}
	}
	for i, ri := range stw.rand {
		for j, _ := range ri {
			randbytes = append(randbytes, stw.rand[i][j].Bytes())
		}
	}

	// fmt.Println("lenth of flat v prime", len(flatvprime))
	// fmt.Println("lenth of randbytes", len(randbytes))

	a, b := gr.GenerateBulletProofs(flatvprime, randbytes)
	bp1 := &bulletproof{a, b}

	// 5. Σ_range, sk
	// The sub-argument can be written as follows: given acctS = (g1, h1, c1, d1),
	// acctε = (g, h, c2, d2), the prover knows (v, sk, r) such that h1 = gsk ∧ d1 = gvcsk ∧
	// (c2, d2) = (gr, gvhr) ∧ v ∈ V. The last condition is just Σrange(acctε, v, r)
	// (i.e., a standard Bulletproof on acctε). The first three conditions can be proven using ΣCom,sk

	scsk := s.group.SigmaComSKQQ(s.acti[0][0], stw.accte[0][0], stw.sk, stw.rand[0][0])
	bp2 := &bulletproof{}

	return &starg{vuargs1, comargs, bp1, vuargs2, bp2, scsk}
}

func (s *Statement) verifySigmaTwo(sta *starg) bool {

	// 1. sigma_vu from i = 1 to i = n
	vub1 := make([][]bool, s.n)
	for i, _ := range vub1 {
		vub1[i] = make([]bool, s.n)
	}
	for i, acti := range s.acti {
		for j, actij := range acti {
			vub1[i][j] = actij.pk.VerifyVUQQ(s.actpi[i][j].pk, sta.vu1[i][j])
		}
	}

	// 2. sigma_com
	// prover shows knowledge of v', r such that VerifyDelta({acctδ,i}),{acctε,i},v',r)=1
	comb1 := make([][]bool, s.n)
	for i, _ := range comb1 {
		comb1[i] = make([]bool, s.n)
	}
	for i, acctdi := range s.acctd {
		for j, acctdij := range acctdi {
			comb1[i][j] = s.group.VerifyComQQ(acctdij, s.accte[i][j], sta.com1[i][j])
		}
	}

	vub2 := make([][]bool, s.n)
	for i, _ := range vub2 {
		vub2[i] = make([]bool, s.n)
	}
	for i, inpi := range s.inputsp {
		for j, inpij := range inpi {
			if i == 0 && j < s.t+2 {
				continue
			} else {
				tempcom := &PublicKey{new(r.Point).Add(inpij.com.c, new(r.Point).Neg(s.outputsp[i][j].com.c)),
					new(r.Point).Add(inpij.com.d, new(r.Point).Neg(s.outputsp[i][j].com.d))}
				vub2[i][j] = inpij.pk.VerifyVUQQ(tempcom, sta.vu2[i][j])
			}
		}
	}

	scb := s.group.VerifyComSKQQ(s.acti[0][0], s.accte[0][0], sta.com2)

	for i, biti := range vub1 {
		for j, bit := range biti {
			if !bit || !comb1[i][j] || !vub2[i][j] {
				return false
			}
		}
	}

	if !scb {
		return false
	}
	return true
}
