package qq

import (
	"fmt"
	"math/rand"
	"testing"

	r "github.com/bwesterb/go-ristretto"
)

var params = SampleParams()

func TestShuffle(*testing.T) {
	s, _, _ := params.SampleStatement(2, 2, 1)
	tau := make([][]*r.Scalar, 2)
	pi := make([][]int, 2)
	var rho *r.Scalar = new(r.Scalar).Rand()
	for i := range tau {
		tau[i] = make([]*r.Scalar, 2)
		pi[i] = make([]int, 2)
	}
	for i, ai := range tau {
		for j := range ai {
			tau[i][j] = new(r.Scalar).SetZero()
			pi[i][j] = rand.Intn(2 - 1)
		}
	}
	proof := s.shuffleprove(&shufflewitness{pi, tau, rho})
}

func benchshuffle(rSize int, sqrtAsize int, b *testing.B) {
	// transact(pks *Account, sks *SecretKey, pkr []*Account, vo *Value, sk *r.Scalar,
	// v *Value, vi []*Value) {
	// 1. Pick anonymity set of size n
	k := sqrtAsize
	s, sk, rvec := params.SampleStatement(k, k, 1)
	// n := k * k // size of anonymity set is N - (rSize + 1) (sender takes 1)
	// t := rSize + 1
	// 2. Let inputs_pre = {pkS} ∪ {pkR} ∪ A
	inputspre := s.acti
	// 3. v_pre = (−v,v1,...,vt,0,...,0)
	vpre := make([][]int64, k)
	for i, _ := range vpre {
		vpre[i] = make([]int64, k)
	}
	for i, vprei := range vpre {
		for j, _ := range vprei {
			vpre[i][j] = int64(rand.Intn(64))
		}
	}
	// 4. Shuffle inputs_pre into inputs using a permutation ψ1 such that
	// (inputs1 , . . . , inputst+1 are updates of (pkS,pkR1 ,...,pkRt );
	perm1 := make([][]int, k)
	tau := make([][]*r.Scalar, k)
	rho := new(r.Scalar).Rand()
	for i := range tau {
		tau[i] = make([]*r.Scalar, k)
		perm1[i] = make([]int, k)
	}
	for i, ai := range tau {
		for j := range ai {
			tau[i][j] = new(r.Scalar).Rand()
			perm1[i][j] = rand.Intn(k - 1)
		}
	}
	inputs := make([][]*Account, k)
	for i, _ := range inputs {
		inputs[i] = make([]*Account, k)
	}
	for i, inpi := range inputspre {
		for j, _ := range inpi {
			inputs[i][j] = inputspre[perm1[i][j]][perm1[j][i]]
		}
	}
	// 5. Set the vector ⃗v such that vi = vpre,ψ1(i) -> vij = vpreψ1(i)ψ1(j);
	vvec := make([][]int64, k)
	for i, _ := range vvec {
		vvec[i] = make([]int64, k)
	}
	for i, vi := range vvec {
		for j, _ := range vi {
			vvec[i][j] = vpre[perm1[i][j]][perm1[j][i]]
		}
	}
	// 6. Set ({pk_delta, i }, {pk_epsilon, i},r) ←$ CreateDelta(inputs, ⃗v)
	acctd, accte, rd, re := params.CreateDelta(inputs, vvec)
	// 7. Update outputs_pre <- UpdateDelta(inputs, {pk_delta})
	outputspre, _ := UpdateDelta(inputs, acctd)
	// 8. Pick a random permutation ψ2, let outputs be a permutation of outputs_pre according to ψ2
	perm2 := make([][]int, k)
	tau2 := make([][]*r.Scalar, k)
	rho2 := new(r.Scalar).Rand()
	for i := range tau2 {
		tau2[i] = make([]*r.Scalar, k)
		perm2[i] = make([]int, k)
	}
	for i, ai := range tau2 {
		for j := range ai {
			tau2[i][j] = new(r.Scalar).SetOne()
			perm2[i][j] = rand.Intn(k - 1)
		}
	}
	outputs := make([][]*Account, k)
	for i, _ := range outputs {
		outputs[i] = make([]*Account, k)
	}
	for i, oi := range outputspre {
		for j, _ := range oi {
			outputs[i][j] = outputspre[perm2[i][j]][perm2[j][i]]
		}
	}

	var sigmatwo *starg
	var shproof1 *shufflearg
	var shproof2 *shufflearg

	for i := 0; i < b.N; i++ {
		// 9. Provide a zero knowledge proof π for the relation R(x,w) = R1 ∧ R2 ∧ R3,
		// where x = (inputs_pre, inputs, outputs_pre, outputs)
		// w = (sk , ⃗v, ⃗r, ψ1 : [n] → [n],ψ2 : [n] → [n],u1,ρ1,u2,ρ2,R⃗)                                                                          // such that
		// R1 = {(inputs_pre,inputs, (ψ1, u1, ρ1)) | inputs = Update(ψ1(inputspre); u1, ρ1)}
		shproof1 = s.shuffleprove(&shufflewitness{perm1, tau, rho})
		// R2 = {((inputs,outputspre,pkδ,pkε),(skS,⃗v,⃗r,R⃗)) | VerifyUD(inputsi, outputspre,i, pkδ,i) = 1 ∀i
		// ∧ VerifyDelta({pkδ,i}, {pkε,i}, ⃗v, ⃗r) = 1
		// ∧ VerifyNonNegative(pkε,i , vi , ri ) = 1 ∀i ∈ ∧ VerifyUV(inputsi, outputspre,i, ri, 0) = 1 ∧VerifyKP(inputs1,skS)>v0 +v1,
		sigmatwo = s.sigmaTwo(&stwitness{sk, inputspre, outputspre, acctd, rd, accte, re, rvec, vvec})
		// R3 = {(outputspre, outputs, (ψ2, u2, ρ2)) | outputs = Update(ψ2(outputspre); u2, ρ2)}
		shproof2 = s.shuffleprove(&shufflewitness{perm2, tau2, rho2})
		// 10. The transaction tx will consist of tx[inputs] = inputspre, tx[outputs] =
		// outputs, and an accompanying proof of correct transaction π.
	}
	b.StopTimer()
	for i := 0; i < b.N; i++ {
		s.shuffleverify(shproof1)
		s.verifySigmaTwo(sigmatwo)
		s.shuffleverify(shproof2)
	}
	b.StartTimer()
}

func BenchmarkShuffle4(b *testing.B)  { benchshuffle(1, 2, b) }
func BenchmarkShuffle16(b *testing.B) { benchshuffle(1, 4, b) }
func BenchmarkShuffle64(b *testing.B) { benchshuffle(1, 8, b) }

func benchshuffleverify(size int, sqrtAsize int, b *testing.B) {
	b.StopTimer()
	// transact(pks *Account, sks *SecretKey, pkr []*Account, vo *Value, sk *r.Scalar,
	// v *Value, vi []*Value) {
	// 1. Pick anonymity set of size n
	k := sqrtAsize
	s, sk, rvec := params.SampleStatement(k, k, 1)
	// n := k * k // size of anonymity set is N - (rSize + 1) (sender takes 1)
	// t := rSize + 1
	// 2. Let inputs_pre = {pkS} ∪ {pkR} ∪ A
	inputspre := s.acti
	// 3. v_pre = (−v,v1,...,vt,0,...,0)
	vpre := make([][]int64, k)
	for i, _ := range vpre {
		vpre[i] = make([]int64, k)
	}
	for i, vprei := range vpre {
		for j, _ := range vprei {
			vpre[i][j] = int64(rand.Intn(64))
		}
	}
	// 4. Shuffle inputs_pre into inputs using a permutation ψ1 such that
	// (inputs1 , . . . , inputst+1 are updates of (pkS,pkR1 ,...,pkRt );
	perm1 := make([][]int, k)
	tau := make([][]*r.Scalar, k)
	rho := new(r.Scalar).Rand()
	for i := range tau {
		tau[i] = make([]*r.Scalar, k)
		perm1[i] = make([]int, k)
	}
	for i, ai := range tau {
		for j := range ai {
			tau[i][j] = new(r.Scalar).Rand()
			perm1[i][j] = rand.Intn(k - 1)
		}
	}
	inputs := make([][]*Account, k)
	for i, _ := range inputs {
		inputs[i] = make([]*Account, k)
	}
	for i, inpi := range inputspre {
		for j, _ := range inpi {
			inputs[i][j] = inputspre[perm1[i][j]][perm1[j][i]]
		}
	}
	// 5. Set the vector ⃗v such that vi = vpre,ψ1(i) -> vij = vpreψ1(i)ψ1(j);
	vvec := make([][]int64, k)
	for i, _ := range vvec {
		vvec[i] = make([]int64, k)
	}
	for i, vi := range vvec {
		for j, _ := range vi {
			vvec[i][j] = vpre[perm1[i][j]][perm1[j][i]]
		}
	}
	// 6. Set ({pk_delta, i }, {pk_epsilon, i},r) ←$ CreateDelta(inputs, ⃗v)
	acctd, accte, rd, re := params.CreateDelta(inputs, vvec)
	// 7. Update outputs_pre <- UpdateDelta(inputs, {pk_delta})
	outputspre, _ := UpdateDelta(inputs, acctd)
	// 8. Pick a random permutation ψ2, let outputs be a permutation of outputs_pre according to ψ2
	perm2 := make([][]int, k)
	tau2 := make([][]*r.Scalar, k)
	rho2 := new(r.Scalar).Rand()
	for i := range tau2 {
		tau2[i] = make([]*r.Scalar, k)
		perm2[i] = make([]int, k)
	}
	for i, ai := range tau2 {
		for j := range ai {
			tau2[i][j] = new(r.Scalar).SetOne()
			perm2[i][j] = rand.Intn(k - 1)
		}
	}
	outputs := make([][]*Account, k)
	for i, _ := range outputs {
		outputs[i] = make([]*Account, k)
	}
	for i, oi := range outputspre {
		for j, _ := range oi {
			outputs[i][j] = outputspre[perm2[i][j]][perm2[j][i]]
		}
	}
	var sigmatwo *starg
	var shproof1 *shufflearg
	var shproof2 *shufflearg

	for i := 0; i < b.N; i++ {
		// 9. Provide a zero knowledge proof π for the relation R(x,w) = R1 ∧ R2 ∧ R3,
		// where x = (inputs_pre, inputs, outputs_pre, outputs)
		// w = (sk , ⃗v, ⃗r, ψ1 : [n] → [n],ψ2 : [n] → [n],u1,ρ1,u2,ρ2,R⃗)                                                                          // such that
		// R1 = {(inputs_pre,inputs, (ψ1, u1, ρ1)) | inputs = Update(ψ1(inputspre); u1, ρ1)}
		shproof1 = s.shuffleprove(&shufflewitness{perm1, tau, rho})
		// R2 = {((inputs,outputspre,pkδ,pkε),(skS,⃗v,⃗r,R⃗)) | VerifyUD(inputsi, outputspre,i, pkδ,i) = 1 ∀i
		// ∧ VerifyDelta({pkδ,i}, {pkε,i}, ⃗v, ⃗r) = 1
		// ∧ VerifyNonNegative(pkε,i , vi , ri ) = 1 ∀i ∈ ∧ VerifyUV(inputsi, outputspre,i, ri, 0) = 1 ∧VerifyKP(inputs1,skS)>v0 +v1,
		sigmatwo = s.sigmaTwo(&stwitness{sk, inputspre, outputspre, acctd, rd, accte, re, rvec, vvec})
		// R3 = {(outputspre, outputs, (ψ2, u2, ρ2)) | outputs = Update(ψ2(outputspre); u2, ρ2)}
		shproof2 = s.shuffleprove(&shufflewitness{perm2, tau2, rho2})
		// 10. The transaction tx will consist of tx[inputs] = inputspre, tx[outputs] =
		// outputs, and an accompanying proof of correct transaction π.
	}
	b.StartTimer()
	for i := 0; i < b.N; i++ {
		s.shuffleverify(shproof1)
		s.verifySigmaTwo(sigmatwo)
		s.shuffleverify(shproof2)
	}
}

func BenchmarkShuffleverify4(b *testing.B)  { benchshuffleverify(1, 2, b) }
func BenchmarkShuffleverify16(b *testing.B) { benchshuffleverify(1, 4, b) }
func BenchmarkShuffleverify64(b *testing.B) { benchshuffleverify(1, 8, b) }

// func BenchmarkShuffleverify25(b *testing.B) { benchshuffleverify(1, 5, b) }

/*
func BenchmarkOr4(b *testing.B) {
	k := 2
	s, sk, r := g.SampleStatementForTesting(k, k, 1)
	for i, pkii := range s.pki {
		for j := range pkii {
			if i == 0 {
				s.pki[i][j].KPORProof(s.upki[i][j], sk[i][j])
			} else {
				s.pki[i][j].UpdateORProof(s.upki[i][j], r[i][j])
			}
		}
	}
}
func BenchmarkOr9(b *testing.B) {
	k := 3
	s, sk, r := g.SampleStatementForTesting(k, k, 1)
	for i, pkii := range s.pki {
		for j := range pkii {
			if i == 0 {
				s.pki[i][j].KPORProof(s.upki[i][j], sk[i][j])
			} else {
				s.pki[i][j].UpdateORProof(s.upki[i][j], r[i][j])
			}
		}
	}
}
func BenchmarkOr16(b *testing.B) {
	k := 4
	s, sk, r := g.SampleStatementForTesting(k, k, 1)
	for i, pkii := range s.pki {
		for j := range pkii {
			if i == 0 {
				s.pki[i][j].KPORProof(s.upki[i][j], sk[i][j])
			} else {
				s.pki[i][j].UpdateORProof(s.upki[i][j], r[i][j])
			}
		}
	}
}
func BenchmarkOr25(b *testing.B) {
	k := 5
	s, sk, r := g.SampleStatementForTesting(k, k, 1)
	for i, pkii := range s.pki {
		for j := range pkii {
			if i == 0 {
				s.pki[i][j].KPORProof(s.upki[i][j], sk[i][j])
			} else {
				s.pki[i][j].UpdateORProof(s.upki[i][j], r[i][j])
			}
		}
	}
}

*/
