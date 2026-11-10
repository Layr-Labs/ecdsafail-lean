import ECDSAAdd.Submission.Entrant.BThreeStagedProof

import ECDSAAdd.Submission.Entrant.BManyTemp

import ECDSAAdd.Submission.Entrant.BManyData
import ECDSAAdd.Submission.Entrant.BManySteps

set_option Elab.async false

set_option maxRecDepth 100000

set_option maxHeartbeats 100000000

namespace ECDSAAdd.Entrant.BManyStaged

open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ZeroReadDevelop BManyTemp

def L := BThreeStaged301.L

def c := BThreeStaged301.c

theorem chain : ParkAChain.Steps [4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4694,4695,4696] BManyData.p0 BManyData.p22 := BManySteps.chain

theorem full_chain : ParkAChain.Steps [4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4694,4695,4696] BData301.p0 BManyData.p22 := .cons 4672 _ _ _ _ BThreeStaged301.step0_eq (.cons 4673 _ _ _ _ BThreeStaged301.step1_eq chain)

theorem hosts_eq : hosts L = [4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4694,4695,4696] := by decide +kernel

theorem actual_compiled : (compileManyChunked? (hosts L) (middle L c)).isSome=true := by
 rw [hosts_eq]
 exact BThreeStaged301.compilerSome_transport _ _ _ BThreeStaged301.input_eq (ParkAChain.isSome _ _ _ full_chain)

private theorem hasWire_transport (p q : Program) (e : p=q) (x : Wire)
 (h : FourthASavedCarryDevelop.hasWire p x=true) :
 FourthASavedCarryDevelop.hasWire q x=true := e ▸ h

private theorem hasWire_middle_to_body (K : CuccaroStreamedSquareWideLayout) (g x : Wire)
 (h : FourthASavedCarryDevelop.hasWire (middle K g) x=true) :
 FourthASavedCarryDevelop.hasWire (ParkCarry10Develop.body K g) x=true := by
 apply (FourthASavedCarryDevelop.hasWire_iff _ _).mpr
 exact BManyTemp.middle_subset_old K g ((FourthASavedCarryDevelop.hasWire_iff _ _).mp h)

theorem used_data : ∀x∈hosts L,FourthASavedCarryDevelop.hasWire BData301.p0 x=true := by
 rw [hosts_eq]
 decide +kernel

#print axioms used_data

theorem actual_ready : Ready L c := by
 refine ⟨by decide +kernel,by decide +kernel,?_⟩
 intro x hx
 have hm:x∈ManyACarryDevelop.loans L := by
  have sub:∀x∈hosts L,x∈ManyACarryDevelop.loans L := by decide +kernel
  exact sub x hx
 have loan:=ManyACarryDevelop.actual_ready.2.2 x hm
 have other:∀x∈hosts L,x∉ControlLoan1589BFFold.mR L ∧ x≠ControlLoan1589BFFold.w192 L ∧ x≠c := by decide +kernel
 refine ⟨loan,(other x hx).1,(other x hx).2.1,(other x hx).2.2,?_⟩
 exact hasWire_middle_to_body L c x
  (hasWire_transport BData301.p0 (middle L c) BThreeStaged301.input_eq x (used_data x hx))

#print axioms actual_compiled

#print axioms actual_ready

end ECDSAAdd.Entrant.BManyStaged
