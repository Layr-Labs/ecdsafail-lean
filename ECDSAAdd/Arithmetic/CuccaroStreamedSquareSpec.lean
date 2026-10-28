import ECDSAAdd.Arithmetic.CuccaroStreamedSquareFull
import ECDSAAdd.Math.StreamedSquareValues

set_option maxRecDepth 5000000
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem checkedProgram_original (L : CuccaroStreamedSquareWideLayout) :
    L.checkedProgram=L.program := by
  rw [L.checkedProgram_eq,L.checkedFirstHalf_eq,L.checkedSecondHalf_eq,
    checkedSeq_eq,checkedSeq_eq,checkedSeq_eq,L.checkedBranchA_eq,
    L.checkedBranchBPrefix_eq,L.checkedBranchBSuffix_eq,L.checkedBranchC_eq]
  simp only [program,branchB,List.append_assoc]

theorem program_square_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B O : Nat)
    (hA : regValue L.core.low base=A) (hAb : A<2^128)
    (hB : regValue L.core.high base=B) (hBb : B<2^128)
    (hsumCarry : base L.core.sumCarry=false)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.program
      (PairFrame L base 0
        ((O+SquareReduction.p-((A+2^128*B)^2)%SquareReduction.p)%SquareReduction.p)) := by
  have hsum : A+B<2^129 := by
    norm_num [Nat.pow_succ] at hAb hBb ⊢
    omega
  have raw := L.program_pair_raw hw hnd base A B O hA hAb hB hBb hsumCarry
    hprod hO hsum hc
  have result := streamedSquareValue_exact A B O hAb hBb
  change branchCMiddleValue (A+B)
      (subTimesProductValue (B^2)
        (addRotateProductValue (B^2) (branchAValue A O) false))=_ at result
  rw [result,L.checkedProgram_original] at raw
  exact raw

/-- Exact square subtraction on every 256-bit source and canonical output.
The source, all workspace bits, every outside wire and the phase are restored. -/
theorem program_square_correct (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hprod : regValue L.core.product s.basis=0)
    (hsumCarry : s.basis L.core.sumCarry=false) (hc : PairClean L s.basis) :
    (run L.program records s).phase=s.phase ∧
    regValue L.core.out (run L.program records s).basis=
      (O+SquareReduction.p-(Y^2)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run L.program records s).basis q=s.basis q := by
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  have hab : A<2^128 := by
    simpa only [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have hbb : B<2^128 := by
    simpa only [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have split : A+2^128*B=Y := by
    have hb : L.core.high=L.core.y.drop 128 := by
      simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have h := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at h
    simpa only [A,B,CuccaroStreamedSquareLayout.low,hb,
      show min 128 256=128 by decide] using h.symm
  have pre : PairFrame L s.basis 0 O s.basis :=
    ⟨hprod,ho,fun _ _ _ => rfl⟩
  have h := L.program_square_pair hw hnd s.basis A B O rfl hab rfl hbb
    hsumCarry hprod hO hc s records pre
  rw [split] at h
  refine ⟨h.1,h.2.out,?_⟩
  intro q hqo
  by_cases hqp : q∈L.core.product
  · exact ((regValue_zero _ _).mp h.2.product q hqp).trans
      ((regValue_zero _ _).mp hprod q hqp).symm
  · exact h.2.frame q hqp hqo

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
