import ECDSAAdd.Arithmetic.MeasuredCopiedFold
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareProof

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measuredFold_eq_copied (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (f : MeasuredSquareFold) :
    L.measuredFold f=measuredCopiedFold L.measuredCore L.core.normFlag f.src f.shift f.canonical
      SquareReduction.c SquareReduction.p := by
  simp [measuredFold,foldDestination,measuredCopiedFold,copySlice,measuredFoldKernel,
    measuredFoldNormalize,measuredCore,normalizeSource,restoreSource,shortCarry,hw.core.work,
    MeasuredSourceNormalizeLayout.normalize,MeasuredSourceNormalizeLayout.restore,List.append_assoc]

theorem measuredFold_interfaces (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
    (src : List Wire) (hs : ∀q,src.count q≤L.core.product.count q) :
    (src++L.core.normFlag::L.measuredCore.wires).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  have bound := hs q
  simp only [wires,CuccaroStreamedSquareLayout.wires,measuredCore,foldCarry,foldPad,
    MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem measuredFold_carry_clean (L : CuccaroStreamedSquareWideLayout) (s : BasisState)
    (hc : L.PairClean s) : ∀q∈L.measuredCore.carry,s q=false := by
  intro q hq
  simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq|rfl|rfl
  · exact (regValue_zero _ _).mp hc.pad q hq
  · exact hc.productHigh
  · exact hc.workHigh

/-- Functional contract for the actual emitted fold, including its
short-source copy, optional normalization, canonical add, undo and unload. -/
theorem measuredFold_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (f : MeasuredSquareFold)
    (hs : ∀q,f.src.count q≤L.core.product.count q) (hl : f.shift+f.src.length≤256)
    (O : Nat) (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hcan : f.canonical=true → regValue f.src s.basis*2^f.shift<SquareReduction.p)
    (ho : regValue L.core.out s.basis=O) (hc : L.PairClean s.basis) :
    (run (L.measuredFold f) records s).phase=s.phase ∧
    regValue L.core.out (run (L.measuredFold f) records s).basis=
      (regValue f.src s.basis*2^f.shift+O)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (L.measuredFold f) records s).basis q=s.basis q := by
  rw [L.measuredFold_eq_copied hw f]
  exact measuredCopiedFold_correct L.measuredCore L.core.normFlag 256 SquareReduction.c SquareReduction.p
    (L.measuredCore_widths hw) f.src f.shift (L.measuredFold_interfaces hn f.src hs) hl
    (by decide) (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    (by norm_num [SquareReduction.c]) (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    f.canonical O hO s records hcan hc.work ho hc.normFlag hc.outHigh hc.modFlag
    (L.measuredFold_carry_clean s.basis hc) hc.cin

theorem reflectOutput_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ho : regValue L.core.out s.basis=O)
    (hc : L.PairClean s.basis) :
    (run L.reflectOutput records s).phase=s.phase ∧
    regValue L.core.out (run L.reflectOutput records s).basis=SquareReduction.p-1-O ∧
    ∀q,q∉L.core.out → (run L.reflectOutput records s).basis q=s.basis q := by
  let N : MeasuredSourceNormalizeLayout :=
    {word:=L.core.out,carry:=L.shortCarry,cin:=L.core.cin,flag:=L.core.normFlag}
  have nd : N.wires.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := (List.take_sublist 255 L.foldCarry).count_le q
    simp only [N,MeasuredSourceNormalizeLayout.wires,shortCarry,foldCarry,foldPad,
      wires,CuccaroStreamedSquareLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ht ⊢
    omega
  have len : N.carry.length+1=N.word.length := by
    change L.shortCarry.length+1=L.core.out.length
    rw [(L.measured_bank_widths hw).2.2.2.2,hw.core.out]
  have carry : ∀q∈N.carry,s.basis q=false := by
    intro q hq
    exact L.measuredFold_carry_clean s.basis hc q (List.mem_of_mem_take hq)
  have init : N.Frame s.basis O false s.basis := ⟨ho,hc.normFlag,fun _ _ => rfl⟩
  have reflected := N.reflect_frame nd len SquareReduction.p O
    (by change SquareReduction.p<2^L.core.out.length;rw [hw.core.out];norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    hO s.basis false carry hc.cin s records init
  have eq : N.reflect SquareReduction.p=L.reflectOutput := rfl
  rw [eq] at reflected
  refine ⟨reflected.1,reflected.2.1,?_⟩
  intro q hq
  by_cases flag : q=L.core.normFlag
  · subst q
    exact reflected.2.2.1.trans hc.normFlag.symm
  · exact reflected.2.2.2 q (by
      simpa only [N,MeasuredSourceNormalizeLayout.mutable,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,not_or] using And.intro hq flag)

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
