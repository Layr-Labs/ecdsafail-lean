import ECDSAAdd.Arithmetic.Paper935.SlotFrontCheckedTotal

namespace ECDSAAdd.Arithmetic.Paper935

private theorem list_separate (a b : List Wire) (h : (a++b).Nodup) : List.Disjoint a b :=
  (List.nodup_append'.mp h).2.2

private theorem meta_member (F : SlotRegisters) (q : Wire)
    (hq : q∈F.one::F.frozen::F.work0::F.work1::F.offset) : q∈F.wires := by
  simp only [SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
  tauto

/-- Address-only arithmetic-semantic checks follow from the same static bank
geometry, with the explicit two-site counter and coefficient-width conditions. -/
theorem SlotFront.Compiled.mathChecks_of_geometry (P : SlotFront) (A : Arena) (b : WindowBank)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (compiled : P.Compiled A b addWidth exitWidth F)
    (addDistinct : (F.wires++P.addBank.rows.flatMap WindowRow.wires).Nodup)
    (addOwned : (F.wires++P.addBank.rows.flatMap WindowRow.wires).toFinset⊆P.addArena.live)
    (exitDistinct : (F.wires++P.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (counterWidth : 2≤F.counter.length) (coefficientWidth : 1≤exitWidth.fv) :
    P.MathChecks F exitWidth := by
  have route := compileRoutedBank_contract F.swap F.parity F.work0 F.work1 F.active P.addBank P.layout compiled.routed
  have beforeEq := route.2.1
  obtain ⟨qeq,beq,ueq,keq,aeq⟩ := route.2.2
  have dn : (F.wires++P.layout.before.rows.flatMap WindowRow.wires).Nodup := by rw [beforeEq]; exact addDistinct
  have ow : (F.wires++P.layout.before.rows.flatMap WindowRow.wires).toFinset⊆P.addArena.live := by rw [beforeEq]; exact addOwned
  have afterDn := (P.layout.after_geometry P.addArena F.wires dn ow).1
  have beforeApart := list_separate _ _ dn
  have afterApart := list_separate _ _ afterDn
  have exitApart := list_separate _ _ exitDistinct
  have inMeta : ∀ q∈P.layout.active::P.layout.q::F.counter,q∈F.wires := by
    intro q hq
    rw [aeq,qeq] at hq
    simp only [SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have counterMem : ∀ q∈F.counter,q∈F.wires := by intro q hq; simp [SlotRegisters.wires,hq]
  have nonempty : F.counter≠[] := by intro he; simp [he] at counterWidth
  have counterView : F.counter=F.counter.dropLast++[F.counter.getLastD 0] := by
    have hc := List.dropLast_concat_getLast nonempty
    have last : F.counter.getLastD 0=F.counter.getLast nonempty := by
      conv_lhs => rw [←hc]
      exact List.getLastD_concat
    rw [last]
    exact hc.symm
  have signMem : F.counter.getLastD 0∈F.counter := by
    rw [counterView]
    simp
  constructor
  · exact List.disjoint_left.mpr (fun q hq hr => List.disjoint_left.mp beforeApart (inMeta q hq) hr)
  · exact List.disjoint_left.mpr (fun q hq hr => List.disjoint_left.mp afterApart (inMeta q hq) hr)
  · exact List.disjoint_left.mpr (fun q hq hr => List.disjoint_left.mp exitApart (counterMem q hq) hr)
  · exact counterView
  · rw [aeq,beq,qeq]
    apply List.nodup_iff_count.mpr
    intro q
    have hc := List.nodup_iff_count.mp dn q
    have hs := (List.singleton_sublist.mpr signMem).count_le q
    simp only [SlotRegisters.wires,RoutedBankLayout.before,WindowBank.rows,WindowRow.wires,
      List.flatMap_cons,List.flatMap_nil,List.count_append,List.count_cons,List.count_nil] at hc hs ⊢
    omega
  · intro q hq
    rw [ueq,keq] at hq
    rw [aeq,beq,qeq]
    have hc := List.nodup_iff_count.mp dn q
    have member : 0<([F.work0,F.work1]++P.layout.before.rows.flatMap WindowRow.wires++F.counter).count q :=
      List.count_pos_iff.mpr (by simpa only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] using hq)
    simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil] at hc member
    constructor
    · intro he; simp only [he,beq_self_eq_true,ite_true] at hc member; omega
    constructor
    · intro he; simp only [he,beq_self_eq_true,ite_true] at hc member; omega
    · intro he; simp only [he,beq_self_eq_true,ite_true] at hc member; omega
  · rw [qeq]
    exact fun hq => List.disjoint_left.mp exitApart (by simp [SlotRegisters.wires]) hq
  · exact coefficientWidth
  · exact counterWidth
  · intro q hq
    have hm := meta_member F q hq
    refine ⟨ow (by simp [hm]),fun hr => List.disjoint_left.mp beforeApart hm hr,?_,?_,?_,?_⟩
    all_goals
      have hc := List.nodup_iff_count.mp dn q
      have member := List.count_pos_iff.mpr hq
      simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil] at hc member
    · intro he
      have hh := List.count_pos_iff.mpr he
      omega
    · rw [aeq]; intro he; simp only [he,beq_self_eq_true,ite_true] at hc member; omega
    · rw [beq]; intro he; simp only [he,beq_self_eq_true,ite_true] at hc member; omega
    · rw [qeq]; intro he; simp only [he,beq_self_eq_true,ite_true] at hc member; omega

end ECDSAAdd.Arithmetic.Paper935
