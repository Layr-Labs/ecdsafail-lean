import ECDSAAdd.Arithmetic.Paper935.SlotStaticMathChecks

namespace ECDSAAdd.Arithmetic.Paper935

/-- The semantic post-stage's frame conditions are consequences of the full
persistent layout; no conditions on stored values are used. -/
theorem postMath_geometry (A : Arena) (F : SlotRegisters) (b : WindowBank) (record : List Wire)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live) :
    (F.active::F.frozen::F.offset).toFinset⊆A.live ∧
    (∀ q∈b.rows.flatMap WindowRow.wires,q≠F.active ∧ q≠F.frozen ∧ q∉F.offset) ∧
    (∀ q∈[F.one,F.swap,F.parity]++F.counter,q≠F.active ∧ q≠F.frozen ∧ q∉F.offset) ∧
    F.active∉F.offset := by
  have disjoint := (List.nodup_append'.mp distinct).2.2
  refine ⟨?_,?_,?_,?_⟩
  · intro q hq
    apply owned
    simp only [List.mem_toFinset,SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    clear distinct disjoint
    tauto
  · intro q hq
    have apart : q∉F.wires := fun hm => List.disjoint_left.mp disjoint (List.mem_append_left _ hm) hq
    constructor
    · intro he; apply apart; simp [SlotRegisters.wires,he]
    constructor
    · intro he; apply apart; simp [SlotRegisters.wires,he]
    · intro he; apply apart; simp [SlotRegisters.wires,he]
  · intro q hq
    have hc := List.nodup_iff_count.mp distinct q
    have hp := List.count_pos_iff.mpr hq
    simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil] at hc hp
    constructor
    · intro he; simp only [he,beq_self_eq_true,ite_true] at hc hp; omega
    constructor
    · intro he; simp only [he,beq_self_eq_true,ite_true] at hc hp; omega
    · intro he; have hh := List.count_pos_iff.mpr he; omega
  · intro he
    have hc := List.nodup_iff_count.mp distinct F.active
    have hp := List.count_pos_iff.mpr he
    simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,ite_true] at hc
    omega

end ECDSAAdd.Arithmetic.Paper935
