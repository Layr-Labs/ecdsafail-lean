import ECDSAAdd.Arithmetic.Paper935.PinInvariants

namespace ECDSAAdd.Arithmetic.Paper935

/-- A complete persistent layout supplies every frame/ownership condition used
by the measured history stage, excluding its numerical push bound. -/
theorem historyValue_geometry (A : Arena) (F : SlotRegisters) (b : WindowBank) (record : List Wire)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live) :
    record.Nodup ∧ record.toFinset⊆A.live ∧ F.parity∈A.live ∧
    (∀ q∈[F.one,F.frozen,F.active,F.swap,F.work0,F.work1]++F.counter++F.offset,
      q∉F.parity::record) ∧
    (∀ q∈b.rows.flatMap WindowRow.wires,q∉F.parity::record) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply List.nodup_iff_count.mpr
    intro q
    have hc := List.nodup_iff_count.mp distinct q
    simp only [List.count_append] at hc
    omega
  · intro q hq
    apply owned
    simp only [List.mem_toFinset,List.mem_append] at hq ⊢
    exact Or.inl (Or.inr hq)
  · apply owned
    simp [SlotRegisters.wires]
  · intro q hq hr
    have hc := List.nodup_iff_count.mp distinct q
    have hm := List.count_pos_iff.mpr hq
    simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil] at hc hm
    rcases List.mem_cons.mp hr with he|hr
    · simp only [he,beq_self_eq_true,ite_true] at hc hm
      omega
    · have hh := List.count_pos_iff.mpr hr
      omega
  · intro q hq hr
    have hd := (List.nodup_append'.mp distinct).2.2
    apply List.disjoint_left.mp hd _ hq
    rcases List.mem_cons.mp hr with he|hr
    · simp [SlotRegisters.wires,he]
    · exact List.mem_append_right _ hr

/-- Public arithmetic leaves the incoming history integer exactly unchanged. -/
theorem compilePublicSlot_history_value (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (armed : Bool) (probeWidth offset : Nat) (P : PublicSlot) (record : List Wire)
    (compiled : compilePublicSlot A b addWidth exitWidth F armed probeWidth offset=some P)
    (counterNonempty : F.counter≠[]) (coefficientNonempty : P.front.exitBank.fv.payload≠[])
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (s : State) (m : List Bool) :
    regValue record (run (P.program F) m s).basis=regValue record s.basis := by
  apply regValue_congr
  intro q hq
  have qOwn : q∈A.live := owned (by simp [hq])
  have noMeta : q∉F.wires := by
    intro hm
    have hd := (List.nodup_append'.mp (List.nodup_append'.mp distinct).1).2.2
    exact List.disjoint_left.mp hd hm hq
  have noRows : q∉b.rows.flatMap WindowRow.wires := by
    intro hr
    have hd := (List.nodup_append'.mp distinct).2.2
    exact List.disjoint_left.mp hd (List.mem_append_right _ hq) hr
  exact (compilePublicSlot_external A b addWidth exitWidth F armed probeWidth offset P compiled
    counterNonempty coefficientNonempty q qOwn noMeta noRows).2.2 s m

end ECDSAAdd.Arithmetic.Paper935
