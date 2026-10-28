import ECDSAAdd.Arithmetic.DialogWires

namespace ECDSAAdd.Arithmetic

theorem dialog_qubits (L : DialogLayout) (p : Nat) (hw : L.Widths) (hn : L.wires.Nodup) :
    qubitCount (dialogDivide L p)=3126 ∧ qubitCount (dialogMultiply L p)=3126 := by
  have hr (rs : List RoundRecord) : (rs.flatMap RoundRecord.wires).length=2*rs.length := by
    induction rs with
    | nil => rfl
    | cons r rs ih => simp [RoundRecord.wires,ih]; omega
  have hc : L.first.counter.bits.length=10 := hw.counter
  have hl : L.wires.length=3126 := by
    rw [←L.registerWires_perm.length_eq]
    simp [DialogLayout.registerWires,DialogLayout.y,DialogLayout.z,
      KaliskiRoundLayout.u,KaliskiRoundLayout.v,KaliskiRoundLayout.r,KaliskiRoundLayout.s,
      KaliskiRoundLayout.data,RoundDataLayout.u,RoundDataLayout.v,RoundDataLayout.r,
      RoundDataLayout.s,RoundDataLayout.reg,KaliskiRoundLayout.k,KaliskiRoundLayout.kNext,
      AdderLayout.x,AdderLayout.y,AdderLayout.out,AdderLayout.carry,hw.low,hc,hr,hw.records]
  have hs := dialog_wires L p hw hn
  simp only [qubitCount,hs.1,hs.2,List.toFinset_card_of_nodup hn,hl,and_self]

/-- 两条同门列资源定理；相位/清理由各自spec给出。 -/
theorem dialog_resources (L : DialogLayout) (p : Nat) (hw : L.Widths) (hn : L.wires.Nodup) :
    (toffoliCount (dialogDivide L p)=3130638 ∧ measurementCount (dialogDivide L p)=1877512 ∧
      qubitCount (dialogDivide L p)=3126) ∧
    (toffoliCount (dialogMultiply L p)=2867470 ∧ measurementCount (dialogMultiply L p)=1614856 ∧
      qubitCount (dialogMultiply L p)=3126) := by
  have h := dialog_counts L p hw hn
  have q := dialog_qubits L p hw hn
  exact ⟨⟨h.1,h.2.1,q.1⟩,h.2.2.1,h.2.2.2,q.2⟩

/-- 布局外任意线路逐位保持，包括未借用的旧分配空间。 -/
theorem dialog_frame (L : DialogLayout) (p : Nat) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (w : Wire) (h : w∉L.wires) :
    (run (dialogDivide L p) m s).basis w=s.basis w ∧
    (run (dialogMultiply L p) m s).basis w=s.basis w := by
  have hs := dialog_wires L p hw hn
  constructor <;> apply run_preserves_outside
  · simpa only [hs.1,List.mem_toFinset] using h
  · simpa only [hs.2,List.mem_toFinset] using h

end ECDSAAdd.Arithmetic
