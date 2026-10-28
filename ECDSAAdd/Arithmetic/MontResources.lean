import ECDSAAdd.Arithmetic.MontWires

namespace ECDSAAdd.Arithmetic

theorem MontLayout.work_length (M : MontLayout) (hw : M.Widths) : M.work.length=1827 := by
  simp [MontLayout.work,MontLayout.activeA,MontLayout.activeZ,MontLayout.a,MontLayout.hA,
    MontLayout.fA,MontLayout.shared,MontStageLayout.work,hw.first.acc,hw.first.history,
    hw.first.table,hw.first.mask,hw.first.carry,hw.first.pad,hw.first.scratch,hw.z,hw.hZ]

/-- 输出字不计入 P/Q 的实际支持；布局中的高位 X 也不计入。 -/
theorem montPQ_resources (M : MontLayout) (p : Nat) (hw : M.Widths) (hnd : M.wires.Nodup) :
    (toffoliCount (montP M p)=189712 ∧ measurementCount (montP M p)=189712 ∧ qubitCount (montP M p)=2339) ∧
    (toffoliCount (montQ M p)=189712 ∧ measurementCount (montQ M p)=189712 ∧ qubitCount (montQ M p)=2339) := by
  have hc := montPQ_counts M p hw
  have hs := montPQ_wires M p hw
  have hn : (M.x.take 256++M.y++M.work).Nodup := by
    apply List.Sublist.nodup ?_ hnd
    change (M.x.take 256++M.y++M.work).Sublist (M.x++M.y++M.out++M.work)
    simpa only [List.nil_append,List.append_assoc] using ((List.take_sublist 256 M.x).append (List.Sublist.refl M.y)).append
      ((List.nil_sublist M.out).append (List.Sublist.refl M.work))
  have hcard : (M.x.take 256++M.y++M.work).toFinset.card=2339 := by
    rw [List.toFinset_card_of_nodup hn]
    simp [List.length_append,hw.x,hw.y,M.work_length hw]
  exact ⟨⟨hc.1.1,hc.1.2,by rw [qubitCount,hs.1,hcard]⟩,
    ⟨hc.2.1,hc.2.2,by rw [qubitCount,hs.2,hcard]⟩⟩

end ECDSAAdd.Arithmetic
