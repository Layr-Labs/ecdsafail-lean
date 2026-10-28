import ECDSAAdd.Arithmetic.Paper935.WindowBank

namespace ECDSAAdd.Arithmetic.Paper935

theorem WindowBank.Encodes.frame (b : WindowBank) (s t : BasisState) (z : ECDSAAdd.Divsteps.ZState)
    (h : b.Encodes s z) (keep : ∀ q∈b.rows.flatMap WindowRow.wires,t q=s q) : b.Encodes t z := by
  have value (r : WindowRow) (hr : r∈b.rows) : r.value t=r.value s := by
    unfold WindowRow.value signedRegValue
    rw [regValue_congr r.wires t s (fun q hq => keep q (List.mem_flatMap.mpr ⟨r,hr,hq⟩))]
  exact ⟨(value b.f (by simp [rows])).trans h.1,
    (value b.g (by simp [rows])).trans h.2.1,
    (value b.fv (by simp [rows])).trans h.2.2.1,
    (value b.gv (by simp [rows])).trans h.2.2.2⟩

end ECDSAAdd.Arithmetic.Paper935
