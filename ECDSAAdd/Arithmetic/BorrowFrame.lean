import ECDSAAdd.Arithmetic.Borrow

namespace ECDSAAdd.Arithmetic

/-- 实际支持集不含未访问的另一计数银行 out。 -/
theorem counterActiveXor_wires (L : AdderLayout) (target : Wire) (i : Nat) :
    wires (counterActiveXor L target i)=(target::L.cin::(L.x++L.y++L.carry)).toFinset := by
  have h := (compareLt_wires none L.x L.y L.carry L.cin target
    (by simp [AdderLayout.x,AdderLayout.y]) (by simp [AdderLayout.carry,AdderLayout.y])).2 (i+1)
  simp [counterActiveXor,wires_append,h,wires,Instr.wires,Finset.insert_comm]

/-- 活动比较只翻转 target；其它线路（包括 out）逐线保持。 -/
theorem counterActiveXor_frame (L : AdderLayout) (target : Wire)
    (hnd : (target::L.wires).Nodup) (hw : L.width=10)
    (i K : Nat) (hi : i<512) (T : Bool) (s : State) (m : List Bool)
    (ht : s.basis target=T) (hx : regValue L.x s.basis=K) (hy : regValue L.y s.basis=0)
    (hc : s.basis L.cin=false) (hcarry : regValue L.carry s.basis=0) :
    ∀ w, w≠target → (run (counterActiveXor L target i) m s).basis w=s.basis w := by
  obtain ⟨_,hv⟩ := counterActiveXor_spec L target hnd hw K i T hi s m
    ⟨⟨⟨⟨ht,hx⟩,hy⟩,hc⟩,hcarry⟩
  intro w hwt
  by_cases hm : w∈L.cin::(L.x++L.y++L.carry)
  · simp only [List.mem_cons,List.mem_append] at hm
    rcases hm with rfl | (hxm | hym) | hcarrym
    · exact hv.1.2.trans hc.symm
    · exact (regValue_eq_iff _ _ _).mp (hv.1.1.1.2.trans hx.symm) w hxm
    · exact (regValue_eq_iff _ _ _).mp (hv.1.1.2.trans hy.symm) w hym
    · exact (regValue_eq_iff _ _ _).mp (hv.2.trans hcarry.symm) w hcarrym
  · apply run_preserves_outside
    rw [counterActiveXor_wires]
    simpa using (show w≠target ∧ w∉L.cin::(L.x++L.y++L.carry) from ⟨hwt,hm⟩)

theorem counterActiveXor_counts (L : AdderLayout) (target : Wire) (i : Nat) :
    toffoliCount (counterActiveXor L target i)=L.width ∧
    measurementCount (counterActiveXor L target i)=L.width := by
  have h := (compareLt_counts none L.x L.y L.carry L.cin target
    (by simp [AdderLayout.x,AdderLayout.y]) (by simp [AdderLayout.carry,AdderLayout.y])).2.2 (i+1)
  simpa [counterActiveXor,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,AdderLayout.y,AdderLayout.width] using h

end ECDSAAdd.Arithmetic
