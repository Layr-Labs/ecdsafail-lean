import ECDSAAdd.Arithmetic.Divsteps.Routing

namespace ECDSAAdd.Arithmetic.Divsteps

/-- The same controlled paired-row routing restores the entire state. Its two
calls may use unrelated records. -/
theorem routeRows_after (q : Wire) (f g fv gv : List Wire)
    (hfg : f.length=g.length) (hvv : fv.length=gv.length)
    (hn : (q::((f++fv)++(g++gv))).Nodup) (s : State) (mf mi : List Bool) :
    run (routeRows q f g fv gv) mi (run (routeRows q f g fv gv) mf s)=s := by
  have hlen : (f++fv).length=(g++gv).length := by simp [hfg,hvv]
  let t := run (routeRows q f g fv gv) mf s
  obtain ⟨hfp,hff,hfa,hfb⟩ := swapRegisters_correct q (f++fv) (g++gv) hlen hn s mf
  have hq : t.basis q=s.basis q := by
    have h := (List.nodup_cons.mp hn).1
    exact hff q (fun hh => h (List.mem_append_left _ hh))
      (fun hh => h (List.mem_append_right _ hh))
  change regValue (f++fv) t.basis=_ at hfa
  change regValue (g++gv) t.basis=_ at hfb
  obtain ⟨hip,hif,hia,hib⟩ := swapRegisters_correct q (f++fv) (g++gv) hlen hn t mi
  change regValue (f++fv) (run (routeRows q f g fv gv) mi t).basis=_ at hia
  change regValue (g++gv) (run (routeRows q f g fv gv) mi t).basis=_ at hib
  have ha : regValue (f++fv) (run (routeRows q f g fv gv) mi t).basis=regValue (f++fv) s.basis := by
    rw [hia,hq,hfa,hfb]
    cases s.basis q <;> rfl
  have hb : regValue (g++gv) (run (routeRows q f g fv gv) mi t).basis=regValue (g++gv) s.basis := by
    rw [hib,hq,hfa,hfb]
    cases s.basis q <;> rfl
  apply congrArg₂ State.mk (hip.trans hfp)
  funext w
  by_cases hwa : w∈f++fv
  · exact (regValue_eq_iff _ _ _).mp ha w hwa
  · by_cases hwb : w∈g++gv
    · exact (regValue_eq_iff _ _ _).mp hb w hwb
    · exact (hif w hwa hwb).trans (hff w hwa hwb)

end ECDSAAdd.Arithmetic.Divsteps
