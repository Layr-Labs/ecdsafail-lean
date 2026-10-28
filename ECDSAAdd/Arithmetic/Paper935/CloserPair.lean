import ECDSAAdd.Arithmetic.Paper935.CloserFan

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Collapse f's payload and cancel gv, retaining f's sign. This groups
commuting fan gates; high sign-extension cancellation is included in the fan. -/
def closerPair (fs gs : Wire) (f gv : List Wire) (p : Nat) : Program :=
  closerFan fs f 1 (2^f.length-1)++closerFan gs gv p (2^gv.length-p)++[.CX fs gs]

theorem closerPair_clear (fs gs : Wire) (f gv : List Wire) (p : Nat)
    (geometry : (fs::gs::f++gv).Nodup) (fwidth : 1<2^f.length)
    (positive : 0<p) (pwidth : p<2^gv.length) (s : State) (m : List Bool)
    (fValue : regValue f s.basis=if s.basis fs then 2^f.length-1 else 1)
    (gvValue : regValue gv s.basis=if s.basis gs then 2^gv.length-p else p)
    (signs : s.basis gs=s.basis fs) :
    let out := run (closerPair fs gs f gv p) m s
    out.phase=s.phase ∧ (∀ q∈f++gv,out.basis q=false) ∧ out.basis gs=false ∧
      ∀ q∉gs::f++gv,out.basis q=s.basis q := by
  obtain ⟨fsAway,nd⟩ := List.nodup_cons.mp geometry
  obtain ⟨gsAway,nd⟩ := List.nodup_cons.mp nd
  obtain ⟨fND,gvND,apart⟩ := List.nodup_append.mp nd
  have fg : fs≠gs := fun e => fsAway (by simp [e])
  have fsF : fs∉f := fun h => fsAway (by simp [h])
  have fsG : fs∉gv := fun h => fsAway (by simp [h])
  have gsF : gs∉f := fun h => gsAway (by simp [h])
  have gsG : gs∉gv := fun h => gsAway (by simp [h])
  have first := closerFan_clear fs f 1 (2^f.length-1) fND fsF fwidth (by omega) s m fValue
  dsimp only at first
  generalize hfirst : run (closerFan fs f 1 (2^f.length-1)) m s=t at first
  have inputGV : regValue gv t.basis=if t.basis gs then 2^gv.length-p else p := by
    rw [first.2.2 gs gsF,regValue_congr gv _ s.basis (by
      intro q hq
      exact first.2.2 q (fun h => apart q h q hq rfl))]
    exact gvValue
  have second := closerFan_clear gs gv p (2^gv.length-p) gvND gsG pwidth (by omega) t m inputGV
  dsimp only at second
  generalize hsecond : run (closerFan gs gv p (2^gv.length-p)) m t=u at second
  have gsValue : u.basis gs=s.basis gs := (second.2.2 gs gsG).trans (first.2.2 gs gsF)
  have fsValue : u.basis fs=s.basis fs := (second.2.2 fs fsG).trans (first.2.2 fs fsF)
  have last : run [.CX fs gs] m u=⟨u.phase,writeBit u.basis gs false⟩ := by
    simp only [run,gsValue,fsValue,signs,Bool.xor_self]
  have execution : run (closerPair fs gs f gv p) m s=⟨u.phase,writeBit u.basis gs false⟩ := by
    rw [closerPair,run_append,run_take,run_append,run_take,
      (closerFan_counts _ _ _ _).2,List.drop_zero,hfirst,hsecond]
    simpa only [measurementCount_append,(closerFan_counts _ _ _ _).2,Nat.zero_add,List.drop_zero] using last
  dsimp only
  rw [execution]
  refine ⟨second.1.trans first.1,?_,by simp [writeBit],?_⟩
  · intro q hq
    have qgs : q≠gs := by intro e; subst q; exact gsAway hq
    change (writeBit u.basis gs false) q=false
    rw [show (writeBit u.basis gs false) q=u.basis q from Function.update_of_ne qgs _ _]
    rcases List.mem_append.mp hq with hf | hg
    · exact (second.2.2 q (fun h => apart q hf q h rfl)).trans (first.2.1 q hf)
    · exact second.2.1 q hg
  · intro q hq
    have qgs : q≠gs := fun e => hq (by simp [e])
    have qf : q∉f := fun h => hq (by simp [h])
    have qg : q∉gv := fun h => hq (by simp [h])
    exact (Function.update_of_ne qgs false u.basis).trans ((second.2.2 q qg).trans (first.2.2 q qf))

theorem closerPair_proper (fs gs : Wire) (f gv : List Wire) (p : Nat)
    (geometry : (fs::gs::f++gv).Nodup) : ProperProgram (closerPair fs gs f gv p) := by
  have fsAway := (List.nodup_cons.mp geometry).1
  have gsAway := (List.nodup_cons.mp (List.nodup_cons.mp geometry).2).1
  have fg : fs≠gs := fun e => fsAway (by simp [e])
  rw [closerPair,properProgram_append,properProgram_append]
  exact ⟨⟨closerFan_proper _ _ _ _ (fun h => fsAway (by simp [h])),
    closerFan_proper _ _ _ _ (fun h => gsAway (by simp [h]))⟩,
    by simpa [ProperProgram,ProperGate] using fg⟩

theorem closerPair_roundtrip (fs gs : Wire) (f gv : List Wire) (p : Nat)
    (geometry : (fs::gs::f++gv).Nodup) (s : State) (m n : List Bool) :
    run (closerPair fs gs f gv p).reverse n (run (closerPair fs gs f gv p) m s)=s :=
  run_reverse_proper _ (closerPair_proper fs gs f gv p geometry) s m n

end ECDSAAdd.Arithmetic.Paper935
