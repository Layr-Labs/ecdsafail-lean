import ECDSAAdd.Submission.Entrant.KAddCallerStructureDraft
import ECDSAAdd.Submission.Entrant.E1CallerValueFactsDraft

/-! Private whole-adder substitutions. The actual real-MF postWord premise
remains explicit; no three-call program gain or full candidate is established. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.KAddCallerBridgeResearch
open Arithmetic RecordedQuantum Challenge HighOutputTailStructuredResearch AdderSpineBridgeResearch

/-- The two forward s6 callers instantiate D=dx, par=dx%2, and the existing
MF output Kword. Their loadK/tk derivations remain the original verified ones. -/
theorem forward_run_eq (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean : s.basis (w 1796)=false) (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool)
    (hp : par=decide (D%2=1)) (flagIn : s.basis (w 1028)=par)
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=
      E1CallerValueFactsResearch.Kword D par) :
    run (literalKAdd w) m s=run (flagKAdd w) m s := by
  have facts:=E1CallerValueFactsResearch.Kword_high_div D hD par hp
  have top:=top_from_div w (run (literalKAdd w) [] s).basis _ par postWord facts.2.1
  rw [literal_split] at top ⊢
  unfold flagKAdd
  apply whole_flag (P w) (R w) (w 1028) (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
    (tail_nd w hinj) s m clean (P_avoid w hinj 1796 (Or.inl rfl))
    (P_avoid w hinj 1028 (Or.inr (Or.inl rfl))) (R_avoid w hinj 1027 (Or.inr (Or.inr rfl)))
  exact top.trans flagIn.symm

/-- Exit s12 supplies the actual canonical Y/2 MF result, including G=false. -/
theorem exit_run_eq (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean : s.basis (w 1796)=false) (Y : Nat) (hY : Y<ECDSAAdd.p)
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Y/2) :
    run (literalKAdd w) m s=run (zeroKAdd w) m s := by
  have hlt : Y/2<2^257 := lt_trans (E1CallerValueFactsResearch.exit_half_bound Y hY)
    (pow_lt_pow_right₀ (a := (2 : Nat)) (m := 255) (n := 257) (by decide) (by decide))
  have hdiv : (Y/2)/2^257=Bool.toNat false := Nat.div_eq_of_lt hlt
  have top:=top_from_div w (run (literalKAdd w) [] s).basis _ false postWord hdiv
  rw [literal_split] at top ⊢
  unfold zeroKAdd
  exact whole_zero (P w) (R w) (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
    (List.nodup_cons.mp (tail_nd w hinj)).2 s m clean
    (P_avoid w hinj 1796 (Or.inl rfl)) (R_avoid w hinj 1027 (Or.inr (Or.inr rfl))) top


/-- Pool-Nodup variant; the real MF postWord premise is still not discharged. -/
theorem forward_run_eq_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool)
    (clean : s.basis (w 1796)=false) (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool)
    (hp : par=decide (D%2=1)) (flagIn : s.basis (w 1028)=par)
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=
      E1CallerValueFactsResearch.Kword D par) :
    run (literalKAdd w) m s=run (flagKAdd w) m s := by
  have facts:=E1CallerValueFactsResearch.Kword_high_div D hD par hp
  have top:=top_from_div w (run (literalKAdd w) [] s).basis _ par postWord facts.2.1
  rw [literal_split] at top ⊢
  unfold flagKAdd
  apply whole_flag (P w) (R w) (w 1028) (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
    (tail_nd_pool w hn) s m clean (P_avoid_pool w hn 1796 (Or.inl rfl))
    (P_avoid_pool w hn 1028 (Or.inr (Or.inl rfl))) (R_avoid_pool w hn 1027 (Or.inr (Or.inr rfl)))
  exact top.trans flagIn.symm

/-- Pool-Nodup variant; the real MF postWord premise is still not discharged. -/
theorem exit_run_eq_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool)
    (clean : s.basis (w 1796)=false) (Y : Nat) (hY : Y<ECDSAAdd.p)
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Y/2) :
    run (literalKAdd w) m s=run (zeroKAdd w) m s := by
  have hlt : Y/2<2^257 := lt_trans (E1CallerValueFactsResearch.exit_half_bound Y hY)
    (pow_lt_pow_right₀ (a := (2 : Nat)) (m := 255) (n := 257) (by decide) (by decide))
  have hdiv : (Y/2)/2^257=Bool.toNat false := Nat.div_eq_of_lt hlt
  have top:=top_from_div w (run (literalKAdd w) [] s).basis _ false postWord hdiv
  rw [literal_split] at top ⊢
  unfold zeroKAdd
  exact whole_zero (P w) (R w) (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
    (List.nodup_cons.mp (tail_nd_pool w hn)).2 s m clean
    (P_avoid_pool w hn 1796 (Or.inl rfl)) (R_avoid_pool w hn 1027 (Or.inr (Or.inr rfl))) top

end ECDSAAdd.Entrant.KAddCallerBridgeResearch
