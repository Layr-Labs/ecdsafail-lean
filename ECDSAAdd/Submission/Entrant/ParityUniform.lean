import ECDSAAdd.Submission.Entrant.ParityEven
namespace ECDSAAdd.Entrant.ParityUniform
open Arithmetic Challenge Secp256k1 ControlledPointLayout BalancedField ParityCarry ParityConvert ParityEven EntryFuseArithmetic
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires GatePhysical toffoliCount measurementCount gateSlots

def entryAll (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) : Program :=
  if k%2=1 then ParityConvert.entryOpt K g k else entryEven K g k

def exitAll (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) : Program :=
  if k%2=1 then ParityConvert.exitOpt K g k else exitEven K g k

theorem entryAll_eq (K:MeasuredCanonicalModLayout) (g:Wire) (k Y:Nat) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (hy:Y<prime) (hk:k<prime)
    (s:State) (m:List Bool) (hY:regValue K.out s.basis=Y) (hs:regValue K.src s.basis=0)
    (hf:s.basis K.flag=false) (hh:s.basis K.high=false) (hc:s.basis K.cin=false)
    (carry:∀q∈K.carry,s.basis q=false) :
    run (entryAll K g k) m s=run (EntryFuse.entry K g complement k) m s := by
  unfold entryAll
  split_ifs with he
  · exact ParityConvert.entryOpt_eq K g k hw hn s m hs hc
  · exact entryEven_eq K g k Y hw hn (by omega) hy hk s m hY hs hf hh hc carry

theorem exitAll_eq (K:MeasuredCanonicalModLayout) (g:Wire) (k H:Fp)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256) (s:State) (m n:List Bool)
    (hH:regValue K.out s.basis=centerWord H) (hs:regValue K.src s.basis=0)
    (hf:s.basis K.flag=false) (hh:s.basis K.high=false) (hc:s.basis K.cin=false)
    (carry:∀q∈K.carry,s.basis q=false) :
    run (exitAll K g k.val) m s=run (ExitFusionResearch.exit K g complement k.val) n s := by
  unfold exitAll
  split_ifs with he
  · exact ParityConvert.exitOpt_eq K g k H hn hw s m n hH hs hf hh hc carry
  · exact exitEven_eq K g k H hn hw (by omega) s m n hH hs hf hh hc carry

theorem entryAll_counts (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    toffoliCount (entryAll K g k)+1=766 ∧ measurementCount (entryAll K g k)=767 ∧
    gateSlots (entryAll K g k)≤gateSlots (EntryFuse.entry K g complement k) := by
  unfold entryAll
  split_ifs with he
  · have H:=ParityConvert.entryOpt_counts K g k hw
    simpa only [oddSavings,he,if_true] using H
  · have H:=entryEven_counts K g hw k
    exact ⟨H.1,H.2.1,H.2.2.le⟩

theorem exitAll_counts (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    toffoliCount (exitAll K g k)+1=766 ∧ measurementCount (exitAll K g k)=766 ∧
    gateSlots (exitAll K g k)≤gateSlots (ExitFusionResearch.exit K g complement k) := by
  unfold exitAll
  split_ifs with he
  · have H:=ParityConvert.exitOpt_counts K g k hw
    simpa only [oddSavings,he,if_true] using H
  · have H:=exitEven_counts K g hw k
    exact ⟨H.1,H.2.1,by omega⟩

theorem entryAll_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    wires (entryAll K g k)⊆wires (EntryFuse.entry K g complement k) := by
  unfold entryAll
  split_ifs
  · exact ParityConvert.entryOpt_wires K g k hw
  · exact entryEven_wires K g k hw

theorem exitAll_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    wires (exitAll K g k)⊆wires (ExitFusionResearch.exit K g complement k) := by
  unfold exitAll
  split_ifs
  · exact ParityConvert.exitOpt_wires K g k hw
  · exact exitEven_wires K g k hw

theorem entryAll_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256) : GatePhysical (entryAll K g k) := by
  unfold entryAll
  split_ifs
  · exact ParityConvert.entryOpt_physical K g k hn hw
  · exact entryEven_physical K g k hn hw

theorem exitAll_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256) : GatePhysical (exitAll K g k) := by
  unfold exitAll
  split_ifs
  · exact ParityConvert.exitOpt_physical K g k hn hw
  · exact exitEven_physical K g k hn hw

def entryYAll (L:ControlledPointLayout) (k:Fp) : Program := entryAll (yLayout L) L.core.generic k.val

def exitYAll (L:ControlledPointLayout) (k:Fp) : Program := exitAll (yLayout L) L.core.generic k.val

theorem entryYAll_eq (L:ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (Y k:Fp) (s:State) (m:List Bool) (hY:regValue L.point.y s.basis=Y.val)
    (hc:regValue L.dialogPool s.basis=0) :
    run (entryYAll L k) m s=run (EntryFuse.fusedY L k) m s := by
  let K:=yLayout L
  have aux:=y_aux_clean L hw s hc
  have sz:regValue K.src s.basis=0:=(regValue_zero _ _).mpr (fun q hq=>aux q (by simp [K,hq]))
  have hy:Y.val<prime:=by rw [EntryFuse.prime_eq_secp];exact Y.isLt
  have hk:k.val<prime:=by rw [EntryFuse.prime_eq_secp];exact k.isLt
  have H:=entryAll_eq K L.core.generic k.val Y.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) hy hk s m hY sz
    (aux _ (by simp [K])) (aux _ (by simp [K])) (aux _ (by simp [K]))
    (fun q hq=>aux q (by simp [K,hq]))
  simpa only [entryYAll,EntryFuse.fusedY,K,yLayout] using H

theorem exitYAll_eq (L:ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (Y k:Fp) (s:State) (m n:List Bool) (hY:regValue L.point.y s.basis=centerWord Y)
    (hc:regValue L.dialogPool s.basis=0) :
    run (exitYAll L k) m s=run (ExitFusionResearch.exitY L k) n s := by
  let K:=yLayout L
  have aux:=y_aux_clean L hw s hc
  have sz:regValue K.src s.basis=0:=(regValue_zero _ _).mpr (fun q hq=>aux q (by simp [K,hq]))
  have H:=exitAll_eq K L.core.generic k Y
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl))
    (L.recoveryConstant_widths hw L.point.y hw.inputY) s m n hY sz
    (aux _ (by simp [K])) (aux _ (by simp [K])) (aux _ (by simp [K]))
    (fun q hq=>aux q (by simp [K,hq]))
  simpa only [exitYAll,ExitFusionResearch.exitY,K,yLayout] using H

theorem entryYAll_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (entryYAll L k)+1=766 ∧ measurementCount (entryYAll L k)=767 ∧
    gateSlots (entryYAll L k)≤gateSlots (EntryFuse.fusedY L k) := by
  exact entryAll_counts (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYAll_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (exitYAll L k)+1=766 ∧ measurementCount (exitYAll L k)=766 ∧
    gateSlots (exitYAll L k)≤gateSlots (ExitFusionResearch.exitY L k) := by
  exact exitAll_counts (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)


theorem entryYAll_wires (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryYAll L k)⊆wires (EntryFuse.fusedY L k) :=
  entryAll_wires (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYAll_wires (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (exitYAll L k)⊆wires (ExitFusionResearch.exitY L k) :=
  exitAll_wires (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem entryYAll_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (entryYAll L k) :=
  entryAll_physical (yLayout L) L.core.generic k.val
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYAll_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (exitYAll L k) :=
  exitAll_physical (yLayout L) L.core.generic k.val
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) (L.recoveryConstant_widths hw L.point.y hw.inputY)


end ECDSAAdd.Entrant.ParityUniform
