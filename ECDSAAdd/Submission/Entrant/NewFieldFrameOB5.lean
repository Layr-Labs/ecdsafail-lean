import ECDSAAdd.Submission.Entrant.NewEncodedFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.NewFieldFrameOB5
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport
open OffsetBorrowedCanonical NewHistory5
attribute [local irreducible] run wires

def EncodedFieldFrame (origin : BasisState) (X Y : Fp) (s : State) : Prop :=
  EncodedFieldFrame5 base (base 2409) origin X Y (pullState (OB5.sig 511) s)

def EncodedCanonicalFrame (origin : BasisState) (X Y : Fp) (s : State) : Prop :=
  EncodedCanonicalFrame5 origin X Y (pullState (OB5.sig 511) s)

















/-- Transport the complete logical field contract through sig511. -/
theorem placed_step (P : Program) (origin : BasisState) (X Y A B : Fp)
    (correct : ∀s m, EncodedFieldFrame5 base (base 2409) origin X Y s →
      (run P m s).phase=s.phase ∧ EncodedFieldFrame5 base (base 2409) origin A B (run P m s))
    (s : State) (m : List Bool) (input : EncodedFieldFrame origin X Y s) :
    (run (renameProgram (OB5.sig 511) P) m s).phase=s.phase ∧
      EncodedFieldFrame origin A B (run (renameProgram (OB5.sig 511) P) m s) := by
  have result := correct (pullState (OB5.sig 511) s) m input
  have same := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide)) P m s
  rw [←same] at result
  exact result






















/-- The one-bank parity site is outside every history codec. -/
theorem otherEncode_parity_away (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (n j : Nat) (bound : 5*n≤512) :
    w 2312∉wires (otherEncode w j n) := by
  intro member
  obtain ⟨k,hk,_,used⟩ := otherEncode_member w n j (w 2312) member
  obtain ⟨r,eq⟩ := NewHistory5.history_gate_mem w (5*k) _ (Or.inl rfl) (w 2312) used
  have b := History5.historyId_bound (5*k) (by omega) r
  have same := skywalkShared_index_inj w hn 2312 (History5.historyId (5*k) r) (by omega) (by omega) eq
  omega

theorem otherEncode_body_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hb : b∉skywalkPoolWires w) (hs : sign∉skywalkPoolWires w) (he : eff∉skywalkPoolWires w)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (body : Program)
    (support : wires body⊆NewHistory5.groupReadSites w b sign eff (5*j) ∪ {w 2312}) :
    Disjoint (wires (otherEncode w j n)) (wires body) := by
  have old := NewHistory5.otherEncode_body_disjoint w b sign eff hn hb hs he n j bound hj
  apply Finset.disjoint_left.mpr
  intro q hq used
  rcases Finset.mem_union.mp (support used) with h|h
  · have one : wires [.X q]⊆NewHistory5.groupReadSites w b sign eff (5*j) := by
      intro t ht
      have same : t=q := by simpa [wires,Instr.wires] using ht
      exact same ▸ h
    exact Finset.disjoint_left.mp (old [.X q] one) hq (by simp [wires,Instr.wires])
  · have same : q=w 2312 := Finset.mem_singleton.mp h
    exact otherEncode_parity_away w hn n j bound (same ▸ hq)

/-- Codec transport with the additional real parity site2312. -/
theorem encoded_window_step (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hp : ∀q∈[b,sign,eff],q∉skywalkPoolWires w)
    (j : Nat) (hj : j<102) (origin : BasisState) (X Y A B : Fp) (body : Program)
    (support : wires body⊆NewHistory5.groupReadSites w b sign eff (5*j) ∪ {w 2312})
    (correct : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord X) (centerWord Y)) body
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame5 w sign origin X Y s)
    (legal : RawLegal w 102 origin) :
    let out := run (decode w (5*j)++body++encode w (5*j)) m s
    out.phase=s.phase ∧ EncodedFieldFrame5 w sign origin A B out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have leg := frame_history_legal w sign hn (hp sign (by simp)) 102 (by decide)
    origin raw.basis _ _ legal frame
  have factor := allEncode_factor w pool 102 j (by decide) hj raw
  have hE := otherEncode_disjoint w pool 102 j (by decide) hj
  have hB := otherEncode_body_disjoint w b sign eff hn
    (hp b (by simp)) (hp sign (by simp)) (hp eff (by simp)) 102 j (by decide) hj body support
  let mb := m.drop 2
  let rawOut := run body mb raw
  have result := correct raw mb frame
  have outLeg := frame_history_legal w sign hn (hp sign (by simp)) 102 (by decide)
    origin rawOut.basis _ _ legal result.2
  have transport := window_transport_other w (5*j) pool (by omega)
    (otherEncode w j 102) body hE hB raw [] [] (m.take 2) mb (mb.drop (measurementCount body)) (leg j hj)
  have records : run (encode w (5*j)) (mb.drop (measurementCount body)) rawOut=
      run (encode w (5*j)) [] rawOut :=
    ParityCodec5New.encodeAt_independent _ (historyMap_injective w pool _ (by omega)) _ _ _ (outLeg j hj)
  rw [records] at transport
  have back := allEncode_factor w pool 102 j (by decide) hj rawOut
  rw [←back] at transport
  have actual : run (decode w (5*j)++body++encode w (5*j)) m s=run (allEncode w 102) [] rawOut := by
    rw [eq,factor]
    simp only [List.append_assoc]
    rw [run_append,(decode_counts w (5*j)).2,run_append,run_take]
    exact transport
  dsimp only
  rw [actual]
  have encPhase := allEncode_zero_phase w pool 102 (by decide) rawOut
  exact ⟨encPhase.trans (result.1.trans phase),rawOut,encPhase.symm,result.2,rfl⟩



theorem pull_swap_zero (a b : Wire) (s : State)
    (ha : s.basis a=false) (hb : s.basis b=false) : pullState (Equiv.swap a b) s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (Equiv.swap a b q)=s.basis q
    by_cases ea : q=a
    · subst q; simp only [Equiv.swap_apply_left,ha,hb]
    · by_cases eb : q=b
      · subst q; simp only [Equiv.swap_apply_right,ha,hb]
      · rw [Equiv.swap_apply_of_ne_of_ne ea eb]

/-- Rebind two clean sites without changing the complete State or phase. -/
theorem rebind_swap_run (a b : Wire) (P : Program) (s : State) (m : List Bool)
    (ha : s.basis a=false) (hb : s.basis b=false)
    (oa : (run P m s).basis a=false) (ob : (run P m s).basis b=false) :
    run (renameProgram (Equiv.swap a b) P) m s=run P m s := by
  apply pullState_perm_injective (Equiv.swap a b)
  rw [run_rename _ (Equiv.swap a b).injective,pull_swap_zero a b s ha hb,
    pull_swap_zero a b (run P m s) oa ob]

end ECDSAAdd.Entrant.NewFieldFrameOB5
