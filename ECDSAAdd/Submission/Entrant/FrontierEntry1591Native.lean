import ECDSAAdd.Submission.Entrant.OneFlag

set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace ECDSAAdd.Entrant.FrontierEntry1591Native.Transport
open Arithmetic RecordedQuantum Challenge
attribute [local irreducible] run wires

def program (work host : Wire) (P : Program) : Program :=
  renameProgram (Equiv.swap work host) P

theorem pull_swap_clean (work host : Wire) (s : State)
    (hw : s.basis work=false) (hh : s.basis host=false) :
    pullState (Equiv.swap work host) s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (Equiv.swap work host q)=s.basis q
    by_cases qw : q=work
    · subst q; simp only [Equiv.swap_apply_left,hw,hh]
    by_cases qh : q=host
    · subst q; simp only [Equiv.swap_apply_right,hw,hh]
    rw [Equiv.swap_apply_of_ne_of_ne qw qh]

theorem pull_swap_invol (work host : Wire) (s : State) :
    pullState (Equiv.swap work host) (pullState (Equiv.swap work host) s)=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (Equiv.swap work host (Equiv.swap work host q))=s.basis q
    rw [Equiv.swap_apply_self]

/-- Renaming preserves the entire output, including phase, for each record tape. -/
theorem run_eq (work host : Wire) (P : Program) (s : State) (m : List Bool)
    (hw : s.basis work=false) (hh : s.basis host=false)
    (ow : (run P m s).basis work=false) (oh : host∉wires P) :
    run (program work host P) m s=run P m s := by
  have hostOut : (run P m s).basis host=false :=
    (run_preserves_outside P m s host oh).trans hh
  have same := ECDSAAdd.run_rename (Equiv.swap work host)
    (Equiv.swap work host).injective P m s
  rw [pull_swap_clean work host s hw hh,
    ←pull_swap_clean work host (run P m s) ow hostOut] at same
  have lifted := congrArg (pullState (Equiv.swap work host)) same
  simpa only [pull_swap_invol,program] using lifted

/-- Independent-record correctness is inherited from the original program. -/
theorem run_eq_independent (work host : Wire) (P : Program) (s : State)
    (m n : List Bool) (hw : s.basis work=false) (hh : s.basis host=false)
    (ow : (run P m s).basis work=false) (oh : host∉wires P)
    (records : run P m s=run P n s) :
    run (program work host P) m s=run P n s :=
  (run_eq work host P s m hw hh ow oh).trans records

theorem counts (work host : Wire) (P : Program) :
    toffoliCount (program work host P)=toffoliCount P ∧
      measurementCount (program work host P)=measurementCount P :=
  renameProgram_counts _ _

theorem slots (work host : Wire) (P : Program) :
    gateSlots (program work host P)=gateSlots P := Baselines.rename_gateSlots _ _

theorem physical (work host : Wire) (P : Program) (hp : GatePhysical P) :
    GatePhysical (program work host P) :=
  gatePhysical_rename _ (Equiv.swap work host).injective _ hp

theorem support (work host : Wire) (P : Program) :
    wires (program work host P)=(wires P).image (Equiv.swap work host) :=
  renameProgram_support _ _

theorem avoids_work (work host : Wire) (P : Program) (oh : host∉wires P) :
    work∉wires (program work host P) := by
  intro used
  rw [support] at used
  obtain ⟨old,mem,eq⟩ := Finset.mem_image.mp used
  have same : old=host := (Equiv.swap work host).injective
    (eq.trans (Equiv.swap_apply_right work host).symm)
  exact oh (same ▸ mem)

theorem support_subset (work host : Wire) (P : Program) (S : Finset Wire)
    (hp : wires P⊆S) (hh : host∈S) (oh : host∉wires P) :
    wires (program work host P)⊆S.erase work := by
  intro q hq
  have notWork : q≠work := fun eq => avoids_work work host P oh (eq ▸ hq)
  refine Finset.mem_erase.mpr ⟨notWork,?_⟩
  rw [support] at hq
  obtain ⟨old,mem,rfl⟩ := Finset.mem_image.mp hq
  by_cases ow : old=work
  · subst old; simpa only [Equiv.swap_apply_left] using hh
  have oh' : old≠host := fun eq => oh (eq ▸ mem)
  simpa only [Equiv.swap_apply_of_ne_of_ne ow oh'] using hp mem

end ECDSAAdd.Entrant.FrontierEntry1591Native.Transport

set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace ECDSAAdd.Entrant.FrontierEntry1591Native
open Arithmetic RecordedQuantum Secp256k1
attribute [local irreducible] run wires NativeFirstDirect.forward NativeFirstKnown.inverse

def forward (w : Nat → Wire) : Program :=
  Transport.program (w 1797) (w 511) (NativeFirstDirect.forward w)

def inverse (w : Nat → Wire) : Program :=
  Transport.program (w 1797) (w 511) (NativeFirstKnown.inverse w)

theorem host_not_prefix (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    w 511∉NativeFirstDirect.prefixSites w := by
  have a := NativeFirstDirect.block_not_mem w hn 511 0 257 (by omega) (by omega) (by omega)
  have b := NativeFirstDirect.block_not_mem w hn 511 770 258 (by omega) (by omega) (by omega)
  have c := NativeFirstDirect.block_not_mem w hn 511 1540 256 (by omega) (by omega) (by omega)
  have s := NativeFirstDirect.index_ne w hn 511 1028 (by omega) (by omega) (by omega)
  have i := NativeFirstDirect.index_ne w hn 511 1797 (by omega) (by omega) (by omega)
  simpa only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,not_or] using And.intro (And.intro (And.intro a b) c) (And.intro s i)

theorem native_host_away (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    w 511∉wires (NativeFirstDirect.forward w) ∧
      w 511∉wires (NativeFirstKnown.inverse w) :=
  ⟨fun h => host_not_prefix w hn (List.mem_toFinset.mp ((NativeFirstDirect.prefix_support w).1 h)),
    fun h => host_not_prefix w hn (List.mem_toFinset.mp (NativeFirstKnown.inverse_support w h))⟩

theorem boundary_not_mutable (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i=511 ∨ i=1797) : w i∉NativeFirstDirect.mutable w := by
  have a := NativeFirstDirect.block_not_mem w hn i 0 257 (by omega) (by omega) (by omega)
  have b := NativeFirstDirect.block_not_mem w hn i 770 258 (by omega) (by omega) (by omega)
  have s := NativeFirstDirect.index_ne w hn i 1028 (by omega) (by omega) (by omega)
  simpa only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
    using And.intro (And.intro a b) s

theorem caller_clean (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (s : State) (hin : SkywalkArithmeticInput w x y s.basis) :
    s.basis (w 1797)=false ∧ s.basis (w 511)=false := by
  have ready := NativeFirstDirect.caller_ready w hn x y s.basis hin
  refine ⟨ready.1.cin,?_⟩
  apply hin.2.2
  · exact List.mem_map.mpr ⟨511,by simp [List.mem_range'_1],rfl⟩
  · exact NativeFirstDirect.block_not_mem w (skywalkShared_integer_nodup w hn)
      511 770 256 (by omega) (by omega) (by omega)
  · intro used
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp used
    simp only [List.mem_range'_1] at hi
    have same := skywalkShared_index_inj w hn i 511 (by omega) (by omega) eq
    omega

theorem forward_clean (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput w x y s.basis) :
    (run (NativeFirstDirect.forward w) m s).basis (w 1797)=false ∧
      (run (NativeFirstDirect.forward w) m s).basis (w 511)=false := by
  have pool := skywalkShared_integer_nodup w hn
  have ready := NativeFirstDirect.caller_ready w hn x y s.basis hin
  have out := NativeFirstDirect.forward_spec w pool x hx s m ready.1
  have zeros := caller_clean w hn x y s hin
  exact ⟨(out.2.2.2.2.2 _ (boundary_not_mutable w pool 1797 (Or.inr rfl))).trans zeros.1,
    (out.2.2.2.2.2 _ (boundary_not_mutable w pool 511 (Or.inl rfl))).trans zeros.2⟩

/-- No extra clean-site premise is added to the actual forward caller. -/
theorem forward_run_eq (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput w x y s.basis) :
    run (forward w) m s=run (NativeFirstDirect.forward w) m s := by
  have before := caller_clean w hn x y s hin
  have after := forward_clean w hn x y hx s m hin
  exact Transport.run_eq _ _ _ s m before.1 before.2 after.1
    (native_host_away w (skywalkShared_integer_nodup w hn)).1

/-- The existing pool-restoration handoff also licenses the hosted inverse.
The forward and inverse record tapes are independent. -/
theorem inverse_run_eq (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx : x<p) (initial field : State) (mF mI : List Bool)
    (hin : SkywalkArithmeticInput w x y initial.basis)
    (hphase : field.phase=(run (NativeFirstDirect.forward w) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires w,
      field.basis q=(run (NativeFirstDirect.forward w) mF initial).basis q) :
    run (inverse w) mI field=run (NativeFirstKnown.inverse w) mI field := by
  have pool := skywalkShared_integer_nodup w hn
  have member (i : Nat) (hi : i<1798) : w i∈skywalkPoolWires w :=
    List.mem_map.mpr ⟨i,by simpa only [List.mem_range'_1] using And.intro (Nat.zero_le i) hi,rfl⟩
  have before := caller_clean w hn x y initial hin
  have after := forward_clean w hn x y hx initial mF hin
  have work : field.basis (w 1797)=false := (hpool _ (member 1797 (by omega))).trans after.1
  have host : field.basis (w 511)=false := (hpool _ (member 511 (by omega))).trans after.2
  have ready := NativeFirstDirect.caller_ready w hn x y initial.basis hin
  have restored := NativeFirstKnown.inverse_restore_after_outside w pool x initial field mF mI
    ready.1 hphase hpool
  have workOut : (run (NativeFirstKnown.inverse w) mI field).basis (w 1797)=false :=
    (restored.2.1 _ (member 1797 (by omega))).trans before.1
  exact Transport.run_eq _ _ _ field mI work host workOut (native_host_away w pool).2

def sites (w : Nat → Wire) : Finset Wire :=
  (insert (w 511) (NativeFirstDirect.prefixSites w).toFinset).erase (w 1797)

theorem support (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    wires (forward w)⊆sites w ∧ wires (inverse w)⊆sites w := by
  have sub : (NativeFirstDirect.prefixSites w).toFinset⊆
      insert (w 511) (NativeFirstDirect.prefixSites w).toFinset := Finset.subset_insert _ _
  exact ⟨Transport.support_subset _ _ _ _
      ((NativeFirstDirect.prefix_support w).1.trans sub) (Finset.mem_insert_self _ _)
      (native_host_away w hn).1,
    Transport.support_subset _ _ _ _
      ((NativeFirstKnown.inverse_support w).trans sub) (Finset.mem_insert_self _ _)
      (native_host_away w hn).2⟩

theorem avoids_work (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    w 1797∉wires (forward w) ∧ w 1797∉wires (inverse w) :=
  ⟨Transport.avoids_work _ _ _ (native_host_away w hn).1,
    Transport.avoids_work _ _ _ (native_host_away w hn).2⟩

theorem counts (w : Nat → Wire) :
    toffoliCount (forward w)=508 ∧ measurementCount (forward w)=508 ∧
      toffoliCount (inverse w)=256 ∧ measurementCount (inverse w)=508 := by
  have f := Transport.counts (w 1797) (w 511) (NativeFirstDirect.forward w)
  have i := Transport.counts (w 1797) (w 511) (NativeFirstKnown.inverse w)
  simpa only [forward,inverse,NativeFirstDirect.forward_counts,NativeFirstKnown.inverse_counts]
    using And.intro f.1 (And.intro f.2 i)

theorem slots (w : Nat → Wire) :
    Challenge.gateSlots (forward w)=Challenge.gateSlots (NativeFirstDirect.forward w) ∧
      Challenge.gateSlots (inverse w)=Challenge.gateSlots (NativeFirstKnown.inverse w) :=
  ⟨Transport.slots _ _ _,Transport.slots _ _ _⟩

theorem physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (forward w) ∧ GatePhysical (inverse w) :=
  ⟨Transport.physical _ _ _ (NativeFirstDirect.programs_physical w hn).1,
    Transport.physical _ _ _ (NativeFirstKnown.inverse_physical w hn)⟩

end ECDSAAdd.Entrant.FrontierEntry1591Native

namespace ECDSAAdd.Entrant.FrontierEntry1591Native
open Arithmetic RecordedQuantum Secp256k1 MappedCompressed
attribute [local irreducible] run wires NativeFirstDirect.forward NativeFirstKnown.inverse

theorem forward_phase (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput w x y s.basis) :
    (run (forward w) m s).phase=s.phase := by
  rw [forward_run_eq w hn x y hx s m hin]
  exact (NativeFirstDirect.forward_spec w (skywalkShared_integer_nodup w hn) x hx s m
    (NativeFirstDirect.caller_ready w hn x y s.basis hin).1).1

theorem caller_first_stage (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput w x y s.basis) :
    CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 1
      (run (forward w) m s).basis := by
  rw [forward_run_eq w hn x y hx s m hin]
  exact NativeFirstDirect.caller_first_stage w hn x y hx0 hx s m hin

theorem inverse_restore_after_outside (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx : x<p) (initial field : State) (mF mI : List Bool)
    (hin : SkywalkArithmeticInput w x y initial.basis)
    (hphase : field.phase=(run (forward w) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires w,
      field.basis q=(run (forward w) mF initial).basis q) :
    (run (inverse w) mI field).phase=initial.phase ∧
    (∀q∈skywalkPoolWires w,(run (inverse w) mI field).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires w → (run (inverse w) mI field).basis q=field.basis q) := by
  rw [forward_run_eq w hn x y hx initial mF hin] at hphase hpool
  rw [inverse_run_eq w hn x y hx initial field mF mI hin hphase hpool]
  exact NativeFirstKnown.inverse_restore_after_outside w (skywalkShared_integer_nodup w hn)
    x initial field mF mI (NativeFirstDirect.caller_ready w hn x y initial.basis hin).1 hphase hpool

/-- The exact order used by the accepted integer host composition. -/
def hosted (P : Program) : Program :=
  renameProgram Q7IntegerHost.swap
    (renameProgram Q6IntegerHost.swap (renameProgram Q5Global718.swap P))

def acceptedSwap : Equiv.Perm Wire :=
  Q5Global718.swap.trans (Q6IntegerHost.swap.trans Q7IntegerHost.swap)

theorem hosted_eq (P : Program) : hosted P=renameProgram acceptedSwap P := by
  rw [hosted,renameProgram_comp,renameProgram_comp]
  rfl

theorem acceptedSwap_work : acceptedSwap (base 1797)=base 1797 := by decide +kernel

theorem acceptedSwap_host : acceptedSwap (base 511)=base 511 := by decide +kernel

theorem hosted_append (P Q : Program) : hosted (P++Q)=hosted P++hosted Q := by
  simp only [hosted,renameProgram,List.map_append]

theorem hosted_run (P : Program) (m : List Bool) (s : State) :
    pullState acceptedSwap (run (hosted P) m s)=run P m (pullState acceptedSwap s) := by
  rw [hosted_eq]
  exact run_rename acceptedSwap acceptedSwap.injective P m s

theorem hosted_run_eq (P Q : Program) (s : State) (m n : List Bool)
    (same : run P m (pullState acceptedSwap s)=run Q n (pullState acceptedSwap s)) :
    run (hosted P) m s=run (hosted Q) n s := by
  apply pullState_perm_injective acceptedSwap
  rw [hosted_run,hosted_run]
  exact same

theorem accepted_pull_clean (x y : Nat) (s : State)
    (hin : SkywalkArithmeticInput base x y s.basis) : pullState acceptedSwap s=s := by
  have a := Q5Global718.pull_clean s
    (Q5Global718.input_clean x y 1026 s hin (Or.inr rfl))
    (Q5Global718.input_clean x y 718 s hin (Or.inl rfl))
  have b := Q6IntegerHost.pull_clean s
    (Q6IntegerHost.input_clean x y 1541 s hin (Or.inr rfl))
    (Q6IntegerHost.input_clean x y 719 s hin (Or.inl rfl))
  have c := Q7IntegerHost.pull_clean s
    (Q7IntegerHost.input_clean x y 1542 s hin (Or.inr rfl))
    (Q7IntegerHost.input_clean x y 720 s hin (Or.inl rfl))
  change pullState Q5Global718.swap
    (pullState Q6IntegerHost.swap (pullState Q7IntegerHost.swap s))=s
  rw [c,b,a]

theorem hosted_forward_run_eq (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x y s.basis) :
    run (hosted (forward base)) m s=run (hosted (NativeFirstDirect.forward base)) m s := by
  apply hosted_run_eq
  rw [accepted_pull_clean x y s hin]
  exact forward_run_eq base hn x y hx s m hin

theorem acceptedSwap_pool (q : Wire) (hq : q∈skywalkPoolWires base) :
    acceptedSwap q∈skywalkPoolWires base := by
  have sw (a b : Nat) (ha : a<1798) (hb : b<1798) (v : Wire)
      (hv : v∈skywalkPoolWires base) : Equiv.swap (base a) (base b) v∈skywalkPoolWires base := by
    by_cases va : v=base a
    · subst v
      simpa only [Equiv.swap_apply_left] using DirectSkywalk.arith_mem base 0 1798 b (by omega) hb
    by_cases vb : v=base b
    · subst v
      simpa only [Equiv.swap_apply_right] using DirectSkywalk.arith_mem base 0 1798 a (by omega) ha
    simpa only [Equiv.swap_apply_of_ne_of_ne va vb] using hv
  exact sw 1542 720 (by omega) (by omega) _
    (sw 1541 719 (by omega) (by omega) _ (sw 1026 718 (by omega) (by omega) q hq))

theorem hosted_inverse_run_eq (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx : x<p) (initial field : State) (mF mI : List Bool)
    (hin : SkywalkArithmeticInput base x y initial.basis)
    (hphase : field.phase=(run (hosted (NativeFirstDirect.forward base)) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires base,
      field.basis q=(run (hosted (NativeFirstDirect.forward base)) mF initial).basis q) :
    run (hosted (inverse base)) mI field=run (hosted (NativeFirstKnown.inverse base)) mI field := by
  have f := hosted_run (NativeFirstDirect.forward base) mF initial
  rw [accepted_pull_clean x y initial hin] at f
  have phase : (pullState acceptedSwap field).phase=
      (run (NativeFirstDirect.forward base) mF initial).phase :=
    hphase.trans (by simpa only [pullState] using congrArg State.phase f)
  have pool : ∀q∈skywalkPoolWires base,(pullState acceptedSwap field).basis q=
      (run (NativeFirstDirect.forward base) mF initial).basis q := by
    intro q hq
    exact (hpool _ (acceptedSwap_pool q hq)).trans (congrArg (fun z : State => z.basis q) f)
  apply hosted_run_eq
  exact inverse_run_eq base hn x y hx initial (pullState acceptedSwap field) mF mI hin phase pool

theorem hosted_counts (P : Program) :
    toffoliCount (hosted P)=toffoliCount P ∧ measurementCount (hosted P)=measurementCount P := by
  rw [hosted_eq]
  exact renameProgram_counts _ _

theorem hosted_slots (P : Program) : Challenge.gateSlots (hosted P)=Challenge.gateSlots P := by
  rw [hosted_eq]
  exact Baselines.rename_gateSlots _ _

theorem hosted_physical (P : Program) (hp : GatePhysical P) : GatePhysical (hosted P) := by
  rw [hosted_eq]
  exact gatePhysical_rename _ acceptedSwap.injective _ hp

theorem hosted_support (P : Program) : wires (hosted P)=(wires P).image acceptedSwap := by
  rw [hosted_eq]
  exact renameProgram_support _ _

theorem hosted_work_free (P : Program) (h : base 1797∉wires P) : base 1797∉wires (hosted P) := by
  intro used
  rw [hosted_support] at used
  obtain ⟨q,hq,e⟩ := Finset.mem_image.mp used
  exact h ((acceptedSwap.injective (e.trans acceptedSwap_work.symm)) ▸ hq)

theorem hosted_avoids_work :
    base 1797∉wires (hosted (forward base)) ∧ base 1797∉wires (hosted (inverse base)) :=
  ⟨hosted_work_free _ (avoids_work base base_pool_nodup).1,
    hosted_work_free _ (avoids_work base base_pool_nodup).2⟩


theorem caller_first_stageW (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput w x y s.basis) :
    W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 1
      (run (forward w) m s).basis :=
  (W.compactSkywalkStage_one w _ _).mpr (caller_first_stage w hn x y hx0 hx s m hin)

theorem inverse_roundtrip (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx : x<p) (s : State) (mF mI : List Bool)
    (hin : SkywalkArithmeticInput w x y s.basis) :
    run (inverse w) mI (run (forward w) mF s)=s := by
  rw [forward_run_eq w hn x y hx s mF hin]
  rw [inverse_run_eq w hn x y hx s _ mF mI hin rfl (fun _ _ => rfl)]
  exact NativeFirstKnown.inverse_roundtrip w (skywalkShared_integer_nodup w hn) x s mF mI
    (NativeFirstDirect.caller_ready w hn x y s.basis hin).1

theorem native_pool (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    wires (forward w)⊆(skywalkPoolWires w).toFinset ∧
    wires (inverse w)⊆(skywalkPoolWires w).toFinset := by
  have bound : sites w⊆(skywalkPoolWires w).toFinset := by
    intro q hq
    have h := (Finset.mem_erase.mp hq).2
    rcases Finset.mem_insert.mp h with rfl|h
    · exact List.mem_toFinset.mpr (DirectSkywalk.arith_mem w 0 1798 511 (by omega) (by omega))
    · exact List.mem_toFinset.mpr (NativeFirstDirect.prefix_pool_subset w (List.mem_toFinset.mp h))
  exact ⟨(support w hn).1.trans bound,(support w hn).2.trans bound⟩

theorem hosted_pool (P : Program) (hp : wires P⊆(skywalkPoolWires base).toFinset) :
    wires (hosted P)⊆(skywalkPoolWires base).toFinset := by
  rw [hosted_support]
  intro q hq
  obtain ⟨old,h,rfl⟩ := Finset.mem_image.mp hq
  exact List.mem_toFinset.mpr (acceptedSwap_pool old (List.mem_toFinset.mp (hp h)))

theorem hosted_inverse_roundtrip (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx : x<p) (s : State) (mF mI : List Bool)
    (hin : SkywalkArithmeticInput base x y s.basis) :
    run (hosted (inverse base)) mI (run (hosted (forward base)) mF s)=s := by
  apply pullState_perm_injective acceptedSwap
  rw [hosted_run,hosted_run,accepted_pull_clean x y s hin]
  exact inverse_roundtrip base hn x y hx s mF mI hin

theorem hosted_inverse_restore_after_outside (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx : x<p) (initial field : State) (mF mI : List Bool)
    (hin : SkywalkArithmeticInput base x y initial.basis)
    (hphase : field.phase=(run (hosted (forward base)) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires base,
      field.basis q=(run (hosted (forward base)) mF initial).basis q) :
    (run (hosted (inverse base)) mI field).phase=initial.phase ∧
    (∀q∈skywalkPoolWires base,(run (hosted (inverse base)) mI field).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires base →
      (run (hosted (inverse base)) mI field).basis q=field.basis q) := by
  have sub := hosted_pool _ (native_pool base base_pool_nodup).2
  have restore := hosted_inverse_roundtrip hn x y hx initial mF mI hin
  have agree := pool_run_agrees (hosted (inverse base)) (skywalkPoolWires base).toFinset sub mI
    field (run (hosted (forward base)) mF initial) hphase
    (fun q hq => hpool q (List.mem_toFinset.mp hq))
  rw [restore] at agree
  exact ⟨agree.1,fun q hq => agree.2 q (List.mem_toFinset.mpr hq),
    fun q hq => run_preserves_outside _ mI field q
      (fun h => hq (List.mem_toFinset.mp (sub h)))⟩

theorem acceptedSwap_native (q : Wire) :
    acceptedSwap (Equiv.swap (base 1797) (base 511) q)=
      Equiv.swap (base 1797) (base 511) (acceptedSwap q) := by
  by_cases a : q=base 1797
  · subst q; simp only [Equiv.swap_apply_left,acceptedSwap_host,acceptedSwap_work]
  by_cases b : q=base 511
  · subst q; simp only [Equiv.swap_apply_right,acceptedSwap_host,acceptedSwap_work]
  have a' : acceptedSwap q≠base 1797 := fun e =>
    a (acceptedSwap.injective (e.trans acceptedSwap_work.symm))
  have b' : acceptedSwap q≠base 511 := fun e =>
    b (acceptedSwap.injective (e.trans acceptedSwap_host.symm))
  rw [Equiv.swap_apply_of_ne_of_ne a b,Equiv.swap_apply_of_ne_of_ne a' b']

theorem hosted_transport (P : Program) :
    hosted (Transport.program (base 1797) (base 511) P)=
      Transport.program (base 1797) (base 511) (hosted P) := by
  simp only [hosted_eq,Transport.program,renameProgram_comp]
  apply congrArg (fun f => renameProgram f P)
  funext q
  exact acceptedSwap_native q

theorem integer_work_free : base 1797∉OB5.integerSites := by
  intro used
  obtain ⟨i,e,hi⟩ := (OB5.integerSites_mem _).mp used
  have eq := base_injective e
  omega

theorem stack_work_free : base 1797∉wires stackForwardT ∧ base 1797∉wires stackReverseT :=
  ⟨fun h => integer_work_free ((StackOB5.support_gen 1 511 (by omega) (by omega)).1 _
    (stackForwardT_subset h)),
    fun h => integer_work_free ((StackOB5.support_gen 1 511 (by omega) (by omega)).2 _
    (stackReverseT_subset h))⟩

theorem clear_work_free : base 1797∉wires (skywalkArithmeticClear base) := by
  simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]

def workSites : Finset Wire := [base 1026,base 1541,base 1542].toFinset

def hostSites : Finset Wire := [base 718,base 719,base 720].toFinset

theorem pull_clean_sites (s : State)
    (clean : ∀q∈workSites∪hostSites,s.basis q=false) : pullState acceptedSwap s=s := by
  have a := Q5Global718.pull_clean s (clean _ (by simp [workSites,hostSites]))
    (clean _ (by simp [workSites,hostSites]))
  have b := Q6IntegerHost.pull_clean s (clean _ (by simp [workSites,hostSites]))
    (clean _ (by simp [workSites,hostSites]))
  have c := Q7IntegerHost.pull_clean s (clean _ (by simp [workSites,hostSites]))
    (clean _ (by simp [workSites,hostSites]))
  change pullState Q5Global718.swap
    (pullState Q6IntegerHost.swap (pullState Q7IntegerHost.swap s))=s
  rw [c,b,a]

theorem caller_clean_sites (x y : Nat) (s : State)
    (hin : SkywalkArithmeticInput base x y s.basis) :
    ∀q∈workSites∪hostSites,s.basis q=false := by
  intro q hq
  simp only [workSites,hostSites,Finset.mem_union,List.mem_toFinset,List.mem_cons,
    List.not_mem_nil,or_false] at hq
  rcases hq with (rfl|rfl|rfl)|(rfl|rfl|rfl)
  · exact Q5Global718.input_clean x y 1026 s hin (Or.inr rfl)
  · exact Q6IntegerHost.input_clean x y 1541 s hin (Or.inr rfl)
  · exact Q7IntegerHost.input_clean x y 1542 s hin (Or.inr rfl)
  · exact Q5Global718.input_clean x y 718 s hin (Or.inl rfl)
  · exact Q6IntegerHost.input_clean x y 719 s hin (Or.inl rfl)
  · exact Q7IntegerHost.input_clean x y 720 s hin (Or.inl rfl)

theorem caller_clean_sites_paired (x y : Nat) (a b : State)
    (hin : SkywalkArithmeticInput base x y a.basis) (same : Q5FusionPhase.Paired a b) :
    ∀q∈workSites∪hostSites,b.basis q=false := by
  intro q hq
  apply Eq.trans (same q ?_) (caller_clean_sites x y a hin q hq)
  simp only [workSites,hostSites,Finset.mem_union,List.mem_toFinset,List.mem_cons,
    List.not_mem_nil,or_false] at hq
  rcases hq with (rfl|rfl|rfl)|(rfl|rfl|rfl) <;>
    exact OwnPlusHost.not_block _ 2056 256 (by omega)

theorem hosted_run_eq_of_clean (P : Program) (s : State) (m : List Bool)
    (before : ∀q∈workSites∪hostSites,s.basis q=false)
    (after : ∀q∈workSites∪hostSites,(run P m s).basis q=false) :
    run (hosted P) m s=run P m s := by
  apply pullState_perm_injective acceptedSwap
  rw [hosted_run,pull_clean_sites s before,pull_clean_sites _ after]

theorem hosted_three_states_eq (First F Last : Program) (s : State) (mp mf mr : List Bool)
    (input : ∀q∈workSites∪hostSites,s.basis q=false)
    (first_free : ∀q∈hostSites,q∉wires First)
    (first_clean : ∀q∈workSites,(run First mp s).basis q=false)
    (field_free : ∀q∈workSites,q∉wires F)
    (last_free : ∀q∈hostSites,q∉wires Last)
    (output : ∀q∈workSites∪hostSites,
      (run Last mr (run F mf (run First mp s))).basis q=false) :
    run (hosted Last) mr (run F mf (run (hosted First) mp s))=
      run Last mr (run F mf (run First mp s)) := by
  have first : run (hosted First) mp s=run First mp s := by
    apply hosted_run_eq_of_clean First s mp input
    intro q hq
    rcases Finset.mem_union.mp hq with hq|hq
    · exact first_clean q hq
    · exact (run_preserves_outside _ mp s q (first_free q hq)).trans
        (input q (Finset.mem_union_right _ hq))
  rw [first]
  apply hosted_run_eq_of_clean Last _ mr ?_ output
  intro q hq
  rcases Finset.mem_union.mp hq with hq|hq
  · exact (run_preserves_outside F mf _ q (field_free q hq)).trans (first_clean q hq)
  · exact (run_preserves_outside Last mr _ q (last_free q hq)).symm.trans
      (output q (Finset.mem_union_right _ hq))

def kernel (First F Last : Program) : Program := First++(F++Last)

def relocated (First F Last : Program) : Program := hosted First++(F++hosted Last)

theorem hosted_kernel_run_eq (First F Last : Program) (s : State) (m : List Bool)
    (input : ∀q∈workSites∪hostSites,s.basis q=false)
    (first_free : ∀q∈hostSites,q∉wires First)
    (first_clean : ∀q∈workSites,
      (run First (m.take (measurementCount First)) s).basis q=false)
    (field_free : ∀q∈workSites,q∉wires F)
    (last_free : ∀q∈hostSites,q∉wires Last)
    (output : ∀q∈workSites∪hostSites,(run (kernel First F Last) m s).basis q=false) :
    run (relocated First F Last) m s=run (kernel First F Last) m s := by
  have eq := hosted_three_states_eq First F Last s (m.take (measurementCount First))
    ((m.drop (measurementCount First)).take (measurementCount F))
    ((m.drop (measurementCount First)).drop (measurementCount F)) input first_free first_clean
    field_free last_free (by simpa only [kernel,run_append] using output)
  simpa only [kernel,relocated,run_append,(hosted_counts First).2] using eq

theorem wireFn2_work (L : ControlledPointLayout) : wireFn2 L (base 1797)=L.core.poolWire 769 := by
  rw [wireFn2,show swap2 (base 1797)=base 769 by simp [swap2,base],pointWireFn_base]
  rfl

theorem wireFn2_host (L : ControlledPointLayout) : wireFn2 L (base 511)=L.core.poolWire 511 := by
  rw [wireFn2,swap2_fix _ (by decide) (by decide),pointWireFn_base]
  rfl


theorem native_support_logical :
    wires (forward base)⊆OB5Support.logicalSites ∧ wires (inverse base)⊆OB5Support.logicalSites := by
  have host : base 511∈OB5Support.logicalSites := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨511,?_,rfl⟩
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have bound : sites base⊆OB5Support.logicalSites := by
    intro q hq
    rcases Finset.mem_insert.mp (Finset.mem_erase.mp hq).2 with rfl|hq
    · exact host
    · exact OB5Support.prefixSites_sub_logical hq
  exact ⟨(support base base_pool_nodup).1.trans bound,(support base base_pool_nodup).2.trans bound⟩

theorem hosted_support_logical (P : Program) (hp : wires P⊆OB5Support.logicalSites) :
    wires (hosted P)⊆OB5Support.logicalSites :=
  OneFlagEntryGeometryQ7.rename_support _
    (Q6FusionGeometry.rename_support _ (OwnQ5Integer.rename_support _ hp))

theorem placed_work_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (hp : wires P⊆OB5Support.logicalSites) (free : base 1797∉wires P) :
    L.core.poolWire 769∉wires (renameProgram (wireFn2 L) P) := by
  intro used
  rw [renameProgram_support] at used
  obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp used
  have same := (placement2 L hw hn).injectiveOnSlots q (ArithmeticOB5.logical_sub_old (hp hq))
    (base 1797) m1797 (eq.trans (wireFn2_work L).symm)
  exact free (same ▸ hq)

theorem placed_native_work_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 769∉wires (renameProgram (wireFn2 L) (hosted (forward base))) ∧
    L.core.poolWire 769∉wires (renameProgram (wireFn2 L) (hosted (inverse base))) :=
  ⟨placed_work_free L hw hn _ (hosted_support_logical _ native_support_logical.1)
      hosted_avoids_work.1,
    placed_work_free L hw hn _ (hosted_support_logical _ native_support_logical.2)
      hosted_avoids_work.2⟩

theorem placed_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (hp : wires P⊆OB5Support.logicalSites) (phys : GatePhysical P) :
    GatePhysical (renameProgram (wireFn2 L) P) :=
  gatePhysical_rename_support (wireFn2 L) P
    (fun a ha b hb eq => (placement2 L hw hn).injectiveOnSlots
      a (ArithmeticOB5.logical_sub_old (hp ha)) b (ArithmeticOB5.logical_sub_old (hp hb)) eq) phys

theorem relocated_counts (First F Last : Program) :
    toffoliCount (relocated First F Last)=toffoliCount (kernel First F Last) ∧
    measurementCount (relocated First F Last)=measurementCount (kernel First F Last) := by
  simp only [relocated,kernel,toffoliCount_append,measurementCount_append,
    (hosted_counts First).1,(hosted_counts First).2,(hosted_counts Last).1,(hosted_counts Last).2]
  trivial

theorem relocated_slots (First F Last : Program) :
    Challenge.gateSlots (relocated First F Last)=Challenge.gateSlots (kernel First F Last) := by
  simp only [relocated,kernel,Challenge.gateSlots_append,hosted_slots]

theorem relocated_physical (First F Last : Program) (hp : GatePhysical (kernel First F Last)) :
    GatePhysical (relocated First F Last) := by
  simp only [kernel,gatePhysical_append] at hp
  simp only [relocated,gatePhysical_append]
  exact ⟨hosted_physical _ hp.1,hp.2.1,hosted_physical _ hp.2.2⟩

end ECDSAAdd.Entrant.FrontierEntry1591Native

#print axioms ECDSAAdd.Entrant.FrontierEntry1591Native.forward_run_eq
#print axioms ECDSAAdd.Entrant.FrontierEntry1591Native.inverse_run_eq
#print axioms ECDSAAdd.Entrant.FrontierEntry1591Native.hosted_inverse_restore_after_outside
#print axioms ECDSAAdd.Entrant.FrontierEntry1591Native.hosted_kernel_run_eq
#print axioms ECDSAAdd.Entrant.FrontierEntry1591Native.placed_native_work_free
