import ECDSAAdd.Math.SkywalkTerminalLastControls
import ECDSAAdd.Submission.Entrant.MainPre
import ECDSAAdd.Submission.Entrant.OneFlag


-- Public component FrontierEntry1591Native.lean
section
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

end

-- Public component ParityCodec5NewBase.lean
section
/-! A legal fifth-trit permutation makes the raw sign parity an affine payload bit. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ParityCodec5New
open Arithmetic Challenge RecordedQuantum Baselines
open MeasuredCodec5 (bitsOf legal local_word bitRun legalNat safe run_sim sim_safe)

def twist : Program := [.X 9,.CX 8 9]
def untwist : Program := [.CX 8 9,.X 9]
def encode : Program := twist ++ MeasuredCodec5.encode
def decode : Program := MeasuredCodec5.decode ++ untwist
abbrev legalAt := MeasuredCodec5.legalAt

def rawParity (s : BasisState) : Bool := s 1 ^^ s 3 ^^ s 5 ^^ s 7 ^^ s 9
def payloadParity (s : BasisState) : Bool :=
  s 0 ^^ s 1 ^^ s 2 ^^ s 3 ^^ s 4 ^^ s 6 ^^ s 7 ^^ s 8

theorem twist_phase (s : State) (m : List Bool) : (run twist m s).phase=s.phase := rfl

theorem twist_basis (s : State) (m : List Bool) :
    (run twist m s).basis=writeBit s.basis 9 (!s.basis 9 ^^ s.basis 8) := by
  simp [twist,run,writeBit,Function.update]

theorem twist_roundtrip (s : State) (m n : List Bool) :
    run untwist n (run twist m s)=s := by
  cases s with
  | mk ph b =>
    apply State.extensionality
    · rfl
    · funext q
      by_cases hq:q=9
      · subst q; simp [twist,untwist,run,writeBit,Function.update]
      · simp [twist,untwist,run,writeBit,Function.update,hq]

theorem twist_legal (s : State) (m : List Bool) (h : legal s.basis) :
    legal (run twist m s).basis := by
  intro i hi
  rw [twist_basis]
  interval_cases i
  · simpa [MeasuredCodec5.pair,writeBit,Function.update] using h 0 (by decide)
  · simpa [MeasuredCodec5.pair,writeBit,Function.update] using h 1 (by decide)
  · simpa [MeasuredCodec5.pair,writeBit,Function.update] using h 2 (by decide)
  · simpa [MeasuredCodec5.pair,writeBit,Function.update] using h 3 (by decide)
  · have hh:=h 4 (by decide)
    cases a:s.basis 8 <;> cases b:s.basis 9 <;>
      simp_all [MeasuredCodec5.pair,writeBit,Function.update]

theorem encode_correct (s : State) (m : List Bool) (h : legal s.basis) :
    (run encode m s).phase=s.phase ∧ (run encode m s).basis 5=false ∧
    (run encode m s).basis 9=false := by
  have hh:=MeasuredCodec5.encode_correct (run twist [] s) m (twist_legal s [] h)
  simpa only [encode,run_append,show measurementCount twist=0 from rfl,
    List.take_zero,List.drop_zero,twist_phase] using hh

theorem roundtrip (s : State) (mE mD : List Bool) (h : legal s.basis) :
    run decode mD (run encode mE s)=s := by
  simp only [encode,decode,run_append,show measurementCount twist=0 from rfl,
    List.take_zero,List.drop_zero]
  rw [MeasuredCodec5.roundtrip _ _ _ (twist_legal s [] h),twist_roundtrip]

theorem encode_independent (s : State) (m n : List Bool) (h : legal s.basis) :
    run encode m s=run encode n s := by
  apply State.extensionality
  · exact (encode_correct s m h).1.trans (encode_correct s n h).1.symm
  · exact run_basis_records _ s s m n rfl

theorem support_exact : wires encode=Finset.range 10 ∧ wires decode=Finset.range 10 := by
  simp only [encode,decode,wires_append,MeasuredCodec5.support_exact.1,MeasuredCodec5.support_exact.2]
  decide

theorem support : wires encode⊆Finset.range 10 ∧ wires decode⊆Finset.range 10 := by
  rw [support_exact.1,support_exact.2]
  exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩

theorem counts : toffoliCount encode=9 ∧ measurementCount encode=4 ∧
    toffoliCount decode=11 ∧ measurementCount decode=2 := by
  simp only [encode,decode,toffoliCount_append,measurementCount_append]
  simpa [twist,untwist,toffoliCount,measurementCount] using MeasuredCodec5.counts

theorem slots : gateSlots encode=144 ∧ gateSlots decode=142 := by
  rw [encode,decode,gateSlots_append,gateSlots_append,MeasuredCodec5.slots.1,MeasuredCodec5.slots.2]
  decide

theorem physical : GatePhysical encode ∧ GatePhysical decode := by
  have ht:GatePhysical twist := by simp [GatePhysical,twist,PhysicalInstr,ProperGate]
  have hu:GatePhysical untwist := by simp [GatePhysical,untwist,PhysicalInstr,ProperGate]
  exact ⟨(gatePhysical_append _ _).mpr ⟨ht,MeasuredCodec5.physical.1⟩,
    (gatePhysical_append _ _).mpr ⟨MeasuredCodec5.physical.2,hu⟩⟩

theorem finite_parity : ∀ x<1024, legalNat x=true →
    rawParity (bitsOf x)=payloadParity (bitsOf (bitRun encode x)) := by
  decide +kernel

theorem encode_parity (s : State) (m : List Bool) (h : legal s.basis) :
    rawParity s.basis=payloadParity (run encode m s).basis := by
  obtain ⟨x,hx,lx,hb⟩:=local_word s h
  have hh:=pool_run_agrees encode (Finset.range 10) support.1 m s ⟨s.phase,bitsOf x⟩ rfl hb
  have modeled:=run_sim encode m s.phase x
  have hs:safe encode x=true := by
    change safe MeasuredCodec5.encode (MeasuredCodec5.bitStep (.CX 8 9)
      (MeasuredCodec5.bitStep (.X 9) x))=true
    have old:=MeasuredCodec5.finite_encode
    have legalTwist:∀x<1024,legalNat x=true →
        MeasuredCodec5.bitStep (.CX 8 9) (MeasuredCodec5.bitStep (.X 9) x)<1024 ∧
        legalNat (MeasuredCodec5.bitStep (.CX 8 9) (MeasuredCodec5.bitStep (.X 9) x))=true := by decide +kernel
    exact (old _ (legalTwist x hx lx).1 (legalTwist x hx lx).2).1
  rw [sim_safe encode x hs] at modeled
  have out (q : Nat) (hq:q<10) : (run encode m s).basis q=(bitsOf (bitRun encode x)) q :=
    (hh.2 q (Finset.mem_range.mpr hq)).trans (congrArg (fun t:State=>t.basis q) modeled)
  have rawEq:rawParity s.basis=rawParity (bitsOf x) := by
    simp only [rawParity,hb 1 (by decide),hb 3 (by decide),hb 5 (by decide),hb 7 (by decide),hb 9 (by decide)]
  rw [rawEq,finite_parity x hx lx]
  simp only [payloadParity,out 0 (by decide),out 1 (by decide),out 2 (by decide),out 3 (by decide),
    out 4 (by decide),out 6 (by decide),out 7 (by decide),out 8 (by decide)]

/-- Only the ten declared local ports are mapped. -/
abbrev label := MeasuredCodec5.label

def encodeAt (f : Fin 10→Wire) : Program := renameProgram (label f) encode
def decodeAt (f : Fin 10→Wire) : Program := renameProgram (label f) decode

private theorem label_inj (f : Fin 10→Wire) (hf : Function.Injective f) :
    ∀a∈Finset.range 10,∀b∈Finset.range 10,label f a=label f b → a=b := by
  intro a ha b hb e
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have eq : f ⟨a,ha'⟩=f ⟨b,hb'⟩ := by simpa only [label,MeasuredCodec5.label,dif_pos ha',dif_pos hb'] using e
  exact congrArg Fin.val (hf eq)

private theorem label_image (f : Fin 10→Wire) :
    (Finset.range 10).image (label f)=Finset.univ.image f := by
  ext q
  simp only [Finset.mem_image,Finset.mem_range,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,e⟩
    exact ⟨⟨i,hi⟩,by simpa only [label,MeasuredCodec5.label,dif_pos hi] using e⟩
  · rintro ⟨i,e⟩
    exact ⟨i.val,i.isLt,by simpa only [label,MeasuredCodec5.label,dif_pos i.isLt] using e⟩

theorem supportAt_exact (f : Fin 10→Wire) :
    wires (encodeAt f)=Finset.univ.image f ∧ wires (decodeAt f)=Finset.univ.image f := by
  simp only [encodeAt,decodeAt,renameProgram_support,support_exact.1,support_exact.2,label_image]
  exact ⟨trivial,trivial⟩

theorem supportAt (f : Fin 10→Wire) :
    wires (encodeAt f)⊆Finset.univ.image f ∧ wires (decodeAt f)⊆Finset.univ.image f := by
  rw [(supportAt_exact f).1,(supportAt_exact f).2]
  exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩

theorem site_mem (f : Fin 10→Wire) (i : Fin 10) : f i∈wires (encodeAt f) := by
  rw [(supportAt_exact f).1]
  exact Finset.mem_image_of_mem f (Finset.mem_univ i)

theorem countsAt (f : Fin 10→Wire) : toffoliCount (encodeAt f)=9 ∧ measurementCount (encodeAt f)=4 ∧
    toffoliCount (decodeAt f)=11 ∧ measurementCount (decodeAt f)=2 := by
  simpa only [encodeAt,decodeAt,(renameProgram_counts (label f) encode).1,
    (renameProgram_counts (label f) encode).2,(renameProgram_counts (label f) decode).1,
    (renameProgram_counts (label f) decode).2] using counts

theorem slotsAt (f : Fin 10→Wire) : gateSlots (encodeAt f)=144 ∧ gateSlots (decodeAt f)=142 := by
  simpa only [encodeAt,decodeAt,rename_gateSlots] using slots

theorem physicalAt (f : Fin 10→Wire) (hf : Function.Injective f) :
    GatePhysical (encodeAt f) ∧ GatePhysical (decodeAt f) := by
  exact ⟨gatePhysical_rename_support _ _
    (fun a ha b hb e => label_inj f hf a (support.1 ha) b (support.1 hb) e) physical.1,
    gatePhysical_rename_support _ _
    (fun a ha b hb e => label_inj f hf a (support.2 ha) b (support.2 hb) e) physical.2⟩

theorem encodeAt_correct (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legalAt f s.basis) :
    (run (encodeAt f) m s).phase=s.phase ∧
    (run (encodeAt f) m s).basis (f 5)=false ∧ (run (encodeAt f) m s).basis (f 9)=false := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have localResult := encode_correct t m h
  have placed := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 m t s rfl (fun _ _ => rfl)
  refine ⟨placed.1.trans localResult.1,?_,?_⟩
  · have e := (placed.2 5 (by decide)).trans localResult.2.1
    simpa only [label,MeasuredCodec5.label,dif_pos (show 5<10 by decide)] using e
  · have e := (placed.2 9 (by decide)).trans localResult.2.2
    simpa only [label,MeasuredCodec5.label,dif_pos (show 9<10 by decide)] using e

theorem legalAt_iff (f : Fin 10→Wire) (s : BasisState) : legalAt f s ↔
    ∀i : Fin 5,(s (f ⟨2*i.val,by omega⟩) && s (f ⟨2*i.val+1,by omega⟩))=false :=
  MeasuredCodec5.legalAt_iff f s

theorem encodeAt_phase (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legalAt f s.basis) : (run (encodeAt f) m s).phase=s.phase :=
  (encodeAt_correct f hf s m h).1

theorem encodeAt_independent (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m n : List Bool) (h : legalAt f s.basis) :
    run (encodeAt f) m s=run (encodeAt f) n s := by
  apply State.extensionality
  · exact (encodeAt_phase f hf s m h).trans (encodeAt_phase f hf s n h).symm
  · exact run_basis_records _ s s m n rfl

theorem roundtripAt (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (mE mD : List Bool) (h : legalAt f s.basis) :
    run (decodeAt f) mD (run (encodeAt f) mE s)=s := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have pe := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 mE t s rfl (fun _ _ => rfl)
  have pd := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) decode
    support.2 mD (run encode mE t) (run (encodeAt f) mE s) pe.1.symm
    (fun q hq => (pe.2 q hq).symm)
  have inv := roundtrip t mE mD h
  apply State.extensionality
  · have hp := congrArg State.phase inv
    exact pd.1.trans hp
  · funext q
    by_cases hq : q∈Finset.univ.image f
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
      have eq := (pd.2 i.val (Finset.mem_range.mpr i.isLt)).trans
        (congrArg (fun st : State => st.basis i.val) inv)
      simpa only [t,label,MeasuredCodec5.label,dif_pos i.isLt] using eq
    · exact (run_preserves_outside (decodeAt f) mD (run (encodeAt f) mE s) q
        (fun used => hq ((supportAt f).2 used))).trans
        (run_preserves_outside (encodeAt f) mE s q (fun used => hq ((supportAt f).1 used)))

theorem encodeAt_zero_phase (f : Fin 10→Wire) (hf : Function.Injective f) (s : State) :
    (run (encodeAt f) [] s).phase=s.phase := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have placed := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 [] t s rfl (fun _ _ => rfl)
  exact placed.1.trans (MeasuredCodec5.zero_phase encode (by decide) t)

theorem mapped_support_eq (f : Fin 10→Wire) :
    wires (encodeAt f)=wires (MeasuredCodec5.encodeAt f) ∧
    wires (decodeAt f)=wires (MeasuredCodec5.decodeAt f) := by
  rw [(supportAt_exact f).1,(supportAt_exact f).2,
    (MeasuredCodec5.supportAt_exact f).1,(MeasuredCodec5.supportAt_exact f).2]
  exact ⟨rfl,rfl⟩

theorem encodeAt_parity (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legalAt f s.basis) :
    (s.basis (f 1) ^^ s.basis (f 3) ^^ s.basis (f 5) ^^ s.basis (f 7) ^^ s.basis (f 9))=
    ((run (encodeAt f) m s).basis (f 0) ^^ (run (encodeAt f) m s).basis (f 1) ^^
      (run (encodeAt f) m s).basis (f 2) ^^ (run (encodeAt f) m s).basis (f 3) ^^
      (run (encodeAt f) m s).basis (f 4) ^^ (run (encodeAt f) m s).basis (f 6) ^^
      (run (encodeAt f) m s).basis (f 7) ^^ (run (encodeAt f) m s).basis (f 8)) := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have result := encode_parity t m h
  have placed := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 m t s rfl (fun _ _ => rfl)
  have port (q : Fin 10) : (run (encodeAt f) m s).basis (f q)=(run encode m t).basis q.val := by
    simpa only [label,MeasuredCodec5.label,dif_pos q.isLt] using placed.2 q.val (Finset.mem_range.mpr q.isLt)
  simpa only [rawParity,payloadParity,t,label,dif_pos (show 0<10 by decide),
    dif_pos (show 1<10 by decide),dif_pos (show 2<10 by decide),dif_pos (show 3<10 by decide),
    dif_pos (show 4<10 by decide),dif_pos (show 5<10 by decide),dif_pos (show 6<10 by decide),
    dif_pos (show 7<10 by decide),dif_pos (show 8<10 by decide),dif_pos (show 9<10 by decide),
    port 0,port 1,port 2,port 3,port 4,port 6,port 7,port 8] using result

end ECDSAAdd.Entrant.ParityCodec5New

end

-- Public component TraceParity5.lean
section
/-! The actual signed-rail swap flags telescope, including terminal zero. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TraceParity5
open SkywalkRails SkywalkTrace Secp256k1

def smallSign (r : SkywalkRails.State) : Bool :=
  if r.g then neg r.a else neg r.b

def parity : List Bool → Bool
  | [] => false
  | b::bs => b ^^ parity bs

def swapParity (cs : List (Bool×Bool)) : Bool := parity (cs.map Prod.snd)

theorem smallSign_encode (g s : Bool) (u v : Int) :
    smallSign (encode g s u v)=neg (signed s u) := by
  cases g <;> rfl

theorem smallSign_zero (g s : Bool) (v : Int) :
    smallSign (encode g s 0 v)=false := by
  rw [smallSign_encode,zero_sign]
  rfl

theorem step_swap (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    (code (encode g s (z.u : Int) (z.v : Int))).2=
      (smallSign (encode g s (z.u : Int) (z.v : Int)) ^^
        smallSign (next (encode g s (z.u : Int) (z.v : Int)))) := by
  have hui : (0:Int)≤z.u := by omega
  have hvi : (0:Int)<z.v := by omega
  have hvoi : (z.v : Int)%2=1 := by omega
  by_cases he : z.u%2=0
  · have hei : (z.u : Int)%2=0 := by omega
    have hhalf : signed s ((z.u : Int)/2)=(signed s (z.u : Int))/2 := by
      cases s <;> simp only [signed,Bool.false_eq_true,if_false,if_true]
      omega
    have hsign : neg (signed s ((z.u : Int)/2))=neg (signed s (z.u : Int)) := by
      rw [hhalf]
      apply neg_half
      cases s <;> simp only [signed,Bool.false_eq_true,if_false,if_true] <;> omega
    simp only [code,next]
    rw [step_encode_even g s _ _ hui hvi hvoi hei,smallSign_encode]
    simp only [smallSign,railsOf,if_true]
    rw [hsign,Bool.xor_self]
  · have hei : (z.u : Int)%2≠0 := by omega
    have hlarge : ((z.u : Int)+(z.v : Int))%2=0 := by omega
    have hneg : (-(z.u : Int))%2≠0 := by omega
    have source :
        (route (encode g s (z.u : Int) (z.v : Int)).a
          (encode g s (z.u : Int) (z.v : Int)).b).2=signed s (z.u : Int) := by
      cases g <;> cases s <;> simp [encode,signed,route,odd,hei,hlarge,hneg]
    have hg : (SkywalkRails.step (encode g s (z.u : Int) (z.v : Int))).g=false := by
      have h := (code_classified g s z hv hvo).1
      simpa [code,he] using h
    change (neg (route (encode g s (z.u : Int) (z.v : Int)).a
      (encode g s (z.u : Int) (z.v : Int)).b).2 ^^
      neg (SkywalkRails.step (encode g s (z.u : Int) (z.v : Int))).k)=_
    rw [source,smallSign_encode]
    simp only [next,smallSign,railsOf,hg,Bool.false_eq_true,if_false]

theorem trace_telescope (n : Nat) (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    swapParity (trace n (encode g s (z.u : Int) (z.v : Int)))=
      (smallSign (encode g s (z.u : Int) (z.v : Int)) ^^
        smallSign (next^[n] (encode g s (z.u : Int) (z.v : Int)))) := by
  induction n generalizing g s z with
  | zero => simp [trace,swapParity,parity]
  | succ n ih =>
    let r := encode g s (z.u : Int) (z.v : Int)
    let t := SkywalkRails.step r
    have enc := step_reencode g s z hv hvo
    change next r=encode t.g (smallerSign t) ((SkywalkNat.step z).u : Int)
      ((SkywalkNat.step z).v : Int) at enc
    have valid := SkywalkNat.step_v_odd_pos z hv hvo
    have tail := ih t.g (smallerSign t) (SkywalkNat.step z) valid.1 valid.2
    rw [←enc] at tail
    change ((code r).2 ^^ swapParity (trace n (next r)))=_
    rw [tail,step_swap g s z hv hvo,Function.iterate_succ_apply]
    simp [r,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

theorem trace512_parity (x : Nat) (hx0 : 0<x) (hx : x<p) :
    swapParity (trace 512 (encode false false (x : Int) (p : Int)))=false := by
  have hp0 : 0<p := p_prime.pos
  have hpodd : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have hc : x.Coprime p := by
    apply Nat.Coprime.symm
    apply p_prime.coprime_iff_not_dvd.mpr
    intro hd
    exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)
  have terminal := SkywalkNat.terminates_2n p x 256 hp0 hx0 hpodd hp (hx.trans hp) hc
  obtain ⟨G,S,enc⟩ := iter_encoded 512 false false (SkywalkNat.init x p) hp0 hpodd
  change next^[512] (encode false false (x : Int) (p : Int))=
    encode G S ((SkywalkNat.step^[512] (SkywalkNat.init x p)).u : Int)
      ((SkywalkNat.step^[512] (SkywalkNat.init x p)).v : Int) at enc
  rw [terminal.1,terminal.2] at enc
  have small : smallSign (next^[512] (encode false false (x : Int) (p : Int)))=false := by
    rw [enc]
    exact smallSign_zero G S 1
  have telesc := trace_telescope 512 false false (SkywalkNat.init x p) hp0 hpodd
  simp only [SkywalkNat.init] at telesc
  rw [small] at telesc
  simpa [smallSign_encode,signed,neg] using telesc

def xorRange : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n+1, f => f 0 ^^ xorRange n (fun i => f (i+1))

theorem parity_range (n : Nat) (f : Nat → Bool) :
    parity ((List.range n).map f)=xorRange n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,parity,xorRange]
    exact congrArg (fun b => f 0 ^^ b) (ih (fun i => f (i+1)))

theorem xorRange_congr (n : Nat) (f g : Nat → Bool)
    (h : ∀i,i<n → f i=g i) : xorRange n f=xorRange n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [xorRange]
    rw [h 0 (by omega),ih (fun i => f (i+1)) (fun i => g (i+1))
      (fun i hi => h (i+1) (by omega))]

theorem xorRange_add (n m : Nat) (f : Nat → Bool) :
    xorRange (n+m) f=(xorRange n f ^^ xorRange m (fun i => f (n+i))) := by
  induction n generalizing f with
  | zero => simp [xorRange]
  | succ n ih =>
    rw [show n+1+m=(n+m)+1 by omega]
    simp only [xorRange]
    rw [ih (fun i => f (i+1))]
    simp only [Bool.xor_assoc]
    congr 2
    apply xorRange_congr
    intro i hi
    congr 1
    omega

theorem xorRange_group (n width : Nat) (f : Nat → Bool) :
    xorRange (n*width) f=
      xorRange n (fun j => xorRange width (fun i => f (width*j+i))) := by
  induction n generalizing f with
  | zero => simp only [Nat.zero_mul,xorRange]
  | succ n ih =>
    rw [show (n+1)*width=width+n*width by
      simp only [Nat.add_mul,Nat.one_mul,Nat.add_comm],xorRange_add]
    rw [ih (fun i => f (width+i))]
    simp only [xorRange,Nat.mul_zero,Nat.zero_add]
    congr 1
    apply xorRange_congr
    intro j hj
    apply xorRange_congr
    intro i hi
    congr 1
    simp only [Nat.mul_add,Nat.mul_one]
    omega

theorem swapParity_index (cs : List (Bool×Bool)) (default : Bool×Bool) :
    xorRange cs.length (fun i => (cs.getD i default).2)=swapParity cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.length_cons,xorRange,List.getD_cons_zero,swapParity,List.map_cons,parity]
    change (c.2 ^^ xorRange cs.length (fun i => (cs.getD i default).2))=_
    rw [ih]
    rfl

def rawS (x i : Nat) : Bool :=
  ((trace 512 (encode false false (x : Int) (p : Int))).getD i (false,false)).2

theorem rawS511 (x : Nat) (hx0 : 0<x) (hx : x<p) : rawS x 511=false := by
  simp only [rawS,trace512_last x hx0 hx (false,false)]

theorem rawS512_parity (x : Nat) (hx0 : 0<x) (hx : x<p) :
    xorRange 512 (rawS x)=false := by
  have indexed := swapParity_index
    (trace 512 (encode false false (x : Int) (p : Int))) (false,false)
  rw [trace_length] at indexed
  exact indexed.trans (trace512_parity x hx0 hx)

/-- The unpacked penultimate S flag supplies the parity of the packed prefix. -/
theorem rawS510_relation (x : Nat) (hx0 : 0<x) (hx : x<p) :
    xorRange 510 (rawS x)=rawS x 510 := by
  have whole := rawS512_parity x hx0 hx
  have split := xorRange_add 510 2 (rawS x)
  have last := rawS511 x hx0 hx
  have tail : xorRange 2 (fun i => rawS x (510+i))=rawS x 510 := by
    change (rawS x 510 ^^ (rawS x 511 ^^ false))=rawS x 510
    rw [last]
    simp
  have eq : xorRange 512 (rawS x)=(xorRange 510 (rawS x) ^^ rawS x 510) := by
    rw [tail] at split
    exact split
  rw [eq] at whole
  cases h : xorRange 510 (rawS x) <;> cases k : rawS x 510 <;> simp_all

/-- The local codec supplies each of these 102 equalities. No global host
cleanliness is assumed. -/
theorem encoded_payload_parity (x : Nat) (hx0 : 0<x) (hx : x<p)
    (payload : Nat → Bool)
    (packets : ∀j,j<102 →
      xorRange 8 (fun i => payload (8*j+i))=
        xorRange 5 (fun i => rawS x (5*j+i))) :
    xorRange 816 payload=rawS x 510 := by
  rw [show 816=102*8 from rfl,xorRange_group]
  rw [xorRange_congr 102 _ _ packets]
  rw [←xorRange_group 102 5]
  exact rawS510_relation x hx0 hx

end ECDSAAdd.Entrant.TraceParity5

end

-- Public component NewEncodedFrame.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.NewHistory5
open Arithmetic Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport MappedCompressed
abbrev historyId := History5.historyId
abbrev historyMap := History5.historyMap
abbrev historyMap_injective := History5.historyMap_injective
abbrev historyId_bound := History5.historyId_bound
abbrev historyId_region := History5.historyId_region
abbrev history_active_away := History5.history_active_away
abbrev history_words_away := History5.history_words_away
abbrev frame_history_legal := History5.frame_history_legal

abbrev RawLegal := History5.RawLegal
abbrev packDue := History5.packDue
abbrev packDue_true := History5.packDue_true

def encode (w : Nat → Wire) (start : Nat) : Program := ParityCodec5New.encodeAt (historyMap w start)
def decode (w : Nat → Wire) (start : Nat) : Program := ParityCodec5New.decodeAt (historyMap w start)
def packAfter (w : Nat → Wire) (i : Nat) : Program := if packDue i then encode w (i-5) else []
def decodeBefore (w : Nat → Wire) (i : Nat) : Program := if packDue i then decode w (i-5) else []
def encodePrefix (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => encodePrefix w n++packAfter w n
def decodePrefix (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => decodeBefore w n++decodePrefix w n
def allEncode (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => allEncode w n++encode w (5*n)
def decodeRange (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => decodeRange w (i+1) n++decodeBefore w i

def CompressedCompactStage5 (w : Nat → Wire) (x p i : Nat) (bits : BasisState) : Prop :=
  ∃raw : State,
    W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i raw.basis ∧
    bits=(run (encodePrefix w i) [] raw).basis

def EncodedFieldFrame5 (w : Nat → Wire) (sign : Wire) (origin : BasisState)
    (X Y : Fp) (s : State) : Prop :=
  ∃raw : State,raw.phase=s.phase ∧
    PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
      (centerWord X) (centerWord Y) raw.basis ∧ s=run (allEncode w 102) [] raw

def EncodedCanonicalFrame5 (origin : BasisState) (X Y : Fp) (s : State) : Prop :=
  ∃raw : State,raw.phase=s.phase ∧
    PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin
      X.val Y.val raw.basis ∧ s=run (allEncode base 102) [] raw

def groupReadSites (w : Nat → Wire) (b sign eff : Wire) (start : Nat) : Finset Wire :=
  (sharedSites w sign).toFinset ∪ {b,eff} ∪ wires (encode w start)
def otherEncode (w : Nat → Wire) (j : Nat) : Nat → Program
  | 0 => []
  | n+1 => if n=j then otherEncode w j n else otherEncode w j n++encode w (5*n)

theorem encode_counts (w : Nat → Wire) (start : Nat) :
    toffoliCount (encode w start)=9 ∧ measurementCount (encode w start)=4 :=
  ⟨(ParityCodec5New.countsAt _).1,(ParityCodec5New.countsAt _).2.1⟩
theorem decode_counts (w : Nat → Wire) (start : Nat) :
    toffoliCount (decode w start)=11 ∧ measurementCount (decode w start)=2 :=
  (ParityCodec5New.countsAt _).2.2

theorem encode_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start : Nat) (hs : start+5≤512) (s : State) (m : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w start) s.basis) :
    (run (encode w start) m s).phase=s.phase :=
  ParityCodec5New.encodeAt_phase _ (historyMap_injective w hn start hs) s m legal

theorem encode_correct (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start : Nat) (hs : start+5≤512) (s : State) (m : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w start) s.basis) :
    (run (encode w start) m s).phase=s.phase ∧
      (run (encode w start) m s).basis (historyMap w start 5)=false ∧
      (run (encode w start) m s).basis (historyMap w start 9)=false :=
  ParityCodec5New.encodeAt_correct _ (historyMap_injective w hn start hs) s m legal

theorem encode_support_eq (w : Nat → Wire) (start : Nat) :
    wires (encode w start)=wires (History5.encode w start) :=
  (ParityCodec5New.mapped_support_eq _).1
theorem decode_support_eq (w : Nat → Wire) (start : Nat) :
    wires (decode w start)=wires (History5.decode w start) :=
  (ParityCodec5New.mapped_support_eq _).2

theorem history_site_mem (w : Nat → Wire) (start : Nat) (q : Fin 10) :
    historyMap w start q∈wires (encode w start) := ParityCodec5New.site_mem _ q

theorem allEncode_support_eq (w : Nat → Wire) (n : Nat) :
    wires (allEncode w n)=wires (History5.allEncode w n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [allEncode,History5.allEncode,wires_append,ih,encode_support_eq]

theorem history_gate_mem (w : Nat → Wire) (start : Nat) (p : Program)
    (hp : p=encode w start ∨ p=decode w start) (q : Wire) (hq : q∈wires p) :
    ∃i : Fin 10,q=historyMap w start i := by
  rcases hp with rfl|rfl
  · rw [encode_support_eq] at hq
    exact History5.history_gate_mem w start _ (Or.inl rfl) q hq
  · rw [decode_support_eq] at hq
    exact History5.history_gate_mem w start _ (Or.inr rfl) q hq

theorem windows_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (a b : Nat) (ha : a+5≤512) (hb : b+5≤512) (hab : a+5≤b) :
    Disjoint (wires (encode w a)) (wires (encode w b)) := by
  rw [encode_support_eq,encode_support_eq]
  exact History5.windows_disjoint w hn a b ha hb hab

theorem allEncode_history_support (w : Nat → Wire) (n : Nat) (bound : 5*n≤512) :
    wires (allEncode w n)⊆(wireBlock w 0 512++wireBlock w 1028 512).toFinset := by
  rw [allEncode_support_eq]
  exact History5.allEncode_history_support w n bound

theorem allEncode_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (outside : n≤j) (jb : 5*j+5≤512) :
    Disjoint (wires (allEncode w n)) (wires (encode w (5*j))) := by
  rw [allEncode_support_eq,encode_support_eq]
  exact History5.allEncode_disjoint w hn n j bound outside jb

theorem allEncode_zero_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (bound : 5*n≤512) (s : State) :
    (run (allEncode w n) [] s).phase=s.phase := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allEncode,run_append]
    simp only [List.take_nil,List.drop_nil]
    exact (ParityCodec5New.encodeAt_zero_phase _ (historyMap_injective w hn _ (by omega)) _).trans
      (ih (by omega))

theorem allEncode_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (bound : 5*n≤512) (s : State) (m : List Bool) (legal : RawLegal w n s.basis) :
    (run (allEncode w n) m s).phase=s.phase := by
  induction n generalizing m with
  | zero => simp only [allEncode,run]
  | succ n ih =>
    let before := run (allEncode w n) (m.take (measurementCount (allEncode w n))) s
    have dis := allEncode_disjoint w hn n n (by omega) (Nat.le_refl _) (by omega)
    have same (q : Fin 10) : before.basis (historyMap w (5*n) q)=s.basis (historyMap w (5*n) q) :=
      run_preserves_outside _ _ _ _ (fun used => Finset.disjoint_left.mp dis used (history_site_mem w (5*n) q))
    have dom : MeasuredCodec5.legalAt (historyMap w (5*n)) before.basis := by
      apply (MeasuredCodec5.legalAt_iff _ _).mpr
      intro i
      rw [same,same]
      exact (MeasuredCodec5.legalAt_iff _ _).mp (legal n (by omega)) i
    rw [allEncode,run_append]
    exact (encode_phase w hn (5*n) (by omega) before _ dom).trans
      (ih (by omega) _ (fun j hj => legal j (by omega)))

attribute [local irreducible] run wires

theorem otherEncode_outside (w : Nat → Wire) (n j : Nat) (h : n≤j) :
    otherEncode w j n=allEncode w n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [otherEncode,if_neg (by omega),ih (by omega),allEncode]

theorem otherEncode_member (w : Nat → Wire) (n j : Nat) (q : Wire)
    (h : q∈wires (otherEncode w j n)) : ∃k,k<n ∧ k≠j ∧ q∈wires (encode w (5*k)) := by
  induction n with
  | zero => simp [otherEncode,wires] at h
  | succ n ih =>
    by_cases same : n=j
    · simp only [otherEncode,if_pos same] at h
      obtain ⟨k,hk,hj,member⟩ := ih h
      exact ⟨k,by omega,hj,member⟩
    · simp only [otherEncode,if_neg same,wires_append,Finset.mem_union] at h
      rcases h with h|h
      · obtain ⟨k,hk,hj,member⟩ := ih h
        exact ⟨k,by omega,hj,member⟩
      · exact ⟨n,by omega,same,h⟩

theorem otherEncode_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) :
    Disjoint (wires (otherEncode w j n)) (wires (encode w (5*j))) := by
  apply Finset.disjoint_left.mpr
  intro q hq hc
  obtain ⟨k,hk,ne,member⟩ := otherEncode_member w n j q hq
  have sep : 5*k+5≤5*j ∨ 5*j+5≤5*k := by omega
  rcases sep with h|h
  · exact Finset.disjoint_left.mp (windows_disjoint w hn _ _ (by omega) (by omega) h) member hc
  · exact Finset.disjoint_left.mp (windows_disjoint w hn _ _ (by omega) (by omega) h) hc member

theorem allEncode_factor (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (s : State) :
    run (allEncode w n) [] s=run (otherEncode w j n) [] (run (encode w (5*j)) [] s) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    by_cases same : j=n
    · subst j
      have dis := allEncode_disjoint w hn n n (by omega) (Nat.le_refl _) (by omega)
      rw [allEncode,run_append]
      simp only [List.take_nil,List.drop_nil]
      rw [otherEncode,if_pos rfl,otherEncode_outside w n n (Nat.le_refl _)]
      exact (run_disjoint_commute (allEncode w n) (encode w (5*n)) dis [] [] s).symm
    · have prior := ih j (by omega) (by omega)
      have right : run (otherEncode w j (n+1)) [] (run (encode w (5*j)) [] s)=
          run (encode w (5*n)) [] (run (otherEncode w j n) [] (run (encode w (5*j)) [] s)) := by
        rw [otherEncode,if_neg (Ne.symm same),run_append]
        simp only [List.take_nil,List.drop_nil]
      rw [allEncode,run_append]
      simp only [List.take_nil,List.drop_nil]
      rw [prior,right]

theorem otherEncode_body_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hb : b∉skywalkPoolWires w) (hsign : sign∉skywalkPoolWires w) (heff : eff∉skywalkPoolWires w)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (body : Program)
    (support : wires body⊆groupReadSites w b sign eff (5*j)) :
    Disjoint (wires (otherEncode w j n)) (wires body) := by
  have pool := skywalkShared_integer_nodup w hn
  have groups := otherEncode_disjoint w pool n j bound hj
  apply Finset.disjoint_left.mpr
  intro q hq used
  obtain ⟨k,hk,ne,member⟩ := otherEncode_member w n j q hq
  obtain ⟨r,rfl⟩ := history_gate_mem w (5*k) _ (Or.inl rfl) q member
  have own : historyMap w (5*k) r∈skywalkPoolWires w := by
    apply List.mem_map.mpr
    refine ⟨historyId (5*k) r,?_,rfl⟩
    simp only [List.mem_range'_1]
    have boundId : historyId (5*k) r<1798 := historyId_bound (5*k) (by omega) r
    omega
  have away := history_active_away w sign hn hsign (5*k) (by omega) r
  have read := support used
  simp only [groupReadSites,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at read
  rcases read with (read|read)|read
  · exact away (List.mem_toFinset.mp read)
  · rcases read with eq|eq
    · exact hb (eq ▸ own)
    · exact heff (eq ▸ own)
  · exact Finset.disjoint_left.mp groups hq read

theorem window_transport_other (w : Nat → Wire) (start : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hs : start+5≤512) (other body : Program)
    (he : Disjoint (wires other) (wires (encode w start)))
    (hb : Disjoint (wires other) (wires body)) (s : State) (mO m0 m1 m2 m3 : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w start) s.basis) :
    run (encode w start) m3 (run body m2 (run (decode w start) m1
      (run other mO (run (encode w start) m0 s))))=
      run other mO (run (encode w start) m3 (run body m2 s)) := by
  have otherLegal : MeasuredCodec5.legalAt (historyMap w start) (run other mO s).basis := by
    apply (MeasuredCodec5.legalAt_iff _ _).mpr
    have same (q : Fin 10) : (run other mO s).basis (historyMap w start q)=s.basis (historyMap w start q) :=
      run_preserves_outside _ _ _ _ (fun used => Finset.disjoint_left.mp he used (history_site_mem w start q))
    intro i
    rw [same,same]
    exact (MeasuredCodec5.legalAt_iff _ _).mp legal i
  rw [run_disjoint_commute other (encode w start) he mO m0 s]
  rw [show run (decode w start) m1 (run (encode w start) m0 (run other mO s))=run other mO s from
    ParityCodec5New.roundtripAt _ (historyMap_injective w hn start hs) _ m0 m1 otherLegal]
  rw [←run_disjoint_commute other body hb mO m2 s]
  exact (run_disjoint_commute other (encode w start) he mO m3 (run body m2 s)).symm


private theorem zero_records (p : Program) (hm : measurementCount p=0)
    (s : State) (m n : List Bool) : run p m s=run p n s := by
  rw [←run_take p m s,←run_take p n s,hm]
  simp only [List.take_zero]

theorem encoded_window_step (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hp : ∀q∈[b,sign,eff],q∉skywalkPoolWires w)
    (j : Nat) (hj : j<102) (origin : BasisState) (X Y A B : Fp) (body : Program)
    (support : wires body⊆groupReadSites w b sign eff (5*j))
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


theorem encoded_disjoint_step (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkPoolWires w).Nodup) (origin : BasisState) (X Y A B : Fp) (body : Program)
    (dis : Disjoint (wires (allEncode w 102)) (wires body))
    (correct : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord X) (centerWord Y)) body
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame5 w sign origin X Y s) :
    (run body m s).phase=s.phase ∧ EncodedFieldFrame5 w sign origin A B (run body m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  let rawOut := run body m raw
  have result := correct raw m frame
  have actual : run body m s=run (allEncode w 102) [] rawOut := by
    rw [encoded]
    exact (run_disjoint_commute (allEncode w 102) body dis [] m raw).symm
  rw [actual]
  have ep := allEncode_zero_phase w hn 102 (by decide) rawOut
  exact ⟨ep.trans (result.1.trans phase),rawOut,ep.symm,result.2,rfl⟩


theorem allEncode_hole (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (s : State) (m : List Bool)
    (legal : RawLegal w n s.basis) (port : Fin 10) (hole : port=5 ∨ port=9) :
    (run (allEncode w n) m s).basis (historyMap w (5*j) port)=false := by
  induction n generalizing j m with
  | zero => omega
  | succ n ih =>
    let before := run (allEncode w n) (m.take (measurementCount (allEncode w n))) s
    by_cases current : j=n
    · subst j
      have dis := allEncode_disjoint w hn n n (by omega) (Nat.le_refl _) (by omega)
      have same (q : Fin 10) : before.basis (historyMap w (5*n) q)=s.basis (historyMap w (5*n) q) := by
        apply run_preserves_outside
        intro used
        exact Finset.disjoint_left.mp dis used (history_site_mem w (5*n) q)
      have domain : MeasuredCodec5.legalAt (historyMap w (5*n)) before.basis := by
        apply (MeasuredCodec5.legalAt_iff _ _).mpr
        intro i
        rw [same,same]
        exact (MeasuredCodec5.legalAt_iff _ _).mp (legal n (by omega)) i
      have result := encode_correct w hn (5*n) (by omega) before
        (m.drop (measurementCount (allEncode w n))) domain
      rw [allEncode,run_append]
      rcases hole with rfl|rfl
      · exact result.2.1
      · exact result.2.2
    · have older : j<n := by omega
      have prior := ih j (by omega) older (m.take (measurementCount (allEncode w n)))
        (fun k hk => legal k (by omega))
      have dis := windows_disjoint w hn (5*j) (5*n) (by omega) (by omega) (by omega)
      have keep := run_preserves_outside (encode w (5*n))
        (m.drop (measurementCount (allEncode w n))) before (historyMap w (5*j) port)
        (fun used => Finset.disjoint_left.mp dis (history_site_mem w (5*j) port) used)
      rw [allEncode,run_append]
      exact keep.trans prior


theorem allEncode_holes_zero (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (legal : RawLegal w 102 s.basis)
    (k : Nat) (hk : k<204) : (run (allEncode w 102) m s).basis (w (Placement5.H k))=false := by
  let port : Fin 10 := if k%2=0 then 5 else 9
  have hp : port=5 ∨ port=9 := by unfold port; split <;> simp
  have same : w (Placement5.H k)=historyMap w (5*(k/2)) port := by
    change w (Placement5.H k)=w (historyId (5*(k/2)) port)
    congr 1
    unfold Placement5.H historyId History5.historyId port
    split_ifs <;> omega
  rw [same]
  exact allEncode_hole w hn 102 (k/2) (by decide) (by omega) s m legal port hp

theorem encoded_work_zero (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (origin : BasisState) (env : Env w origin)
    (X Y : Fp) (s : State) (frame : EncodedFieldFrame5 w sign origin X Y s)
    (q : Nat) (hq : Placement5.workRegion q) : s.basis (w q)=false := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have rawEnv := pair_env w sign hn origin raw.basis _ _ env rawFrame
  have zero := OffsetCleanupBorrowedCaller.maskBit_zero w raw.basis rawEnv.1 q
    (by unfold Placement5.workRegion at hq; omega) (by unfold Placement5.workRegion at hq; omega)
  have support := allEncode_history_support w 102 (by decide)
  have away : w q∉wires (allEncode w 102) := by
    intro used
    have member := List.mem_toFinset.mp (support used)
    rcases List.mem_append.mp member with member|member
    all_goals
      obtain ⟨k,hk,eq⟩ := List.mem_map.mp member
      simp only [List.mem_range'_1] at hk
      have same := skywalkShared_index_inj w hn k q (by omega)
        (by unfold Placement5.workRegion at hq; omega) eq
      unfold Placement5.workRegion at hq
      omega
  rw [encoded]
  exact (run_preserves_outside (allEncode w 102) [] raw _ away).trans zero

theorem encoded_zero_region (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkPoolWires w)
    (origin : BasisState) (env : Env w origin) (legal : RawLegal w 102 origin)
    (X Y : Fp) (s : State) (frame : EncodedFieldFrame5 w sign origin X Y s) :
    ∀q,Placement5.zeroRegion q → s.basis (w q)=false := by
  intro q hq
  rcases hq with work|hole
  · exact encoded_work_zero w sign hn origin env X Y s frame q work
  · have recover := Placement5.hole_recover q hole
    obtain ⟨raw,_,rawFrame,encoded⟩ := frame
    have rawLegal := frame_history_legal w sign hn ho 102 (by decide) origin raw.basis _ _ legal rawFrame
    rw [encoded,←recover.2]
    exact allEncode_holes_zero w (skywalkShared_integer_nodup w hn) raw [] rawLegal _ recover.1


theorem encoded_canonical_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : EncodedCanonicalFrame5 origin X Y s) (ht : EncodedCanonicalFrame5 origin X Y t)
    (phase : s.phase=t.phase) : s=t := by
  obtain ⟨a,ha,fa,ea⟩ := hs
  obtain ⟨b,hb,fb,eb⟩ := ht
  have raw : a=b := by
    apply State.extensionality
    · exact ha.trans (phase.trans hb.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ fa fb
  rw [ea,eb,raw]

theorem groupReadSites_eq (w : Nat → Wire) (b sign eff : Wire) (start : Nat) :
    groupReadSites w b sign eff start=History5.groupReadSites w b sign eff start := by
  unfold groupReadSites History5.groupReadSites
  rw [encode_support_eq]

theorem otherEncode_support_eq (w : Nat → Wire) (j n : Nat) :
    wires (otherEncode w j n)=wires (History5.otherEncode w j n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n=j
    · simpa only [otherEncode,History5.otherEncode,h,if_true] using ih
    · simp only [otherEncode,History5.otherEncode,h,if_false,wires_append,ih,encode_support_eq]

def payloadPort (i : Fin 8) : Fin 10 :=
  ⟨if i.val<5 then i.val else i.val+1,by split <;> omega⟩

def payloadWire (w : Nat → Wire) (i : Nat) : Wire :=
  historyMap w (5*(i/8)) (payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩)

theorem payloadWire_packet (w : Nat → Wire) (j i : Nat) (hi : i<8) :
    payloadWire w (8*j+i)=historyMap w (5*j) (payloadPort ⟨i,hi⟩) := by
  have hd : (8*j+i)/8=j := by omega
  have hm : (8*j+i)%8=i := by omega
  simp only [payloadWire,hd,hm]

theorem encode_packet_parity (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start : Nat) (hs : start+5≤512) (s : State) (m : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w start) s.basis) :
    TraceParity5.xorRange 8 (fun i => (run (encode w start) m s).basis
      (historyMap w start (payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩)))=
    TraceParity5.xorRange 5 (fun i => s.basis (w (1028+start+i))) := by
  have localParity := ParityCodec5New.encodeAt_parity (historyMap w start)
    (historyMap_injective w hn start hs) s m legal
  simpa [TraceParity5.xorRange,payloadPort,historyMap,History5.historyMap,
    historyId,History5.historyId,Bool.xor_assoc,Nat.add_assoc,encode] using localParity.symm

theorem allEncode_packet_parity (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (raw : State)
    (legal : RawLegal w n raw.basis) :
    TraceParity5.xorRange 8 (fun i => (run (allEncode w n) [] raw).basis
      (payloadWire w (8*j+i)))=
    TraceParity5.xorRange 5 (fun i => raw.basis (w (1028+5*j+i))) := by
  have factor := allEncode_factor w hn n j bound hj raw
  have dis := otherEncode_disjoint w hn n j bound hj
  have same (q : Fin 10) : (run (allEncode w n) [] raw).basis (historyMap w (5*j) q)=
      (run (encode w (5*j)) [] raw).basis (historyMap w (5*j) q) := by
    rw [factor]
    exact run_preserves_outside _ _ _ _
      (fun used => Finset.disjoint_left.mp dis used (history_site_mem w (5*j) q))
  calc
    TraceParity5.xorRange 8 (fun i => (run (allEncode w n) [] raw).basis (payloadWire w (8*j+i)))=
        TraceParity5.xorRange 8 (fun i => (run (encode w (5*j)) [] raw).basis
          (historyMap w (5*j) (payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩))) := by
      apply TraceParity5.xorRange_congr
      intro i hi
      rw [payloadWire_packet w j i hi]
      simpa only [Nat.mod_eq_of_lt hi] using same (payloadPort ⟨i,hi⟩)
    _ = _ := encode_packet_parity w hn (5*j) (by omega) raw [] (legal j hj)

theorem allEncode_tailS (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n t : Nat) (_bound : 5*n≤512) (ht : 5*n≤t) (ht512 : t<512)
    (s : State) (m : List Bool) :
    (run (allEncode w n) m s).basis (w (1028+t))=s.basis (w (1028+t)) := by
  apply run_preserves_outside
  intro used
  rw [allEncode_support_eq] at used
  obtain ⟨j,hj,member⟩ := History5.allEncode_member w n _ used
  obtain ⟨q,hq⟩ := History5.history_gate_mem w (5*j) _ (Or.inl rfl) _ member
  have ids := skywalkPool_index_inj w hn (1028+t) (History5.historyId (5*j) q)
    (by omega) (History5.historyId_bound (5*j) (by omega) q) hq
  have hq10 := q.isLt
  unfold History5.historyId at ids
  split_ifs at ids <;> omega

theorem encoded_host_relation (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p) (raw s : State)
    (stage : W.CompactSkywalkStage w
      (SkywalkRails.encode false false (x:Int) (ECDSAAdd.p:Int)) 512 raw.basis)
    (encoded : s.basis=(run (allEncode w 102) [] raw).basis) :
    s.basis (w 1538)=TraceParity5.xorRange 816 (fun i => s.basis (payloadWire w i)) := by
  have hp0 : 0<ECDSAAdd.p := p_prime.pos
  have hpodd : ECDSAAdd.p%2=1 := by norm_num [ECDSAAdd.p]
  have legal : RawLegal w 102 raw.basis := by
    intro j hj
    exact W.stage_group_legal w hn x ECDSAAdd.p 512 (5*j) hp0 hpodd (by omega) (by decide) raw.basis stage
  have fields := (W.compactSkywalkStage_fields_iff w _ 512 (by decide) hn raw.basis).mp stage
  have rawS (i : Nat) (hi : i<512) : raw.basis (w (1028+i))=TraceParity5.rawS x i := by
    rw [(fields.2.2.2.1 i hi).2]
    simp only [TraceParity5.rawS,SkywalkTrace.trace_getD_code 512 _ i hi]
  have packets : ∀j,j<102 →
      TraceParity5.xorRange 8 (fun i => s.basis (payloadWire w (8*j+i)))=
      TraceParity5.xorRange 5 (fun i => TraceParity5.rawS x (5*j+i)) := by
    intro j hj
    rw [encoded,allEncode_packet_parity w hn 102 j (by decide) hj raw legal]
    apply TraceParity5.xorRange_congr
    intro i hi
    simpa only [Nat.add_assoc] using rawS (5*j+i) (by omega)
  have whole := TraceParity5.encoded_payload_parity x hx0 hx (fun i => s.basis (payloadWire w i)) packets
  have tail := allEncode_tailS w hn 102 510 (by decide) (by decide) (by decide) raw []
  change (run (allEncode w 102) [] raw).basis (w 1538)=raw.basis (w 1538) at tail
  calc
    s.basis (w 1538)=raw.basis (w 1538) := by rw [encoded]; exact tail
    _ = TraceParity5.rawS x 510 := rawS 510 (by decide)
    _ = TraceParity5.xorRange 816 (fun i => s.basis (payloadWire w i)) := whole.symm

end ECDSAAdd.Entrant.NewHistory5

end

-- Public component ParityCodec5New.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ParityCodec5New
open Arithmetic Challenge RecordedQuantum Baselines

def encodeFirst : Program := twist ++ FirstNonzeroCodec.encodeFirst
def decodeFirst : Program := FirstNonzeroCodec.decodeFirst ++ untwist
def encodeAtFirst (f : Fin 10→Wire) : Program := renameProgram (label f) encodeFirst
def decodeAtFirst (f : Fin 10→Wire) : Program := renameProgram (label f) decodeFirst

theorem first_counts : toffoliCount encodeFirst=8 ∧ toffoliCount decodeFirst=9 ∧
    measurementCount encodeFirst=4 ∧ measurementCount decodeFirst=2 := by
  simp only [encodeFirst,decodeFirst,toffoliCount_append,measurementCount_append]
  simpa [twist,untwist,toffoliCount,measurementCount] using FirstNonzeroCodec.counts

theorem first_slots : gateSlots encodeFirst=146 ∧ gateSlots decodeFirst=144 := by decide +kernel

theorem first_support_exact : wires encodeFirst=Finset.range 10 ∧
    wires decodeFirst=Finset.range 10 := by decide +kernel

theorem first_support : wires encodeFirst⊆Finset.range 10 ∧
    wires decodeFirst⊆Finset.range 10 := by
  rw [first_support_exact.1,first_support_exact.2]
  exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩

theorem first_physical : GatePhysical encodeFirst ∧ GatePhysical decodeFirst := by
  have ht : GatePhysical twist := by simp [GatePhysical,twist,PhysicalInstr,ProperGate]
  have hu : GatePhysical untwist := by simp [GatePhysical,untwist,PhysicalInstr,ProperGate]
  exact ⟨(gatePhysical_append _ _).mpr ⟨ht,FirstNonzeroCodec.physical.1⟩,
    (gatePhysical_append _ _).mpr ⟨FirstNonzeroCodec.physical.2,hu⟩⟩

theorem twist_first (s : State) (m : List Bool) :
    (run twist m s).basis 0=s.basis 0 ∧ (run twist m s).basis 1=s.basis 1 := by
  rw [twist_basis]
  simp [writeBit]

theorem encode_eq (s : State) (m : List Bool) (h : MeasuredCodec5.legal s.basis)
    (hn : s.basis 0=true ∨ s.basis 1=true) : run encodeFirst m s=run encode m s := by
  have nz : (run twist [] s).basis 0=true ∨ (run twist [] s).basis 1=true := by
    simpa only [(twist_first s []).1,(twist_first s []).2] using hn
  simp only [encodeFirst,encode,run_append,show measurementCount twist=0 from rfl,
    List.take_zero,List.drop_zero]
  exact FirstNonzeroCodec.encode_eq _ m (twist_legal s [] h) nz

theorem decode_eq (s : State) (mE mD : List Bool) (h : MeasuredCodec5.legal s.basis)
    (hn : s.basis 0=true ∨ s.basis 1=true) :
    run decodeFirst mD (run encode mE s)=run decode mD (run encode mE s) := by
  have nz : (run twist [] s).basis 0=true ∨ (run twist [] s).basis 1=true := by
    simpa only [(twist_first s []).1,(twist_first s []).2] using hn
  simp only [encode,decodeFirst,decode,run_append,show measurementCount twist=0 from rfl,
    List.take_zero,List.drop_zero,FirstNonzeroCodec.counts.2.2.2,MeasuredCodec5.counts.2.2.2]
  rw [FirstNonzeroCodec.decode_eq _ _ _ (twist_legal s [] h) nz]

theorem roundtripFirst (s : State) (mE mD : List Bool) (h : MeasuredCodec5.legal s.basis)
    (hn : s.basis 0=true ∨ s.basis 1=true) : run decodeFirst mD (run encodeFirst mE s)=s := by
  rw [encode_eq s mE h hn,decode_eq s mE mD h hn,roundtrip s mE mD h]

theorem first_independent (s : State) (m n : List Bool) (h : MeasuredCodec5.legal s.basis)
    (hn : s.basis 0=true ∨ s.basis 1=true) : run encodeFirst m s=run encodeFirst n s := by
  rw [encode_eq s m h hn,encode_eq s n h hn,encode_independent s m n h]

theorem first_countsAt (f : Fin 10→Wire) :
    toffoliCount (encodeAtFirst f)=8 ∧ toffoliCount (decodeAtFirst f)=9 ∧
    measurementCount (encodeAtFirst f)=4 ∧ measurementCount (decodeAtFirst f)=2 := by
  simpa only [encodeAtFirst,decodeAtFirst,(renameProgram_counts (label f) encodeFirst).1,
    (renameProgram_counts (label f) encodeFirst).2,(renameProgram_counts (label f) decodeFirst).1,
    (renameProgram_counts (label f) decodeFirst).2] using first_counts

theorem first_slotsAt (f : Fin 10→Wire) :
    gateSlots (encodeAtFirst f)=146 ∧ gateSlots (decodeAtFirst f)=144 := by
  simpa only [encodeAtFirst,decodeAtFirst,rename_gateSlots] using first_slots

theorem first_mapped_support (f : Fin 10→Wire) :
    wires (encodeAtFirst f)=wires (encodeAt f) ∧ wires (decodeAtFirst f)=wires (decodeAt f) := by
  simp only [encodeAtFirst,decodeAtFirst,encodeAt,decodeAt,renameProgram_support,
    first_support_exact.1,first_support_exact.2,support_exact.1,support_exact.2]
  exact ⟨trivial,trivial⟩

theorem first_mapped_physical (f : Fin 10→Wire) (hf : Function.Injective f) :
    GatePhysical (encodeAtFirst f) ∧ GatePhysical (decodeAtFirst f) := by
  exact ⟨gatePhysical_rename_support _ _
    (fun a ha b hb e => FirstNonzeroCodec.label_inj' f hf a (first_support.1 ha) b (first_support.1 hb) e)
      first_physical.1,
    gatePhysical_rename_support _ _
    (fun a ha b hb e => FirstNonzeroCodec.label_inj' f hf a (first_support.2 ha) b (first_support.2 hb) e)
      first_physical.2⟩

theorem encodeAt_eq (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (hl : legalAt f s.basis)
    (hn : s.basis (f 0)=true ∨ s.basis (f 1)=true) :
    run (encodeAtFirst f) m s=run (encodeAt f) m s := by
  apply FirstNonzeroCodec.renamed_eq f hf _ _ first_support.1 support.1 s m
  apply encode_eq (⟨s.phase,fun q => s.basis (label f q)⟩ : State) m hl
  simpa only [label,MeasuredCodec5.label,dif_pos (show 0<10 by decide),
    dif_pos (show 1<10 by decide)] using hn

theorem decodeAt_eq (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (mE mD : List Bool) (hl : legalAt f s.basis)
    (hn : s.basis (f 0)=true ∨ s.basis (f 1)=true) :
    run (decodeAtFirst f) mD (run (encodeAt f) mE s)=
      run (decodeAt f) mD (run (encodeAt f) mE s) := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have hn' : t.basis 0=true ∨ t.basis 1=true := by
    simpa only [t,label,MeasuredCodec5.label,dif_pos (show 0<10 by decide),
      dif_pos (show 1<10 by decide)] using hn
  have pe := run_rename_pool (label f) (Finset.range 10) (FirstNonzeroCodec.label_inj' f hf)
    encode support.1 mE t s rfl (fun _ _ => rfl)
  have pn := run_rename_pool (label f) (Finset.range 10) (FirstNonzeroCodec.label_inj' f hf)
    decodeFirst first_support.2 mD (run encode mE t) (run (encodeAt f) mE s) pe.1.symm
    (fun q hq => (pe.2 q hq).symm)
  have po := run_rename_pool (label f) (Finset.range 10) (FirstNonzeroCodec.label_inj' f hf)
    decode support.2 mD (run encode mE t) (run (encodeAt f) mE s) pe.1.symm
    (fun q hq => (pe.2 q hq).symm)
  have de := decode_eq t mE mD hl hn'
  apply State.extensionality
  · exact pn.1.trans ((congrArg State.phase de).trans po.1.symm)
  · funext z
    by_cases hz : z∈(Finset.range 10).image (label f)
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      exact (pn.2 q hq).trans ((congrArg (fun st : State => st.basis q) de).trans (po.2 q hq).symm)
    · have noP : z∉wires (decodeAtFirst f) := by
        rw [decodeAtFirst,renameProgram_support]
        intro hh
        obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp hh
        exact hz (Finset.mem_image.mpr ⟨q,first_support.2 hq,eq⟩)
      have noQ : z∉wires (decodeAt f) := by
        rw [decodeAt,renameProgram_support]
        intro hh
        obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp hh
        exact hz (Finset.mem_image.mpr ⟨q,support.2 hq,eq⟩)
      exact (run_preserves_outside _ mD _ z noP).trans (run_preserves_outside _ mD _ z noQ).symm

theorem roundtripAtFirst (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (mE mD : List Bool) (hl : legalAt f s.basis)
    (hn : s.basis (f 0)=true ∨ s.basis (f 1)=true) :
    run (decodeAtFirst f) mD (run (encodeAtFirst f) mE s)=s := by
  rw [encodeAt_eq f hf s mE hl hn,decodeAt_eq f hf s mE mD hl hn,roundtripAt f hf s mE mD hl]

theorem encodeAtFirst_correct (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (hl : legalAt f s.basis)
    (hn : s.basis (f 0)=true ∨ s.basis (f 1)=true) :
    (run (encodeAtFirst f) m s).phase=s.phase ∧
    (run (encodeAtFirst f) m s).basis (f 5)=false ∧
    (run (encodeAtFirst f) m s).basis (f 9)=false := by
  rw [encodeAt_eq f hf s m hl hn]
  exact encodeAt_correct f hf s m hl

theorem encodeAtFirst_independent (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m n : List Bool) (hl : legalAt f s.basis)
    (hn : s.basis (f 0)=true ∨ s.basis (f 1)=true) :
    run (encodeAtFirst f) m s=run (encodeAtFirst f) n s := by
  rw [encodeAt_eq f hf s m hl hn,encodeAt_eq f hf s n hl hn,encodeAt_independent f hf s m n hl]

theorem decodeAt_eq_on_pool (f : Fin 10→Wire) (hf : Function.Injective f)
    (raw s : State) (mE mD : List Bool) (hl : legalAt f raw.basis)
    (hn : raw.basis (f 0)=true ∨ raw.basis (f 1)=true)
    (hb : ∀q∈(Finset.range 10).image (label f),
      s.basis q=(run (encodeAt f) mE raw).basis q) :
    run (decodeAtFirst f) mD s=run (decodeAt f) mD s := by
  apply FirstNonzeroCodec.run_eq_local_transfer _ _ ((Finset.range 10).image (label f)) _ _ s
    (run (encodeAt f) mE raw) mD hb (decodeAt_eq f hf raw mE mD hl hn)
  · rw [decodeAtFirst,renameProgram_support]
    intro q hh
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_image_of_mem _ (first_support.2 hi)
  · rw [decodeAt,renameProgram_support]
    intro q hh
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_image_of_mem _ (support.2 hi)

end ECDSAAdd.Entrant.ParityCodec5New

end

-- Public component FrontierEntry1591Forward.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.NewHistory5
open Arithmetic

 theorem pack_support_eq (w : Nat → Wire) (i : Nat) :
    wires (packAfter w i)=wires (History5.packAfter w i) := by
  unfold packAfter History5.packAfter
  split <;> simp only [encode_support_eq]

 theorem prefix_support_eq (w : Nat → Wire) (i : Nat) :
    wires (encodePrefix w i)=wires (History5.encodePrefix w i) := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [encodePrefix,History5.encodePrefix,wires_append,ih,pack_support_eq]

 theorem prefix_next_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (hb : n<512) (due : History5.packDue n=true) :
    Disjoint (wires (encodePrefix w n)) (wires (encode w (n-5))) := by
  rw [prefix_support_eq,encode_support_eq]
  exact History5.prefix_next_disjoint w hn n hb due

 theorem prefix_next_legal (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (hb : n<512) (due : History5.packDue n=true) (s : State) (m : List Bool)
    (legal : MeasuredCodec5.legalAt (History5.historyMap w (n-5)) s.basis) :
    MeasuredCodec5.legalAt (History5.historyMap w (n-5)) (run (encodePrefix w n) m s).basis := by
  have dis := prefix_next_disjoint w hn n hb due
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  have same (q : Fin 10) : (run (encodePrefix w n) m s).basis (History5.historyMap w (n-5) q)=
      s.basis (History5.historyMap w (n-5) q) :=
    run_preserves_outside _ _ _ _ (fun used => Finset.disjoint_left.mp dis used
      (ParityCodec5New.site_mem _ q))
  intro i
  rw [same,same]
  exact (MeasuredCodec5.legalAt_iff _ _).mp legal i

 theorem encodePrefix_zero_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (hb : n        ≤        512) (s : State) : (run (encodePrefix w n) [] s).phase=s.phase := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [encodePrefix,run_append]
    simp only [List.take_nil,List.drop_nil]
    cases due : History5.packDue n
    · simp only [packAfter,due,Bool.false_eq_true,if_false,run]
      exact ih (by omega)
    · have hd := History5.packDue_true n due
      simp only [packAfter,due,if_true,encode]
      exact (ParityCodec5New.encodeAt_zero_phase _
        (History5.historyMap_injective w hn (n-5) (by omega)) _).trans (ih (by omega))

theorem encodePrefix_index (w : Nat → Wire) (n : Nat) : encodePrefix w (5*n+1)=allEncode w n := by
  induction n with
  | zero => simp [encodePrefix,packAfter,History5.packDue,allEncode]
  | succ n ih =>
    have index : 5*(n+1)+1=5*n+1+1+1+1+1+1 := by omega
    rw [index,encodePrefix,encodePrefix,encodePrefix,encodePrefix,encodePrefix,ih]
    have d1 : History5.packDue (5*n+1)=false := by simp [History5.packDue,Nat.add_mod]
    have d2 : History5.packDue (5*n+1+1)=false := by simp [History5.packDue,Nat.add_mod]
    have d3 : History5.packDue (5*n+1+1+1)=false := by simp [History5.packDue,Nat.add_mod]
    have d4 : History5.packDue (5*n+1+1+1+1)=false := by simp [History5.packDue,Nat.add_mod]
    have d5 : History5.packDue (5*n+1+1+1+1+1)=true := by simp [History5.packDue,Nat.add_mod]
    simp only [packAfter,d1,d2,d3,d4,d5,Bool.false_eq_true,if_false,if_true,List.append_nil]
    rw [show 5*n+1+1+1+1+1-5=5*n by omega]
    rfl

 theorem encodePrefix_512 (w : Nat → Wire) : encodePrefix w 512=allEncode w 102 := by
  rw [show (512:Nat)=511+1 from rfl,encodePrefix]
  rw [show (511:Nat)=5*102+1 from rfl,encodePrefix_index]
  have h : History5.packDue 511=false := by decide
  simp only [packAfter,h,Bool.false_eq_true,if_false,List.append_nil]

end ECDSAAdd.Entrant.NewHistory5

namespace ECDSAAdd.Entrant.NewStackOB5
open Arithmetic MappedCompressed Secp256k1 OB5

abbrev Stage := NewHistory5.CompressedCompactStage5

def packFirst (w : Nat → Wire) (i : Nat) : Program :=
  if i=5 then ParityCodec5New.encodeAtFirst (History5.historyMap w 0)
  else NewHistory5.packAfter w i

def regularForward (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => (W.repairedTick w i++NewHistory5.packAfter w i)++regularForward w (i+1) n

def compactForward (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => (W.compactSkywalkTick w i++NewHistory5.packAfter w i)++compactForward w (i+1) n

def forward (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (sig i) (W.repairedTick base i++packFirst base i)++forward (i+1) n

 theorem prefix_disjoint_layout (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n i : Nat) (hni : n        ≤        i) (hi : i<512) :
    Disjoint (wires (NewHistory5.encodePrefix w n)) (W.compactSkywalkTickLayout w i).wires.toFinset := by
  rw [NewHistory5.prefix_support_eq]
  exact Stack5.prefix_disjoint_layout w hn n i hni hi

 theorem prefix_disjoint_tick (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n i : Nat) (hni : n        ≤        i) (hi : i<512) :
    Disjoint (wires (NewHistory5.encodePrefix w n)) (wires (W.compactSkywalkTick w i)) :=
  Finset.disjoint_left.mpr (fun _ he ht => Finset.disjoint_left.mp
    (prefix_disjoint_layout w hn n i hni hi) he (W.compactSkywalkTick_support w i hi hn ht))

 theorem old_stage_local (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hi : i<512) (s : State) (hs : Stage w x p i s.basis) :
    ∃t : State, W.CompressedCompactStage5 w x p i t.basis ∧
      ∀q∈(W.compactSkywalkTickLayout w i).wires.toFinset,s.basis q=t.basis q := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  refine ⟨run (History5.encodePrefix w i) [] raw,⟨raw,hraw,rfl⟩,?_⟩
  intro q hq
  rw [hbits]
  have dn := prefix_disjoint_layout w hn i i (le_refl _) hi
  have oldDis := Stack5.prefix_disjoint_layout w hn i i (le_refl _) hi
  exact (run_preserves_outside _ _ _ q (fun h=>Finset.disjoint_left.mp dn h hq)).trans
    (run_preserves_outside _ _ _ q (fun h=>Finset.disjoint_left.mp oldDis h hq)).symm

 theorem repaired_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512)
    (s : State) (m n : List Bool) (hs : Stage w x p i s.basis) :
    run (W.repairedTick w i) m s=run (W.compactSkywalkTick w i) n s := by
  obtain ⟨t,ht,read⟩ := old_stage_local w hn x p i hi s hs
  exact Stack5.local_replace _ _ _ (W.repairedTick_support w i hi hn)
    (W.compactSkywalkTick_support w i hi hn) s t m n read
    (Stack5.repaired_eq5 w hn x p i hp0 hx0 hpo hp hgap hx hc hi t m n ht)

 theorem stage_one (w : Nat → Wire) (x p : Nat) (s : State)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    Stage w x p 1 s.basis := by
  refine ⟨s,hs,?_⟩
  simp [NewHistory5.encodePrefix,NewHistory5.packAfter,History5.packDue,run]

theorem compact_step_spec (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (_hlo : History5.HistoryAbove w)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (hq : p+2^32         ≤         2^256) (hx : x < p) (hc : x.Coprime p) (hi : i < 512) :
    Triple (Stage w x p i)
      (W.compactSkywalkTick w i++NewHistory5.packAfter w i) (Stage w x p (i+1)) := by
  intro s m hs
  obtain ⟨raw,hraw,hbits⟩ := hs
  let tick := W.compactSkywalkTick w i
  let mt := m.take (measurementCount tick)
  let me := m.drop (measurementCount tick)
  let actual := run tick mt s
  let next := run tick [] raw
  have step := W.compactSkywalkStageStep w hn x p i hp0 hx0 hpo hp hq hx hc hi
  have hnxt := step raw [] hraw
  have hmt := step raw mt hraw
  have hd := prefix_disjoint_tick w hn i i (Nat.le_refl i) hi
  have read : ∀q∈wires tick,s.basis q=raw.basis q := by
    intro q hq
    rw [hbits]
    exact run_preserves_outside _ _ _ q (fun he => Finset.disjoint_left.mp hd he hq)
  have localStep := run_local_increment tick s raw mt read
  have phase : actual.phase=s.phase := by
    have hh := localStep.1
    rw [hmt.1] at hh
    have neutral : (actual.phase ^^ s.phase)=false := by
      simpa only [Bool.xor_self] using hh
    cases ha : actual.phase <;> cases hb : s.phase <;> simp_all
  have commute := run_disjoint_commute (NewHistory5.encodePrefix w i) tick hd [] [] raw
  have same := run_basis_records tick s (run (NewHistory5.encodePrefix w i) [] raw) mt [] hbits
  have bits : actual.basis=(run (NewHistory5.encodePrefix w i) [] next).basis :=
    same.trans (congrArg State.basis commute.symm)
  have packPhase : (run (NewHistory5.packAfter w i) me actual).phase=actual.phase := by
    cases due : History5.packDue i
    · simp only [NewHistory5.packAfter,due,Bool.false_eq_true,if_false,run]
    · have hd := History5.packDue_true i due
      have nextLegal := W.stage_group_legal w hn x p (i+1) (i-5) hp0 hpo (by omega) (by omega) next.basis hnxt.2
      have encLegal := NewHistory5.prefix_next_legal w hn i hi due next [] nextLegal
      have actualLegal : MeasuredCodec5.legalAt (History5.historyMap w (i-5)) actual.basis := by
        rw [bits]
        exact encLegal
      simpa only [NewHistory5.packAfter,due,if_true,NewHistory5.encode] using
        ParityCodec5New.encodeAt_phase _ (History5.historyMap_injective w hn (i-5) (by omega)) actual me actualLegal
  have packBits := run_basis_records (NewHistory5.packAfter w i) actual
    (run (NewHistory5.encodePrefix w i) [] next) me [] bits
  have nextBits : (run (NewHistory5.packAfter w i) me actual).basis=
      (run (NewHistory5.encodePrefix w (i+1)) [] next).basis := by
    rw [NewHistory5.encodePrefix,run_append]
    simp only [List.take_nil,List.drop_nil]
    exact packBits
  rw [run_append]
  exact ⟨packPhase.trans phase,⟨next,hnxt.2,nextBits⟩⟩

 theorem tick_pack_legal (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512)
    (s : State) (m : List Bool) (hs : Stage w x p i s.basis) (due : History5.packDue i=true) :
    MeasuredCodec5.legalAt (History5.historyMap w (i-5)) (run (W.compactSkywalkTick w i) m s).basis := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  let next := run (W.compactSkywalkTick w i) [] raw
  have ns := W.compactSkywalkStageStep w hn x p i hp0 hx0 hpo hp hgap hx hc hi raw [] hraw
  have dis := prefix_disjoint_tick w hn i i (le_refl _) hi
  have commute := run_disjoint_commute (NewHistory5.encodePrefix w i) (W.compactSkywalkTick w i) dis [] [] raw
  have same := run_basis_records (W.compactSkywalkTick w i) s (run (NewHistory5.encodePrefix w i) [] raw) m [] hbits
  have bits : (run (W.compactSkywalkTick w i) m s).basis=(run (NewHistory5.encodePrefix w i) [] next).basis :=
    same.trans (congrArg State.basis commute.symm)
  have hd := History5.packDue_true i due
  have legal := W.stage_group_legal w hn x p (i+1) (i-5) hp0 hpo (by omega) (by omega) next.basis ns.2
  rw [bits]
  exact NewHistory5.prefix_next_legal w hn i hi due next [] legal

 theorem step_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512)
    (s : State) (m n : List Bool) (hs : Stage w x p i s.basis) :
    run (W.repairedTick w i++NewHistory5.packAfter w i) m s=
      run (W.compactSkywalkTick w i++NewHistory5.packAfter w i) n s := by
  rw [run_append,run_append]
  rw [repaired_eq w hn x p i hp0 hx0 hpo hp hgap hx hc hi s
    (m.take (measurementCount (W.repairedTick w i)))
    (n.take (measurementCount (W.compactSkywalkTick w i))) hs]
  cases due : History5.packDue i
  · simp only [NewHistory5.packAfter,due,Bool.false_eq_true,if_false,run]
  · have hd := History5.packDue_true i due
    have legal := tick_pack_legal w hn x p i hp0 hx0 hpo hp hgap hx hc hi s
      (n.take (measurementCount (W.compactSkywalkTick w i))) hs due
    simp only [NewHistory5.packAfter,due,if_true,NewHistory5.encode]
    exact ParityCodec5New.encodeAt_independent _ (History5.historyMap_injective w hn (i-5) (by omega)) _
      (m.drop (measurementCount (W.repairedTick w i)))
      (n.drop (measurementCount (W.compactSkywalkTick w i))) legal

 theorem step_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (hlo : History5.HistoryAbove w)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512) :
    Triple (Stage w x p i) (W.repairedTick w i++NewHistory5.packAfter w i) (Stage w x p (i+1)) := by
  intro s m hs
  rw [step_eq w hn x p i hp0 hx0 hpo hp hgap hx hc hi s m [] hs]
  exact compact_step_spec w hn hlo x p i hp0 hx0 hpo hp hgap hx hc hi s [] hs

 theorem regularForward_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (hlo : History5.HistoryAbove w)
    (x p i n : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p) (hi : i+n        ≤        512) :
    Triple (Stage w x p i) (regularForward w i n) (Stage w x p (i+n)) := by
  induction n generalizing i with
  | zero =>
    rw [regularForward,Nat.add_zero]
    intro s m hs
    exact ⟨rfl,hs⟩
  | succ n ih =>
    have first := step_spec w hn hlo x p i hp0 hx0 hpo hp hgap hx hc (by omega)
    have rest := ih (i+1) (by omega)
    have idx : i+(n+1)=(i+1)+n := by omega
    rw [regularForward,idx]
    exact first.seq rest

 theorem prefix_keep (i : Nat) (hi : i        ≤        512) (raw : State) (l : Nat) (hl : 1027+i        ≤        l) :
    (run (NewHistory5.encodePrefix base i) [] raw).basis (base l)=raw.basis (base l) := by
  apply run_preserves_outside
  intro hm
  rw [NewHistory5.prefix_support_eq] at hm
  obtain ⟨j,hj,hr⟩ := StackOB5Base.encodePrefix_mem i hi _ hm
  have := base_injective hj
  omega

theorem stage_zero (x i : Nat) (hi : i < 512) (b : BasisState)
    (h : Stage base x p i b) :
    b (base (1028+i)) = false ∧ (257         ≤         i → b (base (2053-i)) = false) := by
  obtain ⟨raw, hraw, rfl⟩ := h
  have virt : ∀ l, 1028         ≤         l → W.compactSkywalkStageVirtual base i raw.basis (base l) =
      raw.basis (base l) := by
    intro l hl
    have ex := W.compactSkywalkStage_expanded base i (by omega)
    apply W.compactSkywalkStage_virtual_outside
    · intro hm
      have hm' : base l ∈ (W.compactSkywalkSignPoolA base i).expanded :=
        List.mem_append_right _ hm
      rw [ex.1] at hm'
      obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
      have := base_injective he
      simp only [List.mem_range'_1] at hj
      omega
    · intro hm
      have hm' : base l ∈ (W.compactSkywalkSignPoolB base i).expanded :=
        List.mem_append_right _ hm
      rw [ex.2] at hm'
      obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
      have := base_injective he
      simp only [List.mem_range'_1] at hj
      omega
  have stage := hraw.1
  have fut := (stage.2.2.2.2.1 i (Nat.le_refl i) hi).2
  have carry := (regValue_zero _ _).mp stage.2.2.2.2.2.1
  constructor
  · rw [prefix_keep i (by omega) raw (1028+i) (by omega), ← virt (1028+i) (by omega)]
    exact fut
  · intro big
    rw [prefix_keep i (by omega) raw (2053-i) (by omega), ← virt (2053-i) (by omega)]
    apply carry
    exact List.mem_map.mpr ⟨2053-i, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩


 theorem forward_step_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p)
    (s : State) (m : List Bool) (hs : Stage w x p i s.basis) :
    run (W.repairedTick w i++packFirst w i) m s=
      run (W.repairedTick w i++NewHistory5.packAfter w i) m s := by
  by_cases hi:i=5
  · subst i
    have rawStage : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 5 s.basis := by
      obtain ⟨raw,hr,hbits⟩ := hs
      have empty : NewHistory5.encodePrefix w 5=[] := by
        simp [NewHistory5.encodePrefix,NewHistory5.packAfter,History5.packDue]
      have bits : s.basis=raw.basis := by simpa only [empty,run] using hbits
      rw [bits]
      exact hr
    let mt := m.take (measurementCount (W.repairedTick w 5))
    have eq := repaired_eq w hn x p 5 hp0 hx0 hpo hp hgap hx hc (by decide) s mt mt hs
    have next := W.compactSkywalkStageStep w hn x p 5 hp0 hx0 hpo hp hgap hx hc (by decide) s mt rawStage
    have actual : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 6
        (run (W.repairedTick w 5) mt s).basis := by rw [eq]; exact next.2
    have legal := W.stage_group_legal w hn x p 6 0 hp0 hpo (by omega) (by omega)
      (run (W.repairedTick w 5) mt s).basis actual
    have nz := FirstNonzeroCodec.w_first_nonzero w hn x p 6 hp0 hpo hx (by decide) (by decide)
      (run (W.repairedTick w 5) mt s).basis actual
    have nz' : (run (W.repairedTick w 5) mt s).basis (History5.historyMap w 0 0)=true ∨
        (run (W.repairedTick w 5) mt s).basis (History5.historyMap w 0 1)=true := by
      simpa [History5.historyMap,History5.historyId,Bool.or_eq_true] using nz
    simp only [packFirst,if_pos rfl,NewHistory5.packAfter,show History5.packDue 5=true from rfl,
      if_true,Nat.sub_self,NewHistory5.encode,run_append]
    exact ParityCodec5New.encodeAt_eq _ (History5.historyMap_injective w hn 0 (by decide)) _ _ legal nz'
  · rw [packFirst,if_neg hi]

 theorem packFirst_records (w : Nat → Wire) (i : Nat) :
    measurementCount (packFirst w i)=measurementCount (NewHistory5.packAfter w i) := by
  by_cases hi:i=5
  · subst i
    simp only [packFirst,if_pos rfl,NewHistory5.packAfter,show History5.packDue 5=true from rfl,
      if_true,Nat.sub_self,NewHistory5.encode]
    exact (ParityCodec5New.first_countsAt _).2.2.1.trans (ParityCodec5New.countsAt _).2.1.symm
  · rw [packFirst,if_neg hi]

 theorem forward_gen (x : Nat) (hx0 : 0<x) (hx : x<p) (n : Nat) :
    ∀i,1        ≤        i → i+n        ≤        512 → ∀(t : State)(m : List Bool), Stage base x p i t.basis →
      run (forward i n) m (pullState (sig (i-1)) t)=
        pullState (sig (i+n-1)) (run (regularForward base i n) m t) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32        ≤        2^256 := by norm_num [p]
  induction n with
  | zero => intro i _ _ t m _; simp only [forward,regularForward,run,Nat.add_zero]
  | succ n ih =>
    intro i h1 hb t m ht
    have hi : i        ≤        511 := by omega
    have z := stage_zero x i (by omega) t.basis ht
    rw [pull_step i hi t z.1 z.2]
    have cnt := (renameProgram_counts (sig i) (W.repairedTick base i++packFirst base i)).2
    have records : measurementCount (W.repairedTick base i++packFirst base i)=
        measurementCount (W.repairedTick base i++NewHistory5.packAfter base i) := by
      rw [measurementCount_append,measurementCount_append,packFirst_records]
    rw [forward,regularForward,run_append,run_append,cnt,records,OB5.run_rename i hi,
      forward_step_eq base base_pool_nodup x p i hp0 hx0 hpo hp hgap hx cop _ _ ht]
    have ht' := (step_spec base base_pool_nodup StackOB5.historyAbove x p i hp0 hx0 hpo hp hgap hx
      cop (by omega) t (m.take (measurementCount (W.repairedTick base i++NewHistory5.packAfter base i))) ht).2
    have rest := ih (i+1) (by omega) (by omega) _
      (m.drop (measurementCount (W.repairedTick base i++NewHistory5.packAfter base i))) ht'
    rw [show i+1-1=i by omega,show i+1+n-1=i+(n+1)-1 by omega] at rest
    exact rest

 theorem forward_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (forward 1 511) m s=pullState (sig 511) (run (regularForward base 1 511) m s) := by
  have h := forward_gen x hx0 hx 511 1 (le_refl _) (by omega) s m (stage_one base x p s hs)
  have e : pullState (sig (1-1)) s=s := by
    apply State.extensionality
    · rfl
    · funext q
      show s.basis (sig 0 q)=s.basis q
      rw [sig_zero]
  rw [e,show 1+511-1=511 from rfl] at h
  exact h


 theorem regularForward_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (hlo : History5.HistoryAbove w)
    (x p : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p)
    (n : Nat) : ∀i,i+n        ≤        512 → ∀(s : State)(m k : List Bool), Stage w x p i s.basis →
      run (regularForward w i n) m s=run (compactForward w i n) k s := by
  induction n with
  | zero => intro i hi s m k hs; rfl
  | succ n ih =>
    intro i hi s m k hs
    have e := step_eq w hn x p i hp0 hx0 hpo hp hgap hx hc (by omega) s
      (m.take (measurementCount (W.repairedTick w i++NewHistory5.packAfter w i)))
      (k.take (measurementCount (W.compactSkywalkTick w i++NewHistory5.packAfter w i))) hs
    have next := (compact_step_spec w hn hlo x p i hp0 hx0 hpo hp hgap hx hc (by omega)
      s (k.take (measurementCount (W.compactSkywalkTick w i++NewHistory5.packAfter w i))) hs).2
    rw [regularForward,compactForward]
    conv_lhs => rw [run_append]
    conv_rhs => rw [run_append]
    rw [e]
    exact ih (i+1) (by omega) _ _ _ next

 theorem compactForward_normalize (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hi : i+n        ≤        512) (s : State) :
    run (compactForward w i n) [] (run (NewHistory5.encodePrefix w i) [] s)=
      run (NewHistory5.encodePrefix w (i+n)) [] (run (W.compactSkywalkForward w i n) [] s) := by
  induction n generalizing i s with
  | zero => simp only [compactForward,W.compactSkywalkForward,Nat.add_zero,run]
  | succ n ih =>
    have dis := prefix_disjoint_tick w hn i i (le_refl _) (by omega)
    have commute := run_disjoint_commute (NewHistory5.encodePrefix w i) (W.compactSkywalkTick w i) dis [] [] s
    have join (t : State) : run (NewHistory5.packAfter w i) [] (run (NewHistory5.encodePrefix w i) [] t)=
        run (NewHistory5.encodePrefix w (i+1)) [] t := by
      rw [NewHistory5.encodePrefix,run_append]
      simp only [List.take_nil,List.drop_nil]
    rw [compactForward,W.compactSkywalkForward]
    simp only [run_append,List.take_nil,List.drop_nil]
    rw [←commute,join,ih (i+1) (by omega)]
    rw [show i+(n+1)=(i+1)+n by omega]

 theorem regularForward_first_normalize (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : History5.HistoryAbove w) (x p : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p)
    (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (regularForward w 1 511) m s=
      run (NewHistory5.allEncode w 102) [] (run (W.compactSkywalkForward w 1 511) [] s) := by
  have h := compactForward_normalize w hn 1 511 (by omega) s
  have empty : NewHistory5.encodePrefix w 1=[] := by
    simp [NewHistory5.encodePrefix,NewHistory5.packAfter,History5.packDue]
  rw [empty,show (1:Nat)+511=512 from rfl,NewHistory5.encodePrefix_512] at h
  simp only [run] at h
  rw [regularForward_eq w hn hlo x p hp0 hx0 hpo hp hgap hx hc 511 1 (by omega)
    s m [] (stage_one w x p s hs)]
  exact h

 theorem regularForward_snoc (w : Nat → Wire) (i n : Nat) :
    regularForward w i (n+1)=regularForward w i n++
      (W.repairedTick w (i+n)++NewHistory5.packAfter w (i+n)) := by
  induction n generalizing i with
  | zero => simp [regularForward]
  | succ n ih =>
    rw [regularForward,ih (i+1),regularForward]
    rw [show i+1+n=i+(n+1) by omega]
    simp only [List.append_assoc]

 theorem forward_snoc (i n : Nat) : forward i (n+1)=forward i n++
    renameProgram (sig (i+n)) (W.repairedTick base (i+n)++packFirst base (i+n)) := by
  induction n generalizing i with
  | zero => simp [forward]
  | succ n ih =>
    rw [forward,ih (i+1),forward]
    rw [show i+1+n=i+(n+1) by omega]
    simp only [List.append_assoc]

 theorem stage511_bits (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State)
    (hs : Stage base x p 511 s.basis) :
    ∃G : Bool, ∀q∈tickSites,s.basis q=preBits G q := by
  obtain ⟨t,ht,read⟩ := old_stage_local base base_pool_nodup x p 511 (by omega) s hs
  obtain ⟨G,bits⟩ := stage511_bits5 x hx0 hx t ht
  refine ⟨G,?_⟩
  intro q hq
  have mem : q∈(W.compactSkywalkTickLayout base 511).wires.toFinset := by
    apply W.compactSkywalkTick_support base 511 (by omega) base_pool_nodup
    have same : W.compactSkywalkTick base 511=Arithmetic.compactSkywalkTick base 511 := by decide +kernel
    rw [same]
    exact tickSites_tick q hq
  exact (read q mem).trans (bits q hq)

 theorem tick509_forced_forward (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State)
    (hs : Stage base x p 509 s.basis) (m : List Bool) :
    run tick509F m s=run (W.repairedTick base 509) m s := by
  obtain ⟨t,ht,read⟩ := old_stage_local base base_pool_nodup x p 509 (by omega) s hs
  have hp : wires tick509F⊆(W.compactSkywalkTickLayout base 509).wires.toFinset := by
    apply Finset.Subset.trans _ (W.repairedTick_support base 509 (by omega) base_pool_nodup)
    rw [tick509ExF_explicit]
    exact tick509F_sub
  exact Stack5.local_replace _ _ _ hp (W.repairedTick_support base 509 (by omega) base_pool_nodup)
    s t m m read (ECDSAAdd.Entrant.tick509_forced_forward x hx0 hx t ht m)

 theorem tick510_forced_forward (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State)
    (hs : Stage base x p 510 s.basis) (m : List Bool) :
    run tick510F m s=run (W.repairedTick base 510) m s := by
  obtain ⟨t,ht,read⟩ := old_stage_local base base_pool_nodup x p 510 (by omega) s hs
  have hp : wires tick510F⊆(W.compactSkywalkTickLayout base 510).wires.toFinset := by
    apply Finset.Subset.trans _ (W.repairedTick_support base 510 (by omega) base_pool_nodup)
    rw [tick510ExF_explicit]
    exact tick510F_sub
  exact Stack5.local_replace _ _ _ hp (W.repairedTick_support base 510 (by omega) base_pool_nodup)
    s t m m read (ECDSAAdd.Entrant.tick510_forced_forward x hx0 hx t ht m)


 theorem packFirst_support_eq (w : Nat → Wire) (i : Nat) :
    wires (packFirst w i)=wires (FirstNonzeroCodec.pack8first w i) := by
  by_cases hi:i=5
  · subst i
    have old : wires FirstNonzeroCodec.encodeFirst=Finset.range 10 := by decide +kernel
    simp only [packFirst,FirstNonzeroCodec.pack8first,if_pos rfl,
      if_true,ParityCodec5New.encodeAtFirst,FirstNonzeroCodec.encodeAtFirst,renameProgram_support,
      ParityCodec5New.first_support_exact.1,old]
  · simp only [packFirst,FirstNonzeroCodec.pack8first,if_neg hi,StackOB5.pack9_eq]
    exact NewHistory5.pack_support_eq w i

 theorem packFirst_metrics (w : Nat → Wire) (i : Nat) :
    toffoliCount (packFirst w i)=toffoliCount (FirstNonzeroCodec.pack8first w i) ∧
    measurementCount (packFirst w i)=measurementCount (FirstNonzeroCodec.pack8first w i) ∧
    Challenge.gateSlots (packFirst w i)=Challenge.gateSlots (FirstNonzeroCodec.pack8first w i)+
      2*(if History5.packDue i then 1 else 0) := by
  by_cases hi:i=5
  · subst i
    have a := ParityCodec5New.first_countsAt (History5.historyMap w 0)
    have b := renameProgram_counts (MeasuredCodec5.label (History5.historyMap w 0)) FirstNonzeroCodec.encodeFirst
    have c := ParityCodec5New.first_slotsAt (History5.historyMap w 0)
    have d := Baselines.rename_gateSlots (MeasuredCodec5.label (History5.historyMap w 0)) FirstNonzeroCodec.encodeFirst
    simp only [packFirst,FirstNonzeroCodec.pack8first,if_pos rfl,show History5.packDue 5=true from rfl,
      if_true,Nat.mul_one,FirstNonzeroCodec.encodeAtFirst]
    rw [b.1,b.2,FirstNonzeroCodec.counts.1,FirstNonzeroCodec.counts.2.2.1,d,FirstNonzeroCodec.restricted_slots.1]
    exact ⟨a.1,a.2.2.1,by rw [c.1]⟩
  · simp only [packFirst,FirstNonzeroCodec.pack8first,if_neg hi,StackOB5.pack9_eq]
    cases due : History5.packDue i
    · simp only [NewHistory5.packAfter,History5.packAfter,due,Bool.false_eq_true,if_false,
        toffoliCount,measurementCount,Challenge.gateSlots,if_false,Nat.mul_zero,Nat.add_zero]
      exact ⟨True.intro,True.intro,True.intro⟩
    · simp only [NewHistory5.packAfter,History5.packAfter,due,if_true,NewHistory5.encode,History5.encode,Nat.mul_one]
      have a := ParityCodec5New.countsAt (History5.historyMap w (i-5))
      have b := MeasuredCodec5.countsAt (History5.historyMap w (i-5))
      have c := ParityCodec5New.slotsAt (History5.historyMap w (i-5))
      have d := MeasuredCodec5.slotsAt (History5.historyMap w (i-5))
      exact ⟨a.1.trans b.1.symm,a.2.1.trans b.2.1.symm,by rw [c.1,d.1]⟩

 theorem counts_gen (i n : Nat) :
    toffoliCount (forward i n)=toffoliCount (StackOB5.forward i n) ∧
    measurementCount (forward i n)=measurementCount (StackOB5.forward i n) ∧
    Challenge.gateSlots (forward i n)=Challenge.gateSlots (StackOB5.forward i n)+2*History5.packCount i n := by
  induction n generalizing i with
  | zero => simp [forward,StackOB5.forward,History5.packCount,toffoliCount,measurementCount,Challenge.gateSlots]
  | succ n ih =>
    have r := ih (i+1)
    have p := packFirst_metrics base i
    have f := renameProgram_counts (sig i) (W.repairedTick base i++packFirst base i)
    have g := renameProgram_counts (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    have fs := Baselines.rename_gateSlots (sig i) (W.repairedTick base i++packFirst base i)
    have gs := Baselines.rename_gateSlots (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    rw [forward,StackOB5.forward]
    simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,History5.packCount] at f g fs gs ⊢
    omega

 theorem forward_regular_records (i n : Nat) :
    measurementCount (forward i n)=measurementCount (regularForward base i n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [forward,regularForward,measurementCount_append,measurementCount_append,
      (renameProgram_counts _ _).2,measurementCount_append,measurementCount_append,packFirst_records,ih]

 theorem forward_support_eq (i n : Nat) : wires (forward i n)=wires (StackOB5.forward i n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [forward,StackOB5.forward,wires_append,renameProgram_support,packFirst_support_eq,ih]

 theorem forward_physical_gen (i n : Nat) (hb : i+n       ≤       512) : GatePhysical (forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,GatePhysical]
  | succ n ih =>
    have tick := W.repairedTick_physical base i (by omega) base_pool_nodup
    have pack : GatePhysical (packFirst base i) := by
      by_cases hi:i=5
      · subst i
        simpa only [packFirst,if_pos rfl] using
          (ParityCodec5New.first_mapped_physical _ (History5.historyMap_injective base base_pool_nodup 0 (by omega))).1
      · simp only [packFirst,if_neg hi,NewHistory5.packAfter]
        split
        · have hd := History5.packDue_true i ‹History5.packDue i=true›
          exact (ParityCodec5New.physicalAt _ (History5.historyMap_injective base base_pool_nodup (i-5) (by omega))).1
        · simp [GatePhysical]
    rw [forward,gatePhysical_append]
    exact ⟨gatePhysical_rename _ (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr ⟨tick,pack⟩),ih (i+1) (by omega)⟩


 theorem packAfter_metrics (w : Nat → Wire) (i : Nat) :
    toffoliCount (NewHistory5.packAfter w i)=toffoliCount (History5.packAfter w i) ∧
    measurementCount (NewHistory5.packAfter w i)=measurementCount (History5.packAfter w i) ∧
    Challenge.gateSlots (NewHistory5.packAfter w i)=Challenge.gateSlots (History5.packAfter w i)+
      2*(if History5.packDue i then 1 else 0) := by
  cases due : History5.packDue i
  · simp [NewHistory5.packAfter,History5.packAfter,due,toffoliCount,measurementCount,Challenge.gateSlots]
  · simp only [NewHistory5.packAfter,History5.packAfter,due,if_true,NewHistory5.encode,History5.encode,Nat.mul_one]
    have a := ParityCodec5New.countsAt (History5.historyMap w (i-5))
    have b := MeasuredCodec5.countsAt (History5.historyMap w (i-5))
    have c := ParityCodec5New.slotsAt (History5.historyMap w (i-5))
    have d := MeasuredCodec5.slotsAt (History5.historyMap w (i-5))
    exact ⟨a.1.trans b.1.symm,a.2.1.trans b.2.1.symm,by rw [c.1,d.1]⟩

 def stackForward509 : Program :=
  forward 1 508++renameProgram (sig 509) (tick509F++NewHistory5.packAfter base 509)
 def stackForward510 : Program :=
  stackForward509++renameProgram (sig 510) (tick510F++NewHistory5.packAfter base 510)
 def stackForwardT : Program := stackForward510++renameProgram (sig 511) tickF

 theorem stackForward_split509 : forward 1 509=forward 1 508++
    renameProgram (sig 509) (W.repairedTick base 509++NewHistory5.packAfter base 509) := by
  rw [forward_snoc 1 508,show (1:Nat)+508=509 from rfl]
  simp only [packFirst,show ¬(509:Nat)=5 by decide,if_false]

 theorem stackForward_split510 : forward 1 510=forward 1 509++
    renameProgram (sig 510) (W.repairedTick base 510++NewHistory5.packAfter base 510) := by
  rw [forward_snoc 1 509,show (1:Nat)+509=510 from rfl]
  simp only [packFirst,show ¬(510:Nat)=5 by decide,if_false]

 theorem pack511 : packFirst base 511=[] := by decide +kernel

 theorem stackForward_splitT : forward 1 511=forward 1 510++
    renameProgram (sig 511) (W.repairedTick base 511) := by
  rw [forward_snoc 1 510,show (1:Nat)+510=511 from rfl,pack511,List.append_nil]

 theorem stackForward509_counts :
    toffoliCount stackForward509=toffoliCount ECDSAAdd.Entrant.stackForward509 ∧
    measurementCount stackForward509=measurementCount ECDSAAdd.Entrant.stackForward509 ∧
    Challenge.gateSlots stackForward509=Challenge.gateSlots ECDSAAdd.Entrant.stackForward509+202 := by
  have f := counts_gen 1 508
  have p := packAfter_metrics base 509
  have pc : History5.packCount 1 508=101 := by decide +kernel
  have due : History5.packDue 509=false := by decide
  rw [pc] at f
  simp only [due,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at p
  simp only [stackForward509,ECDSAAdd.Entrant.stackForward509,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

 theorem stackForward510_counts :
    toffoliCount stackForward510=toffoliCount ECDSAAdd.Entrant.stackForward510 ∧
    measurementCount stackForward510=measurementCount ECDSAAdd.Entrant.stackForward510 ∧
    Challenge.gateSlots stackForward510=Challenge.gateSlots ECDSAAdd.Entrant.stackForward510+204 := by
  have f := stackForward509_counts
  have p := packAfter_metrics base 510
  have due : History5.packDue 510=true := by decide
  simp only [due,if_true,Nat.mul_one] at p
  simp only [stackForward510,ECDSAAdd.Entrant.stackForward510,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

 theorem stackForwardT_counts :
    toffoliCount stackForwardT=toffoliCount ECDSAAdd.Entrant.stackForwardT ∧
    measurementCount stackForwardT=measurementCount ECDSAAdd.Entrant.stackForwardT ∧
    Challenge.gateSlots stackForwardT=Challenge.gateSlots ECDSAAdd.Entrant.stackForwardT+204 := by
  have f := stackForward510_counts
  simp only [stackForwardT,ECDSAAdd.Entrant.stackForwardT,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append]
  omega

 theorem stackForward509_records : measurementCount stackForward509=measurementCount (forward 1 509) :=
  stackForward509_counts.2.1.trans (ECDSAAdd.Entrant.stackForward509_metrics.2.1.trans (counts_gen 1 509).2.1.symm)

 theorem stackForward510_records : measurementCount stackForward510=measurementCount (forward 1 510) :=
  stackForward510_counts.2.1.trans (ECDSAAdd.Entrant.stackForward510_metrics.2.1.trans (counts_gen 1 510).2.1.symm)


theorem stackForward509_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run stackForward509 m s = run (forward 1 509) m s := by
  let k := measurementCount (regularForward base 1 508)
  let a := run (regularForward base 1 508) (m.take k) s
  have cnt := forward_regular_records 1 508
  have e0 : pullState (OB5.sig (1-1)) s = s := by
    apply State.extensionality
    · rfl
    · funext q; show s.basis (OB5.sig 0 q)=s.basis q; rw [OB5.sig_zero]
  have pref := forward_gen x hx0 hx 508 1 (by omega) (by omega) s (m.take k) (stage_one base x p s first)
  rw [e0, show 1+508-1=508 by rfl] at pref
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32     ≤     2^256 := by norm_num [p]
  have stage := ((regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 508
    hp0 hx0 hpo hp hpGap hx cop (by omega)) s (m.take k) (stage_one base x p s first)).2
  change Stage base x p 509 a.basis at stage
  have z := stage_zero x 509 (by omega) a.basis stage
  have move := OB5.pull_step 509 (by omega) a z.1 z.2
  change pullState (OB5.sig 508) a = pullState (OB5.sig 509) a at move
  change run (forward 1 508) (m.take k) s = pullState (OB5.sig 508) a at pref
  have c := tick509_counts
  rw [←tick509ExF_explicit] at c
  have mc : measurementCount tick509F = measurementCount (W.repairedTick base 509) :=
    c.2.2.2.trans c.2.1.symm
  rw [stackForward509,stackForward_split509,run_append,run_append,cnt]
  change run (renameProgram (OB5.sig 509) (tick509F ++ NewHistory5.packAfter base 509)) (m.drop k)
      (run (forward 1 508) (m.take k) s) =
    run (renameProgram (OB5.sig 509) (W.repairedTick base 509 ++ NewHistory5.packAfter base 509)) (m.drop k)
      (run (forward 1 508) (m.take k) s)
  rw [pref,move,OB5.run_rename 509 (by omega),OB5.run_rename 509 (by omega),
    run_append,run_append,mc,tick509_forced_forward x hx0 hx a stage]


theorem stackForward510_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run stackForward510 m s = run (forward 1 510) m s := by
  let k := measurementCount (regularForward base 1 509)
  let a := run (regularForward base 1 509) (m.take k) s
  have cnt := forward_regular_records 1 509
  have e0 : pullState (OB5.sig (1-1)) s = s := by
    apply State.extensionality
    · rfl
    · funext q; show s.basis (OB5.sig 0 q)=s.basis q; rw [OB5.sig_zero]
  have pref := forward_gen x hx0 hx 509 1 (by omega) (by omega) s (m.take k) (stage_one base x p s first)
  rw [e0, show 1+509-1=509 by rfl] at pref
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32     ≤     2^256 := by norm_num [p]
  have stage := ((regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 509
    hp0 hx0 hpo hp hpGap hx cop (by omega)) s (m.take k) (stage_one base x p s first)).2
  change Stage base x p 510 a.basis at stage
  have z := stage_zero x 510 (by omega) a.basis stage
  have move := OB5.pull_step 510 (by omega) a z.1 z.2
  change pullState (OB5.sig 509) a = pullState (OB5.sig 510) a at move
  change run (forward 1 509) (m.take k) s = pullState (OB5.sig 509) a at pref
  have c := tick510_counts
  rw [←tick510ExF_explicit] at c
  have mc : measurementCount tick510F = measurementCount (W.repairedTick base 510) :=
    c.2.2.2.1.trans c.2.1.symm
  rw [stackForward510,stackForward_split510,run_append,run_append,stackForward509_records,cnt,
    stackForward509_run x hx0 hx s _ first]
  change run (renameProgram (OB5.sig 510) (tick510F ++ NewHistory5.packAfter base 510)) (m.drop k)
      (run (forward 1 509) (m.take k) s) =
    run (renameProgram (OB5.sig 510) (W.repairedTick base 510 ++ NewHistory5.packAfter base 510)) (m.drop k)
      (run (forward 1 509) (m.take k) s)
  rw [pref,move,OB5.run_rename 510 (by omega),OB5.run_rename 510 (by omega),
    run_append,run_append,mc,tick510_forced_forward x hx0 hx a stage]


theorem stackForwardT_run (_hn : (skywalkSharedWires base).Nodup) (_hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run stackForwardT m s = run (forward 1 511) m s := by
  let k := measurementCount (regularForward base 1 510)
  let a := run (regularForward base 1 510) (m.take k) s
  have cnt := forward_regular_records 1 510
  have e0 : pullState (OB5.sig (1-1)) s = s := by
    apply State.extensionality
    · rfl
    · funext q; show s.basis (OB5.sig 0 q)=s.basis q; rw [OB5.sig_zero]
  have pref := forward_gen x hx0 hx 510 1 (by omega) (by omega) s (m.take k) (stage_one base x p s first)
  rw [e0, show 1+510-1=510 by rfl] at pref
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32     ≤     2^256 := by norm_num [p]
  have stage := ((regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 510
    hp0 hx0 hpo hp hpGap hx cop (by omega)) s (m.take k) (stage_one base x p s first)).2
  change Stage base x p 511 a.basis at stage
  have z := stage_zero x 511 (by omega) a.basis stage
  have move := OB5.pull_step 511 (by omega) a z.1 z.2
  change pullState (OB5.sig 510) a = pullState (OB5.sig 511) a at move
  obtain ⟨G,bits⟩ := stage511_bits x hx0 hx a stage
  change ∀q∈tickSites,a.basis q=preBits G q at bits
  change run (forward 1 510) (m.take k) s = pullState (OB5.sig 510) a at pref
  rw [stackForwardT,stackForward_splitT,run_append,run_append,stackForward510_records,cnt,
    stackForward510_run x hx0 hx s _ first]
  change run (renameProgram (OB5.sig 511) tickF) (m.drop k) (run (forward 1 510) (m.take k) s) =
    run (renameProgram (OB5.sig 511) (W.repairedTick base 511)) (m.drop k)
      (run (forward 1 510) (m.take k) s)
  rw [pref,move,OB5.run_rename 511 (by omega),OB5.run_rename 511 (by omega),
    repaired511_forced G a bits,tickF_run]



 theorem stackForward509_support_eq : wires stackForward509=wires ECDSAAdd.Entrant.stackForward509 := by
  simp only [stackForward509,ECDSAAdd.Entrant.stackForward509,wires_append,renameProgram_support,
    forward_support_eq,NewHistory5.pack_support_eq]

 theorem stackForward510_support_eq : wires stackForward510=wires ECDSAAdd.Entrant.stackForward510 := by
  simp only [stackForward510,ECDSAAdd.Entrant.stackForward510,wires_append,renameProgram_support,
    stackForward509_support_eq,NewHistory5.pack_support_eq]

 theorem stackForwardT_support_eq : wires stackForwardT=wires ECDSAAdd.Entrant.stackForwardT := by
  simp only [stackForwardT,ECDSAAdd.Entrant.stackForwardT,wires_append,stackForward510_support_eq]

 theorem stackForwardT_subset : wires stackForwardT⊆wires (StackOB5.forward 1 511) := by
  rw [stackForwardT_support_eq]
  exact ECDSAAdd.Entrant.stackForwardT_subset

 theorem stackForwardT_support : wires stackForwardT⊆StackOB5.integerSites :=
  stackForwardT_subset.trans StackOB5.forward_support

 theorem stackForwardT_physical : GatePhysical stackForwardT := by
  have tf : GatePhysical tickF := by simp [tickF,base,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  have pk : GatePhysical (NewHistory5.packAfter base 510) := by
    simp only [NewHistory5.packAfter,show History5.packDue 510=true from rfl,if_true,NewHistory5.encode]
    exact (ParityCodec5New.physicalAt _ (History5.historyMap_injective base base_pool_nodup (510-5) (by omega))).1
  have pk9 : GatePhysical (NewHistory5.packAfter base 509) := by
    simp [NewHistory5.packAfter,History5.packDue,GatePhysical]
  have blk := gatePhysical_rename _ (OB5.sig_injective 510 (by omega)) _
    ((gatePhysical_append tick510F (NewHistory5.packAfter base 510)).mpr ⟨tick510_physical.1,pk⟩)
  have blk9 := gatePhysical_rename _ (OB5.sig_injective 509 (by omega)) _
    ((gatePhysical_append tick509F (NewHistory5.packAfter base 509)).mpr ⟨tick509_physical,pk9⟩)
  exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr
    ⟨(gatePhysical_append _ _).mpr ⟨forward_physical_gen 1 508 (by omega),blk9⟩,blk⟩,
    gatePhysical_rename _ (OB5.sig_injective 511 (by omega)) _ tf⟩

 theorem rawForward_old_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x prime : Nat) (hp0 : 0<prime) (hx0 : 0<x) (hpo : prime%2=1) (hp : prime<2^256)
    (hgap : prime+2^32     ≤     2^256) (hx : x<prime) (hc : x.Coprime prime)
    (s : State) (m n : List Bool)
    (hs : Arithmetic.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (prime:Int)) 1 s.basis) :
    run (W.compactSkywalkForward w 1 511) m s=run (Arithmetic.compactSkywalkForward w 1 511) n s := by
  have fw := W.compactSkywalkForward_spec w hn x prime 1 511 hp0 hx0 hpo hp hgap hx hc (by omega) s m
    ((W.compactSkywalkStage_one w _ s.basis).mpr hs)
  have fo := Arithmetic.compactSkywalkForward_spec w hn x prime 1 511 hp0 hx0 hpo hp hx hc (by omega) s n hs
  have tw := (Arithmetic.compactSkywalkStage_terminal w hn x prime hp0 hx0 hpo hp hx hc _
    ((W.compactSkywalkStage_eq w _ 512 W.narrowSkywalkRouteWidth_endpoints.2.2.1 _).mp fw.2)).2
  have oldTerminal :=  (Arithmetic.compactSkywalkStage_terminal w hn x prime hp0 hx0 hpo hp hx hc _ fo.2).2
  apply State.extensionality
  · exact fw.1.trans fo.1.symm
  · funext q
    by_cases hq:q∈skywalkPoolWires w
    · exact skywalkIntegerStage_agrees w _ 512 (by omega) _ _ tw oldTerminal q hq
    · rw [W.compactSkywalkForward_frame w hn 1 511 (by omega) s m q hq,
        Arithmetic.compactSkywalkForward_frame w hn 1 511 (by omega) s n q hq]


attribute [local irreducible] run wires NewHistory5.allEncode literalSkywalkSeed
  Arithmetic.compactSkywalkForward W.compactSkywalkForward NativeFirstDirect.forward
  NativeFirstDirect.reference skywalkArithmeticClear regularForward stackForwardT forward compactForward

 theorem stackForwardT_boundary (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run stackForwardT m s=pullState (sig 511) (run (NewHistory5.allEncode base 102) []
      (run (W.compactSkywalkForward base 1 511) [] s)) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32   ≤   2^256 := by norm_num [p]
  exact (stackForwardT_run hn hlo x hx0 hx s m hs).trans ((forward_run x hx0 hx s m hs).trans
    (congrArg (pullState (sig 511))
      (regularForward_first_normalize base base_pool_nodup hlo x p hp0 hx0 hpo hp hgap hx cop s m hs)))

open DirectSkywalk CompressedFieldSupport NativeFirstDirect OffsetBorrowedCanonical History5

 theorem encoder_clear_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    Disjoint (wires (NewHistory5.allEncode w 102)) (wires (skywalkArithmeticClear w)) := by
  rw [NewHistory5.allEncode_support_eq]
  exact Kernel5.encoder_clear_disjoint w hn

theorem preparation_facts (hn : (skywalkSharedWires base).Nodup)
    (hlo : HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (s1 s2 s3 : State)
    (hs1 : run (NativeFirstDirect.forward base) m1 s=s1)
    (hs2 : run (regularForward base 1 511) m2 s1=s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2=s3)
    (first : CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis) :
    ∃origin:State,PreparationFacts x Y s origin ∧ History5.RawLegal base 102 origin.basis ∧
      origin.phase=s3.phase ∧ s3=run (NewHistory5.allEncode base 102) [] origin ∧
      NewHistory5.EncodedCanonicalFrame5 origin.basis Y 0 s3 := by
  have hp0 : 0 < p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p < 2^256 := by norm_num [p]
  have cop := arith_coprime x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have ready := caller_ready base hn x Y.val s.basis hin
  let oldSeed := run (literalSkywalkSeed (literalSkywalkPoolSeed base) p) [] s
  have seedEq : run (literalSkywalkSeed (literalSkywalkPoolSeed base) p) [] s=oldSeed := rfl
  have reference := forward_reference_eq base pool x hx s m1 [] ready.1 ready.2
  have referenceEq : run (NativeFirstDirect.reference base) [] s=
      run (compactSkywalkTick base 0) [] oldSeed := by
    rw [NativeFirstDirect.reference,run_append]
    simp only [List.take_nil,List.drop_nil]
    rfl
  have firstEq : s1=run (compactSkywalkTick base 0) [] oldSeed :=
    hs1.symm.trans (reference.trans referenceEq)
  let rawFinal := run (compactSkywalkForward base 0 512) [] oldSeed
  have rawJoin : rawFinal=run (compactSkywalkForward base 1 511) [] s1 := by
    dsimp only [rawFinal]
    rw [compactSkywalkForward,run_append]
    simp only [List.take_nil,List.drop_nil]
    rw [←firstEq]
  have rawStep := compactSkywalkForward_spec base pool x p 1 511 hp0 hx0 hpo hp hx cop
    (by omega) s1 [] first
  have s2Encoded : s2=run (NewHistory5.allEncode base 102) [] rawFinal := by
    rw [←hs2,regularForward_first_normalize base pool hlo x p hp0 hx0 hpo hp (by norm_num [p]) hx cop
      s1 m2 ((W.compactSkywalkStage_one base _ s1.basis).mpr first),
      rawForward_old_eq base pool x p hp0 hx0 hpo hp (by norm_num [p]) hx cop s1 [] [] first,←rawJoin]
  let origin := run (skywalkArithmeticClear base) m3 rawFinal
  have facts := rawPreparation_facts hn ho x Y hx0 hx s [] [] m3 hin oldSeed rawFinal origin seedEq rfl rfl
  have encoded : s3=run (NewHistory5.allEncode base 102) [] origin := by
    rw [←hs3,s2Encoded]
    exact (run_disjoint_commute _ _ (encoder_clear_disjoint base pool) [] m3 rawFinal).symm
  have phase : origin.phase=s3.phase := by
    rw [encoded]
    exact (NewHistory5.allEncode_zero_phase base pool 102 (by decide) origin).symm
  have legalBefore : History5.RawLegal base 102 rawFinal.basis := by
    rw [rawJoin]
    exact rawLegal_of_compactStage base pool x p 512 102 hp0 hpo (by omega) (by omega)
      _ rawStep.2
  have legal := Kernel5.clear_raw_legal5 base pool rawFinal origin m3 rfl legalBefore
  refine ⟨origin,facts,legal,phase,encoded,origin,phase,?_,encoded⟩
  exact ⟨facts.targetValue,by simpa only [ZMod.val_zero] using facts.sourceZero,fun _ _ _ => rfl⟩



attribute [local irreducible] NewHistory5.encodePrefix OB5.sig

 theorem final_prefix_keep (raw : State) (l : Nat) (hl : l=1026 ∨ 1539   ≤   l) :
    (run (NewHistory5.encodePrefix base 512) [] raw).basis (base l)=raw.basis (base l) := by
  apply run_preserves_outside
  intro hm
  rw [NewHistory5.prefix_support_eq] at hm
  obtain ⟨j,hj,hr⟩ := StackOB5Base.encodePrefix_mem 512 (by omega) _ hm
  have := base_injective hj
  omega

 theorem terminal_host_bits (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State)
    (hs : Stage base x p 512 s.basis) :
    s.basis (base 1026)=false ∧ s.basis (base 1541)=false ∧ s.basis (base 1539)=false := by
  obtain ⟨raw,stage,eq⟩ := hs
  have fields := (W.compactSkywalkStage_fields_iff base _ 512 (by omega) base_pool_nodup raw.basis).mp stage
  have mem : base 1026∈(W.compactSkywalkSignPoolB base 512).released := by decide +kernel
  have clean1026 := stage.2.2 _ mem
  have carry : regValue (wireBlock base 1540 257) raw.basis=0 := fields.2.2.2.2.2.1
  have clean1541 : raw.basis (base 1541)=false := (regValue_zero _ _).mp carry _ (by decide +kernel)
  have bit := (fields.2.2.2.1 511 (by omega)).2
  rw [SkywalkTrace.code511 x hx0 hx] at bit
  exact ⟨((congrFun eq (base 1026)).trans (final_prefix_keep raw 1026 (Or.inl rfl))).trans clean1026,
    ((congrFun eq (base 1541)).trans (final_prefix_keep raw 1541 (Or.inr (by omega)))).trans clean1541,
    ((congrFun eq (base 1539)).trans (final_prefix_keep raw 1539 (Or.inr (by omega)))).trans bit⟩

 theorem forward_host_bits (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    (run stackForwardT m s).basis (base 1026)=false ∧
    (run stackForwardT m s).basis (base 1541)=false ∧
    (run stackForwardT m s).basis (base 1542)=false := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  obtain ⟨t,ht⟩ : ∃t : State,run (regularForward base 1 511) m s=t := ⟨_,rfl⟩
  have stage : Stage base x p 512 t.basis := by
    have raw := (regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 511 hp0 hx0 hpo hp hgap hx cop
      (by omega) s m (stage_one base x p s hs)).2
    rw [ht] at raw
    exact raw
  have bits := terminal_host_bits x hx0 hx t stage
  have eq : run stackForwardT m s=pullState (sig 511) t := by
    rw [←ht]
    exact (stackForwardT_run hn StackOB5.historyAbove x hx0 hx s m hs).trans (forward_run x hx0 hx s m hs)
  have fixed0 : sig 511 (base 1026)=base 1026 := by decide +kernel
  have fixed1 : sig 511 (base 1541)=base 1541 := by decide +kernel
  have fixed2 : sig 511 (base 1542)=base 1539 := by decide +kernel
  rw [eq]
  change t.basis (sig 511 (base 1026))=false ∧ t.basis (sig 511 (base 1541))=false ∧
    t.basis (sig 511 (base 1542))=false
  rw [fixed0,fixed1,fixed2]
  exact bits


 theorem forward_clear_zero (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m2 m3 : List Bool)
    (hs : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    let out := run (skywalkArithmeticClear base) m3 (run stackForwardT m2 s)
    out.basis (base 1026)=false ∧ out.basis (base 1541)=false ∧ out.basis (base 1542)=false := by
  have bits := forward_host_bits hn x hx0 hx s m2 hs
  have keep (l : Nat) (hl : l=1026 ∨ l=1541 ∨ l=1542) :
      (run (skywalkArithmeticClear base) m3 (run stackForwardT m2 s)).basis (base l)=
        (run stackForwardT m2 s).basis (base l) := by
    apply run_preserves_outside
    intro hm
    rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at hm
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h|h|h
    all_goals have := base_injective h; omega
  dsimp only
  rw [keep 1026 (by simp),keep 1541 (by simp),keep 1542 (by simp)]
  exact bits


end ECDSAAdd.Entrant.NewStackOB5

end

-- Public component FrontierEntry1591Inverse.lean
section
/-! The new history decoder precedes each unchanged reverse integer tick.
The final parity restore must complete before this program starts. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.NewStackOB5
open Arithmetic MappedCompressed Secp256k1 OB5

def unpackFirst (w : Nat → Wire) (i : Nat) : Program :=
  if i=5 then ParityCodec5New.decodeAtFirst (History5.historyMap w 0)
  else NewHistory5.decodeBefore w i

def regularReverse (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => regularReverse w (i+1) n ++
      (NewHistory5.decodeBefore w i ++ W.ReverseCarry.compactReceiverTick w i)

def reverse (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => reverse (i+1) n ++ renameProgram (sig i)
      (unpackFirst base i ++ W.ReverseCarry.compactReceiverTick base i)

def stackReverse510 : Program :=
  renameProgram (sig 510) (NewHistory5.decodeBefore base 510 ++ tick510R) ++ reverse 1 509

def stackReverseT : Program := renameProgram (sig 511) tickR ++ stackReverse510

attribute [local irreducible] run wires measurementCount regularForward regularReverse reverse
  stackForwardT stackReverseT stackReverse510
  W.repairedTick W.compactSkywalkTick W.ReverseCarry.compactReceiverTick
  ParityCodec5New.encodeAt ParityCodec5New.decodeAt ParityCodec5New.encodeAtFirst ParityCodec5New.decodeAtFirst

theorem regularReverse_snoc (w : Nat → Wire) (i n : Nat) :
    regularReverse w i (n+1)=
      (NewHistory5.decodeBefore w (i+n) ++ W.ReverseCarry.compactReceiverTick w (i+n)) ++
        regularReverse w i n := by
  induction n generalizing i with
  | zero => simp [regularReverse]
  | succ n ih =>
    rw [regularReverse,ih (i+1),regularReverse]
    rw [show i+1+n=i+(n+1) by omega]
    simp only [List.append_assoc]

theorem reverse_snoc (i n : Nat) : reverse i (n+1)=
    renameProgram (sig (i+n))
      (unpackFirst base (i+n) ++ W.ReverseCarry.compactReceiverTick base (i+n)) ++
        reverse i n := by
  induction n generalizing i with
  | zero => simp [reverse]
  | succ n ih =>
    rw [reverse,ih (i+1),reverse]
    rw [show i+1+n=i+(n+1) by omega]
    simp only [List.append_assoc]

theorem unpack511 : unpackFirst base 511=[] := by decide +kernel

theorem reverse_split511 : reverse 1 511=
    renameProgram (sig 511) (W.ReverseCarry.compactReceiverTick base 511) ++ reverse 1 510 := by
  rw [reverse_snoc 1 510,show 1+510=511 by rfl,unpack511,List.nil_append]

theorem reverse_split510 : reverse 1 510=
    renameProgram (sig 510)
      (NewHistory5.decodeBefore base 510 ++ W.ReverseCarry.compactReceiverTick base 510) ++
        reverse 1 509 := by
  have packet : unpackFirst base 510=NewHistory5.decodeBefore base 510 := by
    unfold unpackFirst
    exact if_neg (by decide)
  exact (reverse_snoc 1 509).trans (congrArg
    (fun P : Program => renameProgram (sig 510)
      (P ++ W.ReverseCarry.compactReceiverTick base 510) ++ reverse 1 509) packet)

theorem decodeBefore_support_eq (w : Nat → Wire) (i : Nat) :
    wires (NewHistory5.decodeBefore w i)=wires (History5.decodeBefore w i) := by
  unfold NewHistory5.decodeBefore History5.decodeBefore
  split <;> simp only [NewHistory5.decode_support_eq]

theorem regularReverse_support_eq (w : Nat → Wire) (i n : Nat) :
    wires (regularReverse w i n)=wires (Stack5.reverse5 w i n) := by
  induction n generalizing i with
  | zero => simp only [regularReverse,Stack5.reverse5]
  | succ n ih =>
    simp only [regularReverse,Stack5.reverse5,wires_append,ih,decodeBefore_support_eq,
      Finset.union_assoc]

theorem regularReverse_pool (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hi : i+n  ≤  512) :
    wires (regularReverse w i n)⊆(skywalkPoolWires w).toFinset := by
  rw [regularReverse_support_eq]
  exact (Stack5.support w hn i n hi).2.trans (History5.integerSites5_pool w)

theorem untick_pool (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i<512) :
    wires (NewHistory5.decodeBefore w i ++ W.ReverseCarry.compactReceiverTick w i)⊆
      (skywalkPoolWires w).toFinset := by
  have a := regularReverse_pool w hn i 1 (by omega)
  simpa only [regularReverse,wires_append,wires,Finset.empty_union] using a

theorem oneStep_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32  ≤  2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512)
    (t : State) (ht : Stage w x p i t.basis) (mE mD : List Bool) :
    run (NewHistory5.decodeBefore w i ++ W.ReverseCarry.compactReceiverTick w i) mD
      (run (W.repairedTick w i ++ NewHistory5.packAfter w i) mE t)=t := by
  rw [step_eq w hn x p i hp0 hx0 hpo hp hgap hx hc hi t mE [] ht]
  obtain ⟨raw,hraw,hbits⟩ := ht
  have dis := prefix_disjoint_layout w hn i i (Nat.le_refl i) hi
  have read : ∀q∈(W.compactSkywalkTickLayout w i).wires,t.basis q=raw.basis q := by
    intro q hq
    rw [hbits]
    exact run_preserves_outside _ _ _ q
      (fun he => Finset.disjoint_left.mp dis he (List.mem_toFinset.mpr hq))
  have loc := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hgap hx hc hi raw hraw
  have hh : t.basis (W.compactSkywalkTickLayout w i).history=false := by
    rw [read _ (by simp [SkywalkIntegerLayout.wires])]
    exact loc.2.2.2.2.1
  have clean : regValue (W.compactSkywalkTickLayout w i).carry t.basis=0 := by
    rw [regValue_congr _ t.basis raw.basis (by
      intro q hq
      exact read q (by simp only [SkywalkIntegerLayout.wires,List.mem_append,List.mem_cons]; tauto))]
    exact loc.2.2.2.2.2
  have rt := W.ReverseCarry.compactReceiverTick_roundtrip w i hi hn t []
    (mD.drop (measurementCount (NewHistory5.decodeBefore w i))) hh clean
  have dp : run (NewHistory5.decodeBefore w i)
      (mD.take (measurementCount (NewHistory5.decodeBefore w i)))
      (run (NewHistory5.packAfter w i) [] (run (W.compactSkywalkTick w i) [] t))=
        run (W.compactSkywalkTick w i) [] t := by
    cases due : History5.packDue i
    · simp only [NewHistory5.packAfter,NewHistory5.decodeBefore,due,Bool.false_eq_true,if_false,run]
    · have hd := History5.packDue_true i due
      have legal := tick_pack_legal w hn x p i hp0 hx0 hpo hp hgap hx hc hi t [] ⟨raw,hraw,hbits⟩ due
      simpa only [NewHistory5.packAfter,NewHistory5.decodeBefore,due,if_true,NewHistory5.encode,NewHistory5.decode]
        using ParityCodec5New.roundtripAt (History5.historyMap w (i-5))
          (History5.historyMap_injective w hn (i-5) (by omega)) _ [] _ legal
  rw [run_append,run_append]
  simp only [List.take_nil,List.drop_nil]
  rw [dp]
  exact rt

theorem regularReverse_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : History5.HistoryAbove w) (x p : Nat)
    (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hgap : p+2^32  ≤  2^256) (hx : x<p) (hc : x.Coprime p) (n : Nat) :
    ∀i,i+n  ≤  512 → ∀(s : State)(mE mD : List Bool), Stage w x p i s.basis →
      run (regularReverse w i n) mD (run (regularForward w i n) mE s)=s := by
  induction n with
  | zero => intro i hi s mE mD hs; simp only [regularForward,regularReverse,run]
  | succ n ih =>
    intro i hi s mE mD hs
    have next := (step_spec w hn hlo x p i hp0 hx0 hpo hp hgap hx hc (by omega) s
      (mE.take (measurementCount (W.repairedTick w i ++ NewHistory5.packAfter w i))) hs).2
    rw [regularReverse,run_append]
    conv in (run (regularForward w i (n+1)) mE s) => rw [regularForward,run_append]
    rw [ih (i+1) (by omega) _ _ _ next]
    exact oneStep_roundtrip w hn x p i hp0 hx0 hpo hp hgap hx hc (by omega) s hs _ _

theorem unpack_measurements (w : Nat → Wire) (i : Nat) :
    measurementCount (unpackFirst w i)=measurementCount (NewHistory5.decodeBefore w i) := by
  by_cases hi : i=5
  · subst i
    have due : History5.packDue 5=true := by decide
    simp only [unpackFirst,if_pos rfl,NewHistory5.decodeBefore,due,if_true,
      Nat.sub_self,NewHistory5.decode]
    exact (ParityCodec5New.first_countsAt _).2.2.2.trans (ParityCodec5New.countsAt _).2.2.2.symm
  · simp only [unpackFirst,if_neg hi]

theorem reverse_measurements (i n : Nat) :
    measurementCount (reverse i n)=measurementCount (regularReverse base i n) := by
  induction n generalizing i with
  | zero => simp only [reverse,regularReverse]
  | succ n ih =>
    simp only [reverse,regularReverse,measurementCount_append,
      (renameProgram_counts _ _).2,ih,unpack_measurements]

theorem unpack_support_eq (w : Nat → Wire) (i : Nat) :
    wires (unpackFirst w i)=wires (FirstNonzeroCodec.unpack9first w i) := by
  by_cases hi : i=5
  · subst i
    simp only [unpackFirst,FirstNonzeroCodec.unpack9first,if_true,
      ParityCodec5New.decodeAtFirst,FirstNonzeroCodec.decodeAtFirst,renameProgram_support]
    have h : wires ParityCodec5New.decodeFirst=wires FirstNonzeroCodec.decodeFirst := by decide +kernel
    exact congrArg (Finset.image (ParityCodec5New.label (History5.historyMap w 0))) h
  · simp only [unpackFirst,FirstNonzeroCodec.unpack9first,if_neg hi,StackOB5.unpack11_eq,
      decodeBefore_support_eq]

theorem reverse_support_eq (i n : Nat) :
    wires (reverse i n)=wires (StackOB5.reverse i n) := by
  induction n generalizing i with
  | zero => simp only [reverse,StackOB5.reverse]
  | succ n ih =>
    simp only [reverse,StackOB5.reverse,wires_append,renameProgram_support,ih,unpack_support_eq]

theorem reverse_pool (i n : Nat) (h1 : 1  ≤  i) (hi : i+n  ≤  512) :
    wires (reverse i n)⊆(skywalkPoolWires base).toFinset := by
  rw [reverse_support_eq]
  intro q hq
  have good := (StackOB5.support_gen i n h1 hi).2 q hq
  obtain ⟨j,rfl,hj⟩ := (StackOB5Base.integerSites_mem q).mp good
  exact List.mem_toFinset.mpr (StackOB5Base.base_pool j (by omega))

theorem first_stage_old (w : Nat → Wire) (x p : Nat) (s : State)
    (hs : Stage w x p 5 s.basis) : W.CompressedCompactStage5 w x p 5 s.basis := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  refine ⟨raw,hraw,?_⟩
  have eNew : NewHistory5.encodePrefix w 5=[] := by
    simp [NewHistory5.encodePrefix,NewHistory5.packAfter,History5.packDue]
  have eOld : History5.encodePrefix w 5=[] := by
    simp [History5.encodePrefix,History5.packAfter,History5.packDue]
  simpa only [eNew,eOld] using hbits

theorem first_decode_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32  ≤  2^256) (hx : x<p) (hc : x.Coprime p)
    (t u : State) (mE mD : List Bool) (hs : Stage w x p 5 t.basis)
    (hb : ∀q∈skywalkPoolWires w,u.basis q=
      (run (W.repairedTick w 5 ++ NewHistory5.packAfter w 5) mE t).basis q) :
    run (ParityCodec5New.decodeAtFirst (History5.historyMap w 0)) mD u=
      run (ParityCodec5New.decodeAt (History5.historyMap w 0)) mD u := by
  have old := first_stage_old w x p t hs
  have hr := FirstNonzeroCodec.w_first_tick_stage w hn x p hp0 hx0 hpo hp hgap hx hc t
    (mE.take (measurementCount (W.repairedTick w 5))) old
  generalize hraw : run (W.repairedTick w 5)
    (mE.take (measurementCount (W.repairedTick w 5))) t=raw at hr
  have legal := FirstNonzeroCodec.w_stage_first_legal w hn x p 6 hp0 hpo
    (by decide) (by decide) raw.basis hr
  have nz := FirstNonzeroCodec.w_first_nonzero w hn x p 6 hp0 hpo hx
    (by decide) (by decide) raw.basis hr
  have nz' : raw.basis (History5.historyMap w 0 0)=true ∨
      raw.basis (History5.historyMap w 0 1)=true := by
    simpa [History5.historyMap,History5.historyId,Bool.or_eq_true] using nz
  have due : History5.packDue 5=true := by decide
  apply ParityCodec5New.decodeAt_eq_on_pool _
    (History5.historyMap_injective w hn 0 (by decide)) raw u
    (mE.drop (measurementCount (W.repairedTick w 5))) mD legal nz'
  intro q hq
  have same := hb q (List.mem_toFinset.mp (FirstNonzeroCodec.first_ports_pool w hq))
  simpa only [run_append,NewHistory5.packAfter,due,if_true,Nat.sub_self,
    NewHistory5.encode,hraw] using same

theorem reverse_step_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32  ≤  2^256) (hx : x<p) (hc : x.Coprime p)
    (t u : State) (mE mD : List Bool) (hs : Stage w x p i t.basis)
    (hb : ∀q∈skywalkPoolWires w,u.basis q=
      (run (W.repairedTick w i ++ NewHistory5.packAfter w i) mE t).basis q) :
    run (unpackFirst w i ++ W.ReverseCarry.compactReceiverTick w i) mD u=
      run (NewHistory5.decodeBefore w i ++ W.ReverseCarry.compactReceiverTick w i) mD u := by
  by_cases hi : i=5
  · subst i
    have due : History5.packDue 5=true := by decide
    have he := first_decode_eq w hn x p hp0 hx0 hpo hp hgap hx hc t u mE
      (mD.take (measurementCount (NewHistory5.decodeBefore w 5))) hs hb
    rw [run_append,run_append,unpack_measurements]
    simpa only [unpackFirst,if_pos rfl,NewHistory5.decodeBefore,due,if_true,
      Nat.sub_self,NewHistory5.decode] using congrArg
        (run (W.ReverseCarry.compactReceiverTick w 5)
          (mD.drop (measurementCount (NewHistory5.decodeBefore w 5)))) he
  · simp only [unpackFirst,if_neg hi]

theorem reverse_gen (x : Nat) (hx0 : 0<x) (hx : x<p) (n : Nat) :
    ∀i,1  ≤  i → i+n  ≤  512 → ∀(t : State)(mE : List Bool)(v : State)(mD : List Bool),
    Stage base x p i t.basis →
    (∀q∈skywalkPoolWires base,v.basis q=(run (regularForward base i n) mE t).basis q) →
    run (reverse i n) mD (pullState (sig (i+n-1)) v)=
      pullState (sig (i-1)) (run (regularReverse base i n) mD v) ∧
    ∀q∈skywalkPoolWires base,(run (regularReverse base i n) mD v).basis q=t.basis q := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  induction n with
  | zero =>
    intro i _ _ t mE v mD _ hv
    refine ⟨?_,?_⟩
    · simp only [reverse,regularReverse,run,Nat.add_zero]
    · intro q hq
      simpa only [regularReverse,regularForward,run] using hv q hq
  | succ n ih =>
    intro i h1 hb t mE v mD ht hv
    have hi : i  ≤  511 := by omega
    have e1 : reverse i (n+1)=reverse (i+1) n ++ renameProgram (sig i)
        (unpackFirst base i ++ W.ReverseCarry.compactReceiverTick base i) := by rw [reverse]
    have e2 : regularReverse base i (n+1)=regularReverse base (i+1) n ++
        (NewHistory5.decodeBefore base i ++ W.ReverseCarry.compactReceiverTick base i) := by
      rw [regularReverse]
    have e3 : regularForward base i (n+1)=
        (W.repairedTick base i ++ NewHistory5.packAfter base i) ++ regularForward base (i+1) n := by
      rw [regularForward]
    rw [e3,run_append] at hv
    have ht' := (step_spec base base_pool_nodup StackOB5.historyAbove x p i hp0 hx0 hpo hp hgap hx cop
      (by omega) t (mE.take (measurementCount (W.repairedTick base i ++ NewHistory5.packAfter base i))) ht).2
    have cnt := reverse_measurements (i+1) n
    obtain ⟨r1,r2⟩ := ih (i+1) (by omega) (by omega) _ _ v
      (mD.take (measurementCount (regularReverse base (i+1) n))) ht' hv
    rw [show i+1-1=i by omega,show i+1+n-1=i+(n+1)-1 by omega] at r1
    have rt := oneStep_roundtrip base base_pool_nodup x p i hp0 hx0 hpo hp hgap hx cop
      (by omega) t ht
      (mE.take (measurementCount (W.repairedTick base i ++ NewHistory5.packAfter base i)))
      (mD.drop (measurementCount (regularReverse base (i+1) n)))
    have agree := StackOB5Base.pool_agree _ (untick_pool base base_pool_nodup i (by omega))
      (mD.drop (measurementCount (regularReverse base (i+1) n))) _ _ r2
    rw [rt] at agree
    have z := stage_zero x i (by omega) t.basis ht
    have hz1 : (run (NewHistory5.decodeBefore base i ++ W.ReverseCarry.compactReceiverTick base i)
        (mD.drop (measurementCount (regularReverse base (i+1) n)))
        (run (regularReverse base (i+1) n)
          (mD.take (measurementCount (regularReverse base (i+1) n))) v)).basis (base (1028+i))=false :=
      (agree _ (StackOB5Base.base_pool (1028+i) (by omega))).trans z.1
    have hz2 : 257  ≤  i → (run (NewHistory5.decodeBefore base i ++ W.ReverseCarry.compactReceiverTick base i)
        (mD.drop (measurementCount (regularReverse base (i+1) n)))
        (run (regularReverse base (i+1) n)
          (mD.take (measurementCount (regularReverse base (i+1) n))) v)).basis (base (2053-i))=false :=
      fun big => (agree _ (StackOB5Base.base_pool (2053-i) (by omega))).trans (z.2 big)
    have decoder := reverse_step_eq base base_pool_nodup x p i hp0 hx0 hpo hp hgap hx cop t
      (run (regularReverse base (i+1) n) (mD.take (measurementCount (regularReverse base (i+1) n))) v)
      (mE.take (measurementCount (W.repairedTick base i ++ NewHistory5.packAfter base i)))
      (mD.drop (measurementCount (regularReverse base (i+1) n))) ht r2
    rw [e1,e2,run_append,run_append,cnt,r1,OB5.run_rename i hi,decoder,
      ←pull_step i hi _ hz1 hz2]
    exact ⟨rfl,agree⟩

theorem reverse_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE : List Bool)
    (hs : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis)
    (v : State) (hv : ∀q∈skywalkPoolWires base,
      v.basis q=(run (regularForward base 1 511) mE s).basis q) (mD : List Bool) :
    run (reverse 1 511) mD (pullState (sig 511) v)=run (regularReverse base 1 511) mD v := by
  have h := (reverse_gen x hx0 hx 511 1 (by omega) (by omega) s mE v mD
    (stage_one base x p s hs) hv).1
  have e : ∀u : State,pullState (sig (1-1)) u=u := by
    intro u
    apply State.extensionality
    · rfl
    · funext q
      show u.basis (sig 0 q)=u.basis q
      rw [sig_zero]
  rw [e,show 1+511-1=511 by rfl] at h
  exact h

theorem stage510_bits_new (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State)
    (hs : Stage base x p 510 s.basis) :
    ∃G S : Bool,∃u∈[0,1],∀q∈sites510,s.basis q=pre510 G S u q := by
  obtain ⟨t,ht,read⟩ := old_stage_local base base_pool_nodup x p 510 (by decide) s hs
  obtain ⟨G,S,u,hu,bits⟩ := ECDSAAdd.Entrant.stage510_bits x hx0 hx t ht
  refine ⟨G,S,u,hu,?_⟩
  intro q hq
  exact (read q (W.compactSkywalkTick_support base 510 (by decide) base_pool_nodup
    (sites510_tick q hq))).trans (bits q hq)

theorem block510_eq_new (x : Nat) (hx0 : 0<x) (hx : x<p) (t : State)
    (ht : Stage base x p 510 t.basis) (mE mD : List Bool) :
    run (NewHistory5.decodeBefore base 510 ++ tick510R) mD
        (run (W.repairedTick base 510 ++ NewHistory5.packAfter base 510) mE t)=
      run (NewHistory5.decodeBefore base 510 ++ W.ReverseCarry.compactReceiverTick base 510) mD
        (run (W.repairedTick base 510 ++ NewHistory5.packAfter base 510) mE t) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  obtain ⟨G,S,u,hu,bits⟩ := stage510_bits_new x hx0 hx t ht
  have due : History5.packDue 510=true := by decide
  have rep : W.repairedTick base 510=W.compactSkywalkTick base 510 := by
    rw [tick510ExF_explicit,tick510ExF_compact]
  set k := measurementCount (W.repairedTick base 510) with hk
  set d := measurementCount (NewHistory5.decodeBefore base 510) with hd
  set a := run (W.repairedTick base 510) (mE.take k) t with ha
  have legal := tick_pack_legal base base_pool_nodup x p 510 hp0 hx0 hpo hp hgap hx cop
    (by omega) t (mE.take k) ht due
  rw [←rep] at legal
  have dp : run (NewHistory5.decodeBefore base 510) (mD.take d)
      (run (NewHistory5.packAfter base 510) (mE.drop k) a)=a := by
    simpa only [NewHistory5.packAfter,NewHistory5.decodeBefore,due,if_true,NewHistory5.encode,
      NewHistory5.decode] using ParityCodec5New.roundtripAt (History5.historyMap base (510-5))
        (History5.historyMap_injective base base_pool_nodup (510-5) (by omega)) a
        (mE.drop k) (mD.take d) legal
  have abits : ∀q∈sites510,a.basis q=(run tick510ExF [] ⟨false,pre510 G S u⟩).basis q := by
    intro q hq
    rw [ha,tick510ExF_explicit,
      site_run tick510ExF sites510 (le_of_eq tick510ExF_wires) t ⟨false,pre510 G S u⟩ bits
        (mE.take k) q hq]
    exact congrFun (run_basis_records tick510ExF _ _ (mE.take k) [] rfl) q
  rw [run_append (W.repairedTick base 510),run_append (NewHistory5.decodeBefore base 510) tick510R,
    run_append (NewHistory5.decodeBefore base 510),←hk,←hd,←ha,dp,tick510ExR_explicit]
  symm
  exact forced_eqN tick510ExR tick510R sites510 _ 2 recs2 take2_mem tick510ExR_wires tick510R_wires
    (le_of_eq tick510_counts.2.2.2.2.2.1) (le_of_eq tick510_counts.2.2.2.2.2.2.2)
    (fun c hc => conc510R G S u hu c hc) a abits (mD.drop d)

theorem stackReverse510_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (u : State) (hu : ∀q∈skywalkPoolWires base,
      u.basis q=(run (regularForward base 1 510) mE s1).basis q) (mD : List Bool) :
    run stackReverse510 mD (pullState (sig 510) u)=
      run (reverse 1 510) mD (pullState (sig 510) u) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  have stage : Stage base x p 510
      (run (regularForward base 1 509)
        (mE.take (measurementCount (regularForward base 1 509))) s1).basis :=
    ((regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 509
      hp0 hx0 hpo hp hgap hx cop (by omega)) s1 _ (stage_one base x p s1 first)).2
  have fwd : run (regularForward base 1 510) mE s1=
      run (W.repairedTick base 510 ++ NewHistory5.packAfter base 510)
        (mE.drop (measurementCount (regularForward base 1 509)))
        (run (regularForward base 1 509)
          (mE.take (measurementCount (regularForward base 1 509))) s1) := by
    rw [regularForward_snoc base 1 509,show (1:Nat)+509=510 by rfl,run_append]
  rw [fwd] at hu
  generalize run (regularForward base 1 509)
    (mE.take (measurementCount (regularForward base 1 509))) s1=a at stage hu
  have c := tick510_counts
  rw [←tick510ExR_explicit] at c
  have mc : measurementCount (NewHistory5.decodeBefore base 510 ++ tick510R)=
      measurementCount (NewHistory5.decodeBefore base 510 ++ W.ReverseCarry.compactReceiverTick base 510) := by
    rw [measurementCount_append,measurementCount_append,c.2.2.2.2.2.1,c.2.2.2.2.2.2.2]
  have rn := (renameProgram_counts (sig 510) (NewHistory5.decodeBefore base 510 ++ tick510R)).2
  have ro := (renameProgram_counts (sig 510)
    (NewHistory5.decodeBefore base 510 ++ W.ReverseCarry.compactReceiverTick base 510)).2
  have pool : ∀q∈sites510,q∈(skywalkPoolWires base).toFinset :=
    fun q hq => List.mem_toFinset.mpr (sites510_pool q hq)
  have hB : wires (NewHistory5.decodeBefore base 510 ++ tick510R)⊆(skywalkPoolWires base).toFinset := by
    have dec := (History5.pack_support5 base 510 (by omega)).2.trans (History5.integerSites5_pool base)
    rw [←decodeBefore_support_eq] at dec
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,fun q hq => pool q (List.mem_toFinset.mp (tick510R_wires hq))⟩
  have inner (r : List Bool) :
      run (NewHistory5.decodeBefore base 510 ++ tick510R) r u=
        run (NewHistory5.decodeBefore base 510 ++ W.ReverseCarry.compactReceiverTick base 510) r u :=
    Stack5.local_replace _ _ _ hB (untick_pool base base_pool_nodup 510 (by omega)) u _ r r
      (fun q hq => hu q (List.mem_toFinset.mp hq)) (block510_eq_new x hx0 hx a stage _ r)
  rw [stackReverse510,reverse_split510,run_append,run_append,rn,ro,mc,
    OB5.run_rename 510 (by omega),OB5.run_rename 510 (by omega),inner]

theorem regular_pack511 : NewHistory5.packAfter base 511=[] := by decide +kernel

theorem stackReverseT_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (t5 : State) (agree : ∀q∈skywalkPoolWires base,
      t5.basis q=(run (regularForward base 1 511) mE s1).basis q) (mD : List Bool) :
    run stackReverseT mD (pullState (sig 511) t5)=
      run (reverse 1 511) (false::mD) (pullState (sig 511) t5) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  have aStage : Stage base x p 511
      (run (regularForward base 1 510)
        (mE.take (measurementCount (regularForward base 1 510))) s1).basis :=
    ((regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 510
      hp0 hx0 hpo hp hgap hx cop (by omega)) s1 _ (stage_one base x p s1 first)).2
  have whole : run (regularForward base 1 510)
      (mE.take (measurementCount (regularForward base 1 510))) s1=
        run (regularForward base 1 510) mE s1 := run_take _ mE s1
  have last : run (regularForward base 1 511) mE s1=
      run (W.repairedTick base 511) (mE.drop (measurementCount (regularForward base 1 510)))
        (run (regularForward base 1 510)
          (mE.take (measurementCount (regularForward base 1 510))) s1) := by
    rw [regularForward_snoc base 1 510,show (1:Nat)+510=511 by rfl,regular_pack511,List.append_nil,run_append]
  rw [last] at agree
  generalize run (regularForward base 1 510)
    (mE.take (measurementCount (regularForward base 1 510))) s1=a at aStage whole agree
  obtain ⟨G,bits⟩ := stage511_bits x hx0 hx a aStage
  rw [repaired511_forced G a bits] at agree
  have post : ∀q∈tickSites,t5.basis q=postBits G q := by
    intro q hq
    rw [agree q (tickSites_pool q hq)]
    exact tickF_post G a bits q hq
  have uAgree : ∀q∈skywalkPoolWires base,(run tickR [] t5).basis q=a.basis q := by
    intro q hq
    by_cases ht : q∈tickSites
    · rw [site_run tickR tickSites tickR_wires t5 ⟨false,postBits G⟩ post [] q ht,tickR_pre G q ht]
      exact (bits q ht).symm
    · have hr : q∉wires tickR := fun h => ht (List.mem_toFinset.mp (tickR_wires h))
      have hf : q∉wires tickF := fun h => ht (List.mem_toFinset.mp (tickF_wires h))
      rw [run_preserves_outside tickR [] t5 q hr,agree q hq,run_preserves_outside tickF [] a q hf]
  have z := stage_zero x 511 (by omega) a.basis aStage
  have move : pullState (sig 511) (run tickR [] t5)=pullState (sig 510) (run tickR [] t5) :=
    (OB5.pull_step 511 (by omega) _
      ((uAgree _ (StackOB5Base.base_pool _ (by omega))).trans z.1)
      (fun big => (uAgree _ (StackOB5Base.base_pool _ (by omega))).trans (z.2 big))).symm
  have cn : measurementCount (renameProgram (sig 511) tickR)=0 :=
    (renameProgram_counts (sig 511) tickR).2.trans tickR_counts.2
  have co : measurementCount (renameProgram (sig 511) (W.ReverseCarry.compactReceiverTick base 511))=1 := by
    rw [(renameProgram_counts (sig 511) (W.ReverseCarry.compactReceiverTick base 511)).2,
      receiver511_explicit]
    exact tickExR_counts.2
  rw [stackReverseT,reverse_split511,run_append,run_append,cn,co]
  simp only [List.take_zero,List.drop_zero,List.take_succ_cons,List.drop_succ_cons]
  rw [OB5.run_rename 511 (by omega),OB5.run_rename 511 (by omega),
    receiver511_forced G t5 post,tickR_run,move]
  exact stackReverse510_run x hx0 hx s1 mE first _
    (fun q hq => (uAgree q hq).trans (congrArg (fun st : State => st.basis q) whole)) mD

theorem stackReverseT_support_eq : wires stackReverseT=wires ECDSAAdd.Entrant.stackReverseT := by
  simp only [stackReverseT,ECDSAAdd.Entrant.stackReverseT,stackReverse510,
    ECDSAAdd.Entrant.stackReverse510,wires_append,renameProgram_support,reverse_support_eq,
    decodeBefore_support_eq]

theorem stackReverseT_subset : wires stackReverseT⊆wires (StackOB5.reverse 1 511) := by
  rw [stackReverseT_support_eq]
  exact ECDSAAdd.Entrant.stackReverseT_subset

theorem stackReverseT_pool : wires stackReverseT⊆(skywalkPoolWires base).toFinset := by
  have h := reverse_pool 1 511 (by omega) (by omega)
  rw [reverse_support_eq] at h
  exact stackReverseT_subset.trans h

theorem stackReverseT_outside (s : State) (m : List Bool) (q : Wire)
    (hq : q∉skywalkPoolWires base) : (run stackReverseT m s).basis q=s.basis q :=
  run_preserves_outside stackReverseT m s q
    (fun used => hq (List.mem_toFinset.mp (stackReverseT_pool used)))

theorem decodeBefore_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i<512) : GatePhysical (NewHistory5.decodeBefore w i) := by
  cases due : History5.packDue i
  · simp [NewHistory5.decodeBefore,due,GatePhysical]
  · have hd := History5.packDue_true i due
    simp only [NewHistory5.decodeBefore,due,if_true,NewHistory5.decode]
    exact (ParityCodec5New.physicalAt _ (History5.historyMap_injective w hn (i-5) (by omega))).2

theorem unpackFirst_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i<512) : GatePhysical (unpackFirst w i) := by
  by_cases h5 : i=5
  · simp only [unpackFirst,if_pos h5]
    exact (ParityCodec5New.first_mapped_physical _ (History5.historyMap_injective w hn 0 (by decide))).2
  · simp only [unpackFirst,if_neg h5]
    exact decodeBefore_physical w hn i hi

theorem reverse_physical (i n : Nat) (hi : i+n ≤ 512) : GatePhysical (reverse i n) := by
  induction n generalizing i with
  | zero => simp [reverse,GatePhysical]
  | succ n ih =>
    rw [reverse,gatePhysical_append]
    exact ⟨ih (i+1) (by omega),gatePhysical_rename _ (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr ⟨unpackFirst_physical base base_pool_nodup i (by omega),
        W.ReverseCarry.compactReceiverTick_physical base i (by omega) base_pool_nodup⟩)⟩

theorem stackReverseT_physical : GatePhysical stackReverseT := by
  have tr : GatePhysical tickR := by
    simp [tickR,base,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  have dk := decodeBefore_physical base base_pool_nodup 510 (by omega)
  have blk := gatePhysical_rename _ (sig_injective 510 (by omega)) _
    ((gatePhysical_append _ _).mpr ⟨dk,tick510_physical.2⟩)
  rw [stackReverseT,stackReverse510]
  exact (gatePhysical_append _ _).mpr ⟨gatePhysical_rename _ (sig_injective 511 (by omega)) _ tr,
    (gatePhysical_append _ _).mpr ⟨blk,reverse_physical 1 509 (by omega)⟩⟩

/-- Independent forward and inverse record lists restore the complete State. -/
theorem stack_roundtrip
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis) :
    run stackReverseT mD (run stackForwardT mE s1)=s1 := by
  have fwd : run stackForwardT mE s1=
      pullState (sig 511) (run (regularForward base 1 511) mE s1) :=
    (stackForwardT_run hn hlo x hx0 hx s1 mE first).trans (forward_run x hx0 hx s1 mE first)
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32 ≤ 2^256 := by norm_num [p]
  exact (congrArg (run stackReverseT mD) fwd).trans
    ((stackReverseT_run x hx0 hx s1 mE first
      (run (regularForward base 1 511) mE s1) (fun _ _ => rfl) mD).trans
      ((reverse_run x hx0 hx s1 mE first
        (run (regularForward base 1 511) mE s1) (fun _ _ => rfl) (false::mD)).trans
        (regularReverse_roundtrip base base_pool_nodup hlo x p hp0 hx0 hpo hp hgap hx cop
          511 1 (by omega) s1 mE (false::mD) (stage_one base x p s1 first))))

end ECDSAAdd.Entrant.NewStackOB5

end
