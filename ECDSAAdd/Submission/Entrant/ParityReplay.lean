import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Challenge.Contract
import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Submission.Entrant.OneFlag
import ECDSAAdd.Submission.Entrant.ParityCodec


-- Public component FrontierEntry1591KernelCompose.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk
attribute [local irreducible] run wires

theorem pool_away_numerator (q : Wire) (hq : q∈skywalkPoolWires base) :
    q∉wireBlock base 2056 256 := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [skywalkPoolWires,wireBlock,List.mem_range'_1] at hi
  exact OwnPlusHost.not_block _ 2056 256 (by omega)

theorem numerator_away_pool (q : Wire) (hq : q∈wireBlock base 2056 256) :
    q∉skywalkPoolWires base := by
  intro hp
  exact pool_away_numerator q hp hq

theorem paired_input (x y : Nat) (s t : State)
    (input : SkywalkArithmeticInput base x y s.basis)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q) :
    SkywalkArithmeticInput base x (regValue (wireBlock base 2056 256) t.basis) t.basis := by
  refine ⟨?_,rfl,?_⟩
  · change regValue (wireBlock base 770 256) t.basis=x
    apply (regValue_congr _ _ _ ?_).trans input.1
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact same _ (OwnPlusHost.not_block _ 2056 256 (by omega))
  · intro q hq hdx hdy
    exact (same q hdy).trans (input.2.2 q hq hdx hdy)

theorem sandwich_states (First Last : Program)
    (firstPool : wires First⊆(skywalkPoolWires base).toFinset)
    (lastPool : wires Last⊆(skywalkPoolWires base).toFinset)
    (initial before after out : State) (mp mr : List Bool) (value : Nat)
    (first : run First mp initial=before)
    (last : run Last mr after=out) (roundtrip : run Last mr before=initial)
    (result : after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q) :
    out.phase=initial.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=initial.basis q := by
  have agrees := pool_run_agrees Last (skywalkPoolWires base).toFinset lastPool mr
    after before result.1
    (fun q hq => result.2.2 q (pool_away_numerator q (List.mem_toFinset.mp hq)))
  rw [last,roundtrip] at agrees
  refine ⟨agrees.1,?_,?_⟩
  · have keep : regValue (wireBlock base 2056 256) out.basis=
        regValue (wireBlock base 2056 256) after.basis := by
      apply regValue_congr
      intro q hq
      rw [←last]
      exact run_preserves_outside _ mr after q
        (fun h => numerator_away_pool q hq (List.mem_toFinset.mp (lastPool h)))
    exact keep.trans result.2.1
  · intro q hq
    by_cases pool : q∈skywalkPoolWires base
    · exact agrees.2 q (List.mem_toFinset.mpr pool)
    · have lastKeep : out.basis q=after.basis q := by
        rw [←last]
        exact run_preserves_outside _ mr after q
          (fun h => pool (List.mem_toFinset.mp (lastPool h)))
      have firstKeep : before.basis q=initial.basis q := by
        rw [←first]
        exact run_preserves_outside _ mp initial q
          (fun h => pool (List.mem_toFinset.mp (firstPool h)))
      exact lastKeep.trans ((result.2.2 q hq).trans firstKeep)

end ECDSAAdd.Entrant.FrontierEntry1591Kernel

end

-- Public component FrontierEntry1591PhaseProgram.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1
attribute [local irreducible] run wires NewStackOB5.stackForwardT NewStackOB5.stackReverseT

def firstPhase : Program := FrontierEntry1591Native.forward base ++
  (NewStackOB5.stackForwardT ++ skywalkArithmeticClear base)

def lastPhase : Program := skywalkArithmeticClear base ++
  (NewStackOB5.stackReverseT ++ FrontierEntry1591Native.inverse base)

theorem forward_pool : wires NewStackOB5.stackForwardT⊆(skywalkPoolWires base).toFinset := by
  rw [NewStackOB5.stackForwardT_support_eq]
  exact EntryFuse.forward_pool5

theorem first_pool : wires firstPhase⊆(skywalkPoolWires base).toFinset := by
  simp only [firstPhase,wires_append,Finset.union_subset_iff]
  exact ⟨(FrontierEntry1591Native.native_pool base base_pool_nodup).1,
    forward_pool,EntryFuse.clear_pool5⟩

theorem last_pool : wires lastPhase⊆(skywalkPoolWires base).toFinset := by
  simp only [lastPhase,wires_append,Finset.union_subset_iff]
  exact ⟨EntryFuse.clear_pool5,NewStackOB5.stackReverseT_pool,
    (FrontierEntry1591Native.native_pool base base_pool_nodup).2⟩

end ECDSAAdd.Entrant.FrontierEntry1591Kernel

end

-- Public component ParityHost5.lean
section
/-! A parity-constrained history site is cleared and restored by Clifford gates. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ParityHost5
open TraceParity5 Challenge

def setup (controls : List Wire) (host : Wire) : Program :=
  controls.map (fun q => .CX q host)

theorem setup_run (controls : List Wire) (host : Wire) (s : State) (m : List Bool)
    (hh : host∉controls) :
    run (setup controls host) m s=⟨s.phase,
      writeBit s.basis host (s.basis host ^^ parity (controls.map s.basis))⟩ := by
  induction controls generalizing s with
  | nil =>
    apply State.extensionality
    · rfl
    · funext q
      by_cases qh : q=host
      · subst q;simp [setup,run,parity,writeBit]
      · simp [setup,run,parity,writeBit,qh]
  | cons q qs ih =>
    have hq : q≠host := by intro eq;exact hh (by simp [eq])
    have hs : host∉qs := fun bad => hh (by simp [bad])
    let t : State := ⟨s.phase,writeBit s.basis host (s.basis host ^^ s.basis q)⟩
    have keep : qs.map t.basis=qs.map s.basis := by
      apply List.map_congr_left
      intro a ha
      have ah : a≠host := fun e => hs (e ▸ ha)
      simp [t,writeBit,ah]
    change run (setup qs host) m t=_
    rw [ih t hs,keep]
    apply State.extensionality
    · rfl
    · funext a
      by_cases ah : a=host
      · subst a
        simp [t,writeBit,parity,Bool.xor_assoc]
      · simp [t,writeBit,ah]

/-- The input host need not be clean. Its trace parity clears it. -/
theorem setup_zero (controls : List Wire) (host : Wire) (s : State) (m : List Bool)
    (hh : host∉controls) (hp : s.basis host=parity (controls.map s.basis)) :
    run (setup controls host) m s=⟨s.phase,writeBit s.basis host false⟩ := by
  rw [setup_run controls host s m hh,hp,Bool.xor_self]

theorem restore_run (controls : List Wire) (host : Wire) (initial current : State)
    (m : List Bool) (hh : host∉controls)
    (hp : initial.basis host=parity (controls.map initial.basis))
    (hc : ∀q∈controls,current.basis q=initial.basis q)
    (hz : current.basis host=false) :
    run (setup controls host) m current=
      ⟨current.phase,writeBit current.basis host (initial.basis host)⟩ := by
  have same : controls.map current.basis=controls.map initial.basis :=
    List.map_congr_left hc
  rw [setup_run controls host current m hh,hz,same,←hp,Bool.false_xor]

/-- Both record lists are arbitrary and independent. -/
theorem setup_roundtrip (controls : List Wire) (host : Wire) (s : State)
    (m n : List Bool) (hh : host∉controls) :
    run (setup controls host) n (run (setup controls host) m s)=s := by
  rw [setup_run controls host s m hh]
  let t : State := ⟨s.phase,writeBit s.basis host
    (s.basis host ^^ parity (controls.map s.basis))⟩
  have same : controls.map t.basis=controls.map s.basis := by
    apply List.map_congr_left
    intro q hq
    have qh : q≠host := fun e => hh (e ▸ hq)
    simp [t,writeBit,qh]
  change run (setup controls host) n t=s
  rw [setup_run controls host t n hh,same]
  apply State.extensionality
  · rfl
  · funext q
    by_cases qh : q=host
    · subst q
      simp [t,writeBit,Bool.xor_assoc]
    · simp [t,writeBit,qh]

theorem setup_counts (controls : List Wire) (host : Wire) :
    toffoliCount (setup controls host)=0 ∧
      measurementCount (setup controls host)=0 ∧
      gateSlots (setup controls host)=controls.length := by
  induction controls with
  | nil => simp [setup,toffoliCount,measurementCount,gateSlots]
  | cons q qs ih =>
    refine ⟨ih.1,ih.2.1,?_⟩
    change 1+gateSlots (setup qs host)=qs.length+1
    rw [ih.2.2]
    omega

theorem setup_valid (controls : List Wire) (host : Wire) (hh : host∉controls) :
    ∀i∈setup controls host,instructionValid i := by
  intro i hi
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
  exact fun eq => hh (eq ▸ hq)

theorem setup_support (controls : List Wire) (host : Wire) :
    wires (setup controls host)⊆insert host controls.toFinset := by
  induction controls with
  | nil => simp [setup,wires]
  | cons q qs ih =>
    simp only [setup,List.map_cons,wires,Instr.wires]
    intro a ha
    rcases Finset.mem_union.mp ha with h|h
    · simp only [Finset.mem_insert,Finset.mem_singleton] at h
      simp only [Finset.mem_insert,List.mem_toFinset,List.mem_cons]
      tauto
    · have mem := ih h
      simp only [Finset.mem_insert,List.mem_toFinset] at mem
      simp only [Finset.mem_insert,List.mem_toFinset,List.mem_cons]
      tauto

def payloadControls (payload : Nat → Wire) : List Wire :=
  (List.range 816).map payload

theorem payloadControls_length (payload : Nat → Wire) :
    (payloadControls payload).length=816 := by simp [payloadControls]

/-- The packet identities are the local codec's parity theorem. The host
holds the actual penultimate flag, also after an injective wire placement. -/
theorem encoded_host_relation (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (payload : Nat → Wire) (host : Wire) (s : State)
    (hs : s.basis host=rawS x 510)
    (packets : ∀j,j<102 →
      xorRange 8 (fun i => s.basis (payload (8*j+i)))=
        xorRange 5 (fun i => rawS x (5*j+i))) :
    s.basis host=parity ((payloadControls payload).map s.basis) := by
  rw [hs]
  have whole := encoded_payload_parity x hx0 hx (fun i => s.basis (payload i)) packets
  have list := parity_range 816 (fun i => s.basis (payload i))
  simpa only [payloadControls,List.map_map,Function.comp_def] using whole.symm.trans list.symm

theorem encoded_setup_zero (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (payload : Nat → Wire) (host : Wire) (s : State) (m : List Bool)
    (hh : host∉payloadControls payload) (hs : s.basis host=rawS x 510)
    (packets : ∀j,j<102 →
      xorRange 8 (fun i => s.basis (payload (8*j+i)))=
        xorRange 5 (fun i => rawS x (5*j+i))) :
    run (setup (payloadControls payload) host) m s=
      ⟨s.phase,writeBit s.basis host false⟩ :=
  setup_zero _ _ s m hh (encoded_host_relation x hx0 hx payload host s hs packets)

/-- The field work role returns the host to zero. The restored value is the
actual raw S510, not a new constant or a clean-input assumption. -/
theorem encoded_restore_run (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (payload : Nat → Wire) (host : Wire) (initial current : State) (m : List Bool)
    (hh : host∉payloadControls payload) (hs : initial.basis host=rawS x 510)
    (packets : ∀j,j<102 →
      xorRange 8 (fun i => initial.basis (payload (8*j+i)))=
        xorRange 5 (fun i => rawS x (5*j+i)))
    (hc : ∀q∈payloadControls payload,current.basis q=initial.basis q)
    (hz : current.basis host=false) :
    run (setup (payloadControls payload) host) m current=
      ⟨current.phase,writeBit current.basis host (rawS x 510)⟩ := by
  rw [restore_run _ _ initial current m hh
    (encoded_host_relation x hx0 hx payload host initial hs packets) hc hz,hs]

theorem encoded_setup_counts (payload : Nat → Wire) (host : Wire) :
    toffoliCount (setup (payloadControls payload) host)=0 ∧
      measurementCount (setup (payloadControls payload) host)=0 ∧
      gateSlots (setup (payloadControls payload) host)=816 := by
  simpa only [payloadControls_length] using setup_counts (payloadControls payload) host

end ECDSAAdd.Entrant.ParityHost5

end

-- Public component FrontierEntry1591Boundary.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1
attribute [local irreducible] run wires NewStackOB5.stackForwardT NewHistory5.allEncode

def payloadControls : List Wire := ParityHost5.payloadControls
  (fun i => OB5.sig 511 (NewHistory5.payloadWire base i))

theorem clear_payload_free : ∀q∈payloadControls,q∉wires (skywalkArithmeticClear base) := by
  intro q hq used
  change q∈(List.range 816).map (fun i=>OB5.sig 511 (NewHistory5.payloadWire base i)) at hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  have bound := List.mem_range.mp hi
  have rawFree : NewHistory5.payloadWire base i∉wires (skywalkArithmeticClear base) := by
    unfold NewHistory5.payloadWire
    exact Kernel5.history_clear_away base base_pool_nodup (i/8) (by omega) _
  have pulled : OB5.sig 511 (OB5.sig 511 (NewHistory5.payloadWire base i))∈
      wires (renameProgram (OB5.sig 511) (skywalkArithmeticClear base)) := by
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨_,used,rfl⟩
  rw [KernelOB5.clear_rename,OB5.sig_invol 511 (by decide)] at pulled
  exact rawFree pulled

theorem clear_host_free : base 1543∉wires (skywalkArithmeticClear base) := by
  decide +kernel

theorem placed_host_parity (s : State)
    (parity : s.basis (base 1538)=TraceParity5.xorRange 816
      (fun i=>s.basis (NewHistory5.payloadWire base i))) :
    (pullState (OB5.sig 511) s).basis (base 1543)=
      TraceParity5.parity (payloadControls.map (pullState (OB5.sig 511) s).basis) := by
  have hostMap : OB5.sig 511 (base 1543)=base 1538 := by decide +kernel
  change s.basis (OB5.sig 511 (base 1543))=_
  rw [hostMap,parity]
  simp only [payloadControls,ParityHost5.payloadControls,List.map_map,Function.comp_def,
    TraceParity5.parity_range]
  apply TraceParity5.xorRange_congr
  intro i hi
  change s.basis (NewHistory5.payloadWire base i)=
    s.basis (OB5.sig 511 (OB5.sig 511 (NewHistory5.payloadWire base i)))
  rw [OB5.sig_invol 511 (by decide)]

theorem clear_host_parity (s : State) (m : List Bool)
    (parity : s.basis (base 1543)=TraceParity5.parity (payloadControls.map s.basis)) :
    (run (skywalkArithmeticClear base) m s).basis (base 1543)=TraceParity5.parity
      (payloadControls.map (run (skywalkArithmeticClear base) m s).basis) := by
  have payloadKeep : payloadControls.map (run (skywalkArithmeticClear base) m s).basis=
      payloadControls.map s.basis := by
    apply List.map_congr_left
    intro q hq
    exact run_preserves_outside _ _ _ _ (clear_payload_free q hq)
  rw [payloadKeep,run_preserves_outside _ _ _ _ clear_host_free]
  exact parity

theorem forward_clear_parity (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m2 m3 : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    let out := run (skywalkArithmeticClear base) m3 (run NewStackOB5.stackForwardT m2 s)
    out.basis (base 1543)=TraceParity5.parity (payloadControls.map out.basis) := by
  obtain ⟨raw,hraw⟩ : ∃raw : State,run (W.compactSkywalkForward base 1 511) [] s=raw := ⟨_,rfl⟩
  obtain ⟨enc,henc⟩ : ∃enc : State,run (NewHistory5.allEncode base 102) [] raw=enc := ⟨_,rfl⟩
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32 ≤ 2^256 := by norm_num [p]
  have stage : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 512 raw.basis := by
    have stage := (W.compactSkywalkForward_spec base base_pool_nodup x p 1 511
      hp0 hx0 hpo hp hgap hx cop (by omega) s [] first).2
    rw [hraw] at stage
    exact stage
  have parity := NewHistory5.encoded_host_relation base base_pool_nodup x hx0 hx raw enc stage
    (congrArg State.basis henc.symm)
  have boundary := NewStackOB5.stackForwardT_boundary hn hlo x hx0 hx s m2 first
  rw [hraw,henc] at boundary
  have placed : (run NewStackOB5.stackForwardT m2 s).basis (base 1543)=TraceParity5.parity
      (payloadControls.map (run NewStackOB5.stackForwardT m2 s).basis) := by
    rw [boundary]
    exact placed_host_parity enc parity
  exact clear_host_parity _ m3 placed

end ECDSAAdd.Entrant.FrontierEntry1591Kernel

end

-- Public component FrontierEntry1591Phases.lean (757aa6b5 repair)
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1
attribute [local irreducible] run wires NewStackOB5.stackForwardT NewStackOB5.stackReverseT
  FrontierEntry1591Native.forward FrontierEntry1591Native.inverse skywalkArithmeticClear firstPhase lastPhase

private theorem compose_records (N F C First : Program)
    (shape : First=N++(F++C)) (s : State) (m : List Bool) (P : State → Prop)
    (step : ∀mn mf mc,P (run C mc (run F mf (run N mn s)))) :
    P (run First m s) := by
  rw [shape,run_append,run_append]
  exact step _ _ _

private theorem compose_roundtrip (N F C R I : Program) (s : State) (mp mr : List Bool)
    (clearM : measurementCount C=0)
    (twice : ∀ (t : State) mc,run C [] (run C mc t)=t)
    (stack : ∀ mn mf md,run R md (run F mf (run N mn s))=run N mn s)
    (native : ∀ mn mi,run I mi (run N mn s)=s) :
    run (C++(R++I)) mr (run (N++(F++C)) mp s)=s := by
  simp only [run_append,clearM,List.take_zero,List.drop_zero]
  rw [twice,stack]
  exact native _ _

theorem phases_roundtrip (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (mp mr : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run lastPhase mr (run firstPhase mp s)=s := by
  have clearM : measurementCount (skywalkArithmeticClear base)=0 := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,measurementCount]
  have twice (t : State) (mc : List Bool) : run (skywalkArithmeticClear base) []
      (run (skywalkArithmeticClear base) mc t)=t := by
    simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
      (base 511) (base 512) (base 770) (arith_clear_gates base hn) t mc []
  have stack (mn mf md : List Bool) :
      run NewStackOB5.stackReverseT md (run NewStackOB5.stackForwardT mf
        (run (FrontierEntry1591Native.forward base) mn s))=
      run (FrontierEntry1591Native.forward base) mn s :=
    NewStackOB5.stack_roundtrip hn hlo x hx0 hx _ mf md
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [firstPhase,lastPhase] using compose_roundtrip
    (FrontierEntry1591Native.forward base) NewStackOB5.stackForwardT (skywalkArithmeticClear base)
    NewStackOB5.stackReverseT (FrontierEntry1591Native.inverse base) s mp mr clearM twice stack
    (fun mn mi => FrontierEntry1591Native.inverse_roundtrip base hn x y hx s mn mi input)

theorem raw_result (Field : Program) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (value : Nat)
    (input : SkywalkArithmeticInput base x y s.basis)
    (fieldResult : ∀mp mf,
      let before := run firstPhase mp s
      let after := run Field mf before
      after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q) :
    let out := run (FrontierEntry1591Native.kernel firstPhase Field lastPhase) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have all := run_three_states firstPhase Field lastPhase
    (fun initial out => initial=s → out.phase=s.phase ∧
      regValue (wireBlock base 2056 256) out.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q) (by
      intro initial before after out mp mf mr h1 h2 h3 eq
      subst initial
      have result := fieldResult mp mf
      dsimp only at result
      rw [h1,h2] at result
      have rt : run lastPhase mr before=s := by
        rw [←h1]
        exact phases_roundtrip hn hlo x y hx0 hx s mp mr input
      exact sandwich_states firstPhase lastPhase first_pool last_pool s before after out mp mr
        value h1 h3 rt result) s m
  simpa only [FrontierEntry1591Native.kernel,List.append_assoc] using all rfl

theorem first_work_free : base 1797∉wires firstPhase := by
  have f : base 1797∉wires NewStackOB5.stackForwardT := by
    rw [NewStackOB5.stackForwardT_support_eq]
    exact FrontierEntry1591Native.stack_work_free.1
  simpa only [firstPhase,wires_append,Finset.mem_union,not_or] using
    And.intro (FrontierEntry1591Native.avoids_work base base_pool_nodup).1
      (And.intro f FrontierEntry1591Native.clear_work_free)

theorem first_work_zero (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    (run firstPhase m s).basis (base 1797)=false :=
  (run_preserves_outside _ m s _ first_work_free).trans
    (FrontierEntry1591Native.caller_clean base hn x y s input).1

theorem first_clean (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    ∀q∈FrontierEntry1591Native.workSites,(run firstPhase m s).basis q=false := by
  refine compose_records (FrontierEntry1591Native.forward base) NewStackOB5.stackForwardT
    (skywalkArithmeticClear base) firstPhase (by unfold firstPhase;rfl) s m
    (fun out => ∀q∈FrontierEntry1591Native.workSites,out.basis q=false) ?_
  intro mn mf mc
  have stage := FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input
  have bits := NewStackOB5.forward_clear_zero hn x hx0 hx
    (run (FrontierEntry1591Native.forward base) mn s) mf mc stage
  intro q hq
  simp only [FrontierEntry1591Native.workSites,List.mem_toFinset,List.mem_cons,
    List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  · exact bits.1
  · exact bits.2.1
  · exact bits.2.2

theorem first_parity (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    let out := run firstPhase m s
    out.basis (base 1543)=TraceParity5.parity (payloadControls.map out.basis) := by
  refine compose_records (FrontierEntry1591Native.forward base) NewStackOB5.stackForwardT
    (skywalkArithmeticClear base) firstPhase (by unfold firstPhase;rfl) s m
    (fun out => out.basis (base 1543)=TraceParity5.parity (payloadControls.map out.basis)) ?_
  intro mn mf mc
  exact forward_clear_parity hn hlo x hx0 hx
    (run (FrontierEntry1591Native.forward base) mn s) mf mc
    (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)

end ECDSAAdd.Entrant.FrontierEntry1591Kernel

end

-- Public component NewFieldFrameOB5.lean
section
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

end

-- Public component FrontierEntry1591Preparation.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 History5
attribute [local irreducible] run wires NewStackOB5.stackForwardT
  NewStackOB5.regularForward NativeFirstDirect.forward FrontierEntry1591Native.forward

theorem preparation_placed (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (m1 m2 m3 : List Bool) (input : SkywalkArithmeticInput base x Y.val s.basis) :
    let a1 := run (FrontierEntry1591Native.forward base) m1 s
    let a2 := run NewStackOB5.stackForwardT m2 a1
    let a3 := run (skywalkArithmeticClear base) m3 a2
    ∃origin : State,PreparationFacts x Y s origin ∧ History5.RawLegal base 102 origin.basis ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3 := by
  let a1 := run (FrontierEntry1591Native.forward base) m1 s
  let a2 := run NewStackOB5.stackForwardT m2 a1
  let a3 := run (skywalkArithmeticClear base) m3 a2
  let t2 := run (NewStackOB5.regularForward base 1 511) m2 a1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  have h1 : run (NativeFirstDirect.forward base) m1 s=a1 :=
    (FrontierEntry1591Native.forward_run_eq base hn x Y.val hx s m1 input).symm
  have first := FrontierEntry1591Native.caller_first_stage base hn x Y.val hx0 hx s m1 input
  have firstW := FrontierEntry1591Native.caller_first_stageW base hn x Y.val hx0 hx s m1 input
  have e2 : a2=pullState (OB5.sig 511) t2 :=
    (NewStackOB5.stackForwardT_run hn hlo x hx0 hx a1 m2 firstW).trans
      (NewStackOB5.forward_run x hx0 hx a1 m2 firstW)
  have e3 : a3=pullState (OB5.sig 511) t3 := by
    change run (skywalkArithmeticClear base) m3 a2=_
    rw [e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,_,frame⟩ := NewStackOB5.preparation_facts hn hlo ho x Y hx0 hx s
    m1 m2 m3 input a1 t2 t3 h1 rfl rfl first
  refine ⟨origin,facts,legal,?_⟩
  change NewHistory5.EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) a3)
  rw [e3,OB5.pull_invol 511 (by decide)]
  exact frame

end ECDSAAdd.Entrant.FrontierEntry1591Kernel

end

-- Public component FrontierEntry1591Replay.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.FrontierReplay1591
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount

structure Context (origin : BasisState) : Prop where
  hn : (skywalkSharedWires base).Nodup
  ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base
  hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base
  hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)
  hg0 : origin (base 2409)=false
  hs0 : origin (base 2410)=false
  env : Env base origin
  legal : NewHistory5.RawLegal base 102 origin
  parity : origin (base 2312)=false

def rawReplay (divide : Bool) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => if divide then
      OneFlagCell.cell true base (base 2400) l.1.1 l.1.2 (base 2409) l.2.1 l.2.2++rawReplay true ls
    else rawReplay false ls++
      OneFlagCell.cell false base (base 2400) l.1.1 l.1.2 (base 2409) l.2.1 l.2.2

def body (divide : Bool) (j : Nat) : Program := rawReplay divide (Replay5.letters j)

def basePacket (divide : Bool) (j : Nat) : Program :=
  NewHistory5.decode base (5*j)++body divide j++NewHistory5.encode base (5*j)

def packet (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacket divide j)

def groups (divide : Bool) (j n : Nat) : Program := PacketSequence.program divide (packet divide) j n

def firstSwap : Program := OneFlagCell.selectSwap base (base 2400) (base 1028) (base 2409)
  (mixedTranscriptUnitTrace.getD 0 (false,false)).2
def firstSwapM : Program := OneFlagCell.selectMSwap base (base 2400) (base 1028) (base 2409)
  (mixedTranscriptUnitTrace.getD 0 (false,false)).2

def firstBody (divide : Bool) : Program :=
  if divide then firstSwap++rawReplay true Replay5.restLetters
  else rawReplay false Replay5.restLetters++firstSwapM

def baseFirstPacket (divide : Bool) : Program :=
  NewHistory5.decode base 0++firstBody divide++NewHistory5.encode base 0

def firstPacket (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (baseFirstPacket divide)

def rawEnd (divide : Bool) : Program :=
  Q6EndpointCell.endpoint divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1

def endPacket (divide : Bool) : Program := renameProgram (shifted Placement5.pi0) (rawEnd divide)

def logicalReplay (divide : Bool) : Program :=
  if divide then firstPacket true++groups true 1 101++endPacket true
  else endPacket false++groups false 1 101++firstPacket false

def replay (divide : Bool) : Program := renameProgram (OB5.sig 511) (logicalReplay divide)


def fieldSites : Finset Wire := (base 2409::Q6EndpointCell.ids.map base).toFinset

def readSites (start : Nat) : Finset Wire := fieldSites ∪ {base 2400,base 2410} ∪
  wires (NewHistory5.encode base start)

theorem raw_support (divide : Bool) (ls : List MixedTranscriptLetter) (W : Finset Wire)
    (hi : fieldSites⊆W) (hb : base 2400∈W) (he : base 2410∈W)
    (controls : ∀l∈ls,l.1.1∈W ∧ l.1.2∈W) : wires (rawReplay divide ls)⊆W := by
  induction ls with
  | nil => simp [rawReplay,wires]
  | cons l ls ih =>
    have c := OneFlagCell.support divide base (base 2400) l.1.1 l.1.2 (base 2409)
      l.2.1 l.2.2 W hi hb (controls l (by simp)).1 (controls l (by simp)).2
    have rest := ih (fun k hk => controls k (List.mem_cons_of_mem l hk))
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,wires_append,
      Finset.union_subset_iff] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (body divide j)⊆readSites (5*j) := by
  simpa only [readSites,OneFlagReplay.readSites,NewHistory5.encode_support_eq] using
    OneFlagReplay.body_support divide j hj

theorem readSites_sub (start : Nat) : readSites start⊆
    NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) start ∪ {base 2312} := by
  intro q hq
  simp only [readSites,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · have hp := (Q6EndpointCell.mem_ports_wires base (base 2409) q).mpr (List.mem_toFinset.mp h)
    rcases Q6EndpointCell.ports_site base (base 2409) q hp with h|h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr h)))
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr h)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem body_read_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (body divide j)⊆NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5*j) ∪ {base 2312} :=
  (body_support divide j hj).trans (readSites_sub (5*j))

theorem firstBody_support (divide : Bool) : wires (firstBody divide)⊆readSites 0 := by
  simpa only [readSites,OneFlagReplay.readSites,NewHistory5.encode_support_eq] using
    OneFlagReplay.firstBody_support divide

theorem firstBody_read_support (divide : Bool) :
    wires (firstBody divide)⊆NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} :=
  (firstBody_support divide).trans (readSites_sub 0)

theorem rawEnd_support (divide : Bool) : wires (rawEnd divide)⊆fieldSites ∪ {base 2400,base 510} := by
  apply Q6EndpointCell.endpoint_support divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1
  · exact Finset.subset_union_left
  · exact Finset.mem_union_right _ (by simp)
  · exact Finset.mem_union_right _ (by simp)

theorem rawEnd_read_support (divide : Bool) :
    wires (rawEnd divide)⊆(sharedSites base (base 2409)).toFinset∪{base 2312,base 2400,base 510} := by
  intro q hq
  rcases Finset.mem_union.mp (rawEnd_support divide hq) with h|h
  · have hp := (Q6EndpointCell.mem_ports_wires base (base 2409) q).mpr (List.mem_toFinset.mp h)
    rcases Q6EndpointCell.ports_site base (base 2409) q hp with h|h
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr h)
    · exact Finset.mem_union_right _ (by simp [h])
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    exact Finset.mem_union_right _ (by simp only [Finset.mem_insert,Finset.mem_singleton]; tauto)

theorem rawEnd_disjoint (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base) :
    Disjoint (wires (NewHistory5.allEncode base 102)) (wires (rawEnd divide)) := by
  rw [NewHistory5.allEncode_support_eq]
  exact OneFlagReplay.rawEnd_disjoint divide hn hp

private theorem q7part2_letter_layout (origin : BasisState) (ctx : Context origin)
    (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls)
    (l : MixedTranscriptLetter) (hl : l∈ls) :
    BalancedTranscriptLayout (Q6EndpointCell.ports base (base 2409))
      (base 2400) l.1.1 l.1.2 (base 2410) :=
  Q6EndpointCell.ports_transcript base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) ctx.hn
    (balancedSharedTranscriptLayout_direct base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) (hf l hl) ctx.ho)
    (ctx.ho _ (by simp)) (ctx.ho _ (by simp))

theorem raw_frame (divide : Bool) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawReplay divide ls)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) ls) (X,Y)).1)
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) ls) (X,Y)).2)) := by
  have clean := Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity
  induction ls generalizing X Y with
  | nil =>
    intro s m h
    cases divide <;> simpa only [rawReplay,directionalPayload,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,if_false,if_true,mixedTranscriptControls,List.map_nil,skywalkPayloadReplay,
      skywalkPayloadReplayInverse,run] using And.intro (Eq.refl s.phase) h
  | cons l ls ih =>
    have layout := q7part2_letter_layout origin ctx (l::ls) hf l (by simp)
    have tailLayout := fun k hk => hf k (List.mem_cons_of_mem l hk)
    cases divide
    · let Q := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) ls) (X,Y)
      have rest := ih tailLayout X Y
      have head := OneFlagCell.cell_frame_legacy false base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
        l.2.1 l.2.2 layout origin ctx.hg0 clean Q.1 Q.2
      simpa only [rawReplay,Bool.false_eq_true,if_false,directionalPayload,Bool.not_false,if_true,
        mixedTranscriptControls,List.map_cons,skywalkPayloadReplayInverse,Q6EndpointCell.payload,Q,Prod.mk.eta]
        using rest.seq head
    · let Q := skywalkPayloadCell (mixedTranscriptBit origin (base 2400) l.1.1 l.2.1)
        (mixedTranscriptBit origin (base 2400) l.1.2 l.2.2) (X,Y)
      have head := OneFlagCell.cell_frame_legacy true base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
        l.2.1 l.2.2 layout origin ctx.hg0 clean X Y
      have rest := ih tailLayout Q.1 Q.2
      simpa only [rawReplay,if_true,directionalPayload,Bool.not_true,Bool.false_eq_true,if_false,
        mixedTranscriptControls,List.map_cons,skywalkPayloadReplay,Q6EndpointCell.payload,Q,Prod.mk.eta]
        using head.seq rest

private theorem q7part2_rest_layout
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) Replay5.restLetters := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have bound := List.mem_range'_1.mp hk
  simpa only [Replay5.restLetters,tapeLetter] using
    mixedTape_getD_layout base _ _ _ hf k (by omega)

private theorem q7part2_first_layout (origin : BasisState) (ctx : Context origin) :
    BalancedTranscriptLayout (balancedSharedPorts base (base 2409))
      (base 2400) (base 0) (base 1028) (base 2410) := by
  have h := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 0 (by decide)) ctx.ho
  rw [mixedTape_base_getD 0 (by decide)] at h
  exact h

theorem packet_frame (divide : Bool) (j : Nat) (hj : j<102)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (packet divide j) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)).1
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)).2
        (run (packet divide j) m s) := by
  have raw := raw_frame divide (Replay5.letters j) (Replay5.letters_layouts ctx.hf j hj) origin ctx X Y
  have fresh := NewFieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp j hj origin X Y _ _ _ (body_read_support divide j hj) raw s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi j) (basePacket divide j)
    (fun q hq => Placement5.pi_outside j q hj hq) s m
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (packet divide j) m s=run (basePacket divide j) m s := eq
  rw [same]
  exact fresh


theorem groups_frame (divide : Bool) (j n : Nat) (bound : j+n≤102)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (groups divide j n) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin (Replay5.groupsPayload divide origin j n (X,Y)).1
        (Replay5.groupsPayload divide origin j n (X,Y)).2 (run (groups divide j n) m s) := by
  have result := PacketSequence.frame divide (packet divide) (packet divide)
    (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V)
    (fun V t => NewHistory5.EncodedFieldFrame5 base (base 2409) origin V.1 V.2 t) 102 (fun _ => rfl)
    (fun k hk V t records h => ⟨rfl,packet_frame divide k hk origin ctx V.1 V.2 t records h⟩)
    j n bound (X,Y) s m input
  exact result.2


theorem base_sign_nd : (base 2409::(Q6EndpointCell.ports base (base 2409)).r++
    (Q6EndpointCell.ports base (base 2409)).y).Nodup := by
  have away : base 2409∉Q6EndpointCell.ids.map base := by
    intro h
    obtain ⟨i,hi,he⟩ := List.mem_map.mp h
    have bound := Q6EndpointCell.ids_bound i hi
    have := base_injective he
    omega
  have hn := Q6EndpointCell.ports_nodup_injective base (base 2409) base_injective away
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil,
    Q6EndpointCell.ports_sign] at h ⊢
  omega

theorem firstBody_frame (divide : Bool) (origin : BasisState) (ctx : Context origin) (X Y : Fp)
    (hz : divide=false → (Replay5.firstPayload divide origin (X,Y)).2=0) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (firstBody divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (Replay5.firstPayload divide origin (X,Y)).1)
        (centerWord (Replay5.firstPayload divide origin (X,Y)).2)) := by
  let S := mixedTranscriptBit origin (base 2400) (base 1028) (mixedTranscriptUnitTrace.getD 0 (false,false)).2
  have nl := Q6EndpointCell.ports_transcript base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) ctx.hn (q7part2_first_layout origin ctx) (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  have hb := nl.outside (base 2400) (by simp)
  have hs := nl.outside (base 1028) (by simp)
  have hf := nl.outside (base 2409) (by simp [Q6EndpointCell.ports_sign])
  have swap := OneFlagCell.selectSwap_frame base (base 2400) (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 base_sign_nd (by decide) hb hs hf origin ctx.hg0
  cases divide
  · let V := directionalPayload true (mixedTranscriptControls origin (base 2400) Replay5.restLetters) (X,Y)
    have zero : (if S then V.1 else V.2)=0 := by
      have h := hz rfl
      have k : ∀ (b : Bool) (p : Fp×Fp), (if b then (p.2,p.1) else p).2=(if b then p.1 else p.2) := by
        intro b p; cases b <;> rfl
      simp only [Replay5.firstPayload,Bool.false_eq_true,if_false,k] at h
      exact h
    have swapM := OneFlagCell.selectMSwap_frame base (base 2400) (base 1028) (base 2409)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 base_sign_nd (by decide) hb hs hf origin ctx.hg0 V.1 V.2 zero
    have rest := raw_frame false Replay5.restLetters (q7part2_rest_layout ctx.hf) origin ctx X Y
    have out := rest.seq swapM
    cases hS : S <;> simpa only [firstBody,firstSwapM,Replay5.firstPayload,Bool.false_eq_true,
      if_false,Bool.not_false,if_true,S,hS,V] using out
  · have out := (swap X Y).seq (raw_frame true Replay5.restLetters (q7part2_rest_layout ctx.hf)
      origin ctx (if S then Y else X) (if S then X else Y))
    cases hS : S <;> simpa only [firstBody,firstSwap,Replay5.firstPayload,if_true,Bool.not_true,
      Bool.false_eq_true,if_false,S,hS] using out

theorem firstPacket_frame (divide : Bool) (origin : BasisState) (ctx : Context origin)
    (X Y : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin X Y s)
    (hz : divide=false → (Replay5.firstPayload divide origin (X,Y)).2=0) :
    (run (firstPacket divide) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin (Replay5.firstPayload divide origin (X,Y)).1
        (Replay5.firstPayload divide origin (X,Y)).2 (run (firstPacket divide) m s) := by
  have fresh := NewFieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp 0 (by decide) origin X Y _ _ _ (firstBody_read_support divide)
    (firstBody_frame divide origin ctx X Y hz) s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi 0) (baseFirstPacket divide)
    (fun q hq => Placement5.pi_outside 0 q (by decide) hq) s m
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (firstPacket divide) m s=run (baseFirstPacket divide) m s := eq
  rw [same]
  exact fresh


theorem rawEnd_frame (divide : Bool) (origin : BasisState) (ctx : Context origin) (X Y : Fp)
    (hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawEnd divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (Replay5.endPayload divide origin (X,Y)).1)
        (centerWord (Replay5.endPayload divide origin (X,Y)).2)) := by
  let oldctx : Q6EndpointReplay.Context origin :=
    ⟨ctx.hn,ctx.ho,ctx.hp,ctx.hf,ctx.hg0,ctx.hs0,ctx.env,ctx.legal,ctx.parity⟩
  exact Q6EndpointReplay.rawEnd_frame divide origin oldctx X Y hend

theorem endPacket_frame (divide : Bool) (origin : BasisState) (ctx : Context origin)
    (X Y : Fp) (hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (endPacket divide) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin (Replay5.endPayload divide origin (X,Y)).1
        (Replay5.endPayload divide origin (X,Y)).2 (run (endPacket divide) m s) := by
  have fresh := NewHistory5.encoded_disjoint_step base (base 2409)
    (skywalkShared_integer_nodup base ctx.hn) origin X Y _ _ _ (rawEnd_disjoint divide ctx.hn ctx.hp)
    (rawEnd_frame divide origin ctx X Y hend) s m input
  have eq := Replay5.placed_eq Placement5.pi0 (rawEnd divide) Placement5.pi0_outside s m
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (endPacket divide) m s=run (rawEnd divide) m s := eq
  rw [same]
  exact fresh

attribute [local irreducible] Replay5.groupsPayload Replay5.firstPayload Replay5.endPayload
  mixedTranscriptUnitTrace SkywalkTrace.trace SkywalkTrace.next Nat.iterate

theorem logical_forward_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (logicalReplay true) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin Z Z (run (logicalReplay true) m s) := by
  let Z := if origin (base 2400) then Y/(x:Fp) else Y
  have result := run_three_states (firstPacket true) (groups true 1 101) (endPacket true)
    (fun a b => NewHistory5.EncodedFieldFrame5 base (base 2409) origin Y 0 a →
      b.phase=a.phase ∧ NewHistory5.EncodedFieldFrame5 base (base 2409) origin Z Z b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := firstPacket_frame true origin ctx Y 0 a m1 h (fun e => absurd e (by decide))
      rw [hab] at first
      have middle := groups_frame true 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have fp := Replay5.forward_payload origin x Y hx0 hx trace
      have last := endPacket_frame true origin ctx _ _ (fun _ => by
        rw [Prod.mk.eta,fp]
        exact (congrArg Prod.snd fp).symm.trans (by simp only [Replay5.endPayload])) c m3 middle.2
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.forward_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,if_true,List.append_assoc] using result input

theorem logical_inverse_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (logicalReplay false) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin Z 0 (run (logicalReplay false) m s) := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  have result := run_three_states (endPacket false) (groups false 1 101) (firstPacket false)
    (fun a b => NewHistory5.EncodedFieldFrame5 base (base 2409) origin Y Y a →
      b.phase=a.phase ∧ NewHistory5.EncodedFieldFrame5 base (base 2409) origin Z 0 b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := endPacket_frame false origin ctx Y Y (fun e => absurd e (by decide)) a m1 h
      rw [hab] at first
      have middle := groups_frame false 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have last := firstPacket_frame false origin ctx _ _ c m3 middle.2 (fun _ => by
        simp only [Prod.mk.eta]
        exact congrArg Prod.snd (Replay5.inverse_payload origin x Y hx0 hx trace))
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.inverse_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,Bool.false_eq_true,if_false,List.append_assoc] using result input

theorem forward_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (replay true) m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame origin Z Z (run (replay true) m s) :=
  NewFieldFrameOB5.placed_step (logicalReplay true) origin Y 0 _ _
    (logical_forward_frame origin ctx x hx0 hx trace Y) s m input

theorem inverse_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (replay false) m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame origin Z 0 (run (replay false) m s) :=
  NewFieldFrameOB5.placed_step (logicalReplay false) origin Y Y _ _
    (logical_inverse_frame origin ctx x hx0 hx trace Y) s m input


















end ECDSAAdd.Entrant.FrontierReplay1591

end

-- Public component FrontierEntry1591Selected.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierSW1591
open ECDSAAdd.Arithmetic MappedCompressed CompressedFieldSupport Secp256k1 DirectSkywalk SW
attribute [local irreducible] wires

/-! ### Definitions -/

def swapBody : Program :=
  swapRegisters (base 2409) (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y

def cellS (divide : Bool) (g sw : Wire) : Program :=
 if divide then selW g (base 2409) (Q6EndpointCell.half true base (base 2409))++
   selW sw (base 2409) swapBody
 else selW sw (base 2409) swapBody++
   selW g (base 2409) (Q6EndpointCell.half false base (base 2409))

def rawReplayS (divide : Bool) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => if divide then cellS true l.1.1 l.1.2++rawReplayS true ls
    else rawReplayS false ls++cellS false l.1.1 l.1.2

def basePacketS (divide : Bool) (j : Nat) : Program :=
  NewHistory5.decode base (5*j)++rawReplayS divide (Replay5.letters j)++NewHistory5.encode base (5*j)

def packetS (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacketS divide j)

def groupsS (divide : Bool) (j n : Nat) : Program :=
  PacketSequence.program divide (packetS divide) j n

def firstSwapS : Program := selW (base 1028) (base 2409) swapBody

def swapBodyM : Program :=
  UncompSwap.mswap (base 2409) (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y

def firstSwapMS : Program := selW (base 1028) (base 2409) swapBodyM

def firstBodyS (divide : Bool) : Program :=
  if divide then firstSwapS++rawReplayS true Replay5.restLetters
  else rawReplayS false Replay5.restLetters++firstSwapMS

def baseFirstPacketS (divide : Bool) : Program :=
  NewHistory5.decode base 0++firstBodyS divide++NewHistory5.encode base 0

def firstPacketS (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (baseFirstPacketS divide)

def rawEndS (divide : Bool) : Program :=
  selW (base 510) (base 2409) (Q6EndpointCell.halfE divide base (base 2409))

def endPacketS (divide : Bool) : Program := renameProgram (shifted Placement5.pi0) (rawEndS divide)

def logicalReplayS (divide : Bool) : Program :=
  if divide then firstPacketS true++groupsS true 1 101++endPacketS true
  else endPacketS false++groupsS false 1 101++firstPacketS false

def replayS (divide : Bool) : Program := renameProgram (OB5.sig 511) (logicalReplayS divide)

def segmentS (divide : Bool) : Program :=
  if divide then OwnQ5Endpoint.centerT++(replayS true++(HalfFieldOB5.copyN++OwnQ5Endpoint.canonT))
  else OwnQ5Endpoint.centerT++(HalfFieldOB5.copyN++(replayS false++OwnQ5Endpoint.canonT))

/-- The selector-hosted segment (`KernelOB5.segH`) around the selector-free segment. -/
def segHS (divide : Bool) : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap (segmentS divide) ++ [.X (base 511)])


/-! ### Frames -/

theorem Sel.castb {b b' : Wire} {k : Nat} {P' P : Program} (h : Sel b k P' P) (e : b=b') :
    Sel b' k P' P := e ▸ h

theorem selNotZero5 : ¬Placement5.zeroRegion 2400 := by
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion; omega

theorem selShift_fix (j : Nat) (hj : j < 102) : shifted (Placement5.pi j) (base 2400)=base 2400 := by
  rw [shifted_base,Placement5.pi_outside j 2400 hj selNotZero5]

theorem selShift0_fix : shifted Placement5.pi0 (base 2400)=base 2400 := by
  rw [shifted_base,Placement5.pi0_outside 2400 selNotZero5]

theorem selSig_2400 : OB5.sig 511 (base 2400)=base 2400 := by
  rw [OB5.sig_base 511 2400 (le_refl _),if_neg (by omega)]

theorem selEndpoint_fix : HalfFieldOB5.endpointMap (base 2400)=base 2400 := by
  have hb : HalfFieldOB5.bank 2400=2400 := by decide
  have hp : Placement5.pi 51 2400=2400 := Placement5.pi_outside 51 2400 (by omega) selNotZero5
  have h1 : base 2400≠base 1796 := by decide
  have h2 : base 2400≠base 1285 := by decide
  show OB5.sig 511 ((Equiv.swap (base 1796) (base 1285))
    ((shifted (Placement5.pi 51)) ((shifted HalfFieldOB5.bank) (base 2400))))=base 2400
  rw [shifted_base,hb,shifted_base,hp,Equiv.swap_apply_of_ne_of_ne h1 h2,selSig_2400]

theorem selHost_fix : HostOB5.hostSwap (base 2400)=base 2400 := by
  have a1 : base 2400≠base 2409 := by decide
  have a2 : base 2400≠base 511 := by decide
  have a3 : base 2400≠base 2410 := by decide
  have a4 : base 2400≠base 1542 := by decide
  unfold HostOB5.hostSwap
  rw [if_neg a1,if_neg a2,if_neg a3,if_neg a4]

/-! ### Label 2400 is never used outside the windows -/

theorem selX511_away : base 2400∉wires [Instr.X (base 511)] := by
  intro h
  have e : base 2400=base 511 := by simpa [wires,Instr.wires] using h
  have := base_injective e
  omega

def selW0 : Finset Wire := (base 2409::Q6EndpointCell.ids.map base).toFinset ∪ {base 2410}

theorem selW0_away : base 2400∉selW0 := by
  intro h
  simp only [selW0,Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_map,
    Finset.mem_singleton] at h
  rcases h with (e|⟨j,hj,e⟩)|e
  · have := base_injective e; omega
  · have := base_injective e; have := Q6EndpointCell.ids_bound j hj; omega
  · have := base_injective e; omega

theorem selBody_away (divide : Bool) :
    base 2400∉wires (Q6EndpointCell.body divide base (base 2409) (base 2410)) := fun h =>
  selW0_away (Q6EndpointCell.body_support divide base (base 2409) (base 2410) selW0
    Finset.subset_union_left (Finset.mem_union_right _ (Finset.mem_singleton_self _)) h)

theorem selHalf_away (divide : Bool) : base 2400∉wires (Q6EndpointCell.half divide base (base 2409)) :=
  fun h => selW0_away (Q6EndpointCell.half_support divide base (base 2409) selW0
    Finset.subset_union_left h)

theorem selHalfE_away (divide : Bool) : base 2400∉wires (Q6EndpointCell.halfE divide base (base 2409)) :=
  fun h => selHalf_away divide (Q6EndpointCell.halfE_wires divide _ _ h)

theorem selSwap_away : base 2400∉wires swapBody := by
 have sub : wires swapBody⊆wires (Q6EndpointCell.body true base (base 2409) (base 2409)) := by
  simp only [swapBody,Q6EndpointCell.body,if_true,wires_append,Q6EndpointCell.ports_r,
    Q6EndpointCell.ports_y]
  exact Finset.subset_union_right
 have flag : base 2409∈selW0 := by simp [selW0]
 exact fun h => selW0_away (Q6EndpointCell.body_support true base (base 2409) (base 2409)
   selW0 Finset.subset_union_left flag (sub h))

theorem selSwapM_away : base 2400∉wires swapBodyM := by
  rw [swapBodyM,UncompSwap.mswap_wires]
  exact selSwap_away

theorem selHist_away (start : Nat) (hs : start+5 ≤ 512) :
    base 2400∉wires (NewHistory5.encode base start) ∧ base 2400∉wires (NewHistory5.decode base start) := by
  have lift (P : Program) (he : P=NewHistory5.encode base start ∨ P=NewHistory5.decode base start) :
      base 2400∉wires P := by
    intro hq
    obtain ⟨u,hu⟩ := NewHistory5.history_gate_mem base start P he _ hq
    have bound := NewHistory5.historyId_bound start hs u
    have hu' : base 2400=base (History5.historyId start u) := hu
    have := base_injective hu'
    omega
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

theorem selCenter_away : base 2400∉wires HalfFieldOB5.centerT ∧
    base 2400∉wires HalfFieldOB5.canonT ∧ base 2400∉wires HalfFieldOB5.copyN := by
  have ids (q : Wire) (hq : q∈(HalfField.ids.map base).toFinset) : q≠base 2400 := by
    intro e
    subst e
    obtain ⟨i,hi,e⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have := base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,
      or_false] at hi
    omega
  have ren (P : Program) (hP : wires P⊆(HalfField.ids.map base).toFinset) :
      base 2400∉wires (renameProgram HalfFieldOB5.endpointMap P) := by
    rw [renameProgram_support]
    intro h
    obtain ⟨q,hq,e⟩ := Finset.mem_image.mp h
    rw [← selEndpoint_fix] at e
    exact ids q (hP hq) (HalfFieldOB5.endpointMap.injective e)
  exact ⟨ren _ HalfField.centerT_sites,ren _ HalfField.canonT_sites,
    fun h => ids _ (HalfField.copyN_sites h) rfl⟩

theorem selInt_away : base 2400∉wires (stackForwardT) ∧ base 2400∉wires (stackReverseT) := by
  have bad : base 2400∉OB5.integerSites := by
    intro h
    obtain ⟨l,e,hl⟩ := (OB5.integerSites_mem _).mp h
    have := base_injective e
    omega
  exact ⟨fun h => bad (StackOB5.forward_support (stackForwardT_subset h)),fun h => bad (StackOB5.reverse_support (stackReverseT_subset h))⟩

theorem selPrefix_away : base 2400∉(NativeFirstDirect.prefixSites base).toFinset := by
  intro h
  simp only [NativeFirstDirect.prefixSites,wireBlock,List.mem_toFinset,List.mem_append,
    List.mem_cons,List.mem_map,List.mem_range'_1,List.not_mem_nil,or_false,
    base_injective.eq_iff] at h
  omega

theorem selClear_away : base 2400∉wires (skywalkArithmeticClear base) := by
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires]
  simp [base]

/-! ### Letters -/

theorem selLetter_nodup (i : Nat) (hi : i < 510) :
    [base 2400,(tapeLetter i).1.1,base 2409].Nodup ∧ [base 2400,(tapeLetter i).1.2,base 2409].Nodup := by
  simp only [tapeLetter]
  rw [mixedTape_base_getD i (by omega)]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true,
    not_or,not_false_eq_true,base_injective.eq_iff]
  omega

theorem selLetters_nodup (j : Nat) (hj : j < 102) (l : MixedTranscriptLetter)
    (hl : l∈Replay5.letters j) :
    [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2409].Nodup := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have := List.mem_range.mp hk
  exact selLetter_nodup (5*j+k) (by omega)

theorem selRest_nodup (l : MixedTranscriptLetter) (hl : l∈Replay5.restLetters) :
    [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2409].Nodup := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have := List.mem_range'_1.mp hk
  exact selLetter_nodup k (by omega)

/-! ### Cells and packets -/

theorem selCell_sel (divide : Bool) (g sw : Wire) (ig is : Bool)
 (hg : [base 2400,g,base 2409].Nodup) (hs : [base 2400,sw,base 2409].Nodup) :
 Sel (base 2400) 2 (cellS divide g sw)
   (OneFlagCell.cell divide base (base 2400) g sw (base 2409) ig is) := by
 have swap := ((Sel.refl _ _ selSwap_away).window sw (base 2409) is hs)
 have half (d : Bool) := ((Sel.refl _ _ (selHalf_away d)).window g (base 2409) ig hg)
 cases divide
 · simpa only [cellS,OneFlagCell.cell,OneFlagCell.halfWindow,OneFlagCell.selectSwap,
     swapBody,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,if_false] using
     (swap.append (half false)).cast (by norm_num) rfl rfl
 · simpa only [cellS,OneFlagCell.cell,OneFlagCell.halfWindow,OneFlagCell.selectSwap,
     swapBody,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,if_true] using
     ((half true).append swap).cast (by norm_num) rfl rfl

theorem selRaw_sel (divide : Bool) (ls : List MixedTranscriptLetter)
    (hl : ∀ l∈ls, [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2409].Nodup) :
    Sel (base 2400) (2*ls.length) (rawReplayS divide ls) (FrontierReplay1591.rawReplay divide ls) := by
  induction ls with
  | nil => exact (Sel.refl _ [] (by simp [wires])).cast (by simp) rfl rfl
  | cons l ls ih =>
    have hh := hl l (List.mem_cons_self ..)
    have rest := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    cases divide
    · exact (rest.append (selCell_sel false l.1.1 l.1.2 l.2.1 l.2.2 hh.1 hh.2)).cast
        (by simp only [List.length_cons]; omega) rfl rfl
    · exact ((selCell_sel true l.1.1 l.1.2 l.2.1 l.2.2 hh.1 hh.2).append rest).cast
        (by simp only [List.length_cons]; omega) rfl rfl

theorem selPacket_sel (divide : Bool) (j : Nat) (hj : j < 102) :
    Sel (base 2400) 10 (packetS divide j) (FrontierReplay1591.packet divide j) := by
  have codec := selHist_away (5*j) (by omega)
  have r := selRaw_sel divide (Replay5.letters j) (selLetters_nodup j hj)
  have len : (Replay5.letters j).length=5 := by simp [Replay5.letters]
  rw [len] at r
  have b : Sel (base 2400) 10 (basePacketS divide j) (FrontierReplay1591.basePacket divide j) :=
    (((Sel.refl _ _ codec.2).append r).append (Sel.refl _ _ codec.1)).cast (by norm_num) rfl rfl
  exact b.rename (shifted (Placement5.pi j)) (selShift_fix j hj)

theorem selGroups_sel (divide : Bool) (j n : Nat) (bound : j+n ≤ 102) :
    Sel (base 2400) (10*n) (groupsS divide j n) (FrontierReplay1591.groups divide j n) := by
  unfold groupsS FrontierReplay1591.groups
  induction n generalizing j with
  | zero => exact (Sel.refl _ [] (by simp [wires])).cast (by simp) rfl rfl
  | succ n ih =>
    have head := selPacket_sel divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide
    · simp only [PacketSequence.program,Bool.false_eq_true,if_false]
      exact (rest.append head).cast (by ring) rfl rfl
    · simp only [PacketSequence.program,if_true]
      exact (head.append rest).cast (by ring) rfl rfl

theorem selFirstSwap_sel : Sel (base 2400) 1 firstSwapS FrontierReplay1591.firstSwap := by
  have n : [base 2400,base 1028,base 2409].Nodup := by decide
  exact ((Sel.refl _ _ selSwap_away).window (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 n).cast (by norm_num) rfl rfl

theorem selFirstSwapM_sel : Sel (base 2400) 1 firstSwapMS FrontierReplay1591.firstSwapM := by
  have n : [base 2400,base 1028,base 2409].Nodup := by decide
  exact ((Sel.refl _ _ selSwapM_away).window (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 n).cast (by norm_num) rfl rfl

theorem selFirstPacket_sel (divide : Bool) :
    Sel (base 2400) 9 (firstPacketS divide) (FrontierReplay1591.firstPacket divide) := by
  have codec := selHist_away 0 (by omega)
  have r := selRaw_sel divide Replay5.restLetters selRest_nodup
  have len : Replay5.restLetters.length=4 := by simp [Replay5.restLetters]
  rw [len] at r
  have body : Sel (base 2400) 9 (firstBodyS divide) (FrontierReplay1591.firstBody divide) := by
    cases divide
    · exact (r.append selFirstSwapM_sel).cast (by norm_num) rfl rfl
    · exact (selFirstSwap_sel.append r).cast (by norm_num) rfl rfl
  have b : Sel (base 2400) 9 (baseFirstPacketS divide) (FrontierReplay1591.baseFirstPacket divide) :=
    (((Sel.refl _ _ codec.2).append body).append (Sel.refl _ _ codec.1)).cast (by norm_num) rfl rfl
  exact b.rename (shifted (Placement5.pi 0)) (selShift_fix 0 (by omega))

theorem selEnd_sel (divide : Bool) :
    Sel (base 2400) 1 (endPacketS divide) (FrontierReplay1591.endPacket divide) := by
  have n : [base 2400,base 510,base 2409].Nodup := by decide
  have b : Sel (base 2400) 1 (rawEndS divide) (FrontierReplay1591.rawEnd divide) :=
    ((Sel.refl _ _ (selHalfE_away divide)).window (base 510) (base 2409)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1 n).cast (by norm_num) rfl rfl
  exact b.rename (shifted Placement5.pi0) selShift0_fix

/-! ### Replay, segment, kernel -/

theorem selLogical_sel (divide : Bool) :
    Sel (base 2400) 1020 (logicalReplayS divide) (FrontierReplay1591.logicalReplay divide) := by
  have g := selGroups_sel divide 1 101 (by omega)
  have e := selEnd_sel divide
  have f := selFirstPacket_sel divide
  cases divide
  · exact ((e.append g).append f).cast (by norm_num) rfl rfl
  · exact ((f.append g).append e).cast (by norm_num) rfl rfl

theorem selReplay_sel (divide : Bool) :
    Sel (base 2400) 1020 (replayS divide) (FrontierReplay1591.replay divide) :=
  ((selLogical_sel divide).rename_inj (OB5.sig 511) (OB5.sig_injective 511 (by decide))).castb
    selSig_2400

end ECDSAAdd.Entrant.FrontierSW1591

end

-- Public component FrontierEntry1591Endpoints.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.NewHalfField5
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport
open OffsetBorrowedCanonical RecordedQuantum NewHistory5
attribute [local irreducible] run wires NewHistory5.allEncode

abbrev tgt := HalfField.tgt
abbrev ports := HalfField.ports
abbrev centerT := HalfField.centerT
abbrev canonT := HalfField.canonT
abbrev copyN := HalfField.copyN
abbrev ids := HalfField.ids

private theorem ports_r : ports.r=wireBlock base 2056 256 := balancedSharedPorts_r base (base 2409)
private theorem ports_y : ports.y=wireBlock base 770 256 := balancedSharedPorts_y base (base 2409)

theorem encoder_disjoint (P : Program) (h : wires P⊆(ids.map base).toFinset) :
    Disjoint (wires (NewHistory5.allEncode base 102)) (wires P) := by
  have hist := NewHistory5.allEncode_history_support base 102 (by decide)
  apply Finset.disjoint_left.mpr
  intro q hq hc
  have history := List.mem_toFinset.mp (hist hq)
  have converted := List.mem_toFinset.mp (h hc)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp converted
  simp only [List.mem_append,wireBlock] at history
  rcases history with history|history
  all_goals
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp history
    have same := base_injective eq
    subst i
    simp only [List.mem_range'_1] at hi
    simp only [ids,HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
    omega

private theorem centerT_sites : wires centerT⊆(ids.map base).toFinset := HalfField.centerT_sites
private theorem canonT_sites : wires canonT⊆(ids.map base).toFinset := HalfField.canonT_sites
private theorem copyN_sites : wires copyN⊆(ids.map base).toFinset := HalfField.copyN_sites

private theorem xor_neutral (a b : Bool) (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem encoded_transport (P : Program) (dis : Disjoint (wires (NewHistory5.allEncode base 102)) (wires P))
    (s raw : State) (m : List Bool) (encoded : s=run (NewHistory5.allEncode base 102) [] raw)
    (phase : (run P m raw).phase=raw.phase) :
    (run P m s).phase=s.phase ∧ run P m s=run (NewHistory5.allEncode base 102) [] (run P m raw) := by
  have read : ∀q∈wires P,s.basis q=raw.basis q := by
    intro q hq
    rw [encoded]
    exact run_preserves_outside _ [] raw q (fun he => Finset.disjoint_left.mp dis he hq)
  have increment := (run_local_increment P s raw m read).1
  rw [phase,Bool.xor_self] at increment
  refine ⟨xor_neutral _ _ increment,?_⟩
  rw [encoded]
  exact (run_disjoint_commute _ _ dis [] m raw).symm

/-! Frame steps. -/

private theorem port_split :
    (skywalkSharedField base).z=ports.r++[base 2312] ∧
    (skywalkSharedField base).a=ports.y++[base 1026] := by
  rw [skywalkShared_field_z,ports_r,ports_y]
  constructor
  · have split := wireBlock_append base 2056 256 1
    simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using split.symm
  · have split := wireBlock_append base 770 256 1
    simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using split.symm

private theorem value_bound (X : Fp) : X.val<2^256 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact (ZMod.val_lt X).trans (by norm_num [p])

theorem centerWord_zero : centerWord (0:Fp)=0 := by
  have h : (0:Int)≤q := by norm_num [q,p]
  simp [centerWord,centerFp,encodeWord,h]

private theorem target_clean (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0) (A B : Nat) (st : BasisState)
    (frame : PairFrame ports.r ports.y origin A B st) :
    ∀q∈BalancedConvert.work tgt,st q=false := by
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have away := (balancedSharedBoundary base (base 2409) hn).targetWorkAway
  intro q hq
  exact (frame.2.2 q (away q hq).1 (away q hq).2).trans (clean.1 q hq)

private theorem pair_dis (hn : (skywalkSharedWires base).Nodup) : ports.r.Disjoint ports.y :=
  (List.nodup_append'.mp (balancedSharedLayout_pairND base (base 2409) hn)).2.2

private theorem tgt_word : tgt.word=ports.r := balancedSharedTargetConvert_word base (base 2409)

private theorem center_frame_generic (P : Program)
    (sites : wires P⊆(ids.map base).toFinset) (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame5 origin X 0 s)
    (hcorrect : ∀ (raw : State) (records : List Bool),
      regValue tgt.word raw.basis=X.val →
      (∀q∈BalancedConvert.work tgt,raw.basis q=false) →
      let z := run P records raw
      z.phase=raw.phase ∧ regValue tgt.word z.basis=centerWord (X/2) ∧
      (∀q∈BalancedConvert.work tgt,z.basis q=false) ∧
      (∀q,q∉tgt.word → z.basis q=raw.basis q)) :
    (run P m s).phase=s.phase ∧
    EncodedFieldFrame5 base (base 2409) origin (X/2) 0 (run P m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have split := port_split
  rw [split.1,split.2,ZMod.val_zero] at frame
  have narrow := balancedPair_narrow ports.r ports.y (base 2312) (base 1026) origin raw.basis
    X.val 0 (by rw [ports_r,wireBlock_length]; exact value_bound X)
    (by rw [ports_y,wireBlock_length]; norm_num) frame hr hy
  have c := hcorrect raw m (by rw [tgt_word]; exact narrow.1)
    (target_clean hn origin hw hu _ _ _ narrow)
  have pf : PairFrame ports.r ports.y origin (centerWord (X/2)) (centerWord 0)
      (run P m raw).basis := by
    rw [centerWord_zero]
    exact PairFrame.update_temp ports.r ports.y origin raw.basis _ X.val 0 _ (pair_dis hn) narrow
      (by rw [←tgt_word]; exact c.2.2.2) (by rw [←tgt_word]; exact c.2.1)
  have actual := encoded_transport P (encoder_disjoint _ sites) s raw m encoded c.1
  exact ⟨actual.1,run P m raw,c.1.trans (phase.trans actual.1.symm),pf,actual.2⟩


/-- Halving entry conversion of the target port; the zero source port is
already its own balanced word. -/
theorem center_frame (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame5 origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    EncodedFieldFrame5 base (base 2409) origin (X/2) 0 (run centerT m s) := by
  exact center_frame_generic centerT centerT_sites hn origin hw hu hr hy X s m input
    (HalfConvert.center_correct tgt (balancedSharedTargetConvert_widths base)
      (balancedSharedTargetConvert_nodup base hn) X)


private theorem canon_frame_generic (P : Program)
    (sites : wires P⊆(ids.map base).toFinset) (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame5 base (base 2409) origin X 0 s)
    (hcorrect : ∀ (raw : State) (records : List Bool),
      regValue tgt.word raw.basis=centerWord X →
      (∀q∈BalancedConvert.work tgt,raw.basis q=false) →
      let z := run P records raw
      z.phase=raw.phase ∧ regValue tgt.word z.basis=(2*X).val ∧
      (∀q∈BalancedConvert.work tgt,z.basis q=false) ∧
      (∀q,q∉tgt.word → z.basis q=raw.basis q)) :
    (run P m s).phase=s.phase ∧ EncodedCanonicalFrame5 origin (2*X) 0 (run P m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  rw [centerWord_zero] at frame
  have c := hcorrect raw m (by rw [tgt_word]; exact frame.1)
    (target_clean hn origin hw hu _ _ _ frame)
  have pf : PairFrame ports.r ports.y origin (2*X).val 0 (run P m raw).basis :=
    PairFrame.update_temp ports.r ports.y origin raw.basis _ _ 0 _ (pair_dis hn) frame
      (by rw [←tgt_word]; exact c.2.2.2) (by rw [←tgt_word]; exact c.2.1)
  have outside := balancedSharedDivision_high_outside base hn
  have wide := balancedPair_widen ports.r ports.y (base 2312) (base 1026) origin _ (2*X).val 0 pf
    (by rw [ports_r,ports_y]; exact outside.1) (by rw [ports_r,ports_y]; exact outside.2) hr hy
  have split := port_split
  rw [←split.1,←split.2] at wide
  have actual := encoded_transport P (encoder_disjoint _ sites) s raw m encoded c.1
  refine ⟨actual.1,run P m raw,c.1.trans (phase.trans actual.1.symm),?_,actual.2⟩
  rw [ZMod.val_zero]
  exact wide


/-- Doubling exit conversion of the target port; the zero source port is
already canonical. -/
theorem canon_frame (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame5 base (base 2409) origin X 0 s) :
    (run canonT m s).phase=s.phase ∧ EncodedCanonicalFrame5 origin (2*X) 0 (run canonT m s) := by
  exact canon_frame_generic canonT canonT_sites hn origin hw hu hr hy X s m input
    (HalfConvert.canonical_correct tgt (balancedSharedTargetConvert_widths base)
      (balancedSharedTargetConvert_nodup base hn) X)


private theorem copy_raw (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (A B : Nat) (raw : State) (m : List Bool)
    (frame : PairFrame ports.r ports.y origin A B raw.basis) :
    (run copyN m raw).phase=raw.phase ∧
    PairFrame ports.r ports.y origin A (B ^^^ A) (run copyN m raw).basis := by
  have len : ports.r.length=ports.y.length := by rw [ports_r,ports_y]; simp [wireBlock_length]
  obtain ⟨phase,keep,value⟩ := copyRegister_correct none ports.r ports.y len
    (balancedSharedLayout_pairND base (base 2409) hn) (by simp) raw m
  refine ⟨phase,PairFrame.update_dst _ _ origin raw.basis _ A B _ (pair_dis hn) frame keep ?_⟩
  simpa only [copyValue,frame.1,frame.2.1] using value

/-- Duplicate the balanced target into the clean source. -/
theorem copy_fill (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame5 base (base 2409) origin X 0 s) :
    (run copyN m s).phase=s.phase ∧ EncodedFieldFrame5 base (base 2409) origin X X (run copyN m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have c := copy_raw hn origin _ _ raw m frame
  rw [centerWord_zero,Nat.zero_xor] at c
  have actual := encoded_transport copyN (encoder_disjoint _ copyN_sites) s raw m encoded c.1
  exact ⟨actual.1,run copyN m raw,c.1.trans (phase.trans actual.1.symm),c.2,actual.2⟩

/-- Clear the source against the equal balanced target. -/
theorem copy_clear (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame5 base (base 2409) origin X X s) :
    (run copyN m s).phase=s.phase ∧ EncodedFieldFrame5 base (base 2409) origin X 0 (run copyN m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have c := copy_raw hn origin _ _ raw m frame
  rw [Nat.xor_self,←centerWord_zero] at c
  have actual := encoded_transport copyN (encoder_disjoint _ copyN_sites) s raw m encoded c.1
  exact ⟨actual.1,run copyN m raw,c.1.trans (phase.trans actual.1.symm),c.2,actual.2⟩


theorem encoder_pool_support :
    wires (NewHistory5.allEncode base 102)⊆(skywalkPoolWires base).toFinset := by
  intro q hq
  have member := List.mem_toFinset.mp (NewHistory5.allEncode_history_support base 102 (by decide) hq)
  simp only [List.mem_append,wireBlock] at member
  rcases member with member|member
  all_goals
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
    simp only [List.mem_range'_1] at hi
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨i,by omega,rfl⟩

theorem encodedCanonical_pool_basis5 (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame5 origin X 0 s) :
    ∀q∈skywalkPoolWires base,s.basis q=
      (run (NewHistory5.allEncode base 102) [] ({phase:=false,basis:=origin} : State)).basis q := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have narrow : PairFrame (skywalkSharedField base).z (skywalkSharedField base).a
      origin X.val 0 raw.basis := by simpa only [ZMod.val_zero] using rawFrame
  exact encoded_field_pool_basis base hn (NewHistory5.allEncode base 102) encoder_pool_support origin ha
    X.val raw s narrow encoded

theorem encodedCanonical_caller_frame5 (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame5 origin X 0 s) :
    regValue (skywalkSharedField base).z s.basis=X.val ∧
    ∀q,q∉(skywalkSharedField base).z → q∉skywalkPoolWires base → s.basis q=origin q := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have narrow : PairFrame (skywalkSharedField base).z (skywalkSharedField base).a
      origin X.val 0 raw.basis := by simpa only [ZMod.val_zero] using rawFrame
  have keeps := DirectSkywalk.arith_field_frame (skywalkSharedField base) origin raw.basis X.val ha narrow
  have away (q : Wire) (hq : q∉skywalkPoolWires base) :
      (run (NewHistory5.allEncode base 102) [] raw).basis q=raw.basis q :=
    run_preserves_outside _ [] raw q (fun used => hq (List.mem_toFinset.mp (encoder_pool_support used)))
  constructor
  · apply Eq.trans (regValue_congr _ _ _ ?_) narrow.1
    intro q hq
    rw [encoded]
    exact away q (fun hp => DirectSkywalk.arith_pool_away_z base hn q hp hq)
  · intro q hz hp
    rw [encoded]
    exact (away q hp).trans (keeps q hz)

end ECDSAAdd.Entrant.NewHalfField5

namespace ECDSAAdd.Entrant.NewHalfFieldOB5
open Arithmetic Secp256k1 BalancedField MappedCompressed OffsetBorrowedCanonical NewHistory5
attribute [local irreducible] run wires NewHistory5.allEncode

private def bankFn (i : Nat) : Nat :=
  if 512 ≤ i ∧ i < 767 then i+1028 else if 1540 ≤ i ∧ i < 1795 then i-1028 else i

private theorem bank_invol : Function.Involutive bankFn := by
  intro i
  unfold bankFn
  split_ifs  <;> omega

def bank : Equiv.Perm Nat := ⟨bankFn,bankFn,bank_invol,bank_invol⟩
def relocate : Equiv.Perm Wire :=
  (shifted bank).trans ((shifted (Placement5.pi 51)).trans (Equiv.swap (base 1796) (base 1285)))
def endpointMap : Equiv.Perm Wire := relocate.trans
  ⟨OB5.sig 511,OB5.sig 511,OB5.sig_invol 511 (by decide),OB5.sig_invol 511 (by decide)⟩

def centerT : Program := renameProgram endpointMap NewHalfField5.centerT
def canonT : Program := renameProgram endpointMap NewHalfField5.canonT
abbrev copyN := NewHalfField5.copyN

private def BankRegion (i : Nat) : Prop := (512 ≤ i ∧ i < 767) ∨ (1540 ≤ i ∧ i < 1795)

private theorem bank_fix (i : Nat) (h : ¬BankRegion i) : bank i=i := by
  change bankFn i=i
  simp only [BankRegion,not_or] at h
  simp [bankFn,h.1,h.2]

private theorem shifted_bank_zero (s : State) (hz : ∀i,BankRegion i → s.basis (base i)=false) :
    pullState (shifted bank) s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (shifted bank q)=s.basis q
    by_cases small : q < 16
    · change s.basis (shiftedFn bank q)=s.basis q
      simp only [shiftedFn,if_pos small]
    · have e : q=base (q-16) := by change q=q-16+16; exact (Nat.sub_add_cancel (Nat.le_of_not_gt small)).symm
      rw [e,shifted_base]
      by_cases inside : BankRegion (q-16)
      · have mapped : BankRegion (bank (q-16)) := by
          by_contra outside
          have eq := bank.injective (bank_fix _ outside)
          exact outside (eq.symm ▸ inside)
        exact (hz _ mapped).trans (hz _ inside).symm
      · rw [bank_fix _ inside]

private theorem env_bank (origin : BasisState) (env : Env base origin) (i : Nat)
    (hi : BankRegion i ∨ i=1796) : origin (base i)=false := by
  rcases hi with (h|h)|h
  · exact OffsetCleanupBorrowedCaller.maskBit_zero base origin env.1 i (by omega) (by omega)
  · have mem := DirectSkywalk.arith_mem base 1540 257 i (by omega) (by omega)
    exact (regValue_zero _ _).mp env.1 _ (by
      simp [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,mem])
  · subst i
    have mem := DirectSkywalk.arith_mem base 1540 257 1796 (by omega) (by omega)
    exact (regValue_zero _ _).mp env.1 _ (by
      simp [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,mem])

private theorem encoder_away (i : Nat) (hi : BankRegion i ∨ i=1796) :
    base i∉wires (NewHistory5.allEncode base 102) := by
  intro h
  have mem := List.mem_toFinset.mp (allEncode_history_support base 102 (by decide) h)
  simp only [List.mem_append,wireBlock,List.mem_map,List.mem_range'_1] at mem
  rcases mem with ⟨j,hj,eq⟩|⟨j,hj,eq⟩
  all_goals
    have same := base_injective eq
    unfold BankRegion at hi
    omega

private theorem frame_banks (origin : BasisState) (env : Env base origin) (s raw : State)
    (encoded : s=run (NewHistory5.allEncode base 102) [] raw)
    (keep : ∀i,BankRegion i ∨ i=1796 → raw.basis (base i)=origin (base i)) :
    (∀i,BankRegion i → s.basis (base i)=false) ∧ s.basis (base 1796)=false := by
  have z (i : Nat) (hi : BankRegion i ∨ i=1796) : s.basis (base i)=false := by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_away i hi)).trans
      ((keep i hi).trans (env_bank origin env i hi))
  exact ⟨fun i hi => z i (Or.inl hi),z 1796 (Or.inr rfl)⟩

private theorem canonical_banks (origin : BasisState) (env : Env base origin)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame5 origin X 0 s) :
    (∀i,BankRegion i → s.basis (base i)=false) ∧ s.basis (base 1796)=false := by
  obtain ⟨raw,_,f,e⟩ := frame
  apply frame_banks origin env s raw e
  intro i hi
  apply f.2.2
  · intro mem
    rw [skywalkShared_field_z] at mem
    simp only [wireBlock,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
      List.mem_map,List.mem_range'_1] at mem
    unfold BankRegion at hi
    obtain ⟨j,hj,eq⟩ := mem
    have same := base_injective eq
    omega
  · intro mem
    change base i∈wireBlock base 770 257 at mem
    obtain ⟨j,hj,eq⟩ := List.mem_map.mp mem
    simp only [List.mem_range'_1] at hj
    have same := base_injective eq
    unfold BankRegion at hi
    omega

private theorem field_banks (origin : BasisState) (env : Env base origin)
    (X Y : Fp) (s : State) (frame : EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (∀i,BankRegion i → s.basis (base i)=false) ∧ s.basis (base 1796)=false := by
  obtain ⟨raw,_,f,e⟩ := frame
  apply frame_banks origin env s raw e
  intro i hi
  apply f.2.2
  all_goals
    intro mem
    simp only [balancedSharedPorts_r,balancedSharedPorts_y] at mem
    obtain ⟨j,hj,eq⟩ := List.mem_map.mp mem
    simp only [List.mem_range'_1] at hj
    have same := base_injective eq
    unfold BankRegion at hi
    omega

private theorem canonical_zero (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (env : Env base origin) (legal : RawLegal base 102 origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame5 origin X 0 s) :
    ∀q,Placement5.zeroRegion q → s.basis (base q)=false := by
  intro q hq
  have before := NewHalfField5.encodedCanonical_pool_basis5 hn origin ha X s frame
  have pool : base q∈skywalkPoolWires base := by
    apply List.mem_map.mpr
    refine ⟨q,?_,rfl⟩
    simp only [List.mem_range'_1]
    rcases hq with h|h
    · unfold Placement5.workRegion at h; omega
    · unfold Placement5.holeRegion at h; omega
  rw [before _ pool]
  rcases hq with work|hole
  · exact (run_preserves_outside _ [] ({phase:=false,basis:=origin}:State) _
      (encoder_away q (Or.inl (Or.inl (by unfold Placement5.workRegion at work; omega))))).trans
      (env_bank origin env q (Or.inl (Or.inl (by unfold Placement5.workRegion at work; omega))))
  · have recover := Placement5.hole_recover q hole
    rw [←recover.2]
    exact allEncode_holes_zero base base_pool_nodup ({phase:=false,basis:=origin}:State) [] legal
      (Placement5.holeIndex q) recover.1

private theorem relocation_eq (P : Program) (s : State) (m : List Bool)
    (b0 : ∀i,BankRegion i → s.basis (base i)=false)
    (b1 : ∀i,BankRegion i → (run P m s).basis (base i)=false)
    (z0 : ∀i,Placement5.zeroRegion i → s.basis (base i)=false)
    (z1 : ∀i,Placement5.zeroRegion i → (run P m s).basis (base i)=false)
    (f0 : s.basis (base 1796)=false) (f1 : (run P m s).basis (base 1796)=false) :
    run (renameProgram relocate P) m s=run P m s := by
  have bankRun : run (renameProgram (shifted bank) P) m s=run P m s := by
    apply pullState_perm_injective (shifted bank)
    rw [run_rename _ (shifted bank).injective,shifted_bank_zero s b0,shifted_bank_zero _ b1]
  have piRun : run (renameProgram (shifted (Placement5.pi 51))
      (renameProgram (shifted bank) P)) m s=run P m s := by
    apply pullState_perm_injective (shifted (Placement5.pi 51))
    rw [run_rename _ (shifted (Placement5.pi 51)).injective,
      Placement5.shifted_zero_boundary _ (Placement5.pi_outside 51 · (by decide)) s z0,
      bankRun,Placement5.shifted_zero_boundary _ (Placement5.pi_outside 51 · (by decide)) _ z1]
  have hole : Placement5.zeroRegion 1285 := by right; unfold Placement5.holeRegion; decide
  have swapRun := NewFieldFrameOB5.rebind_swap_run (base 1796) (base 1285)
    (renameProgram (shifted (Placement5.pi 51)) (renameProgram (shifted bank) P)) s m
    f0 (z0 _ hole) (by rw [piRun]; exact f1) (by rw [piRun]; exact z1 _ hole)
  simpa only [relocate,Equiv.trans_apply,renameProgram_comp] using swapRun.trans piRun

attribute [local irreducible] HalfField.centerT HalfField.canonT
set_option maxHeartbeats 30000

theorem logical_center_eq (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame5 origin X 0 s) :
    run (renameProgram relocate NewHalfField5.centerT) m s=run NewHalfField5.centerT m s := by
  have c := NewHalfField5.center_frame hn origin env.1 env.2.1 hr env.2.2 X s m input
  have a := canonical_banks origin env X s input
  have b := field_banks origin env _ _ _ c.2
  exact relocation_eq NewHalfField5.centerT s m a.1 b.1 (canonical_zero hn origin env legal ha X s input)
    (NewHistory5.encoded_zero_region base (base 2409) hn ho origin env legal _ _ _ c.2) a.2 b.2

theorem logical_canon_eq (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame5 base (base 2409) origin X 0 s) :
    run (renameProgram relocate NewHalfField5.canonT) m s=run NewHalfField5.canonT m s := by
  have c := NewHalfField5.canon_frame hn origin env.1 env.2.1 hr env.2.2 X s m input
  have a := field_banks origin env _ _ _ input
  have b := canonical_banks origin env _ _ c.2
  exact relocation_eq NewHalfField5.canonT s m a.1 b.1
    (NewHistory5.encoded_zero_region base (base 2409) hn ho origin env legal _ _ _ input)
    (canonical_zero hn origin env legal ha _ _ c.2) a.2 b.2

private theorem endpointMap_rename (P : Program) :
    renameProgram endpointMap P=renameProgram (OB5.sig 511) (renameProgram relocate P) := by
  change renameProgram ((OB5.sig 511) ∘ relocate) P=_
  exact (renameProgram_comp (OB5.sig 511) relocate P).symm

private theorem center_eq : centerT=renameProgram (OB5.sig 511)
    (renameProgram relocate NewHalfField5.centerT) := endpointMap_rename _

private theorem canon_eq : canonT=renameProgram (OB5.sig 511)
    (renameProgram relocate NewHalfField5.canonT) := endpointMap_rename _

private theorem placed_step (e : Wire → Wire) (he : Function.Injective e) (P : Program)
    (I O : State → Prop)
    (correct : ∀s m,I s → (run P m s).phase=s.phase ∧ O (run P m s))
    (s : State) (m : List Bool) (input : I (pullState e s)) :
    (run (renameProgram e P) m s).phase=s.phase ∧ O (pullState e (run (renameProgram e P) m s)) := by
  have c := correct (pullState e s) m input
  have same := ECDSAAdd.run_rename e he P m s
  rw [←same] at c
  exact c

attribute [local irreducible] relocate endpointMap

theorem center_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedFieldFrame origin (X/2) 0 (run centerT m s) := by
  have correct : ∀t records,EncodedCanonicalFrame5 origin X 0 t →
      (run (renameProgram relocate NewHalfField5.centerT) records t).phase=t.phase ∧
      EncodedFieldFrame5 base (base 2409) origin (X/2) 0
        (run (renameProgram relocate NewHalfField5.centerT) records t) := by
    intro t records hin
    rw [logical_center_eq hn ho origin env legal hr ha X t records hin]
    exact NewHalfField5.center_frame hn origin env.1 env.2.1 hr env.2.2 X t records hin
  have c := placed_step (OB5.sig 511) (OB5.sig_injective 511 (by decide))
    (renameProgram relocate NewHalfField5.centerT) _ _ correct s m input
  rw [←center_eq] at c
  exact c

theorem canon_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run canonT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  have correct : ∀t records,EncodedFieldFrame5 base (base 2409) origin X 0 t →
      (run (renameProgram relocate NewHalfField5.canonT) records t).phase=t.phase ∧
      EncodedCanonicalFrame5 origin (2*X) 0
        (run (renameProgram relocate NewHalfField5.canonT) records t) := by
    intro t records hin
    rw [logical_canon_eq hn ho origin env legal hr ha X t records hin]
    exact NewHalfField5.canon_frame hn origin env.1 env.2.1 hr env.2.2 X t records hin
  have c := placed_step (OB5.sig 511) (OB5.sig_injective 511 (by decide))
    (renameProgram relocate NewHalfField5.canonT) _ _ correct s m input
  rw [←canon_eq] at c
  exact c

theorem copyN_rename : renameProgram (OB5.sig 511) copyN=copyN := by
  have fixed (start len : Nat) (h : (770 ≤ start ∧ start+len ≤ 1026) ∨ (2056 ≤ start ∧ start+len ≤ 2312)) :
      (wireBlock base start len).map (OB5.sig 511)=wireBlock base start len := by
    calc
      (wireBlock base start len).map (OB5.sig 511)=(wireBlock base start len).map id := by
        apply List.map_congr_left
        intro q hq
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
        simp only [List.mem_range'_1] at hi
        rw [OB5.sig_base 511 i (by decide)]
        have outside : ¬((1285 ≤ i ∧ i ≤ 1028+511) ∨ (2053 ≤ i+511 ∧ i ≤ 1796)) := by omega
        simp only [if_neg outside,id_eq]
      _=wireBlock base start len := List.map_id _

  simp only [copyN,NewHalfField5.copyN,HalfField.copyN,FieldRename.copyRegister_natural,
    Option.map_none,HalfField.ports,balancedSharedPorts_r,balancedSharedPorts_y,
    fixed 2056 256 (Or.inr ⟨by omega,by omega⟩),fixed 770 256 (Or.inl ⟨by omega,by omega⟩)]

theorem copy_fill (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run copyN m s).phase=s.phase ∧ NewFieldFrameOB5.EncodedFieldFrame origin X X (run copyN m s) := by
  have c := NewFieldFrameOB5.placed_step copyN origin X 0 X X
    (fun t records h => NewHalfField5.copy_fill hn origin X t records h) s m input
  rw [copyN_rename] at c
  exact c

theorem copy_clear (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X X s) :
    (run copyN m s).phase=s.phase ∧ NewFieldFrameOB5.EncodedFieldFrame origin X 0 (run copyN m s) := by
  have c := NewFieldFrameOB5.placed_step copyN origin X X X 0
    (fun t records h => NewHalfField5.copy_clear hn origin X t records h) s m input
  rw [copyN_rename] at c
  exact c

attribute [local irreducible] toffoliCount measurementCount

theorem endpoint_counts : toffoliCount centerT=254 ∧ measurementCount centerT=254 ∧
    toffoliCount canonT=254 ∧ measurementCount canonT=254 := by
  have old : toffoliCount NewHalfField5.centerT=254 ∧ measurementCount NewHalfField5.centerT=254 ∧
      toffoliCount NewHalfField5.canonT=254 ∧ measurementCount NewHalfField5.canonT=254 := by
    simpa only [NewHalfField5.centerT,NewHalfField5.canonT,HalfField.centerT,HalfField.canonT] using
      HalfConvert.counts HalfField.tgt (balancedSharedTargetConvert_widths base)
  have a := renameProgram_counts endpointMap NewHalfField5.centerT
  have b := renameProgram_counts endpointMap NewHalfField5.canonT
  exact ⟨a.1.trans old.1,a.2.trans old.2.1,b.1.trans old.2.2.1,b.2.trans old.2.2.2⟩

theorem endpoint_physical (hn : (skywalkSharedWires base).Nodup) :
    GatePhysical centerT ∧ GatePhysical canonT ∧ GatePhysical copyN := by
  have old := HalfConvert.physical HalfField.tgt (balancedSharedTargetConvert_widths base)
    (balancedSharedTargetConvert_nodup base hn)
  have oldCenter : GatePhysical NewHalfField5.centerT := by
    simpa only [NewHalfField5.centerT,HalfField.centerT] using old.1
  have oldCanon : GatePhysical NewHalfField5.canonT := by
    simpa only [NewHalfField5.canonT,HalfField.canonT] using old.2
  exact ⟨gatePhysical_rename endpointMap endpointMap.injective _ oldCenter,
    gatePhysical_rename endpointMap endpointMap.injective _ oldCanon,
    copyRegister_physical none _ _ (balancedSharedLayout_pairND base (base 2409) hn) (by simp)⟩

theorem endpoint_gateSlots_le : Challenge.gateSlots centerT ≤ 6000 ∧
    Challenge.gateSlots canonT ≤ 6000 ∧ Challenge.gateSlots copyN ≤ 256 := by
  have a : Challenge.gateSlots NewHalfField5.centerT ≤ 6000 ∧ Challenge.gateSlots NewHalfField5.canonT ≤ 6000 :=
    HalfLane.convert_gateSlots_le
  have cp : Challenge.gateSlots copyN ≤ 256 := by
    simp only [copyN,NewHalfField5.copyN,HalfField.copyN,HalfField.ports,
      Baselines.copyRegister_gateSlots,balancedSharedPorts_r,wireBlock_length]
    omega
  exact ⟨by simpa only [centerT,Baselines.rename_gateSlots] using a.1,
    by simpa only [canonT,Baselines.rename_gateSlots] using a.2,cp⟩

end ECDSAAdd.Entrant.NewHalfFieldOB5

namespace ECDSAAdd.Entrant.NewOwnPlusEndpoint
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
open OwnPlusHost
attribute [local irreducible] run wires

theorem encoder_free (q : Nat) (hq : q=766 ∨ q=768) :
    base q∉wires (NewHistory5.allEncode base 102) := by
  intro used
  have mem:=NewHistory5.allEncode_history_support base 102 (by omega) used
  simp only [List.mem_toFinset,List.mem_append] at mem
  rcases mem with lo|hi
  · exact not_block q 0 512 (by omega) lo
  · exact not_block q 1028 512 (by omega) hi

theorem canonical_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=766 ∨ q=768) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have z:base q∉(skywalkSharedField base).z:=by
    rw [skywalkShared_field_z]
    exact not_block q 2056 257 (by omega)
  have a:base q∉(skywalkSharedField base).a:=not_block q 770 257 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ z a)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem field_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=766 ∨ q=768) (input : NewFieldFrameOB5.EncodedFieldFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have r:base q∉(balancedSharedPorts base (base 2409)).r:=by
    rw [balancedSharedPorts_r]
    exact not_block q 2056 256 (by omega)
  have y:base q∉(balancedSharedPorts base (base 2409)).y:=by
    rw [balancedSharedPorts_y]
    exact not_block q 770 256 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ r y)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem env_zero (origin : BasisState) (env : Env base origin)
    (hr : origin (base 2312)=false) (q : Nat) (hq : q=766 ∨ q=768) : origin (base q)=false := by
  apply OneBankCell5.clean_of_env_work base (base 2409) origin env hr
  rw [OneBankCell5.ports_work]
  rcases hq with rfl|rfl <;> simp [OneBankCell5.workIds]

def swap : Equiv.Perm Wire:=Equiv.swap (base 766) (base 768)
def centerT : Program:=renameProgram swap NewHalfFieldOB5.centerT
def canonT : Program:=renameProgram swap NewHalfFieldOB5.canonT

theorem center_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedFieldFrame origin (X/2) 0 (run centerT m s) := by
  have old:=NewHalfFieldOB5.center_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=766 ∨ q=768) : s.basis (base q)=false :=
    (canonical_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=766 ∨ q=768) : (run NewHalfFieldOB5.centerT m s).basis (base q)=false :=
    (field_at origin (X/2) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 766) (base 768) NewHalfFieldOB5.centerT s m
    (before 766 (Or.inl rfl)) (before 768 (Or.inr rfl))
    (after 766 (Or.inl rfl)) (after 768 (Or.inr rfl))
  simpa only [centerT,swap,eq] using old

theorem canon_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run canonT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  have old:=NewHalfFieldOB5.canon_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=766 ∨ q=768) : s.basis (base q)=false :=
    (field_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=766 ∨ q=768) : (run NewHalfFieldOB5.canonT m s).basis (base q)=false :=
    (canonical_at origin (2*X) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 766) (base 768) NewHalfFieldOB5.canonT s m
    (before 766 (Or.inl rfl)) (before 768 (Or.inr rfl))
    (after 766 (Or.inl rfl)) (after 768 (Or.inr rfl))
  simpa only [canonT,swap,eq] using old
theorem endpoint_counts : toffoliCount centerT=254 ∧ measurementCount centerT=254 ∧
    toffoliCount canonT=254 ∧ measurementCount canonT=254 := by
  simpa only [centerT,canonT,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
    using NewHalfFieldOB5.endpoint_counts

theorem endpoint_physical (hn : (skywalkSharedWires base).Nodup) :
    GatePhysical centerT ∧ GatePhysical canonT ∧ GatePhysical NewHalfFieldOB5.copyN := by
  have old:=NewHalfFieldOB5.endpoint_physical hn
  exact ⟨gatePhysical_rename swap swap.injective _ old.1,
    gatePhysical_rename swap swap.injective _ old.2.1,old.2.2⟩

theorem endpoint_gateSlots_le : Challenge.gateSlots centerT≤6000 ∧ Challenge.gateSlots canonT≤6000 ∧
    Challenge.gateSlots NewHalfFieldOB5.copyN≤256 := by
  simpa only [centerT,canonT,Baselines.rename_gateSlots] using NewHalfFieldOB5.endpoint_gateSlots_le

theorem old_unused (q : Nat) (hq : q=768 ∨ q=2312) :
    base q∉wires NewHalfFieldOB5.centerT ∧ base q∉wires NewHalfFieldOB5.canonT := by
  have no : base q∉(HalfField.ids.map base).toFinset := by
    intro h
    obtain ⟨i,hi,e⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
    have eq:=base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
    omega
  have a:base q∉wires NewHalfField5.centerT:=fun h=>no (@HalfField.centerT_sites (base q) h)
  have b:base q∉wires NewHalfField5.canonT:=fun h=>no (@HalfField.canonT_sites (base q) h)
  have fix : NewHalfFieldOB5.endpointMap (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  exact ⟨rename_avoid _ _ _ fix a,rename_avoid _ _ _ fix b⟩

theorem plus_free : base 766∉wires centerT ∧ base 766∉wires canonT := by
  have avoid (P : Program) (hp : base 768∉wires P) : base 766∉wires (renameProgram swap P) := by
    rw [renameProgram_support]
    intro used
    obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
    have back:swap (base 768)=base 766:=Equiv.swap_apply_right _ _
    have same:old=base 768:=swap.injective (e.trans back.symm)
    exact hp (same ▸ used)
  exact ⟨avoid _ (old_unused 768 (Or.inl rfl)).1,avoid _ (old_unused 768 (Or.inl rfl)).2⟩

theorem parity_free : base 2312∉wires centerT ∧ base 2312∉wires canonT := by
  have fix:swap (base 2312)=base 2312:=by decide +kernel
  exact ⟨rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).1,
    rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).2⟩

end ECDSAAdd.Entrant.NewOwnPlusEndpoint

namespace ECDSAAdd.Entrant.NewOwnGuardEndpoint
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
open OwnPlusHost
attribute [local irreducible] run wires

theorem encoder_free (q : Nat) (hq : q=765 ∨ q=767) :
    base q∉wires (NewHistory5.allEncode base 102) := by
  intro used
  have mem:=NewHistory5.allEncode_history_support base 102 (by omega) used
  simp only [List.mem_toFinset,List.mem_append] at mem
  rcases mem with lo|hi
  · exact not_block q 0 512 (by omega) lo
  · exact not_block q 1028 512 (by omega) hi

theorem canonical_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=765 ∨ q=767) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have z:base q∉(skywalkSharedField base).z:=by
    rw [skywalkShared_field_z]
    exact not_block q 2056 257 (by omega)
  have a:base q∉(skywalkSharedField base).a:=not_block q 770 257 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ z a)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem field_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=765 ∨ q=767) (input : NewFieldFrameOB5.EncodedFieldFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have r:base q∉(balancedSharedPorts base (base 2409)).r:=by
    rw [balancedSharedPorts_r]
    exact not_block q 2056 256 (by omega)
  have y:base q∉(balancedSharedPorts base (base 2409)).y:=by
    rw [balancedSharedPorts_y]
    exact not_block q 770 256 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ r y)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem env_zero (origin : BasisState) (env : Env base origin)
    (hr : origin (base 2312)=false) (q : Nat) (hq : q=765 ∨ q=767) : origin (base q)=false := by
  apply OneBankCell5.clean_of_env_work base (base 2409) origin env hr
  rw [OneBankCell5.ports_work]
  rcases hq with rfl|rfl <;> simp [OneBankCell5.workIds]

def swap : Equiv.Perm Wire:=Equiv.swap (base 765) (base 767)
def centerT : Program:=renameProgram swap NewOwnPlusEndpoint.centerT
def canonT : Program:=renameProgram swap NewOwnPlusEndpoint.canonT

theorem center_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedFieldFrame origin (X/2) 0 (run centerT m s) := by
  have old:=NewOwnPlusEndpoint.center_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=765 ∨ q=767) : s.basis (base q)=false :=
    (canonical_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=765 ∨ q=767) : (run NewOwnPlusEndpoint.centerT m s).basis (base q)=false :=
    (field_at origin (X/2) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 765) (base 767) NewOwnPlusEndpoint.centerT s m
    (before 765 (Or.inl rfl)) (before 767 (Or.inr rfl))
    (after 765 (Or.inl rfl)) (after 767 (Or.inr rfl))
  simpa only [centerT,swap,eq] using old

theorem canon_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run canonT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  have old:=NewOwnPlusEndpoint.canon_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=765 ∨ q=767) : s.basis (base q)=false :=
    (field_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=765 ∨ q=767) : (run NewOwnPlusEndpoint.canonT m s).basis (base q)=false :=
    (canonical_at origin (2*X) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 765) (base 767) NewOwnPlusEndpoint.canonT s m
    (before 765 (Or.inl rfl)) (before 767 (Or.inr rfl))
    (after 765 (Or.inl rfl)) (after 767 (Or.inr rfl))
  simpa only [canonT,swap,eq] using old
theorem endpoint_counts : toffoliCount centerT=254 ∧ measurementCount centerT=254 ∧
    toffoliCount canonT=254 ∧ measurementCount canonT=254 := by
  simpa only [centerT,canonT,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
    using NewOwnPlusEndpoint.endpoint_counts

theorem endpoint_physical (hn : (skywalkSharedWires base).Nodup) :
    GatePhysical centerT ∧ GatePhysical canonT ∧ GatePhysical NewHalfFieldOB5.copyN := by
  have old:=NewOwnPlusEndpoint.endpoint_physical hn
  exact ⟨gatePhysical_rename swap swap.injective _ old.1,
    gatePhysical_rename swap swap.injective _ old.2.1,old.2.2⟩

theorem endpoint_gateSlots_le : Challenge.gateSlots centerT≤6000 ∧ Challenge.gateSlots canonT≤6000 ∧
    Challenge.gateSlots NewHalfFieldOB5.copyN≤256 := by
  simpa only [centerT,canonT,Baselines.rename_gateSlots] using NewOwnPlusEndpoint.endpoint_gateSlots_le

theorem old_unused (q : Nat) (hq : q=767 ∨ q=2312) :
    base q∉wires NewOwnPlusEndpoint.centerT ∧ base q∉wires NewOwnPlusEndpoint.canonT := by
  have no : base q∉(HalfField.ids.map base).toFinset := by
    intro h
    obtain ⟨i,hi,e⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
    have eq:=base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
    omega
  have a:base q∉wires NewHalfField5.centerT:=fun h=>no (@HalfField.centerT_sites (base q) h)
  have b:base q∉wires NewHalfField5.canonT:=fun h=>no (@HalfField.canonT_sites (base q) h)
  have fix : NewHalfFieldOB5.endpointMap (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  have first : base q∉wires NewHalfFieldOB5.centerT ∧ base q∉wires NewHalfFieldOB5.canonT :=
    ⟨OwnPlusHost.rename_avoid _ _ _ fix a,OwnPlusHost.rename_avoid _ _ _ fix b⟩
  have fixPlus : NewOwnPlusEndpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fixPlus first.1,OwnPlusHost.rename_avoid _ _ _ fixPlus first.2⟩

theorem plus_free : base 765∉wires centerT ∧ base 765∉wires canonT := by
  have avoid (P : Program) (hp : base 767∉wires P) : base 765∉wires (renameProgram swap P) := by
    rw [renameProgram_support]
    intro used
    obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
    have back:swap (base 767)=base 765:=Equiv.swap_apply_right _ _
    have same:old=base 767:=swap.injective (e.trans back.symm)
    exact hp (same ▸ used)
  exact ⟨avoid _ (old_unused 767 (Or.inl rfl)).1,avoid _ (old_unused 767 (Or.inl rfl)).2⟩

theorem parity_free : base 2312∉wires centerT ∧ base 2312∉wires canonT := by
  have fix:swap (base 2312)=base 2312:=by decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).1,
    OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).2⟩

end ECDSAAdd.Entrant.NewOwnGuardEndpoint

namespace ECDSAAdd.Entrant.NewOwnQ4Endpoint
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
open OwnPlusHost
attribute [local irreducible] run wires

theorem encoder_free (q : Nat) (hq : q=767 ∨ q=1026) :
    base q∉wires (NewHistory5.allEncode base 102) := by
  intro used
  have mem:=NewHistory5.allEncode_history_support base 102 (by omega) used
  simp only [List.mem_toFinset,List.mem_append] at mem
  rcases mem with lo|hi
  · exact not_block q 0 512 (by omega) lo
  · exact not_block q 1028 512 (by omega) hi

theorem canonical_at (origin : BasisState) (env : Env base origin) (X : Fp) (s : State) (q : Nat)
    (hq : q=767 ∨ q=1026) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    s.basis (base q)=origin (base q) := by
  rcases hq with rfl|rfl
  · exact NewOwnGuardEndpoint.canonical_at origin X 0 s 767 (Or.inr rfl) input
  · obtain ⟨raw,_,pair,encoded⟩:=input
    have member : base 1026∈(skywalkSharedField base).a := by
      simp only [skywalkSharedField,wireBlock,List.mem_map,List.mem_range'_1]
      exact ⟨1026,by omega,rfl⟩
    have value : regValue (skywalkSharedField base).a raw.basis=0 := by simpa using pair.2.1
    have rawzero : raw.basis (base 1026)=false := (regValue_zero _ _).mp value _ member
    have encodedzero : (pullState (OB5.sig 511) s).basis (base 1026)=false := by
      rw [encoded]
      exact (run_preserves_outside _ [] raw _ (encoder_free 1026 (Or.inr rfl))).trans rawzero
    have fix : OB5.sig 511 (base 1026)=base 1026 := by decide +kernel
    have zero : s.basis (base 1026)=false := by simpa only [pullState,fix] using encodedzero
    exact zero.trans env.2.2.symm

theorem field_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=767 ∨ q=1026) (input : NewFieldFrameOB5.EncodedFieldFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have r:base q∉(balancedSharedPorts base (base 2409)).r:=by
    rw [balancedSharedPorts_r]
    exact not_block q 2056 256 (by omega)
  have y:base q∉(balancedSharedPorts base (base 2409)).y:=by
    rw [balancedSharedPorts_y]
    exact not_block q 770 256 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ r y)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem env_zero (origin : BasisState) (env : Env base origin)
    (hr : origin (base 2312)=false) (q : Nat) (hq : q=767 ∨ q=1026) : origin (base q)=false := by
  rcases hq with rfl|rfl
  · exact NewOwnGuardEndpoint.env_zero origin env hr 767 (Or.inr rfl)
  · exact env.2.2

def swap : Equiv.Perm Wire:=Equiv.swap (base 767) (base 1026)
def centerT : Program:=renameProgram swap NewOwnGuardEndpoint.centerT
def canonT : Program:=renameProgram swap NewOwnGuardEndpoint.canonT

theorem center_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedFieldFrame origin (X/2) 0 (run centerT m s) := by
  have old:=NewOwnGuardEndpoint.center_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=767 ∨ q=1026) : s.basis (base q)=false :=
    (canonical_at origin env X s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=767 ∨ q=1026) : (run NewOwnGuardEndpoint.centerT m s).basis (base q)=false :=
    (field_at origin (X/2) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 767) (base 1026) NewOwnGuardEndpoint.centerT s m
    (before 767 (Or.inl rfl)) (before 1026 (Or.inr rfl))
    (after 767 (Or.inl rfl)) (after 1026 (Or.inr rfl))
  simpa only [centerT,swap,eq] using old

theorem canon_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run canonT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  have old:=NewOwnGuardEndpoint.canon_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=767 ∨ q=1026) : s.basis (base q)=false :=
    (field_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=767 ∨ q=1026) : (run NewOwnGuardEndpoint.canonT m s).basis (base q)=false :=
    (canonical_at origin env (2*X) _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 767) (base 1026) NewOwnGuardEndpoint.canonT s m
    (before 767 (Or.inl rfl)) (before 1026 (Or.inr rfl))
    (after 767 (Or.inl rfl)) (after 1026 (Or.inr rfl))
  simpa only [canonT,swap,eq] using old
theorem endpoint_counts : toffoliCount centerT=254 ∧ measurementCount centerT=254 ∧
    toffoliCount canonT=254 ∧ measurementCount canonT=254 := by
  simpa only [centerT,canonT,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
    using NewOwnGuardEndpoint.endpoint_counts

theorem endpoint_physical (hn : (skywalkSharedWires base).Nodup) :
    GatePhysical centerT ∧ GatePhysical canonT ∧ GatePhysical NewHalfFieldOB5.copyN := by
  have old:=NewOwnGuardEndpoint.endpoint_physical hn
  exact ⟨gatePhysical_rename swap swap.injective _ old.1,
    gatePhysical_rename swap swap.injective _ old.2.1,old.2.2⟩

theorem endpoint_gateSlots_le : Challenge.gateSlots centerT≤6000 ∧ Challenge.gateSlots canonT≤6000 ∧
    Challenge.gateSlots NewHalfFieldOB5.copyN≤256 := by
  simpa only [centerT,canonT,Baselines.rename_gateSlots] using NewOwnGuardEndpoint.endpoint_gateSlots_le

theorem old_unused (q : Nat) (hq : q=1026 ∨ q=2312) :
    base q∉wires NewOwnGuardEndpoint.centerT ∧ base q∉wires NewOwnGuardEndpoint.canonT := by
  have no : base q∉(HalfField.ids.map base).toFinset := by
    intro h
    obtain ⟨i,hi,e⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
    have eq:=base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
    omega
  have a:base q∉wires NewHalfField5.centerT:=fun h=>no (@HalfField.centerT_sites (base q) h)
  have b:base q∉wires NewHalfField5.canonT:=fun h=>no (@HalfField.canonT_sites (base q) h)
  have fix : NewHalfFieldOB5.endpointMap (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  have first : base q∉wires NewHalfFieldOB5.centerT ∧ base q∉wires NewHalfFieldOB5.canonT :=
    ⟨OwnPlusHost.rename_avoid _ _ _ fix a,OwnPlusHost.rename_avoid _ _ _ fix b⟩
  have fixPlus : NewOwnPlusEndpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  have second : base q∉wires NewOwnPlusEndpoint.centerT ∧ base q∉wires NewOwnPlusEndpoint.canonT :=
    ⟨OwnPlusHost.rename_avoid _ _ _ fixPlus first.1,OwnPlusHost.rename_avoid _ _ _ fixPlus first.2⟩
  have fixGuard : NewOwnGuardEndpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fixGuard second.1,OwnPlusHost.rename_avoid _ _ _ fixGuard second.2⟩

theorem plus_free : base 767∉wires centerT ∧ base 767∉wires canonT := by
  have avoid (P : Program) (hp : base 1026∉wires P) : base 767∉wires (renameProgram swap P) := by
    rw [renameProgram_support]
    intro used
    obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
    have back:swap (base 1026)=base 767:=Equiv.swap_apply_right _ _
    have same:old=base 1026:=swap.injective (e.trans back.symm)
    exact hp (same ▸ used)
  exact ⟨avoid _ (old_unused 1026 (Or.inl rfl)).1,avoid _ (old_unused 1026 (Or.inl rfl)).2⟩

theorem parity_free : base 2312∉wires centerT ∧ base 2312∉wires canonT := by
  have fix:swap (base 2312)=base 2312:=by decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).1,
    OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).2⟩

end ECDSAAdd.Entrant.NewOwnQ4Endpoint

namespace ECDSAAdd.Entrant.NewOwnQ5Endpoint
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
open OwnPlusHost
attribute [local irreducible] run wires

theorem encoder_free (q : Nat) (hq : q=1026 ∨ q=1540) :
    base q∉wires (NewHistory5.allEncode base 102) := by
  intro used
  have mem:=NewHistory5.allEncode_history_support base 102 (by omega) used
  simp only [List.mem_toFinset,List.mem_append] at mem
  rcases mem with lo|hi
  · exact not_block q 0 512 (by omega) lo
  · exact not_block q 1028 512 (by omega) hi

theorem canonical_at (origin : BasisState) (env : Env base origin) (X : Fp) (s : State) (q : Nat)
    (hq : q=1026 ∨ q=1540) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    s.basis (base q)=origin (base q) := by
  rcases hq with rfl|rfl
  · exact NewOwnQ4Endpoint.canonical_at origin env X s 1026 (Or.inr rfl) input
  · obtain ⟨raw,_,pair,encoded⟩:=input
    have z:base 1540∉(skywalkSharedField base).z:=by
      rw [skywalkShared_field_z];exact not_block 1540 2056 257 (by omega)
    have a:base 1540∉(skywalkSharedField base).a:=not_block 1540 770 257 (by omega)
    have eq:(pullState (OB5.sig 511) s).basis (base 1540)=origin (base 1540):=by
      rw [encoded]
      exact (run_preserves_outside _ [] raw _ (encoder_free 1540 (Or.inr rfl))).trans (pair.2.2 _ z a)
    have fix:OB5.sig 511 (base 1540)=base 1540:=by decide +kernel
    simpa only [pullState,fix] using eq

theorem field_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=1026 ∨ q=1540) (input : NewFieldFrameOB5.EncodedFieldFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have r:base q∉(balancedSharedPorts base (base 2409)).r:=by
    rw [balancedSharedPorts_r]
    exact not_block q 2056 256 (by omega)
  have y:base q∉(balancedSharedPorts base (base 2409)).y:=by
    rw [balancedSharedPorts_y]
    exact not_block q 770 256 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ r y)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem env_zero (origin : BasisState) (env : Env base origin)
    (hr : origin (base 2312)=false) (q : Nat) (hq : q=1026 ∨ q=1540) : origin (base q)=false := by
  rcases hq with rfl|rfl
  · exact env.2.2
  · apply OneBankCell5.clean_of_env_work base (base 2409) origin env hr
    rw [OneBankCell5.ports_work]
    simp [OneBankCell5.workIds]

def swap : Equiv.Perm Wire:=Equiv.swap (base 1026) (base 1540)
def centerT : Program:=renameProgram swap NewOwnQ4Endpoint.centerT
def canonT : Program:=renameProgram swap NewOwnQ4Endpoint.canonT

theorem center_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedFieldFrame origin (X/2) 0 (run centerT m s) := by
  have old:=NewOwnQ4Endpoint.center_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=1026 ∨ q=1540) : s.basis (base q)=false :=
    (canonical_at origin env X s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=1026 ∨ q=1540) : (run NewOwnQ4Endpoint.centerT m s).basis (base q)=false :=
    (field_at origin (X/2) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 1026) (base 1540) NewOwnQ4Endpoint.centerT s m
    (before 1026 (Or.inl rfl)) (before 1540 (Or.inr rfl))
    (after 1026 (Or.inl rfl)) (after 1540 (Or.inr rfl))
  simpa only [centerT,swap,eq] using old

theorem canon_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run canonT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  have old:=NewOwnQ4Endpoint.canon_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=1026 ∨ q=1540) : s.basis (base q)=false :=
    (field_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=1026 ∨ q=1540) : (run NewOwnQ4Endpoint.canonT m s).basis (base q)=false :=
    (canonical_at origin env (2*X) _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 1026) (base 1540) NewOwnQ4Endpoint.canonT s m
    (before 1026 (Or.inl rfl)) (before 1540 (Or.inr rfl))
    (after 1026 (Or.inl rfl)) (after 1540 (Or.inr rfl))
  simpa only [canonT,swap,eq] using old
theorem endpoint_counts : toffoliCount centerT=254 ∧ measurementCount centerT=254 ∧
    toffoliCount canonT=254 ∧ measurementCount canonT=254 := by
  simpa only [centerT,canonT,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
    using NewOwnQ4Endpoint.endpoint_counts

theorem endpoint_physical (hn : (skywalkSharedWires base).Nodup) :
    GatePhysical centerT ∧ GatePhysical canonT ∧ GatePhysical NewHalfFieldOB5.copyN := by
  have old:=NewOwnQ4Endpoint.endpoint_physical hn
  exact ⟨gatePhysical_rename swap swap.injective _ old.1,
    gatePhysical_rename swap swap.injective _ old.2.1,old.2.2⟩

theorem endpoint_gateSlots_le : Challenge.gateSlots centerT≤6000 ∧ Challenge.gateSlots canonT≤6000 ∧
    Challenge.gateSlots NewHalfFieldOB5.copyN≤256 := by
  simpa only [centerT,canonT,Baselines.rename_gateSlots] using NewOwnQ4Endpoint.endpoint_gateSlots_le

theorem old_unused (q : Nat) (hq : q=1540 ∨ q=2312) :
    base q∉wires NewOwnQ4Endpoint.centerT ∧ base q∉wires NewOwnQ4Endpoint.canonT := by
  let i : Nat:=if q=1540 then 512 else 2312
  have back : NewHalfFieldOB5.endpointMap (base i)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  have no : base i∉(HalfField.ids.map base).toFinset := by
    intro h
    obtain ⟨j,hj,e⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
    have eq:=base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
    rcases hq with rfl|rfl <;> simp only [i,if_pos rfl,if_neg (by decide : (2312:Nat)≠1540)] at eq <;> omega
  have lift (P : Program) (hP : wires P⊆(HalfField.ids.map base).toFinset) :
      base q∉wires (renameProgram NewHalfFieldOB5.endpointMap P) := by
    rw [renameProgram_support]
    intro used
    obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
    have same:old=base i:=NewHalfFieldOB5.endpointMap.injective (e.trans back.symm)
    exact no (same ▸ hP used)
  have first : base q∉wires NewHalfFieldOB5.centerT ∧ base q∉wires NewHalfFieldOB5.canonT :=
    ⟨lift _ HalfField.centerT_sites,lift _ HalfField.canonT_sites⟩
  have fixPlus : NewOwnPlusEndpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  have second : base q∉wires NewOwnPlusEndpoint.centerT ∧ base q∉wires NewOwnPlusEndpoint.canonT :=
    ⟨OwnPlusHost.rename_avoid _ _ _ fixPlus first.1,OwnPlusHost.rename_avoid _ _ _ fixPlus first.2⟩
  have fixGuard : NewOwnGuardEndpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  have third : base q∉wires NewOwnGuardEndpoint.centerT ∧ base q∉wires NewOwnGuardEndpoint.canonT :=
    ⟨OwnPlusHost.rename_avoid _ _ _ fixGuard second.1,OwnPlusHost.rename_avoid _ _ _ fixGuard second.2⟩
  have fixQ4 : NewOwnQ4Endpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fixQ4 third.1,OwnPlusHost.rename_avoid _ _ _ fixQ4 third.2⟩

theorem plus_free : base 1026∉wires centerT ∧ base 1026∉wires canonT := by
  have avoid (P : Program) (hp : base 1540∉wires P) : base 1026∉wires (renameProgram swap P) := by
    rw [renameProgram_support]
    intro used
    obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
    have back:swap (base 1540)=base 1026:=Equiv.swap_apply_right _ _
    have same:old=base 1540:=swap.injective (e.trans back.symm)
    exact hp (same ▸ used)
  exact ⟨avoid _ (old_unused 1540 (Or.inl rfl)).1,avoid _ (old_unused 1540 (Or.inl rfl)).2⟩

theorem parity_free : base 2312∉wires centerT ∧ base 2312∉wires canonT := by
  have fix:swap (base 2312)=base 2312:=by decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).1,
    OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).2⟩


end ECDSAAdd.Entrant.NewOwnQ5Endpoint

end

-- Public component FrontierEntry1591FieldSupport.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierReplay1591
open Arithmetic MappedCompressed
attribute [local irreducible] wires

theorem packet_support_eq (divide : Bool) (j : Nat) :
    wires (packet divide j)=wires (OneFlagReplay.packet divide j) := by
  simp only [packet,OneFlagReplay.packet,renameProgram_support,basePacket,
    OneFlagReplay.basePacket,wires_append,NewHistory5.encode_support_eq,NewHistory5.decode_support_eq]
  rfl

theorem first_support_eq (divide : Bool) :
    wires (firstPacket divide)=wires (OneFlagReplay.firstPacket divide) := by
  simp only [firstPacket,OneFlagReplay.firstPacket,renameProgram_support,baseFirstPacket,
    OneFlagReplay.baseFirstPacket,wires_append,NewHistory5.encode_support_eq,NewHistory5.decode_support_eq]
  rfl

theorem groups_support_eq (divide : Bool) (j n : Nat) :
    wires (groups divide j n)=wires (OneFlagReplay.groups divide j n) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases divide <;> simp only [groups,OneFlagReplay.groups,PacketSequence.program,
      Bool.false_eq_true,if_false,if_true,wires_append]
    · rw [←OneFlagReplay.groups,←groups,ih,packet_support_eq]
    · rw [←OneFlagReplay.groups,←groups,ih,packet_support_eq]

theorem support_eq (divide : Bool) :
    wires (replay divide)=wires (OneFlagReplay.replay divide) := by
  have last : endPacket divide=OneFlagReplay.endPacket divide := rfl
  cases divide <;> simp only [replay,OneFlagReplay.replay,renameProgram_support,
    logicalReplay,OneFlagReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,first_support_eq,groups_support_eq,last]
end ECDSAAdd.Entrant.FrontierReplay1591

namespace ECDSAAdd.Entrant.FrontierSW1591
open Arithmetic MappedCompressed
attribute [local irreducible] wires

theorem packet_support_eq (divide : Bool) (j : Nat) :
    wires (packetS divide j)=wires (OneFlagSW.packetS divide j) := by
  simp only [packetS,OneFlagSW.packetS,renameProgram_support,basePacketS,
    OneFlagSW.basePacketS,wires_append,NewHistory5.encode_support_eq,NewHistory5.decode_support_eq]
  rfl

theorem first_support_eq (divide : Bool) :
    wires (firstPacketS divide)=wires (OneFlagSW.firstPacketS divide) := by
  simp only [firstPacketS,OneFlagSW.firstPacketS,renameProgram_support,baseFirstPacketS,
    OneFlagSW.baseFirstPacketS,wires_append,NewHistory5.encode_support_eq,NewHistory5.decode_support_eq]
  rfl

theorem groups_support_eq (divide : Bool) (j n : Nat) :
    wires (groupsS divide j n)=wires (OneFlagSW.groupsS divide j n) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases divide <;> simp only [groupsS,OneFlagSW.groupsS,PacketSequence.program,
      Bool.false_eq_true,if_false,if_true,wires_append]
    · rw [←OneFlagSW.groupsS,←groupsS,ih,packet_support_eq]
    · rw [←OneFlagSW.groupsS,←groupsS,ih,packet_support_eq]

theorem support_eq (divide : Bool) :
    wires (replayS divide)=wires (OneFlagSW.replayS divide) := by
  have last : endPacketS divide=OneFlagSW.endPacketS divide := rfl
  cases divide <;> simp only [replayS,OneFlagSW.replayS,renameProgram_support,
    logicalReplayS,OneFlagSW.logicalReplayS,Bool.false_eq_true,if_false,if_true,
    wires_append,first_support_eq,groups_support_eq,last]
end ECDSAAdd.Entrant.FrontierSW1591

namespace ECDSAAdd.Entrant.FrontierFieldSupport1591
open Arithmetic MappedCompressed OneFlagReplay
attribute [local irreducible] wires

def host : Wire := base 1543

private theorem no_append (q : Wire) (P Q : Program)
    (hp : q∉wires P) (hq : q∉wires Q) : q∉wires (P++Q) := by
  simpa only [wires_append,Finset.mem_union,not_or] using And.intro hp hq

private theorem no_rename (f : Wire → Wire) (hf : Function.Injective f)
    (a b : Wire) (P : Program) (fix : f a=b) (hp : a∉wires P) :
    b∉wires (renameProgram f P) := by
  intro used
  rw [renameProgram_support] at used
  obtain ⟨old,mem,eq⟩ := Finset.mem_image.mp used
  exact hp (hf (eq.trans fix.symm) ▸ mem)

private theorem codec_free (start : Nat) (hs : start+5≤510) (P : Program)
    (hp : P=History5.encode base start ∨ P=History5.decode base start) :
    base 1538∉wires P := by
  intro used
  obtain ⟨r,eq⟩ := History5.history_gate_mem base start P hp _ used
  have same := base_injective eq
  have hr := r.isLt
  unfold History5.historyMap History5.historyId at same
  split_ifs at same <;> omega

private theorem field_free : base 1538∉fieldSites := by
  intro used
  rcases List.mem_cons.mp (List.mem_toFinset.mp used) with eq | used
  · have same := base_injective eq; omega
  · obtain ⟨i,hi,eq⟩ := List.mem_map.mp used
    have same := base_injective eq
    simp only [Q6EndpointCell.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false] at hi
    omega

private theorem read_free (j : Nat) (hj : j<102) : base 1538∉readSites (5*j) := by
  intro used
  simp only [readSites,Finset.mem_union] at used
  rcases used with (used | used) | used
  · exact field_free used
  · simp only [Finset.mem_insert,Finset.mem_singleton] at used
    rcases used with eq | eq <;> have same := base_injective eq <;> omega
  · exact codec_free (5*j) (by omega) _ (Or.inl rfl) used

private theorem pi_fix (j : Nat) (hj : j<102) :
    shifted (Placement5.pi j) (base 1538)=base 1538 := by
  rw [shifted_base,Placement5.pi_outside j 1538 hj]
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
  omega

private theorem packet_free (divide : Bool) (j : Nat) (hj : j<102) :
    base 1538∉wires (packet divide j) := by
  apply no_rename _ (shifted (Placement5.pi j)).injective _ _ _ (pi_fix j hj)
  apply no_append
  · apply no_append
    · exact codec_free _ (by omega) _ (Or.inr rfl)
    · exact fun used => read_free j hj (body_support divide j hj used)
  · exact codec_free _ (by omega) _ (Or.inl rfl)

private theorem first_free (divide : Bool) : base 1538∉wires (firstPacket divide) := by
  apply no_rename _ (shifted (Placement5.pi 0)).injective _ _ _ (pi_fix 0 (by omega))
  apply no_append
  · apply no_append
    · exact codec_free 0 (by omega) _ (Or.inr rfl)
    · exact fun used => read_free 0 (by omega) (firstBody_support divide used)
  · exact codec_free 0 (by omega) _ (Or.inl rfl)

private theorem end_free (divide : Bool) : base 1538∉wires (endPacket divide) := by
  have fix : shifted Placement5.pi0 (base 1538)=base 1538 := by
    rw [shifted_base,Placement5.pi0_outside]
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
    omega
  apply no_rename _ (shifted Placement5.pi0).injective _ _ _ fix
  intro used
  rcases Finset.mem_union.mp (rawEnd_support divide used) with h | h
  · exact field_free h
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with eq | eq <;> have same := base_injective eq <;> omega

private theorem groups_free (divide : Bool) (j n : Nat) (hn : j+n≤102) :
    base 1538∉wires (groups divide j n) := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,wires]
  | succ n ih =>
    have head := packet_free divide j (by omega)
    have tail := ih (j+1) (by omega)
    cases divide
    · exact no_append _ _ _ tail head
    · exact no_append _ _ _ head tail

private theorem old_replay_free (divide : Bool) : host∉wires (replay divide) := by
  have logical : base 1538∉wires (logicalReplay divide) := by
    have first := first_free divide
    have mid := groups_free divide 1 101 (by omega)
    have last := end_free divide
    cases divide
    · exact no_append _ _ _ (no_append _ _ _ last mid) first
    · exact no_append _ _ _ (no_append _ _ _ first mid) last
  exact no_rename _ (OB5.sig_injective 511 (by omega)) _ _ _ (by decide +kernel) logical

theorem replay_avoids (divide : Bool) : host∉wires (FrontierSW1591.replayS divide) := by
  rw [FrontierSW1591.support_eq]
  exact fun used => old_replay_free divide ((OneFlagSW.selReplay_sel divide).sub.wires_sub used)

private theorem old_endpoint_free (P : Program)
    (hp : wires P⊆(HalfField.ids.map base).toFinset) : base 1538∉wires P := by
  intro used
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp (hp used))
  have same := base_injective eq
  simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hi
  omega

private theorem endpoint_host : HalfFieldOB5.endpointMap (base 1538)=host := by
  change OB5.sig 511 (Equiv.swap (base 1796) (base 1285)
    (shifted (Placement5.pi 51) (shifted HalfFieldOB5.bank (base 1538))))=host
  have bank : HalfFieldOB5.bank 1538=1538 := by decide +kernel
  rw [shifted_base,bank,shifted_base,
    Placement5.pi_outside 51 1538 (by omega) (by
      unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
      omega)]
  decide +kernel

theorem endpoints_avoid : host∉wires OwnQ5Endpoint.centerT ∧ host∉wires OwnQ5Endpoint.canonT := by
  have center := no_rename _ HalfFieldOB5.endpointMap.injective _ _ _ endpoint_host
    (old_endpoint_free _ HalfField.centerT_sites)
  have canon := no_rename _ HalfFieldOB5.endpointMap.injective _ _ _ endpoint_host
    (old_endpoint_free _ HalfField.canonT_sites)
  have step (e : Equiv.Perm Wire) (P : Program) (fix : e host=host) (hp : host∉wires P) :
      host∉wires (renameProgram e P) := no_rename e e.injective _ _ _ fix hp
  exact ⟨step OwnQ5Endpoint.swap _ (by decide +kernel)
      (step OwnQ4Endpoint.swap _ (by decide +kernel)
        (step OwnGuardEndpoint.swap _ (by decide +kernel)
          (step OwnPlusEndpoint.swap _ (by decide +kernel) center))),
    step OwnQ5Endpoint.swap _ (by decide +kernel)
      (step OwnQ4Endpoint.swap _ (by decide +kernel)
        (step OwnGuardEndpoint.swap _ (by decide +kernel)
          (step OwnPlusEndpoint.swap _ (by decide +kernel) canon)))⟩

theorem copy_avoids : host∉wires HalfFieldOB5.copyN := by
  intro used
  have mem := copyRegister_wires_subset none
    (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y used
  simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append,
    balancedSharedPorts_r,balancedSharedPorts_y] at mem
  rcases mem with r | y
  · exact OwnPlusHost.not_block 1543 2056 256 (by omega) r
  · exact OwnPlusHost.not_block 1543 770 256 (by omega) y

theorem segment_avoids (divide : Bool) : host∉wires (FrontierSW1591.segmentS divide) := by
  have ends := endpoints_avoid
  have replay := replay_avoids divide
  cases divide
  · exact no_append _ _ _ ends.1 (no_append _ _ _ copy_avoids (no_append _ _ _ replay ends.2))
  · exact no_append _ _ _ ends.1 (no_append _ _ _ replay (no_append _ _ _ copy_avoids ends.2))

theorem hosted_avoids (P : Program) (hp : host∉wires P) :
    host∉wires ([Instr.X (base 511)]++(renameProgram HostOB5.hostSwap P++[Instr.X (base 511)])) := by
  have x : host∉wires [Instr.X (base 511)] := by simp [host,wires,Instr.wires,base]
  exact no_append _ _ _ x (no_append _ _ _
    (no_rename _ HostOB5.hostSwap_injective _ _ _ (by decide +kernel) hp) x)

end ECDSAAdd.Entrant.FrontierFieldSupport1591

end

-- Public component ParityHostTransport5.lean
section
/-! Complete-State transport from a clean work site to a clean, unused host.
The host cleanliness is a boundary fact; no assumption is made about other sites. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace ECDSAAdd.Entrant.ParityHostTransport5
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

end ECDSAAdd.Entrant.ParityHostTransport5

end

-- Public component ParityField1591.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace ECDSAAdd.Entrant.ParityField1591
open ParityHost5 TraceParity5 Challenge Arithmetic RecordedQuantum
attribute [local irreducible] run wires

def clear (host : Wire) (s : State) : State :=
  ⟨s.phase,writeBit s.basis host false⟩

theorem run_clear (P : Program) (host : Wire) (s : State) (m : List Bool)
    (free : host∉wires P) : run P m (clear host s)=clear host (run P m s) := by
  have sameOnSupport := run_measured_locality P (wires P) (fun _ h => h)
    (clear host s) s m rfl (by
      intro q hq
      have ne : q≠host := fun e => free (e ▸ hq)
      simp only [clear,writeBit,Function.update_of_ne ne])
  apply State.extensionality
  · exact sameOnSupport.1
  · funext q
    by_cases same : q=host
    · subst q
      rw [run_preserves_outside P m (clear host s) host free]
      simp only [clear,writeBit,Function.update_self]
    · simp only [clear,writeBit,Function.update_of_ne same]
      by_cases used : q∈wires P
      · exact sameOnSupport.2 q used
      · change (run P m (clear host s)).basis q=(run P m s).basis q
        rw [run_preserves_outside P m (clear host s) q used,
          run_preserves_outside P m s q used]
        simp only [clear,writeBit,Function.update_of_ne same]

def program (controls : List Wire) (work host : Wire) (P : Program) : Program :=
  setup controls host ++ ParityHostTransport5.program work host P ++ setup controls host

/-- The original host value can be nonzero. The setup clears that value and
the final setup restores it after the complete field segment. -/
theorem run_eq (controls : List Wire) (work host : Wire) (P : Program)
    (s : State) (m : List Bool) (distinct : work≠host)
    (outside : host∉controls) (free : host∉wires P)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis))
    (workIn : s.basis work=false) (workOut : (run P m s).basis work=false)
    (payload : ∀q∈controls,(run P m s).basis q=s.basis q) :
    run (program controls work host P) m s=run P m s := by
  let out := run P m s
  have hostOut : out.basis host=s.basis host := run_preserves_outside P m s host free
  have initial := setup_zero controls host s [] outside parity
  have base := run_clear P host s m free
  have field := ParityHostTransport5.run_eq work host P (clear host s) m
    (by simp only [clear,writeBit,Function.update_of_ne distinct,workIn])
    (by simp only [clear,writeBit,Function.update_self])
    (by rw [base];simp only [clear,writeBit,Function.update_of_ne distinct,workOut]) free
  rw [base] at field
  have restored := restore_run controls host s (clear host out)
    (m.drop (measurementCount P)) outside parity
    (by
      intro q hq
      have ne : q≠host := fun e => outside (e ▸ hq)
      simpa only [clear,writeBit,Function.update_of_ne ne] using payload q hq)
    (by simp only [clear,writeBit,Function.update_self])
  have finish : run (setup controls host) (m.drop (measurementCount P))
      (clear host out)=out := by
    rw [restored]
    apply State.extensionality
    · rfl
    · funext q
      by_cases same : q=host
      · subst q;simpa only [writeBit,Function.update_self] using hostOut.symm
      · simp only [clear,writeBit,Function.update_of_ne same]
  have zeroM := (setup_counts controls host).2.1
  have bodyM := (ParityHostTransport5.counts work host P).2
  unfold program
  rw [run_append,measurementCount_append,zeroM,bodyM,Nat.zero_add,
    run_append,zeroM,List.take_zero,List.drop_zero,initial]
  change run (setup controls host) (m.drop (measurementCount P))
    (run (ParityHostTransport5.program work host P) (m.take (measurementCount P))
      (clear host s))=out
  rw [←bodyM,run_take,field]
  simpa only [bodyM] using finish

theorem counts (controls : List Wire) (work host : Wire) (P : Program) :
    toffoliCount (program controls work host P)=toffoliCount P ∧
      measurementCount (program controls work host P)=measurementCount P ∧
      gateSlots (program controls work host P)=gateSlots P+2*controls.length := by
  have setup := setup_counts controls host
  have body := ParityHostTransport5.counts work host P
  have slots := ParityHostTransport5.slots work host P
  simp only [program,toffoliCount_append,measurementCount_append,gateSlots_append,
    setup.1,setup.2.1,setup.2.2,body.1,body.2,slots,Nat.zero_add,Nat.add_zero]
  exact ⟨trivial,trivial,by omega⟩

theorem physical (controls : List Wire) (work host : Wire) (P : Program)
    (outside : host∉controls) (valid : GatePhysical P) :
    GatePhysical (program controls work host P) := by
  have setup : GatePhysical (setup controls host) := by
    intro i hi
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
    have ne : q≠host := fun e => outside (e ▸ hq)
    simpa only [PhysicalInstr,ProperGate] using ne
  exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr
    ⟨setup,ParityHostTransport5.physical work host P valid⟩,setup⟩

theorem avoids_work (controls : List Wire) (work host : Wire) (P : Program)
    (distinct : work≠host) (outside : work∉controls) (free : host∉wires P) :
    work∉wires (program controls work host P) := by
  have setup : work∉wires (setup controls host) := by
    intro used
    have mem := setup_support controls host used
    simp only [Finset.mem_insert,List.mem_toFinset] at mem
    exact mem.elim distinct outside
  have body := ParityHostTransport5.avoids_work work host P free
  simpa only [program,wires_append,Finset.mem_union,not_or] using ⟨⟨setup,body⟩,setup⟩

theorem support (controls : List Wire) (work host : Wire) (P : Program) :
    wires (program controls work host P)⊆
      insert host controls.toFinset ∪ (wires P).image (Equiv.swap work host) := by
  have setup := setup_support controls host
  rw [program,wires_append,wires_append,ParityHostTransport5.support]
  intro q hq
  rcases Finset.mem_union.mp hq with h|h
  · rcases Finset.mem_union.mp h with h|h
    · exact Finset.mem_union_left _ (setup h)
    · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ (setup h)

end ECDSAAdd.Entrant.ParityField1591

end

-- Public component FrontierEntry1591Field.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry1591Field
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

def controls : List Wire := ParityHost5.payloadControls
  (fun i => OB5.sig 511 (NewHistory5.payloadWire base i))

def work : Wire := base 1797
def host : Wire := base 1543

def entryField : Program :=
  FrontierSW1591.replayS true ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)

def exitField : Program :=
  OwnQ5Endpoint.centerT ++ (HalfFieldOB5.copyN ++ FrontierSW1591.replayS false)

def hosted (P : Program) : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap P ++ [.X (base 511)])

def entryHosted : Program := hosted entryField
def exitHosted : Program := hosted exitField

def entry : Program := ParityField1591.program controls work host entryHosted
def exit : Program := ParityField1591.program controls work host exitHosted

theorem controls_length : controls.length=816 := ParityHost5.payloadControls_length _

theorem controls_member (q : Wire) (h : q∈controls) :
    ∃i,i<816 ∧ OB5.sig 511 (NewHistory5.payloadWire base i)=q := by
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp h
  exact ⟨i,List.mem_range.mp hi,eq⟩

theorem payload_index_bound (i : Nat) (hi : i<816) :
    NewHistory5.payloadWire base i=base (History5.historyId (5*(i/8))
      (NewHistory5.payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩)) ∧
    (History5.historyId (5*(i/8))
      (NewHistory5.payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩)<510 ∨
    (1028≤History5.historyId (5*(i/8))
      (NewHistory5.payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩) ∧
    History5.historyId (5*(i/8))
      (NewHistory5.payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩)<1538)) := by
  refine ⟨rfl,?_⟩
  have hq := (NewHistory5.payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩).isLt
  unfold History5.historyId
  split_ifs <;> omega

theorem host_not_controls : host∉controls := by
  intro used
  obtain ⟨i,hi,eq⟩ := controls_member host used
  have back : OB5.sig 511 (base 1538)=host := by decide +kernel
  have same := OB5.sig_injective 511 (by decide) (eq.trans back.symm)
  rw [(payload_index_bound i hi).1] at same
  have index := base_injective same
  have bound := (payload_index_bound i hi).2
  omega

theorem work_not_controls : work∉controls := by
  intro used
  obtain ⟨i,hi,eq⟩ := controls_member work used
  have back : OB5.sig 511 (base 1797)=work := by decide +kernel
  have same := OB5.sig_injective 511 (by decide) (eq.trans back.symm)
  rw [(payload_index_bound i hi).1] at same
  have index := base_injective same
  have bound := (payload_index_bound i hi).2
  omega

theorem entryHosted_avoids_host : host∉wires entryHosted := by
  apply FrontierFieldSupport1591.hosted_avoids entryField
  have replay := FrontierFieldSupport1591.replay_avoids true
  have copy := FrontierFieldSupport1591.copy_avoids
  have endpoint := FrontierFieldSupport1591.endpoints_avoid.2
  simpa only [entryField,wires_append,Finset.mem_union,not_or] using ⟨replay,copy,endpoint⟩

theorem exitHosted_avoids_host : host∉wires exitHosted := by
  apply FrontierFieldSupport1591.hosted_avoids exitField
  have replay := FrontierFieldSupport1591.replay_avoids false
  have copy := FrontierFieldSupport1591.copy_avoids
  have endpoint := FrontierFieldSupport1591.endpoints_avoid.1
  simpa only [exitField,wires_append,Finset.mem_union,not_or] using ⟨endpoint,copy,replay⟩

theorem entry_run_eq (s : State) (m : List Bool)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis))
    (workIn : s.basis work=false) (workOut : (run entryHosted m s).basis work=false)
    (payload : ∀q∈controls,(run entryHosted m s).basis q=s.basis q) :
    run entry m s=run entryHosted m s :=
  ParityField1591.run_eq controls work host entryHosted s m (by decide)
    host_not_controls entryHosted_avoids_host parity workIn workOut payload

theorem exit_run_eq (s : State) (m : List Bool)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis))
    (workIn : s.basis work=false) (workOut : (run exitHosted m s).basis work=false)
    (payload : ∀q∈controls,(run exitHosted m s).basis q=s.basis q) :
    run exit m s=run exitHosted m s :=
  ParityField1591.run_eq controls work host exitHosted s m (by decide)
    host_not_controls exitHosted_avoids_host parity workIn workOut payload

end ECDSAAdd.Entrant.FrontierEntry1591Field

end

-- Public component FrontierEntry1591FieldControl.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry1591
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires

private theorem control_not_block (start len : Nat) (bound : start+len≤2400) :
    base 2400∉wireBlock base start len := by
  intro used
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp used
  have same := base_injective eq
  simp only [List.mem_range'_1] at hi
  omega

private theorem encoder_control_free : base 2400∉wires (NewHistory5.allEncode base 102) := by
  intro used
  have mem := List.mem_toFinset.mp (NewHistory5.allEncode_history_support base 102 (by decide) used)
  simp only [List.mem_append] at mem
  rcases mem with mem|mem
  all_goals
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp mem
    have same := base_injective eq
    simp only [List.mem_range'_1] at hi
    omega

private theorem pair_control_set (r y : List Wire) (hr : base 2400∉r) (hy : base 2400∉y)
    (origin bits : BasisState) (A B : Nat) (value : Bool) (frame : PairFrame r y origin A B bits) :
    PairFrame r y (writeBit origin (base 2400) value) A B (writeBit bits (base 2400) value) := by
  have same (qs : List Wire) (off : base 2400∉qs) :
      regValue qs (writeBit bits (base 2400) value)=regValue qs bits := by
    apply regValue_congr
    intro q hq
    have ne : q≠base 2400 := fun eq => off (eq ▸ hq)
    simp only [writeBit,Function.update_of_ne ne]
  refine ⟨(same r hr).trans frame.1,(same y hy).trans frame.2.1,?_⟩
  intro q qr qy
  by_cases eq : q=base 2400
  · subst q
    simp only [writeBit,Function.update_self]
  · simpa only [writeBit,Function.update_of_ne eq] using frame.2.2 q qr qy

theorem run_control_set (P : Program) (off : base 2400∉wires P)
    (s : State) (m : List Bool) (value : Bool) :
    run P m ⟨s.phase,writeBit s.basis (base 2400) value⟩=
      ⟨(run P m s).phase,writeBit (run P m s).basis (base 2400) value⟩ := by
  let t : State := ⟨s.phase,writeBit s.basis (base 2400) value⟩
  have agrees := pool_run_agrees P (wires P) (Finset.Subset.refl _) m t s rfl (by
    intro q hq
    have ne : q≠base 2400 := fun eq => off (eq ▸ hq)
    simp only [t,writeBit,Function.update_of_ne ne])
  apply State.extensionality
  · exact agrees.1
  · funext q
    change (run P m t).basis q=writeBit (run P m s).basis (base 2400) value q
    by_cases eq : q=base 2400
    · subst q
      simpa only [t,writeBit,Function.update_self] using run_preserves_outside P m t _ off
    · have update : writeBit (run P m s).basis (base 2400) value q=(run P m s).basis q := by
        simp only [writeBit,Function.update_of_ne eq]
      rw [update]
      by_cases used : q∈wires P
      · exact agrees.2 q used
      · exact (run_preserves_outside P m t q used).trans
          ((show t.basis q=s.basis q from by simp only [t,writeBit,Function.update_of_ne eq]).trans
            (run_preserves_outside P m s q used).symm)

theorem run_control_unset (P : Program) (off : base 2400∉wires P)
    (s : State) (m : List Bool) (value : Bool) :
    run P m s=⟨(run P m ⟨s.phase,writeBit s.basis (base 2400) value⟩).phase,
      writeBit (run P m ⟨s.phase,writeBit s.basis (base 2400) value⟩).basis
        (base 2400) (s.basis (base 2400))⟩ := by
  rw [run_control_set P off s m value]
  apply State.extensionality
  · rfl
  · funext q
    by_cases eq : q=base 2400
    · subst q
      simpa only [writeBit,Function.update_self] using run_preserves_outside P m s _ off
    · simp only [writeBit,Function.update_of_ne eq]

private theorem pull_control_set (s : State) (value : Bool) :
    pullState (OB5.sig 511) ⟨s.phase,writeBit s.basis (base 2400) value⟩=
      ⟨(pullState (OB5.sig 511) s).phase,
        writeBit (pullState (OB5.sig 511) s).basis (base 2400) value⟩ := by
  apply State.extensionality
  · rfl
  · funext q
    by_cases eq : q=base 2400
    · subst q
      change writeBit s.basis (base 2400) value (OB5.sig 511 (base 2400))=
        writeBit (pullState (OB5.sig 511) s).basis (base 2400) value (base 2400)
      rw [OneFlagSW.selSig_2400]
      simp only [writeBit,Function.update_self]
    · have ne : OB5.sig 511 q≠base 2400 := fun h => eq
        (OB5.sig_injective 511 (by decide) (h.trans OneFlagSW.selSig_2400.symm))
      simp only [pullState,writeBit,Function.update_of_ne eq,Function.update_of_ne ne]

theorem frame_control_set (origin : BasisState) (X Y : Fp) (s : State) (value : Bool)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin X Y s) :
    NewFieldFrameOB5.EncodedFieldFrame (writeBit origin (base 2400) value) X Y
      ⟨s.phase,writeBit s.basis (base 2400) value⟩ := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  refine ⟨⟨raw.phase,writeBit raw.basis (base 2400) value⟩,phase,?_,?_⟩
  · apply pair_control_set _ _ _ _ origin raw.basis _ _ value frame
    · rw [balancedSharedPorts_r]
      exact control_not_block 2056 256 (by decide)
    · rw [balancedSharedPorts_y]
      exact control_not_block 770 256 (by decide)
  · rw [pull_control_set,encoded,run_control_set _ encoder_control_free]

theorem canonical_control_set (origin : BasisState) (X Y : Fp) (s : State) (value : Bool)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X Y s) :
    NewFieldFrameOB5.EncodedCanonicalFrame (writeBit origin (base 2400) value) X Y
      ⟨s.phase,writeBit s.basis (base 2400) value⟩ := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  refine ⟨⟨raw.phase,writeBit raw.basis (base 2400) value⟩,phase,?_,?_⟩
  · apply pair_control_set _ _ _ _ origin raw.basis _ _ value frame
    · rw [skywalkShared_field_z]
      exact control_not_block 2056 257 (by decide)
    · exact control_not_block 770 257 (by decide)
  · rw [pull_control_set,encoded,run_control_set _ encoder_control_free]

theorem context_control_set (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (value : Bool) : FrontierReplay1591.Context (writeBit origin (base 2400) value) := by
  refine ⟨ctx.hn,ctx.ho,ctx.hp,ctx.hf,?_,?_,?_,?_,?_⟩
  · simpa only [writeBit,Function.update_of_ne (show base 2409≠base 2400 from by decide)] using ctx.hg0
  · simpa only [writeBit,Function.update_of_ne (show base 2410≠base 2400 from by decide)] using ctx.hs0
  · exact env_write base (base 2400) (ctx.ho _ (by simp)) origin value ctx.env
  · intro j hj
    have same (q : Fin 10) :
        (writeBit origin (base 2400) value) (History5.historyMap base (5*j) q)=
          origin (History5.historyMap base (5*j) q) := by
      have bound := History5.historyId_bound (5*j) (by omega) q
      have ne : History5.historyMap base (5*j) q≠base 2400 := by
        intro eq
        have eq := base_injective eq
        omega
      simp only [writeBit,Function.update_of_ne ne]
    apply (MeasuredCodec5.legalAt_iff _ _).mpr
    intro i
    rw [same,same]
    exact (MeasuredCodec5.legalAt_iff _ _).mp (ctx.legal j hj) i
  · simpa only [writeBit,Function.update_of_ne (show base 2312≠base 2400 from by decide)] using ctx.parity

theorem source_zero_control_set (origin : BasisState) (value : Bool)
    (ha : regValue (skywalkSharedField base).a origin=0) :
    regValue (skywalkSharedField base).a (writeBit origin (base 2400) value)=0 := by
  apply Eq.trans (regValue_congr _ _ _ ?_) ha
  intro q hq
  have ne : q≠base 2400 := fun eq => control_not_block 770 257 (by decide) (eq ▸ hq)
  simp only [writeBit,Function.update_of_ne ne]

theorem trace_control_set (origin : BasisState) (value : Bool) :
    skywalkTapeControls (writeBit origin (base 2400) value) (skywalkSharedTape base)=
      skywalkTapeControls origin (skywalkSharedTape base) := by
  simp only [skywalkTapeControls,skywalkSharedTape,List.map_map]
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  have first : base i≠base 2400 := by intro eq; have same := base_injective eq; omega
  have second : base (1028+i)≠base 2400 := by intro eq; have same := base_injective eq; omega
  simp only [Function.comp_apply,writeBit,Function.update_of_ne first,Function.update_of_ne second]

theorem parity_host_control_set (controls : List Wire) (host : Wire)
    (away : host≠base 2400) (off : base 2400∉controls) (s : State) (value : Bool)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis)) :
    (writeBit s.basis (base 2400) value) host=
      TraceParity5.parity (controls.map (writeBit s.basis (base 2400) value)) := by
  have same : controls.map (writeBit s.basis (base 2400) value)=controls.map s.basis := by
    apply List.map_congr_left
    intro q hq
    have ne : q≠base 2400 := fun eq => off (eq ▸ hq)
    simp only [writeBit,Function.update_of_ne ne]
  rw [same]
  simpa only [writeBit,Function.update_of_ne away] using parity

end ECDSAAdd.Entrant.FrontierEntry1591

end
