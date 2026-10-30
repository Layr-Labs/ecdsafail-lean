import ECDSAAdd.Submission.Entrant.TraceParity5
import ECDSAAdd.Challenge.Contract
import ECDSAAdd.Framework.WireRename

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
