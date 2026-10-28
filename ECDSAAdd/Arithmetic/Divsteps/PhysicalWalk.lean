import ECDSAAdd.Arithmetic.Divsteps.LayoutSemantics
import ECDSAAdd.Arithmetic.Divsteps.WalkProgram

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- Fixed chronological sequence of the actual allocated divstep programs. -/
def StepLayout.walk (L : StepLayout) (N : Nat) : Program :=
  forwardWalk (fun i => (L.at i).program) 0 N

/-- Opposite chronology, using retained controls and the original step views. -/
def StepLayout.unwalk (L : StepLayout) (N : Nat) : Program :=
  inverseWalk (fun i => (L.at i).undo) 0 N

private theorem step_spec (L : StepLayout) (h : L.Valid) (p x : Int) (N : Nat)
    (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i)) :
    ∀ i, i<N → Triple ((L.at i).Ready (zWalk p x i)) (L.at i).program
      ((L.at (i+1)).Ready (zWalk p x (i+1))) := by
  intro i hi
  exact (L.at i).program_spec (L.at_valid h i) (zWalk p x i) (hfit i hi)
    (L.at_can_advance i (by omega))

/-- All five outputs are the frozen integer walk, with phase restored, reusable
workspace zero and the next reserved controls fresh. No termination is assumed. -/
theorem StepLayout.walk_spec (L : StepLayout) (h : L.Valid) (p x : Int) (N : Nat)
    (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i)) :
    Triple (L.Ready (zSeed p x)) (L.walk N) ((L.at N).Ready (zWalk p x N)) := by
  simpa only [walk,StepLayout.at,zWalk,Nat.zero_add] using forwardWalk_spec (fun i => (L.at i).program)
    (fun i => (L.at i).Ready (zWalk p x i)) N
    (step_spec L h p x N hhistory hfit) 0 N (by omega)

/-- Full state restoration, including every retained control, for independent
forward and inverse measurement records. -/
theorem StepLayout.unwalk_after (L : StepLayout) (h : L.Valid) (p x : Int) (N : Nat)
    (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i))
    (s : State) (mf mi : List Bool) (hs : L.Ready (zSeed p x) s.basis) :
    run (L.unwalk N) mi (run (L.walk N) mf s)=s := by
  apply inverseWalk_after (fun i => (L.at i).program) (fun i => (L.at i).undo)
    (fun i => (L.at i).Ready (zWalk p x i)) N
    (step_spec L h p x N hhistory hfit) ?_ 0 N (by omega) s mf mi hs
  intro i hi t ma mb ht
  exact (L.at i).undo_after (L.at_valid h i) (zWalk p x i) (hfit i hi)
    t ma mb ht.1 ht.2.1 ht.2.2.1

theorem StepLayout.walk_roundTrip (L : StepLayout) (h : L.Valid) (p x : Int) (N : Nat)
    (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i))
    (s : State) (m : List Bool) (hs : L.Ready (zSeed p x) s.basis) :
    run (L.walk N ++ L.unwalk N) m s=s := by
  rw [run_append,run_take]
  exact L.unwalk_after h p x N hhistory hfit s m _ hs

/-- Same-program exact totals; these include frozen slots and activity checks. -/
theorem StepLayout.walk_counts (L : StepLayout) (h : L.Valid) (n v k N : Nat)
    (hw : L.Sized n v k) :
    toffoliCount (L.walk N)=N*(5*n+5*v+k-4) ∧
    measurementCount (L.walk N)=N*(4*n+3*v+k-5) := by
  exact forwardWalk_counts _ _ _ N (fun i _ =>
    (L.at i).program_counts (L.at_valid h i) n v k (L.at_sized n v k hw i)) 0 N (by omega)

theorem StepLayout.unwalk_counts (L : StepLayout) (h : L.Valid) (n v k N : Nat)
    (hw : L.Sized n v k) :
    toffoliCount (L.unwalk N)=N*(5*n+5*v+k-4) ∧
    measurementCount (L.unwalk N)=N*(4*n+3*v+k-5) := by
  exact inverseWalk_counts _ _ _ N (fun i _ =>
    (L.at i).undo_counts (L.at_valid h i) n v k (L.at_sized n v k hw i)) 0 N (by omega)

theorem StepLayout.walk_support (L : StepLayout) (h : L.Valid) (N : Nat) :
    wires (L.walk N)⊆L.used.toFinset := by
  apply forwardWalk_wires_subset _ _ N ?_ 0 N (by omega)
  intro i _
  rw [←L.at_support i]
  exact (L.at i).program_support (L.at_valid h i)

theorem StepLayout.unwalk_support (L : StepLayout) (h : L.Valid) (N : Nat) :
    wires (L.unwalk N)⊆L.used.toFinset := by
  apply inverseWalk_wires_subset _ _ N ?_ 0 N (by omega)
  intro i _
  rw [←L.at_support i]
  exact (L.at i).undo_support (L.at_valid h i)

theorem StepLayout.walk_roundTrip_qubits (L : StepLayout) (h : L.Valid) (N : Nat) :
    qubitCount (L.walk N ++ L.unwalk N)≤L.used.length := by
  have hh : wires (L.walk N ++ L.unwalk N)⊆L.used.toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨L.walk_support h N,L.unwalk_support h N⟩
  simpa [qubitCount,List.toFinset_card_of_nodup h.unique] using Finset.card_le_card hh

/-- Canonical-input bounds discharge every step's numeric obligations using
one uniform capacity check. This proves safety through N slots, not termination. -/
theorem StepLayout.walk_fits (L : StepLayout) (n v k N : Nat) (hw : L.Sized n v k)
    (p x : Int) (hp : 0≤p) (hodd : p%2=1) (hx : 0≤x) (hxp : x≤p)
    (hg : 2*p<((2^(n-1):Nat):Int))
    (hv : (2:Int)^N<((2^(v-1):Nat):Int))
    (hz : (N:Int)+1<((2^(k-1):Nat):Int)) :
    ∀ i, i<N → (L.at i).Fits (zWalk p x i) := by
  intro i hi
  have hw' := L.at_sized n v k hw i
  have hn : (L.at i).g.middle.length+1=n-1 := by
    have hh := hw'.1
    simp only [StepRow.wires,List.length_cons,List.length_append,List.length_nil] at hh
    omega
  have hc : 2*(2:Int)^i≤2^N := by
    have hh : (2:Int)^(i+1)≤2^N := pow_le_pow_right₀ (by norm_num) hi
    simpa [pow_succ,mul_comm] using hh
  refine ⟨p,(i:Int),(2:Int)^i,zWalk_bounds p x hp hx hxp i,
    (invariant_zWalk hodd x i).fodd,?_,?_,?_⟩
  · simpa only [hn] using hg
  · rw [hw'.2.1]
    linarith
  · rw [hw'.2.2]
    have hh : (i:Int)≤N := by exact_mod_cast Nat.le_of_lt hi
    linarith

theorem StepLayout.walk_spec_of_capacity (L : StepLayout) (h : L.Valid)
    (n v k N : Nat) (hw : L.Sized n v k) (hhistory : N≤L.future.length)
    (p x : Int) (hp : 0≤p) (hodd : p%2=1) (hx : 0≤x) (hxp : x≤p)
    (hg : 2*p<((2^(n-1):Nat):Int))
    (hv : (2:Int)^N<((2^(v-1):Nat):Int))
    (hz : (N:Int)+1<((2^(k-1):Nat):Int)) :
    Triple (L.Ready (zSeed p x)) (L.walk N) ((L.at N).Ready (zWalk p x N)) :=
  L.walk_spec h p x N hhistory (L.walk_fits n v k N hw p x hp hodd hx hxp hg hv hz)

theorem StepLayout.unwalk_after_of_capacity (L : StepLayout) (h : L.Valid)
    (n v k N : Nat) (hw : L.Sized n v k) (hhistory : N≤L.future.length)
    (p x : Int) (hp : 0≤p) (hodd : p%2=1) (hx : 0≤x) (hxp : x≤p)
    (hg : 2*p<((2^(n-1):Nat):Int))
    (hv : (2:Int)^N<((2^(v-1):Nat):Int))
    (hz : (N:Int)+1<((2^(k-1):Nat):Int))
    (s : State) (mf mi : List Bool) (hs : L.Ready (zSeed p x) s.basis) :
    run (L.unwalk N) mi (run (L.walk N) mf s)=s :=
  L.unwalk_after h p x N hhistory (L.walk_fits n v k N hw p x hp hodd hx hxp hg hv hz)
    s mf mi hs

/-- Conservative 258/592/11 data widths safely execute 590 slots for every
canonical input below a 256-bit odd modulus. This says nothing about g=0 at exit. -/
theorem StepLayout.walk590_fits (L : StepLayout) (hw : L.Sized 258 592 11)
    (p x : Int) (hp : 0≤p) (hodd : p%2=1) (hsmall : p<2^256)
    (hx : 0≤x) (hxp : x≤p) :
    ∀ i, i<590 → (L.at i).Fits (zWalk p x i) := by
  apply L.walk_fits 258 592 11 590 hw p x hp hodd hx hxp
  · norm_num at hsmall ⊢
    omega
  · norm_num only [Nat.reduceSub,Nat.cast_pow,Nat.cast_ofNat]
    exact pow_lt_pow_right₀ (by norm_num : (1:Int)<2) (by omega : 590<591)
  · norm_num

theorem StepLayout.walk590_spec (L : StepLayout) (h : L.Valid) (hw : L.Sized 258 592 11)
    (hhistory : 590≤L.future.length)
    (p x : Int) (hp : 0≤p) (hodd : p%2=1) (hsmall : p<2^256)
    (hx : 0≤x) (hxp : x≤p) :
    Triple (L.Ready (zSeed p x)) (L.walk 590) ((L.at 590).Ready (zWalk p x 590)) :=
  L.walk_spec h p x 590 hhistory (L.walk590_fits hw p x hp hodd hsmall hx hxp)

theorem StepLayout.unwalk590_after (L : StepLayout) (h : L.Valid) (hw : L.Sized 258 592 11)
    (hhistory : 590≤L.future.length)
    (p x : Int) (hp : 0≤p) (hodd : p%2=1) (hsmall : p<2^256)
    (hx : 0≤x) (hxp : x≤p)
    (s : State) (mf mi : List Bool) (hs : L.Ready (zSeed p x) s.basis) :
    run (L.unwalk 590) mi (run (L.walk 590) mf s)=s :=
  L.unwalk_after h p x 590 hhistory (L.walk590_fits hw p x hp hodd hsmall hx hxp)
    s mf mi hs

theorem StepLayout.walk590_counts (L : StepLayout) (h : L.Valid) (hw : L.Sized 258 592 11) :
    toffoliCount (L.walk 590)=2511630 ∧ measurementCount (L.walk 590)=1660260 ∧
    toffoliCount (L.unwalk 590)=2511630 ∧ measurementCount (L.unwalk 590)=1660260 := by
  have hf := L.walk_counts h 258 592 11 590 hw
  have hr := L.unwalk_counts h 258 592 11 590 hw
  norm_num at hf hr
  exact ⟨hf.1,hf.2,hr⟩

end ECDSAAdd.Arithmetic.Divsteps
