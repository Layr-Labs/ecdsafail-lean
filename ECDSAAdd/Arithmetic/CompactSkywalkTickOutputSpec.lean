import ECDSAAdd.Arithmetic.CompactSkywalkTickOutputCleanup

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- The post-boundary integer words are physically retained prefixes.
History is still the actual emitted orientation/sign history, not recomputed data. -/
def CompactSkywalkTickOutput (w : Nat → Wire) (i : Nat) (A B : Int) (G : Bool)
    (s : BasisState) : Prop :=
  let L := compactSkywalkTickLayout w i
  let t := SkywalkRails.step ⟨A,B,G⟩
  signedRegValue (compactSkywalkTickARelease w i).retained s = t.h ∧
  signedRegValue (compactSkywalkTickBRelease w i).retained s = t.k ∧
  s L.a0 = t.g ∧ s L.history = t.s ∧ s L.previous = G ∧ regValue L.carry s = 0 ∧
  (compactSkywalkTickARelease w i).Clean s ∧ (compactSkywalkTickBRelease w i).Clean s

/-- The cleanup suffix has zero measurements, so its stream can be chosen
independently of the native tick's consumed prefix. -/
theorem compactSkywalkTickOutput_run (w : Nat → Wire) (i : Nat) (s : State) (m : List Bool) :
    run (compactSkywalkTick w i) m s =
      run (compactSkywalkTickCleanup w i) m
        (run (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)) m s) := by
  rw [compactSkywalkTick,run_append,run_take]
  have hz := (compactSkywalkTick_cleanup_counts w i).2
  have h1 := run_take (compactSkywalkTickCleanup w i)
    (m.drop (measurementCount
      (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i))))
    (run (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)) m s)
  have h2 := run_take (compactSkywalkTickCleanup w i) m
    (run (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)) m s)
  rw [hz,List.take_zero] at h1 h2
  exact h1.symm.trans h2

/-- Full actual compact-tick semantics. Copies for both cleanup banks are
proved from the native result; no sign-copy premise is added to the input. -/
theorem compactSkywalkTickOutput_spec (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (A B : Int) (G : Bool) (hp : (A+B)%2 = 1)
    (ha0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).1/2)
    (ha1 : (SkywalkRails.route A B).1/2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int))
    (hb0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).2)
    (hb1 : (SkywalkRails.route A B).2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int)) :
    Triple (SkywalkIntegerInput (compactSkywalkTickLayout w i) A B G)
      (compactSkywalkTick w i) (CompactSkywalkTickOutput w i A B G) := by
  intro s m hin
  let L := compactSkywalkTickLayout w i
  let t := run (narrowSkywalkTick L (compactSkywalkTickPostWidth i)) m s
  let u := run (compactSkywalkTickCleanup w i) m t
  have native := compactSkywalkTick_native_spec w i hi hn A B G hp ha0 ha1 hb0 hb1 s m hin
  have copies := compactSkywalkTick_native_copies w i hi hn A B G hp ha0 ha1 hb0 hb1 s m hin
  have cleanup := compactSkywalkTickOutput_cleanup_correct w i hi hn t m copies.1 copies.2
  have keep : ∀q,q ∈ [L.a0,L.history,L.previous]++L.carry → u.basis q = t.basis q := by
    intro q hq
    have away := compactSkywalkTickOutput_metadataAway w i hi hn q hq
    exact cleanup.2.2.2.2.2 q away.1 away.2
  have carry : regValue L.carry u.basis = 0 := by
    apply Eq.trans (regValue_congr L.carry u.basis t.basis ?_) native.2.2.2.2.2.2
    intro q hq
    exact keep q (by simp [hq])
  have actual : run (compactSkywalkTick w i) m s = u := compactSkywalkTickOutput_run w i s m
  rw [actual]
  refine ⟨cleanup.1.trans native.1,cleanup.2.2.2.1.trans native.2.1,
    cleanup.2.2.2.2.1.trans native.2.2.1,
    (keep L.a0 (by simp)).trans native.2.2.2.1,
    (keep L.history (by simp)).trans native.2.2.2.2.1,
    (keep L.previous (by simp)).trans native.2.2.2.2.2.1,
    carry,cleanup.2.1,cleanup.2.2.1⟩

/-- Complete outsider frame for the actual compact program, independent of
input values and measurement outcomes. -/
theorem compactSkywalkTickOutput_frame (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool) (q : Wire)
    (hq : q ∉ (compactSkywalkTickLayout w i).wires) :
    (run (compactSkywalkTick w i) m s).basis q = s.basis q :=
  run_preserves_outside _ m s q (fun h =>
    hq (List.mem_toFinset.mp (compactSkywalkTick_support w i hi hn h)))

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTickOutput_run
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTickOutput_spec
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTickOutput_frame
