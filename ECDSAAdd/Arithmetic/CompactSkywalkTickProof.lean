import ECDSAAdd.Arithmetic.CompactSkywalkTickProgram

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem record_fit (H A B : Int) (ha0 : -H ≤ A) (ha1 : A < H)
    (hb0 : -H ≤ B) (hb1 : B < H) :
    -H ≤ signedRecordValue A B ∧ signedRecordValue A B < H := by
  by_cases ha : A < 0 <;> by_cases hb : B < 0 <;>
    simp [signedRecordValue,signedRecordControl,signedIntegerValue,SkywalkRails.neg,ha,hb] <;> omega

/-- Cancellation keeps both post-tick rails inside the strict record interval. -/
theorem compactSkywalkTick_step_fit (A B : Int) (G : Bool) (H : Int)
    (hp : (A+B)%2 = 1)
    (ha0 : -H ≤ (SkywalkRails.route A B).1/2) (ha1 : (SkywalkRails.route A B).1/2 < H)
    (hb0 : -H ≤ (SkywalkRails.route A B).2) (hb1 : (SkywalkRails.route A B).2 < H) :
    -H ≤ (SkywalkRails.step ⟨A,B,G⟩).h ∧ (SkywalkRails.step ⟨A,B,G⟩).h < H ∧
    -H ≤ (SkywalkRails.step ⟨A,B,G⟩).k ∧ (SkywalkRails.step ⟨A,B,G⟩).k < H := by
  have he := SkywalkRails.route_even A B hp
  have hs : SkywalkRails.sameSign ((SkywalkRails.route A B).1/2) (SkywalkRails.route A B).2 =
      SkywalkRails.sameSign (SkywalkRails.route A B).1 (SkywalkRails.route A B).2 := by
    unfold SkywalkRails.sameSign
    rw [SkywalkRails.neg_half _ he]
  have hk := record_fit H ((SkywalkRails.route A B).1/2) (SkywalkRails.route A B).2 ha0 ha1 hb0 hb1
  rw [signedRecordValue_rails,hs] at hk
  exact ⟨ha0,ha1,hk.1,hk.2⟩

/-- The native tick already uses only the actual local prefixes. Every input
fit obligation is the same universally proved post-route envelope. -/
theorem compactSkywalkTick_native_spec (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (A B : Int) (G : Bool) (hp : (A+B)%2 = 1)
    (ha0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).1/2)
    (ha1 : (SkywalkRails.route A B).1/2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int))
    (hb0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).2)
    (hb1 : (SkywalkRails.route A B).2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int)) :
    Triple (SkywalkIntegerInput (compactSkywalkTickLayout w i) A B G)
      (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i))
      (SkywalkIntegerOutput (compactSkywalkTickLayout w i) A B G) := by
  have h := compactSkywalkTick_width_bounds i hi
  exact narrowSkywalkTick_spec _ (compactSkywalkTick_valid w i hi hn) _ (by omega)
    (by rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)
    A B G hp ha0 ha1 hb0 hb1

/-- The actual locally emitted native result supplies both sign-release
premises; no post-tick sign-copy oracle is assumed. -/
theorem compactSkywalkTick_native_copies (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (A B : Int) (G : Bool) (hp : (A+B)%2 = 1)
    (ha0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).1/2)
    (ha1 : (SkywalkRails.route A B).1/2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int))
    (hb0 : -((2^(compactSkywalkTickPostWidth i-1):Nat):Int) ≤ (SkywalkRails.route A B).2)
    (hb1 : (SkywalkRails.route A B).2 < ((2^(compactSkywalkTickPostWidth i-1):Nat):Int))
    (s : State) (m : List Bool)
    (hin : SkywalkIntegerInput (compactSkywalkTickLayout w i) A B G s.basis) :
    let t := run (narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)) m s
    (compactSkywalkTickARelease w i).Copies t.basis ∧
    (compactSkywalkTickBRelease w i).Copies t.basis := by
  dsimp only
  have h := compactSkywalkTick_width_bounds i hi
  have fit := compactSkywalkTick_step_fit A B G _ hp ha0 ha1 hb0 hb1
  have out := (compactSkywalkTick_native_spec w i hi hn A B G hp ha0 ha1 hb0 hb1 s m hin).2
  exact ⟨compactSkywalkSignWord_copies _ _ (by omega)
    (by rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1) _ _
      out.1 fit.1 fit.2.1,
    compactSkywalkSignWord_copies _ _ (by omega)
    (by rw [compactSkywalkTick_b w i hi,wireBlock_length]; exact h.2.2.1) _ _
      out.2.1 fit.2.2.1 fit.2.2.2⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTick_native_spec
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTick_native_copies
