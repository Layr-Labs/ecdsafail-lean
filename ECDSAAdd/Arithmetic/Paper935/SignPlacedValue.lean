import ECDSAAdd.Arithmetic.Paper935.SignCoreSignedValue
import ECDSAAdd.Arithmetic.Paper935.SignPlacedExecution

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] signCore signPayload FusedCall.beforeSign

private theorem value_map (f : Wire → Wire) (xs : List Wire) (s : BasisState) :
    regValue (xs.map f) s=regValue xs (fun q => s (f q)) := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    change (if s (f q) then 1 else 0)+2*regValue (qs.map f) s =
      (if s (f q) then 1 else 0)+2*regValue qs (fun q => s (f q))
    rw [ih]

private theorem payload_bounds (q : Wire) (hq : q∈signPayload) : 0<q ∧ q<281 := by
  simp only [signPayload,List.mem_range'] at hq
  dsimp only [Wire] at *
  omega

private theorem port_ne (f : Wire → Wire) (inj : Set.InjOn f (Finset.range 281))
    (q : Wire) (lo : 0<q) (hi : q<281) : f q≠f 0 := by
  intro eq
  have h := inj (Finset.mem_range.mpr hi) (Finset.mem_range.mpr (by decide)) eq
  dsimp only [Wire] at *
  omega

private theorem word_cx (f : Wire → Wire) (inj : Set.InjOn f (Finset.range 281))
    (sv : Wire) (s : State) (m : List Bool) :
    regValue (signPayload.map f) (run [.CX sv (f 0)] m s).basis=
      regValue (signPayload.map f) s.basis := by
  apply regValue_congr
  intro q hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
  have b := payload_bounds a ha
  simp [run,writeBit,port_ne f inj a b.1 b.2]

/-- Physical sign core, with the value encoding and control binding explicit. -/
theorem placedSignCore_of_good (f : Wire → Wire)
    (inj : Set.InjOn f (Finset.range 281)) (call : FusedCall) (s : State) (m : List Bool)
    (clean : ∀i<24,s.basis (f (257+i))=false)
    (value : regValue (signPayload.map f) s.basis=call.beforeSign)
    (control : s.basis (f 0)=call.negate) (good : call.SignGood) :
    regValue (signPayload.map f) (run (placedSignCore f false) m s).basis=
      if call.negate then fold32Prime-call.beforeSign else call.beforeSign := by
  have sem := run_rename_pool f (Finset.range 281) inj (signCore false)
    (signCore_support false) m (pullState f s) s rfl (fun _ _ => rfl)
  have encoding : regValue signPayload (pullState f s).basis=call.beforeSign := by
    rw [value_map] at value
    exact value
  have flag : (pullState f s).basis 0=call.negate := control
  have noborrow : (pullState f s).basis 0=true →
      2^32+976≤(2^256-1-regValue signPayload (pullState f s).basis)%2^58 := by
    rw [flag,encoding]
    exact fun h => (good.2 h).2
  have result := signCore_value (pullState f s) m clean noborrow
  rw [flag,encoding] at result
  rw [value_map]
  have word : regValue signPayload (fun q => (run (placedSignCore f false) m s).basis (f q))=
      regValue signPayload (run (signCore false) m (pullState f s)).basis := by
    apply regValue_congr
    intro q hq
    exact sem.2 q (Finset.mem_range.mpr (payload_bounds q hq).2)
  exact word.trans result

/-- Actual outer CX pair forms sf XOR sv only for the sign core. SignGood
and this negate binding are distinct hypotheses, not consequences of row_mul. -/
theorem placedSignFix_of_good (f : Wire → Wire) (sv : Wire)
    (inj : Set.InjOn f (Finset.range 281)) (call : FusedCall) (s : State) (m : List Bool)
    (clean : ∀i<24,s.basis (f (257+i))=false)
    (value : regValue (signPayload.map f) s.basis=call.beforeSign)
    (negate : call.negate=(s.basis (f 0) ^^ s.basis sv)) (good : call.SignGood) :
    regValue (signPayload.map f) (run (placedSignFix f sv false) m s).basis=
      if call.negate then fold32Prime-call.beforeSign else call.beforeSign := by
  let t := run [.CX sv (f 0)] m s
  have ready : ∀i<24,t.basis (f (257+i))=false := by
    intro i hi
    have neq := port_ne f inj (257+i) (by dsimp only [Wire] at *; omega)
      (by dsimp only [Wire] at *; omega)
    simpa [t,run,writeBit,neq] using clean i hi
  have encoding : regValue (signPayload.map f) t.basis=call.beforeSign :=
    (word_cx f inj sv s m).trans value
  have control : t.basis (f 0)=call.negate := by simpa [t,run,writeBit] using negate.symm
  have result := placedSignCore_of_good f inj call t m ready encoding control good
  simp only [placedSignFix,run_append,run_take,measurementCount,List.drop_zero]
  rw [word_cx f inj]
  exact result

end ECDSAAdd.Arithmetic.Paper935
