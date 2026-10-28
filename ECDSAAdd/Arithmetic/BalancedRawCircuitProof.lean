import ECDSAAdd.Arithmetic.BalancedFieldCircuitProgram
import ECDSAAdd.Arithmetic.SignedWordBits

set_option maxRecDepth 4096
set_option maxHeartbeats 300000
namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField

/-- The extended raw words and their control/carry sites are physically distinct. -/
theorem rawLayoutND (L : Layout) (hn : L.wires.Nodup) :
    (L.sign::(rawSource L++rawTarget L++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,rawSource,rawTarget,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
    List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

/-- The actual 257-bit signed addition, including every measurement's
phase correction, implements the unbounded signed sum on every centered pair. -/
theorem rawAdd_signed (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y) :
    Triple (fun s => s L.sign=B ∧ signedRegValue (rawSource L) s=Y ∧
      signedRegValue (rawTarget L) s=X ∧ regValue L.carry s=0)
      (rawAdd L)
      (fun s => s L.sign=B ∧ signedRegValue (rawSource L) s=Y ∧
        signedRegValue (rawTarget L) s=rawSum B X Y ∧ regValue L.carry s=0) := by
  have w := widths L hw
  have hsum := rawSum_bounds B X Y hx hy
  have hp := constants
  have bound : -((2^256 : Nat) : Int)≤rawSum B X Y ∧ rawSum B X Y<((2^256 : Nat) : Int) := by
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at ⊢
    have pow : (2^256 : Int)=2*(2^255 : Int) := by norm_num
    omega
  have arithmetic : signedIntegerValue B Y X=rawSum B X Y := by
    cases B <;> simp [signedIntegerValue,rawSum,signedY,sub_eq_add_neg]
  have result := signedAdd_int_spec L.sign (rawSource L) (rawTarget L) L.carry
    (rawLayoutND L hn) (by omega) (by omega) B Y X
    (by rw [w.2.1,arithmetic]; norm_num only [Nat.reduceSub]; exact bound.1)
    (by rw [w.2.1,arithmetic]; norm_num only [Nat.reduceSub]; exact bound.2)
  simpa only [rawAdd,signedAdd,arithmetic] using result

/-- Every physical bit outside the extended target word is restored,
including source, control, raw parity and the complete carry bank. -/
theorem rawAdd_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hc : regValue L.carry s.basis=0)
    (a : Wire) (ha : a∉rawTarget L) :
    (run (rawAdd L) m s).basis a=s.basis a := by
  have w := widths L hw
  have hf := (signedWord_frame L.sign (rawSource L) (rawTarget L) L.carry
    (rawLayoutND L hn) (by omega) (by omega) (s.basis L.sign)
    (regValue (rawSource L) s.basis) (regValue (rawTarget L) s.basis)
    s m rfl rfl rfl hc a ha).1
  simpa only [rawAdd,signedAdd] using hf

end ECDSAAdd.Arithmetic.BalancedCircuit

#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.rawAdd_signed

#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.rawAdd_frame
