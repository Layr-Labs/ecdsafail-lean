import ECDSAAdd.Arithmetic.InverseQuotientPointLayout
import ECDSAAdd.Arithmetic.InverseQuotientSupport
import ECDSAAdd.Arithmetic.ConditionalPointArithmeticBackend

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout

/-- A compact inverse may be placed in this reference point caller without
assuming that it already implements division. Its workspace is explicit. -/
structure PointInverseEndpoint where
  program : ControlledPointLayout → RecordedProgram
  work : ControlledPointLayout → List Wire
  safe : Fp → Bool → Prop
  correct : ∀ L, L.Widths → L.wires.Nodup →
    InverseQuotientRecorded.InverseContract (program L) L.core.generic L.quotientDen
      L.quotientMont.x (work L) safe
  clean : ∀ L, L.Widths → work L ⊆ L.dialogPool
  separate : ∀ L, L.Widths → L.wires.Nodup → ∀ q, q ∈ work L →
    q ∉ L.quotientMont.x ∧ q ∉ L.quotientMont.y
  support : ∀ L, L.Widths → L.wires.Nodup → recordedWires (program L) ⊆ L.dialogUsedWires.toFinset
  wellFormed : ∀ L, L.Widths → L.wires.Nodup → RecordedWellFormedAt 0 (program L)

namespace PointInverseEndpoint

def quotient (ep : PointInverseEndpoint) (L : ControlledPointLayout) : RecordedProgram :=
  InverseQuotientRecorded.program (ep.program L) L.core.generic L.quotientMont L.quotientDen

attribute [local irreducible] InverseQuotientRecorded.program PointArithmeticBackend.skywalk

theorem quotient_correct (ep : PointInverseEndpoint) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (X Y : Nat) (B : Bool)
    (hx : X < p) (hx0 : B = true → X ≠ 0) (hy : Y < p)
    (hsafe : ep.safe (X : Fp) B) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic = B) (hX : regValue L.point.x s.basis = X)
    (hY : regValue L.point.y s.basis = Y) (hz : regValue L.dialogPool s.basis = 0) :
    (runWithTape (ep.quotient L) m 0 s).phase = s.phase ∧
    regValue L.point.y (runWithTape (ep.quotient L) m 0 s).basis =
      (if B then ((Y : Fp)/(X : Fp)).val else Y) ∧
    ∀ q, q ∉ L.point.y → (runWithTape (ep.quotient L) m 0 s).basis q = s.basis q := by
  have xv : (X : Fp).val = X := by simp [ZMod.val_natCast,Nat.mod_eq_of_lt hx]
  have yv : (Y : Fp).val = Y := by simp [ZMod.val_natCast,Nat.mod_eq_of_lt hy]
  have nonzero : B = true → (X : Fp) ≠ 0 := by
    intro h he
    have hv := congrArg ZMod.val he
    rw [xv] at hv
    exact hx0 h (by simpa using hv)
  obtain ⟨hi,ht,hwork,hd⟩ := L.quotient_clean hw s.basis hz
  have hc : regValue (ep.work L) s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (ep.clean L hw hq))
  have h := InverseQuotientRecorded.correct (ep.program L) L.core.generic L.quotientMont
    L.quotientDen (ep.work L) ep.safe (ep.correct L hw hn) (L.quotient_nodup hw hn)
    (L.quotient_widths hw).1 (L.quotient_widths hw).2 (ep.separate L hw hn)
    B (X : Fp) (Y : Fp) hsafe nonzero s m hb (hd.trans (hX.trans xv.symm)) hi
    (hY.trans yv.symm) ht hwork hc
  change _ ∧ regValue L.point.y _ = _ ∧ (∀ q, q ∉ L.point.y → _) at h
  simpa only [quotient,apply_ite,ZMod.val_natCast,Nat.mod_eq_of_lt hy] using h

theorem quotient_support (ep : PointInverseEndpoint) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) :
    recordedWires (ep.quotient L) ⊆ L.dialogUsedWires.toFinset := by
  rw [quotient,InverseQuotientRecorded.support]
  apply Finset.union_subset (ep.support L hw hn)
  apply (InverseQuotientCore.support _ _ _ (L.quotient_widths hw).1 (L.quotient_widths hw).2).trans
  intro q hq
  exact List.mem_toFinset.mpr (L.quotient_subset hw (List.mem_toFinset.mp hq))

/-- The division arm uses the new inverse endpoint; the multiplication arm is
the existing exact reference. This constructor certifies no compact-space bound. -/
def backend (ep : PointInverseEndpoint) : ConditionalPointArithmeticBackend where
  program L multiply := if multiply then embedRecorded (PointArithmeticBackend.skywalk.program L true)
    else ep.quotient L
  safe multiply X _ B := if multiply then True else ep.safe X B
  correct L hw hn multiply X Y B hx hx0 hy hs s m hb hX hY hz := by
    cases multiply with
    | false => exact ep.quotient_correct L hw hn X Y B hx hx0 hy hs s m hb hX hY hz
    | true =>
      simpa only [Bool.true_eq,ite_true,runWithTape_embedRecorded,List.drop_zero] using
        PointArithmeticBackend.skywalk.correct L hw hn true X Y B hx hx0 hy s m hb hX hY hz
  support L hw hn multiply := by
    cases multiply with
    | false => exact ep.quotient_support L hw hn
    | true => simpa only [Bool.true_eq,ite_true,embedRecorded_wires] using
        PointArithmeticBackend.skywalk.support L hw hn true
  wellFormed L hw hn multiply := by
    cases multiply with
    | false => exact InverseQuotientRecorded.wellFormed _ _ _ _ (ep.wellFormed L hw hn)
    | true => exact embedRecorded_wellFormed _ 0

end PointInverseEndpoint
end ECDSAAdd.Arithmetic
