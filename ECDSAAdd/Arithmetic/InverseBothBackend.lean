import ECDSAAdd.Arithmetic.InversePointBackend
import ECDSAAdd.Arithmetic.InverseProductRecorded
namespace ECDSAAdd.Arithmetic.PointInverseEndpoint
open Secp256k1 ControlledPointLayout

def product (ep : PointInverseEndpoint) (L : ControlledPointLayout) : RecordedProgram :=
  InverseProductRecorded.program (ep.program L) L.core.generic L.quotientMont L.quotientDen
attribute [local irreducible] InverseProductRecorded.program

theorem product_correct (ep : PointInverseEndpoint) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (X Y : Nat) (B : Bool)
    (hx : X < p) (hx0 : B = true → X ≠ 0) (hy : Y < p)
    (hsafe : ep.safe (X : Fp) B) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic = B) (hX : regValue L.point.x s.basis = X)
    (hY : regValue L.point.y s.basis = Y) (hz : regValue L.dialogPool s.basis = 0) :
    (runWithTape (ep.product L) m 0 s).phase = s.phase ∧
    regValue L.point.y (runWithTape (ep.product L) m 0 s).basis =
      (if B then ((Y : Fp)*(X : Fp)).val else Y) ∧
    ∀ q, q ∉ L.point.y → (runWithTape (ep.product L) m 0 s).basis q = s.basis q := by
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
  have h := InverseProductRecorded.correct (ep.program L) L.core.generic L.quotientMont
    L.quotientDen (ep.work L) ep.safe (ep.correct L hw hn) (L.quotient_nodup hw hn)
    (L.quotient_widths hw).1 (L.quotient_widths hw).2 (ep.separate L hw hn)
    B (X : Fp) (Y : Fp) hsafe nonzero s m hb (hd.trans (hX.trans xv.symm)) hi
    (hY.trans yv.symm) ht hwork hc
  change _ ∧ regValue L.point.y _ = _ ∧ (∀ q, q ∉ L.point.y → _) at h
  simpa only [product,apply_ite,ZMod.val_natCast,Nat.mod_eq_of_lt hy] using h

theorem product_support (ep : PointInverseEndpoint) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) :
    recordedWires (ep.product L) ⊆ L.dialogUsedWires.toFinset := by
  rw [product,InverseProductRecorded.support]
  apply Finset.union_subset (ep.support L hw hn)
  have hw' : (InverseQuotientCore.denView L.quotientMont L.quotientDen).Widths :=
    ⟨(L.quotient_widths hw).2,(L.quotient_widths hw).1.y,
      (L.quotient_widths hw).1.out,(L.quotient_widths hw).1.first,
      (L.quotient_widths hw).1.z,(L.quotient_widths hw).1.hZ⟩
  apply (InverseQuotientCore.support _ _ _ hw' (L.quotient_widths hw).1.x).trans
  intro q hq
  apply List.mem_toFinset.mpr
  apply L.quotient_subset hw
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,MontLayout.wires,
    InverseQuotientCore.denView] at hq ⊢
  tauto

/-- Both arithmetic arms use the supplied XOR inverse endpoint. -/
def bothBackend (ep : PointInverseEndpoint) : ConditionalPointArithmeticBackend where
  program L multiply := if multiply then ep.product L else ep.quotient L
  safe _ X _ B := ep.safe X B
  correct L hw hn multiply X Y B hx hx0 hy hs s m hb hX hY hz := by
    cases multiply with
    | false => exact ep.quotient_correct L hw hn X Y B hx hx0 hy hs s m hb hX hY hz
    | true => exact ep.product_correct L hw hn X Y B hx hx0 hy hs s m hb hX hY hz
  support L hw hn multiply := by
    cases multiply with
    | false => exact ep.quotient_support L hw hn
    | true => exact ep.product_support L hw hn
  wellFormed L hw hn multiply := by
    cases multiply with
    | false => exact InverseQuotientRecorded.wellFormed _ _ _ _ (ep.wellFormed L hw hn)
    | true => exact InverseProductRecorded.wellFormed _ _ _ _ (ep.wellFormed L hw hn)

end ECDSAAdd.Arithmetic.PointInverseEndpoint
