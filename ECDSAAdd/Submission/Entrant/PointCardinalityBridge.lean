import ECDSAAdd.Submission.Entrant.FrontierMain
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finite.Card

/-!
Conditional cardinality bridge.  This leaf does not select or change a circuit.
The generator-order theorem is an explicit argument until its separate source
port is compiled and checked.  No point enumeration is used.
-/
namespace ECDSAAdd.Entrant.PointCardinalityBridge

open ECDSAAdd Arithmetic Secp256k1

noncomputable section

/-- Abscissas of nonsingular finite points. -/
def HasX (x : Fp) : Prop := ∃ y : Fp, curve.toAffine.Nonsingular x y

abbrev AffineX := {x : Fp // HasX x}
abbrev NonpointX := {x : Fp // ¬HasX x}

/-- The usual compressed point, with infinity represented by `none`. -/
def compressed : Point → Option (AffineX × Bool)
  | .zero => none
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y h =>
      some (⟨x, ⟨y, h⟩⟩, yBit (.some h : Point))

 theorem compressed_injective : Function.Injective compressed := by
  intro P Q eqc
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some h => cases eqc
  | @some x y hx =>
      cases Q with
      | zero => cases eqc
      | @some x' y' hy =>
          have hp : (⟨x, ⟨y, hx⟩⟩, yBit (.some hx : Point)) =
              ((⟨x', ⟨y', hy⟩⟩ : AffineX), yBit (.some hy : Point)) :=
            Option.some.inj eqc
          have hxx : x = x' := congrArg Subtype.val (congrArg Prod.fst hp)
          have hyy : yBit (.some hx : Point) = yBit (.some hy : Point) :=
            congrArg Prod.snd hp
          exact InputSentinel.eq_of_x_ybit hx hy (congrArg ZMod.val hxx) hyy

 theorem compressed_surjective : Function.Surjective compressed := by
  classical
  intro z
  cases z with
  | none => exact ⟨0, rfl⟩
  | some z =>
      rcases z with ⟨⟨x, y, hy⟩, b⟩
      by_cases same : yBit (.some hy : Point) = b
      · refine ⟨.some hy, ?_⟩
        change some ((⟨x, ⟨y, hy⟩⟩ : AffineX), yBit (.some hy : Point)) = _
        rw [same]
      · have other : (!yBit (.some hy : Point)) = b := by
          cases hb : yBit (.some hy : Point) <;> cases b <;> simp_all
        have hneg : curve.toAffine.Nonsingular x (curve.toAffine.negY x y) :=
          (WeierstrassCurve.Affine.nonsingular_neg x y).mpr hy
        have parity : yBit (.some hneg : Point) = !yBit (.some hy : Point) := by
          simpa only [WeierstrassCurve.Affine.Point.neg_some] using yBit_neg hy
        refine ⟨.some hneg, ?_⟩
        change some ((⟨x, ⟨curve.toAffine.negY x y, hneg⟩⟩ : AffineX),
          yBit (.some hneg : Point)) = _
        rw [parity, other]

 def compressedEquiv : Point ≃ Option (AffineX × Bool) :=
  Equiv.ofBijective compressed ⟨compressed_injective, compressed_surjective⟩

/-- Negation supplies exactly two compressed parities over every finite x. -/
 theorem point_card_formula :
    Nat.card Point = 2 * Nat.card AffineX + 1 := by
  calc
    Nat.card Point = Nat.card (Option (AffineX × Bool)) :=
      Nat.card_congr compressedEquiv
    _ = 2 * Nat.card AffineX + 1 := by
      rw [Finite.card_option, Nat.card_prod]
      have hb : Nat.card Bool = 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_bool]
      rw [hb]
      omega

 theorem point_card_le : Nat.card Point ≤ 2 * p + 1 := by
  have hx : Nat.card AffineX ≤ Nat.card Fp :=
    Nat.card_le_card_of_injective (fun x : AffineX => x.val) Subtype.val_injective
  have hp : Nat.card Fp = p := by rw [Nat.card_eq_fintype_card]; exact ZMod.card p
  rw [hp] at hx
  rw [point_card_formula]
  omega

/-- The only group-order input needed by the cardinality bridge. -/
 theorem point_natCard_eq_order_of_generator_order
    (generator_order : addOrderOf G = order) : Nat.card Point = order := by
  have div : order ∣ Nat.card Point := by
    rw [← generator_order]
    exact addOrderOf_dvd_natCard G
  obtain ⟨k, hk⟩ := div
  have card_pos : 0 < Nat.card Point := by rw [point_card_formula]; omega
  have k_pos : 0 < k := by
    by_contra h
    have kz : k = 0 := by omega
    rw [kz, Nat.mul_zero] at hk
    omega
  have three : 2 * p + 1 < order * 3 := by norm_num [p, order]
  have mul_lt : order * k < order * 3 := by
    rw [← hk]
    exact lt_of_le_of_lt point_card_le three
  have k_lt : k < 3 := Nat.lt_of_mul_lt_mul_left mul_lt
  have cases_k : k = 1 ∨ k = 2 := by omega
  have card_eq : Nat.card Point = order := by
    rcases cases_k with one | two
    · simpa only [one, Nat.mul_one] using hk
    · have odd_card := point_card_formula
      rw [two] at hk
      omega
  exact card_eq

 theorem affineX_card_of_point_card (card_points : Nat.card Point = order) :
    Nat.card AffineX = (order - 1) / 2 := by
  have h := point_card_formula
  rw [card_points] at h
  omega

 theorem nonpoint_natCard_of_point_card (card_points : Nat.card Point = order) :
    Nat.card NonpointX = p - (order - 1) / 2 := by
  classical
  letI : Fintype AffineX := Fintype.ofFinite AffineX
  letI : Fintype NonpointX := Fintype.ofFinite NonpointX
  have hx := affineX_card_of_point_card card_points
  simp only [Nat.card_eq_fintype_card] at hx
  have complement : Fintype.card NonpointX =
      Fintype.card Fp - Fintype.card AffineX := by
    simpa only [NonpointX, AffineX] using Fintype.card_subtype_compl HasX
  rw [show Fintype.card Fp = p from ZMod.card p, hx] at complement
  simpa only [Nat.card_eq_fintype_card] using complement

 theorem nonpoint_natCard_gt_half (card_points : Nat.card Point = order) :
    2 ^ 255 < Nat.card NonpointX := by
  rw [nonpoint_natCard_of_point_card card_points]
  norm_num [p, order]

end
end ECDSAAdd.Entrant.PointCardinalityBridge
