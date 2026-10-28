import ECDSAAdd.Arithmetic.Paper935.ScalingSeed
import ECDSAAdd.Arithmetic.InverseBothFailure

namespace ECDSAAdd.Arithmetic.Paper935
open Secp256k1 PointInverseEndpoint
noncomputable section
local instance : DecidableEq Point := Classical.decEq _

/-- Four invocations of the supplied closed XOR inverse, not four independent
random inputs. Cleanup repeats its corresponding compute denominator. -/
inductive InverseCallSite
  | quotientCompute | quotientCleanup | productCompute | productCleanup
  deriving DecidableEq, Fintype

structure InverseCallArgs where
  denominator : Fp
  operand : Fp
  enabled : Bool

def quotientCallArgs (C : Point) (x : Bool × Point) : Option InverseCallArgs :=
  match C with
  | .zero => none
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
    let X := ((coordinates x.2).getD (0,0)).1
    let Y := ((coordinates x.2).getD (0,0)).2
    if dialogOrdinary x.1 x.2 (.some hc) then some ⟨X-cx,Y-cy,true⟩ else some ⟨X,Y,false⟩

def productCallArgs (C : Point) (x : Bool × Point) : Option InverseCallArgs :=
  match C with
  | .zero => none
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
    let X := ((coordinates x.2).getD (0,0)).1
    let Y := ((coordinates x.2).getD (0,0)).2
    if dialogOrdinary x.1 x.2 (.some hc) then
      some ⟨cx-genericX X Y cx cy,genericSlope X Y cx cy,true⟩ else some ⟨X,Y,false⟩

/-- Operand is its current value at that inverse invocation; the closed inverse
itself still acts on denominator alone. -/
def inverseCallArgs (C : Point) (site : InverseCallSite) (x : Bool × Point) : Option InverseCallArgs :=
  match site with
  | .quotientCompute => quotientCallArgs C x
  | .quotientCleanup => (quotientCallArgs C x).map fun a =>
      {a with operand := if a.enabled then a.operand/a.denominator else a.operand}
  | .productCompute => productCallArgs C x
  | .productCleanup => (productCallArgs C x).map fun a =>
      {a with operand := if a.enabled then a.operand*a.denominator else a.operand}

theorem quotientCallArgs_input (C : Point) (x : Bool × Point) :
    (quotientCallArgs C x).map (fun a => (a.denominator,a.enabled))=callInput C x := by
  cases C with
  | zero => rfl
  | some hc => simp only [quotientCallArgs,callInput]; split <;> rfl

theorem productCallArgs_input (C : Point) (x : Bool × Point) :
    (productCallArgs C x).map (fun a => (a.denominator,a.enabled))=productCallInput C x := by
  cases C with
  | zero => rfl
  | some hc => simp only [productCallArgs,productCallInput]; split <;> rfl

theorem inverseCallArgs_input (C : Point) (site : InverseCallSite) (x : Bool × Point) :
    (inverseCallArgs C site x).map (fun a => (a.denominator,a.enabled))=
      match site with
      | .quotientCompute | .quotientCleanup => callInput C x
      | .productCompute | .productCleanup => productCallInput C x := by
  cases site <;> simp only [inverseCallArgs,Option.map_map] <;>
    first | exact quotientCallArgs_input C x | exact productCallArgs_input C x

def inverseCallInput (C : Point) (site : InverseCallSite) (x : Bool × Point) : Int :=
  ((inverseCallArgs C site x).map fun a => (a.denominator.val : Int)).getD 0

/-- Each named call has its own seed function on the original labels. -/
def inverseCallSeed (C : Point) (site : InverseCallSite) (x : Bool × Point) : Nat :=
  scaledInverseSeed p (inverseCallInput C site x)

def inverseCallEnabled (C : Point) (site : InverseCallSite) (x : Bool × Point) : Bool :=
  ((inverseCallArgs C site x).map InverseCallArgs.enabled).getD false

theorem inverseCallSeed_of_args (C : Point) (site : InverseCallSite) (x : Bool × Point)
    (a : InverseCallArgs) (h : inverseCallArgs C site x=some a) :
    inverseCallSeed C site x=scaledInverseSeed p a.denominator.val := by
  simp [inverseCallSeed,inverseCallInput,h]

theorem inverseCallArgs_nonzero (C : Point) (site : InverseCallSite) (x : Bool × Point)
    (a : InverseCallArgs) (h : inverseCallArgs C site x=some a) (active : a.enabled=true) :
    a.denominator≠0 := by
  have hi := inverseCallArgs_input C site x
  rw [h] at hi
  simp only [Option.map_some,active] at hi
  cases site <;>
    first | exact callInput_nonzero C x a.denominator hi.symm
          | exact productCallInput_nonzero C x a.denominator hi.symm

/-- No point addition program is emitted for an infinite fixed point. -/
theorem inverseCallArgs_infinity (site : InverseCallSite) (x : Bool × Point) :
    inverseCallArgs .zero site x=none := by cases site <;> rfl

variable [Fintype (Bool × Point)]
local instance : DecidableEq (Bool × Point) := Classical.decEq _

/-- The fifth event for one actual invocation, masked by its actual enabled
flag. The same original labels also index the four trajectory events. -/
def inverseCallScalingFailure (C : Point) (site : InverseCallSite) : Finset (Bool × Point) :=
  (Finset.univ.filter fun x => inverseCallEnabled C site x=true) ∩
    authorScalingFailure (inverseCallInput C site) (inverseCallSeed C site) p 58 (2^256-p)

theorem mem_inverseCallScalingFailure (C : Point) (site : InverseCallSite) (x : Bool × Point) :
    x∈inverseCallScalingFailure C site ↔ inverseCallEnabled C site x=true ∧
      ¬AuthorScalingNoBorrow p 58 (2^256-p) (inverseCallInput C site x) (inverseCallSeed C site x) := by
  simp [inverseCallScalingFailure,mem_authorScalingFailure]

/-- Two explicit inverse invocations for the selected arithmetic adapter. -/
def adapterScalingFailure (C : Point) (multiply : Bool) : Finset (Bool × Point) :=
  if multiply then inverseCallScalingFailure C .productCompute ∪ inverseCallScalingFailure C .productCleanup
  else inverseCallScalingFailure C .quotientCompute ∪ inverseCallScalingFailure C .quotientCleanup

/-- Union over named call sites; no averaging or independence assumption. -/
def pointScalingFailure (C : Point) : Finset (Bool × Point) :=
  Finset.univ.biUnion (inverseCallScalingFailure C)

theorem mem_pointScalingFailure (C : Point) (x : Bool × Point) :
    x∈pointScalingFailure C ↔ ∃ site, inverseCallEnabled C site x=true ∧
      ¬AuthorScalingNoBorrow p 58 (2^256-p) (inverseCallInput C site x) (inverseCallSeed C site x) := by
  simp [pointScalingFailure,mem_inverseCallScalingFailure]

theorem pointScalingFailure_adapters (C : Point) :
    pointScalingFailure C=adapterScalingFailure C false∪adapterScalingFailure C true := by
  have sites : (Finset.univ : Finset InverseCallSite)=
      {.quotientCompute,.quotientCleanup,.productCompute,.productCleanup} := by decide
  ext x
  simp [pointScalingFailure,sites,adapterScalingFailure]

/-- First union all four call instances, then subtract the existing four-cause
bad set. The prior events remain on these same original point labels. -/
def pointScalingExclusive (C : Point) (prior : FailureEvents (Bool × Point)) : Finset (Bool × Point) :=
  scalingExclusive prior (pointScalingFailure C)

theorem pointScalingExclusive_disjoint (C : Point) (prior : FailureEvents (Bool × Point)) :
    Disjoint prior.bad (pointScalingExclusive C prior) :=
  scalingExclusive_disjoint prior (pointScalingFailure C)

end
end ECDSAAdd.Arithmetic.Paper935
