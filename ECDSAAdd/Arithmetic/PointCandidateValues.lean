import ECDSAAdd.Math.AffineFormula

namespace ECDSAAdd.Arithmetic

/-- 无效的普通加法分支以 1 作除数，使求逆模块在所有分支上满足定义域。 -/
def pointSafeDivisor (generic : Bool) (x cx : Fp) : Fp :=
  if generic then x-cx else 1

/-- 与电路中依次保留的候选寄存器一一对应。 -/
structure PointCandidateValues where
  dx : Fp
  dy : Fp
  divisor : Fp
  inverse : Fp
  slope : Fp
  square : Fp
  offset : Fp
  x : Fp
  delta : Fp
  product : Fp
  y : Fp

def pointCandidateValues (generic : Bool) (x y cx cy : Fp) : PointCandidateValues :=
  let dx := x-cx
  let dy := y-cy
  let divisor := pointSafeDivisor generic x cx
  let inverse := divisor⁻¹
  let slope := dy*inverse
  let square := slope*slope
  let offset := square-x
  let candidateX := offset-cx
  let delta := x-candidateX
  let product := delta*slope
  ⟨dx,dy,divisor,inverse,slope,square,offset,candidateX,delta,product,product-y⟩

theorem pointSafeDivisor_ne_zero (generic : Bool) (x cx : Fp)
    (h : generic=true → x≠cx) : pointSafeDivisor generic x cx≠0 := by
  cases generic
  · simp [pointSafeDivisor]
  · simpa [pointSafeDivisor] using sub_ne_zero.mpr (h rfl)

theorem pointCandidateValues_generic (x y cx cy : Fp) :
    (pointCandidateValues true x y cx cy).x=Secp256k1.genericX x y cx cy ∧
    (pointCandidateValues true x y cx cy).y=Secp256k1.genericY x y cx cy := by
  simp only [pointCandidateValues,pointSafeDivisor,if_true,
    Secp256k1.genericX,Secp256k1.genericY,Secp256k1.genericSlope,
    Secp256k1.genericNumerator,Secp256k1.genericDenominator,pow_two]
  exact ⟨True.intro,by rw [mul_comm]⟩

end ECDSAAdd.Arithmetic
