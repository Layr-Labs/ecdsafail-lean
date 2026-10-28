import ECDSAAdd.Arithmetic.InverseCompactStages

namespace ECDSAAdd.Arithmetic

/-- 原终态参数仅决定计数与负值；r已改为结果，历史显式保留，B为空。 -/
abbrev InverseScaledMiddle (L : InverseLoopLayout) (q : Nat) (z : KState)
    (cs : List (Bool×Bool)) (N : Nat) : BasisState → Prop :=
  CompactPrepared L q z.k N cs

end ECDSAAdd.Arithmetic
