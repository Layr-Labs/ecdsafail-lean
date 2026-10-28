import ECDSAAdd.Arithmetic.MultiplyPorts

namespace ECDSAAdd.Arithmetic

/-- 在已清零借用区的连续片段放置既有1827位Montgomery布局。 -/
def borrowedMont (B : List Wire) (fallback : Wire) (k : Nat) (x y out : List Wire) : MontLayout :=
  poolMul (fun i => B.getD (k+i) fallback) x y out

theorem borrowedMont_widths (B : List Wire) (fallback : Wire) (k : Nat) (x y out : List Wire)
    (hx : x.length=257) (hy : y.length=256) (ho : out.length=257) :
    (borrowedMont B fallback k x y out).Widths := poolMul_widths _ _ _ _ hx hy ho

theorem borrowedMont_prefix (B : List Wire) (fallback : Wire) (k : Nat) (x y out : List Wire)
    (hk : k+1827≤B.length) :
    B.take k ++ (borrowedMont B fallback k x y out).work=B.take (k+1827) := by
  rw [borrowedMont,poolMul_work]
  have hblock : wireBlock (fun i => B.getD (k+i) fallback) 0 1827=(B.drop k).take 1827 := by
    apply List.ext_getElem
    · simp [wireBlock_length]; omega
    · intro i h1 h2
      have hi : i<1827 := by simpa only [wireBlock_length] using h1
      simp [wireBlock,List.getElem_map,List.getElem_range',show k+i<B.length by omega]
  rw [hblock,←List.take_add]

end ECDSAAdd.Arithmetic
