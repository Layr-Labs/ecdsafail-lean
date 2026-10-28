import ECDSAAdd.Arithmetic.PoolLayout
import ECDSAAdd.Arithmetic.MontAdapterFrame

namespace ECDSAAdd.Arithmetic

/-- 两段Montgomery与共享辅助区占池前1827位；历史在输出更新期间存活。 -/
def poolMul (w : Nat → Wire) (x y out : List Wire) : MontLayout :=
  ⟨x,y,out,⟨wireBlock w 0 261,wireBlock w 261 256,w 517,
    wireBlock w 1036 261,wireBlock w 1297 261,wireBlock w 1558 260,w 1818,
    wireBlock w 1819 5,wireBlock w 1824 3⟩,
    wireBlock w 518 261,wireBlock w 779 256,w 1035⟩

theorem poolMul_inputs (w : Nat → Wire) (x y out : List Wire) :
    (poolMul w x y out).x=x ∧ (poolMul w x y out).y=y ∧ (poolMul w x y out).out=out :=
  ⟨rfl,rfl,rfl⟩

theorem poolMul_work (w : Nat → Wire) (x y out : List Wire) :
    (poolMul w x y out).work=wireBlock w 0 1827 := by
  have hsingle (i : Nat) : [w i]=wireBlock w i 1 := by simp [wireBlock,List.range']
  simp only [poolMul,MontLayout.work,MontLayout.activeA,MontLayout.activeZ,MontLayout.a,
    MontLayout.hA,MontLayout.fA,MontLayout.shared,MontStageLayout.work,hsingle,
    ←List.append_assoc]
  rw [wireBlock_append w 0 261 256,
    wireBlock_append w 0 517 1,
    wireBlock_append w 0 518 261,
    wireBlock_append w 0 779 256,
    wireBlock_append w 0 1035 1,
    wireBlock_append w 0 1036 261,
    wireBlock_append w 0 1297 261,
    wireBlock_append w 0 1558 260,
    wireBlock_append w 0 1818 1,
    wireBlock_append w 0 1819 5,
    wireBlock_append w 0 1824 3]

theorem poolMul_widths (w : Nat → Wire) (x y out : List Wire)
    (hx : x.length=257) (hy : y.length=256) (ho : out.length=257) : (poolMul w x y out).Widths := by
  refine ⟨hx,hy,ho,?_,?_,?_⟩
  · constructor <;> simp [poolMul,wireBlock_length]
  · simp [poolMul,wireBlock_length]
  · simp [poolMul,wireBlock_length]

theorem poolMul_nodup (w : Nat → Wire) (x y out : List Wire)
    (h : (x++y++out++wireBlock w 0 1827).Nodup) : (poolMul w x y out).wires.Nodup := by
  change (x++y++out++(poolMul w x y out).work).Nodup
  rw [poolMul_work]
  exact h

end ECDSAAdd.Arithmetic
