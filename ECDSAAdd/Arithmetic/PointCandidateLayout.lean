import ECDSAAdd.Arithmetic.PointCandidate

namespace ECDSAAdd.Arithmetic
namespace PointAddLayout

theorem pool_prefix (L : PointAddLayout) (h : L.Widths) (n : Nat) (hn : n≤5699) :
    wireBlock L.poolWire 0 n=L.pool.take n := by
  apply List.ext_getElem
  · simp [wireBlock,h.pool,Nat.min_eq_left hn]
  · intro i hi hj
    have hi' : i<L.pool.length := lt_of_lt_of_le (by simpa [wireBlock] using hi) (h.pool ▸ hn)
    simp [wireBlock,poolWire,List.getD,List.getElem?_eq_getElem hi']

/-- 三种模块在使用池前缀前，只需验证接口加完整工作池互异。
此处一次列出候选计算所有调用的接口，避免为每段引入额外布局前提。 -/
theorem candidate_interfaces_nodup (L : PointAddLayout) (h : L.wires.Nodup) :
    (L.extendedX++L.constant++L.dx++L.pool).Nodup ∧
    (L.extendedY++L.constant++L.dy++L.pool).Nodup ∧
    (L.square++L.extendedX++L.offset++L.pool).Nodup ∧
    (L.offset++L.constant++L.candidateX++L.pool).Nodup ∧
    (L.extendedX++L.candidateX++L.delta++L.pool).Nodup ∧
    (L.product++L.extendedY++L.candidateY++L.pool).Nodup ∧
    (L.dy++L.inverse++L.slope++L.pool).Nodup ∧
    (L.slope++L.constant.take 256++L.square++L.pool).Nodup ∧
    (L.delta++L.slope.take 256++L.product++L.pool).Nodup ∧
    (L.divisor++L.inverse++L.pool).Nodup := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    apply List.nodup_iff_count.mpr
    intro v
    have hh := List.nodup_iff_count.mp h v
    have hc := (List.take_sublist 256 L.constant).count_le v
    have hs := (List.take_sublist 256 L.slope).count_le v
    simp only [wires,work,words,flags,pointWires,extendedX,extendedY,
      List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,
      List.count_cons,List.count_nil] at hh ⊢
    omega

theorem extended_lengths (L : PointAddLayout) (h : L.Widths) :
    L.extendedX.length=257 ∧ L.extendedY.length=257 := by
  simp [extendedX,extendedY,h.inputX,h.inputY]

theorem poolSub_nodup (L : PointAddLayout) (h : L.Widths) (x y out : List Wire)
    (hx : x.length=257) (hy : y.length=257) (ho : out.length=257)
    (hnd : (x++y++out++L.pool).Nodup) : (Arithmetic.poolSub L.poolWire x y out).wires.Nodup := by
  apply Arithmetic.poolSub_nodup _ _ _ _ hx hy ho
  rw [pool_prefix L h 1287 (by omega)]
  exact hnd.sublist ((List.take_sublist 1287 L.pool).append_left _)

theorem poolMul_nodup (L : PointAddLayout) (h : L.Widths) (x y out : List Wire)
    (hnd : (x++y++out++L.pool).Nodup) :
    (Arithmetic.poolMul L.poolWire x y out).wires.Nodup := by
  apply Arithmetic.poolMul_nodup
  rw [pool_prefix L h 1827 (by omega)]
  exact hnd.sublist ((List.take_sublist 1827 L.pool).append_left _)

theorem poolInverse_nodup (L : PointAddLayout) (h : L.Widths) (x out : List Wire)
    (ho : out.length=256) (hnd : (x++out++L.pool).Nodup) :
    (Arithmetic.poolInverse L.poolWire x out).wires.Nodup := by
  apply Arithmetic.poolInverse_nodup _ _ _ ho
  rw [pool_prefix L h 5699 (by omega)]
  exact hnd.sublist ((List.take_sublist 5699 L.pool).append_left _)

end PointAddLayout
end ECDSAAdd.Arithmetic
