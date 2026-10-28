import ECDSAAdd.Arithmetic.PointCandidateLayout
import ECDSAAdd.Arithmetic.CandidatePool

namespace ECDSAAdd.Arithmetic

/-- 模减法只写低输出；最高位仅作为布局填充。 -/
theorem ModLayout.active_interface (L : ModLayout) :
    (L.x++L.y++L.out.take L.width++L.work).Perm L.activeWires := by
  apply List.perm_iff_count.mpr
  intro w
  rcases L with ⟨low,high,cs,cd⟩
  induction low with
  | nil =>
    simp [ModLayout.x,ModLayout.y,ModLayout.out,ModLayout.work,ModLayout.activeWires,
      ModLayout.width,ModLayout.reg,ModLayout.bits,ModBit.get,List.count_cons]
    omega
  | cons b bs ih =>
    simp [ModLayout.x,ModLayout.y,ModLayout.out,ModLayout.work,ModLayout.activeWires,
      ModLayout.width,ModLayout.reg,ModLayout.bits,ModBit.get,ModBit.all,List.count_cons] at ih ⊢
    omega

theorem poolSub_support (L : PointAddLayout) (h : L.Widths) (x y out : List Wire)
    (hx : x.length=257) (hy : y.length=257) (ho : out.length=257) :
    wires (fieldSub (poolSub L.poolWire x y out))=
      (x++y++out.take 256++L.pool.take 1287).toFinset := by
  rw [fieldSub,modSub_wires,← List.toFinset_eq_of_perm _ _ (ModLayout.active_interface _)]
  obtain ⟨hX,hY,hO⟩ := poolSub_inputs L.poolWire x y out hx hy ho
  rw [hX,hY,hO,poolSub_width,poolSub_work,L.pool_prefix h 1287 (by decide)]

theorem poolMul_support (L : PointAddLayout) (h : L.Widths) (x y out : List Wire)
    (hx : x.length=257) (hy : y.length=256) (ho : out.length=257) :
    wires (fieldMul (poolMul L.poolWire x y out))=(x.take 256++y++out++L.pool.take 1827).toFinset := by
  rw [fieldMul,(montAdapter_wires _ p (poolMul_widths _ _ _ _ hx hy ho)).1]
  change (x.take 256++y++out++(poolMul L.poolWire x y out).work).toFinset=_
  rw [poolMul_work,L.pool_prefix h 1827 (by omega)]

theorem poolInverse_support (L : PointAddLayout) (x out : List Wire)
    (hx : x.length=256) (ho : out.length=256) :
    wires (fieldInverse (poolInverse L.poolWire x out))=
      (x++out++poolInverseUsedWork L.poolWire).toFinset := by
  rw [fieldInverse_wires _ (poolInverse_widths _ _ _ hx ho)]
  exact List.toFinset_eq_of_perm _ _ (poolInverse_used_perm L.poolWire x out)

theorem poolInverse_support_subset (L : PointAddLayout) (h : L.Widths) (x out : List Wire)
    (hx : x.length=256) (ho : out.length=256) :
    wires (fieldInverse (poolInverse L.poolWire x out)) ⊆ (x++out++L.pool.take 5699).toFinset := by
  rw [fieldInverse_wires _ (poolInverse_widths _ _ _ hx ho)]
  have hs := (poolInverse L.poolWire x out).usedWires_subset
  have hp : (poolInverse L.poolWire x out).wires.toFinset=(x++out++L.pool.take 5699).toFinset := by
    change ((poolInverse L.poolWire x out).x++(poolInverse L.poolWire x out).out++
      (poolInverse L.poolWire x out).work).toFinset=_
    obtain ⟨hX,hO⟩ := poolInverse_inputs L.poolWire x out ho
    rw [hX,hO]
    have ht := poolInverse_work_perm L.poolWire x out ho
    rw [List.toFinset_append,List.toFinset_append,List.toFinset_eq_of_perm _ _ ht,
      L.pool_prefix h 5699 (by decide)]
    simp
  rw [← hp]
  exact fun _ hm => List.mem_toFinset.mpr (hs (List.mem_toFinset.mp hm))


theorem pointSubConstant_support (L : PointAddLayout) (h : L.Widths)
    (x out : List Wire) (hx : x.length=257) (ho : out.length=257) (k : Nat) :
    wires (pointSubConstant L x out k)=(x++L.constant++out.take 256++L.pool.take 1287).toFinset := by
  have hk := h.words L.constant (by simp [PointAddLayout.words])
  have hc : wires (xorConstant L.constant k) ⊆
      (x++L.constant++out.take 256++L.pool.take 1287).toFinset := by
    intro w hw
    have hh := xorConstant_wires_subset L.constant k hw
    simp only [List.mem_toFinset,List.mem_append] at hh ⊢
    tauto
  rw [pointSubConstant,wires_append,wires_append,poolSub_support L h x L.constant out hx hk ho,
    Finset.union_eq_right.mpr hc,Finset.union_eq_left.mpr hc]

theorem pointSquare_support (L : PointAddLayout) (h : L.Widths) :
    wires (pointSquare L)=(L.slope++L.constant++L.square++L.pool.take 1827).toFinset := by
  have hs := h.words L.slope (by simp [PointAddLayout.words])
  have hk := h.words L.constant (by simp [PointAddLayout.words])
  have ho := h.words L.square (by simp [PointAddLayout.words])
  have hn : L.slope.isEmpty=false := by cases he : L.slope <;> simp_all
  rw [pointSquare,wires_append,wires_append,copyRegister_wires _ _ _ (hs.trans hk.symm),
    poolMul_support L h _ _ _ hs (by simp [hk]) ho]
  simp only [hn,Bool.false_eq_true,if_false,Option.toList_none,List.nil_append]
  ext w
  have ht : w∈L.constant.take 256 → w∈L.constant := List.mem_of_mem_take
  have hst : w∈L.slope.take 256 → w∈L.slope := List.mem_of_mem_take
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_append]
  tauto

theorem safeDivisor_support (g : Wire) (src : List Wire) (head : Wire) (tail : List Wire)
    (hl : src.length=(head::tail).length) :
    wires (safeDivisor g src head tail)=(g::src++head::tail).toFinset := by
  have hn : src.isEmpty=false := by cases he : src <;> simp_all
  rw [safeDivisor,wires_append,copyRegister_wires _ _ _ hl]
  ext w
  simp [hn,wires,Instr.wires]

theorem PointAddLayout.candidatePool_sublist (L : PointAddLayout) (h : L.Widths) :
    (candidatePool L.poolWire).Sublist L.pool := by
  have hh := Arithmetic.candidatePool_sublist L.poolWire
  rw [L.pool_prefix h 5699 (by omega),List.take_of_length_le (by rw [h.pool])] at hh
  exact hh

theorem PointAddLayout.pool_prefix_used (L : PointAddLayout) (h : L.Widths) (n : Nat) (hn : n≤1827) :
    ∀ q∈L.pool.take n, q∈candidatePool L.poolWire := by
  intro q hq
  rw [← List.mem_toFinset,candidatePool_union,L.pool_prefix h 1827 (by omega)]
  exact Finset.mem_union_left _ (List.mem_toFinset.mpr ((by simpa only [List.take_take,Nat.min_eq_left hn] using List.take_sublist n (L.pool.take 1827) : (L.pool.take n).Sublist (L.pool.take 1827)).subset hq))

def PointAddLayout.candidateUsed (L : PointAddLayout) : List Wire :=
  L.extendedX++L.extendedY++L.dx.take 256++L.dy.take 256++L.slope++L.square++L.offset++
    L.candidateX++L.delta.take 256++L.product++L.candidateY.take 256++L.constant++
    L.divisor++L.inverse++[L.generic]++candidatePool L.poolWire

/-- 同一前向模块的计算与清理具有相同支持集；四根填充高位均不在其中。 -/
theorem pointCandidate_support (L : PointAddLayout) (h : L.Widths) (cx cy : Fp) :
    wires (pointCandidateCompute L cx cy)=L.candidateUsed.toFinset ∧
    wires (pointCandidateClear L cx cy)=L.candidateUsed.toFinset := by
  have hdx := h.words L.dx (by simp [PointAddLayout.words])
  have hdy := h.words L.dy (by simp [PointAddLayout.words])
  have hslope := h.words L.slope (by simp [PointAddLayout.words])
  have hsquare := h.words L.square (by simp [PointAddLayout.words])
  have hoffset := h.words L.offset (by simp [PointAddLayout.words])
  have hcandidateX := h.words L.candidateX (by simp [PointAddLayout.words])
  have hdelta := h.words L.delta (by simp [PointAddLayout.words])
  have hproduct := h.words L.product (by simp [PointAddLayout.words])
  have hcandidateY := h.words L.candidateY (by simp [PointAddLayout.words])
  have hconstant := h.words L.constant (by simp [PointAddLayout.words])
  obtain ⟨heX,heY⟩ := L.extended_lengths h
  have hd : L.divisor.head!::L.divisor.tail=L.divisor :=
    List.cons_head!_tail (by intro he; have hh := h.divisor; rw [he] at hh; simp at hh)
  have hsafe := safeDivisor_support L.generic (L.dx.take 256) L.divisor.head! L.divisor.tail
    (by rw [hd]; simp [hdx,h.divisor])
  rw [hd] at hsafe
  have cDx := pointSubConstant_support L h _ _ heX hdx cx.val
  have cDy := pointSubConstant_support L h _ _ heY hdy cy.val
  have cX := pointSubConstant_support L h _ _ hoffset hcandidateX cx.val
  have cOffset := poolSub_support L h _ _ _ hsquare heX hoffset
  have cDelta := poolSub_support L h _ _ _ heX hcandidateX hdelta
  have cY := poolSub_support L h _ _ _ hproduct heY hcandidateY
  have cSlope := poolMul_support L h _ _ _ hdy h.inverse hslope
  have cProduct := poolMul_support L h L.delta (L.slope.take 256) L.product hdelta (by simp [hslope]) hproduct
  have cSquare := pointSquare_support L h
  have cInverse := poolInverse_support L _ _ h.divisor h.inverse
  simp only [pointCandidateCompute,pointCandidateClear,wires_append,cDx,cDy,cX,
    cOffset,cDelta,cY,cSlope,cProduct,cSquare,hsafe,cInverse]
  constructor <;> ext w
  all_goals
    have hp1 : w∈L.pool.take 1287 → w∈L.pool.take 1827 :=
      fun hh => (by simpa only [List.take_take] using List.take_sublist 1287 (L.pool.take 1827) : (L.pool.take 1287).Sublist (L.pool.take 1827)).subset hh
    have hpool : w∈candidatePool L.poolWire ↔ w∈L.pool.take 1827 ∨ w∈poolInverseUsedWork L.poolWire := by
      rw [← List.mem_toFinset,candidatePool_union,L.pool_prefix h 1827 (by omega)]
      simp
    have hs : w∈L.slope.take 256 → w∈L.slope := List.mem_of_mem_take
    have ho : w∈L.offset.take 256 → w∈L.offset := List.mem_of_mem_take
    have hx : w∈L.candidateX.take 256 → w∈L.candidateX := List.mem_of_mem_take
    have hd : w∈L.delta.take 256 → w∈L.delta := List.mem_of_mem_take
    have hy : w∈L.dy.take 256 → w∈L.dy := List.mem_of_mem_take
    simp only [PointAddLayout.candidateUsed,Finset.mem_union,List.mem_toFinset,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,hpool]
    clear cDx cDy cX cOffset cDelta cY cSlope cProduct cSquare cInverse hsafe
    aesop

end ECDSAAdd.Arithmetic
