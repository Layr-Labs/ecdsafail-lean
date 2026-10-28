import ECDSAAdd.Arithmetic.PointCandidateLayout

namespace ECDSAAdd.Arithmetic

/-- 零检测输入直接连接坐标，工作链借共享池的前缀。 -/
def zeroPorts : List Wire → List Wire → List ZeroBit
  | x::xs,w::ws => ⟨x,w⟩::zeroPorts xs ws
  | _,_ => []

theorem zeroPorts_maps (xs ws : List Wire) (h : xs.length=ws.length) :
    (zeroPorts xs ws).map ZeroBit.input=xs ∧ (zeroPorts xs ws).map ZeroBit.work=ws := by
  induction xs generalizing ws with
  | nil => have he : ws=[] := List.eq_nil_of_length_eq_zero h.symm; subst ws; simp [zeroPorts]
  | cons x xs ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      obtain ⟨hx,hw⟩ := ih ws (by simpa using h)
      simp [zeroPorts,hx,hw]

theorem zeroPorts_perm (xs ws : List Wire) (h : xs.length=ws.length) :
    ((zeroPorts xs ws).flatMap ZeroBit.wires).Perm (xs++ws) := by
  apply List.perm_iff_count.mpr
  intro v
  induction xs generalizing ws with
  | nil => have he : ws=[] := List.eq_nil_of_length_eq_zero h.symm; subst ws; simp [zeroPorts]
  | cons x xs ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      have ht := ih ws (by simpa using h)
      simp only [zeroPorts,List.flatMap_cons,ZeroBit.wires,List.count_append,List.count_cons,List.count_nil] at ht ⊢
      omega

def PointAddLayout.zeroX (L : PointAddLayout) := zeroPorts L.input.x (L.pool.take 256)
def PointAddLayout.zeroY (L : PointAddLayout) := zeroPorts L.input.y (L.pool.take 256)

theorem PointAddLayout.flag_interfaces (L : PointAddLayout) (hn : L.wires.Nodup) :
    (L.input.finite::L.equalX::L.input.x++L.pool.take 256).Nodup ∧
    (L.input.finite::L.equalNegY::L.input.y++L.pool.take 256).Nodup ∧
    [L.input.finite,L.equalX,L.equalNegY,L.generic,L.double].Nodup := by
  have ha (w : Wire) := List.nodup_iff_count.mp hn w
  have hp (w : Wire) : (L.pool.take 256).count w ≤ L.pool.count w := (List.take_sublist 256 L.pool).count_le w
  constructor
  · apply List.nodup_iff_count.mpr; intro w
    have hh := ha w; have ht := hp w
    simp only [PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work,PointAddLayout.flags,
      List.count_append,List.count_cons,List.count_nil] at hh ⊢
    omega
  constructor
  · apply List.nodup_iff_count.mpr; intro w
    have hh := ha w; have ht := hp w
    simp only [PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work,PointAddLayout.flags,
      List.count_append,List.count_cons,List.count_nil] at hh ⊢
    omega
  · apply List.nodup_iff_count.mpr; intro w
    have hh := ha w
    simp only [PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work,PointAddLayout.flags,
      List.count_append,List.count_cons,List.count_nil] at hh ⊢
    omega

def pointFlagsCompute (L : PointAddLayout) (cx cy : Fp) : Program :=
  equalConstant L.input.finite L.equalX L.zeroX cx.val++
  equalConstant L.input.finite L.equalNegY L.zeroY (-cy).val++
  pointBranchFlags L.input.finite L.equalX L.equalNegY L.generic L.double

def pointFlagsClear (L : PointAddLayout) (cx cy : Fp) : Program :=
  pointBranchFlags L.input.finite L.equalX L.equalNegY L.generic L.double++
  equalConstant L.input.finite L.equalNegY L.zeroY (-cy).val++
  equalConstant L.input.finite L.equalX L.zeroX cx.val

end ECDSAAdd.Arithmetic
