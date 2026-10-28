import ECDSAAdd.Arithmetic.PointFlags
import ECDSAAdd.Arithmetic.PointCandidateValues

namespace ECDSAAdd.Arithmetic

/-- 候选计算保留九个 257 位值，另借一个同宽寄存器装载常量或复制乘数。
除数和逆元只需 256 位；两个输入最高位独立保持零。 -/
structure PointAddLayout where
  input : PointReg
  output : PointReg
  dx : List Wire
  dy : List Wire
  slope : List Wire
  square : List Wire
  offset : List Wire
  candidateX : List Wire
  delta : List Wire
  product : List Wire
  candidateY : List Wire
  constant : List Wire
  divisor : List Wire
  inverse : List Wire
  inputXHigh : Wire
  inputYHigh : Wire
  equalX : Wire
  equalNegY : Wire
  generic : Wire
  double : Wire
  pool : List Wire

namespace PointAddLayout

def words (L : PointAddLayout) : List (List Wire) :=
  [L.dx,L.dy,L.slope,L.square,L.offset,L.candidateX,L.delta,L.product,L.candidateY,L.constant]

def flags (L : PointAddLayout) : List Wire :=
  [L.equalX,L.equalNegY,L.generic,L.double]

def pointWires (r : PointReg) : List Wire := r.finite::r.x++r.y

def work (L : PointAddLayout) : List Wire :=
  L.words.flatten++L.divisor++L.inverse++[L.inputXHigh,L.inputYHigh]++L.flags++L.pool

def wires (L : PointAddLayout) : List Wire :=
  pointWires L.input++pointWires L.output++L.work

/-- 宽度是公开布局条件；工作池按求逆的现有分配前缀分配。 -/
structure Widths (L : PointAddLayout) : Prop where
  inputX : L.input.x.length=256
  inputY : L.input.y.length=256
  outputX : L.output.x.length=256
  outputY : L.output.y.length=256
  words : ∀ r∈L.words,r.length=257
  divisor : L.divisor.length=256
  inverse : L.inverse.length=256
  pool : L.pool.length=5699

theorem allocated_length (L : PointAddLayout) (h : L.Widths) : L.wires.length=9813 := by
  have hw : L.words.flatten.length=257*L.words.length := by
    have aux : ∀ rs : List (List Wire), (∀ r∈rs,r.length=257) →
        rs.flatten.length=257*rs.length := by
      intro rs hr
      induction rs with
      | nil => simp
      | cons r rs ih =>
        simp only [List.flatten_cons,List.length_append,List.length_cons]
        rw [hr r (by simp),ih (fun r hm => hr r (by simp [hm]))]
        omega
    exact aux L.words h.words
  have hwl : L.words.length=10 := rfl
  rw [hwl] at hw
  simp only [wires,pointWires,work,flags,List.length_append,List.length_cons,
    List.length_nil,hw,h.inputX,h.inputY,h.outputX,h.outputY,h.divisor,h.inverse,h.pool]

end PointAddLayout
end ECDSAAdd.Arithmetic
