import ECDSAAdd.Arithmetic.SkywalkRoute

namespace ECDSAAdd.Arithmetic

/-- The retired first low bit stores orientation history. A distinct clean
extension avoids duplicating the old MSB in the full-width source view. -/
structure SkywalkIntegerLayout where
  a0 : Wire
  b0 : Wire
  ext : Wire
  history : Wire
  previous : Wire
  aSign : Wire
  bSign : Wire
  aMid : List Wire
  bMid : List Wire
  carry : List Wire

namespace SkywalkIntegerLayout

def ah (L : SkywalkIntegerLayout) : List Wire := L.aMid++[L.aSign]
def bh (L : SkywalkIntegerLayout) : List Wire := L.bMid++[L.bSign]
def a (L : SkywalkIntegerLayout) : List Wire := L.a0::L.ah
def b (L : SkywalkIntegerLayout) : List Wire := L.b0::L.bh
def half (L : SkywalkIntegerLayout) : List Wire := L.ah++[L.ext]
def wires (L : SkywalkIntegerLayout) : List Wire :=
  L.previous::L.history::L.ext::L.a0::L.b0::(L.ah++L.bh++L.carry)

structure Valid (L : SkywalkIntegerLayout) : Prop where
  mids : L.aMid.length=L.bMid.length
  carry : L.carry.length=L.ah.length
  nodup : L.wires.Nodup

theorem route_nodup (L : SkywalkIntegerLayout) (hv : L.Valid) :
    (L.a0::L.b0::(L.ah++L.bh)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hv.nodup q
  simp only [wires,List.count_cons,List.count_append] at hh ⊢
  omega

theorem record_nodup (L : SkywalkIntegerLayout) (hv : L.Valid) :
    (L.history::(L.half++L.b++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hv.nodup q
  simp only [wires,half,b,List.count_cons,List.count_append,List.count_nil] at hh ⊢
  omega

theorem high_lengths (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.ah.length=L.bh.length := by simp [ah,bh,hv.mids]

theorem record_lengths (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.half.length=L.b.length ∧ L.carry.length+1=L.b.length := by
  have hh := L.high_lengths hv
  simp only [half,b,List.length_append,List.length_cons,List.length_nil,hv.carry]
  omega

end SkywalkIntegerLayout

end ECDSAAdd.Arithmetic
