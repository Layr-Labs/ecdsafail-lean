import ECDSAAdd.Arithmetic.BalancedFieldCleanup
import ECDSAAdd.Arithmetic.LiteralConstAddProof
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.Rotate
import ECDSAAdd.Framework.GateInverse

namespace ECDSAAdd.Arithmetic.BalancedCleanup
open BalancedField

structure Layout where
  r0 : Wire
  rtail : List Wire
  rmsb : Wire
  ylow : List Wire
  ymsb : Wire
  carry : List Wire
  sign : Wire
  parity : Wire
  lower : Wire
  one : Wire

def Layout.low (L : Layout) := L.r0::L.rtail
def Layout.r (L : Layout) := L.low++[L.rmsb]
def Layout.y (L : Layout) := L.ylow++[L.ymsb]
def Layout.wires (L : Layout) :=
  [L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0]++L.rtail++L.ylow++L.carry

def Layout.Widths (L : Layout) : Prop :=
  L.rtail.length=254 ∧ L.ylow.length=255 ∧ L.carry.length=256

def negativeLiteral : Nat := encodeWord 255 (-h)
def positiveLiteral : Nat := (h-1).toNat

/-- Copy the live result sign, then complement the signed result to magnitude. -/
def prepareSign (L : Layout) : Program :=
  [.CX L.rmsb L.lower]++signComplement L.lower L.r

/-- Rotate the normalized low word, insert the exact low bit, complement
source under S XOR L, and bias both signed words for the existing comparator. -/
def prepareCompare (L : Layout) : Program :=
  rotateLeft L.r++[.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0]++
  signComplement L.sign L.y++signComplement L.lower L.y++[.X L.rmsb,.X L.ymsb]

def normalize (L : Layout) : Program :=
  literalConstAdd L.low (L.carry.take 254) L.lower L.one negativeLiteral

def unnormalize (L : Layout) : Program :=
  [.X L.lower]++literalConstAdd L.low (L.carry.take 254) L.lower L.one positiveLiteral++[.X L.lower]

/-- Only the two Clifford views are reversed. Both measured literal adders
and the comparator are independently emitted forward programs. -/
def program (L : Layout) : Program :=
  prepareSign L++(normalize L++(prepareCompare L++
    (compareLt none L.y L.r L.carry L.one L.parity++
      ((prepareCompare L).reverse++(unnormalize L++(prepareSign L).reverse)))))

 theorem widths (L : Layout) (hw : L.Widths) :
    L.low.length=255 ∧ L.r.length=256 ∧ L.y.length=256 ∧ (L.carry.take 254).length=254 := by
  simp [Layout.low,Layout.r,Layout.y,List.length_take,hw.1,hw.2.1,hw.2.2]

 theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=764 ∧ measurementCount (program L)=764 := by
  have w := widths L hw
  have a := literalConstAdd_counts L.low (L.carry.take 254) L.lower L.one negativeLiteral
    (by omega)
  have b := literalConstAdd_counts L.low (L.carry.take 254) L.lower L.one positiveLiteral
    (by omega)
  have c := compareLt_counts none L.y L.r L.carry L.one L.parity
    (by omega) (by unfold Layout.Widths at hw; omega)
  have rot := rotate_counts L.r
  have r := signComplement_counts L.lower L.r
  have ys := signComplement_counts L.sign L.y
  have yl := signComplement_counts L.lower L.y
  simp only [program,prepareSign,normalize,prepareCompare,unnormalize,
    toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    rot.2.2.1,rot.2.2.2,r.1,r.2,ys.1,ys.2,yl.1,yl.2,a.1,a.2,b.1,b.2,c.1,c.2]
  simp [toffoliCount,measurementCount,w.1,w.2.1]

end ECDSAAdd.Arithmetic.BalancedCleanup

#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.counts

namespace ECDSAAdd.Arithmetic.BalancedCleanup

 theorem Layout.allND (L : Layout) (hn : L.wires.Nodup) :
    ([L.parity,L.sign,L.lower,L.one]++(L.r++(L.y++L.carry))).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w; have h := List.nodup_iff_count.mp hn w
  simp only [Layout.wires,Layout.r,Layout.low,Layout.y,List.count_append,
    List.count_cons,List.count_nil] at h ⊢
  omega

 theorem Layout.flagsND (L : Layout) (hn : L.wires.Nodup) :
    [L.parity,L.sign,L.lower,L.one].Nodup :=
  (List.nodup_append'.mp (L.allND hn)).1

 theorem Layout.dataND (L : Layout) (hn : L.wires.Nodup) : (L.r++(L.y++L.carry)).Nodup :=
  (List.nodup_append'.mp (L.allND hn)).2.1

 theorem Layout.flagAway (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈[L.parity,L.sign,L.lower,L.one]) : q∉(L.r++(L.y++L.carry)) :=
  fun h => List.disjoint_left.mp (List.nodup_append'.mp (L.allND hn)).2.2 hq h

 theorem Layout.normND (L : Layout) (hn : L.wires.Nodup) :
    (L.one::L.lower::(L.low++L.carry.take 254)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w; have h := List.nodup_iff_count.mp hn w
  have c := (List.take_sublist 254 L.carry).count_le w
  simp only [Layout.wires,Layout.low,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

 theorem Layout.compareND (L : Layout) (hn : L.wires.Nodup) :
    (L.parity::L.one::(L.y++L.r++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w; have h := List.nodup_iff_count.mp (L.allND hn) w
  simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

 theorem complement_proper (c : Wire) (r : List Wire) (hc : c∉r) :
    ProperProgram (signComplement c r) := by
  intro i hi
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
  exact fun he => hc (he ▸ hq)

 theorem rotateLeft_proper (r : List Wire) (hn : r.Nodup) : ProperProgram (rotateLeft r) := by
  induction r with
  | nil => simp [rotateLeft,ProperProgram]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateLeft,ProperProgram]
    | cons b r =>
      have ht := List.nodup_cons.mp hn
      have hab : a≠b := fun he => ht.1 (by simp [he])
      apply (properProgram_append _ _).mpr
      exact ⟨ih ht.2,by simpa [ProperProgram,ProperGate,swapBits] using
        (And.intro (Ne.symm hab) (And.intro hab (Ne.symm hab)))⟩

 theorem prepareSign_proper (L : Layout) (hn : L.wires.Nodup) : ProperProgram (prepareSign L) := by
  have away : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  apply (properProgram_append _ _).mpr
  exact ⟨by simp [ProperProgram,ProperGate,show L.rmsb≠L.lower from
    fun he => away (by simp [Layout.r,he])],complement_proper _ _ away⟩

 theorem prepareCompare_proper (L : Layout) (hn : L.wires.Nodup) : ProperProgram (prepareCompare L) := by
  have ndR := (List.nodup_append'.mp (L.dataND hn)).1
  have sR : L.sign∉L.r := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have lR : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have sY : L.sign∉L.y := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have lY : L.lower∉L.y := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  simp only [prepareCompare,properProgram_append]
  refine ⟨⟨⟨⟨rotateLeft_proper _ ndR,?_⟩,complement_proper _ _ sY⟩,
    complement_proper _ _ lY⟩,by simp [ProperProgram,ProperGate]⟩
  simp only [ProperProgram,ProperGate,List.mem_cons,List.not_mem_nil,or_false]
  have hs : L.sign≠L.r0 := fun he => sR (by simp [Layout.r,Layout.low,he])
  have hl : L.lower≠L.r0 := fun he => lR (by simp [Layout.r,Layout.low,he])
  intro i hi
  rcases hi with rfl|rfl|rfl
  · trivial
  · exact hs
  · exact hl

end ECDSAAdd.Arithmetic.BalancedCleanup

#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.prepareCompare_proper
