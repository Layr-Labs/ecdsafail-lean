import ECDSAAdd.Arithmetic.LiteralConstAddProof
import ECDSAAdd.Arithmetic.SkywalkSeed

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Bank-free seed allocation. Orientation is a boundary observation and
may coincide with Cin; distinctness applies only to physically touched roles. -/
structure LiteralSkywalkSeedLayout where
  a : List Wire
  b : List Wire
  carry : List Wire
  cin : Wire
  one : Wire
  orientation : Wire

namespace LiteralSkywalkSeedLayout

def usedWires (L : LiteralSkywalkSeedLayout) : List Wire :=
  L.one::L.cin::(L.a++L.b++L.carry)

structure Widths (L : LiteralSkywalkSeedLayout) (w : Nat) : Prop where
  a : L.a.length=w
  b : L.b.length=w
  carry : L.carry.length+1=w

structure Valid (L : LiteralSkywalkSeedLayout) : Prop where
  touched : L.usedWires.Nodup
  orientationAway : L.orientation∉L.a

theorem literalND (L : LiteralSkywalkSeedLayout) (hn : L.Valid) :
    (L.one::L.cin::(L.a++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn.touched q
  simp only [usedWires,List.count_cons,List.count_append] at h ⊢
  omega

theorem copyND (L : LiteralSkywalkSeedLayout) (hn : L.Valid) :
    (L.b++L.a).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn.touched q
  simp only [usedWires,List.count_cons,List.count_append] at h ⊢
  omega

theorem outsideA (L : LiteralSkywalkSeedLayout) (hn : L.Valid) (q : Wire)
    (hq : q∈[L.one,L.cin]++L.b++L.carry) : q∉L.a := by
  intro ha
  have h := List.nodup_iff_count.mp hn.touched q
  have hp := List.count_pos_iff.mpr hq
  have hd := List.count_pos_iff.mpr ha
  simp only [usedWires,List.count_cons,List.count_append,List.count_nil] at h hp
  omega

end LiteralSkywalkSeedLayout

structure LiteralSkywalkSeedValues (L : LiteralSkywalkSeedLayout) (A B : Nat)
    (s : BasisState) : Prop where
  a : regValue L.a s=A
  b : regValue L.b s=B
  carry : regValue L.carry s=0
  cin : s L.cin=false
  one : s L.one=false
  orientation : s L.orientation=false

def literalSkywalkSeed (L : LiteralSkywalkSeedLayout) (p : Nat) : Program :=
  copyRegister none L.b L.a++literalConstAdd L.a L.carry L.cin L.one p

/-- Forward literal subtraction and XOR cleanup use fresh measurement records. -/
def literalSkywalkUnseed (L : LiteralSkywalkSeedLayout) (p : Nat) : Program :=
  literalConstAdd L.a L.carry L.cin L.one (2^L.a.length-p)++copyRegister none L.b L.a

theorem literalSkywalkSeed_counts (L : LiteralSkywalkSeedLayout) (w p : Nat)
    (hw : L.Widths w) :
    toffoliCount (literalSkywalkSeed L p)=w-1 ∧
    measurementCount (literalSkywalkSeed L p)=w-1 ∧
    toffoliCount (literalSkywalkUnseed L p)=w-1 ∧
    measurementCount (literalSkywalkUnseed L p)=w-1 := by
  have c := copyRegister_counts none L.b L.a (hw.b.trans hw.a.symm)
  have a := literalConstAdd_counts L.a L.carry L.cin L.one p (hw.carry.trans hw.a.symm)
  have u := literalConstAdd_counts L.a L.carry L.cin L.one (2^L.a.length-p)
    (hw.carry.trans hw.a.symm)
  simp only [literalSkywalkSeed,literalSkywalkUnseed,toffoliCount_append,measurementCount_append]
  rw [c.1,c.2,a.1,a.2,u.1,u.2]
  simp [hw.a]

/-- Allocation support omits a materialized constant bank and counts Cin once. -/
theorem literalSkywalkSeed_support (L : LiteralSkywalkSeedLayout) (w p : Nat)
    (hw : L.Widths w) :
    wires (literalSkywalkSeed L p) ⊆ L.usedWires.toFinset ∧
    wires (literalSkywalkUnseed L p) ⊆ L.usedWires.toFinset := by
  have c := copyRegister_wires none L.b L.a (hw.b.trans hw.a.symm)
  have a := literalConstAdd_wires L.a L.carry L.cin L.one p
  have u := literalConstAdd_wires L.a L.carry L.cin L.one (2^L.a.length-p)
  have cs : wires (copyRegister none L.b L.a) ⊆ L.usedWires.toFinset := by
    intro q hq
    rw [c] at hq
    split_ifs at hq with he
    · simp at hq
    · simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
      simp only [LiteralSkywalkSeedLayout.usedWires,List.mem_toFinset,
        List.mem_cons,List.mem_append]
      tauto
  have lift : ∀k,wires (literalConstAdd L.a L.carry L.cin L.one k) ⊆ L.usedWires.toFinset := by
    intro k q hq
    have h := literalConstAdd_wires L.a L.carry L.cin L.one k hq
    simp only [LiteralSkywalkSeedLayout.usedWires,List.mem_toFinset,
      List.mem_cons,List.mem_append] at h ⊢
    tauto
  constructor <;> intro q hq
  · simp only [literalSkywalkSeed,wires_append,Finset.mem_union] at hq
    exact hq.elim (fun h => cs h) (fun h => (lift p) h)
  · simp only [literalSkywalkUnseed,wires_append,Finset.mem_union] at hq
    exact hq.elim (fun h => (lift _) h) (fun h => cs h)

theorem literalSkywalkSeed_frame (L : LiteralSkywalkSeedLayout) (w p : Nat)
    (hw : L.Widths w) (s : State) (m : List Bool) (q : Wire) (hq : q∉L.usedWires) :
    (run (literalSkywalkSeed L p) m s).basis q=s.basis q ∧
    (run (literalSkywalkUnseed L p) m s).basis q=s.basis q := by
  have hs := literalSkywalkSeed_support L w p hw
  constructor
  · exact run_preserves_outside _ m s q (fun h => hq (List.mem_toFinset.mp (hs.1 h)))
  · exact run_preserves_outside _ m s q (fun h => hq (List.mem_toFinset.mp (hs.2 h)))

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.literalSkywalkSeed_counts
#print axioms ECDSAAdd.Arithmetic.literalSkywalkSeed_frame
