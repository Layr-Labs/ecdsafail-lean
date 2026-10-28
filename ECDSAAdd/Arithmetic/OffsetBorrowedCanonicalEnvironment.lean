import ECDSAAdd.Arithmetic.OffsetBorrowedFieldProgram
import ECDSAAdd.Arithmetic.BalancedSharedFraming
import ECDSAAdd.Arithmetic.DirectSkywalkInput
import ECDSAAdd.Arithmetic.BalancedSharedLayoutTranscript
import ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCallerClean
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedCanonical
open Secp256k1 BalancedField DirectSkywalk

/-- Existing caller invariants plus the canonical source extension. -/
def Env (w : Nat → Wire) (base : BasisState) : Prop :=
  regValue (skywalkSharedField w).work base=0 ∧
  regValue (skywalkSharedUnused w) base=0 ∧ base (w 1026)=false

theorem field_mem_shared (w : Nat → Wire) (q : Wire)
    (hq : q∈(skywalkSharedField w).wires) : q∈skywalkSharedWires w := by
  have block (start len : Nat) (hb : start+len≤2314)
      (hm : q∈wireBlock w start len) : q∈skywalkSharedWires w := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    simp only [List.mem_range'_1] at hi
    exact arith_mem w 0 2314 i (by omega) (by omega)
  simp only [skywalkSharedField,ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,
    ModAddCoreLayout.z,ModAddCoreLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq|hq|hq|hq
  · exact block 770 257 (by omega) hq
  · exact block 2056 256 (by omega) hq
  · subst q; exact arith_mem w 0 2314 2312 (by omega) (by omega)
  · exact block 1540 257 (by omega) hq
  · exact block 1798 256 (by omega) hq
  · subst q; exact arith_mem w 0 2314 1797 (by omega) (by omega)
  · exact block 512 257 (by omega) hq
  · subst q; exact arith_mem w 0 2314 2313 (by omega) (by omega)

theorem unused_mem_shared (w : Nat → Wire) (q : Wire) (hq : q∈skywalkSharedUnused w) :
    q∈skywalkSharedWires w := by
  simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl
  all_goals exact arith_mem w 0 2314 _ (by omega) (by omega)

theorem work_mem_shared (w : Nat → Wire) (q : Wire) (hq : q∈(skywalkSharedField w).work) :
    q∈skywalkSharedWires w := field_mem_shared w q (by simp [ModInPlaceLayout.wires,hq])

theorem env_write (w : Nat → Wire) (q : Wire) (hq : q∉skywalkSharedWires w)
    (base : BasisState) (v : Bool) (h : Env w base) : Env w (writeBit base q v) := by
  have same (i : Wire) (hi : i∈skywalkSharedWires w) : (writeBit base q v) i=base i := by
    simp only [writeBit,Function.update_of_ne (show i≠q from fun e => hq (e ▸ hi))]
  exact ⟨(regValue_congr _ _ _ (fun i hi => same i (work_mem_shared w i hi))).trans h.1,
    (regValue_congr _ _ _ (fun i hi => same i (unused_mem_shared w i hi))).trans h.2.1,
    (same _ (arith_mem w 0 2314 1026 (by omega) (by omega))).trans h.2.2⟩

/-- High-zero follows from the actual original canonical257 source value,
not from a low-word frame or a new unsupported clean-bank premise. -/
theorem env_of_canonical_source (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (base : BasisState) (A : Fp)
    (ha : regValue (skywalkSharedField w).a base=A.val)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) : Env w base := by
  have frame : PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base
      (regValue (wireBlock w 2056 256) base) (regValue (wireBlock w 770 256) base) base :=
    ⟨rfl,rfl,fun _ _ _ => rfl⟩
  exact ⟨hw,hu,OffsetCleanupBorrowedCaller.callerCout_clean w hn base base A _ _ ha frame⟩

theorem pair_env (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (base current : BasisState) (I J : Nat) (he : Env w base)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base I J current) :
    Env w current := by
  let L := balancedSharedPorts w sign
  have full := skywalkShared_field_nodup w hn
  have dis := (List.nodup_append'.mp full).2.2
  have rSub : L.r⊆(skywalkSharedField w).z := by
    rw [balancedSharedPorts_r,skywalkShared_field_z]
    intro q hq
    have eq := wireBlock_append w 2056 256 1
    have mem : q∈wireBlock w 2056 256++wireBlock w 2312 1 := List.mem_append_left _ hq
    simpa only [Nat.reduceAdd,eq] using mem
  have ySub : L.y⊆(skywalkSharedField w).a := by
    rw [balancedSharedPorts_y]
    intro q hq
    change q∈wireBlock w 770 257
    have eq := wireBlock_append w 770 256 1
    have mem : q∈wireBlock w 770 256++wireBlock w 1026 1 := List.mem_append_left _ hq
    simpa only [Nat.reduceAdd,eq] using mem
  have wa (q : Wire) (hq : q∈(skywalkSharedField w).work) : q∉L.r ∧ q∉L.y := by
    constructor
    · intro hm; exact List.disjoint_left.mp dis (List.mem_append_right _ (rSub hm)) hq
    · intro hm; exact List.disjoint_left.mp dis (List.mem_append_left _ (ySub hm)) hq
  have ua (q : Wire) (hq : q∈skywalkSharedUnused w) : q∉L.r ∧ q∉L.y := by
    have no := skywalkShared_unused_outside w hn q hq
    exact ⟨fun hm => no (by simp [ModInPlaceLayout.wires,rSub hm]),
      fun hm => no (by simp [ModInPlaceLayout.wires,ySub hm])⟩
  refine ⟨(regValue_congr _ _ _ (fun q hq => h.2.2 q (wa q hq).1 (wa q hq).2)).trans he.1,
    (regValue_congr _ _ _ (fun q hq => h.2.2 q (ua q hq).1 (ua q hq).2)).trans he.2.1,?_⟩
  have ar : w 1026∉L.r := by rw [balancedSharedPorts_r]; exact arith_block_away w hn 1026 2056 256 (by omega) (by omega) (by omega)
  have ay : w 1026∉L.y := by rw [balancedSharedPorts_y]; exact arith_block_away w hn 1026 770 256 (by omega) (by omega) (by omega)
  exact (h.2.2 _ ar ay).trans he.2.2

end ECDSAAdd.Arithmetic.OffsetBorrowedCanonical

#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedCanonical.env_of_canonical_source
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedCanonical.pair_env
