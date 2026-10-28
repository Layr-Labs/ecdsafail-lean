import ECDSAAdd.Arithmetic.NativeFirstDirectLayout
import ECDSAAdd.Arithmetic.CompactSkywalkTickOutputSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run literalSkywalkSeed

private theorem positive_read (r : List Wire) (s : BasisState) (x : Nat)
    (hv : regValue r s=x) (fit : x<2^(r.length-1)) : signedRegValue r s=(x : Int) := by
  unfold signedRegValue signedDecode
  rw [hv,if_pos fit]

/-- The old emitted seed meets the unchanged first native tick contract.
The extension zero comes from the existing caller workspace invariant. -/
theorem seed_first_input (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s : State) (m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false) :
    SkywalkIntegerInput (compactSkywalkTickLayout w 0)
      ((x : Int)+(p : Int)) (x : Int) false
      (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) m s).basis := by
  have hp : p<2^256 := by norm_num [p]
  have post := literalSkywalkSeed_spec (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w) (literalSkywalkPoolSeed_valid w hn)
    (by omega) hp (hx.trans hp) s m hin
  generalize ht : run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) m s=t at post ⊢
  have p2 : 2^257=2*2^256 := by rw [show 257=256+1 from rfl,pow_succ]; omega
  have sumfit : p+x<2^257 := by rw [p2]; omega
  have xfit : x<2^257 := by rw [p2]; omega
  have ar : (compactSkywalkTickLayout w 0).a=wireBlock w 0 258 := by
    simpa only [compactSkywalkTickPreWidth,narrowSkywalkRouteWidth] using compactSkywalkTick_a w 0 (by omega)
  have br : (compactSkywalkTickLayout w 0).b=wireBlock w 770 258 := by
    simpa only [compactSkywalkTickPreWidth,narrowSkywalkRouteWidth] using compactSkywalkTick_b w 0 (by omega)
  have av : signedRegValue (wireBlock w 0 258) t.basis=((x : Int)+(p : Int)) := by
    have h := positive_read (wireBlock w 0 258) t.basis (p+x) post.2.a
      (by simpa only [wireBlock_length,Nat.reduceSub] using sumfit)
    simpa only [Nat.cast_add,add_comm] using h
  have bv := positive_read (wireBlock w 770 258) t.basis x post.2.b
    (by simpa only [wireBlock_length,Nat.reduceSub] using xfit)
  have keep := literalSkywalkSeed_preserves_outsideA (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w) (literalSkywalkPoolSeed_valid w hn)
    (by omega) hp (hx.trans hp) s m hin (w 258)
    (block_not_mem w hn 258 0 258 (by omega) (by omega) (by omega))
  rw [ht] at keep
  unfold SkywalkIntegerInput
  rw [ar,br]
  refine ⟨av,bv,?_,?_,?_,?_⟩
  · exact post.2.cin
  · exact keep.trans ext
  · exact post.2.one
  · exact post.2.carry

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.seed_first_input
