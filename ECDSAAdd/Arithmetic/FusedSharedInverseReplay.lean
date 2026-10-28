import ECDSAAdd.Arithmetic.FusedSharedInverseCell

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Reverse record order, using independently emitted forward inverse cells. -/
def fusedSharedInverseReplay (w : Nat → Wire) : List (Wire×Wire) → Program
  | [] => []
  | r::rs => fusedSharedInverseReplay w rs ++ fusedSharedInverseCell w r.1 r.2

theorem fusedSharedInverseReplay_spec (active : Wire) (w : Nat → Wire)
    (rs : List (Wire×Wire)) (hn : (skywalkSharedWires w).Nodup)
    (ht : SkywalkTapeLayout active (skywalkSharedField w) rs)
    (hf : FusedSharedTapeLayout w rs) (base : BasisState)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (fusedSharedInverseReplay w rs)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (skywalkPayloadReplayInverse (skywalkTapeControls base rs) (X,Y)).1.val
        (skywalkPayloadReplayInverse (skywalkTapeControls base rs) (X,Y)).2.val) := by
  induction rs generalizing X Y with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons r rs ih =>
    have hr := ht r (by simp)
    have ht' : SkywalkTapeLayout active (skywalkSharedField w) rs :=
      fun q hq => ht q (by simp [hq])
    have hf0 := hf r (by simp)
    have hf' : FusedSharedTapeLayout w rs := fun q hq => hf q (by simp [hq])
    let Q := skywalkPayloadReplayInverse (skywalkTapeControls base rs) (X,Y)
    have h1 := ih ht' hf' X Y
    have h2 := fusedSharedInverse_leaf_frame active r.2 r.1 w hn hf0.1 hr
      hf0.2.1 base hk hu Q.1 Q.2
    simpa only [fusedSharedInverseReplay,skywalkTapeControls,List.map_cons,
      skywalkPayloadReplayInverse,Q] using h1.seq h2

theorem fusedSharedInverseReplay_counts (active : Wire) (w : Nat → Wire)
    (rs : List (Wire×Wire)) (ht : SkywalkTapeLayout active (skywalkSharedField w) rs) :
    toffoliCount (fusedSharedInverseReplay w rs)=rs.length*1794 ∧
    measurementCount (fusedSharedInverseReplay w rs)=rs.length*1538 := by
  induction rs with
  | nil => simp [fusedSharedInverseReplay,toffoliCount,measurementCount]
  | cons r rs ih =>
    have hr := ht r (by simp)
    have ht' : SkywalkTapeLayout active (skywalkSharedField w) rs :=
      fun q hq => ht q (by simp [hq])
    have hnd : (r.2::(skywalkSharedField w).z++(skywalkSharedField w).a).Nodup := by
      apply List.nodup_iff_count.mpr
      intro q
      have hc := List.nodup_iff_count.mp hr q
      simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hc ⊢
      omega
    have hc := fusedSharedInverseCell_counts w r.1 r.2 hnd
    have hi := ih ht'
    simp only [fusedSharedInverseReplay,toffoliCount_append,measurementCount_append,
      hc.1,hc.2,hi.1,hi.2,List.length_cons,Nat.add_mul]
    trivial

end ECDSAAdd.Arithmetic
