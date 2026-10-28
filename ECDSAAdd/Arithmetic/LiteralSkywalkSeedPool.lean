import ECDSAAdd.Arithmetic.LiteralSkywalkSeedState
import ECDSAAdd.Arithmetic.SkywalkPool

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Cin loans the initial orientation; One loans the first future history bit. -/
def literalSkywalkPoolSeed (w : Nat → Wire) : LiteralSkywalkSeedLayout :=
  { a:=wireBlock w 0 258,b:=wireBlock w 770 258,carry:=wireBlock w 1540 257,
    cin:=w 1797,one:=w 1028,orientation:=w 1797 }

private def poolSeedIds : List Nat :=
  [1028,1797]++List.range' 0 258++List.range' 770 258++List.range' 1540 257
private theorem poolSeedIdsND : poolSeedIds.Nodup := by
  have ab : (List.range' 0 258++List.range' 770 258).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_range'_1] at hj hk
    omega
  have abc : (List.range' 0 258++List.range' 770 258++List.range' 1540 257).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨ab,List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_append,List.mem_range'_1] at hj hk
    omega
  have all : (1028::1797::(List.range' 0 258++List.range' 770 258++
      List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_cons.mpr ⟨?_,abc⟩⟩
    · simp only [List.mem_cons,List.mem_append,List.mem_range'_1]
      omega
    · simp only [List.mem_append,List.mem_range'_1]
      omega
  simpa only [poolSeedIds,List.cons_append,List.nil_append] using all
private theorem poolSeedIdsBound (j : Nat) (hj : j∈poolSeedIds) : j<1798 := by
  simp only [poolSeedIds,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hj
  omega
private theorem poolSeedUsed (w : Nat → Wire) :
    (literalSkywalkPoolSeed w).usedWires=poolSeedIds.map w := by
  simp [literalSkywalkPoolSeed,LiteralSkywalkSeedLayout.usedWires,poolSeedIds,wireBlock]

theorem literalSkywalkPoolSeed_widths (w : Nat → Wire) :
    (literalSkywalkPoolSeed w).Widths 258 := by
  constructor <;> simp [literalSkywalkPoolSeed,wireBlock]

theorem literalSkywalkPoolSeed_valid (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) : (literalSkywalkPoolSeed w).Valid := by
  have mapped : (poolSeedIds.map w).Nodup := by
    apply List.Nodup.map_on
    · intro i hi j hj he
      exact skywalkPool_index_inj w hn i j (poolSeedIdsBound i hi) (poolSeedIdsBound j hj) he
    · exact poolSeedIdsND
  have touched : (literalSkywalkPoolSeed w).usedWires.Nodup := by
    rw [poolSeedUsed]
    exact mapped
  refine ⟨touched,?_⟩
  have cinAway := (List.nodup_cons.mp (List.nodup_cons.mp touched).2).1
  intro hq
  apply cinAway
  change (literalSkywalkPoolSeed w).cin∈(literalSkywalkPoolSeed w).a at hq
  exact List.mem_append_left _ (List.mem_append_left _ hq)

/-- No old constant-bank or numerator-guard site is required by the seed allocation. -/
theorem literalSkywalkPoolSeed_used_subset (w : Nat → Wire) :
    (literalSkywalkPoolSeed w).usedWires ⊆ skywalkPoolWires w := by
  rw [poolSeedUsed]
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
  exact ⟨j,by have h := poolSeedIdsBound j hj; omega,rfl⟩

theorem literalSkywalkPoolSeed_support (w : Nat → Wire) (p : Nat) :
    wires (literalSkywalkSeed (literalSkywalkPoolSeed w) p) ⊆ (skywalkPoolWires w).toFinset ∧
    wires (literalSkywalkUnseed (literalSkywalkPoolSeed w) p) ⊆ (skywalkPoolWires w).toFinset := by
  have hs := literalSkywalkSeed_support (literalSkywalkPoolSeed w) 258 p
    (literalSkywalkPoolSeed_widths w)
  have lift : ∀q∈(literalSkywalkPoolSeed w).usedWires.toFinset,
      q∈(skywalkPoolWires w).toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (literalSkywalkPoolSeed_used_subset w (List.mem_toFinset.mp hq))
  exact ⟨fun q hq => lift q (hs.1 hq),fun q hq => lift q (hs.2 hq)⟩

theorem literalSkywalkPoolSeed_qubitBound (w : Nat → Wire) (p : Nat) :
    qubitCount (literalSkywalkSeed (literalSkywalkPoolSeed w) p)≤775 ∧
    qubitCount (literalSkywalkUnseed (literalSkywalkPoolSeed w) p)≤775 := by
  have hs := literalSkywalkSeed_support (literalSkywalkPoolSeed w) 258 p
    (literalSkywalkPoolSeed_widths w)
  have hc := List.toFinset_card_le (literalSkywalkPoolSeed w).usedWires
  have hl : (literalSkywalkPoolSeed w).usedWires.length=775 := by
    simp [LiteralSkywalkSeedLayout.usedWires,literalSkywalkPoolSeed,wireBlock]
  rw [hl] at hc
  unfold qubitCount
  exact ⟨(Finset.card_le_card hs.1).trans hc,(Finset.card_le_card hs.2).trans hc⟩

theorem literalSkywalkPoolSeed_counts (w : Nat → Wire) (p : Nat) :
    toffoliCount (literalSkywalkSeed (literalSkywalkPoolSeed w) p)=257 ∧
    measurementCount (literalSkywalkSeed (literalSkywalkPoolSeed w) p)=257 ∧
    toffoliCount (literalSkywalkUnseed (literalSkywalkPoolSeed w) p)=257 ∧
    measurementCount (literalSkywalkUnseed (literalSkywalkPoolSeed w) p)=257 :=
  literalSkywalkSeed_counts _ 258 p (literalSkywalkPoolSeed_widths w)

/-- The common Cin/orientation site and loaned tick-zero history are clean
again before the first integer tick, for every measurement stream. -/
theorem literalSkywalkPoolSeed_boundary (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (p x : Nat)
    (hp : p<2^256) (hx : x<2^256) (s : State) (m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis) :
    LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) (p+x) x
      (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) m s).basis ∧
    (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) m s).basis
      (skywalkPoolTick w 0).previous=false ∧
    (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) m s).basis
      (skywalkPoolTick w 0).history=false := by
  have h := (literalSkywalkSeed_spec (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w) (literalSkywalkPoolSeed_valid w hn)
    (by decide) hp hx s m hin).2
  refine ⟨h,?_,h.one⟩
  simpa only [skywalkPoolTick,skywalkPoolPreviousId,if_pos rfl,literalSkywalkPoolSeed] using h.cin

/-- Independent unseed returns both loaned scalar sites clean. -/
theorem literalSkywalkPoolUnseed_boundary (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (p x : Nat)
    (hp : p<2^256) (hx : x<2^256) (s : State) (m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) (p+x) x s.basis) :
    LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x
      (run (literalSkywalkUnseed (literalSkywalkPoolSeed w) p) m s).basis :=
  (literalSkywalkUnseed_spec (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w) (literalSkywalkPoolSeed_valid w hn)
    (by decide) hp hx s m hin).2

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.literalSkywalkPoolSeed_valid
#print axioms ECDSAAdd.Arithmetic.literalSkywalkPoolSeed_boundary
#print axioms ECDSAAdd.Arithmetic.literalSkywalkPoolSeed_qubitBound
