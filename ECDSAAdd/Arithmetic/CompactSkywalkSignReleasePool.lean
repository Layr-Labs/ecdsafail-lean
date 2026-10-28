import ECDSAAdd.Arithmetic.CompactSkywalkSignReleaseViews
import ECDSAAdd.Arithmetic.NarrowSkywalkRouteTick

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

def compactSkywalkSignPoolA (w : Nat → Wire) (i : Nat) : CompactSkywalkSignReleaseLayout :=
  compactSkywalkSignWord (skywalkPoolA w i) (narrowSkywalkRouteWidth i)
def compactSkywalkSignPoolB (w : Nat → Wire) (i : Nat) : CompactSkywalkSignReleaseLayout :=
  compactSkywalkSignWord (skywalkPoolB w) (narrowSkywalkRouteWidth i)

def compactSkywalkSignPoolRelease (w : Nat → Wire) (i : Nat) : Program :=
  compactSkywalkSignRelease (compactSkywalkSignPoolA w i)++
    compactSkywalkSignRelease (compactSkywalkSignPoolB w i)
def compactSkywalkSignPoolExpand (w : Nat → Wire) (i : Nat) : Program :=
  compactSkywalkSignExpand (compactSkywalkSignPoolB w i)++
    compactSkywalkSignExpand (compactSkywalkSignPoolA w i)

private theorem blockND (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start count : Nat) (hb : start+count ≤ 1798) : (wireBlock w start count).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj he
    simp only [List.mem_range'_1] at hi hj
    exact skywalkPool_index_inj w hn i j (by omega) (by omega) he
  · exact List.nodup_range'

theorem compactSkywalkSignPool_wordsND (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    (skywalkPoolA w i).Nodup ∧ (skywalkPoolB w).Nodup :=
  ⟨blockND w hn i 258 (by omega),blockND w hn 770 258 (by decide)⟩

theorem compactSkywalkSignPool_valid (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    (compactSkywalkSignPoolA w i).Valid ∧ (compactSkywalkSignPoolB w i).Valid := by
  have hw := narrowSkywalkRouteWidth_bounds i hi
  have nd := compactSkywalkSignPool_wordsND w i hi hn
  exact ⟨compactSkywalkSignWord_valid _ _ (by omega)
    (by simpa [skywalkPoolA,wireBlock] using hw.2.1) nd.1,
    compactSkywalkSignWord_valid _ _ (by omega)
    (by simpa [skywalkPoolB,wireBlock] using hw.2.1) nd.2⟩

theorem compactSkywalkSignPool_wordsDisjoint (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) : (skywalkPoolA w i).Disjoint (skywalkPoolB w) := by
  apply List.disjoint_left.mpr
  intro q ha hb
  simp only [skywalkPoolA,skywalkPoolB,wireBlock,List.mem_map,List.mem_range'_1] at ha hb
  obtain ⟨a,ha,hea⟩ := ha
  obtain ⟨b,hb,heb⟩ := hb
  have he := skywalkPool_index_inj w hn a b (by omega) (by omega) (hea.trans heb.symm)
  omega

/-- The exact universal route bound supplies both physical sign-copy banks
for every complete valid nonzero coprime input and every one of the512 stages. -/
theorem compactSkywalkSignPool_stage_copies (w : Nat → Wire) (x p i : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (hi : i < 512) (s : BasisState)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s) :
    (compactSkywalkSignPoolA w i).Copies s ∧ (compactSkywalkSignPoolB w i).Copies s := by
  have fit := narrowSkywalkRoute_iter_fit x p i hp0 hx0 hpo hp hx hc hi
  have hw := narrowSkywalkRouteWidth_bounds i hi
  exact ⟨compactSkywalkSignWord_copies _ _ (by omega)
    (by simpa [skywalkPoolA,wireBlock] using hw.2.1) s _ hin.1 fit.1 fit.2.1,
    compactSkywalkSignWord_copies _ _ (by omega)
    (by simpa [skywalkPoolB,wireBlock] using hw.2.1) s _ hin.2.1 fit.2.2.1 fit.2.2.2⟩

theorem compactSkywalkSignPool_released_lengths (w : Nat → Wire) (i : Nat) :
    (compactSkywalkSignPoolA w i).released.length = 258-narrowSkywalkRouteWidth i ∧
    (compactSkywalkSignPoolB w i).released.length = 258-narrowSkywalkRouteWidth i := by
  simp [compactSkywalkSignPoolA,compactSkywalkSignPoolB,compactSkywalkSignWord,
    skywalkPoolA,skywalkPoolB,wireBlock]

theorem compactSkywalkSignPool_counts (w : Nat → Wire) (i : Nat) :
    toffoliCount (compactSkywalkSignPoolRelease w i) = 0 ∧
    measurementCount (compactSkywalkSignPoolRelease w i) = 0 ∧
    toffoliCount (compactSkywalkSignPoolExpand w i) = 0 ∧
    measurementCount (compactSkywalkSignPoolExpand w i) = 0 := by
  have a := compactSkywalkSignRelease_counts (compactSkywalkSignPoolA w i)
  have b := compactSkywalkSignRelease_counts (compactSkywalkSignPoolB w i)
  simp only [compactSkywalkSignPoolRelease,compactSkywalkSignPoolExpand,toffoliCount_append,
    measurementCount_append,a.1,a.2.1,a.2.2.1,a.2.2.2,b.1,b.2.1,b.2.2.1,b.2.2.2,Nat.zero_add]
  trivial

/-- All measurement streams are immaterial to these Clifford prefixes. -/

theorem compactSkywalkSign_no_measure_append (p q : Program) (hp : measurementCount p = 0)
    (s : State) (m : List Bool) : run (p++q) m s = run q m (run p m s) := by
  have h := run_take p m s
  rw [hp,List.take_zero] at h
  rw [run_append,hp,List.take_zero,List.drop_zero,h]

/-- Both physical two-bank compositions are exact State inverses. -/
theorem compactSkywalkSignPool_roundtrip (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m1 m2 : List Bool) :
    run (compactSkywalkSignPoolExpand w i) m2 (run (compactSkywalkSignPoolRelease w i) m1 s) = s ∧
    run (compactSkywalkSignPoolRelease w i) m2 (run (compactSkywalkSignPoolExpand w i) m1 s) = s := by
  let A := compactSkywalkSignPoolA w i
  let B := compactSkywalkSignPoolB w i
  have hv := compactSkywalkSignPool_valid w i hi hn
  have ca := compactSkywalkSignRelease_counts A
  have cb := compactSkywalkSignRelease_counts B
  constructor
  · change run (compactSkywalkSignExpand B++compactSkywalkSignExpand A) m2
      (run (compactSkywalkSignRelease A++compactSkywalkSignRelease B) m1 s) = s
    rw [compactSkywalkSign_no_measure_append _ _ ca.2.1,
      compactSkywalkSign_no_measure_append _ _ cb.2.2.2]
    rw [(compactSkywalkSignRelease_roundtrip B hv.2
      (run (compactSkywalkSignRelease A) m1 s) m1 m2).1]
    exact (compactSkywalkSignRelease_roundtrip A hv.1 s m1 m2).1
  · change run (compactSkywalkSignRelease A++compactSkywalkSignRelease B) m2
      (run (compactSkywalkSignExpand B++compactSkywalkSignExpand A) m1 s) = s
    rw [compactSkywalkSign_no_measure_append _ _ cb.2.2.2,
      compactSkywalkSign_no_measure_append _ _ ca.2.1]
    rw [(compactSkywalkSignRelease_roundtrip A hv.1
      (run (compactSkywalkSignExpand B) m1 s) m1 m2).2]
    exact (compactSkywalkSignRelease_roundtrip B hv.2 s m1 m2).2

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignPool_stage_copies
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignPool_roundtrip
