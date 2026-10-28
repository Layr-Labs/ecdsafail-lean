import ECDSAAdd.Arithmetic.SkywalkIntegerLayout
import ECDSAAdd.Arithmetic.PoolLayout

namespace ECDSAAdd.Arithmetic

/-- Fixed exact campaign: 258-bit signed words and all 512 logical rounds. -/
def skywalkPoolWires (w : Nat → Wire) : List Wire := wireBlock w 0 1798

def skywalkPoolPreviousId (i : Nat) : Nat := if i=0 then 1797 else i-1

def skywalkPoolTick (w : Nat → Wire) (i : Nat) : SkywalkIntegerLayout :=
  { a0:=w i,b0:=w 770,ext:=w (i+258),history:=w (1028+i),
    previous:=w (skywalkPoolPreviousId i),aSign:=w (i+257),bSign:=w 1027,
    aMid:=wireBlock w (i+1) 256,bMid:=wireBlock w 771 256,
    carry:=wireBlock w 1540 257 }

def skywalkPoolTickIds (i : Nat) : List Nat :=
  skywalkPoolPreviousId i::(1028+i)::(i+258)::i::770::
    (List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257)

def skywalkPoolA (w : Nat → Wire) (i : Nat) : List Wire := wireBlock w i 258
def skywalkPoolB (w : Nat → Wire) : List Wire := wireBlock w 770 258

def skywalkPoolPastIds (i : Nat) : List Nat := List.range' 0 i++List.range' 1028 i

def skywalkPoolPast (w : Nat → Wire) (i : Nat) : List Wire := (skywalkPoolPastIds i).map w

private theorem block_one (w : Nat → Wire) (s : Nat) : wireBlock w s 1=[w s] := by
  simp [wireBlock,List.range']

theorem skywalkPool_ah (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).ah=wireBlock w (i+1) 257 := by
  change wireBlock w (i+1) 256++[w (i+257)]=_
  have he := wireBlock_append w (i+1) 256 1
  simp only [block_one,Nat.add_assoc,Nat.reduceAdd] at he
  exact he

theorem skywalkPool_bh (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).bh=wireBlock w 771 257 := by
  change wireBlock w 771 256++[w 1027]=_
  have he := wireBlock_append w 771 256 1
  simp only [block_one,Nat.reduceAdd] at he
  exact he

theorem skywalkPool_a (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).a=skywalkPoolA w i := by
  change w i::(skywalkPoolTick w i).ah=wireBlock w i 258
  rw [skywalkPool_ah]
  have he := wireBlock_append w i 1 257
  simp only [block_one,Nat.reduceAdd] at he
  exact he

theorem skywalkPool_b (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).b=skywalkPoolB w := by
  change w 770::(skywalkPoolTick w i).bh=wireBlock w 770 258
  rw [skywalkPool_bh]
  have he := wireBlock_append w 770 1 257
  simp only [block_one,Nat.reduceAdd] at he
  exact he

theorem skywalkPool_half (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).half=skywalkPoolA w (i+1) := by
  change (skywalkPoolTick w i).ah++[w (i+258)]=wireBlock w (i+1) 258
  rw [skywalkPool_ah]
  have he := wireBlock_append w (i+1) 257 1
  simp only [block_one,Nat.add_assoc,Nat.reduceAdd] at he
  exact he

/-- Every successor uses precisely the previous relabelled half-word. -/
theorem skywalkPool_chain (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).half=(skywalkPoolTick w (i+1)).a ∧
    (skywalkPoolTick w i).b=(skywalkPoolTick w (i+1)).b ∧
    (skywalkPoolTick w (i+1)).previous=(skywalkPoolTick w i).a0 := by
  refine ⟨by rw [skywalkPool_half,skywalkPool_a],by rw [skywalkPool_b,skywalkPool_b],?_⟩
  change w (skywalkPoolPreviousId (i+1))=w i
  simp only [skywalkPoolPreviousId,if_neg (show i+1≠0 by omega),Nat.add_sub_cancel]

theorem skywalkPool_wires_map (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).wires=(skywalkPoolTickIds i).map w := by
  change w (skywalkPoolPreviousId i)::w (1028+i)::w (i+258)::w i::w 770::
    ((skywalkPoolTick w i).ah++(skywalkPoolTick w i).bh++wireBlock w 1540 257)=_
  rw [skywalkPool_ah,skywalkPool_bh]
  simp only [skywalkPoolTickIds,List.map_cons,List.map_append,wireBlock]

private theorem pool_tickIds_nodup (i : Nat) (hi : i<512) : (skywalkPoolTickIds i).Nodup := by
  have hab : (List.range' (i+1) 257++List.range' 771 257).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_range'_1] at hj hk
    omega
  have hbase : (List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨hab,List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_append,List.mem_range'_1] at hj hk
    omega
  have h770 : (770::(List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,hbase⟩
    intro hm
    simp only [List.mem_append,List.mem_range'_1] at hm
    omega
  have ha0 : (i::770::(List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,h770⟩
    intro hm
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hm
    omega
  have hext : ((i+258)::i::770::(List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,ha0⟩
    intro hm
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hm
    omega
  have hhist : ((1028+i)::(i+258)::i::770::
      (List.range' (i+1) 257++List.range' 771 257++List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,hext⟩
    intro hm
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hm
    omega
  apply List.nodup_cons.mpr
  refine ⟨?_,hhist⟩
  intro hm
  by_cases hz : i=0
  · subst i
    rw [show skywalkPoolPreviousId 0=1797 from rfl] at hm
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hm
    omega
  · simp only [skywalkPoolPreviousId,if_neg hz,List.mem_cons,List.mem_append,List.mem_range'_1] at hm
    omega

theorem skywalkPool_id_bound (i j : Nat) (hi : i<512) (hj : j∈skywalkPoolTickIds i) : j<1798 := by
  by_cases hz : i=0
  · subst i
    simp only [skywalkPoolTickIds,show skywalkPoolPreviousId 0=1797 from rfl,
      List.mem_cons,List.mem_append,List.mem_range'_1] at hj
    omega
  · simp only [skywalkPoolTickIds,skywalkPoolPreviousId,if_neg hz,List.mem_cons,
      List.mem_append,List.mem_range'_1] at hj
    omega

/-- Pool Nodup supplies precisely the needed local injectivity; the caller's
wire map need not be globally injective outside these 1798 indices. -/
theorem skywalkPool_index_inj (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i<1798) (hj : j<1798) (he : w i=w j) : i=j := by
  change ((List.range' 0 1798).map w).Nodup at hn
  exact List.inj_on_of_nodup_map hn
    (by simp only [List.mem_range'_1]; omega)
    (by simp only [List.mem_range'_1]; omega) he

theorem skywalkPool_valid (w : Nat → Wire) (i : Nat) (hi : i<512)
    (hn : (skywalkPoolWires w).Nodup) : (skywalkPoolTick w i).Valid := by
  constructor
  · simp [skywalkPoolTick,wireBlock_length]
  · rw [skywalkPool_ah]
    simp [skywalkPoolTick,wireBlock_length]
  · rw [skywalkPool_wires_map]
    apply List.Nodup.map_on
    · intro j hj k hk he
      exact skywalkPool_index_inj w hn j k (skywalkPool_id_bound i j hi hj)
        (skywalkPool_id_bound i k hi hk) he
    · exact pool_tickIds_nodup i hi

theorem skywalkPool_valid_injective (w : Nat → Wire) (hw : Function.Injective w)
    (i : Nat) (hi : i<512) : (skywalkPoolTick w i).Valid := by
  apply skywalkPool_valid w i hi
  unfold skywalkPoolWires wireBlock
  exact List.Nodup.map hw List.nodup_range'

theorem skywalkPool_layout_support (w : Nat → Wire) (i : Nat) (hi : i<512) :
    (skywalkPoolTick w i).wires.toFinset⊆(skywalkPoolWires w).toFinset := by
  rw [skywalkPool_wires_map]
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨j,?_,rfl⟩
  simp only [List.mem_range'_1]
  have hb := skywalkPool_id_bound i j hi hj
  omega

/-- Instantiating the native tick's proved support theorem closes support for
any actual program with this concrete tick interface. -/
theorem skywalkPool_program_support (w : Nat → Wire) (i : Nat) (hi : i<512)
    (p : Program) (hp : wires p⊆(skywalkPoolTick w i).wires.toFinset) :
    wires p⊆(skywalkPoolWires w).toFinset := hp.trans (skywalkPool_layout_support w i hi)

private theorem pool_fresh_index (i j : Nat) (hi : i<512) (hj : j < i) :
    i+258∉skywalkPoolTickIds j ∧ 1028+i∉skywalkPoolTickIds j := by
  by_cases hz : j=0
  · subst j
    simp only [skywalkPoolTickIds,show skywalkPoolPreviousId 0=1797 from rfl,
      List.mem_cons,List.mem_append,List.mem_range'_1]
    omega
  · simp only [skywalkPoolTickIds,skywalkPoolPreviousId,if_neg hz,List.mem_cons,
      List.mem_append,List.mem_range'_1]
    omega

private theorem pool_not_mem_map (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (a : Nat) (ha : a<1798) (ls : List Nat) (hl : ∀ j∈ls,j<1798) (he : a∉ls) : w a∉ls.map w := by
  intro hm
  obtain ⟨j,hj,hwa⟩ := List.mem_map.mp hm
  have hij : j=a := skywalkPool_index_inj w hn j a (hl j hj) ha hwa
  subst j
  exact he hj

/-- Fresh extension/history wires cannot have been touched by any previous tick.
This includes all past orientation and sign records as well as reused carries. -/
theorem skywalkPool_fresh_previous (w : Nat → Wire) (i j : Nat) (hi : i<512) (hj : j < i)
    (hn : (skywalkPoolWires w).Nodup) :
    (skywalkPoolTick w i).ext∉(skywalkPoolTick w j).wires ∧
      (skywalkPoolTick w i).history∉(skywalkPoolTick w j).wires := by
  simp only [skywalkPool_wires_map]
  have hji : j<512 := by omega
  have hf := pool_fresh_index i j hi hj
  exact ⟨pool_not_mem_map w hn (i+258) (by omega) _
      (skywalkPool_id_bound j · hji) hf.1,
    pool_not_mem_map w hn (1028+i) (by omega) _
      (skywalkPool_id_bound j · hji) hf.2⟩

theorem skywalkPool_fresh_past (w : Nat → Wire) (i : Nat) (hi : i<512)
    (hn : (skywalkPoolWires w).Nodup) :
    (skywalkPoolTick w i).ext∉skywalkPoolPast w i ∧
      (skywalkPoolTick w i).history∉skywalkPoolPast w i := by
  have hb : ∀ j∈skywalkPoolPastIds i,j<1798 := by
    intro j hj
    simp only [skywalkPoolPastIds,List.mem_append,List.mem_range'_1] at hj
    omega
  have he : i+258∉skywalkPoolPastIds i ∧ 1028+i∉skywalkPoolPastIds i := by
    simp only [skywalkPoolPastIds,List.mem_append,List.mem_range'_1]
    omega
  exact ⟨pool_not_mem_map w hn _ (by omega) _ hb he.1,
    pool_not_mem_map w hn _ (by omega) _ hb he.2⟩

/-- Fresh sites are outside the current data words and every past record. -/
theorem skywalkPool_fresh_current (w : Nat → Wire) (i : Nat) (hi : i<512)
    (hn : (skywalkPoolWires w).Nodup) :
    (skywalkPoolTick w i).ext∉skywalkPoolA w i++skywalkPoolB w++skywalkPoolPast w i ∧
      (skywalkPoolTick w i).history∉skywalkPoolA w i++skywalkPoolB w++skywalkPoolPast w i := by
  let ls := List.range' i 258++List.range' 770 258++skywalkPoolPastIds i
  have hm : skywalkPoolA w i++skywalkPoolB w++skywalkPoolPast w i=ls.map w := by
    simp only [skywalkPoolA,skywalkPoolB,skywalkPoolPast,wireBlock,ls,List.map_append]
  rw [hm]
  have hb : ∀ j∈ls,j<1798 := by
    intro j hj
    simp only [ls,skywalkPoolPastIds,List.mem_append,List.mem_range'_1] at hj
    omega
  have he : i+258∉ls ∧ 1028+i∉ls := by
    simp only [ls,skywalkPoolPastIds,List.mem_append,List.mem_range'_1]
    omega
  exact ⟨pool_not_mem_map w hn _ (by omega) _ hb he.1,
    pool_not_mem_map w hn _ (by omega) _ hb he.2⟩

/-- Initial rail views, terminal post-half views and final orientation record. -/
theorem skywalkPool_endpoints (w : Nat → Wire) :
    (skywalkPoolTick w 0).a=wireBlock w 0 258 ∧
    (skywalkPoolTick w 0).b=wireBlock w 770 258 ∧
    (skywalkPoolTick w 0).previous=w 1797 ∧
    (skywalkPoolTick w 511).half=wireBlock w 512 258 ∧
    (skywalkPoolTick w 511).b=wireBlock w 770 258 ∧
    (skywalkPoolTick w 511).a0=w 511 := by
  exact ⟨skywalkPool_a w 0,skywalkPool_b w 0,rfl,
    skywalkPool_half w 511,skywalkPool_b w 511,rfl⟩

end ECDSAAdd.Arithmetic
