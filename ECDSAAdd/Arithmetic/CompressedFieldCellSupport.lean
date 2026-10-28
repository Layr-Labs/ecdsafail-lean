import ECDSAAdd.Arithmetic.CompressedFieldActiveSupport
import ECDSAAdd.Arithmetic.CompressedFieldGroupProgram
import ECDSAAdd.Arithmetic.CompressedSkywalkPrefix
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open BalancedCircuit DirectSkywalk
attribute [local irreducible] wires OffsetBorrowedCanonical.body OffsetBorrowedInverseCanonical.body

theorem bodies_active (w : Nat → Wire) (sign eff : Wire) (W : Finset Wire)
    (hk : (sharedSites w sign).toFinset ⊆ W) (he : eff ∈ W) :
    wires (OffsetBorrowedCanonical.body w sign eff) ⊆ W ∧
    wires (OffsetBorrowedInverseCanonical.body w sign eff) ⊆ W := by
  let L := balancedSharedPorts w sign
  have native : L.wires.toFinset ⊆ W := by
    intro q hq
    apply hk
    simp only [sharedSites,List.mem_toFinset,List.mem_append]
    exact Or.inl (Or.inr (List.mem_toFinset.mp hq))
  have signIn : sign ∈ W := hk (by simp [sharedSites])
  have xx : wires [.X sign] ⊆ W := by simp [wires,Instr.wires,Finset.subset_iff,signIn]
  have field := kernels_support w sign
  have fw := field.1.trans hk
  have rv := field.2.trans hk
  have width := BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w sign)
  have sw0 := swapRegisters_wires eff L.r L.y (width.2.1.trans width.2.2.1.symm)
  have sw : wires (swapRegisters eff L.r L.y) ⊆ W := by
    intro q hq
    have h := sw0 hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    rcases h with rfl|h|h
    · exact he
    all_goals
      apply native
      simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
        BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
        List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
  simp only [OffsetBorrowedCanonical.body,OffsetBorrowedInverseCanonical.body,
    OffsetBorrowedInverseCanonical.double,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨xx,fw,xx,sw,sw,xx,rv,xx⟩

/-- Only the two current raw controls are added to the nonhistory kernel
support. Descriptor-only history0/1 never enters this actual support. -/
theorem cells_active (w : Nat → Wire) (b g swap sign eff : Wire) (ig is : Bool)
    (W : Finset Wire) (hk : (sharedSites w sign).toFinset ⊆ W)
    (hb : b ∈ W) (hg : g ∈ W) (hs : swap ∈ W) (he : eff ∈ W) :
    wires (OffsetBorrowedCanonical.cell w b g swap sign eff ig is) ⊆ W ∧
    wires (OffsetBorrowedInverseCanonical.cell w b g swap sign eff ig is) ⊆ W := by
  have body := bodies_active w sign eff W hk he
  have sg : sign ∈ W := hk (by simp [sharedSites])
  constructor
  · exact DirectSupport.selectWindow b g sign ig _ W hb hg sg
      (DirectSupport.selectWindow b swap eff is _ W hb hs he body.1)
  · exact DirectSupport.selectWindow b g sign ig _ W hb hg sg
      (DirectSupport.selectWindow b swap eff is _ W hb hs he body.2)

/-- Every history wire is excluded by the actual shared kernel support,
using only descriptor expansion and injectivity of the declared shared map. -/
theorem history_active_away (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign ∉ skywalkPoolWires w)
    (start : Nat) (hs : start+3 ≤ 512) (j : Fin 6) :
    w (compressedHistoryId start j) ∉ sharedSites w sign := by
  let idx := compressedHistoryId start j
  have bound : idx < 1798 := compressedHistoryId_bound start hs j
  have region := compressedHistoryId_region start hs j
  have signNe : w idx ≠ sign := by
    intro e
    apply ho
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨idx,by omega,e⟩
  have noBlock (a n : Nat) (hbn : a+n ≤ 2314)
      (away : idx < a ∨ a+n ≤ idx) : w idx ∉ wireBlock w a n :=
    arith_block_away w hn idx a n (by omega) hbn away
  have nr := noBlock 2057 254 (by omega) (by dsimp [idx] at *; omega)
  have ny := noBlock 770 255 (by omega) (by dsimp [idx] at *; omega)
  have nc := noBlock 1540 256 (by omega) (by dsimp [idx] at *; omega)
  have nb := noBlock 512 253 (by omega) (by dsimp [idx] at *; omega)
  have flags : w idx ∉ ([765,1026,768,767,766,1796,1797,1027,2311,1025,2056].map w) := by
    intro h
    obtain ⟨k,hk,he⟩ := List.mem_map.mp h
    have kb : k < 2314 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
    have eq := skywalkShared_index_inj w hn k idx kb (by omega) he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    dsimp [idx] at *
    omega
  simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,not_or,
    not_false_eq_true,and_true] at flags
  simp only [sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,OffsetCleanupBorrowedCaller.carry,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false]
  tauto

end ECDSAAdd.Arithmetic.CompressedFieldSupport
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.bodies_active
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.cells_active
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.history_active_away
