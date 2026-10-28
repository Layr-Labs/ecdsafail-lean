import ECDSAAdd.Arithmetic.CuccaroNormalizedModProof
import ECDSAAdd.Arithmetic.CuccaroSignedSquareInverse

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic

theorem xorConstant_unitary (r : List Wire) (k : Nat) :
    ProperProgram (xorConstant r k) := by
  induction r generalizing k with
  | nil => simp [xorConstant,ProperProgram]
  | cons q r ih =>
    by_cases h : k%2=1
    · simp only [xorConstant,h,if_true,properProgram_append]
      exact ⟨by simp [ProperProgram,ProperGate],ih (k/2)⟩
    · simpa [xorConstant,h] using ih (k/2)

theorem maskedConstant_unitary (c : Wire) (r : List Wire) (k : Nat)
    (hc : c∉r) : ProperProgram (maskedConstant c r k) := by
  induction r generalizing k with
  | nil => simp [maskedConstant,ProperProgram]
  | cons q r ih =>
    have cq : c≠q := fun e => hc (by simp [e])
    have cr : c∉r := fun h => hc (by simp [h])
    by_cases h : k%2=1
    · simp only [maskedConstant,h,if_true,properProgram_append]
      exact ⟨by simpa [ProperProgram,ProperGate] using cq,ih (k/2) cr⟩
    · simpa [maskedConstant,h] using ih (k/2) cr

private theorem mod_nd (L : CuccaroModLayout) (hn : L.wires.Nodup)
    (r : List Wire) (hr : ∀q,r.count q≤L.wires.count q) : r.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  exact (hr q).trans (List.nodup_iff_count.mp hn q)

theorem cuccaroMod_unitary (L : CuccaroModLayout) (p : Nat) (hn : L.wires.Nodup) :
    ProperProgram (cuccaroModAdd L p) ∧ ProperProgram (cuccaroModSub L p) := by
  have az : (L.cin::L.a++L.z).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have wz : (L.cin::L.scratch++L.z).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have wl : (L.cin::L.work++L.low).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.z,CuccaroModLayout.scratch,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have aw : (L.cin::L.a++L.scratch).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have lw : (L.low++L.work).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.z,CuccaroModLayout.scratch,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have mask : (L.high::L.work).Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.z,CuccaroModLayout.scratch,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have flags : [L.workHigh,L.high,L.flag].Nodup := mod_nd L hn _ (by
    intro q
    simp only [CuccaroModLayout.wires,CuccaroModLayout.allWork,
      CuccaroModLayout.z,CuccaroModLayout.scratch,
      List.count_append,List.count_cons,List.count_nil]
    omega)
  have hfh : L.flag≠L.high := by
    have h := List.nodup_cons.mp (List.nodup_cons.mp flags).2
    simpa [ne_comm] using h.1
  have hwh : L.workHigh≠L.high := by
    have h := List.nodup_cons.mp flags
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact h.1.1
  constructor
  · simp only [cuccaroModAdd,properProgram_append]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cuccaroAdd_proper _ _ _ az,
      xorConstant_unitary _ _⟩,cuccaroSub_proper _ _ _ wz⟩,
      xorConstant_unitary _ _⟩,maskedConstant_unitary _ _ _
        (List.nodup_cons.mp mask).1⟩,cuccaroAdd_proper _ _ _ wl⟩,
      maskedConstant_unitary _ _ _ (List.nodup_cons.mp mask).1⟩,
      copyRegister_none_proper _ _ lw⟩,cuccaroSub_proper _ _ _ aw⟩,
      by simpa [ProperProgram,ProperGate] using hwh⟩,
      cuccaroAdd_proper _ _ _ aw⟩,copyRegister_none_proper _ _ lw⟩
  · simp only [cuccaroModSub,properProgram_append]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cuccaroSub_proper _ _ _ az,
      maskedConstant_unitary _ _ _ (List.nodup_cons.mp mask).1⟩,
      cuccaroAdd_proper _ _ _ wl⟩,
      maskedConstant_unitary _ _ _ (List.nodup_cons.mp mask).1⟩,
      by simpa [ProperProgram,ProperGate] using And.intro hfh.symm hfh⟩,
      cuccaroAdd_proper _ _ _ az⟩,xorConstant_unitary _ _⟩,
      cuccaroSub_proper _ _ _ wz⟩,
      by simpa [ProperProgram,ProperGate] using hfh.symm⟩,
      cuccaroAdd_proper _ _ _ wz⟩,xorConstant_unitary _ _⟩,
      cuccaroSub_proper _ _ _ az⟩

theorem cuccaroNormalizedMod_unitary (L : CuccaroNormalizedModLayout)
    (c p : Nat) (hn : L.wires.Nodup) :
    ProperProgram (cuccaroNormalizedModAdd L c p) ∧
    ProperProgram (cuccaroNormalizedModSub L c p) := by
  have nd : L.normalize.wires.Nodup ∧ L.modular.wires.Nodup := by
    constructor <;> apply List.nodup_iff_count.mpr <;> intro q
    all_goals
      have h := List.nodup_iff_count.mp hn q
      simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.normalize,
        CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,CuccaroNormalizeLayout.scratch,
        CuccaroNormalizedModLayout.modular,CuccaroModLayout.wires,CuccaroModLayout.z,
        CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.count_cons,
        List.count_append,List.count_nil] at h ⊢
      omega
  have norm := cuccaroNormalize_proper L.normalize c nd.1
  have clear := properProgram_reverse _ norm
  have mods := cuccaroMod_unitary L.modular p nd.2
  simp only [cuccaroNormalizedModAdd,cuccaroNormalizedModSub,
    cuccaroNormalizeClear,properProgram_append]
  exact ⟨⟨⟨norm,mods.1⟩,clear⟩,⟨⟨norm,mods.2⟩,clear⟩⟩

theorem cuccaroMod_wires_subset (L : CuccaroModLayout) (n p : Nat)
    (hw : L.Widths n) :
    wires (cuccaroModAdd L p)⊆L.wires.toFinset ∧
    wires (cuccaroModSub L p)⊆L.wires.toFinset := by
  have add (a b : List Wire) (h : ∀q,q∈L.cin::a++b → q∈L.wires) :
      wires (cuccaroAdd a b L.cin)⊆L.wires.toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp
      (cuccaroAdd_wires_subset a b L.cin hq)))
  have sub (a b : List Wire) (h : ∀q,q∈L.cin::a++b → q∈L.wires) :
      wires (cuccaroSub a b L.cin)⊆L.wires.toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp
      (cuccaroSub_wires_subset a b L.cin hq)))
  have xor (r : List Wire) (h : ∀q,q∈r → q∈L.wires) :
      wires (xorConstant r p)⊆L.wires.toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp
      (xorConstant_wires_subset r p hq)))
  have mask : wires (maskedConstant L.high L.work p)⊆L.wires.toFinset := by
    intro q hq
    have h := maskedConstant_wires_subset L.high L.work p hq
    simpa only [List.mem_toFinset,CuccaroModLayout.wires,CuccaroModLayout.z,
      CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.mem_cons,
      List.mem_append,List.not_mem_nil,or_false] using
      (show q∈L.wires from by
        simp only [List.mem_toFinset,List.mem_cons] at h
        simp only [CuccaroModLayout.wires,CuccaroModLayout.z,
          CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.mem_cons,
          List.mem_append,List.not_mem_nil,or_false]
        tauto)
  have copy : wires (copyRegister none L.low L.work)⊆L.wires.toFinset := by
    rw [copyRegister_wires _ _ _ (hw.low.trans hw.work.symm)]
    split
    · exact Finset.empty_subset _
    · intro q hq
      simp only [List.mem_toFinset,Option.toList_none,List.nil_append,
        List.mem_append] at hq
      simp only [List.mem_toFinset,CuccaroModLayout.wires,CuccaroModLayout.z,
        CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.mem_cons,
        List.mem_append,List.not_mem_nil,or_false]
      tauto
  constructor
  all_goals
    simp only [cuccaroModAdd,cuccaroModSub,wires_append,Finset.union_subset_iff]
    repeat' constructor
    all_goals first | exact mask | exact copy | apply add | apply sub | apply xor | skip
    all_goals
      intro q hq
      simp only [List.mem_toFinset,CuccaroModLayout.wires,CuccaroModLayout.z,
        CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.mem_cons,
        List.mem_append,List.not_mem_nil,or_false,wires,Instr.wires,
        Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.notMem_empty,or_false] at hq ⊢
      tauto

theorem cuccaroNormalizedMod_wires_subset (L : CuccaroNormalizedModLayout)
    (n c p : Nat) (hw : L.Widths n) :
    wires (cuccaroNormalizedModAdd L c p)⊆L.wires.toFinset ∧
    wires (cuccaroNormalizedModSub L c p)⊆L.wires.toFinset := by
  have norm : wires (cuccaroNormalize L.normalize c)⊆L.wires.toFinset := by
    intro q hq
    have h := cuccaroNormalize_wires_subset L.normalize c hq
    simp only [List.mem_toFinset,CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,CuccaroNormalizeLayout.scratch,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h
    simp only [List.mem_toFinset,CuccaroNormalizedModLayout.wires,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    tauto
  have clear : wires (cuccaroNormalizeClear L.normalize c)⊆L.wires.toFinset := by
    simpa only [cuccaroNormalizeClear,wires_reverse] using norm
  have mods := cuccaroMod_wires_subset L.modular n p (L.modular_widths n hw)
  have embed : L.modular.wires.toFinset⊆L.wires.toFinset := by
    intro q hq
    simp only [List.mem_toFinset,CuccaroNormalizedModLayout.modular,
      CuccaroModLayout.wires,CuccaroModLayout.z,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,List.mem_cons,List.mem_append,List.not_mem_nil,
      or_false] at hq
    simp only [List.mem_toFinset,CuccaroNormalizedModLayout.wires,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    tauto
  simp only [cuccaroNormalizedModAdd,cuccaroNormalizedModSub,wires_append,
    Finset.union_subset_iff]
  exact ⟨⟨⟨norm,mods.1.trans embed⟩,clear⟩,⟨⟨norm,mods.2.trans embed⟩,clear⟩⟩

end ECDSAAdd.Arithmetic
