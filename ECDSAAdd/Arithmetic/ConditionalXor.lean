import ECDSAAdd.Arithmetic.Copy

namespace ECDSAAdd.Arithmetic

/-- 先计算候选，再 XOR 选择候选或原值，最后用同一核清空候选。 -/
def conditionalXor (kernel : Program) (c : Wire) (src temp dst : List Wire) : Program :=
  kernel ++ copyRegister none src dst ++ copyRegister (some c) src dst ++
  copyRegister (some c) temp dst ++ kernel

/-- 两个可变寄存器以外逐线保持初始状态。 -/
def PairFrame (temp dst : List Wire) (base : BasisState) (T O : Nat) (st : BasisState) : Prop :=
  regValue temp st = T ∧ regValue dst st = O ∧
    ∀ w, w ∉ temp → w ∉ dst → st w = base w

namespace PairFrame

theorem read (temp dst r : List Wire) (base st : BasisState) (T O : Nat)
    (h : PairFrame temp dst base T O st) (ht : r.Disjoint temp) (hd : r.Disjoint dst) :
    regValue r st = regValue r base :=
  regValue_congr _ _ _ (fun w hw => h.2.2 w (List.disjoint_left.mp ht hw) (List.disjoint_left.mp hd hw))

theorem update_temp (temp dst : List Wire) (base s t : BasisState) (T O Z : Nat)
    (hd : temp.Disjoint dst) (h : PairFrame temp dst base T O s)
    (he : ∀ w, w ∉ temp → t w = s w) (hz : regValue temp t = Z) :
    PairFrame temp dst base Z O t :=
  ⟨hz, (regValue_congr _ _ _ (fun w hw => he w
    (fun hh => List.disjoint_left.mp hd hh hw))).trans h.2.1,
    fun w ht hd => (he w ht).trans (h.2.2 w ht hd)⟩

theorem update_dst (temp dst : List Wire) (base s t : BasisState) (T O Z : Nat)
    (hd : temp.Disjoint dst) (h : PairFrame temp dst base T O s)
    (he : ∀ w, w ∉ dst → t w = s w) (hz : regValue dst t = Z) :
    PairFrame temp dst base T Z t :=
  ⟨(regValue_congr _ _ _ (fun w hw => he w (List.disjoint_left.mp hd hw))).trans h.1,
    hz, fun w ht hd => (he w hd).trans (h.2.2 w ht hd)⟩

end PairFrame

/-- 条件包装只要求核自身的 XOR 正确性；并不反转包含测量的程序。 -/
theorem conditionalXor_correct (kernel : Program) (c : Wire) (src temp dst work : List Wire)
    (hnd : (c :: (src ++ temp ++ dst ++ work)).Nodup)
    (hs : src.length = dst.length) (ht : temp.length = dst.length)
    (F : Nat → Nat) (q : Nat)
    (hk : ∀ (s : State) (m : List Bool), regValue src s.basis < q → regValue work s.basis = 0 →
      (run kernel m s).phase = s.phase ∧
      (∀ w, w ∉ temp → (run kernel m s).basis w = s.basis w) ∧
      regValue temp (run kernel m s).basis = regValue temp s.basis ^^^ F (regValue src s.basis))
    (s : State) (m : List Bool) (hX : regValue src s.basis < q)
    (hT : regValue temp s.basis = 0) (hW : regValue work s.basis = 0) :
    (run (conditionalXor kernel c src temp dst) m s).phase = s.phase ∧
    (∀ w, w ∉ dst → (run (conditionalXor kernel c src temp dst) m s).basis w = s.basis w) ∧
    regValue dst (run (conditionalXor kernel c src temp dst) m s).basis =
      regValue dst s.basis ^^^ (if s.basis c then F (regValue src s.basis) else regValue src s.basis) := by
  have hcw := (List.nodup_cons.mp hnd).1
  have h1 := List.nodup_append'.mp (List.nodup_cons.mp hnd).2
  have h2 := List.nodup_append'.mp h1.1
  have h3 := List.nodup_append'.mp h2.1
  have hst : src.Disjoint temp := h3.2.2
  have hsd : src.Disjoint dst := List.disjoint_left.mpr (fun _ ha hb =>
    List.disjoint_left.mp h2.2.2 (List.mem_append_left _ ha) hb)
  have htd : temp.Disjoint dst := List.disjoint_left.mpr (fun _ ha hb =>
    List.disjoint_left.mp h2.2.2 (List.mem_append_right _ ha) hb)
  have hwt : work.Disjoint temp := List.disjoint_left.mpr (fun _ ha hb =>
    List.disjoint_left.mp h1.2.2 (by simp [hb]) ha)
  have hwd : work.Disjoint dst := List.disjoint_left.mpr (fun _ ha hb =>
    List.disjoint_left.mp h1.2.2 (by simp [hb]) ha)
  have hct : c ∉ temp := fun hh => hcw (by simp [hh])
  have hcd : c ∉ dst := fun hh => hcw (by simp [hh])
  let X := regValue src s.basis
  let O := regValue dst s.basis
  let C := s.basis c
  let V := F X
  let P := PairFrame temp dst s.basis
  have kstep (T B : Nat) : Triple (P T B) kernel (P (T ^^^ V) B) := by
    intro st ms h
    have hx := PairFrame.read temp dst src s.basis st.basis T B h hst hsd
    have hw := PairFrame.read temp dst work s.basis st.basis T B h hwt hwd
    obtain ⟨hp, he, hz⟩ := hk st ms (by simpa [hx] using hX) (hw.trans hW)
    exact ⟨hp, PairFrame.update_temp temp dst _ _ _ T B _ htd h he (by simpa [hx, h.1, V, X] using hz)⟩
  have source (ctrl : Option Wire) (T B : Nat) (hc : ctrl = none ∨ ctrl = some c) :
      Triple (P T B) (copyRegister ctrl src dst)
        (P T (B ^^^ (if ctrl.isSome then (if C then X else 0) else X))) := by
    intro st ms h
    have hx := PairFrame.read temp dst src s.basis st.basis T B h hst hsd
    obtain ⟨hp, he, hz⟩ := copyRegister_correct ctrl src dst hs
      (List.nodup_append'.mpr ⟨h3.1,h2.2.1,hsd⟩) (by rcases hc with rfl|rfl; simp; simpa using hcd) st ms
    refine ⟨hp, PairFrame.update_dst temp dst _ _ _ T B _ htd h he ?_⟩
    have hcc := h.2.2 c hct hcd
    rcases hc with rfl|rfl <;> simpa [copyValue,hx,h.2.1,hcc,C,X] using hz
  have candidate (T B : Nat) : Triple (P T B) (copyRegister (some c) temp dst)
      (P T (B ^^^ (if C then T else 0))) := by
    intro st ms h
    obtain ⟨hp, he, hz⟩ := copyRegister_correct (some c) temp dst ht
      (List.nodup_append'.mpr ⟨h3.2.1,h2.2.1,htd⟩) (by simpa using hcd) st ms
    refine ⟨hp, PairFrame.update_dst temp dst _ _ _ T B _ htd h he ?_⟩
    simpa [copyValue,h.1,h.2.1,h.2.2 c hct hcd,C] using hz
  have first : Triple (P 0 O) kernel (P V O) := by simpa using kstep 0 O
  have h := first.seq ((source none V O (Or.inl rfl)).seq
    ((source (some c) V (O ^^^ X) (Or.inr rfl)).seq
    ((candidate V ((O ^^^ X) ^^^ (if C then X else 0))).seq
      (kstep V (((O ^^^ X) ^^^ (if C then X else 0)) ^^^ (if C then V else 0))))))
  have hspec : Triple (P 0 O) (conditionalXor kernel c src temp dst)
      (P 0 (O ^^^ (if C then V else X))) := by
    cases hcval : C <;> simpa [conditionalXor,List.append_assoc,Nat.xor_assoc,hcval] using h
  obtain ⟨hp,hf⟩ := hspec s m ⟨hT,rfl,fun _ _ _ => rfl⟩
  refine ⟨hp, ?_, hf.2.1⟩
  intro w hw
  by_cases hm : w ∈ temp
  · exact ((regValue_zero _ _).mp hf.1 w hm).trans ((regValue_zero _ _).mp hT w hm).symm
  · exact hf.2.2 w hm hw

theorem conditionalXor_counts (kernel : Program) (c : Wire) (src temp dst : List Wire)
    (hs : src.length = dst.length) (ht : temp.length = dst.length) :
    toffoliCount (conditionalXor kernel c src temp dst) = 2*toffoliCount kernel + 2*dst.length ∧
    measurementCount (conditionalXor kernel c src temp dst) = 2*measurementCount kernel := by
  have h0 := copyRegister_counts none src dst hs
  have h1 := copyRegister_counts (some c) src dst hs
  have h2 := copyRegister_counts (some c) temp dst ht
  simp only [conditionalXor,toffoliCount_append,measurementCount_append,h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,
    Option.isSome_none,Option.isSome_some,Bool.false_eq_true,if_false,if_true]
  omega

theorem conditionalXor_wires (kernel : Program) (c : Wire) (src temp dst : List Wire)
    (hs : src.length = dst.length) (ht : temp.length = dst.length) (hn : dst ≠ []) :
    wires (conditionalXor kernel c src temp dst) =
      wires kernel ∪ (c :: (src ++ temp ++ dst)).toFinset := by
  have hsn : src.isEmpty = false := by cases src <;> cases dst <;> simp_all
  have htn : temp.isEmpty = false := by cases temp <;> cases dst <;> simp_all
  have h0 := copyRegister_wires none src dst hs
  have h1 := copyRegister_wires (some c) src dst hs
  have h2 := copyRegister_wires (some c) temp dst ht
  simp only [conditionalXor,wires_append,h0,h1,h2,hsn,htn,Bool.false_eq_true,if_false,
    Option.toList_none,Option.toList_some,List.nil_append]
  ext w
  simp [or_left_comm,or_comm]

end ECDSAAdd.Arithmetic
