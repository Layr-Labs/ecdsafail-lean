import ECDSAAdd.Arithmetic.Registers

namespace ECDSAAdd.Arithmetic

/-- 每个被检测的输入位配一根可复用的零工作位。 -/
structure ZeroBit where
  input : Wire
  work : Wire

def ZeroBit.wires (b : ZeroBit) : List Wire := [b.input,b.work]

private def negAnd (c a t : Wire) : Program := [.X a, .CCX c a t, .X a]

private def negAndErase (c a t : Wire) : Program :=
  [.X a, .measureX t [] [.CZ c a], .X a]

/-- XOR 写入“控制为真且整段为零”；测量清理AND链并修正相位。 -/
def zeroControlled (c target : Wire) : List ZeroBit → Program
  | [] => [.CX c target]
  | b::bs => negAnd c b.input b.work ++ zeroControlled b.work target bs ++ negAndErase c b.input b.work

private theorem negAnd_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (s : State) (m : List Bool) :
    run (negAnd c a t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && !s.basis a))⟩ := by
  simp only [negAnd, run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=a
  · subst w; simp [writeBit, hca, hat]
  · by_cases ht : w=t
    · subst w; simp [writeBit, hca, Ne.symm hat]
    · simp [writeBit, hw, ht, hca]

private theorem negAndErase_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (hct : c≠t) (s : State) (m : List Bool)
    (hq : s.basis t = (s.basis c && !s.basis a)) :
    run (negAndErase c a t) m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  simp only [negAndErase, run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect, correct, writeBit, hca, hat, hat.symm, hct, hq]
  all_goals
    funext w
    by_cases hw : w=a
    · subst w; simp [hat]
    · simp [Function.update_apply, hw]

theorem zeroControlled_counts (c target : Wire) (bs : List ZeroBit) :
    toffoliCount (zeroControlled c target bs) = bs.length ∧
    measurementCount (zeroControlled c target bs) = bs.length := by
  induction bs generalizing c with
  | nil => simp [zeroControlled, toffoliCount, measurementCount]
  | cons b bs ih =>
    simp [zeroControlled, negAnd, negAndErase, toffoliCount_append, measurementCount_append,
      toffoliCount, measurementCount, ih]; omega

/-- 完整状态公式：只有目标翻转，包含所有借用工作位和控制位的恢复。 -/
theorem zeroControlled_correct (c target : Wire) (bs : List ZeroBit)
    (hnd : (c::target::bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (hz : ∀ b∈bs, s.basis b.work=false) :
    run (zeroControlled c target bs) m s =
      ⟨s.phase, writeBit s.basis target
        (s.basis target ^^ (s.basis c && bs.all (fun b => !s.basis b.input)))⟩ := by
  induction bs generalizing c s m with
  | nil => simp [zeroControlled, run]
  | cons b bs ih =>
    have hnames : (c::target::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hnd
    have hni := hnames
    simp only [List.nodup_cons, List.mem_cons, not_or] at hni
    have hca : c≠b.input := hni.1.2.1
    have hai : b.input≠b.work := hni.2.2.1.1
    have hta : target≠b.input := hni.2.1.1
    have htw : target≠b.work := hni.2.1.2.1
    have hcw : c≠b.work := hni.1.2.2.1
    have hchild : (b.work::target::bs.flatMap ZeroBit.wires).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨htw.symm,hni.2.2.2.1⟩,hni.2.1.2.2,hni.2.2.2.2⟩
    let q := s.basis c && !s.basis b.input
    let t : State := ⟨s.phase, writeBit s.basis b.work q⟩
    have hp : run (negAnd c b.input b.work) m s=t := by
      rw [negAnd_run c b.input b.work hca hai]
      simp [t, q, hz b (by simp), writeBit]
    have htail (d : ZeroBit) (hd : d∈bs) : d.work≠b.work ∧ d.input≠b.work := by
      have hh := hni.2.2.2.1
      constructor <;> intro he <;> apply hh <;>
        apply List.mem_flatMap.mpr <;> refine ⟨d,hd,?_⟩ <;> simp [ZeroBit.wires, he]
    have hz' : ∀ d∈bs, t.basis d.work=false := by
      intro d hd
      simpa [t, writeBit, (htail d hd).1] using hz d (by simp [hd])
    have hall : bs.all (fun d => !t.basis d.input) = bs.all (fun d => !s.basis d.input) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor <;> intro h d hd <;> simpa [t, writeBit, (htail d hd).2] using h d hd
    change run (negAnd c b.input b.work ++ zeroControlled b.work target bs ++ negAndErase c b.input b.work) m s = _
    rw [run_append, run_take, run_append, run_take]
    simp only [measurementCount_append, (zeroControlled_counts b.work target bs).2,
      show measurementCount (negAnd c b.input b.work)=0 from rfl, Nat.zero_add, List.drop_zero]
    rw [hp, ih b.work hchild t m hz']
    rw [negAndErase_run c b.input b.work hca hai hcw _ _ (by
      simp [t, writeBit, htw.symm, hcw, hai, hni.1.1, hta.symm, q])]
    simp only [hall, t, List.all_cons]
    apply congrArg (State.mk s.phase)
    funext w
    by_cases ht : w=target
    · subst w
      simp [writeBit, htw, q, Bool.and_assoc]
    · by_cases hw : w=b.work
      · subst w
        simp [writeBit, ht, hz b (by simp)]
      · simp [writeBit, ht, hw]

/-- 输入为零时才按 c 翻转 target，输入和全部工作位保持。 -/
theorem zeroControlled_spec (c target : Wire) (bs : List ZeroBit)
    (hnd : (c::target::bs.flatMap ZeroBit.wires).Nodup) (C T : Bool) (X : Nat) :
    {{ c=C, target=T, (bs.map ZeroBit.input)=X, (bs.map ZeroBit.work)=0 }}
      zeroControlled c target bs
    {{ c=C, target=(T ^^ (C && decide (X=0))),
       (bs.map ZeroBit.input)=X, (bs.map ZeroBit.work)=0 }} := by
  intro s m h
  have hz : ∀ b∈bs, s.basis b.work=false := by
    intro b hb
    exact (regValue_zero _ _).mp h.2 b.work (List.mem_map.mpr ⟨b,hb,rfl⟩)
  have hall : bs.all (fun b => !s.basis b.input) = decide (X=0) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, ← show regValue (bs.map ZeroBit.input) s.basis=X from h.1.2,
      regValue_zero]
    simp [List.all_eq_true]
  have hn := List.nodup_cons.mp hnd
  have ht := (List.nodup_cons.mp hn.2).1
  have hct : c≠target := fun he => hn.1 (by simp [he])
  have hi (b : ZeroBit) (hb : b∈bs) : b.input≠target := by
    intro he
    exact ht (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires, he]⟩)
  have hw (b : ZeroBit) (hb : b∈bs) : b.work≠target := by
    intro he
    exact ht (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires, he]⟩)
  rw [zeroControlled_correct c target bs hnd s m hz]
  refine ⟨rfl, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simpa [Holds.holds, writeBit, hct] using h.1.1.1
  · simp [Holds.holds, writeBit, hall, show s.basis c=C from h.1.1.1,
      show s.basis target=T from h.1.1.2]
  · apply Eq.trans (regValue_congr _ _ _ ?_) h.1.2
    intro w hm
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
    simp [writeBit, hi b hb]
  · apply Eq.trans (regValue_congr _ _ _ ?_) h.2
    intro w hm
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
    simp [writeBit, hw b hb]

theorem zeroControlled_wires (c target : Wire) (bs : List ZeroBit) :
    wires (zeroControlled c target bs) = (c::target::bs.flatMap ZeroBit.wires).toFinset := by
  induction bs generalizing c with
  | nil => simp [zeroControlled, wires, Instr.wires]
  | cons b bs ih =>
    rw [zeroControlled, wires_append, wires_append, ih]
    ext w
    simp [negAnd, negAndErase, wires, Instr.wires, correctionWires, ZeroBit.wires, or_comm, or_left_comm]

theorem zeroControlled_resources (c target : Wire) (bs : List ZeroBit)
    (hnd : (c::target::bs.flatMap ZeroBit.wires).Nodup) :
    toffoliCount (zeroControlled c target bs) = bs.length ∧
    measurementCount (zeroControlled c target bs) = bs.length ∧
    qubitCount (zeroControlled c target bs) = 2*bs.length+2 := by
  refine ⟨(zeroControlled_counts c target bs).1, (zeroControlled_counts c target bs).2, ?_⟩
  rw [qubitCount, zeroControlled_wires, List.toFinset_card_of_nodup hnd]
  have hh : (bs.flatMap ZeroBit.wires).length = 2*bs.length := by
    clear hnd
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp only [ZeroBit.wires, List.length_cons, List.length_nil]
      omega
  simp [hh]

end ECDSAAdd.Arithmetic
