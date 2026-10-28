import ECDSAAdd.Arithmetic.MontStageSpec
import ECDSAAdd.Arithmetic.MontCounts
import ECDSAAdd.Arithmetic.MontWires
import ECDSAAdd.Math.InverseScaleFactor

namespace ECDSAAdd.Arithmetic

/-- 一次计数缩放的实际寄存器视图；不拥有额外分配。 -/
structure InverseScaleLayout where
  a : List Wire
  k : List Wire
  factor : List Wire
  stage : MontStageLayout
  extraScratch : List Wire

namespace InverseScaleLayout

def scratch (L : InverseScaleLayout) : List Wire := L.stage.scratch++L.extraScratch
def work (L : InverseScaleLayout) : List Wire :=
  L.factor++L.stage.work++L.extraScratch
def live (L : InverseScaleLayout) : List Wire := L.stage.acc++L.stage.history++[L.stage.flag]
def wires (L : InverseScaleLayout) : List Wire := L.a++L.k++L.live++L.work

structure Widths (L : InverseScaleLayout) : Prop where
  a : L.a.length=257
  k : L.k.length=10
  factor : L.factor.length=257
  stage : L.stage.Widths
  extraScratch : L.extraScratch.length=6

def lookup (L : InverseScaleLayout) (q : Nat) : Program :=
  Arithmetic.lookup (L.k.headD L.stage.flag) L.k.tail L.scratch L.factor (inverseScaleFactor q)

/-- 三次无控制CX复制交换a与累加器低257位；高4位保持。 -/
def exchange (L : InverseScaleLayout) : Program :=
  copyRegister none L.a (L.stage.acc.take 257) ++
  copyRegister none (L.stage.acc.take 257) L.a ++
  copyRegister none L.a (L.stage.acc.take 257)

def prepare (L : InverseScaleLayout) (q : Nat) : Program :=
  L.lookup q ++ montPrepare L.stage L.factor (L.a.take 256) q ++ L.exchange ++ L.lookup q

def restore (L : InverseScaleLayout) (q : Nat) : Program :=
  L.lookup q ++ L.exchange ++ montRestore L.stage L.factor (L.a.take 256) q ++ L.lookup q

/-- 使用逆元期间仅保留N、Montgomery商和借位，所有借用工作区为空。 -/
def Prepared (L : InverseScaleLayout) (q K N : Nat) (s : BasisState) : Prop :=
  regValue L.k s=K ∧
  regValue L.a s=montgomeryValue q (inverseScaleFactor q K) N 64%q ∧
  regValue L.stage.acc s=N ∧
  regValue L.stage.history s=montgomeryQuotient q (inverseScaleFactor q K) N 64 ∧
  s L.stage.flag=decide (montgomeryValue q (inverseScaleFactor q K) N 64<q) ∧
  regValue L.work s=0

/-- 每个门列边界的寄存器值；最后的零断言不包含factor。 -/
private def Values (L : InverseScaleLayout) (A K Z H C : Nat) (F : Bool) (s : BasisState) : Prop :=
  regValue L.a s=A ∧ regValue L.k s=K ∧ regValue L.stage.acc s=Z ∧
  regValue L.stage.history s=H ∧ s L.stage.flag=F ∧ regValue L.factor s=C ∧
  regValue (L.stage.work++L.extraScratch) s=0

private theorem reordered (L : InverseScaleLayout) (hn : L.wires.Nodup) :
    ((L.a++L.k++L.live++L.stage.work++L.extraScratch)++L.factor).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  simp only [wires,work,List.count_append] at h ⊢
  omega

private theorem lookup_nodup (L : InverseScaleLayout) (hn : L.wires.Nodup) :
    (L.k++L.scratch++L.factor).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  simp only [wires,work,live,scratch,MontStageLayout.work,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

private theorem stage_nodup (L : InverseScaleLayout) (hn : L.wires.Nodup) :
    (L.factor++L.a.take 256++L.stage.wires).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  have ht := (List.take_sublist 256 L.a).count_le w
  simp only [wires,work,live,MontStageLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

private theorem lookup_step (L : InverseScaleLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Nat) (hq : 0<q) (hb : q<2^256) (A K Z H C : Nat) (F : Bool) :
    Triple (Values L A K Z H C F) (L.lookup q)
      (Values L A K Z H (C ^^^ inverseScaleFactor q K) F) := by
  intro s m h
  have hk : L.k≠[] := by intro e; simpa [e] using hw.k
  have he : L.k.headD L.stage.flag :: L.k.tail=L.k := by
    cases hh : L.k with
    | nil => exact False.elim (hk hh)
    | cons a bs => rfl
  have hnd : (L.k.headD L.stage.flag :: (L.k.tail++L.scratch++L.factor)).Nodup := by
    simpa only [←List.cons_append,he] using L.lookup_nodup hn
  have hz : ∀ w∈L.scratch,s.basis w=false := by
    intro w hw'
    apply (regValue_zero _ _).mp h.2.2.2.2.2.2 w
    simp only [scratch,MontStageLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw' ⊢
    tauto
  have hp := lookup10_correct (L.k.headD L.stage.flag) L.k.tail L.scratch L.factor (inverseScaleFactor q)
    hnd (by simp [hw.k]) (by simp [scratch,hw.stage.scratch,hw.extraScratch])
    (by intro j hj; exact (inverseScaleFactor_bound q j hq).trans (by rw [hw.factor]; omega)) s m hz
  change (run (L.lookup q) m s).phase=_ ∧ _ at hp
  have dis := (List.nodup_append'.mp (L.reordered hn)).2.2
  have keep (r : List Wire) (hr : r ⊆ L.a++L.k++L.live++L.stage.work++L.extraScratch) :
      regValue r (run (L.lookup q) m s).basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw' => hp.2.1 w (List.disjoint_left.mp dis (hr hw')))
  refine ⟨hp.1,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by intro w hw'; simp [hw'])).trans h.1
  · exact (keep _ (by intro w hw'; simp [hw'])).trans h.2.1
  · exact (keep _ (by intro w hw'; simp [live,hw'])).trans h.2.2.1
  · exact (keep _ (by intro w hw'; simp [live,hw'])).trans h.2.2.2.1
  · exact (hp.2.1 _ (List.disjoint_left.mp dis (by simp [live]))).trans h.2.2.2.2.1
  · simpa only [he,h.2.1,h.2.2.2.2.2.1] using hp.2.2
  · exact (keep (L.stage.work++L.extraScratch) (by
      intro w hw'
      rcases List.mem_append.mp hw' with hh|hh
      · exact List.mem_append_left _ (List.mem_append_right _ hh)
      · exact List.mem_append_right _ hh)).trans h.2.2.2.2.2.2

private theorem exchange_lists (a b : List Wire) (hlen : a.length=b.length)
    (hnd : (a++b).Nodup) (s : State) (m : List Bool) :
    let p := copyRegister none a b ++ copyRegister none b a ++ copyRegister none a b
    (run p m s).phase=s.phase ∧
    (∀ w,w∉a → w∉b → (run p m s).basis w=s.basis w) ∧
    regValue a (run p m s).basis=regValue b s.basis ∧
    regValue b (run p m s).basis=regValue a s.basis := by
  have hba : (b++a).Nodup := by simpa only [List.nodup_append_comm] using hnd
  have dis := (List.nodup_append'.mp hnd).2.2
  let p := copyRegister none a b
  let r := copyRegister none b a
  let t := run p m s
  let u := run r m t
  have hp := copyRegister_correct none a b hlen hnd (by simp) s m
  have hr := copyRegister_correct none b a hlen.symm hba (by simp) t m
  have hq := copyRegister_correct none a b hlen hnd (by simp) u m
  have ht : regValue a t.basis=regValue a s.basis :=
    regValue_congr _ _ _ (fun w hw => hp.2.1 w (List.disjoint_left.mp dis hw))
  have hu : regValue b u.basis=regValue b t.basis :=
    regValue_congr _ _ _ (fun w hw => hr.2.1 w (List.disjoint_left.mp dis.symm hw))
  have hf : regValue a (run p m u).basis=regValue a u.basis :=
    regValue_congr _ _ _ (fun w hw => hq.2.1 w (List.disjoint_left.mp dis hw))
  have hc := copyRegister_counts none a b hlen
  have hc' := copyRegister_counts none b a hlen.symm
  dsimp only
  simp only [List.append_assoc,run_append,run_take]
  simp only [hc.2,hc'.2,List.drop_zero]
  change (run p m u).phase=s.phase ∧ _
  refine ⟨hq.1.trans (hr.1.trans hp.1),?_,?_,?_⟩
  · intro w ha hb; exact (hq.2.1 w hb).trans ((hr.2.1 w ha).trans (hp.2.1 w hb))
  · rw [hf,hr.2.2,ht,hp.2.2]
    simp [copyValue,←Nat.xor_assoc,Nat.xor_right_comm]
  · rw [hq.2.2,hr.2.2,hu,ht,hp.2.2]
    simp [copyValue,Nat.xor_left_comm]

private theorem low_value (r : List Wire) (n V : Nat) (s : BasisState)
    (hn : n≤r.length) (hv : regValue r s=V) (hV : V<2^n) :
    regValue (r.take n) s=V ∧ regValue (r.drop n) s=0 := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,hv,List.length_take,Nat.min_eq_left hn] at h
  have hz : regValue (r.drop n) s=0 := by
    have hp := Nat.two_pow_pos n
    by_contra hh
    have : 1≤regValue (r.drop n) s := by omega
    nlinarith
  exact ⟨by simpa only [hz,mul_zero,add_zero] using h.symm,hz⟩

private theorem exchange_step (L : InverseScaleLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (A K Z H C : Nat) (F : Bool) (hZ : Z<2^257) :
    Triple (Values L A K Z H C F) L.exchange (Values L Z K A H C F) := by
  intro s m h
  have hnd : (L.a++L.stage.acc).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [wires,work,live,List.count_append,List.count_cons,List.count_nil] at hh ⊢
    omega
  have hp := exchange_lists L.a (L.stage.acc.take 257) (by simp [hw.a,hw.stage.acc])
    ((List.Sublist.refl L.a).append (List.take_sublist 257 L.stage.acc) |>.nodup hnd) s m
  have hz := low_value L.stage.acc 257 Z s.basis (by rw [hw.stage.acc]; omega) h.2.2.1 hZ
  have ndsplit : (L.stage.acc.take 257++L.stage.acc.drop 257).Nodup := by
    simpa only [List.take_append_drop] using (List.nodup_append'.mp hnd).2.1
  have split := List.nodup_append'.mp ndsplit
  have disA := (List.nodup_append'.mp hnd).2.2
  have dis : (L.k++L.stage.history++[L.stage.flag]++L.factor++L.stage.work++L.extraScratch).Disjoint
      (L.a++L.stage.acc) := by
    apply List.disjoint_left.mpr; intro w hm hx
    have hh := List.nodup_iff_count.mp hn w
    have h1 := List.count_pos_iff.mpr hm
    have h2 := List.count_pos_iff.mpr hx
    simp only [wires,work,live,List.count_append,List.count_cons,List.count_nil] at hh h1 h2
    omega
  have keep (r : List Wire) (hr : r ⊆ L.k++L.stage.history++[L.stage.flag]++L.factor++L.stage.work++L.extraScratch) :
      regValue r (run L.exchange m s).basis=regValue r s.basis := by
    apply regValue_congr; intro w hw'
    have hh := List.disjoint_left.mp dis (hr hw')
    exact hp.2.1 w (fun hx => hh (List.mem_append_left _ hx))
      (fun hx => hh (List.mem_append_right _ ((List.take_sublist 257 L.stage.acc).subset hx)))
  have high : regValue (L.stage.acc.drop 257) (run L.exchange m s).basis=0 := by
    rw [←hz.2]; apply regValue_congr; intro w hw'
    exact hp.2.1 w (List.disjoint_left.mp disA.symm ((List.drop_sublist 257 L.stage.acc).subset hw'))
      (List.disjoint_left.mp split.2.2.symm hw')
  refine ⟨hp.1,hp.2.2.1.trans hz.1,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by intro w hw'; simp [hw'])).trans h.2.1
  · rw [←List.take_append_drop 257 L.stage.acc,regValue_append,high,mul_zero,add_zero]
    exact hp.2.2.2.trans h.1
  · exact (keep _ (by intro w hw'; simp [hw'])).trans h.2.2.2.1
  · have hh := List.disjoint_left.mp dis (by simp : L.stage.flag∈L.k++L.stage.history++[L.stage.flag]++L.factor++L.stage.work++L.extraScratch)
    exact (hp.2.1 _ (by intro hx; exact hh (by simp [hx]))
      (by intro hx; exact hh (List.mem_append_right _ ((List.take_sublist 257 L.stage.acc).subset hx)))).trans h.2.2.2.2.1
  · exact (keep _ (by intro w hw'; simp [hw'])).trans h.2.2.2.2.2.1
  · exact (keep (L.stage.work++L.extraScratch) (by
      intro w hw'
      rcases List.mem_append.mp hw' with hh|hh
      · exact List.mem_append_left _ (List.mem_append_right _ hh)
      · exact List.mem_append_right _ hh)).trans h.2.2.2.2.2.2

private theorem stage_keep (L : InverseScaleLayout) (hn : L.wires.Nodup) (s t : BasisState)
    (hf : ∀ w,w∉L.stage.acc → w∉L.stage.history → w≠L.stage.flag → t w=s w)
    (r : List Wire) (hr : r ⊆ L.a++L.k++L.factor++L.stage.work++L.extraScratch) :
    regValue r t=regValue r s := by
  have dis : (L.a++L.k++L.factor++L.stage.work++L.extraScratch).Disjoint L.live := by
    apply List.disjoint_left.mpr; intro w hm hx
    have hh := List.nodup_iff_count.mp hn w
    have h1 := List.count_pos_iff.mpr hm
    have h2 := List.count_pos_iff.mpr hx
    simp only [wires,work,List.count_append] at hh h1 h2
    omega
  apply regValue_congr; intro w hw'
  have hh := List.disjoint_left.mp dis (hr hw')
  apply hf w
  · intro h; exact hh (by simp [live,h])
  · intro h; exact hh (by simp [live,h])
  · intro h; exact hh (by simp [live,h])

private theorem mont_prepare_step (L : InverseScaleLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Nat) (hq : q%16=15) (hb : q<2^256) (N K C : Nat) (hN : N<q) (hC : C<q) :
    Triple (Values L N K 0 0 C false) (montPrepare L.stage L.factor (L.a.take 256) q)
      (Values L N K (montgomeryValue q C N 64%q) (montgomeryQuotient q C N 64) C
        (decide (montgomeryValue q C N 64<q))) := by
  intro s m h
  have ha := (low_value L.a 256 N s.basis (by rw [hw.a]; omega) h.1 (hN.trans hb)).1
  have hz : regValue L.stage.work s.basis=0 :=
    (regValue_zero _ _).mpr (fun w hw' => (regValue_zero _ _).mp h.2.2.2.2.2.2 w (List.mem_append_left _ hw'))
  have hp := montPrepare_correct L.stage L.factor (L.a.take 256) q C N hw.stage (L.stage_nodup hn)
    (by simp [hw.factor]) (by simp [hw.a]) hb hq hC s m h.2.2.2.2.2.1 ha
    h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hz
  generalize ht : run (montPrepare L.stage L.factor (L.a.take 256) q) m s=t at hp ⊢
  have keep := L.stage_keep hn _ _ hp.2.1
  refine ⟨hp.1,?_,?_,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2,?_,?_⟩
  · exact (keep _ (by intro w hw'; simp [hw'])).trans h.1
  · exact (keep _ (by intro w hw'; simp [hw'])).trans h.2.1
  · exact (keep _ (by intro w hw'; simp [hw'])).trans h.2.2.2.2.2.1
  · exact (keep (L.stage.work++L.extraScratch) (by
      intro w hw'
      rcases List.mem_append.mp hw' with hh|hh
      · exact List.mem_append_left _ (List.mem_append_right _ hh)
      · exact List.mem_append_right _ hh)).trans h.2.2.2.2.2.2

private theorem mont_restore_step (L : InverseScaleLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Nat) (hq : q%16=15) (hb : q<2^256) (N K C : Nat) (hN : N<q) (hC : C<q) :
    Triple (Values L N K (montgomeryValue q C N 64%q) (montgomeryQuotient q C N 64) C
        (decide (montgomeryValue q C N 64<q)))
      (montRestore L.stage L.factor (L.a.take 256) q) (Values L N K 0 0 C false) := by
  intro s m h
  have ha := (low_value L.a 256 N s.basis (by rw [hw.a]; omega) h.1 (hN.trans hb)).1
  have hz : regValue L.stage.work s.basis=0 :=
    (regValue_zero _ _).mpr (fun w hw' => (regValue_zero _ _).mp h.2.2.2.2.2.2 w (List.mem_append_left _ hw'))
  have hp := montRestore_correct L.stage L.factor (L.a.take 256) q C N hw.stage (L.stage_nodup hn)
    (by simp [hw.factor]) (by simp [hw.a]) hb hq hC s m h.2.2.2.2.2.1 ha
    h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hz
  generalize ht : run (montRestore L.stage L.factor (L.a.take 256) q) m s=t at hp ⊢
  have keep := L.stage_keep hn _ _ hp.2.1
  refine ⟨hp.1,?_,?_,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2,?_,?_⟩
  · exact (keep _ (by intro w hw'; simp [hw'])).trans h.1
  · exact (keep _ (by intro w hw'; simp [hw'])).trans h.2.1
  · exact (keep _ (by intro w hw'; simp [hw'])).trans h.2.2.2.2.2.1
  · exact (keep (L.stage.work++L.extraScratch) (by
      intro w hw'
      rcases List.mem_append.mp hw' with hh|hh
      · exact List.mem_append_left _ (List.mem_append_right _ hh)
      · exact List.mem_append_right _ hh)).trans h.2.2.2.2.2.2

private theorem prepared_iff (L : InverseScaleLayout) (q K N : Nat) (s : BasisState) :
    L.Prepared q K N s ↔ Values L (montgomeryValue q (inverseScaleFactor q K) N 64%q)
      K N (montgomeryQuotient q (inverseScaleFactor q K) N 64) 0
      (decide (montgomeryValue q (inverseScaleFactor q K) N 64<q)) s := by
  simp only [Prepared,Values,work,regValue_zero,List.mem_append,or_imp,forall_and]
  tauto

/-- 初始a=N，结果a为标准表示的N·2^{-K}；只保留显式历史，借用区全零。 -/
theorem prepare_spec (L : InverseScaleLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Nat) (hq : q%16=15) (hb : q<2^256) (N K : Nat) (hN : N<q) :
    {{ L.a=N,L.k=K,L.live=0,L.work=0 }} L.prepare q
    {{ L.Prepared q K N st }} := by
  have hq0 : 0<q := by omega
  let C := inverseScaleFactor q K
  let M := montgomeryValue q C N 64%q
  let H := montgomeryQuotient q C N 64
  let F := decide (montgomeryValue q C N 64<q)
  have h1 : Triple (Values L N K 0 0 0 false) (L.lookup q) (Values L N K 0 0 C false) := by
    simpa only [Nat.zero_xor] using L.lookup_step hw hn q hq0 hb N K 0 0 0 false
  have h2 := L.mont_prepare_step hw hn q hq hb N K C hN (inverseScaleFactor_bound q K hq0)
  have h3 := L.exchange_step hw hn N K M H C F (lt_trans (Nat.mod_lt _ hq0) (by omega : q<2^257))
  have h4 : Triple (Values L M K N H C F) (L.lookup q) (Values L M K N H 0 F) := by
    simpa only [C,Nat.xor_self] using L.lookup_step hw hn q hq0 hb M K N H C F
  have hp := ((h1.seq h2).seq h3).seq h4
  apply Triple.conseq ?_ hp ?_
  · intro s h
    simp only [Holds.holds,Values,live,work,regValue_zero,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_imp,forall_and,forall_eq] at h ⊢
    tauto
  · intro s h; exact (L.prepared_iff q K N s).mpr h

/-- 使用段保持Prepared后，同一前向恢复门列还原N并清全部历史。 -/
theorem restore_spec (L : InverseScaleLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Nat) (hq : q%16=15) (hb : q<2^256) (N K : Nat) (hN : N<q) :
    {{ L.Prepared q K N st }} L.restore q
    {{ L.a=N,L.k=K,L.live=0,L.work=0 }} := by
  have hq0 : 0<q := by omega
  let C := inverseScaleFactor q K
  let M := montgomeryValue q C N 64%q
  let H := montgomeryQuotient q C N 64
  let F := decide (montgomeryValue q C N 64<q)
  have h1 : Triple (Values L M K N H 0 F) (L.lookup q) (Values L M K N H C F) := by
    simpa only [Nat.zero_xor] using L.lookup_step hw hn q hq0 hb M K N H 0 F
  have h2 := L.exchange_step hw hn M K N H C F (lt_trans hN (by omega : q<2^257))
  have h3 := L.mont_restore_step hw hn q hq hb N K C hN (inverseScaleFactor_bound q K hq0)
  have h4 : Triple (Values L N K 0 0 C false) (L.lookup q) (Values L N K 0 0 0 false) := by
    simpa only [C,Nat.xor_self] using L.lookup_step hw hn q hq0 hb N K 0 0 C false
  have hp := ((h1.seq h2).seq h3).seq h4
  apply Triple.conseq ?_ hp ?_
  · intro s h; exact (L.prepared_iff q K N s).mp h
  · intro s h
    simp only [Holds.holds,Values,live,work,regValue_zero,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_imp,forall_and,forall_eq] at h ⊢
    tauto

private theorem lookup_subset (L : InverseScaleLayout) (hw : L.Widths) (q : Nat) :
    ECDSAAdd.wires (L.lookup q) ⊆ L.wires.toFinset := by
  have hk : L.k≠[] := by intro e; simpa [e] using hw.k
  have he : L.k.headD L.stage.flag :: L.k.tail=L.k := by
    cases hh : L.k with
    | nil => exact False.elim (hk hh)
    | cons a bs => rfl
  intro w hm
  have h := lookup_wires_subset (L.k.headD L.stage.flag) L.k.tail L.scratch L.factor (inverseScaleFactor q) hm
  simp only [he,List.mem_toFinset,List.mem_append,scratch] at h
  simp only [wires,work,MontStageLayout.work,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil]
  tauto

private theorem stage_subset (L : InverseScaleLayout) :
    (L.factor.take 256++(L.a.take 256).take 256++L.stage.wires).toFinset ⊆ L.wires.toFinset := by
  intro w hw
  simp only [List.mem_toFinset,List.mem_append] at hw
  have hF := (List.take_sublist 256 L.factor).subset
  have hA := (List.take_sublist 256 L.a).subset
  have hAA := (List.take_sublist 256 (L.a.take 256)).subset
  rcases hw with (hf|ha)|hs
  · simp [wires,work,hF hf]
  · simp [wires,hA (hAA ha)]
  · simp only [MontStageLayout.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hs
    simp only [wires,work,live,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto

private theorem exchange_subset (L : InverseScaleLayout) (hw : L.Widths) :
    ECDSAAdd.wires L.exchange ⊆ L.wires.toFinset := by
  have hlen : L.a.length=(L.stage.acc.take 257).length := by simp [hw.a,hw.stage.acc]
  have h1 := copyRegister_wires none L.a (L.stage.acc.take 257) hlen
  have h2 := copyRegister_wires none (L.stage.acc.take 257) L.a hlen.symm
  have ha : L.a.isEmpty=false := by
    cases e : L.a with
    | nil => simpa [e] using hw.a
    | cons a as => rfl
  have hs : (L.stage.acc.take 257).isEmpty=false := by
    cases e : L.stage.acc with
    | nil => simpa [e] using hw.stage.acc
    | cons a as => rfl
  intro w hm
  simp only [exchange,wires_append,h1,h2,ha,hs,Bool.false_eq_true,if_false,Option.toList_none,
    List.nil_append,Finset.mem_union,List.mem_toFinset,List.mem_append] at hm
  have ht := (List.take_sublist 257 L.stage.acc).subset
  simp only [wires,live,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  tauto

/-- 新门列只触及此具体视图；最终求逆支持由旧core覆盖另行组合。 -/
theorem wires_subset (L : InverseScaleLayout) (hw : L.Widths) (q : Nat) :
    ECDSAAdd.wires (L.prepare q) ⊆ L.wires.toFinset ∧ ECDSAAdd.wires (L.restore q) ⊆ L.wires.toFinset := by
  have hm := montStage_wires L.stage L.factor (L.a.take 256) q hw.stage
    (by simp [hw.factor]) (by simp [hw.a])
  have h1 := L.lookup_subset hw q
  have h2 := L.exchange_subset hw
  have h3 := L.stage_subset
  constructor <;> intro w hh
  · simp only [prepare,wires_append,hm.1,Finset.mem_union] at hh
    rcases hh with ((h|h)|h)|h
    · exact h1 h
    · exact h3 h
    · exact h2 h
    · exact h1 h
  · simp only [restore,wires_append,hm.2,Finset.mem_union] at hh
    rcases hh with ((h|h)|h)|h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h1 h

/-- 准备只改变a与显式历史；其它位包括借用工作区初末相同。 -/
theorem prepare_frame (L : InverseScaleLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Nat) (hq : q%16=15) (hb : q<2^256) (N K : Nat) (hN : N<q)
    (s : State) (m : List Bool)
    (h : ((regValue L.a s.basis=N ∧ regValue L.k s.basis=K) ∧ regValue L.live s.basis=0) ∧ regValue L.work s.basis=0)
    (w : Wire) (ha : w∉L.a) (hl : w∉L.live) :
    (run (L.prepare q) m s).basis w=s.basis w := by
  have hp := (L.prepare_spec hw hn q hq hb N K hN s m h).2
  by_cases hh : w∈L.work
  · rw [(regValue_zero _ _).mp hp.2.2.2.2.2 w hh,(regValue_zero _ _).mp h.2 w hh]
  by_cases hk : w∈L.k
  · exact (regValue_eq_iff L.k _ _).mp (hp.1.trans h.1.1.2.symm) w hk
  apply run_preserves_outside
  intro hm
  have := (L.wires_subset hw q).1 hm
  simp only [wires,List.mem_toFinset,List.mem_append,ha,hl,hh,hk,or_false] at this

/-- 使用段保留历史后，恢复只改变a与显式历史，其余线路保持。 -/
theorem restore_frame (L : InverseScaleLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Nat) (hq : q%16=15) (hb : q<2^256) (N K : Nat) (hN : N<q)
    (s : State) (m : List Bool) (h : L.Prepared q K N s.basis)
    (w : Wire) (ha : w∉L.a) (hl : w∉L.live) :
    (run (L.restore q) m s).basis w=s.basis w := by
  have hp := (L.restore_spec hw hn q hq hb N K hN s m h).2
  by_cases hh : w∈L.work
  · rw [(regValue_zero _ _).mp hp.2 w hh,(regValue_zero _ _).mp h.2.2.2.2.2 w hh]
  by_cases hk : w∈L.k
  · exact (regValue_eq_iff L.k _ _).mp (hp.1.1.2.trans h.1.symm) w hk
  apply run_preserves_outside
  intro hm
  have := (L.wires_subset hw q).2 hm
  simp only [wires,List.mem_toFinset,List.mem_append,ha,hl,hh,hk,or_false] at this

theorem lookup_counts (L : InverseScaleLayout) (q : Nat) (hw : L.Widths) :
    toffoliCount (L.lookup q)=1022 ∧ measurementCount (L.lookup q)=1022 := by
  apply lookup10_counts
  · simp [hw.k]
  · simp [scratch,hw.stage.scratch,hw.extraScratch]

theorem exchange_counts (L : InverseScaleLayout) (hw : L.Widths) :
    toffoliCount L.exchange=0 ∧ measurementCount L.exchange=0 := by
  have h : L.a.length=(L.stage.acc.take 257).length := by simp [hw.a,hw.stage.acc]
  have h1 := copyRegister_counts none L.a (L.stage.acc.take 257) h
  have h2 := copyRegister_counts none (L.stage.acc.take 257) L.a h.symm
  simp [exchange,toffoliCount_append,measurementCount_append,h1,h2]

theorem counts (L : InverseScaleLayout) (q : Nat) (hw : L.Widths) :
    (toffoliCount (L.prepare q)=154372 ∧ measurementCount (L.prepare q)=154372) ∧
    (toffoliCount (L.restore q)=154372 ∧ measurementCount (L.restore q)=154372) := by
  have hl := L.lookup_counts q hw
  have he := L.exchange_counts hw
  have hm := montStage_counts L.stage L.factor (L.a.take 256) q hw.stage (by simp [hw.factor])
  simp [prepare,restore,toffoliCount_append,measurementCount_append,hl,he,hm]

end InverseScaleLayout
end ECDSAAdd.Arithmetic
