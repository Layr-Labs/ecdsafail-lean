import ECDSAAdd.Arithmetic.InPlaceAdder

namespace ECDSAAdd.Arithmetic

/-- 清除已知等于控制与来源逐位AND的掩码；每位只依赖本次测量记录。 -/
def eraseMask (c : Wire) : List Wire → List Wire → Program
  | a::src, b::dst => .measureX b [] [.CZ c a] :: eraseMask c src dst
  | _, _ => []

private theorem eraseMask_bit (c a b : Wire) (hc : c≠b) (ha : a≠b)
    (s : State) (h : s.basis b = (s.basis c && s.basis a)) (v : Bool) :
    measureAndCorrect b [] [.CZ c a] v s = ⟨s.phase,writeBit s.basis b false⟩ := by
  cases v <;> simp [measureAndCorrect,correct,writeBit,h,hc,ha]

/-- 掩码关系是清理前提；来源、控制和掩码以外的位保持。 -/
theorem eraseMask_correct (c : Wire) (src dst : List Wire)
    (hlen : src.length=dst.length) (hnd : (c::(src++dst)).Nodup)
    (s : State) (m : List Bool)
    (hmask : regValue dst s.basis = if s.basis c then regValue src s.basis else 0) :
    (run (eraseMask c src dst) m s).phase=s.phase ∧
    (∀ w, w∉dst → (run (eraseMask c src dst) m s).basis w=s.basis w) ∧
    regValue dst (run (eraseMask c src dst) m s).basis=0 := by
  induction src generalizing dst s m with
  | nil =>
    have hd : dst=[] := List.eq_nil_of_length_eq_zero hlen.symm
    subst dst
    simp [eraseMask,run,regValue]
  | cons a src ih =>
    cases dst with
    | nil => simp at hlen
    | cons b dst =>
      have hn := List.nodup_cons.mp hnd
      obtain ⟨hs,hd,hsd⟩ := List.nodup_append'.mp hn.2
      have hcb : c≠b := fun h => hn.1 (by simp [h])
      have hab : a≠b := fun h => List.disjoint_left.mp hsd (List.mem_cons_self : a∈a::src) (by simp [h])
      have hbs : b∉src := fun h => List.disjoint_left.mp hsd (List.mem_cons_of_mem a h) (List.mem_cons_self)
      have hbd : b∉dst := (List.nodup_cons.mp hd).1
      have ht : (c::(src++dst)).Nodup := List.nodup_cons.mpr ⟨
        (fun h => hn.1 (by simp only [List.mem_append,List.mem_cons] at h ⊢; tauto)),
        List.nodup_append'.mpr ⟨(List.nodup_cons.mp hs).2,(List.nodup_cons.mp hd).2,
          List.disjoint_left.mpr (fun _ hx hy => List.disjoint_left.mp hsd (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem b hy))⟩⟩
      have hb : s.basis b = (s.basis c && s.basis a) := by
        change (if s.basis b then 1 else 0)+2*regValue dst s.basis =
          (if s.basis c then (if s.basis a then 1 else 0)+2*regValue src s.basis else 0) at hmask
        cases hc : s.basis c <;> cases ha : s.basis a <;> cases hb : s.basis b <;> simp_all <;> omega
      have hv : regValue dst s.basis = if s.basis c then regValue src s.basis else 0 := by
        change (if s.basis b then 1 else 0)+2*regValue dst s.basis =
          (if s.basis c then (if s.basis a then 1 else 0)+2*regValue src s.basis else 0) at hmask
        cases hc : s.basis c <;> cases ha : s.basis a <;> cases hb : s.basis b <;> simp_all
      let t : State := ⟨s.phase,writeBit s.basis b false⟩
      have keep (w : Wire) (hw : w≠b) : t.basis w=s.basis w := by simp [t,writeBit,hw]
      have vs : regValue src t.basis=regValue src s.basis := regValue_congr _ _ _
        (fun w hw => keep w (fun h => hbs (h ▸ hw)))
      have vd : regValue dst t.basis=regValue dst s.basis := regValue_congr _ _ _
        (fun w hw => keep w (fun h => hbd (h ▸ hw)))
      have hm : regValue dst t.basis = if t.basis c then regValue src t.basis else 0 := by
        rw [vs,vd,keep c hcb]; exact hv
      obtain ⟨hp,he,hz⟩ := ih dst (by simpa using hlen) ht t m.tail hm
      simp only [eraseMask,run,eraseMask_bit c a b hcb hab s hb]
      change (run (eraseMask c src dst) m.tail t).phase=s.phase ∧ _
      refine ⟨hp,?_,?_⟩
      · intro w hw
        have hw' : w≠b ∧ w∉dst := by simpa using hw
        exact (he w hw'.2).trans (keep w hw'.1)
      · change (if (run (eraseMask c src dst) m.tail t).basis b then 1 else 0)+2*regValue dst _=0
        rw [he b hbd,hz]
        simp [t,writeBit]


/-- 在确定掩码输入上，测量清理与旧CCX清理恢复完全相同的状态。 -/
theorem eraseMask_eq_copy (c : Wire) (src dst : List Wire)
    (hlen : src.length=dst.length) (hnd : (c::(src++dst)).Nodup)
    (s : State) (m : List Bool)
    (hm : regValue dst s.basis = if s.basis c then regValue src s.basis else 0) :
    run (eraseMask c src dst) m s = run (copyRegister (some c) src dst) m s := by
  obtain ⟨hp,he,hz⟩ := eraseMask_correct c src dst hlen hnd s m hm
  have hn := List.nodup_cons.mp hnd
  have hc : c∉dst := fun h => hn.1 (by simp [h])
  obtain ⟨cp,ce,cv⟩ := copyRegister_correct (some c) src dst hlen hn.2 (by simpa using hc) s m
  have cz : regValue dst (run (copyRegister (some c) src dst) m s).basis=0 := by
    rw [cv,hm]; simp [copyValue]
  have hb : (run (eraseMask c src dst) m s).basis=(run (copyRegister (some c) src dst) m s).basis := by
    funext w
    by_cases hw : w∈dst
    · exact ((regValue_zero _ _).mp hz w hw).trans ((regValue_zero _ _).mp cz w hw).symm
    · exact (he w hw).trans (ce w hw).symm
  cases hx : run (eraseMask c src dst) m s
  cases hy : run (copyRegister (some c) src dst) m s
  simp_all

/-- 受控加法中段保持掩码关系，末段用测量和CZ归零。 -/
def measuredMaskedAddInPlace (c : Wire) (src t y carry : List Wire) (cin : Wire) : Program :=
  copyRegister (some c) src t ++ addInPlace t y carry cin ++ eraseMask c src t

def measuredMaskedSubInPlace (c : Wire) (src t y carry : List Wire) (cin : Wire) : Program :=
  copyRegister (some c) src t ++ subInPlace t y carry cin ++ eraseMask c src t

private theorem eraseMask_frame_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c :: cin :: (src ++ t ++ y ++ carry)).Nodup) (hs : src.length = t.length)
    (C : Bool) (S Y : Nat) :
    {{ c = C, src = S, t = (if C then S else 0), y = Y, cin = false, carry = 0 }} eraseMask c src t
    {{ c = C, src = S, t = 0, y = Y, cin = false, carry = 0 }} := by
  have hst : (c::(src++t)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hn := List.nodup_iff_count.mp hnd w
    simp only [List.count_cons,List.count_append] at hn ⊢
    omega
  intro s m hv
  have hm : regValue t s.basis=if s.basis c then regValue src s.basis else 0 := by
    rw [show s.basis c=C from hv.1.1.1.1.1,show regValue src s.basis=S from hv.1.1.1.1.2]
    exact hv.1.1.1.2
  rw [eraseMask_eq_copy c src t hs hst s m hm]
  have h := maskedCopyWithFrame_spec c cin src t y carry hnd hs C S (if C then S else 0) Y s m hv
  simpa only [Nat.xor_self] using h

/-- 任意W位输入的受控原地加法，掩码、进位和相位全部恢复。 -/
theorem measuredMaskedAddInPlace_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c :: cin :: (src ++ t ++ y ++ carry)).Nodup) (hs : src.length = t.length)
    (ht : t.length = y.length) (hc : carry.length + 1 = y.length) (C : Bool) (S Y : Nat) :
    {{ c = C, src = S, t = 0, y = Y, cin = false, carry = 0 }} measuredMaskedAddInPlace c src t y carry cin
    {{ c = C, src = S, t = 0, y = ((Y + (if C then S else 0)) % 2^y.length), cin = false, carry = 0 }} := by
  have h1 := maskedCopyWithFrame_spec c cin src t y carry hnd hs C S 0 Y
  have h2 := addInPlaceWithSource_spec c cin src t y carry hnd ht hc C S (if C then S else 0) Y
  have h3 := eraseMask_frame_spec c cin src t y carry hnd hs C S
    ((Y + (if C then S else 0)) % 2^y.length)
  simp only [Nat.zero_xor] at h1
  simpa only [measuredMaskedAddInPlace, List.append_assoc] using h1.seq (h2.seq h3)

theorem measuredMaskedSubInPlace_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c :: cin :: (src ++ t ++ y ++ carry)).Nodup) (hs : src.length = t.length)
    (ht : t.length = y.length) (hc : carry.length + 1 = y.length) (C : Bool) (S Y : Nat) :
    {{ c = C, src = S, t = 0, y = Y, cin = false, carry = 0 }} measuredMaskedSubInPlace c src t y carry cin
    {{ c = C, src = S, t = 0, y = ((Y + 2^y.length - (if C then S else 0)) % 2^y.length), cin = false, carry = 0 }} := by
  have h1 := maskedCopyWithFrame_spec c cin src t y carry hnd hs C S 0 Y
  have h2 := subInPlaceWithSource_spec c cin src t y carry hnd ht hc C S (if C then S else 0) Y
  have h3 := eraseMask_frame_spec c cin src t y carry hnd hs C S
    ((Y + 2^y.length - (if C then S else 0)) % 2^y.length)
  simp only [Nat.zero_xor] at h1
  simpa only [measuredMaskedSubInPlace, List.append_assoc] using h1.seq (h2.seq h3)


theorem eraseMask_counts (c : Wire) (src dst : List Wire) (hlen : src.length=dst.length) :
    toffoliCount (eraseMask c src dst)=0 ∧ measurementCount (eraseMask c src dst)=dst.length := by
  induction src generalizing dst with
  | nil => have hd : dst=[] := List.eq_nil_of_length_eq_zero hlen.symm; subst dst; simp [eraseMask,toffoliCount,measurementCount]
  | cons a src ih =>
    cases dst with
    | nil => simp at hlen
    | cons b dst =>
      have h := ih dst (by simpa using hlen)
      simp [eraseMask,toffoliCount,measurementCount,h.1,h.2,Nat.add_comm]

theorem eraseMask_wires_subset (c : Wire) (src dst : List Wire) :
    wires (eraseMask c src dst) ⊆ (c::(src++dst)).toFinset := by
  induction src generalizing dst with
  | nil => simp [eraseMask,wires]
  | cons a src ih =>
    cases dst with
    | nil => simp [eraseMask,wires]
    | cons b dst =>
      intro w hw
      have ht := ih dst
      simp only [eraseMask,wires,Instr.wires,correctionWires] at hw
      have ha : w∈wires (eraseMask c src dst) → w∈(c::(src++dst)).toFinset := fun h => ht h
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,
        List.mem_toFinset,List.mem_cons,List.mem_append] at hw ha ⊢
      tauto

/-- 同一受控门列的精确Toffoli/测量数。 -/
theorem measuredMaskedInPlace_counts (c : Wire) (src t y carry : List Wire) (cin : Wire)
    (hs : src.length=t.length) (ht : t.length=y.length) (hc : carry.length+1=y.length) :
    (toffoliCount (measuredMaskedAddInPlace c src t y carry cin)=2*y.length-1 ∧
      measurementCount (measuredMaskedAddInPlace c src t y carry cin)=2*y.length-1) ∧
    (toffoliCount (measuredMaskedSubInPlace c src t y carry cin)=2*y.length-1 ∧
      measurementCount (measuredMaskedSubInPlace c src t y carry cin)=2*y.length-1) := by
  have cp := copyRegister_counts (some c) src t hs
  have ap := addInPlace_counts t y carry cin ht hc
  have sp := subInPlace_counts t y carry cin ht hc
  have ep := eraseMask_counts c src t hs
  simp only [measuredMaskedAddInPlace,measuredMaskedSubInPlace,toffoliCount_append,
    measurementCount_append,cp.1,cp.2,ap.1,ap.2,sp.1,sp.2,ep.1,ep.2,
    Option.isSome_some,if_true]
  omega

theorem measuredMaskedInPlace_wires (c : Wire) (src t y carry : List Wire) (cin : Wire)
    (hs : src.length=t.length) (ht : t.length=y.length) (hc : carry.length+1=y.length) :
    wires (measuredMaskedAddInPlace c src t y carry cin)=(c::cin::(src++t++y++carry)).toFinset ∧
    wires (measuredMaskedSubInPlace c src t y carry cin)=(c::cin::(src++t++y++carry)).toFinset := by
  have hn : src≠[] := by intro h; simp [h] at hs; omega
  have cp := copyRegister_wires (some c) src t hs
  simp only [List.isEmpty_iff,hn,if_false,Option.toList_some,List.cons_append,List.nil_append] at cp
  have ep := eraseMask_wires_subset c src t
  constructor
  · rw [measuredMaskedAddInPlace,wires_append,wires_append,cp,addInPlace_wires t y carry cin ht hc]
    ext w
    have he := @ep w
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append] at he ⊢
    tauto
  · rw [measuredMaskedSubInPlace,wires_append,wires_append,cp,subInPlace_wires t y carry cin ht hc]
    ext w
    have he := @ep w
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append] at he ⊢
    tauto

theorem measuredMaskedInPlace_qubits (c : Wire) (src t y carry : List Wire) (cin : Wire)
    (hnd : (c::cin::(src++t++y++carry)).Nodup)
    (hs : src.length=t.length) (ht : t.length=y.length) (hc : carry.length+1=y.length) :
    qubitCount (measuredMaskedAddInPlace c src t y carry cin)=4*y.length+1 ∧
    qubitCount (measuredMaskedSubInPlace c src t y carry cin)=4*y.length+1 := by
  have hw := measuredMaskedInPlace_wires c src t y carry cin hs ht hc
  simp only [qubitCount,hw.1,hw.2,List.toFinset_card_of_nodup hnd,List.length_cons,List.length_append]
  omega


private theorem mask_frame (c cin : Wire) (src t y carry : List Wire) (s u : BasisState)
    (hc : u c=s c) (hi : u cin=s cin)
    (hs : regValue src u=regValue src s) (ht : regValue t u=regValue t s)
    (hk : regValue carry u=regValue carry s)
    (he : ∀ w, w∉c::cin::(src++t++y++carry) → u w=s w) :
    ∀ w, w∉y → u w=s w := by
  intro w hy
  by_cases hw : w∈c::cin::(src++t++y++carry)
  · simp only [List.mem_cons,List.mem_append] at hw
    rcases hw with rfl | rfl | ((hw | hw) | hw) | hw
    · exact hc
    · exact hi
    · exact (regValue_eq_iff src u s).mp hs w hw
    · exact (regValue_eq_iff t u s).mp ht w hw
    · exact False.elim (hy hw)
    · exact (regValue_eq_iff carry u s).mp hk w hw
  · exact he w hw

/-- 对满足工作区初值的任意状态，目标y以外的每根线保持。 -/
theorem measuredMaskedAddInPlace_frame (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c :: cin :: (src ++ t ++ y ++ carry)).Nodup) (hs : src.length=t.length)
    (ht : t.length=y.length) (hc : carry.length+1=y.length)
    (s : State) (m : List Bool) (vt : regValue t s.basis=0)
    (vi : s.basis cin=false) (vk : regValue carry s.basis=0) :
    ∀ w, w∉y → (run (measuredMaskedAddInPlace c src t y carry cin) m s).basis w=s.basis w := by
  obtain ⟨_,h⟩ := measuredMaskedAddInPlace_spec c cin src t y carry hnd hs ht hc
    (s.basis c) (regValue src s.basis) (regValue y s.basis) s m ⟨⟨⟨⟨⟨rfl,rfl⟩,vt⟩,rfl⟩,vi⟩,vk⟩
  apply mask_frame c cin src t y carry s.basis _ h.1.1.1.1.1 (h.1.2.trans vi.symm)
    h.1.1.1.1.2 (h.1.1.1.2.trans vt.symm) (h.2.trans vk.symm)
  intro w hw
  apply run_preserves_outside
  rw [(measuredMaskedInPlace_wires c src t y carry cin hs ht hc).1]
  simpa using hw

theorem measuredMaskedSubInPlace_frame (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c :: cin :: (src ++ t ++ y ++ carry)).Nodup) (hs : src.length=t.length)
    (ht : t.length=y.length) (hc : carry.length+1=y.length)
    (s : State) (m : List Bool) (vt : regValue t s.basis=0)
    (vi : s.basis cin=false) (vk : regValue carry s.basis=0) :
    ∀ w, w∉y → (run (measuredMaskedSubInPlace c src t y carry cin) m s).basis w=s.basis w := by
  obtain ⟨_,h⟩ := measuredMaskedSubInPlace_spec c cin src t y carry hnd hs ht hc
    (s.basis c) (regValue src s.basis) (regValue y s.basis) s m ⟨⟨⟨⟨⟨rfl,rfl⟩,vt⟩,rfl⟩,vi⟩,vk⟩
  apply mask_frame c cin src t y carry s.basis _ h.1.1.1.1.1 (h.1.2.trans vi.symm)
    h.1.1.1.1.2 (h.1.1.1.2.trans vt.symm) (h.2.trans vk.symm)
  intro w hw
  apply run_preserves_outside
  rw [(measuredMaskedInPlace_wires c src t y carry cin hs ht hc).2]
  simpa using hw

end ECDSAAdd.Arithmetic
