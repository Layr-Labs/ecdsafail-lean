import ECDSAAdd.Arithmetic.Counter
import ECDSAAdd.Arithmetic.Copy
import ECDSAAdd.Arithmetic.Accumulate

namespace ECDSAAdd.Arithmetic

/-- 将受控来源临时复制进 y；算术与测量顺序不依赖控制值。 -/
def maskedAdd (L : AdderLayout) (src : List Wire) (c : Wire) : Program :=
  copyRegister (some c) src L.y ++ add L ++ sub L.swapCounter ++
  copyRegister (some c) src L.y

def maskedSub (L : AdderLayout) (src : List Wire) (c : Wire) : Program :=
  copyRegister (some c) src L.y ++ sub L ++ add L.swapCounter ++
  copyRegister (some c) src L.y

theorem AdderLayout.interface_perm (L : AdderLayout) :
    (((L.x ++ L.y) ++ L.out) ++ (L.cin::L.carry)).Perm L.wires := by
  apply List.perm_iff_count.mpr
  intro w
  rcases L with ⟨bs, cin⟩
  induction bs with
  | nil => simp [AdderLayout.x, AdderLayout.y, AdderLayout.out, AdderLayout.carry,
      AdderLayout.wires, addWires]
  | cons b bs ih =>
    simp [AdderLayout.x, AdderLayout.y, AdderLayout.out, AdderLayout.carry,
      AdderLayout.wires, addWires, List.count_cons] at ih ⊢
    omega

theorem AdderLayout.reg_subset (L : AdderLayout) :
    L.x ⊆ L.wires ∧ L.y ⊆ L.wires ∧ L.out ⊆ L.wires ∧ L.carry ⊆ L.wires := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro w hw <;> apply (L.interface_perm).mem_iff.mp <;> simp [hw]

private theorem sub_wires (L : AdderLayout) : wires (sub L) = L.wires.toFinset :=
  rippleSubtractor_wires L.bits L.cin

private theorem add_wires (L : AdderLayout) : wires (add L) ⊆ L.wires.toFinset := by
  cases L with
  | mk bs cin =>
    cases bs with
    | nil => simp [add, rippleAdder, wires]
    | cons b bs => rw [add, rippleAdder_wires]; rfl

private def MaskedValues (L : AdderLayout) (src : List Wire) (c : Wire)
    (X : Nat) (C : Bool) (A B O : Nat) (st : BasisState) : Prop :=
  regValue src st = X ∧ st c = C ∧ regValue L.x st = A ∧ regValue L.y st = B ∧
  st L.cin = false ∧ regValue L.out st = O ∧ regValue L.carry st = 0

private theorem mask_copy (L : AdderLayout) (src : List Wire) (c : Wire)
    (hnd : (c::(src++L.wires)).Nodup) (hlen : src.length = L.width)
    (X : Nat) (C : Bool) (A B O : Nat) :
    Triple (MaskedValues L src c X C A B O) (copyRegister (some c) src L.y)
      (MaskedValues L src c X C A (B ^^^ (if C then X else 0)) O) := by
  intro s m hv
  obtain ⟨hc, hr⟩ := List.nodup_cons.mp hnd
  obtain ⟨hs, hl, hsl⟩ := List.nodup_append'.mp hr
  have hi := (L.interface_perm).nodup_iff.mpr hl
  have hy : L.y.Nodup := (List.nodup_append'.mp
    (List.nodup_append'.mp (List.nodup_append'.mp hi).1).1).2.1
  have hsy : src.Disjoint L.y := List.disjoint_left.mpr
    (fun _ ha hb => List.disjoint_left.mp hsl ha ((L.reg_subset).2.1 hb))
  have hcy : c ∉ L.y := fun h => hc (List.mem_append_right _ ((L.reg_subset).2.1 h))
  obtain ⟨hp, he, hz⟩ := copyRegister_correct (some c) src L.y
    (by simpa [AdderLayout.y, AdderLayout.width] using hlen)
    (List.nodup_append'.mpr ⟨hs, hy, hsy⟩) (by simpa using hcy) s m
  have keep (r : List Wire) (hd : r.Disjoint L.y) :
      regValue r (run (copyRegister (some c) src L.y) m s).basis = regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw => he w (List.disjoint_left.mp hd hw))
  have hxdy : L.x.Disjoint L.y := (List.nodup_append'.mp
    (List.nodup_append'.mp (List.nodup_append'.mp hi).1).1).2.2
  have hydrest : L.y.Disjoint (L.out++(L.cin::L.carry)) := by
    have hh : (L.x ++ (L.y ++ (L.out ++ (L.cin::L.carry)))).Nodup := by
      simpa only [List.append_assoc] using hi
    exact (List.nodup_append'.mp (List.nodup_append'.mp hh).2.1).2.2
  have hody : L.out.Disjoint L.y := List.disjoint_left.mpr
    (fun _ ho hy => List.disjoint_left.mp hydrest hy (List.mem_append_left _ ho))
  have hcdy : L.carry.Disjoint L.y := List.disjoint_left.mpr
    (fun _ hca hy => List.disjoint_left.mp hydrest hy (by simp [hca]))
  have hcin : L.cin ∉ L.y := fun hy => List.disjoint_left.mp hydrest hy (by simp)
  refine ⟨hp, (keep src hsy).trans hv.1, (he c hcy).trans hv.2.1,
    (keep L.x hxdy).trans hv.2.2.1, ?_, (he L.cin hcin).trans hv.2.2.2.2.1,
    (keep L.out hody).trans hv.2.2.2.2.2.1, (keep L.carry hcdy).trans hv.2.2.2.2.2.2⟩
  simpa only [copyValue, hv.1, hv.2.1, hv.2.2.2.1] using hz

private theorem inside (L : AdderLayout) (src : List Wire) (c : Wire)
    (hnd : (c::(src++L.wires)).Nodup) (X : Nat) (C : Bool)
    (A B O A' B' O' : Nat) (p : Program) (hw : wires p ⊆ L.wires.toFinset)
    (hp : {{ L.x=A, L.y=B, L.cin=false, L.out=O, L.carry=0 }} p
      {{ L.x=A', L.y=B', L.cin=false, L.out=O', L.carry=0 }}) :
    Triple (MaskedValues L src c X C A B O) p (MaskedValues L src c X C A' B' O') := by
  intro s m hv
  obtain ⟨hc, hr⟩ := List.nodup_cons.mp hnd
  have hs := (List.nodup_append'.mp hr).2.2
  obtain ⟨hphase, h⟩ := hp s m ⟨⟨⟨⟨hv.2.2.1, hv.2.2.2.1⟩, hv.2.2.2.2.1⟩,
    hv.2.2.2.2.2.1⟩, hv.2.2.2.2.2.2⟩
  have keep (w : Wire) (hn : w ∉ L.wires) : (run p m s).basis w = s.basis w :=
    run_preserves_outside p m s w (fun h => hn (List.mem_toFinset.mp (hw h)))
  exact ⟨hphase, (regValue_congr _ _ _ (fun w hm => keep w (List.disjoint_left.mp hs hm))).trans hv.1,
    (keep c (fun hm => hc (List.mem_append_right _ hm))).trans hv.2.1,
    h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- 将受控加法结果移入空 out，清空旧 x，恢复来源、控制及全部工作位。 -/
theorem maskedAdd_spec (L : AdderLayout) (src : List Wire) (c : Wire)
    (hnd : (c::(src++L.wires)).Nodup) (hlen : src.length=L.width)
    (X A : Nat) (C : Bool) :
    {{ src=X, c=C, L.x=A, L.y=0, L.cin=false, L.out=0, L.carry=0 }} maskedAdd L src c
    {{ src=X, c=C, L.x=0, L.y=0, L.cin=false,
       L.out=((A+(if C then X else 0))%2^L.width), L.carry=0 }} := by
  intro s m hv
  have ha : A<2^L.width := by
    have hh := regValue_lt L.x s.basis
    rw [show regValue L.x s.basis = A from hv.1.1.1.1.2] at hh
    simpa [AdderLayout.x, AdderLayout.width] using hh
  have hx : X<2^L.width := by
    have hh := regValue_lt src s.basis
    rw [show regValue src s.basis = X from hv.1.1.1.1.1.1, hlen] at hh
    exact hh
  let M := if C then X else 0
  have hm : M<2^L.width := by dsimp [M]; split <;> (first | assumption | exact Nat.two_pow_pos _)
  have hl := (List.nodup_append'.mp (List.nodup_cons.mp hnd).2).2.1
  let V := (A+M)%2^L.width
  have h0 := mask_copy L src c hnd hlen X C A 0 0
  simp only [Nat.zero_xor] at h0
  have h1 := inside L src c hnd X C A M 0 A M V (add L) (add_wires L)
    (by simpa [V] using add_spec L hl A M 0 false)
  have hcancel : (V+2^L.width-M)%2^L.width=A := modular_sum_sub A M _ ha hm
  obtain ⟨sx, so, sy, sc, si, sw⟩ := L.swapCounter_fields
  have hp := sub_spec L.swapCounter ((L.swapCounter_perm).nodup_iff.mpr hl) V M A
  simp only [sx, so, sy, sc, si, sw, hcancel, Nat.xor_self] at hp
  have hsub : {{ L.x=A, L.y=M, L.cin=false, L.out=V, L.carry=0 }} sub L.swapCounter
      {{ L.x=0, L.y=M, L.cin=false, L.out=V, L.carry=0 }} :=
    Triple.conseq (fun st h => ⟨⟨⟨⟨h.1.2,h.1.1.1.2⟩,h.1.1.2⟩,h.1.1.1.1⟩,h.2⟩) hp
      (fun st h => ⟨⟨⟨⟨h.1.2,h.1.1.1.2⟩,h.1.1.2⟩,h.1.1.1.1⟩,h.2⟩)
  have hsw : wires (sub L.swapCounter) ⊆ L.wires.toFinset := by
    rw [sub_wires]
    intro w hw
    exact List.mem_toFinset.mpr ((L.swapCounter_perm).mem_iff.mp (List.mem_toFinset.mp hw))
  have h2 := inside L src c hnd X C A M V 0 M V (sub L.swapCounter) hsw hsub
  have h3 := mask_copy L src c hnd hlen X C 0 M V
  simp only [show M ^^^ (if C then X else 0)=0 from Nat.xor_self M] at h3
  have h := h0.seq (h1.seq (h2.seq h3))
  have h' : Triple (MaskedValues L src c X C A 0 0) (maskedAdd L src c)
      (MaskedValues L src c X C 0 0 V) := by simpa only [maskedAdd, List.append_assoc, M] using h
  obtain ⟨hp, hv'⟩ := h' s m ⟨hv.1.1.1.1.1.1, hv.1.1.1.1.1.2,
    hv.1.1.1.1.2, hv.1.1.1.2, hv.1.1.2, hv.1.2, hv.2⟩
  exact ⟨hp, ⟨⟨⟨⟨⟨⟨hv'.1,hv'.2.1⟩,hv'.2.2.1⟩,hv'.2.2.2.1⟩,hv'.2.2.2.2.1⟩,
    hv'.2.2.2.2.2.1⟩,hv'.2.2.2.2.2.2⟩⟩

private theorem modular_sub_sum (A B q : Nat) (ha : A<q) (hb : B<q) :
    (((A+q-B)%q)+B)%q = A := by
  by_cases h : B≤A
  · rw [show A+q-B = (A-B)+q by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show A-B<q by omega), Nat.sub_add_cancel h, Nat.mod_eq_of_lt ha]
  · rw [Nat.mod_eq_of_lt (show A+q-B<q by omega),
      show A+q-B+B=A+q by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ha]

/-- 将受控减法结果移入空 out，清空旧 x，恢复来源、控制及全部工作位。 -/
theorem maskedSub_spec (L : AdderLayout) (src : List Wire) (c : Wire)
    (hnd : (c::(src++L.wires)).Nodup) (hlen : src.length=L.width)
    (X A : Nat) (C : Bool) :
    {{ src=X, c=C, L.x=A, L.y=0, L.cin=false, L.out=0, L.carry=0 }} maskedSub L src c
    {{ src=X, c=C, L.x=0, L.y=0, L.cin=false,
       L.out=((A+2^L.width-(if C then X else 0))%2^L.width), L.carry=0 }} := by
  intro s m hv
  have ha : A<2^L.width := by
    have hh := regValue_lt L.x s.basis
    rw [show regValue L.x s.basis = A from hv.1.1.1.1.2] at hh
    simpa [AdderLayout.x, AdderLayout.width] using hh
  have hx : X<2^L.width := by
    have hh := regValue_lt src s.basis
    rw [show regValue src s.basis = X from hv.1.1.1.1.1.1, hlen] at hh
    exact hh
  let M := if C then X else 0
  have hm : M<2^L.width := by dsimp [M]; split <;> (first | assumption | exact Nat.two_pow_pos _)
  have hl := (List.nodup_append'.mp (List.nodup_cons.mp hnd).2).2.1
  let V := (A+2^L.width-M)%2^L.width
  have h0 := mask_copy L src c hnd hlen X C A 0 0
  simp only [Nat.zero_xor] at h0
  have h1 := inside L src c hnd X C A M 0 A M V (sub L) (by rw [sub_wires])
    (by simpa [V] using sub_spec L hl A M 0)
  have hcancel : (V+M)%2^L.width=A := modular_sub_sum A M _ ha hm
  obtain ⟨sx, so, sy, sc, si, sw⟩ := L.swapCounter_fields
  have hp := add_spec L.swapCounter ((L.swapCounter_perm).nodup_iff.mpr hl) V M A false
  simp only [sx, so, sy, sc, si, sw, show false.toNat=0 from rfl, Nat.add_zero, hcancel, Nat.xor_self] at hp
  have hsub : {{ L.x=A, L.y=M, L.cin=false, L.out=V, L.carry=0 }} add L.swapCounter
      {{ L.x=0, L.y=M, L.cin=false, L.out=V, L.carry=0 }} :=
    Triple.conseq (fun st h => ⟨⟨⟨⟨h.1.2,h.1.1.1.2⟩,h.1.1.2⟩,h.1.1.1.1⟩,h.2⟩) hp
      (fun st h => ⟨⟨⟨⟨h.1.2,h.1.1.1.2⟩,h.1.1.2⟩,h.1.1.1.1⟩,h.2⟩)
  have hsw : wires (add L.swapCounter) ⊆ L.wires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr ((L.swapCounter_perm).mem_iff.mp (List.mem_toFinset.mp (add_wires _ hw)))
  have h2 := inside L src c hnd X C A M V 0 M V (add L.swapCounter) hsw hsub
  have h3 := mask_copy L src c hnd hlen X C 0 M V
  simp only [show M ^^^ (if C then X else 0)=0 from Nat.xor_self M] at h3
  have h := h0.seq (h1.seq (h2.seq h3))
  have h' : Triple (MaskedValues L src c X C A 0 0) (maskedSub L src c)
      (MaskedValues L src c X C 0 0 V) := by simpa only [maskedSub, List.append_assoc, M] using h
  obtain ⟨hp, hv'⟩ := h' s m ⟨hv.1.1.1.1.1.1, hv.1.1.1.1.1.2,
    hv.1.1.1.1.2, hv.1.1.1.2, hv.1.1.2, hv.1.2, hv.2⟩
  exact ⟨hp, ⟨⟨⟨⟨⟨⟨hv'.1,hv'.2.1⟩,hv'.2.2.1⟩,hv'.2.2.2.1⟩,hv'.2.2.2.2.1⟩,
    hv'.2.2.2.2.2.1⟩,hv'.2.2.2.2.2.2⟩⟩

/-- 两种前向算术共用相同工作区；活动控制也计入真实线路集合。 -/
theorem maskedAdder_wires (L : AdderLayout) (src : List Wire) (c : Wire)
    (hlen : src.length=L.width) (hpos : 0<L.width) :
    wires (maskedAdd L src c) = (c::(src++L.wires)).toFinset ∧
    wires (maskedSub L src c) = (c::(src++L.wires)).toFinset := by
  have hs : src.isEmpty=false := by cases src <;> simp_all
  have hc := copyRegister_wires (some c) src L.y
    (by simpa [AdderLayout.y, AdderLayout.width] using hlen)
  simp only [hs, Bool.false_eq_true, if_false, Option.toList_some, List.cons_append,
    List.nil_append] at hc
  have ha : wires (add L) = L.wires.toFinset := by
    cases L with
    | mk bs cin =>
      cases bs with
      | nil => simp [AdderLayout.width] at hpos
      | cons b bs => exact rippleAdder_wires b bs cin
  have hsw : L.swapCounter.wires.toFinset = L.wires.toFinset := by
    ext w
    simpa only [List.mem_toFinset] using (L.swapCounter_perm).mem_iff
  have has : wires (add L.swapCounter) ⊆ L.wires.toFinset := by
    rw [← hsw]; exact add_wires _
  constructor
  · rw [maskedAdd, wires_append, wires_append, wires_append, hc, ha, sub_wires, hsw]
    ext w
    have hy : w∈L.y → w∈L.wires := fun h => (L.reg_subset).2.1 h
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto
  · rw [maskedSub, wires_append, wires_append, wires_append, hc, sub_wires]
    ext w
    have hy : w∈L.y → w∈L.wires := fun h => (L.reg_subset).2.1 h
    have hsa : w∈wires (add L.swapCounter) → w∈L.wires :=
      fun h => List.mem_toFinset.mp (has h)
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto

theorem maskedAdder_resources (L : AdderLayout) (src : List Wire) (c : Wire)
    (hnd : (c::(src++L.wires)).Nodup) (hlen : src.length=L.width) (hpos : 0<L.width) :
    toffoliCount (maskedAdd L src c) = 4*L.width ∧
    measurementCount (maskedAdd L src c) = 2*L.width ∧
    qubitCount (maskedAdd L src c) = 5*L.width+2 ∧
    toffoliCount (maskedSub L src c) = 4*L.width ∧
    measurementCount (maskedSub L src c) = 2*L.width ∧
    qubitCount (maskedSub L src c) = 5*L.width+2 := by
  have hl := (List.nodup_append'.mp (List.nodup_cons.mp hnd).2).2.1
  have hls := (L.swapCounter_perm).nodup_iff.mpr hl
  have ha := add_resources L hl
  have hd := sub_resources L hl
  have has := add_resources L.swapCounter hls
  have hds := sub_resources L.swapCounter hls
  have hs := (L.swapCounter_fields).2.2.2.2.2
  have hc := copyRegister_counts (some c) src L.y
    (by simpa [AdderLayout.y, AdderLayout.width] using hlen)
  have hw := maskedAdder_wires L src c hlen hpos
  have hlenw : (c::(src++L.wires)).length = 5*L.width+2 := by
    simp [AdderLayout.wires, AdderLayout.width, addWires_length, hlen]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [maskedAdd, toffoliCount_append, hc.1, ha.1, hds.1, hs]; simp [hlen]; omega
  · simp only [maskedAdd, measurementCount_append, hc.2, ha.2.1, hds.2.1, hs]; omega
  · rw [qubitCount, hw.1, List.toFinset_card_of_nodup hnd, hlenw]
  · simp only [maskedSub, toffoliCount_append, hc.1, hd.1, has.1, hs]; simp [hlen]; omega
  · simp only [maskedSub, measurementCount_append, hc.2, hd.2.1, has.2.1, hs]; omega
  · rw [qubitCount, hw.2, List.toFinset_card_of_nodup hnd, hlenw]

/-- 将受控累加的寄存器保持结论提升为逐线保持，供单轮组合。 -/
theorem AdderLayout.masked_frame (L : AdderLayout) (src : List Wire) (c : Wire)
    (s t : BasisState) (hsrc : regValue src t=regValue src s) (hc : t c=s c)
    (hy : regValue L.y t=regValue L.y s) (hcin : t L.cin=s L.cin)
    (hcarry : regValue L.carry t=regValue L.carry s)
    (he : ∀ w, w∉c::(src++L.wires) → t w=s w) :
    ∀ w, w∉L.x → w∉L.out → t w=s w := by
  intro w hx ho
  by_cases hm : w∈c::(src++L.wires)
  · simp only [List.mem_cons, List.mem_append] at hm
    rcases hm with rfl | hsrcw | hl
    · exact hc
    · exact (regValue_eq_iff src t s).mp hsrc w hsrcw
    · have hm := L.interface_perm.mem_iff.mpr hl
      simp only [List.mem_append, List.mem_cons] at hm
      rcases hm with ((hxw | hyw) | how) | hcinw | hcarryw
      · exact False.elim (hx hxw)
      · exact (regValue_eq_iff L.y t s).mp hy w hyw
      · exact False.elim (ho how)
      · subst w; exact hcin
      · exact (regValue_eq_iff L.carry t s).mp hcarry w hcarryw
  · exact he w hm

end ECDSAAdd.Arithmetic
