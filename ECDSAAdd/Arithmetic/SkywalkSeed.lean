import ECDSAAdd.Arithmetic.SignedRecordProgram
import ECDSAAdd.Arithmetic.Constant
import ECDSAAdd.Arithmetic.Copy
import ECDSAAdd.Math.SkywalkNat

namespace ECDSAAdd.Arithmetic

structure SkywalkSeedLayout where
  a : List Wire
  b : List Wire
  constant : List Wire
  carry : List Wire
  cin : Wire
  orientation : Wire

namespace SkywalkSeedLayout

def wires (L : SkywalkSeedLayout) : List Wire :=
  L.cin::L.orientation::(L.a++L.b++L.constant++L.carry)

def usedWires (L : SkywalkSeedLayout) : List Wire := L.cin::(L.a++L.b++L.constant++L.carry)

structure Widths (L : SkywalkSeedLayout) (w : Nat) : Prop where
  a : L.a.length=w
  b : L.b.length=w
  constant : L.constant.length=w
  carry : L.carry.length+1=w

theorem core_nodup (L : SkywalkSeedLayout) (hn : L.wires.Nodup) :
    (L.cin::(L.constant++L.a++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hn q
  simp only [wires,List.count_cons,List.count_append] at hh ⊢
  omega

private theorem constant_nodup (L : SkywalkSeedLayout) (hn : L.wires.Nodup) :
    L.constant.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hn q
  simp only [wires,List.count_cons,List.count_append] at hh
  omega

private theorem copy_nodup (L : SkywalkSeedLayout) (hn : L.wires.Nodup) :
    (L.b++L.a).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hn q
  simp only [wires,List.count_cons,List.count_append] at hh ⊢
  omega

private theorem outside_constant (L : SkywalkSeedLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈[L.cin,L.orientation]++L.a++L.b++L.carry) : q∉L.constant := by
  intro hc
  have hh := List.nodup_iff_count.mp hn q
  have ho := List.count_pos_iff.mpr hq
  have hd := List.count_pos_iff.mpr hc
  simp only [wires,List.count_cons,List.count_append,List.count_nil] at hh ho
  omega

private theorem outside_a (L : SkywalkSeedLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈[L.cin,L.orientation]++L.b++L.constant++L.carry) : q∉L.a := by
  intro ha
  have hh := List.nodup_iff_count.mp hn q
  have ho := List.count_pos_iff.mpr hq
  have hd := List.count_pos_iff.mpr ha
  simp only [wires,List.count_cons,List.count_append,List.count_nil] at hh ho
  omega

end SkywalkSeedLayout

structure SkywalkSeedValues (L : SkywalkSeedLayout) (A B C : Nat) (s : BasisState) : Prop where
  a : regValue L.a s=A
  b : regValue L.b s=B
  constant : regValue L.constant s=C
  carry : regValue L.carry s=0
  cin : s L.cin=false
  orientation : s L.orientation=false

def skywalkSeed (L : SkywalkSeedLayout) (p : Nat) : Program :=
  copyRegister none L.b L.a ++ xorConstant L.constant p ++
    addInPlace L.constant L.a L.carry L.cin ++ xorConstant L.constant p

def skywalkUnseed (L : SkywalkSeedLayout) (p : Nat) : Program :=
  xorConstant L.constant p ++ subInPlace L.constant L.a L.carry L.cin ++
    xorConstant L.constant p ++ copyRegister none L.b L.a

private theorem seed_constant_stage (L : SkywalkSeedLayout) (hn : L.wires.Nodup)
    (p A B C : Nat) (hp : p<2^L.constant.length) :
    Triple (SkywalkSeedValues L A B C) (xorConstant L.constant p)
      (SkywalkSeedValues L A B (C ^^^ p)) := by
  intro s m hin
  obtain ⟨hphase,he,hv⟩ := xorConstant_correct L.constant (L.constant_nodup hn) p hp s m
  have keep (r : List Wire) (hr : r⊆[L.cin,L.orientation]++L.a++L.b++L.carry) :
      regValue r (run (xorConstant L.constant p) m s).basis=regValue r s.basis := by
    apply regValue_congr
    intro q hq
    exact he q (L.outside_constant hn q (hr hq))
  refine ⟨hphase,(keep _ (by intro q hq; simp [hq])).trans hin.a,
    (keep _ (by intro q hq; simp [hq])).trans hin.b,?_,
    (keep _ (by intro q hq; simp [hq])).trans hin.carry,
    (he _ (L.outside_constant hn _ (by simp))).trans hin.cin,
    (he _ (L.outside_constant hn _ (by simp))).trans hin.orientation⟩
  simpa only [hin.constant] using hv

private theorem seed_copy_stage (L : SkywalkSeedLayout) (hn : L.wires.Nodup)
    (hw : L.b.length=L.a.length) (A B C : Nat) :
    Triple (SkywalkSeedValues L A B C) (copyRegister none L.b L.a)
      (SkywalkSeedValues L (A ^^^ B) B C) := by
  intro s m hin
  obtain ⟨hphase,he,hv⟩ := copyRegister_correct none L.b L.a hw (L.copy_nodup hn)
    (by simp) s m
  have keep (r : List Wire) (hr : r⊆[L.cin,L.orientation]++L.b++L.constant++L.carry) :
      regValue r (run (copyRegister none L.b L.a) m s).basis=regValue r s.basis := by
    apply regValue_congr
    intro q hq
    exact he q (L.outside_a hn q (hr hq))
  refine ⟨hphase,?_,(keep _ (by intro q hq; simp [hq])).trans hin.b,
    (keep _ (by intro q hq; simp [hq])).trans hin.constant,
    (keep _ (by intro q hq; simp [hq])).trans hin.carry,
    (he _ (L.outside_a hn _ (by simp))).trans hin.cin,
    (he _ (L.outside_a hn _ (by simp))).trans hin.orientation⟩
  simpa only [hin.a,hin.b,copyValue] using hv

private theorem seed_add_stage (L : SkywalkSeedLayout) (hn : L.wires.Nodup)
    (hx : L.constant.length=L.a.length) (hc : L.carry.length+1=L.a.length)
    (A B C : Nat) :
    Triple (SkywalkSeedValues L A B C) (addInPlace L.constant L.a L.carry L.cin)
      (SkywalkSeedValues L ((C+A)%2^L.a.length) B C) := by
  intro s m hin
  obtain ⟨hp,he,hv⟩ := addInPlace_correct L.constant L.a L.carry L.cin
    (L.core_nodup hn) hx hc s m ((regValue_zero _ _).mp hin.carry)
  have keep (r : List Wire) (hr : r⊆[L.cin,L.orientation]++L.b++L.constant++L.carry) :
      regValue r (run (addInPlace L.constant L.a L.carry L.cin) m s).basis=regValue r s.basis := by
    apply regValue_congr
    intro q hq
    exact he q (L.outside_a hn q (hr hq))
  refine ⟨hp,?_,(keep _ (by intro q hq; simp [hq])).trans hin.b,
    (keep _ (by intro q hq; simp [hq])).trans hin.constant,
    (keep _ (by intro q hq; simp [hq])).trans hin.carry,
    (he _ (L.outside_a hn _ (by simp))).trans hin.cin,
    (he _ (L.outside_a hn _ (by simp))).trans hin.orientation⟩
  simpa only [hin.constant,hin.a,hin.cin,Bool.toNat_false,Nat.add_zero] using hv

private theorem seed_sub_stage (L : SkywalkSeedLayout) (hn : L.wires.Nodup)
    (hx : L.constant.length=L.a.length) (hc : L.carry.length+1=L.a.length)
    (A B C : Nat) :
    Triple (SkywalkSeedValues L A B C) (subInPlace L.constant L.a L.carry L.cin)
      (SkywalkSeedValues L ((A+2^L.a.length-C)%2^L.a.length) B C) := by
  intro s m hin
  obtain ⟨hp,ho⟩ := subInPlace_spec L.constant L.a L.carry L.cin (L.core_nodup hn) hx hc C A
    s m ⟨⟨⟨hin.constant,hin.a⟩,hin.cin⟩,hin.carry⟩
  have ha : ∀ q,q∈L.b ∨ q=L.orientation → q∉wires (subInPlace L.constant L.a L.carry L.cin) := by
    intro q hq
    rw [subInPlace_wires _ _ _ _ hx hc]
    intro hm
    have hh := List.nodup_iff_count.mp hn q
    have hc' := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    simp only [SkywalkSeedLayout.wires,List.count_cons,List.count_append] at hh hc'
    rcases hq with hb|hg
    · have hb' := List.count_pos_iff.mpr hb
      omega
    · subst q
      simp only [beq_self_eq_true,if_true] at hh
      omega
  refine ⟨hp,ho.1.1.2,?_,ho.1.1.1,ho.2,ho.1.2,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => run_preserves_outside _ m s q
      (ha q (Or.inl hq)))).trans hin.b
  · exact (run_preserves_outside _ m s L.orientation (ha _ (Or.inr rfl))).trans hin.orientation

private theorem seed_small_bounds (w p x : Nat) (hw : 2≤w)
    (hp : p<2^(w-2)) (hx : x<2^(w-2)) :
    p<2^w ∧ x<2^w ∧ p+x<2^(w-1) ∧ p+x<2^w := by
  have hpow : 2^(w-1)=2^(w-2)*2 := by
    rw [show w-1=(w-2)+1 by omega,pow_succ]
  have hmono : 2^(w-1)≤2^w := Nat.pow_le_pow_right (by decide) (by omega)
  have hs : p+x<2^(w-1) := by rw [hpow]; omega
  exact ⟨by omega,by omega,hs,hs.trans_le hmono⟩

/-- Exact positive seed, including all work/control restoration and arbitrary records. -/
theorem skywalkSeed_spec (L : SkywalkSeedLayout) (w p x : Nat) (h : L.Widths w)
    (hn : L.wires.Nodup) (hw : 2≤w) (hp : p<2^(w-2)) (hx : x<2^(w-2)) :
    Triple (SkywalkSeedValues L 0 x 0) (skywalkSeed L p)
      (SkywalkSeedValues L (p+x) x 0) := by
  have hb := seed_small_bounds w p x hw hp hx
  have h1 := seed_copy_stage L hn (h.b.trans h.a.symm) 0 x 0
  simp only [Nat.zero_xor] at h1
  have h2 := seed_constant_stage L hn p x x 0 (by rw [h.constant]; exact hb.1)
  simp only [Nat.zero_xor] at h2
  have h3 := seed_add_stage L hn (h.constant.trans h.a.symm)
    (h.carry.trans h.a.symm) x x p
  rw [h.a,Nat.mod_eq_of_lt hb.2.2.2] at h3
  have h4 := seed_constant_stage L hn p (p+x) x p (by rw [h.constant]; exact hb.1)
  simp only [Nat.xor_self] at h4
  simpa only [skywalkSeed,List.append_assoc] using ((h1.seq h2).seq h3).seq h4

/-- Independent forward arithmetic cleanup; measurements are not reversed. -/
theorem skywalkUnseed_spec (L : SkywalkSeedLayout) (w p x : Nat) (h : L.Widths w)
    (hn : L.wires.Nodup) (hw : 2≤w) (hp : p<2^(w-2)) (hx : x<2^(w-2)) :
    Triple (SkywalkSeedValues L (p+x) x 0) (skywalkUnseed L p)
      (SkywalkSeedValues L 0 x 0) := by
  have hb := seed_small_bounds w p x hw hp hx
  have h1 := seed_constant_stage L hn p (p+x) x 0 (by rw [h.constant]; exact hb.1)
  simp only [Nat.zero_xor] at h1
  have h2 := seed_sub_stage L hn (h.constant.trans h.a.symm)
    (h.carry.trans h.a.symm) (p+x) x p
  rw [h.a,show p+x+2^w-p=x+2^w by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hb.2.1] at h2
  have h3 := seed_constant_stage L hn p x x p (by rw [h.constant]; exact hb.1)
  simp only [Nat.xor_self] at h3
  have h4 := seed_copy_stage L hn (h.b.trans h.a.symm) x x 0
  simp only [Nat.xor_self] at h4
  simpa only [skywalkUnseed,List.append_assoc] using ((h1.seq h2).seq h3).seq h4

/-- The seeded physical state is the false-orientation positive Stein encoding. -/
def skywalkSeedRead (L : SkywalkSeedLayout) (s : BasisState) : SkywalkRails.State :=
  ⟨signedRegValue L.a s,signedRegValue L.b s,s L.orientation⟩

theorem skywalkSeed_encode (L : SkywalkSeedLayout) (w p x : Nat) (h : L.Widths w)
    (hw : 2≤w) (hp : p<2^(w-2)) (hx : x<2^(w-2)) (s : BasisState)
    (hs : SkywalkSeedValues L (p+x) x 0 s) :
    skywalkSeedRead L s=SkywalkRails.encode false false
      ((SkywalkNat.init x p).u:Int) ((SkywalkNat.init x p).v:Int) := by
  have hb := seed_small_bounds w p x hw hp hx
  have hxsign : x<2^(w-1) := by omega
  have ha : signedRegValue L.a s=(p+x:Int) := by
    unfold signedRegValue signedDecode
    rw [h.a,hs.a]
    simp [hb.2.2.1]
  have hbs : signedRegValue L.b s=(x:Int) := by
    unfold signedRegValue signedDecode
    rw [h.b,hs.b]
    simp [hxsign]
  simp only [skywalkSeedRead,ha,hbs,hs.orientation,SkywalkNat.init,
    SkywalkRails.encode,SkywalkRails.signed,Bool.false_eq_true,if_false]
  congr 1
  omega

/-- A caller can append any clean padding to an existing input word. -/
theorem skywalkSeed_padded_value (data pad : List Wire) (x : Nat) (s : BasisState)
    (hx : regValue data s=x) (hp : regValue pad s=0) : regValue (data++pad) s=x := by
  rw [regValue_append,hx,hp]
  simp

theorem skywalkSeed_counts (L : SkywalkSeedLayout) (w p : Nat) (h : L.Widths w) :
    toffoliCount (skywalkSeed L p)=w-1 ∧ measurementCount (skywalkSeed L p)=w-1 ∧
      toffoliCount (skywalkUnseed L p)=w-1 ∧ measurementCount (skywalkUnseed L p)=w-1 := by
  have hc := copyRegister_counts none L.b L.a (h.b.trans h.a.symm)
  have hx := xorConstant_counts L.constant p
  have ha := addInPlace_counts L.constant L.a L.carry L.cin
    (h.constant.trans h.a.symm) (h.carry.trans h.a.symm)
  have hs := subInPlace_counts L.constant L.a L.carry L.cin
    (h.constant.trans h.a.symm) (h.carry.trans h.a.symm)
  simp [skywalkSeed,skywalkUnseed,toffoliCount_append,measurementCount_append,
    hc.1,hc.2,hx.1,hx.2,ha.1,ha.2,hs.1,hs.2,h.a]

theorem skywalkSeed_wires (L : SkywalkSeedLayout) (w p : Nat) (h : L.Widths w) :
    wires (skywalkSeed L p)=L.usedWires.toFinset ∧
      wires (skywalkUnseed L p)=L.usedWires.toFinset := by
  have hpos : 0<w := by have hh := h.carry; omega
  have hne : L.b.isEmpty=false := by
    cases hb : L.b with
    | nil => have hh := h.b; rw [hb] at hh; simp at hh; omega
    | cons b bs => rfl
  have hcopy := copyRegister_wires none L.b L.a (h.b.trans h.a.symm)
  rw [hne] at hcopy
  simp only [Bool.false_eq_true,if_false,Option.toList_none,List.nil_append] at hcopy
  have ha := addInPlace_wires L.constant L.a L.carry L.cin
    (h.constant.trans h.a.symm) (h.carry.trans h.a.symm)
  have hs := subInPlace_wires L.constant L.a L.carry L.cin
    (h.constant.trans h.a.symm) (h.carry.trans h.a.symm)
  have hc := xorConstant_wires_subset L.constant p
  constructor
  · simp only [skywalkSeed,wires_append,hcopy,ha]
    ext q
    have hq : q∈wires (xorConstant L.constant p) → q∈L.constant :=
      fun hh => List.mem_toFinset.mp (hc hh)
    simp only [SkywalkSeedLayout.usedWires,Finset.mem_union,List.mem_toFinset,
      List.mem_cons,List.mem_append]
    tauto
  · simp only [skywalkUnseed,wires_append,hcopy,hs]
    ext q
    have hq : q∈wires (xorConstant L.constant p) → q∈L.constant :=
      fun hh => List.mem_toFinset.mp (hc hh)
    simp only [SkywalkSeedLayout.usedWires,Finset.mem_union,List.mem_toFinset,
      List.mem_cons,List.mem_append]
    tauto

theorem skywalkSeed_frame (L : SkywalkSeedLayout) (w p : Nat) (h : L.Widths w)
    (s : State) (m : List Bool) (q : Wire) (hq : q∉L.usedWires) :
    (run (skywalkSeed L p) m s).basis q=s.basis q ∧
      (run (skywalkUnseed L p) m s).basis q=s.basis q := by
  have hs := skywalkSeed_wires L w p h
  constructor
  · apply run_preserves_outside
    rw [hs.1]
    simpa only [List.mem_toFinset] using hq
  · apply run_preserves_outside
    rw [hs.2]
    simpa only [List.mem_toFinset] using hq

/-- Exact state inverse, with independent measurement records for load/cleanup. -/
theorem skywalkSeed_roundtrip (L : SkywalkSeedLayout) (w p x : Nat) (h : L.Widths w)
    (hn : L.wires.Nodup) (hw : 2≤w) (hp : p<2^(w-2)) (hx : x<2^(w-2))
    (s : State) (m1 m2 : List Bool) (hin : SkywalkSeedValues L 0 x 0 s.basis) :
    run (skywalkUnseed L p) m2 (run (skywalkSeed L p) m1 s)=s := by
  let t := run (skywalkSeed L p) m1 s
  let u := run (skywalkUnseed L p) m2 t
  obtain ⟨hp1,ht⟩ := skywalkSeed_spec L w p x h hn hw hp hx s m1 hin
  obtain ⟨hp2,hu⟩ := skywalkUnseed_spec L w p x h hn hw hp hx t m2 ht
  have ha : ∀ q∈L.a,u.basis q=s.basis q :=
    (regValue_eq_iff _ _ _).mp (hu.a.trans hin.a.symm)
  have hb : ∀ q∈L.b,u.basis q=s.basis q :=
    (regValue_eq_iff _ _ _).mp (hu.b.trans hin.b.symm)
  have hc : ∀ q∈L.constant,u.basis q=s.basis q :=
    (regValue_eq_iff _ _ _).mp (hu.constant.trans hin.constant.symm)
  have hd : ∀ q∈L.carry,u.basis q=s.basis q :=
    (regValue_eq_iff _ _ _).mp (hu.carry.trans hin.carry.symm)
  change u=s
  apply congrArg₂ State.mk
  · exact hp2.trans hp1
  · funext q
    by_cases hqin : q=L.cin
    · subst q
      exact hu.cin.trans hin.cin.symm
    by_cases hqa : q∈L.a
    · exact ha q hqa
    by_cases hqb : q∈L.b
    · exact hb q hqb
    by_cases hqc : q∈L.constant
    · exact hc q hqc
    by_cases hqd : q∈L.carry
    · exact hd q hqd
    have hout : q∉L.usedWires := by
      simp only [SkywalkSeedLayout.usedWires,List.mem_cons,List.mem_append]
      tauto
    exact (skywalkSeed_frame L w p h t m2 q hout).2.trans
      (skywalkSeed_frame L w p h s m1 q hout).1

end ECDSAAdd.Arithmetic
