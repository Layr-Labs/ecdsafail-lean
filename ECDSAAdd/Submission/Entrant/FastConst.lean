import ECDSAAdd.Arithmetic.MeasuredCanonicalMod
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.ComparePhysical
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Baselines.SlotMapped

/-! Compare-first controlled constant modular addition.

`fastAdd` maps `x ↦ x + g·k mod p` and `fastNeg` maps `x ↦ g ? (k - x mod p) : x`.
Each computes its reduction flag with one comparison against a masked
constant, performs one plain addition of a flag-selected constant, and erases
the flag with one measured comparison.  Every scratch wire is restored. -/
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant
open Arithmetic

namespace FastConst

/-- Controlled complement: one CX from `g` onto every wire of `r`. -/
def maskedNot (g : Wire) (r : List Wire) : Program := maskedConstant g r (2^r.length-1)

theorem xorConstant_all (r : List Wire) : xorConstant r (2^r.length-1)=notRegister r := by
  induction r with
  | nil => rfl
  | cons w ws ih =>
    have hp : 0<2^ws.length := Nat.two_pow_pos _
    have e : 2^(ws.length+1)=2*2^ws.length := by rw [Nat.pow_succ]; ring
    have h1 : (2^(ws.length+1)-1)%2=1 := by rw [e]; omega
    have h2 : (2^(ws.length+1)-1)/2=2^ws.length-1 := by rw [e]; omega
    simp only [List.length_cons,xorConstant,h1,if_true,h2,ih,notRegister,List.map_cons]
    rfl

theorem maskedNot_run (g : Wire) (r : List Wire) (hg : g∉r) (s : State) (m : List Bool) :
    run (maskedNot g r) m s=if s.basis g then run (notRegister r) m s else s := by
  rw [maskedNot,maskedConstant_run g r _ hg,xorConstant_all]

variable (K : MeasuredCanonicalModLayout) (g : Wire)

def mutable : List Wire := K.src++K.out++[K.flag]

def Frame (base : BasisState) (S O : Nat) (F : Bool) (s : BasisState) : Prop :=
  regValue K.src s=S ∧ regValue K.out s=O ∧ s K.flag=F ∧ ∀q,q∉mutable K → s q=base q

/-- `x ↦ x + g·k mod p` using `3n-2` Toffolis. -/
def fastAdd (c k : Nat) : Program :=
  maskedConstant g K.src (c+k)++notRegister K.src++
  compareLt none K.src K.out K.carry K.cin K.flag++
  notRegister K.src++maskedConstant g K.src (c+k)++
  maskedConstant g K.src k++maskedConstant K.flag K.src k++maskedConstant K.flag K.src (k+c)++
  mappedAdd (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin++
  maskedConstant K.flag K.src (k+c)++maskedConstant K.flag K.src k++
  eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag++
  maskedConstant g K.src k

/-- `x ↦ g ? (k - x mod p) : x` using `3n-2` Toffolis. -/
def fastNeg (p k : Nat) : Program :=
  maskedConstant g K.src (2^K.out.length-1-k)++notRegister K.src++
  compareLt none K.src K.out K.carry K.cin K.flag++
  notRegister K.src++maskedConstant g K.src (2^K.out.length-1-k)++
  maskedNot g K.out++
  maskedConstant g K.src (k+1)++maskedConstant K.flag K.src (k+1)++
  maskedConstant K.flag K.src ((k+1+p)%2^K.out.length)++
  mappedAdd (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin++
  maskedConstant K.flag K.src ((k+1+p)%2^K.out.length)++maskedConstant K.flag K.src (k+1)++
  maskedConstant g K.src (k+1)++
  maskedConstant g K.src (2^K.out.length-1-k)++notRegister K.src++
  eraseLtChain K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag++
  notRegister K.src++maskedConstant g K.src (2^K.out.length-1-k)

section Facts
variable {K g}

private theorem cnt (hn : (g::K.wires).Nodup) (q : Wire) :
    ((g::K.wires).count q) ≤ 1 := List.nodup_iff_count_le_one.mp hn q

theorem src_nodup (hn : (g::K.wires).Nodup) : K.src.Nodup := by
  apply List.nodup_iff_count.mpr; intro q; have h := cnt hn q
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
  omega

theorem out_nodup (hn : (g::K.wires).Nodup) : K.out.Nodup := by
  apply List.nodup_iff_count.mpr; intro q; have h := cnt hn q
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
  omega

theorem g_not_mutable (hn : (g::K.wires).Nodup) : g∉mutable K := by
  intro bad; have h := cnt hn g; have b := List.count_pos_iff.mpr bad
  simp only [mutable,MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,
    List.count_nil,beq_self_eq_true,if_true] at h b
  omega

theorem g_not_src (hn : (g::K.wires).Nodup) : g∉K.src :=
  fun h => g_not_mutable hn (by simp [mutable,h])

theorem g_not_out (hn : (g::K.wires).Nodup) : g∉K.out :=
  fun h => g_not_mutable hn (by simp [mutable,h])

theorem flag_not_src (hn : (g::K.wires).Nodup) : K.flag∉K.src := by
  intro bad; have h := cnt hn K.flag; have b := List.count_pos_iff.mpr bad
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,
    List.count_nil,beq_self_eq_true,if_true] at h b
  omega

theorem flag_not_out (hn : (g::K.wires).Nodup) : K.flag∉K.out := by
  intro bad; have h := cnt hn K.flag; have b := List.count_pos_iff.mpr bad
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,
    List.count_nil,beq_self_eq_true,if_true] at h b
  omega

theorem out_not_src (hn : (g::K.wires).Nodup) (q : Wire) (hq : q∈K.out) : q∉K.src := by
  intro bad; have h := cnt hn q; have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
  omega

theorem fixed_not_mutable (hn : (g::K.wires).Nodup) (q : Wire) (hq : q∈K.carry++[K.high,K.cin]) :
    q∉mutable K := by
  intro bad; have h := cnt hn q; have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [mutable,MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,
    List.count_nil] at h a b
  omega

theorem compare_nodup (hn : (g::K.wires).Nodup) :
    (K.flag::K.cin::(K.src++K.out++K.carry)).Nodup := by
  apply List.nodup_iff_count.mpr; intro q; have h := cnt hn q
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem erase_nodup (hn : (g::K.wires).Nodup) (j : Nat) :
    (K.flag::K.cin::(K.out++K.src++K.carry.take j)).Nodup ∧
      (K.flag::K.cin::(K.src++K.out++K.carry.take j)).Nodup := by
  constructor <;>
  · apply List.nodup_iff_count.mpr; intro q; have h := cnt hn q
    have t := (List.take_sublist j K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h t ⊢
    omega

theorem add_nodup (hn : (g::K.wires).Nodup) (j : Nat) :
    (K.cin::(K.out++K.carry.take j)).Nodup ∧
      ∀q∈mappedWires (mappedRead K.src false),q∉K.cin::(K.out++K.carry.take j) := by
  rw [mappedRead_wires]
  constructor
  · apply List.nodup_iff_count.mpr; intro q; have h := cnt hn q
    have t := (List.take_sublist j K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h t ⊢
    omega
  · intro q hq bad; have h := cnt hn q; have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    have t := (List.take_sublist j K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h b t
    omega

end Facts

section Steps
variable {K g}
variable (hn : (g::K.wires).Nodup) (n : Nat) (hw : K.Widths n)
include hn hw

theorem step_mask_g (base : BasisState) (S O : Nat) (F : Bool) (v : Nat) (hv : v<2^n) :
    Triple (Frame K base S O F) (maskedConstant g K.src v)
      (Frame K base (S^^^(if base g then v else 0)) O F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct g K.src v (src_nodup hn) (g_not_src hn)
    (by rw [hw.src]; exact hv) s m
  refine ⟨hp,?_,?_,?_,?_⟩
  · rw [hval,h.1,h.2.2.2 g (g_not_mutable hn)]
  · rw [regValue_congr _ _ _ (fun q hq => he q (out_not_src hn q hq))]; exact h.2.1
  · rw [he _ (flag_not_src hn)]; exact h.2.2.1
  · intro q hq; rw [he q (fun hs => hq (by simp [mutable,hs]))]; exact h.2.2.2 q hq

theorem step_mask_flag (base : BasisState) (S O : Nat) (F : Bool) (v : Nat) (hv : v<2^n) :
    Triple (Frame K base S O F) (maskedConstant K.flag K.src v)
      (Frame K base (S^^^(if F then v else 0)) O F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct K.flag K.src v (src_nodup hn) (flag_not_src hn)
    (by rw [hw.src]; exact hv) s m
  refine ⟨hp,?_,?_,?_,?_⟩
  · rw [hval,h.1,h.2.2.1]
  · rw [regValue_congr _ _ _ (fun q hq => he q (out_not_src hn q hq))]; exact h.2.1
  · rw [he _ (flag_not_src hn)]; exact h.2.2.1
  · intro q hq; rw [he q (fun hs => hq (by simp [mutable,hs]))]; exact h.2.2.2 q hq

theorem step_not_src (base : BasisState) (S O : Nat) (F : Bool) :
    Triple (Frame K base S O F) (notRegister K.src) (Frame K base (2^n-1-S) O F) := by
  intro s m h
  rw [notRegister_correct K.src (src_nodup hn)]
  refine ⟨rfl,?_,?_,?_,?_⟩
  · change regValue K.src (fun w => if w∈K.src then !s.basis w else s.basis w)=_
    rw [regValue_congr K.src _ (fun w => !s.basis w) (by intro w hw; simp [hw]),
      regValue_complement,h.1,hw.src]
  · change regValue K.out (fun w => if w∈K.src then !s.basis w else s.basis w)=_
    rw [regValue_congr K.out _ s.basis (by intro w hw; simp [out_not_src hn w hw])]
    exact h.2.1
  · change (if K.flag∈K.src then !s.basis K.flag else s.basis K.flag)=_
    simp [flag_not_src hn,h.2.2.1]
  · intro q hq
    change (if q∈K.src then !s.basis q else s.basis q)=_
    have : q∉K.src := fun hs => hq (by simp [mutable,hs])
    simp [this,h.2.2.2 q hq]

theorem step_not_out (base : BasisState) (S O : Nat) (F : Bool) :
    Triple (Frame K base S O F) (maskedNot g K.out)
      (Frame K base S (if base g then 2^n-1-O else O) F) := by
  intro s m h
  rw [maskedNot_run g K.out (g_not_out hn)]
  have hg : s.basis g=base g := h.2.2.2 g (g_not_mutable hn)
  rw [hg]
  cases base g
  · exact ⟨rfl,h⟩
  · rw [notRegister_correct K.out (out_nodup hn)]
    refine ⟨rfl,?_,?_,?_,?_⟩
    · change regValue K.src (fun w => if w∈K.out then !s.basis w else s.basis w)=_
      rw [regValue_congr K.src _ s.basis (by
        intro w hw; have : w∉K.out := fun h => out_not_src hn w h hw
        simp [this])]
      exact h.1
    · change regValue K.out (fun w => if w∈K.out then !s.basis w else s.basis w)=_
      rw [regValue_congr K.out _ (fun w => !s.basis w) (by intro w hw; simp [hw]),
        regValue_complement,h.2.1,hw.out]
      simp
    · change (if K.flag∈K.out then !s.basis K.flag else s.basis K.flag)=_
      simp [flag_not_out hn,h.2.2.1]
    · intro q hq
      change (if q∈K.out then !s.basis q else s.basis q)=_
      have : q∉K.out := fun hs => hq (by simp [mutable,hs])
      simp [this,h.2.2.2 q hq]

variable (base : BasisState) (hcarry : ∀q∈K.carry,base q=false) (hcin : base K.cin=false)
include hcarry hcin

theorem step_compare (S O : Nat) (F : Bool) :
    Triple (Frame K base S O F) (compareLt none K.src K.out K.carry K.cin K.flag)
      (Frame K base S O (F^^decide (S<O))) := by
  intro s m h
  have cl (q : Wire) (hq : q∈K.carry) : s.basis q=false :=
    (h.2.2.2 q (fixed_not_mutable hn q (by simp [hq]))).trans (hcarry q hq)
  have ci : s.basis K.cin=false :=
    (h.2.2.2 K.cin (fixed_not_mutable hn K.cin (by simp))).trans hcin
  obtain ⟨hp,he,hv⟩ := compareLt_correct none K.src K.out K.carry K.cin K.flag (compare_nodup hn)
    (by simp) (by rw [hw.src,hw.out]) (by rw [hw.carry,hw.out]) s m ci cl
  have ne (q : Wire) (hq : q∈K.src∨q∈K.out) : q≠K.flag := by
    rintro rfl; rcases hq with hq|hq
    · exact flag_not_src hn hq
    · exact flag_not_out hn hq
  refine ⟨hp,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ _ (fun q hq => he q (ne q (Or.inl hq)))]; exact h.1
  · rw [regValue_congr _ _ _ (fun q hq => he q (ne q (Or.inr hq)))]; exact h.2.1
  · rw [hv,h.2.2.1,h.1,h.2.1]; simp [controlValue]
  · intro q hq
    rw [he q (fun e => hq (by simp [mutable,e]))]; exact h.2.2.2 q hq

theorem step_add (npos : 0<n) (S O : Nat) (F : Bool) :
    Triple (Frame K base S O F)
      (mappedAdd (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin)
      (Frame K base S ((S+O)%2^n) F) := by
  intro s m h
  have cl (q : Wire) (hq : q∈K.carry.take (K.out.length-1)) : s.basis q=false := by
    have hq' := List.mem_of_mem_take hq
    exact (h.2.2.2 q (fixed_not_mutable hn q (by simp [hq']))).trans (hcarry q hq')
  have ci : s.basis K.cin=false :=
    (h.2.2.2 K.cin (fixed_not_mutable hn K.cin (by simp))).trans hcin
  have nd := add_nodup hn (K.out.length-1)
  obtain ⟨hp,he,hv⟩ := mappedAdd_correct (mappedRead K.src false) K.out
    (K.carry.take (K.out.length-1)) K.cin nd.1 nd.2
    (by rw [mappedRead_length,hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega) s m cl
  refine ⟨hp,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ _ (fun q hq => he q (fun ho => out_not_src hn q ho hq))]; exact h.1
  · rw [hv,mappedRead_value,h.1,h.2.1,ci,hw.out]; simp
  · rw [he _ (flag_not_out hn)]; exact h.2.2.1
  · intro q hq
    rw [he q (fun e => hq (by simp [mutable,e]))]; exact h.2.2.2 q hq

theorem step_erase_os (npos : 0<n) (S O : Nat) (F : Bool) (hF : F=decide (O<S)) :
    Triple (Frame K base S O F)
      (eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag)
      (Frame K base S O false) := by
  intro s m h
  have cl (q : Wire) (hq : q∈K.carry.take (K.out.length-1)) : s.basis q=false := by
    have hq' := List.mem_of_mem_take hq
    exact (h.2.2.2 q (fixed_not_mutable hn q (by simp [hq']))).trans (hcarry q hq')
  have ci : s.basis K.cin=false :=
    (h.2.2.2 K.cin (fixed_not_mutable hn K.cin (by simp))).trans hcin
  have r := eraseLtChain_correct K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
    (erase_nodup hn _).1 (by rw [hw.src,hw.out]) (by simp [hw.carry,hw.out,hw.src]; omega) s m cl
    (by rw [h.2.2.1,h.1,h.2.1,ci,hF]; simp)
  rw [r]
  have ne (q : Wire) (hq : q∈K.src∨q∈K.out) : q≠K.flag := by
    rintro rfl; rcases hq with hq|hq
    · exact flag_not_src hn hq
    · exact flag_not_out hn hq
  refine ⟨rfl,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,ne q (Or.inl hq)])]; exact h.1
  · rw [regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,ne q (Or.inr hq)])]; exact h.2.1
  · simp [writeBit]
  · intro q hq
    have : q≠K.flag := fun e => hq (by simp [mutable,e])
    simp [writeBit,this,h.2.2.2 q hq]

theorem step_erase_so (npos : 0<n) (S O : Nat) (F : Bool) (hF : F=decide (S<O)) :
    Triple (Frame K base S O F)
      (eraseLtChain K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag)
      (Frame K base S O false) := by
  intro s m h
  have cl (q : Wire) (hq : q∈K.carry.take (K.out.length-1)) : s.basis q=false := by
    have hq' := List.mem_of_mem_take hq
    exact (h.2.2.2 q (fixed_not_mutable hn q (by simp [hq']))).trans (hcarry q hq')
  have ci : s.basis K.cin=false :=
    (h.2.2.2 K.cin (fixed_not_mutable hn K.cin (by simp))).trans hcin
  have r := eraseLtChain_correct K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag
    (erase_nodup hn _).2 (by rw [hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega) s m cl
    (by rw [h.2.2.1,h.1,h.2.1,ci,hF]; simp)
  rw [r]
  have ne (q : Wire) (hq : q∈K.src∨q∈K.out) : q≠K.flag := by
    rintro rfl; rcases hq with hq|hq
    · exact flag_not_src hn hq
    · exact flag_not_out hn hq
  refine ⟨rfl,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,ne q (Or.inl hq)])]; exact h.1
  · rw [regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,ne q (Or.inr hq)])]; exact h.2.1
  · simp [writeBit]
  · intro q hq
    have : q≠K.flag := fun e => hq (by simp [mutable,e])
    simp [writeBit,this,h.2.2.2 q hq]

end Steps


section Main
variable {K g}
variable (hn : (g::K.wires).Nodup) (n : Nat) (hw : K.Widths n) (npos : 0<n)
  (base : BasisState) (hcarry : ∀q∈K.carry,base q=false) (hcin : base K.cin=false)
include hn hw npos hcarry hcin

theorem fastAdd_triple (c p k : Nat) (hpc : p+c=2^n) (hk : k<p) (X : Nat) (hX : X<p) :
    Triple (Frame K base 0 X false) (fastAdd K g c k)
      (Frame K base 0 ((X+(if base g then k else 0))%p) false) := by
  have hck : c+k<2^n := by omega
  have hk2 : k<2^n := by omega
  have hkc : k+c<2^n := by omega
  unfold fastAdd
  refine Triple.conseq (fun _ h => h) (((((((((((((
    step_mask_g hn n hw base 0 X false (c+k) hck).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_compare hn n hw base hcarry hcin _ _ _)).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_mask_g hn n hw base _ _ _ (c+k) hck)).seq
    (step_mask_g hn n hw base _ _ _ k hk2)).seq
    (step_mask_flag hn n hw base _ _ _ k hk2)).seq
    (step_mask_flag hn n hw base _ _ _ (k+c) hkc)).seq
    (step_add hn n hw base hcarry hcin npos _ _ _)).seq
    (step_mask_flag hn n hw base _ _ _ (k+c) hkc)).seq
    (step_mask_flag hn n hw base _ _ _ k hk2)).seq
    (step_erase_os hn n hw base hcarry hcin npos _ _ _ ?hF)).seq
    (step_mask_g hn n hw base _ _ _ k hk2)) ?post
  case hF =>
    cases hG : base g
    · simp; omega
    · have e1 : 2^n-1-(2^n-1-(c+k))=c+k := by omega
      by_cases hP : 2^n-1-(c+k)<X
      · have w : (k+c+X)%2^n=X+k-p := by
          rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]; omega
        simp [hP,e1,w]; omega
      · have w : (k+X)%2^n=X+k := by rw [Nat.mod_eq_of_lt (by omega)]; omega
        simp [hP,e1,w]
  case post =>
    intro s h
    refine ⟨h.1.trans ?_,h.2.1.trans ?_,h.2.2.1,h.2.2.2⟩
    · cases hG : base g
      · simp
      · by_cases hP : 2^n-1-(c+k)<X <;> simp [hP] <;> omega
    · cases hG : base g
      · have hP : ¬2^n-1<X := by omega
        simp [hP,Nat.mod_eq_of_lt hX,Nat.mod_eq_of_lt (show X<2^n by omega)]
      · have e1 : 2^n-1-(2^n-1-(c+k))=c+k := by omega
        by_cases hP : 2^n-1-(c+k)<X
        · have w : (k+c+X)%2^n=X+k-p := by
            rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]; omega
          have v : (X+k)%p=X+k-p := by
            rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
          simp [hP,e1,w,v]
        · have w : (k+X)%2^n=X+k := by rw [Nat.mod_eq_of_lt (by omega)]; omega
          have v : (X+k)%p=X+k := Nat.mod_eq_of_lt (by omega)
          simp [hP,e1,w,v]

theorem fastNeg_triple (p k : Nat) (hp : p<2^n) (hk : k<p) (X : Nat) (hX : X<p) :
    Triple (Frame K base 0 X false) (fastNeg K g p k)
      (Frame K base 0 (if base g then (k+p-X)%p else X) false) := by
  have hN : K.out.length=n := hw.out
  have hA : 2^K.out.length-1-k<2^n := by rw [hN]; omega
  have hk1 : k+1<2^n := by omega
  have he : (k+1+p)%2^K.out.length<2^n := by rw [hN]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold fastNeg
  refine Triple.conseq (fun _ h => h) ((((((((((((((((((
    step_mask_g hn n hw base 0 X false _ hA).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_compare hn n hw base hcarry hcin _ _ _)).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_mask_g hn n hw base _ _ _ _ hA)).seq
    (step_not_out hn n hw base _ _ _)).seq
    (step_mask_g hn n hw base _ _ _ _ hk1)).seq
    (step_mask_flag hn n hw base _ _ _ _ hk1)).seq
    (step_mask_flag hn n hw base _ _ _ _ he)).seq
    (step_add hn n hw base hcarry hcin npos _ _ _)).seq
    (step_mask_flag hn n hw base _ _ _ _ he)).seq
    (step_mask_flag hn n hw base _ _ _ _ hk1)).seq
    (step_mask_g hn n hw base _ _ _ _ hk1)).seq
    (step_mask_g hn n hw base _ _ _ _ hA)).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_erase_so hn n hw base hcarry hcin npos _ _ _ ?hF)).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_mask_g hn n hw base _ _ _ _ hA)) ?post
  case hF =>
    rw [hN]
    cases hG : base g
    · simp; omega
    · have e1 : 2^n-1-(2^n-1-k)=k := by omega
      have e2 : 2^n-1-(2^n-1-(2^n-1-k))=2^n-1-k := by omega
      by_cases hP : k<X
      · have w : ((k+1+p)%2^n+(2^n-1-X))%2^n=k+p-X := by
          rw [Nat.mod_add_mod,show k+1+p+(2^n-1-X)=(k+p-X)+2^n by omega,Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        simp [hP,e1,e2,w]; omega
      · have w : (k+1+(2^n-1-X))%2^n=k-X := by
          rw [show k+1+(2^n-1-X)=(k-X)+2^n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
        simp [hP,e1,e2,w]
  case post =>
    intro s h
    refine ⟨h.1.trans ?_,h.2.1.trans ?_,h.2.2.1,h.2.2.2⟩
    · rw [hN]
      cases hG : base g
      · simp
      · have e1 : 2^n-1-(2^n-1-k)=k := by omega
        have e2 : 2^n-1-(2^n-1-(2^n-1-k))=2^n-1-k := by omega
        by_cases hP : k<X <;> simp [hP,e1,e2]
    · rw [hN]
      cases hG : base g
      · have hP : ¬2^n-1<X := by omega
        simp [hP,Nat.mod_eq_of_lt (show X<2^n by omega)]
      · have e1 : 2^n-1-(2^n-1-k)=k := by omega
        have e2 : 2^n-1-(2^n-1-(2^n-1-k))=2^n-1-k := by omega
        by_cases hP : k<X
        · have w : ((k+1+p)%2^n+(2^n-1-X))%2^n=k+p-X := by
            rw [Nat.mod_add_mod,show k+1+p+(2^n-1-X)=(k+p-X)+2^n by omega,Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)]
          have v : (k+p-X)%p=k+p-X := Nat.mod_eq_of_lt (by omega)
          simp [hP,e1,e2,w,v]
        · have w : (k+1+(2^n-1-X))%2^n=k-X := by
            rw [show k+1+(2^n-1-X)=(k-X)+2^n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
          have v : (k+p-X)%p=k-X := by
            rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]; omega
          simp [hP,e1,e2,w,v]

end Main

section Wrappers
variable {K g}

/-- Run-form contract from a frame triple: phase, output value, and every
non-output site restored. -/
theorem run_of_triple (P : Program) (X Y : Nat) (s : State)
    (hT : Triple (Frame K s.basis 0 X false) P (Frame K s.basis 0 Y false))
    (hs : regValue K.src s.basis=0) (hx : regValue K.out s.basis=X) (hf : s.basis K.flag=false)
    (m : List Bool) :
    (run P m s).phase=s.phase ∧ regValue K.out (run P m s).basis=Y ∧
      ∀q,q∉K.out → (run P m s).basis q=s.basis q := by
  obtain ⟨hp,h⟩ := hT s m ⟨hs,hx,hf,fun _ _ => rfl⟩
  refine ⟨hp,h.2.1,?_⟩
  intro q hq
  by_cases hsrc : q∈K.src
  · rw [(regValue_zero _ _).mp h.1 q hsrc,(regValue_zero _ _).mp hs q hsrc]
  · by_cases hfl : q=K.flag
    · subst q; rw [h.2.2.1,hf]
    · exact h.2.2.2 q (by simp [mutable,hsrc,hq,hfl])

theorem fastAdd_correct (hn : (g::K.wires).Nodup) (n c p k : Nat) (hw : K.Widths n) (npos : 0<n)
    (hpc : p+c=2^n) (hk : k<p) (X : Nat) (hX : X<p) (s : State) (m : List Bool)
    (hs : regValue K.src s.basis=0) (hx : regValue K.out s.basis=X) (hf : s.basis K.flag=false)
    (hc : ∀q∈K.carry,s.basis q=false) (hi : s.basis K.cin=false) :
    (run (fastAdd K g c k) m s).phase=s.phase ∧
    regValue K.out (run (fastAdd K g c k) m s).basis=(X+(if s.basis g then k else 0))%p ∧
    ∀q,q∉K.out → (run (fastAdd K g c k) m s).basis q=s.basis q :=
  run_of_triple _ X _ s (fastAdd_triple hn n hw npos s.basis hc hi c p k hpc hk X hX) hs hx hf m

theorem fastNeg_correct (hn : (g::K.wires).Nodup) (n p k : Nat) (hw : K.Widths n) (npos : 0<n)
    (hp : p<2^n) (hk : k<p) (X : Nat) (hX : X<p) (s : State) (m : List Bool)
    (hs : regValue K.src s.basis=0) (hx : regValue K.out s.basis=X) (hf : s.basis K.flag=false)
    (hc : ∀q∈K.carry,s.basis q=false) (hi : s.basis K.cin=false) :
    (run (fastNeg K g p k) m s).phase=s.phase ∧
    regValue K.out (run (fastNeg K g p k) m s).basis=(if s.basis g then (k+p-X)%p else X) ∧
    ∀q,q∉K.out → (run (fastNeg K g p k) m s).basis q=s.basis q :=
  run_of_triple _ X _ s (fastNeg_triple hn n hw npos s.basis hc hi p k hp hk X hX) hs hx hf m

theorem fastAdd_counts (n c k : Nat) (hw : K.Widths n) (npos : 0<n) :
    toffoliCount (fastAdd K g c k)=3*n-2 ∧ measurementCount (fastAdd K g c k)=3*n-1 := by
  have m1 := maskedConstant_counts g K.src (c+k)
  have m2 := maskedConstant_counts g K.src k
  have m3 := maskedConstant_counts K.flag K.src k
  have m4 := maskedConstant_counts K.flag K.src (k+c)
  have nr := notRegister_counts K.src
  have cmp := (compareLt_counts none K.src K.out K.carry K.cin K.flag (by rw [hw.src,hw.out])
    (by rw [hw.carry,hw.out]))
  have ad := mappedAdd_counts (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin
    (by rw [mappedRead_length,hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega)
  have er := eraseLtChain_counts K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
    (by rw [hw.src,hw.out]) (by simp [hw.carry,hw.out,hw.src]; omega)
  simp only [fastAdd,toffoliCount_append,measurementCount_append,m1.1,m1.2,m2.1,m2.2,m3.1,m3.2,
    m4.1,m4.2,nr.1,nr.2,cmp.1,cmp.2.1,ad.1,ad.2,er.1,er.2]
  simp only [hw.src,hw.out,Option.isSome_none,Bool.false_eq_true,if_false]
  omega

theorem fastNeg_counts (n p k : Nat) (hw : K.Widths n) (npos : 0<n) :
    toffoliCount (fastNeg K g p k)=3*n-2 ∧ measurementCount (fastNeg K g p k)=3*n-1 := by
  have m1 := maskedConstant_counts g K.src (2^K.out.length-1-k)
  have m2 := maskedConstant_counts g K.src (k+1)
  have m3 := maskedConstant_counts K.flag K.src (k+1)
  have m4 := maskedConstant_counts K.flag K.src ((k+1+p)%2^K.out.length)
  have m5 := maskedConstant_counts g K.out (2^K.out.length-1)
  have nr := notRegister_counts K.src
  have cmp := (compareLt_counts none K.src K.out K.carry K.cin K.flag (by rw [hw.src,hw.out])
    (by rw [hw.carry,hw.out]))
  have ad := mappedAdd_counts (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin
    (by rw [mappedRead_length,hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega)
  have er := eraseLtChain_counts K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag
    (by rw [hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega)
  simp only [fastNeg,maskedNot,toffoliCount_append,measurementCount_append,m1.1,m1.2,m2.1,m2.2,
    m3.1,m3.2,m4.1,m4.2,m5.1,m5.2,nr.1,nr.2,cmp.1,cmp.2.1,ad.1,ad.2,er.1,er.2]
  simp only [hw.src,hw.out,Option.isSome_none,Bool.false_eq_true,if_false]
  omega

theorem parts_support (hw : ∃ n, K.Widths n) :
    (∀ c'∈g::K.wires,∀ v,wires (maskedConstant c' K.src v)⊆(g::K.wires).toFinset) ∧
    (∀ v,wires (maskedConstant g K.out v)⊆(g::K.wires).toFinset) ∧
    wires (notRegister K.src)⊆(g::K.wires).toFinset ∧
    wires (compareLt none K.src K.out K.carry K.cin K.flag)⊆(g::K.wires).toFinset ∧
    wires (mappedAdd (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin)⊆
      (g::K.wires).toFinset ∧
    wires (eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag)⊆
      (g::K.wires).toFinset ∧
    wires (eraseLtChain K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag)⊆
      (g::K.wires).toFinset := by
  obtain ⟨n,hw⟩ := hw
  have tk (q : Wire) (h : q∈K.carry.take (K.out.length-1)) : q∈K.carry := List.mem_of_mem_take h
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro c' hc' v q hq
    have h' := List.mem_toFinset.mp (maskedConstant_wires_subset c' K.src v hq)
    apply List.mem_toFinset.mpr
    simp only [List.mem_cons] at h'
    rcases h' with rfl|h'
    · exact hc'
    · simp [MeasuredCanonicalModLayout.wires,h']
  · intro v q hq
    have h' := List.mem_toFinset.mp (maskedConstant_wires_subset g K.out v hq)
    apply List.mem_toFinset.mpr
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append] at h' ⊢
    tauto
  · intro q hq
    rw [notRegister_wires] at hq
    apply List.mem_toFinset.mpr
    simp only [List.mem_toFinset] at hq
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append]
    tauto
  · intro q hq
    rw [(compareLt_wires none K.src K.out K.carry K.cin K.flag (by rw [hw.src,hw.out])
      (by rw [hw.carry,hw.out])).1] at hq
    apply List.mem_toFinset.mpr
    simp only [List.mem_toFinset,Option.toList_none,List.nil_append,List.mem_cons,
      List.mem_append] at hq
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
      or_false]
    tauto
  · intro q hq
    have h' := List.mem_toFinset.mp (mappedAdd_wires_subset _ _ _ _ hq)
    rw [mappedRead_wires] at h'
    apply List.mem_toFinset.mpr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h'
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
      or_false]
    have := tk q
    tauto
  · intro q hq
    have h' := List.mem_toFinset.mp (eraseLtChain_wires_subset _ _ _ _ _ hq)
    apply List.mem_toFinset.mpr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h'
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
      or_false]
    have := tk q
    tauto
  · intro q hq
    have h' := List.mem_toFinset.mp (eraseLtChain_wires_subset _ _ _ _ _ hq)
    apply List.mem_toFinset.mpr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h'
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
      or_false]
    have := tk q
    tauto

theorem fastAdd_support (c k : Nat) (hw : ∃ n, K.Widths n) :
    wires (fastAdd K g c k)⊆(g::K.wires).toFinset := by
  obtain ⟨hm,_,hnr,hc,ha,he,_⟩ := parts_support (K:=K) (g:=g) hw
  have hg : g∈g::K.wires := List.mem_cons_self ..
  have hf : K.flag∈g::K.wires := by simp [MeasuredCanonicalModLayout.wires]
  simp only [fastAdd,wires_append]
  repeat' (first | exact hm _ hg _ | exact hm _ hf _ | exact hnr | exact hc | exact ha | exact he | apply Finset.union_subset)

theorem fastNeg_support (p k : Nat) (hw : ∃ n, K.Widths n) :
    wires (fastNeg K g p k)⊆(g::K.wires).toFinset := by
  obtain ⟨hm,ho,hnr,hc,ha,_,he⟩ := parts_support (K:=K) (g:=g) hw
  have hg : g∈g::K.wires := List.mem_cons_self ..
  have hf : K.flag∈g::K.wires := by simp [MeasuredCanonicalModLayout.wires]
  simp only [fastNeg,maskedNot,wires_append]
  repeat' (first | exact hm _ hg _ | exact hm _ hf _ | exact ho _ | exact hnr | exact hc | exact ha | exact he | apply Finset.union_subset)

theorem fastAdd_physical (hn : (g::K.wires).Nodup) (c k : Nat) : GatePhysical (fastAdd K g c k) := by
  have m1 := maskedConstant_physical g K.src (c+k) (g_not_src hn)
  have m2 := maskedConstant_physical g K.src k (g_not_src hn)
  have m3 := maskedConstant_physical K.flag K.src k (flag_not_src hn)
  have m4 := maskedConstant_physical K.flag K.src (k+c) (flag_not_src hn)
  have nr := notRegister_physical K.src
  have cp := compareLt_physical none K.src K.out K.carry K.cin K.flag (by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count_le_one.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega) (by simp)
  have nd := add_nodup hn (K.out.length-1)
  have ap := mappedAdd_physical (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin
    (by simpa using nd.1) (by
      intro b hb q hq
      apply nd.2 q
      simp only [mappedWires,List.mem_flatMap]
      exact ⟨b,hb,by simpa using hq⟩)
  have ep := eraseLtChain_physical K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag (by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count_le_one.mp hn q
    have t := (List.take_sublist (K.out.length-1) K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h t ⊢
    omega)
  simp only [fastAdd,gatePhysical_append]
  tauto

theorem fastNeg_physical (hn : (g::K.wires).Nodup) (p k : Nat) : GatePhysical (fastNeg K g p k) := by
  have m1 := maskedConstant_physical g K.src (2^K.out.length-1-k) (g_not_src hn)
  have m2 := maskedConstant_physical g K.src (k+1) (g_not_src hn)
  have m3 := maskedConstant_physical K.flag K.src (k+1) (flag_not_src hn)
  have m4 := maskedConstant_physical K.flag K.src ((k+1+p)%2^K.out.length) (flag_not_src hn)
  have m5 := maskedConstant_physical g K.out (2^K.out.length-1) (g_not_out hn)
  have nr := notRegister_physical K.src
  have cp := compareLt_physical none K.src K.out K.carry K.cin K.flag (by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count_le_one.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega) (by simp)
  have nd := add_nodup hn (K.out.length-1)
  have ap := mappedAdd_physical (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin
    (by simpa using nd.1) (by
      intro b hb q hq
      apply nd.2 q
      simp only [mappedWires,List.mem_flatMap]
      exact ⟨b,hb,by simpa using hq⟩)
  have ep := eraseLtChain_physical K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag (by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count_le_one.mp hn q
    have t := (List.take_sublist (K.out.length-1) K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h t ⊢
    omega)
  simp only [fastNeg,maskedNot,gatePhysical_append]
  tauto

theorem fastAdd_gateSlots_le (n c k : Nat) (hw : K.Widths n) :
    Challenge.gateSlots (fastAdd K g c k) ≤ 60*n+8 := by
  have m1 := Baselines.maskedConstant_gateSlots_le g K.src (c+k)
  have m2 := Baselines.maskedConstant_gateSlots_le g K.src k
  have m3 := Baselines.maskedConstant_gateSlots_le K.flag K.src k
  have m4 := Baselines.maskedConstant_gateSlots_le K.flag K.src (k+c)
  have cp := Baselines.compareLt_gateSlots_le none K.src K.out K.carry K.cin K.flag
  have ap := Baselines.mappedAdd_gateSlots_le (mappedRead K.src false) K.out
    (K.carry.take (K.out.length-1)) K.cin
  have ep := Baselines.eraseLt_gateSlots_le K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
  rw [mappedRead_length] at ap
  simp only [fastAdd,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
  have ep2 := ep.trans (le_of_eq (show 14*K.out.length=14*n by rw [hw.out]))
  have cp2 := cp.trans (le_of_eq (show 10*K.src.length+2*K.out.length+4=12*n+4 by
    rw [hw.src,hw.out]; ring))
  rw [hw.src] at m1 m2 m3 m4 ap ⊢
  omega

theorem fastNeg_gateSlots_le (n p k : Nat) (hw : K.Widths n) :
    Challenge.gateSlots (fastNeg K g p k) ≤ 70*n+8 := by
  have m1 := Baselines.maskedConstant_gateSlots_le g K.src (2^K.out.length-1-k)
  have m2 := Baselines.maskedConstant_gateSlots_le g K.src (k+1)
  have m3 := Baselines.maskedConstant_gateSlots_le K.flag K.src (k+1)
  have m4 := Baselines.maskedConstant_gateSlots_le K.flag K.src ((k+1+p)%2^K.out.length)
  have m5 := Baselines.maskedConstant_gateSlots_le g K.out (2^K.out.length-1)
  have cp := Baselines.compareLt_gateSlots_le none K.src K.out K.carry K.cin K.flag
  have ap := Baselines.mappedAdd_gateSlots_le (mappedRead K.src false) K.out
    (K.carry.take (K.out.length-1)) K.cin
  have ep := Baselines.eraseLt_gateSlots_le K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag
  rw [mappedRead_length] at ap
  simp only [fastNeg,maskedNot,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
  have m52 := m5.trans (le_of_eq (show K.out.length=n by rw [hw.out]))
  have cp2 := cp.trans (le_of_eq (show 10*K.src.length+2*K.out.length+4=12*n+4 by
    rw [hw.src,hw.out]; ring))
  rw [hw.src] at m1 m2 m3 m4 ap ep ⊢
  omega

end Wrappers

end FastConst
end ECDSAAdd.Entrant
