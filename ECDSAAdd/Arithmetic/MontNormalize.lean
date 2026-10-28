import ECDSAAdd.Arithmetic.MontConstant
import ECDSAAdd.Arithmetic.ModUnaryResources

namespace ECDSAAdd.Arithmetic

private theorem maskedConstant_frame (subtract : Bool) (L : MontStageLayout) (K : Nat)
    (hnd : (L.flag::L.cin::(L.table++L.acc++L.carry)).Nodup)
    (ht : L.table.length=L.acc.length) (hc : L.carry.length+1=L.acc.length)
    (hK : K<2^L.table.length) (s : State) (m : List Bool)
    (hz : regValue L.table s.basis=0) (hca : regValue L.carry s.basis=0)
    (hci : s.basis L.cin=false) :
    let circuit := if subtract then maskedSubConst L.flag L.table L.acc L.carry L.cin K
      else maskedAddConst L.flag L.table L.acc L.carry L.cin K
    (run circuit m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run circuit m s).basis w=s.basis w) ∧
    regValue L.acc (run circuit m s).basis=(if subtract then
      (regValue L.acc s.basis+2^L.acc.length-(if s.basis L.flag then K else 0))%2^L.acc.length
      else (regValue L.acc s.basis+(if s.basis L.flag then K else 0))%2^L.acc.length) := by
  let circuit := if subtract then maskedSubConst L.flag L.table L.acc L.carry L.cin K
      else maskedAddConst L.flag L.table L.acc L.carry L.cin K
  have h : (run circuit m s).phase=s.phase ∧
      (run circuit m s).basis L.flag=s.basis L.flag ∧
      regValue L.table (run circuit m s).basis=0 ∧
      regValue L.acc (run circuit m s).basis=(if subtract then
        (regValue L.acc s.basis+2^L.acc.length-(if s.basis L.flag then K else 0))%2^L.acc.length
        else (regValue L.acc s.basis+(if s.basis L.flag then K else 0))%2^L.acc.length) ∧
      (run circuit m s).basis L.cin=false ∧ regValue L.carry (run circuit m s).basis=0 := by
    cases subtract with
    | false =>
      have hh := maskedAddConst_spec L.flag L.cin L.table L.acc L.carry hnd ht hc K hK
        (s.basis L.flag) (regValue L.acc s.basis) s m ⟨⟨⟨⟨rfl,hz⟩,rfl⟩,hci⟩,hca⟩
      exact ⟨hh.1,hh.2.1.1.1.1,hh.2.1.1.1.2,hh.2.1.1.2,hh.2.1.2,hh.2.2⟩
    | true =>
      have hh := maskedSubConst_spec L.flag L.cin L.table L.acc L.carry hnd ht hc K hK
        (s.basis L.flag) (regValue L.acc s.basis) s m ⟨⟨⟨⟨rfl,hz⟩,rfl⟩,hci⟩,hca⟩
      exact ⟨hh.1,hh.2.1.1.1.1,hh.2.1.1.1.2,hh.2.1.1.2,hh.2.1.2,hh.2.2⟩
  refine ⟨h.1,?_,h.2.2.2.1⟩
  intro w hw
  by_cases hf : w=L.flag
  · subst w; exact h.2.1
  by_cases hcin : w=L.cin
  · subst w; exact h.2.2.2.2.1.trans hci.symm
  by_cases htw : w∈L.table
  · exact (regValue_eq_iff L.table _ _).mp (h.2.2.1.trans hz.symm) w htw
  by_cases hcw : w∈L.carry
  · exact (regValue_eq_iff L.carry _ _).mp (h.2.2.2.2.2.trans hca.symm) w hcw
  have hwires : wires circuit ⊆ (L.flag::L.cin::(L.table++L.acc++L.carry)).toFinset := by
    have hh := maskedConst_wires_subset L.flag L.table L.acc L.carry L.cin K ht hc
    cases subtract with
    | false => exact hh.1
    | true => exact hh.2
  apply run_preserves_outside
  intro hh
  have := List.mem_toFinset.mp (hwires hh)
  simp [hf,hcin,htw,hw,hcw] at this

/-- W=261 时，a<2p、p<2^256 保证减 p 的最高位恰为借位。 -/
theorem montNormalize_arithmetic (p A : Nat) (hp : p<2^256) (hA : A<2*p) :
    let B := (A+2^261-p)%2^261
    (B/2^260)%2=(if A<p then 1 else 0) ∧
    (B+(if A<p then p else 0))%2^261=A%p := by
  dsimp only
  have hAfit : A<2^261 := by omega
  by_cases h : A<p
  · have hB : (A+2^261-p)%2^261=A+2^261-p := Nat.mod_eq_of_lt (by omega)
    simp only [hB,if_pos h]
    constructor
    · omega
    · rw [show A+2^261-p+p=A+2^261 by omega,Nat.add_mod_right,
        Nat.mod_eq_of_lt hAfit,Nat.mod_eq_of_lt h]
  · have hB : (A+2^261-p)%2^261=A-p := by
      rw [show A+2^261-p=(A-p)+2^261 by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    simp only [hB,if_neg h]
    constructor
    · omega
    · rw [Nat.add_zero,Nat.mod_eq_of_lt (by omega)]
      have hm : A%p=A-p := by
        conv_lhs => rw [show A=(A-p)+p by omega]
        rw [Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
      exact hm.symm


/-- 保存借位的规范化：仅 acc/flag 改变，flag 记录 A<p，其他位逐线保持。 -/
theorem montNormalize_correct (L : MontStageLayout) (p A : Nat)
    (hnd : (L.flag::L.cin::(L.table++L.acc++L.carry)).Nodup)
    (ht : L.table.length=L.acc.length) (hc : L.carry.length+1=L.acc.length)
    (hw : L.acc.length=261) (hp : p<2^256) (hA : A<2*p)
    (s : State) (m : List Bool) (ha : regValue L.acc s.basis=A)
    (hz : regValue L.table s.basis=0) (hca : regValue L.carry s.basis=0)
    (hci : s.basis L.cin=false) (hf : s.basis L.flag=false) :
    (run (montNormalize L p) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w≠L.flag → (run (montNormalize L p) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montNormalize L p) m s).basis=A%p ∧
    (run (montNormalize L p) m s).basis L.flag=decide (A<p) := by
  have hK : p<2^L.table.length := by rw [ht,hw]; omega
  have hn := List.nodup_iff_count.mp hnd
  have flagA : L.flag∉L.acc := by
    intro hh; have h := hn L.flag; have h1 := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
  have cinA : L.cin∉L.acc := by
    intro hh; have h := hn L.cin; have h1 := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
  have cinF : L.cin≠L.flag := by
    intro hh; have h := hn L.cin
    simp only [hh,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
  have tableA : L.table.Disjoint L.acc := by
    apply List.disjoint_left.mpr; intro w hw' ht'
    have h := hn w; have h1 := List.count_pos_iff.mpr hw'; have h2 := List.count_pos_iff.mpr ht'
    simp only [List.count_cons,List.count_append] at h; omega
  have carryA : L.carry.Disjoint L.acc := by
    apply List.disjoint_left.mpr; intro w hw' ht'
    have h := hn w; have h1 := List.count_pos_iff.mpr hw'; have h2 := List.count_pos_iff.mpr ht'
    simp only [List.count_cons,List.count_append] at h; omega
  have outsideF (r : List Wire) (hr : r=L.table ∨ r=L.carry ∨ r=L.acc) : ∀ w∈r, w≠L.flag := by
    intro w hw' he; subst w
    have h := hn L.flag; have h1 := List.count_pos_iff.mpr hw'
    rcases hr with rfl|rfl|rfl <;>
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h <;> omega
  let s1 := run (montConstantSub L p) m s
  let m1 := m.drop (measurementCount (montConstantSub L p))
  let copy : Program := [.CX (L.acc.getD 260 L.flag) L.flag]
  let s2 := run copy m1 s1
  have h1 := montConstantSub_correct L p (List.nodup_cons.mp hnd).2 ht hc hK s m hz hca hci
  have keep1 (r : List Wire) (hr : r.Disjoint L.acc) : regValue r s1.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw' => h1.2.1 w (List.disjoint_left.mp hr hw'))
  have va1 : regValue L.acc s1.basis=(A+2^261-p)%2^261 := by simpa only [ha,hw] using h1.2.2
  have f1 : s1.basis L.flag=false := (h1.2.1 L.flag flagA).trans hf
  have keep2 (w : Wire) (h : w≠L.flag) : s2.basis w=s1.basis w := by simp [s2,copy,run,writeBit,h]
  have va2 : regValue L.acc s2.basis=(A+2^261-p)%2^261 :=
    (regValue_congr _ _ _ (fun w hw' => keep2 w (outsideF _ (Or.inr (Or.inr rfl)) w hw'))).trans va1
  have bval := regValue_bit L.acc 260 L.flag s1.basis (by omega)
  rw [va1,(montNormalize_arithmetic p A hp hA).1] at bval
  have bit : s1.basis (L.acc.getD 260 L.flag)=decide (A<p) := by
    generalize s1.basis (L.acc.getD 260 L.flag)=b at bval ⊢
    cases b <;> by_cases hh : A<p <;> simp [hh] at bval ⊢
  have f2 : s2.basis L.flag=decide (A<p) := by
    simpa only [s2,copy,run,writeBit,if_pos rfl,f1,Bool.false_xor,Function.update_self] using bit
  have table2 : regValue L.table s2.basis=0 :=
    (regValue_congr _ _ _ (fun w hw' => keep2 w (outsideF _ (Or.inl rfl) w hw'))).trans ((keep1 _ tableA).trans hz)
  have carry2 : regValue L.carry s2.basis=0 :=
    (regValue_congr _ _ _ (fun w hw' => keep2 w (outsideF _ (Or.inr (Or.inl rfl)) w hw'))).trans ((keep1 _ carryA).trans hca)
  have cin2 : s2.basis L.cin=false := (keep2 _ cinF).trans ((h1.2.1 _ cinA).trans hci)
  have h3 := maskedConstant_frame false L p hnd ht hc hK s2 m1 table2 carry2 cin2
  simp only [Bool.false_eq_true,if_false] at h3
  have hp' : montNormalize L p=montConstantSub L p++(copy++maskedAddConst L.flag L.table L.acc L.carry L.cin p) := by
    simp only [montNormalize,List.append_assoc,copy]
  rw [hp',run_append,run_take,run_append,run_take]
  simp only [show measurementCount copy=0 by rfl,List.drop_zero]
  change (run (maskedAddConst L.flag L.table L.acc L.carry L.cin p) m1 s2).phase=s.phase ∧ _
  refine ⟨h3.1.trans h1.1,?_,?_,(h3.2.1 _ flagA).trans f2⟩
  · intro w hw' hf'; exact (h3.2.1 w hw').trans ((keep2 w hf').trans (h1.2.1 w hw'))
  · rw [h3.2.2,va2,f2,hw]
    simpa only [decide_eq_true_eq] using (montNormalize_arithmetic p A hp hA).2


private theorem montDenormalize_arithmetic (p A : Nat) (hp : p<2^256) (hA : A<2*p) :
    ((A%p+2^261-(if A<p then p else 0))%2^261)=(A+2^261-p)%2^261 ∧
    (((A+2^261-p)%2^261)+p)%2^261=A := by
  have hAfit : A<2^261 := by omega
  by_cases h : A<p
  · simp only [if_pos h,Nat.mod_eq_of_lt h]
    constructor
    · trivial
    · rw [Nat.mod_eq_of_lt (show A+2^261-p<2^261 by omega),
        show A+2^261-p+p=A+2^261 by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hAfit]
  · have hm : A%p=A-p := by
      conv_lhs => rw [show A=(A-p)+p by omega]
      rw [Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    have hB : (A+2^261-p)%2^261=A-p := by
      rw [show A+2^261-p=(A-p)+2^261 by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    simp only [if_neg h,hm,Nat.sub_zero,hB,Nat.add_mod_right]
    constructor
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [show A-p+p=A by omega,Nat.mod_eq_of_lt hAfit]

/-- 使用已保存借位恢复 A，并将 flag 清零；仍只改变 acc/flag。 -/
theorem montDenormalize_correct (L : MontStageLayout) (p A : Nat)
    (hnd : (L.flag::L.cin::(L.table++L.acc++L.carry)).Nodup)
    (ht : L.table.length=L.acc.length) (hc : L.carry.length+1=L.acc.length)
    (hw : L.acc.length=261) (hp : p<2^256) (hA : A<2*p)
    (s : State) (m : List Bool) (ha : regValue L.acc s.basis=A%p)
    (hz : regValue L.table s.basis=0) (hca : regValue L.carry s.basis=0)
    (hci : s.basis L.cin=false) (hf : s.basis L.flag=decide (A<p)) :
    (run (montDenormalize L p) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w≠L.flag → (run (montDenormalize L p) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montDenormalize L p) m s).basis=A ∧
    (run (montDenormalize L p) m s).basis L.flag=false := by
  have hK : p<2^L.table.length := by rw [ht,hw]; omega
  have hn := List.nodup_iff_count.mp hnd
  have flagA : L.flag∉L.acc := by
    intro hh; have h := hn L.flag; have h1 := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
  have cinA : L.cin∉L.acc := by
    intro hh; have h := hn L.cin; have h1 := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
  have cinF : L.cin≠L.flag := by
    intro hh; have h := hn L.cin
    simp only [hh,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
  have tableA : L.table.Disjoint L.acc := by
    apply List.disjoint_left.mpr; intro w hw' ht'
    have h := hn w; have h1 := List.count_pos_iff.mpr hw'; have h2 := List.count_pos_iff.mpr ht'
    simp only [List.count_cons,List.count_append] at h; omega
  have carryA : L.carry.Disjoint L.acc := by
    apply List.disjoint_left.mpr; intro w hw' ht'
    have h := hn w; have h1 := List.count_pos_iff.mpr hw'; have h2 := List.count_pos_iff.mpr ht'
    simp only [List.count_cons,List.count_append] at h; omega
  have outsideF (r : List Wire) (hr : r=L.table ∨ r=L.carry ∨ r=L.acc) : ∀ w∈r, w≠L.flag := by
    intro w hw' he; subst w
    have h := hn L.flag; have h1 := List.count_pos_iff.mpr hw'
    rcases hr with rfl|rfl|rfl <;>
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h <;> omega
  let s1 := run (maskedSubConst L.flag L.table L.acc L.carry L.cin p) m s
  let m1 := m.drop (measurementCount (maskedSubConst L.flag L.table L.acc L.carry L.cin p))
  let copy : Program := [.CX (L.acc.getD 260 L.flag) L.flag]
  let s2 := run copy m1 s1
  have h1 := maskedConstant_frame true L p hnd ht hc hK s m hz hca hci
  simp only [if_true] at h1
  have keep1 (r : List Wire) (hr : r.Disjoint L.acc) : regValue r s1.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw' => h1.2.1 w (List.disjoint_left.mp hr hw'))
  have va1 : regValue L.acc s1.basis=(A+2^261-p)%2^261 := by
    rw [h1.2.2,ha,hf,hw]
    simpa only [decide_eq_true_eq] using (montDenormalize_arithmetic p A hp hA).1
  have f1 : s1.basis L.flag=decide (A<p) := (h1.2.1 L.flag flagA).trans hf
  have keep2 (w : Wire) (h : w≠L.flag) : s2.basis w=s1.basis w := by simp [s2,copy,run,writeBit,h]
  have va2 : regValue L.acc s2.basis=(A+2^261-p)%2^261 :=
    (regValue_congr _ _ _ (fun w hw' => keep2 w (outsideF _ (Or.inr (Or.inr rfl)) w hw'))).trans va1
  have bval := regValue_bit L.acc 260 L.flag s1.basis (by omega)
  rw [va1,(montNormalize_arithmetic p A hp hA).1] at bval
  have bit : s1.basis (L.acc.getD 260 L.flag)=decide (A<p) := by
    generalize s1.basis (L.acc.getD 260 L.flag)=b at bval ⊢
    cases b <;> by_cases hh : A<p <;> simp [hh] at bval ⊢
  have f2 : s2.basis L.flag=false := by
    simp only [s2,copy,run,writeBit,Function.update_self,f1,bit,Bool.xor_self]
  have table2 : regValue L.table s2.basis=0 :=
    (regValue_congr _ _ _ (fun w hw' => keep2 w (outsideF _ (Or.inl rfl) w hw'))).trans ((keep1 _ tableA).trans hz)
  have carry2 : regValue L.carry s2.basis=0 :=
    (regValue_congr _ _ _ (fun w hw' => keep2 w (outsideF _ (Or.inr (Or.inl rfl)) w hw'))).trans ((keep1 _ carryA).trans hca)
  have cin2 : s2.basis L.cin=false := (keep2 _ cinF).trans ((h1.2.1 _ cinA).trans hci)
  have h3 := montConstantAdd_correct L p (List.nodup_cons.mp hnd).2 ht hc hK s2 m1 table2 carry2 cin2
  have hp' : montDenormalize L p=maskedSubConst L.flag L.table L.acc L.carry L.cin p++(copy++montConstantAdd L p) := by
    simp only [montDenormalize,List.append_assoc,copy]
  rw [hp',run_append,run_take,run_append,run_take]
  simp only [show measurementCount copy=0 by rfl,List.drop_zero]
  change (run (montConstantAdd L p) m1 s2).phase=s.phase ∧ _
  refine ⟨h3.1.trans h1.1,?_,?_,(h3.2.1 _ flagA).trans f2⟩
  · intro w hw' hf'; exact (h3.2.1 w hw').trans ((keep2 w hf').trans (h1.2.1 w hw'))
  · rw [h3.2.2,va2,hw]
    exact (montDenormalize_arithmetic p A hp hA).2

end ECDSAAdd.Arithmetic
