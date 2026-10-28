import ECDSAAdd.Arithmetic.MontReduce

namespace ECDSAAdd.Arithmetic

theorem mont_bit_mem (r : List Wire) (i : Nat) (fallback : Wire) (hi : i<r.length) : r.getD i fallback∈r := by
  induction r generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => simp
    | succ i => simp only [List.getD_cons_succ]; exact List.mem_cons_of_mem _ (ih i (by simpa using hi))

theorem mont_source_value (L : MontStageLayout) (x : List Wire) (j X : Nat)
    (hj : j≤5) (hp : L.pad.length=5) (hx : 256≤x.length) (hX : X<2^256)
    (s : BasisState) (hpad : regValue L.pad s=0) (hv : regValue x s=X) :
    regValue (L.source x j) s=2^j*X := by
  have ht : regValue (L.pad.take j) s=0 := (regValue_zero _ _).mpr (fun w hw =>
    (regValue_zero _ _).mp hpad w ((List.take_sublist j L.pad).subset hw))
  have hd : regValue (L.pad.drop j) s=0 := (regValue_zero _ _).mpr (fun w hw =>
    (regValue_zero _ _).mp hpad w ((List.drop_sublist j L.pad).subset hw))
  have hv' : regValue (x.take 256) s=X := by rw [mont_low_value x 256 hx,hv,Nat.mod_eq_of_lt hX]
  simp only [MontStageLayout.source,regValue_append,ht,hd,hv',Nat.mul_zero,Nat.add_zero,
    Nat.zero_add,List.length_take,hp,Nat.min_eq_left hj]

private theorem maskedDigit_correct (subtract : Bool) (c cin : Wire) (src mask acc carry : List Wire)
    (hnd : (c::cin::(src++mask++acc++carry)).Nodup)
    (hs : src.length=mask.length) (ht : mask.length=acc.length) (hc : carry.length+1=acc.length)
    (s : State) (m : List Bool) (hz : regValue mask s.basis=0)
    (hca : regValue carry s.basis=0) (hci : s.basis cin=false) :
    let circuit := if subtract then measuredMaskedSubInPlace c src mask acc carry cin else measuredMaskedAddInPlace c src mask acc carry cin
    (run circuit m s).phase=s.phase ∧
    (∀ w, w∉acc → (run circuit m s).basis w=s.basis w) ∧
    regValue acc (run circuit m s).basis=(if subtract then
      (regValue acc s.basis+2^acc.length-(if s.basis c then regValue src s.basis else 0))%2^acc.length
      else (regValue acc s.basis+(if s.basis c then regValue src s.basis else 0))%2^acc.length) := by
  let circuit := if subtract then measuredMaskedSubInPlace c src mask acc carry cin else measuredMaskedAddInPlace c src mask acc carry cin
  have h : (run circuit m s).phase=s.phase ∧
      (run circuit m s).basis c=s.basis c ∧ regValue src (run circuit m s).basis=regValue src s.basis ∧
      regValue mask (run circuit m s).basis=0 ∧
      regValue acc (run circuit m s).basis=(if subtract then
        (regValue acc s.basis+2^acc.length-(if s.basis c then regValue src s.basis else 0))%2^acc.length
        else (regValue acc s.basis+(if s.basis c then regValue src s.basis else 0))%2^acc.length) ∧
      (run circuit m s).basis cin=false ∧ regValue carry (run circuit m s).basis=0 := by
    cases subtract with
    | false =>
      have hh := measuredMaskedAddInPlace_spec c cin src mask acc carry hnd hs ht hc
        (s.basis c) (regValue src s.basis) (regValue acc s.basis) s m ⟨⟨⟨⟨⟨rfl,rfl⟩,hz⟩,rfl⟩,hci⟩,hca⟩
      exact ⟨hh.1,hh.2.1.1.1.1.1,hh.2.1.1.1.1.2,hh.2.1.1.1.2,hh.2.1.1.2,hh.2.1.2,hh.2.2⟩
    | true =>
      have hh := measuredMaskedSubInPlace_spec c cin src mask acc carry hnd hs ht hc
        (s.basis c) (regValue src s.basis) (regValue acc s.basis) s m ⟨⟨⟨⟨⟨rfl,rfl⟩,hz⟩,rfl⟩,hci⟩,hca⟩
      exact ⟨hh.1,hh.2.1.1.1.1.1,hh.2.1.1.1.1.2,hh.2.1.1.1.2,hh.2.1.1.2,hh.2.1.2,hh.2.2⟩
  refine ⟨h.1,?_,h.2.2.2.2.1⟩
  intro w hw
  by_cases hcw : w=c
  · subst w; exact h.2.1
  by_cases hcin : w=cin
  · subst w; exact h.2.2.2.2.2.1.trans hci.symm
  by_cases hsrc : w∈src
  · exact (regValue_eq_iff src _ _).mp h.2.2.1 w hsrc
  by_cases hmask : w∈mask
  · exact (regValue_eq_iff mask _ _).mp (h.2.2.2.1.trans hz.symm) w hmask
  by_cases hcarry : w∈carry
  · exact (regValue_eq_iff carry _ _).mp (h.2.2.2.2.2.2.trans hca.symm) w hcarry
  have hwires : wires circuit=(c::cin::(src++mask++acc++carry)).toFinset := by
    have hh := measuredMaskedInPlace_wires c src mask acc carry cin hs ht hc
    cases subtract with
    | false => exact hh.1
    | true => exact hh.2
  apply run_preserves_outside
  rw [hwires]
  simp [hcw,hcin,hsrc,hmask,hw,hcarry]


private theorem montBit_correct (subtract : Bool) (L : MontStageLayout) (x y : List Wire)
    (i j X Y : Nat) (hj : j<4) (hi : 4*i+j<y.length)
    (hnd : (L.cin::(x++y++L.pad++L.mask++L.acc++L.carry)).Nodup)
    (hx : 256≤x.length) (hpad : L.pad.length=5) (hm : L.mask.length=261)
    (hw : L.acc.length=261) (hc : L.carry.length=260) (hX : X<2^256)
    (s : State) (m : List Bool) (hvx : regValue x s.basis=X) (hvy : regValue y s.basis=Y)
    (hpz : regValue L.pad s.basis=0) (hmz : regValue L.mask s.basis=0)
    (hcz : regValue L.carry s.basis=0) (hci : s.basis L.cin=false) :
    let c := y.getD (4*i+j) L.flag
    let circuit := if subtract then measuredMaskedSubInPlace c (L.source x j) L.mask L.acc L.carry L.cin
      else measuredMaskedAddInPlace c (L.source x j) L.mask L.acc L.carry L.cin
    (run circuit m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run circuit m s).basis w=s.basis w) ∧
    regValue L.acc (run circuit m s).basis=(if subtract then
      (regValue L.acc s.basis+2^261-X*2^j*((Y/2^(4*i+j))%2))%2^261
      else (regValue L.acc s.basis+X*2^j*((Y/2^(4*i+j))%2))%2^261) := by
  let c := y.getD (4*i+j) L.flag
  have cmem : c∈y := mont_bit_mem y (4*i+j) L.flag hi
  have hsrc (w : Wire) : List.count w (L.source x j)≤List.count w x+List.count w L.pad := by
    have hp := congrArg (List.count w) (List.take_append_drop j L.pad)
    have ht := (List.take_sublist 256 x).count_le w
    simp only [MontStageLayout.source,List.count_append] at hp ⊢; omega
  have hn : (c::L.cin::(L.source x j++L.mask++L.acc++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    have hs := hsrc w
    have hcm := List.count_pos_iff.mpr cmem
    by_cases he : c=w
    · subst w
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h ⊢
      omega
    · simp only [List.count_cons,List.count_append] at h ⊢
      have hb : (c==w)=false := by simpa using he
      rw [hb]; simp only [Bool.false_eq_true,if_false]; omega
  have hslen : (L.source x j).length=L.mask.length := by
    simp only [MontStageLayout.source,List.length_append,List.length_take,List.length_drop,hpad,
      Nat.min_eq_left (show j≤5 by omega),Nat.min_eq_left hx,hm]
    omega
  have hb := regValue_bit y (4*i+j) L.flag s.basis hi
  rw [hvy] at hb
  have hsrcv := mont_source_value L x j X (by omega) hpad hx hX s.basis hpz hvx
  have hnum : (if s.basis c then regValue (L.source x j) s.basis else 0)=
      X*2^j*((Y/2^(4*i+j))%2) := by
    rw [hsrcv,← hb]
    generalize s.basis c=b
    cases b <;> simp [Nat.mul_comm]
  have hh := maskedDigit_correct subtract c L.cin (L.source x j) L.mask L.acc L.carry hn hslen
    (hm.trans hw.symm) (by omega) s m hmz hcz hci
  simpa only [hw,hnum] using hh


private theorem mont_digit_step (Y i k : Nat) :
    (Y/2^(4*i))%2^(k+1)=(Y/2^(4*i))%2^k+2^k*((Y/2^(4*i+k))%2) := by
  rw [Nat.pow_succ,Nat.mod_mul,Nat.div_div_eq_div_mul,← Nat.pow_add]

private theorem mont_digit_fit (Y i k X U : Nat) (hk : k≤4) (hf : U+16*X<2^261) :
    U+X*((Y/2^(4*i))%2^k)<2^261 := by
  have hb := Nat.mod_lt (Y/2^(4*i)) (Nat.two_pow_pos k)
  have hp : 2^k≤16 := Nat.pow_le_pow_right (by decide) hk
  have hh : X*((Y/2^(4*i))%2^k)≤X*16 := Nat.mul_le_mul_left X (by omega)
  rw [Nat.mul_comm X 16] at hh
  omega

private theorem montAddBits_correct (L : MontStageLayout) (x y : List Wire)
    (i k X Y U : Nat) (hk : k≤4) (hi : 4*i+4≤y.length)
    (hnd : (L.cin::(x++y++L.pad++L.mask++L.acc++L.carry)).Nodup)
    (hx : 256≤x.length) (hpad : L.pad.length=5) (hm : L.mask.length=261)
    (hw : L.acc.length=261) (hc : L.carry.length=260) (hX : X<2^256) (hfit : U+16*X<2^261)
    (s : State) (m : List Bool) (hvx : regValue x s.basis=X) (hvy : regValue y s.basis=Y)
    (hva : regValue L.acc s.basis=U) (hpz : regValue L.pad s.basis=0) (hmz : regValue L.mask s.basis=0)
    (hcz : regValue L.carry s.basis=0) (hci : s.basis L.cin=false) :
    let circuit := (List.range k).flatMap (fun j =>
      measuredMaskedAddInPlace (y.getD (4*i+j) L.flag) (L.source x j) L.mask L.acc L.carry L.cin)
    (run circuit m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run circuit m s).basis w=s.basis w) ∧
    regValue L.acc (run circuit m s).basis=U+X*((Y/2^(4*i))%2^k) := by
  have hn := List.nodup_iff_count.mp hnd
  have outsideA (r : List Wire) (hr : r=x ∨ r=y ∨ r=L.pad ∨ r=L.mask ∨ r=L.carry) : r.Disjoint L.acc := by
    apply List.disjoint_left.mpr; intro w hw' hh
    have h := hn w; have h1 := List.count_pos_iff.mpr hw'; have h2 := List.count_pos_iff.mpr hh
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> simp only [List.count_cons,List.count_append] at h <;> omega
  have cinA : L.cin∉L.acc := by
    intro hh; have h := hn L.cin; have h1 := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
  induction k with
  | zero =>
    simp only [List.range_zero,List.flatMap_nil,run,Nat.pow_zero,Nat.mod_one,Nat.mul_zero,Nat.add_zero]
    exact ⟨trivial,fun w _ => trivial,hva⟩
  | succ k ih =>
    let first := (List.range k).flatMap (fun j =>
      measuredMaskedAddInPlace (y.getD (4*i+j) L.flag) (L.source x j) L.mask L.acc L.carry L.cin)
    let s1 := run first m s
    let m1 := m.drop (measurementCount first)
    have h1 := ih (by omega)
    have keep1 (r : List Wire) (hr : r.Disjoint L.acc) : regValue r s1.basis=regValue r s.basis :=
      regValue_congr _ _ _ (fun w hw' => h1.2.1 w (List.disjoint_left.mp hr hw'))
    have h2 := montBit_correct false L x y i k X Y (by omega) (by omega) hnd hx hpad hm hw hc hX s1 m1
      ((keep1 x (outsideA _ (Or.inl rfl))).trans hvx)
      ((keep1 y (outsideA _ (Or.inr (Or.inl rfl)))).trans hvy)
      ((keep1 L.pad (outsideA _ (Or.inr (Or.inr (Or.inl rfl))))).trans hpz)
      ((keep1 L.mask (outsideA _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).trans hmz)
      ((keep1 L.carry (outsideA _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))).trans hcz)
      ((h1.2.1 _ cinA).trans hci)
    simp only [Bool.false_eq_true,if_false] at h2
    simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [run_append,run_take]
    refine ⟨h2.1.trans h1.1,fun w hw' => (h2.2.1 w hw').trans (h1.2.1 w hw'),?_⟩
    rw [h2.2.2,h1.2.2]
    have he : U+X*((Y/2^(4*i))%2^k)+X*2^k*((Y/2^(4*i+k))%2)=U+X*((Y/2^(4*i))%2^(k+1)) := by
      rw [mont_digit_step]; ring
    rw [he,Nat.mod_eq_of_lt (mont_digit_fit Y i (k+1) X U hk hfit)]


private theorem montSubBits_correct (L : MontStageLayout) (x y : List Wire)
    (i k X Y U : Nat) (hk : k≤4) (hi : 4*i+4≤y.length)
    (hnd : (L.cin::(x++y++L.pad++L.mask++L.acc++L.carry)).Nodup)
    (hx : 256≤x.length) (hpad : L.pad.length=5) (hm : L.mask.length=261)
    (hw : L.acc.length=261) (hc : L.carry.length=260) (hX : X<2^256) (hfit : U+16*X<2^261)
    (s : State) (m : List Bool) (hvx : regValue x s.basis=X) (hvy : regValue y s.basis=Y)
    (hva : regValue L.acc s.basis=U+X*((Y/2^(4*i))%2^k)) (hpz : regValue L.pad s.basis=0) (hmz : regValue L.mask s.basis=0)
    (hcz : regValue L.carry s.basis=0) (hci : s.basis L.cin=false) :
    let circuit := (List.range k).reverse.flatMap (fun j =>
      measuredMaskedSubInPlace (y.getD (4*i+j) L.flag) (L.source x j) L.mask L.acc L.carry L.cin)
    (run circuit m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run circuit m s).basis w=s.basis w) ∧
    regValue L.acc (run circuit m s).basis=U := by
  have hn := List.nodup_iff_count.mp hnd
  have outsideA (r : List Wire) (hr : r=x ∨ r=y ∨ r=L.pad ∨ r=L.mask ∨ r=L.carry) : r.Disjoint L.acc := by
    apply List.disjoint_left.mpr; intro w hw' hh
    have h := hn w; have h1 := List.count_pos_iff.mpr hw'; have h2 := List.count_pos_iff.mpr hh
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> simp only [List.count_cons,List.count_append] at h <;> omega
  have cinA : L.cin∉L.acc := by
    intro hh; have h := hn L.cin; have h1 := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
  induction k generalizing s m with
  | zero =>
    simp only [List.range_zero,List.reverse_nil,List.flatMap_nil,run]
    exact ⟨trivial,fun w _ => trivial,by simpa only [Nat.pow_zero,Nat.mod_one,Nat.mul_zero,Nat.add_zero] using hva⟩
  | succ k ih =>
    let first := measuredMaskedSubInPlace (y.getD (4*i+k) L.flag) (L.source x k) L.mask L.acc L.carry L.cin
    let s1 := run first m s
    let m1 := m.drop (measurementCount first)
    have h1 := montBit_correct true L x y i k X Y (by omega) (by omega) hnd hx hpad hm hw hc hX
      s m hvx hvy hpz hmz hcz hci
    simp only [if_true] at h1
    have keep1 (r : List Wire) (hr : r.Disjoint L.acc) : regValue r s1.basis=regValue r s.basis :=
      regValue_congr _ _ _ (fun w hw' => h1.2.1 w (List.disjoint_left.mp hr hw'))
    have va1 : regValue L.acc s1.basis=U+X*((Y/2^(4*i))%2^k) := by
      rw [h1.2.2,hva,mont_digit_step]
      have he : U+X*((Y/2^(4*i))%2^k+2^k*((Y/2^(4*i+k))%2))=
          U+X*((Y/2^(4*i))%2^k)+X*2^k*((Y/2^(4*i+k))%2) := by ring
      rw [he,show U+X*((Y/2^(4*i))%2^k)+X*2^k*((Y/2^(4*i+k))%2)+2^261-
          X*2^k*((Y/2^(4*i+k))%2)=U+X*((Y/2^(4*i))%2^k)+2^261 by omega,
        Nat.add_mod_right,Nat.mod_eq_of_lt (mont_digit_fit Y i k X U (by omega) hfit)]
    have h2 := ih (by omega) s1 m1
      ((keep1 x (outsideA _ (Or.inl rfl))).trans hvx)
      ((keep1 y (outsideA _ (Or.inr (Or.inl rfl)))).trans hvy) va1
      ((keep1 L.pad (outsideA _ (Or.inr (Or.inr (Or.inl rfl))))).trans hpz)
      ((keep1 L.mask (outsideA _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).trans hmz)
      ((keep1 L.carry (outsideA _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))).trans hcz)
      ((h1.2.1 _ cinA).trans hci)
    simp only [List.range_succ,List.reverse_append,List.reverse_singleton,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [run_append,run_take]
    exact ⟨h2.1.trans h1.1,fun w hw' => (h2.2.1 w hw').trans (h1.2.1 w hw'),h2.2.2⟩


/-- 变量窗口的四次受控Add，只改变累加器并清临时字。 -/
theorem montAddDigit_correct (L : MontStageLayout) (x y : List Wire)
    (i X Y U : Nat) (hi : 4*i+4≤y.length)
    (hnd : (L.cin::(x++y++L.pad++L.mask++L.acc++L.carry)).Nodup)
    (hx : 256≤x.length) (hpad : L.pad.length=5) (hm : L.mask.length=261)
    (hw : L.acc.length=261) (hc : L.carry.length=260) (hX : X<2^256) (hfit : U+16*X<2^261)
    (s : State) (m : List Bool) (hvx : regValue x s.basis=X) (hvy : regValue y s.basis=Y)
    (hva : regValue L.acc s.basis=U) (hpz : regValue L.pad s.basis=0) (hmz : regValue L.mask s.basis=0)
    (hcz : regValue L.carry s.basis=0) (hci : s.basis L.cin=false) :
    (run (montAddDigit L x y i) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run (montAddDigit L x y i) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montAddDigit L x y i) m s).basis=U+X*((Y/16^i)%16) := by
  have hp : 2^(4*i)=16^i := by rw [Nat.pow_mul]
  have hh := montAddBits_correct L x y i 4 X Y U (by omega) hi hnd hx hpad hm hw hc hX hfit
    s m hvx hvy hva hpz hmz hcz hci
  simpa only [montAddDigit,hp,show 2^4=16 from rfl] using hh

/-- 变量窗口的四次受控Sub，只改变累加器并清临时字。 -/
theorem montSubDigit_correct (L : MontStageLayout) (x y : List Wire)
    (i X Y U : Nat) (hi : 4*i+4≤y.length)
    (hnd : (L.cin::(x++y++L.pad++L.mask++L.acc++L.carry)).Nodup)
    (hx : 256≤x.length) (hpad : L.pad.length=5) (hm : L.mask.length=261)
    (hw : L.acc.length=261) (hc : L.carry.length=260) (hX : X<2^256) (hfit : U+16*X<2^261)
    (s : State) (m : List Bool) (hvx : regValue x s.basis=X) (hvy : regValue y s.basis=Y)
    (hva : regValue L.acc s.basis=U+X*((Y/16^i)%16)) (hpz : regValue L.pad s.basis=0) (hmz : regValue L.mask s.basis=0)
    (hcz : regValue L.carry s.basis=0) (hci : s.basis L.cin=false) :
    (run (montSubDigit L x y i) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run (montSubDigit L x y i) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montSubDigit L x y i) m s).basis=U := by
  have hp : 2^(4*i)=16^i := by rw [Nat.pow_mul]
  have hh := montSubBits_correct L x y i 4 X Y U (by omega) hi hnd hx hpad hm hw hc hX hfit
    s m hvx hvy (by simpa only [hp,show 2^4=16 from rfl] using hva) hpz hmz hcz hci
  simpa only [montSubDigit,hp,show 2^4=16 from rfl] using hh

end ECDSAAdd.Arithmetic
