import ECDSAAdd.Arithmetic.KaratsubaSquareResources

namespace ECDSAAdd.Arithmetic

/-- Arithmetic target frame, used by the 129- and 384-bit composition stages. -/
theorem karatsuba_arith_frame (sub : Bool) (src dst carry : List Wire) (cin : Wire)
    (hn : (cin::src++dst++carry).Nodup) (hs : src.length=dst.length)
    (hc : carry.length+1=dst.length) (base : BasisState)
    (hk : regValue carry base=0) (hi : base cin=false) (V : Nat) :
    Triple (SquareFrame dst base V)
      (if sub then subInPlace src dst carry cin else addInPlace src dst carry cin)
      (SquareFrame dst base (if sub then (V+2^dst.length-regValue src base)%2^dst.length
        else (V+regValue src base)%2^dst.length)) := by
  have dis (w : Wire) (hw : w∈cin::src++carry) : w∉dst := by
    intro hd
    have hn' := List.nodup_iff_count.mp hn w
    have hw' := List.count_pos_iff.mpr hw
    have hd' := List.count_pos_iff.mpr hd
    simp only [List.count_cons,List.count_append] at hn' hw'
    omega
  intro s m h
  have sr : regValue src s.basis=regValue src base :=
    regValue_congr _ _ _ (fun w hw => h.2 w (dis w (by simp [hw])))
  have kr : regValue carry s.basis=0 := (regValue_congr _ _ _
    (fun w hw => h.2 w (dis w (by simp [hw])))).trans hk
  have ci : s.basis cin=false := (h.2 cin (dis cin (by simp))).trans hi
  have pre : ((regValue src s.basis=regValue src base ∧ regValue dst s.basis=V) ∧
      s.basis cin=false) ∧ regValue carry s.basis=0 := ⟨⟨⟨sr,h.1⟩,ci⟩,kr⟩
  have ah := addInPlace_spec src dst carry cin hn hs hc (regValue src base) V false s m pre
  have sh := subInPlace_spec src dst carry cin hn hs hc (regValue src base) V s m pre
  cases sub
  · have f := addInPlace_correct src dst carry cin hn hs hc s m ((regValue_zero _ _).mp kr)
    refine ⟨ah.1,?_,?_⟩
    · simpa [Nat.add_comm] using ah.2.1.1.2
    · intro w hw; exact (f.2.1 w hw).trans (h.2 w hw)
  · refine ⟨sh.1,sh.2.1.1.2,?_⟩
    intro w hw
    have eqsrc := (regValue_eq_iff src _ _).mp (sh.2.1.1.1.trans sr.symm)
    have eqcarry := (regValue_eq_iff carry _ _).mp (sh.2.2.trans kr.symm)
    have e : (run (subInPlace src dst carry cin) m s).basis w=s.basis w := by
      by_cases hwi : w=cin
      · subst w; exact sh.2.1.2.trans ci.symm
      by_cases hws : w∈src
      · exact eqsrc w hws
      by_cases hwc : w∈carry
      · exact eqcarry w hwc
      apply run_preserves_outside
      rw [subInPlace_wires src dst carry cin hs hc]
      simpa using And.intro hwi (And.intro hws (And.intro hw hwc))
    exact e.trans (h.2 w hw)

private theorem value_split (r : List Wire) (n : Nat) (hn : n≤r.length) (s : BasisState) :
    regValue r s=regValue (r.take n) s+2^n*regValue (r.drop n) s := by
  conv_lhs => rw [← List.take_append_drop n r]
  rw [regValue_append,List.length_take,Nat.min_eq_left hn]

private theorem small_split (r : List Wire) (n V : Nat) (hn : n≤r.length)
    (s : BasisState) (hv : regValue r s=V) (hV : V<2^n) :
    regValue (r.take n) s=V ∧ regValue (r.drop n) s=0 := by
  have h := value_split r n hn s
  rw [hv] at h
  have hp : 0<2^n := Nat.two_pow_pos _
  have hz : regValue (r.drop n) s=0 := by nlinarith
  simp only [hz,Nat.mul_zero,Nat.add_zero] at h
  exact ⟨h.symm,hz⟩

/-- A clean low-word XOR copy into a wider zero-extended target. -/
theorem karatsuba_copy_low (src dst : List Wire) (n : Nat)
    (hs : src.length=n) (hd : n≤dst.length) (hn : (src++dst).Nodup)
    (base : BasisState) :
    Triple (SquareFrame dst base 0) (copyRegister none src (dst.take n))
      (SquareFrame dst base (regValue src base)) ∧
    Triple (SquareFrame dst base (regValue src base)) (copyRegister none src (dst.take n))
      (SquareFrame dst base 0) := by
  have nd : (src++dst.take n).Nodup :=
    (List.Sublist.append (List.Sublist.refl src) (List.take_sublist n dst)).nodup hn
  have dis (w : Wire) (hw : w∈src) : w∉dst :=
    fun hh => (List.disjoint_left.mp (List.nodup_append'.mp hn).2.2) hw hh
  have dd : List.Disjoint (dst.take n) (dst.drop n) := by
    have hnd : dst.Nodup := (List.nodup_append'.mp hn).2.1
    conv at hnd => rw [← List.take_append_drop n dst]
    exact (List.nodup_append'.mp hnd).2.2
  have len : src.length=(dst.take n).length := by simp [hs,Nat.min_eq_left hd]
  have hb : regValue src base<2^n := by simpa [hs] using regValue_lt src base
  have single (V : Nat) (hV : V<2^n) :
      Triple (SquareFrame dst base V) (copyRegister none src (dst.take n))
        (SquareFrame dst base (V ^^^ regValue src base)) := by
    intro s m h
    have sv := regValue_congr src s.basis base (fun w hw => h.2 w (dis w hw))
    have split := small_split dst n V hd s.basis h.1 hV
    have cc := copyRegister_correct none src (dst.take n) len nd (by simp) s m
    refine ⟨cc.1,?_,?_⟩
    · rw [value_split dst n hd]
      have hz : regValue (dst.drop n) (run (copyRegister none src (dst.take n)) m s).basis=0 := by
        rw [← split.2]
        exact regValue_congr _ _ _ (fun w hw => cc.2.1 w (fun ht => List.disjoint_left.mp dd ht hw))
      rw [hz,Nat.mul_zero,Nat.add_zero]
      simpa [copyValue,split.1,sv] using cc.2.2
    · intro w hw
      exact (cc.2.1 w (fun ht => hw (List.mem_of_mem_take ht))).trans (h.2 w hw)
  constructor
  · simpa using single 0 (Nat.two_pow_pos n)
  · simpa using single (regValue src base) hb

/-- The sum word is a genuine 129-bit L+H, and its inverse clears the extra bit. -/
theorem karatsuba_sum_correct (L : KaratsubaSquareLayout) (h : L.Valid)
    (base : BasisState) (hp : regValue L.pad base=0) (hk : regValue L.carry base=0)
    (hi : base L.cin=false) :
    Triple (SquareFrame L.sum base 0) L.prepareSum
      (SquareFrame L.sum base (regValue L.low base+regValue L.high base)) ∧
    Triple (SquareFrame L.sum base (regValue L.low base+regValue L.high base)) L.clearSum
      (SquareFrame L.sum base 0) := by
  have nc : (L.low++L.sum).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have na : (L.cin::(L.high++L.pad.take 1)++L.sum++L.carry.take 128).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    have hp := (List.take_sublist 1 L.pad).count_le w
    have hk := (List.take_sublist 128 L.carry).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have kp : regValue (L.carry.take 128) base=0 :=
    (regValue_zero _ _).mpr (fun w hw => (regValue_zero _ _).mp hk w (List.mem_of_mem_take hw))
  have pp : regValue (L.pad.take 1) base=0 :=
    (regValue_zero _ _).mpr (fun w hw => (regValue_zero _ _).mp hp w (List.mem_of_mem_take hw))
  have sv : regValue (L.high++L.pad.take 1) base=regValue L.high base := by
    simp [regValue_append,pp]
  have hs : (L.high++L.pad.take 1).length=L.sum.length := by
    simp [h.high_length,h.pad_length,h.sum_length]
  have hc : (L.carry.take 128).length+1=L.sum.length := by simp [h.carry_length,h.sum_length]
  have cp := karatsuba_copy_low L.low L.sum 128 h.low_length (by simp [h.sum_length]) nc base
  have ap := karatsuba_arith_frame false (L.high++L.pad.take 1) L.sum (L.carry.take 128)
    L.cin na hs hc base kp hi (regValue L.low base)
  have sp := karatsuba_arith_frame true (L.high++L.pad.take 1) L.sum (L.carry.take 128)
    L.cin na hs hc base kp hi (regValue L.low base+regValue L.high base)
  have lb : regValue L.low base<2^128 := by simpa [h.low_length] using regValue_lt L.low base
  have hb : regValue L.high base<2^128 := by simpa [h.high_length] using regValue_lt L.high base
  have sumBound := square_sum128_bound _ _ lb hb
  have lbound : regValue L.low base<2^129 := by omega
  have amod : (regValue L.low base+regValue L.high base)%2^129=
      regValue L.low base+regValue L.high base := Nat.mod_eq_of_lt sumBound
  have smod : (regValue L.low base+regValue L.high base+2^129-regValue L.high base)%2^129=
      regValue L.low base := by
    rw [show regValue L.low base+regValue L.high base+2^129-regValue L.high base=
      regValue L.low base+2^129 by omega, Nat.add_mod_right,Nat.mod_eq_of_lt lbound]
  simp only [Bool.false_eq_true,if_false,if_true,sv,h.sum_length,amod,smod] at ap sp
  exact ⟨cp.1.seq ap,sp.seq cp.2⟩


private theorem copy_append (a b c d : List Wire) (h : a.length=c.length) :
    copyRegister none (a++b) (c++d)=copyRegister none a c++copyRegister none b d := by
  induction a generalizing c with
  | nil => have hc : c=[] := List.eq_nil_of_length_eq_zero h.symm; simp [hc,copyRegister]
  | cons x xs ih =>
    cases c with
    | nil => simp at h
    | cons y ys => simp only [List.length_cons,Nat.add_right_cancel_iff] at h
                   simp [copyRegister,ih ys h]

theorem karatsuba_copySquares_frame (L : KaratsubaSquareLayout) (h : L.Valid)
    (base : BasisState) :
    Triple (SquareFrame L.z base 0) L.copySquares
      (SquareFrame L.z base (regValue L.a base+2^256*regValue L.d base)) ∧
    Triple (SquareFrame L.z base (regValue L.a base+2^256*regValue L.d base)) L.copySquares
      (SquareFrame L.z base 0) := by
  have hn : ((L.a++L.d)++L.z).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have eqp : L.copySquares=copyRegister none (L.a++L.d) L.z := by
    conv_rhs => rw [← List.take_append_drop 256 L.z]
    rw [copy_append _ _ _ _ (by simp [h.a_length,h.z_length])]
    rfl
  have cp := karatsuba_copy_low (L.a++L.d) L.z 512
    (by simp [h.a_length,h.d_length]) (by simp [h.z_length]) hn base
  have tz : L.z.take 512=L.z := List.take_of_length_le (by rw [h.z_length])
  simpa [eqp,regValue_append,h.a_length,tz] using cp



/-- An arithmetic operation on the upper 384 bits preserves the low 128 bits. -/
theorem karatsuba_high_correct (sub : Bool) (src z carry : List Wire) (cin : Wire)
    (hn : (cin::src++z++carry).Nodup) (hz : z.length=512)
    (hs : src.length=384) (hc : carry.length=383) (s : State) (m : List Bool)
    (hk : regValue carry s.basis=0) (hi : s.basis cin=false) :
    let V := regValue z s.basis
    let A := regValue src s.basis
    let p := if sub then subInPlace src (z.drop 128) carry cin
                   else addInPlace src (z.drop 128) carry cin
    (run p m s).phase=s.phase ∧
    regValue z (run p m s).basis=V%2^128+2^128*
      (if sub then (V/2^128+2^384-A)%2^384 else (V/2^128+A)%2^384) ∧
    (∀ w,w∉z→(run p m s).basis w=s.basis w) := by
  dsimp only
  have nd : (cin::src++z.drop 128++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp hn w
    have hd := (List.drop_sublist 128 z).count_le w
    simp only [List.count_cons,List.count_append] at hh ⊢; omega
  have znd : z.Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at hh; omega
  have split := value_split z 128 (by omega) s.basis
  have lb := regValue_lt (z.take 128) s.basis
  simp only [List.length_take,hz] at lb
  norm_num at lb
  have hv : regValue (z.drop 128) s.basis=regValue z s.basis/2^128 := by omega
  have hl : regValue (z.take 128) s.basis=regValue z s.basis%2^128 := by omega
  have hr := karatsuba_arith_frame sub src (z.drop 128) carry cin nd
    (by simp [hs,hz]) (by simp [hc,hz]) s.basis hk hi
    (regValue (z.drop 128) s.basis) s m ⟨rfl,fun _ _=>rfl⟩
  refine ⟨hr.1,?_,fun w hw=>hr.2.2 w (fun hd=>hw (List.mem_of_mem_drop hd))⟩
  rw [value_split z 128 (by omega)]
  have nds : (z.take 128++z.drop 128).Nodup := by simpa using znd
  have dis := (List.nodup_append'.mp nds).2.2
  have he := regValue_congr (z.take 128) _ _
    (fun w hw=>hr.2.2 w (fun hd=>List.disjoint_left.mp dis hw hd))
  rw [he,hl,hr.2.1,hv]
  simp only [List.length_drop,hz,Nat.reduceSub]

end ECDSAAdd.Arithmetic
