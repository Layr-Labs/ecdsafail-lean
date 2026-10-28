import ECDSAAdd.Arithmetic.MontRounds

namespace ECDSAAdd.Arithmetic

private theorem constDigit_correct (subtract : Bool) (L : MontStageLayout) (y : List Wire) (i K Y : Nat)
    (hw : L.Widths) (hnd : (y++L.wires).Nodup) (hy : 256≤y.length) (hi : i<64) (hK : K<2^256)
    (s : State) (m : List Bool) (vy : regValue y s.basis=Y) (vw : regValue L.work s.basis=0) :
    let circuit := if subtract then montLookupSub L ((y.drop (4*i)).take 4) K else montLookupAdd L ((y.drop (4*i)).take 4) K
    (run circuit m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run circuit m s).basis w=s.basis w) ∧
    regValue L.acc (run circuit m s).basis=(if subtract then
      (regValue L.acc s.basis+2^261-K*((Y/16^i)%16))%2^261 else (regValue L.acc s.basis+K*((Y/16^i)%16))%2^261) := by
  let addr := (y.drop (4*i)).take 4
  have haddr : addr.Sublist y := (List.take_sublist 4 (y.drop (4*i))).trans (List.drop_sublist (4*i) y)
  have hn : (L.cin::(addr++L.table++L.acc++L.carry++L.scratch)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    have ha := haddr.count_le w
    simp only [MontStageLayout.wires,MontStageLayout.work,List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
  have hlen : addr.length=4 := by simp only [addr,List.length_take,List.length_drop]; omega
  have hpow : 2^(4*i)=16^i := by rw [Nat.pow_mul]
  have hv : regValue addr s.basis=(Y/16^i)%16 := by
    rw [mont_low_value _ 4 (by simp only [List.length_drop]; omega),mont_drop_value y (4*i) (by omega),vy,hpow]
    rfl
  have htable : ∀ d<16, d*K<2^L.table.length := by
    intro d hd; have hh := Nat.mul_le_mul_right K (show d≤15 by omega)
    rw [hw.table]; omega
  have clean (r : List Wire) (hr : r⊆L.work) := L.work_clean _ vw r hr
  cases subtract with
  | false =>
    have hh := montLookupAdd_correct L addr K hn hlen hw.scratch (hw.table.trans hw.acc.symm)
      (by rw [hw.carry,hw.acc]) htable s m
      (clean L.table (by intro w h; simp [MontStageLayout.work,h]))
      (clean L.scratch (by intro w h; simp [MontStageLayout.work,h]))
      (clean L.carry (by intro w h; simp [MontStageLayout.work,h])) (L.cin_clean _ vw)
    simpa only [Bool.false_eq_true,if_false,hv,hw.acc,Nat.mul_comm K] using hh
  | true =>
    have hh := montLookupSub_correct L addr K hn hlen hw.scratch (hw.table.trans hw.acc.symm)
      (by rw [hw.carry,hw.acc]) htable s m
      (clean L.table (by intro w h; simp [MontStageLayout.work,h]))
      (clean L.scratch (by intro w h; simp [MontStageLayout.work,h]))
      (clean L.carry (by intro w h; simp [MontStageLayout.work,h])) (L.cin_clean _ vw)
    simpa only [if_true,hv,hw.acc,Nat.mul_comm K] using hh

theorem constDigitAdd_correct (L : MontStageLayout) (y : List Wire) (i K Y A : Nat)
    (hw : L.Widths) (hnd : (y++L.wires).Nodup) (hy : 256≤y.length) (hi : i<64) (hK : K<2^256)
    (hfit : A+16*K<2^261) (s : State) (m : List Bool) (vy : regValue y s.basis=Y)
    (va : regValue L.acc s.basis=A) (vw : regValue L.work s.basis=0) :
    (run (montLookupAdd L ((y.drop (4*i)).take 4) K) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run (montLookupAdd L ((y.drop (4*i)).take 4) K) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montLookupAdd L ((y.drop (4*i)).take 4) K) m s).basis=A+K*((Y/16^i)%16) := by
  have hh := constDigit_correct false L y i K Y hw hnd hy hi hK s m vy vw
  have hd := Nat.mod_lt (Y/16^i) (by decide : 0<16)
  have hf := Nat.mul_le_mul_left K (show (Y/16^i)%16≤16 by omega)
  rw [Nat.mul_comm K 16] at hf
  simpa only [Bool.false_eq_true,if_false,va,Nat.mod_eq_of_lt (show A+K*((Y/16^i)%16)<2^261 by omega)] using hh

theorem constDigitSub_correct (L : MontStageLayout) (y : List Wire) (i K Y A : Nat)
    (hw : L.Widths) (hnd : (y++L.wires).Nodup) (hy : 256≤y.length) (hi : i<64) (hK : K<2^256)
    (hfit : A+16*K<2^261) (s : State) (m : List Bool) (vy : regValue y s.basis=Y)
    (va : regValue L.acc s.basis=A+K*((Y/16^i)%16)) (vw : regValue L.work s.basis=0) :
    (run (montLookupSub L ((y.drop (4*i)).take 4) K) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run (montLookupSub L ((y.drop (4*i)).take 4) K) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montLookupSub L ((y.drop (4*i)).take 4) K) m s).basis=A := by
  have hh := constDigit_correct true L y i K Y hw hnd hy hi hK s m vy vw
  simp only [if_true,va] at hh
  rw [show A+K*((Y/16^i)%16)+2^261-K*((Y/16^i)%16)=A+2^261 by omega,
    Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)] at hh
  exact hh

end ECDSAAdd.Arithmetic
