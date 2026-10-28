import ECDSAAdd.Arithmetic.DivideLayoutProof

namespace ECDSAAdd.Arithmetic

private theorem controlled_inverse_constant (L : InverseLayout) (c : Wire)
    (hnd : (c::L.wires).Nodup) (v : InverseField → Nat) (B : Bool)
    (f : InverseField) (k : Nat) (hk : k<2^(L.reg f).length) :
    Triple (fun st => InverseValues L v st ∧ st c=B) (xorConstant (L.reg f) k)
      (fun st => InverseValues L (Function.update v f (v f ^^^ k)) st ∧ st c=B) := by
  have hn := (List.nodup_cons.mp hnd).2
  have hc : c∉L.reg f := by
    intro h
    have hp := List.count_pos_iff.mpr h
    have hz := List.count_eq_zero.mpr (List.nodup_cons.mp hnd).1
    have hl := L.reg_count f c
    omega
  apply (inverseConstant_values L hn v f k hk).frame
  intro s t he hb
  exact (he c (fun h => hc (List.mem_toFinset.mp (xorConstant_wires_subset _ _ h)))).symm.trans hb

private theorem controlled_inverse_mask (L : InverseLayout) (c : Wire)
    (hnd : (c::L.wires).Nodup) (v : InverseField → Nat) (B : Bool)
    (f : InverseField) (k : Nat) (hk : k<2^(L.reg f).length) :
    Triple (fun st => InverseValues L v st ∧ st c=B) (maskedConstant c (L.reg f) k)
      (fun st => InverseValues L (Function.update v f (v f ^^^ (if B then k else 0))) st ∧ st c=B) := by
  have hn := (List.nodup_cons.mp hnd).2
  have hc : c∉L.reg f := by
    intro h
    have hp := List.count_pos_iff.mpr h
    have hz := List.count_eq_zero.mpr (List.nodup_cons.mp hnd).1
    have hl := L.reg_count f c
    omega
  intro s m h
  obtain ⟨hp,he,hz⟩ := maskedConstant_correct c (L.reg f) k (L.reg_nodup hn f) hc hk s m
  exact ⟨hp,InverseValues.update L hn v f _ _ _ h.1 he (by simpa only [h.1 f,h.2] using hz),
    (he c hc).trans h.2⟩

private theorem controlled_inverse_copy (L : InverseLayout) (c : Wire)
    (hnd : (c::L.wires).Nodup) (hw : L.Widths) (v : InverseField → Nat) (B : Bool) :
    Triple (fun st => InverseValues L v st ∧ st c=B) (copyRegister (some c) L.x L.vLow)
      (fun st => InverseValues L (Function.update v .v (v .v ^^^ (if B then v .x else 0))) st ∧ st c=B) := by
  have hn := (List.nodup_cons.mp hnd).2
  have hsrc := List.nodup_append'.mpr
    ⟨L.reg_nodup hn .x,L.reg_nodup hn .v,L.reg_disjoint hn .x .v (by decide)⟩
  have hc : c∉L.x++L.vLow := by
    intro h
    have hh : c∈L.wires := by
      simp only [List.mem_append] at h
      rcases h with h|h
      · simp [InverseLayout.wires,h]
      · simp [InverseLayout.wires,InverseLayout.work,h]
    exact (List.nodup_cons.mp hnd).1 hh
  intro s m h
  obtain ⟨hp,he,hz⟩ := copyRegister_correct (some c) L.x L.vLow
    (by simp [InverseLayout.vLow,hw.input,hw.low]) hsrc (by simpa using (fun hh => hc (List.mem_append_right _ hh))) s m
  have hv : regValue L.vLow s.basis=v .v := h.1 .v
  have hx : regValue L.x s.basis=v .x := h.1 .x
  exact ⟨hp,InverseValues.update L hn v .v _ _ _ h.1 he
      (by simpa only [copyValue,hv,hx,h.2] using hz),
    (he c (fun hh => hc (List.mem_append_right _ hh))).trans h.2⟩

private theorem constant_one_head (r : List Wire) (d c : Wire) (hne : r≠[]) :
    xorConstant r 1=[.X (r.headD d)] ∧ maskedConstant c r 1=[.CX c (r.headD d)] := by
  have hz (r : List Wire) : xorConstant r 0=[] ∧ maskedConstant c r 0=[] := by
    induction r with
    | nil => simp [xorConstant,maskedConstant]
    | cons a r ih => simp [xorConstant,maskedConstant,ih.1,ih.2]
  cases r with
  | nil => contradiction
  | cons a r => simp [xorConstant,maskedConstant,(hz r).1,(hz r).2]

/-- 装载后 v = D 或1；控制与外部分母保持，卸载归还全零初值。 -/
theorem divideLoad_values (L : DivideLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (D : Nat) (B : Bool) :
    Triple (fun st => InverseValues L.inverseView (inverseValues D 0 0 0 0) st ∧ st L.control=B)
      (divideLoad L)
      (fun st => InverseValues L.inverseView (inverseValues D p (if B then D else 1) 1 0) st ∧ st L.control=B) ∧
    Triple (fun st => InverseValues L.inverseView (inverseValues D p (if B then D else 1) 1 0) st ∧ st L.control=B)
      (divideUnload L)
      (fun st => InverseValues L.inverseView (inverseValues D 0 0 0 0) st ∧ st L.control=B) := by
  have hn := L.inverse_nodup hnd
  have hu : p<2^(L.inverseView.reg .u).length := by
    change p<2^(L.inner.first.data.reg .u).length
    rw [L.inner.first.data.reg_length]
    have hp : p<2^256 := by norm_num [p]
    have hd : L.inner.first.data.width=257 := by
      simp [KaliskiRoundLayout.data,RoundDataLayout.width,show L.inner.first.low.length=256 from hw.inverse.low]
    exact hp.trans (Nat.pow_lt_pow_right (a:=2) (m:=256)
      (n:=L.inner.first.data.width) (by decide) (by omega))
  have hv : 1<2^(L.inverseView.reg .v).length := by
    change 1<2^L.vLow.length
    rw [L.vLow_length hw]
    exact Nat.one_lt_two_pow (by omega)
  have hs : 1<2^(L.inverseView.reg .s).length := by
    change 1<2^(L.inner.first.data.reg .s).length
    rw [L.inner.first.data.reg_length]
    apply Nat.one_lt_two_pow
    simp [KaliskiRoundLayout.data,RoundDataLayout.width]
  have hu' (U V S : Nat) := controlled_inverse_constant L.inverseView L.control hn
    (inverseValues D U V S 0) B .u p hu
  have hs' (U V S : Nat) := controlled_inverse_constant L.inverseView L.control hn
    (inverseValues D U V S 0) B .s 1 hs
  have hv' (U V S : Nat) := controlled_inverse_constant L.inverseView L.control hn
    (inverseValues D U V S 0) B .v 1 hv
  have hm (U V S : Nat) := controlled_inverse_mask L.inverseView L.control hn
    (inverseValues D U V S 0) B .v 1 hv
  have hc (U V S : Nat) := controlled_inverse_copy L.inverseView L.control hn hw.inverse
    (inverseValues D U V S 0) B
  have equ (U V S K : Nat) : Function.update (inverseValues D U V S 0) .u K=inverseValues D K V S 0 := by
    funext f; cases f <;> simp [inverseValues]
  have eqv (U V S K : Nat) : Function.update (inverseValues D U V S 0) .v K=inverseValues D U K S 0 := by
    funext f; cases f <;> simp [inverseValues]
  have eqs (U V S K : Nat) : Function.update (inverseValues D U V S 0) .s K=inverseValues D U V K 0 := by
    funext f; cases f <;> simp [inverseValues]
  simp only [inverseValues,equ,eqv,eqs] at hu' hs' hv' hm hc
  have hne : L.vLow≠[] := by intro hh; have hl := L.vLow_length hw; simp [hh] at hl
  have hone := constant_one_head L.vLow L.inner.first.high.v L.control hne
  change xorConstant (L.inverseView.reg .v) 1=[.X L.vBit] ∧
    maskedConstant L.control (L.inverseView.reg .v) 1=[.CX L.control L.vBit] at hone
  rw [hone.1] at hv'
  rw [hone.2] at hm
  cases B <;> simp only [Bool.false_eq_true,if_false,if_true,Nat.xor_zero] at *
  all_goals
    have hc0 := hc 0 0 0
    have hcD := hc 0 D 0
    simp at hc0 hcD
  all_goals constructor
  · simpa only [divideLoad,List.append_assoc,List.singleton_append] using
      ((((hv' 0 0 0).seq (hm 0 1 0)).seq (hc 0 1 0)).seq (hu' 0 1 0)).seq (hs' p 1 0)
  · simpa only [divideUnload,List.append_assoc,List.singleton_append] using
      ((((hs' p 1 1).seq (hu' p 1 0)).seq (hc 0 1 0)).seq (hm 0 1 0)).seq (hv' 0 1 0)
  · simpa only [divideLoad,List.append_assoc,List.singleton_append] using
      ((((hv' 0 0 0).seq (hm 0 1 0)).seq hc0).seq (hu' 0 D 0)).seq (hs' p D 0)
  · simpa only [divideUnload,List.append_assoc,List.singleton_append] using
      ((((hs' p D 1).seq (hu' p D 0)).seq hcD).seq (hm 0 0 0)).seq (hv' 0 1 0)

end ECDSAAdd.Arithmetic
