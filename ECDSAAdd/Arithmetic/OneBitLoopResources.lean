import ECDSAAdd.Arithmetic.OneBitLoop

namespace ECDSAAdd.Arithmetic

def KaliskiRoundLayout.usedOneBitTapeWires (L : KaliskiRoundLayout) (sw : Wire) (ts : List Wire) : List Wire :=
  sw::(ts++L.usedSharedWires)

theorem KaliskiRoundLayout.usedOneBitTapeWires_sublist (L : KaliskiRoundLayout) (sw : Wire) (ts : List Wire) :
    (L.usedOneBitTapeWires sw ts).Sublist (L.oneBitTapeWires sw ts) :=
  List.Sublist.cons₂ sw (((L.data.usedWires_sublist.append_left _).append_right _).append_left _)

private theorem usedRecord_perm (L : KaliskiRoundLayout) (r : RoundRecord) :
    (L.withRecord r).usedWires.Perm (r.wires++L.usedSharedWires) := by
  apply List.perm_iff_count.mpr
  intro w
  simp [KaliskiRoundLayout.usedWires,KaliskiRoundLayout.withRecord,KaliskiRoundLayout.usedSharedWires,
    RoundRecord.wires,List.count_cons,KaliskiRoundLayout.data,KaliskiRoundLayout.counter]
  omega

private theorem usedShared_swap (L : KaliskiRoundLayout) :
    L.swapCounter.usedSharedWires.Perm L.usedSharedWires := by
  change (_++L.swapCounter.data.usedWires++L.swapCounter.counter.wires).Perm
    (_++L.data.usedWires++L.counter.wires)
  rw [L.swapCounter_data,L.swapCounter_counter]
  exact List.Perm.append_left _ L.counter.swapCounter_perm

theorem oneBitLoop_counts (L : KaliskiRoundLayout) (sw : Wire) (rs : List Wire) (i : Nat)
    (hnd : (L.oneBitTapeWires sw rs).Nodup) (hw : L.counter.width=10) :
    toffoliCount (oneBitLoop L sw i rs)=rs.length*(12*L.data.width+31) ∧
    measurementCount (oneBitLoop L sw i rs)=rs.length*(6*L.data.width+29) ∧
    toffoliCount (oneBitUnloop L sw i rs)=rs.length*(12*L.data.width+32) ∧
    measurementCount (oneBitUnloop L sw i rs)=rs.length*(6*L.data.width+28) := by
  induction rs generalizing L i with
  | nil => simp [oneBitLoop,oneBitUnloop,toffoliCount,measurementCount]
  | cons r rs ih =>
    have hr := oneBitRound_counts (L.withRecord ⟨sw,r⟩) (L.oneBit_round_nodup sw r rs hnd) hw i
    have hnw : L.swapCounter.counter.width=10 := by rw [L.swapCounter_counter,L.counter.swapCounter_fields.2.2.2.2.2,hw]
    have ht := ih L.swapCounter (i+1) (L.oneBit_tail_nodup sw r rs hnd) hnw
    change _=rs.length*(12*L.data.width+31) ∧ _=rs.length*(6*L.data.width+29) ∧
      _=rs.length*(12*L.data.width+32) ∧ _=rs.length*(6*L.data.width+28) at ht
    change _=12*L.data.width+31 ∧ _=6*L.data.width+29 ∧ _=12*L.data.width+32 ∧ _=6*L.data.width+28 at hr
    simp only [oneBitLoop,oneBitUnloop,toffoliCount_append,measurementCount_append,hr.1,hr.2.1,
      hr.2.2.1,hr.2.2.2,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,List.length_cons,Nat.add_mul,Nat.one_mul]
    simp [Nat.add_comm]

/-- 空循环没有线路；非空循环恰好使用共享布局和整个两位记录带。 -/
theorem oneBitLoop_wires (L : KaliskiRoundLayout) (sw : Wire) (rs : List Wire) (i : Nat)
    (hw : L.counter.width=10) (hd : 2≤L.data.width) :
    wires (oneBitLoop L sw i rs)=(if rs.isEmpty then ∅ else (L.usedOneBitTapeWires sw rs).toFinset) ∧
    wires (oneBitUnloop L sw i rs)=(if rs.isEmpty then ∅ else (L.usedOneBitTapeWires sw rs).toFinset) := by
  induction rs generalizing L i with
  | nil => simp [oneBitLoop,oneBitUnloop,wires]
  | cons r rs ih =>
    have hr := oneBitRound_wires (L.withRecord ⟨sw,r⟩) hw hd i
    have hnw : L.swapCounter.counter.width=10 := by rw [L.swapCounter_counter,L.counter.swapCounter_fields.2.2.2.2.2,hw]
    have ht := ih L.swapCounter (i+1) hnw hd
    have hp : (L.withRecord ⟨sw,r⟩).usedWires.toFinset=([sw,r]++L.usedSharedWires).toFinset := by
      ext w; simpa only [List.mem_toFinset] using (usedRecord_perm L ⟨sw,r⟩).mem_iff (a:=w)
    have hs : L.swapCounter.usedSharedWires.toFinset=L.usedSharedWires.toFinset := by
      ext w; simpa only [List.mem_toFinset] using (usedShared_swap L).mem_iff (a:=w)
    simp only [oneBitLoop,oneBitUnloop,wires_append,hr.1,hr.2,ht.1,ht.2,hp,List.isEmpty_cons,Bool.false_eq_true,if_false]
    cases rs with
    | nil => simp [KaliskiRoundLayout.usedOneBitTapeWires]
    | cons r' rs =>
      simp only [List.isEmpty_cons,Bool.false_eq_true,if_false,KaliskiRoundLayout.usedOneBitTapeWires,
        List.toFinset_cons,List.toFinset_append,hs]
      constructor <;> ext w <;> simp [Finset.mem_union,or_left_comm,or_comm]

theorem oneBitLoop_qubits (L : KaliskiRoundLayout) (sw : Wire) (rs : List Wire) (i : Nat)
    (hnd : (L.oneBitTapeWires sw rs).Nodup) (hw : L.counter.width=10) (hd : 2≤L.data.width) (hne : rs≠[]) :
    qubitCount (oneBitLoop L sw i rs)=7*L.data.width+46+rs.length+1 ∧
    qubitCount (oneBitUnloop L sw i rs)=7*L.data.width+46+rs.length+1 := by
  have hdw (bs : List RoundBit) : (bs.flatMap RoundBit.usedWires).length=7*bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp [RoundBit.usedWires,ih]; omega
  have hlen : (L.usedOneBitTapeWires sw rs).length=7*L.data.width+46+rs.length+1 := by
    simp only [KaliskiRoundLayout.usedOneBitTapeWires,KaliskiRoundLayout.usedSharedWires,List.length_append,
      List.length_cons,List.length_nil,RoundDataLayout.usedWires,hdw,AdderLayout.wires,addWires_length]
    change L.counter.bits.length=10 at hw
    simp only [RoundDataLayout.width]
    omega
  have h := oneBitLoop_wires L sw rs i hw hd
  have he : rs.isEmpty=false := by cases rs <;> simp_all
  simp only [he,Bool.false_eq_true,if_false] at h
  simp only [qubitCount,h.1,h.2,List.toFinset_card_of_nodup ((L.usedOneBitTapeWires_sublist sw rs).nodup hnd),hlen,and_self]

end ECDSAAdd.Arithmetic
