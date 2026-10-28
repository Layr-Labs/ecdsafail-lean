import ECDSAAdd.Arithmetic.BorrowFrame
import ECDSAAdd.Arithmetic.KaliskiRoundProof

namespace ECDSAAdd.Arithmetic

private theorem swap_counts (c : Wire) (a b : List Wire) (hlen : a.length=b.length) :
    toffoliCount (swapRegisters c a b)=a.length ∧ measurementCount (swapRegisters c a b)=0 ∧
    toffoliCount (exchangeRegisters a b)=0 ∧ measurementCount (exchangeRegisters a b)=0 := by
  have ha := copyRegister_counts (some c) a b hlen
  have hb := copyRegister_counts none b a hlen.symm
  have hc := copyRegister_counts none a b hlen
  simp [swapRegisters,exchangeRegisters,ha.1,ha.2,hb.1,hb.2,hc.1,hc.2]

private theorem inplace_counts (L : RoundDataLayout) (f g : RoundField) (c : Wire)
    (neg : Bool) (hw : 0<L.width) :
    toffoliCount (inplaceArithmetic L f g c neg)=2*L.width-1 ∧
    measurementCount (inplaceArithmetic L f g c neg)=2*L.width-1 := by
  have hm := measuredMaskedInPlace_counts c (L.reg g) (L.reg .y) (L.reg f)
    ((L.reg .carry).take (L.width-1)) L.cin
    (by simp [L.reg_length]) (by simp [L.reg_length])
    (by simp [L.reg_length]; omega)
  simp only [L.reg_length] at hm
  cases neg <;> simpa only [inplaceArithmetic,if_true,Bool.false_eq_true,if_false,L.reg_length] using
    (by tauto : _)

private theorem body_counts (L : RoundDataLayout) (a sw su : Wire) (hw : 0<L.width) :
    toffoliCount (kaliskiBodyProgram L a sw su)=10*L.width-4 ∧
    measurementCount (kaliskiBodyProgram L a sw su)=4*L.width-2 ∧
    toffoliCount (kaliskiUnbodyProgram L a sw su)=10*L.width-4 ∧
    measurementCount (kaliskiUnbodyProgram L a sw su)=4*L.width-2 := by
  have huv := swap_counts sw L.u L.v (by simp [RoundDataLayout.u,RoundDataLayout.v,L.reg_length])
  have hrs := swap_counts sw L.r L.s (by simp [RoundDataLayout.r,RoundDataLayout.s,L.reg_length])
  have hmU := inplace_counts L .u .v su true hw
  have hmR := inplace_counts L .r .s su false hw
  have hmUi := inplace_counts L .u .v su false hw
  have hmRi := inplace_counts L .r .s su true hw
  have hsu := shift_counts a L.u
  have hss := shift_counts a L.s
  simp only [kaliskiBodyProgram,kaliskiUnbodyProgram,swapDataPairs,toffoliCount_append,measurementCount_append,
    huv.1,huv.2.1,hrs.1,hrs.2.1,hmU.1,hmU.2,hmR.1,hmR.2,hmUi.1,hmUi.2,hmRi.1,hmRi.2,
    hsu.1,hsu.2.1,hsu.2.2.1,hsu.2.2.2,hss.1,hss.2.1,hss.2.2.1,hss.2.2.2]
  simp only [RoundDataLayout.u,RoundDataLayout.r,RoundDataLayout.s,L.reg_length]
  omega

theorem recordRound_counts (L : KaliskiRoundLayout) :
    toffoliCount (recordRound L)=L.data.width+5 ∧ measurementCount (recordRound L)=L.data.width := by
  have h := compareLt_counts (some L.bothWork) L.v L.u (L.data.reg .carry) L.cin L.swap
    (by simp [KaliskiRoundLayout.v,KaliskiRoundLayout.u,RoundDataLayout.v,RoundDataLayout.u,L.data.reg_length])
    (by simp [KaliskiRoundLayout.u,RoundDataLayout.u,L.data.reg_length])
  simp only [recordRound,toffoliCount_append,measurementCount_append,h.1,h.2.1]
  simp [KaliskiRoundLayout.u,RoundDataLayout.u,L.data.reg_length,toffoliCount,measurementCount]
  omega

/-- 正逆轮使用相同次数的 CCX 与测量；每轮复用数据宽度 w 的算术工作区。 -/
theorem kaliskiRound_counts (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) (hw : L.counter.width=10) (i : Nat) :
    toffoliCount (kaliskiRound L i)=12*L.data.width+31 ∧
    measurementCount (kaliskiRound L i)=6*L.data.width+28 ∧
    toffoliCount (kaliskiUnround L i)=12*L.data.width+31 ∧
    measurementCount (kaliskiUnround L i)=6*L.data.width+28 := by
  have hb := body_counts L.data L.active L.swap L.subtract (by simp [KaliskiRoundLayout.data,RoundDataLayout.width])
  have hr := recordRound_counts L
  have hz := zeroControlled_counts L.active L.done (L.data.zeroBits .v)
  have hc := counter_resources L.counter (L.counter_nodup hnd) hw
  have hci := counter_resources L.counter.swapCounter (L.counter.swapCounter_perm.nodup_iff.mpr (L.counter_nodup hnd))
    (L.counter.swapCounter_fields.2.2.2.2.2.trans hw)
  have ha := counterActiveXor_counts L.comparator L.active i
  rw [L.comparator_fields.2.2.2.2.2,hw] at ha
  have hl : toffoliCount (loadActive L)=0 ∧ measurementCount (loadActive L)=0 := ⟨rfl,rfl⟩
  simp only [kaliskiRound,kaliskiUnround,toffoliCount_append,measurementCount_append,hl.1,hl.2,hr.1,hr.2,
    hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,hc.1,hc.2.1,hci.2.2.2.1,hci.2.2.2.2.1,hz.1,hz.2,
    roundActiveXor,ha.1,ha.2]
  simp only [RoundDataLayout.zeroBits,List.length_map]
  have hpos : 0<L.data.width := by simp [KaliskiRoundLayout.data,RoundDataLayout.width]
  change 0<L.data.bits.length at hpos
  simp only [RoundDataLayout.width] at *
  omega

end ECDSAAdd.Arithmetic
