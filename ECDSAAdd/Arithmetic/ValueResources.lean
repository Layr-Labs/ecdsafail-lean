import ECDSAAdd.Arithmetic.ValueRound

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
    toffoliCount (valueBodyProgram L a sw su)=5*L.width-2 ∧
    measurementCount (valueBodyProgram L a sw su)=2*L.width-1 ∧
    toffoliCount (valueUnbodyProgram L a sw su)=5*L.width-2 ∧
    measurementCount (valueUnbodyProgram L a sw su)=2*L.width-1 := by
  have huv := swap_counts sw L.u L.v (by simp [RoundDataLayout.u,RoundDataLayout.v,L.reg_length])
  have hmU := inplace_counts L .u .v su true hw
  have hmUi := inplace_counts L .u .v su false hw
  have hsu := shift_counts a L.u
  simp only [valueBodyProgram,valueUnbodyProgram,toffoliCount_append,measurementCount_append,
    huv.1,huv.2.1,hmU.1,hmU.2,hmUi.1,hmUi.2,
    hsu.1,hsu.2.1,hsu.2.2.1,hsu.2.2.2]
  simp only [RoundDataLayout.u,L.reg_length]
  omega

/-- 正逆轮使用相同次数的 CCX 与测量；每轮复用数据宽度 w 的算术工作区。 -/
theorem valueRound_counts (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) (hw : L.counter.width=10) (i : Nat) :
    toffoliCount (valueRound L i)=7*L.data.width+33 ∧
    measurementCount (valueRound L i)=4*L.data.width+29 ∧
    toffoliCount (valueUnround L i)=7*L.data.width+33 ∧
    measurementCount (valueUnround L i)=4*L.data.width+29 := by
  have hb := body_counts L.data L.active L.swap L.subtract (by simp [KaliskiRoundLayout.data,RoundDataLayout.width])
  have hr := recordRound_counts L
  have hz := zeroControlled_counts L.active L.done (L.data.zeroBits .v)
  have hc := counter_resources L.counter (L.counter_nodup hnd) hw
  have hci := counter_resources L.counter.swapCounter (L.counter.swapCounter_perm.nodup_iff.mpr (L.counter_nodup hnd))
    (L.counter.swapCounter_fields.2.2.2.2.2.trans hw)
  have ha := counterActiveXor_counts L.comparator L.active i
  rw [L.comparator_fields.2.2.2.2.2,hw] at ha
  have hl : toffoliCount (loadActive L)=0 ∧ measurementCount (loadActive L)=0 := ⟨rfl,rfl⟩
  simp only [valueRound,valueUnround,toffoliCount_append,measurementCount_append,hl.1,hl.2,hr.1,hr.2,
    hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,hc.1,hc.2.1,hci.2.2.2.1,hci.2.2.2.2.1,hz.1,hz.2,
    roundActiveXor,ha.1,ha.2]
  simp only [RoundDataLayout.zeroBits,List.length_map]
  have hpos : 0<L.data.width := by simp [KaliskiRoundLayout.data,RoundDataLayout.width]
  change 0<L.data.bits.length at hpos
  simp only [RoundDataLayout.width] at *
  omega


end ECDSAAdd.Arithmetic
