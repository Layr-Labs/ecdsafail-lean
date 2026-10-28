import ECDSAAdd.Arithmetic.ValueResources

namespace ECDSAAdd.Arithmetic

def RoundBit.valueUsedWires (b : RoundBit) : List Wire := [b.u,b.v,b.y,b.carry,b.zero]
def RoundDataLayout.valueUsedWires (L : RoundDataLayout) : List Wire :=
  L.cin :: L.bits.flatMap RoundBit.valueUsedWires
def KaliskiRoundLayout.valueUsedWires (L : KaliskiRoundLayout) : List Wire :=
  [L.done,L.swap,L.subtract,L.oddWork,L.bothWork,L.compareCin] ++ L.data.valueUsedWires ++ L.counter.wires

theorem RoundDataLayout.valueUsedWires_sublist (L : RoundDataLayout) :
    L.valueUsedWires.Sublist L.wires := by
  apply List.Sublist.cons₂
  suffices h : ∀ bs : List RoundBit,
      (bs.flatMap RoundBit.valueUsedWires).Sublist (bs.flatMap RoundBit.wires) from h L.bits
  intro bs
  induction bs with
  | nil => exact List.Sublist.refl _
  | cons b bs ih =>
    have hb : b.valueUsedWires.Sublist b.wires := by
      exact List.Sublist.cons₂ _ (List.Sublist.cons₂ _
        (List.Sublist.cons _ (List.Sublist.cons _ (List.Sublist.cons₂ _
          (List.Sublist.cons _ (List.Sublist.refl _))))))
    exact hb.append ih

theorem KaliskiRoundLayout.valueUsedWires_sublist (L : KaliskiRoundLayout) :
    L.valueUsedWires.Sublist L.wires :=
  (L.data.valueUsedWires_sublist.append_left _).append_right _

private theorem swap_wires (c : Wire) (a b : List Wire) (hlen : a.length=b.length) (hpos : 0<a.length) :
    wires (swapRegisters c a b)=(c::(a++b)).toFinset ∧
    wires (exchangeRegisters a b)=(a++b).toFinset := by
  have hae : a.isEmpty=false := by cases a <;> simp_all
  have hbe : b.isEmpty=false := by cases b <;> simp_all
  have ha := copyRegister_wires (some c) a b hlen
  have hb := copyRegister_wires none b a hlen.symm
  have hc := copyRegister_wires none a b hlen
  simp only [hae,hbe,Bool.false_eq_true,if_false] at ha hb hc
  constructor <;> ext w <;>
    simp only [swapRegisters,exchangeRegisters,wires_append,ha,hb,hc,Finset.mem_union,List.mem_toFinset,
      List.mem_cons,List.mem_append,Option.toList_some,Option.toList_none,List.mem_nil_iff,or_false,false_or] <;> tauto

private theorem inplace_wires (L : RoundDataLayout) (f g : RoundField) (c : Wire) (neg : Bool)
    (hw : 0<L.width) :
    wires (inplaceArithmetic L f g c neg)=
      (c::L.cin::(L.reg g++L.reg .y++L.reg f++(L.reg .carry).take (L.width-1))).toFinset := by
  have hm := measuredMaskedInPlace_wires c (L.reg g) (L.reg .y) (L.reg f)
    ((L.reg .carry).take (L.width-1)) L.cin
    (by simp [L.reg_length]) (by simp [L.reg_length]) (by simp [L.reg_length]; omega)
  cases neg <;> simp only [inplaceArithmetic,Bool.false_eq_true,if_false,if_true] <;> tauto

private def bodyWires (L : RoundDataLayout) (a sw su : Wire) : Finset Wire :=
  ([a,sw,su,L.cin]++L.u++L.v++L.reg .y++(L.reg .carry).take (L.width-1)).toFinset

private theorem body_wires (L : RoundDataLayout) (a sw su : Wire) (hw : 2≤L.width) :
    wires (valueBodyProgram L a sw su)=bodyWires L a sw su ∧
    wires (valueUnbodyProgram L a sw su)=bodyWires L a sw su := by
  have hp : 0<L.width := by omega
  have huv := (swap_wires sw L.u L.v (by simp [RoundDataLayout.u,RoundDataLayout.v,L.reg_length])
    (by simpa [RoundDataLayout.u,L.reg_length] using hp)).1
  have hru := shift_wires a L.u
  have hu : ¬L.u.length<2 := by simpa [RoundDataLayout.u,L.reg_length] using (show ¬L.width<2 by omega)
  simp only [hu,if_false] at hru
  have hiU := inplace_wires L .u .v su true hp
  have hiUi := inplace_wires L .u .v su false hp
  constructor <;>
    simp only [valueBodyProgram,valueUnbodyProgram,wires_append,
      huv,hru.1,hru.2,hiU,hiUi]
  all_goals
    ext w
    simp only [bodyWires,Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_nil_iff,
      RoundDataLayout.u,RoundDataLayout.v]
    clear huv hru hiU hiUi hu hp hw
    tauto

private theorem data_interface (L : RoundDataLayout) :
    L.valueUsedWires.toFinset=(L.cin::(L.u++L.v++L.reg .y++L.reg .carry++L.reg .zero)).toFinset := by
  ext w
  simp [RoundDataLayout.valueUsedWires,RoundDataLayout.u,RoundDataLayout.v,
    RoundDataLayout.reg,RoundBit.valueUsedWires,RoundBit.get,and_or_left,exists_or,eq_comm]

private theorem zero_interface (L : RoundDataLayout) :
    ((L.zeroBits .v).flatMap ZeroBit.wires).toFinset=(L.v++L.reg .zero).toFinset := by
  ext w
  simp [RoundDataLayout.zeroBits,ZeroBit.wires,RoundDataLayout.v,RoundDataLayout.reg,
    RoundBit.get,and_or_left,exists_or,eq_comm]

private theorem activity_wires (L : KaliskiRoundLayout) (i : Nat) :
    wires (roundActiveXor L i)=(L.active::L.compareCin::
      (L.comparator.x++L.comparator.y++L.comparator.carry)).toFinset := by
  exact counterActiveXor_wires L.comparator L.active i

/-- 静态线路并集恰好等于单轮布局，包括共享工作线而非“最大同时存活”估计。 -/
theorem valueRound_wires (L : KaliskiRoundLayout) (hw : L.counter.width=10)
    (hd : 2≤L.data.width) (i : Nat) :
    wires (valueRound L i)=L.valueUsedWires.toFinset ∧ wires (valueUnround L i)=L.valueUsedWires.toFinset := by
  have hb := body_wires L.data L.active L.swap L.subtract hd
  have hr := recordRound_wires L
  have ha := activity_wires L i
  have hz := zeroControlled_wires L.active L.done (L.data.zeroBits .v)
  have hc := (counterMove_wires L.counter hw).1
  have hci := (counterMove_wires L.counter.swapCounter (L.counter.swapCounter_fields.2.2.2.2.2.trans hw)).2
  have hcp : L.counter.swapCounter.wires.toFinset=L.counter.wires.toFinset := by
    ext w
    simpa only [List.mem_toFinset] using L.counter.swapCounter_perm.mem_iff (a:=w)
  rw [hcp] at hci
  have hl : wires (loadActive L)=[L.active,L.done].toFinset := by
    ext w; simp [loadActive,wires,Instr.wires,or_comm]
  have hdata := data_interface L.data
  have hzero := zero_interface L.data
  constructor <;>
    simp only [valueRound,valueUnround,wires_append,hl,hr,ha,hb.1,hb.2,hz,hc,hci]
  all_goals
    ext w
    have hD := (congrArg (fun s => w∈s) hdata).to_iff
    have hZ := (congrArg (fun s => w∈s) hzero).to_iff
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hD hZ
    have hcomp : ∀ w, w∈L.comparator.x++L.comparator.y++L.comparator.carry → w∈L.counter.wires := by
      intro w hm
      have hf := L.counter.swapCounter_perm.mem_iff (a:=w)
      have ht : w∈L.counter.swapCounter.wires := by
        simp only [List.mem_append] at hm
        rcases hm with (h|h)|h
        · exact L.counter.swapCounter.reg_subset.1 h
        · exact L.counter.swapCounter.reg_subset.2.1 h
        · exact L.counter.swapCounter.reg_subset.2.2.2 h
      exact hf.mp ht
    have hcm := hcomp w
    simp only [List.mem_append] at hcm
    have hac : w=L.active → w∈L.counter.wires := fun he => he ▸ List.mem_cons_self
    have htake : w∈(L.data.reg .carry).take (L.data.width-1) → w∈L.data.reg .carry :=
      fun h => List.mem_of_mem_take h
    simp only [bodyWires,KaliskiRoundLayout.valueUsedWires,Finset.mem_union,List.mem_toFinset,List.mem_cons,
      List.mem_append,List.mem_nil_iff,hD,hZ]
    simp only [KaliskiRoundLayout.u,KaliskiRoundLayout.v,RoundDataLayout.u,RoundDataLayout.v,
      ] at *
    clear hb hr ha hz hc hci hcp hl hdata hzero hD hZ
    aesop

/-- 5w 数据/工作线路、双银行十位计数器及常数个控制位的精确总数。 -/
theorem valueRound_qubits (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (hd : 2≤L.data.width) (i : Nat) :
    qubitCount (valueRound L i)=5*L.data.width+48 ∧
    qubitCount (valueUnround L i)=5*L.data.width+48 := by
  have hlen : L.valueUsedWires.length=5*L.data.width+48 := by
    have he (bs : List RoundBit) : (bs.flatMap RoundBit.valueUsedWires).length=5*bs.length := by
      induction bs with
      | nil => simp
      | cons b bs ih => simp [RoundBit.valueUsedWires,ih]; omega
    simp only [KaliskiRoundLayout.valueUsedWires,List.length_append,List.length_cons,List.length_nil,
      RoundDataLayout.valueUsedWires,he,AdderLayout.wires,addWires_length]
    change L.counter.bits.length=10 at hw
    simp only [RoundDataLayout.width]
    omega
  have h := valueRound_wires L hw hd i
  simp only [qubitCount,h.1,h.2,List.toFinset_card_of_nodup (L.valueUsedWires_sublist.nodup hnd),hlen,and_self]

end ECDSAAdd.Arithmetic
