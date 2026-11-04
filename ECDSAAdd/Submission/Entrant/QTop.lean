import ECDSAAdd.Submission.Entrant.MainB

/-!
Output-only `+flag·p` correction for the measured canonical modular fold `qprog`.

The final carry of `mappedConstAdd (some flag) extended …` (into the `high` bit) always
equals `flag` whenever `A<p` and `X<p`, so the correction can run on `out` only and the
top majority becomes a single `CX flag high`.  This file forks every square-stage
declaration whose statement mentions `qprog` (suffix `Tq`), with counts one smaller per call.
-/

section
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout RecordedQuantum
/-- `qprogTq` whose `+flag·p` correction runs on the 256 output bits only.  Under the canonical
preconditions of `qprog_frameTq` the carry out of that correction always equals `flag`, so the high
bit is set by one CNOT from `flag` instead of a 257th majority/erase pair (−1 Toffoli, −1 measurement). -/
def qprogTq (K : MeasuredCanonicalModLayout) (p : Nat) : Program :=
  notRegister K.out++K.sum++[.CX K.high K.flag,.X K.flag]++
    mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p++[.CX K.flag K.high]++
    [.X K.high,.X K.flag]++
    eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag

namespace QCore

/-- The output-only correction: `out += flag·c (mod 2^n)`, then `high ^= flag`. -/
theorem correctionT_frame (K : MeasuredCanonicalModLayout) (n c : Nat) (hw : K.Widths n)
    (hn : K.wires.Nodup) (hcb : c<2^n) (npos : 0<n) (base : BasisState)
    (O : Nat) (H F : Bool) (hc : ∀q∈K.carry,base q=false) (hi : base K.cin=false) :
    Triple (K.Frame base O H F)
      (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin c++[.CX K.flag K.high])
      (K.Frame base (((if F then c else 0)+O)%2^n) (H ^^ F) F) := by
  have away := K.flags_away hn
  have nd : (K.cin::(K.out++K.carry.take (K.out.length-1))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    have takeBound := (List.take_sublist (K.out.length-1) K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have srcAway : ∀q∈some K.flag,q∉K.cin::(K.out++K.carry.take (K.out.length-1)) := by
    intro q hq bad
    have eq : q=K.flag := by simpa [eq_comm] using hq
    subst q
    have h := List.nodup_iff_count.mp hn K.flag
    have pos := List.count_pos_iff.mpr bad
    have takeBound := (List.take_sublist (K.out.length-1) K.carry).count_le K.flag
    simp only [MeasuredCanonicalModLayout.wires,List.count_append,List.count_cons,List.count_nil,
      beq_self_eq_true,if_true] at h pos
    omega
  have carryLen : (K.carry.take (K.out.length-1)).length+1=K.out.length := by
    simp [hw.carry,hw.out]; omega
  have cBound : c<2^K.out.length := by rw [hw.out]; exact hcb
  have s2 := K.cx_high_frame hn base (((if F then c else 0)+O)%2^n) H F
  refine Triple.seq ?_ s2
  intro s m hf
  have clean := MeasuredCanonicalModLayout.Frame.clean K hn base s.basis O H F hf hc hi
  obtain ⟨phase,same,value⟩ := mappedConstAdd_correct (some K.flag) K.out (K.carry.take (K.out.length-1))
    K.cin c nd srcAway carryLen cBound s m (fun q hq => clean.1 q (List.mem_of_mem_take hq))
  refine ⟨phase,?_,?_,?_,?_⟩
  · rw [value,hf.1,clean.2,hw.out]
    simp only [mappedEnabled,Option.map_some,Option.getD_some,hf.2.2.1,Bool.toNat_false,Nat.add_zero]
  · exact (same K.high away.1).trans hf.2.1
  · exact (same K.flag (fun bad => away.2.1 (by simp [MeasuredCanonicalModLayout.extended,bad]))).trans hf.2.2.1
  · intro q hq
    have no : q∉K.out := fun bad => hq (by simp [MeasuredCanonicalModLayout.mutable,bad])
    exact (same q no).trans (hf.2.2.2 q hq)

theorem qprog_frameTq (K : MeasuredCanonicalModLayout) (n c p : Nat) (hw : K.Widths n)
    (hn : K.wires.Nodup) (npos : 0<n) (hpc : p+c=2^n) (hcp : 0<c)
    (base : BasisState) (A X : Nat) (ha : regValue K.src base=A)
    (hA : A<p) (hX : X<p) (hc : ∀q∈K.carry,base q=false) (hi : base K.cin=false) :
    Triple (K.Frame base X false false) (qprogTq K p)
      (K.Frame base ((A+(p-1-X))%p) false false) := by
  have bpos : 0<2^n := by positivity
  have hR : 2^n-1-X=(p-1-X)+c := by omega
  have sumBound : A+(2^n-1-X)<2^(n+1) := by rw [Nat.pow_succ]; omega
  have flagPred : decide (2^n≤A+(2^n-1-X))=decide ((A+(p-1-X))%p<A) := by
    have h := exactFold_recover_flag (p-1-X) A p (by omega) hA
    rw [Nat.add_comm (p-1-X) A] at h
    apply decide_eq_decide.mpr
    rw [h]
    omega
  generalize hr : decide (2^n≤A+(2^n-1-X))=r at flagPred
  have s1 := not_frame K n hw hn base X
  have s2 := K.sum_frame n hw hn base A (2^n-1-X) ha sumBound hc hi
  rw [hr] at s2
  have s3 : Triple (K.Frame base ((A+(2^n-1-X))%2^n) r false) [.CX K.high K.flag]
      (K.Frame base ((A+(2^n-1-X))%2^n) r r) := by
    simpa using K.cx_flag_frame hn base ((A+(2^n-1-X))%2^n) r false
  have s4 := x_flag_frame K hn base ((A+(2^n-1-X))%2^n) r r
  have s5 := correctionT_frame K n p hw hn (by omega) npos base ((A+(2^n-1-X))%2^n) r (!r) hc hi
  have vlow : ((if !r then p else 0)+(A+(2^n-1-X))%2^n)%2^n=(A+(p-1-X))%p := by
    cases r
    · have small : ¬2^n≤A+(2^n-1-X) := by simpa using hr
      have lt : A+(p-1-X)<p := by omega
      simp only [Bool.not_false,if_true]
      rw [Nat.mod_eq_of_lt (show A+(2^n-1-X)<2^n by omega),Nat.mod_eq_of_lt lt,
        show p+(A+(2^n-1-X))=(A+(p-1-X))+2^n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    · have big : 2^n≤A+(2^n-1-X) := by simpa using hr
      have ge : p≤A+(p-1-X) := by omega
      simp only [Bool.not_true,Bool.false_eq_true,if_false,Nat.zero_add]
      rw [Nat.mod_mod,Nat.mod_eq_sub_mod big,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_sub_mod ge,
        Nat.mod_eq_of_lt (by omega)]
      omega
  have hx : (r ^^ !r)=true := by cases r <;> rfl
  rw [vlow,hx] at s5
  have s6 := x_high_frame K hn base ((A+(p-1-X))%p) true (!r)
  have s7 := x_flag_frame K hn base ((A+(p-1-X))%p) (!true) (!r)
  simp only [Bool.not_true,Bool.not_not] at s7
  have s8 := K.erase_frame n hw hn npos base A ((A+(p-1-X))%p) false ha hc hi
  rw [←flagPred] at s8
  have all := ((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8
  simpa only [qprogTq,List.append_assoc,List.cons_append,List.singleton_append] using all

theorem qprog_correctTq (K : MeasuredCanonicalModLayout) (n c p : Nat) (hw : K.Widths n)
    (hn : K.wires.Nodup) (npos : 0<n) (hpc : p+c=2^n) (hcp : 0<c)
    (A X : Nat) (hA : A<p) (hX : X<p) (s : State) (m : List Bool)
    (ha : regValue K.src s.basis=A) (hx : regValue K.out s.basis=X)
    (hh : s.basis K.high=false) (hf : s.basis K.flag=false)
    (hc : ∀q∈K.carry,s.basis q=false) (hi : s.basis K.cin=false) :
    (run (qprogTq K p) m s).phase=s.phase ∧
    regValue K.out (run (qprogTq K p) m s).basis=(A+(p-1-X))%p ∧
    ∀q,q∉K.out → (run (qprogTq K p) m s).basis q=s.basis q := by
  have initial : K.Frame s.basis X false false s.basis := ⟨hx,hh,hf,fun _ _ => rfl⟩
  obtain ⟨phase,post⟩ := qprog_frameTq K n c p hw hn npos hpc hcp s.basis A X ha hA hX hc hi s m initial
  refine ⟨phase,post.1,?_⟩
  intro q hq
  by_cases high : q=K.high
  · subst q; exact post.2.1.trans hh.symm
  by_cases flag : q=K.flag
  · subst q; exact post.2.2.1.trans hf.symm
  exact post.2.2.2 q (by simpa only [MeasuredCanonicalModLayout.mutable,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or] using ⟨hq,high,flag⟩)

theorem qprog_countsTq (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (hn : 0<n) :
    toffoliCount (qprogTq K p)=3*n-2 ∧ measurementCount (qprogTq K p)=3*n-1 := by
  have extendedLength : K.extended.length=n+1 := by simp [MeasuredCanonicalModLayout.extended,hw.out]
  have sourceLength : (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)]).length=n+1 := by
    simp [mappedRead,hw.src]
  have sumCounts := mappedAdd_counts (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)])
    K.extended K.carry K.cin (sourceLength.trans extendedLength.symm)
    (by rw [hw.carry,extendedLength])
  have correction := mappedConstAdd_counts (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p
    (by simp [hw.carry,hw.out]; omega)
  have eraseCounts := eraseLtChain_counts K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
    (hw.out.trans hw.src.symm) (by simp [hw.carry,hw.out,hw.src]; omega)
  have nc := notRegister_counts K.out
  constructor
  · simp only [qprogTq,MeasuredCanonicalModLayout.sum,toffoliCount_append,toffoliCount]
    rw [sumCounts.1,correction.1,eraseCounts.1,nc.1,extendedLength,hw.src,hw.out]
    omega
  · simp only [qprogTq,MeasuredCanonicalModLayout.sum,measurementCount_append,measurementCount]
    rw [sumCounts.2,correction.2,eraseCounts.2,nc.2,extendedLength,hw.src,hw.out]
    omega

theorem qprog_supportTq (K : MeasuredCanonicalModLayout) (p : Nat) :
    ECDSAAdd.wires (qprogTq K p)⊆K.wires.toFinset := by
  have old := ECDSAAdd.Entrant.QCore.qprog_support K p
  simp only [ECDSAAdd.Entrant.qprog,MeasuredCanonicalModLayout.sum,wires_append,Finset.union_subset_iff] at old
  have hm : ECDSAAdd.wires (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p)⊆
      K.wires.toFinset := by
    apply (mappedConstAdd_wires_subset _ _ _ _ _).trans
    intro q hq
    have tk : q∈K.carry.take (K.out.length-1) → q∈K.carry := List.mem_of_mem_take
    simp only [List.mem_toFinset,List.mem_append,Option.toList_some,List.mem_cons,List.not_mem_nil,
      or_false,MeasuredCanonicalModLayout.wires] at hq ⊢
    tauto
  have g : ECDSAAdd.wires [Instr.CX K.flag K.high]⊆K.wires.toFinset := by
    intro q hq; simp [ECDSAAdd.wires,Instr.wires,MeasuredCanonicalModLayout.wires] at hq ⊢; tauto
  simp only [qprogTq,MeasuredCanonicalModLayout.sum,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨old.1.1.1.1.1,old.1.1.1.1.2⟩,old.1.1.1.2⟩,hm⟩,g⟩,old.1.2⟩,old.2⟩

theorem qprog_physicalTq (K : MeasuredCanonicalModLayout) (p : Nat) (hn : K.wires.Nodup) :
    GatePhysical (qprogTq K p) := by
  have old := ECDSAAdd.Entrant.QCore.qprog_physical K p hn
  simp only [ECDSAAdd.Entrant.qprog,gatePhysical_append] at old
  have hf : K.flag≠K.high := fun h => (K.flags_away hn).2.2.2 h.symm
  have nd : (K.cin::K.out++K.carry.take (K.out.length-1)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    have takeBound := (List.take_sublist (K.out.length-1) K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hm : GatePhysical (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p) := by
    apply mappedConstAdd_physical _ _ _ _ _ nd
    intro q hq bad
    have eq : q=K.flag := by simpa [eq_comm] using hq
    subst q
    have h := List.nodup_iff_count.mp hn K.flag
    have pos := List.count_pos_iff.mpr bad
    have takeBound := (List.take_sublist (K.out.length-1) K.carry).count_le K.flag
    simp only [MeasuredCanonicalModLayout.wires,List.count_append,List.count_cons,List.count_nil,
      beq_self_eq_true,if_true] at h pos
    omega
  have g : GatePhysical [Instr.CX K.flag K.high] := by
    simpa [GatePhysical,PhysicalInstr,ProperGate] using hf
  simp only [qprogTq,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨old.1.1.1.1.1,old.1.1.1.1.2⟩,old.1.1.1.2⟩,hm⟩,g⟩,old.1.2⟩,old.2⟩

theorem qprog_gateSlotsTq (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) :
    Challenge.gateSlots (qprogTq K p)≤67*n+41 := by
  have he : K.extended.length = n+1 := by simp [MeasuredCanonicalModLayout.extended, hw.out]
  have hs := Baselines.mappedAdd_gateSlots_le (mappedRead K.src false++[{wire:=none,flip:=false}])
    K.extended K.carry K.cin
  simp only [List.length_append, List.length_cons, List.length_nil, mappedRead_length, hw.src] at hs
  have hm := Baselines.mappedConst_gateSlots_le (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p
  have hb := Baselines.eraseLt_gateSlots_le K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
  rw [hw.out] at hb hm
  simp only [qprogTq,MeasuredCanonicalModLayout.sum,Challenge.gateSlots_append,Baselines.gateSlots_cons,
    Baselines.gateSlots_nil,Challenge.instructionSlots,Baselines.notRegister_gateSlots,hw.out]
  omega

end QCore

namespace QCore
end QCore
def measuredFoldQTq (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold) : Program :=
  copyRegister none f.src (L.foldDestination f)++qprogTq L.measuredCore SquareReduction.p++
    copyRegister none f.src (L.foldDestination f)


theorem qCopiedFold_correctTq (K : MeasuredCanonicalModLayout)
    (n c p : Nat) (hw : K.Widths n) (src : List Wire) (shift : Nat)
    (hn : (src++K.wires).Nodup) (hlen : shift+src.length≤n)
    (npos : 0<n) (hpc : p+c=2^n) (hcpos : 0<c)
    (O : Nat) (hO : O<p) (s : State) (records : List Bool)
    (hcanonical : regValue src s.basis*2^shift<p)
    (hzero : regValue K.src s.basis=0) (ho : regValue K.out s.basis=O)
    (hhigh : s.basis K.high=false) (hmod : s.basis K.flag=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) (hcin : s.basis K.cin=false) :
    (run (copySlice src K.src shift++qprogTq K p++copySlice src K.src shift) records s).phase=s.phase ∧
    regValue K.out (run (copySlice src K.src shift++qprogTq K p++copySlice src K.src shift) records s).basis=
      (regValue src s.basis*2^shift+(p-1-O))%p ∧
    ∀q,q∉K.out → (run (copySlice src K.src shift++qprogTq K p++copySlice src K.src shift) records s).basis q=
      s.basis q := by
  let dst := (K.src.drop shift).take src.length
  let cp := copySlice src K.src shift
  let kernel := qprogTq K p
  let S := regValue src s.basis*2^shift
  let u := run cp [] s
  let v := run kernel (records.take (measurementCount kernel)) u
  let out := run cp (records.drop (measurementCount kernel)) v
  have coreNd : K.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have nd : (src++K.src).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have bound : shift+src.length≤K.src.length := by simpa [hw.src] using hlen
  have len : dst.length=src.length := by simp [dst];omega
  have dstSub (q : Wire) (hq : q∈dst) : q∈K.src :=
    List.mem_of_mem_drop (List.mem_of_mem_take hq)
  have notWork (q : Wire) (hq : q∈src++K.out++K.carry++[K.high,K.cin,K.flag]) : q∉K.src := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have notDst (q : Wire) (hq : q∈src++K.out++K.carry++[K.high,K.cin,K.flag]) : q∉dst :=
    fun bad => notWork q hq (dstSub q bad)
  have notOut (q : Wire) (hq : q∈src++K.src++K.carry++[K.high,K.cin,K.flag]) : q∉K.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have copy := copySlice_zero_correct src K.src shift nd bound s [] hzero
  have first : u.phase=s.phase ∧ regValue K.src u.basis=S ∧
      ∀q,q∉dst → u.basis q=s.basis q := copy
  have cleanCarry : ∀q∈K.carry,u.basis q=false := by
    intro q hq
    exact (first.2.2 q (notDst q (by simp [hq]))).trans (hcarry q hq)
  have keep (q : Wire) (hq : q∈K.out++[K.high,K.cin,K.flag]) : u.basis q=s.basis q :=
    first.2.2 q (notDst q (by simp only [List.mem_append] at hq ⊢; tauto))
  have outU : regValue K.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans ho
  have body := QCore.qprog_correctTq K n c p hw coreNd npos hpc hcpos S O hcanonical hO u
    (records.take (measurementCount kernel)) first.2.1 outU
    ((keep K.high (by simp)).trans hhigh)
    ((keep K.flag (by simp)).trans hmod) cleanCarry ((keep K.cin (by simp)).trans hcin)
  have nd2 : (src++dst).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp nd q
    have ht := (List.take_sublist src.length (K.src.drop shift)).count_le q
    have hd := (List.drop_sublist shift K.src).count_le q
    simp only [List.count_append] at h ⊢
    dsimp only [dst]
    omega
  have dst0 : regValue dst s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hzero q (dstSub q hq))
  have copied := copyRegister_correct none src dst len.symm nd2 (by simp) s []
  have dstU : regValue dst u.basis=regValue src s.basis := by
    simpa [u,cp,copySlice,dst0,copyValue] using copied.2.2
  have dstV : regValue dst v.basis=regValue src s.basis :=
    (regValue_congr _ _ _ (fun q hq => body.2.2 q (notOut q (by simp [dstSub q hq])))).trans dstU
  have srcV : regValue src v.basis=regValue src s.basis := by
    apply regValue_congr
    intro q hq
    exact (body.2.2 q (notOut q (by simp [hq]))).trans (first.2.2 q (notDst q (by simp [hq])))
  have last := copyRegister_correct none src dst len.symm nd2 (by simp) v (records.drop (measurementCount kernel))
  have lastValue : regValue dst out.basis=0 := by
    simpa [out,cp,copySlice,dstV,srcV,copyValue] using last.2.2
  have finalValue : regValue K.out out.basis=(S+(p-1-O))%p :=
    (regValue_congr _ _ _ (fun q hq => last.2.1 q (notDst q (by simp [hq])))).trans body.2.1
  have final : out.phase=s.phase ∧ regValue K.out out.basis=(S+(p-1-O))%p ∧
      ∀q,q∉K.out → out.basis q=s.basis q := by
    refine ⟨last.1.trans (body.1.trans first.1),finalValue,?_⟩
    intro q hq
    by_cases inside : q∈dst
    · exact ((regValue_zero _ _).mp lastValue q inside).trans ((regValue_zero _ _).mp dst0 q inside).symm
    · exact (last.2.1 q inside).trans ((body.2.2 q hq).trans (first.2.2 q inside))
  have cm : measurementCount cp=0 := (copyNone_free src dst).2
  simpa [cp,kernel,u,v,out,S,run_append,cm] using final


theorem measuredFoldQ_eqTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold) :
    measuredFoldQTq L f=copySlice f.src L.measuredCore.src f.shift++qprogTq L.measuredCore SquareReduction.p++
      copySlice f.src L.measuredCore.src f.shift := by
  simp [measuredFoldQTq,foldDestination,copySlice,measuredCore,List.append_assoc]


theorem measuredFoldQ_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (f : MeasuredSquareFold)
    (hv : L.MeasuredFoldView base f) (hcan : f.canonical=true) (hc : L.PairClean base)
    (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (measuredFoldQTq L f)
      (SquareFrame L.core.out base ((measuredFoldPayload base f+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  have away (q : Wire) (hq : q∈f.src) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    have count := hv.count q
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,
      List.count_cons,List.count_nil] at h
    omega
  have inter : (f.src++L.measuredCore.wires).Nodup := by
    have h := L.measuredFold_interfaces hn f.src hv.count
    exact h.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
  intro s m hf
  have source : regValue f.src s.basis=regValue f.src base :=
    regValue_congr _ _ _ (fun q hq => hf.2 q (away q hq))
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  rw [measuredFoldQ_eqTq L hw f]
  have result := qCopiedFold_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p
    (L.measuredCore_widths hw) f.src f.shift inter hv.span (by decide)
    (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    (by norm_num [SquareReduction.c]) O hO s m (by rw [source];exact hv.canonical hcan)
    clean.work hf.1 clean.outHigh clean.modFlag (L.measuredFold_carry_clean s.basis clean) clean.cin
  refine ⟨result.1,?_,?_⟩
  · simpa [measuredFoldPayload,source] using result.2.1
  · intro q hq
    exact (result.2.2 q hq).trans (hf.2 q hq)


theorem measuredFoldQ_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold) :
    toffoliCount (measuredFoldQTq L f)=766 ∧ measurementCount (measuredFoldQTq L f)=767 := by
  have copy := copyNone_free f.src (L.foldDestination f)
  have core := QCore.qprog_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)
  simp only [measuredFoldQTq,toffoliCount_append,measurementCount_append,copy.1,copy.2,core.1,core.2]
  constructor <;> trivial


theorem measuredFoldQ_supportTq (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (f : MeasuredSquareFold) (hs : ∀q∈f.src,q∈L.core.product) :
    ECDSAAdd.wires (measuredFoldQTq L f)⊆(control::L.wires).toFinset := by
  have cp := copyRegister_wires_subset none f.src (L.foldDestination f)
  have embed : (Option.toList (none : Option Wire)++f.src++L.foldDestination f).toFinset⊆
      (control::L.wires).toFinset := by
    intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
    rcases hq with hq|hq
    · have h := hs q hq
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
    · have h := List.mem_of_mem_drop (List.mem_of_mem_take hq)
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
  have copy := cp.trans embed
  have core := (QCore.qprog_supportTq L.measuredCore SquareReduction.p).trans (measuredCore_in L control)
  simp only [measuredFoldQTq,wires_append,Finset.union_subset_iff]
  exact ⟨⟨copy,core⟩,copy⟩


theorem measuredFoldQ_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (f : MeasuredSquareFold)
    (hs : ∀ q, f.src.count q ≤ L.core.product.count q) : GatePhysical (measuredFoldQTq L f) := by
  have inter : (f.src++L.measuredCore.wires).Nodup := by
    have h := L.measuredFold_interfaces hn f.src hs
    exact h.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
  have coreNd : L.measuredCore.wires.Nodup := (List.nodup_append'.mp inter).2.1
  have cp : GatePhysical (copyRegister none f.src (L.foldDestination f)) := by
    apply copyRegister_physical
    · apply List.nodup_iff_count.mpr
      intro q; have h := List.nodup_iff_count.mp inter q
      have ht := (List.take_sublist f.src.length (L.core.work.drop f.shift)).count_le q
      have hd := (List.drop_sublist f.shift L.core.work).count_le q
      simp only [foldDestination,measuredCore,MeasuredCanonicalModLayout.wires,List.count_append] at h ht hd ⊢
      omega
    · simp
  simp only [measuredFoldQTq,gatePhysical_append]
  exact ⟨⟨cp,QCore.qprog_physicalTq _ _ coreNd⟩,cp⟩


theorem measuredFoldQ_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold) :
    Challenge.gateSlots (measuredFoldQTq L f) ≤ 36000 := by
  have hc := QCore.qprog_gateSlotsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw)
  have hd : (L.foldDestination f).length ≤ 256 := by
    simp only [CuccaroStreamedSquareWideLayout.foldDestination, List.length_take, List.length_drop, hw.core.work]; omega
  have hcopy := Nat.min_le_right f.src.length (L.foldDestination f).length
  simp only [measuredFoldQTq, Challenge.gateSlots_append, Baselines.copyRegister_gateSlots]
  omega


def accFoldQTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  fillIn L a++qprogTq L.measuredCore SquareReduction.p++fillOut L a


def accPriceQTq (a : AccItem) : Nat := 4*Acc.sbuildT 33 a.pre+2*Acc.sbuildT 163 a.terms+766+
  (if a.pre=[] then 0 else 4*127)


theorem accFoldQ_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFoldQTq L a)
      (SquareFrame L.core.out base ((Acc.accVal base 0 a.spec+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillIn_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFoldQTq,List.append_assoc,run_append,run_append]
  let mb := measurementCount (fillIn L a)
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let u := run (fillIn L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u.basis q=b0 q :=
    eu.2.2 q (accReg_away L hn q hq)
  have workU : regValue L.core.work u.basis=A := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using eu.2.1
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A<SquareReduction.p := lt_of_lt_of_le hA (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A O hAp hO u ((m.drop mb).take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) ((m.drop mb).take mk) u
  change v.phase=u.phase ∧ regValue L.core.out v.basis=(A+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u.basis q at ek
  let base2 : BasisState := fun q => if q∈L.core.out then v.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have frame2 : SquareFrame (accReg L) base2 A v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans eu.2.1
    · intro q hq
      by_cases ho : q∈L.core.out
      · simp [base2,ho]
      · rw [b2off q ho,ek.2.2 q ho]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := fillOut_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v ((m.drop mb).drop mk) frame2
  refine ⟨eo.1.trans (ek.1.trans eu.1),?_,?_⟩
  · have e : regValue L.core.out (run (fillOut L a) ((m.drop mb).drop mk) v).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq


theorem accFoldQ_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    toffoliCount (accFoldQTq L a)=accPriceQTq a ∧ measurementCount (accFoldQTq L a)=accPriceQTq a+1 := by
  have b := Acc.sbuild_counts (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms
    (fun f hf => fitsLen_of L hw f (ok f hf))
  have w := Acc.sbuild_counts (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre
    (fun f hf => fitsLen33_of L hw f (okP f hf))
  have k := QCore.qprog_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)
  have sp := split_counts L hw a
  simp only [accFoldQTq,fillIn,fillOut,tempIn,tempOut,accPriceQTq,toffoliCount_append,measurementCount_append,
    sp.1.1,sp.1.2,sp.2.1,sp.2.2]
  split <;> omega


theorem accFoldQ_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    ECDSAAdd.wires (accFoldQTq L a)⊆(control::L.wires).toFinset := by
  have full := accFold_support L hw hn control a cnt ok cntP okP
  simp only [accFold,wires_append,Finset.union_subset_iff] at full
  have core := (QCore.qprog_supportTq L.measuredCore SquareReduction.p).trans (measuredCore_in L control)
  simp only [accFoldQTq,wires_append,Finset.union_subset_iff]
  exact ⟨⟨full.1.1,core⟩,full.2⟩


theorem accFoldQ_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQTq L a) := by
  have full := accFold_physical L hw hn a cnt ok cntP okP
  simp only [accFold,gatePhysical_append] at full
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  simp only [accFoldQTq,gatePhysical_append]
  exact ⟨⟨full.1.1,QCore.qprog_physicalTq _ _ coreNd⟩,full.2⟩


theorem accFoldQ_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    Challenge.gateSlots (accFoldQTq L a)≤2*(a.terms.length*(14*163))+4*(a.pre.length*(14*33))+(67*256+41)+7000 := by
  have full := accFold_gateSlots L hw a ok okP
  have k := Baselines.canonicalMod_gateSlots_le L.measuredCore 256 SquareReduction.c SquareReduction.p
    (L.measuredCore_widths hw)
  have q := QCore.qprog_gateSlotsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw)
  have b := Acc.sbuild_gateSlots (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms
    (fun f hf => fitsLen_of L hw f (ok f hf))
  have w := Acc.sbuild_gateSlots (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre
    (fun f hf => fitsLen33_of L hw f (okP f hf))
  have sp := split_gateSlots L hw a
  simp only [accFoldQTq,fillIn,fillOut,tempIn,tempOut,Challenge.gateSlots_append]
  omega


def mixProgQTq (L : CuccaroStreamedSquareWideLayout) : MixItem → Program
  | .inl f => if f.canonical then measuredFoldQTq L f else L.reflectOutput++L.measuredFold f
  | .inr a => accFoldQTq L a


def mixFoldsQTq (L : CuccaroStreamedSquareWideLayout) : Bool → List MixItem → Program
  | _,[] => []
  | o,i::is => (if o=mixNeg i then mixProg L i else mixProgQTq L i)++mixFoldsQTq L (mixNeg i) is


theorem mixProgQ_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (i : MixItem) (hv : MixView L base i) (hc : L.PairClean base)
    (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (mixProgQTq L i)
      (SquareFrame L.core.out base ((mixPayload base i+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  cases i with
  | inl f =>
    by_cases hcan : f.canonical=true
    · simp only [mixProgQTq,hcan,if_true]
      exact measuredFoldQ_frameTq L hw hn base f hv hcan hc O hO
    · simp only [mixProgQTq,hcan,Bool.false_eq_true,if_false]
      have r := L.measuredReflection_frame hw hn base hc O hO
      have f' := L.measuredFold_frame hw hn base f hv hc (SquareReduction.p-1-O) (by omega)
      exact r.seq f'
  | inr a => exact accFoldQ_frameTq L hw hn base a hv hc O hO


theorem mixFoldsQ_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (hc : L.PairClean base)
    (o : Bool) (O : Nat) (hO : O<SquareReduction.p) (items : List MixItem)
    (views : ∀i∈items,MixView L base i) :
    Triple (SquareFrame L.core.out base O) (mixFoldsQTq L o items)
      (SquareFrame L.core.out base (mixValue base o O items)) := by
  induction items generalizing o O with
  | nil => intro s m hf;exact ⟨rfl,hf⟩
  | cons i is ih =>
    let R := if o=mixNeg i then O else SquareReduction.p-1-O
    have step : Triple (SquareFrame L.core.out base O)
        (if o=mixNeg i then mixProg L i else mixProgQTq L i)
        (SquareFrame L.core.out base ((mixPayload base i+R)%SquareReduction.p)) := by
      by_cases same : o=mixNeg i
      · simp only [same,if_true,R]
        exact mixProg_frame L hw hn base i (views i (by simp)) hc O hO
      · simp only [same,if_false,R]
        exact mixProgQ_frameTq L hw hn base i (views i (by simp)) hc O hO
    have ob : (mixPayload base i+R)%SquareReduction.p<SquareReduction.p :=
      Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    have tail := ih (mixNeg i) _ ob (by intro j hj;exact views j (by simp [hj]))
    exact step.seq tail


def mixFoldsQTTq : Bool → List MixItem → Nat
  | _,[] => 0
  | o,i::is => (if o=mixNeg i then
        (match i with
          | .inl f => 1023+(if f.canonical then 0 else 1022)
          | .inr a => accPrice a)
      else
        (match i with
          | .inl f => if f.canonical then 766 else 255+1023+1022
          | .inr a => accPriceQTq a))+mixFoldsQTTq (mixNeg i) is


def mixFoldsQMTq : Bool → List MixItem → Nat
  | _,[] => 0
  | o,i::is => (if o=mixNeg i then
        (match i with
          | .inl f => 1023+(if f.canonical then 0 else 1020)
          | .inr a => accPrice a)
      else
        (match i with
          | .inl f => if f.canonical then 767 else 255+1023+1020
          | .inr a => accPriceQTq a+1))+mixFoldsQMTq (mixNeg i) is


theorem mixFoldsQ_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    toffoliCount (mixFoldsQTq L o items)=mixFoldsQTTq o items ∧
    measurementCount (mixFoldsQTq L o items)=mixFoldsQMTq o items := by
  induction items generalizing o with
  | nil => simp [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,toffoliCount,measurementCount]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have reflect := (L.measured_small_operation_counts hw).2.2
    have hi := hst i (by simp)
    cases i with
    | inl f =>
      have op := L.measuredFold_counts hw f
      have opq := measuredFoldQ_countsTq L hw f
      by_cases same : o=mixNeg (.inl f)
      · simp only [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,same,if_true,mixProg,toffoliCount_append,
          measurementCount_append,op.1,op.2,t.1,t.2]
        exact ⟨trivial,trivial⟩
      · cases hcan : f.canonical
        · simp only [hcan,Bool.false_eq_true,if_false] at op
          simp only [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,same,if_false,mixProgQTq,hcan,Bool.false_eq_true,
            toffoliCount_append,measurementCount_append,op.1,op.2,reflect.1,reflect.2,t.1,t.2]
          first | exact ⟨trivial,trivial⟩ | (constructor <;> omega)
        · simp only [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,same,if_false,mixProgQTq,hcan,
            if_true,toffoliCount_append,measurementCount_append,opq.1,opq.2,t.1,t.2]
          first | exact ⟨trivial,trivial⟩ | (constructor <;> omega)
    | inr a =>
      have op := accFold_counts L hw a hi.2.1 hi.2.2.2
      have opq := accFoldQ_countsTq L hw a hi.2.1 hi.2.2.2
      by_cases same : o=mixNeg (.inr a)
      · simp only [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,same,if_true,mixProg,toffoliCount_append,
          measurementCount_append,op.1,op.2,t.1,t.2]
        exact ⟨trivial,trivial⟩
      · simp only [mixFoldsQTq,mixFoldsQTTq,mixFoldsQMTq,same,if_false,mixProgQTq,toffoliCount_append,
          measurementCount_append,opq.1,opq.2,t.1,t.2]
        first | exact ⟨trivial,trivial⟩ | (constructor <;> omega)


theorem mixFoldsQ_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    ECDSAAdd.wires (mixFoldsQTq L o items)⊆(control::L.wires).toFinset := by
  induction items generalizing o with
  | nil => simp [mixFoldsQTq,ECDSAAdd.wires]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have reflect : ECDSAAdd.wires L.reflectOutput⊆(control::L.wires).toFinset :=
      (L.measured_small_support control).2.2.1
    have hi := hst i (by simp)
    have mem (f : MeasuredSquareFold) (h : ∀q,f.src.count q≤L.core.product.count q) :
        ∀q∈f.src,q∈L.core.product := by
      intro q hq
      have pos := List.count_pos_iff.mpr hq
      have b := h q
      exact List.count_pos_iff.mp (by omega)
    have hprog : ECDSAAdd.wires (mixProg L i)⊆(control::L.wires).toFinset := by
      cases i with
      | inl f => exact L.measuredFold_support control f (mem f hi)
      | inr a => exact accFold_support L hw hn control a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    have hprogQ : ECDSAAdd.wires (mixProgQTq L i)⊆(control::L.wires).toFinset := by
      cases i with
      | inl f =>
        by_cases hcan : f.canonical=true
        · simp only [mixProgQTq,hcan,if_true]
          exact measuredFoldQ_supportTq L control f (mem f hi)
        · simp only [mixProgQTq,hcan,Bool.false_eq_true,if_false,wires_append,Finset.union_subset_iff]
          exact ⟨reflect,L.measuredFold_support control f (mem f hi)⟩
      | inr a => exact accFoldQ_supportTq L hw hn control a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    by_cases same : o=mixNeg i <;>
      simp only [mixFoldsQTq,same,if_false,if_true,wires_append,Finset.union_subset_iff] <;> tauto


theorem mixFoldsQ_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    GatePhysical (mixFoldsQTq L o items) := by
  induction items generalizing o with
  | nil => simp [mixFoldsQTq,GatePhysical]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have hi := hst i (by simp)
    have hprog : GatePhysical (mixProg L i) := by
      cases i with
      | inl f => exact L.measuredFold_physical hw hn f hi
      | inr a => exact accFold_physical L hw hn a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    have hprogQ : GatePhysical (mixProgQTq L i) := by
      cases i with
      | inl f =>
        by_cases hcan : f.canonical=true
        · simp only [mixProgQTq,hcan,if_true]
          exact measuredFoldQ_physicalTq L hw hn f hi
        · simp only [mixProgQTq,hcan,Bool.false_eq_true,if_false,gatePhysical_append]
          exact ⟨L.reflectOutput_physical hn,L.measuredFold_physical hw hn f hi⟩
      | inr a => exact accFoldQ_physicalTq L hw hn a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    simp only [mixFoldsQTq,gatePhysical_append]
    refine ⟨?_,t⟩
    split
    · exact hprog
    · exact hprogQ


theorem mixFoldsQ_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) (B : Nat)
    (hB : ∀i∈items,∀a,i=.inr a → a.terms.length≤B ∧ a.pre.length≤4) :
    Challenge.gateSlots (mixFoldsQTq L o items)≤ items.length*(41000+2*(B*(14*163))+(67*256+41)) := by
  induction items generalizing o with
  | nil => simp [mixFoldsQTq,Challenge.gateSlots]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj])) (fun j hj a e => hB j (by simp [hj]) a e)
    have hr := (Baselines.streamedFrames_gateSlots_le L hw).2.2
    have hi := hst i (by simp)
    have hprog : Challenge.gateSlots (mixProg L i)≤36000+2*(B*(14*163))+(66*256+37) := by
      cases i with
      | inl f => have := Baselines.measuredFold_gateSlots_le L hw f; simp only [mixProg]; omega
      | inr a =>
        have h1 := accFold_gateSlots L hw a hi.2.1 hi.2.2.2
        have h2 := hB (.inr a) (by simp) a rfl
        have h3 : a.terms.length*(14*163)≤B*(14*163) := Nat.mul_le_mul_right _ h2.1
        have h4 : a.pre.length*(14*33)≤4*(14*33) := Nat.mul_le_mul_right _ h2.2
        simp only [mixProg]; omega
    have hprogQ : Challenge.gateSlots (mixProgQTq L i)≤41000+2*(B*(14*163))+(67*256+41) := by
      cases i with
      | inl f =>
        have a1 := Baselines.measuredFold_gateSlots_le L hw f
        have a2 := measuredFoldQ_gateSlotsTq L hw f
        by_cases hcan : f.canonical=true
        · simp only [mixProgQTq,hcan,if_true]; omega
        · simp only [mixProgQTq,hcan,Bool.false_eq_true,if_false,Challenge.gateSlots_append]; omega
      | inr a =>
        have h1 := accFoldQ_gateSlotsTq L hw a hi.2.1 hi.2.2.2
        have h2 := hB (.inr a) (by simp) a rfl
        have h3 : a.terms.length*(14*163)≤B*(14*163) := Nat.mul_le_mul_right _ h2.1
        have h4 : a.pre.length*(14*33)≤4*(14*33) := Nat.mul_le_mul_right _ h2.2
        simp only [mixProgQTq]; omega
    simp only [mixFoldsQTq,Challenge.gateSlots_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    split
    · omega
    · omega


end ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout RecordedQuantum
/-- `qprog4` with the output-only `+flag·p` correction of `qprogTq`. -/
def qprog4Tq (K : MeasuredCanonicalModLayout) (p : Nat) : Program :=
  notRegister K.out++Skip4.addSkip 4 (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)])
    K.extended K.carry K.cin++[.CX K.high K.flag,.X K.flag]++
    mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p++[.CX K.flag K.high]++
    [.X K.high,.X K.flag]++
    Skip4.eraseSkip 4 K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag

namespace Q4

theorem q4_countsTq (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (n5 : 5≤n) :
    toffoliCount (qprog4Tq K p)+8=toffoliCount (qprogTq K p) ∧
    measurementCount (qprog4Tq K p)=measurementCount (qprogTq K p) := by
  have a := Skip4.addSkip_toff 4 (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)])
    K.extended K.carry K.cin (by simp [mappedRead,hw.src]; omega)
    (by simp [MeasuredCanonicalModLayout.extended,hw.out]; omega) (by rw [hw.carry]; omega)
  have e := Skip4.eraseSkip_toff 4 K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
    (by rw [hw.out]; omega) (by rw [hw.src]; omega) (by simp [hw.carry,hw.out]; omega)
  have am := Skip4.addSkip_mc 4 (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)])
    K.extended K.carry K.cin
  have em := Skip4.eraseSkip_mc 4 K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
  simp only [qprog4Tq,qprogTq,MeasuredCanonicalModLayout.sum,toffoliCount_append,measurementCount_append] at a e am em ⊢
  constructor <;> omega

theorem q4_sublistTq (K : MeasuredCanonicalModLayout) (p : Nat) : List.Sublist (qprog4Tq K p) (qprogTq K p) := by
  unfold qprog4Tq qprogTq MeasuredCanonicalModLayout.sum
  exact ((((((List.Sublist.refl _).append (Skip4.addSkip_sublist 4 _ _ _ _)).append (List.Sublist.refl _)).append
    (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)).append
    (Skip4.eraseSkip_sublist 4 _ _ _ _ _)

theorem q4_run_eqTq (K : MeasuredCanonicalModLayout) (n c p : Nat) (hw : K.Widths n)
    (hn : K.wires.Nodup) (n5 : 5≤n) (hpc : p+c=2^n) (hcp : 0<c)
    (A X : Nat) (hA : A<p) (hX : X<p) (s : State) (m : List Bool)
    (ha : regValue K.src s.basis=A) (hx : regValue K.out s.basis=X)
    (hh : s.basis K.high=false) (hf : s.basis K.flag=false)
    (hc : ∀q∈K.carry,s.basis q=false) (hi : s.basis K.cin=false)
    (hlow : ∀q∈K.src.take 4,s.basis q=false) :
    run (qprog4Tq K p) m s=run (qprogTq K p) m s := by
  have npos : 0<n := by omega
  let base := s.basis
  have initial : K.Frame base X false false s.basis := ⟨hx,hh,hf,fun _ _ => rfl⟩
  have bpos : 0<2^n := by positivity
  have sumBound : A+(2^n-1-X)<2^(n+1) := by rw [Nat.pow_succ]; omega
  generalize hr : decide (2^n≤A+(2^n-1-X))=r
  have s1 := QCore.not_frame K n hw hn base X
  have s2 := K.sum_frame n hw hn base A (2^n-1-X) ha sumBound hc hi
  rw [hr] at s2
  have s3 : Triple (K.Frame base ((A+(2^n-1-X))%2^n) r false) [.CX K.high K.flag]
      (K.Frame base ((A+(2^n-1-X))%2^n) r r) := by
    simpa using K.cx_flag_frame hn base ((A+(2^n-1-X))%2^n) r false
  have s4 := QCore.x_flag_frame K hn base ((A+(2^n-1-X))%2^n) r r
  have s5 := QCore.correctionT_frame K n p hw hn (by omega) npos base ((A+(2^n-1-X))%2^n) r (!r) hc hi
  have s6 := QCore.x_high_frame K hn base (((if !r then p else 0)+(A+(2^n-1-X))%2^n)%2^n) (r ^^ !r) (!r)
  have s7 := QCore.x_flag_frame K hn base (((if !r then p else 0)+(A+(2^n-1-X))%2^n)%2^n) (!(r ^^ !r)) (!r)
  let N := notRegister K.out
  let S := MeasuredCanonicalModLayout.sum K
  let S4 := Skip4.addSkip 4 (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)]) K.extended K.carry K.cin
  let Y : Program := [.CX K.high K.flag,.X K.flag]
  let C := mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p++[.CX K.flag K.high]
  let Z : Program := [.X K.high,.X K.flag]
  let E := eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
  let E4 := Skip4.eraseSkip 4 K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
  have e1 : qprog4Tq K p=N++S4++Y++C++Z++E4 := by simp only [qprog4Tq,N,S4,Y,C,Z,E4,List.append_assoc]
  have e2 : qprogTq K p=N++S++Y++C++Z++E := by simp only [qprogTq,N,S,Y,C,Z,E,List.append_assoc]
  have zeroOf (t : BasisState) (O : Nat) (H F : Bool) (ht : K.Frame base O H F t) :
      (∀q∈K.src.take 4,t q=false) ∧ t K.cin=false ∧ (∀q∈K.carry.take 4,t q=false) :=
    ⟨fun q hq => (frame_zero K hn base t O H F ht q (by simp [List.mem_of_mem_take hq])).trans (hlow q hq),
     (frame_zero K hn base t O H F ht K.cin (by simp)).trans hi,
     fun q hq => (frame_zero K hn base t O H F ht q (by simp [List.mem_of_mem_take hq])).trans
       (hc q (List.mem_of_mem_take hq))⟩
  have mS : measurementCount S4=measurementCount S := Skip4.addSkip_mc 4 _ _ _ _
  have stepNS (m' : List Bool) : run (N++S4) m' s=run (N++S) m' s := by
    rw [run_append,run_append]
    have u := (s1 s (m'.take (measurementCount N)) initial).2
    have z := zeroOf _ _ _ _ u
    exact Skip4.addSkip_run 4 _ _ _ _ _ _ (skipOK K n hw hn n5 _ z.1 z.2.1 z.2.2)
  have stepP (m' : List Bool) : run (N++S4++Y++C++Z) m' s=run (N++S++Y++C++Z) m' s := by
    have mNS : measurementCount (N++S4)=measurementCount (N++S) := by simp only [measurementCount_append,mS]
    have h1 := run_congr_left (N++S4) (N++S) Y s mNS stepNS
    have h2 := run_congr_left (N++S4++Y) (N++S++Y) C s (by simp only [measurementCount_append,mS]) h1
    exact run_congr_left (N++S4++Y++C) (N++S++Y++C) Z s (by simp only [measurementCount_append,mS]) h2 m'
  have pre := (((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7
  rw [e1,e2,run_append (N++S4++Y++C++Z) E4,run_append (N++S++Y++C++Z) E]
  have mP : measurementCount (N++S4++Y++C++Z)=measurementCount (N++S++Y++C++Z) := by
    simp only [measurementCount_append,mS]
  rw [mP,stepP]
  have hP : N++S++Y++C++Z=notRegister K.out++K.sum++[.CX K.high K.flag]++[.X K.flag]++
      (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p++[.CX K.flag K.high])++
      [.X K.high]++[.X K.flag] := by
    simp [N,S,Y,C,Z,List.append_assoc]
  have w := (pre s (m.take (measurementCount (N++S++Y++C++Z))) initial).2
  rw [← hP] at w
  have z := zeroOf _ _ _ _ w
  exact Skip4.eraseSkip_run 4 _ _ _ _ _ _ _ (eok K n hw hn n5 _ z.1 z.2.1 z.2.2)

end Q4

namespace Q4
end Q4
def accFoldQ4Tq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  fillIn L a++qprog4Tq L.measuredCore SquareReduction.p++fillOut L a


namespace Q4
end Q4
end ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Q4
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
theorem accFoldQ4_sublistTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) :
    List.Sublist (accFoldQ4Tq L a) (accFoldQTq L a) :=
  ((List.Sublist.refl _).append (q4_sublistTq _ _)).append (List.Sublist.refl _)


theorem accFoldQ4_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem) :
    toffoliCount (accFoldQ4Tq L a)+8=toffoliCount (accFoldQTq L a) ∧
    measurementCount (accFoldQ4Tq L a)=measurementCount (accFoldQTq L a) := by
  have c := q4_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by norm_num)
  simp only [accFoldQ4Tq,accFoldQTq,toffoliCount_append,measurementCount_append]
  constructor <;> omega


theorem accFoldQ4_wiresTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) :
    ECDSAAdd.wires (accFoldQ4Tq L a)⊆ECDSAAdd.wires (accFoldQTq L a) :=
  Skip4.wires_mono_of_mem _ _ (fun _ hi => (accFoldQ4_sublistTq L a).subset hi)


theorem accFoldQ4_physicalTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem)
    (h : GatePhysical (accFoldQTq L a)) : GatePhysical (accFoldQ4Tq L a) :=
  fun i hi => h i ((accFoldQ4_sublistTq L a).subset hi)


theorem accFoldQ4_slotsTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) :
    Challenge.gateSlots (accFoldQ4Tq L a)≤Challenge.gateSlots (accFoldQTq L a) :=
  Skip4.slots_mono_of_sublist _ _ (accFoldQ4_sublistTq L a)


end ECDSAAdd.Entrant.Q4

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout RecordedQuantum

def accFoldQKTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  OwnDiagAll12Square.fillInK L a++qprogTq L.measuredCore SquareReduction.p++CodexCKAccTail.fillOutTail L a

theorem accFoldQ_frameKTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFoldQKTq L a)
      (SquareFrame L.core.out base ((Acc.accVal base 0 a.spec+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := OwnDiagAll12Square.fillInK_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFoldQKTq,List.append_assoc,run_append,run_append]
  let mb := measurementCount (OwnDiagAll12Square.fillInK L a)
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let u := run (OwnDiagAll12Square.fillInK L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u.basis q=b0 q :=
    eu.2.2 q (accReg_away L hn q hq)
  have workU : regValue L.core.work u.basis=A := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using eu.2.1
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A<SquareReduction.p := lt_of_lt_of_le hA (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A O hAp hO u ((m.drop mb).take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) ((m.drop mb).take mk) u
  change v.phase=u.phase ∧ regValue L.core.out v.basis=(A+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u.basis q at ek
  let base2 : BasisState := fun q => if q∈L.core.out then v.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have frame2 : SquareFrame (accReg L) base2 A v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans eu.2.1
    · intro q hq
      by_cases ho : q∈L.core.out
      · simp [base2,ho]
      · rw [b2off q ho,ek.2.2 q ho]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := CodexCKAccTail.fillOutTail_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v ((m.drop mb).drop mk) frame2
  refine ⟨eo.1.trans (ek.1.trans eu.1),?_,?_⟩
  · have e : regValue L.core.out (run (CodexCKAccTail.fillOutTail L a) ((m.drop mb).drop mk) v).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq



def accFoldQ4KTq (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  OwnDiagAll12Square.fillInK L a++qprog4Tq L.measuredCore SquareReduction.p++CodexCKAccTail.fillOutTail L a

namespace Q4
theorem accFoldQ4_runKTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p)
    (h16 : Acc.accVal base 0 a.spec%16=0)
    (s : State) (m : List Bool) (hf : SquareFrame L.core.out base O s.basis) :
    run (accFoldQ4KTq L a) m s=run (accFoldQKTq L a) m s := by
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := OwnDiagAll12Square.fillInK_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  let mb := measurementCount (OwnDiagAll12Square.fillInK L a)
  let u := run (OwnDiagAll12Square.fillInK L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u.basis q=b0 q :=
    eu.2.2 q (accReg_away L hn q hq)
  have workU : regValue L.core.work u.basis=A := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using eu.2.1
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A<SquareReduction.p := lt_of_lt_of_le hA (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have workLen : L.core.work.length=256 := (L.measuredCore_widths hw).src
  have lowU : ∀q∈L.measuredCore.src.take 4,u.basis q=false := by
    have t := CuccaroStreamedSquareWideLayout.regValue_take_mod L.core.work 4 (by omega) u.basis
    rw [workU] at t
    have z : regValue (L.core.work.take 4) u.basis=0 := by rw [t]; simpa [A] using h16
    exact (regValue_zero _ _).mp z
  rw [accFoldQ4KTq,accFoldQKTq,List.append_assoc,List.append_assoc,run_append (OwnDiagAll12Square.fillInK L a),run_append (OwnDiagAll12Square.fillInK L a)]
  have cnt := q4_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by norm_num)
  exact run_congr_left _ _ _ u cnt.2 (fun m' => q4_run_eqTq L.measuredCore 256 SquareReduction.c SquareReduction.p
    (L.measuredCore_widths hw) coreNd (by norm_num) hp (by norm_num [SquareReduction.c]) A O hAp hO u m'
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin) lowU) _



theorem accFoldQ4KTq_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) :
    toffoliCount (accFoldQ4KTq L a)≤toffoliCount (accFoldQ4Tq L a) ∧
    measurementCount (accFoldQ4KTq L a)=measurementCount (accFoldQ4Tq L a) ∧
    ECDSAAdd.wires (accFoldQ4KTq L a)⊆ECDSAAdd.wires (accFoldQ4Tq L a) ∧
    Challenge.gateSlots (accFoldQ4KTq L a)≤Challenge.gateSlots (accFoldQ4Tq L a) := by
  have r := CodexCKAccTail.fillTail_rel L hw a ok
  simp only [accFoldQ4KTq,accFoldQ4Tq,toffoliCount_append,measurementCount_append,wires_append,
    Challenge.gateSlots_append]
  refine ⟨by omega,by omega,?_,by omega⟩
  exact Finset.union_subset_union (Finset.union_subset_union r.1.2.2.1 (Finset.Subset.refl _)) r.2.2.2.1

theorem accFoldQ4KTq_counts_early (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (src : List Wire) (hsrc : src.length≤130) (he : a.terms=earlyHTerms src)
    (ok : ∀f∈a.terms,TermOK f) :
    toffoliCount (accFoldQ4KTq L a)+31=toffoliCount (accFoldQ4Tq L a) := by
  have e : a.terms=Acc.earlyTerm src false 4::Acc.earlyTerm src false 10::Acc.earlyTerm src true 6::
      Acc.earlyTerm src false 32::[] := by rw [he]; rfl
  have c := CodexCKAccTail.tail_counts_early (accReg L) (accZ L) (accBank L) L.core.cin src
    (acc_lengths L hw).1 hsrc (Acc.earlyTerm src false 32) []
    (by simp [CKAcc.IsT32,Acc.earlyTerm]) (fun f hf => fitsLen_of L hw f (ok f (by rw [e]; exact hf)))
  rw [← e] at c
  simp only [accFoldQ4KTq,accFoldQ4Tq,OwnDiagAll12Square.fillInK,fillIn,CodexCKAccTail.fillOutTail,fillOut,
    toffoliCount_append]
  omega

theorem accFoldQ4KTq_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQ4KTq L a) := by
  have old := accFoldQ4_physicalTq L a (accFoldQ_physicalTq L hw hn a cnt ok cntP okP)
  have k := CodexCKAccTail.fillTail_physical L hw hn a cnt ok cntP okP
  simp only [accFoldQ4Tq,gatePhysical_append] at old
  simp only [accFoldQ4KTq,gatePhysical_append]
  exact ⟨⟨k.1,old.1.2⟩,k.2⟩

end Q4
end ECDSAAdd.Entrant

namespace ECDSAAdd.Entrant.OwnDiagAll12Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
def accFoldQFTq (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) : Program :=
  fillIn L a++(maskedConstant g (accReg L) cFlipK++(qprogTq L.measuredCore SquareReduction.p++
    (maskedConstant g (accReg L) cFlipK++fillOut L a)))


theorem accFoldQF_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (g : Wire) (hg : g∉L.wires) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFoldQFTq L g a)
      (SquareFrame L.core.out base (((if base g then cFlipK-Acc.accVal base 0 a.spec else Acc.accVal base 0 a.spec)+
        (SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have gAcc : g∉accReg L := fun h => hg (accReg_in L g h)
  have gOut : g∉L.core.out := fun h => hg (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have hAK : A≤cFlipK := by unfold cFlipK; omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^163 := by
    simp only [A']; split
    · unfold cFlipK; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillIn_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFoldQFTq,run_append,run_append,run_append,run_append]
  let mb := measurementCount (fillIn L a)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (fillIn L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u1.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using accU1
  have outU : regValue L.core.out u1.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A'<SquareReduction.p := lt_of_lt_of_le hA' (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u1.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) cFlipK) (m3.take mc) v
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc)
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis else regValue (accReg L) v.basis) at fl2
  rw [gV,accV] at fl2
  have back : (if base g then cFlipK-A' else A')=A := by
    simp only [A']
    cases base g
    · simp
    · simp only [if_true]; omega
  rw [back] at fl2
  let base2 : BasisState := fun q => if q∈L.core.out then v1.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have frame2 : SquareFrame (accReg L) base2 A v1.basis := by
    refine ⟨fl2.2.2,?_⟩
    intro q hq
    by_cases ho : q∈L.core.out
    · simp [base2,ho]
    · rw [b2off q ho,fl2.2.1 q hq,ek.2.2 q ho,fl.2.1 q hq]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := fillOut_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v1 (m3.drop mc) frame2
  refine ⟨eo.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have e : regValue L.core.out (run (fillOut L a) (m3.drop mc) v1).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq,fl2.2.1 q na]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq


theorem accFoldQF_countsTq (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) :
    toffoliCount (accFoldQFTq L g a)=toffoliCount (accFoldQTq L a) ∧
    measurementCount (accFoldQFTq L g a)=measurementCount (accFoldQTq L a) := by
  have k := maskedConstant_counts g (accReg L) cFlipK
  simp only [accFoldQFTq,accFoldQTq,toffoliCount_append,measurementCount_append,k.1,k.2]
  constructor <;> omega


theorem accFoldQF_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    ECDSAAdd.wires (accFoldQFTq L g a)⊆(g::L.wires).toFinset := by
  have full := accFoldQ_supportTq L hw hn g a cnt ok cntP okP
  simp only [accFoldQTq,wires_append,Finset.union_subset_iff] at full
  have mc : ECDSAAdd.wires (maskedConstant g (accReg L) cFlipK)⊆(g::L.wires).toFinset := by
    refine (maskedConstant_wires_subset _ _ _).trans ?_
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq ⊢
    rcases hq with h|h
    · exact Or.inl h
    · exact Or.inr (accReg_in L q h)
  simp only [accFoldQFTq,wires_append,Finset.union_subset_iff]
  exact ⟨full.1.1,mc,full.1.2,mc,full.2⟩


theorem accFoldQF_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQFTq L g a) := by
  have full := accFoldQ_physicalTq L hw hn a cnt ok cntP okP
  simp only [accFoldQTq,gatePhysical_append] at full
  have mc := maskedConstant_physical g (accReg L) cFlipK (fun h => hg (accReg_in L g h))
  simp only [accFoldQFTq,gatePhysical_append]
  exact ⟨full.1.1,mc,full.1.2,mc,full.2⟩


theorem accFoldQF_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    Challenge.gateSlots (accFoldQFTq L g a)≤
      2*(a.terms.length*(14*163))+4*(a.pre.length*(14*33))+(67*256+41)+7000+2*163 := by
  have full := accFoldQ_gateSlotsTq L hw a ok okP
  have mc := Baselines.maskedConstant_gateSlots_le g (accReg L) cFlipK
  rw [(acc_lengths L hw).1] at mc
  simp only [accFoldQTq,Challenge.gateSlots_append] at full
  simp only [accFoldQFTq,Challenge.gateSlots_append]
  omega


open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
def accFoldQFKTq (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) : Program :=
  fillInK L a++(maskedConstant g (accReg L) cFlipK++(qprogTq L.measuredCore SquareReduction.p++
    (maskedConstant g (accReg L) cFlipK++CodexCKAccTail.fillOutTail L a)))


theorem accFoldQFK_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (g : Wire) (hg : g∉L.wires) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFoldQFKTq L g a)
      (SquareFrame L.core.out base (((if base g then cFlipK-Acc.accVal base 0 a.spec else Acc.accVal base 0 a.spec)+
        (SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have gAcc : g∉accReg L := fun h => hg (accReg_in L g h)
  have gOut : g∉L.core.out := fun h => hg (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have hAK : A≤cFlipK := by unfold cFlipK; omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^163 := by
    simp only [A']; split
    · unfold cFlipK; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillInK_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFoldQFKTq,run_append,run_append,run_append,run_append]
  let mb := measurementCount (fillInK L a)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (fillInK L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u1.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using accU1
  have outU : regValue L.core.out u1.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A'<SquareReduction.p := lt_of_lt_of_le hA' (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u1.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) cFlipK) (m3.take mc) v
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc)
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis else regValue (accReg L) v.basis) at fl2
  rw [gV,accV] at fl2
  have back : (if base g then cFlipK-A' else A')=A := by
    simp only [A']
    cases base g
    · simp
    · simp only [if_true]; omega
  rw [back] at fl2
  let base2 : BasisState := fun q => if q∈L.core.out then v1.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have frame2 : SquareFrame (accReg L) base2 A v1.basis := by
    refine ⟨fl2.2.2,?_⟩
    intro q hq
    by_cases ho : q∈L.core.out
    · simp [base2,ho]
    · rw [b2off q ho,fl2.2.1 q hq,ek.2.2 q ho,fl.2.1 q hq]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := CodexCKAccTail.fillOutTail_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v1 (m3.drop mc) frame2
  refine ⟨eo.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have e : regValue L.core.out (run (CodexCKAccTail.fillOutTail L a) (m3.drop mc) v1).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq,fl2.2.1 q na]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq



theorem accFoldQFK_relTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) :
    toffoliCount (accFoldQFKTq L g a)≤toffoliCount (accFoldQFTq L g a) ∧
    measurementCount (accFoldQFKTq L g a)=measurementCount (accFoldQFTq L g a) ∧
    ECDSAAdd.wires (accFoldQFKTq L g a)⊆ECDSAAdd.wires (accFoldQFTq L g a) ∧
    Challenge.gateSlots (accFoldQFKTq L g a)≤Challenge.gateSlots (accFoldQFTq L g a) := by
  have r := CodexCKAccTail.fillTail_rel L hw a ok
  simp only [accFoldQFKTq,accFoldQFTq,toffoliCount_append,measurementCount_append,wires_append,
    Challenge.gateSlots_append]
  refine ⟨by omega,by omega,?_,by omega⟩
  exact Finset.union_subset_union r.1.2.2.1 (Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union (Finset.Subset.refl _) r.2.2.2.1)))


theorem accFoldQFK_countsCTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire)
    (ok : ∀f∈(accCItem L).terms,TermOK f) :
    toffoliCount (accFoldQFKTq L g (accCItem L))+31=toffoliCount (accFoldQFTq L g (accCItem L)) ∧
    measurementCount (accFoldQFKTq L g (accCItem L))=measurementCount (accFoldQFTq L g (accCItem L)) := by
  have r := CodexCKAccTail.fillTail_rel L hw (accCItem L) ok
  have hsrc : (L.core.product.drop 128).length≤130 := by simp [hw.core.product]
  have e : (accCItem L).terms=Acc.earlyTerm (L.core.product.drop 128) false 4::
      Acc.earlyTerm (L.core.product.drop 128) false 10::Acc.earlyTerm (L.core.product.drop 128) true 6::
      Acc.earlyTerm (L.core.product.drop 128) false 32::[posTop L] := by
    simp [accCItem,earlyHTerms]
  have c := CodexCKAccTail.tail_counts_early (accReg L) (accZ L) (accBank L) L.core.cin (L.core.product.drop 128)
    (acc_lengths L hw).1 hsrc (Acc.earlyTerm (L.core.product.drop 128) false 32) [posTop L]
    (by simp [CKAcc.IsT32,Acc.earlyTerm]) (fun f hf => fitsLen_of L hw f (ok f (by rw [e]; exact hf)))
  rw [← e] at c
  have r2 := CKAcc.sbuildK_rel (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 (accCItem L).terms
    (fun f hf => fitsLen_of L hw f (ok f hf))
  have r3 := CodexCKAccTail.sunbuildTail_rel (accReg L) (accZ L) (accBank L) L.core.cin 163
    (acc_lengths L hw).1 (accCItem L).terms (fun f hf => fitsLen_of L hw f (ok f hf))
  simp only [accFoldQFKTq,accFoldQFTq,fillInK,fillIn,CodexCKAccTail.fillOutTail,fillOut,toffoliCount_append,measurementCount_append]
  simp only [accFoldQFKTq,accFoldQFTq,toffoliCount_append,measurementCount_append] at r
  constructor <;> omega


theorem accFoldQFK_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQFKTq L g a) := by
  have old := accFoldQF_physicalTq L hw hn g hg a cnt ok cntP okP
  have k := CodexCKAccTail.fillTail_physical L hw hn a cnt ok cntP okP
  simp only [accFoldQFTq,gatePhysical_append] at old
  simp only [accFoldQFKTq,gatePhysical_append]
  exact ⟨k.1,old.2.1,old.2.2.1,old.2.2.2.1,k.2⟩




def bodyCTq (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  mixFoldsQTq L false [.inl (negRot L)]++accFoldQFTq L g (accCItem L)


theorem bodyC_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (bodyCTq L g)=2388 ∧ measurementCount (bodyCTq L g)=2390 := by
  have st := bodyC_static L hw
  have nR : (negRot L).negative=true := rfl
  have cR : (negRot L).canonical=true := rfl
  have nC : (accCItem L).negative=true := rfl
  have f := mixFoldsQ_countsTq L hw false _ st.1
  have f1 : mixFoldsQTTq false [(.inl (negRot L) : MixItem)]=766 := by simp [mixFoldsQTTq,mixNeg,nR,cR]
  have f2 : mixFoldsQMTq false [(.inl (negRot L) : MixItem)]=767 := by simp [mixFoldsQMTq,mixNeg,nR,cR]
  have q := accFoldQ_countsTq L hw (accCItem L) st.2.2.1 st.2.2.2.2
  have qf := accFoldQF_countsTq L g (accCItem L)
  have pr := (accQ_item_prices L hw).2.2
  rw [accCMix_eq] at pr
  simp [mixFoldsQT,mixFoldsQM,mixNeg,nR,cR,nC] at pr
  have rel : accPriceQTq (accCItem L)+257=accPrice (accCItem L) := by simp only [accPriceQTq,accPrice]; omega
  rw [bodyCTq]
  simp only [toffoliCount_append,measurementCount_append]
  rw [f.1,f.2,qf.1,qf.2,q.1,q.2,f1,f2]
  constructor <;> omega


theorem bodyC_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (g : Wire) :
    ECDSAAdd.wires (bodyCTq L g)⊆(g::L.wires).toFinset := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_supportTq L hw hn g false _ st.1
  have b := accFoldQF_supportTq L hw hn g (accCItem L) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  simp only [bodyCTq,wires_append,Finset.union_subset_iff]
  exact ⟨a,b⟩


theorem bodyC_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    Challenge.gateSlots (bodyCTq L g)≤2*(41000+2*(20*(14*163))+(67*256+41)) := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_gateSlotsTq L hw false _ st.1 20 (by intro i hi a e; simp at hi; subst hi; cases e)
  have b := accFoldQF_gateSlotsTq L hw g (accCItem L) st.2.2.1 st.2.2.2.2
  have lt : (accCItem L).terms.length=5 := by simp [accCItem,earlyHTerms]
  have lp : (accCItem L).pre.length=0 := rfl
  rw [lt,lp] at b
  simp only [List.length_singleton] at a
  simp only [bodyCTq,Challenge.gateSlots_append]
  omega


def bodyCKTq (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  mixFoldsQTq L false [.inl (negRot L)]++accFoldQFKTq L g (accCItem L)


theorem bodyCK_relTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (bodyCKTq L g)+31=toffoliCount (bodyCTq L g) ∧
    measurementCount (bodyCKTq L g)=measurementCount (bodyCTq L g) ∧
    ECDSAAdd.wires (bodyCKTq L g)⊆ECDSAAdd.wires (bodyCTq L g) ∧
    Challenge.gateSlots (bodyCKTq L g)≤Challenge.gateSlots (bodyCTq L g) := by
  have st := bodyC_static L hw
  have qk := accFoldQFK_countsCTq L hw g st.2.2.1
  have r := accFoldQFK_relTq L hw g (accCItem L) st.2.2.1
  simp only [bodyCKTq,bodyCTq,toffoliCount_append,measurementCount_append,wires_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,Finset.union_subset_union (Finset.Subset.refl _) r.2.2.1,by omega⟩


theorem bodyCK_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (bodyCKTq L g)=2357 ∧ measurementCount (bodyCKTq L g)=2390 := by
  have r := bodyCK_relTq L hw g
  have c := bodyC_countsTq L hw g
  omega


theorem bodyCK_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (g : Wire) :
    ECDSAAdd.wires (bodyCKTq L g)⊆(g::L.wires).toFinset :=
  (bodyCK_relTq L hw g).2.2.1.trans (bodyC_supportTq L hw hn g)


theorem bodyCK_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires) : GatePhysical (bodyCKTq L g) := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_physicalTq L hw hn false _ st.1
  have b := accFoldQFK_physicalTq L hw hn g hg (accCItem L) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  simp only [bodyCKTq,gatePhysical_append]
  exact ⟨a,b⟩


theorem bodyCK_gateSlotsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    Challenge.gateSlots (bodyCKTq L g)≤2*(41000+2*(20*(14*163))+(67*256+41)) :=
  (bodyCK_relTq L hw g).2.2.2.trans (bodyC_gateSlotsTq L hw g)


theorem accMiddleCFK_bodyTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (M O : Nat) (hO : O<SquareReduction.p)
    (t : State) (m : List Bool) (pv : regValue L.core.product t.basis=M^2)
    (hM : t.basis control=false → M=0)
    (clean : L.PairClean t.basis) (outO : regValue L.core.out t.basis=O) :
    (run (bodyCKTq L control) m t).phase=t.phase ∧
    regValue L.core.out (run (bodyCKTq L control) m t).basis=resCF (t.basis control) (M^2) O ∧
    ∀q,q∉L.core.out → (run (bodyCKTq L control) m t).basis q=t.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have gW : control∉L.wires := (List.nodup_cons.mp hn).1
  have views := accC_views L hw t.basis M pv
  rw [accCMix_eq] at views
  have v1 : ∀i∈[(.inl (negRot L) : MixItem)],MixView L t.basis i := fun i hi => views i (by simp at hi ⊢; exact Or.inl hi)
  have va : AccView L t.basis (accCItem L) := views (.inr (accCItem L)) (by simp)
  let mm := measurementCount (mixFoldsQTq L false [.inl (negRot L)])
  let r1 := run (mixFoldsQTq L false [.inl (negRot L)]) (m.take mm) t
  have e1 := mixFoldsQ_frameTq L hw nd t.basis clean false O hO [.inl (negRot L)] v1 t (m.take mm) ⟨outO,fun _ _ => rfl⟩
  let O1 := mixValue t.basis false O [.inl (negRot L)]
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have e2 := accFoldQFK_frameTq L hw nd control gW t.basis (accCItem L) va clean O1 hO1 r1 (m.drop mm) e1.2
  rw [bodyCKTq,run_append]
  refine ⟨e2.1.trans e1.1,?_,fun q hq => e2.2.2 q hq⟩
  rw [e2.2.1]
  have nR : (negRot L).negative=true := rfl
  have nC : (accCItem L).negative=true := rfl
  have cast1 := mixValue_cast t.basis false O [.inl (negRot L)] hO
  have sum := (accC_mixSum L hw t.basis).trans (L.measuredC_sum hw t.basis (M^2) pv)
  rw [accCMix_eq] at sum
  simp only [mixFinal,mixNeg,nR,nC,mixSignedSum,mixSignedPayload,mixPayload,↓reduceIte,add_zero] at cast1 sum
  simp only [measuredOrientationCast,↓reduceIte,Bool.false_eq_true] at cast1
  have hA : Acc.accVal t.basis 0 (accCItem L).spec<2^163 := Acc.accVal_lt _ 163 _ 0 (by norm_num) va.specValid
  set A := Acc.accVal t.basis 0 (accCItem L).spec with hAdef
  set O1 := mixValue t.basis false O [.inl (negRot L)] with hO1def
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have hp1 : ((SquareReduction.p : Nat) : ZMod SquareReduction.p)=0 := ZMod.natCast_self _
  have e3 : ((SquareReduction.p-1-O1 : Nat) : ZMod SquareReduction.p)=-1-(O1 : ZMod SquareReduction.p) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one,hp1]; ring
  have target : ((((if t.basis control then cFlipK-A else A)+(SquareReduction.p-1-O1)) : Nat) : ZMod SquareReduction.p)=
      measuredOrientationCast false O+(-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)+
        ((if t.basis control then cFlipK else 0 : Nat) : ZMod SquareReduction.p) := by
    simp only [measuredOrientationCast,Bool.false_eq_true,↓reduceIte]
    cases hg : t.basis control
    · have m0 := hM hg
      have a0 : A=0 := by
        have pz : regValue L.core.product t.basis=0 := by rw [pv,m0]; rfl
        exact accC_zero L t.basis pz
      simp only [Bool.false_eq_true,↓reduceIte]
      rw [Nat.cast_add,e3,a0,Nat.cast_zero]
      rw [a0,Nat.cast_zero] at sum
      linear_combination cast1+sum
    · have hAK : A≤cFlipK := by unfold cFlipK; omega
      simp only [↓reduceIte]
      rw [Nat.cast_add,Nat.cast_sub hAK,e3]
      linear_combination cast1+sum
  unfold resCF ofCast
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [←target,ZMod.val_natCast]



end ECDSAAdd.Entrant.OwnDiagAll12Square
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
def wCoreTq (L : CuccaroStreamedSquareWideLayout) : Program := qprogTq (rotWCore L) SquareReduction.p

def wFoldTq (L : CuccaroStreamedSquareWideLayout) : Program :=
  wBuild L++(wCoreTq L++(eSub L (b1Src L)++(eAdd L (whiSrc L)++wUnbuild L)))

def eFoldTq (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  eFlip L c++(accFoldQ4KTq L (eItem L)++eFlip L c)

def bBodyTq (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(wFoldTq L++(eFoldTq L c++wRestore L)))


theorem wCore_stepTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E W : Nat) (hO : O<SquareReduction.p) (hW : W<2^163) :
    Triple (BState L base O E W) (wCoreTq L)
      (BState L base ((W/2^128+2^128*(W%2^128)+(SquareReduction.p-1-O))%SquareReduction.p) E W) := by
  apply lift_out L hn base O E W _ (wCoreTq L)
  intro s m h
  obtain ⟨_,_,hi,padZ,workZ⟩ := zero_regs L hn base hc O E W s.basis h
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hR : W/2^128+2^128*(W%2^128)<SquareReduction.p := by
    have a : W/2^128<2^35 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc W<2^163 := hW
        _ = 2^35*2^128 := by norm_num
    have b := Nat.mod_lt W (show 2^128>0 by positivity)
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at a b ⊢
    omega
  have keep (q : Wire) (hq : q=L.core.outHigh ∨ q=L.core.modFlag ∨ q=L.core.productHigh ∨ q=L.core.workHigh) :
      s.basis q=base q :=
    bstate_other L hn base O E W s.basis h q (Or.inr (Or.inr (Or.inr (by rcases hq with rfl|rfl|rfl|rfl <;> simp))))
  have carryZ : ∀q∈(rotWCore L).carry,s.basis q=false := by
    intro q hq
    simp only [rotWCore,measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact padZ q hq
    · exact (keep _ (Or.inr (Or.inr (Or.inl rfl)))).trans hc.productHigh
    · exact (keep _ (Or.inr (Or.inr (Or.inr rfl)))).trans hc.workHigh
  have ek := QCore.qprog_correctTq (rotWCore L) 256 SquareReduction.c SquareReduction.p (rotWCore_widths L hw)
    (rotWCore_nodup L hn) (by decide) hp (by norm_num [SquareReduction.c]) _ O hR hO s m
    (rotWork_value L hw s.basis W h.2.2.1 workZ) h.1
    ((keep _ (Or.inl rfl)).trans hc.outHigh) ((keep _ (Or.inr (Or.inl rfl))).trans hc.modFlag) carryZ hi
  exact ⟨ek.1,ek.2.1,ek.2.2⟩


theorem eCore_stepTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) (hO : O<SquareReduction.p) :
    Triple (BState L base O E 0) (accFoldQ4KTq L (eItem L))
      (BState L base ((4294968272*E+(SquareReduction.p-1-O))%SquareReduction.p) E 0) := by
  apply lift_out L hn base O E 0 _ (accFoldQ4KTq L (eItem L))
  intro s m h
  have e16 : Acc.accVal s.basis 0 (eItem L).spec%16=0 := by
    rw [show (eItem L).spec=earlyHTerms (eReg L) from rfl,accVal_earlyH,h.2.1]
    omega
  rw [Q4.accFoldQ4_runKTq L hw hn s.basis (eItem L) (eItem_view L hw s.basis)
    (bstate_clean L hn base hc O E s.basis h) O hO e16 s m ⟨h.1,fun _ _ => rfl⟩]
  have tr := accFoldQ_frameKTq L hw hn s.basis (eItem L) (eItem_view L hw s.basis)
    (bstate_clean L hn base hc O E s.basis h) O hO s m ⟨h.1,fun _ _ => rfl⟩
  have e : Acc.accVal s.basis 0 (eItem L).spec=4294968272*E := by
    rw [show (eItem L).spec=earlyHTerms (eReg L) from rfl,accVal_earlyH,h.2.1]
  rw [e] at tr
  exact ⟨tr.1,tr.2.1,tr.2.2⟩


theorem bBody_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (bBodyTq L c) (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let P := M^2
  let b0 := P%2^128
  let b1 := P/2^128
  let W := 4294968272*b1
  let E1 := bE1 P
  let g := base c
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  let O3 := (W/2^128+2^128*(W%2^128)+(SquareReduction.p-1-O2))%SquareReduction.p
  let O4 := (4294968272*flipE g E1+(SquareReduction.p-1-O3))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  have hb1lt : b1<2^128 := by
    show P/2^128<2^128
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hWlt : W<2^163 := by
    show 4294968272*b1<2^163
    norm_num at hb1lt ⊢
    omega
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frameTq L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have e0 : regValue (eReg L) base=b0 := eReg_value L hw base P hP hb
  have a0 : regValue (accReg L) base=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (accReg_work L q hq))
  have hb1 : regValue (hiReg L) base=b1 := by
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have conv1 : ∀s,SquareFrame L.core.out base O2 s → BState L base O2 b0 0 s := by
    intro s hs
    refine ⟨hs.1,?_,?_,fun q h1 _ _ => hs.2 q h1⟩
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (eReg_away L hn q hq).1)).trans e0
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (accReg_out L hn q hq))).trans a0
  -- wFoldTq
  have w1 := wBuild_step L hw hn base hc O2 b0
  rw [hb1] at w1
  have w2 := wCore_stepTq L hw hn base hc O2 b0 W hO2 hWlt
  have w3 := eSub_step L hw hn base hc (b1Src L) (Or.inl rfl) O3 b0 W b1
    (fun t h => (b1Src_value L hw hn base hc O3 b0 W t h).trans hb1)
  have w4 := eAdd_step L hw hn base hc (whiSrc L) (Or.inr rfl) O3 ((b0+2^130-b1)%2^130) W (W/2^128)
    (fun t h => whiSrc_value L hw hn base hc O3 _ W t h)
  have w5 := wUnbuild_step L hw hn base hc O3 (((b0+2^130-b1)%2^130+W/2^128)%2^130)
  rw [hb1] at w5
  have tw : Triple (BState L base O2 b0 0) (wFoldTq L) (BState L base O3 E1 0) :=
    w1.seq (w2.seq (w3.seq (w4.seq w5)))
  -- eFoldTq
  have f1 := eFlip_step L hw hn base c hcw O3 E1 0
  have f2 := eCore_stepTq L hw hn base hc O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn base c hcw O4 (flipE g E1) 0
  rw [flipE_flipE] at f3
  have tf : Triple (BState L base O3 E1 0) (eFoldTq L c) (BState L base O4 E1 0) :=
    f1.seq (f2.seq f3)
  -- wRestore
  have r1 := wBuild_step L hw hn base hc O4 E1
  rw [hb1] at r1
  have r2 := eSub_step L hw hn base hc (whiSrc L) (Or.inr rfl) O4 E1 W (W/2^128)
    (fun t h => whiSrc_value L hw hn base hc O4 E1 W t h)
  have r3 := eAdd_step L hw hn base hc (b1Src L) (Or.inl rfl) O4 ((E1+2^130-W/2^128)%2^130) W b1
    (fun t h => (b1Src_value L hw hn base hc O4 _ W t h).trans hb1)
  have back : ((E1+2^130-W/2^128)%2^130+b1)%2^130=b0 := by
    have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
    have hwh : W/2^128<2^35 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc W<2^163 := hWlt
        _ = 2^35*2^128 := by norm_num
    have e0' : b0=P%2^128 := rfl
    have e1' : b1=P/2^128 := rfl
    have hb0' : P%2^128<2^128 := Nat.mod_lt _ (by positivity)
    show ((bE1 P+2^130-W/2^128)%2^130+b1)%2^130=b0
    unfold bE1
    generalize hx : W/2^128=x at hwh
    norm_num at hb0 hb0' hb1lt hwh ⊢
    omega
  have r4 := wUnbuild_step L hw hn base hc O4 b0
  rw [hb1] at r4
  rw [back] at r3
  have tr : Triple (BState L base O4 E1 0) (wRestore L) (BState L base O4 b0 0) :=
    r1.seq (r2.seq (r3.seq r4))
  have conv2 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
    intro s hs
    refine ⟨hs.1,fun q hq => ?_⟩
    by_cases he : q∈eReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.1.trans e0.symm) q he
    by_cases ha : q∈accReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.2.1.trans a0.symm) q ha
    exact hs.2.2.2 q hq he ha
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tf.seq tr)) conv2))
  exact all


def aFold8Tq (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  wBuild L++(maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK++(qprogTq L.measuredCore SquareReduction.p++
    (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK++wUnbuild L)))


def aBodyTq (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++aFold8Tq L c)


theorem aFold8_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (g : Wire) (hg : g∉L.wires) (base : BasisState)
    (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (aFold8Tq L g)
      (SquareFrame L.core.out base (((if base g then OwnDiagAll12Square.cFlipK-4294968272*regValue (hiReg L) base
        else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have gAcc : g∉accReg L := fun h => hg (OwnDiagAll12Square.accReg_in L g h)
  have gOut : g∉L.core.out := fun h => hg (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := 4294968272*regValue (hiReg L) base
  have hH : regValue (hiReg L) base<2^128 := by
    have h := regValue_lt (hiReg L) base
    rwa [hiReg_length L hw] at h
  have hA : A<2^163 := by
    show 4294968272*regValue (hiReg L) base<2^163
    norm_num at hH ⊢
    omega
  have hAK : A≤OwnDiagAll12Square.cFlipK := by unfold OwnDiagAll12Square.cFlipK; omega
  let A' := if base g then OwnDiagAll12Square.cFlipK-A else A
  have hA' : A'<2^163 := by
    simp only [A']; split
    · unfold OwnDiagAll12Square.cFlipK; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hhi : regValue (hiReg L) b0=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => agree0 q (hiReg_product L q hq))
  have hbuild : Triple (SquareFrame (accReg L) b0 0) (wBuild L) (SquareFrame (accReg L) b0 A) := by
    have h := NarrowAcc.build8_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) b0 hz hb clean.cin
    rw [hhi] at h
    exact h
  rw [aFold8Tq,run_append,run_append,run_append,run_append]
  let mb := measurementCount (wBuild L)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (wBuild L) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK) (m1.take mc) u
  have fl := OwnDiagAll12Square.flip_run L hw hn g gAcc u (m1.take mc)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then OwnDiagAll12Square.cFlipK-regValue (accReg L) u.basis
      else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u1.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using accU1
  have outU : regValue L.core.out u1.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A'<SquareReduction.p := lt_of_lt_of_le hA' (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u1.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK) (m3.take mc) v
  have fl2 := OwnDiagAll12Square.flip_run L hw hn g gAcc v (m3.take mc)
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then OwnDiagAll12Square.cFlipK-regValue (accReg L) v.basis
      else regValue (accReg L) v.basis) at fl2
  rw [gV,accV] at fl2
  have back : (if base g then OwnDiagAll12Square.cFlipK-A' else A')=A := by
    simp only [A']
    cases base g
    · simp
    · simp only [if_true]; omega
  rw [back] at fl2
  let base2 : BasisState := fun q => if q∈L.core.out then v1.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have frame2 : SquareFrame (accReg L) base2 A v1.basis := by
    refine ⟨fl2.2.2,?_⟩
    intro q hq
    by_cases ho : q∈L.core.out
    · simp [base2,ho]
    · rw [b2off q ho,fl2.2.1 q hq,ek.2.2 q ho,fl.2.1 q hq]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hhi2 : regValue (hiReg L) base2=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => (b2off q (prodNotOut q (hiReg_product L q hq))).trans
      (agree0 q (hiReg_product L q hq)))
  have hun : Triple (SquareFrame (accReg L) base2 A) (wUnbuild L) (SquareFrame (accReg L) base2 0) := by
    have h := CodexNarrowTail.unbuild8_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) base2 hz2 hb2 hi2
    rw [hhi2] at h
    exact h
  have eo := hun v1 (m3.drop mc) frame2
  refine ⟨eo.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have e : regValue L.core.out (run (wUnbuild L) (m3.drop mc) v1).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq,fl2.2.1 q na]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq


theorem aBody_frameTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (aBodyTq L c) (SquareFrame L.core.out base (resAF (M^2) O (base c))) := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  let P := M^2
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have v3 : AccView L base (aAcc L) := views (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frameTq L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have hAeq : Acc.accVal base 0 (aAcc L).spec=4294968272*regValue (hiReg L) base := by
    rw [show (aAcc L).spec=earlyHTerms (L.core.product.drop 128) from rfl,accVal_earlyH]
    congr 1
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb,hP]
  have t3 := aFold8_frameTq L hw hn c hcw base hc O2 hO2
  rw [← hAeq] at t3
  have all := t1.seq (t2.seq t3)
  apply Triple.conseq (fun s h => h) all
  intro s hs
  refine ⟨hs.1.trans ?_,hs.2⟩
  -- value
  let A := Acc.accVal base 0 (aAcc L).spec
  have hA : A<2^163 := Acc.accVal_lt base 163 (aAcc L).spec 0 (by norm_num) v3.specValid
  have hsum := (accA_mixSum L hw base).trans (L.measuredA_sum hw base (M^2) hP hb)
  have n1 : mixNeg (.inl (rot128F L) : MixItem)=false := rfl
  have n2 : mixNeg (.inr (aAcc L) : MixItem)=false := rfl
  have n3 : mixNeg (.inl (negP L) : MixItem)=true := rfl
  have e : accAMix L=[.inl (rot128F L),.inr (aAcc L),.inl (negP L)] := rfl
  rw [e] at hsum
  simp only [mixSignedSum,mixSignedPayload,n1,n2,n3,Bool.false_eq_true,if_false,if_true,mixPayload,add_zero,
    pay1,pay2] at hsum
  change ((((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
    (((A : Nat) : ZMod SquareReduction.p)+-((P : Nat) : ZMod SquareReduction.p)))=
      ((P : Nat) : ZMod SquareReduction.p)*2^128-(P : ZMod SquareReduction.p) at hsum
  have bound : ((if base c then OwnDiagAll12Square.cFlipK-A else A)+(SquareReduction.p-1-O2))%SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ pmod
  apply measuredOrientationCast_injective true _ _ bound (ofCast_lt true _)
  refine Eq.trans ?_ (cast_ofCast true (measuredOrientationCast false O+(((M^2 : Nat) : ZMod SquareReduction.p)*2^128-
    ((M^2 : Nat) : ZMod SquareReduction.p)-(if base c then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)))).symm
  simp only [measuredOrientationCast,if_true,Bool.false_eq_true,if_false]
  have c0 := measuredReflection_zmod O hO
  have c1 := measuredReflection_zmod O1 hO1
  have c2 := measuredReflection_zmod O2 hO2
  have k1 : (O1 : ZMod SquareReduction.p)=(P : ZMod SquareReduction.p)+(-1-(O : ZMod SquareReduction.p)) := by
    simp only [O1,ZMod.natCast_mod,Nat.cast_add,c0]
  have k2 : (O2 : ZMod SquareReduction.p)=(((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
      (-1-(O1 : ZMod SquareReduction.p)) := by
    rw [show O2=((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p from rfl,
      ZMod.natCast_mod,Nat.cast_add,c1]
  rw [ZMod.natCast_mod,Nat.cast_add,c2,k2,k1]
  cases hgv : base c
  · have M0 := hg hgv
    have P0 : P=0 := by show M^2=0; rw [M0]; norm_num
    have R0 : (((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)=0 := by rw [P0]; simp
    rw [R0,P0] at hsum
    simp only [Bool.false_eq_true,if_false]
    rw [R0,P0]
    have hM2 : ((M^2 : Nat) : ZMod SquareReduction.p)=0 := by rw [M0]; simp
    rw [hM2]
    simp at hsum ⊢
    linear_combination -hsum
  · simp only [if_true]
    have hAle : A≤OwnDiagAll12Square.cFlipK := by simp only [OwnDiagAll12Square.cFlipK]; omega
    have hoff : ((OwnDiagAll12Square.cFlipK-A : Nat) : ZMod SquareReduction.p)=(OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p)-
        (A : ZMod SquareReduction.p) := by
      rw [Nat.cast_sub hAle]
    rw [hoff]
    linear_combination hsum


end ECDSAAdd.Entrant.ControlLoan1589BFFold
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
theorem bBody_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) : ECDSAAdd.wires (bBodyTq L control)⊆(control::L.wires).toFinset := by
  have memP (f : MeasuredSquareFold) (h : ∀q,f.src.count q≤L.core.product.count q) : ∀q∈f.src,q∈L.core.product :=
    fun q hq => List.count_pos_iff.mp (by have := h q; have := List.count_pos_iff.mpr hq; omega)
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have a1 := measuredFoldQ_supportTq L control (negP L) (memP _ sP)
  have a2 := measuredFoldQ_supportTq L control (rot128F L) (memP _ sR)
  have hS : ∀f∈wTerms L,(L.core.cin::(f.src++accReg L++accZ L++accBank L)).toFinset⊆
      (control::L.wires).toFinset := by
      intro f hf q hq
      have st := (earlyH_static L (hiReg L) (hiReg_count L) (by rw [hiReg_length L hw]; omega)
        (by rw [hiReg_length L hw]; omega)).1 f hf
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
      apply wires_in L control q
      rcases hq with rfl|((h|h)|h)|h
      · simp
      · exact Or.inr (Or.inl (memP f st q h))
      · exact Or.inr (Or.inr (Or.inl (accReg_work L q h)))
      · rcases accZ_mem L q h with h1|h1
        · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
        · exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h))))
  have wb0 := CodexNarrowTail.build8_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn)
  rw [CodexNarrowTail.build8_eq] at wb0
  have place := hS _ (NarrowAcc.terms_mem (hiReg L)).1
  simp only [Acc.earlyTerm_src] at place
  have wb : ECDSAAdd.wires (wBuild L)⊆(control::L.wires).toFinset ∧
      ECDSAAdd.wires (wUnbuild L)⊆(control::L.wires).toFinset :=
    ⟨wb0.1.trans place,wb0.2.trans place⟩
  have wc : ECDSAAdd.wires (wCoreTq L)⊆(control::L.wires).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (QCore.qprog_supportTq (rotWCore L) SquareReduction.p hq)
    have hd : q∈L.core.work.drop 128 → q∈L.core.work := List.mem_of_mem_drop
    have ht : q∈L.core.work.take 128 → q∈L.core.work := List.mem_of_mem_take
    apply wires_in L control q
    simp only [rotWCore,rotWork,measuredCore,foldCarry,MeasuredCanonicalModLayout.wires,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have adder (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      (L.core.cin::(src++eReg L++eBank L)).toFinset⊆(control::L.wires).toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    apply wires_in L control q
    rcases hq with rfl|((h|h)|h)
    · simp
    · rcases hs with rfl|rfl <;> simp only [b1Src,whiSrc,eZ,List.mem_append] at h
      · rcases h with h|h
        · exact Or.inr (Or.inl (hiReg_product L q h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take h)))))
      · rcases h with h|h
        · exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take h)))))
    · exact Or.inr (Or.inl (eReg_product L q h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h))))
  have es (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      ECDSAAdd.wires (eSub L src)⊆(control::L.wires).toFinset := by
    have lens := eSrc_length L hw src hs
    rw [eSub,subInPlace_wires _ _ _ _ lens.1 lens.2]; exact adder src hs
  have ea (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      ECDSAAdd.wires (eAdd L src)⊆(control::L.wires).toFinset := by
    have lens := eSrc_length L hw src hs
    rw [eAdd,addInPlace_wires _ _ _ _ lens.1 lens.2]; exact adder src hs
  have fl : ECDSAAdd.wires (eFlip L control)⊆(control::L.wires).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (maskedConstant_wires_subset control ((eReg L).take 129) (2^129-1) hq)
    rcases List.mem_cons.mp h with rfl|h
    · simp
    · exact wires_in L control q (Or.inr (Or.inl (eReg_product L q (List.mem_of_mem_take h))))
  have st := eItem_static L hw
  have ac := ((Q4.accFoldQ4KTq_rel L hw (eItem L) st.2.1).2.2.1.trans (Q4.accFoldQ4_wiresTq L (eItem L))).trans
    (accFoldQ_supportTq L hw hn control (eItem L) st.1 st.2.1 st.2.2.1 st.2.2.2)
  simp only [bBodyTq,wFoldTq,eFoldTq,wRestore,wires_append,Finset.union_subset_iff]
  exact ⟨a1,a2,⟨wb.1,wc,es _ (Or.inl rfl),ea _ (Or.inr rfl),wb.2⟩,⟨fl,ac,fl⟩,
    ⟨wb.1,es _ (Or.inr rfl),ea _ (Or.inl rfl),wb.2⟩⟩


theorem aBody_supportTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) : ECDSAAdd.wires (aBodyTq L control)⊆(control::L.wires).toFinset := by
  have wb := wBuild_support L hw hn control
  have memP (f : MeasuredSquareFold) (h : ∀q,f.src.count q≤L.core.product.count q) : ∀q∈f.src,q∈L.core.product :=
    fun q hq => List.count_pos_iff.mp (by have := h q; have := List.count_pos_iff.mpr hq; omega)
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have a1 := measuredFoldQ_supportTq L control (negP L) (memP _ sP)
  have a2 := measuredFoldQ_supportTq L control (rot128F L) (memP _ sR)
  have full := accFoldQ_supportTq L hw hn control (aAcc L) sA.1 sA.2.1 sA.2.2.1 sA.2.2.2
  simp only [accFoldQTq,wires_append,Finset.union_subset_iff] at full
  have mc : ECDSAAdd.wires (maskedConstant control (accReg L) OwnDiagAll12Square.cFlipK)⊆
      (control::L.wires).toFinset := by
    refine (maskedConstant_wires_subset _ _ _).trans ?_
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq ⊢
    rcases hq with h|h
    · exact Or.inl h
    · exact Or.inr (OwnDiagAll12Square.accReg_in L q h)
  simp only [aBodyTq,aFold8Tq,wires_append,Finset.union_subset_iff]
  exact ⟨a1,a2,wb.1,mc,full.1.2,mc,wb.2⟩



theorem eItem_priceTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : accPriceQTq (eItem L)=1554 := by
  have hl := eReg_length L hw
  norm_num [eItem,accPriceQTq,earlyHTerms,Acc.earlyTerm,Acc.sbuildT,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,
    Acc.buildT,hl]


theorem bBody_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (bBodyTq L c)=5819 ∧ measurementCount (bBodyTq L c)=5924 := by
  have q1 := measuredFoldQ_countsTq L hw (negP L)
  have q2 := measuredFoldQ_countsTq L hw (rot128F L)
  have bc := CodexNarrowTail.build8_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_okLen L hw)
  rw [CodexNarrowTail.build8_eq] at bc
  have wb : toffoliCount (wBuild L)=387 ∧ measurementCount (wBuild L)=388 := bc.1
  have wu : toffoliCount (wUnbuild L)=358 ∧ measurementCount (wUnbuild L)=388 := bc.2
  have core := QCore.qprog_countsTq (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)
  have wc : toffoliCount (wCoreTq L)=766 ∧ measurementCount (wCoreTq L)=767 :=
    ⟨core.1.trans (by norm_num),core.2.trans (by norm_num)⟩
  have el := eReg_length L hw
  have l1 := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have l2 := eSrc_length L hw (whiSrc L) (Or.inr rfl)
  have s1 : toffoliCount (eSub L (b1Src L))=129 ∧ measurementCount (eSub L (b1Src L))=129 := by
    have h := subInPlace_counts (b1Src L) (eReg L) (eBank L) L.core.cin l1.1 l1.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have s2 : toffoliCount (eSub L (whiSrc L))=129 ∧ measurementCount (eSub L (whiSrc L))=129 := by
    have h := subInPlace_counts (whiSrc L) (eReg L) (eBank L) L.core.cin l2.1 l2.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have a1 : toffoliCount (eAdd L (b1Src L))=129 ∧ measurementCount (eAdd L (b1Src L))=129 := by
    have h := addInPlace_counts (b1Src L) (eReg L) (eBank L) L.core.cin l1.1 l1.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have a2 : toffoliCount (eAdd L (whiSrc L))=129 ∧ measurementCount (eAdd L (whiSrc L))=129 := by
    have h := addInPlace_counts (whiSrc L) (eReg L) (eBank L) L.core.cin l2.1 l2.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have fl : toffoliCount (eFlip L c)=0 ∧ measurementCount (eFlip L c)=0 :=
    maskedConstant_counts c ((eReg L).take 129) (2^129-1)
  have st := eItem_static L hw
  have ac0 := accFoldQ_countsTq L hw (eItem L) st.2.1 st.2.2.2
  rw [eItem_priceTq L hw] at ac0
  have ac4 := Q4.accFoldQ4_countsTq L hw (eItem L)
  have k4 := Q4.accFoldQ4KTq_counts_early L hw (eItem L) (eReg L) (by simp [eReg,hw.core.product]) rfl st.2.1
  have k4m := (Q4.accFoldQ4KTq_rel L hw (eItem L) st.2.1).2.1
  have ac : toffoliCount (accFoldQ4KTq L (eItem L))=1515 ∧ measurementCount (accFoldQ4KTq L (eItem L))=1555 :=
    ⟨by omega,by omega⟩
  simp only [bBodyTq,wFoldTq,eFoldTq,wRestore,toffoliCount_append,measurementCount_append,q1.1,q1.2,q2.1,q2.2,
    wb.1,wb.2,wu.1,wu.2,wc.1,wc.2,s1.1,s1.2,s2.1,s2.2,a1.1,a1.2,a2.1,a2.2,fl.1,fl.2,ac.1,ac.2]
  exact ⟨trivial,trivial⟩


theorem aBody_countsTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (aBodyTq L c)=3043 ∧ measurementCount (aBodyTq L c)=3077 := by
  have q1 := measuredFoldQ_countsTq L hw (negP L)
  have q2 := measuredFoldQ_countsTq L hw (rot128F L)
  have bc := CodexNarrowTail.build8_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_okLen L hw)
  rw [CodexNarrowTail.build8_eq] at bc
  have wb : toffoliCount (wBuild L)=387 ∧ measurementCount (wBuild L)=388 := bc.1
  have wu : toffoliCount (wUnbuild L)=358 ∧ measurementCount (wUnbuild L)=388 := bc.2
  have k := maskedConstant_counts c (accReg L) OwnDiagAll12Square.cFlipK
  have qc := QCore.qprog_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)
  simp only [aBodyTq,aFold8Tq,toffoliCount_append,measurementCount_append,q1.1,q1.2,q2.1,q2.2,wb.1,wb.2,wu.1,wu.2,
    k.1,k.2,qc.1,qc.2]
  constructor <;> norm_num


theorem bBody_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (hn : (c::L.wires).Nodup) : GatePhysical (bBodyTq L c) := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw := (List.nodup_cons.mp hn).1
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have p1 := measuredFoldQ_physicalTq L hw nd (negP L) sP
  have p2 := measuredFoldQ_physicalTq L hw nd (rot128F L) sR
  have wb := CodexNarrowTail.build8_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_fits L hw nd)
  rw [CodexNarrowTail.build8_eq] at wb
  have wc := QCore.qprog_physicalTq (rotWCore L) SquareReduction.p (rotWCore_nodup L nd)
  have adderNd (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      (L.core.cin::src++eReg L++eBank L).Nodup := by
    have h := eAdder_nodup L nd src hs
    simpa only [List.cons_append,List.append_assoc] using h
  have es (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) : GatePhysical (eSub L src) :=
    subInPlace_physical src (eReg L) (eBank L) L.core.cin (adderNd src hs)
  have ea (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) : GatePhysical (eAdd L src) :=
    addInPlace_physical src (eReg L) (eBank L) L.core.cin (adderNd src hs)
  have hct : c∉(eReg L).take 129 := fun hm => hcw (by
    have := eReg_product L c (List.mem_of_mem_take hm)
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this])
  have fl : GatePhysical (eFlip L c) := maskedConstant_physical c ((eReg L).take 129) (2^129-1) hct
  have st := eItem_static L hw
  have ac := Q4.accFoldQ4KTq_physical L hw nd (eItem L) st.1 st.2.1 st.2.2.1 st.2.2.2
  simp only [bBodyTq,wFoldTq,eFoldTq,wRestore,gatePhysical_append]
  exact ⟨p1,p2,⟨wb.1,wc,es _ (Or.inl rfl),ea _ (Or.inr rfl),wb.2⟩,⟨fl,ac,fl⟩,
    ⟨wb.1,es _ (Or.inr rfl),ea _ (Or.inl rfl),wb.2⟩⟩


theorem aBody_physicalTq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (hn : (c::L.wires).Nodup) : GatePhysical (aBodyTq L c) := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw := (List.nodup_cons.mp hn).1
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have p1 := measuredFoldQ_physicalTq L hw nd (negP L) sP
  have p2 := measuredFoldQ_physicalTq L hw nd (rot128F L) sR
  have wb := CodexNarrowTail.build8_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_fits L hw nd)
  rw [CodexNarrowTail.build8_eq] at wb
  have full := accFoldQ_physicalTq L hw nd (aAcc L) sA.1 sA.2.1 sA.2.2.1 sA.2.2.2
  simp only [accFoldQTq,gatePhysical_append] at full
  have mc := maskedConstant_physical c (accReg L) OwnDiagAll12Square.cFlipK
    (fun h => hcw (OwnDiagAll12Square.accReg_in L c h))
  simp only [aBodyTq,aFold8Tq,gatePhysical_append]
  exact ⟨p1,p2,wb.1,mc,full.1.2,mc,wb.2⟩


end ECDSAAdd.Entrant.ControlLoan1589BFFold

/-! ### Support and gate-slot refinement: every `Tq` body uses a subset of the wires and no more
gate slots than the body it replaces. -/

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout RecordedQuantum

namespace QRel

/-- `P'` refines `P` statically: fewer wires and fewer gate slots. -/
def Le (P' P : Program) : Prop :=
  ECDSAAdd.wires P'⊆ECDSAAdd.wires P ∧ Challenge.gateSlots P'≤Challenge.gateSlots P

theorem Le.rfl' (P : Program) : Le P P := ⟨Finset.Subset.refl _,le_rfl⟩

theorem Le.app {A A' B B' : Program} (h1 : Le A' A) (h2 : Le B' B) : Le (A'++B') (A++B) :=
  ⟨by rw [wires_append,wires_append]; exact Finset.union_subset_union h1.1 h2.1,
   by rw [Challenge.gateSlots_append,Challenge.gateSlots_append]; exact Nat.add_le_add h1.2 h2.2⟩

theorem mappedConstant_snoc (c : Option Wire) (n : Nat) : ∀ k : Nat,
    mappedConstant c (n+1) k=mappedConstant c n k++[mappedConstantBit c (decide ((k/2^n)%2=1))] := by
  induction n with
  | zero => intro k; simp [mappedConstant]
  | succ n ih =>
    intro k
    show mappedConstantBit c (decide (k%2=1))::mappedConstant c (n+1) (k/2)=
      (mappedConstantBit c (decide (k%2=1))::mappedConstant c n (k/2))++_
    rw [ih (k/2),Nat.div_div_eq_div_mul,← pow_succ']
    rfl

theorem majority_slots_pos (b : MappedBit) (y c t : Wire) :
    1≤Challenge.gateSlots (mappedMajority b y c t) := by
  rcases b with ⟨_|a,_|_⟩ <;>
    simp [mappedMajority,majority,borrowMajority,Challenge.gateSlots,Challenge.instructionSlots]

theorem mappedAdd_snoc_le (b : MappedBit) (y : Wire) (xs : List MappedBit) : ∀ (ys cs : List Wire) (c : Wire),
    xs.length=ys.length → 0<xs.length → xs.length≤cs.length →
    ECDSAAdd.wires (mappedAdd xs ys (cs.take (xs.length-1)) c)⊆ECDSAAdd.wires (mappedAdd (xs++[b]) (ys++[y]) cs c) ∧
    Challenge.gateSlots (mappedAdd xs ys (cs.take (xs.length-1)) c)+1≤
      Challenge.gateSlots (mappedAdd (xs++[b]) (ys++[y]) cs c) := by
  induction xs with
  | nil => intro ys cs c _ h _; simp at h
  | cons x0 xs ih =>
    intro ys cs c hl _ hc
    rcases ys with _|⟨y0,ys⟩
    · simp at hl
    rcases cs with _|⟨d,ds⟩
    · simp at hc
    simp only [List.length_cons,Nat.add_right_cancel_iff] at hl hc
    rcases xs with _|⟨x1,xs⟩
    · rcases ys with _|⟨y1,ys⟩
      · have m1 := majority_slots_pos x0 y0 c d
        simp only [List.cons_append,List.nil_append,mappedAdd,List.length_cons,List.length_nil,
          Nat.sub_self,List.take_zero,wires_append,Challenge.gateSlots_append]
        refine ⟨fun q h => ?_,by omega⟩
        simp only [Finset.mem_union]; tauto
      · simp at hl
    · rcases ys with _|⟨y1,ys⟩
      · simp at hl
      · have h := ih (y1::ys) ds d (by simpa using hl) (by simp) (by simp at hc ⊢; omega)
        simp only [List.cons_append,List.length_cons,Nat.add_sub_cancel] at h ⊢
        simp only [List.take_succ_cons,mappedAdd,wires_append,Challenge.gateSlots_append]
        refine ⟨Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union
          (Finset.Subset.refl _) h.1) (Finset.Subset.refl _)) (Finset.Subset.refl _),by omega⟩

theorem const_le (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (hn : 0<n) :
    ECDSAAdd.wires (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p)⊆
      ECDSAAdd.wires (mappedConstAdd (some K.flag) K.extended K.carry K.cin p) ∧
    Challenge.gateSlots (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p)+1≤
      Challenge.gateSlots (mappedConstAdd (some K.flag) K.extended K.carry K.cin p) := by
  have h := mappedAdd_snoc_le (mappedConstantBit (some K.flag) (decide ((p/2^K.out.length)%2=1))) K.high
    (mappedConstant (some K.flag) K.out.length p) K.out K.carry K.cin
    (by simp [mappedConstant_length]) (by simp [mappedConstant_length,hw.out]; omega)
    (by simp [mappedConstant_length,hw.out,hw.carry])
  rw [mappedConstant_length] at h
  have e : mappedConstAdd (some K.flag) K.extended K.carry K.cin p=
      mappedAdd (mappedConstant (some K.flag) K.out.length p++
        [mappedConstantBit (some K.flag) (decide ((p/2^K.out.length)%2=1))]) (K.out++[K.high]) K.carry K.cin := by
    rw [← mappedConstant_snoc]; simp [mappedConstAdd,MeasuredCanonicalModLayout.extended]
  rw [e]; exact h

theorem le_core (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (hn : 0<n) (P1 P3 : Program) :
    Le (P1++([.CX K.high K.flag,.X K.flag]++
        (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p++([.CX K.flag K.high]++P3))))
      (P1++([.CX K.high K.flag,.X K.flag]++(mappedConstAdd (some K.flag) K.extended K.carry K.cin p++P3))) := by
  obtain ⟨hw',hs⟩ := const_le K n p hw hn
  constructor
  · intro q hq
    have hcx : q∈ECDSAAdd.wires [Instr.CX K.flag K.high] →
        q∈ECDSAAdd.wires [Instr.CX K.high K.flag,Instr.X K.flag] := by
      intro h; simp [ECDSAAdd.wires,Instr.wires] at h ⊢; tauto
    have hm : q∈ECDSAAdd.wires (mappedConstAdd (some K.flag) K.out (K.carry.take (K.out.length-1)) K.cin p) →
        q∈ECDSAAdd.wires (mappedConstAdd (some K.flag) K.extended K.carry K.cin p) := fun h => hw' h
    simp only [wires_append,Finset.mem_union] at hq ⊢
    tauto
  · simp only [Challenge.gateSlots_append]
    have : Challenge.gateSlots [Instr.CX K.flag K.high]=1 := rfl
    omega

theorem qprog_le (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (hn : 0<n) :
    Le (qprogTq K p) (qprog K p) := by
  have g := le_core K n p hw hn (notRegister K.out++K.sum)
    ([.X K.high,.X K.flag]++eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag)
  simpa only [qprogTq,qprog,List.append_assoc] using g

theorem qprog4_le (K : MeasuredCanonicalModLayout) (n p : Nat) (hw : K.Widths n) (hn : 0<n) :
    Le (qprog4Tq K p) (qprog4 K p) := by
  have g := le_core K n p hw hn (notRegister K.out++Skip4.addSkip 4
      (mappedRead K.src false++[({wire:=none,flip:=false} : MappedBit)]) K.extended K.carry K.cin)
    ([.X K.high,.X K.flag]++Skip4.eraseSkip 4 K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag)
  simpa only [qprog4Tq,qprog4,List.append_assoc] using g

theorem measuredFoldQ_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold) :
    Le (measuredFoldQTq L f) (measuredFoldQ L f) := by
  unfold measuredFoldQTq measuredFoldQ
  exact Le.app (Le.app (Le.rfl' _)
    (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide))) (Le.rfl' _)

theorem accFoldQ_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem) :
    Le (accFoldQTq L a) (accFoldQ L a) := by
  unfold accFoldQTq accFoldQ
  exact Le.app (Le.app (Le.rfl' _)
    (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide))) (Le.rfl' _)

theorem accFoldQ4K_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem) :
    Le (accFoldQ4KTq L a) (CodexCKAccTail.accFoldQ4Tail L a) := by
  unfold accFoldQ4KTq CodexCKAccTail.accFoldQ4Tail
  exact Le.app (Le.app (Le.rfl' _)
    (qprog4_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide))) (Le.rfl' _)

theorem mixProgQ_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (i : MixItem) :
    Le (mixProgQTq L i) (mixProgQ L i) := by
  rcases i with f|a
  · by_cases h : f.canonical
    · simp only [mixProgQTq,mixProgQ,h,if_true]; exact measuredFoldQ_le L hw f
    · simp only [mixProgQTq,mixProgQ,h]; exact Le.rfl' _
  · exact accFoldQ_le L hw a

theorem mixFoldsQ_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (o : Bool) (items : List MixItem) :
    Le (mixFoldsQTq L o items) (mixFoldsQ L o items) := by
  induction items generalizing o with
  | nil => exact Le.rfl' _
  | cons i is ih =>
    simp only [mixFoldsQTq,mixFoldsQ]
    refine Le.app ?_ (ih _)
    rcases Decidable.em (o=mixNeg i) with h|h
    · rw [if_pos h,if_pos h]; exact Le.rfl' _
    · rw [if_neg h,if_neg h]; exact mixProgQ_le L hw i

theorem accFoldQF_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) (a : AccItem) :
    Le (OwnDiagAll12Square.accFoldQFTq L g a) (OwnDiagAll12Square.accFoldQF L g a) := by
  unfold OwnDiagAll12Square.accFoldQFTq OwnDiagAll12Square.accFoldQF
  exact Le.app (Le.rfl' _) (Le.app (Le.rfl' _) (Le.app
    (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)) (Le.rfl' _)))

theorem bodyC_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    Le (OwnDiagAll12Square.bodyCTq L g) (OwnDiagAll12Square.bodyC L g) := by
  unfold OwnDiagAll12Square.bodyCTq OwnDiagAll12Square.bodyC
  exact Le.app (mixFoldsQ_le L hw _ _) (accFoldQF_le L hw g _)

theorem accFoldQFK_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) (a : AccItem) :
    Le (OwnDiagAll12Square.accFoldQFKTq L g a) (CodexCKAccTail.accFoldQFTail L g a) := by
  unfold OwnDiagAll12Square.accFoldQFKTq CodexCKAccTail.accFoldQFTail
  exact Le.app (Le.rfl' _) (Le.app (Le.rfl' _) (Le.app
    (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)) (Le.rfl' _)))

theorem bodyCK_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    Le (OwnDiagAll12Square.bodyCKTq L g) (CodexCKAccTail.bodyCTail L g) := by
  unfold OwnDiagAll12Square.bodyCKTq CodexCKAccTail.bodyCTail
  exact Le.app (mixFoldsQ_le L hw _ _) (accFoldQFK_le L hw g _)

theorem wFold_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Le (ControlLoan1589BFFold.wFoldTq L) (ControlLoan1589BFFold.wFold L) := by
  unfold ControlLoan1589BFFold.wFoldTq ControlLoan1589BFFold.wFold ControlLoan1589BFFold.wCoreTq
    ControlLoan1589BFFold.wCore
  exact Le.app (Le.rfl' _) (Le.app (qprog_le (ControlLoan1589BFFold.rotWCore L) 256 SquareReduction.p
    (ControlLoan1589BFFold.rotWCore_widths L hw) (by decide)) (Le.rfl' _))

theorem eFold_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Le (ControlLoan1589BFFold.eFoldTq L c) (ControlLoan1589BFFold.eFold L c) := by
  unfold ControlLoan1589BFFold.eFoldTq ControlLoan1589BFFold.eFold
  exact Le.app (Le.rfl' _) (Le.app (accFoldQ4K_le L hw _) (Le.rfl' _))

theorem bBody_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Le (ControlLoan1589BFFold.bBodyTq L c) (ControlLoan1589BFFold.bBody L c) := by
  unfold ControlLoan1589BFFold.bBodyTq ControlLoan1589BFFold.bBody
  exact Le.app (measuredFoldQ_le L hw _) (Le.app (measuredFoldQ_le L hw _)
    (Le.app (wFold_le L hw) (Le.app (eFold_le L hw c) (Le.rfl' _))))

theorem aBody_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Le (ControlLoan1589BFFold.aBodyTq L c) (ControlLoan1589BFFold.aBody L c) := by
  unfold ControlLoan1589BFFold.aBodyTq ControlLoan1589BFFold.aBody ControlLoan1589BFFold.aFold8Tq
    ControlLoan1589BFFold.aFold8
  exact Le.app (measuredFoldQ_le L hw _) (Le.app (measuredFoldQ_le L hw _)
    (Le.app (Le.rfl' _) (Le.app (Le.rfl' _) (Le.app
      (qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)) (Le.rfl' _)))))

theorem bodyCK_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (OwnDiagAll12Square.bodyCKTq L g)+2=toffoliCount (CodexCKAccTail.bodyCTail L g) ∧
    measurementCount (OwnDiagAll12Square.bodyCKTq L g)+2=measurementCount (CodexCKAccTail.bodyCTail L g) ∧
    Le (OwnDiagAll12Square.bodyCKTq L g) (CodexCKAccTail.bodyCTail L g) := by
  have a := OwnDiagAll12Square.bodyCK_countsTq L hw g
  have b := CodexCKAccTail.bodyCTail_counts L hw g
  exact ⟨by omega,by omega,bodyCK_le L hw g⟩

theorem bBody_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (ControlLoan1589BFFold.bBodyTq L c)+4=toffoliCount (ControlLoan1589BFFold.bBody L c) ∧
    measurementCount (ControlLoan1589BFFold.bBodyTq L c)+4=measurementCount (ControlLoan1589BFFold.bBody L c) ∧
    Le (ControlLoan1589BFFold.bBodyTq L c) (ControlLoan1589BFFold.bBody L c) := by
  have a := ControlLoan1589BFFold.bBody_countsTq L hw c
  have b := ControlLoan1589BFFold.bBody_counts L hw c
  exact ⟨by omega,by omega,bBody_le L hw c⟩

theorem aBody_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (ControlLoan1589BFFold.aBodyTq L c)+3=toffoliCount (ControlLoan1589BFFold.aBody L c) ∧
    measurementCount (ControlLoan1589BFFold.aBodyTq L c)+3=measurementCount (ControlLoan1589BFFold.aBody L c) ∧
    Le (ControlLoan1589BFFold.aBodyTq L c) (ControlLoan1589BFFold.aBody L c) := by
  have a := ControlLoan1589BFFold.aBody_countsTq L hw c
  have b := ControlLoan1589BFFold.aBody_counts L hw c
  exact ⟨by omega,by omega,aBody_le L hw c⟩

end QRel
end ECDSAAdd.Entrant

end
