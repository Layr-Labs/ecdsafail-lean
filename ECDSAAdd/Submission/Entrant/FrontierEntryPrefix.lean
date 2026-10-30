import ECDSAAdd.Submission.Entrant.FrontierEntryLayout
import ECDSAAdd.Submission.Entrant.FrontierEntryMath

set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField
attribute [local irreducible] run

def copyControl (L : Layout) (J B : Wire) : Program :=
  [.CCX J B (lowY L)]++copyRegister (some J) L.r.tail L.y.tail

def productsSeed (L : Layout) : Program :=
  [.CX L.r0 L.parity,.CCX L.parity L.rmsb L.lower,
    .CCX L.parity (lowY L) L.one,.CCX L.lower (lowY L) L.sign,.CX L.parity L.r0]

def rightShift (L : Layout) : Program :=
  rotateRight L.r++[.CX (L.r.getD 254 0) L.rmsb]

theorem prepare_shape (L : Layout) (J B : Wire) :
    prepare L J B=copyControl L J B++productsSeed L++rightShift L++signComplement (lowY L) L.r := by
  simp only [prepare,copyControl,productsSeed,rightShift,List.append_assoc]

structure PrefixResult (L : Layout) (J B : Wire) (Jv Bv : Bool) (Y : Int) (s t : State) : Prop where
  phase : t.phase=s.phase
  target : regValue L.r t.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y))
  source : regValue L.y t.basis=(Jv && Bv).toNat+2*(if Jv then encodeWord 256 Y/2 else 0)
  parity : t.basis L.parity=originalParity Y
  a : t.basis L.lower=(originalParity Y && negative Y)
  d : t.basis L.one=(originalParity Y && (Jv && Bv))
  e : t.basis L.sign=((originalParity Y && negative Y) && (Jv && Bv))
  u : t.basis (lowY L)=(Jv && Bv)
  j : t.basis J=Jv
  b : t.basis B=Bv
  carry : ∀q∈L.carry,t.basis q=false
  outside : ∀q,q∉L.r++L.y++[L.parity,L.lower,L.one,L.sign] → t.basis q=s.basis q

theorem rightShift_spec (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=2*encodeWord 255 (Y/2)) :
    let t := run (rightShift L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 256 (Y/2) ∧
    (∀q,q∉L.r → t.basis q=s.basis q) := by
  let t := run (rotateRight L.r) [] s
  have len := BalancedCleanup.widths L.toLayout hw
  have nd := EntryHalf5.target_nodup L hn
  have rot := rotateRight_spec L.r nd (2*encodeWord 255 (Y/2)) (by omega) s [] hR
  have frame := rotate_frame L.r s []
  have value : regValue L.r t.basis=encodeWord 255 (Y/2) := by
    have h : regValue L.r t.basis=2*encodeWord 255 (Y/2)/2 := rot.2
    omega
  have bound := encodeWord_bound 255 (Y/2)
  have top : t.basis L.rmsb=false := by
    have h := regValue_highBit L.low L.rmsb t.basis
    change t.basis L.rmsb=true ↔ 2^L.low.length≤regValue L.r t.basis at h
    rw [len.1,value] at h
    cases e : t.basis L.rmsb
    · rfl
    · have := h.mp e;omega
  have low : regValue L.low t.basis=encodeWord 255 (Y/2) := by
    rw [BalancedCleanup.Layout.r,regValue_append,len.1] at value
    simpa [regValue,top] using value
  have msbAway : L.rmsb∉L.low :=
    fun h => List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 h (by simp)
  have split : L.low=L.r.take 254++[L.r.getD 254 0] := by
    have idx : 254<L.r.length := by rw [len.2.1];decide
    have h := List.take_succ_eq_append_getElem idx
    have take : L.r.take 255=L.low := by
      change (L.low++[L.rmsb]).take 255=L.low
      rw [←len.1,List.take_left]
    rw [show 254+1=255 from rfl,take] at h
    simpa only [List.getD_eq_getElem _ _ idx] using h
  let out := run [.CX (L.r.getD 254 0) L.rmsb] [] t
  have off (q : Wire) (hq : q≠L.rmsb) : out.basis q=t.basis q := by simp [out,run,writeBit,hq]
  have newLow : regValue L.low out.basis=encodeWord 255 (Y/2) :=
    (regValue_congr _ _ _ (fun q hq => off q (fun e => msbAway (e ▸ hq)))).trans low
  have signApart : L.r.getD 254 0≠L.rmsb := by
    intro eq
    have member : L.r.getD 254 0∈L.low := by rw [split];simp
    exact msbAway (eq ▸ member)
  have signCopy : out.basis L.rmsb=out.basis (L.r.getD 254 0) := by
    have h : out.basis L.rmsb=t.basis (L.r.getD 254 0) := by simp [out,run,writeBit,top]
    exact h.trans (off _ signApart).symm
  have same := signed_extension (L.r.take 254) (L.r.getD 254 0) L.rmsb out.basis signCopy
  rw [←split] at same
  have signed : signedRegValue L.low out.basis=Y/2 := by
    unfold signedRegValue
    rw [len.1,newLow]
    apply decode_encodeWord 255 (by decide)
    have h := constants
    unfold Centered at hy
    norm_num only [Nat.reducePow,Nat.reduceSub] at h ⊢
    omega
  have result : regValue L.r out.basis=encodeWord 256 (Y/2) :=
    word_encoding L.r 256 len.2.1 out.basis (Y/2) (same.trans signed)
  have actual : run (rightShift L) m s=out := by
    rw [rightShift,run_append,(rotate_counts _).2.1,List.take_zero,List.drop_zero]
    simp only [out,t,run]
  rw [actual]
  refine ⟨?_,result,?_⟩
  · simpa only [out,run] using frame.1
  · intro q hq
    have qa : q≠L.rmsb := fun e => hq (by simp [e,BalancedCleanup.Layout.r])
    exact (off q qa).trans (frame.2.1 q hq)

theorem productsSeed_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P H U : Bool) (s : State) (m : List Bool)
    (hp : s.basis L.r0=P) (hh : s.basis L.rmsb=H) (hu : s.basis (lowY L)=U)
    (zp : s.basis L.parity=false) (za : s.basis L.lower=false)
    (zd : s.basis L.one=false) (ze : s.basis L.sign=false) :
    run (productsSeed L) m s=⟨s.phase,
      writeBit (writeBit (writeBit (writeBit (writeBit s.basis L.parity P)
        L.lower (P && H)) L.one (P && U)) L.sign ((P && H) && U)) L.r0 false⟩ := by
  have nd : [L.r0,L.rmsb,L.parity,L.lower,L.one,L.sign,lowY L].Nodup := by
    cases hys : L.ylow with
    | nil => have h := hw.2.1;simp [hys] at h
    | cons a as =>
      apply List.nodup_iff_count.mpr
      intro q
      have h := List.nodup_iff_count.mp hn q
      simp only [Layout.wires,BalancedCleanup.Layout.wires,lowY,hys,List.getD_cons_zero,
        List.count_append,List.count_cons,List.count_nil] at h ⊢
      omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨n01,n02,n03,n04,n05,n06⟩,⟨⟨n12,n13,n14,n15,n16⟩,⟨⟨n23,n24,n25,n26⟩,⟨⟨n34,n35,n36⟩,⟨⟨n45,n46⟩,n56⟩⟩⟩⟩⟩
  have n10 := Ne.symm n01
  have n20 := Ne.symm n02
  have n30 := Ne.symm n03
  have n40 := Ne.symm n04
  have n50 := Ne.symm n05
  have n60 := Ne.symm n06
  have n21 := Ne.symm n12
  have n31 := Ne.symm n13
  have n41 := Ne.symm n14
  have n51 := Ne.symm n15
  have n61 := Ne.symm n16
  have n32 := Ne.symm n23
  have n42 := Ne.symm n24
  have n52 := Ne.symm n25
  have n62 := Ne.symm n26
  have n43 := Ne.symm n34
  have n53 := Ne.symm n35
  have n63 := Ne.symm n36
  have n54 := Ne.symm n45
  have n64 := Ne.symm n46
  have n65 := Ne.symm n56
  apply State.extensionality
  · simp only [productsSeed,run]
  · funext q
    by_cases qp : q=L.parity
    · subst q;simp_all [productsSeed,run,writeBit,Function.update]
    by_cases qa : q=L.lower
    · subst q;simp_all [productsSeed,run,writeBit,Function.update]
    by_cases qd : q=L.one
    · subst q;simp_all [productsSeed,run,writeBit,Function.update]
    by_cases qe : q=L.sign
    · subst q;simp_all [productsSeed,run,writeBit,Function.update]
    by_cases qr : q=L.r0
    · subst q;simp_all [productsSeed,run,writeBit,Function.update]
    simp_all [productsSeed,run,writeBit,Function.update]

theorem copyControl_spec (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires)
    (Jv Bv : Bool) (V : Nat) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=V) (hY : regValue L.y s.basis=0)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    let t := run (copyControl L J B) m s
    t.phase=s.phase ∧ regValue L.y t.basis=(Jv && Bv).toNat+2*(if Jv then V/2 else 0) ∧
    t.basis (lowY L)=(Jv && Bv) ∧ (∀q,q∉L.y → t.basis q=s.basis q) := by
  let U := Jv && Bv
  have yHead := y_cons L hw
  have y0 : lowY L∈L.y := by rw [yHead];simp
  have data := (List.nodup_append'.mp (allND L hn)).2.1
  have ry := (List.nodup_append'.mp data).1
  have yn := (List.nodup_append'.mp ry).2.1
  have rdy := (List.nodup_append'.mp ry).2.2
  have yAway : lowY L∉L.y.tail := by rw [yHead] at yn;exact (List.nodup_cons.mp yn).1
  have rAway (q : Wire) (hq : q∈L.r) : q≠lowY L :=
    fun e => List.disjoint_left.mp rdy hq (e.symm ▸ y0)
  have notY (q : Wire) (hq : q∉L.wires) : q∉L.y :=
    fun bad => hq (data_member L q (by simp [bad]))
  have jY := notY J hJ
  have bY := notY B hB
  have jy : J≠lowY L := fun e => jY (e.symm ▸ y0)
  have by0 : B≠lowY L := fun e => bY (e.symm ▸ y0)
  have z := (regValue_zero _ _).mp hY (lowY L) y0
  let a : State := ⟨s.phase,writeBit s.basis (lowY L) U⟩
  have first : run [.CCX J B (lowY L)] [] s=a := by simp [a,run,z,U,hj,hb]
  have aOther (q : Wire) (hq : q≠lowY L) : a.basis q=s.basis q := by simp [a,writeBit,hq]
  have aJ : a.basis J=Jv := (aOther J jy).trans hj
  have sameR : regValue L.r.tail a.basis=V/2 := by
    have same : regValue L.r.tail a.basis=regValue L.r.tail s.basis :=
      regValue_congr _ _ _ (fun q hq => aOther q (rAway q (List.mem_of_mem_tail hq)))
    rw [same]
    rw [r_cons L] at hR
    change (if s.basis L.r0 then 1 else 0)+2*regValue L.r.tail s.basis=V at hR
    cases er : s.basis L.r0 <;> simp only [er,Bool.false_eq_true,if_false,if_true] at hR <;> omega
  have cleanY : regValue L.y.tail a.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (aOther q (fun e => yAway (e ▸ hq))).trans
      ((regValue_zero _ _).mp hY q (List.mem_of_mem_tail hq))
  have lengths : L.r.tail.length=L.y.tail.length := by
    have len := BalancedCleanup.widths L.toLayout hw
    simp [len.2.1,len.2.2.1]
  have cp := copyRegister_correct (some J) L.r.tail L.y.tail lengths (copyND L hn)
    (by
      intro q hq
      have eq : J=q := by simpa using hq
      rw [←eq]
      exact fun h => jY (List.mem_of_mem_tail h)) a m
  have tail : regValue L.y.tail (run (copyRegister (some J) L.r.tail L.y.tail) m a).basis=
      if Jv then V/2 else 0 := by
    rw [cp.2.2,cleanY,sameR]
    simp [copyValue,aJ]
  have head : (run (copyRegister (some J) L.r.tail L.y.tail) m a).basis (lowY L)=U := by
    rw [cp.2.1 _ yAway]
    simp [a,writeBit]
  have actual : run (copyControl L J B) m s=run (copyRegister (some J) L.r.tail L.y.tail) m a := by
    rw [copyControl,run_append,show measurementCount [.CCX J B (lowY L)]=0 from rfl,
      List.take_zero,List.drop_zero,first]
  rw [actual]
  refine ⟨cp.1,?_,head,?_⟩
  · rw [yHead]
    change (if (run (copyRegister (some J) L.r.tail L.y.tail) m a).basis (lowY L) then 1 else 0)+
      2*regValue L.y.tail (run (copyRegister (some J) L.r.tail L.y.tail) m a).basis=_
    rw [head,tail]
    cases Jv <;> cases Bv <;> simp [U]
  · intro q hq
    exact (cp.2.1 q (fun h => hq (List.mem_of_mem_tail h))).trans
      (aOther q (fun e => hq (e.symm ▸ y0)))

structure Prepared (L : Layout) (J B : Wire) (Jv Bv : Bool) (Y : Int) (s t : State) : Prop where
  phase : t.phase=s.phase
  target : regValue L.r t.basis=if (Jv && Bv) then 2^256-1-encodeWord 256 (Y/2) else encodeWord 256 (Y/2)
  source : regValue L.y t.basis=(Jv && Bv).toNat+2*(if Jv then encodeWord 256 Y/2 else 0)
  parity : t.basis L.parity=originalParity Y
  a : t.basis L.lower=(originalParity Y && negative Y)
  d : t.basis L.one=(originalParity Y && (Jv && Bv))
  e : t.basis L.sign=((originalParity Y && negative Y) && (Jv && Bv))
  u : t.basis (lowY L)=(Jv && Bv)
  j : t.basis J=Jv
  b : t.basis B=Bv
  carry : ∀q∈L.carry,t.basis q=false
  outside : ∀q,q∉L.r++L.y++[L.parity,L.lower,L.one,L.sign] → t.basis q=s.basis q

set_option maxHeartbeats 300000 in
theorem prepare_spec (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    Prepared L J B Jv Bv Y s (run (prepare L J B) m s) := by
  let U := Jv && Bv
  let P := originalParity Y
  let H := negative Y
  let a := run (copyControl L J B) [] s
  let b := run (productsSeed L) [] a
  let c := run (rightShift L) [] b
  let d := run (signComplement (lowY L) L.r) [] c
  have len := BalancedCleanup.widths L.toLayout hw
  have data := (List.nodup_append'.mp (allND L hn)).2.1
  have ry := (List.nodup_append'.mp data).1
  have dis := (List.nodup_append'.mp ry).2.2
  have r0In : L.r0∈L.r := by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r++L.y++L.carry :=
    flagAway L hn q (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢;tauto)
  have fr (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r :=
    fun h => flag q hq (by simp [h])
  have fy (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.y :=
    fun h => flag q hq (by simp [h])
  have f0 (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q≠L.r0 :=
    fun e => fr q hq (e.symm ▸ r0In)
  have nr (q : Wire) (hq : q∉L.wires) : q∉L.r := fun h => hq (data_member L q (by simp [h]))
  have ny (q : Wire) (hq : q∉L.wires) : q∉L.y := fun h => hq (data_member L q (by simp [h]))
  have cp := copyControl_spec L hw hn J B hJ hB Jv Bv (encodeWord 256 Y) s [] hR hY hj hb
  change a.phase=s.phase ∧ _ at cp
  have R1 : regValue L.r a.basis=encodeWord 256 Y :=
    (regValue_congr _ _ _ (fun q hq => cp.2.2.2 q (fun h => List.disjoint_left.mp dis hq h))).trans hR
  have signed : signedRegValue L.r a.basis=Y := by
    unfold signedRegValue
    rw [len.2.1,R1]
    apply decode_encodeWord 256 (by decide)
    have h := constants
    unfold Centered at hy
    norm_num only [Nat.reduceSub] at ⊢
    omega
  have p1 : a.basis L.r0=P := word_parity L.r0 (L.rtail++[L.rmsb]) a.basis Y signed
  have h1 : a.basis L.rmsb=H := word_sign L.low L.rmsb a.basis Y signed
  have z (q : Wire) (hq : q∈[L.parity,L.lower,L.one]) : a.basis q=false := by
    have mem : q∈[L.parity,L.lower,L.one,L.sign] := by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢;tauto
    have hwork : q∈work L := by
      simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
      tauto
    exact (cp.2.2.2 q (fy q mem)).trans (hc q hwork)
  have e0 : a.basis L.sign=false := (cp.2.2.2 _ (fy _ (by simp))).trans hz
  have seed := productsSeed_run L hw hn P H U a [] p1 h1 cp.2.2.1
    (z _ (by simp)) (z _ (by simp)) (z _ (by simp)) e0
  change b=⟨a.phase,_⟩ at seed
  have nd : [L.parity,L.lower,L.one,L.sign].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨n01,n02,n03⟩,⟨n12,n13⟩,n23⟩
  have n10 := Ne.symm n01
  have n20 := Ne.symm n02
  have n30 := Ne.symm n03
  have n21 := Ne.symm n12
  have n31 := Ne.symm n13
  have n32 := Ne.symm n23
  have bP : b.basis L.parity=P := by rw [seed];simp [writeBit,Function.update,n01,n02,n03,f0 L.parity (by simp)]
  have bA : b.basis L.lower=(P && H) := by rw [seed];simp [writeBit,Function.update,n12,n13,f0 L.lower (by simp)]
  have bD : b.basis L.one=(P && U) := by rw [seed];simp [writeBit,Function.update,n23,f0 L.one (by simp)]
  have bE : b.basis L.sign=((P && H) && U) := by rw [seed];simp [writeBit,Function.update,f0 L.sign (by simp)]
  have bZero : b.basis L.r0=false := by rw [seed];simp [writeBit]
  have seedOff (q : Wire) (hq : q∉[L.parity,L.lower,L.one,L.sign]) (h0 : q≠L.r0) : b.basis q=a.basis q := by
    simp only [List.mem_cons,List.mem_singleton,not_or] at hq
    rw [seed]
    simp [writeBit,hq.1,hq.2.1,hq.2.2.1,hq.2.2.2,h0]
  have tailValue : regValue L.r.tail b.basis=encodeWord 255 (Y/2) := by
    have same : regValue L.r.tail b.basis=regValue L.r.tail a.basis := by
      apply regValue_congr
      intro q hq
      have inR := List.mem_of_mem_tail hq
      apply seedOff q
      · intro h;exact fr q h inR
      · intro e;have nd := EntryHalf5.target_nodup L hn;rw [r_cons L] at nd
        exact (List.nodup_cons.mp nd).1 (e ▸ hq)
    rw [same]
    have enc := half_encoding Y hy
    rw [r_cons L] at R1
    change (if a.basis L.r0 then 1 else 0)+2*regValue L.r.tail a.basis=encodeWord 256 Y at R1
    rw [p1] at R1
    change encodeWord 256 Y=P.toNat+2*encodeWord 255 (Y/2) at enc
    cases pv : P <;> simp only [pv,Bool.false_eq_true,if_false,if_true,Bool.toNat_false,Bool.toNat_true] at R1 enc <;> omega
  have r2 : regValue L.r b.basis=2*encodeWord 255 (Y/2) := by
    rw [r_cons L]
    change (if b.basis L.r0 then 1 else 0)+2*regValue L.r.tail b.basis=_
    rw [bZero,tailValue];simp
  have rs := rightShift_spec L hw hn Y hy b [] r2
  change c.phase=b.phase ∧ _ at rs
  have comp := signComplement_correct (lowY L) L.r (EntryHalf5.target_nodup L hn)
    (by intro h;have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
        exact List.disjoint_left.mp dis h y0) c []
  have after (q : Wire) (hq : q∉L.r) : d.basis q=b.basis q :=
    (comp.2.1 q hq).trans (rs.2.2 q hq)
  have inY (q : Wire) (hq : q∈L.y) : b.basis q=a.basis q := by
    apply seedOff q
    · intro h;exact fy q h hq
    · intro e;exact List.disjoint_left.mp dis (e.symm ▸ r0In) hq
  have uIn : lowY L∈L.y := by rw [y_cons L hw];simp
  have uNotR : lowY L∉L.r := fun h => List.disjoint_left.mp dis h uIn
  have bU : b.basis (lowY L)=U := (inY _ uIn).trans cp.2.2.1
  have cU : c.basis (lowY L)=U := (rs.2.2 _ uNotR).trans bU
  have outside (q : Wire) (hq : q∉L.r++L.y++[L.parity,L.lower,L.one,L.sign]) : d.basis q=s.basis q := by
    simp only [List.mem_append,not_or] at hq
    exact (after q hq.1.1).trans ((seedOff q hq.2 (fun e => hq.1.1 (e.symm ▸ r0In))).trans (cp.2.2.2 q hq.1.2))
  have actual : run (prepare L J B) m s=d := by
    rw [←run_take (prepare L J B) m s,(prepare_counts L hw J B).2,List.take_zero,prepare_shape]
    simp only [run_append]
    have cc : measurementCount (copyControl L J B)=0 := by
      have c := copyRegister_counts (some J) L.r.tail L.y.tail (by simp [len.2.1,len.2.2.1])
      simp [copyControl,measurementCount_append,measurementCount,c.2]
    have ps : measurementCount (productsSeed L)=0 := rfl
    have rr : measurementCount (rightShift L)=0 := by simp [rightShift,measurementCount_append,(rotate_counts _).2.1,measurementCount]
    simp only [measurementCount_append,cc,ps,rr,Nat.zero_add,List.take_zero,List.drop_zero]
    rfl
  rw [actual]
  refine ⟨comp.1.trans (rs.1.trans ((congrArg State.phase seed).trans cp.1)),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,outside⟩
  · rw [comp.2.2,cU,rs.2.1,len.2.1]
  · exact (regValue_congr _ _ _ (fun q hq => (after q (fun r => List.disjoint_left.mp dis r hq)).trans (inY q hq))).trans cp.2.1
  · exact (after _ (fr _ (by simp))).trans bP
  · exact (after _ (fr _ (by simp))).trans bA
  · exact (after _ (fr _ (by simp))).trans bD
  · exact (after _ (fr _ (by simp))).trans bE
  · exact (after _ uNotR).trans bU
  · apply (outside J _).trans hj
    simp only [List.mem_append,not_or]
    refine ⟨⟨nr J hJ,ny J hJ⟩,?_⟩
    intro h
    apply hJ
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> simp [Layout.wires,BalancedCleanup.Layout.wires]
  · apply (outside B _).trans hb
    simp only [List.mem_append,not_or]
    refine ⟨⟨nr B hB,ny B hB⟩,?_⟩
    intro h
    apply hB
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> simp [Layout.wires,BalancedCleanup.Layout.wires]
  · intro q hq
    have nd := List.nodup_append'.mp data
    have qr : q∉L.r++L.y := fun h => List.disjoint_left.mp nd.2.2 h hq
    have qf : q∉[L.parity,L.lower,L.one,L.sign] := fun h => flag q h (by simp [hq])
    exact (outside q (fun h => (List.mem_append.mp h).elim qr qf)).trans (hc q (by simp [work,hq]))

set_option maxHeartbeats 200000 in
theorem prefix_spec (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    PrefixResult L J B Jv Bv Y s (run (prefixProgram L J B) m s) := by
  let a := run (prepare L J B) [] s
  let t := run (arithmetic L) m a
  have prep := prepare_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  change Prepared L J B Jv Bv Y s a at prep
  have len := BalancedCleanup.widths L.toLayout hw
  have add := Affine.add_correct (sources L) L.r (L.carry.take 255) (lowY L)
    (arithmeticND L hw hn) (sources_away L hw hn)
    (by rw [sources_length,len.2.1]) (by simp [List.length_take,hw.2.2,len.2.1]) a m
    (fun q hq => prep.carry q (List.mem_of_mem_take hq)) (sources_valid L hn)
  change t.phase=a.phase ∧ (∀q,q∉L.r → t.basis q=a.basis q) ∧
    regValue L.r t.basis=(Affine.value (sources L) a.basis+regValue L.r a.basis+(a.basis (lowY L)).toNat)%2^L.r.length at add
  have sourceValue := sources_value L (originalParity Y) (negative Y) (Jv && Bv) a.basis
    prep.parity prep.a prep.d prep.e
  have result : regValue L.r t.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) := by
    rw [add.2.2,sourceValue,prep.target,prep.u,len.2.1]
    exact folded_encoding (Jv && Bv) Y hy
  have data := (List.nodup_append'.mp (allND L hn)).2.1
  have dis := (List.nodup_append'.mp (List.nodup_append'.mp data).1).2.2
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r := by
    intro h
    have member : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> simp
    exact flagAway L hn q member (by simp [h])
  have control (q : Wire) (hq : q∉L.wires) : q∉L.r :=
    fun h => hq (data_member L q (by simp [h]))
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have actual : run (prefixProgram L J B) m s=t := by
    rw [prefixProgram,run_append,(prepare_counts L hw J B).2,List.take_zero,List.drop_zero]
  rw [actual]
  refine ⟨add.1.trans prep.phase,result,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => add.2.1 q (fun h => List.disjoint_left.mp dis h hq))).trans prep.source
  · exact (add.2.1 _ (flag _ (by simp))).trans prep.parity
  · exact (add.2.1 _ (flag _ (by simp))).trans prep.a
  · exact (add.2.1 _ (flag _ (by simp))).trans prep.d
  · exact (add.2.1 _ (flag _ (by simp))).trans prep.e
  · exact (add.2.1 _ (fun h => List.disjoint_left.mp dis h y0)).trans prep.u
  · exact (add.2.1 _ (control _ hJ)).trans prep.j
  · exact (add.2.1 _ (control _ hB)).trans prep.b
  · intro q hq
    have apart : q∉L.r := fun h => List.disjoint_left.mp (List.nodup_append'.mp data).2.2 (List.mem_append_left _ h) hq
    exact (add.2.1 q apart).trans (prep.carry q hq)
  · intro q hq
    have apart : q∉L.r := by simp only [List.mem_append,not_or] at hq;exact hq.1.1
    exact (add.2.1 q apart).trans (prep.outside q hq)

end ECDSAAdd.Entrant.EntryRetained5
