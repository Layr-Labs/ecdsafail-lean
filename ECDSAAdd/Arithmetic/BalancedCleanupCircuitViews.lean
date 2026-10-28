import ECDSAAdd.Arithmetic.BalancedCleanupCircuitProgram
import ECDSAAdd.Arithmetic.SignedWordBits

set_option maxHeartbeats 600000
set_option maxRecDepth 4096
namespace ECDSAAdd.Arithmetic.BalancedCleanup
open BalancedField

 theorem complement_encoded (z : Int) : 2^256-1-encodeWord 256 z=encodeWord 256 (-z-1) := by
  have a := encodeWord_cast 256 z
  have b := encodeWord_cast 256 (-z-1)
  have ha := encodeWord_bound 256 z
  have hb := encodeWord_bound 256 (-z-1)
  norm_num only [Nat.reducePow] at a b ha hb ⊢
  omega

 theorem doubled_encoded (z : Int) (b : Bool) :
    encodeWord 256 (2*z+(b.toNat : Int))=2*encodeWord 255 z+b.toNat := by
  have a := encodeWord_cast 255 z
  have c := encodeWord_cast 256 (2*z+(b.toNat : Int))
  have ha := encodeWord_bound 255 z
  have hc := encodeWord_bound 256 (2*z+(b.toNat : Int))
  cases b <;> norm_num only [Bool.toNat_false,Bool.toNat_true,Nat.reducePow] at a c ha hc ⊢ <;> omega

 theorem encoded_nonnegative (n : Nat) (z : Int) (h0 : 0≤z)
    (h1 : z<((2^n : Nat) : Int)) : encodeWord n z=z.toNat := by
  unfold encodeWord
  rw [Int.emod_eq_of_lt h0 h1]

 theorem magnitude_encoded (R : Int) (hr : Centered R) :
    (if negative R then 2^256-1-encodeWord 256 R else encodeWord 256 R)=(magnitude R).toNat := by
  have hp := constants
  have hb := magnitude_bounds R hr
  have hr0 := hr
  unfold Centered at hr0
  by_cases hneg : R<0
  · simp only [magnitude,negative,hneg,decide_true,if_true]
    rw [complement_encoded]
    exact encoded_nonnegative _ _ (by omega) (by norm_num; omega)
  · simp only [magnitude,negative,hneg,decide_false]
    exact encoded_nonnegative _ _ (by omega) (by norm_num; omega)

 theorem result_msb (L : Layout) (hw : L.Widths) (R : Int) (hr : Centered R)
    (s : BasisState) (hs : regValue L.r s=encodeWord 256 R) : s L.rmsb=negative R := by
  have w := widths L hw
  have bit := regValue_highBit L.low L.rmsb s
  have sign := centerWord_sign (R : ECDSAAdd.Fp)
  simp only [centerWord,centerFp_of_center R hr] at sign
  rw [w.1] at bit
  change s L.rmsb=true ↔ 2^255≤regValue L.r s at bit
  rw [hs] at bit
  cases hb : s L.rmsb <;> by_cases hn : R<0 <;> simp [negative,hn] <;>
    simp [hb] at bit <;> omega

 theorem negativeLiteral_value : negativeLiteral=2^255-h.toNat := by
  have hp := constants
  have hi : (-h)%((2^255 : Nat) : Int)=((2^255 : Nat) : Int)-h := by
    have he : (((2^255 : Nat) : Int)-h)%((2^255 : Nat) : Int)=(-h)%((2^255 : Nat) : Int) := by
      rw [show ((2^255 : Nat) : Int)-h=(-h)+((2^255 : Nat) : Int) by ring]
      simp
    rw [Int.emod_eq_of_lt (by norm_num; omega) (by norm_num; omega)] at he
    exact he.symm
  have hc := encodeWord_cast 255 (-h)
  have ht := Int.toNat_of_nonneg (show 0≤h by omega)
  have hb : h.toNat≤2^255 := by norm_num at ⊢; omega
  unfold negativeLiteral
  rw [hi] at hc
  omega

 theorem prepareSign_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hs : regValue L.r s.basis=encodeWord 256 R) (hz : s.basis L.lower=false) :
    let t := run (prepareSign L) m s
    regValue L.r t.basis=(magnitude R).toNat ∧ t.basis L.lower=negative R ∧
    (∀ q,q∉L.r → q≠L.lower → t.basis q=s.basis q) := by
  let c : State := ⟨s.phase,writeBit s.basis L.lower (s.basis L.lower ^^ s.basis L.rmsb)⟩
  have la : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have nd := (List.nodup_append'.mp (L.dataND hn)).1
  have before : regValue L.r c.basis=regValue L.r s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [c,writeBit,show q≠L.lower from fun he => la (he ▸ hq)])
  have lc : c.basis L.lower=negative R := by simp [c,writeBit,hz,result_msb L hw R hr s.basis hs]
  have body := signComplement_correct L.lower L.r nd la c m
  have w := widths L hw
  have hc : ∀ ms,run [.CX L.rmsb L.lower] ms s=c := by intro ms; rfl
  simp only [prepareSign,run_append,measurementCount,List.take_zero,List.drop_zero,hc]
  change regValue L.r (run (signComplement L.lower L.r) m c).basis=_ ∧ _
  refine ⟨?_,(body.2.1 L.lower la).trans lc,?_⟩
  · rw [body.2.2,before,hs,lc,w.2.1,magnitude_encoded R hr]
  · intro q hq hne
    exact (body.2.1 q hq).trans (by simp [c,writeBit,hne])

 theorem normalize_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hv : regValue L.low s.basis=(magnitude R).toNat)
    (hl : s.basis L.lower=negative R) (ho : s.basis L.one=false)
    (hc : ∀ q∈L.carry,s.basis q=false) :
    let t := run (normalize L) m s
    t.phase=s.phase ∧ regValue L.low t.basis=encodeWord 255 (normalizedR R) ∧
    ∀ q,q∉L.low → t.basis q=s.basis q := by
  have w := widths L hw
  have hAdd := literalConstAdd_correct L.low (L.carry.take 254) L.lower L.one negativeLiteral
    (L.normND hn) (by omega) s m ho (fun q hq => hc q (List.mem_of_mem_take hq))
  refine ⟨hAdd.1,?_,hAdd.2.1⟩
  rw [normalize,hAdd.2.2,hv,hl,negativeLiteral_value,w.1]
  have ar := normalizedR_lowword_arithmetic R hr
  have hp := constants
  have ht := Int.toNat_of_nonneg (show 0≤h by omega)
  have hb : h.toNat≤2^255 := by norm_num at ⊢; omega
  rw [ar.2]
  have he : (magnitude R).toNat+(2^255-h.toNat)+(negative R).toNat=
      (magnitude R).toNat+2^255-h.toNat+(negative R).toNat := by omega
  rw [he]

 theorem bias_value (lo : List Wire) (msb : Wire) (nd : (lo++[msb]).Nodup)
    (s : State) (m : List Bool) :
    (regValue (lo++[msb]) (run [.X msb] m s).basis : Int)=
      signedDecode (lo.length+1) (regValue (lo++[msb]) s.basis)+((2^lo.length : Nat) : Int) := by
  have away : msb∉lo := by
    have dis := (List.nodup_append'.mp nd).2.2
    exact fun hm => List.disjoint_left.mp dis hm (by simp)
  have high := signedRegValue_msb lo msb s.basis
  have keep : regValue lo (writeBit s.basis msb (!s.basis msb))=regValue lo s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [writeBit,show q≠msb from fun he => away (he ▸ hq)])
  simp only [signedRegValue,List.length_append,List.length_singleton] at high
  rw [regValue_append] at ⊢
  change ((regValue lo (writeBit s.basis msb (!s.basis msb))+
    2^lo.length*regValue [msb] (writeBit s.basis msb (!s.basis msb)) : Nat) : Int)=_
  rw [keep]
  have hv := regValue_append lo [msb] s.basis
  have sv : regValue [msb] (writeBit s.basis msb (!s.basis msb))=(!s.basis msb).toNat := by
    simp only [regValue,List.foldr_cons,List.foldr_nil,writeBit,Function.update_self]
    cases !s.basis msb <;> rfl
  have oldsv : regValue [msb] s.basis=(s.basis msb).toNat := by
    change (if s.basis msb then 1 else 0)=(s.basis msb).toNat
    cases s.basis msb <;> rfl
  rw [sv]
  rw [oldsv] at hv
  have hp : ((2^(lo.length+1) : Nat) : Int)=2*((2^lo.length : Nat) : Int) := by rw [pow_succ]; push_cast; ring
  rw [hp] at high
  have hvI : (regValue (lo++[msb]) s.basis : Int)=
      (regValue lo s.basis : Int)+((2^lo.length : Nat) : Int)*((s.basis msb).toNat : Int) := by exact_mod_cast hv
  simp only [Nat.cast_add,Nat.cast_mul] at ⊢
  cases hb : s.basis msb <;> simp only [hb,Bool.not_false,Bool.not_true,
    Bool.toNat_false,Bool.toNat_true,Bool.false_eq_true,if_false,if_true,
    Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,add_zero,sub_zero] at high hvI ⊢ <;> omega

 theorem prepareCompare_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 255 (normalizedR R))
    (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hL : s.basis L.lower=negative R) :
    let t := run (prepareCompare L) m s
    (regValue L.r t.basis : Int)=comparisonLeft B R+((2^255 : Nat) : Int) ∧
    (regValue L.y t.basis : Int)=viewedY B R Y+((2^255 : Nat) : Int) ∧
    (∀ q,q∉L.r → q∉L.y → t.basis q=s.basis q) := by
  let U := encodeWord 255 (normalizedR R)
  let v1 := run (rotateLeft L.r) m s
  let ins : Program := [.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0]
  let v2 := run ins m v1
  let v3 := run (signComplement L.sign L.y) m v2
  let v4 := run (signComplement L.lower L.y) m v3
  let v5 := run [.X L.rmsb] m v4
  let v6 := run [.X L.ymsb] m v5
  have w := widths L hw
  have d := List.nodup_append'.mp (L.dataND hn)
  have dr := d.1
  have dy := (List.nodup_append'.mp d.2.1).1
  have dis := d.2.2
  have away (q : Wire) (hq : q∈[L.sign,L.lower]) : q∉L.r ∧ q∉L.y := by
    have a := L.flagAway hn q (by simp only [List.mem_cons] at hq ⊢; tauto)
    exact ⟨fun h => a (by simp [h]),fun h => a (by simp [h])⟩
  have r0R : L.r0∈L.r := by simp [Layout.r,Layout.low]
  have rmR : L.rmsb∈L.r := by simp [Layout.r]
  have ymY : L.ymsb∈L.y := by simp [Layout.y]
  have r0Y : L.r0∉L.y := fun h => List.disjoint_left.mp dis r0R (by simp [h])
  have rmY : L.rmsb∉L.y := fun h => List.disjoint_left.mp dis rmR (by simp [h])
  have ymR : L.ymsb∉L.r := fun h => List.disjoint_left.mp dis h (by simp [ymY])
  have sr : L.sign≠L.r0 := fun e => (away _ (by simp)).1 (e ▸ r0R)
  have lr : L.lower≠L.r0 := fun e => (away _ (by simp)).1 (e ▸ r0R)
  have rot0 := rotateLeft_spec L.r dr U (by have hu := encodeWord_bound 255 (normalizedR R); rw [w.2.1]; norm_num at ⊢; omega) s m hR
  have rot := rot0.2
  have rotfr := (rotate_frame L.r s m).2.2.2
  have S1 : v1.basis L.sign=B := (rotfr _ (away _ (by simp)).1).trans hS
  have L1 : v1.basis L.lower=negative R := (rotfr _ (away _ (by simp)).1).trans hL
  have low0 : v1.basis L.r0=false := by
    change regValue (L.r0::(L.rtail++[L.rmsb])) v1.basis=2*U at rot
    change (if v1.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v1.basis=2*U at rot
    cases e : v1.basis L.r0
    · rfl
    · simp [e] at rot
      omega
  have tail1 : regValue (L.rtail++[L.rmsb]) v1.basis=U := by
    change (if v1.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v1.basis=2*U at rot
    rw [low0] at rot; simp only [Bool.false_eq_true,if_false,zero_add] at rot; omega
  have I2 : v2.basis L.r0=!(B ^^ negative R) := by
    cases b : B <;> cases l : negative R <;> simp [v2,ins,run,writeBit,sr,lr,S1,L1,low0,b,l]
  have out2 (q : Wire) (hq : q≠L.r0) : v2.basis q=v1.basis q := by simp [v2,ins,run,writeBit,hq]
  have S2 : v2.basis L.sign=B := (out2 _ sr).trans S1
  have L2 : v2.basis L.lower=negative R := (out2 _ lr).trans L1
  have tailAway : L.r0∉L.rtail++[L.rmsb] := (List.nodup_cons.mp dr).1
  have R2 : regValue L.r v2.basis=encodeWord 256 (comparisonLeft B R) := by
    change (if v2.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v2.basis=_
    rw [regValue_congr _ _ _ (fun q hq => out2 q (fun e => tailAway (e ▸ hq))),tail1,I2]
    have ib : insertBit B R=((!(B ^^ negative R)).toNat : Int) := by
      cases e : !(B ^^ negative R) <;> simp [insertBit,e]
    rw [comparisonLeft,ib,doubled_encoded]
    cases e : !(B ^^ negative R) <;> simp [U,Bool.toNat,Nat.add_comm]
  have Y2 : regValue L.y v2.basis=encodeWord 256 Y := by
    exact (regValue_congr _ _ _ (fun q hq => (out2 q (fun e => r0Y (e ▸ hq))).trans
      (rotfr q (fun hrq => List.disjoint_left.mp dis hrq (by simp [hq]))))).trans hY
  have cS := signComplement_correct L.sign L.y dy (away _ (by simp)).2 v2 m
  have cL := signComplement_correct L.lower L.y dy (away _ (by simp)).2 v3 m
  have L3 : v3.basis L.lower=negative R := (cS.2.1 _ (away _ (by simp)).2).trans L2
  have R4 : regValue L.r v4.basis=encodeWord 256 (comparisonLeft B R) := by
    exact (regValue_congr _ _ _ (fun q hq => (cL.2.1 q
      (fun hyq => List.disjoint_left.mp dis hq (by simp [hyq]))).trans (cS.2.1 q
      (fun hyq => List.disjoint_left.mp dis hq (by simp [hyq]))))).trans R2
  have Y4 : regValue L.y v4.basis=encodeWord 256 (viewedY B R Y) := by
    rw [cL.2.2,cS.2.2,L3,S2,Y2,w.2.2.1]
    have hb := encodeWord_bound 256 Y
    have comp := complement_encoded Y
    cases B <;> cases l : negative R <;> simp [viewedY,l] <;> omega
  have decoded := comparison_words_decode B R Y hr hy
  have bvR := bias_value L.low L.rmsb dr v4 m
  have bvY := bias_value L.ylow L.ymsb dy v5 m
  have Y5 : regValue L.y v5.basis=regValue L.y v4.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [v5,run,writeBit,show q≠L.rmsb from fun e => rmY (e ▸ hq)])
  have R6 : regValue L.r v6.basis=regValue L.r v5.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [v6,run,writeBit,show q≠L.ymsb from fun e => ymR (e ▸ hq)])
  rw [w.1] at bvR
  change (regValue L.r v5.basis : Int)=signedDecode 256 (regValue L.r v4.basis)+((2^255 : Nat) : Int) at bvR
  rw [R4,decoded.1] at bvR
  rw [hw.2.1] at bvY
  change (regValue L.y v6.basis : Int)=signedDecode 256 (regValue L.y v5.basis)+((2^255 : Nat) : Int) at bvY
  rw [Y5,Y4,decoded.2] at bvY
  have emptyRot (t : State) : run (rotateLeft L.r) (m.take 0) t=run (rotateLeft L.r) m t := by
    simpa only [(rotate_counts L.r).2.2.2] using run_take (rotateLeft L.r) m t
  have emptyS (t : State) : run (signComplement L.sign L.y) (m.take 0) t=run (signComplement L.sign L.y) m t := by
    simpa only [(signComplement_counts L.sign L.y).2] using run_take (signComplement L.sign L.y) m t
  have emptyL (t : State) : run (signComplement L.lower L.y) (m.take 0) t=run (signComplement L.lower L.y) m t := by
    simpa only [(signComplement_counts L.lower L.y).2] using run_take (signComplement L.lower L.y) m t
  have execute : run (prepareCompare L) m s=v6 := by
    simp only [prepareCompare,List.append_assoc,run_append,
      (rotate_counts L.r).2.2.2,(signComplement_counts L.sign L.y).2,
      (signComplement_counts L.lower L.y).2,measurementCount,List.drop_zero,emptyRot,emptyS,emptyL]
    rfl
  rw [execute]
  refine ⟨by rw [R6]; exact bvR,bvY,?_⟩
  intro q qr qy
  have nr : q≠L.r0 := fun e => qr (e ▸ r0R)
  have nm : q≠L.rmsb := fun e => qr (e ▸ rmR)
  have ny : q≠L.ymsb := fun e => qy (e ▸ ymY)
  have v56 : v6.basis q=v4.basis q := by simp [v6,v5,run,writeBit,nm,ny]
  exact v56.trans ((cL.2.1 q qy).trans ((cS.2.1 q qy).trans ((out2 q nr).trans (rotfr q qr))))

end ECDSAAdd.Arithmetic.BalancedCleanup

#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.complement_encoded
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.doubled_encoded
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.encoded_nonnegative
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.magnitude_encoded
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.result_msb
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.negativeLiteral_value
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.prepareSign_value
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.normalize_value
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.bias_value
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.prepareCompare_value
