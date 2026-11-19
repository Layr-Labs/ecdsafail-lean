import ECDSAAdd.Submission.Entrant.PrizeHighBankJoin5ab3264
import ECDSAAdd.Submission.Entrant.PrizeLeave225Join2ee362a
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickEraseActual16ba

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion
open Arithmetic

theorem thresholdBit (x h : Nat) (positive:0<h) :
    (x/h).testBit 0=decide (h≤x%(2*h)) := by
  have d : (x%(2*h))/h=(x/h)%2 := by
    rw [Nat.mul_comm 2 h,Nat.mod_mul_right_div_self]
  have limited := Nat.mod_lt (x/h) (by decide : 0<2)
  have one : ((x/h)%2=1) ↔ h≤x%(2*h) := by
    rw [←d]
    have iff : 1≤(x%(2*h))/h ↔ 1*h≤x%(2*h) := Nat.le_div_iff_mul_le positive
    simp only [one_mul] at iff
    omega
  simp [Nat.testBit_eq_decide_div_mod_eq,one]

theorem borrowBit (half u v sign : Nat) (pos:0<half) :
    (((u-sign)/half).testBit 0 && !((u+v)/half).testBit 0).toNat =
      upperBorrow half u v sign := by
  rw [thresholdBit _ _ pos,thresholdBit _ _ pos]
  unfold upperBorrow
  split_ifs with h <;> simp_all

end ECDSAAdd.Entrant.StairPacket.LeaveCompanion


end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic
theorem signedWords (L:SkywalkIntegerLayout) (g sg:Bool) (u v:Nat) (s:BasisState)
    (a:signedRegValue L.a s=(SkywalkRails.encode g sg u v).a)
    (b:signedRegValue L.b s=(SkywalkRails.encode g sg u v).b) (g0:s L.previous=g) :
    let e:=negative sg u
    s L.previous=g ∧ (s L.aSign ^^ s L.bSign)=e ∧
    regValue (wordPos L g) s=u+v ∧
    regValue (wordSigned L g) (fun q=>s q ^^ e)=u-e.toNat := by
  have orient (lo:List Wire) (sign:Wire) (signed:signedRegValue (lo++[sign]) s=SkywalkRails.signed sg u) :
      s sign=negative sg u ∧ regValue (lo++[sign]) (fun q=>s q ^^ negative sg u)=u-(negative sg u).toNat := by
    have h:=full lo sign s _ signed
    have n:SkywalkRails.neg (SkywalkRails.signed sg u)=negative sg u := by
      cases sg <;> simp [SkywalkRails.neg,SkywalkRails.signed,negative]
    have r:s sign=negative sg u:=h.1.trans n
    rw [r] at h
    have mag:(SkywalkRails.signed sg u).natAbs=u:=by cases sg <;> simp [SkywalkRails.signed]
    exact ⟨r,by simpa only [mag] using h.2⟩
  cases g with
  | false =>
    change signedRegValue ((L.a0::L.aMid)++[L.aSign]) s=(u:Int)+v at a
    change signedRegValue ((L.b0::L.bMid)++[L.bSign]) s=SkywalkRails.signed sg u at b
    obtain ⟨p0,pv⟩:=positive _ _ s (u+v) (by simpa only [Nat.cast_add] using a)
    obtain ⟨s0,sv⟩:=orient _ _ b
    exact ⟨g0,by rw [p0,s0,Bool.false_xor],pv,sv⟩
  | true =>
    change signedRegValue ((L.a0::L.aMid)++[L.aSign]) s=SkywalkRails.signed sg u at a
    change signedRegValue ((L.b0::L.bMid)++[L.bSign]) s=(u:Int)+v at b
    obtain ⟨p0,pv⟩:=positive _ _ s (u+v) (by simpa only [Nat.cast_add] using b)
    obtain ⟨s0,sv⟩:=orient _ _ a
    exact ⟨g0,by rw [s0,p0,Bool.xor_false],pv,sv⟩


/-- Read the positive and signed magnitude limbs from the actual routed short
    registers at tick fifteen. The two future extension wires are no longer needed. -/
theorem scanRouted (j : Fin 23) (k a b g n : Nat) (ps : List (Wire×Wire))
    (loc : RailPair.ScanGeometry a b g n ps)
    (left : ps.map Prod.fst = ((IntegerPacket.ports (shape j) 15).a.drop k).map (windowNet j))
    (right : ps.map Prod.snd = ((IntegerPacket.ports (shape j) 15).b.drop k).map (windowNet j))
    (aTop : a=windowNet j (IntegerPacket.ports (shape j) 15).aSign)
    (bTop : b=windowNet j (IntegerPacket.ports (shape j) 15).bSign)
    (prev : g=windowNet j (IntegerPacket.ports (shape j) 15).previous)
    (s : State) (m : List Bool) (u v : Nat) (G S : Bool)
    (h : onRails j 15 (SkywalkRails.encode G S u v) s.basis) (fresh:s.basis n=false)
    (la : k≤(IntegerPacket.ports (shape j) 15).a.length) (lb : k≤(IntegerPacket.ports (shape j) 15).b.length) :
    let t:=run (RailPair.scan a b g n ps) m s
    let e:=negative S u
    t.basis n=e ∧ regValue (ps.map Prod.fst) t.basis=(u+v)/2^k ∧
      regValue (ps.map Prod.snd) t.basis=(u-e.toNat)/2^k := by
  let L:=IntegerPacket.ports (shape j) 15
  let e:=negative S u
  have gh : mappedBasis j s.basis L.previous=G := by
    have eq := h.2.2.1
    cases G <;> exact eq
  have math := signedWords L G S u v (mappedBasis j s.basis) h.1 h.2.1 gh
  have gg:s.basis g=G := prev ▸ gh
  have ss:(s.basis a ^^ s.basis b)=e := by rw [aTop,bTop];exact math.2.1
  have act:=RailPair.scan_run _ _ _ _ _ loc s m fresh
  have vals:=scan_values _ _ _ _ _ loc s m fresh
  dsimp only at vals ⊢
  refine ⟨act.2.1.trans ss,?_⟩
  rw [gg,ss] at vals
  rw [left,right] at vals ⊢
  simp only [unroute,shiftedValue,la,lb] at vals ⊢
  obtain ⟨pos,mag⟩:=math.2.2
  cases G <;> simp only [wordPos,wordSigned,ite_true,Bool.false_eq_true,ite_false] at pos mag vals
  all_goals
    exact ⟨vals.1.trans (congrArg (· /2^k) pos),vals.2.trans (congrArg (· /2^k) mag)⟩

end ECDSAAdd.Entrant.StairPacket.PortalValues


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225InputScan
open Partial Arithmetic RailPair PortalValues LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
def pairs : List (Wire×Wire) := [(400, 930), (401, 931), (402, 932), (403, 933), (404, 934), (405, 935), (406, 936), (407, 937), (408, 938), (409, 939), (410, 940), (411, 941), (412, 942), (413, 943), (414, 944), (415, 945), (416, 946), (417, 947), (418, 948)]
def scanPart := (leave225.take 78)
abbrev L := IntegerPacket.ports (shape 10) 15
theorem emitted : scanPart=scan 418 948 255 1723 pairs := by decide +kernel
theorem layout : ScanGeometry 418 948 255 1723 pairs := ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem result (s : State) (tape : List Bool) (u v : Nat) (G sg : Bool)
    (ready : onRails 10 15 (SkywalkRails.encode G sg u v) s.basis) (fresh:s.basis 1723=false) :
    let t:=run scanPart tape s
    let e:=negative sg u
    t.phase=s.phase ∧ t.basis 1723=e ∧
      (∀i<19,t.basis (400+i)=((u+v)/2^144).testBit i ∧ t.basis (930+i)=((u-e.toNat)/2^144).testBit i) ∧
      ∀q,q≠1723 → q∉sites pairs → t.basis q=s.basis q := by
  rw [emitted]
  have out:=scanRouted 10 144 418 948 255 1723 pairs layout (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) s tape u v G sg ready fresh (by decide +kernel) (by decide +kernel)
  have frame:=scan_run _ _ _ _ _ layout s tape fresh
  refine ⟨frame.1,out.1,?_,frame.2.2.1⟩
  intro i hi
  have geom : ∀j:Fin 19,(pairs.map Prod.fst).getD j 0=400+j.val ∧ (pairs.map Prod.snd).getD j 0=930+j.val := by decide +kernel
  let ix:Fin 19:=⟨i,hi⟩
  rw [←(geom ix).1,←(geom ix).2,HighBankAdjust.bit_read (pairs.map Prod.fst) ix (run (scan 418 948 255 1723 pairs) tape s).basis hi,HighBankAdjust.bit_read (pairs.map Prod.snd) ix (run (scan 418 948 255 1723 pairs) tape s).basis hi,out.2.1,out.2.2]
  exact ⟨rfl,rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave225InputScan


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240InputScan
open Partial Arithmetic RailPair PortalValues LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
def pairs : List (Wire×Wire) := [(407, 922), (408, 923), (409, 924), (410, 925), (411, 926), (412, 927), (413, 928), (414, 929), (415, 930), (416, 931), (417, 932), (418, 933), (419, 934), (420, 935), (421, 936), (422, 937), (423, 938), (424, 939), (425, 940)]
def scanPart := (leave240.take 78)
abbrev L := IntegerPacket.ports (shape 11) 15
theorem emitted : scanPart=scan 425 940 270 1715 pairs := by decide +kernel
theorem layout : ScanGeometry 425 940 270 1715 pairs := ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem result (s : State) (tape : List Bool) (u v : Nat) (G sg : Bool)
    (ready : onRails 11 15 (SkywalkRails.encode G sg u v) s.basis) (fresh:s.basis 1715=false) :
    let t:=run scanPart tape s
    let e:=negative sg u
    t.phase=s.phase ∧ t.basis 1715=e ∧
      (∀i<19,t.basis (407+i)=((u+v)/2^136).testBit i ∧ t.basis (922+i)=((u-e.toNat)/2^136).testBit i) ∧
      ∀q,q≠1715 → q∉sites pairs → t.basis q=s.basis q := by
  rw [emitted]
  have out:=scanRouted 11 136 425 940 270 1715 pairs layout (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) s tape u v G sg ready fresh (by decide +kernel) (by decide +kernel)
  have frame:=scan_run _ _ _ _ _ layout s tape fresh
  refine ⟨frame.1,out.1,?_,frame.2.2.1⟩
  intro i hi
  have geom : ∀j:Fin 19,(pairs.map Prod.fst).getD j 0=407+j.val ∧ (pairs.map Prod.snd).getD j 0=922+j.val := by decide +kernel
  let ix:Fin 19:=⟨i,hi⟩
  rw [←(geom ix).1,←(geom ix).2,HighBankAdjust.bit_read (pairs.map Prod.fst) ix (run (scan 425 940 270 1715 pairs) tape s).basis hi,HighBankAdjust.bit_read (pairs.map Prod.snd) ix (run (scan 425 940 270 1715 pairs) tape s).basis hi,out.2.1,out.2.2]
  exact ⟨rfl,rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave240InputScan


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255InputScan
open Partial Arithmetic RailPair PortalValues LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
def pairs : List (Wire×Wire) := [(415, 915), (416, 916), (417, 917), (418, 918), (419, 919), (420, 920), (421, 921), (422, 922), (423, 923), (424, 924), (425, 925), (426, 926), (427, 927), (428, 928), (429, 929), (430, 930), (431, 931), (432, 932), (433, 933)]
def scanPart := (leave255.take 78)
abbrev L := IntegerPacket.ports (shape 12) 15
theorem emitted : scanPart=scan 433 933 285 1708 pairs := by decide +kernel
theorem layout : ScanGeometry 433 933 285 1708 pairs := ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem result (s : State) (tape : List Bool) (u v : Nat) (G sg : Bool)
    (ready : onRails 12 15 (SkywalkRails.encode G sg u v) s.basis) (fresh:s.basis 1708=false) :
    let t:=run scanPart tape s
    let e:=negative sg u
    t.phase=s.phase ∧ t.basis 1708=e ∧
      (∀i<19,t.basis (415+i)=((u+v)/2^129).testBit i ∧ t.basis (915+i)=((u-e.toNat)/2^129).testBit i) ∧
      ∀q,q≠1708 → q∉sites pairs → t.basis q=s.basis q := by
  rw [emitted]
  have out:=scanRouted 12 129 433 933 285 1708 pairs layout (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) s tape u v G sg ready fresh (by decide +kernel) (by decide +kernel)
  have frame:=scan_run _ _ _ _ _ layout s tape fresh
  refine ⟨frame.1,out.1,?_,frame.2.2.1⟩
  intro i hi
  have geom : ∀j:Fin 19,(pairs.map Prod.fst).getD j 0=415+j.val ∧ (pairs.map Prod.snd).getD j 0=915+j.val := by decide +kernel
  let ix:Fin 19:=⟨i,hi⟩
  rw [←(geom ix).1,←(geom ix).2,HighBankAdjust.bit_read (pairs.map Prod.fst) ix (run (scan 433 933 285 1708 pairs) tape s).basis hi,HighBankAdjust.bit_read (pairs.map Prod.snd) ix (run (scan 433 933 285 1708 pairs) tape s).basis hi,out.2.1,out.2.2]
  exact ⟨rfl,rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave255InputScan


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225CompanionInput
open Arithmetic PortalAnd LeaveCompanion LeaveCompanion225
set_option maxRecDepth 50000

theorem decode (s : State) (u v sign : Nat) (magFit : (u-sign)/2^144<2^19)
    (bits : ∀i<19,s.basis (400+i)=((u+v)/2^144).testBit i ∧ s.basis (930+i)=((u-sign)/2^144).testBit i) :
    ((digits 930 longPairs).any s.basis = decide (2^144≤u-sign)) ∧
      (s.basis 930 && !s.basis 400).toNat=upperBorrow (2^144) u v sign ∧
      regValue fullA s.basis=((u+v)/2^145)%2^18 ∧
      regValue fullM s.basis=((u-sign)/2^145)%2^18 := by
  have mag := EnterProof.value_of_bits (digits 930 longPairs) s.basis ((u-sign)/2^144) (by
    intro i hi
    have geom : ∀j:Fin 19,(digits 930 longPairs).getD j 0=930+j.val := by decide +kernel
    rw [geom ⟨i,hi⟩]
    exact (bits i hi).2)
  rw [show (digits 930 longPairs).length=19 from rfl,Nat.mod_eq_of_lt magFit] at mag
  refine ⟨?_,?_,?_,?_⟩
  · rw [any_positive,mag]
    simp only [Nat.div_pos_iff,show 0<2^144 by decide,true_and]
  · have bs := bits 0 (by decide)
    simpa only [Nat.add_zero,bs.1,bs.2] using borrowBit (2^144) u v sign (by decide)
  · apply EnterProof.value_of_bits fullA
    intro i hi
    have geom : ∀j:Fin 18,fullA.getD j 0=400+(j.val+1) := by decide +kernel
    rw [geom ⟨i,hi⟩,show (u+v)/2^145=((u+v)/2^144)/2^1 by rw [Nat.div_div_eq_div_mul];rfl,Nat.testBit_div_two_pow]
    have jj : i+1<19 := Nat.succ_lt_succ (show i<18 from hi)
    exact (bits (i+1) jj).1
  · apply EnterProof.value_of_bits fullM
    intro i hi
    have geom : ∀j:Fin 18,fullM.getD j 0=930+(j.val+1) := by decide +kernel
    rw [geom ⟨i,hi⟩,show (u-sign)/2^145=((u-sign)/2^144)/2^1 by rw [Nat.div_div_eq_div_mul];rfl,Nat.testBit_div_two_pow]
    have jj : i+1<19 := Nat.succ_lt_succ (show i<18 from hi)
    exact (bits (i+1) jj).2

end ECDSAAdd.Entrant.StairPacket.Leave225CompanionInput


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240CompanionInput
open Arithmetic PortalAnd LeaveCompanion LeaveCompanion240
set_option maxRecDepth 50000

theorem decode (s : State) (u v sign : Nat) (magFit : (u-sign)/2^136<2^19)
    (bits : ∀i<19,s.basis (407+i)=((u+v)/2^136).testBit i ∧ s.basis (922+i)=((u-sign)/2^136).testBit i) :
    ((digits 922 longPairs).any s.basis = decide (2^136≤u-sign)) ∧
      (s.basis 922 && !s.basis 407).toNat=upperBorrow (2^136) u v sign ∧
      regValue fullA s.basis=((u+v)/2^137)%2^18 ∧
      regValue fullM s.basis=((u-sign)/2^137)%2^18 := by
  have mag := EnterProof.value_of_bits (digits 922 longPairs) s.basis ((u-sign)/2^136) (by
    intro i hi
    have geom : ∀j:Fin 19,(digits 922 longPairs).getD j 0=922+j.val := by decide +kernel
    rw [geom ⟨i,hi⟩]
    exact (bits i hi).2)
  rw [show (digits 922 longPairs).length=19 from rfl,Nat.mod_eq_of_lt magFit] at mag
  refine ⟨?_,?_,?_,?_⟩
  · rw [any_positive,mag]
    simp only [Nat.div_pos_iff,show 0<2^136 by decide,true_and]
  · have bs := bits 0 (by decide)
    simpa only [Nat.add_zero,bs.1,bs.2] using borrowBit (2^136) u v sign (by decide)
  · apply EnterProof.value_of_bits fullA
    intro i hi
    have geom : ∀j:Fin 18,fullA.getD j 0=407+(j.val+1) := by decide +kernel
    rw [geom ⟨i,hi⟩,show (u+v)/2^137=((u+v)/2^136)/2^1 by rw [Nat.div_div_eq_div_mul];rfl,Nat.testBit_div_two_pow]
    have jj : i+1<19 := Nat.succ_lt_succ (show i<18 from hi)
    exact (bits (i+1) jj).1
  · apply EnterProof.value_of_bits fullM
    intro i hi
    have geom : ∀j:Fin 18,fullM.getD j 0=922+(j.val+1) := by decide +kernel
    rw [geom ⟨i,hi⟩,show (u-sign)/2^137=((u-sign)/2^136)/2^1 by rw [Nat.div_div_eq_div_mul];rfl,Nat.testBit_div_two_pow]
    have jj : i+1<19 := Nat.succ_lt_succ (show i<18 from hi)
    exact (bits (i+1) jj).2

end ECDSAAdd.Entrant.StairPacket.Leave240CompanionInput


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255CompanionInput
open Arithmetic PortalAnd LeaveCompanion LeaveCompanion255
set_option maxRecDepth 50000

theorem decode (s : State) (u v sign : Nat) (magFit : (u-sign)/2^129<2^19)
    (bits : ∀i<19,s.basis (415+i)=((u+v)/2^129).testBit i ∧ s.basis (915+i)=((u-sign)/2^129).testBit i) :
    ((digits 915 longPairs).any s.basis = decide (2^129≤u-sign)) ∧
      (s.basis 915 && !s.basis 415).toNat=upperBorrow (2^129) u v sign ∧
      regValue fullA s.basis=((u+v)/2^130)%2^18 ∧
      regValue fullM s.basis=((u-sign)/2^130)%2^18 := by
  have mag := EnterProof.value_of_bits (digits 915 longPairs) s.basis ((u-sign)/2^129) (by
    intro i hi
    have geom : ∀j:Fin 19,(digits 915 longPairs).getD j 0=915+j.val := by decide +kernel
    rw [geom ⟨i,hi⟩]
    exact (bits i hi).2)
  rw [show (digits 915 longPairs).length=19 from rfl,Nat.mod_eq_of_lt magFit] at mag
  refine ⟨?_,?_,?_,?_⟩
  · rw [any_positive,mag]
    simp only [Nat.div_pos_iff,show 0<2^129 by decide,true_and]
  · have bs := bits 0 (by decide)
    simpa only [Nat.add_zero,bs.1,bs.2] using borrowBit (2^129) u v sign (by decide)
  · apply EnterProof.value_of_bits fullA
    intro i hi
    have geom : ∀j:Fin 18,fullA.getD j 0=415+(j.val+1) := by decide +kernel
    rw [geom ⟨i,hi⟩,show (u+v)/2^130=((u+v)/2^129)/2^1 by rw [Nat.div_div_eq_div_mul];rfl,Nat.testBit_div_two_pow]
    have jj : i+1<19 := Nat.succ_lt_succ (show i<18 from hi)
    exact (bits (i+1) jj).1
  · apply EnterProof.value_of_bits fullM
    intro i hi
    have geom : ∀j:Fin 18,fullM.getD j 0=915+(j.val+1) := by decide +kernel
    rw [geom ⟨i,hi⟩,show (u-sign)/2^130=((u-sign)/2^129)/2^1 by rw [Nat.div_div_eq_div_mul];rfl,Nat.testBit_div_two_pow]
    have jj : i+1<19 := Nat.succ_lt_succ (show i<18 from hi)
    exact (bits (i+1) jj).2

end ECDSAAdd.Entrant.StairPacket.Leave255CompanionInput


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225EraseActual
open Arithmetic Partial PortalAnd LeaveCompanion LeaveCompanion225
set_option maxRecDepth 60000
set_option maxHeartbeats 3000000

def program := ((leave225.drop 93).take 149)
theorem emitted : program=long++(mask++erase) := by decide +kernel

private theorem joined (L M E : Program) (Lspec : L=long) (Mspec : M=mask) (Espec : E=erase) (s : State) (tape : List Bool) (u v sign : Nat)
    (se:sign≤1) (su:sign≤u) (small:min u v<2^144) (magFit:(u-sign)/2^144<2^19)
    (bits:∀i<19,s.basis (400+i)=((u+v)/2^144).testBit i ∧ s.basis (930+i)=((u-sign)/2^144).testBit i)
    (clean:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temps:∀p∈longPairs,s.basis p.2=false) :
    let t:=run (L++(M++E)) tape s
    t.phase=s.phase ∧ regValue fullM t.basis=0 ∧ t.basis 1556=decide (2^144≤u-sign) ∧
      (t.basis 1558).toNat=upperBorrow (2^144) u v sign ∧
      ∀q,q∉1556::1557::1558::fullM → t.basis q=s.basis q := by
  let half:=2^144
  let l:=run L tape s
  let s1:=tape.drop (measurementCount L)
  let w:=run M s1 l
  let s2:=s1.drop (measurementCount M)
  have d:=Leave225CompanionInput.decode s u v sign magFit bits
  have flag:l=⟨s.phase,writeBit s.basis 1556 (decide (half≤u-sign))⟩ := by
    rw [show l=run L tape s from rfl,Lspec,long_run s tape temps,d.1,clean _ (by simp),Bool.false_xor]
  have base (q:Wire) (h:q≠1556) : l.basis q=s.basis q := by simp [flag,writeBit,h]
  have maskOn : w=⟨l.phase,writeBit (writeBit l.basis 1557 (!l.basis 400)) 1558 (l.basis 930 && !l.basis 400)⟩ := by
    rw [show w=run M s1 l from rfl,Mspec,mask_eq]
    apply mask_open _ _ _ _ _ _ (by decide) <;> rw [base _ (by decide)] <;> exact clean _ (by simp)
  have kept (q:Wire) (h:q∉[1556,1557,1558]) : w.basis q=s.basis q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    simp [maskOn,flag,writeBit,h.1,h.2.1,h.2.2]
  have isLong : w.basis 1556=decide (half≤u-sign) := by simp [maskOn,flag,writeBit]
  have borrow : (w.basis 1558).toNat=upperBorrow half u v sign := by
    simpa only [maskOn,writeBit,Function.update_self,base _ (by decide : 400≠1556),base _ (by decide : 930≠1556)] using d.2.1
  have same (rs : List Wire) (ok : ∀q∈rs,q∉[1556,1557,1558]) : regValue rs w.basis=regValue rs s.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h=>kept _ (ok q h))
  have cs : ∀q∈fullC,w.basis q=false := by
    intro q h; rw [kept q ((by decide +kernel : ∀q∈fullC,q∉[1556,1557,1558]) q h)];exact clean _ (by simp [h])
  have condition : (regValue fullM w.basis+(w.basis 1558).toNat)%2^fullM.length=copyValue (some 1556) w.basis (regValue fullA w.basis) := by
    rw [same fullM (by decide +kernel),same fullA (by decide +kernel),d.2.2.1,d.2.2.2,borrow]
    have twice : 2*half=2^145 := (Nat.mul_comm 2 half).trans (Nat.pow_succ 2 144).symm
    have calcValue:=upper_clear half u v sign (2^18) (by decide) se su small
    rw [twice] at calcValue
    simpa only [copyValue,isLong,decide_eq_true_eq] using calcValue
  have e:=LeaveCompanion225.erase_run w s2 cs condition
  rw [←Espec] at e
  dsimp only
  rw [run_append,run_take,run_append,run_take]
  have extern (q:Wire) (notM:q∉fullM) : (run E s2 w).basis q=w.basis q := e.2.1 q notM
  refine ⟨e.1.trans (by simp [maskOn,flag]),e.2.2,(extern _ (by decide)).trans isLong,?_,?_⟩
  · rw [extern _ (by decide)];exact borrow
  · intro q out
    simp only [List.mem_cons,not_or] at out
    exact (extern _ out.2.2.2).trans (kept _ (by simp [out.1,out.2.1,out.2.2.1]))

theorem result (s : State) (tape : List Bool) (u v sign : Nat)
    (se:sign≤1) (su:sign≤u) (small:min u v<2^144) (magFit:(u-sign)/2^144<2^19)
    (bits:∀i<19,s.basis (400+i)=((u+v)/2^144).testBit i ∧ s.basis (930+i)=((u-sign)/2^144).testBit i)
    (clean:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temps:∀p∈longPairs,s.basis p.2=false) :
    let t:=run program tape s
    t.phase=s.phase ∧ regValue fullM t.basis=0 ∧ t.basis 1556=decide (2^144≤u-sign) ∧
      (t.basis 1558).toNat=upperBorrow (2^144) u v sign ∧
      ∀q,q∉1556::1557::1558::fullM → t.basis q=s.basis q := by
  rw [emitted]
  exact joined long mask erase rfl rfl rfl s tape u v sign se su small magFit bits clean temps

end ECDSAAdd.Entrant.StairPacket.Leave225EraseActual


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240EraseActual
open Arithmetic Partial PortalAnd LeaveCompanion LeaveCompanion240
set_option maxRecDepth 60000
set_option maxHeartbeats 3000000

def program := ((leave240.drop 93).take 149)
theorem emitted : program=long++(mask++erase) := by decide +kernel

private theorem joined (L M E : Program) (Lspec : L=long) (Mspec : M=mask) (Espec : E=erase) (s : State) (tape : List Bool) (u v sign : Nat)
    (se:sign≤1) (su:sign≤u) (small:min u v<2^136) (magFit:(u-sign)/2^136<2^19)
    (bits:∀i<19,s.basis (407+i)=((u+v)/2^136).testBit i ∧ s.basis (922+i)=((u-sign)/2^136).testBit i)
    (clean:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temps:∀p∈longPairs,s.basis p.2=false) :
    let t:=run (L++(M++E)) tape s
    t.phase=s.phase ∧ regValue fullM t.basis=0 ∧ t.basis 1556=decide (2^136≤u-sign) ∧
      (t.basis 1558).toNat=upperBorrow (2^136) u v sign ∧
      ∀q,q∉1556::1557::1558::fullM → t.basis q=s.basis q := by
  let half:=2^136
  let l:=run L tape s
  let s1:=tape.drop (measurementCount L)
  let w:=run M s1 l
  let s2:=s1.drop (measurementCount M)
  have d:=Leave240CompanionInput.decode s u v sign magFit bits
  have flag:l=⟨s.phase,writeBit s.basis 1556 (decide (half≤u-sign))⟩ := by
    rw [show l=run L tape s from rfl,Lspec,long_run s tape temps,d.1,clean _ (by simp),Bool.false_xor]
  have base (q:Wire) (h:q≠1556) : l.basis q=s.basis q := by simp [flag,writeBit,h]
  have maskOn : w=⟨l.phase,writeBit (writeBit l.basis 1557 (!l.basis 407)) 1558 (l.basis 922 && !l.basis 407)⟩ := by
    rw [show w=run M s1 l from rfl,Mspec,mask_eq]
    apply mask_open _ _ _ _ _ _ (by decide) <;> rw [base _ (by decide)] <;> exact clean _ (by simp)
  have kept (q:Wire) (h:q∉[1556,1557,1558]) : w.basis q=s.basis q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    simp [maskOn,flag,writeBit,h.1,h.2.1,h.2.2]
  have isLong : w.basis 1556=decide (half≤u-sign) := by simp [maskOn,flag,writeBit]
  have borrow : (w.basis 1558).toNat=upperBorrow half u v sign := by
    simpa only [maskOn,writeBit,Function.update_self,base _ (by decide : 407≠1556),base _ (by decide : 922≠1556)] using d.2.1
  have same (rs : List Wire) (ok : ∀q∈rs,q∉[1556,1557,1558]) : regValue rs w.basis=regValue rs s.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h=>kept _ (ok q h))
  have cs : ∀q∈fullC,w.basis q=false := by
    intro q h; rw [kept q ((by decide +kernel : ∀q∈fullC,q∉[1556,1557,1558]) q h)];exact clean _ (by simp [h])
  have condition : (regValue fullM w.basis+(w.basis 1558).toNat)%2^fullM.length=copyValue (some 1556) w.basis (regValue fullA w.basis) := by
    rw [same fullM (by decide +kernel),same fullA (by decide +kernel),d.2.2.1,d.2.2.2,borrow]
    have twice : 2*half=2^137 := (Nat.mul_comm 2 half).trans (Nat.pow_succ 2 136).symm
    have calcValue:=upper_clear half u v sign (2^18) (by decide) se su small
    rw [twice] at calcValue
    simpa only [copyValue,isLong,decide_eq_true_eq] using calcValue
  have e:=LeaveCompanion240.erase_run w s2 cs condition
  rw [←Espec] at e
  dsimp only
  rw [run_append,run_take,run_append,run_take]
  have extern (q:Wire) (notM:q∉fullM) : (run E s2 w).basis q=w.basis q := e.2.1 q notM
  refine ⟨e.1.trans (by simp [maskOn,flag]),e.2.2,(extern _ (by decide)).trans isLong,?_,?_⟩
  · rw [extern _ (by decide)];exact borrow
  · intro q out
    simp only [List.mem_cons,not_or] at out
    exact (extern _ out.2.2.2).trans (kept _ (by simp [out.1,out.2.1,out.2.2.1]))

theorem result (s : State) (tape : List Bool) (u v sign : Nat)
    (se:sign≤1) (su:sign≤u) (small:min u v<2^136) (magFit:(u-sign)/2^136<2^19)
    (bits:∀i<19,s.basis (407+i)=((u+v)/2^136).testBit i ∧ s.basis (922+i)=((u-sign)/2^136).testBit i)
    (clean:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temps:∀p∈longPairs,s.basis p.2=false) :
    let t:=run program tape s
    t.phase=s.phase ∧ regValue fullM t.basis=0 ∧ t.basis 1556=decide (2^136≤u-sign) ∧
      (t.basis 1558).toNat=upperBorrow (2^136) u v sign ∧
      ∀q,q∉1556::1557::1558::fullM → t.basis q=s.basis q := by
  rw [emitted]
  exact joined long mask erase rfl rfl rfl s tape u v sign se su small magFit bits clean temps

end ECDSAAdd.Entrant.StairPacket.Leave240EraseActual


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255EraseActual
open Arithmetic Partial PortalAnd LeaveCompanion LeaveCompanion255
set_option maxRecDepth 60000
set_option maxHeartbeats 3000000

def program := ((leave255.drop 93).take 149)
theorem emitted : program=long++(mask++erase) := by decide +kernel

private theorem joined (L M E : Program) (Lspec : L=long) (Mspec : M=mask) (Espec : E=erase) (s : State) (tape : List Bool) (u v sign : Nat)
    (se:sign≤1) (su:sign≤u) (small:min u v<2^129) (magFit:(u-sign)/2^129<2^19)
    (bits:∀i<19,s.basis (415+i)=((u+v)/2^129).testBit i ∧ s.basis (915+i)=((u-sign)/2^129).testBit i)
    (clean:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temps:∀p∈longPairs,s.basis p.2=false) :
    let t:=run (L++(M++E)) tape s
    t.phase=s.phase ∧ regValue fullM t.basis=0 ∧ t.basis 1556=decide (2^129≤u-sign) ∧
      (t.basis 1558).toNat=upperBorrow (2^129) u v sign ∧
      ∀q,q∉1556::1557::1558::fullM → t.basis q=s.basis q := by
  let half:=2^129
  let l:=run L tape s
  let s1:=tape.drop (measurementCount L)
  let w:=run M s1 l
  let s2:=s1.drop (measurementCount M)
  have d:=Leave255CompanionInput.decode s u v sign magFit bits
  have flag:l=⟨s.phase,writeBit s.basis 1556 (decide (half≤u-sign))⟩ := by
    rw [show l=run L tape s from rfl,Lspec,long_run s tape temps,d.1,clean _ (by simp),Bool.false_xor]
  have base (q:Wire) (h:q≠1556) : l.basis q=s.basis q := by simp [flag,writeBit,h]
  have maskOn : w=⟨l.phase,writeBit (writeBit l.basis 1557 (!l.basis 415)) 1558 (l.basis 915 && !l.basis 415)⟩ := by
    rw [show w=run M s1 l from rfl,Mspec,mask_eq]
    apply mask_open _ _ _ _ _ _ (by decide) <;> rw [base _ (by decide)] <;> exact clean _ (by simp)
  have kept (q:Wire) (h:q∉[1556,1557,1558]) : w.basis q=s.basis q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    simp [maskOn,flag,writeBit,h.1,h.2.1,h.2.2]
  have isLong : w.basis 1556=decide (half≤u-sign) := by simp [maskOn,flag,writeBit]
  have borrow : (w.basis 1558).toNat=upperBorrow half u v sign := by
    simpa only [maskOn,writeBit,Function.update_self,base _ (by decide : 415≠1556),base _ (by decide : 915≠1556)] using d.2.1
  have same (rs : List Wire) (ok : ∀q∈rs,q∉[1556,1557,1558]) : regValue rs w.basis=regValue rs s.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h=>kept _ (ok q h))
  have cs : ∀q∈fullC,w.basis q=false := by
    intro q h; rw [kept q ((by decide +kernel : ∀q∈fullC,q∉[1556,1557,1558]) q h)];exact clean _ (by simp [h])
  have condition : (regValue fullM w.basis+(w.basis 1558).toNat)%2^fullM.length=copyValue (some 1556) w.basis (regValue fullA w.basis) := by
    rw [same fullM (by decide +kernel),same fullA (by decide +kernel),d.2.2.1,d.2.2.2,borrow]
    have twice : 2*half=2^130 := (Nat.mul_comm 2 half).trans (Nat.pow_succ 2 129).symm
    have calcValue:=upper_clear half u v sign (2^18) (by decide) se su small
    rw [twice] at calcValue
    simpa only [copyValue,isLong,decide_eq_true_eq] using calcValue
  have e:=LeaveCompanion255.erase_run w s2 cs condition
  rw [←Espec] at e
  dsimp only
  rw [run_append,run_take,run_append,run_take]
  have extern (q:Wire) (notM:q∉fullM) : (run E s2 w).basis q=w.basis q := e.2.1 q notM
  refine ⟨e.1.trans (by simp [maskOn,flag]),e.2.2,(extern _ (by decide)).trans isLong,?_,?_⟩
  · rw [extern _ (by decide)];exact borrow
  · intro q out
    simp only [List.mem_cons,not_or] at out
    exact (extern _ out.2.2.2).trans (kept _ (by simp [out.1,out.2.1,out.2.2.1]))

theorem result (s : State) (tape : List Bool) (u v sign : Nat)
    (se:sign≤1) (su:sign≤u) (small:min u v<2^129) (magFit:(u-sign)/2^129<2^19)
    (bits:∀i<19,s.basis (415+i)=((u+v)/2^129).testBit i ∧ s.basis (915+i)=((u-sign)/2^129).testBit i)
    (clean:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temps:∀p∈longPairs,s.basis p.2=false) :
    let t:=run program tape s
    t.phase=s.phase ∧ regValue fullM t.basis=0 ∧ t.basis 1556=decide (2^129≤u-sign) ∧
      (t.basis 1558).toNat=upperBorrow (2^129) u v sign ∧
      ∀q,q∉1556::1557::1558::fullM → t.basis q=s.basis q := by
  rw [emitted]
  exact joined long mask erase rfl rfl rfl s tape u v sign se su small magFit bits clean temps

end ECDSAAdd.Entrant.StairPacket.Leave255EraseActual


end
