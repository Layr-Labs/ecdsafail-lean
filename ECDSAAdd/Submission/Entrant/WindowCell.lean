import ECDSAAdd.Arithmetic.Copy
import ECDSAAdd.Arithmetic.SignedWord
import ECDSAAdd.Arithmetic.SkywalkIntegerTick
import ECDSAAdd.Framework.GateInverse
import ECDSAAdd.Submission.Entrant.MainPart07Core
import ECDSAAdd.Submission.Entrant.StairSideA
import ECDSAAdd.Arithmetic.SignedRecordProgram
import ECDSAAdd.Framework.Cost
import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Math.SkywalkTrace
import ECDSAAdd.Submission.Entrant.Window

-- ===== odd division cell on packets 1..45 =====
-- Odd-word half-cell laws and odd packets (P1Life, DirectPass, RouteA), the odd division slice on packets 1..45
-- (slice45) with its frames, counts and slots, and the cell lemmas used by the window.
-- Credit: odd-word cell spariev (8572aff9); window code dadon (0923a0d6 / 3b1a7f50).

-- ===== P1Cell =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def orMajor (a b c : Wire) : Program :=
  [.X a, .X b, .CCX a b c, .X c, .X a, .X b]


def orErase (a b c : Wire) : Program :=
  [.measureX c [] [.Z a, .Z b, .CZ a b]]


def shortConstAdd (L : Layout) (k : Nat) : Program :=
  literalConstAdd (L.low.drop 3) (L.carry.take 251)
    (L.low.getD 2 0) L.one (k/8) ++ [.X (L.low.getD 2 0)]


def p1Seed (L : Layout) : Program :=
  [.CX L.rmsb L.one, .CX (L.ylow.getD 0 0) L.parity,
   .CX L.r0 L.parity, .CX L.sign L.parity, .X L.parity]


def prepareCompare (L : Layout) : Program :=
  rotateLeft L.r ++ [.X L.r0, .CX L.lower L.r0] ++
    signComplement L.sign L.y ++ signComplement L.lower L.y ++
    [.X L.rmsb, .X L.ymsb]


def exposure (L : Layout) : Program := [.X L.lower, .CX L.r0 L.lower]


def rawAdd (retired : Wire) (L : Layout) : Program :=
  let ys := L.ylow
  let rs := L.low
  let cs := (Q6Structural.q6Carry L).take 255
  let a := ys.getD 0 0
  let b := rs.getD 0 0
  let c := cs.getD 0 0
  let clear := [.CX L.parity b, .CX a b, .X b]
  signComplement L.sign L.y ++ orMajor a b c ++ clear ++
    Q6LifetimeResearch.move retired b
      (CoherentTail.addPrefix (ys.drop 1) (rs.drop 1) (cs.drop 1)
        L.ymsb L.rmsb L.one c) ++ clear.reverse ++
    orErase a b c ++ [.CX a b, .X b] ++ signComplement L.sign L.y


def fold (retired : Wire) (L : Layout) : Program :=
  [.CCX L.parity L.lower L.one, .CX L.lower L.rmsb] ++
    Q6LifetimeResearch.move retired L.rmsb
      (mappedAdd (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one) ++
    [.CX L.lower L.rmsb, .CX L.parity L.rmsb, .X L.rmsb,
     .CX L.parity L.lower, .CX L.rmsb L.lower, .X L.lower,
     .measureX L.one [] [.CZ L.parity L.rmsb]]


def unfoldStep (retired : Wire) (L : Layout) : Program :=
  [.CX L.parity L.lower, .CX L.rmsb L.lower, .X L.lower,
   .CCX L.parity L.lower L.one, .CX L.lower L.rmsb,
   .CX L.parity L.rmsb, .X L.rmsb] ++
    Q6LifetimeResearch.move retired L.rmsb
      (mappedSub (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one) ++
    [.CX L.lower L.rmsb, .CX L.rmsb L.lower,
     .measureX L.one [] [.CZ L.parity L.rmsb]]


def compare (retired : Wire) (forward : Bool) (L : Layout) : Program :=
  let a := L.r.getD 0 0
  let b := L.y.getD 0 0
  let cs := (Q6Structural.q6Carry L).take 255
  let c := cs.getD 0 0
  let nr := notRegister (L.one::L.y)
  nr ++ majority a b L.one c ++ [.X L.one] ++
    Q6LifetimeResearch.move retired L.one
      (Q6LifetimeResearch.compareChain forward (L.r.drop 1) (L.y.drop 1)
        (cs.drop 1) c L.parity) ++
    [.X L.one] ++ eraseCarry a b L.one c ++ nr


def rawSub (retired : Wire) (L : Layout) : Program :=
  let xs := GuardCompression.source L
  let ys := BalancedCircuit.rawTarget L
  let cs := (Q6Structural.q6Carry L).take 255
  let a := xs.getD 0 0
  let b := ys.getD 0 0
  let c := cs.getD 0 0
  signComplement L.sign L.y ++ notRegister ys ++ orMajor a b c ++
    [.X b, .CX L.parity b] ++
    Q6LifetimeResearch.move retired b
      (Q6LifetimeResearch.addTop (xs.drop 1) (ys.drop 1) (cs.drop 1) c) ++
    [.CX L.parity b, .X b] ++ orErase a b c ++ [.CX a b, .X b] ++
    notRegister ys ++ signComplement L.sign L.y ++
    [.CX b L.parity, .CX (L.ylow.getD 0 0) L.parity, .CX L.sign L.parity,
     .X L.parity, .CX L.rmsb L.one]


def forward (retired : Wire) (L : Layout) : Program :=
  p1Seed L ++ rawAdd retired L ++ OneReuse.newPrepare L ++
    rotateRight (BalancedCircuit.rawTarget L) ++ fold retired L ++
    BalancedCleanup.prepareSign L.toLayout ++ BiasedCircuit.flipBias L ++
    prepareCompare L ++ exposure L ++ compare retired true L ++
    (exposure L).reverse ++ (prepareCompare L).reverse ++
    Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L h.toNat) ++
    (BalancedCleanup.prepareSign L.toLayout).reverse


def inverse (retired : Wire) (L : Layout) : Program :=
  BalancedCleanup.prepareSign L.toLayout ++
    Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L (encodeWord 255 (-h))) ++
    prepareCompare L ++ exposure L ++ compare retired false L ++
    (exposure L).reverse ++ (prepareCompare L).reverse ++ BiasedInverse.unbiasView L ++
    unfoldStep retired L ++ rotateLeft (BalancedCircuit.rawTarget L) ++
    [.CX L.parity L.r0] ++ rawSub retired L


def half (retired : Wire) (divide : Bool) (w : Nat → Wire) (sign : Wire) : Program :=
  let L := Q6EndpointCell.ports w sign
  [.X sign] ++ (if divide then forward retired L else inverse retired L) ++ [.X sign]

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Junction =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def recodeBits (msb : Wire) : List MappedBit :=
  (List.range 255).map fun i => ⟨some msb, (2*BiasedCircuit.jh).testBit i⟩


def recodeBank (retired : Wire) (L : Layout) : List Wire :=
  (L.carry.take 254).filter (fun q => q != retired) ++ [L.one]


def recode (retired : Wire) (toOdd : Bool) (L : Layout) (reg : List Wire) : Program :=
  let low := reg.take 255
  let msb := reg.getD 255 0
  if toOdd then mappedAdd (recodeBits msb) low (recodeBank retired L) L.lower ++ [.X msb]
  else [.X msb] ++ mappedSub (recodeBits msb) low (recodeBank retired L) L.lower


def junctionStdHead (retired : Wire) (L : Layout) : Program :=
  GuardCompression.seed L ++ Q6LifetimeResearch.rawAdd retired L ++ OneReuse.newPrepare L ++
    rotateRight (rawTarget L) ++ Q6LifetimeResearch.fold retired L ++
    BalancedCleanup.prepareSign L.toLayout ++ BiasedCircuit.flipBias L ++
    BalancedCleanup.prepareCompare L.toLayout ++ Q6StructuralCell.exposure L ++
    Q6LifetimeResearch.compare retired true L ++ (Q6StructuralCell.exposure L).reverse ++
    (BalancedCleanup.prepareCompare L.toLayout).reverse


def junctionOddHead (retired : Wire) (L : Layout) : Program :=
  p1Seed L ++ rawAdd retired L ++ OneReuse.newPrepare L ++ rotateRight (rawTarget L) ++
    fold retired L ++ BalancedCleanup.prepareSign L.toLayout ++ BiasedCircuit.flipBias L ++
    prepareCompare L ++ exposure L ++ compare retired true L ++
    (exposure L).reverse ++ (prepareCompare L).reverse


def emitOdd (retired : Wire) (L : Layout) : Program :=
  notRegister L.low ++ Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L h.toNat) ++
    [.X L.lower] ++ signComplement L.lower L.r ++ [.CX L.rmsb L.lower]


def acceptOdd (retired : Wire) (L : Layout) : Program :=
  [.CX L.rmsb L.lower] ++ signComplement L.lower L.r ++ [.X L.lower] ++
    Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L (encodeWord 255 (-h))) ++
    notRegister L.low


def emitStandard (retired : Wire) (L : Layout) : Program :=
  notRegister L.low ++ Q6LifetimeResearch.move retired L.rmsb
    (literalConstAdd L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral) ++
    [.X L.lower] ++ signComplement L.lower L.r ++ [.CX L.rmsb L.lower]


def junctionStdRest (retired : Wire) (L : Layout) : Program :=
  BalancedCleanup.prepareCompare L.toLayout ++ Q6StructuralCell.exposure L ++
    Q6LifetimeResearch.compare retired false L ++ (Q6StructuralCell.exposure L).reverse ++
    (BalancedCleanup.prepareCompare L.toLayout).reverse ++ BiasedInverse.unbiasView L ++
    Q6LifetimeResearch.unfoldStep retired L ++ rotateLeft (rawTarget L) ++
    [.CX L.parity L.r0] ++ Q6LifetimeResearch.rawSubTail retired L


def dstart (retired : Wire) (w : Nat → Wire) (sign : Wire) : Program :=
  let L := Q6EndpointCell.ports w sign
  [.X sign] ++ junctionStdHead retired L ++ emitOdd retired L ++
    recode retired true L L.y ++ [.X sign]


def dend (retired : Wire) (w : Nat → Wire) (sign : Wire) : Program :=
  let L := Q6EndpointCell.ports w sign
  [.X sign] ++ junctionOddHead retired L ++ emitStandard retired L ++
    recode retired false L L.y ++ [.X sign]


def mend (retired : Wire) (w : Nat → Wire) (sign : Wire) : Program :=
  let L := Q6EndpointCell.ports w sign
  [.X sign] ++ recode retired false L L.y ++ acceptOdd retired L ++
    junctionStdRest retired L ++ [.X sign]


/-- The flag-controlled offset `2^31+488 = 8*(2^28+61)` has three zero low bits and the
carry-in is clean, so only bits `3..254` of the low register take part in the add. -/
def centerOddBits (L : BalancedConvert.Layout) : List MappedBit :=
  (List.range 252).map fun i =>
    ⟨if (2^28+61 : Nat).testBit i then some L.flag else none, false⟩


def centerOdd (L : BalancedConvert.Layout) : Program :=
  [.CX (HalfConvert.lowBit L) L.flag, .CX L.flag (HalfConvert.lowBit L), .X L.flag] ++
    rotateRight L.word ++
    mappedAdd (centerOddBits L) (L.low.drop 3) ((L.carry.take 254).drop 3) L.cin ++
    [.CX L.flag L.msb, .CX L.msb L.flag]

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== PassCoherent =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- Direct arithmetic/frame induction for the exact coherent-tail recursion.
The source top is read twice; only its single physical site is in the nodup list. -/
theorem coherent_prefix_correct (x y cs : List Wire) (a t z cin : Wire)
    (hy : y.length=x.length) (hc : cs.length=x.length)
    (nd : (cin::(x++[a]++y++[t,z]++cs)).Nodup)
    (s : State) (m : List Bool) (top : s.basis z=s.basis t)
    (clean : ∀ q∈cs,s.basis q=false) :
    (run (CoherentTail.addPrefix x y cs a t z cin) m s).phase=s.phase ∧
    (∀ q,q∉y++[t,z] →
      (run (CoherentTail.addPrefix x y cs a t z cin) m s).basis q=s.basis q) ∧
    regValue (y++[t,z]) (run (CoherentTail.addPrefix x y cs a t z cin) m s).basis=
      (regValue (x++[a,a]) s.basis+regValue (y++[t,z]) s.basis+
        (s.basis cin).toNat)%2^(y++[t,z]).length := by
  induction x generalizing y cs cin s m with
  | nil =>
    have ye : y=[] := List.eq_nil_of_length_eq_zero hy
    have ce : cs=[] := List.eq_nil_of_length_eq_zero hc
    subst y; subst cs
    have four : [a,t,cin,z].Nodup := by
      apply List.nodup_iff_count.mpr
      intro q
      have h := List.nodup_iff_count.mp nd q
      simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
      omega
    have tz : t≠z := by
      have h := List.nodup_iff_count.mp four t
      intro e; subst z
      simp only [List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
      omega
    rw [CoherentTail.addPrefix,CoherentTail.correct a t cin z four s m top]
    refine ⟨rfl,?_,?_⟩
    · intro q hq
      have qt : q≠t := fun e => hq (by simp [e])
      have qz : q≠z := fun e => hq (by simp [e])
      simp [writeBit,qt,qz]
    · cases ha : s.basis a <;> cases ht : s.basis t <;> cases hi : s.basis cin <;>
        simp [regValue,writeBit,sumBit,carryBit,top,ha,ht,hi,tz,Ne.symm tz]
  | cons b xs ih =>
    cases y with
    | nil => simp at hy
    | cons d ys =>
      cases cs with
      | nil => simp at hc
      | cons k ks =>
        have four : [b,d,cin,k].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := List.nodup_iff_count.mp nd q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have tailND : (k::(xs++[a]++ys++[t,z]++ks)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := List.nodup_iff_count.mp nd q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have headAway (q : Wire) (hq : q∈[b,d,cin,k]) : q∉ys++[t,z] := by
          intro bad
          have h := List.nodup_iff_count.mp nd q
          have l := List.count_pos_iff.mpr hq
          have r := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,List.count_nil] at h l r
          omega
        have kAway (q : Wire) (hq : q∈xs++[a]++ys++[t,z]++ks) : q≠k := by
          intro e
          have h := List.nodup_iff_count.mp nd k
          have r := List.count_pos_iff.mpr (e ▸ hq)
          simp only [List.count_cons,List.count_append,List.count_nil,
            beq_self_eq_true,if_true] at h r
          omega
        have n4 := four
        simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
          not_or,not_false_eq_true,and_true] at n4
        obtain ⟨⟨bd,bi,bk⟩,⟨di,dk⟩,ik⟩ := n4
        let A := s.basis b
        let B := s.basis d
        let C := s.basis cin
        let K := carryBit A B C
        let u : State := ⟨s.phase,writeBit s.basis k K⟩
        have keep (q : Wire) (hq : q≠k) : u.basis q=s.basis q := by
          simp [u,writeBit,hq]
        have first (ms : List Bool) : run (majority b d cin k) ms s=u := by
          rw [majority_correct _ _ _ _ four]
          simp [u,K,A,B,C,clean k (by simp)]
        have high := ih ys ks k (by simpa using hy) (by simpa using hc) tailND u m
          (by rw [keep z (kAway z (by simp)),keep t (kAway t (by simp)),top])
          (by intro q hq; rw [keep q (kAway q (by simp [hq]))]; exact clean q (by simp [hq]))
        let v := run (CoherentTail.addPrefix xs ys ks a t z k) m u
        have va : v.basis b=A := (high.2.1 b (headAway b (by simp))).trans (keep b bk)
        have vb : v.basis d=B := (high.2.1 d (headAway d (by simp))).trans (keep d dk)
        have vi : v.basis cin=C := (high.2.1 cin (headAway cin (by simp))).trans (keep cin ik)
        have vk : v.basis k=K := by
          rw [high.2.1 k (headAway k (by simp))]
          simp [u,writeBit]
        have erase (ms : List Bool) : run (eraseCarry b d cin k) ms v=
            ⟨v.phase,writeBit v.basis k false⟩ := by
          apply eraseCarry_correct b d cin k bk dk ik v _ ms
          rw [va,vb,vi,vk]
        have last (ms : List Bool) :
            run [.CX b d,.CX cin d] ms ⟨v.phase,writeBit v.basis k false⟩=
              ⟨v.phase,writeBit (writeBit v.basis k false) d (sumBit A B C)⟩ := by
          simp only [run]
          apply congrArg (State.mk v.phase)
          funext q
          by_cases eq : q=d
          · subst q
            simp only [writeBit,Function.update_self,Function.update_of_ne (Ne.symm di),
              Function.update_of_ne bk,Function.update_of_ne dk,Function.update_of_ne ik,
              va,vb,vi,sumBit]
            cases A <;> cases B <;> cases C <;> rfl
          · simp [writeBit,Function.update,eq]
        simp only [CoherentTail.addPrefix,List.append_assoc,run_append,run_take,
          show measurementCount (majority b d cin k)=0 from rfl,List.drop_zero]
        rw [first,erase,last]
        refine ⟨high.1,?_,?_⟩
        · intro q hq
          have qd : q≠d := fun e => hq (by simp [e])
          have qt : q∉ys++[t,z] := fun h => hq (by simp [h])
          simp only [writeBit,Function.update_of_ne qd]
          by_cases qk : q=k
          · subst q; simp [writeBit,clean k (by simp)]
          · simp only [writeBit,Function.update_of_ne qk]
            exact (high.2.1 q qt).trans (keep q qk)
        · have tailKeep : regValue (ys++[t,z])
              (writeBit (writeBit v.basis k false) d (sumBit A B C))=
                regValue (ys++[t,z]) v.basis := by
            apply regValue_congr
            intro q hq
            have qd : q≠d := fun e => headAway d (by simp) (e ▸ hq)
            have qk : q≠k := fun e => headAway k (by simp) (e ▸ hq)
            simp [writeBit,qd,qk]
          have xin : regValue (xs++[a,a]) u.basis=regValue (xs++[a,a]) s.basis := by
            apply regValue_congr
            intro q hq
            apply keep q
            apply kAway q
            simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self] at hq ⊢
            itauto
          have yin : regValue (ys++[t,z]) u.basis=regValue (ys++[t,z]) s.basis :=
            regValue_congr _ _ _ (fun q hq => keep q (kAway q (by
              simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
              itauto)))
          have uk : u.basis k=K := by simp [u,writeBit]
          change (if (writeBit (writeBit v.basis k false) d (sumBit A B C)) d
            then 1 else 0)+2*regValue (ys++[t,z])
              (writeBit (writeBit v.basis k false) d (sumBit A B C))=_
          rw [tailKeep,high.2.2,xin,yin,uk]
          simp only [writeBit,Function.update_self]
          have col := sum_value_step A B C (regValue (xs++[a,a]) s.basis)
            (regValue (ys++[t,z]) s.basis) (ys++[t,z]).length
          simpa only [List.cons_append,regValue,List.foldr_cons,Bool.toNat,
            Bool.cond_eq_ite,List.length_cons,A,B,C,K] using col

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassLiteral =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- A single mutable word, with the complete remaining basis state fixed. -/
def WordFrame (xs : List Wire) (origin : BasisState) (v : Nat)
    (b : BasisState) : Prop :=
  regValue xs b = v ∧ ∀ q, q∉xs → b q=origin q


def CleanExcept (cs : List Wire) (retired : Wire) (b : BasisState) : Prop :=
  ∀ q∈cs, q≠retired → b q=false


/-- The retired site itself is unrestricted; its physical host is clean. -/
theorem literal_loan_reserved (xs cs : List Wire) (cin one host retired : Wire) (k : Nat)
    (nd : (host::one::cin::(xs++cs)).Nodup) (reserved : retired∉one::cin::xs)
    (len : cs.length+1=xs.length) (s : State) (m : List Bool)
    (one0 : s.basis one=false) (host0 : s.basis host=false)
    (clean : CleanExcept cs retired s.basis) :
    (run (renameProgram (Equiv.swap retired host)
      (literalConstAdd xs cs cin one k)) m s).phase=s.phase ∧
    WordFrame xs s.basis
      ((regValue xs s.basis+k+(s.basis cin).toNat)%2^xs.length)
      (run (renameProgram (Equiv.swap retired host)
        (literalConstAdd xs cs cin one k)) m s).basis := by
  let f := Equiv.swap retired host
  have hn := List.nodup_cons.mp nd
  have baseND := hn.2
  have fixed (q : Wire) (hq : q∈one::cin::xs) : f q=q := by
    have qh : q≠host := fun e => hn.1 (by
      simp only [List.mem_cons,List.mem_append] at hq ⊢; subst q; itauto)
    have qr : q≠retired := fun e => reserved (e ▸ hq)
    exact Equiv.swap_apply_of_ne_of_ne qr qh
  have fx : xs.map f=xs := by
    calc
      xs.map f=xs.map id := List.map_congr_left (fun q hq => fixed q (by simp [hq]))
      _=xs := List.map_id xs
  have fi : f cin=cin := fixed cin (by simp)
  have fo : f one=one := fixed one (by simp)
  have mapped : (one::cin::(xs++cs.map f)).Nodup := by
    have h := baseND.map f.injective
    simpa only [List.map_cons,List.map_append,fo,fi,fx] using h
  have mappedClean : ∀ q∈cs.map f,s.basis q=false := by
    intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    by_cases eq : r=retired
    · subst r; simpa only [f,Equiv.swap_apply_left] using host0
    · have rh : r≠host := fun e => hn.1 (by simp [←e,hr])
      rw [show f r=r from Equiv.swap_apply_of_ne_of_ne eq rh]
      exact clean r hr eq
  rw [FieldRename.literalConstAdd_natural,fx,fi,fo]
  have h := literalConstAdd_correct xs (cs.map f) cin one k mapped
    (by simpa using len) s m one0 mappedClean
  exact ⟨h.1,h.2.2,h.2.1⟩


theorem literal_loan (xs cs : List Wire) (cin one host retired : Wire) (k : Nat)
    (nd : (host::one::cin::(xs++cs)).Nodup) (member : retired∈cs)
    (len : cs.length+1=xs.length) (s : State) (m : List Bool)
    (one0 : s.basis one=false) (host0 : s.basis host=false)
    (clean : CleanExcept cs retired s.basis) :
    (run (renameProgram (Equiv.swap retired host)
      (literalConstAdd xs cs cin one k)) m s).phase=s.phase ∧
    WordFrame xs s.basis
      ((regValue xs s.basis+k+(s.basis cin).toNat)%2^xs.length)
      (run (renameProgram (Equiv.swap retired host)
        (literalConstAdd xs cs cin one k)) m s).basis := by
  apply literal_loan_reserved xs cs cin one host retired k nd
  · intro bad
    have h := List.nodup_iff_count.mp (List.nodup_cons.mp nd).2 retired
    have a := List.count_pos_iff.mpr bad
    have b := List.count_pos_iff.mpr member
    simp only [List.count_cons,List.count_append,List.count_nil] at h a
    omega
  · exact len
  · exact one0
  · exact host0
  · exact clean


















































end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassLoan =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- Transport a complete word frame through an arbitrary wire permutation.
Only the target word must be fixed; logical scratch sites may move. -/
theorem rename_frame (f : Equiv.Perm Wire) (p : Program) (ys : List Wire)
    (s : State) (m : List Bool) (v : Nat)
    (fixed : ∀ q∈ys,f q=q)
    (h : (run p m (pullState f s)).phase=s.phase ∧
      WordFrame ys (pullState f s).basis v (run p m (pullState f s)).basis) :
    (run (renameProgram f p) m s).phase=s.phase ∧
      WordFrame ys s.basis v (run (renameProgram f p) m s).basis := by
  rw [←run_rename f f.injective p m s] at h
  refine ⟨h.1,?_,?_⟩
  · have same : regValue ys (pullState f (run (renameProgram f p) m s)).basis=
        regValue ys (run (renameProgram f p) m s).basis := by
      apply regValue_congr
      intro q hq
      change (run (renameProgram f p) m s).basis (f q)=
        (run (renameProgram f p) m s).basis q
      rw [fixed q hq]
    exact same.symm.trans h.2.1
  · intro q hq
    have away : f.symm q∉ys := by
      intro bad
      have eq := fixed (f.symm q) bad
      rw [f.apply_symm_apply] at eq
      exact hq (eq.symm ▸ bad)
    have e := h.2.2 (f.symm q) away
    simpa only [pullState,f.apply_symm_apply] using e


/-- Direct loan contract for the coherent recursion, retaining arbitrary
history at the retired physical site and restoring every outsider. -/
theorem coherent_loan_correct (x y cs : List Wire) (a t z cin host retired : Wire)
    (hy : y.length=x.length) (hc : cs.length=x.length)
    (nd : (host::cin::(x++[a]++y++[t,z]++cs)).Nodup)
    (member : retired∈cs) (s : State) (m : List Bool)
    (top : s.basis z=s.basis t) (host0 : s.basis host=false)
    (clean : CleanExcept cs retired s.basis) :
    (run (renameProgram (Equiv.swap retired host)
      (CoherentTail.addPrefix x y cs a t z cin)) m s).phase=s.phase ∧
    WordFrame (y++[t,z]) s.basis
      ((regValue (x++[a,a]) s.basis+regValue (y++[t,z]) s.basis+
        (s.basis cin).toNat)%2^(y++[t,z]).length)
      (run (renameProgram (Equiv.swap retired host)
        (CoherentTail.addPrefix x y cs a t z cin)) m s).basis := by
  let f := Equiv.swap retired host
  have hn := List.nodup_cons.mp nd
  have fixed (q : Wire) (hq : q∈cin::(x++[a]++y++[t,z])) : f q=q := by
    have qh : q≠host := fun e => hn.1 (by
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
      subst q; itauto)
    have qr : q≠retired := by
      intro e
      have n := List.nodup_iff_count.mp hn.2 retired
      have p := List.count_pos_iff.mpr (e ▸ hq)
      have c := List.count_pos_iff.mpr member
      simp only [List.count_cons,List.count_append,List.count_nil] at n p
      omega
    exact Equiv.swap_apply_of_ne_of_ne qr qh
  have keep (q : Wire) (hq : q∈cin::(x++[a]++y++[t,z])) :
      (pullState f s).basis q=s.basis q := by
    change s.basis (f q)=_
    rw [fixed q hq]
  have h := coherent_prefix_correct x y cs a t z cin hy hc hn.2 (pullState f s) m
    (by rw [keep z (by simp),keep t (by simp),top]) (by
      intro q hq
      change s.basis (f q)=false
      by_cases e : q=retired
      · subst q; simpa only [f,Equiv.swap_apply_left] using host0
      · have qh : q≠host := fun eq => hn.1 (by simp [←eq,hq])
        rw [show f q=q from Equiv.swap_apply_of_ne_of_ne e qh]
        exact clean q hq e)
  have rvx : regValue (x++[a,a]) (pullState f s).basis=regValue (x++[a,a]) s.basis := by
    apply regValue_congr
    intro q hq
    apply keep q
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_self] at hq ⊢
    itauto
  have rvy : regValue (y++[t,z]) (pullState f s).basis=regValue (y++[t,z]) s.basis := by
    apply regValue_congr
    intro q hq
    apply keep q
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    itauto
  apply rename_frame f _ (y++[t,z]) s m _
  · intro q hq
    apply fixed q
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    itauto
  · refine ⟨h.1,?_,h.2.1⟩
    simpa only [rvx,rvy,keep cin (by simp)] using h.2.2

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassMapped =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- Raw complement form permits a quantum carry-in, including a full-width
source plus one. This avoids the zero carry-in restriction of mappedSub_correct. -/
def mappedResult (sub : Bool) (n a b c : Nat) : Nat :=
  if sub then 2^n-1-((a+(2^n-1-b)+c)%2^n) else (a+b+c)%2^n


def mappedProgram (sub : Bool) (bits : List MappedBit) (ys cs : List Wire)
    (cin : Wire) : Program :=
  if sub then mappedSub bits ys cs cin else mappedAdd bits ys cs cin


theorem mapped_correct (sub : Bool) (bits : List MappedBit) (ys cs : List Wire)
    (cin : Wire) (nd : (cin::(ys++cs)).Nodup)
    (src : ∀q∈mappedWires bits,q∉cin::(ys++cs))
    (hl : bits.length=ys.length) (hc : cs.length+1=ys.length)
    (s : State) (m : List Bool) (clean : ∀q∈cs,s.basis q=false) :
    (run (mappedProgram sub bits ys cs cin) m s).phase=s.phase ∧
    WordFrame ys s.basis
      (mappedResult sub ys.length (mappedValue bits s.basis)
        (regValue ys s.basis) (s.basis cin).toNat)
      (run (mappedProgram sub bits ys cs cin) m s).basis := by
  cases sub
  · have h := mappedAdd_correct bits ys cs cin nd src hl hc s m clean
    exact ⟨h.1,h.2.2,h.2.1⟩
  · have ynd := (List.nodup_append'.mp (List.nodup_cons.mp nd).2).1
    have away (q : Wire) (hq : q∈cin::cs) : q∉ys := by
      intro bad
      have h := List.nodup_iff_count.mp nd q
      have a := List.count_pos_iff.mpr hq
      have b := List.count_pos_iff.mpr bad
      simp only [List.count_cons,List.count_append] at h a
      omega
    let u : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
    have first (r : List Bool) : run (notRegister ys) r s=u :=
      notRegister_correct ys ynd s r
    have keep (q : Wire) (hq : q∉ys) : u.basis q=s.basis q := by simp [u,hq]
    have h := mappedAdd_correct bits ys cs cin nd src hl hc u m (by
      intro q hq
      exact (keep q (away q (by simp [hq]))).trans (clean q hq))
    let v := run (mappedAdd bits ys cs cin) m u
    have source : mappedValue bits u.basis=mappedValue bits s.basis := by
      apply mappedValue_congr
      intro q hq
      exact keep q (fun bad => src q hq (by simp [bad]))
    have input : regValue ys u.basis=2^ys.length-1-regValue ys s.basis := by
      rw [regValue_congr ys u.basis (fun q => !s.basis q)
        (by intro q hq; simp [u,hq]),regValue_complement]
    have output : regValue ys (fun q => if q∈ys then !v.basis q else v.basis q)=
        2^ys.length-1-regValue ys v.basis := by
      rw [regValue_congr ys _ (fun q => !v.basis q)
        (by intro q hq; simp [hq]),regValue_complement]
    simp only [mappedProgram,mappedSub,if_true,List.append_assoc,run_append,run_take,
      (notRegister_counts ys).2,List.take_zero,List.drop_zero]
    rw [first]
    change (run (notRegister ys) _ v).phase=s.phase ∧ _
    rw [notRegister_correct ys ynd]
    refine ⟨h.1,?_,?_⟩
    · rw [output,h.2.2,source,input,keep cin (away cin (by simp))]
      rfl
    · intro q hq
      simp only [hq,if_false]
      exact (h.2.1 q hq).trans (keep q hq)


/-- Loan an arbitrary internal carry to a clean data host. The retired wire
may contain arbitrary history and is restored by the complete outsider frame. -/
theorem mapped_loan (sub : Bool) (bits : List MappedBit) (ys cs : List Wire)
    (cin host retired : Wire) (nd : (host::cin::(ys++cs)).Nodup)
    (src : ∀q∈mappedWires bits,q∉host::cin::(ys++cs))
    (hl : bits.length=ys.length) (hc : cs.length+1=ys.length)
    (member : retired∈cs) (s : State) (m : List Bool)
    (host0 : s.basis host=false) (clean : CleanExcept cs retired s.basis) :
    (run (renameProgram (Equiv.swap retired host)
      (mappedProgram sub bits ys cs cin)) m s).phase=s.phase ∧
    WordFrame ys s.basis
      (mappedResult sub ys.length (mappedValue bits s.basis)
        (regValue ys s.basis) (s.basis cin).toNat)
      (run (renameProgram (Equiv.swap retired host)
        (mappedProgram sub bits ys cs cin)) m s).basis := by
  let f := Equiv.swap retired host
  have hn := List.nodup_cons.mp nd
  have fixed (q : Wire) (hq : q∈cin::ys ∨ q∈mappedWires bits) : f q=q := by
    have qh : q≠host := by
      intro e
      rcases hq with hq|hq
      · exact hn.1 (by simp only [List.mem_cons,List.mem_append] at hq ⊢; subst q; itauto)
      · exact src q hq (by simp [e])
    have qr : q≠retired := by
      intro e
      rcases hq with hq|hq
      · have h := List.nodup_iff_count.mp hn.2 retired
        have a := List.count_pos_iff.mpr (e ▸ hq)
        have b := List.count_pos_iff.mpr member
        simp only [List.count_cons,List.count_append] at h a
        omega
      · exact src q hq (by simp [e,member])
    exact Equiv.swap_apply_of_ne_of_ne qr qh
  have keep (q : Wire) (hq : q∈cin::ys ∨ q∈mappedWires bits) :
      (pullState f s).basis q=s.basis q := by
    change s.basis (f q)=s.basis q
    rw [fixed q hq]
  have h := mapped_correct sub bits ys cs cin hn.2 (by
      intro q hq bad; exact src q hq (List.mem_cons_of_mem host bad)) hl hc
    (pullState f s) m (by
      intro q hq
      change s.basis (f q)=false
      by_cases e : q=retired
      · subst q; simpa only [f,Equiv.swap_apply_left] using host0
      · have qh : q≠host := fun e => hn.1 (by simp [←e,hq])
        rw [show f q=q from Equiv.swap_apply_of_ne_of_ne e qh]
        exact clean q hq e)
  have source : mappedValue bits (pullState f s).basis=mappedValue bits s.basis :=
    mappedValue_congr _ _ _ (fun q hq => keep q (Or.inr hq))
  have word : regValue ys (pullState f s).basis=regValue ys s.basis :=
    regValue_congr _ _ _ (fun q hq => keep q (Or.inl (by simp [hq])))
  apply rename_frame f _ ys s m _
  · intro q hq; exact fixed q (Or.inl (by simp [hq]))
  · simpa only [source,word,keep cin (Or.inl (by simp))] using h

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFoldFlags =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


def foldHead_mode (oddMode sub : Bool) (p l o t : Wire) : Program :=
  if sub then
    if oddMode then [.CX p l,.CX t l,.X l,.CCX p l o,.CX l t,.CX p t,.X t]
    else [.CX p l,.CX t l,.CCX p l o,.CX l t,.CX p t]
  else [.CCX p l o,.CX l t]


def foldTail_mode (oddMode sub : Bool) (p l o t : Wire) : Program :=
  if sub then
    if oddMode then [.CX l t,.CX t l,.measureX o [] [.CZ p t]]
    else [.CX p t,.CX l t,.CX p t,.CX t l,.measureX o [] [.CZ p t]]
  else
    if oddMode then [.CX l t,.CX p t,.X t,.CX p l,.CX t l,.X l,.measureX o [] [.CZ p t]]
    else [.CX l t,.CX p t,.CX p l,.CX t l,.measureX o [] [.Z p,.CZ p t]]


def foldSelector_mode (oddMode sub P N : Bool) : Bool := if sub then P ^^ N ^^ oddMode else N


def foldTop_mode (oddMode sub P S : Bool) : Bool := if sub then S else S ^^ P ^^ oddMode


def foldHead (sub : Bool) (p l o t : Wire) : Program := foldHead_mode false sub p l o t

def foldTail (sub : Bool) (p l o t : Wire) : Program := foldTail_mode false sub p l o t

/-- Direct truth table for the preparation. Only four distinct wires occur. -/
theorem fold_head_mode (oddMode sub : Bool) (p l o t : Wire) (nd : [p,l,o,t].Nodup)
    (s : State) (m : List Bool) (one0 : s.basis o=false)
    (lower : s.basis l=if sub then false else s.basis t) :
    run (foldHead_mode oddMode sub p l o t) m s=
      ⟨s.phase,writeBit (writeBit (writeBit s.basis l
        (foldSelector_mode oddMode sub (s.basis p) (s.basis t))) o
        (s.basis p && foldSelector_mode oddMode sub (s.basis p) (s.basis t))) t false⟩ := by
  have ne := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ne
  apply State.extensionality
  · cases oddMode <;> cases sub <;> rfl
  · funext q
    by_cases qt : q=t
    · subst q
      cases oddMode <;> cases sub <;> cases hp : s.basis p <;> cases ht : s.basis t <;>
        simp_all [foldHead_mode,foldSelector_mode,run,writeBit,ne_comm]
    · by_cases qo : q=o
      · subst q
        cases oddMode <;> cases sub <;> simp_all [foldHead_mode,foldSelector_mode,run,writeBit,ne_comm]
      · by_cases ql : q=l
        · subst q
          cases oddMode <;> cases sub <;> simp_all [foldHead_mode,foldSelector_mode,run,writeBit,ne_comm]
        · cases oddMode <;> cases sub <;> simp [foldHead_mode,run,writeBit,qt,qo,ql]


/-- Both measurement repair polynomials agree with the product stored in
one. No condition is imposed on the incoming phase or record bit. -/
theorem fold_tail_mode (oddMode sub : Bool) (p l o t : Wire) (nd : [p,l,o,t].Nodup)
    (s : State) (m : List Bool) (top0 : s.basis t=false)
    (product : s.basis o=(s.basis p && s.basis l)) :
    run (foldTail_mode oddMode sub p l o t) m s=
      ⟨s.phase,writeBit (writeBit (writeBit s.basis t
        (foldTop_mode oddMode sub (s.basis p) (s.basis l))) l false) o false⟩ := by
  have ne := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ne
  apply State.extensionality
  · cases oddMode <;> cases sub <;> cases hm : m.headD false <;>
      cases hp : s.basis p <;> cases hl : s.basis l <;>
      simp_all [foldTail_mode,run,measureAndCorrect,correct,writeBit,ne_comm]
  · funext q
    by_cases qo : q=o
    · subst q
      cases oddMode <;> cases sub <;> simp [foldTail_mode,run,measureAndCorrect,writeBit]
    · by_cases ql : q=l
      · subst q
        cases oddMode <;> cases sub <;> cases hp : s.basis p <;> cases hl : s.basis l <;>
          simp_all [foldTail_mode,foldTop_mode,run,measureAndCorrect,writeBit,ne_comm]
      · by_cases qt : q=t
        · subst q
          cases oddMode <;> cases sub <;> cases hp : s.basis p <;> cases hl : s.basis l <;>
            simp_all [foldTail_mode,foldTop_mode,run,measureAndCorrect,writeBit,ne_comm]
        · cases oddMode <;> cases sub <;> simp [foldTail_mode,run,measureAndCorrect,writeBit,qo,ql,qt]
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFoldWindow =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- Symbolic-width fold/unfold with an implicit repeated selector source.
The scalar sandwich is exactly the lifetime windowram in both directions. -/
theorem fold_window_mode (oddMode sub : Bool) (bits : List MappedBit) (ys cs : List Wire)
    (p l o t retired : Wire) (nd : ([p,l,o,t]++ys++cs).Nodup)
    (src : ∀q∈mappedWires bits,q=l)
    (hl : bits.length=ys.length) (hc : cs.length+1=ys.length)
    (member : retired∈cs) (s : State) (m : List Bool)
    (one0 : s.basis o=false) (lower : s.basis l=if sub then false else s.basis t)
    (clean : CleanExcept cs retired s.basis) :
    let S := foldSelector_mode oddMode sub (s.basis p) (s.basis t)
    let body := renameProgram (Equiv.swap retired t) (mappedProgram sub bits ys cs o)
    let window := foldHead_mode oddMode sub p l o t++body++foldTail_mode oddMode sub p l o t
    (run window m s).phase=s.phase ∧
    regValue ys (run window m s).basis=
      mappedResult sub ys.length (mappedValue bits (writeBit s.basis l S))
        (regValue ys s.basis) (s.basis p && S).toNat ∧
    (run window m s).basis t=foldTop_mode oddMode sub (s.basis p) S ∧
    (run window m s).basis l=false ∧ (run window m s).basis o=false ∧
    ∀q,q∉ys → q≠t → q≠l → q≠o → (run window m s).basis q=s.basis q := by
  let P := s.basis p
  let S := foldSelector_mode oddMode sub P (s.basis t)
  let u : State := ⟨s.phase,writeBit (writeBit (writeBit s.basis l S) o (P&&S)) t false⟩
  let body := renameProgram (Equiv.swap retired t) (mappedProgram sub bits ys cs o)
  have n4 : [p,l,o,t].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ne := n4
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ne
  have away (q : Wire) (hq : q∈[p,l,o,t]) : q∉ys++cs := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append,List.count_nil] at h a b
    omega
  have keep (q : Wire) (ql : q≠l) (qo : q≠o) (qt : q≠t) :
      u.basis q=s.basis q := by simp [u,writeBit,ql,qo,qt]
  have dataKeep (q : Wire) (hq : q∈ys++cs) : u.basis q=s.basis q := by
    apply keep q
    all_goals intro e; exact away q (by simp [e]) hq
  have first (r : List Bool) : run (foldHead_mode oddMode sub p l o t) r s=u :=
    fold_head_mode oddMode sub p l o t n4 s r one0 lower
  have loanND : (t::o::(ys++cs)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have sourceAway : ∀q∈mappedWires bits,q∉t::o::(ys++cs) := by
    intro q hq
    have e := src q hq
    subst q
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨ne.2.1.2,ne.2.1.1,fun h => away l (by simp) (by simp [h]),
      fun h => away l (by simp) (by simp [h])⟩
  have h := mapped_loan sub bits ys cs o t retired loanND sourceAway hl hc member u m
    (by simp [u,writeBit]) (by
      intro q hq qr
      rw [dataKeep q (by simp [hq])]
      exact clean q hq qr)
  let v := run body m u
  have vp : v.basis p=P := (h.2.2 p (fun bad => away p (by simp) (by simp [bad]))).trans
    (keep p ne.1.1 ne.1.2.1 ne.1.2.2)
  have vl : v.basis l=S := by
    rw [h.2.2 l (fun bad => away l (by simp) (by simp [bad]))]
    simp [u,writeBit,ne_comm,ne]
  have vo : v.basis o=(P&&S) := by
    rw [h.2.2 o (fun bad => away o (by simp) (by simp [bad]))]
    simp [u,writeBit,ne_comm,ne]
  have vt : v.basis t=false := by
    rw [h.2.2 t (fun bad => away t (by simp) (by simp [bad]))]
    simp [u,writeBit]
  have last (r : List Bool) : run (foldTail_mode oddMode sub p l o t) r v=
      ⟨v.phase,writeBit (writeBit (writeBit v.basis t (foldTop_mode oddMode sub P S)) l false) o false⟩ := by
    simpa only [vp,vl] using fold_tail_mode oddMode sub p l o t n4 v r vt (by rw [vo,vp,vl])
  have first0 : measurementCount (foldHead_mode oddMode sub p l o t)=0 := by cases oddMode <;> cases sub <;> rfl
  simp only [List.append_assoc,run_append,run_take,first0,List.drop_zero]
  rw [first,last]
  refine ⟨h.1,?_,?_,?_,?_,?_⟩
  · have outKeep : regValue ys
        (writeBit (writeBit (writeBit v.basis t (foldTop_mode oddMode sub P S)) l false) o false)=
          regValue ys v.basis := by
      apply regValue_congr
      intro q hq
      have qt : q≠t := fun e => away q (by simp [e]) (by simp [hq])
      have ql : q≠l := fun e => away q (by simp [e]) (by simp [hq])
      have qo : q≠o := fun e => away q (by simp [e]) (by simp [hq])
      simp [writeBit,qt,ql,qo]
    have input := regValue_congr ys u.basis s.basis
      (fun q hq => dataKeep q (by simp [hq]))
    have source : mappedValue bits u.basis=mappedValue bits (writeBit s.basis l S) := by
      apply mappedValue_congr
      intro q hq
      rw [src q hq]
      simp [u,writeBit,ne_comm,ne]
    rw [outKeep,h.2.1,input,source]
    simp [u,writeBit,ne_comm,ne,P,S]
  · simp [writeBit,ne_comm,ne,P,S]
  · simp [writeBit,ne_comm,ne]
  · simp [writeBit]
  · intro q hq qt ql qo
    simp only [writeBit,Function.update_of_ne qt,Function.update_of_ne ql,
      Function.update_of_ne qo]
    exact (h.2.2 q hq).trans (keep q ql qo qt)
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassContracts =====
section
namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


/-- Representation choices are isolated from the ripple/loan machinery.
These are interface parameters, not claims that the remaining passes are proved. -/
structure HalfEncoding where
  source : Int → Nat
  raw : Int → Nat
  folded : Int → Nat
  normalized : Int → Nat
  magnitude : Int → Nat
  output : Int → Nat
  odd : Int → Bool
  negative : Int → Bool


def standardEncoding : HalfEncoding where
  source := encodeWord 256
  raw := encodeWord 257
  folded := fun R => encodeWord 256
    (if R<0 then R-(BiasedCircuit.jh : Int)-1 else R+(BiasedCircuit.jh : Int))
  normalized := fun R => encodeWord 255 (normalizedR R)
  magnitude := fun R => encodeWord 255 (BalancedField.magnitude R)
  output := encodeWord 256
  odd := originalParity
  negative := fun R => decide (R<0)


/-- Proposed P1 boundary representation, read from the odd-word emitter.
Its pass proofs and arithmetic bridge are deliberately outside this probe. -/
def oddEncoding : HalfEncoding where
  source := encodeWord 256
  raw := encodeWord 257
  folded := fun R => encodeWord 256
    (if R<0 then R-(BiasedCircuit.jh : Int) else R+(BiasedCircuit.jh : Int))
  normalized := fun R => encodeWord 255 (BalancedField.magnitude R-h)
  magnitude := fun R => encodeWord 255 (BalancedField.magnitude R)
  output := encodeWord 256
  odd := originalParity
  negative := fun R => decide (R<0)


/-- Only data and the three named live flags may differ from the half origin. -/
def HalfOutside (L : Layout) (origin b : BasisState) : Prop :=
  ∀ q, q∉L.r → q≠L.parity → q≠L.lower → q≠L.one → b q=origin q


def LiveFlags (L : Layout) (P N O : Bool) (b : BasisState) : Prop :=
  b L.parity=P ∧ b L.lower=N ∧ b L.one=O


/-- Boundary immediately after rawAdd, before newPrepare and rotation.
The top-copy wire is part of the 257-bit raw result, not clean scratch here. -/
def AfterRaw (E : HalfEncoding) (L : Layout) (retired : Wire)
    (origin : BasisState) (T Y : Int) (b : BasisState) : Prop :=
  regValue (rawTarget L) b=E.raw T ∧ regValue L.y b=E.source Y ∧
  b L.parity=E.odd T ∧ b L.lower=false ∧
  CleanExcept (L.carry.take 254) retired b ∧ HalfOutside L origin b


/-- Boundary immediately after fold. Parity remains live for comparison. -/
def AfterFold (E : HalfEncoding) (L : Layout) (retired : Wire)
    (origin : BasisState) (T R Y : Int) (b : BasisState) : Prop :=
  regValue L.r b=E.folded R ∧ regValue L.y b=E.source Y ∧
  LiveFlags L (E.odd T) false false b ∧
  CleanExcept (L.carry.take 254) retired b ∧ HalfOutside L origin b


/-- Boundary after compare AND the exposure/prepareCompare reverse views.
This is the input to the literal unnormalize pass. -/
def AfterComparison (E : HalfEncoding) (L : Layout) (retired : Wire)
    (origin : BasisState) (R Y : Int) (b : BasisState) : Prop :=
  regValue L.low b=E.normalized R ∧ b L.rmsb=false ∧
  regValue L.y b=E.source Y ∧ LiveFlags L false (E.negative R) false b ∧
  CleanExcept (L.carry.take 254) retired b ∧ HalfOutside L origin b


/-- Boundary immediately after unnormalize, before reverse prepareSign. -/
def AfterUnnormalize (E : HalfEncoding) (L : Layout) (retired : Wire)
    (origin : BasisState) (R Y : Int) (b : BasisState) : Prop :=
  regValue L.low b=E.magnitude R ∧ b L.rmsb=false ∧
  regValue L.y b=E.source Y ∧ LiveFlags L false (E.negative R) false b ∧
  CleanExcept (L.carry.take 254) retired b ∧ HalfOutside L origin b


/-- The inverse uses these boundaries in reverse order. The comparator
computes parity rather than erasing it; the sign/view is otherwise shared. -/
def InverseComparison (E : HalfEncoding) (L : Layout) (retired : Wire)
    (origin : BasisState) (T R Y : Int) (b : BasisState) : Prop :=
  regValue L.low b=E.normalized R ∧ b L.rmsb=false ∧
  regValue L.y b=E.source Y ∧ LiveFlags L (E.odd T) (E.negative R) false b ∧
  CleanExcept (L.carry.take 254) retired b ∧ HalfOutside L origin b

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFoldMath =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedField


/-- The implicit source contains only the selector wire, even though it
is repeated once per bit. No materialized constant register is required. -/
theorem lowBits_sources (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q∈mappedWires (ShortBiasedFold.lowBits L)) : q=L.lower := by
  have shape : ShortBiasedFold.lowBits L=(List.range 255).map
      (fun i => ({wire:=some L.lower,flip:=BiasedCircuit.jh.testBit i} : MappedBit)) := by
    simp [ShortBiasedFold.lowBits,BiasedCircuit.biasBits,List.take_append]
  rw [shape] at hq
  simp only [mappedWires,List.flatMap_map,List.mem_flatMap] at hq
  obtain ⟨i,hi,hq⟩ := hq
  simpa using hq


theorem lowBits_value (L : BalancedCircuit.Layout) (s : BasisState)
    (ne : L.lower≠L.one) :
    mappedValue (ShortBiasedFold.lowBits L) s=
      (if s L.lower then 2^255-1-BiasedCircuit.jh else BiasedCircuit.jh) := by
  let b := writeBit s L.one false
  have same : mappedValue (ShortBiasedFold.lowBits L) b=
      mappedValue (ShortBiasedFold.lowBits L) s := by
    apply mappedValue_congr
    intro q hq
    rw [lowBits_sources L q hq]
    simp [b,writeBit,ne]
  have h := BiasedCircuit.biasBits_value L b
  rw [ShortBiasedFold.biasBits_split,mappedValue_append] at h
  simp only [mappedValue,MappedBit.value,Option.map_some,Option.getD_some,
    Bool.false_xor,mappedValue,Nat.mul_zero,Nat.add_zero] at h
  simp only [b,writeBit,Function.update_self,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
  rw [←same]
  simpa [BiasedCircuit.virtualBias_value,b,writeBit,ne] using h


theorem low_add_mod (n x a c hi : Nat) :
    (x%2^n+a+c)%2^n=((x+(a+2^n*hi)+c)%2^(n+1))%2^n := by
  rw [Nat.mod_mod_of_dvd _ (show 2^n∣2^(n+1) from ⟨2,by simp [Nat.pow_succ]⟩)]
  simp [Nat.add_mod,Nat.mul_mod]


theorem standard_fold_low (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    let S := decide (T<0)
    let P := originalParity T
    ((encodeWord 257 T/2)%2^255+
      (if S then 2^255-1-BiasedCircuit.jh else BiasedCircuit.jh)+(P&&S).toNat)%2^255=
      encodeWord 256 (BiasedCircuit.biasedValue (halfResult T))%2^255 := by
  have h := congrArg (fun x : Nat => x%2^255) (BiasedCircuit.fold_arithmetic T ht)
  rw [BiasedCircuit.virtualBias_value] at h
  dsimp only
  rw [low_add_mod 255]
  exact h


/-- Modular add/subtract cancellation, including the source+carry=N case. -/
theorem undo_mapped_add (N a b c : Nat) (pos : 0<N) (fit : b<N)
    (bound : a+c≤N) :
    N-1-((a+(N-1-((a+b+c)%N))+c)%N)=b := by
  by_cases carry : a+b+c<N
  · rw [Nat.mod_eq_of_lt carry]
    have e : a+(N-1-(a+b+c))+c=N-1-b := by omega
    rw [e,Nat.mod_eq_of_lt (by omega)]
    omega
  · have e : a+b+c=(a+b+c-N)+N := by omega
    have small : a+b+c-N<N := by omega
    rw [e,Nat.add_mod_right,Nat.mod_eq_of_lt small]
    have e2 : a+(N-1-(a+b+c-N))+c=(N-1-b)+N := by omega
    rw [e2,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega


/-- Splitting an encoded signed word at its sign bit, at symbolic width. -/
theorem encode_sign_split (n : Nat) (z : Int)
    (hz : -((2^n : Nat) : Int)≤z ∧ z<((2^n : Nat) : Int)) :
    encodeWord (n+1) z=encodeWord (n+1) z%2^n+2^n*(decide (z<0)).toNat := by
  have pow : 2^(n+1)=2*2^n := by rw [Nat.pow_succ,Nat.mul_comm]
  have h := BalancedFold.encode_shift (n+1) z (by
    rw [pow,Nat.cast_mul]; simp only [Nat.cast_ofNat]; omega)
  by_cases neg : z<0
  · simp only [neg,if_true] at h
    rw [pow,Nat.cast_mul] at h
    norm_num only [Nat.cast_ofNat] at h
    have lo : 2^n≤encodeWord (n+1) z := by omega
    have hi : encodeWord (n+1) z-2^n<2^n := by omega
    have e : encodeWord (n+1) z=(encodeWord (n+1) z-2^n)+2^n := by omega
    conv_rhs => rw [e,Nat.add_mod_right,Nat.mod_eq_of_lt hi]
    simp only [neg,decide_true,Bool.toNat_true,Nat.mul_one]
    omega
  · simp only [neg,if_false] at h
    have hi : encodeWord (n+1) z<2^n := by omega
    simp only [Nat.mod_eq_of_lt hi,neg,decide_false,Bool.toNat_false,Nat.mul_zero,Nat.add_zero]


/-- The scalar sign relation needed by unfold follows from the field half
identity, rather than any equality between circuit generations. -/
theorem fold_sign (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    (originalParity T ^^ negative (halfResult T))=decide (T<0) := by
  have h := halfResult_sign T ht
  change negative (halfResult T)=_ at h
  rw [h]
  cases originalParity T <;> cases decide (T<0) <;> rfl


/-- Raw sign extraction on the entire signed 257-bit range. -/
theorem raw_sign_full (T : Int)
    (range : -((2^256 : Nat) : Int)≤T ∧ T<((2^256 : Nat) : Int)) :
    encodeWord 257 T/2^256=(decide (T<0)).toNat := by
  have a := BalancedFold.encode_shift 257 T (by
    norm_num only [Nat.reducePow] at range ⊢; omega)
  by_cases sn : T<0 <;> simp [sn] at a ⊢ <;>
    norm_num only [Nat.reducePow] at a range ⊢ <;> omega

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFold =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


/-- Exact lifetime fold/unfold, with no semantic encoding assumptions. -/
theorem fold_correct_mode (oddMode sub : Bool) (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈L.carry.take 254)
    (s : State) (m : List Bool) (one0 : s.basis L.one=false)
    (lower : s.basis L.lower=if sub then false else s.basis L.rmsb)
    (clean : CleanExcept (L.carry.take 254) retired s.basis) :
    let S := foldSelector_mode oddMode sub (s.basis L.parity) (s.basis L.rmsb)
    let cell := if oddMode then (if sub then P1Life.unfoldStep retired L else P1Life.fold retired L)
      else (if sub then Q6LifetimeResearch.unfoldStep retired L else Q6LifetimeResearch.fold retired L)
    (run cell m s).phase=s.phase ∧
    regValue L.low (run cell m s).basis=
      mappedResult sub 255 (if S then 2^255-1-BiasedCircuit.jh else BiasedCircuit.jh)
        (regValue L.low s.basis) (s.basis L.parity && S).toNat ∧
    (run cell m s).basis L.rmsb=foldTop_mode oddMode sub (s.basis L.parity) S ∧
    (run cell m s).basis L.lower=false ∧ (run cell m s).basis L.one=false ∧
    ∀q,q∉L.low → q≠L.rmsb → q≠L.lower → q≠L.one →
      (run cell m s).basis q=s.basis q := by
  have nd : ([L.parity,L.lower,L.one,L.rmsb]++L.low++L.carry.take 254).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have lim := (List.take_sublist 254 L.carry).count_le q
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have lowlen : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have len : (L.carry.take 254).length+1=L.low.length := by
    simp [List.length_take,hw.2.2,lowlen]
  have ne : L.lower≠L.one := by
    intro e
    have h := List.nodup_iff_count.mp nd L.lower
    simp only [List.count_cons,List.count_append,List.count_nil] at h
    simp [←e] at h
    omega
  have h := fold_window_mode oddMode sub (ShortBiasedFold.lowBits L) L.low
    (L.carry.take 254) L.parity L.lower L.one L.rmsb retired nd
    (lowBits_sources L) (by rw [ShortBiasedFold.lowBits_length,lowlen]) len member s m
    one0 lower clean
  have value : mappedValue (ShortBiasedFold.lowBits L)
      (writeBit s.basis L.lower (foldSelector_mode oddMode sub (s.basis L.parity) (s.basis L.rmsb)))=
      (if foldSelector_mode oddMode sub (s.basis L.parity) (s.basis L.rmsb)
        then 2^255-1-BiasedCircuit.jh else BiasedCircuit.jh) := by
    exact (lowBits_value L _ ne).trans (by simp only [writeBit,Function.update_self])
  dsimp only at h ⊢
  rw [value,lowlen] at h
  cases oddMode <;> cases sub <;>
    simpa only [P1Life.fold,P1Life.unfoldStep,Q6LifetimeResearch.fold,Q6LifetimeResearch.unfoldStep,
      Q6LifetimeResearch.move,foldHead,foldTail,foldHead_mode,foldTail_mode,mappedProgram,if_true,if_false,
      Bool.false_eq_true,List.append_assoc] using h
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassShift =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


def AfterShift (L : Layout) (retired : Wire) (origin : BasisState)
    (T Y : Int) (b : BasisState) : Prop :=
  regValue L.r b=encodeWord 257 T/2 ∧ regValue L.y b=encodeWord 256 Y ∧
  LiveFlags L (originalParity T) (decide (T<0)) false b ∧ b L.rmsb=decide (T<0) ∧
  CleanExcept (L.carry.take 254) retired b ∧ HalfOutside L origin b


/-- Exact newPrepare and rotation, using the generic rotation proof. -/
theorem shift_boundary_full (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (origin : BasisState) (T Y : Int)
    (ht : -((2^256 : Nat) : Int)≤T ∧ T<((2^256 : Nat) : Int)) :
    Triple (AfterRaw standardEncoding L retired origin T Y)
      (OneReuse.newPrepare L++rotateRight (rawTarget L))
      (AfterShift L retired origin T Y) := by
  have size := BalancedCleanup.widths L.toLayout hw
  have nd : [L.one,L.lower,L.parity,L.r0,L.rmsb].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ne := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ne
  have shape : rawTarget L=L.r0::foldTarget L := by
    simp [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have away (q : Wire) (hq : q∈[L.parity,L.lower]++L.y++L.carry) : q∉rawTarget L := by
    intro bad
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [rawTarget,BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h a b
    omega
  have dataAway (q : Wire) (hq : q∈L.y++L.carry) : q≠L.lower ∧ q≠L.r0 := by
    refine ⟨?_,?_⟩
    · intro e
      exact BalancedCircuit.flagAway L hn L.lower (by simp) (by
        simp only [List.mem_append] at hq ⊢
        rcases hq with hq|hq
        · exact Or.inl (Or.inr (e ▸ hq))
        · exact Or.inr (e ▸ hq))
    · intro e
      exact away q (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; itauto)
        (by simp [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e])
  intro s m hs
  rcases hs with ⟨raw,ys,parity,lower,clean,frame⟩
  change s.basis L.parity=originalParity T at parity
  change regValue (rawTarget L) s.basis=encodeWord 257 T at raw
  have range := ht
  have decode : signedRegValue (rawTarget L) s.basis=T := by
    unfold signedRegValue
    rw [show (rawTarget L).length=257 by simp [rawTarget,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low,hw.1],raw]
    exact decode_encodeWord 257 (by decide) T range
  have bit : s.basis L.r0=originalParity T := by
    apply word_parity L.r0 (foldTarget L) s.basis T
    simpa only [shape] using decode
  have sign : s.basis L.one=decide (T<0) :=
    word_sign L.r L.one s.basis T decode
  let u := run (OneReuse.newPrepare L) [] s
  have u0 : u.basis L.r0=false := by
    simp_all [u,OneReuse.newPrepare,run,writeBit,ne_comm]
  have ul : u.basis L.lower=decide (T<0) := by
    simp_all [u,OneReuse.newPrepare,run,writeBit,ne_comm]
  have keep (q : Wire) (ql : q≠L.lower) (q0 : q≠L.r0) : u.basis q=s.basis q := by
    simp [u,OneReuse.newPrepare,run,writeBit,ql,q0]
  have half : regValue (foldTarget L) s.basis=encodeWord 257 T/2 := by
    rw [shape] at raw
    change (if s.basis L.r0 then 1 else 0)+2*regValue (foldTarget L) s.basis=_ at raw
    cases e : s.basis L.r0 <;> simp only [e,Bool.false_eq_true,if_false,if_true,zero_add] at raw <;> omega
  have even : regValue (rawTarget L) u.basis=2*(encodeWord 257 T/2) := by
    rw [shape]
    change (if u.basis L.r0 then 1 else 0)+2*regValue (foldTarget L) u.basis=_
    rw [u0]
    simp only [Bool.false_eq_true,if_false,zero_add]
    congr 1
    apply Eq.trans _ half
    apply regValue_congr
    intro q hq
    exact keep q (fun e => away q (by simp [e]) (by rw [shape];simp [hq]))
      (fun e => compose_not_fold_r0 L hn (e ▸ hq))
  let v := run (rotateRight (rawTarget L)) m u
  have rot := rotateRight_spec (rawTarget L) (rawTargetND L hn)
    (2*(encodeWord 257 T/2)) (by omega) u m even
  have value : regValue (rawTarget L) v.basis=encodeWord 257 T/2 := by
    have h := rot.2
    change regValue (rawTarget L) v.basis=2*(encodeWord 257 T/2)/2 at h
    omega
  have top0 : v.basis L.one=false := by
    have bound := encodeWord_bound 257 T
    have hb := regValue_highBit L.r L.one v.basis
    change v.basis L.one=true ↔ 2^L.r.length≤regValue (rawTarget L) v.basis at hb
    rw [size.2.1,value] at hb
    cases e : v.basis L.one <;> simp_all <;> omega
  have result : regValue L.r v.basis=encodeWord 257 T/2 := by
    rw [rawTarget,regValue_append] at value
    simpa [regValue,top0] using value
  have vf (q : Wire) (hq : q∉rawTarget L) : v.basis q=u.basis q :=
    (rotate_frame (rawTarget L) u m).2.1 q hq
  have vl : v.basis L.lower=decide (T<0) := (vf _ (away _ (by simp))).trans ul
  have vp : v.basis L.parity=originalParity T :=
    (vf _ (away _ (by simp))).trans ((keep _ (by tauto) (by itauto)).trans parity)
  have msb : v.basis L.rmsb=decide (T<0) := by
    have hb := regValue_highBit L.low L.rmsb v.basis
    change v.basis L.rmsb=true ↔ 2^L.low.length≤regValue L.r v.basis at hb
    rw [size.1,result] at hb
    have rawsign := raw_sign_full T ht
    cases e : v.basis L.rmsb <;> cases neg : decide (T<0) <;>
      simp [e,neg] at hb rawsign ⊢ <;> omega
  have pre0 : measurementCount (OneReuse.newPrepare L)=0 := rfl
  simp only [run_append,run_take,pre0,List.drop_zero,List.take_zero]
  change v.phase=s.phase ∧ _
  refine ⟨rot.1.trans (by simp [u,OneReuse.newPrepare,run]),result,?_,⟨vp,vl,top0⟩,msb,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq =>
      (vf q (away q (by simp [hq]))).trans
        (keep q (dataAway q (by simp [hq])).1 (dataAway q (by simp [hq])).2))).trans ys
  · intro q hq qr
    have hc := List.mem_of_mem_take hq
    rw [vf q (away q (by simp [hc])),keep q (dataAway q (by simp [hc])).1
      (dataAway q (by simp [hc])).2]
    exact clean q hq qr
  · intro q hq hp hl ho
    have qa : q∉rawTarget L := by simp [rawTarget,hq,ho]
    exact (vf q qa).trans ((keep q hl (fun e => hq (by
      simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e]))).trans (frame q hq hp hl ho))


theorem shift_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (origin : BasisState) (T Y : Int)
    (ht : -(2*q)≤T ∧ T≤2*q) :
    Triple (AfterRaw standardEncoding L retired origin T Y)
      (OneReuse.newPrepare L++rotateRight (rawTarget L))
      (AfterShift L retired origin T Y) := by
  apply shift_boundary_full retired L hw hn origin T Y
  have hp := constants
  norm_num [q,p] at ht ⊢
  omega

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFoldBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


/-- The exact fold, after the shift, produces the biased standard word. -/
theorem fold_boundary_math (oddMode : Bool) (E : HalfEncoding)
    (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) (origin : BasisState) (T F Y bias : Int)
    (bound : -((2^255 : Nat) : Int)≤bias ∧ bias<((2^255 : Nat) : Int))
    (sourceCode : E.source Y=encodeWord 256 Y) (parityCode : E.odd T=originalParity T)
    (foldedCode : E.folded F=encodeWord 256 bias)
    (arithmetic : ((encodeWord 257 T/2)%2^255+
      (if decide (T<0) then 2^255-1-BiasedCircuit.jh else BiasedCircuit.jh)+
      (originalParity T&&decide (T<0)).toNat)%2^255=encodeWord 256 bias%2^255)
    (sign : foldTop_mode oddMode false (originalParity T) (decide (T<0))=decide (bias<0)) :
    Triple (AfterShift L retired origin T Y)
      (if oddMode then P1Life.fold retired L else Q6LifetimeResearch.fold retired L)
      (AfterFold E L retired origin T F Y) := by
  have len : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have away (q : Wire) (hq : q∈[L.parity]++L.y++L.carry) :
      q∉L.low ∧ q≠L.rmsb ∧ q≠L.lower ∧ q≠L.one := by
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have a := List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,List.count_nil] at a
    refine ⟨?_,?_,?_,?_⟩
    · intro bad
      have b := List.count_pos_iff.mpr bad
      simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h
      omega
    all_goals
      intro bad
      subst q
      simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil,
        beq_self_eq_true,if_true] at h a
      omega
  intro s m hs
  rcases hs with ⟨value,ys,flags,top,clean,frame⟩
  rcases flags with ⟨parity,lower,one⟩
  have h := fold_correct_mode oddMode false retired L hw hn member s m one (lower.trans top.symm) clean
  simp only [Bool.false_eq_true,if_false,foldSelector_mode] at h
  have low : regValue L.low s.basis=(encodeWord 257 T/2)%2^255 := by
    have a := ShortBiasedFold.reg_low_mod L.low L.rmsb s.basis
    change regValue L.r s.basis%2^L.low.length=regValue L.low s.basis at a
    rw [len,value] at a
    exact a.symm
  have outlow : regValue L.low (run ((if oddMode then P1Life.fold retired L else Q6LifetimeResearch.fold retired L)) m s).basis=
      encodeWord 256 bias%2^255 := by
    rw [h.2.1,low,parity,top]
    have a := arithmetic
    simpa only [mappedResult,Bool.false_eq_true,if_false,Nat.add_comm] using a
  have outtop : (run ((if oddMode then P1Life.fold retired L else Q6LifetimeResearch.fold retired L)) m s).basis L.rmsb=
      decide (bias<0) := by
    rw [h.2.2.1,top,parity]
    exact sign
  have split := encode_sign_split 255 bias bound
  have outvalue : regValue L.r (run ((if oddMode then P1Life.fold retired L else Q6LifetimeResearch.fold retired L)) m s).basis=
      encodeWord 256 bias := by
    change regValue (L.low++[L.rmsb]) _=_
    rw [regValue_append,len,outlow]
    simp only [regValue,List.foldr_cons,List.foldr_nil,Nat.mul_zero,Nat.add_zero]
    rw [outtop]
    simpa only [Bool.toNat,Bool.cond_eq_ite] using split.symm
  have keep (q : Wire) (hq : q∈[L.parity]++L.y++L.carry) :
      (run ((if oddMode then P1Life.fold retired L else Q6LifetimeResearch.fold retired L)) m s).basis q=s.basis q := by
    have a := away q hq
    exact h.2.2.2.2.2 q a.1 a.2.1 a.2.2.1 a.2.2.2
  refine ⟨h.1,?_,?_,?_,?_,?_⟩
  · exact outvalue.trans foldedCode.symm
  · exact ((regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans ys).trans sourceCode.symm
  · exact ⟨((keep _ (by simp)).trans parity).trans parityCode.symm,h.2.2.2.1,h.2.2.2.2.1⟩
  · intro q hq qr
    exact (keep q (by simp [List.mem_of_mem_take hq])).trans (clean q hq qr)
  · intro q hq hp hl ho
    have qlow : q∉L.low := fun bad => hq (by simp [BalancedCleanup.Layout.r,bad])
    have qt : q≠L.rmsb := fun e => hq (by simp [BalancedCleanup.Layout.r,e])
    exact (h.2.2.2.2.2 q qlow qt hl ho).trans (frame q hq hp hl ho)


theorem fold_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254)
    (origin : BasisState) (T Y : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    Triple (AfterShift L retired origin T Y) (Q6LifetimeResearch.fold retired L)
      (AfterFold standardEncoding L retired origin T (halfResult T) Y) := by
  have bound := BiasedCircuit.biased_bounds (halfResult T) (halfResult_spec T ht).1
  apply fold_boundary_math false standardEncoding retired L hw hn member origin T (halfResult T) Y
    (BiasedCircuit.biasedValue (halfResult T)) ⟨bound.1,bound.2.1⟩ rfl rfl
    (by simp [standardEncoding,BiasedCircuit.biasedValue,negative]) (standard_fold_low T ht)
  have neg : decide (BiasedCircuit.biasedValue (halfResult T)<0)=negative (halfResult T) :=
    decide_eq_decide.mpr bound.2.2
  rw [neg]
  simpa [foldTop_mode,negative] using (halfResult_sign T ht).symm


/-- Unit 1 forward boundary, on the emitted preparation/shift/fold list. -/
theorem raw_to_fold (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254)
    (origin : BasisState) (T Y : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    Triple (AfterRaw standardEncoding L retired origin T Y)
      (OneReuse.newPrepare L++rotateRight (rawTarget L)++Q6LifetimeResearch.fold retired L)
      (AfterFold standardEncoding L retired origin T (halfResult T) Y) :=
  Triple.seq (shift_boundary retired L hw hn origin T Y ht)
    (fold_boundary retired L hw hn member origin T Y ht)

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassUnfold =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


def AfterUnfold (L : Layout) (retired : Wire) (origin : BasisState)
    (T Y : Int) (b : BasisState) : Prop :=
  regValue L.r b=encodeWord 257 T/2 ∧ regValue L.y b=encodeWord 256 Y ∧
  LiveFlags L (originalParity T) false false b ∧
  CleanExcept (L.carry.take 254) retired b ∧ HalfOutside L origin b


/-- The inverse fold at the standard boundary, including exact host release. -/
theorem unfold_boundary_math (oddMode : Bool) (E : HalfEncoding)
    (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) (origin : BasisState) (T F Y bias : Int)
    (range : -((2^256 : Nat) : Int)≤T ∧ T<((2^256 : Nat) : Int))
    (bound : -((2^255 : Nat) : Int)≤bias ∧ bias<((2^255 : Nat) : Int))
    (sourceCode : E.source Y=encodeWord 256 Y) (parityCode : E.odd T=originalParity T)
    (foldedCode : E.folded F=encodeWord 256 bias)
    (arithmetic : ((encodeWord 257 T/2)%2^255+
      (if decide (T<0) then 2^255-1-BiasedCircuit.jh else BiasedCircuit.jh)+
      (originalParity T&&decide (T<0)).toNat)%2^255=encodeWord 256 bias%2^255)
    (sign : foldSelector_mode oddMode true (originalParity T) (decide (bias<0))=decide (T<0)) :
    Triple (AfterFold E L retired origin T F Y)
      (if oddMode then P1Life.unfoldStep retired L else Q6LifetimeResearch.unfoldStep retired L)
      (AfterUnfold L retired origin T Y) := by
  have len : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have away (q : Wire) (hq : q∈[L.parity]++L.y++L.carry) :
      q∉L.low ∧ q≠L.rmsb ∧ q≠L.lower ∧ q≠L.one := by
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have a := List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,List.count_nil] at a
    refine ⟨?_,?_,?_,?_⟩
    · intro bad
      have b := List.count_pos_iff.mpr bad
      simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h
      omega
    all_goals
      intro bad
      subst q
      simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil,
        beq_self_eq_true,if_true] at h a
      omega
  intro s m hs
  rcases hs with ⟨value,ys,flags,clean,frame⟩
  rcases flags with ⟨parity,lower,one⟩
  have value2 : regValue L.r s.basis=encodeWord 256 bias := by
    exact value.trans foldedCode
  replace parity := parity.trans parityCode
  have decode : signedRegValue L.r s.basis=bias := by
    unfold signedRegValue
    rw [(BalancedCleanup.widths L.toLayout hw).2.1,value2]
    exact decode_encodeWord 256 (by decide) bias bound
  have top := word_sign L.low L.rmsb s.basis bias decode
  have selector : foldSelector_mode oddMode true (s.basis L.parity) (s.basis L.rmsb)=decide (T<0) := by
    rw [parity,top]
    exact sign
  have h := fold_correct_mode oddMode true retired L hw hn member s m one lower clean
  simp only [if_true] at h
  rw [selector,parity] at h
  have prelow : regValue L.low s.basis=
      encodeWord 256 bias%2^255 := by
    have a := ShortBiasedFold.reg_low_mod L.low L.rmsb s.basis
    change regValue L.r s.basis%2^L.low.length=regValue L.low s.basis at a
    rw [len,value2] at a
    exact a.symm
  let C := if decide (T<0) then 2^255-1-BiasedCircuit.jh else BiasedCircuit.jh
  let K := (originalParity T&&decide (T<0)).toNat
  have cb : C+K≤2^255 := by
    dsimp only [C,K]
    cases originalParity T <;> cases decide (T<0) <;> norm_num [BiasedCircuit.jh]
  have ar := arithmetic
  have outlow : regValue L.low (run ((if oddMode then P1Life.unfoldStep retired L else Q6LifetimeResearch.unfoldStep retired L)) m s).basis=
      (encodeWord 257 T/2)%2^255 := by
    rw [h.2.1,prelow,←ar]
    change 2^255-1-((C+(2^255-1-((_+C+K)%2^255))+K)%2^255)=_
    rw [show (encodeWord 257 T/2)%2^255+C+K=C+(encodeWord 257 T/2)%2^255+K by omega]
    exact undo_mapped_add _ C _ K (Nat.two_pow_pos _) (Nat.mod_lt _ (Nat.two_pow_pos _)) cb
  have outtop : (run ((if oddMode then P1Life.unfoldStep retired L else Q6LifetimeResearch.unfoldStep retired L)) m s).basis L.rmsb=decide (T<0) :=
    h.2.2.1
  have rawsign := raw_sign_full T range
  have div : (encodeWord 257 T/2)/2^255=(decide (T<0)).toNat := by
    rw [Nat.div_div_eq_div_mul]
    exact rawsign
  have split := Nat.mod_add_div (encodeWord 257 T/2) (2^255)
  rw [div] at split
  have outvalue : regValue L.r (run ((if oddMode then P1Life.unfoldStep retired L else Q6LifetimeResearch.unfoldStep retired L)) m s).basis=
      encodeWord 257 T/2 := by
    change regValue (L.low++[L.rmsb]) _=_
    rw [regValue_append,len,outlow]
    simp only [regValue,List.foldr_cons,List.foldr_nil,Nat.mul_zero,Nat.add_zero,outtop]
    simpa only [Bool.toNat,Bool.cond_eq_ite] using split
  have keep (q : Wire) (hq : q∈[L.parity]++L.y++L.carry) :
      (run ((if oddMode then P1Life.unfoldStep retired L else Q6LifetimeResearch.unfoldStep retired L)) m s).basis q=s.basis q := by
    have a := away q hq
    exact h.2.2.2.2.2 q a.1 a.2.1 a.2.2.1 a.2.2.2
  refine ⟨h.1,outvalue,?_,?_,?_,?_⟩
  · exact ((regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans ys).trans sourceCode
  · exact ⟨(keep _ (by simp)).trans parity,h.2.2.2.1,h.2.2.2.2.1⟩
  · intro q hq qr
    exact (keep q (by simp [List.mem_of_mem_take hq])).trans (clean q hq qr)
  · intro q hq hp hl ho
    have qlow : q∉L.low := fun bad => hq (by simp [BalancedCleanup.Layout.r,bad])
    have qt : q≠L.rmsb := fun e => hq (by simp [BalancedCleanup.Layout.r,e])
    exact (h.2.2.2.2.2 q qlow qt hl ho).trans (frame q hq hp hl ho)


theorem unfold_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254)
    (origin : BasisState) (T Y : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    Triple (AfterFold standardEncoding L retired origin T (halfResult T) Y)
      (Q6LifetimeResearch.unfoldStep retired L) (AfterUnfold L retired origin T Y) := by
  have b := BiasedCircuit.biased_bounds (halfResult T) (halfResult_spec T ht).1
  have range : -((2^256 : Nat) : Int)≤T ∧ T<((2^256 : Nat) : Int) := by
    norm_num [q,p] at ht ⊢
    omega
  apply unfold_boundary_math false standardEncoding retired L hw hn member origin T (halfResult T) Y
    (BiasedCircuit.biasedValue (halfResult T)) range ⟨b.1,b.2.1⟩ rfl rfl
    (by simp [standardEncoding,BiasedCircuit.biasedValue,negative]) (standard_fold_low T ht)
  have neg : decide (BiasedCircuit.biasedValue (halfResult T)<0)=negative (halfResult T) :=
    decide_eq_decide.mpr b.2.2
  rw [neg]
  simpa [foldSelector_mode] using fold_sign T ht

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassUnshift =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


/-- Reinsert parity after the inverse rotation. -/
theorem unshift_boundary_full (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (origin : BasisState) (T Y : Int)
    (ht : -((2^256 : Nat) : Int)≤T ∧ T<((2^256 : Nat) : Int)) :
    Triple (AfterUnfold L retired origin T Y)
      (rotateLeft (rawTarget L)++[.CX L.parity L.r0])
      (AfterRaw standardEncoding L retired origin T Y) := by
  have shape : rawTarget L=L.r0::foldTarget L := by
    simp [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have len : (rawTarget L).length=257 := by
    simp [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,hw.1]
  have away (q : Wire) (hq : q∈[L.parity,L.lower]++L.y++L.carry) : q∉rawTarget L := by
    intro bad
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [rawTarget,BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h a b
    omega
  intro s m hs
  rcases hs with ⟨value,ys,flags,clean,frame⟩
  rcases flags with ⟨parity,lower,one⟩
  have input : regValue (rawTarget L) s.basis=encodeWord 257 T/2 := by
    rw [rawTarget,regValue_append,value]
    simp [regValue,one]
  have fit : 2*(encodeWord 257 T/2)<2^(rawTarget L).length := by
    rw [len]
    have h := encodeWord_bound 257 T
    omega
  let u := run (rotateLeft (rawTarget L)) m s
  have rot := rotateLeft_spec (rawTarget L) (rawTargetND L hn)
    (encodeWord 257 T/2) fit s m input
  have uv : regValue (rawTarget L) u.basis=2*(encodeWord 257 T/2) := rot.2
  have uf (q : Wire) (hq : q∉rawTarget L) : u.basis q=s.basis q :=
    (rotate_frame (rawTarget L) s m).2.2.2 q hq
  have up : u.basis L.parity=originalParity T := (uf _ (away _ (by simp))).trans parity
  have u0 : u.basis L.r0=false := by
    rw [shape] at uv
    change (if u.basis L.r0 then 1 else 0)+2*regValue (foldTarget L) u.basis=_ at uv
    cases e : u.basis L.r0 <;> simp [e] at uv ⊢ <;> omega
  have rawpar : encodeWord 257 T%2=(originalParity T).toNat := by
    have range := ht
    have h := signedDecode_mod_two 257 (encodeWord 257 T) (by decide)
    rw [decode_encodeWord 257 (by decide) T range] at h
    have a := originalParity_value T
    cases e : originalParity T <;> simp [e] at a ⊢ <;> omega
  let v := run [.CX L.parity L.r0] [] u
  have vk (q : Wire) (hq : q≠L.r0) : v.basis q=u.basis q := by
    simp [v,run,writeBit,hq]
  have v0 : v.basis L.r0=originalParity T := by simp [v,run,writeBit,u0,up]
  have outvalue : regValue (rawTarget L) v.basis=encodeWord 257 T := by
    have tail : regValue (foldTarget L) v.basis=regValue (foldTarget L) u.basis := by
      apply regValue_congr
      intro q hq
      exact vk q (fun e => compose_not_fold_r0 L hn (e ▸ hq))
    rw [shape] at uv ⊢
    change (if u.basis L.r0 then 1 else 0)+2*regValue (foldTarget L) u.basis=_ at uv
    change (if v.basis L.r0 then 1 else 0)+2*regValue (foldTarget L) v.basis=_
    have twice : 2*regValue (foldTarget L) u.basis=2*(encodeWord 257 T/2) := by
      simpa only [u0,Bool.false_eq_true,if_false,zero_add] using uv
    rw [v0,tail]
    rw [twice]
    simpa only [rawpar,Bool.toNat,Bool.cond_eq_ite] using Nat.mod_add_div (encodeWord 257 T) 2
  have keep (q : Wire) (hq : q∈[L.parity,L.lower]++L.y++L.carry) : v.basis q=s.basis q :=
    (vk q (fun e => away q hq (by rw [shape];simp [e]))).trans (uf q (away q hq))
  simp only [run_append,run_take]
  have last (r : List Bool) : run [.CX L.parity L.r0] r u=v := rfl
  rw [last]
  refine ⟨rot.1,outvalue,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans ys
  · exact (keep _ (by simp)).trans parity
  · exact (keep _ (by simp)).trans lower
  · intro q hq qr
    exact (keep q (by simp [List.mem_of_mem_take hq])).trans (clean q hq qr)
  · intro q hq hp hl ho
    have qa : q∉rawTarget L := by simp [rawTarget,hq,ho]
    have q0 : q≠L.r0 := fun e => hq (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e])
    exact (vk q q0).trans ((uf q qa).trans (frame q hq hp hl ho))


theorem unshift_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (origin : BasisState) (T Y : Int)
    (ht : -(2*q)≤T ∧ T≤2*q) :
    Triple (AfterUnfold L retired origin T Y)
      (rotateLeft (rawTarget L)++[.CX L.parity L.r0])
      (AfterRaw standardEncoding L retired origin T Y) := by
  apply unshift_boundary_full retired L hw hn origin T Y
  norm_num [q,p] at ht ⊢
  omega


/-- Unit 1 inverse boundary, on the exact emitted unfold/rotation/reinsert list. -/
theorem fold_to_raw (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254)
    (origin : BasisState) (T Y : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    Triple (AfterFold standardEncoding L retired origin T (halfResult T) Y)
      (Q6LifetimeResearch.unfoldStep retired L++rotateLeft (rawTarget L)++[.CX L.parity L.r0])
      (AfterRaw standardEncoding L retired origin T Y) := by
  simpa only [List.append_assoc] using Triple.seq
    (unfold_boundary retired L hw hn member origin T Y ht)
    (unshift_boundary retired L hw hn origin T Y ht)

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareLeaf =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- Forward consumes a known answer; inverse computes an answer into zero. -/
def compareInput (erase answer : Bool) : Bool := if erase then answer else false

def compareOutput (erase answer : Bool) : Bool := if erase then false else answer


theorem compare_leaf (erase : Bool) (a b cin target : Wire)
    (nd : [a,b,cin,target].Nodup) (s : State) (m : List Bool)
    (ready : s.basis target=compareInput erase
      (!(carryBit (s.basis a) (s.basis b) (s.basis cin)))) :
    run (Q6LifetimeResearch.compareLeaf erase a b cin target) m s=
      ⟨s.phase,writeBit s.basis target (compareOutput erase
        (!(carryBit (s.basis a) (s.basis b) (s.basis cin))))⟩ := by
  have ne := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ne
  cases erase
  · have h (r : List Bool) := majority_correct a b cin target nd s r
    simp only [compareInput,Bool.false_eq_true,if_false] at ready
    simp only [Q6LifetimeResearch.compareLeaf,Bool.false_eq_true,if_false,
      run_append,run_take,show measurementCount (majority a b cin target)=0 from rfl,
      List.drop_zero,h,run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases e : q=target
    · subst q; simp [writeBit,ready,compareOutput]
    · simp [writeBit,e]
  · let u : State := ⟨s.phase,writeBit s.basis target (!s.basis target)⟩
    have k : u.basis target=carryBit (u.basis a) (u.basis b) (u.basis cin) := by
      simp only [compareInput,if_true] at ready
      simp [u,writeBit,ne.1.2.2,ne.2.1.2,ne.2.2,ready]
    have h := eraseCarry_correct a b cin target ne.1.2.2 ne.2.1.2 ne.2.2 u k m
    simp only [Q6LifetimeResearch.compareLeaf,if_true,run_append,run_take,
      show measurementCount [.X target]=0 from rfl,List.drop_zero,List.take_zero,run]
    change run (eraseCarry a b cin target) m u=_
    rw [h]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases e : q=target <;> simp [u,writeBit,e,compareOutput]


/-- One ripple column converts the numeric threshold to its high tail. -/
theorem compare_threshold (A B C : Bool) (X Y n : Nat) :
    decide (2^(n+1)≤(A.toNat+2*X)+(B.toNat+2*Y)+C.toNat)=
      decide (2^n≤X+Y+(carryBit A B C).toNat) := by
  apply decide_eq_decide.mpr
  have h := fullAdder_bit_value A B C
  have low : (sumBit A B C).toNat≤1 := by cases sumBit A B C <;> decide
  rw [Nat.pow_succ]
  omega

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareChain =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- Direct induction on the lifetime comparator, including both terminal
modes. Only the answer changes; every carry and outsider is restored. -/
theorem compare_chain (erase : Bool) (xs ys cs : List Wire) (cin target : Wire)
    (nd : (target::cin::(xs++ys++cs)).Nodup)
    (hl : xs.length=ys.length) (hc : cs.length+1=ys.length)
    (s : State) (m : List Bool) (clean : ∀q∈cs,s.basis q=false)
    (ready : s.basis target=compareInput erase
      (!decide (2^ys.length≤regValue xs s.basis+regValue ys s.basis+(s.basis cin).toNat))) :
    (run (Q6LifetimeResearch.compareChain erase xs ys cs cin target) m s).phase=s.phase ∧
    (∀q,q≠target → (run (Q6LifetimeResearch.compareChain erase xs ys cs cin target) m s).basis q=s.basis q) ∧
    (run (Q6LifetimeResearch.compareChain erase xs ys cs cin target) m s).basis target=
      compareOutput erase (!decide
        (2^ys.length≤regValue xs s.basis+regValue ys s.basis+(s.basis cin).toNat)) := by
  induction ys generalizing xs cs cin s m with
  | nil => simp at hc
  | cons b bs ih =>
    cases xs with
    | nil => simp at hl
    | cons a as =>
      have count := List.nodup_iff_count.mp nd
      have h4 : [a,b,cin,target].Nodup := by
        apply List.nodup_iff_count.mpr
        intro q
        have h := count q
        simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
        omega
      cases bs with
      | nil =>
        have az : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        have cz : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
        subst as cs
        have pred : (!decide (2^([b]:List Wire).length≤regValue [a] s.basis+
            regValue [b] s.basis+(s.basis cin).toNat))=
            !(carryBit (s.basis a) (s.basis b) (s.basis cin)) := by
          cases ha : s.basis a <;> cases hb : s.basis b <;> cases hi : s.basis cin <;>
            simp [regValue,carryBit,ha,hb,hi]
        rw [pred] at ready ⊢
        rw [Q6LifetimeResearch.compareChain,compare_leaf erase a b cin target h4 s m ready]
        exact ⟨rfl,fun q hq => by simp [writeBit,hq],by simp [writeBit]⟩
      | cons b' bs =>
        cases as with
        | nil => simp at hl
        | cons a' as =>
          cases cs with
          | nil => simp at hc
          | cons c cs =>
            have cAway (q : Wire) (hq : q∈target::cin::((a::a'::as)++(b::b'::bs)++cs)) : q≠c := by
              intro e
              have h := count q
              have pos := List.count_pos_iff.mpr hq
              subst q
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have targetAway (q : Wire)
                (hq : q∈cin::((a::a'::as)++(b::b'::bs)++c::cs)) : q≠target := by
              intro e
              exact (List.nodup_cons.mp nd).1 (e ▸ hq)
            have n4 : [a,b,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := count q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have tailND : (target::c::((a'::as)++(b'::bs)++cs)).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := count q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            let K := carryBit (s.basis a) (s.basis b) (s.basis cin)
            let u : State := ⟨s.phase,writeBit s.basis c K⟩
            have keep (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,hq]
            have first0 := clean c (by simp)
            have first (r : List Bool) : run (majority a b cin c) r s=u := by
              rw [majority_correct _ _ _ _ n4]
              simp [u,K,first0]
            have ux : regValue (a'::as) u.basis=regValue (a'::as) s.basis :=
              regValue_congr _ _ _ (fun q hq => keep q (cAway q (by simp only [List.mem_cons,List.mem_append] at hq ⊢; itauto)))
            have uy : regValue (b'::bs) u.basis=regValue (b'::bs) s.basis :=
              regValue_congr _ _ _ (fun q hq => keep q (cAway q (by simp only [List.mem_cons,List.mem_append] at hq ⊢; itauto)))
            have uc : u.basis c=K := by simp [u,writeBit]
            have pred : (!decide (2^(b'::bs).length≤regValue (a'::as) u.basis+
                  regValue (b'::bs) u.basis+(u.basis c).toNat))=
                !decide (2^(b::b'::bs).length≤regValue (a::a'::as) s.basis+
                  regValue (b::b'::bs) s.basis+(s.basis cin).toNat) := by
              rw [ux,uy,uc]
              simpa only [regValue,List.foldr_cons,List.length_cons,Bool.toNat,Bool.cond_eq_ite,K] using
                congrArg Bool.not (compare_threshold (s.basis a) (s.basis b) (s.basis cin)
                  (regValue (a'::as) s.basis) (regValue (b'::bs) s.basis) (b'::bs).length).symm
            have h := ih (a'::as) cs c tailND (by simpa using hl) (by simpa using hc) u m
              (by
                intro q hq
                rw [keep q (cAway q (by simp only [List.mem_cons,List.mem_append] at hq ⊢; itauto))]
                exact clean q (by simp only [List.mem_cons,List.mem_append] at hq ⊢; itauto))
              (by rw [pred,keep target (cAway target (by simp))];exact ready)
            let v := run (Q6LifetimeResearch.compareChain erase (a'::as) (b'::bs) cs c target) m u
            have va : v.basis a=s.basis a :=
              (h.2.1 a (targetAway a (by simp))).trans (keep a (cAway a (by simp)))
            have vb : v.basis b=s.basis b :=
              (h.2.1 b (targetAway b (by simp))).trans (keep b (cAway b (by simp)))
            have vi : v.basis cin=s.basis cin :=
              (h.2.1 cin (targetAway cin (by simp))).trans (keep cin (cAway cin (by simp)))
            have vc : v.basis c=K := (h.2.1 c (targetAway c (by simp))).trans uc
            have last (r : List Bool) : run (eraseCarry a b cin c) r v=
                ⟨v.phase,writeBit v.basis c false⟩ := by
              apply eraseCarry_correct a b cin c (cAway a (by simp)) (cAway b (by simp))
                (cAway cin (by simp)) v _ r
              rw [va,vb,vi,vc]
            simp only [Q6LifetimeResearch.compareChain,List.append_assoc,run_append,run_take,
              show measurementCount (majority a b cin c)=0 from rfl,List.drop_zero]
            rw [first,last]
            refine ⟨h.1,?_,?_⟩
            · intro q hq
              by_cases e : q=c
              · subst q; simp [writeBit,first0]
              · simp only [writeBit,Function.update_of_ne e]
                exact (h.2.1 q hq).trans (keep q e)
            · change (writeBit v.basis c false) target=_
              rw [show (writeBit v.basis c false) target=v.basis target from by
                simp [writeBit,cAway target (by simp)],h.2.2,pred]

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareLoan =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


theorem compare_loan (erase : Bool) (xs ys cs : List Wire)
    (cin target host retired : Wire) (nd : (host::target::cin::(xs++ys++cs)).Nodup)
    (hl : xs.length=ys.length) (hc : cs.length+1=ys.length) (member : retired∈cs)
    (s : State) (m : List Bool) (host0 : s.basis host=false)
    (clean : CleanExcept cs retired s.basis)
    (ready : s.basis target=compareInput erase
      (!decide (2^ys.length≤regValue xs s.basis+regValue ys s.basis+(s.basis cin).toNat))) :
    (run (renameProgram (Equiv.swap retired host)
      (Q6LifetimeResearch.compareChain erase xs ys cs cin target)) m s).phase=s.phase ∧
    (∀q,q≠target → (run (renameProgram (Equiv.swap retired host)
      (Q6LifetimeResearch.compareChain erase xs ys cs cin target)) m s).basis q=s.basis q) ∧
    (run (renameProgram (Equiv.swap retired host)
      (Q6LifetimeResearch.compareChain erase xs ys cs cin target)) m s).basis target=
      compareOutput erase (!decide
        (2^ys.length≤regValue xs s.basis+regValue ys s.basis+(s.basis cin).toNat)) := by
  let f := Equiv.swap retired host
  have hn := List.nodup_cons.mp nd
  have fixed (q : Wire) (hq : q∈target::cin::(xs++ys)) : f q=q := by
    have qh : q≠host := by
      intro e
      exact hn.1 (by simp only [List.mem_cons,List.mem_append] at hq ⊢;subst q;itauto)
    have qr : q≠retired := by
      intro e
      have h := List.nodup_iff_count.mp hn.2 retired
      have a := List.count_pos_iff.mpr (e ▸ hq)
      have b := List.count_pos_iff.mpr member
      simp only [List.count_cons,List.count_append] at h a
      omega
    exact Equiv.swap_apply_of_ne_of_ne qr qh
  have keep (q : Wire) (hq : q∈target::cin::(xs++ys)) :
      (pullState f s).basis q=s.basis q := by
    change s.basis (f q)=s.basis q
    rw [fixed q hq]
  have xval : regValue xs (pullState f s).basis=regValue xs s.basis :=
    regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))
  have yval : regValue ys (pullState f s).basis=regValue ys s.basis :=
    regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))
  have h := compare_chain erase xs ys cs cin target hn.2 hl hc (pullState f s) m
    (by
      intro q hq
      change s.basis (f q)=false
      by_cases e : q=retired
      · subst q; simpa only [f,Equiv.swap_apply_left] using host0
      · have qh : q≠host := fun e => hn.1 (by simp [←e,hq])
        rw [show f q=q from Equiv.swap_apply_of_ne_of_ne e qh]
        exact clean q hq e)
    (by rw [xval,yval,keep cin (by simp),keep target (by simp)];exact ready)
  rw [←run_rename f f.injective] at h
  refine ⟨h.1,?_,?_⟩
  · intro q hq
    have ne : f.symm q≠target := by
      intro e
      have eq := congrArg f e
      rw [f.apply_symm_apply,fixed target (by simp)] at eq
      exact hq eq
    have a := h.2.1 (f.symm q) ne
    simpa only [pullState,f.apply_symm_apply] using a
  · have a := h.2.2
    change (run _ m s).basis (f target)=_ at a
    simpa only [fixed target (by simp),xval,yval,keep cin (by simp)] using a

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareHead =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


theorem compare_head (erase : Bool) (xs ys cs : List Wire)
    (a b cin c target retired : Wire)
    (nd : ([a,b,cin,c,target]++xs++ys++cs).Nodup)
    (hl : xs.length=ys.length) (hc : cs.length+1=ys.length) (member : retired∈cs)
    (s : State) (m : List Bool) (cin1 : s.basis cin=true) (first0 : s.basis c=false)
    (clean : CleanExcept cs retired s.basis)
    (ready : s.basis target=compareInput erase
      (!decide (2^(b::ys).length≤regValue (a::xs) s.basis+regValue (b::ys) s.basis+(s.basis cin).toNat))) :
    let body := renameProgram (Equiv.swap retired cin)
      (Q6LifetimeResearch.compareChain erase xs ys cs c target)
    let cell := majority a b cin c++[.X cin]++body++[.X cin]++eraseCarry a b cin c
    (run cell m s).phase=s.phase ∧
    (∀q,q≠target → (run cell m s).basis q=s.basis q) ∧
    (run cell m s).basis target=compareOutput erase
      (!decide (2^(b::ys).length≤regValue (a::xs) s.basis+regValue (b::ys) s.basis+(s.basis cin).toNat)) := by
  let body := renameProgram (Equiv.swap retired cin)
    (Q6LifetimeResearch.compareChain erase xs ys cs c target)
  have n4 : [a,b,cin,c].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ne := n4
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ne
  have away (q : Wire) (hq : q∈[a,b,target]++xs++ys++cs) : q≠cin ∧ q≠c := by
    have h := List.nodup_iff_count.mp nd q
    have pos := List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,List.count_nil] at h pos
    constructor <;> intro e <;> subst q <;>
      simp only [beq_self_eq_true,if_true] at h pos <;> omega
  have loanND : (cin::target::c::(xs++ys++cs)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  let K := carryBit (s.basis a) (s.basis b) (s.basis cin)
  let u : State := ⟨s.phase,writeBit s.basis c K⟩
  let w : State := ⟨s.phase,writeBit u.basis cin false⟩
  have keep (q : Wire) (qi : q≠cin) (qc : q≠c) : w.basis q=s.basis q := by
    simp [w,u,writeBit,qi,qc]
  have first (r : List Bool) : run (majority a b cin c) r s=u := by
    rw [majority_correct _ _ _ _ n4]
    simp [u,K,first0]
  have clear (r : List Bool) : run [.X cin] r u=w := by
    simp [run,u,w,writeBit,ne.2.2,cin1]
  have wx : regValue xs w.basis=regValue xs s.basis := by
    apply regValue_congr
    intro q hq
    have a := away q (by simp [hq])
    exact keep q a.1 a.2
  have wy : regValue ys w.basis=regValue ys s.basis := by
    apply regValue_congr
    intro q hq
    have a := away q (by simp [hq])
    exact keep q a.1 a.2
  have wc : w.basis c=K := by simp [w,u,writeBit,ne_comm,ne]
  have pred : (!decide (2^ys.length≤regValue xs w.basis+regValue ys w.basis+(w.basis c).toNat))=
      !decide (2^(b::ys).length≤regValue (a::xs) s.basis+regValue (b::ys) s.basis+(s.basis cin).toNat) := by
    rw [wx,wy,wc]
    simpa only [regValue,List.foldr_cons,List.length_cons,Bool.toNat,Bool.cond_eq_ite,K] using
      congrArg Bool.not (compare_threshold (s.basis a) (s.basis b) (s.basis cin)
        (regValue xs s.basis) (regValue ys s.basis) ys.length).symm
  have h := compare_loan erase xs ys cs c target cin retired loanND hl hc member w m
    (by simp [w,writeBit]) (by
      intro q hq qr
      have a := away q (by simp [hq])
      rw [keep q a.1 a.2]
      exact clean q hq qr)
    (by rw [pred,keep target (away target (by simp)).1 (away target (by simp)).2];exact ready)
  let v := run body m w
  have targetNe (q : Wire) (hq : q∈[a,b,cin,c]) : q≠target := by
    intro e
    have count := List.nodup_iff_count.mp nd target
    have pos := List.count_pos_iff.mpr (e ▸ hq)
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at count pos
    omega
  have va : v.basis a=s.basis a :=
    (h.2.1 a (targetNe a (by simp))).trans (keep a ne.1.2.1 ne.1.2.2)
  have vb : v.basis b=s.basis b :=
    (h.2.1 b (targetNe b (by simp))).trans (keep b ne.2.1.1 ne.2.1.2)
  have vi : v.basis cin=false := by rw [h.2.1 cin (targetNe cin (by simp))];simp [w,writeBit]
  have vc : v.basis c=K := (h.2.1 c (targetNe c (by simp))).trans wc
  let z : State := ⟨v.phase,writeBit v.basis cin true⟩
  have restore (r : List Bool) : run [.X cin] r v=z := by simp [z,run,vi]
  have last (r : List Bool) : run (eraseCarry a b cin c) r z=
      ⟨v.phase,writeBit z.basis c false⟩ := by
    apply eraseCarry_correct a b cin c ne.1.2.2 ne.2.1.2 ne.2.2 z _ r
    simp only [z,writeBit,Function.update_of_ne ne.1.2.1,
      Function.update_of_ne ne.2.1.1,Function.update_of_ne (Ne.symm ne.2.2),
      Function.update_self,va,vb,vc,K,cin1]
  simp only [List.append_assoc,run_append,run_take,
    show measurementCount (majority a b cin c)=0 from rfl,
    show measurementCount [.X cin]=0 from rfl,List.drop_zero]
  rw [first,clear,restore,last]
  refine ⟨h.1,?_,?_⟩
  · intro q hq
    by_cases qc : q=c
    · subst q; simp [writeBit,first0]
    · by_cases qi : q=cin
      · subst q; simp [z,writeBit,ne.2.2,cin1]
      · simp only [z,writeBit,Function.update_of_ne qc,Function.update_of_ne qi]
        exact (h.2.1 q hq).trans (keep q qi qc)
  · have a := away target (by simp)
    simp only [z,writeBit,Function.update_of_ne a.1,Function.update_of_ne a.2]
    rw [h.2.2,pred]

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareWindow =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- Complemented-register comparison and the initialized-head carry loan. -/
theorem compare_window (erase : Bool) (xs ys cs : List Wire)
    (a b cin c target retired : Wire)
    (nd : (target::cin::((a::xs)++(b::ys)++c::cs)).Nodup)
    (hl : xs.length=ys.length) (hc : cs.length+1=ys.length) (member : retired∈cs)
    (s : State) (m : List Bool) (cin0 : s.basis cin=false)
    (clean : CleanExcept (c::cs) retired s.basis)
    (ready : s.basis target=compareInput erase
      (decide (regValue (a::xs) s.basis<regValue (b::ys) s.basis))) :
    let pre := notRegister (cin::b::ys)
    let body := majority a b cin c++[.X cin]++renameProgram (Equiv.swap retired cin)
      (Q6LifetimeResearch.compareChain erase xs ys cs c target)++[.X cin]++eraseCarry a b cin c
    (run (pre++body++pre) m s).phase=s.phase ∧
    (∀q,q≠target → (run (pre++body++pre) m s).basis q=s.basis q) ∧
    (run (pre++body++pre) m s).basis target=compareOutput erase
      (decide (regValue (a::xs) s.basis<regValue (b::ys) s.basis)) := by
  have count := List.nodup_iff_count.mp nd
  have preND : (cin::b::ys).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := count q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have targetAway : target∉cin::b::ys := by
    intro bad
    have h := count target
    have p := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h p
    omega
  have otherAway (q : Wire) (hq : q∈(a::xs)++c::cs) : q∉cin::b::ys := by
    intro bad
    have h := count q
    have p := List.count_pos_iff.mpr hq
    have r := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h p r
    omega
  have firstNe : c≠retired := by
    intro e
    have h := count c
    have p := List.count_pos_iff.mpr (e.symm ▸ member : c∈cs)
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
    omega
  let u : State := ⟨s.phase,fun q => if q∈cin::b::ys then !s.basis q else s.basis q⟩
  have first (r : List Bool) : run (notRegister (cin::b::ys)) r s=u :=
    notRegister_correct _ preND s r
  have keep (q : Wire) (hq : q∉cin::b::ys) : u.basis q=s.basis q := by simp [u,hq]
  have ux : regValue (a::xs) u.basis=regValue (a::xs) s.basis :=
    regValue_congr _ _ _ (fun q hq => keep q (otherAway q (by simp only [List.mem_cons,List.mem_append] at hq ⊢;itauto)))
  have uy : regValue (b::ys) u.basis=2^(b::ys).length-1-regValue (b::ys) s.basis := by
    rw [regValue_congr (b::ys) u.basis (fun q => !s.basis q)
      (by intro q hq;simp [u,hq]),regValue_complement]
  have ui : u.basis cin=true := by simp [u,cin0]
  have pred : (!decide (2^(b::ys).length≤regValue (a::xs) u.basis+
      regValue (b::ys) u.basis+(u.basis cin).toNat))=
      decide (regValue (a::xs) s.basis<regValue (b::ys) s.basis) := by
    rw [ux,uy,ui]
    have fit := regValue_lt (b::ys) s.basis
    have iff : (2^(b::ys).length≤regValue (a::xs) s.basis+
        (2^(b::ys).length-1-regValue (b::ys) s.basis)+1) ↔
        regValue (b::ys) s.basis≤regValue (a::xs) s.basis := by omega
    simp only [Bool.toNat_true]
    rw [←decide_not]
    exact decide_eq_decide.mpr (by omega)
  have headND : ([a,b,cin,c,target]++xs++ys++cs).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := count q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have h := compare_head erase xs ys cs a b cin c target retired headND hl hc member u m ui
    ((keep c (otherAway c (by simp))).trans (clean c (by simp) firstNe))
    (by
      intro q hq qr
      rw [keep q (otherAway q (by simp only [List.mem_cons,List.mem_append] at hq ⊢;itauto))]
      exact clean q (by simp [hq]) qr)
    (by rw [pred,keep target targetAway];exact ready)
  let core := majority a b cin c++[.X cin]++renameProgram (Equiv.swap retired cin)
    (Q6LifetimeResearch.compareChain erase xs ys cs c target)++[.X cin]++eraseCarry a b cin c
  let v := run core m u
  have zero := (notRegister_counts (cin::b::ys)).2
  have execute (p : Program) :
      run (notRegister (cin::b::ys)++p++notRegister (cin::b::ys)) m s=
        run (notRegister (cin::b::ys)) (m.drop (measurementCount p)) (run p m u) := by
    rw [run_append,run_take,run_append,run_take,measurementCount_append,zero,
      Nat.zero_add,List.drop_zero,first]
  dsimp only
  rw [execute]
  change (run (notRegister (cin::b::ys)) _ v).phase=s.phase ∧ _
  rw [notRegister_correct _ preND]
  refine ⟨h.1,?_,?_⟩
  · intro q hq
    change (if q∈cin::b::ys then !v.basis q else v.basis q)=s.basis q
    rw [h.2.1 q hq]
    by_cases e : q∈cin::b::ys <;> simp [u,e]
  · simp only [targetAway,if_false]
    rw [h.2.2,pred]

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCarryHead =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


def carryValue (constant : Bool) (cin : Wire) (b : BasisState) : Bool :=
  if constant then true else b cin


def carryMajor (constant : Bool) (a b cin k : Wire) : Program :=
  if constant then P1Life.orMajor a b k else majority a b cin k


def carryErase (constant : Bool) (a b cin k : Wire) : Program :=
  if constant then P1Life.orErase a b k else eraseCarry a b cin k


def carryStep (constant : Bool) (cin b : Wire) : Program :=
  if constant then [.X b] else [.CX cin b]


def carryClear (constant : Bool) (parity a b cin : Wire) : Program :=
  [.CX parity b,.CX a b]++carryStep constant cin b


def carrySum (constant : Bool) (a b cin : Wire) : Program :=
  [.CX a b]++carryStep constant cin b


theorem or_major_run (a b k : Wire) (nd : [a,b,k].Nodup) (s : State) (m : List Bool) :
    run (P1Life.orMajor a b k) m s=
      ⟨s.phase,writeBit s.basis k (s.basis k ^^ (s.basis a || s.basis b))⟩ := by
  have ne := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ne
  apply State.extensionality
  · rfl
  · funext q
    by_cases qa : q=a
    · subst q; simp [P1Life.orMajor,run,writeBit,ne_comm,ne]
    · by_cases qb : q=b
      · subst q; simp [P1Life.orMajor,run,writeBit,ne_comm,ne]
      · by_cases qk : q=k
        · subst q
          cases ha : s.basis a <;> cases hb : s.basis b <;> cases hk : s.basis k <;>
            simp [P1Life.orMajor,run,writeBit,ne_comm,ne,ha,hb,hk]
        · simp [P1Life.orMajor,run,writeBit,qa,qb,qk]


theorem or_erase_run (a b k : Wire) (ak : a≠k) (bk : b≠k)
    (s : State) (m : List Bool) (ready : s.basis k=(s.basis a || s.basis b)) :
    run (P1Life.orErase a b k) m s=⟨s.phase,writeBit s.basis k false⟩ := by
  apply State.extensionality
  · cases ha : s.basis a <;> cases hb : s.basis b <;> cases hm : m.headD false <;>
      simp_all [P1Life.orErase,run,measureAndCorrect,correct,writeBit]
  · simp [P1Life.orErase,run,measureAndCorrect,correct]


theorem carry_major_run (constant : Bool) (a b cin k : Wire)
    (nd : [a,b,cin,k].Nodup) (s : State) (m : List Bool) (first0 : s.basis k=false) :
    run (carryMajor constant a b cin k) m s=
      ⟨s.phase,writeBit s.basis k
        (carryBit (s.basis a) (s.basis b) (carryValue constant cin s.basis))⟩ := by
  cases constant
  · simpa [carryMajor,carryValue,first0] using majority_correct a b cin k nd s m
  · have n3 : [a,b,k].Nodup := by
      have ne := nd
      simp_all [List.nodup_cons,List.mem_cons]
    change run (P1Life.orMajor a b k) m s=_
    rw [or_major_run a b k n3]
    cases ha : s.basis a <;> cases hb : s.basis b <;>
      simp [carryValue,carryBit,first0,ha,hb]


theorem carry_erase_run (constant : Bool) (a b cin k : Wire)
    (ak : a≠k) (bk : b≠k) (ik : cin≠k) (s : State) (m : List Bool)
    (ready : s.basis k=carryBit (s.basis a) (s.basis b) (carryValue constant cin s.basis)) :
    run (carryErase constant a b cin k) m s=⟨s.phase,writeBit s.basis k false⟩ := by
  cases constant
  · exact eraseCarry_correct a b cin k ak bk ik s (by simpa [carryValue] using ready) m
  · apply or_erase_run a b k ak bk s m
    cases ha : s.basis a <;> cases hb : s.basis b <;> simpa [carryValue,carryBit,ha,hb] using ready


theorem carry_head_records (constant : Bool) (a b cin k parity : Wire) :
    measurementCount (carryMajor constant a b cin k)=0 ∧
    measurementCount (carryClear constant parity a b cin)=0 ∧
    measurementCount (carryClear constant parity a b cin).reverse=0 := by
  cases constant <;> exact ⟨rfl,rfl,rfl⟩























theorem carry_sum_run (constant : Bool) (a b cin : Wire) (nd : [a,b,cin].Nodup)
    (s : State) (m : List Bool) :
    run (carrySum constant a b cin) m s=
      ⟨s.phase,writeBit s.basis b
        (sumBit (s.basis a) (s.basis b) (carryValue constant cin s.basis))⟩ := by
  have ne := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ne
  apply State.extensionality
  · cases constant <;> rfl
  · funext q
    by_cases eq : q=b
    · subst q
      cases constant <;> cases ha : s.basis a <;> cases hb : s.basis b <;>
        cases hi : s.basis cin <;>
        simp [carrySum,carryStep,carryValue,sumBit,run,writeBit,ne_comm,ne,ha,hb,hi]
    · cases constant <;> simp [carrySum,carryStep,run,writeBit,eq]

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassRawHead =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- The literal lifetime head and its cleared-data carry loan. This is a
direct full-state arithmetic proof, with no comparison to an older program. -/
theorem raw_head_withCarry (constant : Bool) (x y cs : List Wire)
    (a b cin k parity ta t z retired : Wire)
    (hy : y.length=x.length) (hc : cs.length=x.length)
    (nd : ([parity,a,cin,b,k]++x++[ta]++y++[t,z]++cs).Nodup)
    (member : retired∈cs) (s : State) (m : List Bool)
    (parityValue : s.basis parity=(s.basis b ^^ s.basis a ^^ carryValue constant cin s.basis))
    (top : s.basis z=s.basis t) (first0 : s.basis k=false)
    (clean : CleanExcept cs retired s.basis) :
    let clear : Program := carryClear constant parity a b cin
    let body := renameProgram (Equiv.swap retired b)
      (CoherentTail.addPrefix x y cs ta t z k)
    let p := carryMajor constant a b cin k++clear++body++clear.reverse++
      carryErase constant a b cin k++carrySum constant a b cin
    (run p m s).phase=s.phase ∧
    WordFrame (b::(y++[t,z])) s.basis
      ((regValue (a::(x++[ta,ta])) s.basis+regValue (b::(y++[t,z])) s.basis+
        (carryValue constant cin s.basis).toNat)%2^(b::(y++[t,z])).length) (run p m s).basis := by
  let clear : Program := carryClear constant parity a b cin
  let body := renameProgram (Equiv.swap retired b) (CoherentTail.addPrefix x y cs ta t z k)
  have n5 : [parity,a,cin,b,k].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have n4 : [a,b,cin,k].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp n5 q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  have n5' := n5
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at n5'
  obtain ⟨⟨pa,pi,pb,pk⟩,⟨ai,ab,ak⟩,⟨ib,ik⟩,bk⟩ := n5'
  have headAway (q : Wire) (hq : q∈[parity,a,cin,b,k]) : q∉y++[t,z] := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have l := List.count_pos_iff.mpr hq
    have r := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append,List.count_nil] at h l r
    omega
  have tailAway (q : Wire) (hq : q∈x++[ta]++y++[t,z]++cs) : q≠b ∧ q≠k := by
    constructor <;> intro e
    all_goals
      have h := List.nodup_iff_count.mp nd q
      have r := List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append,List.count_nil] at h r
      subst q
      simp only [beq_self_eq_true,if_true] at h
      omega
  have loanND : (b::k::(x++[ta]++y++[t,z]++cs)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  let A := s.basis a
  let B := s.basis b
  let C := carryValue constant cin s.basis
  let K := carryBit A B C
  let u : State := ⟨s.phase,writeBit s.basis k K⟩
  let w : State := ⟨s.phase,writeBit u.basis b false⟩
  have uk (q : Wire) (hq : q≠k) : u.basis q=s.basis q := by simp [u,writeBit,hq]
  have wk (q : Wire) (qb : q≠b) (qk : q≠k) : w.basis q=s.basis q := by
    simp [w,u,writeBit,qb,qk]
  have first (ms : List Bool) : run (carryMajor constant a b cin k) ms s=u := by
    exact carry_major_run constant a b cin k n4 s ms first0
  have clearRun (ms : List Bool) : run clear ms u=w := by
    apply State.extensionality
    · cases constant <;> rfl
    · funext q
      by_cases eq : q=b
      · subst q
        cases constant <;> cases ha : s.basis a <;> cases hb : s.basis b <;>
          cases hi : s.basis cin <;>
          simp_all [clear,carryClear,carryStep,carryValue,run,u,w,writeBit,ne_comm]
      · cases constant <;> simp [clear,carryClear,carryStep,run,u,w,writeBit,eq]
  have wclean : CleanExcept cs retired w.basis := by
    intro q hq qr
    have away := tailAway q (by simp [hq])
    rw [wk q away.1 away.2]
    exact clean q hq qr
  have high := coherent_loan_correct x y cs ta t z k b retired hy hc loanND member w m
    (by rw [wk z (tailAway z (by simp)).1 (tailAway z (by simp)).2,
      wk t (tailAway t (by simp)).1 (tailAway t (by simp)).2,top])
    (by simp [w,writeBit]) wclean
  let v := run body m w
  have va : v.basis a=A := (high.2.2 a (headAway a (by simp))).trans (wk a ab ak)
  have vi : v.basis cin=s.basis cin := (high.2.2 cin (headAway cin (by simp))).trans (wk cin ib ik)
  have vp : v.basis parity=s.basis parity :=
    (high.2.2 parity (headAway parity (by simp))).trans (wk parity pb pk)
  have vb : v.basis b=false := by
    rw [high.2.2 b (headAway b (by simp))]
    simp [w,writeBit]
  have vk : v.basis k=K := by
    rw [high.2.2 k (headAway k (by simp))]
    simp [w,u,writeBit,Ne.symm bk]
  let v2 : State := ⟨v.phase,writeBit v.basis b B⟩
  have reverseRun (ms : List Bool) : run clear.reverse ms v=v2 := by
    apply State.extensionality
    · cases constant <;> rfl
    · funext q
      by_cases eq : q=b
      · subst q
        cases constant <;> cases ha : s.basis a <;> cases hb : s.basis b <;>
          cases hi : s.basis cin <;>
          simp_all [clear,carryClear,carryStep,carryValue,run,v2,writeBit,A,B,C,ne_comm]
      · cases constant <;> simp [clear,carryClear,carryStep,run,v2,writeBit,eq]
  have erase (ms : List Bool) : run (carryErase constant a b cin k) ms v2=
      ⟨v2.phase,writeBit v2.basis k false⟩ := by
    apply carry_erase_run constant a b cin k ak bk ik v2 ms
    simp only [v2,writeBit,Function.update_self,Function.update_of_ne ab,
      Function.update_of_ne ib,Function.update_of_ne (Ne.symm bk),va,vi,vk,K]
    cases constant <;> simp [carryValue,C,ib,vi]
  have last (ms : List Bool) :
      run (carrySum constant a b cin) ms ⟨v2.phase,writeBit v2.basis k false⟩=
        ⟨v.phase,writeBit (writeBit v.basis k false) b (sumBit A B C)⟩ := by
    apply State.extensionality
    · cases constant <;> rfl
    · funext q
      by_cases eq : q=b
      · subst q
        cases constant <;> cases ha : s.basis a <;> cases hb : s.basis b <;>
          cases hi : s.basis cin <;>
          simp_all [carrySum,carryStep,carryValue,run,v2,writeBit,A,B,C,sumBit,ne_comm]
      · cases constant <;> simp [carrySum,carryStep,run,v2,writeBit,Function.update,eq]
  have clear0 : measurementCount clear=0 := (carry_head_records constant a b cin k parity).2.1
  have rev0 : measurementCount clear.reverse=0 := (carry_head_records constant a b cin k parity).2.2
  have actual : run (carryMajor constant a b cin k++clear++body++clear.reverse++
      carryErase constant a b cin k++carrySum constant a b cin) m s=
        ⟨v.phase,writeBit (writeBit v.basis k false) b (sumBit A B C)⟩ := by
    simp only [List.append_assoc,run_append,run_take,
      show measurementCount (carryMajor constant a b cin k)=0 from (carry_head_records constant a b cin k parity).1,clear0,rev0,List.drop_zero]
    rw [first,clearRun,reverseRun,erase,last]
  change (run (carryMajor constant a b cin k++clear++body++clear.reverse++
      carryErase constant a b cin k++carrySum constant a b cin) m s).phase=s.phase ∧ _
  rw [actual]
  refine ⟨high.1,?_,?_⟩
  · have targetKeep : regValue (y++[t,z])
        (writeBit (writeBit v.basis k false) b (sumBit A B C))=regValue (y++[t,z]) v.basis := by
      apply regValue_congr
      intro q hq
      have away := tailAway q (by
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; itauto)
      simp [writeBit,away.1,away.2]
    have xin : regValue (x++[ta,ta]) w.basis=regValue (x++[ta,ta]) s.basis := by
      apply regValue_congr
      intro q hq
      have away := tailAway q (by
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self] at hq ⊢; itauto)
      exact wk q away.1 away.2
    have yin : regValue (y++[t,z]) w.basis=regValue (y++[t,z]) s.basis := by
      apply regValue_congr
      intro q hq
      have away := tailAway q (by
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; itauto)
      exact wk q away.1 away.2
    have carryIn : w.basis k=K := by simp [w,u,writeBit,Ne.symm bk]
    change (if (writeBit (writeBit v.basis k false) b (sumBit A B C)) b then 1 else 0)+
      2*regValue (y++[t,z]) (writeBit (writeBit v.basis k false) b (sumBit A B C))=_
    rw [targetKeep,high.2.1,xin,yin,carryIn]
    simp only [writeBit,Function.update_self]
    have col := sum_value_step A B C (regValue (x++[ta,ta]) s.basis)
      (regValue (y++[t,z]) s.basis) (y++[t,z]).length
    simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,List.length_cons,A,B,C,K] using col
  · intro q hq
    have qb : q≠b := fun e => hq (by simp [e])
    have qt : q∉y++[t,z] := fun h => hq (by simp [h])
    simp only [writeBit,Function.update_of_ne qb]
    by_cases qk : q=k
    · subst q; simp [writeBit,first0]
    · simp only [writeBit,Function.update_of_ne qk]
      exact (high.2.2 q qt).trans (wk q qb qk)
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassRaw =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


private theorem raw_split_nonempty (xs : List Wire) (h : xs≠[]) :
    xs=xs.getD 0 0::xs.drop 1 := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons a xs => rfl


private theorem signed_value_mod (n X Y : Nat) (B : Bool) (bound : X<2^n) :
    ((if B then 2^n-1-X else X)+Y+B.toNat)%2^n=signedWordValue n B X Y := by
  cases B
  · simp [signedWordValue,Nat.add_comm]
  · simp only [signedWordValue,ite_true,Bool.toNat_true]
    congr 1
    omega


theorem active_carry_shape (L : Layout) (hw : L.Widths) :
    (Q6Structural.q6Carry L).take 255=L.carry.take 254++[L.lower] := by
  simp [Q6Structural.q6Carry,List.take_append,List.take_take,List.length_take,hw.2.2]


def rawAddMode (constant : Bool) (retired : Wire) (L : Layout) : Program :=
  if constant then P1Life.rawAdd retired L else Q6LifetimeResearch.rawAdd retired L


/-- The exact final-list standard raw-add pass, specified on arbitrary words.
The only nonarithmetic input condition is the seeded parity/top coherence.
The retired site may hold arbitrary history. -/
theorem rawAdd_withCarry (constant : Bool) (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m : List Bool)
    (parityValue : s.basis L.parity=(s.basis L.r0 ^^ s.basis (L.ylow.getD 0 0) ^^
      (s.basis L.sign ^^ carryValue constant L.sign s.basis)))
    (top : s.basis L.one=s.basis L.rmsb)
    (clean : CleanExcept ((Q6Structural.q6Carry L).take 255) retired s.basis) :
    (run (rawAddMode constant retired L) m s).phase=s.phase ∧
    WordFrame (rawTarget L) s.basis
      (((if s.basis L.sign then 2^257-1-regValue (GuardCompression.source L) s.basis
        else regValue (GuardCompression.source L) s.basis)+regValue (rawTarget L) s.basis+
        (carryValue constant L.sign s.basis).toNat)%2^257)
      (run (rawAddMode constant retired L) m s).basis := by
  let cs := (Q6Structural.q6Carry L).take 255
  let a := L.ylow.getD 0 0
  let c := cs.getD 0 0
  let x := L.ylow.drop 1
  let tail := cs.drop 1
  let S := signComplement L.sign L.y
  let clear : Program := carryClear constant L.parity a L.r0 L.sign
  let body := renameProgram (Equiv.swap retired L.r0)
    (CoherentTail.addPrefix x L.rtail tail L.ymsb L.rmsb L.one c)
  let H := carryMajor constant a L.r0 L.sign c++clear++body++clear.reverse++
    carryErase constant a L.r0 L.sign c++carrySum constant a L.r0 L.sign
  have shape : cs=L.carry.take 254++[L.lower] := active_carry_shape L hw
  have clen : cs.length=255 := by rw [shape]; simp [List.length_take,hw.2.2]
  have yl : L.ylow=a::x := raw_split_nonempty _ (by
    intro e; have h := hw.2.1; rw [e] at h; cases h)
  have cl : cs=c::tail := raw_split_nonempty _ (by intro e; rw [e] at clen; cases clen)
  have memberTail : retired∈tail := by
    dsimp only [tail]
    rw [shape,List.drop_append]
    have len : (L.carry.take 254).length=254 := by simp [List.length_take,hw.2.2]
    simp only [len,show 1-254=0 from rfl,List.drop_zero,List.mem_append,List.mem_singleton]
    exact Or.inl member
  have rawND : (L.ylow++[L.ymsb]++L.low++[L.rmsb,L.one]++cs++
      [L.sign,L.parity]).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have lim := (List.take_sublist 254 L.carry).count_le q
    rw [shape]
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have headND : ([L.parity,a,L.sign,L.r0,c]++x++[L.ymsb]++L.rtail++
      [L.rmsb,L.one]++tail).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp rawND q
    rw [yl,cl] at h
    simp only [BalancedCleanup.Layout.low,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have cy : L.rtail.length=x.length := by simp [x,hw.1,hw.2.1]
  have ct : tail.length=x.length := by simp [tail,x,clen,hw.2.1]
  have nd2 : (([L.sign,L.parity]++rawTarget L++cs)++L.y).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp rawND q
    simp only [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.y,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have yND : L.y.Nodup := (List.nodup_append'.mp nd2).2.1
  have notY (q : Wire) (hq : q∈[L.sign,L.parity]++rawTarget L++cs) : q∉L.y :=
    fun bad => List.disjoint_left.mp (List.nodup_append'.mp nd2).2.2 hq bad
  have signAway : L.sign∉L.y := notY _ (by simp)
  have signTarget : L.sign∉rawTarget L := by
    intro bad
    have h := List.nodup_iff_count.mp rawND L.sign
    have p := List.count_pos_iff.mpr bad
    simp only [rawTarget,BalancedCleanup.Layout.r,List.count_cons,List.count_append,
      List.count_nil,beq_self_eq_true,if_true] at h p
    omega
  have sourceAway (q : Wire) (hq : q∈L.y) : q∉rawTarget L := by
    intro bad
    exact notY q (by simp [bad]) hq
  let u := run S m s
  have first := signComplement_correct L.sign L.y yND signAway s m
  have view (q : Wire) : u.basis q=
      if q∈L.y then s.basis q ^^ s.basis L.sign else s.basis q :=
    GuardCompression.complement_bit L.sign L.y yND signAway s m q
  have keep (q : Wire) (hq : q∈[L.sign,L.parity]++rawTarget L++cs) : u.basis q=s.basis q := by
    rw [view,if_neg (notY q hq)]
  have aIn : a∈L.y := by change a∈L.ylow++[L.ymsb]; rw [yl]; simp
  have pv : u.basis L.parity=(u.basis L.r0 ^^ u.basis a ^^ carryValue constant L.sign u.basis) := by
    have sig := keep L.sign (by simp)
    simp only [carryValue,sig]
    rw [keep L.parity (by simp),keep L.r0 (by simp [rawTarget,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]),view a,if_pos aIn,parityValue]
    simp only [carryValue]
    cases constant <;> cases s.basis L.r0 <;> cases s.basis a <;>
      cases s.basis L.sign <;> rfl
  have topU : u.basis L.one=u.basis L.rmsb := by
    rw [keep L.one (by simp [rawTarget]),keep L.rmsb (by
      simp [rawTarget,BalancedCleanup.Layout.r]),top]
  have cNe : c≠retired := by
    intro e
    have h := List.nodup_iff_count.mp headND retired
    have r := List.count_pos_iff.mpr memberTail
    simp only [List.count_cons,List.count_append,List.count_nil] at h
    rw [e] at h
    simp only [beq_self_eq_true,if_true] at h
    omega
  have first0 : u.basis c=false := by
    rw [keep c (by simp [cl])]
    exact clean c (by change c∈cs; rw [cl]; simp) cNe
  have cleanU : CleanExcept tail retired u.basis := by
    intro q hq qr
    have mem : q∈cs := by rw [cl]; simp [hq]
    rw [keep q (by simp [mem])]
    exact clean q mem qr
  have second := raw_head_withCarry constant x L.rtail tail a L.r0 L.sign c L.parity
    L.ymsb L.rmsb L.one retired cy ct headND memberTail u m pv topU first0 cleanU
  have targetShape : (L.r0::(L.rtail++[L.rmsb,L.one]))=rawTarget L := by
    simp [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have sourceShape : (a::(x++[L.ymsb,L.ymsb]))=GuardCompression.source L := by
    simp only [GuardCompression.source,BalancedCleanup.Layout.y,yl,List.cons_append,List.append_assoc,
      List.singleton_append,List.nil_append]
  change (run H m u).phase=u.phase ∧ WordFrame _ u.basis _ (run H m u).basis at second
  rw [targetShape,sourceShape] at second
  let v := run H m u
  let out := run S (m.drop (measurementCount H)) v
  have third := signComplement_correct L.sign L.y yND signAway v (m.drop (measurementCount H))
  have signV : v.basis L.sign=s.basis L.sign :=
    (second.2.2 L.sign signTarget).trans (keep L.sign (by simp))
  have outside (q : Wire) (hq : q∉rawTarget L) : out.basis q=s.basis q := by
    rw [GuardCompression.complement_bit L.sign L.y yND signAway v _ q,
      second.2.2 q hq,view q,signV]
    by_cases mem : q∈L.y <;> simp [mem]
  have targetOut : regValue (rawTarget L) out.basis=regValue (rawTarget L) v.basis :=
    regValue_congr _ _ _ (fun q hq => third.2.1 q (notY q (by simp [hq])))
  have targetIn : regValue (rawTarget L) u.basis=regValue (rawTarget L) s.basis :=
    regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))
  have sourceIn : regValue (GuardCompression.source L) u.basis=
      if s.basis L.sign then 2^(GuardCompression.source L).length-1-
        regValue (GuardCompression.source L) s.basis else regValue (GuardCompression.source L) s.basis :=
    GuardCompression.complement_read L.sign L.y (GuardCompression.source L) yND signAway
      (by intro q hq
          simp only [GuardCompression.source,BalancedCleanup.Layout.y,List.mem_append,
            List.mem_singleton] at hq ⊢
          itauto) s m
  have targetLen : (rawTarget L).length=257 := by
    simp [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,hw.1]
  have sourceLen : (GuardCompression.source L).length=257 := by
    simp [GuardCompression.source,BalancedCleanup.Layout.y,hw.2.1]
  have actual : run (rawAddMode constant retired L) m s=out := by
    have programShape : rawAddMode constant retired L=S++H++S := by
      cases constant <;> simp only [rawAddMode,Q6LifetimeResearch.rawAdd,P1Life.rawAdd,
        carryClear,carryMajor,carryErase,carrySum,carryStep,Bool.false_eq_true,if_true,if_false,
        Q6LifetimeResearch.move,
        BalancedCleanup.Layout.low,List.getD_cons_zero,List.drop_succ_cons,List.drop_zero,
        S,H,clear,body,a,c,x,tail,cs,List.append_assoc] <;> rfl
    rw [programShape,List.append_assoc,run_append,run_take,(signComplement_counts L.sign L.y).2,
      List.drop_zero,run_append,run_take]
  rw [actual]
  refine ⟨third.1.trans (second.1.trans first.1),?_,outside⟩
  rw [targetOut,second.2.1,targetIn,sourceIn,targetLen,sourceLen]
  simp only [carryValue,keep L.sign (by simp)]


theorem rawAdd_correct (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m : List Bool)
    (parityValue : s.basis L.parity=(s.basis L.r0 ^^ s.basis (L.ylow.getD 0 0)))
    (top : s.basis L.one=s.basis L.rmsb)
    (clean : CleanExcept ((Q6Structural.q6Carry L).take 255) retired s.basis) :
    (run (Q6LifetimeResearch.rawAdd retired L) m s).phase=s.phase ∧
    WordFrame (rawTarget L) s.basis
      (signedWordValue 257 (s.basis L.sign)
        (regValue (GuardCompression.source L) s.basis) (regValue (rawTarget L) s.basis))
      (run (Q6LifetimeResearch.rawAdd retired L) m s).basis := by
  have pv : s.basis L.parity=(s.basis L.r0 ^^ s.basis (L.ylow.getD 0 0) ^^
      (s.basis L.sign ^^ carryValue false L.sign s.basis)) := by
    simpa [carryValue] using parityValue
  have h := rawAdd_withCarry false retired L hw hn member s m pv top clean
  have bound : regValue (GuardCompression.source L) s.basis<2^257 := by
    have len : (GuardCompression.source L).length=257 := by
      simp [GuardCompression.source,BalancedCleanup.Layout.y,hw.2.1]
    simpa only [len] using regValue_lt (GuardCompression.source L) s.basis
  simpa only [rawAddMode,Bool.false_eq_true,if_false,carryValue,
    signed_value_mod 257 _ _ _ bound] using h

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassRawTriple =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


/-- The seeded raw-add interface, with a frozen complete outsider state.
Only coherence and the seed relation refer to the representation; no
centered-word or canonical field-element premise enters the ripple proof. -/
def RawReady (L : Layout) (b : BasisState) : Prop :=
  b L.one=b L.rmsb ∧ b L.parity=(b L.r0 ^^ b (L.ylow.getD 0 0))
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompare =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


/-- Full-state contract for the exact lifetime comparator in either mode. -/
theorem compare_correct_order (exchange erase : Bool) (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m : List Bool)
    (one0 : s.basis L.one=false) (lower0 : s.basis L.lower=false)
    (clean : CleanExcept (L.carry.take 254) retired s.basis)
    (ready : s.basis L.parity=compareInput erase
      (decide (regValue (if exchange then L.r else L.y) s.basis<regValue (if exchange then L.y else L.r) s.basis))) :
    (run ((if exchange then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)) m s).phase=s.phase ∧
    (∀q,q≠L.parity → (run ((if exchange then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)) m s).basis q=s.basis q) ∧
    (run ((if exchange then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)) m s).basis L.parity=
      compareOutput erase (decide (regValue (if exchange then L.r else L.y) s.basis<regValue (if exchange then L.y else L.r) s.basis)) := by
  let A := if exchange then L.r else L.y
  let B := if exchange then L.y else L.r
  let cs := (Q6Structural.q6Carry L).take 255
  have shape : cs=L.carry.take 254++[L.lower] := active_carry_shape L hw
  have clen : cs.length=255 := by simp [shape,List.length_take,hw.2.2]
  have widths := BalancedCleanup.widths L.toLayout hw
  have alen : A.length=256 := by cases exchange <;> simp [A,widths.2.1,widths.2.2.1]
  have blen : B.length=256 := by cases exchange <;> simp [B,widths.2.1,widths.2.2.1]
  have split (xs : List Wire) (nonempty : 0<xs.length) : xs=xs.getD 0 0::xs.drop 1 := by
    cases xs with
    | nil => simp at nonempty
    | cons a as => rfl
  have xsplit := split A (by rw [alen];omega)
  have ysplit := split B (by rw [blen];omega)
  have csplit := split cs (by rw [clen];omega)
  have member' : retired∈cs.drop 1 := by
    rw [shape,List.drop_append]
    exact List.mem_append_left _ member
  have nd : (L.parity::L.one::(A++B++cs)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have lim := (List.take_sublist 254 L.carry).count_le q
    rw [shape]
    cases exchange <;> simp only [A,B,Bool.false_eq_true,if_false,if_true,
      BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h ⊢ <;> omega
  have clean' : CleanExcept cs retired s.basis := by
    intro q hq qr
    rw [shape,List.mem_append,List.mem_singleton] at hq
    rcases hq with hq|rfl
    · exact clean q hq qr
    · exact lower0
  have nd' : (L.parity::L.one::((A.getD 0 0::A.drop 1)++
      (B.getD 0 0::B.drop 1)++cs.getD 0 0::cs.drop 1)).Nodup := by
    simpa only [←xsplit,←ysplit,←csplit] using nd
  have h := compare_window erase (A.drop 1) (B.drop 1) (cs.drop 1)
    (A.getD 0 0) (B.getD 0 0) L.one (cs.getD 0 0) L.parity retired nd'
    (by simp [List.length_drop,alen,blen])
    (by simp [List.length_drop,blen,clen]) member' s m one0
    (by simpa only [←csplit] using clean')
    (by simpa only [←xsplit,←ysplit] using ready)
  have wholeR := split L.r (by rw [widths.2.1];omega)
  have wholeY := split L.y (by rw [widths.2.2.1];omega)
  cases exchange
  all_goals
    dsimp only [A,B] at xsplit ysplit h
    simpa only [P1Life.compare,Q6LifetimeResearch.compare,Q6LifetimeResearch.move,
      Bool.false_eq_true,if_false,if_true,←wholeR,←wholeY,
      List.cons_append,List.singleton_append,List.nil_append,List.append_assoc,cs] using h
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassComparePrepare =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


def compareInsert (oddMode : Bool) (L : BalancedCleanup.Layout) : Program :=
  if oddMode then [.X L.r0,.CX L.lower L.r0]
  else [.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0]


def comparePrepareMode (oddMode : Bool) (L : BalancedCleanup.Layout) : Program :=
  rotateLeft L.r++compareInsert oddMode L++signComplement L.sign L.y++
    signComplement L.lower L.y++[.X L.rmsb,.X L.ymsb]


def compareInsertValue (oddMode B N : Bool) : Bool := if oddMode then !N else !(B ^^ N)

def compareLeftValue (oddMode B N : Bool) (u : Int) : Int :=
  2*u+((compareInsertValue oddMode B N).toNat : Int)

def compareViewedValue (B N : Bool) (Y : Int) : Int := if B ^^ N then -Y-1 else Y


theorem prepare_compare_value_mode (oddMode : Bool) (L : BalancedCleanup.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (u Y : Int) (B N : Bool)
    (hu : -((2^254 : Nat) : Int)≤u ∧ u<((2^254 : Nat) : Int))
    (hy : -((2^255 : Nat) : Int)≤Y ∧ Y<((2^255 : Nat) : Int)) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 255 u) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hL : s.basis L.lower=N) :
    let t := run (comparePrepareMode oddMode L) m s
    (regValue L.r t.basis : Int)=compareLeftValue oddMode B N u+((2^255 : Nat) : Int) ∧
    (regValue L.y t.basis : Int)=compareViewedValue B N Y+((2^255 : Nat) : Int) ∧
    ∀q,q∉L.r → q∉L.y → t.basis q=s.basis q := by
  let U := encodeWord 255 (u)
  let v1 := run (rotateLeft L.r) m s
  let ins := compareInsert oddMode L
  let v2 := run ins m v1
  let v3 := run (signComplement L.sign L.y) m v2
  let v4 := run (signComplement L.lower L.y) m v3
  let v5 := run [.X L.rmsb] m v4
  let v6 := run [.X L.ymsb] m v5
  have w := BalancedCleanup.widths L hw
  have d := List.nodup_append'.mp (L.dataND hn)
  have dr := d.1
  have dy := (List.nodup_append'.mp d.2.1).1
  have dis := d.2.2
  have away (q : Wire) (hq : q∈[L.sign,L.lower]) : q∉L.r ∧ q∉L.y := by
    have a := L.flagAway hn q (by simp only [List.mem_cons] at hq ⊢; itauto)
    exact ⟨fun h => a (by simp [h]),fun h => a (by simp [h])⟩
  have r0R : L.r0∈L.r := by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
  have rmR : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have ymY : L.ymsb∈L.y := by simp [BalancedCleanup.Layout.y]
  have r0Y : L.r0∉L.y := fun h => List.disjoint_left.mp dis r0R (by simp [h])
  have rmY : L.rmsb∉L.y := fun h => List.disjoint_left.mp dis rmR (by simp [h])
  have ymR : L.ymsb∉L.r := fun h => List.disjoint_left.mp dis h (by simp [ymY])
  have sr : L.sign≠L.r0 := fun e => (away _ (by simp)).1 (e ▸ r0R)
  have lr : L.lower≠L.r0 := fun e => (away _ (by simp)).1 (e ▸ r0R)
  have rot0 := rotateLeft_spec L.r dr U (by have hu := encodeWord_bound 255 (u); rw [w.2.1]; norm_num at ⊢; omega) s m hR
  have rot := rot0.2
  have rotfr := (rotate_frame L.r s m).2.2.2
  have S1 : v1.basis L.sign=B := (rotfr _ (away _ (by simp)).1).trans hS
  have L1 : v1.basis L.lower=N := (rotfr _ (away _ (by simp)).1).trans hL
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
  have I2 : v2.basis L.r0=compareInsertValue oddMode B N := by
    cases oddMode <;> cases b : B <;> cases l : N <;>
      simp [v2,ins,compareInsert,compareInsertValue,run,writeBit,sr,lr,S1,L1,low0,b,l]
  have out2 (q : Wire) (hq : q≠L.r0) : v2.basis q=v1.basis q := by cases oddMode <;> simp [v2,ins,compareInsert,run,writeBit,hq]
  have S2 : v2.basis L.sign=B := (out2 _ sr).trans S1
  have L2 : v2.basis L.lower=N := (out2 _ lr).trans L1
  have tailAway : L.r0∉L.rtail++[L.rmsb] := (List.nodup_cons.mp dr).1
  have R2 : regValue L.r v2.basis=encodeWord 256 (compareLeftValue oddMode B N u) := by
    change (if v2.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v2.basis=_
    rw [regValue_congr _ _ _ (fun q hq => out2 q (fun e => tailAway (e ▸ hq))),tail1,I2]
    rw [compareLeftValue,BalancedCleanup.doubled_encoded]
    cases e : compareInsertValue oddMode B N <;> simp [U,e,Bool.toNat,Nat.add_comm]
  have Y2 : regValue L.y v2.basis=encodeWord 256 Y := by
    exact (regValue_congr _ _ _ (fun q hq => (out2 q (fun e => r0Y (e ▸ hq))).trans
      (rotfr q (fun hrq => List.disjoint_left.mp dis hrq (by simp [hq]))))).trans hY
  have cS := signComplement_correct L.sign L.y dy (away _ (by simp)).2 v2 m
  have cL := signComplement_correct L.lower L.y dy (away _ (by simp)).2 v3 m
  have L3 : v3.basis L.lower=N := (cS.2.1 _ (away _ (by simp)).2).trans L2
  have R4 : regValue L.r v4.basis=encodeWord 256 (compareLeftValue oddMode B N u) := by
    exact (regValue_congr _ _ _ (fun q hq => (cL.2.1 q
      (fun hyq => List.disjoint_left.mp dis hq (by simp [hyq]))).trans (cS.2.1 q
      (fun hyq => List.disjoint_left.mp dis hq (by simp [hyq]))))).trans R2
  have Y4 : regValue L.y v4.basis=encodeWord 256 (compareViewedValue B N Y) := by
    rw [cL.2.2,cS.2.2,L3,S2,Y2,w.2.2.1]
    have hb := encodeWord_bound 256 Y
    have comp := BalancedCleanup.complement_encoded Y
    cases B <;> cases l : N <;> simp [compareViewedValue,l] <;> omega
  have leftRange : -((2^255 : Nat) : Int)≤compareLeftValue oddMode B N u ∧
      compareLeftValue oddMode B N u<((2^255 : Nat) : Int) := by
    cases e : compareInsertValue oddMode B N <;> simp [compareLeftValue,e] <;>
      norm_num only [Nat.reducePow] at hu ⊢ <;> omega
  have sourceRange : -((2^255 : Nat) : Int)≤compareViewedValue B N Y ∧
      compareViewedValue B N Y<((2^255 : Nat) : Int) := by
    cases B <;> cases N <;> simp [compareViewedValue] <;> omega
  have decoded := And.intro
    (decode_encodeWord 256 (by decide) _ leftRange)
    (decode_encodeWord 256 (by decide) _ sourceRange)
  have bvR := BalancedCleanup.bias_value L.low L.rmsb dr v4 m
  have bvY := BalancedCleanup.bias_value L.ylow L.ymsb dy v5 m
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
  have execute : run (comparePrepareMode oddMode L) m s=v6 := by
    cases oddMode <;> simp only [comparePrepareMode,compareInsert,Bool.false_eq_true,if_false,if_true,List.append_assoc,run_append,
      (rotate_counts L.r).2.2.2,(signComplement_counts L.sign L.y).2,
      (signComplement_counts L.lower L.y).2,measurementCount,List.drop_zero,emptyRot,emptyS,emptyL]
    all_goals rfl
  rw [execute]
  refine ⟨by rw [R6]; exact bvR,bvY,?_⟩
  intro q qr qy
  have nr : q≠L.r0 := fun e => qr (e ▸ r0R)
  have nm : q≠L.rmsb := fun e => qr (e ▸ rmR)
  have ny : q≠L.ymsb := fun e => qy (e ▸ ymY)
  have v56 : v6.basis q=v4.basis q := by simp [v6,v5,run,writeBit,nm,ny]
  exact v56.trans ((cL.2.1 q qy).trans ((cS.2.1 q qy).trans ((out2 q nr).trans (rotfr q qr))))


theorem prepare_compare_low_mode (oddMode : Bool) (L : BalancedCleanup.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (u Y : Int) (B N : Bool)
    (hu : -((2^254 : Nat) : Int)≤u ∧ u<((2^254 : Nat) : Int))
    (hy : -((2^255 : Nat) : Int)≤Y ∧ Y<((2^255 : Nat) : Int)) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 255 u) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hL : s.basis L.lower=N) :
    (run (comparePrepareMode oddMode L) m s).basis L.r0=compareInsertValue oddMode B N := by
  have h := (prepare_compare_value_mode oddMode L hw hn u Y B N hu hy s m hR hY hS hL).1
  change (((if (run (comparePrepareMode oddMode L) m s).basis L.r0 then 1 else 0)+
    2*regValue (L.rtail++[L.rmsb]) (run (comparePrepareMode oddMode L) m s).basis : Nat) : Int)=_ at h
  cases e : compareInsertValue oddMode B N <;>
    cases bit : (run (comparePrepareMode oddMode L) m s).basis L.r0
  all_goals simp only [compareLeftValue,e,bit,Bool.toNat_false,Bool.toNat_true,
    Bool.false_eq_true,if_false,if_true,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at h ⊢
  all_goals norm_num only [Nat.reducePow] at h
  all_goals first | rfl | omega

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareModes =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


def compareExposeMode (oddMode : Bool) (L : Layout) : Program :=
  if oddMode then P1Life.exposure L else Q6StructuralCell.exposure L


def comparisonPredicate (oddMode B N : Bool) (u Y : Int) : Bool :=
  if oddMode then decide (compareLeftValue oddMode B N u<compareViewedValue B N Y)
  else decide (compareViewedValue B N Y<compareLeftValue oddMode B N u)


theorem prepare_compare_proper_mode (oddMode : Bool) (L : BalancedCleanup.Layout) (hn : L.wires.Nodup) :
    ProperProgram (comparePrepareMode oddMode L) := by
  have ndR := (List.nodup_append'.mp (L.dataND hn)).1
  have sY : L.sign∉L.y := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have lY : L.lower∉L.y := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have sR : L.sign∉L.r := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have lR : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have sr : L.sign≠L.r0 := fun e => sR (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e])
  have lr : L.lower≠L.r0 := fun e => lR (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e])
  simp only [comparePrepareMode,properProgram_append]
  refine ⟨⟨⟨⟨BalancedCleanup.rotateLeft_proper _ ndR,?_⟩,BalancedCleanup.complement_proper _ _ sY⟩,
    BalancedCleanup.complement_proper _ _ lY⟩,by simp [ProperProgram,ProperGate]⟩
  cases oddMode <;> simp [compareInsert,ProperProgram,ProperGate,sr,lr]


theorem prepare_compare_parity_free (oddMode : Bool) (L : BalancedCleanup.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) : L.parity∉wires (comparePrepareMode oddMode L) := by
  have old := (BalancedCleanup.clifford_parity_away L hw hn).2
  intro bad
  apply old
  have subset : wires (comparePrepareMode oddMode L)⊆wires (BalancedCleanup.prepareCompare L) := by
    intro q hq
    cases oddMode <;>
      simp only [comparePrepareMode,compareInsert,BalancedCleanup.prepareCompare,Bool.false_eq_true,
        if_false,if_true,wires_append,Finset.mem_union,wires,Instr.wires,List.foldr_cons,List.foldr_nil,
        Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq ⊢ <;> itauto
  exact subset bad


theorem expose_correct_mode (oddMode : Bool) (L : Layout) (sl : L.sign≠L.lower) (rl : L.r0≠L.lower)
    (s : State) (m : List Bool) (B N : Bool) (sign : s.basis L.sign=B) (lower : s.basis L.lower=N)
    (ready : s.basis L.r0=compareInsertValue oddMode B N) :
    (run (compareExposeMode oddMode L) m s).phase=s.phase ∧
    (run (compareExposeMode oddMode L) m s).basis L.lower=false ∧
    ∀q,q≠L.lower → (run (compareExposeMode oddMode L) m s).basis q=s.basis q := by
  cases oddMode
  · apply Q6LowerExposure.expose_correct L.sign L.lower L.r0 sl rl s m
    simpa [compareInsertValue,sign,lower] using ready
  · refine ⟨rfl,?_,?_⟩
    · cases B <;> cases N <;>
        simp_all [compareExposeMode,P1Life.exposure,compareInsertValue,run,writeBit]
    · intro q hq
      simp [compareExposeMode,P1Life.exposure,run,writeBit,hq]

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareView =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


theorem zero_records (p : Program) (zero : measurementCount p=0)
    (s : State) (m : List Bool) : run p m s=run p [] s := by
  rw [←run_take p m s,zero,List.take_zero]


/-- Prepare the signed interval view, expose lower as a clean carry, run
the exact comparator, and undo both views. The only changed bit is parity. -/
theorem comparison_sandwich_mode (oddMode erase : Bool) (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (U Y : Int) (B N : Bool)
    (hu : -((2^254 : Nat) : Int)≤U ∧ U<((2^254 : Nat) : Int))
    (hy : -((2^255 : Nat) : Int)≤Y ∧ Y<((2^255 : Nat) : Int))
    (s : State) (m : List Bool) (rv : regValue L.r s.basis=encodeWord 255 U)
    (yv : regValue L.y s.basis=encodeWord 256 Y) (sign : s.basis L.sign=B) (lower : s.basis L.lower=N)
    (one : s.basis L.one=false) (clean : CleanExcept (L.carry.take 254) retired s.basis)
    (ready : s.basis L.parity=compareInput erase (comparisonPredicate oddMode B N U Y)) :
    let front := comparePrepareMode oddMode L.toLayout++compareExposeMode oddMode L
    let cell := front++(if oddMode then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)++front.reverse
    BalancedCleanup.Except L.parity (run cell m s) s ∧
    (run cell m s).basis L.parity=compareOutput erase (comparisonPredicate oddMode B N U Y) := by
  have n0 : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have nd : [L.sign,L.lower,L.r0,L.parity].Nodup := by
    apply List.nodup_iff_count.mpr
    intro x
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) x
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ne := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ne
  have flagsAway (x : Wire) (hx : x∈[L.parity,L.lower,L.one]++L.carry) :
      x∉L.r ∧ x∉L.y := by
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) x
    have pos := List.count_pos_iff.mpr hx
    simp only [List.count_cons,List.count_append,List.count_nil] at pos
    constructor <;> intro bad
    all_goals
      have p := List.count_pos_iff.mpr bad
      simp only [List.count_cons,List.count_append] at h
      omega
  have lowerAway (x : Wire) (hx : x∈[L.parity,L.one]++L.carry) : x≠L.lower := by
    intro e
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) x
    have p := List.count_pos_iff.mpr hx
    subst x
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h p
    omega
  let prep := comparePrepareMode oddMode L.toLayout
  let expose := compareExposeMode oddMode L
  let front := prep++expose
  have prepProper := prepare_compare_proper_mode oddMode L.toLayout n0
  have exposeProper : ProperProgram expose := by
    cases oddMode <;>
      simp [expose,compareExposeMode,P1Life.exposure,Q6StructuralCell.exposure,Q6LowerExposure.expose,
        ProperProgram,ProperGate,ne_comm,ne] <;> exact Ne.symm ne.2.1.1
  have proper : ProperProgram front := (properProgram_append _ _).mpr ⟨prepProper,exposeProper⟩
  have zero : measurementCount front=0 := properProgram_measurementCount front proper
  have prep0 : measurementCount prep=0 := properProgram_measurementCount prep prepProper
  have expose0 : measurementCount expose=0 := by cases oddMode <;> rfl
  have free : L.parity∉wires front := by
    have p := prepare_compare_parity_free oddMode L.toLayout hw n0
    simp only [front,wires_append,Finset.mem_union,not_or]
    refine ⟨p,?_⟩
    cases oddMode <;>
      simp [expose,compareExposeMode,P1Life.exposure,Q6StructuralCell.exposure,Q6LowerExposure.expose,
        wires,Instr.wires,ne_comm,ne] <;> exact Ne.symm ne.2.1.2
  let u := run prep [] s
  let v := run expose [] u
  have fv : run front [] s=v := by
    rw [run_append,run_take,prep0,List.drop_zero]
  have values := prepare_compare_value_mode oddMode L.toLayout hw n0 U Y B N hu hy s [] rv yv sign lower
  have relation := prepare_compare_low_mode oddMode L.toLayout hw n0 U Y B N hu hy s [] rv yv sign lower
  have signFree := L.toLayout.flagAway n0 L.sign (by simp)
  have usign : u.basis L.sign=B := (values.2.2 L.sign
    (fun bad => signFree (by simp [bad])) (fun bad => signFree (by simp [bad]))).trans sign
  have ulower : u.basis L.lower=N := (values.2.2 L.lower
    (flagsAway _ (by simp)).1 (flagsAway _ (by simp)).2).trans lower
  have exposeValue := expose_correct_mode oddMode L ne.1.1 (Ne.symm ne.2.1.1) u [] B N usign ulower relation
  have vkeep (x : Wire) (hx : x≠L.lower) : v.basis x=u.basis x := exposeValue.2.2 x hx
  have pkeep (x : Wire) (hx : x∈[L.parity,L.lower,L.one]++L.carry) : u.basis x=s.basis x :=
    values.2.2 x (flagsAway x hx).1 (flagsAway x hx).2
  have noLowerData (x : Wire) (hx : x∈L.r++L.y) : x≠L.lower := by
    intro e
    have a := flagsAway L.lower (by simp)
    rcases List.mem_append.mp hx with h|h
    · exact a.1 (e ▸ h)
    · exact a.2 (e ▸ h)
  have vr : (regValue L.r v.basis : Int)=compareLeftValue oddMode B N U+((2^255 : Nat) : Int) := by
    rw [regValue_congr L.r v.basis u.basis
      (fun x hx => vkeep x (noLowerData x (by simp [hx])))]
    exact values.1
  have vy : (regValue L.y v.basis : Int)=compareViewedValue B N Y+((2^255 : Nat) : Int) := by
    rw [regValue_congr L.y v.basis u.basis
      (fun x hx => vkeep x (noLowerData x (by simp [hx])))]
    exact values.2.1
  have pred : decide (regValue (if oddMode then L.r else L.y) v.basis<
      regValue (if oddMode then L.y else L.r) v.basis)=comparisonPredicate oddMode B N U Y := by
    cases oddMode <;> simp only [comparisonPredicate,Bool.false_eq_true,if_false,if_true] <;>
      apply decide_eq_decide.mpr <;> omega
  have cmp := compare_correct_order oddMode erase retired L hw hn member v m
    ((vkeep L.one (lowerAway _ (by simp))).trans ((pkeep _ (by simp)).trans one)) exposeValue.2.1
    (by
      intro x hx xr
      have hc := List.mem_of_mem_take hx
      rw [vkeep x (lowerAway _ (by simp [hc])),pkeep x (by simp [hc])]
      exact clean x hx xr)
    (by rw [pred,vkeep L.parity (lowerAway _ (by simp)),pkeep L.parity (by simp)];exact ready)
  let t := run ((if oddMode then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)) m v
  have back (r : List Bool) := BalancedCleanup.inverse_except front proper L.parity free s t [] r
    (by rw [fv];exact ⟨cmp.1,cmp.2.1⟩)
  have execute : run (front++(if oddMode then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)++front.reverse) m s=
      run front.reverse (m.drop (measurementCount ((if oddMode then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)))) t := by
    rw [run_append,run_take,run_append,run_take,measurementCount_append,zero,Nat.zero_add,
      List.drop_zero,zero_records front zero,fv]
  change BalancedCleanup.Except L.parity
    (run (front++(if oddMode then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)++front.reverse) m s) s ∧ _
  rw [execute]
  refine ⟨back (m.drop (measurementCount ((if oddMode then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)))),?_⟩
  exact (run_preserves_outside front.reverse
    (m.drop (measurementCount ((if oddMode then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)))) t L.parity
    (by rw [wires_reverse];exact free)).trans
      (cmp.2.2.trans (congrArg (compareOutput erase) pred))


theorem standard_comparison_predicate (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    comparisonPredicate false B (negative R) (normalizedR R) Y=decide (q < |2*R-signedY B Y|) := by
  have left : compareLeftValue false B (negative R) (normalizedR R)=comparisonLeft B R := by
    cases B <;> cases n : negative R <;>
      simp [compareLeftValue,compareInsertValue,comparisonLeft,insertBit,n]
  simp only [comparisonPredicate,Bool.false_eq_true,if_false,left]
  exact decide_eq_decide.mpr (cleanup_interval_identity B R Y hr hy).symm
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFoldView =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


/-- The biased fold has already paid for normalization; prepareSign and
one high-low-word X expose the standard normalized comparison boundary. -/
theorem fold_view_values (E : HalfEncoding) (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (origin : BasisState) (T R Y : Int) (V : Nat)
    (bound : E.normalized R<2^255)
    (prepareValue : ∀(s : State)(m : List Bool),regValue L.r s.basis=E.folded R → s.basis L.lower=false →
      let u := run (BalancedCleanup.prepareSign L.toLayout) m s
      u.phase=s.phase ∧ regValue L.r u.basis=V ∧ u.basis L.lower=E.negative R ∧
      ∀q,q∉L.r → q≠L.lower → u.basis q=s.basis q)
    (flipValue : ∀(s : State)(m : List Bool),regValue L.r s.basis=V →
      regValue L.r (run (BiasedCircuit.flipBias L) m s).basis=E.normalized R) :
    Triple (AfterFold E L retired origin T R Y)
      (BalancedCleanup.prepareSign L.toLayout++BiasedCircuit.flipBias L)
      (InverseComparison E L retired origin T R Y) := by
  have width := BalancedCleanup.widths L.toLayout hw
  have dataND := List.nodup_append'.mp
    (L.toLayout.dataND (List.nodup_append'.mp hn).2.1)
  have away (x : Wire) (hx : x∈[L.parity,L.one,L.lower]++L.y++L.carry) : x∉L.r := by
    intro bad
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) x
    have p := List.count_pos_iff.mpr hx
    have r := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append,List.count_nil] at h p
    omega
  have lowerAway (x : Wire) (hx : x∈[L.parity,L.one]++L.y++L.carry) : x≠L.lower := by
    intro e
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) x
    have p := List.count_pos_iff.mpr hx
    subst x
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h p
    omega
  have flipIn : L.rtail.getD 253 0∈L.r := by
    have bound : 253<L.rtail.length := by rw [hw.1];omega
    rw [List.getD_eq_getElem _ _ bound]
    simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.getElem_mem]
  intro s m hs
  rcases hs with ⟨value,ys,flags,clean,frame⟩
  rcases flags with ⟨parity,lower,one⟩
  let u := run (BalancedCleanup.prepareSign L.toLayout) [] s
  let v := run (BiasedCircuit.flipBias L) [] u
  have prep := prepareValue s [] value lower
  have fv := flipValue u [] prep.2.1
  have fk (x : Wire) (hx : x∉L.r) : v.basis x=u.basis x := by
    simp only [v,BiasedCircuit.flipBias,run,writeBit,
      Function.update_of_ne (show x≠L.rtail.getD 253 0 from fun e => hx (e ▸ flipIn))]
  have keep (x : Wire) (hx : x∈[L.parity,L.one]++L.y++L.carry) : v.basis x=s.basis x :=
    (fk x (away x (by simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hx ⊢;itauto))).trans
      (prep.2.2.2 x (away x (by simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hx ⊢;itauto))
        (lowerAway x hx))
  have top0 : v.basis L.rmsb=false := by
    have h := regValue_highBit L.low L.rmsb v.basis
    change v.basis L.rmsb=true ↔ 2^L.low.length≤regValue L.r v.basis at h
    rw [width.1,fv] at h
    have fit := bound
    cases e : v.basis L.rmsb <;> simp_all <;> omega
  have low : regValue L.low v.basis=E.normalized R := by
    have h := fv
    change regValue (L.low++[L.rmsb]) v.basis=_ at h
    rw [regValue_append] at h
    simpa [regValue,top0] using h
  have prep0 := properProgram_measurementCount _
    (BalancedCleanup.prepareSign_proper L.toLayout (List.nodup_append'.mp hn).2.1)
  have last (r : List Bool) : run (BiasedCircuit.flipBias L) r u=v := rfl
  rw [run_append,run_take,prep0,List.drop_zero,zero_records _ prep0,last]
  refine ⟨prep.1,low,top0,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun x hx => keep x (by simp [hx]))).trans ys
  · exact ⟨(keep _ (by simp)).trans parity,(fk _ (away _ (by simp))).trans prep.2.2.1,
      (keep _ (by simp)).trans one⟩
  · intro x hx xr
    exact (keep x (by simp [List.mem_of_mem_take hx])).trans (clean x hx xr)
  · intro x hx hp hl ho
    exact (fk x hx).trans ((prep.2.2.2 x hx hl).trans (frame x hx hp hl ho))


theorem fold_view (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (origin : BasisState) (T R Y : Int) (hr : Centered R) :
    Triple (AfterFold standardEncoding L retired origin T R Y)
      (BalancedCleanup.prepareSign L.toLayout++BiasedCircuit.flipBias L)
      (InverseComparison standardEncoding L retired origin T R Y) := by
  apply fold_view_values standardEncoding retired L hw hn origin T R Y (|R|+(BiasedCircuit.jh : Int)).toNat
    (encodeWord_bound 255 (normalizedR R))
  · intro s m value lower
    have code : regValue L.r s.basis=encodeWord 256 (BiasedCircuit.biasedValue R) := by
      simpa [standardEncoding,BiasedCircuit.biasedValue,negative] using value
    exact BiasedCircuit.prepareSign_biased L hw hn R hr s m code lower
  · intro s m value
    exact BiasedCircuit.flipBias_value L hw hn R hr s m value

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassLowFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


def LowBoundary (L : Layout) (retired : Wire) (origin : BasisState)
    (v Y : Nat) (P N : Bool) (b : BasisState) : Prop :=
  regValue L.low b=v ∧ b L.rmsb=false ∧ regValue L.y b=Y ∧
  LiveFlags L P N false b ∧ CleanExcept (L.carry.take 254) retired b ∧ HalfOutside L origin b


def WordBoundary (L : Layout) (retired : Wire) (origin : BasisState)
    (v Y : Nat) (P : Bool) (b : BasisState) : Prop :=
  regValue L.r b=v ∧ regValue L.y b=Y ∧ LiveFlags L P false false b ∧
  CleanExcept (L.carry.take 254) retired b ∧ HalfOutside L origin b


theorem low_frame_of_word (L : Layout) (hn : L.wires.Nodup) (retired : Wire)
    (origin : BasisState) (v u Y : Nat) (P N : Bool) (program : Program) (s : State) (m : List Bool)
    (input : LowBoundary L retired origin v Y P N s.basis)
    (h : (run program m s).phase=s.phase ∧ WordFrame L.low s.basis u (run program m s).basis) :
    (run program m s).phase=s.phase ∧ LowBoundary L retired origin u Y P N (run program m s).basis := by
  have away (q : Wire) (hq : q∈[L.rmsb,L.one,L.lower,L.parity]++L.y++L.carry) : q∉L.low := by
    intro bad
    have n := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at n a
    omega
  rcases input with ⟨value,host,ys,⟨parity,lower,one⟩,clean,frame⟩
  refine ⟨h.1,h.2.1,?_,?_,?_,?_,?_⟩
  · exact (h.2.2 _ (away _ (by simp))).trans host
  · exact (regValue_congr _ _ _ (fun q hq => h.2.2 q (away q (by simp [hq])))).trans ys
  · exact ⟨(h.2.2 _ (away _ (by simp))).trans parity,
      (h.2.2 _ (away _ (by simp))).trans lower,(h.2.2 _ (away _ (by simp))).trans one⟩
  · intro q hq qr
    exact (h.2.2 q (away q (by simp [List.mem_of_mem_take hq]))).trans (clean q hq qr)
  · intro q hq hp hl ho
    exact (h.2.2 q (fun bad => hq (by simp [BalancedCleanup.Layout.r,bad]))).trans (frame q hq hp hl ho)


theorem encoded_add_nat (n : Nat) (z : Int) (k : Nat) :
    (encodeWord n z+k)%2^n=encodeWord n (z+(k : Int)) := by
  apply Int.ofNat_inj.mp
  simp only [Int.natCast_emod,Nat.cast_add,encodeWord_cast,Int.add_emod,Int.emod_emod]


theorem encoded_add_encoded (n : Nat) (z k : Int) :
    (encodeWord n z+encodeWord n k)%2^n=encodeWord n (z+k) := by
  apply Int.ofNat_inj.mp
  simp only [Int.natCast_emod,Nat.cast_add,encodeWord_cast,Int.add_emod,Int.emod_emod]

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


def ComparisonFrame (L : Layout) (retired : Wire) (origin : BasisState)
    (R Y : Int) (P : Bool) (b : BasisState) : Prop :=
  regValue L.low b=encodeWord 255 (normalizedR R) ∧ b L.rmsb=false ∧
  regValue L.y b=encodeWord 256 Y ∧ LiveFlags L P (negative R) false b ∧
  CleanExcept (L.carry.take 254) retired b ∧ HalfOutside L origin b


theorem comparison_boundary_mode (oddMode erase : Bool) (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (U Y : Int) (N : Bool)
    (hu : -((2^254 : Nat) : Int)≤U ∧ U<((2^254 : Nat) : Int))
    (hy : -((2^255 : Nat) : Int)≤Y ∧ Y<((2^255 : Nat) : Int)) :
    let answer := comparisonPredicate oddMode (origin L.sign) N U Y
    Triple (LowBoundary L retired origin (encodeWord 255 U) (encodeWord 256 Y) (compareInput erase answer) N)
      (comparePrepareMode oddMode L.toLayout++compareExposeMode oddMode L++
        (if oddMode then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)++
        (compareExposeMode oddMode L).reverse++(comparePrepareMode oddMode L.toLayout).reverse)
      (LowBoundary L retired origin (encodeWord 255 U) (encodeWord 256 Y) (compareOutput erase answer) N) := by
  dsimp only
  have notParity (x : Wire) (hx : x∈L.r++L.y++[L.lower,L.one]++L.carry) : x≠L.parity := by
    intro e
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) x
    have p := List.count_pos_iff.mpr hx
    subst x
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h p
    omega
  have signND : [L.sign,L.parity,L.lower,L.one].Nodup := by
    apply List.nodup_iff_count.mpr
    intro x
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) x
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have sn := (List.nodup_cons.mp signND).1
  have signAway : L.sign∉L.r := fun h => BalancedCircuit.flagAway L hn L.sign (by simp) (by simp [h])
  intro s m hs
  rcases hs with ⟨low,top,ys,flags,clean,frame⟩
  rcases flags with ⟨parity,lower,one⟩
  have value : regValue L.r s.basis=encodeWord 255 U := by
    change regValue (L.low++[L.rmsb]) s.basis=_
    rw [regValue_append,low]
    simp [regValue,top]
  have sign : s.basis L.sign=origin L.sign := frame L.sign signAway
    (fun e => sn (by simp [e])) (fun e => sn (by simp [e])) (fun e => sn (by simp [e]))
  have h := comparison_sandwich_mode oddMode erase retired L hw hn member U Y (origin L.sign) N hu hy
    s m value ys sign lower one clean parity
  simp only [List.reverse_append,List.append_assoc] at h
  simp only [List.append_assoc]
  refine ⟨h.1.1,?_,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun x hx => h.1.2 x (notParity x (by
      simp [BalancedCleanup.Layout.r,hx])))).trans low
  · exact (h.1.2 _ (notParity _ (by simp [BalancedCleanup.Layout.r]))).trans top
  · exact (regValue_congr _ _ _ (fun x hx => h.1.2 x (notParity x (by simp [hx])))).trans ys
  · exact ⟨h.2,(h.1.2 _ (notParity _ (by simp))).trans lower,
      (h.1.2 _ (notParity _ (by simp))).trans one⟩
  · intro x hx xr
    exact (h.1.2 x (notParity x (by simp [List.mem_of_mem_take hx]))).trans (clean x hx xr)
  · intro x hx hp hl ho
    exact (h.1.2 x hp).trans (frame x hx hp hl ho)


theorem comparison_boundary (erase : Bool) (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    let answer := decide (q < |2*R-signedY (origin L.sign) Y|)
    Triple (ComparisonFrame L retired origin R Y (compareInput erase answer))
      (BalancedCleanup.prepareCompare L.toLayout++Q6StructuralCell.exposure L++
        Q6LifetimeResearch.compare retired erase L++(Q6StructuralCell.exposure L).reverse++
        (BalancedCleanup.prepareCompare L.toLayout).reverse)
      (ComparisonFrame L retired origin R Y (compareOutput erase answer)) := by
  have hp := constants
  have ur := normalizedR_bounds R hr
  have hu : -((2^254 : Nat) : Int)≤normalizedR R ∧ normalizedR R<((2^254 : Nat) : Int) := by omega
  have yr : -((2^255 : Nat) : Int)≤Y ∧ Y<((2^255 : Nat) : Int) := by unfold Centered at hy; omega
  have h := comparison_boundary_mode false erase retired L hw hn member origin (normalizedR R) Y (negative R) hu yr
  dsimp only at h ⊢
  rw [standard_comparison_predicate (origin L.sign) R Y hr hy] at h
  simpa only [ComparisonFrame,LowBoundary,comparePrepareMode,compareInsert,compareExposeMode,
    BalancedCleanup.prepareCompare,Bool.false_eq_true,if_false] using h


/-- Unit 2 forward: the original parity equals the signed interval test. -/
theorem fold_to_comparison (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (X Y : Int) (hx : Centered X) (hy : Centered Y) :
    let T := rawSum (origin L.sign) X Y
    Triple (AfterFold standardEncoding L retired origin T (halfResult T) Y)
      (BalancedCleanup.prepareSign L.toLayout++BiasedCircuit.flipBias L++
        BalancedCleanup.prepareCompare L.toLayout++Q6StructuralCell.exposure L++
        Q6LifetimeResearch.compare retired true L++(Q6StructuralCell.exposure L).reverse++
        (BalancedCleanup.prepareCompare L.toLayout).reverse)
      (AfterComparison standardEncoding L retired origin (halfResult T) Y) := by
  let T := rawSum (origin L.sign) X Y
  have hr := (halfResult_spec T (rawSum_bounds _ X Y hx hy)).1
  have interval : originalParity T=decide (q < |2*halfResult T-signedY (origin L.sign) Y|) := by
    apply decide_eq_decide.mpr
    exact halfResult_parity_interval _ X Y hx hy
  have b := comparison_boundary true retired L hw hn member origin (halfResult T) Y hr hy
  simp only [compareInput,compareOutput,if_true,←interval] at b
  simpa only [List.append_assoc,ComparisonFrame,InverseComparison,AfterComparison,standardEncoding,
    negative] using Triple.seq (fold_view retired L hw hn origin T (halfResult T) Y hr) b

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassUnbias =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


/-- Exact Clifford inverse view, preserving the computed parity and all
caller history outside the payload and the released sign selector. -/
theorem unbias_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (origin : BasisState) (T R Y : Int) (hr : Centered R) :
    Triple (InverseComparison standardEncoding L retired origin T R Y)
      (BiasedInverse.unbiasView L) (AfterFold standardEncoding L retired origin T R Y) := by
  have away (x : Wire) (hx : x∈[L.parity,L.one]++L.y++L.carry) : x∉L.r ∧ x≠L.lower := by
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) x
    have p := List.count_pos_iff.mpr hx
    simp only [List.count_cons,List.count_append,List.count_nil] at p
    refine ⟨?_,?_⟩
    · intro bad
      have r := List.count_pos_iff.mpr bad
      simp only [List.count_cons,List.count_append] at h
      omega
    · intro e
      subst x
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  intro s m hs
  rcases hs with ⟨low,top,ys,flags,clean,frame⟩
  rcases flags with ⟨parity,lower,one⟩
  have value : regValue L.r s.basis=encodeWord 255 (normalizedR R) := by
    change regValue (L.low++[L.rmsb]) s.basis=_
    rw [regValue_append,low]
    simp [regValue,top,standardEncoding]
  have h := BiasedInverse.unbiasView_correct L hw (List.nodup_append'.mp hn).2.1 R hr s m value lower
  have keep (x : Wire) (hx : x∈[L.parity,L.one]++L.y++L.carry) :
      (run (BiasedInverse.unbiasView L) m s).basis x=s.basis x :=
    h.2.2.2 x (away x hx).1 (away x hx).2
  refine ⟨h.1,?_,?_,?_,?_,?_⟩
  · simpa [standardEncoding,BiasedInverse.biased,BiasedInverse.halfBias,BiasedCircuit.jh] using h.2.1
  · exact (regValue_congr _ _ _ (fun x hx => keep x (by simp [hx]))).trans ys
  · exact ⟨(keep _ (by simp)).trans parity,h.2.2.1,(keep _ (by simp)).trans one⟩
  · intro x hx xr
    exact (keep x (by simp [List.mem_of_mem_take hx])).trans (clean x hx xr)
  · intro x hx hp hl ho
    exact (h.2.2.2 x hx hl).trans (frame x hx hp hl ho)


/-- Unit 2 inverse: compute the interval bit, restore the comparison view,
then expose the biased word for unfold. -/
theorem comparison_to_fold (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (T R Y : Int) (hr : Centered R) (hy : Centered Y)
    (interval : originalParity T=decide (q < |2*R-signedY (origin L.sign) Y|)) :
    Triple (AfterComparison standardEncoding L retired origin R Y)
      (BalancedCleanup.prepareCompare L.toLayout++Q6StructuralCell.exposure L++
        Q6LifetimeResearch.compare retired false L++(Q6StructuralCell.exposure L).reverse++
        (BalancedCleanup.prepareCompare L.toLayout).reverse++BiasedInverse.unbiasView L)
      (AfterFold standardEncoding L retired origin T R Y) := by
  have b := comparison_boundary false retired L hw hn member origin R Y hr hy
  simp only [compareInput,compareOutput,Bool.false_eq_true,if_false,←interval] at b
  simpa only [List.append_assoc,ComparisonFrame,InverseComparison,AfterComparison,standardEncoding,
    negative] using Triple.seq b (unbias_boundary retired L hw hn origin T R Y hr)

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassDependent =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- Two equal high result bits, expressed entirely as a numeric predicate. -/
def Extended (n v : Nat) : Prop := v<2^n ∨ 3*2^n≤v


/-- A ripple step preserves the high-two-bit extension condition. -/
theorem extended_tail (A B C : Bool) (X Y n : Nat)
    (h : Extended (n+1) (((A.toNat+2*X)+(B.toNat+2*Y)+C.toNat)%2^(n+3))) :
    Extended n ((X+Y+(carryBit A B C).toNat)%2^(n+2)) := by
  have sum := sum_value_step A B C X Y (n+2)
  have low : (sumBit A B C).toNat≤1 := by cases sumBit A B C <;> decide
  have pow : n+2+1=n+3 := by omega
  rw [pow] at sum
  unfold Extended at h ⊢
  have step : 2^(n+1)=2*2^n := by rw [Nat.pow_succ,Nat.mul_comm]
  rw [←sum,step] at h
  omega


/-- Direct measured dependent top. This reuses only the generic four-wire
truth table, whose conclusion is an explicit State, not another program. -/
theorem dependent_top (a t z cin : Wire) (nd : [a,t,cin,z].Nodup)
    (s : State) (m : List Bool)
    (extended : Extended 0 ((regValue [a,a] s.basis+regValue [t,z] s.basis+
      (s.basis cin).toNat)%4)) :
    run (Q6LifetimeResearch.dependentTop a t cin z) m s=
      ⟨s.phase,writeBit (writeBit s.basis t (sumBit (s.basis a) (s.basis t) (s.basis cin)))
        z (sumBit (s.basis a) (s.basis t) (s.basis cin))⟩ := by
  have relation : s.basis z=(carryBit (s.basis a) (s.basis t) (s.basis cin) ^^
      s.basis t ^^ s.basis cin) := by
    cases ha : s.basis a <;> cases ht : s.basis t <;> cases hz : s.basis z <;>
      cases hc : s.basis cin <;> simp_all [Extended,regValue,carryBit]
  simpa only [Q6LifetimeResearch.dependentTop,C4Lifetime.dependentTop,
    C4Lifetime.eraseDependentTop,List.cons_append,List.nil_append,sumBit] using
    C4Lifetime.dependentTop_correct a t cin z nd s m relation

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassDependentPrefix =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


theorem dependent_cons (x y cs : List Wire) (a t z b d k cin : Wire) :
    Q6LifetimeResearch.addTop ((b::x)++[a,a]) ((d::y)++[t,z]) (k::cs) cin=
      majority b d cin k++Q6LifetimeResearch.addTop (x++[a,a]) (y++[t,z]) cs k++
        eraseCarry b d cin k++[.CX b d,.CX cin d] := by
  have two (xs : List Wire) (u v : Wire) : ∃ a b bs, xs++[u,v]=a::b::bs := by
    cases xs with
    | nil => exact ⟨u,v,[],rfl⟩
    | cons a xs =>
      cases xs with
      | nil => exact ⟨a,u,[v],rfl⟩
      | cons b bs => exact ⟨a,b,bs++[u,v],rfl⟩
  obtain ⟨u,v,us,hx⟩ := two x a a
  obtain ⟨p,q,qs,hy⟩ := two y t z
  simp only [List.cons_append,hx,hy]
  rfl


/-- Numeric sign-extension justifies every measured dependent-top leaf. -/
theorem dependent_prefix_correct (x y cs : List Wire) (a t z cin : Wire)
    (hy : y.length=x.length) (hc : cs.length=x.length)
    (nd : (cin::(x++[a]++y++[t,z]++cs)).Nodup)
    (s : State) (m : List Bool)
    (extended : Extended x.length ((regValue (x++[a,a]) s.basis+
      regValue (y++[t,z]) s.basis+(s.basis cin).toNat)%2^(y++[t,z]).length))
    (clean : ∀ q∈cs,s.basis q=false) :
    (run (Q6LifetimeResearch.addTop (x++[a,a]) (y++[t,z]) cs cin) m s).phase=s.phase ∧
    (∀ q,q∉y++[t,z] →
      (run (Q6LifetimeResearch.addTop (x++[a,a]) (y++[t,z]) cs cin) m s).basis q=s.basis q) ∧
    regValue (y++[t,z]) (run (Q6LifetimeResearch.addTop (x++[a,a]) (y++[t,z]) cs cin) m s).basis=
      (regValue (x++[a,a]) s.basis+regValue (y++[t,z]) s.basis+
        (s.basis cin).toNat)%2^(y++[t,z]).length := by
  induction x generalizing y cs cin s m with
  | nil =>
    have ye : y=[] := List.eq_nil_of_length_eq_zero hy
    have ce : cs=[] := List.eq_nil_of_length_eq_zero hc
    subst y; subst cs
    have four : [a,t,cin,z].Nodup := by
      apply List.nodup_iff_count.mpr
      intro q
      have h := List.nodup_iff_count.mp nd q
      simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
      omega
    have tz : t≠z := by
      have h := List.nodup_iff_count.mp four t
      intro e; subst z
      simp only [List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
      omega
    simp only [List.nil_append]
    rw [Q6LifetimeResearch.addTop,dependent_top a t z cin four s m (by simpa using extended)]
    refine ⟨rfl,?_,?_⟩
    · intro q hq
      have qt : q≠t := fun e => hq (by simp [e])
      have qz : q≠z := fun e => hq (by simp [e])
      simp [writeBit,qt,qz]
    · cases ha : s.basis a <;> cases ht : s.basis t <;> cases hi : s.basis cin <;>
        cases hz : s.basis z <;>
        simp_all [Extended,regValue,writeBit,sumBit,carryBit,tz,Ne.symm tz]
  | cons b xs ih =>
    cases y with
    | nil => simp at hy
    | cons d ys =>
      cases cs with
      | nil => simp at hc
      | cons k ks =>
        have four : [b,d,cin,k].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := List.nodup_iff_count.mp nd q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have tailND : (k::(xs++[a]++ys++[t,z]++ks)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := List.nodup_iff_count.mp nd q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have headAway (q : Wire) (hq : q∈[b,d,cin,k]) : q∉ys++[t,z] := by
          intro bad
          have h := List.nodup_iff_count.mp nd q
          have l := List.count_pos_iff.mpr hq
          have r := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,List.count_nil] at h l r
          omega
        have kAway (q : Wire) (hq : q∈xs++[a]++ys++[t,z]++ks) : q≠k := by
          intro e
          have h := List.nodup_iff_count.mp nd k
          have r := List.count_pos_iff.mpr (e ▸ hq)
          simp only [List.count_cons,List.count_append,List.count_nil,
            beq_self_eq_true,if_true] at h r
          omega
        have n4 := four
        simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
          not_or,not_false_eq_true,and_true] at n4
        obtain ⟨⟨bd,bi,bk⟩,⟨di,dk⟩,ik⟩ := n4
        let A := s.basis b
        let B := s.basis d
        let C := s.basis cin
        let K := carryBit A B C
        let u : State := ⟨s.phase,writeBit s.basis k K⟩
        have keep (q : Wire) (hq : q≠k) : u.basis q=s.basis q := by
          simp [u,writeBit,hq]
        have first (ms : List Bool) : run (majority b d cin k) ms s=u := by
          rw [majority_correct _ _ _ _ four]
          simp [u,K,A,B,C,clean k (by simp)]
        have sameX : regValue (xs++[a,a]) u.basis=regValue (xs++[a,a]) s.basis := by
          apply regValue_congr
          intro q hq
          apply keep q
          apply kAway q
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self] at hq ⊢
          itauto
        have sameY : regValue (ys++[t,z]) u.basis=regValue (ys++[t,z]) s.basis :=
          regValue_congr _ _ _ (fun q hq => keep q (kAway q (by
            simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢;itauto)))
        have uk0 : u.basis k=K := by simp [u,writeBit]
        have ylen : ys.length=xs.length := by simpa using hy
        have tailExt : Extended xs.length ((regValue (xs++[a,a]) u.basis+
            regValue (ys++[t,z]) u.basis+(u.basis k).toNat)%2^(ys++[t,z]).length) := by
          rw [sameX,sameY,uk0]
          have e := extended_tail A B C (regValue (xs++[a,a]) s.basis)
            (regValue (ys++[t,z]) s.basis) xs.length (by
              simpa only [List.cons_append,regValue,List.foldr_cons,List.length_cons,
                List.length_append,List.length_cons,List.length_nil,Nat.add_zero,ylen,
                Bool.toNat,Bool.cond_eq_ite,A,B,C] using extended)
          simpa only [List.length_append,List.length_cons,List.length_nil,Nat.add_zero,ylen,K] using e
        have high := ih ys ks k (by simpa using hy) (by simpa using hc) tailND u m tailExt
          (by intro q hq; rw [keep q (kAway q (by simp [hq]))]; exact clean q (by simp [hq]))
        let v := run (Q6LifetimeResearch.addTop (xs++[a,a]) (ys++[t,z]) ks k) m u
        have va : v.basis b=A := (high.2.1 b (headAway b (by simp))).trans (keep b bk)
        have vb : v.basis d=B := (high.2.1 d (headAway d (by simp))).trans (keep d dk)
        have vi : v.basis cin=C := (high.2.1 cin (headAway cin (by simp))).trans (keep cin ik)
        have vk : v.basis k=K := by
          rw [high.2.1 k (headAway k (by simp))]
          simp [u,writeBit]
        have erase (ms : List Bool) : run (eraseCarry b d cin k) ms v=
            ⟨v.phase,writeBit v.basis k false⟩ := by
          apply eraseCarry_correct b d cin k bk dk ik v _ ms
          rw [va,vb,vi,vk]
        have last (ms : List Bool) :
            run [.CX b d,.CX cin d] ms ⟨v.phase,writeBit v.basis k false⟩=
              ⟨v.phase,writeBit (writeBit v.basis k false) d (sumBit A B C)⟩ := by
          simp only [run]
          apply congrArg (State.mk v.phase)
          funext q
          by_cases eq : q=d
          · subst q
            simp only [writeBit,Function.update_self,Function.update_of_ne (Ne.symm di),
              Function.update_of_ne bk,Function.update_of_ne dk,Function.update_of_ne ik,
              va,vb,vi,sumBit]
            cases A <;> cases B <;> cases C <;> rfl
          · simp [writeBit,Function.update,eq]
        simp only [dependent_cons,List.append_assoc,run_append,run_take,
          show measurementCount (majority b d cin k)=0 from rfl,List.drop_zero]
        rw [first,erase,last]
        refine ⟨high.1,?_,?_⟩
        · intro q hq
          have qd : q≠d := fun e => hq (by simp [e])
          have qt : q∉ys++[t,z] := fun h => hq (by simp [h])
          simp only [writeBit,Function.update_of_ne qd]
          by_cases qk : q=k
          · subst q; simp [writeBit,clean k (by simp)]
          · simp only [writeBit,Function.update_of_ne qk]
            exact (high.2.1 q qt).trans (keep q qk)
        · have tailKeep : regValue (ys++[t,z])
              (writeBit (writeBit v.basis k false) d (sumBit A B C))=
                regValue (ys++[t,z]) v.basis := by
            apply regValue_congr
            intro q hq
            have qd : q≠d := fun e => headAway d (by simp) (e ▸ hq)
            have qk : q≠k := fun e => headAway k (by simp) (e ▸ hq)
            simp [writeBit,qd,qk]
          have xin : regValue (xs++[a,a]) u.basis=regValue (xs++[a,a]) s.basis := by
            apply regValue_congr
            intro q hq
            apply keep q
            apply kAway q
            simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self] at hq ⊢
            itauto
          have yin : regValue (ys++[t,z]) u.basis=regValue (ys++[t,z]) s.basis :=
            regValue_congr _ _ _ (fun q hq => keep q (kAway q (by
              simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
              itauto)))
          have uk : u.basis k=K := by simp [u,writeBit]
          change (if (writeBit (writeBit v.basis k false) d (sumBit A B C)) d
            then 1 else 0)+2*regValue (ys++[t,z])
              (writeBit (writeBit v.basis k false) d (sumBit A B C))=_
          rw [tailKeep,high.2.2,xin,yin,uk]
          simp only [writeBit,Function.update_self]
          have col := sum_value_step A B C (regValue (xs++[a,a]) s.basis)
            (regValue (ys++[t,z]) s.basis) (ys++[t,z]).length
          simpa only [List.cons_append,regValue,List.foldr_cons,Bool.toNat,
            Bool.cond_eq_ite,List.length_cons,A,B,C,K] using col

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassDependentLoan =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- Direct loan contract for the dependent-top recursion, retaining arbitrary
history at the retired physical site and restoring every outsider. -/
theorem dependent_loan_correct (x y cs : List Wire) (a t z cin host retired : Wire)
    (hy : y.length=x.length) (hc : cs.length=x.length)
    (nd : (host::cin::(x++[a]++y++[t,z]++cs)).Nodup)
    (member : retired∈cs) (s : State) (m : List Bool)
    (extended : Extended x.length ((regValue (x++[a,a]) s.basis+
      regValue (y++[t,z]) s.basis+(s.basis cin).toNat)%2^(y++[t,z]).length))
    (host0 : s.basis host=false)
    (clean : CleanExcept cs retired s.basis) :
    (run (renameProgram (Equiv.swap retired host)
      (Q6LifetimeResearch.addTop (x++[a,a]) (y++[t,z]) cs cin)) m s).phase=s.phase ∧
    WordFrame (y++[t,z]) s.basis
      ((regValue (x++[a,a]) s.basis+regValue (y++[t,z]) s.basis+
        (s.basis cin).toNat)%2^(y++[t,z]).length)
      (run (renameProgram (Equiv.swap retired host)
        (Q6LifetimeResearch.addTop (x++[a,a]) (y++[t,z]) cs cin)) m s).basis := by
  let f := Equiv.swap retired host
  have hn := List.nodup_cons.mp nd
  have fixed (q : Wire) (hq : q∈cin::(x++[a]++y++[t,z])) : f q=q := by
    have qh : q≠host := fun e => hn.1 (by
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
      subst q; itauto)
    have qr : q≠retired := by
      intro e
      have n := List.nodup_iff_count.mp hn.2 retired
      have p := List.count_pos_iff.mpr (e ▸ hq)
      have c := List.count_pos_iff.mpr member
      simp only [List.count_cons,List.count_append,List.count_nil] at n p
      omega
    exact Equiv.swap_apply_of_ne_of_ne qr qh
  have keep (q : Wire) (hq : q∈cin::(x++[a]++y++[t,z])) :
      (pullState f s).basis q=s.basis q := by
    change s.basis (f q)=_
    rw [fixed q hq]
  have rvx : regValue (x++[a,a]) (pullState f s).basis=regValue (x++[a,a]) s.basis := by
    apply regValue_congr
    intro q hq
    apply keep q
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_self] at hq ⊢
    itauto
  have rvy : regValue (y++[t,z]) (pullState f s).basis=regValue (y++[t,z]) s.basis := by
    apply regValue_congr
    intro q hq
    apply keep q
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    itauto
  have h := dependent_prefix_correct x y cs a t z cin hy hc hn.2 (pullState f s) m
    (by simpa only [rvx,rvy,keep cin (by simp)] using extended) (by
      intro q hq
      change s.basis (f q)=false
      by_cases e : q=retired
      · subst q; simpa only [f,Equiv.swap_apply_left] using host0
      · have qh : q≠host := fun eq => hn.1 (by simp [←eq,hq])
        rw [show f q=q from Equiv.swap_apply_of_ne_of_ne e qh]
        exact clean q hq e)
  apply rename_frame f _ (y++[t,z]) s m _
  · intro q hq
    apply fixed q
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    itauto
  · refine ⟨h.1,?_,h.2.1⟩
    simpa only [rvx,rvy,keep cin (by simp)] using h.2.2

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubHead =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- Direct subtraction head: complemented r0 is cleared using its retained
parity, loaned, restored, and erased before the low sum is formed. -/
theorem sub_head_withCarry (constant : Bool) (x y cs : List Wire)
    (a b cin k parity ta t z retired : Wire)
    (hy : y.length=x.length) (hc : cs.length=x.length)
    (nd : ([parity,a,cin,b,k]++x++[ta]++y++[t,z]++cs).Nodup)
    (member : retired∈cs) (s : State) (m : List Bool)
    (parityValue : s.basis parity= !s.basis b)
    (extended : Extended (x.length+1) ((regValue (a::(x++[ta,ta])) s.basis+
      regValue (b::(y++[t,z])) s.basis+(carryValue constant cin s.basis).toNat)%2^(b::(y++[t,z])).length)) (first0 : s.basis k=false)
    (clean : CleanExcept cs retired s.basis) :
    let clear : Program := [.X b,.CX parity b]
    let body := renameProgram (Equiv.swap retired b)
      (Q6LifetimeResearch.addTop (x++[ta,ta]) (y++[t,z]) cs k)
    let p := carryMajor constant a b cin k++clear++body++clear.reverse++
      carryErase constant a b cin k++carrySum constant a b cin
    (run p m s).phase=s.phase ∧
    WordFrame (b::(y++[t,z])) s.basis
      ((regValue (a::(x++[ta,ta])) s.basis+regValue (b::(y++[t,z])) s.basis+
        (carryValue constant cin s.basis).toNat)%2^(b::(y++[t,z])).length) (run p m s).basis := by
  let clear : Program := [.X b,.CX parity b]
  let body := renameProgram (Equiv.swap retired b) (Q6LifetimeResearch.addTop (x++[ta,ta]) (y++[t,z]) cs k)
  have n5 : [parity,a,cin,b,k].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have n4 : [a,b,cin,k].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp n5 q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  have n5' := n5
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at n5'
  obtain ⟨⟨pa,pi,pb,pk⟩,⟨ai,ab,ak⟩,⟨ib,ik⟩,bk⟩ := n5'
  have headAway (q : Wire) (hq : q∈[parity,a,cin,b,k]) : q∉y++[t,z] := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have l := List.count_pos_iff.mpr hq
    have r := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append,List.count_nil] at h l r
    omega
  have tailAway (q : Wire) (hq : q∈x++[ta]++y++[t,z]++cs) : q≠b ∧ q≠k := by
    constructor <;> intro e
    all_goals
      have h := List.nodup_iff_count.mp nd q
      have r := List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append,List.count_nil] at h r
      subst q
      simp only [beq_self_eq_true,if_true] at h
      omega
  have loanND : (b::k::(x++[ta]++y++[t,z]++cs)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  let A := s.basis a
  let B := s.basis b
  let C := carryValue constant cin s.basis
  let K := carryBit A B C
  let u : State := ⟨s.phase,writeBit s.basis k K⟩
  let w : State := ⟨s.phase,writeBit u.basis b false⟩
  have uk (q : Wire) (hq : q≠k) : u.basis q=s.basis q := by simp [u,writeBit,hq]
  have wk (q : Wire) (qb : q≠b) (qk : q≠k) : w.basis q=s.basis q := by
    simp [w,u,writeBit,qb,qk]
  have first (ms : List Bool) : run (carryMajor constant a b cin k) ms s=u := by
    exact carry_major_run constant a b cin k n4 s ms first0
  have clearRun (ms : List Bool) : run clear ms u=w := by
    simp only [clear,run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases eq : q=b
    · subst q
      simp only [writeBit,Function.update_self,Function.update_of_ne pb]
      rw [uk parity pk,uk b bk,parityValue]
      cases s.basis b <;> rfl
    · simp [w,writeBit,eq]
  have wclean : CleanExcept cs retired w.basis := by
    intro q hq qr
    have away := tailAway q (by simp [hq])
    rw [wk q away.1 away.2]
    exact clean q hq qr
  have xin0 : regValue (x++[ta,ta]) w.basis=regValue (x++[ta,ta]) s.basis := by
    apply regValue_congr
    intro q hq
    have a := tailAway q (by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self] at hq ⊢;itauto)
    exact wk q a.1 a.2
  have yin0 : regValue (y++[t,z]) w.basis=regValue (y++[t,z]) s.basis := by
    apply regValue_congr
    intro q hq
    have a := tailAway q (by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢;itauto)
    exact wk q a.1 a.2
  have wk0 : w.basis k=K := by simp [w,u,writeBit,Ne.symm bk]
  have ext : Extended x.length ((regValue (x++[ta,ta]) w.basis+
      regValue (y++[t,z]) w.basis+(w.basis k).toNat)%2^(y++[t,z]).length) := by
    rw [xin0,yin0,wk0]
    have e := extended_tail A B C (regValue (x++[ta,ta]) s.basis)
      (regValue (y++[t,z]) s.basis) x.length (by
        simpa only [regValue,List.foldr_cons,List.length_cons,List.length_append,
          List.length_nil,Nat.add_zero,hy,Bool.toNat,Bool.cond_eq_ite,A,B,C] using extended)
    simpa only [List.length_append,List.length_cons,List.length_nil,Nat.add_zero,hy,K] using e
  have high := dependent_loan_correct x y cs ta t z k b retired hy hc loanND member w m ext
    (by simp [w,writeBit]) wclean
  let v := run body m w
  have va : v.basis a=A := (high.2.2 a (headAway a (by simp))).trans (wk a ab ak)
  have vi : v.basis cin=s.basis cin := (high.2.2 cin (headAway cin (by simp))).trans (wk cin ib ik)
  have vp : v.basis parity=s.basis parity :=
    (high.2.2 parity (headAway parity (by simp))).trans (wk parity pb pk)
  have vb : v.basis b=false := by
    rw [high.2.2 b (headAway b (by simp))]
    simp [w,writeBit]
  have vk : v.basis k=K := by
    rw [high.2.2 k (headAway k (by simp))]
    simp [w,u,writeBit,Ne.symm bk]
  let v2 : State := ⟨v.phase,writeBit v.basis b B⟩
  have reverseRun (ms : List Bool) : run clear.reverse ms v=v2 := by
    change run [.CX parity b,.X b] ms v=v2
    simp only [run]
    apply congrArg (State.mk v.phase)
    funext q
    by_cases eq : q=b
    · subst q
      simp only [writeBit,Function.update_self,Function.update_of_ne pb,vp,vb]
      rw [parityValue]
      dsimp only [B]
      cases s.basis b <;> rfl
    · simp [v2,writeBit,eq]
  have erase (ms : List Bool) : run (carryErase constant a b cin k) ms v2=
      ⟨v2.phase,writeBit v2.basis k false⟩ := by
    apply carry_erase_run constant a b cin k ak bk ik v2 ms
    simp only [v2,writeBit,Function.update_self,Function.update_of_ne ab,
      Function.update_of_ne ib,Function.update_of_ne (Ne.symm bk),va,vi,vk,K]
    cases constant <;> simp [carryValue,C,ib,vi]
  have last (ms : List Bool) :
      run (carrySum constant a b cin) ms ⟨v2.phase,writeBit v2.basis k false⟩=
        ⟨v.phase,writeBit (writeBit v.basis k false) b (sumBit A B C)⟩ := by
    have nd3 : [a,b,cin].Nodup := by
      have count := List.nodup_iff_count.mp n4
      apply List.nodup_iff_count.mpr
      intro q
      have n := count q
      simp only [List.count_cons,List.count_nil] at n ⊢
      omega
    rw [carry_sum_run constant a b cin nd3]
    apply State.extensionality
    · rfl
    · funext q
      by_cases eq : q=b
      · subst q
        cases constant <;>
          simp [v2,writeBit,carryValue,A,B,C,ab,ak,bk,ib,ik,va,vi]
      · simp [v2,writeBit,Function.update,eq]
  have clear0 : measurementCount clear=0 := rfl
  have rev0 : measurementCount clear.reverse=0 := rfl
  have actual : run (carryMajor constant a b cin k++clear++body++clear.reverse++
      carryErase constant a b cin k++carrySum constant a b cin) m s=
        ⟨v.phase,writeBit (writeBit v.basis k false) b (sumBit A B C)⟩ := by
    simp only [List.append_assoc,run_append,run_take,
      show measurementCount (carryMajor constant a b cin k)=0 from (carry_head_records constant a b cin k parity).1,clear0,rev0,List.drop_zero]
    rw [first,clearRun,reverseRun,erase,last]
  change (run (carryMajor constant a b cin k++clear++body++clear.reverse++
      carryErase constant a b cin k++carrySum constant a b cin) m s).phase=s.phase ∧ _
  rw [actual]
  refine ⟨high.1,?_,?_⟩
  · have targetKeep : regValue (y++[t,z])
        (writeBit (writeBit v.basis k false) b (sumBit A B C))=regValue (y++[t,z]) v.basis := by
      apply regValue_congr
      intro q hq
      have away := tailAway q (by
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; itauto)
      simp [writeBit,away.1,away.2]
    have xin : regValue (x++[ta,ta]) w.basis=regValue (x++[ta,ta]) s.basis := by
      apply regValue_congr
      intro q hq
      have away := tailAway q (by
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self] at hq ⊢; itauto)
      exact wk q away.1 away.2
    have yin : regValue (y++[t,z]) w.basis=regValue (y++[t,z]) s.basis := by
      apply regValue_congr
      intro q hq
      have away := tailAway q (by
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; itauto)
      exact wk q away.1 away.2
    have carryIn : w.basis k=K := by simp [w,u,writeBit,Ne.symm bk]
    change (if (writeBit (writeBit v.basis k false) b (sumBit A B C)) b then 1 else 0)+
      2*regValue (y++[t,z]) (writeBit (writeBit v.basis k false) b (sumBit A B C))=_
    rw [targetKeep,high.2.1,xin,yin,carryIn]
    simp only [writeBit,Function.update_self]
    have col := sum_value_step A B C (regValue (x++[ta,ta]) s.basis)
      (regValue (y++[t,z]) s.basis) (y++[t,z]).length
    simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,List.length_cons,A,B,C,K] using col
  · intro q hq
    have qb : q≠b := fun e => hq (by simp [e])
    have qt : q∉y++[t,z] := fun h => hq (by simp [h])
    simp only [writeBit,Function.update_of_ne qb]
    by_cases qk : q=k
    · subst q; simp [writeBit,first0]
    · simp only [writeBit,Function.update_of_ne qk]
      exact (high.2.2 q qt).trans (wk q qb qk)
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubLayout =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


private theorem sub_split_nonempty (xs : List Wire) (h : xs≠[]) :
    xs=xs.getD 0 0::xs.drop 1 := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons a xs => rfl


def rawSubHeadMode (constant : Bool) (retired : Wire) (L : Layout) : Program :=
  let a := L.ylow.getD 0 0
  let c := ((Q6Structural.q6Carry L).take 255).getD 0 0
  let clear : Program := [.X L.r0,.CX L.parity L.r0]
  carryMajor constant a L.r0 L.sign c++clear++
    Q6LifetimeResearch.move retired L.r0
      (Q6LifetimeResearch.addTop (L.ylow.drop 1++[L.ymsb,L.ymsb])
        (L.rtail++[L.rmsb,L.one]) (((Q6Structural.q6Carry L).take 255).drop 1) c)++
    clear.reverse++carryErase constant a L.r0 L.sign c++carrySum constant a L.r0 L.sign

/-- The emitted inner add used by raw subtraction, after both complements. -/
theorem sub_head_layout_mode (constant : Bool) (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m : List Bool)
    (parityValue : s.basis L.parity= !s.basis L.r0)
    (extended : Extended 255 ((regValue (GuardCompression.source L) s.basis+
      regValue (rawTarget L) s.basis+(carryValue constant L.sign s.basis).toNat)%2^257))
    (clean : CleanExcept ((Q6Structural.q6Carry L).take 255) retired s.basis) :
    (run (rawSubHeadMode constant retired L) m s).phase=s.phase ∧
    WordFrame (rawTarget L) s.basis
      ((regValue (GuardCompression.source L) s.basis+regValue (rawTarget L) s.basis+
        (carryValue constant L.sign s.basis).toNat)%2^257)
      (run (rawSubHeadMode constant retired L) m s).basis := by
  let cs := (Q6Structural.q6Carry L).take 255
  let a := L.ylow.getD 0 0
  let c := cs.getD 0 0
  let x := L.ylow.drop 1
  let tail := cs.drop 1
  let clear : Program := [.X L.r0,.CX L.parity L.r0]
  let body := renameProgram (Equiv.swap retired L.r0)
    (Q6LifetimeResearch.addTop (x++[L.ymsb,L.ymsb]) (L.rtail++[L.rmsb,L.one]) tail c)
  let H := carryMajor constant a L.r0 L.sign c++clear++body++clear.reverse++
    carryErase constant a L.r0 L.sign c++carrySum constant a L.r0 L.sign
  have shape : cs=L.carry.take 254++[L.lower] := active_carry_shape L hw
  have clen : cs.length=255 := by rw [shape]; simp [List.length_take,hw.2.2]
  have yl : L.ylow=a::x := sub_split_nonempty _ (by
    intro e; have h := hw.2.1; rw [e] at h; cases h)
  have cl : cs=c::tail := sub_split_nonempty _ (by intro e; rw [e] at clen; cases clen)
  have memberTail : retired∈tail := by
    dsimp only [tail]
    rw [shape,List.drop_append]
    have len : (L.carry.take 254).length=254 := by simp [List.length_take,hw.2.2]
    simp only [len,show 1-254=0 from rfl,List.drop_zero,List.mem_append,List.mem_singleton]
    exact Or.inl member
  have rawND : (L.ylow++[L.ymsb]++L.low++[L.rmsb,L.one]++cs++
      [L.sign,L.parity]).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have lim := (List.take_sublist 254 L.carry).count_le q
    rw [shape]
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have headND : ([L.parity,a,L.sign,L.r0,c]++x++[L.ymsb]++L.rtail++
      [L.rmsb,L.one]++tail).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp rawND q
    rw [yl,cl] at h
    simp only [BalancedCleanup.Layout.low,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have cy : L.rtail.length=x.length := by simp [x,hw.1,hw.2.1]
  have ct : tail.length=x.length := by simp [tail,x,clen,hw.2.1]
  have cNe : c≠retired := by
    intro e
    have h := List.nodup_iff_count.mp headND retired
    have r := List.count_pos_iff.mpr memberTail
    simp only [List.count_cons,List.count_append,List.count_nil] at h
    rw [e] at h
    simp only [beq_self_eq_true,if_true] at h
    omega
  have first0 : s.basis c=false := clean c (by change c∈cs;rw [cl];simp) cNe
  have cleanTail : CleanExcept tail retired s.basis := by
    intro q hq qr
    exact clean q (by change q∈cs;rw [cl];simp [hq]) qr
  have targetShape : (L.r0::(L.rtail++[L.rmsb,L.one]))=rawTarget L := by
    simp [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have sourceShape : (a::(x++[L.ymsb,L.ymsb]))=GuardCompression.source L := by
    simp only [GuardCompression.source,BalancedCleanup.Layout.y,yl,List.cons_append,List.append_assoc,
      List.singleton_append,List.nil_append]
  have ext : Extended (x.length+1) ((regValue (a::(x++[L.ymsb,L.ymsb])) s.basis+
      regValue (L.r0::(L.rtail++[L.rmsb,L.one])) s.basis+(carryValue constant L.sign s.basis).toNat)%
        2^(L.r0::(L.rtail++[L.rmsb,L.one])).length) := by
    rw [sourceShape,targetShape]
    simpa [-Nat.reducePow,x,List.length_drop,hw.2.1,rawTarget,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low,hw.1] using extended
  have second := sub_head_withCarry constant x L.rtail tail a L.r0 L.sign c L.parity
    L.ymsb L.rmsb L.one retired cy ct headND memberTail s m parityValue ext first0 cleanTail
  change (run H m s).phase=s.phase ∧ WordFrame _ s.basis _ (run H m s).basis at second
  rw [targetShape,sourceShape] at second
  simpa only [rawSubHeadMode,Q6LifetimeResearch.move,H,clear,body,cs,a,c,x,tail,
    rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
    List.length_append,List.length_cons,List.length_nil,Nat.add_zero,Nat.reduceAdd,hw.1] using second
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedField


/-- Pure encoded signed addition, with no circuit or range premise. -/
theorem signed_encoded_add (n : Nat) (B : Bool) (X Y : Int) :
    signedWordValue n B (encodeWord n Y) (encodeWord n X)=encodeWord n (rawSum B X Y) := by
  have fit : signedWordValue n B (encodeWord n Y) (encodeWord n X)<2^n := by
    cases B <;> exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have castfit : (signedWordValue n B (encodeWord n Y) (encodeWord n X) : Int)<((2^n : Nat) : Int) := by
    exact_mod_cast fit
  have h := signedWordValue_emod n B (encodeWord n Y) (encodeWord n X) (encodeWord_bound _ _)
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) castfit] at h
  have e : (signedWordValue n B (encodeWord n Y) (encodeWord n X) : Int)=
      (encodeWord n (rawSum B X Y) : Int) := by
    rw [encodeWord_cast]
    cases B
    · have hh : (signedWordValue n false (encodeWord n Y) (encodeWord n X) : Int)=
          ((X%((2^n : Nat) : Int))+(Y%((2^n : Nat) : Int)))%((2^n : Nat) : Int) := by
        simpa only [signedIntegerValue,Bool.false_eq_true,if_false,encodeWord_cast] using h
      simpa only [rawSum,signedY,Bool.false_eq_true,if_false] using
        hh.trans (Int.add_emod X Y ((2^n : Nat) : Int)).symm
    · have hh : (signedWordValue n true (encodeWord n Y) (encodeWord n X) : Int)=
          ((X%((2^n : Nat) : Int))-(Y%((2^n : Nat) : Int)))%((2^n : Nat) : Int) := by
        simpa only [signedIntegerValue,if_true,encodeWord_cast] using h
      simpa only [rawSum,signedY,if_true,sub_eq_add_neg] using
        hh.trans (Int.sub_emod X Y ((2^n : Nat) : Int)).symm
  exact_mod_cast e


theorem signed_view_add (n X Y : Nat) (B : Bool) (fit : X<2^n) :
    ((if B then 2^n-1-X else X)+Y+B.toNat)%2^n=signedWordValue n B X Y := by
  cases B
  · simp [signedWordValue,Nat.add_comm]
  · simp only [signedWordValue,if_true,Bool.toNat_true]
    congr 1
    omega


theorem complement_add_inverse (M C X T K : Nat) (pos : 0<M) (fit : X<M)
    (bound : C+K≤M) (sum : (C+X+K)%M=T) :
    (C+(M-1-T)+K)%M=M-1-X := by
  have h := undo_mapped_add M C X K pos fit bound
  rw [sum] at h
  have small := Nat.mod_lt (C+(M-1-T)+K) pos
  omega


theorem extended_complement (n v : Nat) (fit : v<2^(n+2)) (h : Extended n v) :
    Extended n (2^(n+2)-1-v) := by
  have pow : 2^(n+2)=4*2^n := by rw [Nat.pow_add];norm_num;omega
  unfold Extended at h ⊢
  rw [pow] at fit ⊢
  omega


theorem encoded_extended (n : Nat) (z : Int)
    (range : -((2^n : Nat) : Int)≤z ∧ z<((2^n : Nat) : Int)) :
    Extended n (encodeWord (n+2) z) := by
  have pow : 2^(n+2)=4*2^n := by rw [Nat.pow_add];norm_num;omega
  have h := BalancedFold.encode_shift (n+2) z (by
    rw [pow,Nat.cast_mul];simp only [Nat.cast_ofNat];omega)
  rw [pow,Nat.cast_mul] at h
  simp only [Nat.cast_ofNat] at h
  unfold Extended
  by_cases neg : z<0 <;> simp only [neg,if_true,if_false] at h <;> omega

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubInner =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


def rawSubInnerMode (constant : Bool) (retired : Wire) (L : Layout) : Program :=
  notRegister (rawTarget L)++rawSubHeadMode constant retired L++notRegister (rawTarget L)

/-- Undo a known modular addition. The high-two-bit premise is numeric,
so it is independent of any execution of an older subtraction program. -/
theorem sub_inner_mode (constant : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m : List Bool)
    (parity : s.basis L.parity=s.basis L.r0)
    (clean : CleanExcept ((Q6Structural.q6Carry L).take 255) retired s.basis)
    (v : Nat) (fit : v<2^257) (extended : Extended 255 v)
    (bound : regValue (GuardCompression.source L) s.basis+(carryValue constant L.sign s.basis).toNat≤2^257)
    (sum : (regValue (GuardCompression.source L) s.basis+v+(carryValue constant L.sign s.basis).toNat)%2^257=
      regValue (rawTarget L) s.basis) :
    (run (rawSubInnerMode constant retired L) m s).phase=s.phase ∧
    WordFrame (rawTarget L) s.basis v (run (rawSubInnerMode constant retired L) m s).basis := by
  have len : (rawTarget L).length=257 := by
    simp [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,hw.1]
  have shape := active_carry_shape L hw
  have away (q : Wire) (hq : q∈[L.sign,L.parity]++L.y++(Q6Structural.q6Carry L).take 255) :
      q∉rawTarget L := by
    intro bad
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    have lim := (List.take_sublist 254 L.carry).count_le q
    rw [shape] at a
    simp only [rawTarget,BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h a b
    omega
  let u : State := ⟨s.phase,fun q => if q∈rawTarget L then !s.basis q else s.basis q⟩
  have first (r : List Bool) : run (notRegister (rawTarget L)) r s=u :=
    notRegister_correct _ (rawTargetND L hn) s r
  have keep (q : Wire) (hq : q∉rawTarget L) : u.basis q=s.basis q := by simp [u,hq]
  have source : regValue (GuardCompression.source L) u.basis=
      regValue (GuardCompression.source L) s.basis := by
    apply regValue_congr
    intro q hq
    apply keep q
    apply away q
    simp only [GuardCompression.source,BalancedCleanup.Layout.y,List.mem_append,List.mem_singleton] at hq ⊢
    itauto
  have input : regValue (rawTarget L) u.basis=2^257-1-regValue (rawTarget L) s.basis := by
    rw [regValue_congr (rawTarget L) u.basis (fun q => !s.basis q)
      (by intro q hq;simp [u,hq]),regValue_complement,len]
  have si : u.basis L.sign=s.basis L.sign := keep _ (away _ (by simp))
  have ci : carryValue constant L.sign u.basis=carryValue constant L.sign s.basis := by
    cases constant <;> simp [carryValue,si]
  have gamma := complement_add_inverse (2^257) (regValue (GuardCompression.source L) s.basis)
    v (regValue (rawTarget L) s.basis) (carryValue constant L.sign s.basis).toNat (by omega) fit bound sum
  have h := sub_head_layout_mode constant retired L hw hn member u m (by
      rw [keep L.parity (away _ (by simp)),parity]
      simp [u,rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
    (by
      rw [source,input,ci,gamma]
      have complement := extended_complement 255 v
      simp only [Nat.reduceAdd] at complement
      exact complement fit extended)
    (by intro q hq qr;rw [keep q (away q (by simp [hq]))];exact clean q hq qr)
  let t := run (rawSubHeadMode constant retired L) m u
  have output : regValue (rawTarget L) (fun q => if q∈rawTarget L then !t.basis q else t.basis q)=
      2^257-1-regValue (rawTarget L) t.basis := by
    rw [regValue_congr (rawTarget L) _ (fun q => !t.basis q)
      (by intro q hq;simp [hq]),regValue_complement,len]
  have execute : run (rawSubInnerMode constant retired L) m s=
      run (notRegister (rawTarget L)) (m.drop (measurementCount (rawSubHeadMode constant retired L))) t := by
    rw [rawSubInnerMode,run_append,run_take,run_append,run_take,measurementCount_append,
      (notRegister_counts (rawTarget L)).2,Nat.zero_add,List.drop_zero,first]
  rw [execute,notRegister_correct _ (rawTargetND L hn)]
  refine ⟨h.1,?_,?_⟩
  · rw [output,h.2.1,source,input,ci,gamma]
    omega
  · intro q hq
    simp only [hq,if_false]
    exact (h.2.2 q hq).trans (keep q hq)
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


def rawSubCoreMode (constant : Bool) (retired : Wire) (L : Layout) : Program :=
  signComplement L.sign L.y++rawSubInnerMode constant retired L++signComplement L.sign L.y

/-- The source view and target complement cancel directly around the
measured subtraction. Every source/control/carry outsider is restored. -/
theorem sub_core_mode (constant : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m : List Bool)
    (parity : s.basis L.parity=s.basis L.r0)
    (clean : CleanExcept ((Q6Structural.q6Carry L).take 255) retired s.basis)
    (v : Nat) (fit : v<2^257) (extended : Extended 255 v)
    (sum : ((if s.basis L.sign then 2^257-1-regValue (GuardCompression.source L) s.basis
      else regValue (GuardCompression.source L) s.basis)+v+
        (carryValue constant L.sign s.basis).toNat)%2^257=regValue (rawTarget L) s.basis) :
    (run (rawSubCoreMode constant retired L) m s).phase=s.phase ∧
    WordFrame (rawTarget L) s.basis v (run (rawSubCoreMode constant retired L) m s).basis := by
  let cs := (Q6Structural.q6Carry L).take 255
  let S := signComplement L.sign L.y
  have shape : cs=L.carry.take 254++[L.lower] := active_carry_shape L hw
  have nd : (([L.sign,L.parity]++rawTarget L++cs)++L.y).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have lim := (List.take_sublist 254 L.carry).count_le q
    rw [shape]
    simp only [rawTarget,BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have yND : L.y.Nodup := (List.nodup_append'.mp nd).2.1
  have notY (q : Wire) (hq : q∈[L.sign,L.parity]++rawTarget L++cs) : q∉L.y :=
    fun bad => List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 hq bad
  have signAway : L.sign∉L.y := notY _ (by simp)
  have signTarget : L.sign∉rawTarget L := by
    intro bad
    have h := List.nodup_iff_count.mp nd L.sign
    have p := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h p
    omega
  let u := run S m s
  have first := signComplement_correct L.sign L.y yND signAway s m
  have view (q : Wire) : u.basis q=
      if q∈L.y then s.basis q ^^ s.basis L.sign else s.basis q :=
    GuardCompression.complement_bit L.sign L.y yND signAway s m q
  have keep (q : Wire) (hq : q∈[L.sign,L.parity]++rawTarget L++cs) : u.basis q=s.basis q := by
    rw [view,if_neg (notY q hq)]
  have targetIn : regValue (rawTarget L) u.basis=regValue (rawTarget L) s.basis :=
    regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))
  have sourceLen : (GuardCompression.source L).length=257 := by
    simp [GuardCompression.source,BalancedCleanup.Layout.y,hw.2.1]
  have sourceIn : regValue (GuardCompression.source L) u.basis=
      if s.basis L.sign then 2^257-1-regValue (GuardCompression.source L) s.basis
      else regValue (GuardCompression.source L) s.basis := by
    have h := GuardCompression.complement_read L.sign L.y (GuardCompression.source L) yND signAway
      (by intro q hq
          simp only [GuardCompression.source,BalancedCleanup.Layout.y,List.mem_append,List.mem_singleton] at hq ⊢
          itauto) s m
    simpa only [sourceLen] using h
  have sourceFit : regValue (GuardCompression.source L) s.basis<2^257 := by
    simpa only [sourceLen] using regValue_lt (GuardCompression.source L) s.basis
  have h := sub_inner_mode constant retired L hw hn member u m
    (by rw [keep L.parity (by simp),keep L.r0 (by
      simp [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]),parity])
    (by intro q hq qr;rw [keep q (by simp [cs,hq])];exact clean q hq qr) v fit extended
    (by
      rw [sourceIn]
      simp only [carryValue,keep L.sign (by simp)]
      cases constant <;> cases s.basis L.sign <;> simp [-Nat.reducePow] <;> omega)
    (by rw [sourceIn,targetIn]; simpa only [carryValue,keep L.sign (by simp)] using sum)
  let t := run (rawSubInnerMode constant retired L) m u
  let out := run S (m.drop (measurementCount (rawSubInnerMode constant retired L))) t
  have last := signComplement_correct L.sign L.y yND signAway t
    (m.drop (measurementCount (rawSubInnerMode constant retired L)))
  have st : t.basis L.sign=s.basis L.sign :=
    (h.2.2 _ signTarget).trans (keep _ (by simp))
  have outside (q : Wire) (hq : q∉rawTarget L) : out.basis q=s.basis q := by
    rw [GuardCompression.complement_bit L.sign L.y yND signAway t _ q,h.2.2 q hq,view q,st]
    by_cases mem : q∈L.y <;> simp [mem]
  have output : regValue (rawTarget L) out.basis=regValue (rawTarget L) t.basis :=
    regValue_congr _ _ _ (fun q hq => last.2.1 q (notY q (by simp [hq])))
  have actual : run (rawSubCoreMode constant retired L) m s=out := by
    rw [rawSubCoreMode,List.append_assoc,run_append,run_take,(signComplement_counts L.sign L.y).2,
      List.drop_zero,run_append,run_take]
  rw [actual]
  exact ⟨last.1.trans (h.1.trans first.1),output.trans h.2.1,outside⟩
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassRawBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


/-- Centered semantics are added after the arbitrary-word gate proof. -/
theorem rawAdd_signed (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (ready : RawReady L s.basis)
    (sign : s.basis L.sign=B)
    (source : signedRegValue (GuardCompression.source L) s.basis=Y)
    (target : signedRegValue (rawTarget L) s.basis=X)
    (clean : CleanExcept ((Q6Structural.q6Carry L).take 255) retired s.basis) :
    (run (Q6LifetimeResearch.rawAdd retired L) m s).phase=s.phase ∧
    WordFrame (rawTarget L) s.basis (encodeWord 257 (rawSum B X Y))
      (run (Q6LifetimeResearch.rawAdd retired L) m s).basis := by
  have h := rawAdd_correct retired L hw hn member s m ready.2 ready.1 clean
  have sl : (GuardCompression.source L).length=257 := by
    simp [GuardCompression.source,BalancedCleanup.Layout.y,hw.2.1]
  have tl : (rawTarget L).length=257 := by
    simp [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,hw.1]
  have sd : signedDecode 257 (regValue (GuardCompression.source L) s.basis)=Y := by
    simpa only [signedRegValue,sl] using source
  have td : signedDecode 257 (regValue (rawTarget L) s.basis)=X := by
    simpa only [signedRegValue,tl] using target
  have ar : signedIntegerValue B Y X=rawSum B X Y := by
    cases B <;> simp [signedIntegerValue,rawSum,signedY,sub_eq_add_neg]
  have rb := rawSum_bounds B X Y hx hy
  have co := constants
  have pow : ((2^256 : Nat) : Int)=2*((2^255 : Nat) : Int) := by
    rw [show 256=255+1 from rfl,Nat.pow_succ,Nat.cast_mul]
    ring
  have range : -((2^256 : Nat) : Int)≤rawSum B X Y ∧
      rawSum B X Y<((2^256 : Nat) : Int) := by omega
  have fit : regValue (GuardCompression.source L) s.basis<2^257 := by
    simpa only [sl] using regValue_lt (GuardCompression.source L) s.basis
  have lift := signedWordValue_lift 257 B (regValue (GuardCompression.source L) s.basis)
    (regValue (rawTarget L) s.basis) (by decide) fit
    (by simpa only [sd,td,ar,show 257-1=256 from rfl] using range.1)
    (by simpa only [sd,td,ar,show 257-1=256 from rfl] using range.2)
  rw [sd,td,ar] at lift
  refine ⟨h.1,?_,h.2.2⟩
  have signedOut : signedRegValue (rawTarget L)
      (run (Q6LifetimeResearch.rawAdd retired L) m s).basis=rawSum B X Y := by
    change signedDecode (rawTarget L).length _=rawSum B X Y
    rw [tl,h.2.1,sign]
    exact lift
  exact BalancedCircuit.word_encoding (rawTarget L) 257 tl _ _ signedOut


/-- Source sign-extension does not change its low parity bit. -/
theorem raw_source_parity (L : Layout) (hw : L.Widths) (s : BasisState) (Y : Int)
    (source : signedRegValue (GuardCompression.source L) s=Y) :
    s (L.ylow.getD 0 0)=originalParity Y := by
  cases e : L.ylow with
  | nil => have h := hw.2.1; simp [e] at h
  | cons a as =>
    apply word_parity a (as++[L.ymsb,L.ymsb]) s Y
    simpa [GuardCompression.source,BalancedCleanup.Layout.y,e,List.append_assoc] using source


/-- Lift an arbitrary full-state raw-word triple to the shared raw boundary. -/
theorem after_raw_of_word (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (T Y : Int) (program : Program) (s : State) (m : List Bool)
    (h : (run program m s).phase=s.phase ∧
      WordFrame (rawTarget L) s.basis (encodeWord 257 T) (run program m s).basis)
    (parity : s.basis L.parity=originalParity T) (ys : regValue L.y s.basis=encodeWord 256 Y)
    (clean : CleanExcept ((Q6Structural.q6Carry L).take 255) retired s.basis)
    (frame : HalfOutside L origin s.basis) :
    (run program m s).phase=s.phase ∧ AfterRaw standardEncoding L retired origin T Y (run program m s).basis := by
  have shape := active_carry_shape L hw
  have away (q : Wire) (hq : q∈[L.parity,L.lower]++L.y++L.carry) : q∉rawTarget L := by
    intro bad
    have n := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have l := List.count_pos_iff.mpr hq
    have r := List.count_pos_iff.mpr bad
    simp only [rawTarget,BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at n l r
    omega
  have retireNeLower : L.lower≠retired := by
    intro e
    have mem : retired∈L.carry := List.mem_of_mem_take (List.mem_of_mem_drop member)
    exact BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [e,mem])
  refine ⟨h.1,h.2.1,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => h.2.2 q (away q (by simp [hq])))).trans ys
  · exact (h.2.2 L.parity (away _ (by simp))).trans parity
  · rw [h.2.2 L.lower (away _ (by simp))]
    exact clean L.lower (by rw [shape];simp) retireNeLower
  · intro q hq qr
    rw [h.2.2 q (away q (by simp [List.mem_of_mem_take hq]))]
    exact clean q (by rw [shape];simp [hq]) qr
  · intro q hq hp hl ho
    exact (h.2.2 q (by simp only [rawTarget,List.mem_append,List.mem_singleton,not_or];exact ⟨hq,ho⟩)).trans
      (frame q hq hp hl ho)


/-- The standard raw boundary, including live parity, clean active scratch,
restored source and frozen whole-half outsider state. The seed itself is
outside this pass and its two invariants are explicit in RawReady. -/
theorem rawAdd_boundary (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y) :
    Triple (fun b => RawReady L b ∧ b L.sign=B ∧
      signedRegValue (GuardCompression.source L) b=Y ∧ signedRegValue (rawTarget L) b=X ∧
      regValue L.y b=encodeWord 256 Y ∧
      CleanExcept ((Q6Structural.q6Carry L).take 255) retired b ∧ HalfOutside L origin b)
      (Q6LifetimeResearch.rawAdd retired L)
      (AfterRaw standardEncoding L retired origin (rawSum B X Y) Y) := by
  intro s m hs
  rcases hs with ⟨ready,sign,source,target,ys,clean,frame⟩
  have h := rawAdd_signed retired L hw hn member B X Y hx hy s m ready sign source target clean
  have rt : signedRegValue (L.r0::(L.rtail++[L.rmsb,L.one])) s.basis=X := by
    simpa only [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.cons_append,
      List.append_assoc,List.singleton_append] using target
  have parityX := BalancedCircuit.word_parity L.r0 _ s.basis X rt
  have parityY := raw_source_parity L hw s.basis Y source
  have parityIn : s.basis L.parity=originalParity (rawSum B X Y) := by
    rw [ready.2,parityX,parityY,BalancedCircuit.raw_parity]
    cases originalParity X <;> cases originalParity Y <;> rfl
  exact after_raw_of_word retired L hw hn member origin _ Y
    (Q6LifetimeResearch.rawAdd retired L) s m h parityIn ys clean frame

end ECDSAAdd.Entrant.DirectPass

#print axioms ECDSAAdd.Entrant.DirectPass.rawAdd_boundary
end -- ticket 8 pasted module

-- ===== PassSubFinish =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


def subFinish (constant : Bool) (b a sign parity top one : Wire) : Program :=
  [.CX b parity,.CX a parity]++(if constant then [.CX sign parity,.X parity] else [])++[.CX top one]


theorem sub_finish_run (constant : Bool) (b a sign parity top one : Wire)
    (nd : [b,a,sign,parity,top,one].Nodup) (s : State) (m : List Bool)
    (ready : s.basis parity=(s.basis b ^^ s.basis a ^^ (if constant then s.basis sign ^^ true else false)))
    (coherent : s.basis one=s.basis top) :
    run (subFinish constant b a sign parity top one) m s=
      ⟨s.phase,writeBit (writeBit s.basis parity false) one false⟩ := by
  have ne := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ne
  apply State.extensionality
  · cases constant <;> rfl
  · funext q
    by_cases qp : q=parity
    · subst q
      cases constant <;> cases hb : s.basis b <;> cases ha : s.basis a <;>
        cases hs : s.basis sign <;>
        simp_all [subFinish,run,writeBit,ne_comm]
    · by_cases qo : q=one
      · subst q
        cases constant <;> simp_all [subFinish,run,writeBit,ne_comm]
      · cases constant <;> simp [subFinish,run,writeBit,qp,qo]

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubBoundary =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


def AfterHalf (L : Layout) (retired : Wire) (origin : BasisState)
    (X Y : Int) (b : BasisState) : Prop :=
  regValue L.r b=encodeWord 256 X ∧ regValue L.y b=encodeWord 256 Y ∧
  LiveFlags L false false false b ∧ CleanExcept (L.carry.take 254) retired b ∧
  HalfOutside L origin b


theorem extended_bits (lo : List Wire) (t z : Wire) (b : BasisState)
    (extended : Extended lo.length (regValue (lo++[t,z]) b)) : b z=b t := by
  have low := regValue_lt lo b
  rw [regValue_append] at extended
  simp only [regValue] at low
  cases ht : b t <;> cases hz : b z <;>
    simp [Extended,regValue,ht,hz] at extended ⊢ <;> omega


/-- The exact raw subtraction including the final parity and top-copy
cleanup; the encoded result is centered, so no extra half premise is needed. -/
theorem rawSub_boundary_math (constant : Bool) (retired : Wire) (L : Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (B : Bool) (X Y T : Int)
    (hx : -((2^255 : Nat) : Int)≤X ∧ X<((2^255 : Nat) : Int))
    (hy : -((2^255 : Nat) : Int)≤Y ∧ Y<((2^255 : Nat) : Int))
    (ht : -((2^256 : Nat) : Int)≤T ∧ T<((2^256 : Nat) : Int))
    (addition : ((if B then 2^257-1-encodeWord 257 Y else encodeWord 257 Y)+encodeWord 257 X+
      (if constant then true else B).toNat)%2^257=encodeWord 257 T)
    (parityLaw : originalParity T=(originalParity X ^^ originalParity Y ^^ (if constant then B ^^ true else false)))
    (signOrigin : origin L.sign=B) :
    Triple (AfterRaw standardEncoding L retired origin T Y)
      (if constant then P1Life.rawSub retired L else Q6LifetimeResearch.rawSubTail retired L)
      (AfterHalf L retired origin X Y) := by
  have widths := BalancedCleanup.widths L.toLayout hw
  have tlen : (rawTarget L).length=257 := by
    simp [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,hw.1]
  have slen : (GuardCompression.source L).length=257 := by
    simp [GuardCompression.source,BalancedCleanup.Layout.y,hw.2.1]
  have shape := active_carry_shape L hw
  have y0 : L.ylow.getD 0 0∈L.y := by
    have ne : 0<L.ylow.length := by rw [hw.2.1];omega
    rw [List.getD_eq_getElem _ _ ne]
    simp [BalancedCleanup.Layout.y,List.getElem_mem]
  have flagND : [L.sign,L.parity,L.lower,L.one,L.r0,L.rmsb,L.ylow.getD 0 0].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have p := (List.count_pos_iff.mpr y0)
    have yr : ∀x,List.count x [L.ylow.getD 0 0]≤List.count x L.y := by
      intro x
      by_cases e : L.ylow.getD 0 0=x
      · rw [←e]
        simp only [List.count_cons,List.count_nil,beq_self_eq_true,if_true,Nat.add_zero]
        omega
      · simp only [List.count_cons,List.count_nil,beq_iff_eq,e,if_false,Nat.zero_add]
        exact Nat.zero_le _
    have lim := yr q
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_cons,List.count_append,List.count_nil] at h lim ⊢
    omega
  have ne := flagND
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ne
  have away (q : Wire) (hq : q∈[L.sign,L.parity,L.lower]++L.y++L.carry) : q∉rawTarget L := by
    intro bad
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [rawTarget,BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h a b
    omega
  have finishAway (q : Wire) (hq : q∈L.r++L.y++L.carry++[L.lower]) : q≠L.parity ∧ q≠L.one := by
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have p := List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,List.count_nil] at h p
    constructor <;> intro e <;> subst q <;>
      simp only [beq_self_eq_true,if_true] at h p <;> omega
  intro s m hs
  rcases hs with ⟨raw,ys,parity,lower,clean,frame⟩
  change regValue (rawTarget L) s.basis=encodeWord 257 (T) at raw
  change regValue L.y s.basis=encodeWord 256 Y at ys
  change s.basis L.parity=originalParity (T) at parity
  have yrange := hy
  have yd : signedRegValue L.y s.basis=Y := by
    unfold signedRegValue
    rw [widths.2.2.1,ys]
    exact decode_encodeWord 256 (by decide) Y yrange
  have sd : signedRegValue (GuardCompression.source L) s.basis=Y :=
    (signed_extension L.ylow L.ymsb L.ymsb s.basis rfl).trans yd
  have sc : regValue (GuardCompression.source L) s.basis=encodeWord 257 Y :=
    word_encoding _ 257 slen _ _ sd
  have trange := ht
  have td : signedRegValue (rawTarget L) s.basis=T := by
    unfold signedRegValue
    rw [tlen,raw]
    exact decode_encodeWord 257 (by decide) _ trange
  have bit : s.basis L.r0=originalParity (T) := by
    apply word_parity L.r0 (L.rtail++[L.rmsb,L.one]) s.basis _
    simpa only [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.cons_append,
      List.append_assoc,List.singleton_append] using td
  have sign : s.basis L.sign=B := (frame L.sign (fun h => away L.sign (by simp)
    (by simp [rawTarget,h])) (by itauto) (by itauto) (by itauto)).trans signOrigin
  have xrange := hx
  have h := sub_core_mode constant retired L hw hn member s m (parity.trans bit.symm)
    (by intro q hq qr;rw [shape,List.mem_append,List.mem_singleton] at hq
        rcases hq with hq|rfl
        · exact clean q hq qr
        · exact lower)
    (encodeWord 257 X) (encodeWord_bound _ _) (encoded_extended 255 X xrange)
    (by rw [sc,raw];simpa only [carryValue,sign] using addition)
  let u := run (rawSubCoreMode constant retired L) m s
  have ud : signedRegValue (rawTarget L) u.basis=X := by
    unfold signedRegValue
    rw [tlen,h.2.1]
    exact decode_encodeWord 257 (by decide) X (by omega)
  have equalTop : u.basis L.one=u.basis L.rmsb := by
    apply extended_bits L.low L.rmsb L.one u.basis
    have e : L.low++[L.rmsb,L.one]=rawTarget L := by
      simp [rawTarget,BalancedCleanup.Layout.r,List.append_assoc]
    rw [e]
    rw [widths.1,h.2.1]
    exact encoded_extended 255 X xrange
  have ur : signedRegValue L.r u.basis=X :=
    (signed_extension L.low L.rmsb L.one u.basis equalTop).symm.trans ud
  have rvalue := word_encoding L.r 256 widths.2.1 u.basis X ur
  have ub : u.basis L.r0=originalParity X := by
    apply word_parity L.r0 (L.rtail++[L.rmsb]) u.basis X
    simpa only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.cons_append] using ur
  have yp := raw_source_parity L hw s.basis Y sd
  have up : u.basis L.parity=originalParity (T) :=
    (h.2.2 _ (away _ (by simp))).trans parity
  have uy : u.basis (L.ylow.getD 0 0)=originalParity Y :=
    (h.2.2 _ (away _ (List.mem_append_left _ (List.mem_append_right _ y0)))).trans yp
  have usign : u.basis L.sign=B := (h.2.2 _ (away _ (by simp))).trans sign
  let finish := subFinish constant L.r0 (L.ylow.getD 0 0) L.sign L.parity L.rmsb L.one
  let v := run finish [] u
  have nd6 : [L.r0,L.ylow.getD 0 0,L.sign,L.parity,L.rmsb,L.one].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have n := List.nodup_iff_count.mp flagND q
    simp only [List.count_cons,List.count_nil] at n ⊢
    omega
  have ready : u.basis L.parity=(u.basis L.r0 ^^ u.basis (L.ylow.getD 0 0) ^^
      (if constant then u.basis L.sign ^^ true else false)) := by
    rw [up,ub,uy,usign]
    exact parityLaw
  have last := sub_finish_run constant L.r0 (L.ylow.getD 0 0) L.sign L.parity L.rmsb L.one nd6 u [] ready equalTop
  have vk (q : Wire) (qp : q≠L.parity) (qo : q≠L.one) : v.basis q=u.basis q := by
    change (run finish [] u).basis q=_
    rw [last]
    simp [writeBit,qp,qo]
  have vphase : v.phase=u.phase := by
    change (run finish [] u).phase=u.phase
    rw [last]
  have vp : v.basis L.parity=false := by
    change (run finish [] u).basis L.parity=_
    rw [last]
    have po : L.parity≠L.one := by itauto
    simp [writeBit,po]
  have vo : v.basis L.one=false := by
    change (run finish [] u).basis L.one=_
    rw [last]
    simp [writeBit]
  have sourceShape : GuardCompression.source L=L.ylow.getD 0 0::
      (L.ylow.drop 1++[L.ymsb,L.ymsb]) := by
    have split : L.ylow=L.ylow.getD 0 0::L.ylow.drop 1 := by
      cases e : L.ylow with
      | nil => have w := hw.2.1;simp [e] at w
      | cons a as => rfl
    simp only [GuardCompression.source,BalancedCleanup.Layout.y]
    rw [split]
    simp only [List.cons_append,List.append_assoc,List.singleton_append,List.nil_append,List.getD_cons_zero,List.drop_succ_cons,List.drop_zero]
  have actual : (if constant then P1Life.rawSub retired L else Q6LifetimeResearch.rawSubTail retired L)=
      rawSubCoreMode constant retired L++finish := by
    cases constant <;>
      simp only [P1Life.rawSub,Q6LifetimeResearch.rawSubTail,rawSubCoreMode,rawSubInnerMode,rawSubHeadMode,
      carryMajor,carryErase,carrySum,carryStep,Bool.false_eq_true,if_false,if_true,subFinish,
      Q6LifetimeResearch.move,sourceShape,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,rawTarget,List.getD_cons_zero,
      List.drop_succ_cons,List.drop_zero,List.drop_append,List.length_cons,List.length_nil,
      List.cons_append,List.singleton_append,List.nil_append,List.append_assoc,Nat.zero_sub,List.reverse_cons,List.reverse_nil,List.append_nil,finish]
  have zero : measurementCount finish=0 := by cases constant <;> rfl
  rw [actual,run_append,run_take,zero_records finish zero]
  refine ⟨vphase.trans h.1,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr L.r v.basis u.basis (fun q hq =>
      vk q (finishAway q (by simp [hq])).1 (finishAway q (by simp [hq])).2)).trans rvalue
  · exact (regValue_congr _ _ _ (fun q hq => (vk q (finishAway q (by simp [hq])).1
      (finishAway q (by simp [hq])).2).trans (h.2.2 q (away q (by simp [hq]))))).trans ys
  · exact ⟨vp,(vk _ (finishAway _ (by simp)).1 (finishAway _ (by simp)).2).trans
      ((h.2.2 _ (away _ (by simp))).trans lower),vo⟩
  · intro q hq qr
    have cq := List.mem_of_mem_take hq
    exact (vk q (finishAway q (by simp [cq])).1 (finishAway q (by simp [cq])).2).trans
      ((h.2.2 q (away q (by simp [cq]))).trans (clean q hq qr))
  · intro q hq hp hl ho
    have qa : q∉rawTarget L := by simp [rawTarget,hq,ho]
    exact (vk q hp ho).trans ((h.2.2 q qa).trans (frame q hq hp hl ho))


theorem rawSub_boundary (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (signOrigin : origin L.sign=B) :
    Triple (AfterRaw standardEncoding L retired origin (rawSum B X Y) Y)
      (Q6LifetimeResearch.rawSubTail retired L) (AfterHalf L retired origin X Y) := by
  have hp := constants
  have rx : -((2^255 : Nat) : Int)≤X ∧ X<((2^255 : Nat) : Int) := by unfold Centered at hx; omega
  have ry : -((2^255 : Nat) : Int)≤Y ∧ Y<((2^255 : Nat) : Int) := by unfold Centered at hy; omega
  have rb := rawSum_bounds B X Y hx hy
  have rt : -((2^256 : Nat) : Int)≤rawSum B X Y ∧ rawSum B X Y<((2^256 : Nat) : Int) := by
    norm_num [q,p] at rb ⊢; omega
  apply rawSub_boundary_math false retired L hw hn member origin B X Y (rawSum B X Y) rx ry rt
  · have bound := encodeWord_bound 257 Y
    simp only [Bool.false_eq_true,if_false]
    rw [signed_view_add _ _ _ _ bound]
    exact signed_encoded_add 257 B X Y
  · simpa [Bool.xor_comm] using raw_parity B X Y
  · exact signOrigin

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSignedMagnitude =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedField


theorem magnitude_wide_bounds (R : Int)
    (hr : -((2^255 : Nat) : Int)≤R ∧ R<((2^255 : Nat) : Int)) :
    0≤magnitude R ∧ magnitude R<((2^255 : Nat) : Int) := by
  by_cases rn : R<0 <;> simp [magnitude,negative,rn] <;> omega


theorem magnitude_code_wide (R : Int)
    (hr : -((2^255 : Nat) : Int)≤R ∧ R<((2^255 : Nat) : Int)) :
    encodeWord 255 (magnitude R)=(magnitude R).toNat := by
  have hb := magnitude_wide_bounds R hr
  exact BalancedCleanup.encoded_nonnegative _ _ hb.1 hb.2


theorem magnitude_encoded_wide (R : Int)
    (hr : -((2^255 : Nat) : Int)≤R ∧ R<((2^255 : Nat) : Int)) :
    (if negative R then 2^256-1-encodeWord 256 R else encodeWord 256 R)=(magnitude R).toNat := by
  by_cases rn : R<0
  · simp only [negative,rn,decide_true,if_true,magnitude]
    rw [BalancedCleanup.complement_encoded]
    exact BalancedCleanup.encoded_nonnegative _ _ (by omega) (by norm_num; omega)
  · simp only [negative,rn,decide_false,Bool.false_eq_true,if_false,magnitude]
    exact BalancedCleanup.encoded_nonnegative _ _ (by omega) (by norm_num; omega)


theorem prepare_sign_value_wide (L : BalancedCleanup.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : -((2^255 : Nat) : Int)≤R ∧ R<((2^255 : Nat) : Int))
    (s : State) (m : List Bool) (hs : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) :
    let t := run (BalancedCleanup.prepareSign L) m s
    regValue L.r t.basis=(magnitude R).toNat ∧ t.basis L.lower=negative R ∧
    ∀q,q∉L.r → q≠L.lower → t.basis q=s.basis q := by
  have w := BalancedCleanup.widths L hw
  have decode : signedRegValue L.r s.basis=R := by
    unfold signedRegValue
    rw [w.2.1,hs]
    exact decode_encodeWord 256 (by decide) R hr
  have msb := BalancedCircuit.word_sign L.low L.rmsb s.basis R decode
  let c : State := ⟨s.phase,writeBit s.basis L.lower (s.basis L.lower ^^ s.basis L.rmsb)⟩
  have la : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have nd := (List.nodup_append'.mp (L.dataND hn)).1
  have before : regValue L.r c.basis=regValue L.r s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [c,writeBit,show q≠L.lower from fun e => la (e ▸ hq)])
  have lc : c.basis L.lower=negative R := by simp [c,writeBit,hz,msb,negative]
  have body := signComplement_correct L.lower L.r nd la c m
  have first (r : List Bool) : run [.CX L.rmsb L.lower] r s=c := rfl
  simp only [BalancedCleanup.prepareSign,run_append,measurementCount,List.take_zero,List.drop_zero,first]
  refine ⟨?_,(body.2.1 L.lower la).trans lc,?_⟩
  · rw [body.2.2,before,hs,lc,w.2.1,magnitude_encoded_wide R hr]
  · intro q hq hl
    exact (body.2.1 q hq).trans (by simp [c,writeBit,hl])

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassPrepareSign =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField

/-- The inverse half starts from the ordinary centered word and prepares
its complemented magnitude and negative selector, with a clean top host. -/
theorem prepare_sign_boundary_wide (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (origin : BasisState) (R Y : Int) (hr : -((2^255 : Nat) : Int)≤R ∧ R<((2^255 : Nat) : Int)) :
    Triple (AfterHalf L retired origin R Y) (BalancedCleanup.prepareSign L.toLayout)
      (AfterUnnormalize standardEncoding L retired origin R Y) := by
  have n0 : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have widths := BalancedCleanup.widths L.toLayout hw
  have away (q : Wire) (hq : q∈[L.parity,L.one]++L.y++L.carry) : q∉L.r ∧ q≠L.lower := by
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have p := List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,List.count_nil] at p
    refine ⟨?_,?_⟩
    · intro bad
      have b := List.count_pos_iff.mpr bad
      simp only [List.count_cons,List.count_append] at h
      omega
    · intro e
      subst q
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  intro s m hs
  rcases hs with ⟨value,ys,flags,clean,frame⟩
  rcases flags with ⟨parity,lower,one⟩
  have h := prepare_sign_value_wide L.toLayout hw n0 R hr s m value lower
  let u := run (BalancedCleanup.prepareSign L.toLayout) m s
  have top0 : u.basis L.rmsb=false := by
    have b := magnitude_wide_bounds R hr
    have c := constants
    have cast := Int.toNat_of_nonneg b.1
    have top := regValue_highBit L.low L.rmsb u.basis
    change u.basis L.rmsb=true ↔ 2^L.low.length≤regValue L.r u.basis at top
    rw [widths.1,h.1] at top
    cases e : u.basis L.rmsb <;> simp [e] at top ⊢ <;> omega
  have low : regValue L.low u.basis=encodeWord 255 (BalancedField.magnitude R) := by
    have a := h.1
    change regValue (L.low++[L.rmsb]) u.basis=_ at a
    rw [regValue_append] at a
    simpa [regValue,top0,magnitude_code_wide R hr] using a
  have keep (q : Wire) (hq : q∈[L.parity,L.one]++L.y++L.carry) : u.basis q=s.basis q :=
    h.2.2 q (away q hq).1 (away q hq).2
  refine ⟨run_no_measurement_phase _
    (properProgram_measurementCount _ (BalancedCleanup.prepareSign_proper L.toLayout n0)) s m,
    low,top0,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans ys
  · exact ⟨(keep _ (by simp)).trans parity,h.2.1,(keep _ (by simp)).trans one⟩
  · intro q hq qr
    exact (keep q (by simp [List.mem_of_mem_take hq])).trans (clean q hq qr)
  · intro q hq hp hl ho
    exact (h.2.2 q hq hl).trans (frame q hq hp hl ho)
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassRestoreSign =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


/-- Undo the magnitude view after literal unnormalization. -/
theorem restore_sign_boundary_values (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (origin : BasisState) (R : Int) (Y : Nat) (P : Bool)
    (hr : -((2^255 : Nat) : Int)≤R ∧ R<((2^255 : Nat) : Int)) :
    Triple (LowBoundary L retired origin (encodeWord 255 (magnitude R)) Y P (negative R))
      (BalancedCleanup.prepareSign L.toLayout).reverse
      (WordBoundary L retired origin (encodeWord 256 R) Y P) := by
  have n0 : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have widths := BalancedCleanup.widths L.toLayout hw
  have rND : L.r.Nodup := (List.nodup_append'.mp (L.toLayout.dataND n0)).1
  have lowerAway : L.lower∉L.r := fun h => BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [h])
  have away (q : Wire) (hq : q∈[L.parity,L.one]++L.y++L.carry) : q∉L.r ∧ q≠L.lower := by
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have p := List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,List.count_nil] at p
    refine ⟨?_,?_⟩
    · intro bad
      have b := List.count_pos_iff.mpr bad
      simp only [List.count_cons,List.count_append] at h
      omega
    · intro e
      subst q
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  intro s m hs
  rcases hs with ⟨low,top,ys,flags,clean,frame⟩
  rcases flags with ⟨parity,lower,one⟩
  change s.basis L.lower=negative R at lower
  have value : regValue L.r s.basis=(BalancedField.magnitude R).toNat := by
    change regValue (L.low++[L.rmsb]) s.basis=_
    rw [regValue_append,low]
    simp [regValue,top,standardEncoding,magnitude_code_wide R hr]
  let u := run (signComplement L.lower L.r) m s
  have comp := signComplement_correct L.lower L.r rND lowerAway s m
  have uv : regValue L.r u.basis=encodeWord 256 R := by
    rw [comp.2.2,value,widths.2.1,lower]
    have mag := magnitude_encoded_wide R hr
    have fit := encodeWord_bound 256 R
    cases e : negative R <;> simp only [e,if_false,if_true,Bool.false_eq_true] at mag ⊢ <;> omega
  have ul : u.basis L.lower=negative R := (comp.2.1 _ lowerAway).trans lower
  have range := hr
  have decoded : signedRegValue L.r u.basis=R := by
    unfold signedRegValue
    rw [widths.2.1,uv]
    exact decode_encodeWord 256 (by decide) R range
  have ut : u.basis L.rmsb=negative R := word_sign L.low L.rmsb u.basis R decoded
  let v := run [.CX L.rmsb L.lower] [] u
  have vk (q : Wire) (hq : q≠L.lower) : v.basis q=u.basis q := by simp [v,run,writeBit,hq]
  have vl : v.basis L.lower=false := by simp [v,run,writeBit,ul,ut]
  have keep (q : Wire) (hq : q∈[L.parity,L.one]++L.y++L.carry) : v.basis q=s.basis q :=
    (vk q (away q hq).2).trans (comp.2.1 q (away q hq).1)
  have actual : run (BalancedCleanup.prepareSign L.toLayout).reverse m s=v := by
    simp only [BalancedCleanup.prepareSign,List.reverse_append,List.reverse_singleton,
      run_append,run_take]
    rw [BiasedInverse.complement_reverse L.lower L.r rND lowerAway]
    rfl
  rw [actual]
  refine ⟨comp.1,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => vk q (fun e => lowerAway (e ▸ hq)))).trans uv
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans ys
  · exact ⟨(keep _ (by simp)).trans parity,vl,(keep _ (by simp)).trans one⟩
  · intro q hq qr
    exact (keep q (by simp [List.mem_of_mem_take hq])).trans (clean q hq qr)
  · intro q hq hp hl ho
    exact (vk q hl).trans ((comp.2.1 q hq).trans (frame q hq hp hl ho))


theorem restore_sign_boundary_wide (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (origin : BasisState) (R Y : Int) (hr : -((2^255 : Nat) : Int)≤R ∧ R<((2^255 : Nat) : Int)) :
    Triple (AfterUnnormalize standardEncoding L retired origin R Y)
      (BalancedCleanup.prepareSign L.toLayout).reverse (AfterHalf L retired origin R Y) := by
  exact restore_sign_boundary_values retired L hw hn origin R (encodeWord 256 Y) false hr




end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSeed =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


def seedMode (constant : Bool) (L : Layout) : Program :=
  if constant then P1Life.p1Seed L else GuardCompression.seed L


def SeedFacts (constant : Bool) (L : Layout) (retired : Wire)
    (origin : BasisState) (B : Bool) (X Y : Int) (b : BasisState) : Prop :=
  b L.one=b L.rmsb ∧
  b L.parity=(b L.r0 ^^ b (L.ylow.getD 0 0) ^^ (b L.sign ^^ carryValue constant L.sign b)) ∧
  b L.sign=B ∧ signedRegValue (GuardCompression.source L) b=Y ∧
  signedRegValue (rawTarget L) b=X ∧ regValue L.y b=encodeWord 256 Y ∧
  CleanExcept ((Q6Structural.q6Carry L).take 255) retired b ∧ HalfOutside L origin b


theorem seed_prepare (constant : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState)
    (X Y : Int) (hx : -((2^255 : Nat) : Int)≤X ∧ X<((2^255 : Nat) : Int))
    (hy : -((2^255 : Nat) : Int)≤Y ∧ Y<((2^255 : Nat) : Int)) :
    Triple (AfterHalf L retired origin X Y)
      (seedMode constant L)
      (SeedFacts constant L retired origin (origin L.sign) X Y) := by
  have widths := BalancedCleanup.widths L.toLayout hw
  have dataAway (q : Wire) (hq : q∈L.r++L.y++L.carry++[L.lower,L.sign]) :
      q≠L.parity ∧ q≠L.one := by
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have p := List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,List.count_nil] at h p
    constructor <;> intro e <;> subst q <;>
      simp only [beq_self_eq_true,if_true] at h p <;> omega
  have po : L.parity≠L.one := by
    intro e
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) L.one
    simp only [List.count_cons,List.count_append,List.count_nil,e,beq_self_eq_true,if_true] at h
    omega
  have y0 : L.ylow.getD 0 0∈L.y := by
    have h : 0<L.ylow.length := by rw [hw.2.1];omega
    rw [List.getD_eq_getElem _ _ h]
    simp [BalancedCleanup.Layout.y,List.getElem_mem]
  have qy := dataAway (L.ylow.getD 0 0) (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ y0)))
  have q0 := dataAway L.r0 (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
  have qt := dataAway L.rmsb (by simp [BalancedCleanup.Layout.r])
  intro s m hs
  rcases hs with ⟨value,ys,flags,clean,frame⟩
  rcases flags with ⟨parity,lower,one⟩
  let u := run (seedMode constant L) [] s
  have keep (q : Wire) (qp : q≠L.parity) (qo : q≠L.one) : u.basis q=s.basis q := by
    cases constant <;> simp [u,seedMode,GuardCompression.seed,P1Life.p1Seed,run,writeBit,qp,qo]
  have top : u.basis L.one=u.basis L.rmsb := by
    cases constant <;> simp [u,seedMode,GuardCompression.seed,P1Life.p1Seed,run,writeBit,Ne.symm po,qt.1,qt.2,one]
  have y1 : (L.ylow[0]?.getD 0)≠L.one := qy.2
  have qs := dataAway L.sign (by simp)
  have seedParity : u.basis L.parity=(u.basis L.r0 ^^ u.basis (L.ylow.getD 0 0) ^^
      (u.basis L.sign ^^ carryValue constant L.sign u.basis)) := by
    rw [keep L.r0 q0.1 q0.2,keep _ qy.1 qy.2]
    have sg := keep L.sign qs.1 qs.2
    simp only [carryValue,sg]
    cases constant <;> cases h0 : s.basis L.r0 <;>
      cases hy0 : s.basis (L.ylow.getD 0 0) <;> cases hs0 : s.basis L.sign
    all_goals
      change s.basis (L.ylow[0]?.getD 0)=_ at hy0
      simp [u,seedMode,GuardCompression.seed,P1Life.p1Seed,run,writeBit,
        po,q0.1,q0.2,qy.1,qy.2,y1,parity,qs.1,qs.2,h0,hy0,hs0,ne_comm]
  have ur : regValue L.r u.basis=encodeWord 256 X :=
    (regValue_congr _ _ _ (fun q hq => keep q (dataAway q (by simp [hq])).1
      (dataAway q (by simp [hq])).2)).trans value
  have uy : regValue L.y u.basis=encodeWord 256 Y :=
    (regValue_congr _ _ _ (fun q hq => keep q (dataAway q (by simp [hq])).1
      (dataAway q (by simp [hq])).2)).trans ys
  have rdecode : signedRegValue L.r u.basis=X := by
    unfold signedRegValue
    rw [widths.2.1,ur]
    exact decode_encodeWord 256 (by decide) X hx
  have ydecode : signedRegValue L.y u.basis=Y := by
    unfold signedRegValue
    rw [widths.2.2.1,uy]
    exact decode_encodeWord 256 (by decide) Y hy
  have target : signedRegValue (rawTarget L) u.basis=X :=
    (signed_extension L.low L.rmsb L.one u.basis top).trans rdecode
  have source : signedRegValue (GuardCompression.source L) u.basis=Y :=
    (signed_extension L.ylow L.ymsb L.ymsb u.basis rfl).trans ydecode
  have signAway : L.sign∉L.r := fun bad => BalancedCircuit.flagAway L hn L.sign (by simp) (by simp [bad])
  have signNe : L.sign≠L.parity ∧ L.sign≠L.lower ∧ L.sign≠L.one := by
    have n := scalarND L hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at n
    tauto
  have sign : u.basis L.sign=origin L.sign :=
    (keep _ signNe.1 signNe.2.2).trans (frame _ signAway signNe.1 signNe.2.1 signNe.2.2)
  have active := active_carry_shape L hw
  have carry : CleanExcept ((Q6Structural.q6Carry L).take 255) retired u.basis := by
    intro q hq qr
    rw [active,List.mem_append,List.mem_singleton] at hq
    rcases hq with hq|rfl
    · have cq := List.mem_of_mem_take hq
      rw [keep q (dataAway q (by simp [cq])).1 (dataAway q (by simp [cq])).2]
      exact clean q hq qr
    · exact (keep _ (dataAway _ (by simp)).1 (dataAway _ (by simp)).2).trans lower
  have outside : HalfOutside L origin u.basis := by
    intro q hq hp hl ho
    exact (keep q hp ho).trans (frame q hq hp hl ho)
  have zero : measurementCount (seedMode constant L)=0 := by cases constant <;> rfl
  rw [zero_records _ zero s m]
  refine ⟨?_,top,seedParity,sign,source,target,uy,carry,outside⟩
  exact run_no_measurement_phase _ zero s []


theorem seed_to_raw (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState)
    (X Y : Int) (hx : Centered X) (hy : Centered Y) :
    Triple (AfterHalf L retired origin X Y)
      (GuardCompression.seed L++Q6LifetimeResearch.rawAdd retired L)
      (AfterRaw standardEncoding L retired origin (rawSum (origin L.sign) X Y) Y) := by
  have rx : -((2^255 : Nat) : Int)≤X ∧ X<((2^255 : Nat) : Int) := by
    have hp := constants; unfold Centered at hx; omega
  have ry : -((2^255 : Nat) : Int)≤Y ∧ Y<((2^255 : Nat) : Int) := by
    have hp := constants; unfold Centered at hy; omega
  have prep : Triple (AfterHalf L retired origin X Y) (GuardCompression.seed L)
      (fun b => RawReady L b ∧ b L.sign=origin L.sign ∧
        signedRegValue (GuardCompression.source L) b=Y ∧ signedRegValue (rawTarget L) b=X ∧
        regValue L.y b=encodeWord 256 Y ∧
        CleanExcept ((Q6Structural.q6Carry L).take 255) retired b ∧ HalfOutside L origin b) := by
    intro s m hs
    have h := seed_prepare false retired L hw hn member origin X Y rx ry s m hs
    rcases h with ⟨phase,top,pv,sign,source,target,ys,clean,frame⟩
    exact ⟨phase,⟨top,by simpa [carryValue] using pv⟩,sign,source,target,ys,clean,frame⟩
  exact Triple.seq prep (rawAdd_boundary retired L hw hn member origin (origin L.sign) X Y hx hy)

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== P1OddRep =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


def OddDomain (R : Int) : Prop := -q-1≤R ∧ R≤q-1


def oddRep (x : Fp) : Int :=
  let z := centerFp x
  if z<0 then z+q else z-q-1


def oddWord (x : Fp) : Nat := encodeWord 256 (oddRep x)


def oddDecode (R : Int) : Fp := (R : Fp)+1/2


theorem p1_two_ne_zero : (2 : Fp)≠0 := by decide


theorem p1_q_field : (q : Fp)+1/2=0 := by
  have eq := congrArg (fun z : Int => (z : Fp)) constants.2.1
  have qp : (2 : Fp)*(q : Fp)+1=0 := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,ZMod.natCast_self] using eq.symm
  apply (mul_left_cancel₀ p1_two_ne_zero)
  calc
    (2 : Fp)*((q : Fp)+1/2)=2*(q : Fp)+1 := by field_simp [p1_two_ne_zero]
    _=2*0 := by simpa using qp


theorem oddRep_bounds (x : Fp) : OddDomain (oddRep x) := by
  have hz := centerFp_bounds x
  unfold Centered at hz
  dsimp only [oddRep,OddDomain]
  split_ifs <;> omega


theorem oddRep_field (x : Fp) : oddDecode (oddRep x)=x := by
  have hq := p1_q_field
  dsimp only [oddDecode,oddRep]
  split_ifs
  · push_cast
    rw [add_assoc,hq,add_zero,centerFp_cast]
  · push_cast
    calc
      (centerFp x : Fp)-(q : Fp)-1+1/2=(centerFp x : Fp) := by
        field_simp [p1_two_ne_zero] at hq ⊢
        linear_combination -hq
      _=x := centerFp_cast x


theorem oddDomain_unique (R T : Int) (hr : OddDomain R) (ht : OddDomain T)
    (eq : oddDecode R=oddDecode T) : R=T := by
  have fieldEq : ((R+1 : Int) : Fp)=((T+1 : Int) : Fp) := by
    simp only [oddDecode] at eq
    push_cast
    linear_combination eq
  have u := centered_cast_unique (R+1) (T+1)
    (by unfold OddDomain at hr; unfold Centered; omega)
    (by unfold OddDomain at ht; unfold Centered; omega) fieldEq
  omega


theorem oddRep_inverse (R : Int) (hr : OddDomain R) : oddRep (oddDecode R)=R :=
  oddDomain_unique _ _ (oddRep_bounds _) hr (oddRep_field _)





























































end ECDSAAdd.Entrant.P1Life



end -- ticket 8 pasted module

-- ===== P1FoldMath =====
section
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


def oddViewed (s : Bool) (Y : Int) : Int := if s then -Y-1 else Y


def oddSum (s : Bool) (R Y : Int) : Int := R+oddViewed s Y+1


def oddFold (S : Int) : Int :=
  if S%2≠0 then S/2 else if S<0 then S/2+q else S/2-q-1







theorem oddSum_bounds (s : Bool) (R Y : Int) (hr : OddDomain R) (hy : OddDomain Y) :
    -(p : Int)≤oddSum s R Y ∧ oddSum s R Y≤(p : Int)-1 := by
  have hp := constants
  unfold OddDomain at hr hy
  cases s <;> simp only [oddSum,oddViewed,Bool.false_eq_true,if_false,if_true] <;> omega


theorem oddSum_field (s : Bool) (R Y : Int) :
    (oddSum s R Y : Fp)=oddDecode R+(if s then -oddDecode Y else oddDecode Y) := by
  cases s <;> simp only [oddSum,oddViewed,oddDecode,Bool.false_eq_true,if_false,if_true]
  all_goals push_cast; field_simp [p1_two_ne_zero] <;> ring


theorem oddFold_bounds (S : Int)
    (hs : -(p : Int)≤S ∧ S≤(p : Int)-1) : OddDomain (oddFold S) := by
  have hp := constants
  unfold oddFold OddDomain
  split_ifs <;> omega


theorem oddFold_double (S : Int) :
    2*oddFold S+1=
      if S%2≠0 then S else if S<0 then S+(p : Int) else S-(p : Int) := by
  have hp := constants
  unfold oddFold
  split_ifs <;> omega


theorem oddFold_field (S : Int) : oddDecode (oddFold S)=(S : Fp)/2 := by
  have hc := congrArg (fun z : Int => (z : Fp)) (oddFold_double S)
  have twice : (2 : Fp)*(oddFold S : Fp)+1=(S : Fp) := by
    split_ifs at hc <;> simpa [Int.cast_add,Int.cast_sub,Int.cast_mul] using hc
  unfold oddDecode
  field_simp [p1_two_ne_zero]
  linear_combination twice


theorem oddFold_sign (S : Int)
    (hs : -(p : Int)≤S ∧ S≤(p : Int)-1) :
    decide (oddFold S<0)= !(decide (S<0) ^^ originalParity S) := by
  have hp := constants
  have d := oddFold_double S
  by_cases po : S%2≠0 <;> by_cases sn : S<0
  all_goals
    simp [po,sn] at d
    have sg : (oddFold S<0) ↔ (if S%2≠0 then S<0 else ¬S<0) := by
      simp [po,sn]
      omega
    simp [sg,po,sn,originalParity]

















theorem oddFold_contract (s : Bool) (R Y : Int) (hr : OddDomain R) (hy : OddDomain Y) :
    oddFold (oddSum s R Y)=
      oddRep ((oddDecode R+(if s then -oddDecode Y else oddDecode Y))/2) := by
  apply oddDomain_unique _ _ (oddFold_bounds _ (oddSum_bounds s R Y hr hy)) (oddRep_bounds _)
  rw [oddRep_field,oddFold_field,oddSum_field]


def oddInverse (s : Bool) (F Y : Int) : Int :=
  oddRep (2*oddDecode F-(if s then -oddDecode Y else oddDecode Y))













theorem oddForward_inverse (s : Bool) (F Y : Int) (hf : OddDomain F) (hy : OddDomain Y) :
    oddFold (oddSum s (oddInverse s F Y) Y)=F := by
  apply oddDomain_unique _ _ (oddFold_bounds _ (oddSum_bounds _ _ _ (oddRep_bounds _) hy)) hf
  rw [oddFold_field,oddSum_field]
  rw [oddRep_field]
  field_simp [p1_two_ne_zero]
  ring


















end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.oddFold_contract
#print axioms ECDSAAdd.Entrant.P1Life.oddForward_inverse
end -- ticket 8 pasted module

-- ===== P1CompareMath =====
section
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


def oddNormalized (F : Int) : Int := magnitude F-h


def oddComparisonLeft (F : Int) : Int :=
  2*oddNormalized F+(if F<0 then 0 else 1)


def oddComparisonY (s : Bool) (F Y : Int) : Int :=
  if s ^^ negative F then -Y-1 else Y


theorem oddMagnitude_bounds (F : Int) (hf : OddDomain F) : 0≤magnitude F ∧ magnitude F≤q := by
  unfold OddDomain at hf
  by_cases fn : F<0 <;> simp only [magnitude,negative,fn,decide_true,decide_false,Bool.false_eq_true,if_true,if_false] <;> omega


theorem oddNormalized_bounds (F : Int) (hf : OddDomain F) :
    -h≤oddNormalized F ∧ oddNormalized F<h := by
  have hm := oddMagnitude_bounds F hf
  have hp := constants
  unfold oddNormalized
  omega















/-- Exact strict form: oddness is the measured comparator's input bit.
The canonical endpoint -q-1 and the noncanonical viewed endpoint q are retained. -/
theorem oddComparison_strict (s : Bool) (R Y : Int) (hr : OddDomain R) (hy : OddDomain Y) :
    oddSum s R Y%2≠0 ↔
      oddComparisonLeft (oddFold (oddSum s R Y))<oddComparisonY s (oddFold (oddSum s R Y)) Y := by
  have hp := constants
  have d := oddFold_double (oddSum s R Y)
  unfold OddDomain at hr hy
  by_cases po : oddSum s R Y%2≠0 <;>
    by_cases sn : oddSum s R Y<0 <;>
    by_cases fn : oddFold (oddSum s R Y)<0 <;> cases s
  all_goals
    simp only [po,sn,Bool.false_eq_true,if_true,if_false] at d
    simp only [oddComparisonLeft,oddNormalized,magnitude,negative,oddComparisonY,
      fn,decide_true,decide_false,Bool.false_xor,Bool.true_xor,Bool.not_true,Bool.not_false,
      Bool.false_eq_true,if_true,if_false]
    simp only [oddSum,oddViewed,Bool.false_eq_true,if_false,if_true] at d po sn fn ⊢
    omega









theorem oddComparison_parity (s : Bool) (R Y : Int) (hr : OddDomain R) (hy : OddDomain Y) :
    originalParity (oddSum s R Y)=
      decide (oddComparisonLeft (oddFold (oddSum s R Y))<oddComparisonY s (oddFold (oddSum s R Y)) Y) :=
  decide_eq_decide.mpr (oddComparison_strict s R Y hr hy)

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.oddComparison_strict
end -- ticket 8 pasted module

-- ===== P1ShortMath =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


/-- Lift a residue through three untouched low positions, at symbolic width. -/
theorem p1_mod_lift (M a V : Nat) (pos : 0<M) (small : a<8) :
    (a+8*V)%(8*M)=a+8*(V%M) := by
  have bound : a+8*(V%M)<8*M := by have h := Nat.mod_lt V pos; omega
  calc
    (a+8*V)%(8*M)=(a+8*(V%M)+(8*M)*(V/M))%(8*M) := by
      congr 1
      calc
        a+8*V=a+8*(V%M+M*(V/M)) := by rw [Nat.mod_add_div]
        _=a+8*(V%M)+(8*M)*(V/M) := by ring
    _=a+8*(V%M) := by rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]


theorem p1_short_arithmetic (n a u k : Nat) (B : Bool) (small : a<4) :
    a+4*(!B).toNat+8*((u+k+B.toNat)%2^n)=
      (a+4*B.toNat+8*u+(4+8*k))%2^(n+3) := by
  have power : 2^(n+3)=8*2^n := by rw [pow_add]; norm_num; ring
  rw [power]
  cases B
  · simp only [Bool.not_false,Bool.toNat_true,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,
      Nat.mul_one]
    rw [show a+8*u+(4+8*k)=(a+4)+8*(u+k) by ring]
    exact (p1_mod_lift (2^n) (a+4) (u+k) (Nat.two_pow_pos _) (by omega)).symm
  · simp only [Bool.not_true,Bool.toNat_true,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,
      Nat.mul_one]
    rw [show a+4+8*u+(4+8*k)=a+8*(u+k+1) by ring]
    exact (p1_mod_lift (2^n) a (u+k+1) (Nat.two_pow_pos _) (by omega)).symm


















theorem p1_h_short_constants : h.toNat%8=4 ∧ encodeWord 255 (-h)%8=4 := by
  norm_num [h,q,p,encodeWord,Int.toNat]





















end ECDSAAdd.Entrant.P1Life


end -- ticket 8 pasted module

-- ===== P1BiasMath =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


def oddBiased (F : Int) : Int :=
  if F<0 then F-(BiasedCircuit.jh : Int) else F+(BiasedCircuit.jh : Int)


theorem oddBiased_bounds (F : Int) (hf : OddDomain F) :
    -((2^255 : Nat) : Int)≤oddBiased F ∧ oddBiased F<((2^255 : Nat) : Int) ∧
    (oddBiased F<0 ↔ F<0) := by
  unfold OddDomain at hf
  by_cases fn : F<0 <;> simp [oddBiased,fn,BiasedCircuit.jh] <;>
    norm_num [q,p] at hf ⊢ <;> omega


theorem oddBiased_magnitude (F : Int) :
    magnitude (oddBiased F)=magnitude F+(BiasedCircuit.jh : Int) := by
  have sg : (oddBiased F<0) ↔ F<0 := by
    by_cases fn : F<0 <;> simp [oddBiased,fn,BiasedCircuit.jh] <;> omega
  have sf : negative (oddBiased F)=negative F := decide_eq_decide.mpr sg
  unfold magnitude
  rw [sf]
  by_cases fn : F<0 <;> simp [negative,oddBiased,fn] <;> ring


theorem oddFold_low (S : Int) (hs : -(p : Int)≤S ∧ S≤(p : Int)-1) :
    ((encodeWord 257 S/2)%2^255+
      (if decide (S<0) then 2^255-1-BiasedCircuit.jh else BiasedCircuit.jh)+
      (originalParity S && decide (S<0)).toNat)%2^255=
        encodeWord 256 (oddBiased (oddFold S))%2^255 := by
  have fb := oddFold_bounds S hs
  have bb := oddBiased_bounds _ fb
  have a := BalancedFold.encode_shift 257 S (by norm_num [p] at hs ⊢; omega)
  have b := BalancedFold.encode_shift 256 (oddBiased (oddFold S)) (by
    norm_num only [Nat.reducePow] at bb ⊢; omega)
  have par := originalParity_value S
  have half := oddFold_double S
  have sig := oddFold_sign S hs
  by_cases po : S%2=0 <;> by_cases sn : S<0 <;> by_cases fn : oddFold S<0
  all_goals
    simp [originalParity,po,sn,fn] at sig <;>
      simp [oddBiased,originalParity,po,sn,fn] at a b half ⊢ <;>
      norm_num [BiasedCircuit.jh,q,p] at a b hs par half ⊢ <;> omega
















theorem odd_bias_constant : h+(BiasedCircuit.jh : Int)=((2^254 : Nat) : Int) := by
  norm_num [h,q,p,BiasedCircuit.jh]


theorem oddBiased_flip (R : Int) (hr : OddDomain R) :
    ((magnitude (oddBiased R)).toNat+2^254)%2^255=encodeWord 255 (oddNormalized R) := by
  have hb := oddMagnitude_bounds R hr
  have nonneg : 0≤magnitude (oddBiased R) := by
    rw [oddBiased_magnitude]
    norm_num [BiasedCircuit.jh]
    omega
  have cast := Int.toNat_of_nonneg nonneg
  rw [oddBiased_magnitude] at cast
  have enc := encodeWord_cast 255 (oddNormalized R)
  have fit := encodeWord_bound 255 (oddNormalized R)
  have rel := odd_bias_constant
  unfold oddNormalized at enc fit ⊢
  rw [oddBiased_magnitude]
  norm_num only [BiasedCircuit.jh,Nat.reducePow,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add] at cast enc fit rel ⊢
  omega

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.oddFold_low
end -- ticket 8 pasted module

-- ===== P1RawMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


theorem oddDomain_signed (R : Int) (hr : OddDomain R) :
    -((2^255 : Nat) : Int)≤R ∧ R<((2^255 : Nat) : Int) := by
  have hp := constants
  unfold OddDomain at hr
  omega


theorem oddSum_signed (s : Bool) (R Y : Int) (hr : OddDomain R) (hy : OddDomain Y) :
    -((2^256 : Nat) : Int)≤oddSum s R Y ∧ oddSum s R Y<((2^256 : Nat) : Int) := by
  have hs := oddSum_bounds s R Y hr hy
  norm_num [p] at hs ⊢
  omega


theorem oddSum_parity (s : Bool) (R Y : Int) :
    originalParity (oddSum s R Y)=(originalParity R ^^ originalParity Y ^^ s ^^ true) := by
  have a := originalParity_value R
  have b := originalParity_value Y
  have c := originalParity_value (oddSum s R Y)
  cases ps : originalParity (oddSum s R Y) <;> cases s <;>
    cases pr : originalParity R <;> cases py : originalParity Y
  all_goals simp only [pr,py,ps,if_true,if_false,Bool.false_eq_true] at a b c ⊢
  all_goals simp only [oddSum,oddViewed,Bool.false_eq_true,if_false,if_true] at c
  all_goals first | rfl | omega


theorem oddSum_encoded (n : Nat) (s : Bool) (R Y : Int) :
    ((if s then 2^n-1-encodeWord n Y else encodeWord n Y)+encodeWord n R+1)%2^n=
      encodeWord n (oddSum s R Y) := by
  have fit := encodeWord_bound n Y
  have pow := Nat.two_pow_pos n
  apply Int.ofNat_inj.mp
  cases s
  · simp only [Bool.false_eq_true,if_false,oddSum,oddViewed]
    push_cast
    simp only [encodeWord_cast,Nat.cast_pow,Nat.cast_ofNat,Int.add_emod,Int.emod_emod]
    ac_rfl
  · simp only [if_true,oddSum,oddViewed]
    rw [Int.natCast_emod,Nat.cast_add,Nat.cast_add,Nat.cast_one,
      Nat.cast_sub (by omega : encodeWord n Y≤2^n-1),
      Nat.cast_sub (by omega : 1≤2^n),Nat.cast_one,encodeWord_cast,encodeWord_cast,encodeWord_cast]
    have e : (((2^n : Nat) : Int)-1-Y%((2^n : Nat) : Int))+R%((2^n : Nat) : Int)+1=
        (R%((2^n : Nat) : Int)-Y%((2^n : Nat) : Int))+((2^n : Nat) : Int) := by ring
    rw [e,Int.add_emod_right]
    have h := Int.sub_emod R Y ((2^n : Nat) : Int)
    simpa only [show R+(-Y-1)+1=R-Y by ring] using h.symm

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Raw =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem rawAdd_correct (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m : List Bool)
    (parityValue : s.basis L.parity=
      (s.basis L.r0 ^^ s.basis (L.ylow.getD 0 0) ^^ (s.basis L.sign ^^ true)))
    (top : s.basis L.one=s.basis L.rmsb)
    (clean : DirectPass.CleanExcept ((Q6Structural.q6Carry L).take 255) retired s.basis) :
    (run (rawAdd retired L) m s).phase=s.phase ∧
    DirectPass.WordFrame (rawTarget L) s.basis
      (((if s.basis L.sign then 2^257-1-regValue (GuardCompression.source L) s.basis
        else regValue (GuardCompression.source L) s.basis)+regValue (rawTarget L) s.basis+1)%2^257)
      (run (rawAdd retired L) m s).basis := by
  simpa only [DirectPass.rawAddMode,DirectPass.carryValue,if_true,Bool.toNat_true] using
    DirectPass.rawAdd_withCarry true retired L hw hn member s m parityValue top clean


theorem rawAdd_signed (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m : List Bool) (R Y : Int)
    (parityValue : s.basis L.parity=
      (s.basis L.r0 ^^ s.basis (L.ylow.getD 0 0) ^^ (s.basis L.sign ^^ true)))
    (top : s.basis L.one=s.basis L.rmsb)
    (source : signedRegValue (GuardCompression.source L) s.basis=Y)
    (target : signedRegValue (rawTarget L) s.basis=R)
    (clean : DirectPass.CleanExcept ((Q6Structural.q6Carry L).take 255) retired s.basis) :
    (run (rawAdd retired L) m s).phase=s.phase ∧
    DirectPass.WordFrame (rawTarget L) s.basis (encodeWord 257 (oddSum (s.basis L.sign) R Y))
      (run (rawAdd retired L) m s).basis := by
  have a := rawAdd_correct retired L hw hn member s m parityValue top clean
  have sl : (GuardCompression.source L).length=257 := by
    simp [GuardCompression.source,BalancedCleanup.Layout.y,hw.2.1]
  have tl : (rawTarget L).length=257 := by
    simp [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,hw.1]
  have sv := word_encoding (GuardCompression.source L) 257 sl s.basis Y source
  have tv := word_encoding (rawTarget L) 257 tl s.basis R target
  rw [sv,tv,oddSum_encoded] at a
  exact a

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.rawAdd_correct
end -- ticket 8 pasted module

-- ===== P1RawBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def OddRawReady (L : Layout) (b : BasisState) : Prop :=
  b L.one=b L.rmsb ∧
  b L.parity=(b L.r0 ^^ b (L.ylow.getD 0 0) ^^ (b L.sign ^^ true))


theorem rawAdd_boundary (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState) (B : Bool) (R Y : Int) :
    Triple (fun b => OddRawReady L b ∧ b L.sign=B ∧
      signedRegValue (GuardCompression.source L) b=Y ∧ signedRegValue (rawTarget L) b=R ∧
      regValue L.y b=encodeWord 256 Y ∧
      DirectPass.CleanExcept ((Q6Structural.q6Carry L).take 255) retired b ∧
      DirectPass.HalfOutside L origin b) (rawAdd retired L)
      (DirectPass.AfterRaw DirectPass.standardEncoding L retired origin (oddSum B R Y) Y) := by
  intro s m hs
  rcases hs with ⟨ready,sign,source,target,ys,clean,frame⟩
  have h := rawAdd_signed retired L hw hn member s m R Y ready.2 ready.1 source target clean
  rw [sign] at h
  have rt : signedRegValue (L.r0::(L.rtail++[L.rmsb,L.one])) s.basis=R := by
    simpa [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc] using target
  have px := word_parity L.r0 _ s.basis R rt
  have py := DirectPass.raw_source_parity L hw s.basis Y source
  have pv : s.basis L.parity=originalParity (oddSum B R Y) := by
    rw [ready.2,px,py,sign]
    simpa only [Bool.xor_assoc] using (oddSum_parity B R Y).symm
  exact DirectPass.after_raw_of_word retired L hw hn member origin _ Y (rawAdd retired L) s m h pv ys clean frame

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Seed =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem seed_to_raw (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState)
    (R Y : Int) (hr : OddDomain R) (hy : OddDomain Y) :
    Triple (DirectPass.AfterHalf L retired origin R Y) (p1Seed L++rawAdd retired L)
      (DirectPass.AfterRaw DirectPass.standardEncoding L retired origin (oddSum (origin L.sign) R Y) Y) := by
  have prep : Triple (DirectPass.AfterHalf L retired origin R Y) (p1Seed L)
      (fun b => OddRawReady L b ∧ b L.sign=origin L.sign ∧
        signedRegValue (GuardCompression.source L) b=Y ∧ signedRegValue (rawTarget L) b=R ∧
        regValue L.y b=encodeWord 256 Y ∧
        DirectPass.CleanExcept ((Q6Structural.q6Carry L).take 255) retired b ∧ DirectPass.HalfOutside L origin b) := by
    intro s m hs
    have h := DirectPass.seed_prepare true retired L hw hn member origin R Y
      (oddDomain_signed R hr) (oddDomain_signed Y hy) s m hs
    rcases h with ⟨phase,top,pv,sign,source,target,ys,clean,frame⟩
    exact ⟨phase,⟨top,pv⟩,sign,source,target,ys,clean,frame⟩
  exact Triple.seq prep (rawAdd_boundary retired L hw hn member origin (origin L.sign) R Y)

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1SignFrames =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem prepare_sign_odd (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (origin : BasisState) (R Y : Int) (hr : OddDomain R) :
    Triple (DirectPass.AfterHalf L retired origin R Y) (BalancedCleanup.prepareSign L.toLayout)
      (DirectPass.AfterUnnormalize DirectPass.oddEncoding L retired origin R Y) := by
  intro s m hs
  have h := DirectPass.prepare_sign_boundary_wide retired L hw hn origin R Y (oddDomain_signed R hr) s m hs
  rcases h with ⟨phase,low,host,ys,flags,clean,frame⟩
  exact ⟨phase,low,host,ys,flags,clean,frame⟩


theorem restore_sign_odd (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (origin : BasisState) (R Y : Int) (hr : OddDomain R) :
    Triple (DirectPass.AfterUnnormalize DirectPass.oddEncoding L retired origin R Y)
      (BalancedCleanup.prepareSign L.toLayout).reverse (DirectPass.AfterHalf L retired origin R Y) := by
  intro s m hs
  rcases hs with ⟨low,host,ys,flags,clean,frame⟩
  exact DirectPass.restore_sign_boundary_wide retired L hw hn origin R Y (oddDomain_signed R hr)
    s m ⟨low,host,ys,flags,clean,frame⟩

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Chunks =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem forward_chunks (retired : Wire) (L : Layout) : forward retired L=
    (p1Seed L++rawAdd retired L)++
      ((OneReuse.newPrepare L++rotateRight (rawTarget L)++fold retired L)++
        ((BalancedCleanup.prepareSign L.toLayout++BiasedCircuit.flipBias L++
          prepareCompare L++exposure L++compare retired true L++
          (exposure L).reverse++(prepareCompare L).reverse)++
          (Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L h.toNat)++
            (BalancedCleanup.prepareSign L.toLayout).reverse))) := by
  simp only [forward,List.append_assoc]


theorem inverse_chunks (retired : Wire) (L : Layout) : inverse retired L=
    BalancedCleanup.prepareSign L.toLayout++
      (Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L (encodeWord 255 (-h)))++
        ((prepareCompare L++exposure L++compare retired false L++(exposure L).reverse++
          (prepareCompare L).reverse++BiasedInverse.unbiasView L)++
          ((unfoldStep retired L++rotateLeft (rawTarget L)++[.CX L.parity L.r0])++rawSub retired L))) := by
  simp only [inverse,List.append_assoc]

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== PassShortLiteral =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


/-- Short literal at arbitrary width, allowing the retired name to be unused.
The low lo is untouched, cin is flipped, and every outsider is restored. -/
theorem short_literal_loan (lo xs cs : List Wire) (cin one host retired : Wire) (k : Nat)
    (nd : (host::one::((lo++cin::xs)++cs)).Nodup) (plen : lo.length=2)
    (reserved : retired∉one::(lo++cin::xs)) (len : cs.length+1=xs.length)
    (s : State) (m : List Bool) (one0 : s.basis one=false) (host0 : s.basis host=false)
    (clean : CleanExcept cs retired s.basis) :
    let body := renameProgram (Equiv.swap retired host) (literalConstAdd xs cs cin one k)
    let cell := body++[.X cin]
    (run cell m s).phase=s.phase ∧
    WordFrame (lo++cin::xs) s.basis
      ((regValue (lo++cin::xs) s.basis+(4+8*k))%2^(lo++cin::xs).length)
      (run cell m s).basis := by
  have count := List.nodup_iff_count.mp nd
  have nloan : (host::one::cin::(xs++cs)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := count q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have res : retired∉one::cin::xs := by
    intro bad
    apply reserved
    simp only [List.mem_cons,List.mem_append] at bad ⊢
    itauto
  have earlyAway (q : Wire) (hq : q∈lo++[cin]) : q∉xs := by
    intro bad
    have h := count q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have prefCin (q : Wire) (hq : q∈lo) : q≠cin := by
    intro e
    have h := count q
    have a := List.count_pos_iff.mpr hq
    subst q
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
    omega
  have h := literal_loan_reserved xs cs cin one host retired k nloan res len s m one0 host0 clean
  let body := renameProgram (Equiv.swap retired host) (literalConstAdd xs cs cin one k)
  let u := run body m s
  let t := run [.X cin] [] u
  have ui : u.basis cin=s.basis cin := h.2.2 cin (earlyAway cin (by simp))
  have tf (q : Wire) (hq : q≠cin) : t.basis q=u.basis q := by simp [t,run,writeBit,hq]
  have tv : regValue xs t.basis=regValue xs u.basis :=
    regValue_congr _ _ _ (fun q hq => tf q (fun e => earlyAway cin (by simp) (e ▸ hq)))
  have tp : regValue lo t.basis=regValue lo s.basis :=
    regValue_congr _ _ _ (fun q hq => (tf q (prefCin q hq)).trans
      (h.2.2 q (earlyAway q (by simp [hq]))))
  have ti : t.basis cin= !s.basis cin := by simp [t,run,writeBit,ui]
  have actual : run (body++[.X cin]) m s=t := by
    rw [run_append,run_take]
    rfl
  dsimp only
  rw [actual]
  refine ⟨h.1,?_,?_⟩
  · have small : regValue lo s.basis<4 := by simpa [plen] using regValue_lt lo s.basis
    have ar := P1Life.p1_short_arithmetic xs.length (regValue lo s.basis)
      (regValue xs s.basis) k (s.basis cin) small
    have out : regValue (lo++cin::xs) t.basis=
        regValue lo s.basis+4*(!s.basis cin).toNat+
          8*((regValue xs s.basis+k+(s.basis cin).toNat)%2^xs.length) := by
      rw [regValue_append,plen,tp]
      change regValue lo s.basis+4*((if t.basis cin then 1 else 0)+2*regValue xs t.basis)=_
      rw [ti,tv,h.2.1]
      simp only [Bool.toNat,Bool.cond_eq_ite]
      ring
    have inp : regValue (lo++cin::xs) s.basis=
        regValue lo s.basis+4*(s.basis cin).toNat+8*regValue xs s.basis := by
      rw [regValue_append,plen]
      change regValue lo s.basis+4*((if s.basis cin then 1 else 0)+2*regValue xs s.basis)=_
      simp only [Bool.toNat,Bool.cond_eq_ite]
      ring
    have length : (lo++cin::xs).length=xs.length+3 := by simp [plen]; omega
    rw [out,inp,length]
    exact ar
  · intro q hq
    have qi : q≠cin := fun e => hq (by simp [e])
    have qx : q∉xs := fun bad => hq (by simp [bad])
    exact (tf q qi).trans (h.2.2 q qx)

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== P1Short =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem short_word_split (xs : List Wire) (size : 3≤xs.length) :
    xs.take 2++xs.getD 2 0::xs.drop 3=xs := by
  cases xs with
  | nil => simp at size
  | cons a as =>
    cases as with
    | nil => simp at size
    | cons b bs =>
      cases bs with
      | nil => simp at size
      | cons c cs => rfl


theorem short_correct (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (k : Nat) (val : k%8=4)
    (s : State) (m : List Bool) (one0 : s.basis L.one=false) (host0 : s.basis L.rmsb=false)
    (clean : DirectPass.CleanExcept (L.carry.take 254) retired s.basis) :
    (run (Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L k)) m s).phase=s.phase ∧
    DirectPass.WordFrame L.low s.basis ((regValue L.low s.basis+k)%2^255)
      (run (Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L k)) m s).basis := by
  let lo := L.low.take 2
  let xs := L.low.drop 3
  let cs := L.carry.take 251
  let cin := L.low.getD 2 0
  have len : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have split : lo++cin::xs=L.low := short_word_split L.low (by omega)
  have nd : (L.rmsb::L.one::(L.low++cs)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have lim := (List.take_sublist 251 L.carry).count_le q
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil,cs] at h ⊢
    omega
  have reserved : retired∉L.one::L.low := by
    intro bad
    have n := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) retired
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take (List.mem_of_mem_drop member))
    have b := List.count_pos_iff.mpr bad
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at n b
    omega
  have cinmem : cin∈L.low := by rw [←split]; simp
  have ri : retired≠cin := fun e => reserved (by simp [e,cinmem])
  have hi : L.rmsb≠cin := fun e => (List.nodup_cons.mp nd).1 (by simp [e,cinmem])
  have fi : Equiv.swap retired L.rmsb cin=cin := Equiv.swap_apply_of_ne_of_ne ri.symm hi.symm
  have h := DirectPass.short_literal_loan lo xs cs cin L.one L.rmsb retired (k/8)
    (by simpa only [split] using nd) (by simp [lo,List.length_take,len])
    (by simpa only [split] using reserved) (by simp [cs,xs,List.length_take,len,hw.2.2]) s m one0 host0
    (by
      intro q hq qr
      have sub : cs=(L.carry.take 254).take 251 := by simp [cs,List.take_take]
      rw [sub] at hq
      exact clean q (List.mem_of_mem_take hq) qr)
  have scalar : 4+8*(k/8)=k := by have a := Nat.mod_add_div k 8; omega
  have program : Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L k)=
      renameProgram (Equiv.swap retired L.rmsb) (literalConstAdd xs cs cin L.one (k/8))++[.X cin] := by
    change renameProgram (Equiv.swap retired L.rmsb)
      (literalConstAdd xs cs cin L.one (k/8)++[.X cin])=_
    rw [FieldRename.rename_append]
    simp only [renameProgram,List.map_cons,List.map_nil,renameInstr,fi]
  simpa only [program,split,len,scalar] using h

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.short_correct
end -- ticket 8 pasted module

-- ===== P1ShortBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem short_boundary (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState)
    (v u Y k : Nat) (P N : Bool) (val : k%8=4) (arithmetic : (v+k)%2^255=u) :
    Triple (DirectPass.LowBoundary L retired origin v Y P N)
      (Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L k))
      (DirectPass.LowBoundary L retired origin u Y P N) := by
  intro s m input
  have h := short_correct retired L hw hn member k val s m input.2.2.2.1.2.2 input.2.1 input.2.2.2.2.1
  rw [input.1,arithmetic] at h
  exact DirectPass.low_frame_of_word L hn retired origin v u Y P N _ s m input h


theorem unnormalize_boundary (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState) (R Y : Int) :
    Triple (DirectPass.AfterComparison DirectPass.oddEncoding L retired origin R Y)
      (Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L h.toNat))
      (DirectPass.AfterUnnormalize DirectPass.oddEncoding L retired origin R Y) := by
  apply short_boundary retired L hw hn member origin _ _ _ _ false (negative R) p1_h_short_constants.1
  change (encodeWord 255 (oddNormalized R)+h.toNat)%2^255=encodeWord 255 (magnitude R)
  rw [DirectPass.encoded_add_nat,Int.toNat_of_nonneg (le_of_lt constants.2.2.2.2.1)]
  congr 1
  unfold oddNormalized
  ring


theorem normalize_boundary (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState) (R Y : Int) :
    Triple (DirectPass.AfterUnnormalize DirectPass.oddEncoding L retired origin R Y)
      (Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L (encodeWord 255 (-h))))
      (DirectPass.AfterComparison DirectPass.oddEncoding L retired origin R Y) := by
  apply short_boundary retired L hw hn member origin _ _ _ _ false (negative R) p1_h_short_constants.2
  change (encodeWord 255 (magnitude R)+encodeWord 255 (-h))%2^255=encodeWord 255 (oddNormalized R)
  rw [DirectPass.encoded_add_encoded]
  rfl

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== PassFlipBias =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


theorem flip_top_mod (lo : List Wire) (top : Wire) (nd : (lo++[top]).Nodup)
    (s : State) (m : List Bool) :
    regValue (lo++[top]) (run [.X top] m s).basis=
      (regValue (lo++[top]) s.basis+2^lo.length)%2^(lo.length+1) := by
  have away : top∉lo := fun h => List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 h (by simp)
  have keep : regValue lo (run [.X top] m s).basis=regValue lo s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [run,writeBit,show q≠top from fun e => away (e ▸ hq)])
  have fit := regValue_lt lo s.basis
  have power : 2^(lo.length+1)=2*2^lo.length := by rw [pow_succ,Nat.mul_comm]
  have single (b : BasisState) : regValue [top] b=(b top).toNat := by
    simp only [regValue,List.foldr_cons,List.foldr_nil]
    cases b top <;> rfl
  have topValue : (run [.X top] m s).basis top= !s.basis top := by simp [run,writeBit]
  rw [regValue_append,regValue_append,keep,power]
  simp only [single,topValue]
  cases bit : s.basis top
  · simp only [bit,Bool.not_false,Bool.toNat_true,Bool.toNat_false,
      Nat.mul_zero,Nat.mul_one,Nat.add_zero]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · simp only [bit,Bool.not_true,Bool.toNat_true,Bool.toNat_false,
      Nat.mul_zero,Nat.mul_one,Nat.add_zero]
    rw [show regValue lo s.basis+2^lo.length+2^lo.length=regValue lo s.basis+2*2^lo.length by ring,
      Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]


theorem flip_bias_low (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (s : State) (m : List Bool) :
    regValue L.low (run (BiasedCircuit.flipBias L) m s).basis=
      (regValue L.low s.basis+2^254)%2^255 := by
  have lowND : L.low.Nodup := by
    have n0 := (List.nodup_append'.mp hn).2.1
    exact (List.nodup_append'.mp (List.nodup_append'.mp (L.toLayout.dataND n0)).1).1
  have split := BiasedCircuit.low_split L hw
  have nd : (L.low.take 254++[L.rtail.getD 253 0]).Nodup := by rw [split]; exact lowND
  have len : (L.low.take 254).length=254 := by
    simp [List.length_take,BalancedCleanup.Layout.low,hw.1]
  have h := flip_top_mod (L.low.take 254) (L.rtail.getD 253 0) nd s m
  simpa only [len,split,BiasedCircuit.flipBias] using h


theorem flip_bias_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (s : State) (m : List Bool) :
    (run (BiasedCircuit.flipBias L) m s).phase=s.phase ∧
    WordFrame L.low s.basis ((regValue L.low s.basis+2^254)%2^255)
      (run (BiasedCircuit.flipBias L) m s).basis := by
  refine ⟨rfl,flip_bias_low L hw hn s m,?_⟩
  intro q hq
  have inside : L.rtail[253]?.getD 0∈L.low := by
    have h : L.rtail.getD 253 0∈L.low := by rw [←BiasedCircuit.low_split L hw]; simp
    exact h
  have ne : q≠L.rtail[253]?.getD 0 := fun e => hq (e ▸ inside)
  simp [BiasedCircuit.flipBias,run,writeBit,ne]

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== P1FoldView =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem fold_view (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (origin : BasisState) (T R Y : Int) (hr : OddDomain R) :
    Triple (DirectPass.AfterFold DirectPass.oddEncoding L retired origin T R Y)
      (BalancedCleanup.prepareSign L.toLayout++BiasedCircuit.flipBias L)
      (DirectPass.InverseComparison DirectPass.oddEncoding L retired origin T R Y) := by
  have bound := oddBiased_bounds R hr
  have mb := DirectPass.magnitude_wide_bounds (oddBiased R) ⟨bound.1,bound.2.1⟩
  have vc := Int.toNat_of_nonneg mb.1
  have fit : (magnitude (oddBiased R)).toNat<2^255 := by omega
  have lowlen : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have n0 := (List.nodup_append'.mp hn).2.1
  apply DirectPass.fold_view_values DirectPass.oddEncoding retired L hw hn origin T R Y
    (magnitude (oddBiased R)).toNat (encodeWord_bound 255 (oddNormalized R))
  · intro s m value lower
    have h := DirectPass.prepare_sign_value_wide L.toLayout hw n0 (oddBiased R)
      ⟨bound.1,bound.2.1⟩ s m value lower
    have zero := properProgram_measurementCount _ (BalancedCleanup.prepareSign_proper L.toLayout n0)
    exact ⟨run_no_measurement_phase _ zero s m,h.1,
      h.2.1.trans (decide_eq_decide.mpr bound.2.2),h.2.2⟩
  · intro s m value
    have top := regValue_highBit L.low L.rmsb s.basis
    change s.basis L.rmsb=true ↔ 2^L.low.length≤regValue L.r s.basis at top
    have top0 : s.basis L.rmsb=false := by
      cases bit : s.basis L.rmsb
      · rfl
      · have bad := top.mp bit
        rw [lowlen,value] at bad
        omega
    have low : regValue L.low s.basis=(magnitude (oddBiased R)).toNat := by
      have v := value
      change regValue (L.low++[L.rmsb]) s.basis=_ at v
      rw [regValue_append] at v
      simpa [regValue,top0] using v
    have inLow : L.rtail.getD 253 0∈L.low := by
      rw [←BiasedCircuit.low_split L hw]
      simp
    have rND := (List.nodup_append'.mp (L.toLayout.dataND n0)).1
    have ne : L.rmsb≠L.rtail.getD 253 0 := by
      intro e
      exact List.disjoint_left.mp (List.nodup_append'.mp rND).2.2 (e ▸ inLow) (by simp)
    have ne' : L.rmsb≠L.rtail[253]?.getD 0 := ne
    have outtop : (run (BiasedCircuit.flipBias L) m s).basis L.rmsb=false := by
      simp [BiasedCircuit.flipBias,run,writeBit,ne',top0]
    change regValue (L.low++[L.rmsb]) (run (BiasedCircuit.flipBias L) m s).basis=_
    rw [regValue_append]
    simp only [regValue,List.foldr_cons,List.foldr_nil,outtop,Bool.false_eq_true,if_false,
      Nat.mul_zero,Nat.add_zero]
    change regValue L.low (run (BiasedCircuit.flipBias L) m s).basis=_
    rw [DirectPass.flip_bias_low L hw hn s m,low,oddBiased_flip R hr]
    rfl

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1CompareBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def OddComparisonFrame (L : Layout) (retired : Wire) (origin : BasisState)
    (R Y : Int) (P : Bool) : BasisState → Prop :=
  DirectPass.LowBoundary L retired origin (encodeWord 255 (oddNormalized R)) (encodeWord 256 Y) P (negative R)


theorem odd_comparison_predicate (B : Bool) (R Y : Int) :
    DirectPass.comparisonPredicate true B (negative R) (oddNormalized R) Y=
      decide (oddComparisonLeft R<oddComparisonY B R Y) := by
  have left : DirectPass.compareLeftValue true B (negative R) (oddNormalized R)=oddComparisonLeft R := by
    by_cases rn : R<0 <;>
      simp [DirectPass.compareLeftValue,DirectPass.compareInsertValue,oddComparisonLeft,negative,rn]
  simp only [DirectPass.comparisonPredicate,if_true,left]
  rfl


theorem comparison_boundary (erase : Bool) (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (R Y : Int) (hr : OddDomain R) (hy : OddDomain Y) :
    let answer := decide (oddComparisonLeft R<oddComparisonY (origin L.sign) R Y)
    Triple (OddComparisonFrame L retired origin R Y (DirectPass.compareInput erase answer))
      (prepareCompare L++exposure L++compare retired erase L++
        (exposure L).reverse++(prepareCompare L).reverse)
      (OddComparisonFrame L retired origin R Y (DirectPass.compareOutput erase answer)) := by
  have ur := oddNormalized_bounds R hr
  have hp := constants
  have hu : -((2^254 : Nat) : Int)≤oddNormalized R ∧ oddNormalized R<((2^254 : Nat) : Int) := by omega
  have h := DirectPass.comparison_boundary_mode true erase retired L hw hn member origin
    (oddNormalized R) Y (negative R) hu (oddDomain_signed Y hy)
  dsimp only at h ⊢
  rw [odd_comparison_predicate] at h
  simpa only [OddComparisonFrame,DirectPass.comparePrepareMode,DirectPass.compareInsert,
    DirectPass.compareExposeMode,prepareCompare,if_true] using h


theorem fold_to_comparison (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState)
    (R Y : Int) (hr : OddDomain R) (hy : OddDomain Y) :
    let T := oddSum (origin L.sign) R Y
    Triple (DirectPass.AfterFold DirectPass.oddEncoding L retired origin T (oddFold T) Y)
      (BalancedCleanup.prepareSign L.toLayout++BiasedCircuit.flipBias L++
        prepareCompare L++exposure L++compare retired true L++(exposure L).reverse++(prepareCompare L).reverse)
      (DirectPass.AfterComparison DirectPass.oddEncoding L retired origin (oddFold T) Y) := by
  let T := oddSum (origin L.sign) R Y
  have hf := oddFold_bounds T (oddSum_bounds _ R Y hr hy)
  have interval : originalParity T=decide (oddComparisonLeft (oddFold T)<oddComparisonY (origin L.sign) (oddFold T) Y) :=
    oddComparison_parity (origin L.sign) R Y hr hy
  have b := comparison_boundary true retired L hw hn member origin (oddFold T) Y hf hy
  simp only [DirectPass.compareInput,DirectPass.compareOutput,if_true,←interval] at b
  simpa only [List.append_assoc,OddComparisonFrame,DirectPass.LowBoundary,
    DirectPass.InverseComparison,DirectPass.AfterComparison,DirectPass.oddEncoding,oddNormalized,negative] using
    Triple.seq (fold_view retired L hw hn origin T (oddFold T) Y hf) b

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Unbias =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem unbias_boundary (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (origin : BasisState) (T R Y : Int) (hr : OddDomain R) :
    Triple (DirectPass.InverseComparison DirectPass.oddEncoding L retired origin T R Y)
      (BiasedInverse.unbiasView L)
      (DirectPass.AfterFold DirectPass.oddEncoding L retired origin T R Y) := by
  have bound := oddBiased_bounds R hr
  have neg : negative (oddBiased R)=negative R := decide_eq_decide.mpr bound.2.2
  have arithmetic : (encodeWord 255 (oddNormalized R)+2^254)%2^255=
      encodeWord 255 (magnitude (oddBiased R)) := by
    rw [DirectPass.encoded_add_nat,oddBiased_magnitude]
    congr 1
    unfold oddNormalized
    have rel := odd_bias_constant
    omega
  have front : Triple (DirectPass.InverseComparison DirectPass.oddEncoding L retired origin T R Y)
      (BiasedCircuit.flipBias L)
      (DirectPass.LowBoundary L retired origin (encodeWord 255 (magnitude (oddBiased R)))
        (encodeWord 256 Y) (originalParity T) (negative (oddBiased R))) := by
    intro s m hs
    have input : DirectPass.LowBoundary L retired origin (encodeWord 255 (oddNormalized R))
        (encodeWord 256 Y) (originalParity T) (negative R) s.basis := hs
    have h := DirectPass.flip_bias_frame L hw hn s m
    rw [input.1,arithmetic] at h
    have out := DirectPass.low_frame_of_word L hn retired origin _ _ _ _ _ _ s m input h
    simpa only [neg] using out
  have back := DirectPass.restore_sign_boundary_values retired L hw hn origin (oddBiased R)
    (encodeWord 256 Y) (originalParity T) ⟨bound.1,bound.2.1⟩
  have cell : BiasedInverse.unbiasView L=BiasedCircuit.flipBias L++
      (BalancedCleanup.prepareSign L.toLayout).reverse := by
    have site : L.r.getD 254 0=L.rtail.getD 253 0 := by
      simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.getD,hw.1]
    simp only [BiasedInverse.unbiasView,BiasedCircuit.flipBias,site]
  rw [cell]
  exact Triple.seq front back

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1InverseBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem comparison_to_fold (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState)
    (T R Y : Int) (hr : OddDomain R) (hy : OddDomain Y)
    (interval : originalParity T=decide (oddComparisonLeft R<oddComparisonY (origin L.sign) R Y)) :
    Triple (DirectPass.AfterComparison DirectPass.oddEncoding L retired origin R Y)
      (prepareCompare L++exposure L++compare retired false L++(exposure L).reverse++
        (prepareCompare L).reverse++BiasedInverse.unbiasView L)
      (DirectPass.AfterFold DirectPass.oddEncoding L retired origin T R Y) := by
  have b := comparison_boundary false retired L hw hn member origin R Y hr hy
  simp only [DirectPass.compareInput,DirectPass.compareOutput,Bool.false_eq_true,if_false,←interval] at b
  simpa only [List.append_assoc,OddComparisonFrame,DirectPass.LowBoundary,
    DirectPass.InverseComparison,DirectPass.AfterComparison,DirectPass.oddEncoding,oddNormalized,negative] using
    Triple.seq b (unbias_boundary retired L hw hn origin T R Y hr)

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1FoldBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem fold_boundary (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) (origin : BasisState) (T Y : Int)
    (ht : -(p : Int)≤T ∧ T≤(p : Int)-1) :
    Triple (DirectPass.AfterShift L retired origin T Y) (fold retired L)
      (DirectPass.AfterFold DirectPass.oddEncoding L retired origin T (oddFold T) Y) := by
  have bound := oddBiased_bounds (oddFold T) (oddFold_bounds T ht)
  apply DirectPass.fold_boundary_math true DirectPass.oddEncoding retired L hw hn member origin
    T (oddFold T) Y (oddBiased (oddFold T)) ⟨bound.1,bound.2.1⟩ rfl rfl rfl (oddFold_low T ht)
  have neg : decide (oddBiased (oddFold T)<0)=decide (oddFold T<0) :=
    decide_eq_decide.mpr bound.2.2
  rw [neg]
  simpa [DirectPass.foldTop_mode] using (oddFold_sign T ht).symm


theorem raw_to_fold (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) (origin : BasisState) (T Y : Int)
    (ht : -(p : Int)≤T ∧ T≤(p : Int)-1) :
    Triple (DirectPass.AfterRaw DirectPass.standardEncoding L retired origin T Y)
      (OneReuse.newPrepare L++rotateRight (rawTarget L)++fold retired L)
      (DirectPass.AfterFold DirectPass.oddEncoding L retired origin T (oddFold T) Y) := by
  have range : -((2^256 : Nat) : Int)≤T ∧ T<((2^256 : Nat) : Int) := by
    norm_num [p] at ht ⊢
    omega
  exact Triple.seq (DirectPass.shift_boundary_full retired L hw hn origin T Y range)
    (fold_boundary retired L hw hn member origin T Y ht)

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1UnfoldBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem unfold_boundary (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) (origin : BasisState) (T Y : Int)
    (ht : -(p : Int)≤T ∧ T≤(p : Int)-1) :
    Triple (DirectPass.AfterFold DirectPass.oddEncoding L retired origin T (oddFold T) Y)
      (unfoldStep retired L) (DirectPass.AfterUnfold L retired origin T Y) := by
  have bound := oddBiased_bounds (oddFold T) (oddFold_bounds T ht)
  have range : -((2^256 : Nat) : Int)≤T ∧ T<((2^256 : Nat) : Int) := by norm_num [p] at ht ⊢; omega
  apply DirectPass.unfold_boundary_math true DirectPass.oddEncoding retired L hw hn member origin
    T (oddFold T) Y (oddBiased (oddFold T)) range ⟨bound.1,bound.2.1⟩ rfl rfl rfl (oddFold_low T ht)
  have neg : decide (oddBiased (oddFold T)<0)=decide (oddFold T<0) := decide_eq_decide.mpr bound.2.2
  rw [neg,oddFold_sign T ht]
  simp only [DirectPass.foldSelector_mode,if_true]
  cases originalParity T <;> cases decide (T<0) <;> rfl


theorem fold_to_raw (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) (origin : BasisState) (T Y : Int)
    (ht : -(p : Int)≤T ∧ T≤(p : Int)-1) :
    Triple (DirectPass.AfterFold DirectPass.oddEncoding L retired origin T (oddFold T) Y)
      (unfoldStep retired L++rotateLeft (rawTarget L)++[.CX L.parity L.r0])
      (DirectPass.AfterRaw DirectPass.standardEncoding L retired origin T Y) := by
  have range : -((2^256 : Nat) : Int)≤T ∧ T<((2^256 : Nat) : Int) := by norm_num [p] at ht ⊢; omega
  simpa only [List.append_assoc] using Triple.seq
    (unfold_boundary retired L hw hn member origin T Y ht)
    (DirectPass.unshift_boundary_full retired L hw hn origin T Y range)

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1SubBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem rawSub_boundary (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState)
    (B : Bool) (R Y : Int) (hr : OddDomain R) (hy : OddDomain Y) (signOrigin : origin L.sign=B) :
    Triple (DirectPass.AfterRaw DirectPass.standardEncoding L retired origin (oddSum B R Y) Y)
      (rawSub retired L) (DirectPass.AfterHalf L retired origin R Y) := by
  apply DirectPass.rawSub_boundary_math true retired L hw hn member origin B R Y (oddSum B R Y)
    (oddDomain_signed R hr) (oddDomain_signed Y hy) (oddSum_signed B R Y hr hy)
  · simpa only [if_true,Bool.toNat_true] using oddSum_encoded 257 B R Y
  · simpa only [if_true,Bool.xor_assoc] using oddSum_parity B R Y
  · exact signOrigin

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.rawSub_boundary
end -- ticket 8 pasted module

-- ===== P1Kernel =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem forward_boundary (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState)
    (R Y : Int) (hr : OddDomain R) (hy : OddDomain Y) :
    Triple (DirectPass.AfterHalf L retired origin R Y) (forward retired L)
      (DirectPass.AfterHalf L retired origin (oddFold (oddSum (origin L.sign) R Y)) Y) := by
  let T := oddSum (origin L.sign) R Y
  have ht := oddSum_bounds (origin L.sign) R Y hr hy
  have hf := oddFold_bounds T ht
  have mt : retired∈L.carry.take 254 := List.mem_of_mem_drop member
  have a := seed_to_raw retired L hw hn member origin R Y hr hy
  have b := raw_to_fold retired L hw hn mt origin T Y ht
  have c := fold_to_comparison retired L hw hn member origin R Y hr hy
  have d := unnormalize_boundary retired L hw hn member origin (oddFold T) Y
  have e := restore_sign_odd retired L hw hn origin (oddFold T) Y hf
  rw [forward_chunks]
  exact Triple.seq a (Triple.seq b (Triple.seq c (Triple.seq d e)))


theorem inverse_boundary (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (origin : BasisState)
    (F Y : Int) (hf : OddDomain F) (hy : OddDomain Y) :
    Triple (DirectPass.AfterHalf L retired origin F Y) (inverse retired L)
      (DirectPass.AfterHalf L retired origin (oddInverse (origin L.sign) F Y) Y) := by
  let B := origin L.sign
  let R := oddInverse B F Y
  let T := oddSum B R Y
  have hr : OddDomain R := oddRep_bounds _
  have ht := oddSum_bounds B R Y hr hy
  have result : oddFold T=F := oddForward_inverse B F Y hf hy
  have interval : originalParity T=decide (oddComparisonLeft F<oddComparisonY B F Y) := by
    have h := oddComparison_parity B R Y hr hy
    rw [result] at h
    exact h
  have mt : retired∈L.carry.take 254 := List.mem_of_mem_drop member
  have a := prepare_sign_odd retired L hw hn origin F Y hf
  have b := normalize_boundary retired L hw hn member origin F Y
  have c := comparison_to_fold retired L hw hn member origin T F Y hf hy interval
  have d := fold_to_raw retired L hw hn mt origin T Y ht
  rw [result] at d
  have e := rawSub_boundary retired L hw hn member origin B R Y hr hy rfl
  rw [inverse_chunks]
  exact Triple.seq a (Triple.seq b (Triple.seq c (Triple.seq d e)))

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.forward_boundary
#print axioms ECDSAAdd.Entrant.P1Life.inverse_boundary
end -- ticket 8 pasted module

-- ===== PassKernelFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


def kernelResult (divide : Bool) (B : Bool) (X Y : Int) : Int :=
  if divide then halfResult (rawSum B X Y) else BalancedInverse.result B X Y


theorem kernel_frame_of_boundary (retired : Wire) (L : Layout) (X Y R : Int)
    (program : Program) (s : State) (m : List Bool)
    (rv : regValue L.r s.basis=encodeWord 256 X) (yv : regValue L.y s.basis=encodeWord 256 Y)
    (flags : LiveFlags L false false false s.basis)
    (clean : CleanExcept (L.carry.take 254) retired s.basis)
    (boundary : Triple (AfterHalf L retired s.basis X Y) program (AfterHalf L retired s.basis R Y)) :
    (run program m s).phase=s.phase ∧ WordFrame L.r s.basis (encodeWord 256 R) (run program m s).basis := by
  have input : AfterHalf L retired s.basis X Y s.basis := ⟨rv,yv,flags,clean,fun _ _ _ _ _ => rfl⟩
  have out := boundary s m input
  refine ⟨out.1,out.2.1,?_⟩
  intro q hq
  by_cases ep : q=L.parity
  · subst q
    exact out.2.2.2.1.1.trans flags.1.symm
  · by_cases el : q=L.lower
    · subst q
      exact out.2.2.2.1.2.1.trans flags.2.1.symm
    · by_cases eo : q=L.one
      · subst q
        exact out.2.2.2.1.2.2.trans flags.2.2.symm
      · exact out.2.2.2.2.2 q hq ep el eo
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== P1KernelFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def kernelResult (divide B : Bool) (R Y : Int) : Int :=
  if divide then oddFold (oddSum B R Y) else oddInverse B R Y


theorem kernel_frame (retired : Wire) (divide : Bool) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (R Y : Int) (hr : OddDomain R) (hy : OddDomain Y) (s : State) (m : List Bool)
    (rv : regValue L.r s.basis=encodeWord 256 R) (yv : regValue L.y s.basis=encodeWord 256 Y)
    (flags : DirectPass.LiveFlags L false false false s.basis)
    (clean : DirectPass.CleanExcept (L.carry.take 254) retired s.basis) :
    let cell := if divide then forward retired L else inverse retired L
    (run cell m s).phase=s.phase ∧ DirectPass.WordFrame L.r s.basis
      (encodeWord 256 (kernelResult divide (s.basis L.sign) R Y)) (run cell m s).basis := by
  have h : Triple (DirectPass.AfterHalf L retired s.basis R Y)
      (if divide then forward retired L else inverse retired L)
      (DirectPass.AfterHalf L retired s.basis (kernelResult divide (s.basis L.sign) R Y) Y) := by
    cases divide
    · simp only [kernelResult,Bool.false_eq_true,if_false]
      exact inverse_boundary retired L hw hn member s.basis R Y hr hy
    · simp only [kernelResult,if_true]
      exact forward_boundary retired L hw hn member s.basis R Y hr hy
  exact DirectPass.kernel_frame_of_boundary retired L R Y _ _ s m rv yv flags clean h


theorem kernel_field (divide B : Bool) (X Y : Fp) :
    kernelResult divide (!B) (oddRep X) (oddRep Y)=
      oddRep (if divide then (X+(if B then Y else -Y))/2
        else 2*X+(if B then -Y else Y)) := by
  cases divide
  · simp only [kernelResult,Bool.false_eq_true,if_false,oddInverse,oddRep_field]
    cases B <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true] <;>
      congr 1 <;> ring
  · have h := oddFold_contract (!B) (oddRep X) (oddRep Y) (oddRep_bounds X) (oddRep_bounds Y)
    rw [oddRep_field,oddRep_field] at h
    cases B <;> simpa only [kernelResult,Bool.false_eq_true,if_false,if_true,Bool.not_true,Bool.not_false] using h

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== PassHalfFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


theorem work_outside (L : Layout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈work L) :
    q∉L.r ∧ q∉L.y ∧ q≠L.sign := by
  have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
  have p := List.count_pos_iff.mpr hq
  simp only [work,List.count_cons,List.count_append,List.count_nil] at p
  refine ⟨?_,?_,?_⟩
  · intro bad
    have a := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append,List.count_nil] at h
    omega
  · intro bad
    have a := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append,List.count_nil] at h
    omega
  · intro e
    subst q
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
    omega


theorem kernel_field (divide B : Bool) (X Y : Fp) :
    kernelResult divide (!B) (centerFp X) (centerFp Y)=
      centerFp (if divide then (X+(if B then Y else -Y))/2
        else 2*X+(if B then -Y else Y)) := by
  cases divide
  · cases B <;> simp [kernelResult,BalancedInverse.result,signedY,centerFp_cast,
      Int.cast_sub,Int.cast_mul,Int.cast_ofNat,sub_eq_add_neg]
  · have h := centeredFp_signedHalf (!B) X Y
    cases B <;> simpa [kernelResult] using h


/-- Direct replacement with exactly the existing lifetime half-frame
statement and hypotheses. No older program is used to certify this half. -/
theorem half_frame_from_pair_kernel (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (origin : BasisState) (clean : Q6EndpointCell.Clean w origin)
    (inputR inputY : Nat) (outputR : Bool→Nat) (outputY : Nat)
    (program bodyProgram : Program)
    (shape : program=[.X sign]++bodyProgram++[.X sign])
    (kernel : ∀(s : State)(m : List Bool),
      regValue (Q6EndpointCell.ports w sign).r s.basis=inputR →
      regValue (Q6EndpointCell.ports w sign).y s.basis=inputY →
      LiveFlags (Q6EndpointCell.ports w sign) false false false s.basis →
      CleanExcept ((Q6EndpointCell.ports w sign).carry.take 254) retired s.basis →
      (run bodyProgram m s).phase=s.phase ∧
      PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y s.basis
        (outputR (!s.basis sign)) outputY (run bodyProgram m s).basis) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin inputR inputY)
      program (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (outputR (origin sign)) outputY) := by
  let L := Q6EndpointCell.ports w sign
  have cl := Q6EndpointCell.clean_work w sign origin clean
  have signAway := BalancedCircuit.flagAway L hn L.sign (by simp)
  have sr : L.sign∉L.r := fun h => signAway (by simp [h])
  have sy : L.sign∉L.y := fun h => signAway (by simp [h])
  intro s m input
  let u := run [.X L.sign] [] s
  have uf (q : Wire) (hq : q≠L.sign) : u.basis q=s.basis q := by simp [u,run,writeBit,hq]
  have ug : u.basis L.sign= !origin sign := by
    simp only [u,run,writeBit,Function.update_self,input.2.2 L.sign sr sy]
    rfl
  have rv : regValue L.r u.basis=inputR :=
    (regValue_congr _ _ _ (fun q hq => uf q (fun e => sr (e ▸ hq)))).trans input.1
  have yv : regValue L.y u.basis=inputY :=
    (regValue_congr _ _ _ (fun q hq => uf q (fun e => sy (e ▸ hq)))).trans input.2.1
  have uc (q : Wire) (hq : q∈work L) : u.basis q=false := by
    have a := work_outside L hn q hq
    exact (uf q a.2.2).trans ((input.2.2 q a.1 a.2.1).trans (cl q hq))
  have flags : LiveFlags L false false false u.basis :=
    ⟨uc _ (by simp [work]),uc _ (by simp [work]),uc _ (by simp [work])⟩
  have carry : CleanExcept (L.carry.take 254) retired u.basis := by
    intro q hq qr
    exact uc q (by simp [work,List.mem_of_mem_take hq])
  have body := kernel u m rv yv flags carry
  let v := run bodyProgram m u
  let t := run [.X L.sign] [] v
  have tf (q : Wire) (hq : q≠L.sign) : t.basis q=v.basis q := by simp [t,run,writeBit,hq]
  have outside (q : Wire) (hr : q∉L.r) (hy : q∉L.y) : t.basis q=s.basis q := by
    by_cases e : q=L.sign
    · subst q
      have vs : v.basis L.sign=u.basis L.sign := body.2.2.2 L.sign sr sy
      calc
        t.basis L.sign= !v.basis L.sign := by simp [t,run,writeBit]
        _= !u.basis L.sign := congrArg Bool.not vs
        _=s.basis L.sign := by simp [u,run,writeBit]
    · exact (tf q e).trans ((body.2.2.2 q hr hy).trans (uf q e))
  have actual : run program m s=t := by
    rw [shape]
    change run ([.X L.sign]++bodyProgram++[.X L.sign]) m s=t
    rw [List.append_assoc,run_append]
    simp only [measurementCount,List.take_zero,List.drop_zero]
    rw [run_append,run_take,zero_records [.X L.sign] rfl]
  rw [actual]
  refine ⟨body.1,?_,?_,?_⟩
  · have rkeep : regValue L.r t.basis=regValue L.r v.basis :=
      regValue_congr _ _ _ (fun q hq => tf q (fun e => sr (e ▸ hq)))
    have ug' : u.basis sign= !origin sign := ug
    rw [rkeep,body.2.1,ug']
    simp only [Bool.not_not]
  · exact (regValue_congr _ _ _ (fun q hq => tf q (fun e => sy (e ▸ hq)))).trans body.2.2.1
  · intro q hr hy
    exact (outside q hr hy).trans (input.2.2 q hr hy)


theorem half_frame_from_kernel (retired : Wire) (divide : Bool) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (origin : BasisState) (clean : Q6EndpointCell.Clean w origin) (X Y : Fp) (word : Fp→Nat)
    (program bodyProgram : Program)
    (shape : program=[.X sign]++bodyProgram++[.X sign])
    (kernel : ∀(s : State)(m : List Bool),
      regValue (Q6EndpointCell.ports w sign).r s.basis=word X →
      regValue (Q6EndpointCell.ports w sign).y s.basis=word Y →
      LiveFlags (Q6EndpointCell.ports w sign) false false false s.basis →
      CleanExcept ((Q6EndpointCell.ports w sign).carry.take 254) retired s.basis →
      (run bodyProgram m s).phase=s.phase ∧
      WordFrame (Q6EndpointCell.ports w sign).r s.basis
        (word (if divide then (X+(if !s.basis sign then Y else -Y))/2
          else 2*X+(if !s.basis sign then -Y else Y))) (run bodyProgram m s).basis) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin (word X) (word Y))
      program (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (word (if divide then (X+(if origin sign then Y else -Y))/2
          else 2*X+(if origin sign then -Y else Y))) (word Y)) := by
  let L := Q6EndpointCell.ports w sign
  apply half_frame_from_pair_kernel retired w sign hn origin clean (word X) (word Y)
    (fun B => word (if divide then (X+(if B then Y else -Y))/2
      else 2*X+(if B then -Y else Y))) (word Y) program bodyProgram shape
  intro s m rv yv flags carry
  have h := kernel s m rv yv flags carry
  have dis : List.Disjoint L.r L.y := by
    have d := (List.nodup_append'.mp (L.toLayout.dataND (List.nodup_append'.mp hn).2.1)).2.2
    apply List.disjoint_left.mpr
    intro q hr hy
    exact List.disjoint_left.mp d hr (by simp [hy])
  refine ⟨h.1,h.2.1,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => h.2.2 q
      (fun bad => List.disjoint_left.mp dis bad hq))).trans yv
  · intro q hr hy
    exact h.2.2 q hr
end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== P1HalfFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


/-- The record's lifetime half frame, with oddWord on both words and
exactly its original layout, retired-member and Clean hypotheses. -/
theorem half_frame (retired : Wire) (divide : Bool) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1)
    (origin : BasisState) (clean : Q6EndpointCell.Clean w origin) (X Y : Fp) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y
      origin (oddWord X) (oddWord Y)) (half retired divide w sign)
      (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (oddWord (if divide then (X+(if origin sign then Y else -Y))/2
          else 2*X+(if origin sign then -Y else Y))) (oddWord Y)) := by
  let L := Q6EndpointCell.ports w sign
  apply DirectPass.half_frame_from_kernel retired divide w sign hn origin clean X Y oddWord
    (half retired divide w sign) (if divide then forward retired L else inverse retired L) rfl
  intro s m rv yv flags carry
  have h := kernel_frame retired divide L (Q6EndpointCell.ports_widths w sign) hn member
    (oddRep X) (oddRep Y) (oddRep_bounds X) (oddRep_bounds Y) s m rv yv flags carry
  have field := kernel_field divide (!s.basis sign) X Y
  simp only [Bool.not_not] at field
  dsimp only at h
  rw [show L.sign=sign from rfl,field] at h
  exact h

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.half_frame
end -- ticket 8 pasted module

-- ===== P1RecodeMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


def recodeForwardWord (n J v : Nat) : Nat :=
  (v%2^n+(if 2^n≤v then 2^n-1-J else J))%2^n+
    2^n*(decide (v<2^n)).toNat


def recodeBackwardWord (n J v : Nat) : Nat :=
  2^n-1-(((if v<2^n then 2^n-1-J else J)+(2^n-1-v%2^n))%2^n)+
    2^n*(decide (v<2^n)).toNat


/-- The sign-controlled low-word addition, at symbolic width and modulus. -/
theorem recode_forward_integer (n J : Nat) (Q z : Int)
    (qpos : 0≤Q) (offset : (J : Int)+Q+1=(2^n : Nat))
    (range : -Q≤z ∧ z≤Q) :
    encodeWord (n+1) (if z<0 then z+Q else z-Q-1)=
      recodeForwardWord n J (encodeWord (n+1) z) := by
  have pos := Nat.two_pow_pos n
  have pow : 2^(n+1)=2*2^n := by rw [Nat.pow_succ,Nat.mul_comm]
  have zr : -((2^(n+1) : Nat) : Int)≤z ∧ z<((2^(n+1) : Nat) : Int) := by
    rw [pow,Nat.cast_mul]; norm_num only [Nat.cast_ofNat]; omega
  have a := BalancedFold.encode_shift (n+1) z zr
  have tr : -((2^(n+1) : Nat) : Int)≤(if z<0 then z+Q else z-Q-1) ∧
      (if z<0 then z+Q else z-Q-1)<((2^(n+1) : Nat) : Int) := by
    rw [pow,Nat.cast_mul]; norm_num only [Nat.cast_ofNat]
    split_ifs <;> omega
  have b := BalancedFold.encode_shift (n+1) (if z<0 then z+Q else z-Q-1) tr
  rw [pow,Nat.cast_mul] at a b
  norm_num only [Nat.cast_ofNat] at a b
  unfold recodeForwardWord
  by_cases neg : z<0
  · simp only [neg,if_true] at a b ⊢
    have outpos : ¬z+Q<0 := by omega
    simp only [outpos,if_false] at b
    have hi : 2^n≤encodeWord (n+1) z := by omega
    have upper : encodeWord (n+1) z-2^n<2^n := by omega
    have lo : encodeWord (n+1) z%2^n=encodeWord (n+1) z-2^n := by
      conv_lhs => rw [show encodeWord (n+1) z=(encodeWord (n+1) z-2^n)+2^n by omega]
      rw [Nat.add_mod_right,Nat.mod_eq_of_lt upper]
    simp only [hi,if_true,show ¬encodeWord (n+1) z<2^n by omega,
      decide_false,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,lo]
    have small : encodeWord (n+1) (z+Q)<2^n := by omega
    rw [show encodeWord (n+1) z-2^n+(2^n-1-J)=
      encodeWord (n+1) (z+Q)+2^n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt small]
  · simp only [neg,if_false] at a b ⊢
    have outneg : z-Q-1<0 := by omega
    simp only [outneg,if_true] at b
    have hi : encodeWord (n+1) z<2^n := by omega
    simp only [show ¬2^n≤encodeWord (n+1) z by omega,if_false,hi,
      decide_true,Bool.toNat_true,Nat.mul_one,Nat.mod_eq_of_lt hi]
    have small : encodeWord (n+1) z+J<2^n := by omega
    rw [Nat.mod_eq_of_lt small]
    omega


/-- The subtraction sees the already-flipped sign, hence the same source
as the preceding forward addition. This includes zero and both endpoints. -/
theorem recode_words_cancel (n J v : Nat) (jfit : J<2^n) (fit : v<2^(n+1)) :
    recodeBackwardWord n J (recodeForwardWord n J v)=v := by
  have pos := Nat.two_pow_pos n
  have pow : 2^(n+1)=2*2^n := by rw [Nat.pow_succ,Nat.mul_comm]
  rw [pow] at fit
  have low := Nat.mod_lt v pos
  have split (hi : 2^n≤v) : v%2^n+2^n=v := by
    have upper : v-2^n<2^n := by omega
    have e : v%2^n=v-2^n := by
      conv_lhs => rw [show v=(v-2^n)+2^n by omega]
      rw [Nat.add_mod_right,Nat.mod_eq_of_lt upper]
    omega
  unfold recodeForwardWord recodeBackwardWord
  by_cases hi : 2^n≤v
  · simp only [hi,if_true,show ¬v<2^n by omega,decide_false,Bool.toNat_false,
      Nat.mul_zero,Nat.add_zero]
    have sum := Nat.mod_lt (v%2^n+(2^n-1-J)) pos
    simp only [sum,if_true,Nat.mod_eq_of_lt sum,decide_true,Bool.toNat_true,Nat.mul_one]
    have cancel := DirectPass.undo_mapped_add (2^n) (2^n-1-J) (v%2^n) 0 pos low (by omega)
    simp only [Nat.add_zero] at cancel
    rw [Nat.add_comm (v%2^n),cancel]
    exact split hi
  · have small : v<2^n := by omega
    simp only [hi,if_false,small,decide_true,Bool.toNat_true,Nat.mul_one,Nat.mod_eq_of_lt small]
    have sum := Nat.mod_lt (v+J) pos
    have high : ¬(v+J)%2^n+2^n<2^n := by omega
    simp only [high,if_false,decide_false,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,
      Nat.add_mod_right,Nat.mod_eq_of_lt sum]
    have cancel := DirectPass.undo_mapped_add (2^n) J v 0 pos small (by omega)
    simp only [Nat.add_zero] at cancel
    rw [Nat.add_comm v J,cancel]


theorem recode_odd_word (x : Fp) :
    encodeWord 256 (oddRep x)=recodeForwardWord 255 (2*BiasedCircuit.jh) (centerWord x) := by
  have hz := centerFp_bounds x
  unfold Centered at hz
  exact recode_forward_integer 255 (2*BiasedCircuit.jh) q (centerFp x)
    (by have c := constants; omega) (by norm_num [BiasedCircuit.jh,q,p]) hz


theorem recode_center_word (x : Fp) :
    centerWord x=recodeBackwardWord 255 (2*BiasedCircuit.jh) (oddWord x) := by
  rw [oddWord,recode_odd_word]
  exact (recode_words_cancel 255 (2*BiasedCircuit.jh) (centerWord x)
    (by norm_num [BiasedCircuit.jh]) (encodeWord_bound _ _)).symm

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.recode_odd_word
#print axioms ECDSAAdd.Entrant.P1Life.recode_center_word
end -- ticket 8 pasted module

-- ===== P1RecodeBits =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def junctionXorBits (n k msb : Nat) : List MappedBit :=
  (List.range n).map fun i => ⟨some msb,k.testBit i⟩


theorem junction_xor_value (n k msb : Nat) (s : BasisState) (fit : k<2^n) :
    mappedValue (junctionXorBits n k msb) s=if s msb then 2^n-1-k else k := by
  induction n generalizing k with
  | zero =>
    have z : k=0 := by simpa using fit
    simp [junctionXorBits,mappedValue,z]
  | succ n ih =>
    have hd : k/2<2^n := by rw [Nat.pow_succ] at fit; omega
    have shape : junctionXorBits (n+1) k msb=
        (⟨some msb,k.testBit 0⟩ : MappedBit)::junctionXorBits n (k/2) msb := by
      simp [junctionXorBits,List.range_succ_eq_map,List.map_map,Function.comp_def,Nat.testBit_succ]
    rw [shape,mappedValue,ih _ hd,Nat.pow_succ]
    have split := Nat.mod_add_div k 2
    have small := Nat.mod_lt k (by decide : 0<2)
    cases sn : s msb <;> by_cases odd : k%2=1 <;>
      simp [MappedBit.value,Nat.testBit_zero,sn,odd] <;> omega


theorem junction_xor_sources (n k msb q : Nat)
    (hq : q∈mappedWires (junctionXorBits n k msb)) : q=msb := by
  simp only [junctionXorBits,mappedWires,List.flatMap_map,List.mem_flatMap] at hq
  obtain ⟨i,hi,hq⟩ := hq
  simpa using hq











end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1RecodeCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_read_shape (low : List Wire) (msb : Wire) (b : BasisState) :
    regValue (low++[msb]) b%2^low.length=regValue low b ∧
    decide (2^low.length≤regValue (low++[msb]) b)=b msb ∧
    decide (regValue (low++[msb]) b<2^low.length)= !b msb := by
  have bound := regValue_lt low b
  have split : regValue (low++[msb]) b=regValue low b+2^low.length*(b msb).toNat := by
    rw [regValue_append]
    simp [regValue,Bool.toNat,Bool.cond_eq_ite]
  rw [split]
  cases h : b msb <;> simp only [h,Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,
    Nat.mul_one,Nat.add_zero,Bool.not_false,Bool.not_true]
  · simp [Nat.mod_eq_of_lt bound,show ¬2^low.length≤regValue low b by omega,bound]
  · simp [Nat.add_mod_right,Nat.mod_eq_of_lt bound,
      show 2^low.length≤regValue low b+2^low.length by omega,
      show ¬regValue low b+2^low.length<2^low.length by omega]


theorem junction_recode_forward_core (low cs : List Wire) (msb cin k : Wire)
    (nd : (msb::cin::(low++cs)).Nodup) (len : cs.length+1=low.length)
    (fit : k<2^low.length) (s : State) (m : List Bool)
    (zero : s.basis cin=false) (clean : ∀q∈cs,s.basis q=false) :
    let p := mappedAdd (junctionXorBits low.length k msb) low cs cin++[.X msb]
    (run p m s).phase=s.phase ∧ DirectPass.WordFrame (low++[msb]) s.basis
      (recodeForwardWord low.length k (regValue (low++[msb]) s.basis)) (run p m s).basis := by
  have mn : msb∉low := by
    intro h; exact (List.nodup_cons.mp nd).1 (by simp [h])
  have add := DirectPass.mapped_correct false (junctionXorBits low.length k msb) low cs cin
    (List.nodup_cons.mp nd).2 (by
      intro q hq
      rw [junction_xor_sources _ _ _ q hq]
      exact (List.nodup_cons.mp nd).1)
    (by simp [junctionXorBits]) len s m clean
  simp only [DirectPass.mappedProgram,Bool.false_eq_true,if_false] at add
  let u := run (mappedAdd (junctionXorBits low.length k msb) low cs cin) m s
  let t := run [.X msb] [] u
  have um : u.basis msb=s.basis msb := add.2.2 _ mn
  have tk (q : Wire) (hq : q≠msb) : t.basis q=u.basis q := by simp [t,run,writeBit,hq]
  have tl : regValue low t.basis=regValue low u.basis :=
    regValue_congr _ _ _ (fun q hq => tk q (fun e => mn (e ▸ hq)))
  have tm : t.basis msb= !s.basis msb := by simp [t,run,writeBit,um]
  have shape := junction_read_shape low msb s.basis
  have value : regValue (low++[msb]) t.basis=
      recodeForwardWord low.length k (regValue (low++[msb]) s.basis) := by
    rw [regValue_append,tl]
    have av := add.2.1
    simp only [DirectPass.mappedResult,Bool.false_eq_true,if_false,junction_xor_value _ _ _ _ fit,
      zero,Bool.toNat_false,Nat.add_zero] at av
    rw [av]
    unfold recodeForwardWord
    rw [shape.1,shape.2.2]
    have cond : (if 2^low.length≤regValue (low++[msb]) s.basis then 2^low.length-1-k else k)=
        (if s.basis msb then 2^low.length-1-k else k) := by
      rw [←shape.2.1]; simp
    rw [cond,Nat.add_comm (regValue low s.basis)]
    simp [regValue,tm,Bool.toNat,Bool.cond_eq_ite]
  simp only [run_append,run_take]
  change t.phase=s.phase ∧ DirectPass.WordFrame _ _ _ t.basis
  refine ⟨add.1,value,?_⟩
  intro q hq
  have h : q∉low ∧ q≠msb := by simpa only [List.mem_append,List.mem_singleton,not_or] using hq
  exact (tk q h.2).trans (add.2.2 q h.1)


theorem junction_recode_backward_core (low cs : List Wire) (msb cin k : Wire)
    (nd : (msb::cin::(low++cs)).Nodup) (len : cs.length+1=low.length)
    (fit : k<2^low.length) (s : State) (m : List Bool)
    (zero : s.basis cin=false) (clean : ∀q∈cs,s.basis q=false) :
    let p := [.X msb]++mappedSub (junctionXorBits low.length k msb) low cs cin
    (run p m s).phase=s.phase ∧ DirectPass.WordFrame (low++[msb]) s.basis
      (recodeBackwardWord low.length k (regValue (low++[msb]) s.basis)) (run p m s).basis := by
  have hnd := List.nodup_cons.mp nd
  have mn : msb∉low := fun h => hnd.1 (by simp [h])
  let u := run [.X msb] [] s
  have uk (q : Wire) (hq : q≠msb) : u.basis q=s.basis q := by simp [u,run,writeBit,hq]
  have um : u.basis msb= !s.basis msb := by simp [u,run,writeBit]
  have ul : regValue low u.basis=regValue low s.basis :=
    regValue_congr _ _ _ (fun q hq => uk q (fun e => mn (e ▸ hq)))
  have uc : u.basis cin=false := (uk cin (by intro e; exact hnd.1 (by simp [←e]))).trans zero
  have add := DirectPass.mapped_correct true (junctionXorBits low.length k msb) low cs cin
    hnd.2 (by intro q hq; rw [junction_xor_sources _ _ _ q hq]; exact hnd.1)
    (by simp [junctionXorBits]) len u m (by
      intro q hq
      exact (uk q (by intro e; exact hnd.1 (by simp [←e,hq]))).trans (clean q hq))
  simp only [DirectPass.mappedProgram,if_true] at add
  let t := run (mappedSub (junctionXorBits low.length k msb) low cs cin) m u
  have tm : t.basis msb= !s.basis msb := (add.2.2 _ mn).trans um
  have shape := junction_read_shape low msb s.basis
  have value : regValue (low++[msb]) t.basis=
      recodeBackwardWord low.length k (regValue (low++[msb]) s.basis) := by
    rw [regValue_append]
    have av := add.2.1
    simp only [DirectPass.mappedResult,if_true,junction_xor_value _ _ _ _ fit,
      uc,Bool.toNat_false,Nat.add_zero,ul,um] at av
    rw [av]
    unfold recodeBackwardWord
    rw [shape.1,shape.2.2]
    have cond : (if regValue (low++[msb]) s.basis<2^low.length then 2^low.length-1-k else k)=
        (if !s.basis msb then 2^low.length-1-k else k) := by
      rw [←shape.2.2]; simp
    rw [cond]
    simp [regValue,tm,Bool.toNat,Bool.cond_eq_ite]
  simp only [run_append,measurementCount,List.take_zero,List.drop_zero]
  change t.phase=s.phase ∧ DirectPass.WordFrame _ _ _ t.basis
  refine ⟨add.1,value,?_⟩
  intro q hq
  have h : q∉low ∧ q≠msb := by simpa only [List.mem_append,List.mem_singleton,not_or] using hq
  exact (add.2.2 q h.1).trans (uk q h.2)

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1RecodeLayout =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_filter_length (xs : List Wire) (retired : Wire)
    (nd : xs.Nodup) (member : retired∈xs) :
    (xs.filter (fun q => q != retired)).length+1=xs.length := by
  induction xs with
  | nil => simp at member
  | cons a xs ih =>
    have hn := List.nodup_cons.mp nd
    by_cases eq : a=retired
    · subst a
      have same : xs.filter (fun q => q != retired)=xs := by
        apply List.filter_eq_self.mpr
        intro q hq
        simp only [bne_iff_ne]
        intro e
        exact hn.1 (e ▸ hq)
      simp [same]
    · have mem : retired∈xs := by simpa [Ne.symm eq] using member
      have h := ih hn.2 mem
      simp [eq,h]


theorem recode_y_shape (retired : Wire) (toOdd : Bool) (L : Layout) (hw : L.Widths) :
    recode retired toOdd L L.y=
      if toOdd then mappedAdd (junctionXorBits L.ylow.length (2*BiasedCircuit.jh) L.ymsb)
        L.ylow (recodeBank retired L) L.lower++[.X L.ymsb]
      else [.X L.ymsb]++mappedSub (junctionXorBits L.ylow.length (2*BiasedCircuit.jh) L.ymsb)
        L.ylow (recodeBank retired L) L.lower := by
  have take : L.y.take 255=L.ylow := by
    change (L.ylow++[L.ymsb]).take 255=L.ylow
    rw [←hw.2.1,List.take_left]
  have top : L.y.getD 255 0=L.ymsb := by
    change (L.ylow++[L.ymsb]).getD 255 0=L.ymsb
    rw [List.getD_append_right _ _ _ _ (by rw [hw.2.1]),hw.2.1]
    simp
  simp only [recode,take,top,hw.2.1]
  rfl


theorem recode_bank_length (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    (recodeBank retired L).length=254 := by
  have nd : (L.carry.take 254).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have lim := (List.take_sublist 254 L.carry).count_le q
    simp only [List.count_cons,List.count_append,List.count_nil] at h
    omega
  have h := junction_filter_length (L.carry.take 254) retired nd member
  have len : (L.carry.take 254).length=254 := by simp [List.length_take,hw.2.2]
  simp only [recodeBank,List.length_append,List.length_singleton]
  omega


theorem recode_y_nodup (retired : Wire) (L : Layout) (hn : L.wires.Nodup) :
    (L.ymsb::L.lower::(L.ylow++recodeBank retired L)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
  have a := (List.filter_sublist (p := fun w => w != retired) (l := L.carry.take 254)).count_le q
  have b := (List.take_sublist 254 L.carry).count_le q
  simp only [recodeBank,BalancedCleanup.Layout.y,List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega


theorem recode_y_correct (retired : Wire) (toOdd : Bool) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254)
    (s : State) (m : List Bool) (lower : s.basis L.lower=false)
    (one : s.basis L.one=false)
    (clean : DirectPass.CleanExcept (L.carry.take 254) retired s.basis) :
    (run (recode retired toOdd L L.y) m s).phase=s.phase ∧
    DirectPass.WordFrame L.y s.basis
      ((if toOdd then recodeForwardWord else recodeBackwardWord)
        255 (2*BiasedCircuit.jh) (regValue L.y s.basis))
      (run (recode retired toOdd L L.y) m s).basis := by
  have nd := recode_y_nodup retired L hn
  have len : (recodeBank retired L).length+1=L.ylow.length := by
    rw [recode_bank_length retired L hw hn member,hw.2.1]
  have fit : 2*BiasedCircuit.jh<2^L.ylow.length := by rw [hw.2.1]; norm_num [BiasedCircuit.jh]
  have bank (q : Wire) (hq : q∈recodeBank retired L) : s.basis q=false := by
    simp only [recodeBank,List.mem_append,List.mem_filter,List.mem_singleton,bne_iff_ne] at hq
    rcases hq with hq|rfl
    · exact clean q hq.1 hq.2
    · exact one
  rw [recode_y_shape retired toOdd L hw]
  cases toOdd
  · simpa only [Bool.false_eq_true,if_false,hw.2.1] using
      junction_recode_backward_core L.ylow (recodeBank retired L) L.ymsb L.lower
        (2*BiasedCircuit.jh) nd len fit s m lower bank
  · simpa only [if_true,hw.2.1] using
      junction_recode_forward_core L.ylow (recodeBank retired L) L.ymsb L.lower
        (2*BiasedCircuit.jh) nd len fit s m lower bank

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1RecodeTriple =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


























































end ECDSAAdd.Entrant.P1Life



end -- ticket 8 pasted module

-- ===== P1JunctionMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def junctionToOdd (R : Int) : Int := if R<0 then R+q else R-q-1

def junctionToStandard (R : Int) : Int := if R<0 then R+q+1 else R-q


theorem junction_to_odd_rep (R : Int) (hr : Centered R) :
    oddRep (R : Fp)=junctionToOdd R := by
  simp only [oddRep,centerFp_of_center R hr,junctionToOdd]


theorem junction_to_odd_bounds (R : Int) (hr : Centered R) : OddDomain (junctionToOdd R) := by
  rw [←junction_to_odd_rep R hr]
  exact oddRep_bounds _


theorem junction_to_standard_center (R : Int) (hr : OddDomain R) :
    centerFp (oddDecode R)=junctionToStandard R := by
  have eq := oddRep_inverse R hr
  have bound := centerFp_bounds (oddDecode R)
  dsimp only [oddRep] at eq
  unfold Centered at bound
  unfold OddDomain at hr
  unfold junctionToStandard
  split_ifs at eq ⊢ <;> omega


theorem junction_to_standard_bounds (R : Int) (hr : OddDomain R) :
    Centered (junctionToStandard R) := by
  rw [←junction_to_standard_center R hr]
  exact centerFp_bounds _


theorem junction_to_odd_sign (R : Int) (hr : Centered R) :
    negative (junctionToOdd R)= !negative R := by
  unfold Centered at hr
  by_cases rn : R<0 <;> simp [junctionToOdd,negative,rn] <;> omega


theorem junction_to_standard_sign (R : Int) (hr : OddDomain R) :
    negative (junctionToStandard R)= !negative R := by
  unfold OddDomain at hr
  by_cases rn : R<0 <;> simp [junctionToStandard,negative,rn] <;> omega


/-- Complement is a word identity at symbolic width, independent of domain. -/
theorem junction_complement_encoded (n : Nat) (R : Int) :
    2^n-1-encodeWord n R=encodeWord n (-R-1) := by
  have pos : (0 : Int)<((2^n : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos n
  have bound := encodeWord_bound n R
  have rem := Int.emod_nonneg R (ne_of_gt pos)
  have small := Int.emod_lt_of_pos R pos
  have eq : (-R-1)%((2^n : Nat) : Int)=
      (- (R%((2^n : Nat) : Int))-1)%((2^n : Nat) : Int) := by
    have div := Int.emod_add_mul_ediv R ((2^n : Nat) : Int)
    have adjust : -R-1=(- (R%((2^n : Nat) : Int))-1)+
        ((2^n : Nat) : Int)*(-(R/((2^n : Nat) : Int))) := by nlinarith [div]
    rw [adjust]
    simp
  have plus : (- (R%((2^n : Nat) : Int))-1)%((2^n : Nat) : Int)=
      (((2^n : Nat) : Int)-1-R%((2^n : Nat) : Int))%((2^n : Nat) : Int) := by
    rw [show ((2^n : Nat) : Int)-1-R%((2^n : Nat) : Int)=
      (- (R%((2^n : Nat) : Int))-1)+((2^n : Nat) : Int) by ring,Int.add_emod_right]
  have reduced : (((2^n : Nat) : Int)-1-R%((2^n : Nat) : Int))%((2^n : Nat) : Int)=
      ((2^n : Nat) : Int)-1-R%((2^n : Nat) : Int) :=
    Int.emod_eq_of_lt (by omega) (by omega)
  apply Int.ofNat_inj.mp
  rw [Nat.cast_sub (by omega : encodeWord n R≤2^n-1),
    Nat.cast_sub (by have h := Nat.two_pow_pos n; omega : 1≤2^n),Nat.cast_one,
    encodeWord_cast,encodeWord_cast,eq,plus,reduced]


theorem junction_emit_odd_value (R : Int) (hr : Centered R) :
    (2^255-1-encodeWord 255 (normalizedR R)+h.toNat)%2^255=
      encodeWord 255 (magnitude (junctionToOdd R)) := by
  rw [junction_complement_encoded,DirectPass.encoded_add_nat,
    Int.toNat_of_nonneg (le_of_lt constants.2.2.2.2.1)]
  congr 1
  have c := constants
  have sg := junction_to_odd_sign R hr
  unfold normalizedR magnitude signBit
  rw [sg]
  by_cases rn : R<0 <;> simp [negative,rn,junctionToOdd] <;> omega


theorem junction_emit_standard_value (R : Int) (hr : OddDomain R) :
    (2^255-1-encodeWord 255 (oddNormalized R)+BalancedCleanup.positiveLiteral+
      (negative R).toNat)%2^255=encodeWord 255 (magnitude (junctionToStandard R)) := by
  rw [junction_complement_encoded,Nat.add_assoc,DirectPass.encoded_add_nat,Nat.cast_add]
  have c := constants
  have lit : (BalancedCleanup.positiveLiteral : Int)=h-1 :=
    Int.toNat_of_nonneg (by omega)
  rw [lit]
  congr 1
  have sg := junction_to_standard_sign R hr
  unfold oddNormalized magnitude
  rw [sg]
  by_cases rn : R<0 <;> simp [negative,rn,junctionToStandard] <;> omega


theorem junction_accept_odd_value (R : Int) (hr : OddDomain R) :
    2^255-1-encodeWord 255 (magnitude R-h)=
      encodeWord 255 (normalizedR (junctionToStandard R)) := by
  rw [junction_complement_encoded]
  congr 1
  have c := constants
  have sg := junction_to_standard_sign R hr
  unfold normalizedR magnitude signBit
  rw [sg]
  by_cases rn : R<0 <;> simp [negative,rn,junctionToStandard] <;> omega

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionViews =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_not_low (retired : Wire) (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (origin : BasisState) (v Y : Nat) (P N : Bool) :
    Triple (DirectPass.LowBoundary L retired origin v Y P N) (notRegister L.low)
      (DirectPass.LowBoundary L retired origin (2^255-1-v) Y P N) := by
  have nd : L.low.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h
    omega
  intro s m input
  apply DirectPass.low_frame_of_word L hn retired origin _ _ Y P N _ s m input
  rw [notRegister_correct L.low nd]
  refine ⟨rfl,?_,?_⟩
  · rw [regValue_congr L.low _ (fun q => !s.basis q) (by intro q hq; simp [hq]),regValue_complement]
    have len : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
    rw [len,input.1]
  · intro q hq
    simp [hq]


theorem junction_flip_lower (retired : Wire) (L : Layout) (hn : L.wires.Nodup)
    (origin : BasisState) (v Y : Nat) (P N : Bool) :
    Triple (DirectPass.LowBoundary L retired origin v Y P N) [.X L.lower]
      (DirectPass.LowBoundary L retired origin v Y P (!N)) := by
  have away (q : Wire) (hq : q∈L.r++L.y++[L.parity,L.one]++L.carry) : q≠L.lower := by
    intro e
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have a := List.count_pos_iff.mpr hq
    subst q
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h a
    omega
  intro s m input
  rcases input with ⟨low,top,ys,⟨parity,lower,one⟩,clean,frame⟩
  have keep (q : Wire) (hq : q≠L.lower) : (run [.X L.lower] m s).basis q=s.basis q := by
    simp [run,writeBit,hq]
  refine ⟨rfl,?_,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => keep q (away q (by
      simp [BalancedCleanup.Layout.r,hq])))).trans low
  · exact (keep _ (away _ (by simp [BalancedCleanup.Layout.r]))).trans top
  · exact (regValue_congr _ _ _ (fun q hq => keep q (away q (by simp [hq])))).trans ys
  · refine ⟨(keep _ (away _ (by simp))).trans parity,?_,(keep _ (away _ (by simp))).trans one⟩
    simp [run,writeBit,lower]
  · intro q hq qr
    exact (keep q (away q (by simp [List.mem_of_mem_take hq]))).trans (clean q hq qr)
  · intro q hq hp hl ho
    exact (keep q hl).trans (frame q hq hp hl ho)


theorem junction_literal_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) (origin : BasisState)
    (v Y k : Nat) (P N : Bool) :
    Triple (DirectPass.LowBoundary L retired origin v Y P N)
      (Q6LifetimeResearch.move retired L.rmsb
        (literalConstAdd L.low (L.carry.take 254) L.lower L.one k))
      (DirectPass.LowBoundary L retired origin ((v+k+N.toNat)%2^255) Y P N) := by
  have nd : (L.rmsb::L.one::L.lower::(L.low++L.carry.take 254)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have lim := (List.take_sublist 254 L.carry).count_le q
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have len : (L.carry.take 254).length+1=L.low.length := by
    simp [BalancedCleanup.Layout.low,List.length_take,hw.1,hw.2.2]
  have lowlen : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  intro s m input
  have h := DirectPass.literal_loan L.low (L.carry.take 254) L.lower L.one L.rmsb retired k
    nd member len s m input.2.2.2.1.2.2 input.2.1 input.2.2.2.2.1
  rw [input.1,input.2.2.2.1.2.1,lowlen] at h
  exact DirectPass.low_frame_of_word L hn retired origin _ _ Y P N _ s m input h


/-- Explicit sign-complement emitter; only its generic commuting-CNOT
reversal is used, never a bridge between generations of a cell. -/
theorem junction_restore_explicit (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (origin : BasisState) (R : Int) (Y : Nat) (P : Bool)
    (hr : -((2^255 : Nat) : Int)≤R ∧ R<((2^255 : Nat) : Int)) :
    Triple (DirectPass.LowBoundary L retired origin (encodeWord 255 (magnitude R)) Y P (negative R))
      (signComplement L.lower L.r++[.CX L.rmsb L.lower])
      (DirectPass.WordBoundary L retired origin (encodeWord 256 R) Y P) := by
  have n0 : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have rnd : L.r.Nodup := (List.nodup_append'.mp (L.toLayout.dataND n0)).1
  have away : L.lower∉L.r := fun h => BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [h])
  intro s m input
  have h := DirectPass.restore_sign_boundary_values retired L hw hn origin R Y P hr s m input
  have shape : run (BalancedCleanup.prepareSign L.toLayout).reverse m s=
      run (signComplement L.lower L.r++[.CX L.rmsb L.lower]) m s := by
    simp only [BalancedCleanup.prepareSign,List.reverse_append,List.reverse_singleton,run_append,run_take]
    rw [BiasedInverse.complement_reverse L.lower L.r rnd away]
    simp only [measurementCount_reverse]
  rw [shape] at h
  exact h

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionPasses =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem emit_odd_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (R Y : Int) (hr : Centered R) :
    Triple (DirectPass.AfterComparison DirectPass.standardEncoding L retired origin R Y)
      (emitOdd retired L) (DirectPass.AfterHalf L retired origin (junctionToOdd R) Y) := by
  have a := junction_not_low retired L hw hn origin (encodeWord 255 (normalizedR R))
    (encodeWord 256 Y) false (negative R)
  have b := short_boundary retired L hw hn member origin
    (2^255-1-encodeWord 255 (normalizedR R)) (encodeWord 255 (magnitude (junctionToOdd R)))
    (encodeWord 256 Y) h.toNat false (negative R) p1_h_short_constants.1 (junction_emit_odd_value R hr)
  have c := junction_flip_lower retired L hn origin (encodeWord 255 (magnitude (junctionToOdd R)))
    (encodeWord 256 Y) false (negative R)
  have d := junction_restore_explicit retired L hw hn origin (junctionToOdd R) (encodeWord 256 Y) false
    (oddDomain_signed _ (junction_to_odd_bounds R hr))
  rw [junction_to_odd_sign R hr] at d
  simpa only [emitOdd,List.append_assoc] using Triple.seq a (Triple.seq b (Triple.seq c d))


theorem emit_standard_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (R Y : Int) (hr : OddDomain R) :
    Triple (DirectPass.AfterComparison DirectPass.oddEncoding L retired origin R Y)
      (emitStandard retired L) (DirectPass.AfterHalf L retired origin (junctionToStandard R) Y) := by
  have a := junction_not_low retired L hw hn origin (encodeWord 255 (oddNormalized R))
    (encodeWord 256 Y) false (negative R)
  have b := junction_literal_boundary retired L hw hn (List.mem_of_mem_drop member) origin
    (2^255-1-encodeWord 255 (oddNormalized R)) (encodeWord 256 Y)
    BalancedCleanup.positiveLiteral false (negative R)
  rw [junction_emit_standard_value R hr] at b
  have c := junction_flip_lower retired L hn origin (encodeWord 255 (magnitude (junctionToStandard R)))
    (encodeWord 256 Y) false (negative R)
  have range : -((2^255 : Nat) : Int)≤junctionToStandard R ∧
      junctionToStandard R<((2^255 : Nat) : Int) := by
    have h := junction_to_standard_bounds R hr
    have hp := constants
    unfold Centered at h
    omega
  have d := junction_restore_explicit retired L hw hn origin (junctionToStandard R)
    (encodeWord 256 Y) false range
  rw [junction_to_standard_sign R hr] at d
  simpa only [emitStandard,List.append_assoc] using Triple.seq a (Triple.seq b (Triple.seq c d))


theorem accept_odd_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (R Y : Int) (hr : OddDomain R) :
    Triple (DirectPass.AfterHalf L retired origin R Y) (acceptOdd retired L)
      (DirectPass.AfterComparison DirectPass.standardEncoding L retired origin (junctionToStandard R) Y) := by
  have a := DirectPass.prepare_sign_boundary_wide retired L hw hn origin R Y (oddDomain_signed R hr)
  have b := junction_flip_lower retired L hn origin (encodeWord 255 (magnitude R))
    (encodeWord 256 Y) false (negative R)
  have arithmetic : (encodeWord 255 (magnitude R)+encodeWord 255 (-h))%2^255=
      encodeWord 255 (magnitude R-h) := by
    simpa only [sub_eq_add_neg] using DirectPass.encoded_add_encoded 255 (magnitude R) (-h)
  have c := short_boundary retired L hw hn member origin (encodeWord 255 (magnitude R))
    (encodeWord 255 (magnitude R-h)) (encodeWord 256 Y) (encodeWord 255 (-h))
    false (!negative R) p1_h_short_constants.2 arithmetic
  have d := junction_not_low retired L hw hn origin (encodeWord 255 (magnitude R-h))
    (encodeWord 256 Y) false (!negative R)
  rw [junction_accept_odd_value R hr,←junction_to_standard_sign R hr] at d
  rw [←junction_to_standard_sign R hr] at b c
  simpa only [acceptOdd,BalancedCleanup.prepareSign,List.append_assoc] using
    Triple.seq a (Triple.seq b (Triple.seq c d))

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.emit_odd_boundary
#print axioms ECDSAAdd.Entrant.P1Life.emit_standard_boundary
#print axioms ECDSAAdd.Entrant.P1Life.accept_odd_boundary
end -- ticket 8 pasted module

-- ===== P1JunctionChains =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_standard_head_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (X Y : Int) (hx : Centered X) (hy : Centered Y) :
    Triple (DirectPass.AfterHalf L retired origin X Y) (junctionStdHead retired L)
      (DirectPass.AfterComparison DirectPass.standardEncoding L retired origin
        (halfResult (rawSum (origin L.sign) X Y)) Y) := by
  have a := DirectPass.seed_to_raw retired L hw hn member origin X Y hx hy
  have b := DirectPass.raw_to_fold retired L hw hn (List.mem_of_mem_drop member) origin
    (rawSum (origin L.sign) X Y) Y (rawSum_bounds _ X Y hx hy)
  have c := DirectPass.fold_to_comparison retired L hw hn member origin X Y hx hy
  simpa only [junctionStdHead,List.append_assoc] using Triple.seq a (Triple.seq b c)


theorem junction_odd_head_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (X Y : Int) (hx : OddDomain X) (hy : OddDomain Y) :
    Triple (DirectPass.AfterHalf L retired origin X Y) (junctionOddHead retired L)
      (DirectPass.AfterComparison DirectPass.oddEncoding L retired origin
        (oddFold (oddSum (origin L.sign) X Y)) Y) := by
  have a := seed_to_raw retired L hw hn member origin X Y hx hy
  have b := raw_to_fold retired L hw hn (List.mem_of_mem_drop member) origin
    (oddSum (origin L.sign) X Y) Y (oddSum_bounds _ X Y hx hy)
  have c := fold_to_comparison retired L hw hn member origin X Y hx hy
  simpa only [junctionOddHead,List.append_assoc] using Triple.seq a (Triple.seq b c)


theorem junction_standard_rest_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    Triple (DirectPass.AfterComparison DirectPass.standardEncoding L retired origin R Y)
      (junctionStdRest retired L)
      (DirectPass.AfterHalf L retired origin (BalancedInverse.result (origin L.sign) R Y) Y) := by
  let B := origin L.sign
  let X := BalancedInverse.result B R Y
  let T := rawSum B X Y
  have hx := BalancedInverse.result_bounds B R Y
  have ht := rawSum_bounds B X Y hx hy
  have half : halfResult T=R := BalancedInverse.result_half B R Y hr hy
  have interval : originalParity T=decide (q < |2*R-signedY B Y|) :=
    (BalancedInverse.result_parity B R Y hr hy).symm
  have a := DirectPass.comparison_to_fold retired L hw hn member origin T R Y hr hy interval
  have b := DirectPass.fold_to_raw retired L hw hn (List.mem_of_mem_drop member) origin T Y ht
  rw [half] at b
  have c := DirectPass.rawSub_boundary retired L hw hn member origin B X Y hx hy rfl
  simpa only [junctionStdRest,List.append_assoc] using Triple.seq a (Triple.seq b c)


theorem junction_fso_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (X Y : Int) (hx : Centered X) (hy : Centered Y) :
    Triple (DirectPass.AfterHalf L retired origin X Y) (junctionStdHead retired L++emitOdd retired L)
      (DirectPass.AfterHalf L retired origin (junctionToOdd (halfResult (rawSum (origin L.sign) X Y))) Y) :=
  Triple.seq (junction_standard_head_boundary retired L hw hn member origin X Y hx hy)
    (emit_odd_boundary retired L hw hn member origin _ Y
      (halfResult_spec _ (rawSum_bounds _ X Y hx hy)).1)


theorem junction_fos_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (X Y : Int) (hx : OddDomain X) (hy : OddDomain Y) :
    Triple (DirectPass.AfterHalf L retired origin X Y) (junctionOddHead retired L++emitStandard retired L)
      (DirectPass.AfterHalf L retired origin (junctionToStandard (oddFold (oddSum (origin L.sign) X Y))) Y) :=
  Triple.seq (junction_odd_head_boundary retired L hw hn member origin X Y hx hy)
    (emit_standard_boundary retired L hw hn member origin _ Y
      (oddFold_bounds _ (oddSum_bounds _ X Y hx hy)))


theorem junction_gso_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (R Y : Int) (hr : OddDomain R) (hy : Centered Y) :
    Triple (DirectPass.AfterHalf L retired origin R Y) (acceptOdd retired L++junctionStdRest retired L)
      (DirectPass.AfterHalf L retired origin (BalancedInverse.result (origin L.sign) (junctionToStandard R) Y) Y) :=
  Triple.seq (accept_odd_boundary retired L hw hn member origin R Y hr)
    (junction_standard_rest_boundary retired L hw hn member origin _ Y (junction_to_standard_bounds R hr) hy)

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionKernelFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_to_standard_odd_rep (x : Fp) : junctionToStandard (oddRep x)=centerFp x := by
  rw [←junction_to_standard_center _ (oddRep_bounds x),oddRep_field]


theorem junction_fso_frame (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (X Y : Fp) (s : State) (m : List Bool)
    (rv : regValue L.r s.basis=centerWord X) (yv : regValue L.y s.basis=centerWord Y)
    (flags : DirectPass.LiveFlags L false false false s.basis)
    (clean : DirectPass.CleanExcept (L.carry.take 254) retired s.basis) :
    let p := junctionStdHead retired L++emitOdd retired L
    (run p m s).phase=s.phase ∧ DirectPass.WordFrame L.r s.basis
      (oddWord ((X+(if !s.basis L.sign then Y else -Y))/2)) (run p m s).basis := by
  have b := junction_fso_boundary retired L hw hn member s.basis
    (centerFp X) (centerFp Y) (centerFp_bounds X) (centerFp_bounds Y)
  have h := DirectPass.kernel_frame_of_boundary retired L (centerFp X) (centerFp Y) _ _
    s m rv yv flags clean b
  have field := DirectPass.kernel_field true (!s.basis L.sign) X Y
  simp only [DirectPass.kernelResult,if_true,Bool.not_not] at field
  rw [field] at h
  exact h


theorem junction_fos_frame (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (X Y : Fp) (s : State) (m : List Bool)
    (rv : regValue L.r s.basis=oddWord X) (yv : regValue L.y s.basis=oddWord Y)
    (flags : DirectPass.LiveFlags L false false false s.basis)
    (clean : DirectPass.CleanExcept (L.carry.take 254) retired s.basis) :
    let p := junctionOddHead retired L++emitStandard retired L
    (run p m s).phase=s.phase ∧ DirectPass.WordFrame L.r s.basis
      (centerWord ((X+(if !s.basis L.sign then Y else -Y))/2)) (run p m s).basis := by
  have b := junction_fos_boundary retired L hw hn member s.basis
    (oddRep X) (oddRep Y) (oddRep_bounds X) (oddRep_bounds Y)
  have h := DirectPass.kernel_frame_of_boundary retired L (oddRep X) (oddRep Y) _ _
    s m rv yv flags clean b
  have field := kernel_field true (!s.basis L.sign) X Y
  simp only [kernelResult,if_true,Bool.not_not] at field
  rw [field,junction_to_standard_odd_rep] at h
  exact h


theorem junction_gso_frame (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (X Y : Fp) (s : State) (m : List Bool)
    (rv : regValue L.r s.basis=oddWord X) (yv : regValue L.y s.basis=centerWord Y)
    (flags : DirectPass.LiveFlags L false false false s.basis)
    (clean : DirectPass.CleanExcept (L.carry.take 254) retired s.basis) :
    let p := acceptOdd retired L++junctionStdRest retired L
    (run p m s).phase=s.phase ∧ DirectPass.WordFrame L.r s.basis
      (centerWord (2*X+(if !s.basis L.sign then -Y else Y))) (run p m s).basis := by
  have b := junction_gso_boundary retired L hw hn member s.basis
    (oddRep X) (centerFp Y) (oddRep_bounds X) (centerFp_bounds Y)
  have h := DirectPass.kernel_frame_of_boundary retired L (oddRep X) (centerFp Y) _ _
    s m rv yv flags clean b
  have field := DirectPass.kernel_field false (!s.basis L.sign) X Y
  simp only [DirectPass.kernelResult,Bool.false_eq_true,if_false,Bool.not_not] at field
  rw [junction_to_standard_odd_rep,field] at h
  exact h

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionCompose =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_register_disjoint (L : Layout) (hn : L.wires.Nodup) : L.r.Disjoint L.y := by
  apply List.disjoint_left.mpr
  intro q hr hy
  have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
  have a := List.count_pos_iff.mpr hr
  have b := List.count_pos_iff.mpr hy
  simp only [List.count_cons,List.count_append,List.count_nil] at h
  omega


theorem junction_scratch_preserved (retired : Wire) (L : Layout) (s t : State)
    (same : ∀q∈[L.parity,L.lower,L.one]++L.carry,t.basis q=s.basis q)
    (flags : DirectPass.LiveFlags L false false false s.basis)
    (clean : DirectPass.CleanExcept (L.carry.take 254) retired s.basis) :
    DirectPass.LiveFlags L false false false t.basis ∧
      DirectPass.CleanExcept (L.carry.take 254) retired t.basis := by
  refine ⟨⟨(same _ (by simp)).trans flags.1,(same _ (by simp)).trans flags.2.1,
    (same _ (by simp)).trans flags.2.2⟩,?_⟩
  intro q hq qr
  exact (same q (by simp [List.mem_of_mem_take hq])).trans (clean q hq qr)


theorem junction_recode_after (retired : Wire) (toOdd : Bool) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254)
    (body : Program) (R Y : Nat) (s : State) (m : List Bool)
    (yv : regValue L.y s.basis=Y)
    (flags : DirectPass.LiveFlags L false false false s.basis)
    (clean : DirectPass.CleanExcept (L.carry.take 254) retired s.basis)
    (bodyProof : ∀ tape, (run body tape s).phase=s.phase ∧
      DirectPass.WordFrame L.r s.basis R (run body tape s).basis) :
    (run (body++recode retired toOdd L L.y) m s).phase=s.phase ∧
    PairFrame L.r L.y s.basis R
      ((if toOdd then recodeForwardWord else recodeBackwardWord) 255 (2*BiasedCircuit.jh) Y)
      (run (body++recode retired toOdd L L.y) m s).basis := by
  have dis := junction_register_disjoint L hn
  let u := run body (m.take (measurementCount body)) s
  have a := bodyProof (m.take (measurementCount body))
  have uv : regValue L.y u.basis=Y :=
    (regValue_congr _ _ _ (fun q hq => a.2.2 q
      (fun bad => List.disjoint_left.mp dis bad hq))).trans yv
  have scratch := junction_scratch_preserved retired L s u (by
    intro q hq
    exact a.2.2 q (DirectPass.work_outside L hn q (by
      simp only [List.mem_append,List.mem_cons,List.mem_singleton] at hq
      simp only [work,List.mem_append,List.mem_cons,List.mem_singleton]
      itauto)).1) flags clean
  have b := recode_y_correct retired toOdd L hw hn member u (m.drop (measurementCount body))
    scratch.1.2.1 scratch.1.2.2 scratch.2
  rw [uv] at b
  rw [run_append]
  exact ⟨b.1.trans a.1,PairFrame.update_dst L.r L.y s.basis u.basis _ R Y _ dis
    ⟨a.2.1,uv,fun q hr hy => a.2.2 q hr⟩ b.2.2 b.2.1⟩


theorem junction_recode_before (retired : Wire) (toOdd : Bool) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254)
    (body : Program) (X Y : Nat) (result : Bool→Nat) (s : State) (m : List Bool)
    (rv : regValue L.r s.basis=X) (yv : regValue L.y s.basis=Y)
    (flags : DirectPass.LiveFlags L false false false s.basis)
    (clean : DirectPass.CleanExcept (L.carry.take 254) retired s.basis)
    (bodyProof : ∀(u : State)(tape : List Bool), regValue L.r u.basis=X →
      regValue L.y u.basis=
        (if toOdd then recodeForwardWord else recodeBackwardWord) 255 (2*BiasedCircuit.jh) Y →
      DirectPass.LiveFlags L false false false u.basis →
      DirectPass.CleanExcept (L.carry.take 254) retired u.basis →
      (run body tape u).phase=u.phase ∧
        DirectPass.WordFrame L.r u.basis (result (u.basis L.sign)) (run body tape u).basis) :
    (run (recode retired toOdd L L.y++body) m s).phase=s.phase ∧
    PairFrame L.r L.y s.basis (result (s.basis L.sign))
      ((if toOdd then recodeForwardWord else recodeBackwardWord) 255 (2*BiasedCircuit.jh) Y)
      (run (recode retired toOdd L L.y++body) m s).basis := by
  have dis := junction_register_disjoint L hn
  let coder := recode retired toOdd L L.y
  let u := run coder (m.take (measurementCount coder)) s
  have a := recode_y_correct retired toOdd L hw hn member s (m.take (measurementCount coder))
    flags.2.1 flags.2.2 clean
  rw [yv] at a
  have uv : regValue L.r u.basis=X :=
    (regValue_congr _ _ _ (fun q hq => a.2.2 q (List.disjoint_left.mp dis hq))).trans rv
  have scratch := junction_scratch_preserved retired L s u (by
    intro q hq
    exact a.2.2 q (DirectPass.work_outside L hn q (by
      simp only [List.mem_append,List.mem_cons,List.mem_singleton] at hq
      simp only [work,List.mem_append,List.mem_cons,List.mem_singleton]
      itauto)).2.1) flags clean
  have b := bodyProof u (m.drop (measurementCount coder)) uv a.2.1 scratch.1 scratch.2
  have signAway : L.sign∉L.y := fun h => BalancedCircuit.flagAway L hn L.sign (by simp) (by simp [h])
  have sg : u.basis L.sign=s.basis L.sign := a.2.2 _ signAway
  rw [sg] at b
  rw [run_append]
  exact ⟨b.1.trans a.1,PairFrame.update_temp L.r L.y s.basis u.basis _ X _ _ dis
    ⟨uv,a.2.1,fun q hr hy => a.2.2 q hy⟩ b.2.2 b.2.1⟩

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionFrames =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem dstart_frame (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1)
    (origin : BasisState) (clean : Q6EndpointCell.Clean w origin) (X Y : Fp) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y
      origin (centerWord X) (centerWord Y)) (dstart retired w sign)
      (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (oddWord ((X+(if origin sign then Y else -Y))/2)) (oddWord Y)) := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  apply DirectPass.half_frame_from_pair_kernel retired w sign hn origin clean (centerWord X) (centerWord Y)
    (fun B => oddWord ((X+(if B then Y else -Y))/2)) (oddWord Y) (dstart retired w sign)
    ((junctionStdHead retired L++emitOdd retired L)++recode retired true L L.y)
    (by simp only [dstart,L,List.append_assoc])
  intro s m rv yv flags carry
  have h := junction_recode_after retired true L hw hn (List.mem_of_mem_drop member)
    (junctionStdHead retired L++emitOdd retired L)
    (oddWord ((X+(if !s.basis L.sign then Y else -Y))/2)) (centerWord Y) s m yv flags carry
    (fun tape => junction_fso_frame retired L hw hn member X Y s tape rv yv flags carry)
  simpa only [if_true,←recode_odd_word,oddWord] using h


theorem dend_frame (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1)
    (origin : BasisState) (clean : Q6EndpointCell.Clean w origin) (X Y : Fp) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y
      origin (oddWord X) (oddWord Y)) (dend retired w sign)
      (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (centerWord ((X+(if origin sign then Y else -Y))/2)) (centerWord Y)) := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  apply DirectPass.half_frame_from_pair_kernel retired w sign hn origin clean (oddWord X) (oddWord Y)
    (fun B => centerWord ((X+(if B then Y else -Y))/2)) (centerWord Y) (dend retired w sign)
    ((junctionOddHead retired L++emitStandard retired L)++recode retired false L L.y)
    (by simp only [dend,L,List.append_assoc])
  intro s m rv yv flags carry
  have h := junction_recode_after retired false L hw hn (List.mem_of_mem_drop member)
    (junctionOddHead retired L++emitStandard retired L)
    (centerWord ((X+(if !s.basis L.sign then Y else -Y))/2)) (oddWord Y) s m yv flags carry
    (fun tape => junction_fos_frame retired L hw hn member X Y s tape rv yv flags carry)
  simpa only [Bool.false_eq_true,if_false,←recode_center_word] using h


theorem mend_frame (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1)
    (origin : BasisState) (clean : Q6EndpointCell.Clean w origin) (X Y : Fp) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y
      origin (oddWord X) (oddWord Y)) (mend retired w sign)
      (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (centerWord (2*X+(if origin sign then -Y else Y))) (centerWord Y)) := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  apply DirectPass.half_frame_from_pair_kernel retired w sign hn origin clean (oddWord X) (oddWord Y)
    (fun B => centerWord (2*X+(if B then -Y else Y))) (centerWord Y) (mend retired w sign)
    (recode retired false L L.y++(acceptOdd retired L++junctionStdRest retired L))
    (by simp only [mend,L,List.append_assoc])
  intro s m rv yv flags carry
  have h := junction_recode_before retired false L hw hn (List.mem_of_mem_drop member)
    (acceptOdd retired L++junctionStdRest retired L) (oddWord X) (oddWord Y)
    (fun B => centerWord (2*X+(if !B then -Y else Y))) s m rv yv flags carry (by
      intro u tape ur uy uf uc
      have uy' : regValue L.y u.basis=centerWord Y := by
        simpa only [Bool.false_eq_true,if_false,←recode_center_word] using uy
      exact junction_gso_frame retired L hw hn member X Y u tape ur uy' uf uc)
  simpa only [Bool.false_eq_true,if_false,←recode_center_word] using h

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.dstart_frame
#print axioms ECDSAAdd.Entrant.P1Life.dend_frame
#print axioms ECDSAAdd.Entrant.P1Life.mend_frame
end -- ticket 8 pasted module

-- ===== P1CountCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem p1_head_counts (a b cin c : Wire) :
    toffoliCount (majority a b cin c)=1 ∧ measurementCount (majority a b cin c)=0 ∧
    toffoliCount (eraseCarry a b cin c)=0 ∧ measurementCount (eraseCarry a b cin c)=1 ∧
    toffoliCount (orMajor a b c)=1 ∧ measurementCount (orMajor a b c)=0 ∧
    toffoliCount (orErase a b c)=0 ∧ measurementCount (orErase a b c)=1 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩


theorem p1_compare_chain_counts (erase : Bool) (xs ys cs : List Wire) (cin target : Wire)
    (hl : xs.length=ys.length) (hc : cs.length+1=ys.length) :
    toffoliCount (Q6LifetimeResearch.compareChain erase xs ys cs cin target)=
      cs.length+(if erase then 0 else 1) ∧
    measurementCount (Q6LifetimeResearch.compareChain erase xs ys cs cin target)=
      cs.length+(if erase then 1 else 0) := by
  induction ys generalizing xs cs cin with
  | nil => simp at hc
  | cons b bs ih =>
    cases xs with
    | nil => simp at hl
    | cons a as =>
      cases bs with
      | nil =>
        have az : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        have cz : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
        subst as cs
        cases erase <;>
          simp [Q6LifetimeResearch.compareChain,Q6LifetimeResearch.compareLeaf,majority,eraseCarry,
            toffoliCount,measurementCount]
      | cons b' bs =>
        cases as with
        | nil => simp at hl
        | cons a' as =>
          cases cs with
          | nil => simp at hc
          | cons c cs =>
            have step := ih (a'::as) cs c (by simpa using hl) (by simpa using hc)
            have head := p1_head_counts a b cin c
            simp only [Q6LifetimeResearch.compareChain,toffoliCount_append,measurementCount_append,
              step.1,step.2,head.1,head.2.1,head.2.2.1,head.2.2.2.1,List.length_cons]
            omega


theorem p1_add_top_counts (xs ys cs : List Wire) (cin : Wire)
    (hy : ys.length=xs.length) (hc : cs.length+2=xs.length) :
    toffoliCount (Q6LifetimeResearch.addTop xs ys cs cin)=cs.length ∧
    measurementCount (Q6LifetimeResearch.addTop xs ys cs cin)=cs.length+1 := by
  induction cs generalizing xs ys cin with
  | nil =>
    cases xs with
    | nil => simp at hc
    | cons a xs =>
      cases xs with
      | nil => simp at hc
      | cons a' as =>
        have az : as=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hc; omega)
        subst as
        cases ys with
        | nil => simp at hy
        | cons b ys =>
          cases ys with
          | nil => simp at hy
          | cons z zs =>
            have zz : zs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hy; omega)
            subst zs
            exact ⟨rfl,rfl⟩
  | cons c cs ih =>
    cases xs with
    | nil => simp at hc
    | cons a xs =>
      cases xs with
      | nil => simp at hc
      | cons a' as =>
        cases as with
        | nil => simp at hc
        | cons a'' as =>
          cases ys with
          | nil => simp at hy
          | cons b ys =>
            cases ys with
            | nil => simp at hy
            | cons b' bs =>
              cases bs with
              | nil => simp at hy
              | cons b'' bs =>
                have step := ih (a'::a''::as) (b'::b''::bs) c (by simpa using hy) (by simpa using hc)
                have head := p1_head_counts a b cin c
                simp only [Q6LifetimeResearch.addTop,toffoliCount_append,measurementCount_append,
                  step.1,step.2,head.1,head.2.1,head.2.2.1,head.2.2.2.1,
                  toffoliCount,measurementCount,List.length_cons]
                omega

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1PassCounts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem p1_active_length (L : Layout) (hw : L.Widths) :
    ((Q6Structural.q6Carry L).take 255).length=255 := by
  simp [Q6Structural.q6Carry,List.length_take,hw.2.2]


theorem p1_short_counts (L : Layout) (hw : L.Widths) (k : Nat) :
    toffoliCount (shortConstAdd L k)=251 ∧ measurementCount (shortConstAdd L k)=251 := by
  have lowlen : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have h := literalConstAdd_counts (L.low.drop 3) (L.carry.take 251) (L.low.getD 2 0) L.one (k/8)
    (by simp [List.length_take,List.length_drop,hw.2.2,lowlen])
  simpa [shortConstAdd,List.length_drop,lowlen,toffoliCount,measurementCount] using h


theorem junction_fold_counts (oddMode sub : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) :
    let cell := if oddMode then (if sub then unfoldStep retired L else fold retired L)
      else (if sub then Q6LifetimeResearch.unfoldStep retired L else Q6LifetimeResearch.fold retired L)
    toffoliCount cell=255 ∧ measurementCount cell=255 := by
  have lowlen : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have bits : (ShortBiasedFold.lowBits L).length=L.low.length := by
    rw [ShortBiasedFold.lowBits_length,lowlen]
  have carry : (L.carry.take 254).length+1=L.low.length := by simp [List.length_take,hw.2.2,lowlen]
  have a := mappedAdd_counts (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one bits carry
  have b := mappedSub_counts (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one bits carry
  rw [lowlen] at a b
  cases oddMode <;> cases sub <;>
    simp only [fold,unfoldStep,Q6LifetimeResearch.fold,Q6LifetimeResearch.unfoldStep,Bool.false_eq_true,if_false,if_true,Q6LifetimeResearch.move,
      toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
      a.1,a.2,b.1,b.2,toffoliCount,measurementCount] <;> exact ⟨True.intro,True.intro⟩


theorem junction_raw_add_counts (oddMode : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (if oddMode then rawAdd retired L else Q6LifetimeResearch.rawAdd retired L)=256 ∧ measurementCount (if oddMode then rawAdd retired L else Q6LifetimeResearch.rawAdd retired L)=255 := by
  have lowlen : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have clen := p1_active_length L hw
  have h := CoherentTail.addPrefix_counts (L.ylow.drop 1) (L.low.drop 1)
    (((Q6Structural.q6Carry L).take 255).drop 1) L.ymsb L.rmsb L.one
    (((Q6Structural.q6Carry L).take 255).getD 0 0)
    (by simp [List.length_drop,lowlen,hw.2.1]) (by simp [List.length_drop,clen,hw.2.1])
  simp only [List.length_drop,hw.2.1] at h
  cases oddMode
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true,rawAdd,Q6LifetimeResearch.rawAdd,toffoliCount_append,measurementCount_append,Q6LifetimeResearch.move,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,h.1,h.2,
    (signComplement_counts L.sign L.y).1,(signComplement_counts L.sign L.y).2,
    toffoliCount_reverse,measurementCount_reverse,orMajor,orErase,majority,eraseCarry,toffoliCount,measurementCount]
    exact ⟨True.intro,True.intro⟩


theorem junction_compare_counts (exchange erase : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (if exchange then compare retired erase L else Q6LifetimeResearch.compare retired erase L)=(if erase then 255 else 256) ∧
    measurementCount (if exchange then compare retired erase L else Q6LifetimeResearch.compare retired erase L)=(if erase then 256 else 255) := by
  have width := BalancedCleanup.widths L.toLayout hw
  let A := if exchange then L.r else L.y
  let B := if exchange then L.y else L.r
  have alen : A.length=256 := by cases exchange <;> simp [A,width.2.1,width.2.2.1]
  have blen : B.length=256 := by cases exchange <;> simp [B,width.2.1,width.2.2.1]
  have clen := p1_active_length L hw
  have h := p1_compare_chain_counts erase (A.drop 1) (B.drop 1)
    (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity
    (by simp [List.length_drop,alen,blen])
    (by simp [List.length_drop,clen,blen])
  simp only [List.length_drop,clen] at h
  cases exchange
  all_goals
    dsimp only [A,B] at h
    simp only [Bool.false_eq_true,if_false,if_true] at h
    simp only [compare,Q6LifetimeResearch.compare,Bool.false_eq_true,if_false,if_true,toffoliCount_append,measurementCount_append,Q6LifetimeResearch.move,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,h.1,h.2,
    (notRegister_counts (L.one::L.y)).1,(notRegister_counts (L.one::L.y)).2,
    (notRegister_counts (L.one::L.r)).1,(notRegister_counts (L.one::L.r)).2,
    majority,eraseCarry,toffoliCount,measurementCount]
    cases erase <;> norm_num


theorem junction_raw_sub_counts (oddMode : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (if oddMode then rawSub retired L else Q6LifetimeResearch.rawSubTail retired L)=255 ∧ measurementCount (if oddMode then rawSub retired L else Q6LifetimeResearch.rawSubTail retired L)=256 := by
  have width := BalancedCleanup.widths L.toLayout hw
  have clen := p1_active_length L hw
  have slen : (GuardCompression.source L).length=257 := by
    simp [GuardCompression.source,BalancedCleanup.Layout.y,hw.2.1]
  have tlen : (rawTarget L).length=257 := by simp [rawTarget,width.2.1]
  have h := p1_add_top_counts ((GuardCompression.source L).drop 1) ((rawTarget L).drop 1)
    (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0)
    (by simp [List.length_drop,slen,tlen]) (by simp [List.length_drop,slen,clen])
  simp only [List.length_drop,clen] at h
  cases oddMode
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true,rawSub,Q6LifetimeResearch.rawSubTail,toffoliCount_append,measurementCount_append,Q6LifetimeResearch.move,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,h.1,h.2,
    (signComplement_counts L.sign L.y).1,(signComplement_counts L.sign L.y).2,
    (notRegister_counts (rawTarget L)).1,(notRegister_counts (rawTarget L)).2,
    orMajor,orErase,majority,eraseCarry,toffoliCount,measurementCount]
    exact ⟨True.intro,True.intro⟩


theorem p1_fold_counts (sub : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) :
    let cell := if sub then unfoldStep retired L else fold retired L
    toffoliCount cell=255 ∧ measurementCount cell=255 :=
  junction_fold_counts true sub retired L hw


theorem p1_raw_add_counts (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (rawAdd retired L)=256 ∧ measurementCount (rawAdd retired L)=255 :=
  junction_raw_add_counts true retired L hw


theorem p1_compare_counts (erase : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (compare retired erase L)=(if erase then 255 else 256) ∧
    measurementCount (compare retired erase L)=(if erase then 256 else 255) :=
  junction_compare_counts true erase retired L hw


theorem p1_raw_sub_counts (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (rawSub retired L)=255 ∧ measurementCount (rawSub retired L)=256 :=
  junction_raw_sub_counts true retired L hw

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Counts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem p1_sign_view_counts (L : Layout) :
    toffoliCount (BalancedCleanup.prepareSign L.toLayout)=0 ∧
    measurementCount (BalancedCleanup.prepareSign L.toLayout)=0 := by
  simp only [BalancedCleanup.prepareSign,toffoliCount_append,measurementCount_append,
    (signComplement_counts L.lower L.r).1,(signComplement_counts L.lower L.r).2,
    toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem junction_compare_view_counts (oddMode : Bool) (L : Layout) :
    toffoliCount (if oddMode then prepareCompare L else BalancedCleanup.prepareCompare L.toLayout)=0 ∧ measurementCount (if oddMode then prepareCompare L else BalancedCleanup.prepareCompare L.toLayout)=0 := by
  cases oddMode
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true,prepareCompare,BalancedCleanup.prepareCompare,toffoliCount_append,measurementCount_append,
    (rotate_counts L.r).2.2.1,(rotate_counts L.r).2.2.2,
    (signComplement_counts L.sign L.y).1,(signComplement_counts L.sign L.y).2,
    (signComplement_counts L.lower L.y).1,(signComplement_counts L.lower L.y).2,
    toffoliCount,measurementCount]
    exact ⟨True.intro,True.intro⟩


theorem p1_compare_view_counts (L : Layout) :
    toffoliCount (prepareCompare L)=0 ∧ measurementCount (prepareCompare L)=0 :=
  junction_compare_view_counts true L


theorem p1_unbias_view_counts (L : Layout) :
    toffoliCount (BiasedInverse.unbiasView L)=0 ∧ measurementCount (BiasedInverse.unbiasView L)=0 := by
  have h := p1_sign_view_counts L
  simp only [BiasedInverse.unbiasView,toffoliCount_append,measurementCount_append,
    toffoliCount_reverse,measurementCount_reverse,h.1,h.2,toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem forward_counts (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (forward retired L)=1017 ∧ measurementCount (forward retired L)=1017 := by
  have a := p1_raw_add_counts retired L hw
  have b := p1_fold_counts false retired L hw
  have c := p1_compare_counts true retired L hw
  have d := p1_short_counts L hw h.toNat
  have ps := p1_sign_view_counts L
  have pc := p1_compare_view_counts L
  have rot := rotate_counts (rawTarget L)
  simp only [Bool.false_eq_true,if_false,if_true] at b c
  simp only [forward,toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    Q6LifetimeResearch.move,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    a.1,a.2,b.1,b.2,c.1,c.2,d.1,d.2,ps.1,ps.2,pc.1,pc.2,rot.1,rot.2.1,
    p1Seed,OneReuse.newPrepare,BiasedCircuit.flipBias,exposure,toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem inverse_counts (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (inverse retired L)=1017 ∧ measurementCount (inverse retired L)=1017 := by
  have a := p1_short_counts L hw (encodeWord 255 (-h))
  have b := p1_compare_counts false retired L hw
  have c := p1_fold_counts true retired L hw
  have d := p1_raw_sub_counts retired L hw
  have ps := p1_sign_view_counts L
  have pc := p1_compare_view_counts L
  have ub := p1_unbias_view_counts L
  have rot := rotate_counts (rawTarget L)
  simp only [Bool.false_eq_true,if_false,if_true] at b c
  simp only [inverse,toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    Q6LifetimeResearch.move,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    a.1,a.2,b.1,b.2,c.1,c.2,d.1,d.2,ps.1,ps.2,pc.1,pc.2,ub.1,ub.2,rot.2.2.1,rot.2.2.2,
    exposure,toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem half_counts (retired : Wire) (divide : Bool) (w : Nat→Wire) (sign : Wire) :
    toffoliCount (half retired divide w sign)=1017 ∧ measurementCount (half retired divide w sign)=1017 := by
  have hw := Q6EndpointCell.ports_widths w sign
  have shape : half retired divide w sign=[.X sign]++(if divide then
      forward retired (Q6EndpointCell.ports w sign)
      else inverse retired (Q6EndpointCell.ports w sign))++[.X sign] := rfl
  rw [shape]
  cases divide
  · have hi := inverse_counts retired (Q6EndpointCell.ports w sign) hw
    simp only [Bool.false_eq_true,if_false,toffoliCount_append,measurementCount_append,hi.1,hi.2]
    exact ⟨rfl,rfl⟩
  · have hf := forward_counts retired (Q6EndpointCell.ports w sign) hw
    simp only [if_true,toffoliCount_append,measurementCount_append,hf.1,hf.2]
    exact ⟨rfl,rfl⟩

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.half_counts
end -- ticket 8 pasted module

-- ===== P1JunctionCountCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem recode_counts (retired : Wire) (toOdd : Bool) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    toffoliCount (recode retired toOdd L L.y)=254 ∧
      measurementCount (recode retired toOdd L L.y)=254 := by
  have bl : (junctionXorBits L.ylow.length (2*BiasedCircuit.jh) L.ymsb).length=L.ylow.length :=
    by simp [junctionXorBits]
  have cl : (recodeBank retired L).length+1=L.ylow.length := by
    rw [recode_bank_length retired L hw hn member,hw.2.1]
  have a := mappedAdd_counts (junctionXorBits L.ylow.length (2*BiasedCircuit.jh) L.ymsb)
    L.ylow (recodeBank retired L) L.lower bl cl
  have b := mappedSub_counts (junctionXorBits L.ylow.length (2*BiasedCircuit.jh) L.ymsb)
    L.ylow (recodeBank retired L) L.lower bl cl
  rw [hw.2.1] at a b
  rw [recode_y_shape retired toOdd L hw,hw.2.1]
  cases toOdd <;> simp only [Bool.false_eq_true,if_false,if_true,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,toffoliCount,measurementCount] <;>
    exact ⟨True.intro,True.intro⟩


theorem junction_heads_counts (oddMode : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) :
    let p := if oddMode then junctionOddHead retired L else junctionStdHead retired L
    toffoliCount p=766 ∧ measurementCount p=766 := by
  have a := junction_raw_add_counts oddMode retired L hw
  have b := junction_fold_counts oddMode false retired L hw
  have c := junction_compare_counts oddMode true retired L hw
  have ps := p1_sign_view_counts L
  have pc := junction_compare_view_counts oddMode L
  have rot := rotate_counts (rawTarget L)
  cases oddMode
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true] at a b c pc ⊢
    simp only [junctionOddHead,junctionStdHead,toffoliCount_append,measurementCount_append,
      toffoliCount_reverse,measurementCount_reverse,a.1,a.2,b.1,b.2,c.1,c.2,
      ps.1,ps.2,pc.1,pc.2,rot.1,rot.2.1,p1Seed,GuardCompression.seed,OneReuse.newPrepare,
      BiasedCircuit.flipBias,exposure,Q6StructuralCell.exposure,Q6LowerExposure.expose,toffoliCount,measurementCount]
    exact ⟨True.intro,True.intro⟩


theorem junction_emit_odd_counts (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (emitOdd retired L)=251 ∧ measurementCount (emitOdd retired L)=251 ∧
    toffoliCount (acceptOdd retired L)=251 ∧ measurementCount (acceptOdd retired L)=251 := by
  have a := p1_short_counts L hw h.toNat
  have b := p1_short_counts L hw (encodeWord 255 (-h))
  simp only [emitOdd,acceptOdd,toffoliCount_append,measurementCount_append,Q6LifetimeResearch.move,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,a.1,a.2,b.1,b.2,
    (notRegister_counts L.low).1,(notRegister_counts L.low).2,
    (signComplement_counts L.lower L.r).1,(signComplement_counts L.lower L.r).2,
    toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro,True.intro,True.intro⟩


theorem junction_emit_standard_counts (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (emitStandard retired L)=254 ∧ measurementCount (emitStandard retired L)=254 := by
  have lowlen : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have a := literalConstAdd_counts L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral
    (by simp [List.length_take,hw.2.2,lowlen])
  rw [lowlen] at a
  simp only [emitStandard,toffoliCount_append,measurementCount_append,Q6LifetimeResearch.move,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,a.1,a.2,
    (notRegister_counts L.low).1,(notRegister_counts L.low).2,
    (signComplement_counts L.lower L.r).1,(signComplement_counts L.lower L.r).2,
    toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem junction_standard_rest_counts (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (junctionStdRest retired L)=766 ∧ measurementCount (junctionStdRest retired L)=766 := by
  have a := junction_compare_counts false false retired L hw
  have b := junction_fold_counts false true retired L hw
  have c := junction_raw_sub_counts false retired L hw
  have pc := junction_compare_view_counts false L
  have ub := p1_unbias_view_counts L
  have rot := rotate_counts (rawTarget L)
  simp only [Bool.false_eq_true,if_false,if_true] at a b c pc
  simp only [junctionStdRest,toffoliCount_append,measurementCount_append,toffoliCount_reverse,
    measurementCount_reverse,a.1,a.2,b.1,b.2,c.1,c.2,pc.1,pc.2,ub.1,ub.2,
    rot.2.2.1,rot.2.2.2,Q6StructuralCell.exposure,Q6LowerExposure.expose,toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionCounts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_divide_counts (oddIn : Bool) (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈(Q6EndpointCell.ports w sign).carry.take 254) :
    let p := if oddIn then dend retired w sign else dstart retired w sign
    toffoliCount p=(if oddIn then 1274 else 1271) ∧
      measurementCount p=(if oddIn then 1274 else 1271) := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have a := junction_heads_counts oddIn retired L hw
  have b := junction_emit_odd_counts retired L hw
  have c := junction_emit_standard_counts retired L hw
  have d := recode_counts retired (!oddIn) L hw hn member
  dsimp only [L] at a b c d
  cases oddIn
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true,Bool.not_false,Bool.not_true] at a d ⊢
    simp only [dstart,dend]
    change toffoliCount _=_ ∧ measurementCount _=_
    simp only [toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2.1,c.1,c.2,d.1,d.2,
      toffoliCount,measurementCount]
    exact ⟨True.intro,True.intro⟩


theorem dstart_counts (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈(Q6EndpointCell.ports w sign).carry.take 254) :
    toffoliCount (dstart retired w sign)=1271 ∧ measurementCount (dstart retired w sign)=1271 :=
  junction_divide_counts false retired w sign hn member


theorem dend_counts (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈(Q6EndpointCell.ports w sign).carry.take 254) :
    toffoliCount (dend retired w sign)=1274 ∧ measurementCount (dend retired w sign)=1274 :=
  junction_divide_counts true retired w sign hn member


theorem mend_counts (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈(Q6EndpointCell.ports w sign).carry.take 254) :
    toffoliCount (mend retired w sign)=1271 ∧ measurementCount (mend retired w sign)=1271 := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have a := recode_counts retired false L hw hn member
  have b := junction_emit_odd_counts retired L hw
  have c := junction_standard_rest_counts retired L hw
  dsimp only [L] at a b c
  simp only [mend,toffoliCount_append,measurementCount_append,a.1,a.2,b.2.2.1,b.2.2.2,c.1,c.2,
    toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem centerOdd_counts (L : BalancedConvert.Layout) (hw : L.Widths) :
    toffoliCount (centerOdd L)=251 ∧ measurementCount (centerOdd L)=251 := by
  have a := mappedAdd_counts (centerOddBits L) (L.low.drop 3) ((L.carry.take 254).drop 3) L.cin
    (by simp [centerOddBits,hw.1]) (by simp [List.length_take,hw.1,hw.2])
  rw [List.length_drop,hw.1] at a
  have rot := rotate_counts L.word
  simp only [centerOdd,toffoliCount_append,measurementCount_append,a.1,a.2,rot.1,rot.2.1,
    toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.dstart_counts
#print axioms ECDSAAdd.Entrant.P1Life.dend_counts
#print axioms ECDSAAdd.Entrant.P1Life.mend_counts
#print axioms ECDSAAdd.Entrant.P1Life.centerOdd_counts
end -- ticket 8 pasted module

-- ===== P1ResourceCoherent =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_nodup_mono (xs ys : List Wire) (nd : xs.Nodup)
    (le : ∀q,ys.count q≤xs.count q) : ys.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp nd q
  have k := le q
  omega


theorem junction_majority_support (a b cin target : Wire) :
    wires (majority a b cin target)={a,b,cin,target} := by
  ext q
  simp [majority,wires,Instr.wires]
  itauto


theorem junction_erase_support (a b cin target : Wire) :
    wires (eraseCarry a b cin target)⊆{a,b,cin,target} := by
  intro q hq
  simpa [eraseCarry,wires,Instr.wires,correctionWires,Finset.mem_insert,Finset.mem_singleton,or_assoc,or_left_comm,or_comm] using hq


theorem junction_coherent_leaf_physical (a t z cin : Wire) (nd : [a,t,z,cin].Nodup) :
    GatePhysical (CoherentTail.program a t cin z) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd
  simp_all [CoherentTail.program,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ne_comm]


theorem junction_coherent_physical (xs ys cs : List Wire) (a t z cin : Wire)
    (hy : ys.length=xs.length) (hc : cs.length=xs.length)
    (nd : (a::t::z::cin::(xs++ys++cs)).Nodup) :
    GatePhysical (CoherentTail.addPrefix xs ys cs a t z cin) := by
  induction xs generalizing ys cs cin with
  | nil =>
    have ye : ys=[] := List.eq_nil_of_length_eq_zero hy
    have ce : cs=[] := List.eq_nil_of_length_eq_zero hc
    subst ys cs
    exact junction_coherent_leaf_physical a t z cin nd
  | cons x xs ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have headND : [x,y,cin,c].Nodup := by
          apply junction_nodup_mono _ _ nd
          intro q
          simp only [List.count_cons,List.count_append,List.count_nil]
          omega
        have tailND : (a::t::z::c::(xs++ys++cs)).Nodup := by
          apply junction_nodup_mono _ _ nd
          intro q
          simp only [List.count_cons,List.count_append,List.count_nil]
          omega
        have step := ih ys cs c (by simpa using hy) (by simpa using hc) tailND
        have finish : GatePhysical [.CX x y,.CX cin y] := by
          simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
            not_false_eq_true,and_true] at headND
          simp_all [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ne_comm]
        simpa only [CoherentTail.addPrefix,gatePhysical_append] using
          And.intro (And.intro (And.intro (majority_physical _ _ _ _ headND) step)
            (eraseCarry_physical x y cin c)) finish


theorem junction_coherent_support (xs ys cs : List Wire) (a t z cin : Wire)
    (hy : ys.length=xs.length) (hc : cs.length=xs.length) :
    wires (CoherentTail.addPrefix xs ys cs a t z cin)⊆(a::t::z::cin::(xs++ys++cs)).toFinset := by
  induction xs generalizing ys cs cin with
  | nil =>
    have ye : ys=[] := List.eq_nil_of_length_eq_zero hy
    have ce : cs=[] := List.eq_nil_of_length_eq_zero hc
    subst ys cs
    intro q hq
    simpa [CoherentTail.addPrefix,CoherentTail.program,wires,Instr.wires,or_assoc,or_left_comm,or_comm] using hq
  | cons x xs ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have step := ih ys cs c (by simpa using hy) (by simpa using hc)
        intro q used
        simp only [CoherentTail.addPrefix,wires_append,Finset.mem_union] at used
        simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
        rcases used with ((h|h)|h)|h
        · rw [junction_majority_support] at h
          simp only [Finset.mem_insert,Finset.mem_singleton] at h
          itauto
        · have h := step h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h
          itauto
        · have h := junction_erase_support x y cin c h
          simp only [Finset.mem_insert,Finset.mem_singleton] at h
          itauto
        · have h : q=cin ∨ q=y ∨ q=x := by
            simpa [wires,Instr.wires,or_assoc,or_left_comm,or_comm] using h
          itauto

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceTop =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_add_top_step (a a' b b' c cin : Wire) (xs ys cs : List Wire)
    (notLast : ¬(xs=[] ∧ ys=[])) :
    Q6LifetimeResearch.addTop (a::a'::xs) (b::b'::ys) (c::cs) cin=
      majority a b cin c++Q6LifetimeResearch.addTop (a'::xs) (b'::ys) cs c++
        eraseCarry a b cin c++[.CX a b,.CX cin b] := by
  cases xs <;> cases ys <;> first | rfl | exact (notLast ⟨rfl,rfl⟩).elim


theorem junction_add_top_support (xs ys cs : List Wire) (cin : Wire) :
    wires (Q6LifetimeResearch.addTop xs ys cs cin)⊆(cin::(xs++ys++cs)).toFinset := by
  induction xs generalizing ys cs cin with
  | nil => simp [Q6LifetimeResearch.addTop,wires]
  | cons a xs ih =>
    cases xs with
    | nil => cases ys <;> simp [Q6LifetimeResearch.addTop,wires]
    | cons a' xs =>
      cases ys with
      | nil => simp [Q6LifetimeResearch.addTop,wires]
      | cons b ys =>
        cases ys with
        | nil => simp [Q6LifetimeResearch.addTop,wires]
        | cons b' ys =>
          by_cases last : xs=[] ∧ ys=[]
          · rcases last with ⟨rfl,rfl⟩
            intro q used
            simp [Q6LifetimeResearch.addTop,Q6LifetimeResearch.dependentTop,wires,Instr.wires,correctionWires] at used ⊢
            itauto
          · cases cs with
            | nil => cases xs <;> cases ys <;> simp_all [Q6LifetimeResearch.addTop,wires]
            | cons c cs =>
              have child := ih (b'::ys) cs c
              rw [junction_add_top_step a a' b b' c cin xs ys cs last]
              intro q used
              simp only [wires_append,Finset.mem_union,junction_majority_support,eraseCarry_wires] at used
              rcases used with ((head|tail)|finish)|sum
              all_goals
                simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
              · simp only [Finset.mem_insert,Finset.mem_singleton] at head; itauto
              · have h := child tail
                simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
                itauto
              · simp only [Finset.mem_insert,Finset.mem_singleton] at finish; itauto
              · simp [wires,Instr.wires] at sum; itauto


theorem junction_add_top_physical (xs ys cs : List Wire) (cin : Wire)
    (nd : (cin::(ys++cs)).Nodup) (apart : List.Disjoint xs (cin::(ys++cs))) :
    GatePhysical (Q6LifetimeResearch.addTop xs ys cs cin) := by
  induction xs generalizing ys cs cin with
  | nil => simp [Q6LifetimeResearch.addTop,GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil => cases ys <;> simp [Q6LifetimeResearch.addTop,GatePhysical]
    | cons a' xs =>
      cases ys with
      | nil => simp [Q6LifetimeResearch.addTop,GatePhysical]
      | cons b ys =>
        cases ys with
        | nil => simp [Q6LifetimeResearch.addTop,GatePhysical]
        | cons b' ys =>
          have ab : a≠b := fun e => List.disjoint_left.mp apart List.mem_cons_self (by simp [e])
          have cb : cin≠b := by
            intro e
            have h := (List.nodup_cons.mp nd).1
            exact h (by simp [e])
          by_cases last : xs=[] ∧ ys=[]
          · rcases last with ⟨rfl,rfl⟩
            have bb : b≠b' := by
              have h := (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
              intro e; exact h (by simp [e])
            simp [Q6LifetimeResearch.addTop,Q6LifetimeResearch.dependentTop,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ab,cb,bb]
          · cases cs with
            | nil =>
              cases xs <;> cases ys <;> simp_all [Q6LifetimeResearch.addTop,GatePhysical]
            | cons c cs =>
              have localND : [a,b,cin,c].Nodup := by
                have small : [b,cin,c].Nodup := by
                  apply List.nodup_iff_count.mpr
                  intro q
                  have h := List.nodup_iff_count.mp nd q
                  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
                  omega
                have off : a∉[b,cin,c] := by
                  intro h
                  apply List.disjoint_left.mp apart List.mem_cons_self
                  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h ⊢
                  tauto
                exact List.nodup_cons.mpr ⟨off,small⟩
              have tailND : (c::((b'::ys)++cs)).Nodup := by
                apply List.nodup_iff_count.mpr
                intro q
                have h := List.nodup_iff_count.mp nd q
                simp only [List.count_cons,List.count_append] at h ⊢
                omega
              have tailApart : List.Disjoint (a'::xs) (c::((b'::ys)++cs)) := by
                apply List.disjoint_left.mpr
                intro q hq h
                apply List.disjoint_left.mp apart (List.mem_cons_of_mem _ hq)
                simp only [List.mem_cons,List.mem_append] at h ⊢
                tauto
              rw [junction_add_top_step a a' b b' c cin xs ys cs last]
              simp only [gatePhysical_append]
              exact ⟨⟨⟨majority_physical _ _ _ _ localND,ih (b'::ys) cs c tailND tailApart⟩,
                eraseCarry_physical _ _ _ _⟩,by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ab,cb]⟩


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceCompare =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_compare_chain_support (forward : Bool) (xs ys cs : List Wire)
    (cin target : Wire) :
    wires (Q6LifetimeResearch.compareChain forward xs ys cs cin target)⊆
      (target::cin::(xs++ys++cs)).toFinset := by
  induction xs generalizing ys cs cin with
  | nil => cases ys <;> simp [Q6LifetimeResearch.compareChain,wires]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp [Q6LifetimeResearch.compareChain,wires]
      | cons b ys =>
        cases ys with
        | cons b' ys => simp [Q6LifetimeResearch.compareChain,wires]
        | nil =>
          cases forward <;> intro q used <;>
            simp [Q6LifetimeResearch.compareChain,Q6LifetimeResearch.compareLeaf,wires_append,junction_majority_support,
              eraseCarry_wires,wires,Instr.wires] at used ⊢ <;> itauto
    | cons a' xs =>
      cases ys with
      | nil => simp [Q6LifetimeResearch.compareChain,wires]
      | cons b ys =>
        cases ys with
        | nil => simp [Q6LifetimeResearch.compareChain,wires]
        | cons b' ys =>
          cases cs with
          | nil => simp [Q6LifetimeResearch.compareChain,wires]
          | cons c cs =>
            have child := ih (b'::ys) cs c
            intro q used
            simp only [Q6LifetimeResearch.compareChain,wires_append,Finset.mem_union,
              junction_majority_support,eraseCarry_wires] at used
            simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
            rcases used with (head|tail)|finish
            · simp only [Finset.mem_insert,Finset.mem_singleton] at head
              itauto
            · have h := child tail
              simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
              itauto
            · simp only [Finset.mem_insert,Finset.mem_singleton] at finish
              itauto


theorem junction_compare_chain_physical (forward : Bool) (xs ys cs : List Wire)
    (cin target : Wire) (nd : (target::cin::(xs++ys++cs)).Nodup) :
    GatePhysical (Q6LifetimeResearch.compareChain forward xs ys cs cin target) := by
  induction xs generalizing ys cs cin with
  | nil => cases ys <;> simp [Q6LifetimeResearch.compareChain,GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp [Q6LifetimeResearch.compareChain,GatePhysical]
      | cons b ys =>
        cases ys with
        | cons b' ys => simp [Q6LifetimeResearch.compareChain,GatePhysical]
        | nil =>
          have localND : [a,b,cin,target].Nodup := by
            apply List.nodup_iff_count.mpr
            intro q
            have h := List.nodup_iff_count.mp nd q
            simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
            omega
          cases forward
          · simpa only [Q6LifetimeResearch.compareChain,Q6LifetimeResearch.compareLeaf,Bool.false_eq_true,if_false,
              gatePhysical_append] using And.intro (majority_physical _ _ _ _ localND)
                (show GatePhysical [.X target] by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate])
          · simpa only [Q6LifetimeResearch.compareChain,Q6LifetimeResearch.compareLeaf,if_true,gatePhysical_append] using
              And.intro (show GatePhysical [.X target] by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate])
                (eraseCarry_physical _ _ _ _)
    | cons a' xs =>
      cases ys with
      | nil => simp [Q6LifetimeResearch.compareChain,GatePhysical]
      | cons b ys =>
        cases ys with
        | nil => simp [Q6LifetimeResearch.compareChain,GatePhysical]
        | cons b' ys =>
          cases cs with
          | nil => simp [Q6LifetimeResearch.compareChain,GatePhysical]
          | cons c cs =>
            have localND : [a,b,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := List.nodup_iff_count.mp nd q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have tailND : (target::c::((a'::xs)++(b'::ys)++cs)).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := List.nodup_iff_count.mp nd q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            simpa only [Q6LifetimeResearch.compareChain,gatePhysical_append] using
              And.intro (And.intro (majority_physical _ _ _ _ localND)
                (ih (b'::ys) cs c tailND)) (eraseCarry_physical _ _ _ _)


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceLayout =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


/-- The record's named footprint, before deleting the retired carry. -/
def junctionFootprint (L : Layout) : Finset Wire :=
  (L.sign::L.parity::L.lower::L.one::(L.r++L.y++L.carry.take 254)).toFinset


theorem junction_footprint_shape (L : Layout) (hw : L.Widths) :
    junctionFootprint L=(L.sign::L.parity::L.one::
      (L.y++L.r++(Q6Structural.q6Carry L).take 255)).toFinset := by
  rw [DirectPass.active_carry_shape L hw]
  ext q
  simp only [junctionFootprint,List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_singleton]
  tauto











theorem junction_retired_data_away (retired : Wire) (L : Layout) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) :
    retired∉[L.sign,L.parity,L.lower,L.one]++L.r++L.y := by
  intro bad
  have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) retired
  have a := List.count_pos_iff.mpr (List.mem_of_mem_take member)
  have b := List.count_pos_iff.mpr bad
  simp only [List.count_cons,List.count_append,List.count_nil] at h b
  omega


theorem junction_move_support (retired host : Wire) (P : Program) (S : Finset Wire)
    (hp : wires P⊆S) (hh : host∈S) (off : host∉wires P) :
    wires (Q6LifetimeResearch.move retired host P)⊆S.erase retired := by
  rw [Q6LifetimeResearch.move,renameProgram_support]
  rintro q used
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp used
  have ah : a≠host := fun e => off (e ▸ ha)
  apply Finset.mem_erase.mpr
  constructor
  · intro e
    have back : Equiv.swap retired host host=retired := Equiv.swap_apply_right _ _
    exact ah ((Equiv.swap retired host).injective (e.trans back.symm))
  · by_cases ar : a=retired
    · simpa only [ar,Equiv.swap_apply_left] using hh
    · simpa only [Equiv.swap_apply_of_ne_of_ne ar ah] using hp ha


theorem junction_move_physical (retired host : Wire) (P : Program) (hp : GatePhysical P) :
    GatePhysical (Q6LifetimeResearch.move retired host P) :=
  gatePhysical_rename _ (Equiv.swap retired host).injective _ hp


theorem junction_reverse_physical (P : Program) (hp : GatePhysical P) : GatePhysical P.reverse := by
  intro i hi
  exact hp i (List.mem_reverse.mp hi)


theorem junction_mapped_resources (sub : Bool) (bits : List MappedBit) (xs cs : List Wire)
    (cin : Wire) (nd : (cin::(xs++cs)).Nodup)
    (away : ∀q∈mappedWires bits,q∉cin::(xs++cs)) :
    let p := if sub then mappedSub bits xs cs cin else mappedAdd bits xs cs cin
    GatePhysical p ∧ wires p⊆(cin::(mappedWires bits++xs++cs)).toFinset := by
  have phy := mappedAdd_physical bits xs cs cin nd (by
    intro b hb q hq
    exact away q (List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩))
  have sup : wires (mappedAdd bits xs cs cin)⊆(cin::(mappedWires bits++xs++cs)).toFinset := by
    intro q hq
    have h := mappedAdd_wires_subset bits xs cs cin hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.mem_singleton] at h ⊢
    tauto
  cases sub
  · simp only [Bool.false_eq_true,if_false]
    exact ⟨phy,sup⟩
  · simp only [if_true]
    constructor
    · simpa only [mappedSub,gatePhysical_append] using
        And.intro (And.intro (notRegister_physical xs) phy) (notRegister_physical xs)
    · intro q hq
      simp only [mappedSub,wires_append,Finset.mem_union] at hq
      rcases hq with (h|h)|h
      · rw [notRegister_wires] at h
        simp only [List.mem_toFinset] at h
        simp [h]
      · exact sup h
      · rw [notRegister_wires] at h
        simp only [List.mem_toFinset] at h
        simp [h]

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceEnds =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_data_support (L : Layout) (q : Wire)
    (hq : q∈[L.sign,L.parity,L.lower,L.one]++L.r++L.y) : q∈junctionFootprint L := by
  simp only [junctionFootprint,List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_singleton,
    List.not_mem_nil,or_false] at hq ⊢
  itauto


theorem junction_data_erased (retired : Wire) (L : Layout) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) (q : Wire)
    (hq : q∈[L.sign,L.parity,L.lower,L.one]++L.r++L.y) : q∈(junctionFootprint L).erase retired := by
  refine Finset.mem_erase.mpr ⟨?_,junction_data_support L q hq⟩
  intro e
  exact junction_retired_data_away retired L hn member (e ▸ hq)


theorem recode_y_resources (retired : Wire) (toOdd : Bool) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    GatePhysical (recode retired toOdd L L.y) ∧
      wires (recode retired toOdd L L.y)⊆(junctionFootprint L).erase retired := by
  have nd := recode_y_nodup retired L hn
  have bits := junction_mapped_resources (!toOdd)
    (junctionXorBits L.ylow.length (2*BiasedCircuit.jh) L.ymsb) L.ylow (recodeBank retired L) L.lower
    (List.nodup_cons.mp nd).2 (by
      intro q hq
      rw [junction_xor_sources _ _ _ q hq]
      exact (List.nodup_cons.mp nd).1)
  have dat (q : Wire) (hq : q∈[L.lower,L.one,L.ymsb]++L.ylow) :
      q∈(junctionFootprint L).erase retired :=
    junction_data_erased retired L hn member q (by
      simp only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
      simp only [BalancedCleanup.Layout.y,List.mem_append,List.mem_cons,List.mem_singleton,
        List.not_mem_nil,or_false]
      tauto)
  have sup : (L.lower::(mappedWires (junctionXorBits L.ylow.length (2*BiasedCircuit.jh) L.ymsb)++
      L.ylow++recodeBank retired L)).toFinset⊆(junctionFootprint L).erase retired := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
    rcases hq with rfl|h|h|h
    · exact dat _ (by simp)
    · rw [junction_xor_sources _ _ _ q h]
      exact dat _ (by simp)
    · exact dat q (by simp [h])
    · simp only [recodeBank,List.mem_append,List.mem_filter,List.mem_singleton,bne_iff_ne] at h
      rcases h with h|rfl
      · exact Finset.mem_erase.mpr ⟨h.2,by simp [junctionFootprint,h.1]⟩
      · exact dat _ (by simp)
  have small : GatePhysical [.X L.ymsb] ∧ wires [.X L.ymsb]⊆(junctionFootprint L).erase retired := by
    exact ⟨by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate],by
      intro q hq
      have e : q=L.ymsb := by simpa [wires,Instr.wires] using hq
      subst q
      exact dat _ (by simp)⟩
  rw [recode_y_shape retired toOdd L hw]
  cases toOdd
  all_goals
    simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true] at bits ⊢
    exact ⟨by simp only [gatePhysical_append]; tauto,by
      rw [wires_append,Finset.union_subset_iff]
      have h := bits.2.trans sup
      tauto⟩


theorem junction_short_resources (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Nat) :
    GatePhysical (Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L k)) ∧
      wires (Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L k))⊆
        (junctionFootprint L).erase retired := by
  have len : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have split := short_word_split L.low (by omega : 3≤L.low.length)
  have nd : (L.rmsb::L.one::(L.low++L.carry.take 251)).Nodup := by
    apply junction_nodup_mono _ _ (BalancedCircuit.allND L hn)
    intro q
    have le := (List.take_sublist 251 L.carry).count_le q
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil]
    omega
  have smallND : (L.low.getD 2 0::(L.low.drop 3++L.carry.take 251)).Nodup := by
    apply junction_nodup_mono _ _ nd
    intro q
    conv_rhs => rw [←split]
    simp only [List.count_cons,List.count_append,List.count_nil]
    omega
  have phys : GatePhysical (shortConstAdd L k) := by
    rw [shortConstAdd,gatePhysical_append]
    exact ⟨literalAdd_physical _ _ _ _ _ smallND,by
      simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]⟩
  have cinmem : L.low.getD 2 0∈L.low := by
    have h : L.low.getD 2 0∈L.low.take 2++L.low.getD 2 0::L.low.drop 3 := by simp
    rwa [split] at h
  have sup : wires (shortConstAdd L k)⊆(L.one::(L.low++L.carry.take 251)).toFinset := by
    intro q hq
    simp only [shortConstAdd,wires_append,Finset.mem_union] at hq
    rcases hq with h|h
    · have h := literalConstAdd_wires (L.low.drop 3) (L.carry.take 251) (L.low.getD 2 0) L.one (k/8) h
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
      rcases h with rfl|rfl|h|h
      · simp
      · exact Or.inr (Or.inl cinmem)
      · exact Or.inr (Or.inl (List.mem_of_mem_drop h))
      · exact Or.inr (Or.inr h)
    · have e : q=L.low.getD 2 0 := by simpa [wires,Instr.wires] using h
      subst q
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
      exact Or.inr (Or.inl cinmem)
  have full : (L.one::(L.low++L.carry.take 251)).toFinset⊆junctionFootprint L := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
    rcases hq with rfl|h|h
    · simp [junctionFootprint]
    · simp [junctionFootprint,BalancedCleanup.Layout.r,h]
    · have h' : q∈L.carry.take 254 := by
        have eq : (L.carry.take 254).take 251=L.carry.take 251 := by simp [List.take_take]
        rw [←eq] at h
        exact List.mem_of_mem_take h
      simp [junctionFootprint,h']
  have off : L.rmsb∉wires (shortConstAdd L k) := fun h =>
    (List.nodup_cons.mp nd).1 (by simpa using sup h)
  exact ⟨junction_move_physical _ _ _ phys,junction_move_support _ _ _ _ (sup.trans full)
    (by simp [junctionFootprint,BalancedCleanup.Layout.r]) off⟩

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceActive =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_head_split (xs : List Wire) (pos : 0<xs.length) :
    xs=xs.getD 0 0::xs.drop 1 := by
  cases xs with
  | nil => simp at pos
  | cons a xs => rfl


theorem junction_active_nodup (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.sign::L.parity::L.one::(L.r++L.y++(Q6Structural.q6Carry L).take 255)).Nodup := by
  apply junction_nodup_mono _ _ (BalancedCircuit.allND L hn)
  intro q
  rw [DirectPass.active_carry_shape L hw]
  have le := (List.take_sublist 254 L.carry).count_le q
  simp only [List.count_cons,List.count_append,List.count_nil]
  omega


theorem junction_low_layout_nodup (L : Layout) (hn : L.wires.Nodup) :
    (L.rmsb::L.one::L.lower::(L.low++L.carry.take 254)).Nodup := by
  apply junction_nodup_mono _ _ (BalancedCircuit.allND L hn)
  intro q
  have le := (List.take_sublist 254 L.carry).count_le q
  simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil]
  omega


theorem junction_fold_body_resources (sub : Bool) (retired : Wire) (L : Layout)
    (hn : L.wires.Nodup) :
    let p := if sub then mappedSub (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one
      else mappedAdd (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one
    GatePhysical (Q6LifetimeResearch.move retired L.rmsb p) ∧
      wires (Q6LifetimeResearch.move retired L.rmsb p)⊆(junctionFootprint L).erase retired := by
  have nd := junction_low_layout_nodup L hn
  have mnd : (L.one::(L.low++L.carry.take 254)).Nodup := by
    apply junction_nodup_mono _ _ nd
    intro q
    simp only [List.count_cons,List.count_append]
    omega
  have res := junction_mapped_resources sub (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one
    mnd (by
      intro q hq bad
      rw [DirectPass.lowBits_sources L q hq] at bad
      have count := List.nodup_iff_count.mp nd L.lower
      have mem := List.count_pos_iff.mpr bad
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at count mem
      omega)
  have env : (L.one::(mappedWires (ShortBiasedFold.lowBits L)++L.low++L.carry.take 254)).toFinset⊆
      junctionFootprint L := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
    rcases hq with rfl|h|h|h
    · simp [junctionFootprint]
    · rw [DirectPass.lowBits_sources L q h]
      simp [junctionFootprint]
    · simp [junctionFootprint,BalancedCleanup.Layout.r,h]
    · simp [junctionFootprint,h]
  have off : L.rmsb∉(L.one::(mappedWires (ShortBiasedFold.lowBits L)++L.low++L.carry.take 254)).toFinset := by
    intro hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
    have away := (List.nodup_cons.mp nd).1
    rcases hq with h|h|h|h
    · exact away (by simp [h])
    · have eq := DirectPass.lowBits_sources L L.rmsb h
      exact away (by simp [eq])
    · exact away (by simp [h])
    · exact away (by simp [h])
  exact ⟨junction_move_physical _ _ _ res.1,
    junction_move_support _ _ _ _ (res.2.trans env)
      (by simp [junctionFootprint,BalancedCleanup.Layout.r]) (fun h => off (res.2 h))⟩


theorem junction_literal_resources (retired : Wire) (L : Layout) (hn : L.wires.Nodup) (k : Nat) :
    GatePhysical (Q6LifetimeResearch.move retired L.rmsb
      (literalConstAdd L.low (L.carry.take 254) L.lower L.one k)) ∧
    wires (Q6LifetimeResearch.move retired L.rmsb
      (literalConstAdd L.low (L.carry.take 254) L.lower L.one k))⊆(junctionFootprint L).erase retired := by
  have nd := junction_low_layout_nodup L hn
  have res := literalConstAdd_wires L.low (L.carry.take 254) L.lower L.one k
  have env : (L.one::L.lower::(L.low++L.carry.take 254)).toFinset⊆junctionFootprint L := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    simp only [junctionFootprint,BalancedCleanup.Layout.r,List.mem_toFinset,List.mem_cons,List.mem_append]
    itauto
  have off : L.rmsb∉wires (literalConstAdd L.low (L.carry.take 254) L.lower L.one k) := fun h =>
    (List.nodup_cons.mp nd).1 (by simpa using res h)
  exact ⟨junction_move_physical _ _ _ (literalAdd_physical _ _ _ _ _
      (List.nodup_cons.mp (List.nodup_cons.mp nd).2).2),
    junction_move_support _ _ _ _ (res.trans env)
      (by simp [junctionFootprint,BalancedCleanup.Layout.r]) off⟩

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceData =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_not_resources (retired : Wire) (L : Layout) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) (xs : List Wire)
    (data : ∀q∈xs,q∈[L.sign,L.parity,L.lower,L.one]++L.r++L.y) :
    GatePhysical (notRegister xs) ∧ wires (notRegister xs)⊆(junctionFootprint L).erase retired := by
  refine ⟨notRegister_physical xs,?_⟩
  rw [notRegister_wires]
  intro q hq
  exact junction_data_erased retired L hn member q (data q (List.mem_toFinset.mp hq))


theorem junction_sign_resources (retired : Wire) (L : Layout) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) (c : Wire) (xs : List Wire)
    (control : c∈[L.sign,L.parity,L.lower,L.one]++L.r++L.y)
    (data : ∀q∈xs,q∈[L.sign,L.parity,L.lower,L.one]++L.r++L.y) (away : c∉xs) :
    GatePhysical (signComplement c xs) ∧
      wires (signComplement c xs)⊆(junctionFootprint L).erase retired := by
  refine ⟨signComplement_physical c xs away,?_⟩
  intro q hq
  have h := signComplement_wires_subset c xs hq
  simp only [List.mem_toFinset,List.mem_cons] at h
  rcases h with rfl|h
  · exact junction_data_erased retired L hn member q control
  · exact junction_data_erased retired L hn member q (data q h)


theorem junction_rotate_resources (right : Bool) (retired : Wire) (L : Layout) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) (xs : List Wire) (nd : xs.Nodup)
    (data : ∀q∈xs,q∈[L.sign,L.parity,L.lower,L.one]++L.r++L.y) :
    let p := if right then rotateRight xs else rotateLeft xs
    GatePhysical p ∧ wires p⊆(junctionFootprint L).erase retired := by
  have phy := rotate_physical xs nd
  have sup := rotate_wires xs
  cases right
  · simp only [Bool.false_eq_true,if_false]
    refine ⟨phy.2,?_⟩
    intro q hq
    rw [sup.2] at hq
    split_ifs at hq with small
    · simp at hq
    · exact junction_data_erased retired L hn member q (data q (List.mem_toFinset.mp hq))
  · simp only [if_true]
    refine ⟨phy.1,?_⟩
    intro q hq
    rw [sup.1] at hq
    split_ifs at hq with small
    · simp at hq
    · exact junction_data_erased retired L hn member q (data q (List.mem_toFinset.mp hq))


theorem junction_active_support (L : Layout) (hw : L.Widths) (q : Wire)
    (hq : q∈(Q6Structural.q6Carry L).take 255) : q∈junctionFootprint L := by
  rw [junction_footprint_shape L hw]
  simp [hq]

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceSmall =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def junctionCliffordPieces (L : Layout) : List Program :=
  [GuardCompression.seed L,p1Seed L,OneReuse.newPrepare L,[.CX L.rmsb L.lower],[.X L.lower],
   [.X L.r0,.CX L.lower L.r0],[.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0],
   [.X L.rmsb,.X L.ymsb],exposure L,Q6StructuralCell.exposure L,[.CX L.parity L.r0],[.X L.sign],
   [.CX L.r0 L.parity,.CX (L.ylow.getD 0 0) L.parity,.CX L.rmsb L.one],
   [.CX L.r0 L.parity,.CX (L.ylow.getD 0 0) L.parity,.CX L.sign L.parity,.X L.parity,.CX L.rmsb L.one]]


theorem junction_small_resources (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254)
    (P : Program) (hp : P∈junctionCliffordPieces L) :
    GatePhysical P ∧ wires P⊆(junctionFootprint L).erase retired := by
  have yp := junction_head_split L.ylow (by rw [hw.2.1]; omega)
  have nd : [L.sign,L.parity,L.lower,L.one,L.rmsb,L.ymsb,L.r0,L.ylow.getD 0 0].Nodup := by
    apply junction_nodup_mono _ _ (BalancedCircuit.allND L hn)
    intro q
    conv_rhs => rw [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,yp]
    simp only [List.count_cons,List.count_append,List.count_nil]
    omega
  have yh : L.ylow.getD 0 0∈L.ylow := by
    have h : L.ylow.getD 0 0∈L.ylow.getD 0 0::L.ylow.drop 1 := by simp
    rwa [←yp] at h
  clear yp
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd
  simp only [junctionCliffordPieces,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    constructor
    · clear hn hw member yh
      simp_all [GuardCompression.seed,p1Seed,OneReuse.newPrepare,exposure,Q6StructuralCell.exposure,
        Q6LowerExposure.expose,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ne_comm]
    · intro q hq
      apply junction_data_erased retired L hn member q
      have ymem : q=L.ylow.getD 0 0 → q∈L.ylow := by intro e; simpa only [e] using yh
      simp [GuardCompression.seed,p1Seed,OneReuse.newPrepare,exposure,Q6StructuralCell.exposure,
        Q6LowerExposure.expose,wires,Instr.wires] at hq
      simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
        List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
      itauto


theorem junction_x_resources (retired : Wire) (L : Layout) (hn : L.wires.Nodup)
    (member : retired∈L.carry.take 254) (q : Wire)
    (data : q∈[L.sign,L.parity,L.lower,L.one]++L.r++L.y) :
    GatePhysical [.X q] ∧ wires [.X q]⊆(junctionFootprint L).erase retired := by
  refine ⟨by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate],?_⟩
  intro t ht
  have eq : t=q := by simpa [wires,Instr.wires] using ht
  subst t
  exact junction_data_erased retired L hn member q data

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceViews =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def JunctionSafe (S : Finset Wire) (P : Program) : Prop := GatePhysical P ∧ wires P⊆S


theorem junction_safe_append (S : Finset Wire) (P Q : Program) :
    JunctionSafe S (P++Q) ↔ JunctionSafe S P ∧ JunctionSafe S Q := by
  simp only [JunctionSafe,gatePhysical_append,wires_append,Finset.union_subset_iff]
  itauto


theorem junction_safe_reverse (S : Finset Wire) (P : Program) (h : JunctionSafe S P) :
    JunctionSafe S P.reverse :=
  ⟨junction_reverse_physical P h.1,by rw [wires_reverse]; exact h.2⟩


theorem junction_prepare_sign_resources (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    JunctionSafe ((junctionFootprint L).erase retired) (BalancedCleanup.prepareSign L.toLayout) := by
  have a := junction_small_resources retired L hw hn member [.CX L.rmsb L.lower]
    (by simp [junctionCliffordPieces])
  have b := junction_sign_resources retired L hn member L.lower L.r
    (by simp) (by intro q hq; simp [hq]) (by
      intro h; exact BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [h]))
  rw [BalancedCleanup.prepareSign,junction_safe_append]
  exact ⟨a,b⟩


theorem junction_prepare_compare_resources (oddMode : Bool) (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    JunctionSafe ((junctionFootprint L).erase retired)
      (if oddMode then prepareCompare L else BalancedCleanup.prepareCompare L.toLayout) := by
  have rnd : L.r.Nodup := by
    apply junction_nodup_mono _ _ (BalancedCircuit.allND L hn)
    intro q
    simp only [List.count_cons,List.count_append,List.count_nil]
    omega
  have rot := junction_rotate_resources false retired L hn member L.r rnd (by intro q hq; simp [hq])
  have sg := junction_sign_resources retired L hn member L.sign L.y
    (by simp) (by intro q hq; simp [hq]) (by
      intro h; exact BalancedCircuit.flagAway L hn L.sign (by simp) (by simp [h]))
  have lo := junction_sign_resources retired L hn member L.lower L.y
    (by simp) (by intro q hq; simp [hq]) (by
      intro h; exact BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [h]))
  have top := junction_small_resources retired L hw hn member [.X L.rmsb,.X L.ymsb]
    (by simp [junctionCliffordPieces])
  let insert : Program := if oddMode then [.X L.r0,.CX L.lower L.r0]
    else [.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0]
  have ins := junction_small_resources retired L hw hn member insert (by
    cases oddMode <;> simp [insert,junctionCliffordPieces])
  cases oddMode
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true]
    simp only [prepareCompare,BalancedCleanup.prepareCompare,junction_safe_append]
    dsimp only [insert] at ins
    simp only [Bool.false_eq_true,if_false,if_true] at ins
    exact ⟨⟨⟨⟨rot,ins⟩,sg⟩,lo⟩,top⟩


theorem junction_flip_bias_resources (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    JunctionSafe ((junctionFootprint L).erase retired) (BiasedCircuit.flipBias L) := by
  apply junction_x_resources retired L hn member
  have bound : 253<L.rtail.length := by rw [hw.1]; omega
  have mem : L.rtail.getD 253 0∈L.rtail := by
    rw [List.getD_eq_getElem _ _ bound]
    exact List.getElem_mem _
  simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_append,List.mem_cons,
    List.mem_singleton,List.not_mem_nil,or_false]
  itauto


theorem junction_unbias_resources (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    JunctionSafe ((junctionFootprint L).erase retired) (BiasedInverse.unbiasView L) := by
  have prep := junction_prepare_sign_resources retired L hw hn member
  have rev := junction_safe_reverse _ _ prep
  have x := junction_x_resources retired L hn member (L.r.getD 254 0) (by
    have bound : 254<L.r.length := by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,hw.1]
    have mem : L.r.getD 254 0∈L.r := by
      rw [List.getD_eq_getElem _ _ bound]
      exact List.getElem_mem _
    simp only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
    itauto)
  rw [BiasedInverse.unbiasView,junction_safe_append]
  exact ⟨x,rev⟩


theorem junction_raw_rotate_resources (right : Bool) (retired : Wire) (L : Layout)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    JunctionSafe ((junctionFootprint L).erase retired) (if right then rotateRight (rawTarget L)
      else rotateLeft (rawTarget L)) :=
  junction_rotate_resources right retired L hn member (rawTarget L) (BalancedCircuit.rawTargetND L hn)
    (by intro q hq; simp only [rawTarget,List.mem_append,List.mem_singleton] at hq;
        simp only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]; itauto)

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceTails =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_emit_resources (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    JunctionSafe ((junctionFootprint L).erase retired) (emitOdd retired L) ∧
    JunctionSafe ((junctionFootprint L).erase retired) (acceptOdd retired L) ∧
    JunctionSafe ((junctionFootprint L).erase retired) (emitStandard retired L) := by
  have nt := junction_not_resources retired L hn member L.low (by
    intro q hq
    simp [BalancedCleanup.Layout.r,hq])
  have add := junction_short_resources retired L hw hn h.toNat
  have sub := junction_short_resources retired L hw hn (encodeWord 255 (-h))
  have lit := junction_literal_resources retired L hn BalancedCleanup.positiveLiteral
  have lower := junction_small_resources retired L hw hn member [.X L.lower]
    (by simp [junctionCliffordPieces])
  have top := junction_small_resources retired L hw hn member [.CX L.rmsb L.lower]
    (by simp [junctionCliffordPieces])
  have sc := junction_sign_resources retired L hn member L.lower L.r
    (by simp) (by intro q hq; simp [hq]) (by
      intro bad; exact BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [bad]))
  refine ⟨?_,?_,?_⟩
  · simp only [emitOdd,junction_safe_append]
    exact ⟨⟨⟨⟨nt,add⟩,lower⟩,sc⟩,top⟩
  · simp only [acceptOdd,junction_safe_append]
    exact ⟨⟨⟨⟨top,sc⟩,lower⟩,sub⟩,nt⟩
  · simp only [emitStandard,junction_safe_append]
    exact ⟨⟨⟨⟨nt,lit⟩,lower⟩,sc⟩,top⟩

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceRaw =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_raw_small (oddMode sub : Bool) (a b c sign parity : Wire)
    (nd : [a,b,c,sign,parity].Nodup) :
    let H := if oddMode then orMajor a b c else majority a b sign c
    let C := if sub then [.X b,.CX parity b] else
      if oddMode then [.CX parity b,.CX a b,.X b] else [.CX parity b,.CX a b,.CX sign b]
    let E := if oddMode then orErase a b c else eraseCarry a b sign c
    let F := if oddMode then [.CX a b,.X b] else [.CX a b,.CX sign b]
    GatePhysical (H++C++C.reverse++E++F) ∧ wires (H++C++C.reverse++E++F)⊆{a,b,c,sign,parity} := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd
  cases oddMode <;> cases sub
  all_goals
    constructor
    · simp_all [orMajor,orErase,majority,eraseCarry,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ne_comm]
    · intro q hq
      simp [orMajor,orErase,majority,eraseCarry,wires_append,wires,Instr.wires,correctionWires] at hq ⊢
      tauto


theorem junction_raw_head_nodup (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    [L.ylow.getD 0 0,L.low.getD 0 0,((Q6Structural.q6Carry L).take 255).getD 0 0,
      L.sign,L.parity].Nodup := by
  let cs := (Q6Structural.q6Carry L).take 255
  have ys := junction_head_split L.ylow (by rw [hw.2.1]; omega)
  have cslen : cs.length=255 := p1_active_length L hw
  have cp := junction_head_split cs (by rw [cslen]; omega)
  have nd := junction_active_nodup L hw hn
  change (L.sign::L.parity::L.one::(L.r++L.y++cs)).Nodup at nd
  apply junction_nodup_mono _ _ nd
  intro q
  conv_rhs => rw [BalancedCleanup.Layout.r,BalancedCleanup.Layout.y,ys,cp]
  simp only [BalancedCleanup.Layout.low,List.getD_cons_zero,List.count_cons,List.count_append,List.count_nil]
  dsimp only [cs]
  omega


theorem junction_active_head_erased (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1) :
    ((Q6Structural.q6Carry L).take 255).getD 0 0∈(junctionFootprint L).erase retired := by
  let cs := (Q6Structural.q6Carry L).take 255
  have clen : cs.length=255 := p1_active_length L hw
  have cp := junction_head_split cs (by rw [clen]; omega)
  have cmem : cs.getD 0 0∈cs := by
    have h : cs.getD 0 0∈cs.getD 0 0::cs.drop 1 := by simp
    rwa [←cp] at h
  have tail : retired∈cs.drop 1 := by
    simp only [cs,DirectPass.active_carry_shape L hw,List.drop_append,List.mem_append]
    exact Or.inl member
  have nd : cs.Nodup := by
    apply junction_nodup_mono _ _ (junction_active_nodup L hw hn)
    intro q
    simp only [List.count_cons,List.count_append,List.count_nil]
    dsimp only [cs]
    omega
  rw [cp] at nd
  refine Finset.mem_erase.mpr ⟨?_,junction_active_support L hw _ cmem⟩
  intro e
  exact (List.nodup_cons.mp nd).1 (by rw [e]; exact tail)


theorem junction_raw_leaf_envelope (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1) :
    ({L.ylow.getD 0 0,L.low.getD 0 0,((Q6Structural.q6Carry L).take 255).getD 0 0,
      L.sign,L.parity} : Finset Wire)⊆(junctionFootprint L).erase retired := by
  have yp := junction_head_split L.ylow (by rw [hw.2.1]; omega)
  have ym : L.ylow.getD 0 0∈L.ylow := by
    have h : L.ylow.getD 0 0∈L.ylow.getD 0 0::L.ylow.drop 1 := by simp
    rwa [←yp] at h
  intro q hq
  simp only [Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl
  · exact junction_data_erased retired L hn (List.mem_of_mem_drop member) _
      (by
        simp only [BalancedCleanup.Layout.y,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
        itauto)
  · exact junction_data_erased retired L hn (List.mem_of_mem_drop member) _
      (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
  · exact junction_active_head_erased retired L hw hn member
  · exact junction_data_erased retired L hn (List.mem_of_mem_drop member) _ (by simp)
  · exact junction_data_erased retired L hn (List.mem_of_mem_drop member) _ (by simp)


theorem junction_raw_add_resources (oddMode : Bool) (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1) :
    let p := if oddMode then rawAdd retired L else Q6LifetimeResearch.rawAdd retired L
    GatePhysical p ∧ wires p⊆(junctionFootprint L).erase retired := by
  let cs := (Q6Structural.q6Carry L).take 255
  let a := L.ylow.getD 0 0
  let b := L.low.getD 0 0
  let c := cs.getD 0 0
  have lowlen : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have clen : cs.length=255 := p1_active_length L hw
  have ysplit := junction_head_split L.ylow (by rw [hw.2.1]; omega)
  have csplit := junction_head_split cs (by rw [clen]; omega)
  have act := junction_active_nodup L hw hn
  change (L.sign::L.parity::L.one::(L.r++L.y++cs)).Nodup at act
  have pnd : (L.r0::L.ymsb::L.rmsb::L.one::c::(L.ylow.drop 1++L.low.drop 1++cs.drop 1)).Nodup := by
    apply junction_nodup_mono _ _ act
    intro q
    conv_rhs => rw [BalancedCleanup.Layout.r,BalancedCleanup.Layout.y,ysplit,csplit]
    simp only [c,BalancedCleanup.Layout.low,List.drop_succ_cons,List.drop_zero,
      List.count_cons,List.count_append,List.count_nil]
    omega
  have snd : [a,b,c,L.sign,L.parity].Nodup := junction_raw_head_nodup L hw hn
  let P := CoherentTail.addPrefix (L.ylow.drop 1) (L.low.drop 1) (cs.drop 1) L.ymsb L.rmsb L.one c
  have phy : GatePhysical P := junction_coherent_physical _ _ _ _ _ _ _
    (by simp [List.length_drop,lowlen,hw.2.1]) (by simp [List.length_drop,clen,hw.2.1])
    (List.nodup_cons.mp pnd).2
  have sup := junction_coherent_support (L.ylow.drop 1) (L.low.drop 1) (cs.drop 1) L.ymsb L.rmsb L.one c
    (by simp [List.length_drop,lowlen,hw.2.1]) (by simp [List.length_drop,clen,hw.2.1])
  have cmem : c∈cs := by
    have h : cs.getD 0 0∈cs.getD 0 0::cs.drop 1 := by simp
    rwa [←csplit] at h
  have env : (L.ymsb::L.rmsb::L.one::c::(L.ylow.drop 1++L.low.drop 1++cs.drop 1)).toFinset⊆
      junctionFootprint L := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
    rcases hq with rfl|rfl|rfl|rfl|h|h|h
    · simp [junctionFootprint,BalancedCleanup.Layout.y]
    · simp [junctionFootprint,BalancedCleanup.Layout.r]
    · simp [junctionFootprint]
    · exact junction_active_support L hw c cmem
    · have h := List.mem_of_mem_drop h
      simp [junctionFootprint,BalancedCleanup.Layout.y,h]
    · have h := List.mem_of_mem_drop h
      simp [junctionFootprint,BalancedCleanup.Layout.r,h]
    · exact junction_active_support L hw q (List.mem_of_mem_drop h)
  have moved : GatePhysical (Q6LifetimeResearch.move retired L.r0 P) ∧
      wires (Q6LifetimeResearch.move retired L.r0 P)⊆(junctionFootprint L).erase retired := by
    exact ⟨junction_move_physical _ _ _ phy,junction_move_support _ _ _ _ (sup.trans env)
      (by simp [junctionFootprint,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
      (fun h => (List.nodup_cons.mp pnd).1 (List.mem_toFinset.mp (sup h)))⟩
  have small := junction_raw_small oddMode false a b c L.sign L.parity snd
  have leafEnv : ({a,b,c,L.sign,L.parity} : Finset Wire)⊆(junctionFootprint L).erase retired :=
    junction_raw_leaf_envelope retired L hw hn member
  have sign := junction_sign_resources retired L hn (List.mem_of_mem_drop member) L.sign L.y
    (by simp) (by intro q hq; simp [hq]) (by
      intro bad; exact BalancedCircuit.flagAway L hn L.sign (by simp) (by simp [bad]))
  have leafSupport := small.2.trans leafEnv
  have leafPhysical := small.1
  simp only [gatePhysical_append] at leafPhysical
  simp only [wires_append,Finset.union_subset_iff] at leafSupport
  cases oddMode
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true] at leafSupport leafPhysical ⊢
    simp only [rawAdd,Q6LifetimeResearch.rawAdd,gatePhysical_append,wires_append,Finset.union_subset_iff]
    have revOdd := junction_reverse_physical [.CX L.parity b,.CX a b,.X b]
    have revStd := junction_reverse_physical [.CX L.parity b,.CX a b,.CX L.sign b]
    dsimp only [P,a,b,c,cs] at moved leafSupport leafPhysical revOdd revStd
    constructor <;> tauto

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceSub =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_raw_sub_resources (oddMode : Bool) (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1) :
    let p := if oddMode then rawSub retired L else Q6LifetimeResearch.rawSubTail retired L
    GatePhysical p ∧ wires p⊆(junctionFootprint L).erase retired := by
  let cs := (Q6Structural.q6Carry L).take 255
  let a := L.ylow.getD 0 0
  let b := L.low.getD 0 0
  let c := cs.getD 0 0
  let xs := L.ylow.drop 1++[L.ymsb,L.ymsb]
  let ys := L.rtail++[L.rmsb,L.one]
  let P := Q6LifetimeResearch.addTop xs ys (cs.drop 1) c
  have ysplit := junction_head_split L.ylow (by rw [hw.2.1]; omega)
  have clen : cs.length=255 := p1_active_length L hw
  have csplit := junction_head_split cs (by rw [clen]; omega)
  have source : GuardCompression.source L=a::xs := by
    rw [GuardCompression.source]
    change (L.ylow++[L.ymsb])++[L.ymsb]=a::xs
    conv_lhs => rw [ysplit]
    simp only [a,xs,List.cons_append,List.nil_append,List.append_assoc]
  have target : rawTarget L=b::ys := by
    simp only [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,b,ys,
      List.getD_cons_zero,List.cons_append,List.nil_append,List.append_assoc]
  have act := junction_active_nodup L hw hn
  change (L.sign::L.parity::L.one::(L.r++L.y++cs)).Nodup at act
  have pnd : (L.r0::(L.y++c::(ys++cs.drop 1))).Nodup := by
    apply junction_nodup_mono _ _ act
    intro q
    conv_rhs => rw [BalancedCleanup.Layout.r,csplit]
    simp only [ys,c,BalancedCleanup.Layout.low,List.count_cons,List.count_append,List.count_nil]
    omega
  have tailND : (c::(ys++cs.drop 1)).Nodup := by
    apply junction_nodup_mono _ _ pnd
    intro q
    simp only [List.count_cons,List.count_append]
    omega
  have src (q : Wire) (hq : q∈xs) : q∈L.y := by
    simp only [xs,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
    simp only [BalancedCleanup.Layout.y,List.mem_append,List.mem_singleton]
    rcases hq with h|h|h
    · exact Or.inl (List.mem_of_mem_drop h)
    · exact Or.inr h
    · exact Or.inr h
  have apart : xs.Disjoint (c::(ys++cs.drop 1)) := by
    apply List.disjoint_left.mpr
    intro q hx hy
    exact List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp pnd).2).2.2 (src q hx) hy
  have phy : GatePhysical P := junction_add_top_physical xs ys (cs.drop 1) c tailND apart
  have sup := junction_add_top_support xs ys (cs.drop 1) c
  have coarse : (c::(xs++ys++cs.drop 1)).toFinset⊆(L.y++c::(ys++cs.drop 1)).toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq ⊢
    have sr := src q
    tauto
  have env : (L.y++c::(ys++cs.drop 1)).toFinset⊆junctionFootprint L := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
    rcases hq with h|h|h|h
    · exact junction_data_support L q (by simp [h])
    · subst q
      have h : c∈cs := by
        have h : cs.getD 0 0∈cs.getD 0 0::cs.drop 1 := by simp
        rwa [←csplit] at h
      exact junction_active_support L hw c h
    · apply junction_data_support L q
      simp only [ys,List.mem_append,List.mem_cons,List.mem_singleton] at h
      simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_append,List.mem_cons,
        List.mem_singleton,List.not_mem_nil,or_false]
      tauto
    · exact junction_active_support L hw q (List.mem_of_mem_drop h)
  have moved : GatePhysical (Q6LifetimeResearch.move retired L.r0 P) ∧
      wires (Q6LifetimeResearch.move retired L.r0 P)⊆(junctionFootprint L).erase retired := by
    exact ⟨junction_move_physical _ _ _ phy,junction_move_support _ _ _ _ (sup.trans (coarse.trans env))
      (by simp [junctionFootprint,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
      (fun h => (List.nodup_cons.mp pnd).1 (List.mem_toFinset.mp (coarse (sup h))))⟩
  have small := junction_raw_small oddMode true a b c L.sign L.parity (junction_raw_head_nodup L hw hn)
  have smallSupport := small.2.trans (junction_raw_leaf_envelope retired L hw hn member)
  have smallPhysical := small.1
  simp only [gatePhysical_append] at smallPhysical
  simp only [wires_append,Finset.union_subset_iff] at smallSupport
  let cleanup : Program := if oddMode then
    [.CX L.r0 L.parity,.CX a L.parity,.CX L.sign L.parity,.X L.parity,.CX L.rmsb L.one]
    else [.CX L.r0 L.parity,.CX a L.parity,.CX L.rmsb L.one]
  have finish := junction_small_resources retired L hw hn (List.mem_of_mem_drop member) cleanup (by
    cases oddMode <;> simp [cleanup,a,junctionCliffordPieces])
  have nt := junction_not_resources retired L hn (List.mem_of_mem_drop member) (rawTarget L)
    (by intro q hq; simp only [rawTarget,List.mem_append,List.mem_singleton] at hq; simp; tauto)
  have sc := junction_sign_resources retired L hn (List.mem_of_mem_drop member) L.sign L.y
    (by simp) (by intro q hq; simp [hq]) (by
      intro bad; exact BalancedCircuit.flagAway L hn L.sign (by simp) (by simp [bad]))
  rw [target] at nt
  cases oddMode
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true] at smallSupport smallPhysical finish ⊢
    simp only [rawSub,Q6LifetimeResearch.rawSubTail,source,target,List.getD_cons_zero,
      List.drop_succ_cons,List.drop_zero,gatePhysical_append,wires_append,Finset.union_subset_iff]
    dsimp only [P,xs,ys,a,b,c,cs,cleanup] at moved smallSupport smallPhysical finish
    simp only [Bool.false_eq_true,if_false,if_true] at finish
    clear ysplit csplit source target act pnd tailND src apart phy sup coarse env small
    constructor <;> tauto

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceComparePass =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_compare_resources (exchange erase : Bool) (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1) :
    let p := if exchange then compare retired erase L else Q6LifetimeResearch.compare retired erase L
    GatePhysical p ∧ wires p⊆(junctionFootprint L).erase retired := by
  let A := if exchange then L.r else L.y
  let B := if exchange then L.y else L.r
  let cs := (Q6Structural.q6Carry L).take 255
  let a := A.getD 0 0
  let b := B.getD 0 0
  let c := cs.getD 0 0
  have widths := BalancedCleanup.widths L.toLayout hw
  have alen : A.length=256 := by cases exchange <;> simp [A,widths.2.1,widths.2.2.1]
  have blen : B.length=256 := by cases exchange <;> simp [B,widths.2.1,widths.2.2.1]
  have clen : cs.length=255 := p1_active_length L hw
  have ap := junction_head_split A (by omega)
  have bp := junction_head_split B (by omega)
  have cp := junction_head_split cs (by omega)
  have nd : (L.one::L.parity::(A++B++cs)).Nodup := by
    apply junction_nodup_mono _ _ (junction_active_nodup L hw hn)
    intro q
    cases exchange <;> simp only [A,B,cs,Bool.false_eq_true,if_false,if_true,
      List.count_cons,List.count_append,List.count_nil] <;> omega
  have headND : [a,b,L.one,c].Nodup := by
    apply junction_nodup_mono _ _ nd
    intro q
    conv_rhs => rw [ap,bp,cp]
    simp only [a,b,c,List.count_cons,List.count_append,List.count_nil]
    omega
  have preND : (L.one::L.parity::c::(A.drop 1++B.drop 1++cs.drop 1)).Nodup := by
    apply junction_nodup_mono _ _ nd
    intro q
    conv_rhs => rw [ap,bp,cp]
    simp only [c,List.count_cons,List.count_append,List.count_nil]
    omega
  let P := Q6LifetimeResearch.compareChain erase (A.drop 1) (B.drop 1) (cs.drop 1) c L.parity
  have phy : GatePhysical P := junction_compare_chain_physical erase _ _ _ _ _ (List.nodup_cons.mp preND).2
  have sup := junction_compare_chain_support erase (A.drop 1) (B.drop 1) (cs.drop 1) c L.parity
  have adata (q : Wire) (hq : q∈A) : q∈L.r++L.y := by
    cases exchange <;> simp only [A,Bool.false_eq_true,if_false,if_true] at hq <;>
      simp only [List.mem_append] <;> tauto
  have bdata (q : Wire) (hq : q∈B) : q∈L.r++L.y := by
    cases exchange <;> simp only [B,Bool.false_eq_true,if_false,if_true] at hq <;>
      simp only [List.mem_append] <;> tauto
  have env : (L.parity::c::(A.drop 1++B.drop 1++cs.drop 1)).toFinset⊆junctionFootprint L := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
    rcases hq with rfl|rfl|h|h|h
    · simp [junctionFootprint]
    · exact (Finset.mem_erase.mp (junction_active_head_erased retired L hw hn member)).2
    · exact junction_data_support L q (by
        have h := adata q (List.mem_of_mem_drop h)
        simp only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h ⊢
        tauto)
    · exact junction_data_support L q (by
        have h := bdata q (List.mem_of_mem_drop h)
        simp only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h ⊢
        tauto)
    · exact junction_active_support L hw q (List.mem_of_mem_drop h)
  have moved : GatePhysical (Q6LifetimeResearch.move retired L.one P) ∧
      wires (Q6LifetimeResearch.move retired L.one P)⊆(junctionFootprint L).erase retired :=
    ⟨junction_move_physical _ _ _ phy,junction_move_support _ _ _ _ (sup.trans env)
      (by simp [junctionFootprint])
      (fun h => (List.nodup_cons.mp preND).1 (List.mem_toFinset.mp (sup h)))⟩
  have am : a∈A := by
    have h : a∈a::A.drop 1 := by simp
    simpa only [a,←ap] using h
  have bm : b∈B := by
    have h : b∈b::B.drop 1 := by simp
    simpa only [b,←bp] using h
  have leafenv : ({a,b,L.one,c} : Finset Wire)⊆(junctionFootprint L).erase retired := by
    intro q hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact junction_data_erased retired L hn (List.mem_of_mem_drop member) _ (by
        have h := adata a am; simp only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h ⊢; tauto)
    · exact junction_data_erased retired L hn (List.mem_of_mem_drop member) _ (by
        have h := bdata b bm; simp only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h ⊢; tauto)
    · exact junction_data_erased retired L hn (List.mem_of_mem_drop member) _ (by simp)
    · exact junction_active_head_erased retired L hw hn member
  have maj : GatePhysical (majority a b L.one c) ∧
      wires (majority a b L.one c)⊆(junctionFootprint L).erase retired := by
    refine ⟨majority_physical _ _ _ _ headND,?_⟩
    rw [junction_majority_support]
    exact leafenv
  have ers := And.intro (eraseCarry_physical a b L.one c) ((junction_erase_support a b L.one c).trans leafenv)
  have flip := junction_x_resources retired L hn (List.mem_of_mem_drop member) L.one (by simp)
  have nr := junction_not_resources retired L hn (List.mem_of_mem_drop member) (L.one::B) (by
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl|hq
    · simp
    · have h := bdata q hq
      simp only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h ⊢
      tauto)
  cases exchange
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true]
    simp only [compare,Q6LifetimeResearch.compare,gatePhysical_append,wires_append,Finset.union_subset_iff]
    dsimp only [A,B,P,a,b,c,cs] at moved maj ers flip nr
    simp only [Bool.false_eq_true,if_false,if_true] at moved maj ers flip nr
    constructor <;> tauto

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceFold =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_fold_small (oddMode sub : Bool) (p l o t : Wire) (nd : [p,l,o,t].Nodup) :
    GatePhysical (DirectPass.foldHead_mode oddMode sub p l o t) ∧
    GatePhysical (DirectPass.foldTail_mode oddMode sub p l o t) ∧
    wires (DirectPass.foldHead_mode oddMode sub p l o t)⊆{p,l,o,t} ∧
    wires (DirectPass.foldTail_mode oddMode sub p l o t)⊆{p,l,o,t} := by
  have flat := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at flat
  cases oddMode <;> cases sub
  all_goals
    refine ⟨?_,?_,?_,?_⟩
    · simp_all [DirectPass.foldHead_mode,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ne_comm]
    · simp_all [DirectPass.foldTail_mode,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ne_comm]
    · intro q hq
      simp [DirectPass.foldHead_mode,wires,Instr.wires] at hq ⊢
      itauto
    · intro q hq
      simp [DirectPass.foldTail_mode,wires,Instr.wires,correctionWires] at hq ⊢
      itauto


theorem junction_fold_resources (oddMode sub : Bool) (retired : Wire) (L : Layout)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    let p := if oddMode then (if sub then unfoldStep retired L else fold retired L)
      else (if sub then Q6LifetimeResearch.unfoldStep retired L else Q6LifetimeResearch.fold retired L)
    GatePhysical p ∧ wires p⊆(junctionFootprint L).erase retired := by
  have nd : [L.parity,L.lower,L.one,L.rmsb].Nodup := by
    apply junction_nodup_mono _ _ (BalancedCircuit.allND L hn)
    intro q
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil]
    omega
  have small := junction_fold_small oddMode sub L.parity L.lower L.one L.rmsb nd
  have body := junction_fold_body_resources sub retired L hn
  let H := DirectPass.foldHead_mode oddMode sub L.parity L.lower L.one L.rmsb
  let T := DirectPass.foldTail_mode oddMode sub L.parity L.lower L.one L.rmsb
  let B := Q6LifetimeResearch.move retired L.rmsb
    (if sub then mappedSub (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one
      else mappedAdd (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one)
  have shape : (if oddMode then (if sub then unfoldStep retired L else fold retired L)
      else (if sub then Q6LifetimeResearch.unfoldStep retired L else Q6LifetimeResearch.fold retired L))=
      H++B++T := by
    cases oddMode <;> cases sub <;>
      simp only [H,B,T,DirectPass.foldHead_mode,DirectPass.foldTail_mode,fold,unfoldStep,
        Q6LifetimeResearch.fold,Q6LifetimeResearch.unfoldStep,Bool.false_eq_true,if_false,if_true,
        List.cons_append,List.nil_append,List.append_assoc]
  have env : ({L.parity,L.lower,L.one,L.rmsb} : Finset Wire)⊆(junctionFootprint L).erase retired := by
    intro q hq
    apply junction_data_erased retired L hn member q
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    simp only [BalancedCleanup.Layout.r,List.mem_append,List.mem_cons,List.mem_singleton,
      List.not_mem_nil,or_false]
    itauto
  rw [shape]
  refine ⟨?_,?_⟩
  · rw [gatePhysical_append,gatePhysical_append]
    exact ⟨⟨small.1,body.1⟩,small.2.1⟩
  · rw [wires_append,wires_append,Finset.union_subset_iff,Finset.union_subset_iff]
    exact ⟨⟨small.2.2.1.trans env,body.2⟩,small.2.2.2.trans env⟩

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceChains =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_heads_resources (oddMode : Bool) (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1) :
    JunctionSafe ((junctionFootprint L).erase retired)
      (if oddMode then junctionOddHead retired L else junctionStdHead retired L) := by
  let S := (junctionFootprint L).erase retired
  have mt := List.mem_of_mem_drop member
  have ra : JunctionSafe S (if oddMode then rawAdd retired L else Q6LifetimeResearch.rawAdd retired L) :=
    junction_raw_add_resources oddMode retired L hw hn member
  have fo : JunctionSafe S (if oddMode then fold retired L else Q6LifetimeResearch.fold retired L) :=
    junction_fold_resources oddMode false retired L hn mt
  have co : JunctionSafe S (if oddMode then compare retired true L else Q6LifetimeResearch.compare retired true L) :=
    junction_compare_resources oddMode true retired L hw hn member
  have pc := junction_prepare_compare_resources oddMode retired L hw hn mt
  have pr := junction_safe_reverse _ _ pc
  have ps := junction_prepare_sign_resources retired L hw hn mt
  have fb := junction_flip_bias_resources retired L hw hn mt
  have rot := junction_raw_rotate_resources true retired L hn mt
  have seed := junction_small_resources retired L hw hn mt
    (if oddMode then p1Seed L else GuardCompression.seed L) (by
      cases oddMode <;> simp [junctionCliffordPieces])
  have prep := junction_small_resources retired L hw hn mt (OneReuse.newPrepare L)
    (by simp [junctionCliffordPieces])
  have ex := junction_small_resources retired L hw hn mt
    (if oddMode then exposure L else Q6StructuralCell.exposure L) (by
      cases oddMode <;> simp [junctionCliffordPieces])
  have er := junction_safe_reverse _ _ ex
  cases oddMode
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true] at ra fo co pc pr seed ex er ⊢
    simp only [junctionOddHead,junctionStdHead,junction_safe_append]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨seed,ra⟩,prep⟩,rot⟩,fo⟩,ps⟩,fb⟩,pc⟩,ex⟩,co⟩,er⟩,pr⟩


theorem junction_rest_resources (oddMode : Bool) (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1) :
    let p := if oddMode then
      prepareCompare L++exposure L++compare retired false L++(exposure L).reverse++
        (prepareCompare L).reverse++BiasedInverse.unbiasView L++unfoldStep retired L++
        rotateLeft (rawTarget L)++[.CX L.parity L.r0]++rawSub retired L
      else junctionStdRest retired L
    JunctionSafe ((junctionFootprint L).erase retired) p := by
  let S := (junctionFootprint L).erase retired
  have mt := List.mem_of_mem_drop member
  have su : JunctionSafe S (if oddMode then rawSub retired L else Q6LifetimeResearch.rawSubTail retired L) :=
    junction_raw_sub_resources oddMode retired L hw hn member
  have un : JunctionSafe S (if oddMode then unfoldStep retired L else Q6LifetimeResearch.unfoldStep retired L) :=
    junction_fold_resources oddMode true retired L hn mt
  have co : JunctionSafe S (if oddMode then compare retired false L else Q6LifetimeResearch.compare retired false L) :=
    junction_compare_resources oddMode false retired L hw hn member
  have pc := junction_prepare_compare_resources oddMode retired L hw hn mt
  have pr := junction_safe_reverse _ _ pc
  have ub := junction_unbias_resources retired L hw hn mt
  have rot := junction_raw_rotate_resources false retired L hn mt
  have ex := junction_small_resources retired L hw hn mt
    (if oddMode then exposure L else Q6StructuralCell.exposure L) (by
      cases oddMode <;> simp [junctionCliffordPieces])
  have er := junction_safe_reverse _ _ ex
  have parity := junction_small_resources retired L hw hn mt [.CX L.parity L.r0]
    (by simp [junctionCliffordPieces])
  cases oddMode
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true] at su un co pc pr ex er ⊢
    simp only [junctionStdRest,junction_safe_append]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨pc,ex⟩,co⟩,er⟩,pr⟩,ub⟩,un⟩,rot⟩,parity⟩,su⟩


theorem junction_forward_resources (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1) :
    JunctionSafe ((junctionFootprint L).erase retired) (forward retired L) := by
  have head := junction_heads_resources true retired L hw hn member
  have lit := junction_short_resources retired L hw hn h.toNat
  have view := junction_safe_reverse _ _ (junction_prepare_sign_resources retired L hw hn (List.mem_of_mem_drop member))
  have shape : forward retired L=junctionOddHead retired L++
      Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L h.toNat)++
      (BalancedCleanup.prepareSign L.toLayout).reverse := by
    simp only [forward,junctionOddHead,List.append_assoc]
  rw [shape,junction_safe_append,junction_safe_append]
  exact ⟨⟨head,lit⟩,view⟩


theorem junction_inverse_resources (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1) :
    JunctionSafe ((junctionFootprint L).erase retired) (inverse retired L) := by
  have view := junction_prepare_sign_resources retired L hw hn (List.mem_of_mem_drop member)
  have lit := junction_short_resources retired L hw hn (encodeWord 255 (-h))
  have rest := junction_rest_resources true retired L hw hn member
  have shape : inverse retired L=(BalancedCleanup.prepareSign L.toLayout++
      Q6LifetimeResearch.move retired L.rmsb (shortConstAdd L (encodeWord 255 (-h))))++
      (prepareCompare L++exposure L++compare retired false L++(exposure L).reverse++
        (prepareCompare L).reverse++BiasedInverse.unbiasView L++unfoldStep retired L++
        rotateLeft (rawTarget L)++[.CX L.parity L.r0]++rawSub retired L) := by
    simp only [inverse,List.append_assoc]
  rw [shape,junction_safe_append,junction_safe_append]
  exact ⟨⟨view,lit⟩,rest⟩

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Resources =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem half_resources (retired : Wire) (divide : Bool) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1) :
    GatePhysical (half retired divide w sign) ∧ wires (half retired divide w sign)⊆
      (junctionFootprint (Q6EndpointCell.ports w sign)).erase retired := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have flip := junction_small_resources retired L hw hn (List.mem_of_mem_drop member) [.X L.sign]
    (by simp [junctionCliffordPieces])
  have f := junction_forward_resources retired L hw hn member
  have i := junction_inverse_resources retired L hw hn member
  change JunctionSafe ((junctionFootprint L).erase retired) (half retired divide w sign)
  have shape : half retired divide w sign=[.X sign]++
      (if divide then forward retired L else inverse retired L)++[.X sign] := rfl
  rw [shape,junction_safe_append,junction_safe_append]
  refine ⟨⟨flip,?_⟩,flip⟩
  cases divide
  · exact i
  · exact f


theorem junction_divide_resources (oddIn : Bool) (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1) :
    let p := if oddIn then dend retired w sign else dstart retired w sign
    GatePhysical p ∧ wires p⊆(junctionFootprint (Q6EndpointCell.ports w sign)).erase retired := by
  let L := Q6EndpointCell.ports w sign
  let S := (junctionFootprint L).erase retired
  have hw := Q6EndpointCell.ports_widths w sign
  have mt := List.mem_of_mem_drop member
  have head := junction_heads_resources oddIn retired L hw hn member
  have tails := junction_emit_resources retired L hw hn mt
  have tail : JunctionSafe S (if oddIn then emitStandard retired L else emitOdd retired L) := by
    cases oddIn
    · exact tails.1
    · exact tails.2.2
  have recoder := recode_y_resources retired (!oddIn) L hw hn mt
  have body : JunctionSafe S
      ((if oddIn then junctionOddHead retired L else junctionStdHead retired L)++
        (if oddIn then emitStandard retired L else emitOdd retired L)++recode retired (!oddIn) L L.y) := by
    rw [junction_safe_append,junction_safe_append]
    exact ⟨⟨head,tail⟩,recoder⟩
  have flip := junction_small_resources retired L hw hn mt [.X L.sign]
    (by simp [junctionCliffordPieces])
  change JunctionSafe S (if oddIn then dend retired w sign else dstart retired w sign)
  have shape : (if oddIn then dend retired w sign else dstart retired w sign)=[.X sign]++
      ((if oddIn then junctionOddHead retired L else junctionStdHead retired L)++
        (if oddIn then emitStandard retired L else emitOdd retired L)++recode retired (!oddIn) L L.y)++
      [.X sign] := by
    cases oddIn <;> simp only [dstart,dend,L,Bool.false_eq_true,if_false,if_true,
      Bool.not_false,Bool.not_true,List.append_assoc]
  rw [shape,junction_safe_append,junction_safe_append]
  exact ⟨⟨flip,body⟩,flip⟩


theorem dstart_resources (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1) :
    GatePhysical (dstart retired w sign) ∧ wires (dstart retired w sign)⊆
      (junctionFootprint (Q6EndpointCell.ports w sign)).erase retired :=
  junction_divide_resources false retired w sign hn member


theorem dend_resources (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1) :
    GatePhysical (dend retired w sign) ∧ wires (dend retired w sign)⊆
      (junctionFootprint (Q6EndpointCell.ports w sign)).erase retired :=
  junction_divide_resources true retired w sign hn member


theorem mend_resources (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1) :
    GatePhysical (mend retired w sign) ∧ wires (mend retired w sign)⊆
      (junctionFootprint (Q6EndpointCell.ports w sign)).erase retired := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have mt := List.mem_of_mem_drop member
  have tails := junction_emit_resources retired L hw hn mt
  have recoder := recode_y_resources retired false L hw hn mt
  have rest := junction_rest_resources false retired L hw hn member
  have flip := junction_small_resources retired L hw hn mt [.X L.sign]
    (by simp [junctionCliffordPieces])
  change JunctionSafe ((junctionFootprint L).erase retired) (mend retired w sign)
  have shape : mend retired w sign=[.X sign]++recode retired false L L.y++
      acceptOdd retired L++junctionStdRest retired L++[.X sign] := rfl
  rw [shape]
  simp only [junction_safe_append]
  exact ⟨⟨⟨⟨flip,recoder⟩,tails.2.1⟩,rest⟩,flip⟩

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.half_resources
#print axioms ECDSAAdd.Entrant.P1Life.dstart_resources
#print axioms ECDSAAdd.Entrant.P1Life.dend_resources
#print axioms ECDSAAdd.Entrant.P1Life.mend_resources
end -- ticket 8 pasted module

-- ===== P1ResourcePorts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


/-- The same numeric blocks as the record's lifetime footprint; no
cardinality-only substitution for the actual allowed wire locations. -/
theorem junction_footprint_ports (w : Nat→Wire) (sign : Wire) :
    junctionFootprint (Q6EndpointCell.ports w sign)=
      (sign::w 768::w 1797::w 1027::(wireBlock w 2056 256++wireBlock w 770 256++
        (wireBlock w 512 253++[w 1540]))).toFinset := by
  let L := Q6EndpointCell.ports w sign
  have rs : L.r=wireBlock w 2056 256 :=
    (Q6EndpointCell.ports_r w sign).trans (balancedSharedPorts_r w sign)
  have ys : L.y=wireBlock w 770 256 :=
    (Q6EndpointCell.ports_y w sign).trans (balancedSharedPorts_y w sign)
  have cs : L.carry=wireBlock w 512 253++[w 1540,w 1541,w 1026] := rfl
  have len : (wireBlock w 512 253).length=253 := by
    simp only [wireBlock,List.length_map,List.length_range']
  have bank : (wireBlock w 512 253++[w 1540,w 1541,w 1026]).take 254=
      wireBlock w 512 253++[w 1540] := by
    rw [List.take_append,List.take_of_length_le (by rw [len]; omega),len]
    rfl
  change (sign::w 768::w 1797::w 1027::(L.r++L.y++L.carry.take 254)).toFinset=_
  rw [rs,ys,cs,bank]
























end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.junction_footprint_ports

end -- ticket 8 pasted module

-- ===== P1CenterMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def junctionMaskBits (n k flag : Nat) : List MappedBit :=
  (List.range n).map fun i => ⟨if k.testBit i then some flag else none,false⟩


theorem junction_mask_value (n k flag : Nat) (s : BasisState) (fit : k<2^n) :
    mappedValue (junctionMaskBits n k flag) s=if s flag then k else 0 := by
  induction n generalizing k with
  | zero =>
    have z : k=0 := by simpa using fit
    simp [junctionMaskBits,mappedValue,z]
  | succ n ih =>
    have hd : k/2<2^n := by rw [Nat.pow_succ] at fit; omega
    have shape : junctionMaskBits (n+1) k flag=
        (⟨if k.testBit 0 then some flag else none,false⟩ : MappedBit)::junctionMaskBits n (k/2) flag := by
      simp [junctionMaskBits,List.range_succ_eq_map,List.map_map,Function.comp_def,Nat.testBit_succ]
    rw [shape,mappedValue,ih _ hd]
    have split := Nat.mod_add_div k 2
    have small := Nat.mod_lt k (by decide : 0<2)
    cases sn : s flag <;> by_cases odd : k%2=1 <;>
      simp [MappedBit.value,Nat.testBit_zero,sn,odd] <;> omega


theorem junction_mask_sources (n k flag q : Nat)
    (hq : q∈mappedWires (junctionMaskBits n k flag)) : q=flag := by
  simp only [junctionMaskBits,mappedWires,List.flatMap_map,List.mem_flatMap] at hq
  obtain ⟨i,hi,hq⟩ := hq
  cases h : k.testBit i <;> simpa [h] using hq


theorem center_odd_bits_value (L : BalancedConvert.Layout) (s : BasisState) :
    mappedValue (centerOddBits L) s=if s L.flag then 2^28+61 else 0 :=
  junction_mask_value 252 (2^28+61) L.flag s (by norm_num)


theorem center_odd_bits_sources (L : BalancedConvert.Layout) (q : Wire)
    (hq : q∈mappedWires (centerOddBits L)) : q=L.flag :=
  junction_mask_sources 252 (2^28+61) L.flag q hq


/-- Scalar converter arithmetic, abstracting the prime before case splitting. -/
theorem center_odd_scalar_rep (N v : Nat) (Q : Int) (pn : (N : Int)=2*Q+1) (fit : v<N) :
    let w := if v%2=0 then v/2 else (v+N)/2
    let z := if (w : Int)≤Q then (w : Int) else (w : Int)-(N : Int)
    (if z<0 then z+Q else z-Q-1)=((v/2 : Nat) : Int)-(if v%2=1 then 0 else Q+1) := by
  dsimp only
  by_cases even : v%2=0
  · simp only [even,if_true]
    split_ifs <;> (try contradiction) <;> omega
  · simp only [even,if_false]
    split_ifs <;> (try contradiction) <;> omega


/-- Canonical parity selects the two intervals of the odd code directly. -/
theorem center_odd_rep_half (x : Fp) :
    oddRep (x/2)=((x.val/2 : Nat) : Int)-(if x.val%2=1 then 0 else q+1) := by
  dsimp only [oddRep]
  unfold centerFp
  rw [HalfConvert.half_val]
  exact center_odd_scalar_rep p x.val q constants.2.1 (ZMod.val_lt x)


/-- Exact output word, including canonical zero and p-1. -/
theorem center_odd_word_value (x : Fp) :
    oddWord (x/2)=x.val/2+(if x.val%2=1 then 0 else 2^255+(2^31+488)) := by
  rw [oddWord,center_odd_rep_half]
  have hv := ZMod.val_lt x
  have hp := constants
  generalize hval : x.val=v at *
  by_cases odd : v%2=1
  · simp only [odd,if_true,sub_zero,Nat.add_zero]
    exact BalancedCleanup.encoded_nonnegative _ _ (by omega) (by norm_num [p] at hv ⊢; omega)
  · simp only [odd,if_false]
    have range : -((2^256 : Nat) : Int)≤((v/2 : Nat) : Int)-(q+1) ∧
        ((v/2 : Nat) : Int)-(q+1)<((2^256 : Nat) : Int) := by
      norm_num [q,p] at hv ⊢
      omega
    have e := BalancedFold.encode_shift 256 (((v/2 : Nat) : Int)-(q+1)) range
    have neg : ((v/2 : Nat) : Int)-(q+1)<0 := by omega
    rw [if_pos neg] at e
    norm_num [q,p] at hv e ⊢
    omega

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.center_odd_word_value
end -- ticket 8 pasted module

-- ===== P1CenterViews =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


theorem junction_swap_in_mode (flip : Bool) (a f : Wire) (ha : a≠f)
    (s : State) (m : List Bool) (hf : s.basis f=false) :
    let p := [.CX a f,.CX f a]++(if flip then [.X f] else [])
    (run p m s).phase=s.phase ∧ (run p m s).basis f=(s.basis a ^^ flip) ∧
    (run p m s).basis a=false ∧
    ∀q,q≠a → q≠f → (run p m s).basis q=s.basis q := by
  cases flip
  all_goals
    refine ⟨rfl,?_,?_,?_⟩
    · simp [run,writeBit,Function.update_apply,ha,Ne.symm ha,hf]
    · simp [run,writeBit,Function.update_apply,ha,Ne.symm ha,hf]
    · intro q hqa hqf
      simp [run,writeBit,Function.update_apply,hqa,hqf]


theorem center_odd_word_shape (L : BalancedConvert.Layout) (hw : L.Widths) :
    ∃a rest,HalfConvert.lowBit L=a ∧ L.word=a::rest := by
  cases h : L.low with
  | nil => have e := hw.1; rw [h] at e; simp at e
  | cons a tl => exact ⟨a,tl++[L.msb],by simp [HalfConvert.lowBit,h],by simp [BalancedConvert.Layout.word,h]⟩


theorem center_odd_word_nodup (L : BalancedConvert.Layout) (hn : L.wires.Nodup) : L.word.Nodup :=
  (List.nodup_append'.mp (List.nodup_cons.mp (BalancedConvert.layout_add L hn)).2).1


theorem center_odd_low_nodup (L : BalancedConvert.Layout) (hn : L.wires.Nodup) :
    (L.cin::(L.low++L.carry.take 254)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  have lim := (List.take_sublist 254 L.carry).count_le q
  simp only [BalancedConvert.Layout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega


theorem center_odd_low_away (L : BalancedConvert.Layout) (hn : L.wires.Nodup) :
    L.flag∉L.cin::(L.low++L.carry.take 254) := by
  intro bad
  have h := List.nodup_iff_count.mp hn L.flag
  have a := List.count_pos_iff.mpr bad
  have lim := (List.take_sublist 254 L.carry).count_le L.flag
  simp only [BalancedConvert.Layout.wires,List.count_cons,List.count_append,List.count_nil,
    beq_self_eq_true,if_true] at h a
  omega


/-- The adder ports of `centerOdd` (bits `3..254` and their carries) are a sublist of the
full low-register ports. -/
theorem center_odd_high_sub (L : BalancedConvert.Layout) :
    (L.cin::(L.low.drop 3++(L.carry.take 254).drop 3)).Sublist (L.cin::(L.low++L.carry.take 254)) :=
  List.Sublist.cons₂ L.cin ((List.drop_sublist 3 L.low).append (List.drop_sublist 3 _))


theorem center_odd_high_nodup (L : BalancedConvert.Layout) (hn : L.wires.Nodup) :
    (L.cin::(L.low.drop 3++(L.carry.take 254).drop 3)).Nodup :=
  (center_odd_high_sub L).nodup (center_odd_low_nodup L hn)


theorem center_odd_high_away (L : BalancedConvert.Layout) (hn : L.wires.Nodup) :
    L.flag∉L.cin::(L.low.drop 3++(L.carry.take 254).drop 3) :=
  fun h => center_odd_low_away L hn ((center_odd_high_sub L).subset h)


theorem center_odd_msb_away (L : BalancedConvert.Layout) (hn : L.wires.Nodup) : L.msb∉L.low := by
  intro bad
  have h := List.nodup_iff_count.mp hn L.msb
  have a := List.count_pos_iff.mpr bad
  simp only [BalancedConvert.Layout.wires,List.count_cons,List.count_append,List.count_nil,
    beq_self_eq_true,if_true] at h
  omega

end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1CenterCorrect =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


/-- Direct four-pass proof on the converter's own layout. The untouched
register, including any borrowed zero hosts, remains raw zero. -/
theorem centerOdd_correct (L : BalancedConvert.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=x.val)
    (hc : ∀q∈BalancedConvert.work L,s.basis q=false) :
    let t := run (centerOdd L) m s
    t.phase=s.phase ∧ regValue L.word t.basis=oddWord (x/2) ∧
    (∀q∈BalancedConvert.work L,t.basis q=false) ∧
    (∀q,q∉L.word → t.basis q=s.basis q) := by
  obtain ⟨a,rest,hlow,hword⟩ := center_odd_word_shape L hw
  have nd := center_odd_word_nodup L hn
  rw [hword] at nd
  have aRest : a∉rest := (List.nodup_cons.mp nd).1
  have aw : a∈L.word := by rw [hword]; simp
  have fa : a≠L.flag := fun e => BalancedConvert.layout_away L hn L.flag (by simp) (e ▸ aw)
  have hflag : s.basis L.flag=false := hc _ (by simp [BalancedConvert.work])
  have flagWord : L.flag∉L.word := BalancedConvert.layout_away L hn L.flag (by simp)
  have restFlag : L.flag∉rest := fun h => flagWord (by rw [hword]; simp [h])
  have msbWord : L.msb∈L.word := by simp [BalancedConvert.Layout.word]
  have fm : L.flag≠L.msb := fun e => flagWord (e ▸ msbWord)
  have lowWord (q : Wire) (hq : q∈L.low) : q∈L.word := by simp [BalancedConvert.Layout.word,hq]
  have msbLow := center_odd_msb_away L hn
  have xv := ZMod.val_lt x
  norm_num [p] at xv
  have hp := constants
  dsimp only
  obtain ⟨m1,m2,m3,m4,e⟩ := HalfConvert.run_four
    [.CX a L.flag,.CX L.flag a,.X L.flag] (rotateRight L.word)
    (mappedAdd (centerOddBits L) (L.low.drop 3) ((L.carry.take 254).drop 3) L.cin)
    [.CX L.flag L.msb,.CX L.msb L.flag] m s
  rw [show centerOdd L=[.CX a L.flag,.CX L.flag a,.X L.flag]++rotateRight L.word++
      mappedAdd (centerOddBits L) (L.low.drop 3) ((L.carry.take 254).drop 3) L.cin++
      [.CX L.flag L.msb,.CX L.msb L.flag] by rw [centerOdd,hlow],e]
  generalize e1 : run [.CX a L.flag,.CX L.flag a,.X L.flag] m1 s=s1
  generalize e2 : run (rotateRight L.word) m2 s1=s2
  generalize e3 : run (mappedAdd (centerOddBits L) (L.low.drop 3) ((L.carry.take 254).drop 3)
    L.cin) m3 s2=s3
  generalize e4 : run [.CX L.flag L.msb,.CX L.msb L.flag] m4 s3=s4
  have h1 := junction_swap_in_mode true a L.flag fa s m1 hflag
  simp only [if_true,Bool.xor_true,List.cons_append,List.nil_append] at h1
  rw [e1] at h1
  let R := regValue rest s.basis
  have hxv : x.val=(if s.basis a then 1 else 0)+2*R := by rw [←hx,hword]; rfl
  have restSame : regValue rest s1.basis=R :=
    regValue_congr _ _ _ (fun q hq => h1.2.2.2 q
      (fun e => aRest (e ▸ hq)) (fun e => restFlag (e ▸ hq)))
  have v1 : regValue L.word s1.basis=2*R := by
    rw [hword]
    change (if s1.basis a then 1 else 0)+2*regValue rest s1.basis=2*R
    rw [h1.2.2.1,restSame]
    simp
  have r2 := rotateRight_spec L.word (center_odd_word_nodup L hn) (2*R) (by omega) s1 m2 v1
  have f2 := (rotate_frame L.word s1 m2).2.1
  rw [e2] at r2 f2
  have v2 : regValue L.word s2.basis=R := by
    have h := r2.2
    change regValue L.word s2.basis=2*R/2 at h
    omega
  have clean2 (q : Wire) (hq : q∈BalancedConvert.scratch L) : s2.basis q=false := by
    have away := BalancedConvert.scratch_away L hn q hq
    have qa : q≠a := fun e => away.1 (e ▸ aw)
    rw [f2 q away.1,h1.2.2.2 q qa away.2]
    exact hc q (by simp [BalancedConvert.work,hq])
  have flag2 : s2.basis L.flag= !s.basis a := by rw [f2 _ flagWord,h1.2.1]
  have split2 := HalfConvert.word_split L hw s2.basis
  rw [v2] at split2
  have msb2 : s2.basis L.msb=false := by
    cases h : s2.basis L.msb
    · rfl
    · rw [h] at split2
      simp only [if_true,Nat.mul_one] at split2
      omega
  have low2 : regValue L.low s2.basis=R := by
    rw [msb2] at split2
    simp only [Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at split2
    omega
  have p3 := mappedAdd_correct (centerOddBits L) (L.low.drop 3) ((L.carry.take 254).drop 3) L.cin
    (center_odd_high_nodup L hn)
    (fun q hq => (center_odd_bits_sources L q hq).symm ▸ center_odd_high_away L hn)
    (by simp [centerOddBits,hw.1]) (by simp [List.length_take,hw.1,hw.2]) s2 m3
    (fun q hq => clean2 q (by
      simp [BalancedConvert.scratch,List.mem_of_mem_take (List.mem_of_mem_drop hq)]))
  rw [e3] at p3
  -- Bits 0..2 of the low register are untouched; bits 3..254 receive `f*(2^28+61)`.
  have lowSplit (t : BasisState) :
      regValue L.low t=regValue (L.low.take 3) t+8*regValue (L.low.drop 3) t := by
    have h := regValue_append (L.low.take 3) (L.low.drop 3) t
    rw [List.take_append_drop,List.length_take,hw.1] at h
    exact h
  have lowDisjoint : ∀q∈L.low.take 3,q∉L.low.drop 3 := by
    have nd3 : (L.low.take 3++L.low.drop 3).Nodup := by
      rw [List.take_append_drop]
      exact (List.nodup_append'.mp (center_odd_word_nodup L hn)).1
    exact fun q hq hd => List.disjoint_left.mp (List.nodup_append'.mp nd3).2.2 hq hd
  have head3 : regValue (L.low.take 3) s3.basis=regValue (L.low.take 3) s2.basis :=
    regValue_congr _ _ _ (fun q hq => p3.2.1 q (lowDisjoint q hq))
  have v3 : regValue L.low s3.basis=(if s.basis a then 0 else 2^31+488)+R := by
    have old := lowSplit s2.basis
    rw [low2] at old
    rw [lowSplit,head3,p3.2.2,center_odd_bits_value,flag2,
      clean2 _ (by simp [BalancedConvert.scratch]),List.length_drop,hw.1]
    cases hk : s.basis a <;> simp only [hk,Bool.not_false,Bool.not_true,Bool.false_eq_true,
      if_false,if_true,Bool.toNat_false,Nat.add_zero,Nat.zero_add] at hxv ⊢ <;>
      norm_num only [Nat.reducePow] <;> omega
  have flag3 : s3.basis L.flag= !s.basis a :=
    (p3.2.1 _ (fun h => flagWord (lowWord _ (List.mem_of_mem_drop h)))).trans flag2
  have msb3 : s3.basis L.msb=false :=
    (p3.2.1 _ (fun h => msbLow (List.mem_of_mem_drop h))).trans msb2
  have h4 := junction_swap_in_mode false L.flag L.msb fm s3 m4 msb3
  simp only [Bool.false_eq_true,if_false,List.append_nil,Bool.xor_false] at h4
  rw [e4] at h4
  have low4 : regValue L.low s4.basis=regValue L.low s3.basis :=
    regValue_congr _ _ _ (fun q hq => h4.2.2.2 q
      (fun e => flagWord (e ▸ lowWord q hq)) (fun e => msbLow (e ▸ hq)))
  have frame (q : Wire) (hq : q∉L.word) : s4.basis q=s.basis q := by
    by_cases hf : q=L.flag
    · subst q
      rw [h4.2.2.1,hflag]
    · have qa : q≠a := fun e => hq (e ▸ aw)
      have qm : q≠L.msb := fun e => hq (e ▸ msbWord)
      rw [h4.2.2.2 q hf qm,p3.2.1 q (fun h => hq (lowWord q (List.mem_of_mem_drop h))),
        f2 q hq,h1.2.2.2 q qa hf]
  refine ⟨h4.1.trans (p3.1.trans (r2.1.trans h1.1)),?_,
    BalancedConvert.work_of_frame L hn s s4 hc frame,frame⟩
  rw [HalfConvert.word_split L hw,low4,v3,h4.2.1,flag3,center_odd_word_value]
  cases hk : s.basis a
  · have h : ¬x.val%2=1 := by simp only [hk,Bool.false_eq_true,if_false] at hxv; omega
    rw [if_neg h]
    simp only [hk,Bool.not_false,if_true,Bool.false_eq_true,if_false] at hxv ⊢
    omega
  · have h : x.val%2=1 := by simp only [hk,if_true] at hxv; omega
    rw [if_pos h]
    simp only [hk,Bool.not_true,Bool.false_eq_true,if_false,if_true] at hxv ⊢
    omega

end ECDSAAdd.Entrant.P1Life

#print axioms ECDSAAdd.Entrant.P1Life.centerOdd_correct
end -- ticket 8 pasted module

-- ===== RouteASlotCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic Challenge Baselines


def mappedLeafSlots (b : MappedBit) : Nat :=
  (if b.wire.isSome then 2 else 1)+(if b.flip then 1 else 0)

def mappedStepSlots (b : MappedBit) : Nat :=
  (if b.wire.isSome then 12 else 4)+(if b.flip then 5 else 0)

def mappedSlots : List MappedBit → Nat
  | [] => 0
  | [b] => mappedLeafSlots b
  | b::b'::bs => mappedStepSlots b+mappedSlots (b'::bs)


theorem mapped_leaf_slots (b : MappedBit) (y cin : Wire) :
    gateSlots (mappedSum b y cin)=mappedLeafSlots b := by
  rcases b with ⟨wire,flip⟩
  cases wire <;> cases flip <;> rfl


theorem mapped_step_slots (b : MappedBit) (y cin c : Wire) :
    gateSlots (mappedMajority b y cin c)+gateSlots (mappedEraseCarry b y cin c)+
      gateSlots (mappedSum b y cin)=mappedStepSlots b := by
  rcases b with ⟨wire,flip⟩
  cases wire <;> cases flip <;> rfl


theorem mapped_add_slots (bits : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (hy : ys.length=bits.length) (hc : cs.length+1=bits.length) :
    gateSlots (mappedAdd bits ys cs cin)=mappedSlots bits := by
  induction bits generalizing ys cs cin with
  | nil => simp at hc
  | cons b bs ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      cases bs with
      | nil =>
        have e : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy)
        subst ys
        exact mapped_leaf_slots b y cin
      | cons b' bs =>
        cases ys with
        | nil => simp at hy
        | cons y' ys =>
          cases cs with
          | nil => simp at hc
          | cons c cs =>
            have step := ih (y'::ys) cs c (by simpa using hy) (by simpa using hc)
            have head := mapped_step_slots b y cin c
            simp only [mappedAdd,gateSlots_append,step,mappedSlots]
            omega


theorem mapped_sub_slots (bits : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (hy : ys.length=bits.length) (hc : cs.length+1=bits.length) :
    gateSlots (mappedSub bits ys cs cin)=mappedSlots bits+2*ys.length := by
  simp only [mappedSub,gateSlots_append,notRegister_gateSlots,mapped_add_slots bits ys cs cin hy hc]
  omega


def literalSlots : Nat → Nat → Nat
  | 0,_ => 0
  | 1,k => 1+k%2
  | n+2,k => 7+5*(k%2)+literalSlots (n+1) (k/2)


theorem literal_leaf_slots (bit : Bool) (x cin : Wire) :
    gateSlots (literalConstSum bit x cin)=1+bit.toNat := by cases bit <;> rfl


theorem literal_step_slots (bit : Bool) (x cin c one : Wire) :
    gateSlots (literalConstStep bit x cin c)+gateSlots (literalConstErase bit x cin c one)=7+5*bit.toNat := by
  cases bit <;> rfl


theorem literal_slots (xs cs : List Wire) (cin one : Wire) (k : Nat)
    (hc : cs.length+1=xs.length) :
    gateSlots (literalConstAdd xs cs cin one k)=literalSlots xs.length k := by
  induction xs generalizing cs cin k with
  | nil => simp at hc
  | cons x xs ih =>
    have bit : (decide (k%2=1)).toNat=k%2 := by
      have bound := Nat.mod_lt k (by decide : 0<2)
      by_cases h : k%2=1 <;> simp [h,Bool.toNat] <;> omega
    cases xs with
    | nil => simpa only [literalConstAdd,List.length_singleton,literalSlots,bit] using
        literal_leaf_slots (decide (k%2=1)) x cin
    | cons y ys =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have step := ih cs c (k/2) (by simpa using hc)
        have head := literal_step_slots (decide (k%2=1)) x cin c one
        simp only [literalConstAdd,gateSlots_append,step,List.length_cons,literalSlots]
        rw [bit] at head
        omega


theorem rotate_slots (xs : List Wire) :
    gateSlots (rotateRight xs)=3*(xs.length-1) ∧
    gateSlots (rotateLeft xs)=3*(xs.length-1) := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨rfl,rfl⟩
    | cons y ys =>
      simp only [rotateRight,rotateLeft,gateSlots_append,List.length_cons] at ih ⊢
      have head : gateSlots (swapBits x y)=3 := rfl
      rw [head]
      exact ⟨by omega,by omega⟩
end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotChains =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic Challenge Baselines


theorem compare_chain_slots (erase : Bool) (xs ys cs : List Wire) (cin target : Wire)
    (hl : xs.length=ys.length) (hc : cs.length+1=ys.length) :
    gateSlots (Q6LifetimeResearch.compareChain erase xs ys cs cin target)=10*cs.length+(if erase then 5 else 7) := by
  induction ys generalizing xs cs cin with
  | nil => simp at hc
  | cons b bs ih =>
    cases xs with
    | nil => simp at hl
    | cons a as =>
      cases bs with
      | nil =>
        have az : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        have cz : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
        subst as cs
        cases erase <;> rfl
      | cons b' bs =>
        cases as with
        | nil => simp at hl
        | cons a' as =>
          cases cs with
          | nil => simp at hc
          | cons c cs =>
            have step := ih (a'::as) cs c (by simpa using hl) (by simpa using hc)
            have maj : gateSlots (majority a b cin c)=6 := rfl
            have ers : gateSlots (eraseCarry a b cin c)=4 := rfl
            simp only [Q6LifetimeResearch.compareChain,gateSlots_append,step,maj,ers,List.length_cons]
            omega


theorem add_top_slots (xs ys cs : List Wire) (cin : Wire)
    (hy : ys.length=xs.length) (hc : cs.length+2=xs.length) :
    gateSlots (Q6LifetimeResearch.addTop xs ys cs cin)=12*cs.length+9 := by
  induction cs generalizing xs ys cin with
  | nil =>
    cases xs with
    | nil => simp at hc
    | cons a xs =>
      cases xs with
      | nil => simp at hc
      | cons a' as =>
        have az : as=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hc; omega)
        subst as
        cases ys with
        | nil => simp at hy
        | cons b ys =>
          cases ys with
          | nil => simp at hy
          | cons z zs =>
            have zz : zs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hy; omega)
            subst zs
            rfl
  | cons c cs ih =>
    cases xs with
    | nil => simp at hc
    | cons a xs =>
      cases xs with
      | nil => simp at hc
      | cons a' as =>
        cases as with
        | nil => simp at hc
        | cons a'' as =>
          cases ys with
          | nil => simp at hy
          | cons b ys =>
            cases ys with
            | nil => simp at hy
            | cons b' bs =>
              cases bs with
              | nil => simp at hy
              | cons b'' bs =>
                have step := ih (a'::a''::as) (b'::b''::bs) c (by simpa using hy) (by simpa using hc)
                have maj : gateSlots (majority a b cin c)=6 := rfl
                have ers : gateSlots (eraseCarry a b cin c)=4 := rfl
                have tail : gateSlots [.CX a b,.CX cin b]=2 := rfl
                simp only [Q6LifetimeResearch.addTop,gateSlots_append,step,maj,ers,tail,List.length_cons]
                omega
end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotShape =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic


def mappedShapeSlots : List (Bool×Bool) → Nat
  | [] => 0
  | [(wire,flip)] => (if wire then 2 else 1)+(if flip then 1 else 0)
  | (wire,flip)::b::bs => (if wire then 12 else 4)+(if flip then 5 else 0)+mappedShapeSlots (b::bs)


theorem mapped_slots_shape (bits : List MappedBit) :
    mappedSlots bits=mappedShapeSlots (bits.map (fun b => (b.wire.isSome,b.flip))) := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    cases bs with
    | nil => rfl
    | cons c cs =>
      simpa only [mappedSlots,mappedShapeSlots,List.map_cons,mappedStepSlots] using
        congrArg (fun n => mappedStepSlots b+n) ih


theorem mapped_option_if (bit : Bool) (w : Wire) :
    (if bit then some w else none).isSome=bit := by cases bit <;> rfl
end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotPasses =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic BalancedCircuit BalancedField Challenge Baselines
attribute [local irreducible] P1Life.half P1Life.forward P1Life.inverse P1Life.dstart P1Life.dend P1Life.mend
attribute [local irreducible] Q6LifetimeResearch.half Q6LifetimeResearch.forward Q6LifetimeResearch.inverse


theorem slot_layout_lengths (L : Layout) (hw : L.Widths) :
    L.low.length=255 ∧ L.r.length=256 ∧ L.y.length=256 ∧
    (rawTarget L).length=257 ∧ ((Q6Structural.q6Carry L).take 255).length=255 := by
  have a := BalancedCleanup.widths L.toLayout hw
  exact ⟨a.1,a.2.1,a.2.2.1,by simp [rawTarget,a.2.1],P1Life.p1_active_length L hw⟩


theorem slot_views (L : Layout) (hw : L.Widths) :
    gateSlots (BalancedCleanup.prepareSign L.toLayout)=257 ∧
    gateSlots (P1Life.prepareCompare L)=1281 ∧
    gateSlots (BalancedCleanup.prepareCompare L.toLayout)=1282 ∧
    gateSlots (BiasedInverse.unbiasView L)=258 := by
  have len := slot_layout_lengths L hw
  have rot := rotate_slots L.r
  simp only [BalancedCleanup.prepareSign,P1Life.prepareCompare,BalancedCleanup.prepareCompare,
    BiasedInverse.unbiasView,gateSlots_append,reverse_gateSlots,signComplement_gateSlots,
    len.2.1,len.2.2.1,rot.2,gateSlots_cons,gateSlots_nil,instructionSlots]
  exact ⟨by first | omega | exact True.intro,by first | omega | exact True.intro,by first | omega | exact True.intro,by first | omega | exact True.intro⟩


theorem slot_fold (oddMode sub : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (if oddMode then (if sub then P1Life.unfoldStep retired L else P1Life.fold retired L)
      else (if sub then Q6LifetimeResearch.unfoldStep retired L else Q6LifetimeResearch.fold retired L))=
      3080+(if sub then 510+11 else if oddMode then 10 else 9) := by
  have len := slot_layout_lengths L hw
  have bl : (ShortBiasedFold.lowBits L).length=L.low.length := by rw [ShortBiasedFold.lowBits_length,len.1]
  have cl : (L.carry.take 254).length+1=(ShortBiasedFold.lowBits L).length := by
    rw [bl,len.1];simp [List.length_take,hw.2.2]
  have a := mapped_add_slots (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one bl.symm cl
  have b := mapped_sub_slots (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one bl.symm cl
  have cost : mappedSlots (ShortBiasedFold.lowBits L)=3080 := by
    rw [mapped_slots_shape]
    change mappedShapeSlots ((List.range 255).map (fun i => (true,BiasedCircuit.jh.testBit i)))=3080
    decide +kernel
  rw [cost] at a b
  cases oddMode <;> cases sub
  all_goals simp only [P1Life.fold,P1Life.unfoldStep,Q6LifetimeResearch.fold,Q6LifetimeResearch.unfoldStep,
    Bool.false_eq_true,if_false,if_true,Q6LifetimeResearch.move,rename_gateSlots,gateSlots_append,
    a,b,len.1,gateSlots_cons,gateSlots_nil,instructionSlots,List.length_cons,List.length_nil]
  all_goals first | omega | exact True.intro


theorem slot_raw_add (oddMode : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (if oddMode then P1Life.rawAdd retired L else Q6LifetimeResearch.rawAdd retired L)=3586 := by
  have len := slot_layout_lengths L hw
  have tail := CoherentTail.addPrefix_gateSlots (L.ylow.drop 1) (L.low.drop 1)
    (((Q6Structural.q6Carry L).take 255).drop 1) L.ymsb L.rmsb L.one
    (((Q6Structural.q6Carry L).take 255).getD 0 0)
    (by simp [List.length_drop,hw.2.1,len.1]) (by simp [List.length_drop,hw.2.1,len.2.2.2.2])
  simp only [List.length_drop,hw.2.1] at tail
  cases oddMode
  all_goals simp only [Bool.false_eq_true,if_false,if_true,P1Life.rawAdd,Q6LifetimeResearch.rawAdd,
    Q6LifetimeResearch.move,rename_gateSlots,gateSlots_append,reverse_gateSlots,signComplement_gateSlots,
    len.2.2.1,tail,P1Life.orMajor,P1Life.orErase,majority,eraseCarry,
    gateSlots_cons,gateSlots_nil,instructionSlots,List.length_cons,List.length_nil]
  all_goals first | omega | exact True.intro


theorem slot_compare (exchange erase : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (if exchange then P1Life.compare retired erase L else Q6LifetimeResearch.compare retired erase L)=
      (if erase then 3071 else 3073) := by
  have len := slot_layout_lengths L hw
  have a := compare_chain_slots erase (L.r.drop 1) (L.y.drop 1)
    (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity
    (by simp [List.length_drop,len.2.1,len.2.2.1])
    (by simp [List.length_drop,len.2.2.1,len.2.2.2.2])
  have b := compare_chain_slots erase (L.y.drop 1) (L.r.drop 1)
    (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity
    (by simp [List.length_drop,len.2.1,len.2.2.1])
    (by simp [List.length_drop,len.2.1,len.2.2.2.2])
  simp only [List.length_drop,len.2.2.2.2] at a b
  cases exchange <;> cases erase
  all_goals simp only [Bool.false_eq_true,if_false,if_true,P1Life.compare,Q6LifetimeResearch.compare,
    Q6LifetimeResearch.move,rename_gateSlots,gateSlots_append,notRegister_gateSlots,
    List.length_cons,len.2.1,len.2.2.1,a,b,majority,eraseCarry,
    gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]
  all_goals first | omega | exact True.intro


theorem slot_raw_sub (oddMode : Bool) (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (if oddMode then P1Life.rawSub retired L else Q6LifetimeResearch.rawSubTail retired L)=
      (if oddMode then 4104 else 4102) := by
  have len := slot_layout_lengths L hw
  have sl : (GuardCompression.source L).length=257 := by simp [GuardCompression.source,len.2.2.1]
  have tail := add_top_slots ((GuardCompression.source L).drop 1) ((rawTarget L).drop 1)
    (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0)
    (by simp [List.length_drop,sl,len.2.2.2.1])
    (by simp [List.length_drop,sl,len.2.2.2.2])
  simp only [List.length_drop,len.2.2.2.2] at tail
  cases oddMode
  all_goals simp only [Bool.false_eq_true,if_false,if_true,P1Life.rawSub,Q6LifetimeResearch.rawSubTail,
    Q6LifetimeResearch.move,rename_gateSlots,gateSlots_append,signComplement_gateSlots,
    notRegister_gateSlots,len.2.2.1,len.2.2.2.1,tail,P1Life.orMajor,P1Life.orErase,majority,eraseCarry,
    gateSlots_cons,gateSlots_nil,instructionSlots,List.length_cons,List.length_nil]
  all_goals first | omega | exact True.intro
end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotBodies =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic BalancedCircuit BalancedField Challenge Baselines
attribute [local irreducible] P1Life.half P1Life.forward P1Life.inverse P1Life.dstart P1Life.dend P1Life.mend
attribute [local irreducible] Q6LifetimeResearch.half Q6LifetimeResearch.forward Q6LifetimeResearch.inverse


theorem slot_short (L : Layout) (hw : L.Widths) :
    gateSlots (P1Life.shortConstAdd L h.toNat)=2989 ∧
    gateSlots (P1Life.shortConstAdd L (encodeWord 255 (-h)))=1785 := by
  have len := slot_layout_lengths L hw
  have cl : (L.carry.take 251).length+1=(L.low.drop 3).length := by
    simp [List.length_take,List.length_drop,hw.2.2,len.1]
  have a := literal_slots (L.low.drop 3) (L.carry.take 251) (L.low.getD 2 0) L.one (h.toNat/8) cl
  have b := literal_slots (L.low.drop 3) (L.carry.take 251) (L.low.getD 2 0) L.one (encodeWord 255 (-h)/8) cl
  have ca : literalSlots 252 (h.toNat/8)=2988 := by decide +kernel
  have cb : literalSlots 252 (encodeWord 255 (-h)/8)=1784 := by decide +kernel
  simp only [List.length_drop,len.1] at a b
  simp only [P1Life.shortConstAdd,gateSlots_append,a,b,ca,cb,gateSlots_cons,gateSlots_nil,instructionSlots]
  exact ⟨True.intro,True.intro⟩


theorem slot_half (retired : Wire) (divide : Bool) (w : Nat→Wire) (sign : Wire) :
    gateSlots (P1Life.half retired divide w sign)=(if divide then 16594 else 16415) := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have len := slot_layout_lengths L hw
  have a := slot_raw_add true retired L hw
  have b := slot_fold true false retired L hw
  have c := slot_compare true true retired L hw
  have d := slot_short L hw
  have e := slot_views L hw
  have f := slot_fold true true retired L hw
  have g := slot_compare true false retired L hw
  have i := slot_raw_sub true retired L hw
  have rt := rotate_slots (rawTarget L)
  simp only [if_true,Bool.false_eq_true,if_false] at a b c f g i
  have shape : P1Life.half retired divide w sign=[.X sign]++
    (if divide then P1Life.forward retired L else P1Life.inverse retired L)++[.X sign] := by simp only [P1Life.half]; rfl
  rw [shape]
  cases divide
  all_goals simp only [P1Life.forward,P1Life.inverse,Bool.false_eq_true,if_false,if_true,
    gateSlots_append,reverse_gateSlots,Q6LifetimeResearch.move,rename_gateSlots,
    a,b,c,d.1,d.2,e.1,e.2.1,e.2.2.2,f,g,i,rt.1,rt.2,len.2.2.2.1,
    P1Life.p1Seed,OneReuse.newPrepare,BiasedCircuit.flipBias,P1Life.exposure,
    gateSlots_cons,gateSlots_nil,instructionSlots]
  all_goals first | omega | exact True.intro


theorem slot_recode (retired : Wire) (toOdd : Bool) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    gateSlots (P1Life.recode retired toOdd L L.y)=(if toOdd then 3081 else 3591) := by
  have bl : (P1Life.junctionXorBits L.ylow.length (2*BiasedCircuit.jh) L.ymsb).length=L.ylow.length := by simp [P1Life.junctionXorBits]
  have cl : (P1Life.recodeBank retired L).length+1=(P1Life.junctionXorBits L.ylow.length (2*BiasedCircuit.jh) L.ymsb).length := by
    rw [bl,P1Life.recode_bank_length retired L hw hn member,hw.2.1]
  have a := mapped_add_slots _ L.ylow (P1Life.recodeBank retired L) L.lower bl.symm cl
  have b := mapped_sub_slots _ L.ylow (P1Life.recodeBank retired L) L.lower bl.symm cl
  have cost : mappedSlots (P1Life.junctionXorBits 255 (2*BiasedCircuit.jh) L.ymsb)=3080 := by
    rw [mapped_slots_shape]
    change mappedShapeSlots ((List.range 255).map (fun i => (true,(2*BiasedCircuit.jh).testBit i)))=3080
    decide +kernel
  rw [P1Life.recode_y_shape retired toOdd L hw,hw.2.1] at *
  rw [cost] at a b
  cases toOdd <;> simp only [Bool.false_eq_true,if_false,if_true,gateSlots_append,a,b,
    gateSlots_cons,gateSlots_nil,instructionSlots] <;> omega


theorem slot_center (L : BalancedConvert.Layout) (hw : L.Widths) :
    gateSlots (P1Life.centerOdd L)=1823 := by
  have bl : (P1Life.centerOddBits L).length=(L.low.drop 3).length := by
    simp [P1Life.centerOddBits,hw.1]
  have cl : ((L.carry.take 254).drop 3).length+1=(P1Life.centerOddBits L).length := by
    simp [P1Life.centerOddBits,List.length_take,hw.2]
  have add := mapped_add_slots _ (L.low.drop 3) ((L.carry.take 254).drop 3) L.cin bl.symm cl
  have cost : mappedSlots (P1Life.centerOddBits L)=1053 := by
    rw [mapped_slots_shape]
    simp only [P1Life.centerOddBits,List.map_map,Function.comp_def,mapped_option_if]
    decide +kernel
  have rotation := rotate_slots L.word
  have len : L.word.length=256 := by simp [BalancedConvert.Layout.word,hw.1]
  simp only [P1Life.centerOdd,gateSlots_append,add,cost,rotation.1,len,
    gateSlots_cons,gateSlots_nil,instructionSlots]
end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotJunctions =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic BalancedCircuit BalancedField Challenge Baselines MappedCompressed
attribute [local irreducible] P1Life.half P1Life.forward P1Life.inverse P1Life.dstart P1Life.dend P1Life.mend
attribute [local irreducible] Q6LifetimeResearch.half Q6LifetimeResearch.forward Q6LifetimeResearch.inverse


theorem slot_junction_heads (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (P1Life.junctionStdHead retired L)=13347 ∧
    gateSlots (P1Life.junctionOddHead retired L)=13346 := by
  have len := slot_layout_lengths L hw
  have raw0 := slot_raw_add false retired L hw
  have raw1 := slot_raw_add true retired L hw
  have fold0 := slot_fold false false retired L hw
  have fold1 := slot_fold true false retired L hw
  have comp0 := slot_compare false true retired L hw
  have comp1 := slot_compare true true retired L hw
  have views := slot_views L hw
  have rt := rotate_slots (rawTarget L)
  simp only [Bool.false_eq_true,if_false,if_true] at raw0 raw1 fold0 fold1 comp0 comp1
  simp only [P1Life.junctionStdHead,P1Life.junctionOddHead,gateSlots_append,reverse_gateSlots,
    raw0,raw1,fold0,fold1,comp0,comp1,views.1,views.2.1,views.2.2.1,rt.1,len.2.2.2.1,
    GuardCompression.seed,P1Life.p1Seed,OneReuse.newPrepare,BiasedCircuit.flipBias,
    P1Life.exposure,Q6StructuralCell.exposure,Q6LowerExposure.expose,
    gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]
  exact ⟨by first | omega | exact True.intro,by first | omega | exact True.intro⟩


theorem slot_junction_emits (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (P1Life.emitOdd retired L)=3502 ∧
    gateSlots (P1Life.acceptOdd retired L)=2298 ∧
    gateSlots (P1Life.emitStandard retired L)=3532 := by
  have len := slot_layout_lengths L hw
  have short := slot_short L hw
  have cl : (L.carry.take 254).length+1=L.low.length := by simp [List.length_take,hw.2.2,len.1]
  have lit := literal_slots L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral cl
  have cost : literalSlots 255 BalancedCleanup.positiveLiteral=3019 := by decide +kernel
  rw [len.1,cost] at lit
  simp only [P1Life.emitOdd,P1Life.acceptOdd,P1Life.emitStandard,
    gateSlots_append,Q6LifetimeResearch.move,rename_gateSlots,notRegister_gateSlots,
    signComplement_gateSlots,len.1,len.2.1,short.1,short.2,lit,
    gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]
  exact ⟨by first | omega | exact True.intro,by first | omega | exact True.intro,by first | omega | exact True.intro⟩


theorem slot_junction_rest (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (P1Life.junctionStdRest retired L)=14373 := by
  have len := slot_layout_lengths L hw
  have comp := slot_compare false false retired L hw
  have fold := slot_fold false true retired L hw
  have sub := slot_raw_sub false retired L hw
  have views := slot_views L hw
  have rt := rotate_slots (rawTarget L)
  simp only [Bool.false_eq_true,if_false,if_true] at comp fold sub
  simp only [P1Life.junctionStdRest,gateSlots_append,reverse_gateSlots,
    comp,fold,sub,views.2.2.1,views.2.2.2,rt.2,len.2.2.2.1,
    Q6StructuralCell.exposure,Q6LowerExposure.expose,
    gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]
  all_goals first | omega | exact True.intro


theorem slot_junctions (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈(Q6EndpointCell.ports w sign).carry.take 254) :
    gateSlots (P1Life.dstart retired w sign)=19932 ∧
    gateSlots (P1Life.dend retired w sign)=20471 ∧
    gateSlots (P1Life.mend retired w sign)=20264 := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have heads := slot_junction_heads retired L hw
  have emits := slot_junction_emits retired L hw
  have rest := slot_junction_rest retired L hw
  have odd := slot_recode retired true L hw hn member
  have standard := slot_recode retired false L hw hn member
  simp only [if_true,Bool.false_eq_true,if_false] at odd standard
  dsimp only [L] at heads emits rest odd standard
  simp only [P1Life.dstart,P1Life.dend,P1Life.mend,gateSlots_append,
    heads.1,heads.2,emits.1,emits.2.1,emits.2.2,rest,odd,standard,
    gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]
  exact ⟨by first | omega | exact True.intro,by first | omega | exact True.intro,by first | omega | exact True.intro⟩


theorem slot_standard_passes (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (Q6LifetimeResearch.forward retired false L)=16626 ∧
    gateSlots (Q6LifetimeResearch.inverse retired L)=16440 := by
  have heads := slot_junction_heads retired L hw
  have rest := slot_junction_rest retired L hw
  have views := slot_views L hw
  have len := slot_layout_lengths L hw
  have cl : (L.carry.take 254).length+1=L.low.length := by simp [List.length_take,hw.2.2,len.1]
  have pos := literal_slots L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral cl
  have neg := literal_slots L.low (L.carry.take 254) L.lower L.one BalancedCleanup.negativeLiteral cl
  have cp : literalSlots 255 BalancedCleanup.positiveLiteral=3019 := by decide +kernel
  have cn : literalSlots 255 BalancedCleanup.negativeLiteral=1810 := by decide +kernel
  rw [len.1,cp] at pos
  rw [len.1,cn] at neg
  have trueShape : Q6LifetimeResearch.forward retired false L=P1Life.junctionStdHead retired L++
      Q6LifetimeResearch.unnormalize retired false L++
      (BalancedCleanup.prepareSign L.toLayout).reverse++[.measureX L.one [] []] := by
    simp only [Q6LifetimeResearch.forward,P1Life.junctionStdHead,List.append_assoc]
  have falseShape : Q6LifetimeResearch.inverse retired L=BalancedCleanup.prepareSign L.toLayout++
      Q6LifetimeResearch.normalize retired L++P1Life.junctionStdRest retired L := by
    simp only [Q6LifetimeResearch.inverse,P1Life.junctionStdRest,List.append_assoc]
  constructor
  · rw [trueShape]
    simp only [gateSlots_append,Q6LifetimeResearch.unnormalize,
      Q6LifetimeResearch.move,rename_gateSlots,BalancedCleanup.unnormalize,views.1,reverse_gateSlots,pos,heads.1,
      if_true,Bool.false_eq_true,if_false,gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]
    all_goals omega
  · rw [falseShape]
    simp only [gateSlots_append,Q6LifetimeResearch.normalize,
      Q6LifetimeResearch.move,rename_gateSlots,BalancedCleanup.normalize,views.1,neg,rest,
      Bool.false_eq_true,if_false,gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]
    all_goals omega


theorem slot_standard_half (retired : Wire) (divide : Bool) (w : Nat→Wire) (sign : Wire) :
    gateSlots (Q6LifetimeResearch.half retired divide w sign)=(if divide then 16628 else 16442) := by
  have passes := slot_standard_passes retired (Q6EndpointCell.ports w sign) (Q6EndpointCell.ports_widths w sign)
  cases divide
  all_goals simp only [Q6LifetimeResearch.half,Bool.false_eq_true,if_false,if_true,gateSlots_append,
    passes.1,passes.2,gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]


theorem slot_record_half (divide : Bool) : gateSlots (R2Life760.half760 divide)=(if divide then 16628 else 16443) := by
  have half := slot_standard_half (base 760) divide base (base 2409)
  cases divide
  · rw [R2Life760.half760_false,gateSlots_append]
    simp only [Bool.false_eq_true,if_false] at half ⊢
    rw [half]
    rfl
  · rw [R2Life760.half760_true]
    simpa only [if_true] using half
end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotShift =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic Challenge Baselines
attribute [local irreducible] gateSlots


def SlotShift (P Q : Program) (a b : Nat) : Prop := Nat.succ (gateSlots P)+a=Nat.succ (gateSlots Q)+b

def SlotBound (P Q : Program) (a b : Nat) : Prop := Nat.succ (gateSlots P)+a≤Nat.succ (gateSlots Q)+b




theorem SlotShift.normalized (P Q : Program) (a b A B : Nat) (x : gateSlots P+a=gateSlots Q+b)
    (ha : a=A) (hb : b=B) : SlotShift P Q A B := by cases ha;cases hb;unfold SlotShift;omega


theorem SlotShift.increase (P Q : Program) (n : Nat) (h : gateSlots P=gateSlots Q+n) :
    SlotShift P Q 0 n := by unfold SlotShift;omega


theorem SlotShift.shrink (P Q : Program) (n : Nat) (h : gateSlots P+n=gateSlots Q) :
    SlotShift P Q n 0 := by unfold SlotShift;omega


theorem SlotBound.plain (P Q : Program) (n : Nat) (h : gateSlots P≤gateSlots Q+n) :
    SlotBound P Q 0 n := by unfold SlotBound;omega


theorem SlotShift.of_values (P Q : Program) (a b : Nat) (hp : gateSlots P=a) (hq : gateSlots Q=b) :
    SlotShift P Q b a := by unfold SlotShift;omega


theorem SlotShift.ident (P : Program) : SlotShift P P 0 0 := by unfold SlotShift;omega


theorem SlotShift.app_as {P Q P0 Q0 : Program} {a b c d : Nat}
    (x : SlotShift P P0 a b) (y : SlotShift Q Q0 c d) (A B : Nat) (ha : a+c=A) (hb : b+d=B) :
    SlotShift (P++Q) (P0++Q0) A B := by
  simp only [SlotShift,gateSlots_append] at x y ⊢
  omega


theorem SlotShift.ren {P Q : Program} {a b : Nat} (x : SlotShift P Q a b) (f : Wire→Wire) :
    SlotShift (renameProgram f P) (renameProgram f Q) a b := by simpa only [SlotShift,rename_gateSlots] using x


theorem SlotShift.program_eq {P Q P0 Q0 : Program} {a b : Nat}
    (x : SlotShift P0 Q0 a b) (hp : P=P0) (hq : Q=Q0) : SlotShift P Q a b := by cases hp;cases hq;exact x






theorem SlotShift.upper {P Q : Program} {a b : Nat} (x : SlotShift P Q a b) : SlotBound P Q a b := by
  unfold SlotShift at x
  unfold SlotBound
  omega


theorem SlotShift.to_bound {P Q : Program} {a b : Nat} (x : SlotShift P Q a b)
    (n : Nat) (h : b≤a+n) : SlotBound P Q 0 n := by unfold SlotShift at x;unfold SlotBound;omega





theorem SlotBound.ident (P : Program) : SlotBound P P 0 0 := by unfold SlotBound;omega


theorem SlotBound.app_as {P Q P0 Q0 : Program} {a b c d : Nat}
    (x : SlotBound P P0 a b) (y : SlotBound Q Q0 c d) (A B : Nat) (ha : a+c=A) (hb : b+d=B) :
    SlotBound (P++Q) (P0++Q0) A B := by
  simp only [SlotBound,gateSlots_append] at x y ⊢
  omega


theorem SlotBound.ren {P Q : Program} {a b : Nat} (x : SlotBound P Q a b) (f : Wire→Wire) :
    SlotBound (renameProgram f P) (renameProgram f Q) a b := by simpa only [SlotBound,rename_gateSlots] using x


theorem SlotBound.program_eq {P Q P0 Q0 : Program} {a b : Nat}
    (x : SlotBound P0 Q0 a b) (hp : P=P0) (hq : Q=Q0) : SlotBound P Q a b := by cases hp;cases hq;exact x


theorem SlotBound.trans_as {P Q R : Program} {a b c d : Nat}
    (x : SlotBound P Q a b) (y : SlotBound Q R c d) (A B : Nat) (ha : a+c=A) (hb : b+d=B) :
    SlotBound P R A B := by unfold SlotBound at x y ⊢;omega


theorem SlotBound.normalize {P Q : Program} {a b : Nat} (x : SlotBound P Q a b)
    (A B : Nat) (h : b+A≤a+B) : SlotBound P Q A B := by unfold SlotBound at x ⊢;omega


theorem SlotBound.bound {P Q : Program} {a b : Nat} (x : SlotBound P Q a b)
    (n : Nat) (h : b≤a+n) : gateSlots P≤gateSlots Q+n := by unfold SlotBound at x;omega
end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASchedule =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed
open ECDSAAdd.Entrant.Rolling1588


def halfWindowWith (P : Program) (j active hole : Nat) : Program :=
  ControlLoan1589.loanWindow (g j active) (base 2409) (packetCarry j)
    (renameProgram (Equiv.swap (base 719) (s j hole)) P)


def halfWindow (divide : Bool) (j active hole : Nat) : Program :=
  halfWindowWith (P1Life.half (base 760) divide base (base 2409)) j active hole


def cellWith (divide : Bool) (P : Program) (j active hole : Nat) : Program :=
  if divide then
    halfWindowWith P j active hole ++
      SW.selW (s j active) (base 2409) FrontierSW1591.swapBody
  else
    SW.selW (s j active) (base 2409) FrontierSW1591.swapBody ++
      halfWindowWith P j active hole


def cell (divide : Bool) (j active hole : Nat) : Program :=
  if divide then
    halfWindow true j active hole ++
      SW.selW (s j active) (base 2409) FrontierSW1591.swapBody
  else
    SW.selW (s j active) (base 2409) FrontierSW1591.swapBody ++
      halfWindow false j active hole


def basePacket (divide : Bool) (j : Nat) : Program :=
  onPacket j (dp ++ ParityCodec5New.untwist) ++
    (if divide then
      cell true j 3 2 ++ cell true j 4 2 ++ onPacket j bridge7 ++
      cell true j 4 2 ++ cell true j 3 2 ++ onPacket j bridge5 ++
      (if j=84 then cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2
        else cell true j 4 2)
    else
      cell false j 4 2 ++ onPacket j bridge5 ++
      cell false j 3 2 ++ cell false j 4 2 ++ onPacket j bridge7inv ++
      cell false j 4 2 ++ cell false j 3 2) ++
    onPacket j (ParityCodec5New.twist ++ ep)


def packet (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacket divide j)


def groups (divide : Bool) (j n : Nat) : Program :=
  PacketSequence.program divide (packet divide) j n


def firstRestZ : Program :=
  triple 2 3 4 d3short ++ triple 1 3 4 e3short ++ cellWith true (P1Life.dstart (base 760) base (base 2409)) 0 2 4 ++
  triple 1 3 4 d3 ++ triple 4 1 2 e3 ++ cell true 0 3 2 ++
  triple 4 1 2 d3short ++ triple 3 1 2 e3short ++ cell true 0 4 2 ++
  triple 3 1 2 d3


def firstHead : Program :=
  triple 3 1 2 e3 ++ cell false 0 4 2 ++
  triple 3 1 2 d3short ++ triple 4 1 2 e3short ++ cell false 0 3 2 ++
  triple 4 1 2 d3 ++ triple 1 3 4 e3 ++ cellWith false (P1Life.mend (base 760) base (base 2409)) 0 2 4 ++
  triple 1 3 4 d3short ++ triple 2 3 4 e3short


def firstJoint : Program :=
  firstHead ++ SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody ++ JointInverse1588.paddedD ++
    triple 2 3 4 d3


def firstCellsJ : Program :=
  triple 2 3 4 e3 ++ (JointForward1588.paddedGD ++
    (SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody ++ firstRestZ))


def firstBody (divide : Bool) : Program :=
  if divide then firstCellsJ
  else firstJoint


def firstRestZFront : Program :=
  triple 2 3 4 d3short ++ triple 1 3 4 e3short ++ cellWith true (P1Life.dstart (base 760) base (base 2409)) 0 2 4 ++
  triple 1 3 4 d3 ++ triple 4 1 2 e3 ++ cell true 0 3 2 ++
  triple 4 1 2 d3short ++ triple 3 1 2 e3short ++ cell true 0 4 2


def firstCellsJFront : Program :=
  triple 2 3 4 e3 ++ (JointForward1588.paddedGD ++
    (SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody ++ firstRestZFront))


def firstJointBack : Program :=
  cell false 0 4 2 ++
  triple 3 1 2 d3short ++ triple 4 1 2 e3short ++ cell false 0 3 2 ++
  triple 4 1 2 d3 ++ triple 1 3 4 e3 ++ cellWith false (P1Life.mend (base 760) base (base 2409)) 0 2 4 ++
  triple 1 3 4 d3short ++ triple 2 3 4 e3short ++
  SW.selW (s 0 1) (base 2409) FrontierSW1591.swapBody ++ JointInverse1588.paddedD ++
  triple 2 3 4 d3


def firstBodyShort (divide : Bool) : Program :=
  if divide then firstCellsJFront++triple 3 1 2 d3short
  else triple 3 1 2 e3short++firstJointBack


def firstCore (divide : Bool) : Program :=
  (if divide then Prefix1590.firstDecode else firstDecodeShort) ++
    G0CarryLoan5.program (base 1028) (base 0) (base 768) (firstBodyShort divide) ++
    (if divide then firstEncodeShort else Prefix1590.firstEncode)


def firstPacket (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (firstCore divide)


def placedFirstPacket (divide : Bool) : Program :=
  renameProgram (OB5.sig 511) (firstPacket divide)

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAFrames =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
  MappedCompressed Challenge RecordedQuantum Baselines
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


abbrev fieldR : List Wire := (balancedSharedPorts base (base 2409)).r

abbrev fieldY : List Wire := (balancedSharedPorts base (base 2409)).y


def EncodedFieldFrame5 (wordR wordY : Fp → Nat) (w : Nat→Wire) (sign : Wire) (isA : Bool)
    (origin : BasisState) (X Y : Fp) (state : State) : Prop :=
  ∃raw : State,raw.phase=state.phase ∧
    PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
      (wordR X) (wordY Y) raw.basis ∧ state=run (allEncode w isA 102) [] raw


def CodeFrame (wordR wordY : Fp → Nat) (E : Program) (origin : BasisState)
    (X Y : Fp) (state : State) : Prop :=
  ∃raw : State,raw.phase=state.phase ∧
    PairFrame fieldR fieldY origin (wordR X) (wordY Y) raw.basis ∧ state=run E [] raw


def CutFrame (wordR wordY : Fp → Nat) (cut : Nat) (origin : BasisState)
    (X Y : Fp) (state : State) : Prop :=
  CodeFrame wordR wordY (allEncodeCut base cut 102) origin X Y state


theorem CodeFrame.arithmetic_step_zero (wordR wordY outR outY : Fp → Nat) (E : Program) (origin : BasisState)
    (X Y A B : Fp) (before after : State)
    (zero : ∀raw : State,(run E [] raw).phase=raw.phase)
    (disjoint : Disjoint (wires E) (fieldR++fieldY).toFinset)
    (input : CodeFrame wordR wordY E origin X Y before) (phase : after.phase=before.phase)
    (step : PairFrame fieldR fieldY before.basis (outR A) (outY B) after.basis) :
    CodeFrame outR outY E origin A B after := by
  obtain ⟨raw,rawPhase,rawFrame,encoded⟩ := input
  let rawOut : State := ⟨after.phase,fun q =>
    if q∈fieldR ∨ q∈fieldY then after.basis q else raw.basis q⟩
  have away (q : Wire) (used : q∈wires E) : q∉fieldR ∧ q∉fieldY := by
    constructor <;> intro member
    · exact Finset.disjoint_left.mp disjoint used
        (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl member)))
    · exact Finset.disjoint_left.mp disjoint used
        (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inr member)))
  have rawOutFrame : PairFrame fieldR fieldY origin
      (outR A) (outY B) rawOut.basis := by
    refine ⟨?_,?_,?_⟩
    · exact (regValue_congr fieldR _ _ (by
        intro q hq
        simp only [rawOut,if_pos (Or.inl hq)])).trans step.1
    · exact (regValue_congr fieldY _ _ (by
        intro q hq
        simp only [rawOut,if_pos (Or.inr hq)])).trans step.2.1
    · intro q qr qy
      simpa only [rawOut,if_neg (not_or.mpr ⟨qr,qy⟩)] using rawFrame.2.2 q qr qy
  have localRun := run_measured_locality E (wires E) (Finset.Subset.refl _)
    rawOut raw [] (phase.trans rawPhase.symm) (by
      intro q used
      have off := away q used
      simp only [rawOut,if_neg (not_or.mpr off)])
  have actual : run E [] rawOut=after := by
    apply State.extensionality
    · exact zero rawOut
    · funext q
      by_cases used : q∈wires E
      · have off := away q used
        exact (localRun.2 q used).trans
          ((congrArg (fun state : State => state.basis q) encoded.symm).trans
            (step.2.2 q off.1 off.2).symm)
      · rw [run_preserves_outside E [] rawOut q used]
        by_cases arithmetic : q∈fieldR ∨ q∈fieldY
        · simp only [rawOut,if_pos arithmetic]
        · have off := not_or.mp arithmetic
          simp only [rawOut,if_neg arithmetic]
          exact ((step.2.2 q off.1 off.2).trans
            ((congrArg (fun state : State => state.basis q) encoded).trans
              (run_preserves_outside E [] raw q used))).symm
  exact ⟨rawOut,rfl,rawOutFrame,actual.symm⟩



theorem CodeFrame.arithmetic_step (wordR wordY outR outY : Fp → Nat) (E : Program) (origin : BasisState)
    (X Y A B : Fp) (before after : State)
    (neutral : MeasuredCodec5.zeroNeutral E=true)
    (disjoint : Disjoint (wires E) (fieldR++fieldY).toFinset)
    (input : CodeFrame wordR wordY E origin X Y before) (phase : after.phase=before.phase)
    (step : PairFrame fieldR fieldY before.basis (outR A) (outY B) after.basis) :
    CodeFrame outR outY E origin A B after := by
  exact CodeFrame.arithmetic_step_zero wordR wordY outR outY E origin X Y A B before after
    (MeasuredCodec5.zero_phase E neutral) disjoint input phase step


theorem CodeFrame.codec_step (wordR wordY : Fp → Nat) (E F : Program) (origin : BasisState) (X Y : Fp)
    (state : State) (records : List Bool) (neutral : MeasuredCodec5.zeroNeutral F=true)
    (input : CodeFrame wordR wordY E origin X Y state)
    (phase : (run F records state).phase=state.phase) :
    CodeFrame wordR wordY (E++F) origin X Y (run F records state) := by
  obtain ⟨raw,rawPhase,rawFrame,encoded⟩ := input
  have same : run F records state=run F [] state :=
    State.extensionality _ _
      (phase.trans (MeasuredCodec5.zero_phase F neutral state).symm)
      (run_basis_records F state state records [] rfl)
  refine ⟨raw,rawPhase.trans phase.symm,rawFrame,?_⟩
  rw [same,encoded,run_append]
  simp only [List.take_nil,List.drop_nil]























theorem encoded_center_instance (w : Nat→Wire) (sign : Wire) (isA : Bool)
    (origin : BasisState) (X Y : Fp) (state : State) :
    EncodedFieldFrame5 centerWord centerWord w sign isA origin X Y state ↔
      ECDSAAdd.Entrant.Rolling1588.EncodedFieldFrame5 w sign isA origin X Y state := Iff.rfl











end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAStageFrames =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


theorem route_packet_label_g (j i : Nat) (hi : i<5) :
    MeasuredCodec5.label (History5.historyMap base (5*j)) (2*i)=g j i := by
  interval_cases i <;> rfl


theorem route_packet_label_s (j i : Nat) (hi : i<5) :
    MeasuredCodec5.label (History5.historyMap base (5*j)) (2*i+1)=s j i := by
  interval_cases i <;> rfl


structure StageFacts (wordR wordY : Fp → Nat) (divide : Bool) (j k : Nat) (origin : BasisState)
    (X Y : Fp) (state : State) : Prop where
  clean : Q6EndpointCell.Clean base state.basis
  flag : state.basis (base 2409)=false
  enabled : state.basis (base 2400)=true
  rValue : regValue (balancedSharedPorts base (base 2409)).r state.basis=wordR X
  yValue : regValue (balancedSharedPorts base (base 2409)).y state.basis=wordY Y
  hole : state.basis (s j 2)=false
  active : ∀logical physical,(logical,physical)∈activeSlots divide k →
    state.basis (g j physical)=origin (g j logical) ∧
    state.basis (s j physical)=origin (s j logical)


theorem stage_frame_facts (wordR wordY : Fp → Nat) (divide : Bool) (j k : Nat) (hj : j<102) (hk : k<3)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (state : State)
    (input : CodeFrame wordR wordY (stageCodeAt divide k (History5.historyMap base (5*j))) origin X Y state) :
    StageFacts wordR wordY divide j k origin X Y state := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := input
  have domain := NewHistory5.frame_history_legal base (base 2409) ctx.hn (ctx.hp _ (by simp))
    102 (by decide) origin raw.basis _ _ ctx.legal rawFrame
  have correct := stageCodeAt_correct divide k hk (History5.historyMap base (5*j))
    (History5.historyMap_injective base base_pool_nodup (5*j) (by omega)) raw [] (domain j hj)
  have historySame (port : Fin 10) :
      raw.basis (History5.historyMap base (5*j) port)=origin (History5.historyMap base (5*j) port) :=
    rawFrame.2.2 _ (History5.history_words_away base (base 2409) ctx.hn (ctx.hp _ (by simp))
      (5*j) (by omega) port).1
      (History5.history_words_away base (base 2409) ctx.hn (ctx.hp _ (by simp))
        (5*j) (by omega) port).2
  have rawSame (q : Nat) (hq : q<10) :
      raw.basis (MeasuredCodec5.label (History5.historyMap base (5*j)) q)=
        origin (MeasuredCodec5.label (History5.historyMap base (5*j)) q) := by
    simpa only [MeasuredCodec5.label,dif_pos hq] using historySame ⟨q,hq⟩
  have dis := stageCodeAt_disjoint divide j k hj hk origin ctx
  have before (q : Wire) (off : q∉wires (stageCodeAt divide k (History5.historyMap base (5*j)))) :
      state.basis q=raw.basis q := by
    rw [encoded]
    exact run_preserves_outside _ [] raw q off
  have valuesR : regValue (balancedSharedPorts base (base 2409)).r state.basis=
      regValue (balancedSharedPorts base (base 2409)).r raw.basis := by
    apply regValue_congr
    intro q hq
    exact before q (fun used => Finset.disjoint_left.mp dis used
      (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl hq))))
  have valuesY : regValue (balancedSharedPorts base (base 2409)).y state.basis=
      regValue (balancedSharedPorts base (base 2409)).y raw.basis := by
    apply regValue_congr
    intro q hq
    exact before q (fun used => Finset.disjoint_left.mp dis used
      (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inr hq))))
  refine ⟨?_,?_,?_,valuesR.trans rawFrame.1,valuesY.trans rawFrame.2.1,?_,?_⟩
  · have originalClean := Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity
    intro q used
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp used
    have index := hi
    simp only [Q6EndpointCell.workIds,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false] at index
    have off := half_work_away (base i) (List.mem_map.mpr ⟨i,hi,rfl⟩)
    exact (before _ (stageCodeAt_free divide j k hj hk i (by omega) (by omega))).trans
      ((rawFrame.2.2 _ off.1 off.2).trans
        (originalClean _ (List.mem_map.mpr ⟨i,hi,rfl⟩)))
  · exact (before _ (stageCodeAt_free divide j k hj hk 2409 (by omega) (by omega))).trans
      ((rawFrame.2.2 _ half_flag_away.1 half_flag_away.2).trans ctx.hg0)
  · have away : base 2400∉(balancedSharedPorts base (base 2409)).r ∧
        base 2400∉(balancedSharedPorts base (base 2409)).y := by
      rw [balancedSharedPorts_r,balancedSharedPorts_y]
      exact ⟨OwnPlusHost.not_block 2400 2056 256 (by omega),
        OwnPlusHost.not_block 2400 770 256 (by omega)⟩
    exact (before _ (stageCodeAt_free divide j k hj hk 2400 (by omega) (by omega))).trans
      ((rawFrame.2.2 _ away.1 away.2).trans enabled)
  · rw [encoded]
    exact correct.2.1
  · intro logical physical used
    have bound := activeSlots_bound divide k hk (logical,physical) used
    have active := correct.2.2 logical physical used
    have a := active.1.trans (rawSame (2*logical) (by omega))
    have b := active.2.trans (rawSame (2*logical+1) (by omega))
    rw [encoded]
    simpa only [route_packet_label_g j physical bound.2,route_packet_label_s j physical bound.2,
      route_packet_label_g j logical bound.1,route_packet_label_s j logical bound.1] using And.intro a b



theorem route_raw_current_legal (wordR wordY : Fp → Nat) (j : Nat) (hj : j<102) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X Y : Fp) (raw : State)
    (frame : PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (wordR X) (wordY Y) raw.basis) :
    MeasuredCodec5.legalAt (History5.historyMap base (5*j)) raw.basis :=
  (NewHistory5.frame_history_legal base (base 2409) ctx.hn (ctx.hp _ (by simp))
    102 (by decide) origin raw.basis _ _ ctx.legal frame) j hj


theorem regular_open_frame (wordR wordY : Fp → Nat) (divide : Bool) (j : Nat) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (X Y : Fp)
    (state : State) (records : List Bool)
    (input : CodeFrame wordR wordY (codeEncodeAt divide (History5.historyMap base (5*j))) origin X Y state) :
    (run (onPacket j stageOpen) records state).phase=state.phase ∧
      CodeFrame wordR wordY (stageCodeAt divide 0 (History5.historyMap base (5*j))) origin X Y
        (run (onPacket j stageOpen) records state) := by
  obtain ⟨raw,rawPhase,rawFrame,encoded⟩ := input
  have legal := route_raw_current_legal wordR wordY j hj origin ctx X Y raw rawFrame
  have injective := History5.historyMap_injective base base_pool_nodup (5*j) (by omega)
  have actual : run (onPacket j stageOpen) records state=
      run (stageCodeAt divide 0 (History5.historyMap base (5*j))) [] raw := by
    rw [encoded]
    exact stageOpenAt_run divide _ injective raw [] records [] legal
  have phase := (congrArg State.phase actual).trans
    (stageCodeAt_correct divide 0 (by decide) _ injective raw [] legal).1
  exact ⟨phase.trans rawPhase,raw,phase.symm,rawFrame,actual⟩


theorem regular_transition_frame (wordR wordY : Fp → Nat) (divide : Bool) (j k : Nat) (hj : j<102) (hk : k<2)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (X Y : Fp)
    (state : State) (records : List Bool)
    (input : CodeFrame wordR wordY (stageCodeAt divide k (History5.historyMap base (5*j))) origin X Y state) :
    (run (onPacket j (stageTransition divide k)) records state).phase=state.phase ∧
      CodeFrame wordR wordY (stageCodeAt divide (k+1) (History5.historyMap base (5*j))) origin X Y
        (run (onPacket j (stageTransition divide k)) records state) := by
  obtain ⟨raw,rawPhase,rawFrame,encoded⟩ := input
  have legal := route_raw_current_legal wordR wordY j hj origin ctx X Y raw rawFrame
  have injective := History5.historyMap_injective base base_pool_nodup (5*j) (by omega)
  have actual : run (onPacket j (stageTransition divide k)) records state=
      run (stageCodeAt divide (k+1) (History5.historyMap base (5*j))) [] raw := by
    rw [encoded]
    exact stageTransitionAt_run divide k hk _ injective raw [] records [] legal
  have phase := (congrArg State.phase actual).trans
    (stageCodeAt_correct divide (k+1) (by omega) _ injective raw [] legal).1
  exact ⟨phase.trans rawPhase,raw,phase.symm,rawFrame,actual⟩


theorem regular_close_frame (wordR wordY : Fp → Nat) (divide : Bool) (j : Nat) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (X Y : Fp)
    (state : State) (records : List Bool)
    (input : CodeFrame wordR wordY (stageCodeAt divide 2 (History5.historyMap base (5*j))) origin X Y state) :
    (run (onPacket j stageClose) records state).phase=state.phase ∧
      CodeFrame wordR wordY (codeEncodeAt (!divide) (History5.historyMap base (5*j))) origin X Y
        (run (onPacket j stageClose) records state) := by
  obtain ⟨raw,rawPhase,rawFrame,encoded⟩ := input
  have legal := route_raw_current_legal wordR wordY j hj origin ctx X Y raw rawFrame
  have injective := History5.historyMap_injective base base_pool_nodup (5*j) (by omega)
  have actual : run (onPacket j stageClose) records state=
      run (codeEncodeAt (!divide) (History5.historyMap base (5*j))) [] raw := by
    rw [encoded]
    exact stageCloseAt_run divide _ injective raw [] records [] legal
  have phase := (congrArg State.phase actual).trans
    (codeEncodeAt_correct (!divide) _ injective raw [] legal).1
  exact ⟨phase.trans rawPhase,raw,phase.symm,rawFrame,actual⟩


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteACutFrames =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
  MappedCompressed Challenge RecordedQuantum Baselines
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


theorem cut_window_frame (wordR wordY outR outY : Fp → Nat) (beforeCut afterCut j : Nat) (hj : j<102)
    (origin : BasisState) (X Y A B : Fp) (body : Program)
    (sameOther : otherEncodeCut base beforeCut j 102=otherEncodeCut base afterCut j 102)
    (disjoint : Disjoint (wires (otherEncodeCut base beforeCut j 102)) (wires body))
    (currentLaw : ∀state records,
      CodeFrame wordR wordY (encodeGroup base (decide (beforeCut≤j)) j) origin X Y state →
      (run body records state).phase=state.phase ∧
      CodeFrame outR outY (encodeGroup base (decide (afterCut≤j)) j) origin A B (run body records state))
    (state : State) (records : List Bool) (input : CutFrame wordR wordY beforeCut origin X Y state) :
    (run body records state).phase=state.phase ∧
      CutFrame outR outY afterCut origin A B (run body records state) := by
  obtain ⟨raw,rawPhase,rawFrame,encoded⟩ := input
  let current := run (encodeGroup base (decide (beforeCut≤j)) j) [] raw
  have currentPhase : current.phase=raw.phase :=
    encodeGroup_zero_phase base (decide (beforeCut≤j)) base_pool_nodup j (by omega) raw
  have currentFrame : CodeFrame wordR wordY (encodeGroup base (decide (beforeCut≤j)) j) origin X Y current :=
    ⟨raw,currentPhase.symm,rawFrame,rfl⟩
  have result := currentLaw current records currentFrame
  obtain ⟨rawOut,outPhase,outFrame,outEncoded⟩ := result.2
  have factor := allEncodeCut_factor base beforeCut base_pool_nodup 102 j (by decide) hj raw
  have actual : run body records state=run (otherEncodeCut base beforeCut j 102) []
      (run body records current) := by
    rw [encoded,factor]
    exact (run_disjoint_commute (otherEncodeCut base beforeCut j 102) body
      disjoint [] records current).symm
  have afterFactor := allEncodeCut_factor base afterCut base_pool_nodup 102 j
    (by decide) hj rawOut
  have actualOut : run body records state=run (allEncodeCut base afterCut 102) [] rawOut := by
    rw [actual,outEncoded,sameOther,←afterFactor]
  have finalPhase : (run body records state).phase=state.phase :=
    (congrArg State.phase actual).trans
      ((otherEncodeCut_zero_phase base beforeCut j base_pool_nodup 102 (by decide) _).trans
        (result.1.trans (currentPhase.trans rawPhase)))
  refine ⟨finalPhase,rawOut,?_,outFrame,actualOut⟩
  exact ((congrArg State.phase actualOut).trans
    (allEncodeCut_zero_phase base afterCut base_pool_nodup 102 (by decide) rawOut)).symm


theorem cutFrame_one (wordR wordY : Fp → Nat) (origin : BasisState) (X Y : Fp) (state : State) :
    CutFrame wordR wordY 1 origin X Y state ↔ EncodedFieldFrame5 wordR wordY base (base 2409) true origin X Y state := by
  simp only [CutFrame,CodeFrame,EncodedFieldFrame5,allEncodeCut_one]


theorem cutFrame_end (wordR wordY : Fp → Nat) (origin : BasisState) (X Y : Fp) (state : State) :
    CutFrame wordR wordY 102 origin X Y state ↔ EncodedFieldFrame5 wordR wordY base (base 2409) false origin X Y state := by
  simp only [CutFrame,CodeFrame,EncodedFieldFrame5,allEncodeCut_end base 102 (Nat.le_refl _)]


theorem cutFrame_work_zero (wordR wordY : Fp → Nat) (cut : Nat) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X Y : Fp) (state : State)
    (frame : CutFrame wordR wordY cut origin X Y state) (q : Nat) (hq : Placement5.workRegion q) :
    state.basis (base q)=false := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have rawEnv := pair_env base (base 2409) ctx.hn origin raw.basis _ _ ctx.env rawFrame
  have zero := OffsetCleanupBorrowedCaller.maskBit_zero base raw.basis rawEnv.1 q
    (by unfold Placement5.workRegion at hq;omega) (by unfold Placement5.workRegion at hq;omega)
  have support : wires (allEncodeCut base cut 102)⊆
      (wireBlock base 0 512++wireBlock base 1028 512).toFinset := by
    rw [allEncodeCut_support_eq]
    exact NewHistory5.allEncode_history_support base 102 (by decide)
  have away : base q∉wires (allEncodeCut base cut 102) := by
    intro used
    have member := support used
    simp only [List.mem_toFinset,List.mem_append] at member
    rcases member with low|high
    · exact OwnPlusHost.not_block q 0 512 (by unfold Placement5.workRegion at hq;omega) low
    · exact OwnPlusHost.not_block q 1028 512 (by unfold Placement5.workRegion at hq;omega) high
  rw [encoded]
  exact (run_preserves_outside (allEncodeCut base cut 102) [] raw _ away).trans zero


theorem cutFrame_zero_region (wordR wordY : Fp → Nat) (cut : Nat) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X Y : Fp) (state : State)
    (frame : CutFrame wordR wordY cut origin X Y state) :
    ∀q,Placement5.zeroRegion q → state.basis (base q)=false := by
  intro q hq
  rcases hq with work|hole
  · exact cutFrame_work_zero wordR wordY cut origin ctx X Y state frame q work
  · have recover := Placement5.hole_recover q hole
    obtain ⟨raw,_,rawFrame,encoded⟩ := frame
    have rawLegal := NewHistory5.frame_history_legal base (base 2409) ctx.hn
      (ctx.hp _ (by simp)) 102 (by decide) origin raw.basis _ _ ctx.legal rawFrame
    rw [encoded,←recover.2]
    exact allEncodeCut_holes_zero base cut base_pool_nodup raw [] rawLegal _ recover.1

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteABodyFacts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


def HalfLaw (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat) : Prop :=
  ∀(origin : BasisState), Q6EndpointCell.Clean base origin → ∀X Y : Fp,
    Triple (PairFrame (Q6EndpointCell.ports base (base 2409)).r
      (Q6EndpointCell.ports base (base 2409)).y origin (wordIn X) (wordIn Y)) P
      (PairFrame (Q6EndpointCell.ports base (base 2409)).r
        (Q6EndpointCell.ports base (base 2409)).y origin
        (wordOut (if divide then (X+(if origin (base 2409) then Y else -Y))/2
          else 2*X+(if origin (base 2409) then -Y else Y))) (wordOut Y))


def HalfSupport (P : Program) : Prop :=
  wires P ⊆ (P1Life.junctionFootprint (Q6EndpointCell.ports base (base 2409))).erase (base 760)


theorem route_retired_member : base 760∈
    ((Q6EndpointCell.ports base (base 2409)).carry.take 254).drop 1 := by decide +kernel


theorem half_law (divide : Bool) :
    HalfLaw (P1Life.half (base 760) divide base (base 2409)) divide P1Life.oddWord P1Life.oddWord :=
  fun origin clean X Y => P1Life.half_frame _ _ _ _ half_ports_nodup route_retired_member origin clean X Y


theorem dstart_law :
    HalfLaw (P1Life.dstart (base 760) base (base 2409)) true centerWord P1Life.oddWord := by
  intro origin clean X Y
  simpa only [if_true] using
    P1Life.dstart_frame _ _ _ half_ports_nodup route_retired_member origin clean X Y


theorem dend_law :
    HalfLaw (P1Life.dend (base 760) base (base 2409)) true P1Life.oddWord centerWord := by
  intro origin clean X Y
  simpa only [if_true] using
    P1Life.dend_frame _ _ _ half_ports_nodup route_retired_member origin clean X Y


theorem mend_law :
    HalfLaw (P1Life.mend (base 760) base (base 2409)) false P1Life.oddWord centerWord := by
  intro origin clean X Y
  simpa only [Bool.false_eq_true,if_false] using
    P1Life.mend_frame _ _ _ half_ports_nodup route_retired_member origin clean X Y


theorem half_support (divide : Bool) : HalfSupport (P1Life.half (base 760) divide base (base 2409)) :=
  (P1Life.half_resources _ _ _ _ half_ports_nodup route_retired_member).2


theorem dstart_support : HalfSupport (P1Life.dstart (base 760) base (base 2409)) :=
  (P1Life.dstart_resources _ _ _ half_ports_nodup route_retired_member).2


theorem dend_support : HalfSupport (P1Life.dend (base 760) base (base 2409)) :=
  (P1Life.dend_resources _ _ _ half_ports_nodup route_retired_member).2


theorem mend_support : HalfSupport (P1Life.mend (base 760) base (base 2409)) :=
  (P1Life.mend_resources _ _ _ half_ports_nodup route_retired_member).2


theorem body_history_gap_free (P : Program) (support : HalfSupport P) (i : Nat)
    (history : i < 512 ∨ (1028 ≤ i ∧ i < 1538)) : base i∉wires P := by
  intro used
  have member := Finset.mem_of_mem_erase (support used)
  rw [P1Life.junction_footprint_ports] at member
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_singleton,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with eq|eq|eq|eq|reg|reg|bank|eq
  · have := base_injective eq; omega
  · have := base_injective eq; omega
  · have := base_injective eq; omega
  · have := base_injective eq; omega
  · exact OwnPlusHost.not_block i 2056 256 (by omega) reg
  · exact OwnPlusHost.not_block i 770 256 (by omega) reg
  · exact OwnPlusHost.not_block i 512 253 (by omega) bank
  · have := base_injective eq; omega


theorem body_history_free (P : Program) (support : HalfSupport P) (i : Nat)
    (history : i < 510 ∨ (1028 ≤ i ∧ i < 1538)) : base i∉wires P :=
  body_history_gap_free P support i (by
    rcases history with low|high
    · exact Or.inl (by omega)
    · exact Or.inr high)


theorem route_numeric_away (q : Nat) (hr : q<2056 ∨ 2312≤q) (hy : q<770 ∨ 1026≤q) :
    base q∉(Q6EndpointCell.ports base (base 2409)).r ∧
      base q∉(Q6EndpointCell.ports base (base 2409)).y := by
  rw [Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y]
  exact ⟨OwnPlusHost.not_block q 2056 256 (by omega),OwnPlusHost.not_block q 770 256 (by omega)⟩


theorem route_cell_controls (j active : Nat) (hj : j<102) (ha : active<5) :
    [base 2400,g j active,base 2409].Nodup ∧ [base 2400,s j active,base 2409].Nodup := by
  have old := FrontierSW1591.selLetter_nodup (5*j+active) (by omega)
  simpa only [g,s,tapeLetter,mixedTape_base_getD (5*j+active) (by omega),Nat.add_assoc] using old


theorem route_flag_not_work : base 2409∉Q6EndpointCell.workIds.map base := by
  intro used
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp used
  have same := base_injective eq
  have bound := Q6EndpointCell.work_bound i hi
  omega

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAHalfLoan =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


theorem halfWindowWith_selected_eq_of_bound (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat)
    (law : HalfLaw P divide wordIn wordOut) (support : HalfSupport P) (j active hole : Nat)
    (hj : j<102) (activeBound : 5*j+active < 512) (hh : hole<5) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (rValue : regValue (balancedSharedPorts base (base 2409)).r state.basis=wordIn X)
    (yValue : regValue (balancedSharedPorts base (base 2409)).y state.basis=wordIn Y)
    (flagIn : state.basis (base 2409)=false) (holeIn : state.basis (s j hole)=false) :
    run (halfWindowWith P j active hole) records state=
      run (SW.selW (g j active) (base 2409)
        P) records state := by
  let copied := run [.CX (g j active) (base 2409)] [] state
  let original := P
  let fresh := P
  let rebound := renameProgram (Equiv.swap (base 719) (s j hole)) fresh
  have holeBound : 1028+5*j+hole<1538 := by omega
  have holeFlag : s j hole≠base 2409 :=
    HostOB5.host_ne _ _ (by omega)
  have holeFree : s j hole∉wires fresh :=
    body_history_free P support _ (Or.inr ⟨by omega,holeBound⟩)
  have copiedHole : copied.basis (s j hole)=false := by
    simpa only [copied,run,writeBit,Function.update_of_ne holeFlag] using holeIn
  have copiedClean := copied_work_clean (g j active) state clean
  have copiedFrame := copied_self_frame (g j active) state
    (wordIn X) (wordIn Y) rValue yValue
  have freshEq (m : List Bool) : run fresh m copied=run original m copied := rfl
  have member719 : base 719∈Q6EndpointCell.workIds.map base :=
    List.mem_map.mpr ⟨719,by simp [Q6EndpointCell.workIds,List.mem_range'_1],rfl⟩
  have away719 := half_work_away _ member719
  have bodyEq : ∀m,run rebound m copied=run original m copied := by
    intro m
    have result := law copied.basis copiedClean X Y copied m copiedFrame
    have after : (run fresh m copied).basis (base 719)=false := by
      rw [freshEq m]
      exact (result.2.2.2 _ (by simpa only [Q6EndpointCell.ports_r] using away719.1)
        (by simpa only [Q6EndpointCell.ports_y] using away719.2)).trans (copiedClean _ member719)
    exact (NewFieldFrameOB5.rebind_swap_run _ _ _ copied m (copiedClean _ member719) copiedHole after
      ((run_preserves_outside _ m copied _ holeFree).trans copiedHole)).trans (freshEq m)
  have oldResult := law copied.basis copiedClean X Y copied records copiedFrame
  have carryMember := packetCarry_mem_work j hj
  have carryAway := half_work_away _ carryMember
  have keep : (run rebound records copied).basis (base 2409)=copied.basis (base 2409) := by
    rw [bodyEq]
    exact oldResult.2.2.2 _
      (by simpa only [Q6EndpointCell.ports_r] using half_flag_away.1)
      (by simpa only [Q6EndpointCell.ports_y] using half_flag_away.2)
  have carryOut : (run rebound records copied).basis (packetCarry j)=false := by
    rw [bodyEq]
    exact (oldResult.2.2.2 _
      (by simpa only [Q6EndpointCell.ports_r] using carryAway.1)
      (by simpa only [Q6EndpointCell.ports_y] using carryAway.2)).trans
        (copiedClean _ carryMember)
  have activeFree : g j active∉wires rebound := by
    change g j active∉wires (renameProgram (Equiv.swap (base 719) (s j hole)) fresh)
    rw [renameProgram_support]
    intro used
    obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp used
    have fix : Equiv.swap (base 719) (s j hole) (g j active)=g j active :=
      Equiv.swap_apply_of_ne_of_ne
        (HostOB5.host_ne _ _ (by omega)) (HostOB5.host_ne _ _ (by omega))
    have same := (Equiv.swap (base 719) (s j hole)).injective (eq.trans fix.symm)
    have noG : g j active∉wires fresh := body_history_gap_free P support _ (Or.inl activeBound)
    apply noG
    rw [←same]
    exact hq
  have gf : g j active≠base 2409 := HostOB5.host_ne _ _ (by omega)
  have cg : packetCarry j≠g j active := HostOB5.host_ne _ _ (by omega)
  have cf : packetCarry j≠base 2409 := HostOB5.host_ne _ _ (by omega)
  have loan := ControlLoan1589.loanWindow_eq (g j active) (base 2409) (packetCarry j)
    rebound state records gf cg cf activeFree flagIn (clean _ carryMember) keep carryOut
  have loanEq : run (halfWindowWith P j active hole) records state=
      run (SW.selW (g j active) (base 2409) rebound) records state := loan
  rw [loanEq]
  have headCount : measurementCount [.CX (g j active) (base 2409)]=0 := rfl
  simp only [SW.selW,List.append_assoc,run_append,headCount,List.take_zero,
    List.drop_zero,run_take]
  rw [show measurementCount rebound=measurementCount original from
    (renameProgram_counts (Equiv.swap (base 719) (s j hole)) P).2]
  rw [show run rebound records (run [.CX (g j active) (base 2409)] [] state)=
    run original records (run [.CX (g j active) (base 2409)] [] state) from bodyEq records]



theorem halfWindowWith_selected_eq (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat)
    (law : HalfLaw P divide wordIn wordOut) (support : HalfSupport P) (j active hole : Nat)
    (hj : j<102) (ha : active<5) (hh : hole<5) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (rValue : regValue (balancedSharedPorts base (base 2409)).r state.basis=wordIn X)
    (yValue : regValue (balancedSharedPorts base (base 2409)).y state.basis=wordIn Y)
    (flagIn : state.basis (base 2409)=false) (holeIn : state.basis (s j hole)=false) :
    run (halfWindowWith P j active hole) records state=
      run (SW.selW (g j active) (base 2409)
        P) records state := by
  exact halfWindowWith_selected_eq_of_bound P divide wordIn wordOut law support j active hole hj
    (by omega) hh X Y state records clean rValue yValue flagIn holeIn

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteASelected =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


theorem body_enable_free (P : Program) (support : HalfSupport P) : base 2400∉wires P := by
  intro used
  have member := Finset.mem_of_mem_erase (support used)
  rw [P1Life.junction_footprint_ports] at member
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_singleton,
    List.not_mem_nil,or_false,or_assoc] at member
  rcases member with eq|eq|eq|eq|reg|reg|bank|eq
  · have := base_injective eq; omega
  · have := base_injective eq; omega
  · have := base_injective eq; omega
  · have := base_injective eq; omega
  · exact OwnPlusHost.not_block 2400 2056 256 (by omega) reg
  · exact OwnPlusHost.not_block 2400 770 256 (by omega) reg
  · exact OwnPlusHost.not_block 2400 512 253 (by omega) bank
  · have := base_injective eq; omega


theorem selected_half_frame_of_bound (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat)
    (law : HalfLaw P divide wordIn wordOut) (support : HalfSupport P)
    (j active : Nat) (activeBound : 5*j+active < 512) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (enabled : state.basis (base 2400)=true) (flagIn : state.basis (base 2409)=false)
    (rValue : regValue fieldR state.basis=wordIn X) (yValue : regValue fieldY state.basis=wordIn Y) :
    (run (SW.selW (g j active) (base 2409) P) records state).phase=state.phase ∧
    PairFrame fieldR fieldY state.basis
      (wordOut (if divide then (X+(if state.basis (g j active) then Y else -Y))/2
        else 2*X+(if state.basis (g j active) then -Y else Y))) (wordOut Y)
      (run (SW.selW (g j active) (base 2409) P) records state).basis := by
  have controls : [base 2400,g j active,base 2409].Nodup := by
    have a : base 2400≠g j active := HostOB5.host_ne _ _ (by omega)
    have b : base 2400≠base 2409 := by decide
    have c : g j active≠base 2409 := HostOB5.host_ne _ _ (by omega)
    simp [List.nodup_cons,a,b,c]
  let origin := mixedTranscriptBase state.basis (base 2400) (g j active) (base 2409) false
  have cl : Q6EndpointCell.Clean base origin := by
    intro q hq
    have ne : q≠base 2409 := fun e => route_flag_not_work (e ▸ hq)
    simpa only [origin,mixedTranscriptBase,writeBit,Function.update_of_ne ne] using clean q hq
  have body := law origin cl X Y
  simp only [origin,mixedTranscriptBase,writeBit,Function.update_self] at body
  have proof := transcriptSelectWindow_pairFrame (base 2400) (g j active) (base 2409) false
    (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y
    controls
    (route_numeric_away 2400 (by omega) (by omega))
    (route_numeric_away (5*j+active) (by omega) (by omega))
    (route_numeric_away 2409 (by omega) (by omega)) state.basis flagIn _ _ _ _ P body
  have selected := (SW.Sel.refl (base 2400) P (body_enable_free P support)).window
    (g j active) (base 2409) false controls
  rw [(selected.eq records state enabled).1]
  simpa only [Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,mixedTranscriptBit,enabled,if_true]
    using proof state records ⟨rValue,yValue,fun _ _ _ => rfl⟩



theorem selected_half_frame (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat)
    (law : HalfLaw P divide wordIn wordOut) (support : HalfSupport P)
    (j active : Nat) (hj : j<102) (ha : active<5) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (enabled : state.basis (base 2400)=true) (flagIn : state.basis (base 2409)=false)
    (rValue : regValue fieldR state.basis=wordIn X) (yValue : regValue fieldY state.basis=wordIn Y) :
    (run (SW.selW (g j active) (base 2409) P) records state).phase=state.phase ∧
    PairFrame fieldR fieldY state.basis
      (wordOut (if divide then (X+(if state.basis (g j active) then Y else -Y))/2
        else 2*X+(if state.basis (g j active) then -Y else Y))) (wordOut Y)
      (run (SW.selW (g j active) (base 2409) P) records state).basis := by
  exact selected_half_frame_of_bound P divide wordIn wordOut law support j active (by omega) X Y
    state records clean enabled flagIn rValue yValue


theorem halfWindowWith_frame (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat)
    (law : HalfLaw P divide wordIn wordOut) (support : HalfSupport P)
    (j active hole : Nat) (hj : j<102) (ha : active<5) (hh : hole<5) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (enabled : state.basis (base 2400)=true) (flagIn : state.basis (base 2409)=false)
    (rValue : regValue fieldR state.basis=wordIn X) (yValue : regValue fieldY state.basis=wordIn Y)
    (holeIn : state.basis (s j hole)=false) :
    (run (halfWindowWith P j active hole) records state).phase=state.phase ∧
    PairFrame fieldR fieldY state.basis
      (wordOut (if divide then (X+(if state.basis (g j active) then Y else -Y))/2
        else 2*X+(if state.basis (g j active) then -Y else Y))) (wordOut Y)
      (run (halfWindowWith P j active hole) records state).basis := by
  rw [halfWindowWith_selected_eq P divide wordIn wordOut law support j active hole hj ha hh X Y
    state records clean rValue yValue flagIn holeIn]
  exact selected_half_frame P divide wordIn wordOut law support j active hj ha X Y
    state records clean enabled flagIn rValue yValue



theorem halfWindowWith_frame_of_bound (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat)
    (law : HalfLaw P divide wordIn wordOut) (support : HalfSupport P)
    (j active hole : Nat) (hj : j<102) (activeBound : 5*j+active < 512) (hh : hole<5) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (enabled : state.basis (base 2400)=true) (flagIn : state.basis (base 2409)=false)
    (rValue : regValue fieldR state.basis=wordIn X) (yValue : regValue fieldY state.basis=wordIn Y)
    (holeIn : state.basis (s j hole)=false) :
    (run (halfWindowWith P j active hole) records state).phase=state.phase ∧
    PairFrame fieldR fieldY state.basis
      (wordOut (if divide then (X+(if state.basis (g j active) then Y else -Y))/2
        else 2*X+(if state.basis (g j active) then -Y else Y))) (wordOut Y)
      (run (halfWindowWith P j active hole) records state).basis := by
  rw [halfWindowWith_selected_eq_of_bound P divide wordIn wordOut law support j active hole hj activeBound hh X Y
    state records clean rValue yValue flagIn holeIn]
  exact selected_half_frame_of_bound P divide wordIn wordOut law support j active activeBound X Y
    state records clean enabled flagIn rValue yValue


theorem selected_swap_frame (word : Fp → Nat) (j active : Nat) (hj : j<102) (ha : active<5)
    (X Y : Fp) (state : State) (records : List Bool)
    (enabled : state.basis (base 2400)=true) (flagIn : state.basis (base 2409)=false)
    (rValue : regValue fieldR state.basis=word X) (yValue : regValue fieldY state.basis=word Y) :
    (run (SW.selW (s j active) (base 2409) FrontierSW1591.swapBody) records state).phase=state.phase ∧
    PairFrame fieldR fieldY state.basis
      (word (if state.basis (s j active) then Y else X))
      (word (if state.basis (s j active) then X else Y))
      (run (SW.selW (s j active) (base 2409) FrontierSW1591.swapBody) records state).basis := by
  let origin := mixedTranscriptBase state.basis (base 2400) (s j active) (base 2409) false
  let L := Q6EndpointCell.ports base (base 2409)
  have len := BalancedCleanup.widths L.toLayout (Q6EndpointCell.ports_widths base (base 2409))
  have body := OneFlagCell.swap_frame L.r L.y (base 2409)
    (len.2.1.trans len.2.2.1.symm) FrontierReplay1591.base_sign_nd origin (word X) (word Y)
  have flagval : origin (base 2409)=mixedTranscriptBit state.basis (base 2400) (s j active) false := by
    simp only [origin,mixedTranscriptBase,writeBit,Function.update_self]
  rw [flagval] at body
  have proof := transcriptSelectWindow_pairFrame (base 2400) (s j active) (base 2409) false L.r L.y
    (route_cell_controls j active hj ha).2
    (route_numeric_away 2400 (by omega) (by omega))
    (route_numeric_away (1028+5*j+active) (by omega) (by omega))
    (route_numeric_away 2409 (by omega) (by omega)) state.basis flagIn _ _ _ _ _ body
  have selected := (SW.Sel.refl (base 2400) FrontierSW1591.swapBody
    FrontierSW1591.selSwap_away).window (s j active) (base 2409) false
    (route_cell_controls j active hj ha).2
  rw [(selected.eq records state enabled).1]
  have result := proof state records ⟨rValue,yValue,fun _ _ _ => rfl⟩
  cases e : state.basis (s j active) <;>
    simpa only [L,FrontierSW1591.swapBody,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,
      mixedTranscriptBit,enabled,e,if_true,Bool.false_eq_true,if_false] using result

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteACell =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


theorem route_pair_compose (a b : BasisState) (x y u v : Nat) (c : BasisState)
    (before : PairFrame fieldR fieldY a x y b) (after : PairFrame fieldR fieldY b u v c) :
    PairFrame fieldR fieldY a u v c :=
  ⟨after.1,after.2.1,fun q qr qy => (after.2.2 q qr qy).trans (before.2.2 q qr qy)⟩


theorem route_pair_numeric (a b : BasisState) (x y : Nat) (h : PairFrame fieldR fieldY a x y b)
    (q : Nat) (hr : q<2056 ∨ 2312≤q) (hy : q<770 ∨ 1026≤q) : b (base q)=a (base q) :=
  h.2.2 _ (by simpa only [Q6EndpointCell.ports_r] using (route_numeric_away q hr hy).1)
    (by simpa only [Q6EndpointCell.ports_y] using (route_numeric_away q hr hy).2)


theorem route_pair_clean (a b : BasisState) (x y : Nat) (h : PairFrame fieldR fieldY a x y b)
    (clean : Q6EndpointCell.Clean base a) : Q6EndpointCell.Clean base b := by
  intro q used
  have off := half_work_away q used
  exact (h.2.2 q off.1 off.2).trans (clean q used)


theorem cellWith_frame (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat)
    (law : HalfLaw P divide wordIn wordOut) (support : HalfSupport P)
    (j active hole : Nat) (hj : j<102) (ha : active<5) (hh : hole<5) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (enabled : state.basis (base 2400)=true) (flagIn : state.basis (base 2409)=false)
    (rValue : regValue fieldR state.basis=wordIn X) (yValue : regValue fieldY state.basis=wordIn Y)
    (holeIn : state.basis (s j hole)=false) :
    (run (cellWith divide P j active hole) records state).phase=state.phase ∧
    PairFrame fieldR fieldY state.basis
      (wordOut (Q6EndpointCell.payload divide (state.basis (g j active)) (state.basis (s j active)) (X,Y)).1)
      (wordOut (Q6EndpointCell.payload divide (state.basis (g j active)) (state.basis (s j active)) (X,Y)).2)
      (run (cellWith divide P j active hole) records state).basis := by
  cases divide
  · let head := SW.selW (s j active) (base 2409) FrontierSW1591.swapBody
    let before := run head (records.take (measurementCount head)) state
    let A : Fp := if state.basis (s j active) then Y else X
    let B : Fp := if state.basis (s j active) then X else Y
    have swapped := selected_swap_frame wordIn j active hj ha X Y state
      (records.take (measurementCount head)) enabled flagIn rValue yValue
    have same (q : Nat) (hr : q<2056 ∨ 2312≤q) (hy : q<770 ∨ 1026≤q) :
        before.basis (base q)=state.basis (base q) := route_pair_numeric _ _ _ _ swapped.2 q hr hy
    have result := halfWindowWith_frame P false wordIn wordOut law support j active hole hj ha hh A B before
      (records.drop (measurementCount head)) (route_pair_clean _ _ _ _ swapped.2 clean)
      ((same 2400 (by omega) (by omega)).trans enabled)
      ((same 2409 (by omega) (by omega)).trans flagIn) swapped.2.1 swapped.2.2.1
      ((same (1028+5*j+hole) (by omega) (by omega)).trans holeIn)
    have composed := route_pair_compose _ _ _ _ _ _ _ swapped.2 result.2
    have gSame : before.basis (g j active)=state.basis (g j active) := same _ (by omega) (by omega)
    simp only [cellWith,Bool.false_eq_true,if_false,run_append]
    refine ⟨result.1.trans swapped.1,?_⟩
    cases e : state.basis (s j active) <;>
      simpa only [Q6EndpointCell.payload,skywalkPayloadUncell,Bool.false_eq_true,if_false,
        if_true,A,B,gSame,e] using composed
  · let head := halfWindowWith P j active hole
    let before := run head (records.take (measurementCount head)) state
    let A : Fp := (X+(if state.basis (g j active) then Y else -Y))/2
    have first := halfWindowWith_frame P true wordIn wordOut law support j active hole hj ha hh X Y state
      (records.take (measurementCount head)) clean enabled flagIn rValue yValue holeIn
    have same (q : Nat) (hr : q<2056 ∨ 2312≤q) (hy : q<770 ∨ 1026≤q) :
        before.basis (base q)=state.basis (base q) := route_pair_numeric _ _ _ _ first.2 q hr hy
    have result := selected_swap_frame wordOut j active hj ha A Y before
      (records.drop (measurementCount head))
      ((same 2400 (by omega) (by omega)).trans enabled)
      ((same 2409 (by omega) (by omega)).trans flagIn) first.2.1 first.2.2.1
    have composed := route_pair_compose _ _ _ _ _ _ _ first.2 result.2
    have sSame : before.basis (s j active)=state.basis (s j active) := same _ (by omega) (by omega)
    rw [cellWith,if_pos rfl,run_append]
    refine ⟨result.1.trans first.1,?_⟩
    cases e : state.basis (s j active) <;>
      simpa only [Q6EndpointCell.payload,skywalkPayloadCell,if_true,A,sSame,e,
        Bool.false_eq_true,if_false] using composed



















end ECDSAAdd.Entrant.RouteA.Rolling1588

#print axioms ECDSAAdd.Entrant.RouteA.Rolling1588.cellWith_frame

end -- ticket 8 pasted module

-- ===== RouteARegularCell =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


theorem regular_cellWith_frame (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat)
    (law : HalfLaw P divide wordIn wordOut) (support : HalfSupport P) (j k logical physical : Nat)
    (hj : j<102) (hk : k<3) (used : (logical,physical)∈activeSlots divide k)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (state : State) (records : List Bool)
    (input : CodeFrame wordIn wordIn (stageCodeAt divide k (History5.historyMap base (5*j))) origin X Y state) :
    let V := Q6EndpointCell.payload divide (origin (g j logical)) (origin (s j logical)) (X,Y)
    (run (cellWith divide P j physical 2) records state).phase=state.phase ∧
      CodeFrame wordOut wordOut (stageCodeAt divide k (History5.historyMap base (5*j))) origin V.1 V.2
        (run (cellWith divide P j physical 2) records state) := by
  have facts := stage_frame_facts wordIn wordIn divide j k hj hk origin ctx enabled X Y state input
  have bounds := activeSlots_bound divide k hk (logical,physical) used
  have result := cellWith_frame P divide wordIn wordOut law support j physical 2 hj bounds.2 (by decide) X Y state records
    facts.clean facts.enabled facts.flag facts.rValue facts.yValue facts.hole
  have controls := facts.active logical physical used
  rw [controls.1,controls.2] at result
  refine ⟨result.1,?_⟩
  exact CodeFrame.arithmetic_step wordIn wordIn wordOut wordOut _ origin X Y _ _ state _
    (stageCodeAt_neutral divide k hk _) (stageCodeAt_disjoint divide j k hj hk origin ctx)
    input result.1 result.2



theorem regular_cell_frame (divide : Bool) (j k logical physical : Nat)
    (hj : j<102) (hk : k<3) (used : (logical,physical)∈activeSlots divide k)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (state : State) (records : List Bool)
    (input : CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt divide k (History5.historyMap base (5*j))) origin X Y state) :
    let V := Q6EndpointCell.payload divide (origin (g j logical)) (origin (s j logical)) (X,Y)
    (run (cell divide j physical 2) records state).phase=state.phase ∧
      CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt divide k (History5.historyMap base (5*j))) origin V.1 V.2
        (run (cell divide j physical 2) records state) := by
  have shape : cell divide j physical 2=cellWith divide (P1Life.half (base 760) divide base (base 2409)) j physical 2 := by
    cases divide <;> rfl
  rw [shape]
  exact regular_cellWith_frame _ divide _ _ (half_law divide) (half_support divide)
    j k logical physical hj hk used origin ctx enabled X Y state records input

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteARegularPacket =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


theorem basePacket_frame (divide : Bool) (j : Nat) (hj : j<102) (regular : divide=true → j≠84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt divide (History5.historyMap base (5*j))) origin X Y)
      (basePacket divide j)
      (fun state => let V := regularPayload divide j origin (X,Y)
        CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt (!divide) (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  let Frame (d : Bool) (k : Nat) (V : Fp×Fp) :=
    CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt d k (History5.historyMap base (5*j))) origin V.1 V.2
  have opening (d : Bool) (V : Fp×Fp) : StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt d (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageOpen) (Frame d 0 V) := by
    intro state records input
    exact regular_open_frame P1Life.oddWord P1Life.oddWord d j hj origin ctx V.1 V.2 state records input
  have step (d : Bool) (k logical physical : Nat) (hk : k<3)
      (used : (logical,physical)∈activeSlots d k) (V : Fp×Fp) :
      StateTriple (Frame d k V) (cell d j physical 2)
        (Frame d k (regularStep d j origin logical V)) := by
    intro state records input
    exact regular_cell_frame d j k logical physical hj hk used origin ctx enabled
      V.1 V.2 state records input
  have transfer (d : Bool) (k : Nat) (hk : k<2) (V : Fp×Fp) :
      StateTriple (Frame d k V) (onPacket j (stageTransition d k)) (Frame d (k+1) V) := by
    intro state records input
    exact regular_transition_frame P1Life.oddWord P1Life.oddWord d j k hj hk origin ctx V.1 V.2 state records input
  have closing (d : Bool) (V : Fp×Fp) : StateTriple (Frame d 2 V)
      (onPacket j stageClose)
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt (!d) (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_close_frame P1Life.oddWord P1Life.oddWord d j hj origin ctx V.1 V.2 state records input
  cases divide
  · let V1 := regularStep false j origin 4 (X,Y)
    let V2 := regularStep false j origin 3 V1
    let V3 := regularStep false j origin 2 V2
    let V4 := regularStep false j origin 1 V3
    let V5 := regularStep false j origin 0 V4
    have result := (opening false (X,Y)).seq
      ((step false 0 4 4 (by decide) (by decide) (X,Y)).seq
      ((transfer false 0 (by decide) V1).seq
      ((step false 1 3 3 (by decide) (by decide) V1).seq
      ((step false 1 2 4 (by decide) (by decide) V2).seq
      ((transfer false 1 (by decide) V3).seq
      ((step false 2 1 4 (by decide) (by decide) V3).seq
      ((step false 2 0 3 (by decide) (by decide) V4).seq (closing false V5))))))))
    simpa only [basePacket,stageOpen,stageClose,stageTransition,regularPayload,
      Bool.false_eq_true,if_false,if_true,show ¬(1:Nat)=0 from by decide,List.append_assoc] using result
  · have nonterminal : j≠84 := regular rfl
    let V1 := regularStep true j origin 0 (X,Y)
    let V2 := regularStep true j origin 1 V1
    let V3 := regularStep true j origin 2 V2
    let V4 := regularStep true j origin 3 V3
    let V5 := regularStep true j origin 4 V4
    have result := (opening true (X,Y)).seq
      ((step true 0 0 3 (by decide) (by decide) (X,Y)).seq
      ((step true 0 1 4 (by decide) (by decide) V1).seq
      ((transfer true 0 (by decide) V2).seq
      ((step true 1 2 4 (by decide) (by decide) V2).seq
      ((step true 1 3 3 (by decide) (by decide) V3).seq
      ((transfer true 1 (by decide) V4).seq
      ((step true 2 4 4 (by decide) (by decide) V4).seq (closing true V5))))))))
    simpa only [basePacket,stageOpen,stageClose,stageTransition,regularPayload,
      if_true,if_false,if_neg nonterminal,show ¬(1:Nat)=0 from by decide,List.append_assoc] using result



theorem basePacket_replay_frame (divide : Bool) (j : Nat) (hj : j<102) (regular : divide=true → j≠84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt divide (History5.historyMap base (5*j))) origin X Y)
      (basePacket divide j)
      (fun state => let V := directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt (!divide) (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  simpa only [regularPayload_eq divide j hj origin enabled] using
    basePacket_frame divide j hj regular origin ctx enabled X Y

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteASupport =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires


theorem route_fieldIds_read (j : Nat) :
    (base 2409::Q6EndpointCell.ids.map base).toFinset⊆FrontierReplay1591.readSites (5*j) :=
  fun _ used => Finset.mem_union_left _ (Finset.mem_union_left _ used)


theorem route_id_read (j i : Nat) (used : i∈Q6EndpointCell.ids) :
    base i∈FrontierReplay1591.readSites (5*j) :=
  route_fieldIds_read j (List.mem_toFinset.mpr
    (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,used,rfl⟩)))


theorem route_flag_read (j : Nat) : base 2409∈FrontierReplay1591.readSites (5*j) :=
  route_fieldIds_read j (by simp)


theorem route_history_read (j active : Nat) (ha : active<5) :
    g j active∈FrontierReplay1591.readSites (5*j) ∧
      s j active∈FrontierReplay1591.readSites (5*j) := by
  have controls := Replay5.history_controls (5*j) active ha
  rw [←NewHistory5.encode_support_eq] at controls
  exact ⟨Finset.mem_union_right _ controls.1,Finset.mem_union_right _ controls.2⟩


theorem route_selected_read_support (source flag : Wire) (P : Program) (W : Finset Wire)
    (sourceIn : source∈W) (flagIn : flag∈W) (body : wires P⊆W) :
    wires (SW.selW source flag P)⊆W := by
  simpa [SW.selW,wires_append,wires,Instr.wires,correctionWires,
    Finset.union_subset_iff,Finset.insert_subset_iff,sourceIn,flagIn] using body


theorem route_rename_swap_support (P : Program) (a b : Wire) (W : Finset Wire)
    (old : wires P⊆W) (ha : a∈W) (hb : b∈W) :
    wires (renameProgram (Equiv.swap a b) P)⊆W := by
  rw [renameProgram_support]
  intro q used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp used
  by_cases sameA : i=a
  · subst i
    simpa only [Equiv.swap_apply_left] using hb
  · by_cases sameB : i=b
    · subst i
      simpa only [Equiv.swap_apply_right] using ha
    · simpa only [Equiv.swap_apply_of_ne_of_ne sameA sameB] using old hi



theorem body_ids_support (P : Program) (support : HalfSupport P) :
    wires P⊆(base 2409::Q6EndpointCell.ids.map base).toFinset := by
  intro q used
  have member := Finset.mem_of_mem_erase (support used)
  rw [P1Life.junction_footprint_ports] at member
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_singleton,
    List.not_mem_nil,or_false,or_assoc] at member
  have block (lo n : Nat) (range : ∀i, lo ≤ i → i < lo+n → i∈Q6EndpointCell.ids)
      (h : q∈wireBlock base lo n) : q∈(base 2409::Q6EndpointCell.ids.map base).toFinset := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    have bounds := List.mem_range'_1.mp hi
    exact List.mem_toFinset.mpr (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨i,range i bounds.1 bounds.2,rfl⟩))
  rcases member with rfl|rfl|rfl|rfl|reg|reg|bank|rfl
  · exact List.mem_toFinset.mpr (List.mem_cons_self)
  · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨768,by decide +kernel,rfl⟩))
  · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨1797,by decide +kernel,rfl⟩))
  · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨1027,by decide +kernel,rfl⟩))
  · apply block 2056 256 _ reg
    intro i low high
    simp only [Q6EndpointCell.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false]
    omega
  · apply block 770 256 _ reg
    intro i low high
    simp only [Q6EndpointCell.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false]
    omega
  · apply block 512 253 _ bank
    intro i low high
    simp only [Q6EndpointCell.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false]
    omega
  · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨1540,by decide +kernel,rfl⟩))




theorem halfWindowWith_read_support (P : Program) (support : HalfSupport P) (j active hole : Nat)
    (hj : j<102) (ha : active<5) (hh : hole<5) :
    wires (halfWindowWith P j active hole)⊆FrontierReplay1591.readSites (5*j) := by
  let W := FrontierReplay1591.readSites (5*j)
  let rebound := renameProgram (Equiv.swap (base 719) (s j hole)) P
  have raw : wires P⊆W := (body_ids_support P support).trans (route_fieldIds_read j)
  have carry719 : base 719∈W := route_id_read j 719 (by
    simp only [Q6EndpointCell.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false]
    omega)
  have carry : packetCarry j∈W := route_id_read j (516+2*j) (by
    simp only [Q6EndpointCell.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false]
    omega)
  have source := (route_history_read j active ha).1
  have rebind : wires rebound⊆W := route_rename_swap_support P
    (base 719) (s j hole) W raw carry719 (route_history_read j hole hh).2
  have loanBody : (wires rebound).image (Equiv.swap (packetCarry j) (g j active))⊆W := by
    rw [←renameProgram_support]
    exact route_rename_swap_support rebound (packetCarry j) (g j active)
      W rebind carry source
  intro q used
  rcases Finset.mem_union.mp
      (ControlLoan1589.loanWindow_support (g j active) (base 2409) (packetCarry j) rebound used)
      with edge|body
  · simp only [Finset.mem_insert,Finset.mem_singleton] at edge
    rcases edge with rfl|rfl
    · exact source
    · exact route_flag_read j
  · exact loanBody body



theorem cellWith_read_support (divide : Bool) (P : Program) (support : HalfSupport P) (j active hole : Nat)
    (hj : j<102) (ha : active<5) (hh : hole<5) :
    wires (cellWith divide P j active hole)⊆FrontierReplay1591.readSites (5*j) := by
  let W := FrontierReplay1591.readSites (5*j)
  have swap : wires FrontierSW1591.swapBody⊆W := by
    have old : wires FrontierSW1591.swapBody⊆
        wires (Q6EndpointCell.body true base (base 2409) (base 2409)) := by
      simp only [FrontierSW1591.swapBody,Q6EndpointCell.body,if_true,wires_append,
        Q6EndpointCell.ports_r,Q6EndpointCell.ports_y]
      exact Finset.subset_union_right
    exact old.trans (Q6EndpointCell.body_support true base (base 2409) (base 2409) W
      (route_fieldIds_read j) (route_flag_read j))
  have selected := route_selected_read_support (s j active) (base 2409) FrontierSW1591.swapBody W
    (route_history_read j active ha).2 (route_flag_read j) swap
  have half := halfWindowWith_read_support P support j active hole hj ha hh
  cases divide <;> simp only [cellWith,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.union_subset_iff] at half ⊢
  · exact ⟨selected,half⟩
  · exact ⟨half,selected⟩




theorem cell_read_support (divide : Bool) (j active hole : Nat)
    (hj : j<102) (ha : active<5) (hh : hole<5) :
    wires (cell divide j active hole)⊆FrontierReplay1591.readSites (5*j) := by
  have shape : cell divide j active hole=cellWith divide (P1Life.half (base 760) divide base (base 2409)) j active hole := by
    cases divide <;> rfl
  rw [shape]
  exact cellWith_read_support divide _ (half_support divide) j active hole hj ha hh



theorem basePacket_readSites_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (basePacket divide j)⊆FrontierReplay1591.readSites (5*j) := by
  have opening := onPacket_read_support j stageOpen stageOpen_support
  have closing := onPacket_read_support j stageClose stageClose_support
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_read_support j (stageTransition d k) (stageTransition_support d k hk)
  have cellAt (d : Bool) (active : Nat) (ha : active<5) :=
    cell_read_support d j active 2 hj ha (by decide)
  have last := cellWith_read_support true _ dend_support j 4 2 hj (by decide) (by decide)
  cases divide
  · simp only [basePacket,Bool.false_eq_true,if_false,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨cellAt false 4 (by decide),transfer false 0 (by decide)⟩,
      cellAt false 3 (by decide)⟩,cellAt false 4 (by decide)⟩,transfer false 1 (by decide)⟩,
      cellAt false 4 (by decide)⟩,cellAt false 3 (by decide)⟩⟩,closing⟩
  · have ending : wires (if j=84 then cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2
        else cell true j 4 2)⊆FrontierReplay1591.readSites (5*j) := by
      by_cases terminal : j=84
      · rw [if_pos terminal]; exact last
      · rw [if_neg terminal]; exact cellAt true 4 (by decide)
    simp only [basePacket,if_true,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨cellAt true 3 (by decide),cellAt true 4 (by decide)⟩,
      transfer true 0 (by decide)⟩,cellAt true 4 (by decide)⟩,cellAt true 3 (by decide)⟩,
      transfer true 1 (by decide)⟩,ending⟩⟩,closing⟩




theorem basePacket_read_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (basePacket divide j)⊆NewHistory5.groupReadSites base (base 2400)
      (base 2409) (base 2410) (5*j) ∪ {base 2312} :=
  (basePacket_readSites_support divide j hj).trans (FrontierReplay1591.readSites_sub (5*j))

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAGroups =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed Secp256k1 CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


theorem basePacket_cut_frame (divide : Bool) (j : Nat) (first : 1≤j) (hj : j<102) (regular : divide=true → j≠84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord (if divide then j else j+1) origin X Y) (basePacket divide j)
      (fun state => let V := directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord (if divide then j+1 else j) origin V.1 V.2 state) := by
  have nonzero : j≠0 := by omega
  cases divide
  · intro state records input
    apply cut_window_frame P1Life.oddWord P1Life.oddWord P1Life.oddWord P1Life.oddWord (j+1) j j hj origin X Y _ _ (basePacket false j)
      (otherEncodeCut_step base j 102).symm
      (otherEncodeCut_body_disjoint (j+1) j hj origin ctx _
        (basePacket_read_support false j hj)) _ state records input
    intro current tape frame
    have normalized : CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt false (History5.historyMap base (5*j)))
        origin X Y current := by
      simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using
      basePacket_replay_frame false j hj (by simp) origin ctx enabled X Y current tape normalized
  · intro state records input
    apply cut_window_frame P1Life.oddWord P1Life.oddWord P1Life.oddWord P1Life.oddWord j (j+1) j hj origin X Y _ _ (basePacket true j)
      (otherEncodeCut_step base j 102)
      (otherEncodeCut_body_disjoint j j hj origin ctx _
        (basePacket_read_support true j hj)) _ state records input
    intro current tape frame
    have normalized : CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt true (History5.historyMap base (5*j)))
        origin X Y current := by
      simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using
      basePacket_replay_frame true j hj regular origin ctx enabled X Y current tape normalized


theorem packet_cut_frame (divide : Bool) (j : Nat) (first : 1≤j) (hj : j<102) (regular : divide=true → j≠84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord (if divide then j else j+1) origin X Y) (packet divide j)
      (fun state => let V := directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord (if divide then j+1 else j) origin V.1 V.2 state) := by
  intro state records input
  have raw := basePacket_cut_frame divide j first hj regular origin ctx enabled X Y state records input
  have same := Replay5.placed_eq (Placement5.pi j) (basePacket divide j)
    (fun q hq => Placement5.pi_outside j q hj hq) state records
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx X Y state input)
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx _ _ _ raw.2)
  change run (packet divide j) records state=run (basePacket divide j) records state at same
  rw [same]
  exact raw


theorem route_cut_sequence_frame {α : Type} (divide : Bool)
    (P : Nat→Program) (step : Nat→α→α) (F : Nat→α→State→Prop) (N : Nat)
    (packetLaw : ∀j,1≤j → j<N → ∀V,
      StateTriple (F (if divide then j else j+1) V) (P j)
        (F (if divide then j+1 else j) (step j V)))
    (j n : Nat) (first : 1≤j) (bound : j+n≤N) (V : α) :
    StateTriple (F (if divide then j else j+n) V) (PacketSequence.program divide P j n)
      (F (if divide then j+n else j) (PacketSequence.payload divide step j n V)) := by
  induction n generalizing j V with
  | zero =>
    intro state records input
    simpa only [PacketSequence.program,PacketSequence.payload,Nat.add_zero,run] using
      And.intro (Eq.refl state.phase) input
  | succ n ih =>
    have hj : j<N := by omega
    have index : j+(n+1)=(j+1)+n := by omega
    cases divide
    · let W := PacketSequence.payload false step (j+1) n V
      have later := ih (j+1) (by omega) (by omega) V
      have last := packetLaw j first hj W
      simpa only [PacketSequence.program,PacketSequence.payload,Bool.false_eq_true,
        if_false,index] using later.seq last
    · have head := packetLaw j first hj V
      have later := ih (j+1) (by omega) (by omega) (step j V)
      simpa only [PacketSequence.program,PacketSequence.payload,if_true,index] using head.seq later


theorem groups_cut_frame (divide : Bool) (j n : Nat) (first : 1≤j) (bound : j+n ≤ (if divide then 84 else 102))
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord (if divide then j else j+n) origin X Y) (groups divide j n)
      (fun state => let V := Replay5.groupsPayload divide origin j n (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord (if divide then j+n else j) origin V.1 V.2 state) := by
  let step := fun k V => directionalPayload (!divide)
    (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V
  have limit : (if divide then 84 else 102) ≤ 102 := by cases divide <;> decide
  exact route_cut_sequence_frame divide (packet divide) step
    (fun k (V : Fp×Fp) => CutFrame P1Life.oddWord P1Life.oddWord k origin V.1 V.2) (if divide then 84 else 102)
    (fun k hk kb V => packet_cut_frame divide k hk (lt_of_lt_of_le kb limit)
      (by intro e; exact ne_of_lt (by simpa only [e,if_true] using kb))
      origin ctx enabled V.1 V.2)
    j n first bound (X,Y)



theorem allMultiplyGroups_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (EncodedFieldFrame5 P1Life.oddWord P1Life.oddWord base (base 2409) false origin X Y)
      (groups false 1 101)
      (fun state => let V := Replay5.groupsPayload false origin 1 101 (X,Y)
        EncodedFieldFrame5 P1Life.oddWord P1Life.oddWord base (base 2409) true origin V.1 V.2 state) := by
  intro state records input
  have before := (cutFrame_end P1Life.oddWord P1Life.oddWord origin X Y state).mpr input
  have result := groups_cut_frame false 1 101 (by decide) (by decide) origin ctx enabled X Y state records before
  exact ⟨result.1,(cutFrame_one P1Life.oddWord P1Life.oddWord origin _ _ _).mp result.2⟩

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteALastDivide =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


theorem lastDivideBasePacket_frame (j : Nat) (hj : j < 102) (terminal : j=84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt true (History5.historyMap base (5*j))) origin X Y)
      (basePacket true j)
      (fun state => let V := regularPayload true j origin (X,Y)
        CodeFrame centerWord centerWord (codeEncodeAt false (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  let Frame (d : Bool) (k : Nat) (V : Fp×Fp) :=
    CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt d k (History5.historyMap base (5*j))) origin V.1 V.2
  have opening (d : Bool) (V : Fp×Fp) : StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt d (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageOpen) (Frame d 0 V) := by
    intro state records input
    exact regular_open_frame P1Life.oddWord P1Life.oddWord d j hj origin ctx V.1 V.2 state records input
  have step (d : Bool) (k logical physical : Nat) (hk : k < 3)
      (used : (logical,physical)∈activeSlots d k) (V : Fp×Fp) :
      StateTriple (Frame d k V) (cell d j physical 2)
        (Frame d k (regularStep d j origin logical V)) := by
    intro state records input
    exact regular_cell_frame d j k logical physical hj hk used origin ctx enabled
      V.1 V.2 state records input
  have transfer (d : Bool) (k : Nat) (hk : k < 2) (V : Fp×Fp) :
      StateTriple (Frame d k V) (onPacket j (stageTransition d k)) (Frame d (k+1) V) := by
    intro state records input
    exact regular_transition_frame P1Life.oddWord P1Life.oddWord d j k hj hk origin ctx V.1 V.2 state records input
  have closing (d : Bool) (V : Fp×Fp) : StateTriple (CodeFrame centerWord centerWord (stageCodeAt d 2 (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageClose)
      (CodeFrame centerWord centerWord (codeEncodeAt (!d) (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_close_frame centerWord centerWord d j hj origin ctx V.1 V.2 state records input
  have finalStep (V : Fp×Fp) : StateTriple (Frame true 2 V)
      (cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2)
      (CodeFrame centerWord centerWord (stageCodeAt true 2 (History5.historyMap base (5*j))) origin
        (regularStep true j origin 4 V).1 (regularStep true j origin 4 V).2) := by
    intro state records input
    exact regular_cellWith_frame _ true P1Life.oddWord centerWord dend_law dend_support
      j 2 4 4 hj (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  let V1 := regularStep true j origin 0 (X,Y)
  let V2 := regularStep true j origin 1 V1
  let V3 := regularStep true j origin 2 V2
  let V4 := regularStep true j origin 3 V3
  let V5 := regularStep true j origin 4 V4
  have result := (opening true (X,Y)).seq
    ((step true 0 0 3 (by decide) (by decide) (X,Y)).seq
    ((step true 0 1 4 (by decide) (by decide) V1).seq
    ((transfer true 0 (by decide) V2).seq
    ((step true 1 2 4 (by decide) (by decide) V2).seq
    ((step true 1 3 3 (by decide) (by decide) V3).seq
    ((transfer true 1 (by decide) V4).seq
    ((finalStep V4).seq (closing true V5))))))))
  simpa only [basePacket,stageOpen,stageClose,stageTransition,regularPayload,
    if_true,if_false,if_pos terminal,show ¬(1:Nat)=0 from by decide,List.append_assoc] using result


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteADivideGroups =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed Secp256k1 BalancedField CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


theorem lastDivideBasePacket_cut_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord 84 origin X Y) (basePacket true 84)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters 84)) (X,Y)
        CutFrame centerWord centerWord 85 origin V.1 V.2 state) := by
  intro state records input
  apply cut_window_frame P1Life.oddWord P1Life.oddWord centerWord centerWord 84 85 84 (by decide)
    origin X Y _ _ (basePacket true 84) (otherEncodeCut_step base 84 102)
    (otherEncodeCut_body_disjoint 84 84 (by decide) origin ctx _
      (basePacket_read_support true 84 (by decide))) _ state records input
  intro current tape frame
  have normalized : CodeFrame P1Life.oddWord P1Life.oddWord
      (codeEncodeAt true (History5.historyMap base (5*84))) origin X Y current := by
    simpa only [encodeGroup,show ¬(84:Nat)=0 from by decide,if_false,decide_true] using frame
  have result := lastDivideBasePacket_frame 84 (by decide) rfl origin ctx enabled X Y current tape normalized
  simpa only [regularPayload_eq true 84 (by decide) origin enabled,encodeGroup,
    show ¬(84:Nat)=0 from by decide,if_false,show decide ((85:Nat) ≤ 84)=false from rfl,
    Bool.not_true] using result


theorem lastDividePacket_cut_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord 84 origin X Y) (packet true 84)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters 84)) (X,Y)
        CutFrame centerWord centerWord 85 origin V.1 V.2 state) := by
  intro state records input
  have result := lastDivideBasePacket_cut_frame origin ctx enabled X Y state records input
  have same := Replay5.placed_eq (Placement5.pi 84) (basePacket true 84)
    (fun q hq => Placement5.pi_outside 84 q (by decide) hq) state records
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx X Y state input)
    (cutFrame_zero_region centerWord centerWord _ origin ctx _ _ _ result.2)
  change run (packet true 84) records state=run (basePacket true 84) records state at same
  rw [same]
  exact result


theorem route_program_snoc (P : Nat→Program) (j n : Nat) :
    PacketSequence.program true P j (n+1)=PacketSequence.program true P j n++P (j+n) := by
  induction n generalizing j with
  | zero => simp only [PacketSequence.program,if_true,List.append_nil,List.nil_append,Nat.add_zero]
  | succ n ih =>
    rw [PacketSequence.program,if_pos rfl,ih,PacketSequence.program,if_pos rfl]
    simp only [List.append_assoc,show j+(n+1)=(j+1)+n from by omega]


theorem route_payload_snoc {α : Type} (step : Nat→α→α) (j n : Nat) (V : α) :
    PacketSequence.payload true step j (n+1) V=
      step (j+n) (PacketSequence.payload true step j n V) := by
  induction n generalizing j V with
  | zero => simp only [PacketSequence.payload,if_true,Nat.add_zero]
  | succ n ih =>
    rw [PacketSequence.payload,if_pos rfl,ih,PacketSequence.payload,if_pos rfl]
    rw [show j+(n+1)=(j+1)+n from by omega]


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteASupportOld =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit MappedCompressed RecordedQuantum
attribute [local irreducible] wires


theorem route_top_chain_support_eq (xs ys cs : List Wire) (cin target : Wire)
    (ne : xs≠[]) (hy : ys.length=xs.length) (hc : cs.length=xs.length) :
    wires (TopCarry.compareChainTop xs ys cs cin target)=
      (target::cin::(xs++ys++cs)).toFinset := by
  induction xs generalizing ys cs cin with
  | nil => exact (ne rfl).elim
  | cons a xs ih =>
    cases ys with
    | nil => simp at hy
    | cons b ys =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        by_cases last : xs=[]
        · subst xs
          have ye : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy)
          have ce : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
          subst ys; subst cs
          ext q
          simp [TopCarry.compareChainTop,eraseCarry,wires,Instr.wires,correctionWires]
          simp only [or_assoc,or_left_comm,or_comm,or_self,or_self_left,or_self_right]
        · have child := ih ys cs c last (by simpa using hy) (by simpa using hc)
          rw [TopCarry.compareChainTop,if_neg last,wires_append,wires_append,
            child,P1Life.junction_majority_support,eraseCarry_wires]
          ext q
          simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
            List.mem_toFinset,List.mem_cons,List.mem_append]
          simp only [or_assoc,or_left_comm,or_comm,or_self,or_self_left,or_self_right]


theorem route_top_compare_support_eq (xs ys cs : List Wire) (cin target : Wire)
    (ne : cs≠[]) (hy : ys.length=xs.length) (hc : cs.length+1=xs.length)
    (two : 2≤xs.length) :
    wires (TopCarryBorrow.compare xs ys cs cin target)=
      (target::cin::(xs++ys++cs)).toFinset := by
  cases xs with
  | nil => simp at two
  | cons a xs =>
    cases ys with
    | nil => simp at hy
    | cons b ys =>
      cases cs with
      | nil => exact (ne rfl).elim
      | cons c cs =>
        have xn : xs≠[] := by intro e; simp [e] at two
        have hy' : ys.length=xs.length := Nat.succ.inj hy
        have hc' : cs.length+1=xs.length := Nat.succ.inj hc
        have child := route_top_chain_support_eq xs ys (cs++[cin]) c target xn hy'
          (by simpa only [List.length_append,List.length_singleton] using hc')
        simp only [TopCarryBorrow.compare,TopCarryBorrow.compareHeadTop,
          TopCarryBorrow.headChainTop,wires_append,child,P1Life.junction_majority_support,
          eraseCarry_wires,notRegister_wires]
        ext q
        simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
          List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,
          wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
          Finset.notMem_empty,or_false]
        simp only [or_assoc,or_left_comm,or_comm,or_self,or_self_left,or_self_right]


theorem old_compare_footprint (L : Layout) (hw : L.Widths) (divide : Bool) :
    wires (if divide then Q6Structural.compareForward L else Q6Structural.compareInverse L)=
      (L.parity::L.one::(L.y++L.r++(Q6Structural.q6Carry L).take 255)).toFinset := by
  have count : ((Q6Structural.q6Carry L).take 255).length=255 := by
    rw [DirectPass.active_carry_shape L hw]
    have len : (L.carry.take 254).length=254 := (BalancedCleanup.widths L.toLayout hw).2.2.2
    simp only [List.length_append,List.length_singleton,len]
  have yn : L.y.length=256 := (BalancedCleanup.widths L.toLayout hw).2.2.1
  have rn : L.r.length=256 := (BalancedCleanup.widths L.toLayout hw).2.1
  cases divide
  · exact CarryBorrow.program_support_eq (Q6Structural.carryLayout L) (Q6StructuralCell.carry_widths L hw)
  · have nonempty : (Q6Structural.q6Carry L).take 255≠[] := by
      intro eq;rw [eq] at count; simp at count
    exact route_top_compare_support_eq L.y L.r ((Q6Structural.q6Carry L).take 255) L.one L.parity
      nonempty (rn.trans yn.symm) (by omega) (by omega)


theorem standard_half_program_shape (divide : Bool) (w : Nat→Wire) (sign : Wire) :
    Q6EndpointCell.half divide w sign=[.X sign]++
      (if divide then Q6StructuralCell.forward (Q6EndpointCell.ports w sign)
       else Q6StructuralCell.inverse (Q6EndpointCell.ports w sign))++[.X sign] := rfl


theorem compare_sub_standard_body (L : Layout) (divide : Bool) :
    wires (if divide then Q6Structural.compareForward L else Q6Structural.compareInverse L)⊆
      wires (if divide then Q6StructuralCell.forward L else Q6StructuralCell.inverse L) := by
  cases divide
  all_goals
    intro q used
    simp only [Bool.false_eq_true,if_false,if_true] at used ⊢
    simp only [Q6StructuralCell.inverse,Q6StructuralCell.inversePrefix,Q6StructuralCell.recoverPrefix,
      Q6StructuralCell.forward,Q6StructuralCell.forwardPrefix,Q6StructuralCell.cleanup,
      wires_append,Finset.mem_union]
    itauto


theorem junction_footprint_sub_standard (divide : Bool) (w : Nat→Wire) (sign : Wire) :
    P1Life.junctionFootprint (Q6EndpointCell.ports w sign)⊆wires (Q6EndpointCell.half divide w sign) := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have cmp := old_compare_footprint L hw divide
  intro q used
  rw [P1Life.junction_footprint_shape L hw] at used
  simp only [List.mem_toFinset,List.mem_cons] at used
  rcases used with isSign|rest
  · subst q
    rw [standard_half_program_shape,wires_append,wires_append]
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (by simp [wires,Instr.wires,Q6EndpointCell.ports_sign,L]))
  · have part : q∈wires (if divide then Q6Structural.compareForward L else Q6Structural.compareInverse L) :=
      cmp.symm ▸ (by simpa only [List.mem_toFinset,List.mem_cons] using rest)
    have body := compare_sub_standard_body L divide part
    rw [standard_half_program_shape,wires_append,wires_append]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ body)


theorem body_sub_old (P : Program) (support : HalfSupport P) (divide : Bool) :
    wires P⊆wires (Q6EndpointCell.half divide base (base 2409)) :=
  support.trans ((Finset.erase_subset _ _).trans (junction_footprint_sub_standard divide base (base 2409)))


theorem body_retired_free (P : Program) (support : HalfSupport P) : base 760∉wires P :=
  fun used => (Finset.mem_erase.mp (support used)).1 rfl


















end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAFreeWires =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires


theorem wire_rename_free (e : Equiv.Perm Wire) (P : Program) (a b : Wire)
    (image : e a=b) (free : a∉wires P) : b∉wires (renameProgram e P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp used
  exact free (e.injective (eq.trans image.symm) ▸ hi)


theorem wire_selected_free (source flag q : Wire) (P : Program)
    (sourceAway : q≠source) (flagAway : q≠flag) (free : q∉wires P) :
    q∉wires (SW.selW source flag P) := by
  simpa [SW.selW,wires_append,wires,Instr.wires,correctionWires,sourceAway,flagAway] using free


theorem swap_body_low_free (i : Nat) (low : i < 770) : base i∉wires FrontierSW1591.swapBody := by
  intro used
  have member := swapRegisters_wires (base 2409) (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y
    (by simp [balancedSharedPorts_r,balancedSharedPorts_y,wireBlock]) used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,balancedSharedPorts_r,
    balancedSharedPorts_y,wireBlock,List.mem_map,List.mem_range'_1,base_injective.eq_iff] at member
  omega


theorem halfWindowWith_719_free (P : Program) (support : HalfSupport P) (j active hole : Nat)
    (hj : j < 102) (sourceBound : 5*j+active < 512) (hh : hole < 5) : base 719∉wires (halfWindowWith P j active hole) := by
  let rebound := renameProgram (Equiv.swap (base 719) (s j hole)) P
  have noHole : s j hole∉wires P := body_history_free P support _ (Or.inr ⟨by omega,by omega⟩)
  have no719 : base 719∉wires rebound :=
    wire_rename_free _ P (s j hole) (base 719) (Equiv.swap_apply_right _ _) noHole
  have awayG : base 719≠g j active := HostOB5.host_ne _ _ (by omega)
  have awayC : base 719≠packetCarry j := HostOB5.host_ne _ _ (by omega)
  have fixed : Equiv.swap (packetCarry j) (g j active) (base 719)=base 719 :=
    Equiv.swap_apply_of_ne_of_ne awayC awayG
  have mid := wire_rename_free (Equiv.swap (packetCarry j) (g j active)) rebound
    (base 719) (base 719) fixed no719
  intro used
  rcases Finset.mem_union.mp
      (ControlLoan1589.loanWindow_support (g j active) (base 2409) (packetCarry j) rebound used)
      with edge|body
  · simp only [Finset.mem_insert,Finset.mem_singleton] at edge
    exact edge.elim awayG (by decide)
  · exact mid (by simpa only [renameProgram_support] using body)


theorem halfWindowWith_760_free (P : Program) (support : HalfSupport P) (j active hole : Nat)
    (hj : j < 102) (sourceBound : 5*j+active < 512) (hh : hole < 5) : base 760∉wires (halfWindowWith P j active hole) := by
  let rebound := renameProgram (Equiv.swap (base 719) (s j hole)) P
  have fixHole : Equiv.swap (base 719) (s j hole) (base 760)=base 760 :=
    Equiv.swap_apply_of_ne_of_ne (HostOB5.host_ne _ _ (by omega)) (HostOB5.host_ne _ _ (by omega))
  have no760 : base 760∉wires rebound :=
    wire_rename_free _ P (base 760) (base 760) fixHole (body_retired_free P support)
  have awayG : base 760≠g j active := HostOB5.host_ne _ _ (by omega)
  have awayC : base 760≠packetCarry j := HostOB5.host_ne _ _ (by omega)
  have fixed : Equiv.swap (packetCarry j) (g j active) (base 760)=base 760 :=
    Equiv.swap_apply_of_ne_of_ne awayC awayG
  have mid := wire_rename_free (Equiv.swap (packetCarry j) (g j active)) rebound
    (base 760) (base 760) fixed no760
  intro used
  rcases Finset.mem_union.mp
      (ControlLoan1589.loanWindow_support (g j active) (base 2409) (packetCarry j) rebound used)
      with edge|body
  · simp only [Finset.mem_insert,Finset.mem_singleton] at edge
    exact edge.elim awayG (by decide)
  · exact mid (by simpa only [renameProgram_support] using body)


theorem cellWith_pool_free (divide : Bool) (P : Program) (support : HalfSupport P) (j active hole i : Nat)
    (hj : j < 102) (ha : active < 5) (hh : hole < 5) (hi : i=719 ∨ i=760) :
    base i∉wires (cellWith divide P j active hole) := by
  have half : base i∉wires (halfWindowWith P j active hole) := by
    rcases hi with rfl|rfl
    · exact halfWindowWith_719_free P support j active hole hj (by omega) hh
    · exact halfWindowWith_760_free P support j active hole hj (by omega) hh
  have swap := wire_selected_free (s j active) (base 2409) (base i) FrontierSW1591.swapBody
    (HostOB5.host_ne _ _ (by rcases hi with rfl|rfl <;> omega))
    (HostOB5.host_ne _ _ (by rcases hi with rfl|rfl <;> omega))
    (swap_body_low_free i (by rcases hi with rfl|rfl <;> omega))
  cases divide <;> simp only [cellWith,Bool.false_eq_true,if_false,if_true,wires_append,Finset.mem_union,not_or]
  · exact ⟨swap,half⟩
  · exact ⟨half,swap⟩



































theorem cell_pool_free (divide : Bool) (j active hole i : Nat)
    (hj : j < 102) (ha : active < 5) (hh : hole < 5) (hi : i=719 ∨ i=760) :
    base i∉wires (cell divide j active hole) := by
  cases divide
  · simpa only [cell,cellWith,halfWindow,Bool.false_eq_true,if_false] using
      cellWith_pool_free false _ (half_support false) j active hole i hj ha hh hi
  · simpa only [cell,cellWith,halfWindow,if_true] using
      cellWith_pool_free true _ (half_support true) j active hole i hj ha hh hi

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteARegularFree =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires


theorem codec_pool_free (j i : Nat) (hj : j < 102) (hi : i=719 ∨ i=760) :
    base i∉wires (NewHistory5.encode base (5*j)) := by
  intro used
  obtain ⟨port,eq⟩ := NewHistory5.history_gate_mem base (5*j) _ (Or.inl rfl) _ used
  have bound := port.isLt
  have same := base_injective eq
  unfold History5.historyId at same
  rcases hi with rfl|rfl <;> split_ifs at same <;> omega


theorem onPacket_pool_free (j : Nat) (hj : j < 102) (i : Nat) (hi : i=719 ∨ i=760)
    (P : Program) (support : wires P⊆Finset.range 10) : base i∉wires (onPacket j P) := by
  intro used
  rw [onPacket,renameProgram_support] at used
  obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp used
  have bound := Finset.mem_range.mp (support hq)
  have member := NewHistory5.history_site_mem base (5*j) ⟨q,bound⟩
  have image : MeasuredCodec5.label (History5.historyMap base (5*j)) q=
      History5.historyMap base (5*j) ⟨q,bound⟩ := by simp only [MeasuredCodec5.label,dif_pos bound]
  rw [image] at eq
  exact codec_pool_free j i hj hi (eq ▸ member)


theorem basePacket_pool_free (divide : Bool) (j i : Nat) (hj : j < 102) (hi : i=719 ∨ i=760) :
    base i∉wires (basePacket divide j) := by
  have opening := onPacket_pool_free j hj i hi stageOpen stageOpen_support
  have closing := onPacket_pool_free j hj i hi stageClose stageClose_support
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_pool_free j hj i hi (stageTransition d k) (stageTransition_support d k hk)
  have cellAt (d : Bool) (active : Nat) (ha : active<5) :=
    cell_pool_free d j active 2 i hj ha (by decide) hi
  have last := cellWith_pool_free true _ dend_support j 4 2 i hj (by decide) (by decide) hi
  cases divide
  · simp only [basePacket,Bool.false_eq_true,if_false,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨cellAt false 4 (by decide),transfer false 0 (by decide)⟩,
      cellAt false 3 (by decide)⟩,cellAt false 4 (by decide)⟩,transfer false 1 (by decide)⟩,
      cellAt false 4 (by decide)⟩,cellAt false 3 (by decide)⟩⟩,closing⟩
  · have ending : base i∉wires (if j=84 then cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2
        else cell true j 4 2) := by
      by_cases terminal : j=84
      · rw [if_pos terminal]; exact last
      · rw [if_neg terminal]; exact cellAt true 4 (by decide)
    simp only [basePacket,if_true,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨cellAt true 3 (by decide),cellAt true 4 (by decide)⟩,
      transfer true 0 (by decide)⟩,cellAt true 4 (by decide)⟩,cellAt true 3 (by decide)⟩,
      transfer true 1 (by decide)⟩,ending⟩⟩,closing⟩



theorem packet_pool_free (divide : Bool) (j i : Nat) (hj : j < 102) (hi : i=719 ∨ i=760) :
    base i∉wires (packet divide j) := by
  apply wire_rename_free (shifted (Placement5.pi j)) (basePacket divide j) (base i) (base i)
  · rw [shifted_base,Placement5.pi_outside j i hj]
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
    rcases hi with rfl|rfl <;> omega
  · exact basePacket_pool_free divide j i hj hi


theorem groups_pool_free (divide : Bool) (j n i : Nat) (bound : j+n ≤ 102) (hi : i=719 ∨ i=760) :
    base i∉wires (groups divide j n) := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,wires]
  | succ n ih =>
    have head := packet_pool_free divide j i (by omega) hi
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,
      if_true,wires_append,Finset.mem_union,not_or] at rest ⊢
    · exact ⟨rest,head⟩
    · exact ⟨head,rest⟩

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAResourcePhysical =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic BalancedCircuit BalancedField MappedCompressed Challenge Baselines RecordedQuantum
attribute [local irreducible] GatePhysical P1Life.half P1Life.dstart P1Life.dend P1Life.mend
attribute [local irreducible] JointForward1588.paddedGD JointInverse1588.paddedD


theorem centerOdd_physical (L : BalancedConvert.Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (P1Life.centerOdd L) := by
  have mapped := mappedAdd_physical (P1Life.centerOddBits L) (L.low.drop 3)
    ((L.carry.take 254).drop 3) L.cin (P1Life.center_odd_high_nodup L hn) (by
      intro b hb q hq
      have source : q∈mappedWires (P1Life.centerOddBits L) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [P1Life.center_odd_bits_sources L q source]
      exact P1Life.center_odd_high_away L hn)
  have rotation := rotate_physical L.word (P1Life.center_odd_word_nodup L hn)
  have flagLow : HalfConvert.lowBit L≠L.flag := by
    have a := P1Life.center_odd_word_shape L hw
    obtain ⟨a,rest,low,word⟩ := a
    have nd := List.nodup_iff_count.mp hn L.flag
    intro eq
    have mem : L.flag∈L.low := by
      have lm : HalfConvert.lowBit L∈L.low := by
        cases h : L.low with
        | nil => have bad := hw.1;rw [h] at bad;simp at bad
        | cons x xs => simp [HalfConvert.lowBit,h]
      exact eq ▸ lm
    have count := List.count_pos_iff.mpr mem
    simp only [BalancedConvert.Layout.wires,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at nd
    first | omega | exact True.intro
  have flagMsb : L.flag≠L.msb := by
    have nd := List.nodup_iff_count.mp hn L.flag
    intro eq
    simp only [BalancedConvert.Layout.wires,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true,←eq] at nd
    first | omega | exact True.intro
  have first : GatePhysical [.CX (HalfConvert.lowBit L) L.flag,.CX L.flag (HalfConvert.lowBit L),.X L.flag] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,flagLow,Ne.symm flagLow]
  have last : GatePhysical [.CX L.flag L.msb,.CX L.msb L.flag] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,flagMsb,Ne.symm flagMsb]
  simpa only [P1Life.centerOdd,gatePhysical_append] using
    And.intro (And.intro (And.intro first rotation.1) mapped) last

namespace Rolling1588
open ECDSAAdd.Entrant.Rolling1588
open Rolling1588Lifetime
attribute [local irreducible] cell cellWith groups placedFirstPacket entryField exitField entryTail exitHead


theorem route_body_physical (divide : Bool) :
    GatePhysical (P1Life.half (base 760) divide base (base 2409)) :=
  (P1Life.half_resources _ _ _ _ half_ports_nodup route_retired_member).1


theorem route_junction_physical :
    GatePhysical (P1Life.dstart (base 760) base (base 2409)) ∧
    GatePhysical (P1Life.dend (base 760) base (base 2409)) ∧
    GatePhysical (P1Life.mend (base 760) base (base 2409)) :=
  ⟨(P1Life.dstart_resources _ _ _ half_ports_nodup route_retired_member).1,
   (P1Life.dend_resources _ _ _ half_ports_nodup route_retired_member).1,
   (P1Life.mend_resources _ _ _ half_ports_nodup route_retired_member).1⟩


theorem route_selected_physical (source flag : Wire) (P : Program)
    (away : source≠flag) (physical : GatePhysical P) : GatePhysical (SW.selW source flag P) := by
  have first : GatePhysical [.CX source flag] := by simp [GatePhysical,PhysicalInstr,ProperGate,away]
  have last : GatePhysical [.measureX flag [] [.Z source]] := by simp [GatePhysical,PhysicalInstr]
  simpa only [SW.selW,gatePhysical_append] using And.intro (And.intro first physical) last


theorem route_swap_physical : GatePhysical FrontierSW1591.swapBody := by
  rw [FrontierSW1591.swapBody]
  exact swapRegisters_physical _ _ _ FrontierReplay1591.base_sign_nd


theorem halfWindowWith_physical (P : Program) (hp : GatePhysical P)
    (j active hole : Nat) (hj : j<102) (ha : active<6) : GatePhysical (halfWindowWith P j active hole) := by
  apply ControlLoan1589.loanWindow_physical
  · exact HostOB5.host_ne _ _ (by first | omega | exact True.intro)
  · exact gatePhysical_rename _ (Equiv.swap (base 719) (s j hole)).injective _ hp


theorem cellWith_physical (divide : Bool) (P : Program) (hp : GatePhysical P)
    (j active hole : Nat) (hj : j<102) (ha : active<5) : GatePhysical (cellWith divide P j active hole) := by
  have half := halfWindowWith_physical P hp j active hole hj (by first | omega | exact True.intro)
  have swap := route_selected_physical (s j active) (base 2409) FrontierSW1591.swapBody
    (HostOB5.host_ne _ _ (by first | omega | exact True.intro)) route_swap_physical
  cases divide <;> simp only [cellWith,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨swap,half⟩
  · exact ⟨half,swap⟩


theorem cell_physical (divide : Bool) (j active hole : Nat) (hj : j<102) (ha : active<5) :
    GatePhysical (cell divide j active hole) := by
  have a := cellWith_physical divide _ (route_body_physical divide) j active hole hj ha
  cases divide <;> simpa only [cell,cellWith,halfWindow] using a


theorem onPacket_physical (j : Nat) (hj : j<102) (P : Program)
    (support : wires P⊆Finset.range 10) (physical : GatePhysical P) : GatePhysical (onPacket j P) :=
  gatePhysical_rename_support _ P
    (fun a ha b hb eq => FirstNonzeroCodec.label_inj'
      (History5.historyMap base (5*j))
      (History5.historyMap_injective base base_pool_nodup (5*j) (by first | omega | exact True.intro))
      a (support ha) b (support hb) eq) physical


theorem stage_physical : GatePhysical stageOpen ∧ GatePhysical stageClose ∧
    ∀divide k,k<2→GatePhysical (stageTransition divide k) := by
  refine ⟨?_,?_,?_⟩
  · apply physicalGateCheck_correct
    decide +kernel
  · apply physicalGateCheck_correct
    decide +kernel
  · intro divide k hk
    apply physicalGateCheck_correct
    cases divide <;> interval_cases k <;> decide +kernel


theorem basePacket_physical (divide : Bool) (j : Nat) (hj : j<102) :
    GatePhysical (basePacket divide j) := by
  have opening := onPacket_physical j hj stageOpen stageOpen_support stage_physical.1
  have closing := onPacket_physical j hj stageClose stageClose_support stage_physical.2.1
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_physical j hj (stageTransition d k) (stageTransition_support d k hk)
      (stage_physical.2.2 d k hk)
  have cellAt (k : Nat) (hk : k<5) := cell_physical divide j k 2 hj hk
  have junction := cellWith_physical true _ route_junction_physical.2.1 j 4 2 hj (by decide)
  cases divide <;> simp only [basePacket,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  all_goals try split_ifs
  all_goals repeat' apply And.intro
  all_goals first
    | exact junction
    | exact opening
    | exact closing
    | exact transfer false 0 (by decide)
    | exact transfer false 1 (by decide)
    | exact transfer true 0 (by decide)
    | exact transfer true 1 (by decide)
    | exact cellAt 3 (by decide)
    | exact cellAt 4 (by decide)


theorem packet_physical (divide : Bool) (j : Nat) (hj : j<102) :
    GatePhysical (packet divide j) :=
  gatePhysical_rename _ (shifted (Placement5.pi j)).injective _ (basePacket_physical divide j hj)


theorem groups_physical (divide : Bool) (j n : Nat) (bound : j+n≤102) :
    GatePhysical (groups divide j n) := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,GatePhysical]
  | succ n ih =>
    have head := packet_physical divide j (by first | omega | exact True.intro)
    have rest := ih (j+1) (by first | omega | exact True.intro)
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,
      if_true,gatePhysical_append] at rest ⊢
    · exact ⟨rest,head⟩
    · exact ⟨head,rest⟩


theorem c3_physical : GatePhysical e3 ∧ GatePhysical d3 ∧
    GatePhysical e3short ∧ GatePhysical d3short := by
  repeat' apply And.intro
  all_goals apply physicalGateCheck_correct
  all_goals decide +kernel


theorem triple_physical (a b c : Nat) (P : Program)
    (support : wires P⊆Finset.range 6)
    (injective : Function.Injective (fun i : Fin 6 => tripleMap a b c i.val))
    (physical : GatePhysical P) : GatePhysical (triple a b c P) := by
  apply gatePhysical_rename_support _ P _ physical
  intro i hi j hj eq
  have same := @injective ⟨i,Finset.mem_range.mp (support hi)⟩
    ⟨j,Finset.mem_range.mp (support hj)⟩ eq
  exact congrArg Fin.val same

section
attribute [local irreducible] SW.selW FrontierSW1591.swapBody
attribute [local irreducible] ECDSAAdd.Entrant.Rolling1588.triple
attribute [local irreducible] ECDSAAdd.Entrant.Rolling1588.e3 ECDSAAdd.Entrant.Rolling1588.d3
attribute [local irreducible] ECDSAAdd.Entrant.Rolling1588.e3short ECDSAAdd.Entrant.Rolling1588.d3short


theorem firstBodyShort_physical (divide : Bool) : GatePhysical (firstBodyShort divide) := by
  have cellAt (d : Bool) (k hole : Nat) (hk : k<5) := cell_physical d 0 k hole (by decide) hk
  have ds := cellWith_physical true _ route_junction_physical.1 0 2 4 (by decide) (by decide)
  have ms := cellWith_physical false _ route_junction_physical.2.2 0 2 4 (by decide) (by decide)
  have swap := route_selected_physical (s 0 1) (base 2409) FrontierSW1591.swapBody (by decide) route_swap_physical
  have tiny (a b c : Nat) (P : Program) (sup : wires P⊆Finset.range 6)
      (inj : Function.Injective (fun i : Fin 6 => tripleMap a b c i.val)) (phy : GatePhysical P) :=
    triple_physical a b c P sup inj phy
  cases divide <;> simp only [firstBodyShort,Bool.false_eq_true,if_false,if_true,
    firstCellsJFront,firstRestZFront,firstJointBack,gatePhysical_append]
  all_goals repeat' apply And.intro
  all_goals first
    | exact ds
    | exact ms
    | exact swap
    | exact JointForward1588.paddedGD_physical
    | exact JointInverse1588.paddedD_physical
    | exact cellAt false 3 2 (by decide)
    | exact cellAt false 4 2 (by decide)
    | exact cellAt true 3 2 (by decide)
    | exact cellAt true 4 2 (by decide)
    | exact triple_physical 3 1 2 e3 ECDSAAdd.Entrant.Rolling1588.c3_support.1 (by decide +kernel) c3_physical.1
    | exact triple_physical 4 1 2 e3 ECDSAAdd.Entrant.Rolling1588.c3_support.1 (by decide +kernel) c3_physical.1
    | exact triple_physical 1 3 4 e3 ECDSAAdd.Entrant.Rolling1588.c3_support.1 (by decide +kernel) c3_physical.1
    | exact triple_physical 2 3 4 e3 ECDSAAdd.Entrant.Rolling1588.c3_support.1 (by decide +kernel) c3_physical.1
    | exact triple_physical 3 1 2 d3 ECDSAAdd.Entrant.Rolling1588.c3_support.2.1 (by decide +kernel) c3_physical.2.1
    | exact triple_physical 4 1 2 d3 ECDSAAdd.Entrant.Rolling1588.c3_support.2.1 (by decide +kernel) c3_physical.2.1
    | exact triple_physical 1 3 4 d3 ECDSAAdd.Entrant.Rolling1588.c3_support.2.1 (by decide +kernel) c3_physical.2.1
    | exact triple_physical 2 3 4 d3 ECDSAAdd.Entrant.Rolling1588.c3_support.2.1 (by decide +kernel) c3_physical.2.1
    | exact triple_physical 3 1 2 e3short ECDSAAdd.Entrant.Rolling1588.c3_support.2.2.1 (by decide +kernel) c3_physical.2.2.1
    | exact triple_physical 4 1 2 e3short ECDSAAdd.Entrant.Rolling1588.c3_support.2.2.1 (by decide +kernel) c3_physical.2.2.1
    | exact triple_physical 1 3 4 e3short ECDSAAdd.Entrant.Rolling1588.c3_support.2.2.1 (by decide +kernel) c3_physical.2.2.1
    | exact triple_physical 2 3 4 e3short ECDSAAdd.Entrant.Rolling1588.c3_support.2.2.1 (by decide +kernel) c3_physical.2.2.1
    | exact triple_physical 3 1 2 d3short ECDSAAdd.Entrant.Rolling1588.c3_support.2.2.2 (by decide +kernel) c3_physical.2.2.2
    | exact triple_physical 4 1 2 d3short ECDSAAdd.Entrant.Rolling1588.c3_support.2.2.2 (by decide +kernel) c3_physical.2.2.2
    | exact triple_physical 1 3 4 d3short ECDSAAdd.Entrant.Rolling1588.c3_support.2.2.2 (by decide +kernel) c3_physical.2.2.2
    | exact triple_physical 2 3 4 d3short ECDSAAdd.Entrant.Rolling1588.c3_support.2.2.2 (by decide +kernel) c3_physical.2.2.2

end


theorem placedFirstPacket_physical (divide : Bool) : GatePhysical (placedFirstPacket divide) := by
  have body := G0CarryLoan5.physical (base 1028) (base 0) (base 768) (firstBodyShort divide)
    (by decide) (firstBodyShort_physical divide)
  have cd : GatePhysical Prefix1590.firstDecode ∧ GatePhysical firstDecodeShort ∧
      GatePhysical Prefix1590.firstEncode ∧ GatePhysical firstEncodeShort := by
    repeat' apply And.intro
    all_goals apply physicalGateCheck_correct
    all_goals decide +kernel
  have core : GatePhysical (firstCore divide) := by
    cases divide <;> simp only [firstCore,Bool.false_eq_true,if_false,if_true,gatePhysical_append] at body ⊢
    · exact ⟨⟨cd.2.1,body⟩,cd.2.2.1⟩
    · exact ⟨⟨cd.1,body⟩,cd.2.2.2⟩
  rw [placedFirstPacket,firstPacket]
  exact gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _
    (gatePhysical_rename _ (shifted (Placement5.pi 0)).injective _ core)


end Rolling1588
end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteAResourceSupportCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical DirectSkywalk Challenge RecordedQuantum
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires run
attribute [local irreducible] cell cellWith halfWindowWith groups placedFirstPacket
attribute [local irreducible] P1Life.half P1Life.dstart P1Life.dend P1Life.mend
attribute [local irreducible] ControlLoan1589.cell ControlLoan1589.halfWindow ControlLoan1589.groups








theorem rename_sub (f : Wire→Wire) (P Q : Program) (sub : wires P⊆wires Q) :
    wires (renameProgram f P)⊆wires (renameProgram f Q) := by
  rw [renameProgram_support,renameProgram_support]
  exact Finset.image_mono f sub


theorem rename_free (f : Wire→Wire) (hf : Function.Injective f)
    (P : Program) (a b : Wire) (mapped : f a=b) (free : a∉wires P) :
    b∉wires (renameProgram f P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp used
  exact free (hf (eq.trans mapped.symm) ▸ hq)


theorem append_extra (P Q P0 Q0 : Program) (extra : Wire)
    (hp : wires P⊆wires P0∪{extra}) (hq : wires Q⊆wires Q0∪{extra}) :
    wires (P++Q)⊆wires (P0++Q0)∪{extra} := by
  simp only [wires_append] at hp hq ⊢
  intro q used
  rcases Finset.mem_union.mp used with used|used
  · rcases Finset.mem_union.mp (hp used) with old|fresh
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ old)
    · exact Finset.mem_union_right _ fresh
  · rcases Finset.mem_union.mp (hq used) with old|fresh
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ old)
    · exact Finset.mem_union_right _ fresh


theorem rename_extra (f : Wire→Wire) (P Q : Program) (extra : Wire)
    (fixed : f extra=extra) (sub : wires P⊆wires Q∪{extra}) :
    wires (renameProgram f P)⊆wires (renameProgram f Q)∪{extra} := by
  rw [renameProgram_support,renameProgram_support]
  intro q used
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp used
  rcases Finset.mem_union.mp (sub ha) with old|fresh
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,old,rfl⟩)
  · have eq := Finset.mem_singleton.mp fresh
    subst a
    exact Finset.mem_union_right _ (Finset.mem_singleton.mpr fixed)


theorem rebind_support (a b : Wire) (P : Program) (off : b∉wires P) :
    wires (renameProgram (Equiv.swap a b) P)⊆wires P∪{b} := by
  rw [renameProgram_support]
  intro q used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp used
  by_cases left : i=a
  · subst i
    exact Finset.mem_union_right _ (by simp)
  have right : i≠b := fun eq => off (eq ▸ hi)
  rw [Equiv.swap_apply_of_ne_of_ne left right]
  exact Finset.mem_union_left _ hi


theorem halfWindowWith_extra (P : Program) (support : HalfSupport P) (divide : Bool) (j active hole : Nat)
    (hj : j<102) (ha : active<5) (hh : hole<5) :
    wires (halfWindowWith P j active hole)⊆
      wires (ControlLoan1589.halfWindow divide j (g j active))∪{s j hole} := by
  let Old := Q6EndpointCell.half divide base (base 2409)
  let F := P
  have off : s j hole∉wires F :=
    body_history_free P support _ (Or.inr ⟨by first | omega | exact True.intro,by first | omega | exact True.intro⟩)
  have fixed : Equiv.swap (packetCarry j) (g j active) (s j hole)=s j hole :=
    Equiv.swap_apply_of_ne_of_ne (HostOB5.host_ne _ _ (by first | omega | exact True.intro))
      (HostOB5.host_ne _ _ (by first | omega | exact True.intro))
  have mid := rename_extra (Equiv.swap (packetCarry j) (g j active))
    (renameProgram (Equiv.swap (base 719) (s j hole)) F) Old (s j hole) fixed
    ((rebind_support (base 719) (s j hole) F off).trans
      (Finset.union_subset_union (body_sub_old P support divide) (Finset.Subset.refl _)))
  have first := append_extra
    [.CX (g j active) (base 2409),.CX (base 2409) (g j active)] _
    [.CX (g j active) (base 2409),.CX (base 2409) (g j active)] _ (s j hole)
    Finset.subset_union_left mid
  have all := append_extra _ [.CX (base 2409) (g j active),
      .measureX (base 2409) [] [.Z (g j active)]]
    _ [.CX (base 2409) (g j active),.measureX (base 2409) [] [.Z (g j active)]]
    (s j hole) first Finset.subset_union_left
  simpa only [halfWindowWith,ControlLoan1589.halfWindow,ControlLoan1589.loanWindow,
    ControlLoan1589.packetCarry,packetCarry,F,Old] using all


theorem old_cell_parts (divide : Bool) (j active : Nat) (W : Finset Wire)
    (sub : wires (ControlLoan1589.cell divide j (g j active) (s j active))⊆W) :
    wires (ControlLoan1589.halfWindow divide j (g j active))⊆W ∧
      wires (SW.selW (s j active) (base 2409) FrontierSW1591.swapBody)⊆W := by
  cases divide <;> simp only [ControlLoan1589.cell,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff] at sub ⊢
  · exact sub.symm
  · exact sub


theorem history_controls (j k : Nat) (hk : k<5) :
    g j k∈wires (NewHistory5.encode base (5*j)) ∧
      s j k∈wires (NewHistory5.encode base (5*j)) := by
  simpa only [g,s,NewHistory5.encode_support_eq] using Replay5.history_controls (5*j) k hk


theorem cellWith_support_into (P : Program) (support : HalfSupport P) (divide : Bool) (j active hole : Nat)
    (hj : j<102) (ha : active<5) (hh : hole<5) (W : Finset Wire)
    (old : wires (ControlLoan1589.cell divide j (g j active) (s j active))⊆W)
    (history : wires (NewHistory5.encode base (5*j))⊆W) :
    wires (cellWith divide P j active hole)⊆W := by
  have parts := old_cell_parts divide j active W old
  have half : wires (halfWindowWith P j active hole)⊆W := by
    intro q used
    rcases Finset.mem_union.mp (halfWindowWith_extra P support divide j active hole hj ha hh used) with old|fresh
    · exact parts.1 old
    · have eq := Finset.mem_singleton.mp fresh
      subst q
      exact history (history_controls j hole hh).2
  cases divide <;> simp only [cellWith,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.union_subset_iff]
  · exact ⟨parts.2,half⟩
  · exact ⟨half,parts.2⟩


theorem cell_support_into (divide : Bool) (j active hole : Nat)
    (hj : j<102) (ha : active<5) (hh : hole<5) (W : Finset Wire)
    (old : wires (ControlLoan1589.cell divide j (g j active) (s j active))⊆W)
    (history : wires (NewHistory5.encode base (5*j))⊆W) : wires (cell divide j active hole)⊆W := by
  have h := cellWith_support_into _ (half_support divide) divide j active hole hj ha hh W old history
  cases divide <;> simpa only [cell,cellWith,halfWindow] using h


theorem rawReplay_member (divide : Bool) (j : Nat)
    (letters : List MixedTranscriptLetter) (l : MixedTranscriptLetter) (member : l∈letters) :
    wires (ControlLoan1589.cell divide j l.1.1 l.1.2)⊆
      wires (ControlLoan1589.rawReplay divide j letters) := by
  induction letters with
  | nil => simp at member
  | cons head rest ih =>
    cases divide <;> simp only [ControlLoan1589.rawReplay,Bool.false_eq_true,if_false,if_true,wires_append]
    all_goals rcases List.mem_cons.mp member with rfl|member
    · exact Finset.subset_union_right
    · exact (ih member).trans Finset.subset_union_left
    · exact Finset.subset_union_left
    · exact (ih member).trans Finset.subset_union_right


theorem rawReplay_cell_at (divide : Bool) (j active : Nat)
    (hj : j<102) (ha : active<5) (letters : List MixedTranscriptLetter)
    (member : tapeLetter (5*j+active)∈letters) :
    wires (ControlLoan1589.cell divide j (g j active) (s j active))⊆
      wires (ControlLoan1589.rawReplay divide j letters) := by
  have sub := rawReplay_member divide j letters _ member
  have tape := mixedTape_base_getD (5*j+active) (by first | omega | exact True.intro)
  simpa only [tapeLetter,tape,g,s,Nat.add_assoc] using sub


theorem onPacket_support_into (j : Nat) (P : Program)
    (support : wires P⊆Finset.range 10) (W : Finset Wire)
    (history : wires (NewHistory5.encode base (5*j))⊆W) :
    wires (onPacket j P)⊆W := by
  rw [onPacket,renameProgram_support]
  intro q used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp used
  have bound := Finset.mem_range.mp (support hi)
  simpa only [MeasuredCodec5.label,dif_pos bound] using
    history (NewHistory5.history_site_mem base (5*j) ⟨i,bound⟩)


theorem basePacket_old_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (basePacket divide j)⊆wires (ControlLoan1589.basePacket divide j) := by
  let W := wires (ControlLoan1589.basePacket divide j)
  have history : wires (NewHistory5.encode base (5*j))⊆W := by
    simp only [W,ControlLoan1589.basePacket,wires_append]
    exact Finset.subset_union_right
  have old (active : Nat) (ha : active<5) :
      wires (ControlLoan1589.cell divide j (g j active) (s j active))⊆W := by
    have member : tapeLetter (5*j+active)∈Replay5.letters j :=
      List.mem_map.mpr ⟨active,List.mem_range.mpr ha,rfl⟩
    have sub := rawReplay_cell_at divide j active hj ha _ member
    exact sub.trans (by
      simp only [W,ControlLoan1589.basePacket,wires_append]
      exact Finset.subset_union_right.trans Finset.subset_union_left)
  have cellAt (active : Nat) (ha : active<5) :=
    cell_support_into divide j active 2 hj ha (by decide) W (old active ha) history
  have opening := onPacket_support_into j stageOpen stageOpen_support W history
  have closing := onPacket_support_into j stageClose stageClose_support W history
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_support_into j (stageTransition d k) (stageTransition_support d k hk) W history
  have junction : divide=true → wires (cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2)⊆W := by
    intro eq
    subst divide
    exact cellWith_support_into _ dend_support true j 4 2 hj (by decide) (by decide) W (old 4 (by decide)) history
  cases divide <;> simp only [basePacket,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.union_subset_iff]
  all_goals try split_ifs
  all_goals repeat' apply And.intro
  all_goals first
    | exact junction rfl
    | exact opening
    | exact closing
    | exact transfer false 0 (by decide)
    | exact transfer false 1 (by decide)
    | exact transfer true 0 (by decide)
    | exact transfer true 1 (by decide)
    | exact cellAt 3 (by decide)
    | exact cellAt 4 (by decide)


theorem packet_old_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (packet divide j)⊆wires (ControlLoan1589.packet divide j) :=
  rename_sub _ _ _ (basePacket_old_support divide j hj)


theorem groups_old_support (divide : Bool) (j n : Nat) (bound : j+n≤102) :
    wires (groups divide j n)⊆wires (ControlLoan1589.groups divide j n) := by
  induction n generalizing j with
  | zero => simp [groups,ControlLoan1589.groups,PacketSequence.program,wires]
  | succ n ih =>
    have head := packet_old_support divide j (by first | omega | exact True.intro)
    have rest := ih (j+1) (by first | omega | exact True.intro)
    cases divide <;> simp only [groups,ControlLoan1589.groups,PacketSequence.program,
      Bool.false_eq_true,if_false,if_true,wires_append,Finset.union_subset_iff] at rest ⊢
    · exact ⟨rest.trans Finset.subset_union_left,head.trans Finset.subset_union_right⟩
    · exact ⟨head.trans Finset.subset_union_left,rest.trans Finset.subset_union_right⟩


theorem triple_support_into (a b c : Nat) (ha : a<5) (hb : b<5) (hc : c<5)
    (P : Program) (support : wires P⊆Finset.range 6) (W : Finset Wire)
    (history : wires (NewHistory5.encode base 0)⊆W) : wires (triple a b c P)⊆W := by
  rw [triple,renameProgram_support]
  intro q used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp used
  have _bound := Finset.mem_range.mp (support hi)
  let t := if i/2=0 then a else if i/2=1 then b else c
  have ht : t<5 := by dsimp only [t]; split_ifs <;> assumption
  change (if i%2=0 then g 0 t else s 0 t)∈W
  split
  · exact history (history_controls 0 t ht).1
  · exact history (history_controls 0 t ht).2

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAResourceCounts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed
open ECDSAAdd.Entrant.Rolling1588
open Rolling1588Lifetime
attribute [local irreducible] toffoliCount measurementCount


theorem route_retired_count_member : base 760∈(Q6EndpointCell.ports base (base 2409)).carry.take 254 :=
  List.mem_of_mem_drop route_retired_member


theorem route_selected_counts (source flag : Wire) (P : Program) :
    toffoliCount (SW.selW source flag P)=toffoliCount P ∧
    measurementCount (SW.selW source flag P)=measurementCount P+1 := by
  simp only [SW.selW,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount]
  exact ⟨by omega,by omega⟩


theorem halfWindowWith_counts (P : Program) (j active hole : Nat) :
    toffoliCount (halfWindowWith P j active hole)=toffoliCount P ∧
    measurementCount (halfWindowWith P j active hole)=measurementCount P+1 := by
  have a := ControlLoan1589.loanWindow_counts (g j active) (base 2409) (packetCarry j)
    (renameProgram (Equiv.swap (base 719) (s j hole)) P)
  have b := route_selected_counts (g j active) (base 2409)
    (renameProgram (Equiv.swap (base 719) (s j hole)) P)
  simp only [renameProgram_counts] at b
  exact ⟨a.1.trans b.1,a.2.trans b.2⟩


theorem route_swap_counts : toffoliCount FrontierSW1591.swapBody=256 ∧
    measurementCount FrontierSW1591.swapBody=0 := by
  have a := ECDSAAdd.Entrant.Rolling1588.cell_resources true 0 3 2
  have b := ECDSAAdd.Entrant.Rolling1588.halfWindow_counts true 0 3 2
  have c := route_selected_counts (s 0 3) (base 2409) FrontierSW1591.swapBody
  simp only [ECDSAAdd.Entrant.Rolling1588.cell,if_true,toffoliCount_append,measurementCount_append] at a
  exact ⟨by omega,by omega⟩


theorem cellWith_counts (divide : Bool) (P : Program) (j active hole : Nat) :
    toffoliCount (cellWith divide P j active hole)=toffoliCount P+256 ∧
    measurementCount (cellWith divide P j active hole)=measurementCount P+2 := by
  have a := halfWindowWith_counts P j active hole
  have b := route_selected_counts (s j active) (base 2409) FrontierSW1591.swapBody
  rw [route_swap_counts.1,route_swap_counts.2] at b
  cases divide <;> simp only [cellWith,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append] <;> exact ⟨by omega,by omega⟩


theorem cell_counts (divide : Bool) (j active hole : Nat) :
    toffoliCount (cell divide j active hole)=1273 ∧
    measurementCount (cell divide j active hole)=1019 := by
  have a := cellWith_counts divide (P1Life.half (base 760) divide base (base 2409)) j active hole
  have b := P1Life.half_counts (base 760) divide base (base 2409)
  have shape : cell divide j active hole=cellWith divide (P1Life.half (base 760) divide base (base 2409)) j active hole := by
    cases divide <;> rfl
  rw [shape]
  exact ⟨by omega,by omega⟩


theorem route_junction_counts :
    toffoliCount (P1Life.dstart (base 760) base (base 2409))=1271 ∧
    measurementCount (P1Life.dstart (base 760) base (base 2409))=1271 ∧
    toffoliCount (P1Life.dend (base 760) base (base 2409))=1274 ∧
    measurementCount (P1Life.dend (base 760) base (base 2409))=1274 ∧
    toffoliCount (P1Life.mend (base 760) base (base 2409))=1271 ∧
    measurementCount (P1Life.mend (base 760) base (base 2409))=1271 := by
  have a := P1Life.dstart_counts (base 760) base (base 2409) half_ports_nodup route_retired_count_member
  have b := P1Life.dend_counts (base 760) base (base 2409) half_ports_nodup route_retired_count_member
  have c := P1Life.mend_counts (base 760) base (base 2409) half_ports_nodup route_retired_count_member
  exact ⟨a.1,a.2,b.1,b.2,c.1,c.2⟩


theorem cell_count_delta (divide : Bool) (j active hole : Nat) :
    toffoliCount (cell divide j active hole)+3=toffoliCount (ECDSAAdd.Entrant.Rolling1588.cell divide j active hole) ∧
    measurementCount (cell divide j active hole)+4=measurementCount (ECDSAAdd.Entrant.Rolling1588.cell divide j active hole) := by
  have a := cell_counts divide j active hole
  have b := ECDSAAdd.Entrant.Rolling1588.cell_resources divide j active hole
  exact ⟨by omega,by omega⟩


theorem packet_count_delta (divide : Bool) (j : Nat) :
    toffoliCount (packet divide j)+15=toffoliCount (ECDSAAdd.Entrant.Rolling1588.packet divide j)+(if divide && decide (j=84) then 257 else 0) ∧
    measurementCount (packet divide j)+20=measurementCount (ECDSAAdd.Entrant.Rolling1588.packet divide j)+(if divide && decide (j=84) then 257 else 0) := by
  have a := cell_count_delta divide j 3 2
  have b := cell_count_delta divide j 4 2
  have c := cellWith_counts true (P1Life.dend (base 760) base (base 2409)) j 4 2
  have d := route_junction_counts
  have e := cell_counts true j 4 2
  simp only [packet,ECDSAAdd.Entrant.Rolling1588.packet,renameProgram_counts]
  cases divide <;> by_cases last : j=84
  all_goals simp only [basePacket,ECDSAAdd.Entrant.Rolling1588.basePacket,
    Bool.false_eq_true,if_false,if_true,Bool.false_and,Bool.true_and,
    toffoliCount_append,measurementCount_append]
  all_goals try simp only [last,decide_true,decide_false,Bool.false_eq_true,if_true,if_false] at *
  all_goals try split_ifs at *
  all_goals exact ⟨by omega,by omega⟩


theorem groups_count_delta (divide : Bool) (j n : Nat) (bound : j+n≤102) :
    toffoliCount (groups divide j n)+15*n=
      toffoliCount (ECDSAAdd.Entrant.Rolling1588.groups divide j n)+(if divide && decide (j≤84 ∧ 84<j+n) then 257 else 0) ∧
    measurementCount (groups divide j n)+20*n=
      measurementCount (ECDSAAdd.Entrant.Rolling1588.groups divide j n)+(if divide && decide (j≤84 ∧ 84<j+n) then 257 else 0) := by
  induction n generalizing j with
  | zero => simp [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,toffoliCount,measurementCount]
  | succ n ih =>
    have head := packet_count_delta divide j
    have tail := ih (j+1) (by omega)
    cases divide
    · simp only [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,
        Bool.false_eq_true,if_false,toffoliCount_append,measurementCount_append,
        Bool.false_and] at head tail ⊢
      exact ⟨by omega,by omega⟩
    · have indicator : (if j=84 then 257 else 0)+(if j+1≤84 ∧ 84<j+1+n then 257 else 0)=
          (if j≤84 ∧ 84<j+(n+1) then 257 else 0) := by split_ifs <;> omega
      simp only [Bool.true_and,decide_eq_true_eq] at head tail ⊢
      simp only [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,
        if_true,toffoliCount_append,measurementCount_append] at tail ⊢
      exact ⟨by omega,by omega⟩

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAFieldSlotDeltas =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed BalancedCircuit BalancedField Challenge Baselines
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] gateSlots


def halfSlotSaving (divide : Bool) : Nat := if divide then 34 else 28


theorem halfWindowWith_slots (P : Program) (j active hole : Nat) :
    gateSlots (halfWindowWith P j active hole)=gateSlots P+5 := by
  rw [halfWindowWith,ControlLoan1589.loanWindow_slots,SW.selW_slots,rename_gateSlots]


theorem cellWith_slots (divide : Bool) (P : Program) (j active hole : Nat) :
    gateSlots (cellWith divide P j active hole)=gateSlots P+776 := by
  have half := halfWindowWith_slots P j active hole
  have sw : gateSlots (SW.selW (s j active) (base 2409) FrontierSW1591.swapBody)=771 := by
    rw [SW.selW_slots,FrontierSW1591.swapBody,swapRegisters_gateSlots,
      balancedSharedPorts_r,balancedSharedPorts_y,wireBlock_length,wireBlock_length]
    decide
  cases divide <;> simp only [cellWith,Bool.false_eq_true,if_false,if_true,gateSlots_append,half,sw] <;> omega


theorem cell_slot_delta (divide : Bool) (j active hole : Nat) :
    gateSlots (cell divide j active hole)+halfSlotSaving divide=
      gateSlots (ECDSAAdd.Entrant.Rolling1588.cell divide j active hole) := by
  have a := cellWith_slots divide (P1Life.half (base 760) divide base (base 2409)) j active hole
  have b := slot_half (base 760) divide base (base 2409)
  have c := ECDSAAdd.Entrant.Rolling1588.halfWindow_slots divide j active hole
  have old := slot_record_half divide
  have r := R2Life760.half760_slots divide
  have sw : gateSlots (SW.selW (s j active) (base 2409) FrontierSW1591.swapBody)=771 := by
    rw [SW.selW_slots,FrontierSW1591.swapBody,swapRegisters_gateSlots,
      balancedSharedPorts_r,balancedSharedPorts_y,wireBlock_length,wireBlock_length]
    decide
  have shape : cell divide j active hole=cellWith divide (P1Life.half (base 760) divide base (base 2409)) j active hole := by cases divide <;> rfl
  rw [shape,a]
  cases divide <;> simp only [halfSlotSaving,halfExtra,Bool.false_eq_true,if_false,if_true,
    ECDSAAdd.Entrant.Rolling1588.cell,gateSlots_append,sw] at old r c b ⊢
  all_goals first | omega | exact True.intro


theorem packet_slot_delta (divide : Bool) (j : Nat) :
    gateSlots (packet divide j)+5*halfSlotSaving divide=
      gateSlots (ECDSAAdd.Entrant.Rolling1588.packet divide j)+(if divide && decide (j=84) then 3877 else 0) := by
  have a := cell_slot_delta divide j 3 2
  have b := cell_slot_delta divide j 4 2
  have c := cellWith_slots true (P1Life.dend (base 760) base (base 2409)) j 4 2
  have d := slot_junctions (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have h := slot_half (base 760) true base (base 2409)
  have regular := cellWith_slots true (P1Life.half (base 760) true base (base 2409)) j 4 2
  have eq : cell true j 4 2=cellWith true (P1Life.half (base 760) true base (base 2409)) j 4 2 := rfl
  rw [←eq] at regular
  simp only [packet,ECDSAAdd.Entrant.Rolling1588.packet,rename_gateSlots]
  cases divide <;> by_cases last : j=84
  all_goals simp only [basePacket,ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,
    if_false,if_true,Bool.false_and,Bool.true_and,gateSlots_append]
  all_goals try simp only [last,decide_true,decide_false,Bool.false_eq_true,if_true,if_false] at *
  all_goals first | omega | exact True.intro


theorem groups_slot_delta (divide : Bool) (j n : Nat) (bound : j+n≤102) :
    gateSlots (groups divide j n)+5*halfSlotSaving divide*n=
      gateSlots (ECDSAAdd.Entrant.Rolling1588.groups divide j n)+(if divide && decide (j≤84 ∧ 84<j+n) then 3877 else 0) := by
  induction n generalizing j with
  | zero => simp [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,gateSlots]
  | succ n ih =>
    have head := packet_slot_delta divide j
    have tail := ih (j+1) (by first | omega | exact True.intro)
    cases divide
    · simp only [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,
        Bool.false_eq_true,if_false,gateSlots_append,Bool.false_and,halfSlotSaving] at head tail ⊢
      first | omega | exact True.intro
    · have indicator : (if j=84 then 3877 else 0)+(if j+1≤84 ∧ 84<j+1+n then 3877 else 0)=
          (if j≤84 ∧ 84<j+(n+1) then 3877 else 0) := by split_ifs <;> omega
      simp only [Bool.true_and,decide_eq_true_eq,halfSlotSaving,if_true] at head tail ⊢
      simp only [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,
        if_true,gateSlots_append] at tail ⊢
      first | omega | exact True.intro


theorem placedFirstPacket_slot_delta (divide : Bool) :
    gateSlots (placedFirstPacket divide)=gateSlots (ECDSAAdd.Entrant.Rolling1588.placedFirstPacket divide)+(if divide then 3236 else 3765) := by
  have a := cell_slot_delta divide 0 3 2
  have b := cell_slot_delta divide 0 4 2
  have c := cellWith_slots divide
    (if divide then P1Life.dstart (base 760) base (base 2409) else P1Life.mend (base 760) base (base 2409)) 0 2 4
  have d := slot_junctions (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have e := ECDSAAdd.Entrant.Rolling1588.cell_resources divide 0 2 4
  have hs := R2Life760.half760_slots divide
  have old := slot_record_half divide
  have sw : gateSlots FrontierSW1591.swapBody=768 := by
    rw [FrontierSW1591.swapBody,swapRegisters_gateSlots,balancedSharedPorts_r,balancedSharedPorts_y,
      wireBlock_length,wireBlock_length];decide
  simp only [placedFirstPacket,firstPacket,ECDSAAdd.Entrant.Rolling1588.placedFirstPacket,
    ECDSAAdd.Entrant.Rolling1588.firstPacket,rename_gateSlots,firstCore,ECDSAAdd.Entrant.Rolling1588.firstCore,
    gateSlots_append,G0CarryLoan5.slots]
  cases divide
  all_goals simp only [Bool.false_eq_true,if_false,if_true,halfExtra,halfSlotSaving] at a b c e hs old ⊢
  all_goals simp only [firstBodyShort,ECDSAAdd.Entrant.Rolling1588.firstBodyShort,firstCellsJFront,
    firstRestZFront,firstJointBack,ECDSAAdd.Entrant.Rolling1588.firstCellsJFront,
    ECDSAAdd.Entrant.Rolling1588.firstRestZFront,ECDSAAdd.Entrant.Rolling1588.firstJointBack,
    Bool.false_eq_true,if_false,if_true,gateSlots_append]
  all_goals rw [sw] at e
  all_goals first | omega | exact True.intro
end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module


-- ===== RouteAOddPrefix (M1a: odd division slice, packets 1..84) =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

/-- Division packet `j` whose first division cell runs `dstart` (standard words in, odd words out);
the other four cells are ordinary odd halves. -/
def dstartBasePacket (j : Nat) : Program :=
  onPacket j (dp ++ ParityCodec5New.untwist) ++
    (cellWith true (P1Life.dstart (base 760) base (base 2409)) j 3 2 ++ cell true j 4 2 ++ onPacket j bridge7 ++
      cell true j 4 2 ++ cell true j 3 2 ++ onPacket j bridge5 ++ cell true j 4 2) ++
    onPacket j (ParityCodec5New.twist ++ ep)

def dstartPacket (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (dstartBasePacket j)

/-- The odd division slice of M1a: `dstart` in packet 1, ordinary odd packets 2..83,
`dend` in packet 84.  It replaces the record groups `1..84` of the division kernel. -/
def slice : Program := dstartPacket 1 ++ groups true 2 82 ++ packet true 84

theorem dstartBasePacket_frame (j : Nat) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame centerWord centerWord (codeEncodeAt true (History5.historyMap base (5*j))) origin X Y)
      (dstartBasePacket j)
      (fun state => let V := regularPayload true j origin (X,Y)
        CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt false (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  let Frame (d : Bool) (k : Nat) (V : Fp×Fp) :=
    CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt d k (History5.historyMap base (5*j))) origin V.1 V.2
  have opening (V : Fp×Fp) : StateTriple
      (CodeFrame centerWord centerWord (codeEncodeAt true (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageOpen)
      (CodeFrame centerWord centerWord (stageCodeAt true 0 (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_open_frame centerWord centerWord true j hj origin ctx V.1 V.2 state records input
  have firstStep (V : Fp×Fp) : StateTriple
      (CodeFrame centerWord centerWord (stageCodeAt true 0 (History5.historyMap base (5*j))) origin V.1 V.2)
      (cellWith true (P1Life.dstart (base 760) base (base 2409)) j 3 2)
      (Frame true 0 (regularStep true j origin 0 V)) := by
    intro state records input
    exact regular_cellWith_frame _ true centerWord P1Life.oddWord dstart_law dstart_support
      j 0 0 3 hj (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  have step (d : Bool) (k logical physical : Nat) (hk : k < 3)
      (used : (logical,physical)∈activeSlots d k) (V : Fp×Fp) :
      StateTriple (Frame d k V) (cell d j physical 2)
        (Frame d k (regularStep d j origin logical V)) := by
    intro state records input
    exact regular_cell_frame d j k logical physical hj hk used origin ctx enabled
      V.1 V.2 state records input
  have transfer (d : Bool) (k : Nat) (hk : k < 2) (V : Fp×Fp) :
      StateTriple (Frame d k V) (onPacket j (stageTransition d k)) (Frame d (k+1) V) := by
    intro state records input
    exact regular_transition_frame P1Life.oddWord P1Life.oddWord d j k hj hk origin ctx V.1 V.2 state records input
  have closing (V : Fp×Fp) : StateTriple (Frame true 2 V) (onPacket j stageClose)
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt (!true) (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_close_frame P1Life.oddWord P1Life.oddWord true j hj origin ctx V.1 V.2 state records input
  let V1 := regularStep true j origin 0 (X,Y)
  let V2 := regularStep true j origin 1 V1
  let V3 := regularStep true j origin 2 V2
  let V4 := regularStep true j origin 3 V3
  let V5 := regularStep true j origin 4 V4
  have result := (opening (X,Y)).seq
    ((firstStep (X,Y)).seq
    ((step true 0 1 4 (by decide) (by decide) V1).seq
    ((transfer true 0 (by decide) V2).seq
    ((step true 1 2 4 (by decide) (by decide) V2).seq
    ((step true 1 3 3 (by decide) (by decide) V3).seq
    ((transfer true 1 (by decide) V4).seq
    ((step true 2 4 4 (by decide) (by decide) V4).seq (closing V5))))))))
  simpa only [dstartBasePacket,stageOpen,stageClose,stageTransition,regularPayload,
    if_true,if_false,show ¬(1:Nat)=0 from by decide,List.append_assoc,Bool.not_true] using result

theorem dstartBasePacket_read_support (j : Nat) (hj : j<102) :
    wires (dstartBasePacket j)⊆NewHistory5.groupReadSites base (base 2400)
      (base 2409) (base 2410) (5*j) ∪ {base 2312} := by
  have opening := onPacket_read_support j stageOpen stageOpen_support
  have closing := onPacket_read_support j stageClose stageClose_support
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_read_support j (stageTransition d k) (stageTransition_support d k hk)
  have cellAt (d : Bool) (active : Nat) (ha : active<5) :=
    cell_read_support d j active 2 hj ha (by decide)
  have first := cellWith_read_support true _ dstart_support j 3 2 hj (by decide) (by decide)
  have sites : wires (dstartBasePacket j)⊆FrontierReplay1591.readSites (5*j) := by
    simp only [dstartBasePacket,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨first,cellAt true 4 (by decide)⟩,
      transfer true 0 (by decide)⟩,cellAt true 4 (by decide)⟩,cellAt true 3 (by decide)⟩,
      transfer true 1 (by decide)⟩,cellAt true 4 (by decide)⟩⟩,closing⟩
  exact sites.trans (FrontierReplay1591.readSites_sub (5*j))

theorem dstartBasePacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord j origin X Y) (dstartBasePacket j)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord (j+1) origin V.1 V.2 state) := by
  have nonzero : j≠0 := by omega
  intro state records input
  apply cut_window_frame centerWord centerWord P1Life.oddWord P1Life.oddWord j (j+1) j hj origin X Y _ _
    (dstartBasePacket j) (otherEncodeCut_step base j 102)
    (otherEncodeCut_body_disjoint j j hj origin ctx _ (dstartBasePacket_read_support j hj)) _ state records input
  intro current tape frame
  have normalized : CodeFrame centerWord centerWord (codeEncodeAt true (History5.historyMap base (5*j)))
      origin X Y current := by
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
  have result := dstartBasePacket_frame j hj origin ctx enabled X Y current tape normalized
  simpa [regularPayload_eq true j hj origin enabled,encodeGroup,nonzero,show ¬j+1≤j from by omega] using result

theorem dstartPacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord j origin X Y) (dstartPacket j)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord (j+1) origin V.1 V.2 state) := by
  intro state records input
  have raw := dstartBasePacket_cut_frame j first hj origin ctx enabled X Y state records input
  have same := Replay5.placed_eq (Placement5.pi j) (dstartBasePacket j)
    (fun q hq => Placement5.pi_outside j q hj hq) state records
    (cutFrame_zero_region centerWord centerWord _ origin ctx X Y state input)
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx _ _ _ raw.2)
  change run (dstartPacket j) records state=run (dstartBasePacket j) records state at same
  rw [same]
  exact raw

theorem slice_payload (origin : BasisState) (X Y : Fp) :
    Replay5.groupsPayload true origin 1 84 (X,Y)=
      directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters 84))
        (Replay5.groupsPayload true origin 2 82
          (directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters 1)) (X,Y))) := by
  show PacketSequence.payload true _ 1 (83+1) (X,Y)=_
  rw [PacketSequence.payload.eq_2,if_pos rfl]
  exact route_payload_snoc _ 2 82 _

theorem slice_eq : slice=(dstartPacket 1 ++ groups true 2 82) ++ packet true 84 := rfl

theorem slice_cut_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord 1 origin X Y) slice
      (fun state => let V := Replay5.groupsPayload true origin 1 84 (X,Y)
        CutFrame centerWord centerWord 85 origin V.1 V.2 state) := by
  have a : StateTriple (CutFrame centerWord centerWord 1 origin X Y) (dstartPacket 1)
      (CutFrame P1Life.oddWord P1Life.oddWord 2 origin
        (directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters 1)) (X,Y)).1
        (directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters 1)) (X,Y)).2) := by
    intro state records input
    exact dstartPacket_cut_frame 1 (by decide) (by decide) origin ctx enabled X Y state records input
  have b (V : Fp×Fp) : StateTriple (CutFrame P1Life.oddWord P1Life.oddWord 2 origin V.1 V.2) (groups true 2 82)
      (CutFrame P1Life.oddWord P1Life.oddWord 84 origin
        (Replay5.groupsPayload true origin 2 82 V).1 (Replay5.groupsPayload true origin 2 82 V).2) := by
    intro state records input
    exact groups_cut_frame true 2 82 (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  have c (V : Fp×Fp) := lastDividePacket_cut_frame origin ctx enabled V.1 V.2
  have total := (a.seq (b _)).seq (c _)
  intro state records input
  have r := total state records input
  refine ⟨r.1,?_⟩
  rw [slice_eq]
  show CutFrame centerWord centerWord 85 origin (Replay5.groupsPayload true origin 1 84 (X,Y)).1
    (Replay5.groupsPayload true origin 1 84 (X,Y)).2 _
  rw [slice_payload origin X Y]
  exact r.2

theorem cutFrame_unique_route (cut : Nat) (origin : BasisState) (X Y : Fp)
    (a b : State) (ha : ECDSAAdd.Entrant.Rolling1588.CutFrame cut origin X Y a)
    (hb : ECDSAAdd.Entrant.Rolling1588.CutFrame cut origin X Y b)
    (phase : a.phase = b.phase) : a = b := by
  obtain ⟨rawA, phaseA, frameA, encodedA⟩ := ha
  obtain ⟨rawB, phaseB, frameB, encodedB⟩ := hb
  have rawEq : rawA = rawB := by
    apply State.extensionality
    · exact phaseA.trans (phase.trans phaseB.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ frameA frameB
  rw [encodedA, encodedB, rawEq]

/-- On the record cut frame at cut 1, the odd slice and the record groups `1..84` end in the
same state (independent measurement tapes). -/
theorem slice_run_eq (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (s : State) (fresh old : List Bool)
    (input : ECDSAAdd.Entrant.Rolling1588.CutFrame 1 origin X Y s) :
    run slice fresh s = run (ECDSAAdd.Entrant.Rolling1588.groups true 1 84) old s := by
  have odd := slice_cut_frame origin ctx enabled X Y s fresh input
  have record := ECDSAAdd.Entrant.Rolling1588.groups_cut_frame true 1 84 (by decide) (by decide)
    origin ctx enabled X Y s old input
  exact cutFrame_unique_route 85 origin _ _ _ _ odd.2 record.2 (odd.1.trans record.1.symm)


theorem record_groups_shape : ECDSAAdd.Entrant.Rolling1588.groups true 1 84=
    ECDSAAdd.Entrant.Rolling1588.packet true 1 ++
      (ECDSAAdd.Entrant.Rolling1588.groups true 2 82 ++ ECDSAAdd.Entrant.Rolling1588.packet true 84) := by
  show PacketSequence.program true (ECDSAAdd.Entrant.Rolling1588.packet true) 1 (83+1)=_
  rw [PacketSequence.program.eq_2,if_pos rfl,show (83:Nat)=82+1 from rfl,route_program_snoc]
  rfl

theorem dstartPacket_counts :
    toffoliCount (dstartPacket 1)=toffoliCount (ECDSAAdd.Entrant.Rolling1588.packet true 1)+239 ∧
    measurementCount (dstartPacket 1)=measurementCount (ECDSAAdd.Entrant.Rolling1588.packet true 1)+234 := by
  have a := cell_count_delta true 1 3 2
  have b := cell_count_delta true 1 4 2
  have c := cellWith_counts true (P1Life.dstart (base 760) base (base 2409)) 1 3 2
  have d := route_junction_counts
  have e := cell_counts true 1 3 2
  simp only [dstartPacket,ECDSAAdd.Entrant.Rolling1588.packet,renameProgram_counts,dstartBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,if_true,toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

/-- The odd slice has exactly 749 fewer Toffolis and 1,169 fewer measurements than the record
groups `1..84`. -/
theorem slice_counts :
    toffoliCount slice+749=toffoliCount (ECDSAAdd.Entrant.Rolling1588.groups true 1 84) ∧
    measurementCount slice+1169=measurementCount (ECDSAAdd.Entrant.Rolling1588.groups true 1 84) := by
  have p := dstartPacket_counts
  have g := groups_count_delta true 2 82 (by decide)
  have l := packet_count_delta true 84
  rw [if_neg (by decide)] at g
  rw [if_pos (by decide)] at l
  rw [slice_eq,record_groups_shape]
  simp only [toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem dstartPacket_slots :
    Challenge.gateSlots (dstartPacket 1)+136=Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.packet true 1)+3304 := by
  have a := cell_slot_delta true 1 3 2
  have b := cell_slot_delta true 1 4 2
  have c := cellWith_slots true (P1Life.dstart (base 760) base (base 2409)) 1 3 2
  have d := slot_junctions (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have h := slot_half (base 760) true base (base 2409)
  have regular := cellWith_slots true (P1Life.half (base 760) true base (base 2409)) 1 3 2
  have eq : cell true 1 3 2=cellWith true (P1Life.half (base 760) true base (base 2409)) 1 3 2 := rfl
  rw [←eq] at regular
  simp only [if_true] at h
  simp only [dstartPacket,ECDSAAdd.Entrant.Rolling1588.packet,Baselines.rename_gateSlots,dstartBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,if_true,Challenge.gateSlots_append]
  simp only [halfSlotSaving,if_true] at a b
  omega

/-- The odd slice uses fewer gate slots than the record groups `1..84`. -/
theorem slice_slots_le : Challenge.gateSlots slice≤Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.groups true 1 84) := by
  have p := dstartPacket_slots
  have g := groups_slot_delta true 2 82 (by decide)
  have l := packet_slot_delta true 84
  rw [if_neg (by decide)] at g
  rw [if_pos (by decide)] at l
  simp only [halfSlotSaving,if_true] at g l
  rw [slice_eq,record_groups_shape]
  simp only [Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== RouteARecordHalfLower (support bridge: footprint minus 760 inside the record half) =====
section
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit MappedCompressed RecordedQuantum
attribute [local irreducible] ECDSAAdd.wires

theorem lw_majority (a b c d : Wire) : wires (Arithmetic.majority a b c d)={a,b,c,d} := by
  ext q
  simp [Arithmetic.majority,wires,Instr.wires]
  itauto

theorem lw_signComplement (s x : Wire) : ∀ xs : List Wire, x∈xs → x∈wires (signComplement s xs)
  | [], h => by simp at h
  | y::ys, h => by
    rw [show signComplement s (y::ys)=[Instr.CX s y]++signComplement s ys from rfl,wires_append,
      Finset.mem_union]
    rcases List.mem_cons.mp h with e | h
    · left; subst e; simp [wires,Instr.wires]
    · right; exact lw_signComplement s x ys h

theorem lw_head_or_tail (l : List Wire) (q : Wire) (h : q∈l) : q=l.getD 0 0 ∨ q∈l.drop 1 := by
  cases l with
  | nil => simp at h
  | cons x xs => simpa using h

theorem lw_compareChain (fwd : Bool) (target q : Wire) :
    ∀ (as bs cs : List Wire) (cin : Wire), bs.length=as.length → as.length≤cs.length+1 →
      q∈cs.take (as.length-1) → q∈wires (Q6LifetimeResearch.compareChain fwd as bs cs cin target) := by
  intro as
  induction as with
  | nil => intro bs cs cin _ _ h; simp at h
  | cons a as ih =>
    intro bs cs cin hb hc h
    cases as with
    | nil => simp at h
    | cons a' as' =>
      match bs, cs, hb, hc, h with
      | [], _, hb, _, _ => exact absurd hb (by simp)
      | [_], _, hb, _, _ => exact absurd hb (by simp)
      | _::_::_, [], _, hc, _ => exact absurd hc (by simp)
      | b::b'::bs', c::cs', hb, hc, h =>
        simp only [Q6LifetimeResearch.compareChain,wires_append,Finset.mem_union]
        have h' : q=c ∨ q∈cs'.take as'.length := by
          simpa only [List.length_cons,Nat.add_sub_cancel,List.take_succ_cons,List.mem_cons] using h
        rcases h' with e | h'
        · left; left; rw [lw_majority]; simp [e]
        · left; right
          exact ih (b'::bs') cs' c (by simpa using hb) (by simp only [List.length_cons] at hc ⊢; omega)
            (by simpa only [List.length_cons,Nat.add_sub_cancel] using h')

theorem rh_viaCompare (q : Wire) (h : q∈wires (Q6LifetimeResearch.compare (base 760) true (Q6EndpointCell.ports base (base 2409)))) :
    q∈wires (Q6LifetimeResearch.forward (base 760) false (Q6EndpointCell.ports base (base 2409))) := by
  simp only [Q6LifetimeResearch.forward,wires_append,Finset.mem_union,h,true_or,or_true]

theorem rh_viaRawAdd (q : Wire) (h : q∈wires (Q6LifetimeResearch.rawAdd (base 760) (Q6EndpointCell.ports base (base 2409)))) :
    q∈wires (Q6LifetimeResearch.forward (base 760) false (Q6EndpointCell.ports base (base 2409))) := by
  simp only [Q6LifetimeResearch.forward,wires_append,Finset.mem_union,h,true_or,or_true]

theorem rh_viaFold (q : Wire) (h : q∈wires (Q6LifetimeResearch.fold (base 760) (Q6EndpointCell.ports base (base 2409)))) :
    q∈wires (Q6LifetimeResearch.forward (base 760) false (Q6EndpointCell.ports base (base 2409))) := by
  simp only [Q6LifetimeResearch.forward,wires_append,Finset.mem_union,h,true_or,or_true]

theorem rh_regs (q : Wire) (h : q∈(Q6EndpointCell.ports base (base 2409)).one::(Q6EndpointCell.ports base (base 2409)).r) :
    q∈wires (Q6LifetimeResearch.compare (base 760) true (Q6EndpointCell.ports base (base 2409))) := by
  have n : q∈wires (notRegister ((Q6EndpointCell.ports base (base 2409)).one::(Q6EndpointCell.ports base (base 2409)).r)) := by
    rw [notRegister_wires]; exact List.mem_toFinset.mpr h
  simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rh_y (q : Wire) (h : q∈(Q6EndpointCell.ports base (base 2409)).y) :
    q∈wires (Q6LifetimeResearch.rawAdd (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  have n := lw_signComplement (Q6EndpointCell.ports base (base 2409)).sign q (Q6EndpointCell.ports base (base 2409)).y h
  simp only [Q6LifetimeResearch.rawAdd,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rh_flags (q : Wire) (h : q=(Q6EndpointCell.ports base (base 2409)).parity ∨ q=(Q6EndpointCell.ports base (base 2409)).lower) :
    q∈wires (Q6LifetimeResearch.fold (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  have n : q∈wires [Instr.CCX (Q6EndpointCell.ports base (base 2409)).parity (Q6EndpointCell.ports base (base 2409)).lower (Q6EndpointCell.ports base (base 2409)).one, Instr.CX (Q6EndpointCell.ports base (base 2409)).lower (Q6EndpointCell.ports base (base 2409)).rmsb] := by
    rw [wires,wires,wires,Instr.wires,Instr.wires]
    rcases h with e | e
    · rw [e]; exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    · rw [e]; exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  simp only [Q6LifetimeResearch.fold,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rh_not_one (q : Wire) (hc : q∈(Q6EndpointCell.ports base (base 2409)).carry.take 254) : q≠(Q6EndpointCell.ports base (base 2409)).one := by
  intro e
  have hc' := List.mem_of_mem_take hc
  change q∈(List.range' 512 253).map base++[base 1540,base 1541,base 1026] at hc'
  change q=base 1027 at e
  subst e
  simp only [List.mem_append,List.mem_map,List.mem_range'_1,List.mem_cons,List.not_mem_nil,
    or_false] at hc'
  rcases hc' with ⟨i,hi,e⟩ | e | e | e
  · have := base_injective e; omega
  · have := base_injective e; omega
  · have := base_injective e; omega
  · have := base_injective e; omega

theorem rh_carries_gen (L : Layout) (retired q : Wire) (hne : q≠retired) (hone : q≠L.one)
    (hlen : (L.carry.take 254).length=254) (hyl : (L.y.drop 1).length=255) (hrl : (L.r.drop 1).length=255)
    (hc : q∈L.carry.take 254) : q∈wires (Q6LifetimeResearch.compare retired true L) := by
  have hcs : q∈(Q6Structural.q6Carry L).take 255 := by
    rw [Q6Structural.q6Carry,List.append_assoc,List.take_append]
    exact List.mem_append_left _ (by rw [List.take_of_length_le (by omega)]; exact hc)
  have hcsl : ((Q6Structural.q6Carry L).take 255).length=255 := by
    simp only [List.length_take,Q6Structural.q6Carry,List.length_append,List.length_singleton,hlen]
    omega
  rcases lw_head_or_tail _ q hcs with e | tail
  · have n : q∈wires (Arithmetic.majority (L.y.getD 0 0) (L.r.getD 0 0) L.one
        (((Q6Structural.q6Carry L).take 255).getD 0 0)) := by
      rw [lw_majority,e]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)))
    simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]
  · have hdl : (((Q6Structural.q6Carry L).take 255).drop 1).length=254 := by
      rw [List.length_drop,hcsl]
    have a3 : q∈(((Q6Structural.q6Carry L).take 255).drop 1).take ((L.y.drop 1).length-1) := by
      rw [hyl,List.take_of_length_le (by rw [hdl])]
      exact tail
    have chain := lw_compareChain true L.parity q (L.y.drop 1) (L.r.drop 1)
      (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0)
      (by rw [hyl,hrl]) (by rw [hdl,hyl]) a3
    have n : q∈wires (Q6LifetimeResearch.move retired L.one
        (Q6LifetimeResearch.compareChain true (L.y.drop 1) (L.r.drop 1)
          (((Q6Structural.q6Carry L).take 255).drop 1)
          (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity)) := by
      rw [Q6LifetimeResearch.move,renameProgram_support]
      exact Finset.mem_image.mpr ⟨q,chain,Equiv.swap_apply_of_ne_of_ne hne hone⟩
    simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]

theorem gen_y_length (L : Layout) (hw : L.Widths) : L.y.length=256 :=
  (BalancedCleanup.widths L.toLayout hw).2.2.1

theorem gen_r_length (L : Layout) (hw : L.Widths) : L.r.length=256 :=
  (BalancedCleanup.widths L.toLayout hw).2.1

theorem gen_carry_length (L : Layout) (hw : L.Widths) : (L.carry.take 254).length=254 :=
  (BalancedCleanup.widths L.toLayout hw).2.2.2

theorem gen_carries (L : Layout) (hw : L.Widths) (retired q : Wire) (hne : q≠retired) (hone : q≠L.one)
    (hc : q∈L.carry.take 254) : q∈wires (Q6LifetimeResearch.compare retired true L) :=
  rh_carries_gen L retired q hne hone (gen_carry_length L hw)
    (by rw [List.length_drop,gen_y_length L hw]) (by rw [List.length_drop,gen_r_length L hw]) hc

theorem rh_carries (q : Wire) (hne : q≠base 760) (hc : q∈(Q6EndpointCell.ports base (base 2409)).carry.take 254) :
    q∈wires (Q6LifetimeResearch.compare (base 760) true (Q6EndpointCell.ports base (base 2409))) :=
  gen_carries (Q6EndpointCell.ports base (base 2409)) (Q6EndpointCell.ports_widths base (base 2409))
    (base 760) q hne (rh_not_one q hc) hc

/-- Every wire of the junction footprint except the retired carry `base 760` occurs in the record
lifetime half of the division direction. -/
theorem record_half_lower :
    (P1Life.junctionFootprint (Q6EndpointCell.ports base (base 2409))).erase (base 760)⊆wires (R2Life760.half760 true) := by
  intro q hq
  obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hq
  have fwd : q∈wires (Q6LifetimeResearch.forward (base 760) false (Q6EndpointCell.ports base (base 2409))) ∨ q=base 2409 := by
    simp only [P1Life.junctionFootprint,List.mem_toFinset,List.mem_cons,List.mem_append] at hmem
    rcases hmem with e | e | e | e | (hr | hy) | hc
    · exact Or.inr e
    · exact Or.inl (rh_viaFold q (rh_flags q (Or.inl e)))
    · exact Or.inl (rh_viaFold q (rh_flags q (Or.inr e)))
    · exact Or.inl (rh_viaCompare q (rh_regs q (List.mem_cons.mpr (Or.inl e))))
    · exact Or.inl (rh_viaCompare q (rh_regs q (List.mem_cons_of_mem _ hr)))
    · exact Or.inl (rh_viaRawAdd q (rh_y q hy))
    · exact Or.inl (rh_viaCompare q (rh_carries q hne hc))
  rw [R2Life760.half760_true]
  simp only [Q6LifetimeResearch.half,if_true,wires_append,Finset.mem_union]
  rcases fwd with h | e
  · exact Or.inl (Or.inr h)
  · left; left
    rw [e,wires,wires,Instr.wires]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

end ECDSAAdd.Entrant.RouteA.Rolling1588
end


-- ===== odd45: the odd division slice on packets 1..45 =====
/-
# odd45: odd division slice on packets 1..45

The window needs standard words in the first staircase group's packets 46..53.  The odd division slice
therefore runs `dstart` in packet 1, ordinary odd packets 2..44 and `dend` in packet 45 (`slice45`),
followed by the record packets 46..84 (`dslice`).  It saves 164 T / 389 M against the record packets.
`dendBasePacket` is the division packet with its last cell on `dend`, generic in `j` (`basePacket`
fixes the `dend` packet at `j = 84`).
-/
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

theorem odd45_program_true_add (p : Nat → Program) :
    ∀ (a b j : Nat),
      PacketSequence.program true p j (a + b) =
        PacketSequence.program true p j a ++
          PacketSequence.program true p (j + a) b
  | 0, b, j => by simp [PacketSequence.program]
  | a + 1, b, j => by
      have h : a + 1 + b = (a + b) + 1 := by omega
      rw [h]
      simp only [PacketSequence.program, if_true, List.append_assoc]
      rw [odd45_program_true_add p a b (j + 1)]
      have hj : j + 1 + a = j + (a + 1) := by omega
      rw [hj]

theorem odd45_payload_true_add {α : Type} (step : Nat→α→α) (j m : Nat) :
    ∀ (n : Nat) (Q : α), PacketSequence.payload true step j (m+n) Q =
      PacketSequence.payload true step (j+m) n (PacketSequence.payload true step j m Q)
  | 0, Q => by simp only [Nat.add_zero, PacketSequence.payload]
  | n+1, Q => by
      rw [← Nat.add_assoc, route_payload_snoc, odd45_payload_true_add step j m n Q,
        route_payload_snoc, Nat.add_assoc]

/-- Division packet `j` whose last division cell runs `dend` (odd words in, standard words out);
the other four cells are ordinary odd halves. -/
def dendBasePacket (j : Nat) : Program :=
  onPacket j (dp ++ ParityCodec5New.untwist) ++
    (cell true j 3 2 ++ cell true j 4 2 ++ onPacket j bridge7 ++
      cell true j 4 2 ++ cell true j 3 2 ++ onPacket j bridge5 ++
      cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2) ++
    onPacket j (ParityCodec5New.twist ++ ep)

def dendPacket (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (dendBasePacket j)

/-- odd45 division slice: `dstart` in packet 1, ordinary odd packets 2..44, `dend` in packet 45. -/
def slice45 : Program := dstartPacket 1 ++ groups true 2 43 ++ dendPacket 45

/-- The division first group (deficit 0, packets 1..84) of odd45: odd 1..45, record 46..84. -/
def dslice : Program := slice45 ++ ECDSAAdd.Entrant.Rolling1588.groups true 46 39

theorem slice45_eq : slice45=(dstartPacket 1 ++ groups true 2 43) ++ dendPacket 45 := rfl
theorem dslice_eq : dslice=slice45 ++ ECDSAAdd.Entrant.Rolling1588.groups true 46 39 := rfl
theorem dendBasePacket_frame (j : Nat) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt true (History5.historyMap base (5*j))) origin X Y)
      (dendBasePacket j)
      (fun state => let V := regularPayload true j origin (X,Y)
        CodeFrame centerWord centerWord (codeEncodeAt false (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  let Frame (d : Bool) (k : Nat) (V : Fp×Fp) :=
    CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt d k (History5.historyMap base (5*j))) origin V.1 V.2
  have opening (d : Bool) (V : Fp×Fp) : StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt d (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageOpen) (Frame d 0 V) := by
    intro state records input
    exact regular_open_frame P1Life.oddWord P1Life.oddWord d j hj origin ctx V.1 V.2 state records input
  have step (d : Bool) (k logical physical : Nat) (hk : k < 3)
      (used : (logical,physical)∈activeSlots d k) (V : Fp×Fp) :
      StateTriple (Frame d k V) (cell d j physical 2)
        (Frame d k (regularStep d j origin logical V)) := by
    intro state records input
    exact regular_cell_frame d j k logical physical hj hk used origin ctx enabled
      V.1 V.2 state records input
  have transfer (d : Bool) (k : Nat) (hk : k < 2) (V : Fp×Fp) :
      StateTriple (Frame d k V) (onPacket j (stageTransition d k)) (Frame d (k+1) V) := by
    intro state records input
    exact regular_transition_frame P1Life.oddWord P1Life.oddWord d j k hj hk origin ctx V.1 V.2 state records input
  have closing (d : Bool) (V : Fp×Fp) : StateTriple (CodeFrame centerWord centerWord (stageCodeAt d 2 (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageClose)
      (CodeFrame centerWord centerWord (codeEncodeAt (!d) (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_close_frame centerWord centerWord d j hj origin ctx V.1 V.2 state records input
  have finalStep (V : Fp×Fp) : StateTriple (Frame true 2 V)
      (cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2)
      (CodeFrame centerWord centerWord (stageCodeAt true 2 (History5.historyMap base (5*j))) origin
        (regularStep true j origin 4 V).1 (regularStep true j origin 4 V).2) := by
    intro state records input
    exact regular_cellWith_frame _ true P1Life.oddWord centerWord dend_law dend_support
      j 2 4 4 hj (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  let V1 := regularStep true j origin 0 (X,Y)
  let V2 := regularStep true j origin 1 V1
  let V3 := regularStep true j origin 2 V2
  let V4 := regularStep true j origin 3 V3
  let V5 := regularStep true j origin 4 V4
  have result := (opening true (X,Y)).seq
    ((step true 0 0 3 (by decide) (by decide) (X,Y)).seq
    ((step true 0 1 4 (by decide) (by decide) V1).seq
    ((transfer true 0 (by decide) V2).seq
    ((step true 1 2 4 (by decide) (by decide) V2).seq
    ((step true 1 3 3 (by decide) (by decide) V3).seq
    ((transfer true 1 (by decide) V4).seq
    ((finalStep V4).seq (closing true V5))))))))
  simpa only [dendBasePacket,stageOpen,stageClose,stageTransition,regularPayload,
    if_true,if_false,show ¬(1:Nat)=0 from by decide,List.append_assoc] using result

theorem dendBasePacket_read_support (j : Nat) (hj : j<102) :
    wires (dendBasePacket j)⊆NewHistory5.groupReadSites base (base 2400)
      (base 2409) (base 2410) (5*j) ∪ {base 2312} := by
  have opening := onPacket_read_support j stageOpen stageOpen_support
  have closing := onPacket_read_support j stageClose stageClose_support
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_read_support j (stageTransition d k) (stageTransition_support d k hk)
  have cellAt (d : Bool) (active : Nat) (ha : active<5) :=
    cell_read_support d j active 2 hj ha (by decide)
  have last := cellWith_read_support true _ dend_support j 4 2 hj (by decide) (by decide)
  have sites : wires (dendBasePacket j)⊆FrontierReplay1591.readSites (5*j) := by
    simp only [dendBasePacket,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨cellAt true 3 (by decide),cellAt true 4 (by decide)⟩,
      transfer true 0 (by decide)⟩,cellAt true 4 (by decide)⟩,cellAt true 3 (by decide)⟩,
      transfer true 1 (by decide)⟩,last⟩⟩,closing⟩
  exact sites.trans (FrontierReplay1591.readSites_sub (5*j))

theorem dendBasePacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord j origin X Y) (dendBasePacket j)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame centerWord centerWord (j+1) origin V.1 V.2 state) := by
  have nonzero : j≠0 := by omega
  intro state records input
  apply cut_window_frame P1Life.oddWord P1Life.oddWord centerWord centerWord j (j+1) j hj origin X Y _ _
    (dendBasePacket j) (otherEncodeCut_step base j 102)
    (otherEncodeCut_body_disjoint j j hj origin ctx _ (dendBasePacket_read_support j hj)) _ state records input
  intro current tape frame
  have normalized : CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt true (History5.historyMap base (5*j)))
      origin X Y current := by
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
  have result := dendBasePacket_frame j hj origin ctx enabled X Y current tape normalized
  simpa [regularPayload_eq true j hj origin enabled,encodeGroup,nonzero,show ¬j+1≤j from by omega] using result

theorem dendPacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord j origin X Y) (dendPacket j)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame centerWord centerWord (j+1) origin V.1 V.2 state) := by
  intro state records input
  have raw := dendBasePacket_cut_frame j first hj origin ctx enabled X Y state records input
  have same := Replay5.placed_eq (Placement5.pi j) (dendBasePacket j)
    (fun q hq => Placement5.pi_outside j q hj hq) state records
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx X Y state input)
    (cutFrame_zero_region centerWord centerWord _ origin ctx _ _ _ raw.2)
  change run (dendPacket j) records state=run (dendBasePacket j) records state at same
  rw [same]
  exact raw

theorem slice45_payload (origin : BasisState) (X Y : Fp) :
    Replay5.groupsPayload true origin 1 45 (X,Y)=
      directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters 45))
        (Replay5.groupsPayload true origin 2 43
          (directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters 1)) (X,Y))) := by
  show PacketSequence.payload true _ 1 (44+1) (X,Y)=_
  rw [PacketSequence.payload.eq_2,if_pos rfl]
  exact route_payload_snoc _ 2 43 _

theorem slice45_cut_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord 1 origin X Y) slice45
      (fun state => let V := Replay5.groupsPayload true origin 1 45 (X,Y)
        CutFrame centerWord centerWord 46 origin V.1 V.2 state) := by
  have a : StateTriple (CutFrame centerWord centerWord 1 origin X Y) (dstartPacket 1)
      (CutFrame P1Life.oddWord P1Life.oddWord 2 origin
        (directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters 1)) (X,Y)).1
        (directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters 1)) (X,Y)).2) := by
    intro state records input
    exact dstartPacket_cut_frame 1 (by decide) (by decide) origin ctx enabled X Y state records input
  have b (V : Fp×Fp) : StateTriple (CutFrame P1Life.oddWord P1Life.oddWord 2 origin V.1 V.2) (groups true 2 43)
      (CutFrame P1Life.oddWord P1Life.oddWord 45 origin
        (Replay5.groupsPayload true origin 2 43 V).1 (Replay5.groupsPayload true origin 2 43 V).2) := by
    intro state records input
    exact groups_cut_frame true 2 43 (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  have c (V : Fp×Fp) := dendPacket_cut_frame 45 (by decide) (by decide) origin ctx enabled V.1 V.2
  have total := (a.seq (b _)).seq (c _)
  intro state records input
  have r := total state records input
  refine ⟨r.1,?_⟩
  rw [slice45_eq]
  show CutFrame centerWord centerWord 46 origin (Replay5.groupsPayload true origin 1 45 (X,Y)).1
    (Replay5.groupsPayload true origin 1 45 (X,Y)).2 _
  rw [slice45_payload origin X Y]
  have r2 := r.2
  simp only [Prod.mk.eta] at r2
  exact r2

theorem dslice_payload (origin : BasisState) (V : Fp×Fp) :
    Replay5.groupsPayload true origin 1 84 V=
      Replay5.groupsPayload true origin 46 39 (Replay5.groupsPayload true origin 1 45 V) :=
  odd45_payload_true_add _ 1 45 39 V

theorem dslice_cut_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord 1 origin X Y) dslice
      (fun state => let V := Replay5.groupsPayload true origin 1 84 (X,Y)
        CutFrame centerWord centerWord 85 origin V.1 V.2 state) := by
  have a : StateTriple (CutFrame centerWord centerWord 1 origin X Y) slice45
      (CutFrame centerWord centerWord 46 origin
        (Replay5.groupsPayload true origin 1 45 (X,Y)).1 (Replay5.groupsPayload true origin 1 45 (X,Y)).2) := by
    intro state records input
    exact slice45_cut_frame origin ctx enabled X Y state records input
  have b (V : Fp×Fp) : StateTriple (CutFrame centerWord centerWord 46 origin V.1 V.2)
      (ECDSAAdd.Entrant.Rolling1588.groups true 46 39)
      (CutFrame centerWord centerWord 85 origin
        (Replay5.groupsPayload true origin 46 39 (V.1,V.2)).1 (Replay5.groupsPayload true origin 46 39 (V.1,V.2)).2) := by
    intro state records input
    exact ECDSAAdd.Entrant.Rolling1588.groups_cut_frame true 46 39 (by decide) (by decide)
      origin ctx enabled V.1 V.2 state records input
  have total := a.seq (b _)
  intro state records input
  have r := total state records input
  refine ⟨r.1,?_⟩
  rw [dslice_eq]
  show CutFrame centerWord centerWord 85 origin (Replay5.groupsPayload true origin 1 84 (X,Y)).1
    (Replay5.groupsPayload true origin 1 84 (X,Y)).2 _
  rw [dslice_payload origin (X,Y)]
  have r2 := r.2
  simp only [Prod.mk.eta] at r2
  exact r2

/-- On the record cut frame at cut 1, the odd45 division group and the record groups `1..84` end
in the same state (independent measurement tapes). -/
theorem dslice_run_eq (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (s : State) (fresh old : List Bool)
    (input : ECDSAAdd.Entrant.Rolling1588.CutFrame 1 origin X Y s) :
    run dslice fresh s = run (ECDSAAdd.Entrant.Rolling1588.groups true 1 84) old s := by
  have odd := dslice_cut_frame origin ctx enabled X Y s fresh input
  have record := ECDSAAdd.Entrant.Rolling1588.groups_cut_frame true 1 84 (by decide) (by decide)
    origin ctx enabled X Y s old input
  exact cutFrame_unique_route 85 origin _ _ _ _ odd.2 record.2 (odd.1.trans record.1.symm)

theorem record_groups45_shape : ECDSAAdd.Entrant.Rolling1588.groups true 1 45=
    (ECDSAAdd.Entrant.Rolling1588.packet true 1 ++ ECDSAAdd.Entrant.Rolling1588.groups true 2 43) ++
      ECDSAAdd.Entrant.Rolling1588.packet true 45 := by
  have h : ECDSAAdd.Entrant.Rolling1588.groups true 1 45=
      ECDSAAdd.Entrant.Rolling1588.packet true 1 ++
        (ECDSAAdd.Entrant.Rolling1588.groups true 2 43 ++ ECDSAAdd.Entrant.Rolling1588.packet true 45) := by
    show PacketSequence.program true (ECDSAAdd.Entrant.Rolling1588.packet true) 1 (44+1)=_
    rw [PacketSequence.program.eq_2,if_pos rfl,show (44:Nat)=43+1 from rfl,route_program_snoc]
    rfl
  rw [h,List.append_assoc]

theorem record_groups_split_true : ECDSAAdd.Entrant.Rolling1588.groups true 1 84=
    ECDSAAdd.Entrant.Rolling1588.groups true 1 45 ++ ECDSAAdd.Entrant.Rolling1588.groups true 46 39 :=
  odd45_program_true_add _ 45 39 1

theorem dendPacket_counts (j : Nat) :
    toffoliCount (dendPacket j)=toffoliCount (ECDSAAdd.Entrant.Rolling1588.packet true j)+242 ∧
    measurementCount (dendPacket j)=measurementCount (ECDSAAdd.Entrant.Rolling1588.packet true j)+237 := by
  have a := cell_count_delta true j 3 2
  have b := cell_count_delta true j 4 2
  have c := cellWith_counts true (P1Life.dend (base 760) base (base 2409)) j 4 2
  have d := route_junction_counts
  have e := cell_counts true j 4 2
  simp only [dendPacket,ECDSAAdd.Entrant.Rolling1588.packet,renameProgram_counts,dendBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,if_true,toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

/-- odd45: the division slice `1..45` has exactly 164 fewer Toffolis and 389 fewer measurements
than the record groups `1..45`. -/
theorem slice45_counts :
    toffoliCount slice45+164=toffoliCount (ECDSAAdd.Entrant.Rolling1588.groups true 1 45) ∧
    measurementCount slice45+389=measurementCount (ECDSAAdd.Entrant.Rolling1588.groups true 1 45) := by
  have p := dstartPacket_counts
  have g := groups_count_delta true 2 43 (by decide)
  have l := dendPacket_counts 45
  rw [if_neg (by decide)] at g
  rw [slice45_eq,record_groups45_shape]
  simp only [toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

/-- odd45: the division first group saves 164 T / 389 M against the record groups `1..84`. -/
theorem dslice_counts :
    toffoliCount dslice+164=toffoliCount (ECDSAAdd.Entrant.Rolling1588.groups true 1 84) ∧
    measurementCount dslice+389=measurementCount (ECDSAAdd.Entrant.Rolling1588.groups true 1 84) := by
  have s := slice45_counts
  rw [dslice_eq,record_groups_split_true]
  simp only [toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem dendPacket_slots (j : Nat) :
    Challenge.gateSlots (dendPacket j)+170=Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.packet true j)+3877 := by
  have a := cell_slot_delta true j 3 2
  have b := cell_slot_delta true j 4 2
  have c := cellWith_slots true (P1Life.dend (base 760) base (base 2409)) j 4 2
  have d := slot_junctions (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have h := slot_half (base 760) true base (base 2409)
  have regular := cellWith_slots true (P1Life.half (base 760) true base (base 2409)) j 4 2
  have eq : cell true j 4 2=cellWith true (P1Life.half (base 760) true base (base 2409)) j 4 2 := rfl
  rw [←eq] at regular
  simp only [if_true] at h
  simp only [dendPacket,ECDSAAdd.Entrant.Rolling1588.packet,Baselines.rename_gateSlots,dendBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,if_true,Challenge.gateSlots_append]
  simp only [halfSlotSaving,if_true] at a b
  omega

/-- odd45: the division first group still uses fewer gate slots than the record groups `1..84`
(the slice `1..45` alone saves 435 slots). -/
theorem dslice_slots_le : Challenge.gateSlots dslice≤Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.groups true 1 84) := by
  have p := dstartPacket_slots
  have g := groups_slot_delta true 2 43 (by decide)
  have l := dendPacket_slots 45
  rw [if_neg (by decide)] at g
  simp only [halfSlotSaving,if_true] at g
  rw [dslice_eq,slice45_eq,record_groups_split_true,record_groups45_shape]
  simp only [Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.RouteA.Rolling1588
end


section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
/-- the odd division slice on packets 1..45 uses 435 gate slots fewer than the record packets. -/
theorem slice45_slots :
    Challenge.gateSlots slice45 + 435 = Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.groups true 1 45) := by
  have p := dstartPacket_slots
  have g := groups_slot_delta true 2 43 (by decide)
  have l := dendPacket_slots 45
  rw [if_neg (by decide)] at g
  simp only [halfSlotSaving,if_true] at g
  rw [slice45_eq,record_groups45_shape]
  simp only [Challenge.gateSlots_append]
  omega
end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== cell support: the hosted odd45 slice is physical, stays inside the
-- record packets 1..45 and, on a record cut frame at cut 1, ends where the record packets 1..45 end =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

/-- on the record cut frame at cut 1, the odd45 division slice and the record packets
`1..45` end in the same state (independent measurement tapes). -/
theorem slice45_run_eq (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (s : State) (fresh old : List Bool)
    (input : ECDSAAdd.Entrant.Rolling1588.CutFrame 1 origin X Y s) :
    run slice45 fresh s = run (ECDSAAdd.Entrant.Rolling1588.groups true 1 45) old s := by
  have odd := slice45_cut_frame origin ctx enabled X Y s fresh input
  have record := ECDSAAdd.Entrant.Rolling1588.groups_cut_frame true 1 45 (by decide) (by decide)
    origin ctx enabled X Y s old input
  exact cutFrame_unique_route 46 origin _ _ _ _ odd.2 record.2 (odd.1.trans record.1.symm)

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed Challenge RecordedQuantum
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] GatePhysical P1Life.half P1Life.dstart P1Life.dend P1Life.mend

/-- the `dstart` packet is physical. -/
theorem c45_dstartBasePacket_physical (j : Nat) (hj : j<102) : GatePhysical (dstartBasePacket j) := by
  have opening := onPacket_physical j hj stageOpen stageOpen_support stage_physical.1
  have closing := onPacket_physical j hj stageClose stageClose_support stage_physical.2.1
  have t0 := onPacket_physical j hj (stageTransition true 0) (stageTransition_support true 0 (by decide))
    (stage_physical.2.2 true 0 (by decide))
  have t1 := onPacket_physical j hj (stageTransition true 1) (stageTransition_support true 1 (by decide))
    (stage_physical.2.2 true 1 (by decide))
  have c3 := cell_physical true j 3 2 hj (by decide)
  have c4 := cell_physical true j 4 2 hj (by decide)
  have d0 := cellWith_physical true _ route_junction_physical.1 j 3 2 hj (by decide)
  simp only [dstartBasePacket,gatePhysical_append]
  exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨d0,c4⟩,t0⟩,c4⟩,c3⟩,t1⟩,c4⟩⟩,closing⟩

/-- the generic `dend` packet of odd45 is physical. -/
theorem c45_dendBasePacket_physical (j : Nat) (hj : j<102) : GatePhysical (dendBasePacket j) := by
  have opening := onPacket_physical j hj stageOpen stageOpen_support stage_physical.1
  have closing := onPacket_physical j hj stageClose stageClose_support stage_physical.2.1
  have t0 := onPacket_physical j hj (stageTransition true 0) (stageTransition_support true 0 (by decide))
    (stage_physical.2.2 true 0 (by decide))
  have t1 := onPacket_physical j hj (stageTransition true 1) (stageTransition_support true 1 (by decide))
    (stage_physical.2.2 true 1 (by decide))
  have c3 := cell_physical true j 3 2 hj (by decide)
  have c4 := cell_physical true j 4 2 hj (by decide)
  have e0 := cellWith_physical true _ route_junction_physical.2.1 j 4 2 hj (by decide)
  simp only [dendBasePacket,gatePhysical_append]
  exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨c3,c4⟩,t0⟩,c4⟩,c3⟩,t1⟩,e0⟩⟩,closing⟩

/-- the odd45 division slice is physical. -/
theorem c45_slice45_physical : GatePhysical slice45 := by
  rw [slice45_eq]
  simp only [gatePhysical_append]
  exact ⟨⟨gatePhysical_rename _ (shifted (Placement5.pi 1)).injective _ (c45_dstartBasePacket_physical 1 (by decide)),
    groups_physical true 2 43 (by decide)⟩,
    gatePhysical_rename _ (shifted (Placement5.pi 45)).injective _ (c45_dendBasePacket_physical 45 (by decide))⟩

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairLoanGroupSupport
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
attribute [local irreducible] wires StairLoan.half760Loan StairGroups.halfWindow StairGroups.cell Rolling1588.onPacket

/-- an odd division cell stays inside the record cell. -/
theorem c45_oddCell_sub (P : Program) (hP : RouteA.Rolling1588.HalfSupport P) (j active hole : Nat) :
    wires (RouteA.Rolling1588.cellWith true P j active hole) ⊆ wires (Rolling1588.cell true j active hole) := by
  have h : wires (RouteA.Rolling1588.halfWindowWith P j active hole) ⊆
      wires (Rolling1588.halfWindow true j active hole) := by
    unfold RouteA.Rolling1588.halfWindowWith Rolling1588.halfWindow
    exact loanWindow_sub _ _ _ _ _ (rename_sub _ _ _ (hP.trans RouteA.Rolling1588.record_half_lower))
  simp only [RouteA.Rolling1588.cellWith,Rolling1588.cell,if_true]
  exact append_sub _ _ _ _ h (Finset.Subset.refl _)

theorem c45_oddPlainCell_sub (j active hole : Nat) :
    wires (RouteA.Rolling1588.cell true j active hole) ⊆ wires (Rolling1588.cell true j active hole) := by
  have h := c45_oddCell_sub _ (RouteA.Rolling1588.half_support true) j active hole
  simpa only [RouteA.Rolling1588.cellWith,RouteA.Rolling1588.cell,RouteA.Rolling1588.halfWindow,if_true] using h

theorem c45_oddBasePacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.basePacket true j) ⊆ wires (Rolling1588.basePacket true j) := by
  have c := fun active hole => c45_oddPlainCell_sub j active hole
  have last : wires (if j=84 then RouteA.Rolling1588.cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2
      else RouteA.Rolling1588.cell true j 4 2) ⊆ wires (Rolling1588.cell true j 4 2) := by
    split
    · exact c45_oddCell_sub _ RouteA.Rolling1588.dend_support j 4 2
    · exact c 4 2
  simp only [RouteA.Rolling1588.basePacket,Rolling1588.basePacket,if_true]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ (c 3 2) (c 4 2)) (Finset.Subset.refl _)) (c 4 2)) (c 3 2))
    (Finset.Subset.refl _)) last

theorem c45_dstartBasePacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.dstartBasePacket j) ⊆ wires (Rolling1588.basePacket true j) := by
  have c := fun active hole => c45_oddPlainCell_sub j active hole
  have hd := c45_oddCell_sub _ RouteA.Rolling1588.dstart_support j 3 2
  simp only [RouteA.Rolling1588.dstartBasePacket,Rolling1588.basePacket,if_true]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ hd (c 4 2)) (Finset.Subset.refl _)) (c 4 2)) (c 3 2))
    (Finset.Subset.refl _)) (c 4 2)

/-- the generic `dend` packet of odd45 stays inside the record division packet. -/
theorem c45_dendBasePacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.dendBasePacket j) ⊆ wires (Rolling1588.basePacket true j) := by
  have c := fun active hole => c45_oddPlainCell_sub j active hole
  have hd := c45_oddCell_sub _ RouteA.Rolling1588.dend_support j 4 2
  simp only [RouteA.Rolling1588.dendBasePacket,Rolling1588.basePacket,if_true]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ (c 3 2) (c 4 2)) (Finset.Subset.refl _)) (c 4 2)) (c 3 2))
    (Finset.Subset.refl _)) hd

theorem c45_oddPacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.packet true j) ⊆ wires (Rolling1588.packet true j) := by
  unfold RouteA.Rolling1588.packet Rolling1588.packet
  exact rename_sub _ _ _ (c45_oddBasePacket_sub j)

/-- the odd45 division slice stays inside the record packets `1..45` (no new wire). -/
theorem c45_slice45_sub : wires RouteA.Rolling1588.slice45 ⊆ wires (Rolling1588.groups true 1 45) := by
  rw [RouteA.Rolling1588.record_groups45_shape,RouteA.Rolling1588.slice45_eq]
  apply append_sub
  · apply append_sub
    · unfold RouteA.Rolling1588.dstartPacket Rolling1588.packet
      exact rename_sub _ _ _ (c45_dstartBasePacket_sub 1)
    · unfold RouteA.Rolling1588.groups Rolling1588.groups
      exact sequence_sub true _ _ (fun i => c45_oddPacket_sub i) 2 43
  · unfold RouteA.Rolling1588.dendPacket Rolling1588.packet
    exact rename_sub _ _ _ (c45_dendBasePacket_sub 45)

end ECDSAAdd.Entrant.StairLoanGroupSupport
end

-- ===== end odd division cell =====

-- ===== odd multiplication cell on packets 45..1 =====
-- The multiplication-kernel half cell `mstart` and its packets, the odd multiplication slices (`mslice` on
-- packets 84..1, `mslice45` on packets 45..1) with their frames, counts and slots, and the cell lemmas used by
-- the window.
/-
# Odd-word slice in the multiplication field

A multiplication packet runs `mstart` (standard words in, odd words out) in place of its first
multiplication half, or `mend` (odd words in, standard words out) in place of its last one; the
other halves are the ordinary odd halves of `P1Life`.  `mstart` is the inverse of `dend`: recode Y
to the odd code, accept the standard X (`acceptStandard`, the involution of `emitStandard`'s core),
then the odd inverse tail (`junctionOddRest`).
-/

-- ===== P1MultiplyStart =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def acceptStandard (retired : Wire) (L : Layout) : Program :=
  [.CX L.rmsb L.lower] ++ signComplement L.lower L.r ++ [.X L.lower] ++ notRegister L.low ++
    Q6LifetimeResearch.move retired L.rmsb
      (literalConstAdd L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral)


def junctionOddRest (retired : Wire) (L : Layout) : Program :=
  prepareCompare L++exposure L++compare retired false L++(exposure L).reverse++
    (prepareCompare L).reverse++BiasedInverse.unbiasView L++unfoldStep retired L++
    rotateLeft (rawTarget L)++[.CX L.parity L.r0]++rawSub retired L


def mstart (retired : Wire) (w : Nat → Wire) (sign : Wire) : Program :=
  let L := Q6EndpointCell.ports w sign
  [.X sign] ++ recode retired true L L.y ++ acceptStandard retired L ++
    junctionOddRest retired L ++ [.X sign]


theorem junction_accept_standard_value (X : Int) (hx : Centered X) :
    (2^255-1-encodeWord 255 (magnitude X)+BalancedCleanup.positiveLiteral+
      (negative (junctionToOdd X)).toNat)%2^255=encodeWord 255 (oddNormalized (junctionToOdd X)) := by
  rw [junction_complement_encoded,Nat.add_assoc,DirectPass.encoded_add_nat,Nat.cast_add]
  have c := constants
  have lit : (BalancedCleanup.positiveLiteral : Int)=h-1 :=
    Int.toNat_of_nonneg (by omega)
  rw [lit]
  congr 1
  have sg := junction_to_odd_sign X hx
  unfold oddNormalized magnitude
  rw [sg]
  unfold Centered at hx
  by_cases xn : X<0 <;> simp [negative,xn,junctionToOdd] <;> omega


theorem accept_standard_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (X Y : Int) (hx : Centered X) :
    Triple (DirectPass.AfterHalf L retired origin X Y) (acceptStandard retired L)
      (DirectPass.AfterComparison DirectPass.oddEncoding L retired origin (junctionToOdd X) Y) := by
  have range : -((2^255 : Nat) : Int)≤X ∧ X<((2^255 : Nat) : Int) := by
    have hp := constants
    unfold Centered at hx
    omega
  have a := DirectPass.prepare_sign_boundary_wide retired L hw hn origin X Y range
  have b := junction_flip_lower retired L hn origin (encodeWord 255 (magnitude X))
    (encodeWord 256 Y) false (negative X)
  have c := junction_not_low retired L hw hn origin (encodeWord 255 (magnitude X))
    (encodeWord 256 Y) false (!negative X)
  have d := junction_literal_boundary retired L hw hn (List.mem_of_mem_drop member) origin
    (2^255-1-encodeWord 255 (magnitude X)) (encodeWord 256 Y)
    BalancedCleanup.positiveLiteral false (!negative X)
  rw [←junction_to_odd_sign X hx] at b c d
  rw [junction_accept_standard_value X hx] at d
  simpa only [acceptStandard,BalancedCleanup.prepareSign,List.append_assoc] using
    Triple.seq a (Triple.seq b (Triple.seq c d))


theorem junction_odd_rest_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (F Y : Int) (hf : OddDomain F) (hy : OddDomain Y) :
    Triple (DirectPass.AfterComparison DirectPass.oddEncoding L retired origin F Y)
      (junctionOddRest retired L)
      (DirectPass.AfterHalf L retired origin (oddInverse (origin L.sign) F Y) Y) := by
  let B := origin L.sign
  let R := oddInverse B F Y
  let T := oddSum B R Y
  have hr : OddDomain R := oddRep_bounds _
  have ht := oddSum_bounds B R Y hr hy
  have result : oddFold T=F := oddForward_inverse B F Y hf hy
  have interval : originalParity T=decide (oddComparisonLeft F<oddComparisonY B F Y) := by
    have h := oddComparison_parity B R Y hr hy
    rw [result] at h
    exact h
  have mt : retired∈L.carry.take 254 := List.mem_of_mem_drop member
  have c := comparison_to_fold retired L hw hn member origin T F Y hf hy interval
  have d := fold_to_raw retired L hw hn mt origin T Y ht
  rw [result] at d
  have e := rawSub_boundary retired L hw hn member origin B R Y hr hy rfl
  simpa only [junctionOddRest,List.append_assoc] using Triple.seq c (Triple.seq d e)


theorem junction_sgo_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (X Y : Int) (hx : Centered X) (hy : OddDomain Y) :
    Triple (DirectPass.AfterHalf L retired origin X Y) (acceptStandard retired L++junctionOddRest retired L)
      (DirectPass.AfterHalf L retired origin (oddInverse (origin L.sign) (junctionToOdd X) Y) Y) :=
  Triple.seq (accept_standard_boundary retired L hw hn member origin X Y hx)
    (junction_odd_rest_boundary retired L hw hn member origin _ Y (junction_to_odd_bounds X hx) hy)


theorem junction_to_odd_center (x : Fp) : junctionToOdd (centerFp x)=oddRep x := by
  rw [←junction_to_odd_rep _ (centerFp_bounds x),centerFp_cast]


theorem junction_sgo_frame (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (X Y : Fp) (s : State) (m : List Bool)
    (rv : regValue L.r s.basis=centerWord X) (yv : regValue L.y s.basis=oddWord Y)
    (flags : DirectPass.LiveFlags L false false false s.basis)
    (clean : DirectPass.CleanExcept (L.carry.take 254) retired s.basis) :
    let p := acceptStandard retired L++junctionOddRest retired L
    (run p m s).phase=s.phase ∧ DirectPass.WordFrame L.r s.basis
      (oddWord (2*X+(if !s.basis L.sign then -Y else Y))) (run p m s).basis := by
  have b := junction_sgo_boundary retired L hw hn member s.basis
    (centerFp X) (oddRep Y) (centerFp_bounds X) (oddRep_bounds Y)
  have h := DirectPass.kernel_frame_of_boundary retired L (centerFp X) (oddRep Y) _ _
    s m rv yv flags clean b
  have field := kernel_field false (!s.basis L.sign) X Y
  simp only [kernelResult,Bool.false_eq_true,if_false,Bool.not_not] at field
  rw [junction_to_odd_center X,field] at h
  exact h


theorem mstart_frame (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1)
    (origin : BasisState) (clean : Q6EndpointCell.Clean w origin) (X Y : Fp) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y
      origin (centerWord X) (centerWord Y)) (mstart retired w sign)
      (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (oddWord (2*X+(if origin sign then -Y else Y))) (oddWord Y)) := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  apply DirectPass.half_frame_from_pair_kernel retired w sign hn origin clean (centerWord X) (centerWord Y)
    (fun B => oddWord (2*X+(if B then -Y else Y))) (oddWord Y) (mstart retired w sign)
    (recode retired true L L.y++(acceptStandard retired L++junctionOddRest retired L))
    (by simp only [mstart,L,List.append_assoc])
  intro s m rv yv flags carry
  have h := junction_recode_before retired true L hw hn (List.mem_of_mem_drop member)
    (acceptStandard retired L++junctionOddRest retired L) (centerWord X) (centerWord Y)
    (fun B => oddWord (2*X+(if !B then -Y else Y))) s m rv yv flags carry (by
      intro u tape ur uy uf uc
      have uy' : regValue L.y u.basis=oddWord Y := by
        simpa only [if_true,←recode_odd_word,oddWord] using uy
      exact junction_sgo_frame retired L hw hn member X Y u tape ur uy' uf uc)
  simpa only [if_true,←recode_odd_word,oddWord] using h


theorem junction_odd_rest_counts (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (junctionOddRest retired L)=766 ∧ measurementCount (junctionOddRest retired L)=766 := by
  have b := p1_compare_counts false retired L hw
  have c := p1_fold_counts true retired L hw
  have d := p1_raw_sub_counts retired L hw
  have pc := p1_compare_view_counts L
  have ub := p1_unbias_view_counts L
  have rot := rotate_counts (rawTarget L)
  simp only [Bool.false_eq_true,if_false,if_true] at b c
  simp only [junctionOddRest,toffoliCount_append,measurementCount_append,toffoliCount_reverse,
    measurementCount_reverse,b.1,b.2,c.1,c.2,d.1,d.2,pc.1,pc.2,ub.1,ub.2,rot.2.2.1,rot.2.2.2,
    exposure,toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem accept_standard_counts (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (acceptStandard retired L)=254 ∧ measurementCount (acceptStandard retired L)=254 := by
  have lowlen : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have a := literalConstAdd_counts L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral
    (by simp [List.length_take,hw.2.2,lowlen])
  rw [lowlen] at a
  simp only [acceptStandard,toffoliCount_append,measurementCount_append,Q6LifetimeResearch.move,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,a.1,a.2,
    (notRegister_counts L.low).1,(notRegister_counts L.low).2,
    (signComplement_counts L.lower L.r).1,(signComplement_counts L.lower L.r).2,
    toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem mstart_counts (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈(Q6EndpointCell.ports w sign).carry.take 254) :
    toffoliCount (mstart retired w sign)=1274 ∧ measurementCount (mstart retired w sign)=1274 := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have a := recode_counts retired true L hw hn member
  have b := accept_standard_counts retired L hw
  have c := junction_odd_rest_counts retired L hw
  dsimp only [L] at a b c
  simp only [mstart,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,
    toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem accept_standard_resources (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    JunctionSafe ((junctionFootprint L).erase retired) (acceptStandard retired L) := by
  have nt := junction_not_resources retired L hn member L.low (by
    intro q hq
    simp [BalancedCleanup.Layout.r,hq])
  have lit := junction_literal_resources retired L hn BalancedCleanup.positiveLiteral
  have lower := junction_small_resources retired L hw hn member [.X L.lower]
    (by simp [junctionCliffordPieces])
  have top := junction_small_resources retired L hw hn member [.CX L.rmsb L.lower]
    (by simp [junctionCliffordPieces])
  have sc := junction_sign_resources retired L hn member L.lower L.r
    (by simp) (by intro q hq; simp [hq]) (by
      intro bad; exact BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [bad]))
  simp only [acceptStandard,junction_safe_append]
  exact ⟨⟨⟨⟨top,sc⟩,lower⟩,nt⟩,lit⟩


theorem mstart_resources (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1) :
    GatePhysical (mstart retired w sign) ∧ wires (mstart retired w sign)⊆
      (junctionFootprint (Q6EndpointCell.ports w sign)).erase retired := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have mt := List.mem_of_mem_drop member
  have acc := accept_standard_resources retired L hw hn mt
  have recoder := recode_y_resources retired true L hw hn mt
  have rest := junction_rest_resources true retired L hw hn member
  have flip := junction_small_resources retired L hw hn mt [.X L.sign]
    (by simp [junctionCliffordPieces])
  change JunctionSafe ((junctionFootprint L).erase retired) (mstart retired w sign)
  have shape : mstart retired w sign=[.X sign]++recode retired true L L.y++
      acceptStandard retired L++junctionOddRest retired L++[.X sign] := rfl
  rw [shape]
  simp only [junction_safe_append]
  exact ⟨⟨⟨⟨flip,recoder⟩,acc⟩,rest⟩,flip⟩

end ECDSAAdd.Entrant.P1Life
end

-- ===== RouteAMultiplyStartSlots =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic Challenge Baselines BalancedCircuit


theorem slot_odd_rest (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (P1Life.junctionOddRest retired L)=14371 := by
  have len := slot_layout_lengths L hw
  have comp := slot_compare true false retired L hw
  have fold := slot_fold true true retired L hw
  have sub := slot_raw_sub true retired L hw
  have views := slot_views L hw
  have rt := rotate_slots (rawTarget L)
  simp only [Bool.false_eq_true,if_false,if_true] at comp fold sub
  simp only [P1Life.junctionOddRest,gateSlots_append,reverse_gateSlots,
    comp,fold,sub,views.1,views.2.1,views.2.2.1,views.2.2.2,rt.1,rt.2,len.2.2.2.1,
    P1Life.exposure,gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]


/-- `acceptStandard` has the gates of `emitStandard` in another order (no kernel evaluation). -/
theorem slot_accept_standard (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (P1Life.acceptStandard retired L)=3532 := by
  have e := (slot_junction_emits retired L hw).2.2
  simp only [P1Life.acceptStandard,P1Life.emitStandard,gateSlots_append] at e ⊢
  omega


theorem slot_mstart (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈(Q6EndpointCell.ports w sign).carry.take 254) :
    gateSlots (P1Life.mstart retired w sign)=20986 := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have acc := slot_accept_standard retired L hw
  have rest := slot_odd_rest retired L hw
  have odd := slot_recode retired true L hw hn member
  simp only [if_true] at odd
  dsimp only [L] at acc rest odd
  simp only [P1Life.mstart,gateSlots_append,acc,rest,odd,
    gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]

end ECDSAAdd.Entrant.RouteA
end

-- ===== RouteARecordHalfLowerFalse (support bridge: footprint minus 760 inside the record multiply half) =====
section
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit MappedCompressed RecordedQuantum
attribute [local irreducible] ECDSAAdd.wires

theorem rhf_viaCompare (q : Wire) (h : q∈wires (Q6LifetimeResearch.compare (base 760) false (Q6EndpointCell.ports base (base 2409)))) :
    q∈wires (Q6LifetimeResearch.inverse (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  simp only [Q6LifetimeResearch.inverse,wires_append,Finset.mem_union,h,true_or,or_true]

theorem rhf_viaRawSub (q : Wire) (h : q∈wires (Q6LifetimeResearch.rawSubTail (base 760) (Q6EndpointCell.ports base (base 2409)))) :
    q∈wires (Q6LifetimeResearch.inverse (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  simp only [Q6LifetimeResearch.inverse,wires_append,Finset.mem_union,h,true_or,or_true]

theorem rhf_regs (q : Wire) (h : q∈(Q6EndpointCell.ports base (base 2409)).one::(Q6EndpointCell.ports base (base 2409)).r) :
    q∈wires (Q6LifetimeResearch.compare (base 760) false (Q6EndpointCell.ports base (base 2409))) := by
  have n : q∈wires (notRegister ((Q6EndpointCell.ports base (base 2409)).one::(Q6EndpointCell.ports base (base 2409)).r)) := by
    rw [notRegister_wires]; exact List.mem_toFinset.mpr h
  simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rhf_y (q : Wire) (h : q∈(Q6EndpointCell.ports base (base 2409)).y) :
    q∈wires (Q6LifetimeResearch.rawSubTail (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  have n := lw_signComplement (Q6EndpointCell.ports base (base 2409)).sign q (Q6EndpointCell.ports base (base 2409)).y h
  simp only [Q6LifetimeResearch.rawSubTail,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rhf_parity (q : Wire) (h : q=(Q6EndpointCell.ports base (base 2409)).parity) :
    q∈wires (Q6LifetimeResearch.inverse (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  have n : q∈wires [Instr.CX (Q6EndpointCell.ports base (base 2409)).parity (Q6EndpointCell.ports base (base 2409)).r0] := by
    rw [wires,wires,Instr.wires,h]
    exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  simp only [Q6LifetimeResearch.inverse,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rhf_lower (q : Wire) (h : q=(Q6EndpointCell.ports base (base 2409)).lower) :
    q∈wires (Q6LifetimeResearch.inverse (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  have n : q∈wires [Instr.CX (Q6EndpointCell.ports base (base 2409)).rmsb (Q6EndpointCell.ports base (base 2409)).lower] := by
    rw [wires,wires,Instr.wires,h]
    exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have m : q∈wires (BalancedCleanup.prepareSign (Q6EndpointCell.ports base (base 2409)).toLayout) := by
    simp only [BalancedCleanup.prepareSign,wires_append,Finset.mem_union]
    exact Or.inl n
  simp only [Q6LifetimeResearch.inverse,wires_append,Finset.mem_union,m,true_or,or_true]

theorem rhf_carries_gen (fwd : Bool) (L : Layout) (retired q : Wire) (hne : q≠retired) (hone : q≠L.one)
    (hlen : (L.carry.take 254).length=254) (hyl : (L.y.drop 1).length=255) (hrl : (L.r.drop 1).length=255)
    (hc : q∈L.carry.take 254) : q∈wires (Q6LifetimeResearch.compare retired fwd L) := by
  have hcs : q∈(Q6Structural.q6Carry L).take 255 := by
    rw [Q6Structural.q6Carry,List.append_assoc,List.take_append]
    exact List.mem_append_left _ (by rw [List.take_of_length_le (by omega)]; exact hc)
  have hcsl : ((Q6Structural.q6Carry L).take 255).length=255 := by
    simp only [List.length_take,Q6Structural.q6Carry,List.length_append,List.length_singleton,hlen]
    omega
  rcases lw_head_or_tail _ q hcs with e | tail
  · have n : q∈wires (Arithmetic.majority (L.y.getD 0 0) (L.r.getD 0 0) L.one
        (((Q6Structural.q6Carry L).take 255).getD 0 0)) := by
      rw [lw_majority,e]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)))
    simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]
  · have hdl : (((Q6Structural.q6Carry L).take 255).drop 1).length=254 := by
      rw [List.length_drop,hcsl]
    have a3 : q∈(((Q6Structural.q6Carry L).take 255).drop 1).take ((L.y.drop 1).length-1) := by
      rw [hyl,List.take_of_length_le (by rw [hdl])]
      exact tail
    have chain := lw_compareChain fwd L.parity q (L.y.drop 1) (L.r.drop 1)
      (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0)
      (by rw [hyl,hrl]) (by rw [hdl,hyl]) a3
    have n : q∈wires (Q6LifetimeResearch.move retired L.one
        (Q6LifetimeResearch.compareChain fwd (L.y.drop 1) (L.r.drop 1)
          (((Q6Structural.q6Carry L).take 255).drop 1)
          (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity)) := by
      rw [Q6LifetimeResearch.move,renameProgram_support]
      exact Finset.mem_image.mpr ⟨q,chain,Equiv.swap_apply_of_ne_of_ne hne hone⟩
    simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rhf_carries (q : Wire) (hne : q≠base 760) (hc : q∈(Q6EndpointCell.ports base (base 2409)).carry.take 254) :
    q∈wires (Q6LifetimeResearch.compare (base 760) false (Q6EndpointCell.ports base (base 2409))) :=
  rhf_carries_gen false (Q6EndpointCell.ports base (base 2409)) (base 760) q hne (rh_not_one q hc)
    (gen_carry_length _ (Q6EndpointCell.ports_widths base (base 2409)))
    (by rw [List.length_drop,gen_y_length _ (Q6EndpointCell.ports_widths base (base 2409))])
    (by rw [List.length_drop,gen_r_length _ (Q6EndpointCell.ports_widths base (base 2409))]) hc

/-- Every wire of the junction footprint except the retired carry `base 760` occurs in the record
lifetime half of the multiplication direction. -/
theorem record_half_lower_false :
    (P1Life.junctionFootprint (Q6EndpointCell.ports base (base 2409))).erase (base 760)⊆wires (R2Life760.half760 false) := by
  intro q hq
  obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hq
  have inv : q∈wires (Q6LifetimeResearch.inverse (base 760) (Q6EndpointCell.ports base (base 2409))) ∨ q=base 2409 := by
    simp only [P1Life.junctionFootprint,List.mem_toFinset,List.mem_cons,List.mem_append] at hmem
    rcases hmem with e | e | e | e | (hr | hy) | hc
    · exact Or.inr e
    · exact Or.inl (rhf_parity q e)
    · exact Or.inl (rhf_lower q e)
    · exact Or.inl (rhf_viaCompare q (rhf_regs q (List.mem_cons.mpr (Or.inl e))))
    · exact Or.inl (rhf_viaCompare q (rhf_regs q (List.mem_cons_of_mem _ hr)))
    · exact Or.inl (rhf_viaRawSub q (rhf_y q hy))
    · exact Or.inl (rhf_viaCompare q (rhf_carries q hne hc))
  rw [R2Life760.half760_false]
  rcases inv with h | e
  · simp only [Q6LifetimeResearch.half,Bool.false_eq_true,if_false,wires_append,Finset.mem_union,h,
      true_or,or_true]
  · rw [e]
    simp only [Q6LifetimeResearch.half,Bool.false_eq_true,if_false,wires_append,Finset.mem_union]
    left; left; left
    rw [wires,wires,Instr.wires]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== RouteA odd multiplication slice (packets 84..1) =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

theorem mstart_law :
    HalfLaw (P1Life.mstart (base 760) base (base 2409)) false centerWord P1Life.oddWord := by
  intro origin clean X Y
  simpa only [Bool.false_eq_true,if_false] using
    P1Life.mstart_frame _ _ _ half_ports_nodup route_retired_member origin clean X Y

theorem mstart_support : HalfSupport (P1Life.mstart (base 760) base (base 2409)) :=
  (P1Life.mstart_resources _ _ _ half_ports_nodup route_retired_member).2

theorem route_mstart_physical : GatePhysical (P1Life.mstart (base 760) base (base 2409)) :=
  (P1Life.mstart_resources _ _ _ half_ports_nodup route_retired_member).1

theorem route_mstart_counts :
    toffoliCount (P1Life.mstart (base 760) base (base 2409))=1274 ∧
    measurementCount (P1Life.mstart (base 760) base (base 2409))=1274 :=
  P1Life.mstart_counts (base 760) base (base 2409) half_ports_nodup route_retired_count_member

/-- Multiplication packet `j` whose first multiplication cell runs `mstart` (standard words in,
odd words out); the other four cells are ordinary odd halves. -/
def mstartBasePacket (j : Nat) : Program :=
  onPacket j (dp ++ ParityCodec5New.untwist) ++
    (cellWith false (P1Life.mstart (base 760) base (base 2409)) j 4 2 ++ onPacket j bridge5 ++
      cell false j 3 2 ++ cell false j 4 2 ++ onPacket j bridge7inv ++
      cell false j 4 2 ++ cell false j 3 2) ++
    onPacket j (ParityCodec5New.twist ++ ep)

def mstartPacket (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (mstartBasePacket j)

/-- Multiplication packet `j` whose last multiplication cell runs `mend` (odd words in,
standard words out). -/
def mendBasePacket (j : Nat) : Program :=
  onPacket j (dp ++ ParityCodec5New.untwist) ++
    (cell false j 4 2 ++ onPacket j bridge5 ++
      cell false j 3 2 ++ cell false j 4 2 ++ onPacket j bridge7inv ++
      cell false j 4 2 ++ cellWith false (P1Life.mend (base 760) base (base 2409)) j 3 2) ++
    onPacket j (ParityCodec5New.twist ++ ep)

def mendPacket (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (mendBasePacket j)

/-- The odd multiplication slice on packets 84..1: `mstart` in packet 84, ordinary odd packets 83..2,
`mend` in packet 1 (the window runs the slice on packets 45..1, `mslice45`). -/
def mslice : Program := mstartPacket 84 ++ groups false 2 82 ++ mendPacket 1

theorem mslice_eq : mslice=(mstartPacket 84 ++ groups false 2 82) ++ mendPacket 1 := rfl

theorem mstartBasePacket_frame (j : Nat) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame centerWord centerWord (codeEncodeAt false (History5.historyMap base (5*j))) origin X Y)
      (mstartBasePacket j)
      (fun state => let V := regularPayload false j origin (X,Y)
        CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt true (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  let Frame (d : Bool) (k : Nat) (V : Fp×Fp) :=
    CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt d k (History5.historyMap base (5*j))) origin V.1 V.2
  have opening (V : Fp×Fp) : StateTriple
      (CodeFrame centerWord centerWord (codeEncodeAt false (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageOpen)
      (CodeFrame centerWord centerWord (stageCodeAt false 0 (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_open_frame centerWord centerWord false j hj origin ctx V.1 V.2 state records input
  have firstStep (V : Fp×Fp) : StateTriple
      (CodeFrame centerWord centerWord (stageCodeAt false 0 (History5.historyMap base (5*j))) origin V.1 V.2)
      (cellWith false (P1Life.mstart (base 760) base (base 2409)) j 4 2)
      (Frame false 0 (regularStep false j origin 4 V)) := by
    intro state records input
    exact regular_cellWith_frame _ false centerWord P1Life.oddWord mstart_law mstart_support
      j 0 4 4 hj (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  have step (d : Bool) (k logical physical : Nat) (hk : k < 3)
      (used : (logical,physical)∈activeSlots d k) (V : Fp×Fp) :
      StateTriple (Frame d k V) (cell d j physical 2)
        (Frame d k (regularStep d j origin logical V)) := by
    intro state records input
    exact regular_cell_frame d j k logical physical hj hk used origin ctx enabled
      V.1 V.2 state records input
  have transfer (d : Bool) (k : Nat) (hk : k < 2) (V : Fp×Fp) :
      StateTriple (Frame d k V) (onPacket j (stageTransition d k)) (Frame d (k+1) V) := by
    intro state records input
    exact regular_transition_frame P1Life.oddWord P1Life.oddWord d j k hj hk origin ctx V.1 V.2 state records input
  have closing (V : Fp×Fp) : StateTriple (Frame false 2 V) (onPacket j stageClose)
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt (!false) (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_close_frame P1Life.oddWord P1Life.oddWord false j hj origin ctx V.1 V.2 state records input
  let V1 := regularStep false j origin 4 (X,Y)
  let V2 := regularStep false j origin 3 V1
  let V3 := regularStep false j origin 2 V2
  let V4 := regularStep false j origin 1 V3
  let V5 := regularStep false j origin 0 V4
  have result := (opening (X,Y)).seq
    ((firstStep (X,Y)).seq
    ((transfer false 0 (by decide) V1).seq
    ((step false 1 3 3 (by decide) (by decide) V1).seq
    ((step false 1 2 4 (by decide) (by decide) V2).seq
    ((transfer false 1 (by decide) V3).seq
    ((step false 2 1 4 (by decide) (by decide) V3).seq
    ((step false 2 0 3 (by decide) (by decide) V4).seq (closing V5))))))))
  simpa only [mstartBasePacket,stageOpen,stageClose,stageTransition,regularPayload,
    Bool.false_eq_true,if_false,if_true,show ¬(1:Nat)=0 from by decide,List.append_assoc,
    Bool.not_false] using result

theorem mendBasePacket_frame (j : Nat) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt false (History5.historyMap base (5*j))) origin X Y)
      (mendBasePacket j)
      (fun state => let V := regularPayload false j origin (X,Y)
        CodeFrame centerWord centerWord (codeEncodeAt true (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  let Frame (d : Bool) (k : Nat) (V : Fp×Fp) :=
    CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt d k (History5.historyMap base (5*j))) origin V.1 V.2
  have opening (V : Fp×Fp) : StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt false (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageOpen) (Frame false 0 V) := by
    intro state records input
    exact regular_open_frame P1Life.oddWord P1Life.oddWord false j hj origin ctx V.1 V.2 state records input
  have step (d : Bool) (k logical physical : Nat) (hk : k < 3)
      (used : (logical,physical)∈activeSlots d k) (V : Fp×Fp) :
      StateTriple (Frame d k V) (cell d j physical 2)
        (Frame d k (regularStep d j origin logical V)) := by
    intro state records input
    exact regular_cell_frame d j k logical physical hj hk used origin ctx enabled
      V.1 V.2 state records input
  have transfer (d : Bool) (k : Nat) (hk : k < 2) (V : Fp×Fp) :
      StateTriple (Frame d k V) (onPacket j (stageTransition d k)) (Frame d (k+1) V) := by
    intro state records input
    exact regular_transition_frame P1Life.oddWord P1Life.oddWord d j k hj hk origin ctx V.1 V.2 state records input
  have finalStep (V : Fp×Fp) : StateTriple (Frame false 2 V)
      (cellWith false (P1Life.mend (base 760) base (base 2409)) j 3 2)
      (CodeFrame centerWord centerWord (stageCodeAt false 2 (History5.historyMap base (5*j))) origin
        (regularStep false j origin 0 V).1 (regularStep false j origin 0 V).2) := by
    intro state records input
    exact regular_cellWith_frame _ false P1Life.oddWord centerWord mend_law mend_support
      j 2 0 3 hj (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  have closing (V : Fp×Fp) : StateTriple
      (CodeFrame centerWord centerWord (stageCodeAt false 2 (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageClose)
      (CodeFrame centerWord centerWord (codeEncodeAt (!false) (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_close_frame centerWord centerWord false j hj origin ctx V.1 V.2 state records input
  let V1 := regularStep false j origin 4 (X,Y)
  let V2 := regularStep false j origin 3 V1
  let V3 := regularStep false j origin 2 V2
  let V4 := regularStep false j origin 1 V3
  let V5 := regularStep false j origin 0 V4
  have result := (opening (X,Y)).seq
    ((step false 0 4 4 (by decide) (by decide) (X,Y)).seq
    ((transfer false 0 (by decide) V1).seq
    ((step false 1 3 3 (by decide) (by decide) V1).seq
    ((step false 1 2 4 (by decide) (by decide) V2).seq
    ((transfer false 1 (by decide) V3).seq
    ((step false 2 1 4 (by decide) (by decide) V3).seq
    ((finalStep V4).seq (closing V5))))))))
  simpa only [mendBasePacket,stageOpen,stageClose,stageTransition,regularPayload,
    Bool.false_eq_true,if_false,if_true,show ¬(1:Nat)=0 from by decide,List.append_assoc,
    Bool.not_false] using result

theorem mstartBasePacket_read_support (j : Nat) (hj : j<102) :
    wires (mstartBasePacket j)⊆NewHistory5.groupReadSites base (base 2400)
      (base 2409) (base 2410) (5*j) ∪ {base 2312} := by
  have opening := onPacket_read_support j stageOpen stageOpen_support
  have closing := onPacket_read_support j stageClose stageClose_support
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_read_support j (stageTransition d k) (stageTransition_support d k hk)
  have cellAt (d : Bool) (active : Nat) (ha : active<5) :=
    cell_read_support d j active 2 hj ha (by decide)
  have first := cellWith_read_support false _ mstart_support j 4 2 hj (by decide) (by decide)
  have sites : wires (mstartBasePacket j)⊆FrontierReplay1591.readSites (5*j) := by
    simp only [mstartBasePacket,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨first,transfer false 0 (by decide)⟩,
      cellAt false 3 (by decide)⟩,cellAt false 4 (by decide)⟩,transfer false 1 (by decide)⟩,
      cellAt false 4 (by decide)⟩,cellAt false 3 (by decide)⟩⟩,closing⟩
  exact sites.trans (FrontierReplay1591.readSites_sub (5*j))

theorem mendBasePacket_read_support (j : Nat) (hj : j<102) :
    wires (mendBasePacket j)⊆NewHistory5.groupReadSites base (base 2400)
      (base 2409) (base 2410) (5*j) ∪ {base 2312} := by
  have opening := onPacket_read_support j stageOpen stageOpen_support
  have closing := onPacket_read_support j stageClose stageClose_support
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_read_support j (stageTransition d k) (stageTransition_support d k hk)
  have cellAt (d : Bool) (active : Nat) (ha : active<5) :=
    cell_read_support d j active 2 hj ha (by decide)
  have last := cellWith_read_support false _ mend_support j 3 2 hj (by decide) (by decide)
  have sites : wires (mendBasePacket j)⊆FrontierReplay1591.readSites (5*j) := by
    simp only [mendBasePacket,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨cellAt false 4 (by decide),transfer false 0 (by decide)⟩,
      cellAt false 3 (by decide)⟩,cellAt false 4 (by decide)⟩,transfer false 1 (by decide)⟩,
      cellAt false 4 (by decide)⟩,last⟩⟩,closing⟩
  exact sites.trans (FrontierReplay1591.readSites_sub (5*j))

theorem mstartBasePacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord (j+1) origin X Y) (mstartBasePacket j)
      (fun state => let V := directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord j origin V.1 V.2 state) := by
  have nonzero : j≠0 := by omega
  intro state records input
  apply cut_window_frame centerWord centerWord P1Life.oddWord P1Life.oddWord (j+1) j j hj origin X Y _ _
    (mstartBasePacket j) (otherEncodeCut_step base j 102).symm
    (otherEncodeCut_body_disjoint (j+1) j hj origin ctx _ (mstartBasePacket_read_support j hj)) _ state records input
  intro current tape frame
  have normalized : CodeFrame centerWord centerWord (codeEncodeAt false (History5.historyMap base (5*j)))
      origin X Y current := by
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
  have result := mstartBasePacket_frame j hj origin ctx enabled X Y current tape normalized
  simpa [regularPayload_eq false j hj origin enabled,encodeGroup,nonzero,show ¬j+1≤j from by omega] using result

theorem mendBasePacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord (j+1) origin X Y) (mendBasePacket j)
      (fun state => let V := directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame centerWord centerWord j origin V.1 V.2 state) := by
  have nonzero : j≠0 := by omega
  intro state records input
  apply cut_window_frame P1Life.oddWord P1Life.oddWord centerWord centerWord (j+1) j j hj origin X Y _ _
    (mendBasePacket j) (otherEncodeCut_step base j 102).symm
    (otherEncodeCut_body_disjoint (j+1) j hj origin ctx _ (mendBasePacket_read_support j hj)) _ state records input
  intro current tape frame
  have normalized : CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt false (History5.historyMap base (5*j)))
      origin X Y current := by
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
  have result := mendBasePacket_frame j hj origin ctx enabled X Y current tape normalized
  simpa [regularPayload_eq false j hj origin enabled,encodeGroup,nonzero,show ¬j+1≤j from by omega] using result

theorem mstartPacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord (j+1) origin X Y) (mstartPacket j)
      (fun state => let V := directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord j origin V.1 V.2 state) := by
  intro state records input
  have raw := mstartBasePacket_cut_frame j first hj origin ctx enabled X Y state records input
  have same := Replay5.placed_eq (Placement5.pi j) (mstartBasePacket j)
    (fun q hq => Placement5.pi_outside j q hj hq) state records
    (cutFrame_zero_region centerWord centerWord _ origin ctx X Y state input)
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx _ _ _ raw.2)
  change run (mstartPacket j) records state=run (mstartBasePacket j) records state at same
  rw [same]
  exact raw

theorem mendPacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord (j+1) origin X Y) (mendPacket j)
      (fun state => let V := directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame centerWord centerWord j origin V.1 V.2 state) := by
  intro state records input
  have raw := mendBasePacket_cut_frame j first hj origin ctx enabled X Y state records input
  have same := Replay5.placed_eq (Placement5.pi j) (mendBasePacket j)
    (fun q hq => Placement5.pi_outside j q hj hq) state records
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx X Y state input)
    (cutFrame_zero_region centerWord centerWord _ origin ctx _ _ _ raw.2)
  change run (mendPacket j) records state=run (mendBasePacket j) records state at same
  rw [same]
  exact raw

theorem route_program_snoc_false (P : Nat→Program) (j n : Nat) :
    PacketSequence.program false P j (n+1)=P (j+n)++PacketSequence.program false P j n := by
  induction n generalizing j with
  | zero => simp only [PacketSequence.program,Bool.false_eq_true,if_false,List.append_nil,List.nil_append,Nat.add_zero]
  | succ n ih =>
    rw [PacketSequence.program,if_neg (by decide),ih,PacketSequence.program,if_neg (by decide)]
    simp only [List.append_assoc,show j+(n+1)=(j+1)+n from by omega]

theorem route_payload_snoc_false {α : Type} (step : Nat→α→α) (j n : Nat) (V : α) :
    PacketSequence.payload false step j (n+1) V=
      PacketSequence.payload false step j n (step (j+n) V) := by
  induction n generalizing j V with
  | zero => simp only [PacketSequence.payload,Bool.false_eq_true,if_false,Nat.add_zero]
  | succ n ih =>
    rw [PacketSequence.payload,if_neg (by decide),ih,PacketSequence.payload,if_neg (by decide)]
    rw [show j+(n+1)=(j+1)+n from by omega]

theorem mslice_payload (origin : BasisState) (X Y : Fp) :
    Replay5.groupsPayload false origin 1 84 (X,Y)=
      directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters 1))
        (Replay5.groupsPayload false origin 2 82
          (directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters 84)) (X,Y))) := by
  show PacketSequence.payload false _ 1 (83+1) (X,Y)=_
  rw [PacketSequence.payload.eq_2,if_neg (by decide),route_payload_snoc_false]
  rfl

theorem mslice_cut_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord 85 origin X Y) mslice
      (fun state => let V := Replay5.groupsPayload false origin 1 84 (X,Y)
        CutFrame centerWord centerWord 1 origin V.1 V.2 state) := by
  have a : StateTriple (CutFrame centerWord centerWord 85 origin X Y) (mstartPacket 84)
      (CutFrame P1Life.oddWord P1Life.oddWord 84 origin
        (directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters 84)) (X,Y)).1
        (directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters 84)) (X,Y)).2) := by
    intro state records input
    exact mstartPacket_cut_frame 84 (by decide) (by decide) origin ctx enabled X Y state records input
  have b (V : Fp×Fp) : StateTriple (CutFrame P1Life.oddWord P1Life.oddWord 84 origin V.1 V.2) (groups false 2 82)
      (CutFrame P1Life.oddWord P1Life.oddWord 2 origin
        (Replay5.groupsPayload false origin 2 82 V).1 (Replay5.groupsPayload false origin 2 82 V).2) := by
    intro state records input
    exact groups_cut_frame false 2 82 (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  have c (V : Fp×Fp) := mendPacket_cut_frame 1 (by decide) (by decide) origin ctx enabled V.1 V.2
  have total := (a.seq (b _)).seq (c _)
  intro state records input
  have r := total state records input
  refine ⟨r.1,?_⟩
  rw [mslice_eq]
  show CutFrame centerWord centerWord 1 origin (Replay5.groupsPayload false origin 1 84 (X,Y)).1
    (Replay5.groupsPayload false origin 1 84 (X,Y)).2 _
  rw [mslice_payload origin X Y]
  -- `r.2` carries the pair `(p.1, p.2)`; folding it with `Prod.mk.eta` keeps the kernel from
  -- evaluating the 82-packet payload.
  have r2 := r.2
  simp only [Prod.mk.eta] at r2
  exact r2

/-- On the record cut frame at cut 85, the odd multiplication slice and the record groups
`84..1` end in the same state (independent measurement tapes). -/
theorem mslice_run_eq (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (s : State) (fresh old : List Bool)
    (input : ECDSAAdd.Entrant.Rolling1588.CutFrame 85 origin X Y s) :
    run mslice fresh s = run (ECDSAAdd.Entrant.Rolling1588.groups false 1 84) old s := by
  have odd := mslice_cut_frame origin ctx enabled X Y s fresh input
  have record := ECDSAAdd.Entrant.Rolling1588.groups_cut_frame false 1 84 (by decide) (by decide)
    origin ctx enabled X Y s old input
  exact cutFrame_unique_route 1 origin _ _ _ _ odd.2 record.2 (odd.1.trans record.1.symm)

theorem record_groups_shape_false : ECDSAAdd.Entrant.Rolling1588.groups false 1 84=
    (ECDSAAdd.Entrant.Rolling1588.packet false 84 ++
      ECDSAAdd.Entrant.Rolling1588.groups false 2 82) ++ ECDSAAdd.Entrant.Rolling1588.packet false 1 := by
  show PacketSequence.program false (ECDSAAdd.Entrant.Rolling1588.packet false) 1 (83+1)=_
  rw [PacketSequence.program.eq_2,if_neg (by decide),show (83:Nat)=82+1 from rfl,route_program_snoc_false]
  rfl

theorem mstartPacket_counts :
    toffoliCount (mstartPacket 84)=toffoliCount (ECDSAAdd.Entrant.Rolling1588.packet false 84)+242 ∧
    measurementCount (mstartPacket 84)=measurementCount (ECDSAAdd.Entrant.Rolling1588.packet false 84)+237 := by
  have a := cell_count_delta false 84 3 2
  have b := cell_count_delta false 84 4 2
  have c := cellWith_counts false (P1Life.mstart (base 760) base (base 2409)) 84 4 2
  have d := route_mstart_counts
  have e := cell_counts false 84 4 2
  simp only [mstartPacket,ECDSAAdd.Entrant.Rolling1588.packet,renameProgram_counts,mstartBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,if_false,toffoliCount_append,
    measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem mendPacket_counts :
    toffoliCount (mendPacket 1)=toffoliCount (ECDSAAdd.Entrant.Rolling1588.packet false 1)+239 ∧
    measurementCount (mendPacket 1)=measurementCount (ECDSAAdd.Entrant.Rolling1588.packet false 1)+234 := by
  have a := cell_count_delta false 1 3 2
  have b := cell_count_delta false 1 4 2
  have c := cellWith_counts false (P1Life.mend (base 760) base (base 2409)) 1 3 2
  have d := route_junction_counts
  have e := cell_counts false 1 3 2
  simp only [mendPacket,ECDSAAdd.Entrant.Rolling1588.packet,renameProgram_counts,mendBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,if_false,toffoliCount_append,
    measurementCount_append]
  exact ⟨by omega,by omega⟩

/-- The odd multiplication slice has exactly 749 fewer Toffolis and 1,169 fewer measurements than
the record groups `1..84`. -/
theorem mslice_counts :
    toffoliCount mslice+749=toffoliCount (ECDSAAdd.Entrant.Rolling1588.groups false 1 84) ∧
    measurementCount mslice+1169=measurementCount (ECDSAAdd.Entrant.Rolling1588.groups false 1 84) := by
  have p := mstartPacket_counts
  have q := mendPacket_counts
  have g := groups_count_delta false 2 82 (by decide)
  rw [if_neg (by decide)] at g
  rw [mslice_eq,record_groups_shape_false]
  simp only [toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem mstartPacket_slots :
    Challenge.gateSlots (mstartPacket 84)+112=Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.packet false 84)+4543 := by
  have a := cell_slot_delta false 84 3 2
  have b := cell_slot_delta false 84 4 2
  have c := cellWith_slots false (P1Life.mstart (base 760) base (base 2409)) 84 4 2
  have d := slot_mstart (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have h := slot_half (base 760) false base (base 2409)
  have regular := cellWith_slots false (P1Life.half (base 760) false base (base 2409)) 84 4 2
  have eq : cell false 84 4 2=cellWith false (P1Life.half (base 760) false base (base 2409)) 84 4 2 := rfl
  rw [←eq] at regular
  simp only [Bool.false_eq_true,if_false] at h
  simp only [mstartPacket,ECDSAAdd.Entrant.Rolling1588.packet,Baselines.rename_gateSlots,mstartBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,if_false,Challenge.gateSlots_append]
  simp only [halfSlotSaving,Bool.false_eq_true,if_false] at a b
  omega

theorem mendPacket_slots :
    Challenge.gateSlots (mendPacket 1)+112=Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.packet false 1)+3821 := by
  have a := cell_slot_delta false 1 3 2
  have b := cell_slot_delta false 1 4 2
  have c := cellWith_slots false (P1Life.mend (base 760) base (base 2409)) 1 3 2
  have d := slot_junctions (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have h := slot_half (base 760) false base (base 2409)
  have regular := cellWith_slots false (P1Life.half (base 760) false base (base 2409)) 1 3 2
  have eq : cell false 1 3 2=cellWith false (P1Life.half (base 760) false base (base 2409)) 1 3 2 := rfl
  rw [←eq] at regular
  simp only [Bool.false_eq_true,if_false] at h
  simp only [mendPacket,ECDSAAdd.Entrant.Rolling1588.packet,Baselines.rename_gateSlots,mendBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,if_false,Challenge.gateSlots_append]
  simp only [halfSlotSaving,Bool.false_eq_true,if_false] at a b
  omega

/-- The odd multiplication slice uses fewer gate slots than the record groups `1..84`. -/
theorem mslice_slots_le : Challenge.gateSlots mslice≤Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.groups false 1 84) := by
  have p := mstartPacket_slots
  have q := mendPacket_slots
  have g := groups_slot_delta false 2 82 (by decide)
  rw [if_neg (by decide)] at g
  simp only [halfSlotSaving,Bool.false_eq_true,if_false] at g
  rw [mslice_eq,record_groups_shape_false]
  simp only [Challenge.gateSlots_append]
  omega

theorem mstartBasePacket_physical (j : Nat) (hj : j<102) : GatePhysical (mstartBasePacket j) := by
  have opening := onPacket_physical j hj stageOpen stageOpen_support stage_physical.1
  have closing := onPacket_physical j hj stageClose stageClose_support stage_physical.2.1
  have t0 := onPacket_physical j hj (stageTransition false 0) (stageTransition_support false 0 (by decide))
    (stage_physical.2.2 false 0 (by decide))
  have t1 := onPacket_physical j hj (stageTransition false 1) (stageTransition_support false 1 (by decide))
    (stage_physical.2.2 false 1 (by decide))
  have c3 := cell_physical false j 3 2 hj (by decide)
  have c4 := cell_physical false j 4 2 hj (by decide)
  have m0 := cellWith_physical false _ route_mstart_physical j 4 2 hj (by decide)
  simp only [mstartBasePacket,gatePhysical_append]
  exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨m0,t0⟩,c3⟩,c4⟩,t1⟩,c4⟩,c3⟩⟩,closing⟩

theorem mendBasePacket_physical (j : Nat) (hj : j<102) : GatePhysical (mendBasePacket j) := by
  have opening := onPacket_physical j hj stageOpen stageOpen_support stage_physical.1
  have closing := onPacket_physical j hj stageClose stageClose_support stage_physical.2.1
  have t0 := onPacket_physical j hj (stageTransition false 0) (stageTransition_support false 0 (by decide))
    (stage_physical.2.2 false 0 (by decide))
  have t1 := onPacket_physical j hj (stageTransition false 1) (stageTransition_support false 1 (by decide))
    (stage_physical.2.2 false 1 (by decide))
  have c3 := cell_physical false j 3 2 hj (by decide)
  have c4 := cell_physical false j 4 2 hj (by decide)
  have m0 := cellWith_physical false _ route_junction_physical.2.2 j 3 2 hj (by decide)
  simp only [mendBasePacket,gatePhysical_append]
  exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨c4,t0⟩,c3⟩,c4⟩,t1⟩,c4⟩,m0⟩⟩,closing⟩

theorem mslice_physical : GatePhysical mslice := by
  rw [mslice_eq]
  simp only [gatePhysical_append]
  exact ⟨⟨gatePhysical_rename _ (shifted (Placement5.pi 84)).injective _ (mstartBasePacket_physical 84 (by decide)),
    groups_physical false 2 82 (by decide)⟩,
    gatePhysical_rename _ (shifted (Placement5.pi 1)).injective _ (mendBasePacket_physical 1 (by decide))⟩

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== odd45: the odd multiplication slice on packets 45..1 =====
/-
# odd45: odd multiplication slice on packets 45..1

The multiplication kernel runs the record packets 84..46, then `mstart` in packet 45, ordinary odd
packets 44..2 and `mend` in packet 1 (`mslice45`; with the record packets, `mdslice`).  The slice
saves 164 T / 389 M against the record packets 45..1 and uses 2120 more gate slots.
-/
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

theorem odd45_program_false_add (p : Nat → Program) :
    ∀ (a b j : Nat),
      PacketSequence.program false p j (a + b) =
        PacketSequence.program false p (j + a) b ++
          PacketSequence.program false p j a
  | 0, b, j => by simp [PacketSequence.program]
  | a + 1, b, j => by
      have h : a + 1 + b = (a + b) + 1 := by omega
      rw [h]
      simp only [PacketSequence.program, Bool.false_eq_true, if_false,
        List.append_assoc]
      rw [odd45_program_false_add p a b (j + 1)]
      have hj : j + 1 + a = j + (a + 1) := by omega
      rw [hj, List.append_assoc]

theorem odd45_payload_false_add {α : Type} (step : Nat→α→α) (j m : Nat) :
    ∀ (n : Nat) (Q : α), PacketSequence.payload false step j (m+n) Q =
      PacketSequence.payload false step j m (PacketSequence.payload false step (j+m) n Q)
  | 0, Q => by simp only [Nat.add_zero, PacketSequence.payload]
  | n+1, Q => by
      rw [← Nat.add_assoc, route_payload_snoc_false, odd45_payload_false_add step j m n,
        route_payload_snoc_false, Nat.add_assoc]

/-- odd45 multiplication slice: `mstart` in packet 45, ordinary odd packets 44..2, `mend` in packet 1. -/
def mslice45 : Program := mstartPacket 45 ++ groups false 2 43 ++ mendPacket 1

/-- The multiplication first group (packets 84..1) of odd45: record 84..46, odd 45..1. -/
def mdslice : Program := ECDSAAdd.Entrant.Rolling1588.groups false 46 39 ++ mslice45

theorem mslice45_eq : mslice45=(mstartPacket 45 ++ groups false 2 43) ++ mendPacket 1 := rfl

theorem mdslice_eq : mdslice=ECDSAAdd.Entrant.Rolling1588.groups false 46 39 ++ mslice45 := rfl

theorem mslice45_payload (origin : BasisState) (X Y : Fp) :
    Replay5.groupsPayload false origin 1 45 (X,Y)=
      directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters 1))
        (Replay5.groupsPayload false origin 2 43
          (directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters 45)) (X,Y))) := by
  show PacketSequence.payload false _ 1 (44+1) (X,Y)=_
  rw [PacketSequence.payload.eq_2,if_neg (by decide),route_payload_snoc_false]
  rfl

theorem mslice45_cut_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord 46 origin X Y) mslice45
      (fun state => let V := Replay5.groupsPayload false origin 1 45 (X,Y)
        CutFrame centerWord centerWord 1 origin V.1 V.2 state) := by
  have a : StateTriple (CutFrame centerWord centerWord 46 origin X Y) (mstartPacket 45)
      (CutFrame P1Life.oddWord P1Life.oddWord 45 origin
        (directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters 45)) (X,Y)).1
        (directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters 45)) (X,Y)).2) := by
    intro state records input
    exact mstartPacket_cut_frame 45 (by decide) (by decide) origin ctx enabled X Y state records input
  have b (V : Fp×Fp) : StateTriple (CutFrame P1Life.oddWord P1Life.oddWord 45 origin V.1 V.2) (groups false 2 43)
      (CutFrame P1Life.oddWord P1Life.oddWord 2 origin
        (Replay5.groupsPayload false origin 2 43 V).1 (Replay5.groupsPayload false origin 2 43 V).2) := by
    intro state records input
    exact groups_cut_frame false 2 43 (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  have c (V : Fp×Fp) := mendPacket_cut_frame 1 (by decide) (by decide) origin ctx enabled V.1 V.2
  have total := (a.seq (b _)).seq (c _)
  intro state records input
  have r := total state records input
  refine ⟨r.1,?_⟩
  rw [mslice45_eq]
  show CutFrame centerWord centerWord 1 origin (Replay5.groupsPayload false origin 1 45 (X,Y)).1
    (Replay5.groupsPayload false origin 1 45 (X,Y)).2 _
  rw [mslice45_payload origin X Y]
  have r2 := r.2
  simp only [Prod.mk.eta] at r2
  exact r2

theorem mdslice_payload (origin : BasisState) (V : Fp×Fp) :
    Replay5.groupsPayload false origin 1 84 V=
      Replay5.groupsPayload false origin 1 45 (Replay5.groupsPayload false origin 46 39 V) :=
  odd45_payload_false_add _ 1 45 39 V

theorem mdslice_cut_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord 85 origin X Y) mdslice
      (fun state => let V := Replay5.groupsPayload false origin 1 84 (X,Y)
        CutFrame centerWord centerWord 1 origin V.1 V.2 state) := by
  have a : StateTriple (CutFrame centerWord centerWord 85 origin X Y)
      (ECDSAAdd.Entrant.Rolling1588.groups false 46 39)
      (CutFrame centerWord centerWord 46 origin
        (Replay5.groupsPayload false origin 46 39 (X,Y)).1 (Replay5.groupsPayload false origin 46 39 (X,Y)).2) := by
    intro state records input
    exact ECDSAAdd.Entrant.Rolling1588.groups_cut_frame false 46 39 (by decide) (by decide)
      origin ctx enabled X Y state records input
  have b (V : Fp×Fp) : StateTriple (CutFrame centerWord centerWord 46 origin V.1 V.2) mslice45
      (CutFrame centerWord centerWord 1 origin
        (Replay5.groupsPayload false origin 1 45 (V.1,V.2)).1 (Replay5.groupsPayload false origin 1 45 (V.1,V.2)).2) := by
    intro state records input
    exact mslice45_cut_frame origin ctx enabled V.1 V.2 state records input
  have total := a.seq (b _)
  intro state records input
  have r := total state records input
  refine ⟨r.1,?_⟩
  rw [mdslice_eq]
  show CutFrame centerWord centerWord 1 origin (Replay5.groupsPayload false origin 1 84 (X,Y)).1
    (Replay5.groupsPayload false origin 1 84 (X,Y)).2 _
  rw [mdslice_payload origin (X,Y)]
  have r2 := r.2
  simp only [Prod.mk.eta] at r2
  exact r2

/-- On the record cut frame at cut 85, the odd45 multiplication group and the record groups
`84..1` end in the same state (independent measurement tapes). -/
theorem mdslice_run_eq (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (s : State) (fresh old : List Bool)
    (input : ECDSAAdd.Entrant.Rolling1588.CutFrame 85 origin X Y s) :
    run mdslice fresh s = run (ECDSAAdd.Entrant.Rolling1588.groups false 1 84) old s := by
  have odd := mdslice_cut_frame origin ctx enabled X Y s fresh input
  have record := ECDSAAdd.Entrant.Rolling1588.groups_cut_frame false 1 84 (by decide) (by decide)
    origin ctx enabled X Y s old input
  exact cutFrame_unique_route 1 origin _ _ _ _ odd.2 record.2 (odd.1.trans record.1.symm)

theorem record_groups45_shape_false : ECDSAAdd.Entrant.Rolling1588.groups false 1 45=
    (ECDSAAdd.Entrant.Rolling1588.packet false 45 ++
      ECDSAAdd.Entrant.Rolling1588.groups false 2 43) ++ ECDSAAdd.Entrant.Rolling1588.packet false 1 := by
  show PacketSequence.program false (ECDSAAdd.Entrant.Rolling1588.packet false) 1 (44+1)=_
  rw [PacketSequence.program.eq_2,if_neg (by decide),show (44:Nat)=43+1 from rfl,route_program_snoc_false]
  rfl

theorem record_groups_split_false : ECDSAAdd.Entrant.Rolling1588.groups false 1 84=
    ECDSAAdd.Entrant.Rolling1588.groups false 46 39 ++ ECDSAAdd.Entrant.Rolling1588.groups false 1 45 :=
  odd45_program_false_add _ 45 39 1

theorem mstartPacket45_counts :
    toffoliCount (mstartPacket 45)=toffoliCount (ECDSAAdd.Entrant.Rolling1588.packet false 45)+242 ∧
    measurementCount (mstartPacket 45)=measurementCount (ECDSAAdd.Entrant.Rolling1588.packet false 45)+237 := by
  have a := cell_count_delta false 45 3 2
  have b := cell_count_delta false 45 4 2
  have c := cellWith_counts false (P1Life.mstart (base 760) base (base 2409)) 45 4 2
  have d := route_mstart_counts
  have e := cell_counts false 45 4 2
  simp only [mstartPacket,ECDSAAdd.Entrant.Rolling1588.packet,renameProgram_counts,mstartBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,if_false,toffoliCount_append,
    measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem mslice45_counts :
    toffoliCount mslice45+164=toffoliCount (ECDSAAdd.Entrant.Rolling1588.groups false 1 45) ∧
    measurementCount mslice45+389=measurementCount (ECDSAAdd.Entrant.Rolling1588.groups false 1 45) := by
  have p := mstartPacket45_counts
  have q := mendPacket_counts
  have g := groups_count_delta false 2 43 (by decide)
  rw [if_neg (by decide)] at g
  rw [mslice45_eq,record_groups45_shape_false]
  simp only [toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

/-- odd45: the multiplication first group saves 164 T / 389 M against the record groups `84..1`. -/
theorem mdslice_counts :
    toffoliCount mdslice+164=toffoliCount (ECDSAAdd.Entrant.Rolling1588.groups false 1 84) ∧
    measurementCount mdslice+389=measurementCount (ECDSAAdd.Entrant.Rolling1588.groups false 1 84) := by
  have s := mslice45_counts
  rw [mdslice_eq,record_groups_split_false]
  simp only [toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem mstartPacket45_slots :
    Challenge.gateSlots (mstartPacket 45)+112=Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.packet false 45)+4543 := by
  have a := cell_slot_delta false 45 3 2
  have b := cell_slot_delta false 45 4 2
  have c := cellWith_slots false (P1Life.mstart (base 760) base (base 2409)) 45 4 2
  have d := slot_mstart (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have h := slot_half (base 760) false base (base 2409)
  have regular := cellWith_slots false (P1Life.half (base 760) false base (base 2409)) 45 4 2
  have eq : cell false 45 4 2=cellWith false (P1Life.half (base 760) false base (base 2409)) 45 4 2 := rfl
  rw [←eq] at regular
  simp only [Bool.false_eq_true,if_false] at h
  simp only [mstartPacket,ECDSAAdd.Entrant.Rolling1588.packet,Baselines.rename_gateSlots,mstartBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,if_false,Challenge.gateSlots_append]
  simp only [halfSlotSaving,Bool.false_eq_true,if_false] at a b
  omega

/-- odd45: the multiplication first group uses exactly 2120 gate slots more than the record
groups `84..1` (mstart / mend cost 8140 over the record cells, 43 odd packets save 6020). -/
theorem mdslice_slots :
    Challenge.gateSlots mdslice=Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.groups false 1 84)+2120 := by
  have p := mstartPacket45_slots
  have q := mendPacket_slots
  have g := groups_slot_delta false 2 43 (by decide)
  rw [if_neg (by decide)] at g
  simp only [halfSlotSaving,Bool.false_eq_true,if_false] at g
  rw [mdslice_eq,mslice45_eq,record_groups_split_false,record_groups45_shape_false]
  simp only [Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
/-- the odd multiplication slice on packets 45..1 uses 2120 gate slots more than the record packets. -/
theorem mslice45_slots :
    Challenge.gateSlots mslice45 = Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.groups false 1 45) + 2120 := by
  have p := mstartPacket45_slots
  have q := mendPacket_slots
  have g := groups_slot_delta false 2 43 (by decide)
  rw [if_neg (by decide)] at g
  simp only [halfSlotSaving,Bool.false_eq_true,if_false] at g
  rw [mslice45_eq,record_groups45_shape_false]
  simp only [Challenge.gateSlots_append]
  omega
end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== cell support: the hosted odd45 multiplication slice is physical, stays inside the
-- record packets 45..1 and, on a record cut frame at cut 46, ends where the record packets 45..1 end =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

/-- on the record cut frame at cut 46, the odd45 multiplication slice and the record packets
`45..1` end in the same state (independent measurement tapes). -/
theorem mslice45_run_eq (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (s : State) (fresh old : List Bool)
    (input : ECDSAAdd.Entrant.Rolling1588.CutFrame 46 origin X Y s) :
    run mslice45 fresh s = run (ECDSAAdd.Entrant.Rolling1588.groups false 1 45) old s := by
  have odd := mslice45_cut_frame origin ctx enabled X Y s fresh input
  have record := ECDSAAdd.Entrant.Rolling1588.groups_cut_frame false 1 45 (by decide) (by decide)
    origin ctx enabled X Y s old input
  exact cutFrame_unique_route 1 origin _ _ _ _ odd.2 record.2 (odd.1.trans record.1.symm)

/-- the odd45 multiplication slice is physical. -/
theorem c45_mslice45_physical : GatePhysical mslice45 := by
  rw [mslice45_eq]
  simp only [gatePhysical_append]
  exact ⟨⟨gatePhysical_rename _ (shifted (Placement5.pi 45)).injective _ (mstartBasePacket_physical 45 (by decide)),
    groups_physical false 2 43 (by decide)⟩,
    gatePhysical_rename _ (shifted (Placement5.pi 1)).injective _ (mendBasePacket_physical 1 (by decide))⟩

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairLoanGroupSupport
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
attribute [local irreducible] wires StairLoan.half760Loan StairGroups.halfWindow StairGroups.cell Rolling1588.onPacket

/-- an odd multiplication cell stays inside the record cell. -/
theorem c45_oddCell_sub_false (P : Program) (hP : RouteA.Rolling1588.HalfSupport P) (j active hole : Nat) :
    wires (RouteA.Rolling1588.cellWith false P j active hole) ⊆ wires (Rolling1588.cell false j active hole) := by
  have h : wires (RouteA.Rolling1588.halfWindowWith P j active hole) ⊆
      wires (Rolling1588.halfWindow false j active hole) := by
    unfold RouteA.Rolling1588.halfWindowWith Rolling1588.halfWindow
    exact loanWindow_sub _ _ _ _ _ (rename_sub _ _ _ (hP.trans RouteA.Rolling1588.record_half_lower_false))
  simp only [RouteA.Rolling1588.cellWith,Rolling1588.cell,Bool.false_eq_true,if_false]
  exact append_sub _ _ _ _ (Finset.Subset.refl _) h

theorem c45_oddPlainCell_sub_false (j active hole : Nat) :
    wires (RouteA.Rolling1588.cell false j active hole) ⊆ wires (Rolling1588.cell false j active hole) := by
  have h := c45_oddCell_sub_false _ (RouteA.Rolling1588.half_support false) j active hole
  simpa only [RouteA.Rolling1588.cellWith,RouteA.Rolling1588.cell,RouteA.Rolling1588.halfWindow,
    Bool.false_eq_true,if_false] using h

theorem c45_oddBasePacket_sub_false (j : Nat) :
    wires (RouteA.Rolling1588.basePacket false j) ⊆ wires (Rolling1588.basePacket false j) := by
  have c := fun active hole => c45_oddPlainCell_sub_false j active hole
  simp only [RouteA.Rolling1588.basePacket,Rolling1588.basePacket,Bool.false_eq_true,if_false]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ (c 4 2) (Finset.Subset.refl _)) (c 3 2)) (c 4 2))
    (Finset.Subset.refl _)) (c 4 2)) (c 3 2)

/-- the `mstart` packet stays inside the record multiplication packet. -/
theorem c45_mstartBasePacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.mstartBasePacket j) ⊆ wires (Rolling1588.basePacket false j) := by
  have c := fun active hole => c45_oddPlainCell_sub_false j active hole
  have hm := c45_oddCell_sub_false _ RouteA.Rolling1588.mstart_support j 4 2
  simp only [RouteA.Rolling1588.mstartBasePacket,Rolling1588.basePacket,Bool.false_eq_true,if_false]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ hm (Finset.Subset.refl _)) (c 3 2)) (c 4 2))
    (Finset.Subset.refl _)) (c 4 2)) (c 3 2)

/-- the `mend` packet stays inside the record multiplication packet. -/
theorem c45_mendBasePacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.mendBasePacket j) ⊆ wires (Rolling1588.basePacket false j) := by
  have c := fun active hole => c45_oddPlainCell_sub_false j active hole
  have hd := c45_oddCell_sub_false _ RouteA.Rolling1588.mend_support j 3 2
  simp only [RouteA.Rolling1588.mendBasePacket,Rolling1588.basePacket,Bool.false_eq_true,if_false]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ (c 4 2) (Finset.Subset.refl _)) (c 3 2)) (c 4 2))
    (Finset.Subset.refl _)) (c 4 2)) hd

theorem c45_oddPacket_sub_false (j : Nat) :
    wires (RouteA.Rolling1588.packet false j) ⊆ wires (Rolling1588.packet false j) := by
  unfold RouteA.Rolling1588.packet Rolling1588.packet
  exact rename_sub _ _ _ (c45_oddBasePacket_sub_false j)

/-- the odd45 multiplication slice stays inside the record packets `45..1` (no new wire). -/
theorem c45_mslice45_sub : wires RouteA.Rolling1588.mslice45 ⊆ wires (Rolling1588.groups false 1 45) := by
  rw [RouteA.Rolling1588.record_groups45_shape_false,RouteA.Rolling1588.mslice45_eq]
  apply append_sub
  · apply append_sub
    · unfold RouteA.Rolling1588.mstartPacket Rolling1588.packet
      exact rename_sub _ _ _ (c45_mstartBasePacket_sub 45)
    · unfold RouteA.Rolling1588.groups Rolling1588.groups
      exact sequence_sub false _ _ (fun i => c45_oddPacket_sub_false i) 2 43
  · unfold RouteA.Rolling1588.mendPacket Rolling1588.packet
    exact rename_sub _ _ _ (c45_mendBasePacket_sub 1)

end ECDSAAdd.Entrant.StairLoanGroupSupport
end
-- ===== end odd multiplication cell =====

