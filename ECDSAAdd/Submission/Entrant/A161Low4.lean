import ECDSAAdd.Submission.Entrant.FullLogic

open ECDSAAdd
-- Low4 component Math
section
namespace A161Low4Math
set_option maxHeartbeats 4000000

theorem mask_xor (n v : Nat) (hv : v<2^n) :
 (2^n-1) ^^^ v=2^n-1-v := by
 apply Nat.eq_of_testBit_eq
 intro i
 rw [Nat.testBit_xor,Nat.testBit_two_pow_sub_one,
  show 2^n-1-v=2^n-(v+1) by omega,Nat.testBit_two_pow_sub_succ hv]
 by_cases h:i<n
 · simp [h]
 · have hi : n ≤ i := by omega
   have z:v.testBit i=false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hi))
   simp [h,z]

theorem shifted_mask_xor (v : Nat) (hv:v<2^157) :
 (2^161-16) ^^^ (16*v)=2^161-16-16*v := by
 have h := @Nat.shiftLeft_xor_distrib 4 (2^157-1) v
 simp only [Nat.shiftLeft_eq] at h
 have flip : (2^161-16) ^^^ (16*v)=((2^157-1) ^^^ v)*16 := by
  norm_num only [Nat.reducePow,Nat.reduceSub] at h ⊢
  simpa only [Nat.mul_comm] using h.symm
 rw [flip,mask_xor 157 v hv]
 norm_num at hv ⊢
 omega

theorem accumulator_div16_bound (H : Nat) (hH:H<2^128) :
 268435517*H<2^157 := by
 norm_num at hH ⊢
 omega





theorem mask_xor_multiple (v : Nat) (hv:v<2^161) (hz:v%16=0) :
 (2^161-16) ^^^ v=2^161-16-v := by
 have hvq : v/16<2^157 := by norm_num at hv ⊢; omega
 have h := shifted_mask_xor (v/16) hvq
 have e : 16*(v/16)=v := by omega
 simpa only [e] using h

end A161Low4Math
end

-- Low4 component Mask
section
namespace ECDSAAdd.Entrant.A161Low4Facts
open Arithmetic
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def Klow : Nat := 2^161-16




theorem sub_mod16 (v : Nat) (hz:v%16=0) : (Klow-v)%16=0 := by
 norm_num [Klow]
 omega

theorem flip_run (r : List Wire) (hlen:r.length=161) (hn:r.Nodup)
 (g : Wire) (hg:g∉r) (s : State) (m : List Bool)
 (hz:regValue r s.basis%16=0) :
 (run (maskedConstant g r Klow) m s).phase=s.phase ∧
 (∀q,q∉r → (run (maskedConstant g r Klow) m s).basis q=s.basis q) ∧
 regValue r (run (maskedConstant g r Klow) m s).basis=
 (if s.basis g then Klow-regValue r s.basis else regValue r s.basis) := by
 have hk:Klow<2^r.length := by rw [hlen];norm_num [Klow]
 have h:=maskedConstant_correct g r Klow hn hg hk s m
 refine ⟨h.1,h.2.1,?_⟩
 rw [h.2.2]
 cases s.basis g
 · simp
 · simp only [if_true]
   rw [Nat.xor_comm]
   exact A161Low4Math.mask_xor_multiple _ (by simpa only [hlen] using regValue_lt r s.basis) hz

end ECDSAAdd.Entrant.A161Low4Facts
end

-- Low4 component Ghost
section
namespace ECDSAAdd.Entrant.A161Low4Ghost
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def ghosts (L : CuccaroStreamedSquareWideLayout) : List Wire :=
 [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.normFlag]
def reg (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 161
def ghostAcc (L : CuccaroStreamedSquareWideLayout) : List Wire := ghosts L ++ (reg L).drop 4

theorem ghostAcc_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (b : BasisState) (K : Nat) (hv : regValue (reg L) b=16*K)
 (hz : ∀w∈ghosts L,b w=false) : regValue (ghostAcc L) b=regValue (reg L) b := by
 have len : (reg L).length=161 := by simp [reg,hw.core.work]
 have low : regValue ((reg L).take 4) b=0 := by
  rw [regValue_take_mod _ 4 (by omega) b,hv]
  omega
 have old : regValue (reg L) b=16*regValue ((reg L).drop 4) b := by
  calc
   _=regValue (((reg L).take 4)++(reg L).drop 4) b := by rw [List.take_append_drop]
   _=_ := by rw [regValue_append,low];simp [len]
 have gz : regValue (ghosts L) b=0 := (regValue_zero _ _).mpr hz
 rw [ghostAcc,regValue_append,gz]
 simpa [ghosts] using old.symm

theorem ghostAcc_drop (L : CuccaroStreamedSquareWideLayout) (n : Nat) (hn : 4≤n) :
 (ghostAcc L).drop n = (reg L).drop n := by
 have gl : (ghosts L).length=4 := rfl
 have gd : (ghosts L).drop n=[] := List.drop_eq_nil_of_le (by omega)
 rw [ghostAcc,List.drop_append,gd,List.nil_append,gl,List.drop_drop]
 congr 1
 omega

theorem ghostAcc_take_drop (L : CuccaroStreamedSquareWideLayout) (w n : Nat) (hn : 4≤n) :
 ((ghostAcc L).take w).drop n = ((reg L).take w).drop n := by
 rw [List.drop_take,List.drop_take,ghostAcc_drop L n hn]

theorem ghostAcc_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 (ghostAcc L).length=161 := by simp [ghostAcc,ghosts,reg,hw.core.work]
theorem ghosts_clean (L:CuccaroStreamedSquareWideLayout) (base:BasisState) (hc:L.PairClean base) :
 ∀q∈ghosts L,base q=false := by
 intro q hq
 simp only [ghosts,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl|rfl
 · exact hc.productHigh
 · exact hc.outHigh
 · exact hc.workHigh
 · exact hc.normFlag

theorem ghosts_out_free (L:CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
 ∀q∈ghosts L,q∉L.core.out := by
 intro q hq
 simp only [ghosts,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl|rfl
 all_goals exact (L.pairAuxAway hn _ (by simp)).2
theorem ghostAcc_zero (L:CuccaroStreamedSquareWideLayout) (base:BasisState) (hc:L.PairClean base) :
 regValue (ghostAcc L) base=0 := by
 apply (regValue_zero _ _).mpr
 intro q hq
 rcases List.mem_append.mp hq with hq|hq
 · exact ghosts_clean L base hc q hq
 · exact (regValue_zero _ _).mp hc.work q (List.mem_of_mem_take (List.mem_of_mem_drop hq))
theorem ghosts_work_free (L:CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
 ∀q∈ghosts L,q∉L.core.work := by
 intro q hq bad
 have parent:=List.nodup_iff_count_le_one.mp hn q
 have work:=List.count_pos_iff.mpr bad
 have flag:=List.count_pos_iff.mpr hq
 simp only [ghosts,List.count_cons,List.count_nil] at flag
 simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
  List.count_cons,List.count_append,List.count_nil] at parent
 omega


end ECDSAAdd.Entrant.A161Low4Ghost
end

-- Low4 component Domains
section
namespace ECDSAAdd.Entrant.A161Low4Domains
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout A161Low4Ghost

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

def smallPad (L:CuccaroStreamedSquareWideLayout) : List Wire := (L.foldPad.drop 160).take 31

theorem small_domain_nodup (L:CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
 (L.core.cin::(hiReg L++ghostAcc L++smallPad L++accBank L)).Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro w
 have parent:=List.nodup_iff_count_le_one.mp hn w
 have src:(hiReg L).count w≤L.core.product.count w :=
  ((List.drop_sublist 128 (L.core.product.take 256)).trans (List.take_sublist 256 L.core.product)).count_le w
 have work:((reg L).drop 4).count w≤L.core.work.count w :=
  ((List.drop_sublist 4 (L.core.work.take 161)).trans (List.take_sublist 161 L.core.work)).count_le w
 have ps : (L.foldPad.take 160++(L.foldPad.drop 160).take 31).Sublist L.foldPad := by
  have h:=(List.Sublist.refl (L.foldPad.take 160)).append (List.take_sublist 31 (L.foldPad.drop 160))
  rwa [List.take_append_drop] at h
 have pb:=ps.count_le w
 simp only [List.count_append] at pb
 change (accBank L).count w+(smallPad L).count w≤L.foldPad.count w at pb
 simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
  List.count_cons,List.count_append,List.count_nil] at parent pb
 simp only [ghostAcc,ghosts,List.count_cons,List.count_append,List.count_nil]
 omega
theorem full_domain_nodup (L:CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
 (L.core.cin::(hiReg L++ghostAcc L++accZ L++accBank L)).Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro w
 have parent:=List.nodup_iff_count_le_one.mp hn w
 have src:(hiReg L).count w≤L.core.product.count w :=
  ((List.drop_sublist 128 (L.core.product.take 256)).trans (List.take_sublist 256 L.core.product)).count_le w
 have pref : (L.core.work.take 161).Sublist (L.core.work.take 196) := by
  have h:=List.take_sublist 161 (L.core.work.take 196)
  simpa only [List.take_take,show min 161 196=161 by decide] using h
 have ws : ((reg L).drop 4++L.core.work.drop 196).Sublist L.core.work := by
  have h:=((List.drop_sublist 4 (L.core.work.take 161)).trans pref).append (List.Sublist.refl (L.core.work.drop 196))
  rwa [List.take_append_drop] at h
 have work:=ws.count_le w
 simp only [List.count_append] at work
 have pb:(L.foldPad.drop 160).count w+(accBank L).count w=L.foldPad.count w := by
  have h:=congrArg (fun xs:List Wire=>xs.count w) (List.take_append_drop 160 L.foldPad)
  simp only [List.count_append] at h
  change (L.foldPad.drop 160).count w+(L.foldPad.take 160).count w=L.foldPad.count w
  omega
 simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
  List.count_cons,List.count_append,List.count_nil] at parent pb
 simp only [ghostAcc,ghosts,accZ,foldPad,List.count_cons,List.count_append,List.count_nil]
 omega


end ECDSAAdd.Entrant.A161Low4Domains
end

section
-- Peak-memory helper: linear-time bitmask freshness/duplicate checks (kernel-accelerated Nat bit ops).
namespace ECDSAAdd.Entrant.PeakNodupFL

/-- Linear-time duplicate check with a bitmask accumulator. -/
def nodupMask : List Nat → Nat → Bool
  | [], _ => true
  | a :: as, m => !(m.testBit a) && nodupMask as (m ||| (1 <<< a))

theorem nodupMask_sound : ∀ (l : List Nat) (m : Nat), nodupMask l m = true →
    l.Nodup ∧ ∀ a ∈ l, m.testBit a = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | a :: as, m, h => by
    simp only [nodupMask, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨ha, hrest⟩ := h
    obtain ⟨hnd, hbits⟩ := nodupMask_sound as _ hrest
    have key : ∀ b ∈ as, b ≠ a ∧ m.testBit b = false := by
      intro b hb
      have hb' := hbits b hb
      rw [Nat.testBit_or, Bool.or_eq_false_iff] at hb'
      refine ⟨?_, hb'.1⟩
      rintro rfl
      have h2 := hb'.2
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow_self] at h2
      exact Bool.noConfusion h2
    refine ⟨List.nodup_cons.mpr ⟨fun hm => (key a hm).1 rfl, hnd⟩, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact (key b hb).2

theorem nodup_of_mask (l : List Nat) (h : nodupMask l 0 = true) : l.Nodup :=
  (nodupMask_sound l 0 h).1

/-- Bitmask of a list of wires. -/
def mkMask : List Nat → Nat
  | [] => 0
  | a :: as => mkMask as ||| (1 <<< a)

def freshMask (us l : List Nat) : Bool := us.all (fun u => !(mkMask l).testBit u)

theorem fresh_of_mask (us l : List Nat) (h : freshMask us l = true) : ∀ u ∈ us, u ∉ l := by
  intro u hu hl
  simp only [freshMask, List.all_eq_true, Bool.not_eq_true'] at h
  have h1 := h u hu
  have h2 : (mkMask l).testBit u = true := by
    clear h h1 hu
    induction l with
    | nil => cases hl
    | cons a as ih =>
      simp only [mkMask, Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow]
      rcases List.mem_cons.mp hl with rfl | h
      · exact Or.inr (decide_eq_true rfl)
      · exact Or.inl (ih h)
  rw [h1] at h2
  exact Bool.noConfusion h2

end ECDSAAdd.Entrant.PeakNodupFL
end

-- Low4 component Geometry
section
namespace ECDSAAdd.Entrant.A161Low4Geometry
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout A161Low4Ghost

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
abbrev L := Baselines.layout.dialogStreamedSquareWide
abbrev g := Baselines.layout.core.generic
abbrev d := Baselines.layout.core.poolWire 1540
abbrev ga := ghostAcc L
abbrev src := hiReg L
abbrev pad := (L.foldPad.drop 160).take 31

abbrev bank := accBank L
abbrev q := L.core.sumCarry
abbrev r := (L.core.product.drop 256).getD 1 0
abbrev p := L.core.product.getD 1 0

def loans93 := (L.core.work.drop 163).take 33 ++ (L.core.work.drop 255).take 1 ++
 (L.core.work.drop 227).take 28 ++ (L.core.work.drop 201).take 10 ++ (L.core.work.drop 212).take 15 ++
 (L.core.work.drop 211).take 1 ++ (L.core.work.drop 196).take 5
def hs99 := (loans93++(L.core.work.drop 161).take 2)++L.core.work.take 4
def hs100 := hs99++[d]
def domain := L.core.cin::(src++ga++pad++bank)








theorem geometry : g∉L.wires ∧ hs100.length=100 ∧ hs100.Nodup ∧
 (∀u∈hs100,u∉domain) ∧ (∀u∈hs100,u≠q ∧ u≠r ∧ u≠p) ∧
 q∉domain ∧ r∉domain ∧ p∉domain ∧ r≠q ∧ p≠q ∧ p≠r ∧
 (∀u∈([q,r,p,d]:List Wire),u∉g::(L.core.work.take 161) ∧ u∉L.measuredCore.wires ∧ u∉L.core.out) ∧
 (∀u∈hs99,u∈L.core.work) := by
 -- Peak memory: each conjunct is its own kernel check; the 100×483 freshness check uses a bitmask.
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · decide +kernel
 · decide +kernel
 · decide +kernel
 · exact PeakNodupFL.fresh_of_mask hs100 domain (by decide +kernel)
 · decide +kernel
 · decide +kernel
 · decide +kernel
 · decide +kernel
 · decide +kernel
 · decide +kernel
 · decide +kernel
 · decide +kernel
 · decide +kernel














end ECDSAAdd.Entrant.A161Low4Geometry
end

-- Low4 component StructuralBase
section
namespace ECDSAAdd.Entrant.A161Low4StructuralBase
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout A161Low4Ghost
set_option maxHeartbeats 4000000






















end ECDSAAdd.Entrant.A161Low4StructuralBase
end

-- Low4 component Structural
section
namespace ECDSAAdd.Entrant.A161Low4Structural
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout A161Low4Ghost

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

-- Uses the retained ghost-register structural technique from LowAccCarry.lean.
theorem ty (L:CuccaroStreamedSquareWideLayout) (src:List Wire) (neg:Bool) (n:Nat) (hn:4≤n) :
 Acc.ty (ghostAcc L) (Acc.earlyTerm src neg n)=Acc.ty (A161Fold.accReg L) (Acc.earlyTerm src neg n) := by
 change (ghostAcc L).drop n=(reg L).drop n
 exact ghostAcc_drop L n hn

theorem ty_take (L:CuccaroStreamedSquareWideLayout) (src:List Wire) (neg:Bool) (w n:Nat) (hn:4≤n) :
 Acc.ty ((ghostAcc L).take w) (Acc.earlyTerm src neg n)=Acc.ty ((A161Fold.accReg L).take w) (Acc.earlyTerm src neg n) := by
 change ((ghostAcc L).take w).drop n=((reg L).take w).drop n
 exact ghostAcc_take_drop L w n hn

theorem build_eq (L:CuccaroStreamedSquareWideLayout) (Z bank src:List Wire) (cin:Wire) :
 A161NarrowAcc.build8 (ghostAcc L) Z bank cin src=A161NarrowAcc.build8 (A161Fold.accReg L) Z bank cin src := by
 simp only [A161NarrowAcc.build8,A161NarrowAcc.pre8,CodexNarrowSub.accSub,Acc.seedOp,Acc.op]
 rw [ty L src false 4 (by decide),ty_take L src false 139 10 (by decide),
  ty_take L src true 139 6 (by decide),ty_take L src false 161 32 (by decide)]

theorem unbuild_eq (L:CuccaroStreamedSquareWideLayout) (Z bank src:List Wire) (cin:Wire) :
 A161SourceAdd.unbuild (ghostAcc L) Z bank cin src=A161SourceAdd.unbuild (A161Fold.accReg L) Z bank cin src := by
 simp only [A161SourceAdd.unbuild,CodexKnownOnesTail.accSub,A161SourceAdd.add,A161SourceTail.tail,Acc.seedOp]
 rw [ty_take L src false 161 32 (by decide),ghostAcc_take_drop L 139 6 (by decide),
  ghostAcc_take_drop L 139 10 (by decide),ty L src false 4 (by decide)]
 all_goals rfl

theorem buildMany_eq (L:CuccaroStreamedSquareWideLayout) (k:Nat) (Z bank src hs:List Wire) (cin q r p:Wire) :
 A161Carry.buildMany k (ghostAcc L) Z bank cin src hs q r p=
 A161Carry.buildMany k (A161Fold.accReg L) Z bank cin src hs q r p := by
 simp only [A161Carry.buildMany,A161Carry.buildPre,A161Carry.buildPost,Acc.seedOp,Acc.op]
 rw [ty L src false 4 (by decide),ty_take L src false 139 10 (by decide),
  ty_take L src true 139 6 (by decide),ty_take L src false 161 32 (by decide)]

theorem unbuildMany_eq (L:CuccaroStreamedSquareWideLayout) (k:Nat) (Z bank src hs:List Wire) (cin q r p:Wire) :
 A161Carry.unbuildMany k (ghostAcc L) Z bank cin src hs q r p=
 A161Carry.unbuildMany k (A161Fold.accReg L) Z bank cin src hs q r p := by
 simp only [A161Carry.unbuildMany,A161Carry.unbuildPre,A161Carry.unbuildPost,CodexKnownOnesTail.accSub,A161SourceTail.tail,Acc.seedOp]
 rw [ty_take L src false 161 32 (by decide),ghostAcc_take_drop L 139 6 (by decide),
  ghostAcc_take_drop L 139 10 (by decide),ty L src false 4 (by decide)]
 all_goals rfl


end ECDSAAdd.Entrant.A161Low4Structural
end

-- Low4 component InputEq
section
namespace ECDSAAdd.Entrant.A161Low4Facts
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
set_option linter.unusedSimpArgs false
def acc161 := A161Facts.acc161

def trimMasks (P:Program) : Program :=
 P.filter (fun i => decide (i≠.CX 4113 4501 ∧ i≠.CX 4113 4502 ∧ i≠.CX 4113 4503 ∧
  i≠.CX 4113 4504 ∧ i≠.CX 4113 4662 ∧ i≠.CX 4113 4663))
def pLow := trimMasks ParkAData.p0
def middleLow (L:CuccaroStreamedSquareWideLayout) (g:Wire) : Program :=
 maskedConstant g (acc161 L) Klow++(qprogTq L.measuredCore SquareReduction.p++maskedConstant g (acc161 L) Klow)

theorem trimMasks_append (P Q : Program) :
 trimMasks (P++Q)=trimMasks P++trimMasks Q := List.filter_append P Q

theorem trimMasks_eq (P : Program) (hg : 4113∉wires P) : trimMasks P=P := by
 induction P with
 | nil => rfl
 | cons i P ih =>
   have hgi : 4113∉i.wires := fun h => hg (Finset.mem_union_left _ h)
   have hgp : 4113∉wires P := fun h => hg (Finset.mem_union_right _ h)
   have neq (w : Wire) : i≠.CX 4113 w := by
    intro e;subst i;exact hgi (by simp [Instr.wires])
   have keep : decide (i≠.CX 4113 4501 ∧ i≠.CX 4113 4502 ∧ i≠.CX 4113 4503 ∧
    i≠.CX 4113 4504 ∧ i≠.CX 4113 4662 ∧ i≠.CX 4113 4663)=true := by simp [neq]
   simp only [trimMasks,List.filter_cons,keep,ite_true]
   exact congrArg (List.cons i) (ih hgp)

set_option maxRecDepth 100000
set_option maxHeartbeats 500000000

theorem trim_mask :
 trimMasks (maskedConstant A161FixedFold.g (accReg A161FixedFold.L)
   OwnDiagAll12Square.cFlipK)=maskedConstant A161FixedFold.g (acc161 A161FixedFold.L) Klow := by
 rfl

theorem trim_core_general (K : MeasuredCanonicalModLayout) (p : Nat)
 (free : 4113∉K.wires.toFinset) : trimMasks (qprogTq K p)=qprogTq K p :=
 trimMasks_eq (qprogTq K p) (fun h => free (QCore.qprog_supportTq K p h))

theorem trim_core : trimMasks (qprogTq A161FixedFold.L.measuredCore SquareReduction.p)=
 qprogTq A161FixedFold.L.measuredCore SquareReduction.p := by
 have freeList : 4113∉A161FixedFold.L.measuredCore.wires := by decide
 have freeSet : 4113∉A161FixedFold.L.measuredCore.wires.toFinset := by
  simpa only [List.mem_toFinset] using freeList
 exact trim_core_general A161FixedFold.L.measuredCore SquareReduction.p freeSet

theorem input_eq : pLow=middleLow A161FixedFold.L A161FixedFold.g := by
 let A := maskedConstant A161FixedFold.g (accReg A161FixedFold.L) OwnDiagAll12Square.cFlipK
 let Q := qprogTq A161FixedFold.L.measuredCore SquareReduction.p
 let N := maskedConstant A161FixedFold.g (acc161 A161FixedFold.L) Klow
 calc
  pLow=trimMasks (InverseCarryDevelop.aMiddle A161FixedFold.L A161FixedFold.g) :=
   congrArg trimMasks ParkAStagedProof.input_eq
  _ = trimMasks A++(trimMasks Q++trimMasks A) :=
   (trimMasks_append A (Q++A)).trans
    (congrArg (fun t => trimMasks A++t) (trimMasks_append Q A))
  _ = N++(Q++N) :=
   congrArg₂ (fun (P R : Program) => P++R) trim_mask
    (congrArg₂ (fun (P R : Program) => P++R) trim_core trim_mask)
  _ = middleLow A161FixedFold.L A161FixedFold.g := rfl



end ECDSAAdd.Entrant.A161Low4Facts
end

-- Low4 component Compile99



-- D1 (gate margin): output literal of compileS? hs99 pLow; moved verbatim from KnownZeroArithmetic (same names).
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.KnownAMidStaged
set_option autoImplicit false
set_option maxRecDepth 100000

def block0:Program:=[
.CX 4113 4505,
.CX 4113 4506,
.CX 4113 4507,
.CX 4113 4508,
.CX 4113 4509,
.CX 4113 4510,
.CX 4113 4511,
.CX 4113 4512,
.CX 4113 4513,
.CX 4113 4514,
.CX 4113 4515,
.CX 4113 4516,
.CX 4113 4517,
.CX 4113 4518,
.CX 4113 4519,
.CX 4113 4520,
.CX 4113 4521,
.CX 4113 4522,
.CX 4113 4523,
.CX 4113 4524,
.CX 4113 4525,
.CX 4113 4526,
.CX 4113 4527,
.CX 4113 4528,
.CX 4113 4529,
.CX 4113 4530,
.CX 4113 4531,
.CX 4113 4532,
.CX 4113 4533,
.CX 4113 4534,
.CX 4113 4535,
.CX 4113 4536,
.CX 4113 4537,
.CX 4113 4538,
.CX 4113 4539,
.CX 4113 4540,
.CX 4113 4541,
.CX 4113 4542,
.CX 4113 4543,
.CX 4113 4544,
.CX 4113 4545,
.CX 4113 4546,
.CX 4113 4547,
.CX 4113 4548,
.CX 4113 4549,
.CX 4113 4550,
.CX 4113 4551,
.CX 4113 4552,
.CX 4113 4553,
.CX 4113 4554,
.CX 4113 4555,
.CX 4113 4556,
.CX 4113 4557,
.CX 4113 4558,
.CX 4113 4559,
.CX 4113 4560,
.CX 4113 4561,
.CX 4113 4562,
.CX 4113 4563,
.CX 4113 4564,
.CX 4113 4565,
.CX 4113 4566,
.CX 4113 4567,
.CX 4113 4568,
.CX 4113 4569,
.CX 4113 4570,
.CX 4113 4571,
.CX 4113 4572,
.CX 4113 4573,
.CX 4113 4574,
.CX 4113 4575,
.CX 4113 4576,
.CX 4113 4577,
.CX 4113 4578,
.CX 4113 4579,
.CX 4113 4580,
.CX 4113 4581,
.CX 4113 4582,
.CX 4113 4583,
.CX 4113 4584,
.CX 4113 4585,
.CX 4113 4586,
.CX 4113 4587,
.CX 4113 4588,
.CX 4113 4589,
.CX 4113 4590,
.CX 4113 4591,
.CX 4113 4592,
.CX 4113 4593,
.CX 4113 4594,
.CX 4113 4595,
.CX 4113 4596,
.CX 4113 4597,
.CX 4113 4598,
.CX 4113 4599,
.CX 4113 4600,
.CX 4113 4601,
.CX 4113 4602,
.CX 4113 4603,
.CX 4113 4604,
.CX 4113 4605,
.CX 4113 4606,
.CX 4113 4607,
.CX 4113 4608,
.CX 4113 4609,
.CX 4113 4610,
.CX 4113 4611,
.CX 4113 4612,
.CX 4113 4613,
.CX 4113 4614,
.CX 4113 4615,
.CX 4113 4616,
.CX 4113 4617,
.CX 4113 4618,
.CX 4113 4619,
.CX 4113 4620,
.CX 4113 4621,
.CX 4113 4622,
.CX 4113 4623,
.CX 4113 4624,
.CX 4113 4625,
.CX 4113 4626,
.CX 4113 4627,
.CX 4113 4628,
.CX 4113 4629,
.CX 4113 4630,
.CX 4113 4631,
.CX 4113 4632
]
def block1:Program:=[
.CX 4113 4633,
.CX 4113 4634,
.CX 4113 4635,
.CX 4113 4636,
.CX 4113 4637,
.CX 4113 4638,
.CX 4113 4639,
.CX 4113 4640,
.CX 4113 4641,
.CX 4113 4642,
.CX 4113 4643,
.CX 4113 4644,
.CX 4113 4645,
.CX 4113 4646,
.CX 4113 4647,
.CX 4113 4648,
.CX 4113 4649,
.CX 4113 4650,
.CX 4113 4651,
.CX 4113 4652,
.CX 4113 4653,
.CX 4113 4654,
.CX 4113 4655,
.CX 4113 4656,
.CX 4113 4657,
.CX 4113 4658,
.CX 4113 4659,
.CX 4113 4660,
.CX 4113 4661,
.X 2,
.X 3,
.X 4,
.X 5,
.X 6,
.X 7,
.X 8,
.X 9,
.X 10,
.X 11,
.X 12,
.X 13,
.X 14,
.X 15,
.X 16,
.X 17,
.X 18,
.X 19,
.X 20,
.X 21,
.X 22,
.X 23,
.X 24,
.X 25,
.X 26,
.X 27,
.X 28,
.X 29,
.X 30,
.X 31,
.X 32,
.X 33,
.X 34,
.X 35,
.X 36,
.X 37,
.X 38,
.X 39,
.X 40,
.X 41,
.X 42,
.X 43,
.X 44,
.X 45,
.X 46,
.X 47,
.X 48,
.X 49,
.X 50,
.X 51,
.X 52,
.X 53,
.X 54,
.X 55,
.X 56,
.X 57,
.X 58,
.X 59,
.X 60,
.X 61,
.X 62,
.X 63,
.X 64,
.X 65,
.X 66,
.X 67,
.X 68,
.X 69,
.X 70,
.X 71,
.X 72,
.X 73,
.X 74,
.X 75,
.X 76,
.X 77,
.X 78,
.X 79,
.X 80,
.X 81,
.X 82,
.X 83,
.X 84,
.X 85,
.X 86,
.X 87,
.X 88,
.X 89,
.X 90,
.X 91,
.X 92,
.X 93,
.X 94,
.X 95,
.X 96,
.X 97,
.X 98,
.X 99,
.X 100
]
def block2:Program:=[
.X 101,
.X 102,
.X 103,
.X 104,
.X 105,
.X 106,
.X 107,
.X 108,
.X 109,
.X 110,
.X 111,
.X 112,
.X 113,
.X 114,
.X 115,
.X 116,
.X 117,
.X 118,
.X 119,
.X 120,
.X 121,
.X 122,
.X 123,
.X 124,
.X 125,
.X 126,
.X 127,
.X 128,
.X 129,
.X 130,
.X 131,
.X 132,
.X 133,
.X 134,
.X 135,
.X 136,
.X 137,
.X 138,
.X 139,
.X 140,
.X 141,
.X 142,
.X 143,
.X 144,
.X 145,
.X 146,
.X 147,
.X 148,
.X 149,
.X 150,
.X 151,
.X 152,
.X 153,
.X 154,
.X 155,
.X 156,
.X 157,
.X 158,
.X 159,
.X 160,
.X 161,
.X 162,
.X 163,
.X 164,
.X 165,
.X 166,
.X 167,
.X 168,
.X 169,
.X 170,
.X 171,
.X 172,
.X 173,
.X 174,
.X 175,
.X 176,
.X 177,
.X 178,
.X 179,
.X 180,
.X 181,
.X 182,
.X 183,
.X 184,
.X 185,
.X 186,
.X 187,
.X 188,
.X 189,
.X 190,
.X 191,
.X 192,
.X 193,
.X 194,
.X 195,
.X 196,
.X 197,
.X 198,
.X 199,
.X 200,
.X 201,
.X 202,
.X 203,
.X 204,
.X 205,
.X 206,
.X 207,
.X 208,
.X 209,
.X 210,
.X 211,
.X 212,
.X 213,
.X 214,
.X 215,
.X 216,
.X 217,
.X 218,
.X 219,
.X 220,
.X 221,
.X 222,
.X 223,
.X 224,
.X 225,
.X 226,
.X 227,
.X 228
]
def block3:Program:=[
.X 229,
.X 230,
.X 231,
.X 232,
.X 233,
.X 234,
.X 235,
.X 236,
.X 237,
.X 238,
.X 239,
.X 240,
.X 241,
.X 242,
.X 243,
.X 244,
.X 245,
.X 246,
.X 247,
.X 248,
.X 249,
.X 250,
.X 251,
.X 252,
.X 253,
.X 254,
.X 255,
.X 256,
.X 257,
.CCX 2 4760 4373,
.CCX 3 4373 4374,
.CCX 4 4374 4375,
.CCX 5 4375 4376,
.CX 4505 6,
.CX 4505 4376,
.CCX 6 4376 4377,
.CX 4505 4377,
.CX 4505 4376,
.CX 4505 6,
.CX 4506 7,
.CX 4506 4377,
.CCX 7 4377 4378,
.CX 4506 4378,
.CX 4506 4377,
.CX 4506 7,
.CX 4507 8,
.CX 4507 4378,
.CCX 8 4378 4379,
.CX 4507 4379,
.CX 4507 4378,
.CX 4507 8,
.CX 4508 9,
.CX 4508 4379,
.CCX 9 4379 4380,
.CX 4508 4380,
.CX 4508 4379,
.CX 4508 9,
.CX 4509 10,
.CX 4509 4380,
.CCX 10 4380 4381,
.CX 4509 4381,
.CX 4509 4380,
.CX 4509 10,
.CX 4510 11,
.CX 4510 4381,
.CCX 11 4381 4382,
.CX 4510 4382,
.CX 4510 4381,
.CX 4510 11,
.CX 4511 12,
.CX 4511 4382,
.CCX 12 4382 4383,
.CX 4511 4383,
.CX 4511 4382,
.CX 4511 12,
.CX 4512 13,
.CX 4512 4383,
.CCX 13 4383 4384,
.CX 4512 4384,
.CX 4512 4383,
.CX 4512 13,
.CX 4513 14,
.CX 4513 4384,
.CCX 14 4384 4385,
.CX 4513 4385,
.CX 4513 4384,
.CX 4513 14,
.CX 4514 15,
.CX 4514 4385,
.CCX 15 4385 4386,
.CX 4514 4386,
.CX 4514 4385,
.CX 4514 15,
.CX 4515 16,
.CX 4515 4386,
.CCX 16 4386 4387,
.CX 4515 4387,
.CX 4515 4386,
.CX 4515 16,
.CX 4516 17,
.CX 4516 4387,
.CCX 17 4387 4388,
.CX 4516 4388,
.CX 4516 4387,
.CX 4516 17,
.CX 4517 18,
.CX 4517 4388,
.CCX 18 4388 4389,
.CX 4517 4389,
.CX 4517 4388,
.CX 4517 18,
.CX 4518 19,
.CX 4518 4389,
.CCX 19 4389 4390,
.CX 4518 4390,
.CX 4518 4389,
.CX 4518 19,
.CX 4519 20,
.CX 4519 4390,
.CCX 20 4390 4391,
.CX 4519 4391,
.CX 4519 4390,
.CX 4519 20
]
def block4:Program:=[
.CX 4520 21,
.CX 4520 4391,
.CCX 21 4391 4392,
.CX 4520 4392,
.CX 4520 4391,
.CX 4520 21,
.CX 4521 22,
.CX 4521 4392,
.CCX 22 4392 4393,
.CX 4521 4393,
.CX 4521 4392,
.CX 4521 22,
.CX 4522 23,
.CX 4522 4393,
.CCX 23 4393 4394,
.CX 4522 4394,
.CX 4522 4393,
.CX 4522 23,
.CX 4523 24,
.CX 4523 4394,
.CCX 24 4394 4395,
.CX 4523 4395,
.CX 4523 4394,
.CX 4523 24,
.CX 4524 25,
.CX 4524 4395,
.CCX 25 4395 4396,
.CX 4524 4396,
.CX 4524 4395,
.CX 4524 25,
.CX 4525 26,
.CX 4525 4396,
.CCX 26 4396 4397,
.CX 4525 4397,
.CX 4525 4396,
.CX 4525 26,
.CX 4526 27,
.CX 4526 4397,
.CCX 27 4397 4398,
.CX 4526 4398,
.CX 4526 4397,
.CX 4526 27,
.CX 4527 28,
.CX 4527 4398,
.CCX 28 4398 4399,
.CX 4527 4399,
.CX 4527 4398,
.CX 4527 28,
.CX 4528 29,
.CX 4528 4399,
.CCX 29 4399 4400,
.CX 4528 4400,
.CX 4528 4399,
.CX 4528 29,
.CX 4529 30,
.CX 4529 4400,
.CCX 30 4400 4401,
.CX 4529 4401,
.CX 4529 4400,
.CX 4529 30,
.CX 4530 31,
.CX 4530 4401,
.CCX 31 4401 4402,
.CX 4530 4402,
.CX 4530 4401,
.CX 4530 31,
.CX 4531 32,
.CX 4531 4402,
.CCX 32 4402 4403,
.CX 4531 4403,
.CX 4531 4402,
.CX 4531 32,
.CX 4532 33,
.CX 4532 4403,
.CCX 33 4403 4404,
.CX 4532 4404,
.CX 4532 4403,
.CX 4532 33,
.CX 4533 34,
.CX 4533 4404,
.CCX 34 4404 4405,
.CX 4533 4405,
.CX 4533 4404,
.CX 4533 34,
.CX 4534 35,
.CX 4534 4405,
.CCX 35 4405 4406,
.CX 4534 4406,
.CX 4534 4405,
.CX 4534 35,
.CX 4535 36,
.CX 4535 4406,
.CCX 36 4406 4407,
.CX 4535 4407,
.CX 4535 4406,
.CX 4535 36,
.CX 4536 37,
.CX 4536 4407,
.CCX 37 4407 4408,
.CX 4536 4408,
.CX 4536 4407,
.CX 4536 37,
.CX 4537 38,
.CX 4537 4408,
.CCX 38 4408 4409,
.CX 4537 4409,
.CX 4537 4408,
.CX 4537 38,
.CX 4538 39,
.CX 4538 4409,
.CCX 39 4409 4410,
.CX 4538 4410,
.CX 4538 4409,
.CX 4538 39,
.CX 4539 40,
.CX 4539 4410,
.CCX 40 4410 4411,
.CX 4539 4411,
.CX 4539 4410,
.CX 4539 40,
.CX 4540 41,
.CX 4540 4411,
.CCX 41 4411 4412,
.CX 4540 4412,
.CX 4540 4411,
.CX 4540 41
]
def block5:Program:=[
.CX 4541 42,
.CX 4541 4412,
.CCX 42 4412 4413,
.CX 4541 4413,
.CX 4541 4412,
.CX 4541 42,
.CX 4542 43,
.CX 4542 4413,
.CCX 43 4413 4414,
.CX 4542 4414,
.CX 4542 4413,
.CX 4542 43,
.CX 4543 44,
.CX 4543 4414,
.CCX 44 4414 4415,
.CX 4543 4415,
.CX 4543 4414,
.CX 4543 44,
.CX 4544 45,
.CX 4544 4415,
.CCX 45 4415 4416,
.CX 4544 4416,
.CX 4544 4415,
.CX 4544 45,
.CX 4545 46,
.CX 4545 4416,
.CCX 46 4416 4417,
.CX 4545 4417,
.CX 4545 4416,
.CX 4545 46,
.CX 4546 47,
.CX 4546 4417,
.CCX 47 4417 4418,
.CX 4546 4418,
.CX 4546 4417,
.CX 4546 47,
.CX 4547 48,
.CX 4547 4418,
.CCX 48 4418 4419,
.CX 4547 4419,
.CX 4547 4418,
.CX 4547 48,
.CX 4548 49,
.CX 4548 4419,
.CCX 49 4419 4420,
.CX 4548 4420,
.CX 4548 4419,
.CX 4548 49,
.CX 4549 50,
.CX 4549 4420,
.CCX 50 4420 4421,
.CX 4549 4421,
.CX 4549 4420,
.CX 4549 50,
.CX 4550 51,
.CX 4550 4421,
.CCX 51 4421 4422,
.CX 4550 4422,
.CX 4550 4421,
.CX 4550 51,
.CX 4551 52,
.CX 4551 4422,
.CCX 52 4422 4423,
.CX 4551 4423,
.CX 4551 4422,
.CX 4551 52,
.CX 4552 53,
.CX 4552 4423,
.CCX 53 4423 4424,
.CX 4552 4424,
.CX 4552 4423,
.CX 4552 53,
.CX 4553 54,
.CX 4553 4424,
.CCX 54 4424 4425,
.CX 4553 4425,
.CX 4553 4424,
.CX 4553 54,
.CX 4554 55,
.CX 4554 4425,
.CCX 55 4425 4426,
.CX 4554 4426,
.CX 4554 4425,
.CX 4554 55,
.CX 4555 56,
.CX 4555 4426,
.CCX 56 4426 4427,
.CX 4555 4427,
.CX 4555 4426,
.CX 4555 56,
.CX 4556 57,
.CX 4556 4427,
.CCX 57 4427 4428,
.CX 4556 4428,
.CX 4556 4427,
.CX 4556 57,
.CX 4557 58,
.CX 4557 4428,
.CCX 58 4428 4429,
.CX 4557 4429,
.CX 4557 4428,
.CX 4557 58,
.CX 4558 59,
.CX 4558 4429,
.CCX 59 4429 4430,
.CX 4558 4430,
.CX 4558 4429,
.CX 4558 59,
.CX 4559 60,
.CX 4559 4430,
.CCX 60 4430 4431,
.CX 4559 4431,
.CX 4559 4430,
.CX 4559 60,
.CX 4560 61,
.CX 4560 4431,
.CCX 61 4431 4432,
.CX 4560 4432,
.CX 4560 4431,
.CX 4560 61,
.CX 4561 62,
.CX 4561 4432,
.CCX 62 4432 4433,
.CX 4561 4433,
.CX 4561 4432,
.CX 4561 62
]
def block6:Program:=[
.CX 4562 63,
.CX 4562 4433,
.CCX 63 4433 4434,
.CX 4562 4434,
.CX 4562 4433,
.CX 4562 63,
.CX 4563 64,
.CX 4563 4434,
.CCX 64 4434 4435,
.CX 4563 4435,
.CX 4563 4434,
.CX 4563 64,
.CX 4564 65,
.CX 4564 4435,
.CCX 65 4435 4436,
.CX 4564 4436,
.CX 4564 4435,
.CX 4564 65,
.CX 4565 66,
.CX 4565 4436,
.CCX 66 4436 4437,
.CX 4565 4437,
.CX 4565 4436,
.CX 4565 66,
.CX 4566 67,
.CX 4566 4437,
.CCX 67 4437 4438,
.CX 4566 4438,
.CX 4566 4437,
.CX 4566 67,
.CX 4567 68,
.CX 4567 4438,
.CCX 68 4438 4439,
.CX 4567 4439,
.CX 4567 4438,
.CX 4567 68,
.CX 4568 69,
.CX 4568 4439,
.CCX 69 4439 4440,
.CX 4568 4440,
.CX 4568 4439,
.CX 4568 69,
.CX 4569 70,
.CX 4569 4440,
.CCX 70 4440 4441,
.CX 4569 4441,
.CX 4569 4440,
.CX 4569 70,
.CX 4570 71,
.CX 4570 4441,
.CCX 71 4441 4442,
.CX 4570 4442,
.CX 4570 4441,
.CX 4570 71,
.CX 4571 72,
.CX 4571 4442,
.CCX 72 4442 4443,
.CX 4571 4443,
.CX 4571 4442,
.CX 4571 72,
.CX 4572 73,
.CX 4572 4443,
.CCX 73 4443 4444,
.CX 4572 4444,
.CX 4572 4443,
.CX 4572 73,
.CX 4573 74,
.CX 4573 4444,
.CCX 74 4444 4445,
.CX 4573 4445,
.CX 4573 4444,
.CX 4573 74,
.CX 4574 75,
.CX 4574 4445,
.CCX 75 4445 4446,
.CX 4574 4446,
.CX 4574 4445,
.CX 4574 75,
.CX 4575 76,
.CX 4575 4446,
.CCX 76 4446 4447,
.CX 4575 4447,
.CX 4575 4446,
.CX 4575 76,
.CX 4576 77,
.CX 4576 4447,
.CCX 77 4447 4448,
.CX 4576 4448,
.CX 4576 4447,
.CX 4576 77,
.CX 4577 78,
.CX 4577 4448,
.CCX 78 4448 4449,
.CX 4577 4449,
.CX 4577 4448,
.CX 4577 78,
.CX 4578 79,
.CX 4578 4449,
.CCX 79 4449 4450,
.CX 4578 4450,
.CX 4578 4449,
.CX 4578 79,
.CX 4579 80,
.CX 4579 4450,
.CCX 80 4450 4451,
.CX 4579 4451,
.CX 4579 4450,
.CX 4579 80,
.CX 4580 81,
.CX 4580 4451,
.CCX 81 4451 4452,
.CX 4580 4452,
.CX 4580 4451,
.CX 4580 81,
.CX 4581 82,
.CX 4581 4452,
.CCX 82 4452 4453,
.CX 4581 4453,
.CX 4581 4452,
.CX 4581 82,
.CX 4582 83,
.CX 4582 4453,
.CCX 83 4453 4454,
.CX 4582 4454,
.CX 4582 4453,
.CX 4582 83
]
def block7:Program:=[
.CX 4583 84,
.CX 4583 4454,
.CCX 84 4454 4455,
.CX 4583 4455,
.CX 4583 4454,
.CX 4583 84,
.CX 4584 85,
.CX 4584 4455,
.CCX 85 4455 4456,
.CX 4584 4456,
.CX 4584 4455,
.CX 4584 85,
.CX 4585 86,
.CX 4585 4456,
.CCX 86 4456 4457,
.CX 4585 4457,
.CX 4585 4456,
.CX 4585 86,
.CX 4586 87,
.CX 4586 4457,
.CCX 87 4457 4458,
.CX 4586 4458,
.CX 4586 4457,
.CX 4586 87,
.CX 4587 88,
.CX 4587 4458,
.CCX 88 4458 4459,
.CX 4587 4459,
.CX 4587 4458,
.CX 4587 88,
.CX 4588 89,
.CX 4588 4459,
.CCX 89 4459 4460,
.CX 4588 4460,
.CX 4588 4459,
.CX 4588 89,
.CX 4589 90,
.CX 4589 4460,
.CCX 90 4460 4461,
.CX 4589 4461,
.CX 4589 4460,
.CX 4589 90,
.CX 4590 91,
.CX 4590 4461,
.CCX 91 4461 4462,
.CX 4590 4462,
.CX 4590 4461,
.CX 4590 91,
.CX 4591 92,
.CX 4591 4462,
.CCX 92 4462 4463,
.CX 4591 4463,
.CX 4591 4462,
.CX 4591 92,
.CX 4592 93,
.CX 4592 4463,
.CCX 93 4463 4464,
.CX 4592 4464,
.CX 4592 4463,
.CX 4592 93,
.CX 4593 94,
.CX 4593 4464,
.CCX 94 4464 4465,
.CX 4593 4465,
.CX 4593 4464,
.CX 4593 94,
.CX 4594 95,
.CX 4594 4465,
.CCX 95 4465 4466,
.CX 4594 4466,
.CX 4594 4465,
.CX 4594 95,
.CX 4595 96,
.CX 4595 4466,
.CCX 96 4466 4467,
.CX 4595 4467,
.CX 4595 4466,
.CX 4595 96,
.CX 4596 97,
.CX 4596 4467,
.CCX 97 4467 4468,
.CX 4596 4468,
.CX 4596 4467,
.CX 4596 97,
.CX 4597 98,
.CX 4597 4468,
.CCX 98 4468 4469,
.CX 4597 4469,
.CX 4597 4468,
.CX 4597 98,
.CX 4598 99,
.CX 4598 4469,
.CCX 99 4469 4470,
.CX 4598 4470,
.CX 4598 4469,
.CX 4598 99,
.CX 4599 100,
.CX 4599 4470,
.CCX 100 4470 4471,
.CX 4599 4471,
.CX 4599 4470,
.CX 4599 100,
.CX 4600 101,
.CX 4600 4471,
.CCX 101 4471 4472,
.CX 4600 4472,
.CX 4600 4471,
.CX 4600 101,
.CX 4601 102,
.CX 4601 4472,
.CCX 102 4472 4473,
.CX 4601 4473,
.CX 4601 4472,
.CX 4601 102,
.CX 4602 103,
.CX 4602 4473,
.CCX 103 4473 4474,
.CX 4602 4474,
.CX 4602 4473,
.CX 4602 103,
.CX 4603 104,
.CX 4603 4474,
.CCX 104 4474 4475,
.CX 4603 4475,
.CX 4603 4474,
.CX 4603 104
]
def block8:Program:=[
.CX 4604 105,
.CX 4604 4475,
.CCX 105 4475 4476,
.CX 4604 4476,
.CX 4604 4475,
.CX 4604 105,
.CX 4605 106,
.CX 4605 4476,
.CCX 106 4476 4477,
.CX 4605 4477,
.CX 4605 4476,
.CX 4605 106,
.CX 4606 107,
.CX 4606 4477,
.CCX 107 4477 4478,
.CX 4606 4478,
.CX 4606 4477,
.CX 4606 107,
.CX 4607 108,
.CX 4607 4478,
.CCX 108 4478 4479,
.CX 4607 4479,
.CX 4607 4478,
.CX 4607 108,
.CX 4608 109,
.CX 4608 4479,
.CCX 109 4479 4480,
.CX 4608 4480,
.CX 4608 4479,
.CX 4608 109,
.CX 4609 110,
.CX 4609 4480,
.CCX 110 4480 4481,
.CX 4609 4481,
.CX 4609 4480,
.CX 4609 110,
.CX 4610 111,
.CX 4610 4481,
.CCX 111 4481 4482,
.CX 4610 4482,
.CX 4610 4481,
.CX 4610 111,
.CX 4611 112,
.CX 4611 4482,
.CCX 112 4482 4483,
.CX 4611 4483,
.CX 4611 4482,
.CX 4611 112,
.CX 4612 113,
.CX 4612 4483,
.CCX 113 4483 4484,
.CX 4612 4484,
.CX 4612 4483,
.CX 4612 113,
.CX 4613 114,
.CX 4613 4484,
.CCX 114 4484 4485,
.CX 4613 4485,
.CX 4613 4484,
.CX 4613 114,
.CX 4614 115,
.CX 4614 4485,
.CCX 115 4485 4486,
.CX 4614 4486,
.CX 4614 4485,
.CX 4614 115,
.CX 4615 116,
.CX 4615 4486,
.CCX 116 4486 4487,
.CX 4615 4487,
.CX 4615 4486,
.CX 4615 116,
.CX 4616 117,
.CX 4616 4487,
.CCX 117 4487 4488,
.CX 4616 4488,
.CX 4616 4487,
.CX 4616 117,
.CX 4617 118,
.CX 4617 4488,
.CCX 118 4488 4489,
.CX 4617 4489,
.CX 4617 4488,
.CX 4617 118,
.CX 4618 119,
.CX 4618 4489,
.CCX 119 4489 4490,
.CX 4618 4490,
.CX 4618 4489,
.CX 4618 119,
.CX 4619 120,
.CX 4619 4490,
.CCX 120 4490 4491,
.CX 4619 4491,
.CX 4619 4490,
.CX 4619 120,
.CX 4620 121,
.CX 4620 4491,
.CCX 121 4491 4492,
.CX 4620 4492,
.CX 4620 4491,
.CX 4620 121,
.CX 4621 122,
.CX 4621 4492,
.CCX 122 4492 4493,
.CX 4621 4493,
.CX 4621 4492,
.CX 4621 122,
.CX 4622 123,
.CX 4622 4493,
.CCX 123 4493 4494,
.CX 4622 4494,
.CX 4622 4493,
.CX 4622 123,
.CX 4623 124,
.CX 4623 4494,
.CCX 124 4494 4495,
.CX 4623 4495,
.CX 4623 4494,
.CX 4623 124,
.CX 4624 125,
.CX 4624 4495,
.CCX 125 4495 4496,
.CX 4624 4496,
.CX 4624 4495,
.CX 4624 125
]
def block9:Program:=[
.CX 4625 126,
.CX 4625 4496,
.CCX 126 4496 4497,
.CX 4625 4497,
.CX 4625 4496,
.CX 4625 126,
.CX 4626 127,
.CX 4626 4497,
.CCX 127 4497 4498,
.CX 4626 4498,
.CX 4626 4497,
.CX 4626 127,
.CX 4627 128,
.CX 4627 4498,
.CCX 128 4498 4499,
.CX 4627 4499,
.CX 4627 4498,
.CX 4627 128,
.CX 4628 129,
.CX 4628 4499,
.CCX 129 4499 4500,
.CX 4628 4500,
.CX 4628 4499,
.CX 4628 129,
.CX 4629 130,
.CX 4629 4500,
.CCX 130 4500 4764,
.CX 4629 4764,
.CX 4629 4500,
.CX 4629 130,
.CX 4630 131,
.CX 4630 4764,
.CCX 131 4764 4765,
.CX 4630 4765,
.CX 4630 4764,
.CX 4630 131,
.CX 4631 132,
.CX 4631 4765,
.CCX 132 4765 4766,
.CX 4631 4766,
.CX 4631 4765,
.CX 4631 132,
.CX 4632 133,
.CX 4632 4766,
.CCX 133 4766 4767,
.CX 4632 4767,
.CX 4632 4766,
.CX 4632 133,
.CX 4633 134,
.CX 4633 4767,
.CCX 134 4767 4768,
.CX 4633 4768,
.CX 4633 4767,
.CX 4633 134,
.CX 4634 135,
.CX 4634 4768,
.CCX 135 4768 4769,
.CX 4634 4769,
.CX 4634 4768,
.CX 4634 135,
.CX 4635 136,
.CX 4635 4769,
.CCX 136 4769 4770,
.CX 4635 4770,
.CX 4635 4769,
.CX 4635 136,
.CX 4636 137,
.CX 4636 4770,
.CCX 137 4770 4771,
.CX 4636 4771,
.CX 4636 4770,
.CX 4636 137,
.CX 4637 138,
.CX 4637 4771,
.CCX 138 4771 4772,
.CX 4637 4772,
.CX 4637 4771,
.CX 4637 138,
.CX 4638 139,
.CX 4638 4772,
.CCX 139 4772 4773,
.CX 4638 4773,
.CX 4638 4772,
.CX 4638 139,
.CX 4639 140,
.CX 4639 4773,
.CCX 140 4773 4774,
.CX 4639 4774,
.CX 4639 4773,
.CX 4639 140,
.CX 4640 141,
.CX 4640 4774,
.CCX 141 4774 4775,
.CX 4640 4775,
.CX 4640 4774,
.CX 4640 141,
.CX 4641 142,
.CX 4641 4775,
.CCX 142 4775 4776,
.CX 4641 4776,
.CX 4641 4775,
.CX 4641 142,
.CX 4642 143,
.CX 4642 4776,
.CCX 143 4776 4777,
.CX 4642 4777,
.CX 4642 4776,
.CX 4642 143,
.CX 4643 144,
.CX 4643 4777,
.CCX 144 4777 4778,
.CX 4643 4778,
.CX 4643 4777,
.CX 4643 144,
.CX 4644 145,
.CX 4644 4778,
.CCX 145 4778 4779,
.CX 4644 4779,
.CX 4644 4778,
.CX 4644 145,
.CX 4645 146,
.CX 4645 4779,
.CCX 146 4779 4780,
.CX 4645 4780,
.CX 4645 4779,
.CX 4645 146
]
def block10:Program:=[
.CX 4646 147,
.CX 4646 4780,
.CCX 147 4780 4781,
.CX 4646 4781,
.CX 4646 4780,
.CX 4646 147,
.CX 4647 148,
.CX 4647 4781,
.CCX 148 4781 4782,
.CX 4647 4782,
.CX 4647 4781,
.CX 4647 148,
.CX 4648 149,
.CX 4648 4782,
.CCX 149 4782 4783,
.CX 4648 4783,
.CX 4648 4782,
.CX 4648 149,
.CX 4649 150,
.CX 4649 4783,
.CCX 150 4783 4784,
.CX 4649 4784,
.CX 4649 4783,
.CX 4649 150,
.CX 4650 151,
.CX 4650 4784,
.CCX 151 4784 4785,
.CX 4650 4785,
.CX 4650 4784,
.CX 4650 151,
.CX 4651 152,
.CX 4651 4785,
.CCX 152 4785 4786,
.CX 4651 4786,
.CX 4651 4785,
.CX 4651 152,
.CX 4652 153,
.CX 4652 4786,
.CCX 153 4786 4787,
.CX 4652 4787,
.CX 4652 4786,
.CX 4652 153,
.CX 4653 154,
.CX 4653 4787,
.CCX 154 4787 4788,
.CX 4653 4788,
.CX 4653 4787,
.CX 4653 154,
.CX 4654 155,
.CX 4654 4788,
.CCX 155 4788 4789,
.CX 4654 4789,
.CX 4654 4788,
.CX 4654 155,
.CX 4655 156,
.CX 4655 4789,
.CCX 156 4789 4790,
.CX 4655 4790,
.CX 4655 4789,
.CX 4655 156,
.CX 4656 157,
.CX 4656 4790,
.CCX 157 4790 4791,
.CX 4656 4791,
.CX 4656 4790,
.CX 4656 157,
.CX 4657 158,
.CX 4657 4791,
.CCX 158 4791 4792,
.CX 4657 4792,
.CX 4657 4791,
.CX 4657 158,
.CX 4658 159,
.CX 4658 4792,
.CCX 159 4792 4793,
.CX 4658 4793,
.CX 4658 4792,
.CX 4658 159,
.CX 4659 160,
.CX 4659 4793,
.CCX 160 4793 4794,
.CX 4659 4794,
.CX 4659 4793,
.CX 4659 160,
.CX 4660 161,
.CX 4660 4794,
.CCX 161 4794 4795,
.CX 4660 4795,
.CX 4660 4794,
.CX 4660 161,
.CX 4661 162,
.CX 4661 4795,
.CCX 162 4795 4796,
.CX 4661 4796,
.CX 4661 4795,
.CX 4661 162,
.CCX 163 4796 4797,
.CCX 164 4797 4798,
.CCX 165 4798 4799,
.CCX 166 4799 4800,
.CCX 167 4800 4801,
.CCX 168 4801 4802,
.CCX 169 4802 4803,
.CCX 170 4803 4804,
.CCX 171 4804 4805,
.CCX 172 4805 4806,
.CCX 173 4806 4807,
.CCX 174 4807 4808,
.CCX 175 4808 4809,
.CCX 176 4809 4810,
.CCX 177 4810 4811,
.CCX 178 4811 4812,
.CCX 179 4812 4813,
.CCX 180 4813 4814,
.CCX 181 4814 4815,
.CCX 182 4815 4816,
.CCX 183 4816 4817,
.CCX 184 4817 4818,
.CCX 185 4818 4819,
.CCX 186 4819 4820,
.CCX 187 4820 4821,
.CCX 188 4821 4822,
.CCX 189 4822 4823,
.CCX 190 4823 4824,
.CCX 191 4824 4825,
.CCX 192 4825 4826,
.CCX 193 4826 4827,
.CCX 194 4827 4828
]
def block11:Program:=[
.CCX 195 4828 4829,
.CCX 196 4829 4830,
.CCX 197 4830 4831,
.CCX 198 4831 4832,
.CCX 199 4832 4833,
.CCX 200 4833 4834,
.CCX 201 4834 4835,
.CCX 202 4835 4836,
.CCX 203 4836 4837,
.CCX 204 4837 4838,
.CCX 205 4838 4839,
.CCX 206 4839 4840,
.CCX 207 4840 4841,
.CCX 208 4841 4842,
.CCX 209 4842 4843,
.CCX 210 4843 4844,
.CCX 211 4844 4845,
.CCX 212 4845 4846,
.CCX 213 4846 4847,
.CCX 214 4847 4848,
.CCX 215 4848 4849,
.CCX 216 4849 4850,
.CCX 217 4850 4851,
.CCX 218 4851 4852,
.CCX 219 4852 4853,
.CCX 220 4853 4854,
.CCX 221 4854 4855,
.CCX 222 4855 4856,
.CCX 223 4856 4857,
.CCX 224 4857 4858,
.CCX 225 4858 4859,
.CCX 226 4859 4860,
.CCX 227 4860 4861,
.CCX 228 4861 4862,
.CCX 229 4862 4863,
.CCX 230 4863 4864,
.CCX 231 4864 4865,
.CCX 232 4865 4866,
.CCX 233 4866 4867,
.CCX 234 4867 4868,
.CCX 235 4868 4869,
.CCX 236 4869 4870,
.CCX 237 4870 4871,
.CCX 238 4871 4872,
.CCX 239 4872 4873,
.CCX 240 4873 4874,
.CCX 241 4874 4875,
.CCX 242 4875 4876,
.CCX 243 4876 4877,
.CCX 244 4877 4878,
.CCX 245 4878 4879,
.CCX 246 4879 4880,
.CCX 247 4880 4881,
.CCX 248 4881 4882,
.CCX 249 4882 4883,
.CCX 250 4883 4884,
.CCX 251 4884 4885,
.CCX 252 4885 4886,
.CCX 253 4886 4887,
.CCX 254 4887 4888,
.CCX 255 4888 4889,
.CCX 256 4889 4757,
.CCX 257 4757 4759,
.CX 4759 4758,
.measureX 4759 [] [.CZ 257 4757],
.CX 4757 257,
.measureX 4757 [] [.CZ 256 4889],
.CX 4889 256,
.measureX 4889 [] [.CZ 255 4888],
.CX 4888 255,
.measureX 4888 [] [.CZ 254 4887],
.CX 4887 254,
.measureX 4887 [] [.CZ 253 4886],
.CX 4886 253,
.measureX 4886 [] [.CZ 252 4885],
.CX 4885 252,
.measureX 4885 [] [.CZ 251 4884],
.CX 4884 251,
.measureX 4884 [] [.CZ 250 4883],
.CX 4883 250,
.measureX 4883 [] [.CZ 249 4882],
.CX 4882 249,
.measureX 4882 [] [.CZ 248 4881],
.CX 4881 248,
.measureX 4881 [] [.CZ 247 4880],
.CX 4880 247,
.measureX 4880 [] [.CZ 246 4879],
.CX 4879 246,
.measureX 4879 [] [.CZ 245 4878],
.CX 4878 245,
.measureX 4878 [] [.CZ 244 4877],
.CX 4877 244,
.measureX 4877 [] [.CZ 243 4876],
.CX 4876 243,
.measureX 4876 [] [.CZ 242 4875],
.CX 4875 242,
.measureX 4875 [] [.CZ 241 4874],
.CX 4874 241,
.measureX 4874 [] [.CZ 240 4873],
.CX 4873 240,
.measureX 4873 [] [.CZ 239 4872],
.CX 4872 239,
.measureX 4872 [] [.CZ 238 4871],
.CX 4871 238,
.measureX 4871 [] [.CZ 237 4870],
.CX 4870 237,
.measureX 4870 [] [.CZ 236 4869],
.CX 4869 236,
.measureX 4869 [] [.CZ 235 4868],
.CX 4868 235,
.measureX 4868 [] [.CZ 234 4867],
.CX 4867 234,
.measureX 4867 [] [.CZ 233 4866],
.CX 4866 233,
.measureX 4866 [] [.CZ 232 4865],
.CX 4865 232,
.measureX 4865 [] [.CZ 231 4864],
.CX 4864 231,
.measureX 4864 [] [.CZ 230 4863],
.CX 4863 230,
.measureX 4863 [] [.CZ 229 4862],
.CX 4862 229,
.measureX 4862 [] [.CZ 228 4861],
.CX 4861 228,
.measureX 4861 [] [.CZ 227 4860],
.CX 4860 227,
.measureX 4860 [] [.CZ 226 4859],
.CX 4859 226
]
def block12:Program:=[
.measureX 4859 [] [.CZ 225 4858],
.CX 4858 225,
.measureX 4858 [] [.CZ 224 4857],
.CX 4857 224,
.measureX 4857 [] [.CZ 223 4856],
.CX 4856 223,
.measureX 4856 [] [.CZ 222 4855],
.CX 4855 222,
.measureX 4855 [] [.CZ 221 4854],
.CX 4854 221,
.measureX 4854 [] [.CZ 220 4853],
.CX 4853 220,
.measureX 4853 [] [.CZ 219 4852],
.CX 4852 219,
.measureX 4852 [] [.CZ 218 4851],
.CX 4851 218,
.measureX 4851 [] [.CZ 217 4850],
.CX 4850 217,
.measureX 4850 [] [.CZ 216 4849],
.CX 4849 216,
.measureX 4849 [] [.CZ 215 4848],
.CX 4848 215,
.measureX 4848 [] [.CZ 214 4847],
.CX 4847 214,
.measureX 4847 [] [.CZ 213 4846],
.CX 4846 213,
.measureX 4846 [] [.CZ 212 4845],
.CX 4845 212,
.measureX 4845 [] [.CZ 211 4844],
.CX 4844 211,
.measureX 4844 [] [.CZ 210 4843],
.CX 4843 210,
.measureX 4843 [] [.CZ 209 4842],
.CX 4842 209,
.measureX 4842 [] [.CZ 208 4841],
.CX 4841 208,
.measureX 4841 [] [.CZ 207 4840],
.CX 4840 207,
.measureX 4840 [] [.CZ 206 4839],
.CX 4839 206,
.measureX 4839 [] [.CZ 205 4838],
.CX 4838 205,
.measureX 4838 [] [.CZ 204 4837],
.CX 4837 204,
.measureX 4837 [] [.CZ 203 4836],
.CX 4836 203,
.measureX 4836 [] [.CZ 202 4835],
.CX 4835 202,
.measureX 4835 [] [.CZ 201 4834],
.CX 4834 201,
.measureX 4834 [] [.CZ 200 4833],
.CX 4833 200,
.measureX 4833 [] [.CZ 199 4832],
.CX 4832 199,
.measureX 4832 [] [.CZ 198 4831],
.CX 4831 198,
.measureX 4831 [] [.CZ 197 4830],
.CX 4830 197,
.measureX 4830 [] [.CZ 196 4829],
.CX 4829 196,
.measureX 4829 [] [.CZ 195 4828],
.CX 4828 195,
.measureX 4828 [] [.CZ 194 4827],
.CX 4827 194,
.measureX 4827 [] [.CZ 193 4826],
.CX 4826 193,
.measureX 4826 [] [.CZ 192 4825],
.CX 4825 192,
.measureX 4825 [] [.CZ 191 4824],
.CX 4824 191,
.measureX 4824 [] [.CZ 190 4823],
.CX 4823 190,
.measureX 4823 [] [.CZ 189 4822],
.CX 4822 189,
.measureX 4822 [] [.CZ 188 4821],
.CX 4821 188,
.measureX 4821 [] [.CZ 187 4820],
.CX 4820 187,
.measureX 4820 [] [.CZ 186 4819],
.CX 4819 186,
.measureX 4819 [] [.CZ 185 4818],
.CX 4818 185,
.measureX 4818 [] [.CZ 184 4817],
.CX 4817 184,
.measureX 4817 [] [.CZ 183 4816],
.CX 4816 183,
.measureX 4816 [] [.CZ 182 4815],
.CX 4815 182,
.measureX 4815 [] [.CZ 181 4814],
.CX 4814 181,
.measureX 4814 [] [.CZ 180 4813],
.CX 4813 180,
.measureX 4813 [] [.CZ 179 4812],
.CX 4812 179,
.measureX 4812 [] [.CZ 178 4811],
.CX 4811 178,
.measureX 4811 [] [.CZ 177 4810],
.CX 4810 177,
.measureX 4810 [] [.CZ 176 4809],
.CX 4809 176,
.measureX 4809 [] [.CZ 175 4808],
.CX 4808 175,
.measureX 4808 [] [.CZ 174 4807],
.CX 4807 174,
.measureX 4807 [] [.CZ 173 4806],
.CX 4806 173,
.measureX 4806 [] [.CZ 172 4805],
.CX 4805 172,
.measureX 4805 [] [.CZ 171 4804],
.CX 4804 171,
.measureX 4804 [] [.CZ 170 4803],
.CX 4803 170,
.measureX 4803 [] [.CZ 169 4802],
.CX 4802 169,
.measureX 4802 [] [.CZ 168 4801],
.CX 4801 168,
.measureX 4801 [] [.CZ 167 4800],
.CX 4800 167,
.measureX 4800 [] [.CZ 166 4799],
.CX 4799 166,
.measureX 4799 [] [.CZ 165 4798],
.CX 4798 165,
.measureX 4798 [] [.CZ 164 4797],
.CX 4797 164,
.measureX 4797 [] [.CZ 163 4796],
.CX 4796 163,
.measureX 4796 [] [.CZ 4661 162,.CZ 4661 4795,.CZ 162 4795],
.CX 4661 162
]
def block13:Program:=[
.CX 4795 162,
.measureX 4795 [] [.CZ 4660 161,.CZ 4660 4794,.CZ 161 4794],
.CX 4660 161,
.CX 4794 161,
.measureX 4794 [] [.CZ 4659 160,.CZ 4659 4793,.CZ 160 4793],
.CX 4659 160,
.CX 4793 160,
.measureX 4793 [] [.CZ 4658 159,.CZ 4658 4792,.CZ 159 4792],
.CX 4658 159,
.CX 4792 159,
.measureX 4792 [] [.CZ 4657 158,.CZ 4657 4791,.CZ 158 4791],
.CX 4657 158,
.CX 4791 158,
.measureX 4791 [] [.CZ 4656 157,.CZ 4656 4790,.CZ 157 4790],
.CX 4656 157,
.CX 4790 157,
.measureX 4790 [] [.CZ 4655 156,.CZ 4655 4789,.CZ 156 4789],
.CX 4655 156,
.CX 4789 156,
.measureX 4789 [] [.CZ 4654 155,.CZ 4654 4788,.CZ 155 4788],
.CX 4654 155,
.CX 4788 155,
.measureX 4788 [] [.CZ 4653 154,.CZ 4653 4787,.CZ 154 4787],
.CX 4653 154,
.CX 4787 154,
.measureX 4787 [] [.CZ 4652 153,.CZ 4652 4786,.CZ 153 4786],
.CX 4652 153,
.CX 4786 153,
.measureX 4786 [] [.CZ 4651 152,.CZ 4651 4785,.CZ 152 4785],
.CX 4651 152,
.CX 4785 152,
.measureX 4785 [] [.CZ 4650 151,.CZ 4650 4784,.CZ 151 4784],
.CX 4650 151,
.CX 4784 151,
.measureX 4784 [] [.CZ 4649 150,.CZ 4649 4783,.CZ 150 4783],
.CX 4649 150,
.CX 4783 150,
.measureX 4783 [] [.CZ 4648 149,.CZ 4648 4782,.CZ 149 4782],
.CX 4648 149,
.CX 4782 149,
.measureX 4782 [] [.CZ 4647 148,.CZ 4647 4781,.CZ 148 4781],
.CX 4647 148,
.CX 4781 148,
.measureX 4781 [] [.CZ 4646 147,.CZ 4646 4780,.CZ 147 4780],
.CX 4646 147,
.CX 4780 147,
.measureX 4780 [] [.CZ 4645 146,.CZ 4645 4779,.CZ 146 4779],
.CX 4645 146,
.CX 4779 146,
.measureX 4779 [] [.CZ 4644 145,.CZ 4644 4778,.CZ 145 4778],
.CX 4644 145,
.CX 4778 145,
.measureX 4778 [] [.CZ 4643 144,.CZ 4643 4777,.CZ 144 4777],
.CX 4643 144,
.CX 4777 144,
.measureX 4777 [] [.CZ 4642 143,.CZ 4642 4776,.CZ 143 4776],
.CX 4642 143,
.CX 4776 143,
.measureX 4776 [] [.CZ 4641 142,.CZ 4641 4775,.CZ 142 4775],
.CX 4641 142,
.CX 4775 142,
.measureX 4775 [] [.CZ 4640 141,.CZ 4640 4774,.CZ 141 4774],
.CX 4640 141,
.CX 4774 141,
.measureX 4774 [] [.CZ 4639 140,.CZ 4639 4773,.CZ 140 4773],
.CX 4639 140,
.CX 4773 140,
.measureX 4773 [] [.CZ 4638 139,.CZ 4638 4772,.CZ 139 4772],
.CX 4638 139,
.CX 4772 139,
.measureX 4772 [] [.CZ 4637 138,.CZ 4637 4771,.CZ 138 4771],
.CX 4637 138,
.CX 4771 138,
.measureX 4771 [] [.CZ 4636 137,.CZ 4636 4770,.CZ 137 4770],
.CX 4636 137,
.CX 4770 137,
.measureX 4770 [] [.CZ 4635 136,.CZ 4635 4769,.CZ 136 4769],
.CX 4635 136,
.CX 4769 136,
.measureX 4769 [] [.CZ 4634 135,.CZ 4634 4768,.CZ 135 4768],
.CX 4634 135,
.CX 4768 135,
.measureX 4768 [] [.CZ 4633 134,.CZ 4633 4767,.CZ 134 4767],
.CX 4633 134,
.CX 4767 134,
.measureX 4767 [] [.CZ 4632 133,.CZ 4632 4766,.CZ 133 4766],
.CX 4632 133,
.CX 4766 133,
.measureX 4766 [] [.CZ 4631 132,.CZ 4631 4765,.CZ 132 4765],
.CX 4631 132,
.CX 4765 132,
.measureX 4765 [] [.CZ 4630 131,.CZ 4630 4764,.CZ 131 4764],
.CX 4630 131,
.CX 4764 131,
.measureX 4764 [] [.CZ 4629 130,.CZ 4629 4500,.CZ 130 4500],
.CX 4629 130,
.CX 4500 130,
.measureX 4500 [] [.CZ 4628 129,.CZ 4628 4499,.CZ 129 4499],
.CX 4628 129,
.CX 4499 129,
.measureX 4499 [] [.CZ 4627 128,.CZ 4627 4498,.CZ 128 4498],
.CX 4627 128,
.CX 4498 128,
.measureX 4498 [] [.CZ 4626 127,.CZ 4626 4497,.CZ 127 4497],
.CX 4626 127,
.CX 4497 127,
.measureX 4497 [] [.CZ 4625 126,.CZ 4625 4496,.CZ 126 4496],
.CX 4625 126,
.CX 4496 126,
.measureX 4496 [] [.CZ 4624 125,.CZ 4624 4495,.CZ 125 4495],
.CX 4624 125,
.CX 4495 125,
.measureX 4495 [] [.CZ 4623 124,.CZ 4623 4494,.CZ 124 4494],
.CX 4623 124,
.CX 4494 124,
.measureX 4494 [] [.CZ 4622 123,.CZ 4622 4493,.CZ 123 4493],
.CX 4622 123,
.CX 4493 123,
.measureX 4493 [] [.CZ 4621 122,.CZ 4621 4492,.CZ 122 4492],
.CX 4621 122,
.CX 4492 122,
.measureX 4492 [] [.CZ 4620 121,.CZ 4620 4491,.CZ 121 4491],
.CX 4620 121,
.CX 4491 121,
.measureX 4491 [] [.CZ 4619 120,.CZ 4619 4490,.CZ 120 4490],
.CX 4619 120,
.CX 4490 120,
.measureX 4490 [] [.CZ 4618 119,.CZ 4618 4489,.CZ 119 4489]
]
def block14:Program:=[
.CX 4618 119,
.CX 4489 119,
.measureX 4489 [] [.CZ 4617 118,.CZ 4617 4488,.CZ 118 4488],
.CX 4617 118,
.CX 4488 118,
.measureX 4488 [] [.CZ 4616 117,.CZ 4616 4487,.CZ 117 4487],
.CX 4616 117,
.CX 4487 117,
.measureX 4487 [] [.CZ 4615 116,.CZ 4615 4486,.CZ 116 4486],
.CX 4615 116,
.CX 4486 116,
.measureX 4486 [] [.CZ 4614 115,.CZ 4614 4485,.CZ 115 4485],
.CX 4614 115,
.CX 4485 115,
.measureX 4485 [] [.CZ 4613 114,.CZ 4613 4484,.CZ 114 4484],
.CX 4613 114,
.CX 4484 114,
.measureX 4484 [] [.CZ 4612 113,.CZ 4612 4483,.CZ 113 4483],
.CX 4612 113,
.CX 4483 113,
.measureX 4483 [] [.CZ 4611 112,.CZ 4611 4482,.CZ 112 4482],
.CX 4611 112,
.CX 4482 112,
.measureX 4482 [] [.CZ 4610 111,.CZ 4610 4481,.CZ 111 4481],
.CX 4610 111,
.CX 4481 111,
.measureX 4481 [] [.CZ 4609 110,.CZ 4609 4480,.CZ 110 4480],
.CX 4609 110,
.CX 4480 110,
.measureX 4480 [] [.CZ 4608 109,.CZ 4608 4479,.CZ 109 4479],
.CX 4608 109,
.CX 4479 109,
.measureX 4479 [] [.CZ 4607 108,.CZ 4607 4478,.CZ 108 4478],
.CX 4607 108,
.CX 4478 108,
.measureX 4478 [] [.CZ 4606 107,.CZ 4606 4477,.CZ 107 4477],
.CX 4606 107,
.CX 4477 107,
.measureX 4477 [] [.CZ 4605 106,.CZ 4605 4476,.CZ 106 4476],
.CX 4605 106,
.CX 4476 106,
.measureX 4476 [] [.CZ 4604 105,.CZ 4604 4475,.CZ 105 4475],
.CX 4604 105,
.CX 4475 105,
.measureX 4475 [] [.CZ 4603 104,.CZ 4603 4474,.CZ 104 4474],
.CX 4603 104,
.CX 4474 104,
.measureX 4474 [] [.CZ 4602 103,.CZ 4602 4473,.CZ 103 4473],
.CX 4602 103,
.CX 4473 103,
.measureX 4473 [] [.CZ 4601 102,.CZ 4601 4472,.CZ 102 4472],
.CX 4601 102,
.CX 4472 102,
.measureX 4472 [] [.CZ 4600 101,.CZ 4600 4471,.CZ 101 4471],
.CX 4600 101,
.CX 4471 101,
.measureX 4471 [] [.CZ 4599 100,.CZ 4599 4470,.CZ 100 4470],
.CX 4599 100,
.CX 4470 100,
.measureX 4470 [] [.CZ 4598 99,.CZ 4598 4469,.CZ 99 4469],
.CX 4598 99,
.CX 4469 99,
.measureX 4469 [] [.CZ 4597 98,.CZ 4597 4468,.CZ 98 4468],
.CX 4597 98,
.CX 4468 98,
.measureX 4468 [] [.CZ 4596 97,.CZ 4596 4467,.CZ 97 4467],
.CX 4596 97,
.CX 4467 97,
.measureX 4467 [] [.CZ 4595 96,.CZ 4595 4466,.CZ 96 4466],
.CX 4595 96,
.CX 4466 96,
.measureX 4466 [] [.CZ 4594 95,.CZ 4594 4465,.CZ 95 4465],
.CX 4594 95,
.CX 4465 95,
.measureX 4465 [] [.CZ 4593 94,.CZ 4593 4464,.CZ 94 4464],
.CX 4593 94,
.CX 4464 94,
.measureX 4464 [] [.CZ 4592 93,.CZ 4592 4463,.CZ 93 4463],
.CX 4592 93,
.CX 4463 93,
.measureX 4463 [] [.CZ 4591 92,.CZ 4591 4462,.CZ 92 4462],
.CX 4591 92,
.CX 4462 92,
.measureX 4462 [] [.CZ 4590 91,.CZ 4590 4461,.CZ 91 4461],
.CX 4590 91,
.CX 4461 91,
.measureX 4461 [] [.CZ 4589 90,.CZ 4589 4460,.CZ 90 4460],
.CX 4589 90,
.CX 4460 90,
.measureX 4460 [] [.CZ 4588 89,.CZ 4588 4459,.CZ 89 4459],
.CX 4588 89,
.CX 4459 89,
.measureX 4459 [] [.CZ 4587 88,.CZ 4587 4458,.CZ 88 4458],
.CX 4587 88,
.CX 4458 88,
.measureX 4458 [] [.CZ 4586 87,.CZ 4586 4457,.CZ 87 4457],
.CX 4586 87,
.CX 4457 87,
.measureX 4457 [] [.CZ 4585 86,.CZ 4585 4456,.CZ 86 4456],
.CX 4585 86,
.CX 4456 86,
.measureX 4456 [] [.CZ 4584 85,.CZ 4584 4455,.CZ 85 4455],
.CX 4584 85,
.CX 4455 85,
.measureX 4455 [] [.CZ 4583 84,.CZ 4583 4454,.CZ 84 4454],
.CX 4583 84,
.CX 4454 84,
.measureX 4454 [] [.CZ 4582 83,.CZ 4582 4453,.CZ 83 4453],
.CX 4582 83,
.CX 4453 83,
.measureX 4453 [] [.CZ 4581 82,.CZ 4581 4452,.CZ 82 4452],
.CX 4581 82,
.CX 4452 82,
.measureX 4452 [] [.CZ 4580 81,.CZ 4580 4451,.CZ 81 4451],
.CX 4580 81,
.CX 4451 81,
.measureX 4451 [] [.CZ 4579 80,.CZ 4579 4450,.CZ 80 4450],
.CX 4579 80,
.CX 4450 80,
.measureX 4450 [] [.CZ 4578 79,.CZ 4578 4449,.CZ 79 4449],
.CX 4578 79,
.CX 4449 79,
.measureX 4449 [] [.CZ 4577 78,.CZ 4577 4448,.CZ 78 4448],
.CX 4577 78,
.CX 4448 78,
.measureX 4448 [] [.CZ 4576 77,.CZ 4576 4447,.CZ 77 4447],
.CX 4576 77,
.CX 4447 77
]
def block15:Program:=[
.measureX 4447 [] [.CZ 4575 76,.CZ 4575 4446,.CZ 76 4446],
.CX 4575 76,
.CX 4446 76,
.measureX 4446 [] [.CZ 4574 75,.CZ 4574 4445,.CZ 75 4445],
.CX 4574 75,
.CX 4445 75,
.measureX 4445 [] [.CZ 4573 74,.CZ 4573 4444,.CZ 74 4444],
.CX 4573 74,
.CX 4444 74,
.measureX 4444 [] [.CZ 4572 73,.CZ 4572 4443,.CZ 73 4443],
.CX 4572 73,
.CX 4443 73,
.measureX 4443 [] [.CZ 4571 72,.CZ 4571 4442,.CZ 72 4442],
.CX 4571 72,
.CX 4442 72,
.measureX 4442 [] [.CZ 4570 71,.CZ 4570 4441,.CZ 71 4441],
.CX 4570 71,
.CX 4441 71,
.measureX 4441 [] [.CZ 4569 70,.CZ 4569 4440,.CZ 70 4440],
.CX 4569 70,
.CX 4440 70,
.measureX 4440 [] [.CZ 4568 69,.CZ 4568 4439,.CZ 69 4439],
.CX 4568 69,
.CX 4439 69,
.measureX 4439 [] [.CZ 4567 68,.CZ 4567 4438,.CZ 68 4438],
.CX 4567 68,
.CX 4438 68,
.measureX 4438 [] [.CZ 4566 67,.CZ 4566 4437,.CZ 67 4437],
.CX 4566 67,
.CX 4437 67,
.measureX 4437 [] [.CZ 4565 66,.CZ 4565 4436,.CZ 66 4436],
.CX 4565 66,
.CX 4436 66,
.measureX 4436 [] [.CZ 4564 65,.CZ 4564 4435,.CZ 65 4435],
.CX 4564 65,
.CX 4435 65,
.measureX 4435 [] [.CZ 4563 64,.CZ 4563 4434,.CZ 64 4434],
.CX 4563 64,
.CX 4434 64,
.measureX 4434 [] [.CZ 4562 63,.CZ 4562 4433,.CZ 63 4433],
.CX 4562 63,
.CX 4433 63,
.measureX 4433 [] [.CZ 4561 62,.CZ 4561 4432,.CZ 62 4432],
.CX 4561 62,
.CX 4432 62,
.measureX 4432 [] [.CZ 4560 61,.CZ 4560 4431,.CZ 61 4431],
.CX 4560 61,
.CX 4431 61,
.measureX 4431 [] [.CZ 4559 60,.CZ 4559 4430,.CZ 60 4430],
.CX 4559 60,
.CX 4430 60,
.measureX 4430 [] [.CZ 4558 59,.CZ 4558 4429,.CZ 59 4429],
.CX 4558 59,
.CX 4429 59,
.measureX 4429 [] [.CZ 4557 58,.CZ 4557 4428,.CZ 58 4428],
.CX 4557 58,
.CX 4428 58,
.measureX 4428 [] [.CZ 4556 57,.CZ 4556 4427,.CZ 57 4427],
.CX 4556 57,
.CX 4427 57,
.measureX 4427 [] [.CZ 4555 56,.CZ 4555 4426,.CZ 56 4426],
.CX 4555 56,
.CX 4426 56,
.measureX 4426 [] [.CZ 4554 55,.CZ 4554 4425,.CZ 55 4425],
.CX 4554 55,
.CX 4425 55,
.measureX 4425 [] [.CZ 4553 54,.CZ 4553 4424,.CZ 54 4424],
.CX 4553 54,
.CX 4424 54,
.measureX 4424 [] [.CZ 4552 53,.CZ 4552 4423,.CZ 53 4423],
.CX 4552 53,
.CX 4423 53,
.measureX 4423 [] [.CZ 4551 52,.CZ 4551 4422,.CZ 52 4422],
.CX 4551 52,
.CX 4422 52,
.measureX 4422 [] [.CZ 4550 51,.CZ 4550 4421,.CZ 51 4421],
.CX 4550 51,
.CX 4421 51,
.measureX 4421 [] [.CZ 4549 50,.CZ 4549 4420,.CZ 50 4420],
.CX 4549 50,
.CX 4420 50,
.measureX 4420 [] [.CZ 4548 49,.CZ 4548 4419,.CZ 49 4419],
.CX 4548 49,
.CX 4419 49,
.measureX 4419 [] [.CZ 4547 48,.CZ 4547 4418,.CZ 48 4418],
.CX 4547 48,
.CX 4418 48,
.measureX 4418 [] [.CZ 4546 47,.CZ 4546 4417,.CZ 47 4417],
.CX 4546 47,
.CX 4417 47,
.measureX 4417 [] [.CZ 4545 46,.CZ 4545 4416,.CZ 46 4416],
.CX 4545 46,
.CX 4416 46,
.measureX 4416 [] [.CZ 4544 45,.CZ 4544 4415,.CZ 45 4415],
.CX 4544 45,
.CX 4415 45,
.measureX 4415 [] [.CZ 4543 44,.CZ 4543 4414,.CZ 44 4414],
.CX 4543 44,
.CX 4414 44,
.measureX 4414 [] [.CZ 4542 43,.CZ 4542 4413,.CZ 43 4413],
.CX 4542 43,
.CX 4413 43,
.measureX 4413 [] [.CZ 4541 42,.CZ 4541 4412,.CZ 42 4412],
.CX 4541 42,
.CX 4412 42,
.measureX 4412 [] [.CZ 4540 41,.CZ 4540 4411,.CZ 41 4411],
.CX 4540 41,
.CX 4411 41,
.measureX 4411 [] [.CZ 4539 40,.CZ 4539 4410,.CZ 40 4410],
.CX 4539 40,
.CX 4410 40,
.measureX 4410 [] [.CZ 4538 39,.CZ 4538 4409,.CZ 39 4409],
.CX 4538 39,
.CX 4409 39,
.measureX 4409 [] [.CZ 4537 38,.CZ 4537 4408,.CZ 38 4408],
.CX 4537 38,
.CX 4408 38,
.measureX 4408 [] [.CZ 4536 37,.CZ 4536 4407,.CZ 37 4407],
.CX 4536 37,
.CX 4407 37,
.measureX 4407 [] [.CZ 4535 36,.CZ 4535 4406,.CZ 36 4406],
.CX 4535 36,
.CX 4406 36,
.measureX 4406 [] [.CZ 4534 35,.CZ 4534 4405,.CZ 35 4405],
.CX 4534 35,
.CX 4405 35,
.measureX 4405 [] [.CZ 4533 34,.CZ 4533 4404,.CZ 34 4404],
.CX 4533 34
]
def block16:Program:=[
.CX 4404 34,
.measureX 4404 [] [.CZ 4532 33,.CZ 4532 4403,.CZ 33 4403],
.CX 4532 33,
.CX 4403 33,
.measureX 4403 [] [.CZ 4531 32,.CZ 4531 4402,.CZ 32 4402],
.CX 4531 32,
.CX 4402 32,
.measureX 4402 [] [.CZ 4530 31,.CZ 4530 4401,.CZ 31 4401],
.CX 4530 31,
.CX 4401 31,
.measureX 4401 [] [.CZ 4529 30,.CZ 4529 4400,.CZ 30 4400],
.CX 4529 30,
.CX 4400 30,
.measureX 4400 [] [.CZ 4528 29,.CZ 4528 4399,.CZ 29 4399],
.CX 4528 29,
.CX 4399 29,
.measureX 4399 [] [.CZ 4527 28,.CZ 4527 4398,.CZ 28 4398],
.CX 4527 28,
.CX 4398 28,
.measureX 4398 [] [.CZ 4526 27,.CZ 4526 4397,.CZ 27 4397],
.CX 4526 27,
.CX 4397 27,
.measureX 4397 [] [.CZ 4525 26,.CZ 4525 4396,.CZ 26 4396],
.CX 4525 26,
.CX 4396 26,
.measureX 4396 [] [.CZ 4524 25,.CZ 4524 4395,.CZ 25 4395],
.CX 4524 25,
.CX 4395 25,
.measureX 4395 [] [.CZ 4523 24,.CZ 4523 4394,.CZ 24 4394],
.CX 4523 24,
.CX 4394 24,
.measureX 4394 [] [.CZ 4522 23,.CZ 4522 4393,.CZ 23 4393],
.CX 4522 23,
.CX 4393 23,
.measureX 4393 [] [.CZ 4521 22,.CZ 4521 4392,.CZ 22 4392],
.CX 4521 22,
.CX 4392 22,
.measureX 4392 [] [.CZ 4520 21,.CZ 4520 4391,.CZ 21 4391],
.CX 4520 21,
.CX 4391 21,
.measureX 4391 [] [.CZ 4519 20,.CZ 4519 4390,.CZ 20 4390],
.CX 4519 20,
.CX 4390 20,
.measureX 4390 [] [.CZ 4518 19,.CZ 4518 4389,.CZ 19 4389],
.CX 4518 19,
.CX 4389 19,
.measureX 4389 [] [.CZ 4517 18,.CZ 4517 4388,.CZ 18 4388],
.CX 4517 18,
.CX 4388 18,
.measureX 4388 [] [.CZ 4516 17,.CZ 4516 4387,.CZ 17 4387],
.CX 4516 17,
.CX 4387 17,
.measureX 4387 [] [.CZ 4515 16,.CZ 4515 4386,.CZ 16 4386],
.CX 4515 16,
.CX 4386 16,
.measureX 4386 [] [.CZ 4514 15,.CZ 4514 4385,.CZ 15 4385],
.CX 4514 15,
.CX 4385 15,
.measureX 4385 [] [.CZ 4513 14,.CZ 4513 4384,.CZ 14 4384],
.CX 4513 14,
.CX 4384 14,
.measureX 4384 [] [.CZ 4512 13,.CZ 4512 4383,.CZ 13 4383],
.CX 4512 13,
.CX 4383 13,
.measureX 4383 [] [.CZ 4511 12,.CZ 4511 4382,.CZ 12 4382],
.CX 4511 12,
.CX 4382 12,
.measureX 4382 [] [.CZ 4510 11,.CZ 4510 4381,.CZ 11 4381],
.CX 4510 11,
.CX 4381 11,
.measureX 4381 [] [.CZ 4509 10,.CZ 4509 4380,.CZ 10 4380],
.CX 4509 10,
.CX 4380 10,
.measureX 4380 [] [.CZ 4508 9,.CZ 4508 4379,.CZ 9 4379],
.CX 4508 9,
.CX 4379 9,
.measureX 4379 [] [.CZ 4507 8,.CZ 4507 4378,.CZ 8 4378],
.CX 4507 8,
.CX 4378 8,
.measureX 4378 [] [.CZ 4506 7,.CZ 4506 4377,.CZ 7 4377],
.CX 4506 7,
.CX 4377 7,
.measureX 4377 [] [.CZ 4505 6,.CZ 4505 4376,.CZ 6 4376],
.CX 4505 6,
.CX 4376 6,
.measureX 4376 [] [.CZ 5 4375],
.CX 4375 5,
.measureX 4375 [] [.CZ 4 4374],
.CX 4374 4,
.measureX 4374 [] [.CZ 3 4373],
.CX 4373 3,
.measureX 4373 [] [.CZ 2 4760],
.CX 4760 2,
.CX 4758 4762,
.X 4762,
.CX 4762 2,
.CX 4762 4760,
.CCX 2 4760 4373,
.CX 4762 4373,
.CX 4762 4760,
.CX 4762 2,
.CX 4762 3,
.CX 4762 4373,
.CCX 3 4373 4374,
.CX 4762 4374,
.CX 4762 4373,
.CX 4762 3,
.CX 4762 4,
.CX 4762 4374,
.CCX 4 4374 4375,
.CX 4762 4375,
.CX 4762 4374,
.CX 4762 4,
.CX 4762 5,
.CX 4762 4375,
.CCX 5 4375 4376,
.CX 4762 4376,
.CX 4762 4375,
.CX 4762 5,
.CCX 6 4376 4377,
.CX 4762 7,
.CX 4762 4377,
.CCX 7 4377 4378,
.CX 4762 4378,
.CX 4762 4377,
.CX 4762 7,
.CCX 8 4378 4379,
.CCX 9 4379 4380
]
def block17:Program:=[
.CCX 10 4380 4381,
.CCX 11 4381 4382,
.CX 4762 12,
.CX 4762 4382,
.CCX 12 4382 4383,
.CX 4762 4383,
.CX 4762 4382,
.CX 4762 12,
.CX 4762 13,
.CX 4762 4383,
.CCX 13 4383 4384,
.CX 4762 4384,
.CX 4762 4383,
.CX 4762 13,
.CX 4762 14,
.CX 4762 4384,
.CCX 14 4384 4385,
.CX 4762 4385,
.CX 4762 4384,
.CX 4762 14,
.CX 4762 15,
.CX 4762 4385,
.CCX 15 4385 4386,
.CX 4762 4386,
.CX 4762 4385,
.CX 4762 15,
.CX 4762 16,
.CX 4762 4386,
.CCX 16 4386 4387,
.CX 4762 4387,
.CX 4762 4386,
.CX 4762 16,
.CX 4762 17,
.CX 4762 4387,
.CCX 17 4387 4388,
.CX 4762 4388,
.CX 4762 4387,
.CX 4762 17,
.CX 4762 18,
.CX 4762 4388,
.CCX 18 4388 4389,
.CX 4762 4389,
.CX 4762 4388,
.CX 4762 18,
.CX 4762 19,
.CX 4762 4389,
.CCX 19 4389 4390,
.CX 4762 4390,
.CX 4762 4389,
.CX 4762 19,
.CX 4762 20,
.CX 4762 4390,
.CCX 20 4390 4391,
.CX 4762 4391,
.CX 4762 4390,
.CX 4762 20,
.CX 4762 21,
.CX 4762 4391,
.CCX 21 4391 4392,
.CX 4762 4392,
.CX 4762 4391,
.CX 4762 21,
.CX 4762 22,
.CX 4762 4392,
.CCX 22 4392 4393,
.CX 4762 4393,
.CX 4762 4392,
.CX 4762 22,
.CX 4762 23,
.CX 4762 4393,
.CCX 23 4393 4394,
.CX 4762 4394,
.CX 4762 4393,
.CX 4762 23,
.CX 4762 24,
.CX 4762 4394,
.CCX 24 4394 4395,
.CX 4762 4395,
.CX 4762 4394,
.CX 4762 24,
.CX 4762 25,
.CX 4762 4395,
.CCX 25 4395 4396,
.CX 4762 4396,
.CX 4762 4395,
.CX 4762 25,
.CX 4762 26,
.CX 4762 4396,
.CCX 26 4396 4397,
.CX 4762 4397,
.CX 4762 4396,
.CX 4762 26,
.CX 4762 27,
.CX 4762 4397,
.CCX 27 4397 4398,
.CX 4762 4398,
.CX 4762 4397,
.CX 4762 27,
.CX 4762 28,
.CX 4762 4398,
.CCX 28 4398 4399,
.CX 4762 4399,
.CX 4762 4398,
.CX 4762 28,
.CX 4762 29,
.CX 4762 4399,
.CCX 29 4399 4400,
.CX 4762 4400,
.CX 4762 4399,
.CX 4762 29,
.CX 4762 30,
.CX 4762 4400,
.CCX 30 4400 4401,
.CX 4762 4401,
.CX 4762 4400,
.CX 4762 30,
.CX 4762 31,
.CX 4762 4401,
.CCX 31 4401 4402,
.CX 4762 4402,
.CX 4762 4401,
.CX 4762 31,
.CX 4762 32,
.CX 4762 4402,
.CCX 32 4402 4403,
.CX 4762 4403,
.CX 4762 4402,
.CX 4762 32
]
def block18:Program:=[
.CX 4762 33,
.CX 4762 4403,
.CCX 33 4403 4404,
.CX 4762 4404,
.CX 4762 4403,
.CX 4762 33,
.CCX 34 4404 4405,
.CX 4762 35,
.CX 4762 4405,
.CCX 35 4405 4406,
.CX 4762 4406,
.CX 4762 4405,
.CX 4762 35,
.CX 4762 36,
.CX 4762 4406,
.CCX 36 4406 4407,
.CX 4762 4407,
.CX 4762 4406,
.CX 4762 36,
.CX 4762 37,
.CX 4762 4407,
.CCX 37 4407 4408,
.CX 4762 4408,
.CX 4762 4407,
.CX 4762 37,
.CX 4762 38,
.CX 4762 4408,
.CCX 38 4408 4409,
.CX 4762 4409,
.CX 4762 4408,
.CX 4762 38,
.CX 4762 39,
.CX 4762 4409,
.CCX 39 4409 4410,
.CX 4762 4410,
.CX 4762 4409,
.CX 4762 39,
.CX 4762 40,
.CX 4762 4410,
.CCX 40 4410 4411,
.CX 4762 4411,
.CX 4762 4410,
.CX 4762 40,
.CX 4762 41,
.CX 4762 4411,
.CCX 41 4411 4412,
.CX 4762 4412,
.CX 4762 4411,
.CX 4762 41,
.CX 4762 42,
.CX 4762 4412,
.CCX 42 4412 4413,
.CX 4762 4413,
.CX 4762 4412,
.CX 4762 42,
.CX 4762 43,
.CX 4762 4413,
.CCX 43 4413 4414,
.CX 4762 4414,
.CX 4762 4413,
.CX 4762 43,
.CX 4762 44,
.CX 4762 4414,
.CCX 44 4414 4415,
.CX 4762 4415,
.CX 4762 4414,
.CX 4762 44,
.CX 4762 45,
.CX 4762 4415,
.CCX 45 4415 4416,
.CX 4762 4416,
.CX 4762 4415,
.CX 4762 45,
.CX 4762 46,
.CX 4762 4416,
.CCX 46 4416 4417,
.CX 4762 4417,
.CX 4762 4416,
.CX 4762 46,
.CX 4762 47,
.CX 4762 4417,
.CCX 47 4417 4418,
.CX 4762 4418,
.CX 4762 4417,
.CX 4762 47,
.CX 4762 48,
.CX 4762 4418,
.CCX 48 4418 4419,
.CX 4762 4419,
.CX 4762 4418,
.CX 4762 48,
.CX 4762 49,
.CX 4762 4419,
.CCX 49 4419 4420,
.CX 4762 4420,
.CX 4762 4419,
.CX 4762 49,
.CX 4762 50,
.CX 4762 4420,
.CCX 50 4420 4421,
.CX 4762 4421,
.CX 4762 4420,
.CX 4762 50,
.CX 4762 51,
.CX 4762 4421,
.CCX 51 4421 4422,
.CX 4762 4422,
.CX 4762 4421,
.CX 4762 51,
.CX 4762 52,
.CX 4762 4422,
.CCX 52 4422 4423,
.CX 4762 4423,
.CX 4762 4422,
.CX 4762 52,
.CX 4762 53,
.CX 4762 4423,
.CCX 53 4423 4424,
.CX 4762 4424,
.CX 4762 4423,
.CX 4762 53,
.CX 4762 54,
.CX 4762 4424,
.CCX 54 4424 4425,
.CX 4762 4425,
.CX 4762 4424,
.CX 4762 54
]
def block19:Program:=[
.CX 4762 55,
.CX 4762 4425,
.CCX 55 4425 4426,
.CX 4762 4426,
.CX 4762 4425,
.CX 4762 55,
.CX 4762 56,
.CX 4762 4426,
.CCX 56 4426 4427,
.CX 4762 4427,
.CX 4762 4426,
.CX 4762 56,
.CX 4762 57,
.CX 4762 4427,
.CCX 57 4427 4428,
.CX 4762 4428,
.CX 4762 4427,
.CX 4762 57,
.CX 4762 58,
.CX 4762 4428,
.CCX 58 4428 4429,
.CX 4762 4429,
.CX 4762 4428,
.CX 4762 58,
.CX 4762 59,
.CX 4762 4429,
.CCX 59 4429 4430,
.CX 4762 4430,
.CX 4762 4429,
.CX 4762 59,
.CX 4762 60,
.CX 4762 4430,
.CCX 60 4430 4431,
.CX 4762 4431,
.CX 4762 4430,
.CX 4762 60,
.CX 4762 61,
.CX 4762 4431,
.CCX 61 4431 4432,
.CX 4762 4432,
.CX 4762 4431,
.CX 4762 61,
.CX 4762 62,
.CX 4762 4432,
.CCX 62 4432 4433,
.CX 4762 4433,
.CX 4762 4432,
.CX 4762 62,
.CX 4762 63,
.CX 4762 4433,
.CCX 63 4433 4434,
.CX 4762 4434,
.CX 4762 4433,
.CX 4762 63,
.CX 4762 64,
.CX 4762 4434,
.CCX 64 4434 4435,
.CX 4762 4435,
.CX 4762 4434,
.CX 4762 64,
.CX 4762 65,
.CX 4762 4435,
.CCX 65 4435 4436,
.CX 4762 4436,
.CX 4762 4435,
.CX 4762 65,
.CX 4762 66,
.CX 4762 4436,
.CCX 66 4436 4437,
.CX 4762 4437,
.CX 4762 4436,
.CX 4762 66,
.CX 4762 67,
.CX 4762 4437,
.CCX 67 4437 4438,
.CX 4762 4438,
.CX 4762 4437,
.CX 4762 67,
.CX 4762 68,
.CX 4762 4438,
.CCX 68 4438 4439,
.CX 4762 4439,
.CX 4762 4438,
.CX 4762 68,
.CX 4762 69,
.CX 4762 4439,
.CCX 69 4439 4440,
.CX 4762 4440,
.CX 4762 4439,
.CX 4762 69,
.CX 4762 70,
.CX 4762 4440,
.CCX 70 4440 4441,
.CX 4762 4441,
.CX 4762 4440,
.CX 4762 70,
.CX 4762 71,
.CX 4762 4441,
.CCX 71 4441 4442,
.CX 4762 4442,
.CX 4762 4441,
.CX 4762 71,
.CX 4762 72,
.CX 4762 4442,
.CCX 72 4442 4443,
.CX 4762 4443,
.CX 4762 4442,
.CX 4762 72,
.CX 4762 73,
.CX 4762 4443,
.CCX 73 4443 4444,
.CX 4762 4444,
.CX 4762 4443,
.CX 4762 73,
.CX 4762 74,
.CX 4762 4444,
.CCX 74 4444 4445,
.CX 4762 4445,
.CX 4762 4444,
.CX 4762 74,
.CX 4762 75,
.CX 4762 4445,
.CCX 75 4445 4446,
.CX 4762 4446,
.CX 4762 4445,
.CX 4762 75
]
def block20:Program:=[
.CX 4762 76,
.CX 4762 4446,
.CCX 76 4446 4447,
.CX 4762 4447,
.CX 4762 4446,
.CX 4762 76,
.CX 4762 77,
.CX 4762 4447,
.CCX 77 4447 4448,
.CX 4762 4448,
.CX 4762 4447,
.CX 4762 77,
.CX 4762 78,
.CX 4762 4448,
.CCX 78 4448 4449,
.CX 4762 4449,
.CX 4762 4448,
.CX 4762 78,
.CX 4762 79,
.CX 4762 4449,
.CCX 79 4449 4450,
.CX 4762 4450,
.CX 4762 4449,
.CX 4762 79,
.CX 4762 80,
.CX 4762 4450,
.CCX 80 4450 4451,
.CX 4762 4451,
.CX 4762 4450,
.CX 4762 80,
.CX 4762 81,
.CX 4762 4451,
.CCX 81 4451 4452,
.CX 4762 4452,
.CX 4762 4451,
.CX 4762 81,
.CX 4762 82,
.CX 4762 4452,
.CCX 82 4452 4453,
.CX 4762 4453,
.CX 4762 4452,
.CX 4762 82,
.CX 4762 83,
.CX 4762 4453,
.CCX 83 4453 4454,
.CX 4762 4454,
.CX 4762 4453,
.CX 4762 83,
.CX 4762 84,
.CX 4762 4454,
.CCX 84 4454 4455,
.CX 4762 4455,
.CX 4762 4454,
.CX 4762 84,
.CX 4762 85,
.CX 4762 4455,
.CCX 85 4455 4456,
.CX 4762 4456,
.CX 4762 4455,
.CX 4762 85,
.CX 4762 86,
.CX 4762 4456,
.CCX 86 4456 4457,
.CX 4762 4457,
.CX 4762 4456,
.CX 4762 86,
.CX 4762 87,
.CX 4762 4457,
.CCX 87 4457 4458,
.CX 4762 4458,
.CX 4762 4457,
.CX 4762 87,
.CX 4762 88,
.CX 4762 4458,
.CCX 88 4458 4459,
.CX 4762 4459,
.CX 4762 4458,
.CX 4762 88,
.CX 4762 89,
.CX 4762 4459,
.CCX 89 4459 4460,
.CX 4762 4460,
.CX 4762 4459,
.CX 4762 89,
.CX 4762 90,
.CX 4762 4460,
.CCX 90 4460 4461,
.CX 4762 4461,
.CX 4762 4460,
.CX 4762 90,
.CX 4762 91,
.CX 4762 4461,
.CCX 91 4461 4462,
.CX 4762 4462,
.CX 4762 4461,
.CX 4762 91,
.CX 4762 92,
.CX 4762 4462,
.CCX 92 4462 4463,
.CX 4762 4463,
.CX 4762 4462,
.CX 4762 92,
.CX 4762 93,
.CX 4762 4463,
.CCX 93 4463 4464,
.CX 4762 4464,
.CX 4762 4463,
.CX 4762 93,
.CX 4762 94,
.CX 4762 4464,
.CCX 94 4464 4465,
.CX 4762 4465,
.CX 4762 4464,
.CX 4762 94,
.CX 4762 95,
.CX 4762 4465,
.CCX 95 4465 4466,
.CX 4762 4466,
.CX 4762 4465,
.CX 4762 95,
.CX 4762 96,
.CX 4762 4466,
.CCX 96 4466 4467,
.CX 4762 4467,
.CX 4762 4466,
.CX 4762 96
]
def block21:Program:=[
.CX 4762 97,
.CX 4762 4467,
.CCX 97 4467 4468,
.CX 4762 4468,
.CX 4762 4467,
.CX 4762 97,
.CX 4762 98,
.CX 4762 4468,
.CCX 98 4468 4469,
.CX 4762 4469,
.CX 4762 4468,
.CX 4762 98,
.CX 4762 99,
.CX 4762 4469,
.CCX 99 4469 4470,
.CX 4762 4470,
.CX 4762 4469,
.CX 4762 99,
.CX 4762 100,
.CX 4762 4470,
.CCX 100 4470 4471,
.CX 4762 4471,
.CX 4762 4470,
.CX 4762 100,
.CX 4762 101,
.CX 4762 4471,
.CCX 101 4471 4472,
.CX 4762 4472,
.CX 4762 4471,
.CX 4762 101,
.CX 4762 102,
.CX 4762 4472,
.CCX 102 4472 4473,
.CX 4762 4473,
.CX 4762 4472,
.CX 4762 102,
.CX 4762 103,
.CX 4762 4473,
.CCX 103 4473 4474,
.CX 4762 4474,
.CX 4762 4473,
.CX 4762 103,
.CX 4762 104,
.CX 4762 4474,
.CCX 104 4474 4475,
.CX 4762 4475,
.CX 4762 4474,
.CX 4762 104,
.CX 4762 105,
.CX 4762 4475,
.CCX 105 4475 4476,
.CX 4762 4476,
.CX 4762 4475,
.CX 4762 105,
.CX 4762 106,
.CX 4762 4476,
.CCX 106 4476 4477,
.CX 4762 4477,
.CX 4762 4476,
.CX 4762 106,
.CX 4762 107,
.CX 4762 4477,
.CCX 107 4477 4478,
.CX 4762 4478,
.CX 4762 4477,
.CX 4762 107,
.CX 4762 108,
.CX 4762 4478,
.CCX 108 4478 4479,
.CX 4762 4479,
.CX 4762 4478,
.CX 4762 108,
.CX 4762 109,
.CX 4762 4479,
.CCX 109 4479 4480,
.CX 4762 4480,
.CX 4762 4479,
.CX 4762 109,
.CX 4762 110,
.CX 4762 4480,
.CCX 110 4480 4481,
.CX 4762 4481,
.CX 4762 4480,
.CX 4762 110,
.CX 4762 111,
.CX 4762 4481,
.CCX 111 4481 4482,
.CX 4762 4482,
.CX 4762 4481,
.CX 4762 111,
.CX 4762 112,
.CX 4762 4482,
.CCX 112 4482 4483,
.CX 4762 4483,
.CX 4762 4482,
.CX 4762 112,
.CX 4762 113,
.CX 4762 4483,
.CCX 113 4483 4484,
.CX 4762 4484,
.CX 4762 4483,
.CX 4762 113,
.CX 4762 114,
.CX 4762 4484,
.CCX 114 4484 4485,
.CX 4762 4485,
.CX 4762 4484,
.CX 4762 114,
.CX 4762 115,
.CX 4762 4485,
.CCX 115 4485 4486,
.CX 4762 4486,
.CX 4762 4485,
.CX 4762 115,
.CX 4762 116,
.CX 4762 4486,
.CCX 116 4486 4487,
.CX 4762 4487,
.CX 4762 4486,
.CX 4762 116,
.CX 4762 117,
.CX 4762 4487,
.CCX 117 4487 4488,
.CX 4762 4488,
.CX 4762 4487,
.CX 4762 117
]
def block22:Program:=[
.CX 4762 118,
.CX 4762 4488,
.CCX 118 4488 4489,
.CX 4762 4489,
.CX 4762 4488,
.CX 4762 118,
.CX 4762 119,
.CX 4762 4489,
.CCX 119 4489 4490,
.CX 4762 4490,
.CX 4762 4489,
.CX 4762 119,
.CX 4762 120,
.CX 4762 4490,
.CCX 120 4490 4491,
.CX 4762 4491,
.CX 4762 4490,
.CX 4762 120,
.CX 4762 121,
.CX 4762 4491,
.CCX 121 4491 4492,
.CX 4762 4492,
.CX 4762 4491,
.CX 4762 121,
.CX 4762 122,
.CX 4762 4492,
.CCX 122 4492 4493,
.CX 4762 4493,
.CX 4762 4492,
.CX 4762 122,
.CX 4762 123,
.CX 4762 4493,
.CCX 123 4493 4494,
.CX 4762 4494,
.CX 4762 4493,
.CX 4762 123,
.CX 4762 124,
.CX 4762 4494,
.CCX 124 4494 4495,
.CX 4762 4495,
.CX 4762 4494,
.CX 4762 124,
.CX 4762 125,
.CX 4762 4495,
.CCX 125 4495 4496,
.CX 4762 4496,
.CX 4762 4495,
.CX 4762 125,
.CX 4762 126,
.CX 4762 4496,
.CCX 126 4496 4497,
.CX 4762 4497,
.CX 4762 4496,
.CX 4762 126,
.CX 4762 127,
.CX 4762 4497,
.CCX 127 4497 4498,
.CX 4762 4498,
.CX 4762 4497,
.CX 4762 127,
.CX 4762 128,
.CX 4762 4498,
.CCX 128 4498 4499,
.CX 4762 4499,
.CX 4762 4498,
.CX 4762 128,
.CX 4762 129,
.CX 4762 4499,
.CCX 129 4499 4500,
.CX 4762 4500,
.CX 4762 4499,
.CX 4762 129,
.CX 4762 130,
.CX 4762 4500,
.CCX 130 4500 4764,
.CX 4762 4764,
.CX 4762 4500,
.CX 4762 130,
.CX 4762 131,
.CX 4762 4764,
.CCX 131 4764 4765,
.CX 4762 4765,
.CX 4762 4764,
.CX 4762 131,
.CX 4762 132,
.CX 4762 4765,
.CCX 132 4765 4766,
.CX 4762 4766,
.CX 4762 4765,
.CX 4762 132,
.CX 4762 133,
.CX 4762 4766,
.CCX 133 4766 4767,
.CX 4762 4767,
.CX 4762 4766,
.CX 4762 133,
.CX 4762 134,
.CX 4762 4767,
.CCX 134 4767 4768,
.CX 4762 4768,
.CX 4762 4767,
.CX 4762 134,
.CX 4762 135,
.CX 4762 4768,
.CCX 135 4768 4769,
.CX 4762 4769,
.CX 4762 4768,
.CX 4762 135,
.CX 4762 136,
.CX 4762 4769,
.CCX 136 4769 4770,
.CX 4762 4770,
.CX 4762 4769,
.CX 4762 136,
.CX 4762 137,
.CX 4762 4770,
.CCX 137 4770 4771,
.CX 4762 4771,
.CX 4762 4770,
.CX 4762 137,
.CX 4762 138,
.CX 4762 4771,
.CCX 138 4771 4772,
.CX 4762 4772,
.CX 4762 4771,
.CX 4762 138
]
def block23:Program:=[
.CX 4762 139,
.CX 4762 4772,
.CCX 139 4772 4773,
.CX 4762 4773,
.CX 4762 4772,
.CX 4762 139,
.CX 4762 140,
.CX 4762 4773,
.CCX 140 4773 4774,
.CX 4762 4774,
.CX 4762 4773,
.CX 4762 140,
.CX 4762 141,
.CX 4762 4774,
.CCX 141 4774 4775,
.CX 4762 4775,
.CX 4762 4774,
.CX 4762 141,
.CX 4762 142,
.CX 4762 4775,
.CCX 142 4775 4776,
.CX 4762 4776,
.CX 4762 4775,
.CX 4762 142,
.CX 4762 143,
.CX 4762 4776,
.CCX 143 4776 4777,
.CX 4762 4777,
.CX 4762 4776,
.CX 4762 143,
.CX 4762 144,
.CX 4762 4777,
.CCX 144 4777 4778,
.CX 4762 4778,
.CX 4762 4777,
.CX 4762 144,
.CX 4762 145,
.CX 4762 4778,
.CCX 145 4778 4779,
.CX 4762 4779,
.CX 4762 4778,
.CX 4762 145,
.CX 4762 146,
.CX 4762 4779,
.CCX 146 4779 4780,
.CX 4762 4780,
.CX 4762 4779,
.CX 4762 146,
.CX 4762 147,
.CX 4762 4780,
.CCX 147 4780 4781,
.CX 4762 4781,
.CX 4762 4780,
.CX 4762 147,
.CX 4762 148,
.CX 4762 4781,
.CCX 148 4781 4782,
.CX 4762 4782,
.CX 4762 4781,
.CX 4762 148,
.CX 4762 149,
.CX 4762 4782,
.CCX 149 4782 4783,
.CX 4762 4783,
.CX 4762 4782,
.CX 4762 149,
.CX 4762 150,
.CX 4762 4783,
.CCX 150 4783 4784,
.CX 4762 4784,
.CX 4762 4783,
.CX 4762 150,
.CX 4762 151,
.CX 4762 4784,
.CCX 151 4784 4785,
.CX 4762 4785,
.CX 4762 4784,
.CX 4762 151,
.CX 4762 152,
.CX 4762 4785,
.CCX 152 4785 4786,
.CX 4762 4786,
.CX 4762 4785,
.CX 4762 152,
.CX 4762 153,
.CX 4762 4786,
.CCX 153 4786 4787,
.CX 4762 4787,
.CX 4762 4786,
.CX 4762 153,
.CX 4762 154,
.CX 4762 4787,
.CCX 154 4787 4788,
.CX 4762 4788,
.CX 4762 4787,
.CX 4762 154,
.CX 4762 155,
.CX 4762 4788,
.CCX 155 4788 4789,
.CX 4762 4789,
.CX 4762 4788,
.CX 4762 155,
.CX 4762 156,
.CX 4762 4789,
.CCX 156 4789 4790,
.CX 4762 4790,
.CX 4762 4789,
.CX 4762 156,
.CX 4762 157,
.CX 4762 4790,
.CCX 157 4790 4791,
.CX 4762 4791,
.CX 4762 4790,
.CX 4762 157,
.CX 4762 158,
.CX 4762 4791,
.CCX 158 4791 4792,
.CX 4762 4792,
.CX 4762 4791,
.CX 4762 158,
.CX 4762 159,
.CX 4762 4792,
.CCX 159 4792 4793,
.CX 4762 4793,
.CX 4762 4792,
.CX 4762 159
]
def block24:Program:=[
.CX 4762 160,
.CX 4762 4793,
.CCX 160 4793 4794,
.CX 4762 4794,
.CX 4762 4793,
.CX 4762 160,
.CX 4762 161,
.CX 4762 4794,
.CCX 161 4794 4795,
.CX 4762 4795,
.CX 4762 4794,
.CX 4762 161,
.CX 4762 162,
.CX 4762 4795,
.CCX 162 4795 4796,
.CX 4762 4796,
.CX 4762 4795,
.CX 4762 162,
.CX 4762 163,
.CX 4762 4796,
.CCX 163 4796 4797,
.CX 4762 4797,
.CX 4762 4796,
.CX 4762 163,
.CX 4762 164,
.CX 4762 4797,
.CCX 164 4797 4798,
.CX 4762 4798,
.CX 4762 4797,
.CX 4762 164,
.CX 4762 165,
.CX 4762 4798,
.CCX 165 4798 4799,
.CX 4762 4799,
.CX 4762 4798,
.CX 4762 165,
.CX 4762 166,
.CX 4762 4799,
.CCX 166 4799 4800,
.CX 4762 4800,
.CX 4762 4799,
.CX 4762 166,
.CX 4762 167,
.CX 4762 4800,
.CCX 167 4800 4801,
.CX 4762 4801,
.CX 4762 4800,
.CX 4762 167,
.CX 4762 168,
.CX 4762 4801,
.CCX 168 4801 4802,
.CX 4762 4802,
.CX 4762 4801,
.CX 4762 168,
.CX 4762 169,
.CX 4762 4802,
.CCX 169 4802 4803,
.CX 4762 4803,
.CX 4762 4802,
.CX 4762 169,
.CX 4762 170,
.CX 4762 4803,
.CCX 170 4803 4804,
.CX 4762 4804,
.CX 4762 4803,
.CX 4762 170,
.CX 4762 171,
.CX 4762 4804,
.CCX 171 4804 4805,
.CX 4762 4805,
.CX 4762 4804,
.CX 4762 171,
.CX 4762 172,
.CX 4762 4805,
.CCX 172 4805 4806,
.CX 4762 4806,
.CX 4762 4805,
.CX 4762 172,
.CX 4762 173,
.CX 4762 4806,
.CCX 173 4806 4807,
.CX 4762 4807,
.CX 4762 4806,
.CX 4762 173,
.CX 4762 174,
.CX 4762 4807,
.CCX 174 4807 4808,
.CX 4762 4808,
.CX 4762 4807,
.CX 4762 174,
.CX 4762 175,
.CX 4762 4808,
.CCX 175 4808 4809,
.CX 4762 4809,
.CX 4762 4808,
.CX 4762 175,
.CX 4762 176,
.CX 4762 4809,
.CCX 176 4809 4810,
.CX 4762 4810,
.CX 4762 4809,
.CX 4762 176,
.CX 4762 177,
.CX 4762 4810,
.CCX 177 4810 4811,
.CX 4762 4811,
.CX 4762 4810,
.CX 4762 177,
.CX 4762 178,
.CX 4762 4811,
.CCX 178 4811 4812,
.CX 4762 4812,
.CX 4762 4811,
.CX 4762 178,
.CX 4762 179,
.CX 4762 4812,
.CCX 179 4812 4813,
.CX 4762 4813,
.CX 4762 4812,
.CX 4762 179,
.CX 4762 180,
.CX 4762 4813,
.CCX 180 4813 4814,
.CX 4762 4814,
.CX 4762 4813,
.CX 4762 180
]
def block25:Program:=[
.CX 4762 181,
.CX 4762 4814,
.CCX 181 4814 4815,
.CX 4762 4815,
.CX 4762 4814,
.CX 4762 181,
.CX 4762 182,
.CX 4762 4815,
.CCX 182 4815 4816,
.CX 4762 4816,
.CX 4762 4815,
.CX 4762 182,
.CX 4762 183,
.CX 4762 4816,
.CCX 183 4816 4817,
.CX 4762 4817,
.CX 4762 4816,
.CX 4762 183,
.CX 4762 184,
.CX 4762 4817,
.CCX 184 4817 4818,
.CX 4762 4818,
.CX 4762 4817,
.CX 4762 184,
.CX 4762 185,
.CX 4762 4818,
.CCX 185 4818 4819,
.CX 4762 4819,
.CX 4762 4818,
.CX 4762 185,
.CX 4762 186,
.CX 4762 4819,
.CCX 186 4819 4820,
.CX 4762 4820,
.CX 4762 4819,
.CX 4762 186,
.CX 4762 187,
.CX 4762 4820,
.CCX 187 4820 4821,
.CX 4762 4821,
.CX 4762 4820,
.CX 4762 187,
.CX 4762 188,
.CX 4762 4821,
.CCX 188 4821 4822,
.CX 4762 4822,
.CX 4762 4821,
.CX 4762 188,
.CX 4762 189,
.CX 4762 4822,
.CCX 189 4822 4823,
.CX 4762 4823,
.CX 4762 4822,
.CX 4762 189,
.CX 4762 190,
.CX 4762 4823,
.CCX 190 4823 4824,
.CX 4762 4824,
.CX 4762 4823,
.CX 4762 190,
.CX 4762 191,
.CX 4762 4824,
.CCX 191 4824 4825,
.CX 4762 4825,
.CX 4762 4824,
.CX 4762 191,
.CX 4762 192,
.CX 4762 4825,
.CCX 192 4825 4826,
.CX 4762 4826,
.CX 4762 4825,
.CX 4762 192,
.CX 4762 193,
.CX 4762 4826,
.CCX 193 4826 4827,
.CX 4762 4827,
.CX 4762 4826,
.CX 4762 193,
.CX 4762 194,
.CX 4762 4827,
.CCX 194 4827 4828,
.CX 4762 4828,
.CX 4762 4827,
.CX 4762 194,
.CX 4762 195,
.CX 4762 4828,
.CCX 195 4828 4829,
.CX 4762 4829,
.CX 4762 4828,
.CX 4762 195,
.CX 4762 196,
.CX 4762 4829,
.CCX 196 4829 4830,
.CX 4762 4830,
.CX 4762 4829,
.CX 4762 196,
.CX 4762 197,
.CX 4762 4830,
.CCX 197 4830 4831,
.CX 4762 4831,
.CX 4762 4830,
.CX 4762 197,
.CX 4762 198,
.CX 4762 4831,
.CCX 198 4831 4832,
.CX 4762 4832,
.CX 4762 4831,
.CX 4762 198,
.CX 4762 199,
.CX 4762 4832,
.CCX 199 4832 4833,
.CX 4762 4833,
.CX 4762 4832,
.CX 4762 199,
.CX 4762 200,
.CX 4762 4833,
.CCX 200 4833 4834,
.CX 4762 4834,
.CX 4762 4833,
.CX 4762 200,
.CX 4762 201,
.CX 4762 4834,
.CCX 201 4834 4835,
.CX 4762 4835,
.CX 4762 4834,
.CX 4762 201
]
def block26:Program:=[
.CX 4762 202,
.CX 4762 4835,
.CCX 202 4835 4836,
.CX 4762 4836,
.CX 4762 4835,
.CX 4762 202,
.CX 4762 203,
.CX 4762 4836,
.CCX 203 4836 4837,
.CX 4762 4837,
.CX 4762 4836,
.CX 4762 203,
.CX 4762 204,
.CX 4762 4837,
.CCX 204 4837 4838,
.CX 4762 4838,
.CX 4762 4837,
.CX 4762 204,
.CX 4762 205,
.CX 4762 4838,
.CCX 205 4838 4839,
.CX 4762 4839,
.CX 4762 4838,
.CX 4762 205,
.CX 4762 206,
.CX 4762 4839,
.CCX 206 4839 4840,
.CX 4762 4840,
.CX 4762 4839,
.CX 4762 206,
.CX 4762 207,
.CX 4762 4840,
.CCX 207 4840 4841,
.CX 4762 4841,
.CX 4762 4840,
.CX 4762 207,
.CX 4762 208,
.CX 4762 4841,
.CCX 208 4841 4842,
.CX 4762 4842,
.CX 4762 4841,
.CX 4762 208,
.CX 4762 209,
.CX 4762 4842,
.CCX 209 4842 4843,
.CX 4762 4843,
.CX 4762 4842,
.CX 4762 209,
.CX 4762 210,
.CX 4762 4843,
.CCX 210 4843 4844,
.CX 4762 4844,
.CX 4762 4843,
.CX 4762 210,
.CX 4762 211,
.CX 4762 4844,
.CCX 211 4844 4845,
.CX 4762 4845,
.CX 4762 4844,
.CX 4762 211,
.CX 4762 212,
.CX 4762 4845,
.CCX 212 4845 4846,
.CX 4762 4846,
.CX 4762 4845,
.CX 4762 212,
.CX 4762 213,
.CX 4762 4846,
.CCX 213 4846 4847,
.CX 4762 4847,
.CX 4762 4846,
.CX 4762 213,
.CX 4762 214,
.CX 4762 4847,
.CCX 214 4847 4848,
.CX 4762 4848,
.CX 4762 4847,
.CX 4762 214,
.CX 4762 215,
.CX 4762 4848,
.CCX 215 4848 4849,
.CX 4762 4849,
.CX 4762 4848,
.CX 4762 215,
.CX 4762 216,
.CX 4762 4849,
.CCX 216 4849 4850,
.CX 4762 4850,
.CX 4762 4849,
.CX 4762 216,
.CX 4762 217,
.CX 4762 4850,
.CCX 217 4850 4851,
.CX 4762 4851,
.CX 4762 4850,
.CX 4762 217,
.CX 4762 218,
.CX 4762 4851,
.CCX 218 4851 4852,
.CX 4762 4852,
.CX 4762 4851,
.CX 4762 218,
.CX 4762 219,
.CX 4762 4852,
.CCX 219 4852 4853,
.CX 4762 4853,
.CX 4762 4852,
.CX 4762 219,
.CX 4762 220,
.CX 4762 4853,
.CCX 220 4853 4854,
.CX 4762 4854,
.CX 4762 4853,
.CX 4762 220,
.CX 4762 221,
.CX 4762 4854,
.CCX 221 4854 4855,
.CX 4762 4855,
.CX 4762 4854,
.CX 4762 221,
.CX 4762 222,
.CX 4762 4855,
.CCX 222 4855 4856,
.CX 4762 4856,
.CX 4762 4855,
.CX 4762 222
]
def block27:Program:=[
.CX 4762 223,
.CX 4762 4856,
.CCX 223 4856 4857,
.CX 4762 4857,
.CX 4762 4856,
.CX 4762 223,
.CX 4762 224,
.CX 4762 4857,
.CCX 224 4857 4858,
.CX 4762 4858,
.CX 4762 4857,
.CX 4762 224,
.CX 4762 225,
.CX 4762 4858,
.CCX 225 4858 4859,
.CX 4762 4859,
.CX 4762 4858,
.CX 4762 225,
.CX 4762 226,
.CX 4762 4859,
.CCX 226 4859 4860,
.CX 4762 4860,
.CX 4762 4859,
.CX 4762 226,
.CX 4762 227,
.CX 4762 4860,
.CCX 227 4860 4861,
.CX 4762 4861,
.CX 4762 4860,
.CX 4762 227,
.CX 4762 228,
.CX 4762 4861,
.CCX 228 4861 4862,
.CX 4762 4862,
.CX 4762 4861,
.CX 4762 228,
.CX 4762 229,
.CX 4762 4862,
.CCX 229 4862 4863,
.CX 4762 4863,
.CX 4762 4862,
.CX 4762 229,
.CX 4762 230,
.CX 4762 4863,
.CCX 230 4863 4864,
.CX 4762 4864,
.CX 4762 4863,
.CX 4762 230,
.CX 4762 231,
.CX 4762 4864,
.CCX 231 4864 4865,
.CX 4762 4865,
.CX 4762 4864,
.CX 4762 231,
.CX 4762 232,
.CX 4762 4865,
.CCX 232 4865 4866,
.CX 4762 4866,
.CX 4762 4865,
.CX 4762 232,
.CX 4762 233,
.CX 4762 4866,
.CCX 233 4866 4867,
.CX 4762 4867,
.CX 4762 4866,
.CX 4762 233,
.CX 4762 234,
.CX 4762 4867,
.CCX 234 4867 4868,
.CX 4762 4868,
.CX 4762 4867,
.CX 4762 234,
.CX 4762 235,
.CX 4762 4868,
.CCX 235 4868 4869,
.CX 4762 4869,
.CX 4762 4868,
.CX 4762 235,
.CX 4762 236,
.CX 4762 4869,
.CCX 236 4869 4870,
.CX 4762 4870,
.CX 4762 4869,
.CX 4762 236,
.CX 4762 237,
.CX 4762 4870,
.CCX 237 4870 4871,
.CX 4762 4871,
.CX 4762 4870,
.CX 4762 237,
.CX 4762 238,
.CX 4762 4871,
.CCX 238 4871 4872,
.CX 4762 4872,
.CX 4762 4871,
.CX 4762 238,
.CX 4762 239,
.CX 4762 4872,
.CCX 239 4872 4873,
.CX 4762 4873,
.CX 4762 4872,
.CX 4762 239,
.CX 4762 240,
.CX 4762 4873,
.CCX 240 4873 4874,
.CX 4762 4874,
.CX 4762 4873,
.CX 4762 240,
.CX 4762 241,
.CX 4762 4874,
.CCX 241 4874 4875,
.CX 4762 4875,
.CX 4762 4874,
.CX 4762 241,
.CX 4762 242,
.CX 4762 4875,
.CCX 242 4875 4876,
.CX 4762 4876,
.CX 4762 4875,
.CX 4762 242,
.CX 4762 243,
.CX 4762 4876,
.CCX 243 4876 4877,
.CX 4762 4877,
.CX 4762 4876,
.CX 4762 243
]
def block28:Program:=[
.CX 4762 244,
.CX 4762 4877,
.CCX 244 4877 4878,
.CX 4762 4878,
.CX 4762 4877,
.CX 4762 244,
.CX 4762 245,
.CX 4762 4878,
.CCX 245 4878 4879,
.CX 4762 4879,
.CX 4762 4878,
.CX 4762 245,
.CX 4762 246,
.CX 4762 4879,
.CCX 246 4879 4880,
.CX 4762 4880,
.CX 4762 4879,
.CX 4762 246,
.CX 4762 247,
.CX 4762 4880,
.CCX 247 4880 4881,
.CX 4762 4881,
.CX 4762 4880,
.CX 4762 247,
.CX 4762 248,
.CX 4762 4881,
.CCX 248 4881 4882,
.CX 4762 4882,
.CX 4762 4881,
.CX 4762 248,
.CX 4762 249,
.CX 4762 4882,
.CCX 249 4882 4883,
.CX 4762 4883,
.CX 4762 4882,
.CX 4762 249,
.CX 4762 250,
.CX 4762 4883,
.CCX 250 4883 4884,
.CX 4762 4884,
.CX 4762 4883,
.CX 4762 250,
.CX 4762 251,
.CX 4762 4884,
.CCX 251 4884 4885,
.CX 4762 4885,
.CX 4762 4884,
.CX 4762 251,
.CX 4762 252,
.CX 4762 4885,
.CCX 252 4885 4886,
.CX 4762 4886,
.CX 4762 4885,
.CX 4762 252,
.CX 4762 253,
.CX 4762 4886,
.CCX 253 4886 4887,
.CX 4762 4887,
.CX 4762 4886,
.CX 4762 253,
.CX 4762 254,
.CX 4762 4887,
.CCX 254 4887 4888,
.CX 4762 4888,
.CX 4762 4887,
.CX 4762 254,
.CX 4762 255,
.CX 4762 4888,
.CCX 255 4888 4889,
.CX 4762 4889,
.CX 4762 4888,
.CX 4762 255,
.CX 4762 256,
.CX 4762 4889,
.CCX 256 4889 4757,
.CX 4762 4757,
.CX 4762 4889,
.CX 4762 256,
.CX 4762 257,
.CX 4757 257,
.measureX 4757 [] [.CZ 4762 256,.CZ 4762 4889,.CZ 256 4889],
.CX 4762 256,
.CX 4889 256,
.measureX 4889 [] [.CZ 4762 255,.CZ 4762 4888,.CZ 255 4888],
.CX 4762 255,
.CX 4888 255,
.measureX 4888 [] [.CZ 4762 254,.CZ 4762 4887,.CZ 254 4887],
.CX 4762 254,
.CX 4887 254,
.measureX 4887 [] [.CZ 4762 253,.CZ 4762 4886,.CZ 253 4886],
.CX 4762 253,
.CX 4886 253,
.measureX 4886 [] [.CZ 4762 252,.CZ 4762 4885,.CZ 252 4885],
.CX 4762 252,
.CX 4885 252,
.measureX 4885 [] [.CZ 4762 251,.CZ 4762 4884,.CZ 251 4884],
.CX 4762 251,
.CX 4884 251,
.measureX 4884 [] [.CZ 4762 250,.CZ 4762 4883,.CZ 250 4883],
.CX 4762 250,
.CX 4883 250,
.measureX 4883 [] [.CZ 4762 249,.CZ 4762 4882,.CZ 249 4882],
.CX 4762 249,
.CX 4882 249,
.measureX 4882 [] [.CZ 4762 248,.CZ 4762 4881,.CZ 248 4881],
.CX 4762 248,
.CX 4881 248,
.measureX 4881 [] [.CZ 4762 247,.CZ 4762 4880,.CZ 247 4880],
.CX 4762 247,
.CX 4880 247,
.measureX 4880 [] [.CZ 4762 246,.CZ 4762 4879,.CZ 246 4879],
.CX 4762 246,
.CX 4879 246,
.measureX 4879 [] [.CZ 4762 245,.CZ 4762 4878,.CZ 245 4878],
.CX 4762 245,
.CX 4878 245,
.measureX 4878 [] [.CZ 4762 244,.CZ 4762 4877,.CZ 244 4877],
.CX 4762 244,
.CX 4877 244,
.measureX 4877 [] [.CZ 4762 243,.CZ 4762 4876,.CZ 243 4876],
.CX 4762 243,
.CX 4876 243,
.measureX 4876 [] [.CZ 4762 242,.CZ 4762 4875,.CZ 242 4875],
.CX 4762 242,
.CX 4875 242,
.measureX 4875 [] [.CZ 4762 241,.CZ 4762 4874,.CZ 241 4874],
.CX 4762 241,
.CX 4874 241
]
def block29:Program:=[
.measureX 4874 [] [.CZ 4762 240,.CZ 4762 4873,.CZ 240 4873],
.CX 4762 240,
.CX 4873 240,
.measureX 4873 [] [.CZ 4762 239,.CZ 4762 4872,.CZ 239 4872],
.CX 4762 239,
.CX 4872 239,
.measureX 4872 [] [.CZ 4762 238,.CZ 4762 4871,.CZ 238 4871],
.CX 4762 238,
.CX 4871 238,
.measureX 4871 [] [.CZ 4762 237,.CZ 4762 4870,.CZ 237 4870],
.CX 4762 237,
.CX 4870 237,
.measureX 4870 [] [.CZ 4762 236,.CZ 4762 4869,.CZ 236 4869],
.CX 4762 236,
.CX 4869 236,
.measureX 4869 [] [.CZ 4762 235,.CZ 4762 4868,.CZ 235 4868],
.CX 4762 235,
.CX 4868 235,
.measureX 4868 [] [.CZ 4762 234,.CZ 4762 4867,.CZ 234 4867],
.CX 4762 234,
.CX 4867 234,
.measureX 4867 [] [.CZ 4762 233,.CZ 4762 4866,.CZ 233 4866],
.CX 4762 233,
.CX 4866 233,
.measureX 4866 [] [.CZ 4762 232,.CZ 4762 4865,.CZ 232 4865],
.CX 4762 232,
.CX 4865 232,
.measureX 4865 [] [.CZ 4762 231,.CZ 4762 4864,.CZ 231 4864],
.CX 4762 231,
.CX 4864 231,
.measureX 4864 [] [.CZ 4762 230,.CZ 4762 4863,.CZ 230 4863],
.CX 4762 230,
.CX 4863 230,
.measureX 4863 [] [.CZ 4762 229,.CZ 4762 4862,.CZ 229 4862],
.CX 4762 229,
.CX 4862 229,
.measureX 4862 [] [.CZ 4762 228,.CZ 4762 4861,.CZ 228 4861],
.CX 4762 228,
.CX 4861 228,
.measureX 4861 [] [.CZ 4762 227,.CZ 4762 4860,.CZ 227 4860],
.CX 4762 227,
.CX 4860 227,
.measureX 4860 [] [.CZ 4762 226,.CZ 4762 4859,.CZ 226 4859],
.CX 4762 226,
.CX 4859 226,
.measureX 4859 [] [.CZ 4762 225,.CZ 4762 4858,.CZ 225 4858],
.CX 4762 225,
.CX 4858 225,
.measureX 4858 [] [.CZ 4762 224,.CZ 4762 4857,.CZ 224 4857],
.CX 4762 224,
.CX 4857 224,
.measureX 4857 [] [.CZ 4762 223,.CZ 4762 4856,.CZ 223 4856],
.CX 4762 223,
.CX 4856 223,
.measureX 4856 [] [.CZ 4762 222,.CZ 4762 4855,.CZ 222 4855],
.CX 4762 222,
.CX 4855 222,
.measureX 4855 [] [.CZ 4762 221,.CZ 4762 4854,.CZ 221 4854],
.CX 4762 221,
.CX 4854 221,
.measureX 4854 [] [.CZ 4762 220,.CZ 4762 4853,.CZ 220 4853],
.CX 4762 220,
.CX 4853 220,
.measureX 4853 [] [.CZ 4762 219,.CZ 4762 4852,.CZ 219 4852],
.CX 4762 219,
.CX 4852 219,
.measureX 4852 [] [.CZ 4762 218,.CZ 4762 4851,.CZ 218 4851],
.CX 4762 218,
.CX 4851 218,
.measureX 4851 [] [.CZ 4762 217,.CZ 4762 4850,.CZ 217 4850],
.CX 4762 217,
.CX 4850 217,
.measureX 4850 [] [.CZ 4762 216,.CZ 4762 4849,.CZ 216 4849],
.CX 4762 216,
.CX 4849 216,
.measureX 4849 [] [.CZ 4762 215,.CZ 4762 4848,.CZ 215 4848],
.CX 4762 215,
.CX 4848 215,
.measureX 4848 [] [.CZ 4762 214,.CZ 4762 4847,.CZ 214 4847],
.CX 4762 214,
.CX 4847 214,
.measureX 4847 [] [.CZ 4762 213,.CZ 4762 4846,.CZ 213 4846],
.CX 4762 213,
.CX 4846 213,
.measureX 4846 [] [.CZ 4762 212,.CZ 4762 4845,.CZ 212 4845],
.CX 4762 212,
.CX 4845 212,
.measureX 4845 [] [.CZ 4762 211,.CZ 4762 4844,.CZ 211 4844],
.CX 4762 211,
.CX 4844 211,
.measureX 4844 [] [.CZ 4762 210,.CZ 4762 4843,.CZ 210 4843],
.CX 4762 210,
.CX 4843 210,
.measureX 4843 [] [.CZ 4762 209,.CZ 4762 4842,.CZ 209 4842],
.CX 4762 209,
.CX 4842 209,
.measureX 4842 [] [.CZ 4762 208,.CZ 4762 4841,.CZ 208 4841],
.CX 4762 208,
.CX 4841 208,
.measureX 4841 [] [.CZ 4762 207,.CZ 4762 4840,.CZ 207 4840],
.CX 4762 207,
.CX 4840 207,
.measureX 4840 [] [.CZ 4762 206,.CZ 4762 4839,.CZ 206 4839],
.CX 4762 206,
.CX 4839 206,
.measureX 4839 [] [.CZ 4762 205,.CZ 4762 4838,.CZ 205 4838],
.CX 4762 205,
.CX 4838 205,
.measureX 4838 [] [.CZ 4762 204,.CZ 4762 4837,.CZ 204 4837],
.CX 4762 204,
.CX 4837 204,
.measureX 4837 [] [.CZ 4762 203,.CZ 4762 4836,.CZ 203 4836],
.CX 4762 203,
.CX 4836 203,
.measureX 4836 [] [.CZ 4762 202,.CZ 4762 4835,.CZ 202 4835],
.CX 4762 202,
.CX 4835 202,
.measureX 4835 [] [.CZ 4762 201,.CZ 4762 4834,.CZ 201 4834],
.CX 4762 201,
.CX 4834 201,
.measureX 4834 [] [.CZ 4762 200,.CZ 4762 4833,.CZ 200 4833],
.CX 4762 200,
.CX 4833 200,
.measureX 4833 [] [.CZ 4762 199,.CZ 4762 4832,.CZ 199 4832],
.CX 4762 199,
.CX 4832 199,
.measureX 4832 [] [.CZ 4762 198,.CZ 4762 4831,.CZ 198 4831],
.CX 4762 198
]
def block30:Program:=[
.CX 4831 198,
.measureX 4831 [] [.CZ 4762 197,.CZ 4762 4830,.CZ 197 4830],
.CX 4762 197,
.CX 4830 197,
.measureX 4830 [] [.CZ 4762 196,.CZ 4762 4829,.CZ 196 4829],
.CX 4762 196,
.CX 4829 196,
.measureX 4829 [] [.CZ 4762 195,.CZ 4762 4828,.CZ 195 4828],
.CX 4762 195,
.CX 4828 195,
.measureX 4828 [] [.CZ 4762 194,.CZ 4762 4827,.CZ 194 4827],
.CX 4762 194,
.CX 4827 194,
.measureX 4827 [] [.CZ 4762 193,.CZ 4762 4826,.CZ 193 4826],
.CX 4762 193,
.CX 4826 193,
.measureX 4826 [] [.CZ 4762 192,.CZ 4762 4825,.CZ 192 4825],
.CX 4762 192,
.CX 4825 192,
.measureX 4825 [] [.CZ 4762 191,.CZ 4762 4824,.CZ 191 4824],
.CX 4762 191,
.CX 4824 191,
.measureX 4824 [] [.CZ 4762 190,.CZ 4762 4823,.CZ 190 4823],
.CX 4762 190,
.CX 4823 190,
.measureX 4823 [] [.CZ 4762 189,.CZ 4762 4822,.CZ 189 4822],
.CX 4762 189,
.CX 4822 189,
.measureX 4822 [] [.CZ 4762 188,.CZ 4762 4821,.CZ 188 4821],
.CX 4762 188,
.CX 4821 188,
.measureX 4821 [] [.CZ 4762 187,.CZ 4762 4820,.CZ 187 4820],
.CX 4762 187,
.CX 4820 187,
.measureX 4820 [] [.CZ 4762 186,.CZ 4762 4819,.CZ 186 4819],
.CX 4762 186,
.CX 4819 186,
.measureX 4819 [] [.CZ 4762 185,.CZ 4762 4818,.CZ 185 4818],
.CX 4762 185,
.CX 4818 185,
.measureX 4818 [] [.CZ 4762 184,.CZ 4762 4817,.CZ 184 4817],
.CX 4762 184,
.CX 4817 184,
.measureX 4817 [] [.CZ 4762 183,.CZ 4762 4816,.CZ 183 4816],
.CX 4762 183,
.CX 4816 183,
.measureX 4816 [] [.CZ 4762 182,.CZ 4762 4815,.CZ 182 4815],
.CX 4762 182,
.CX 4815 182,
.measureX 4815 [] [.CZ 4762 181,.CZ 4762 4814,.CZ 181 4814],
.CX 4762 181,
.CX 4814 181,
.measureX 4814 [] [.CZ 4762 180,.CZ 4762 4813,.CZ 180 4813],
.CX 4762 180,
.CX 4813 180,
.measureX 4813 [] [.CZ 4762 179,.CZ 4762 4812,.CZ 179 4812],
.CX 4762 179,
.CX 4812 179,
.measureX 4812 [] [.CZ 4762 178,.CZ 4762 4811,.CZ 178 4811],
.CX 4762 178,
.CX 4811 178,
.measureX 4811 [] [.CZ 4762 177,.CZ 4762 4810,.CZ 177 4810],
.CX 4762 177,
.CX 4810 177,
.measureX 4810 [] [.CZ 4762 176,.CZ 4762 4809,.CZ 176 4809],
.CX 4762 176,
.CX 4809 176,
.measureX 4809 [] [.CZ 4762 175,.CZ 4762 4808,.CZ 175 4808],
.CX 4762 175,
.CX 4808 175,
.measureX 4808 [] [.CZ 4762 174,.CZ 4762 4807,.CZ 174 4807],
.CX 4762 174,
.CX 4807 174,
.measureX 4807 [] [.CZ 4762 173,.CZ 4762 4806,.CZ 173 4806],
.CX 4762 173,
.CX 4806 173,
.measureX 4806 [] [.CZ 4762 172,.CZ 4762 4805,.CZ 172 4805],
.CX 4762 172,
.CX 4805 172,
.measureX 4805 [] [.CZ 4762 171,.CZ 4762 4804,.CZ 171 4804],
.CX 4762 171,
.CX 4804 171,
.measureX 4804 [] [.CZ 4762 170,.CZ 4762 4803,.CZ 170 4803],
.CX 4762 170,
.CX 4803 170,
.measureX 4803 [] [.CZ 4762 169,.CZ 4762 4802,.CZ 169 4802],
.CX 4762 169,
.CX 4802 169,
.measureX 4802 [] [.CZ 4762 168,.CZ 4762 4801,.CZ 168 4801],
.CX 4762 168,
.CX 4801 168,
.measureX 4801 [] [.CZ 4762 167,.CZ 4762 4800,.CZ 167 4800],
.CX 4762 167,
.CX 4800 167,
.measureX 4800 [] [.CZ 4762 166,.CZ 4762 4799,.CZ 166 4799],
.CX 4762 166,
.CX 4799 166,
.measureX 4799 [] [.CZ 4762 165,.CZ 4762 4798,.CZ 165 4798],
.CX 4762 165,
.CX 4798 165,
.measureX 4798 [] [.CZ 4762 164,.CZ 4762 4797,.CZ 164 4797],
.CX 4762 164,
.CX 4797 164,
.measureX 4797 [] [.CZ 4762 163,.CZ 4762 4796,.CZ 163 4796],
.CX 4762 163,
.CX 4796 163,
.measureX 4796 [] [.CZ 4762 162,.CZ 4762 4795,.CZ 162 4795],
.CX 4762 162,
.CX 4795 162,
.measureX 4795 [] [.CZ 4762 161,.CZ 4762 4794,.CZ 161 4794],
.CX 4762 161,
.CX 4794 161,
.measureX 4794 [] [.CZ 4762 160,.CZ 4762 4793,.CZ 160 4793],
.CX 4762 160,
.CX 4793 160,
.measureX 4793 [] [.CZ 4762 159,.CZ 4762 4792,.CZ 159 4792],
.CX 4762 159,
.CX 4792 159,
.measureX 4792 [] [.CZ 4762 158,.CZ 4762 4791,.CZ 158 4791],
.CX 4762 158,
.CX 4791 158,
.measureX 4791 [] [.CZ 4762 157,.CZ 4762 4790,.CZ 157 4790],
.CX 4762 157,
.CX 4790 157,
.measureX 4790 [] [.CZ 4762 156,.CZ 4762 4789,.CZ 156 4789],
.CX 4762 156,
.CX 4789 156,
.measureX 4789 [] [.CZ 4762 155,.CZ 4762 4788,.CZ 155 4788]
]
def block31:Program:=[
.CX 4762 155,
.CX 4788 155,
.measureX 4788 [] [.CZ 4762 154,.CZ 4762 4787,.CZ 154 4787],
.CX 4762 154,
.CX 4787 154,
.measureX 4787 [] [.CZ 4762 153,.CZ 4762 4786,.CZ 153 4786],
.CX 4762 153,
.CX 4786 153,
.measureX 4786 [] [.CZ 4762 152,.CZ 4762 4785,.CZ 152 4785],
.CX 4762 152,
.CX 4785 152,
.measureX 4785 [] [.CZ 4762 151,.CZ 4762 4784,.CZ 151 4784],
.CX 4762 151,
.CX 4784 151,
.measureX 4784 [] [.CZ 4762 150,.CZ 4762 4783,.CZ 150 4783],
.CX 4762 150,
.CX 4783 150,
.measureX 4783 [] [.CZ 4762 149,.CZ 4762 4782,.CZ 149 4782],
.CX 4762 149,
.CX 4782 149,
.measureX 4782 [] [.CZ 4762 148,.CZ 4762 4781,.CZ 148 4781],
.CX 4762 148,
.CX 4781 148,
.measureX 4781 [] [.CZ 4762 147,.CZ 4762 4780,.CZ 147 4780],
.CX 4762 147,
.CX 4780 147,
.measureX 4780 [] [.CZ 4762 146,.CZ 4762 4779,.CZ 146 4779],
.CX 4762 146,
.CX 4779 146,
.measureX 4779 [] [.CZ 4762 145,.CZ 4762 4778,.CZ 145 4778],
.CX 4762 145,
.CX 4778 145,
.measureX 4778 [] [.CZ 4762 144,.CZ 4762 4777,.CZ 144 4777],
.CX 4762 144,
.CX 4777 144,
.measureX 4777 [] [.CZ 4762 143,.CZ 4762 4776,.CZ 143 4776],
.CX 4762 143,
.CX 4776 143,
.measureX 4776 [] [.CZ 4762 142,.CZ 4762 4775,.CZ 142 4775],
.CX 4762 142,
.CX 4775 142,
.measureX 4775 [] [.CZ 4762 141,.CZ 4762 4774,.CZ 141 4774],
.CX 4762 141,
.CX 4774 141,
.measureX 4774 [] [.CZ 4762 140,.CZ 4762 4773,.CZ 140 4773],
.CX 4762 140,
.CX 4773 140,
.measureX 4773 [] [.CZ 4762 139,.CZ 4762 4772,.CZ 139 4772],
.CX 4762 139,
.CX 4772 139,
.measureX 4772 [] [.CZ 4762 138,.CZ 4762 4771,.CZ 138 4771],
.CX 4762 138,
.CX 4771 138,
.measureX 4771 [] [.CZ 4762 137,.CZ 4762 4770,.CZ 137 4770],
.CX 4762 137,
.CX 4770 137,
.measureX 4770 [] [.CZ 4762 136,.CZ 4762 4769,.CZ 136 4769],
.CX 4762 136,
.CX 4769 136,
.measureX 4769 [] [.CZ 4762 135,.CZ 4762 4768,.CZ 135 4768],
.CX 4762 135,
.CX 4768 135,
.measureX 4768 [] [.CZ 4762 134,.CZ 4762 4767,.CZ 134 4767],
.CX 4762 134,
.CX 4767 134,
.measureX 4767 [] [.CZ 4762 133,.CZ 4762 4766,.CZ 133 4766],
.CX 4762 133,
.CX 4766 133,
.measureX 4766 [] [.CZ 4762 132,.CZ 4762 4765,.CZ 132 4765],
.CX 4762 132,
.CX 4765 132,
.measureX 4765 [] [.CZ 4762 131,.CZ 4762 4764,.CZ 131 4764],
.CX 4762 131,
.CX 4764 131,
.measureX 4764 [] [.CZ 4762 130,.CZ 4762 4500,.CZ 130 4500],
.CX 4762 130,
.CX 4500 130,
.measureX 4500 [] [.CZ 4762 129,.CZ 4762 4499,.CZ 129 4499],
.CX 4762 129,
.CX 4499 129,
.measureX 4499 [] [.CZ 4762 128,.CZ 4762 4498,.CZ 128 4498],
.CX 4762 128,
.CX 4498 128,
.measureX 4498 [] [.CZ 4762 127,.CZ 4762 4497,.CZ 127 4497],
.CX 4762 127,
.CX 4497 127,
.measureX 4497 [] [.CZ 4762 126,.CZ 4762 4496,.CZ 126 4496],
.CX 4762 126,
.CX 4496 126,
.measureX 4496 [] [.CZ 4762 125,.CZ 4762 4495,.CZ 125 4495],
.CX 4762 125,
.CX 4495 125,
.measureX 4495 [] [.CZ 4762 124,.CZ 4762 4494,.CZ 124 4494],
.CX 4762 124,
.CX 4494 124,
.measureX 4494 [] [.CZ 4762 123,.CZ 4762 4493,.CZ 123 4493],
.CX 4762 123,
.CX 4493 123,
.measureX 4493 [] [.CZ 4762 122,.CZ 4762 4492,.CZ 122 4492],
.CX 4762 122,
.CX 4492 122,
.measureX 4492 [] [.CZ 4762 121,.CZ 4762 4491,.CZ 121 4491],
.CX 4762 121,
.CX 4491 121,
.measureX 4491 [] [.CZ 4762 120,.CZ 4762 4490,.CZ 120 4490],
.CX 4762 120,
.CX 4490 120,
.measureX 4490 [] [.CZ 4762 119,.CZ 4762 4489,.CZ 119 4489],
.CX 4762 119,
.CX 4489 119,
.measureX 4489 [] [.CZ 4762 118,.CZ 4762 4488,.CZ 118 4488],
.CX 4762 118,
.CX 4488 118,
.measureX 4488 [] [.CZ 4762 117,.CZ 4762 4487,.CZ 117 4487],
.CX 4762 117,
.CX 4487 117,
.measureX 4487 [] [.CZ 4762 116,.CZ 4762 4486,.CZ 116 4486],
.CX 4762 116,
.CX 4486 116,
.measureX 4486 [] [.CZ 4762 115,.CZ 4762 4485,.CZ 115 4485],
.CX 4762 115,
.CX 4485 115,
.measureX 4485 [] [.CZ 4762 114,.CZ 4762 4484,.CZ 114 4484],
.CX 4762 114,
.CX 4484 114,
.measureX 4484 [] [.CZ 4762 113,.CZ 4762 4483,.CZ 113 4483],
.CX 4762 113,
.CX 4483 113
]
def block32:Program:=[
.measureX 4483 [] [.CZ 4762 112,.CZ 4762 4482,.CZ 112 4482],
.CX 4762 112,
.CX 4482 112,
.measureX 4482 [] [.CZ 4762 111,.CZ 4762 4481,.CZ 111 4481],
.CX 4762 111,
.CX 4481 111,
.measureX 4481 [] [.CZ 4762 110,.CZ 4762 4480,.CZ 110 4480],
.CX 4762 110,
.CX 4480 110,
.measureX 4480 [] [.CZ 4762 109,.CZ 4762 4479,.CZ 109 4479],
.CX 4762 109,
.CX 4479 109,
.measureX 4479 [] [.CZ 4762 108,.CZ 4762 4478,.CZ 108 4478],
.CX 4762 108,
.CX 4478 108,
.measureX 4478 [] [.CZ 4762 107,.CZ 4762 4477,.CZ 107 4477],
.CX 4762 107,
.CX 4477 107,
.measureX 4477 [] [.CZ 4762 106,.CZ 4762 4476,.CZ 106 4476],
.CX 4762 106,
.CX 4476 106,
.measureX 4476 [] [.CZ 4762 105,.CZ 4762 4475,.CZ 105 4475],
.CX 4762 105,
.CX 4475 105,
.measureX 4475 [] [.CZ 4762 104,.CZ 4762 4474,.CZ 104 4474],
.CX 4762 104,
.CX 4474 104,
.measureX 4474 [] [.CZ 4762 103,.CZ 4762 4473,.CZ 103 4473],
.CX 4762 103,
.CX 4473 103,
.measureX 4473 [] [.CZ 4762 102,.CZ 4762 4472,.CZ 102 4472],
.CX 4762 102,
.CX 4472 102,
.measureX 4472 [] [.CZ 4762 101,.CZ 4762 4471,.CZ 101 4471],
.CX 4762 101,
.CX 4471 101,
.measureX 4471 [] [.CZ 4762 100,.CZ 4762 4470,.CZ 100 4470],
.CX 4762 100,
.CX 4470 100,
.measureX 4470 [] [.CZ 4762 99,.CZ 4762 4469,.CZ 99 4469],
.CX 4762 99,
.CX 4469 99,
.measureX 4469 [] [.CZ 4762 98,.CZ 4762 4468,.CZ 98 4468],
.CX 4762 98,
.CX 4468 98,
.measureX 4468 [] [.CZ 4762 97,.CZ 4762 4467,.CZ 97 4467],
.CX 4762 97,
.CX 4467 97,
.measureX 4467 [] [.CZ 4762 96,.CZ 4762 4466,.CZ 96 4466],
.CX 4762 96,
.CX 4466 96,
.measureX 4466 [] [.CZ 4762 95,.CZ 4762 4465,.CZ 95 4465],
.CX 4762 95,
.CX 4465 95,
.measureX 4465 [] [.CZ 4762 94,.CZ 4762 4464,.CZ 94 4464],
.CX 4762 94,
.CX 4464 94,
.measureX 4464 [] [.CZ 4762 93,.CZ 4762 4463,.CZ 93 4463],
.CX 4762 93,
.CX 4463 93,
.measureX 4463 [] [.CZ 4762 92,.CZ 4762 4462,.CZ 92 4462],
.CX 4762 92,
.CX 4462 92,
.measureX 4462 [] [.CZ 4762 91,.CZ 4762 4461,.CZ 91 4461],
.CX 4762 91,
.CX 4461 91,
.measureX 4461 [] [.CZ 4762 90,.CZ 4762 4460,.CZ 90 4460],
.CX 4762 90,
.CX 4460 90,
.measureX 4460 [] [.CZ 4762 89,.CZ 4762 4459,.CZ 89 4459],
.CX 4762 89,
.CX 4459 89,
.measureX 4459 [] [.CZ 4762 88,.CZ 4762 4458,.CZ 88 4458],
.CX 4762 88,
.CX 4458 88,
.measureX 4458 [] [.CZ 4762 87,.CZ 4762 4457,.CZ 87 4457],
.CX 4762 87,
.CX 4457 87,
.measureX 4457 [] [.CZ 4762 86,.CZ 4762 4456,.CZ 86 4456],
.CX 4762 86,
.CX 4456 86,
.measureX 4456 [] [.CZ 4762 85,.CZ 4762 4455,.CZ 85 4455],
.CX 4762 85,
.CX 4455 85,
.measureX 4455 [] [.CZ 4762 84,.CZ 4762 4454,.CZ 84 4454],
.CX 4762 84,
.CX 4454 84,
.measureX 4454 [] [.CZ 4762 83,.CZ 4762 4453,.CZ 83 4453],
.CX 4762 83,
.CX 4453 83,
.measureX 4453 [] [.CZ 4762 82,.CZ 4762 4452,.CZ 82 4452],
.CX 4762 82,
.CX 4452 82,
.measureX 4452 [] [.CZ 4762 81,.CZ 4762 4451,.CZ 81 4451],
.CX 4762 81,
.CX 4451 81,
.measureX 4451 [] [.CZ 4762 80,.CZ 4762 4450,.CZ 80 4450],
.CX 4762 80,
.CX 4450 80,
.measureX 4450 [] [.CZ 4762 79,.CZ 4762 4449,.CZ 79 4449],
.CX 4762 79,
.CX 4449 79,
.measureX 4449 [] [.CZ 4762 78,.CZ 4762 4448,.CZ 78 4448],
.CX 4762 78,
.CX 4448 78,
.measureX 4448 [] [.CZ 4762 77,.CZ 4762 4447,.CZ 77 4447],
.CX 4762 77,
.CX 4447 77,
.measureX 4447 [] [.CZ 4762 76,.CZ 4762 4446,.CZ 76 4446],
.CX 4762 76,
.CX 4446 76,
.measureX 4446 [] [.CZ 4762 75,.CZ 4762 4445,.CZ 75 4445],
.CX 4762 75,
.CX 4445 75,
.measureX 4445 [] [.CZ 4762 74,.CZ 4762 4444,.CZ 74 4444],
.CX 4762 74,
.CX 4444 74,
.measureX 4444 [] [.CZ 4762 73,.CZ 4762 4443,.CZ 73 4443],
.CX 4762 73,
.CX 4443 73,
.measureX 4443 [] [.CZ 4762 72,.CZ 4762 4442,.CZ 72 4442],
.CX 4762 72,
.CX 4442 72,
.measureX 4442 [] [.CZ 4762 71,.CZ 4762 4441,.CZ 71 4441],
.CX 4762 71,
.CX 4441 71,
.measureX 4441 [] [.CZ 4762 70,.CZ 4762 4440,.CZ 70 4440],
.CX 4762 70
]
def block33:Program:=[
.CX 4440 70,
.measureX 4440 [] [.CZ 4762 69,.CZ 4762 4439,.CZ 69 4439],
.CX 4762 69,
.CX 4439 69,
.measureX 4439 [] [.CZ 4762 68,.CZ 4762 4438,.CZ 68 4438],
.CX 4762 68,
.CX 4438 68,
.measureX 4438 [] [.CZ 4762 67,.CZ 4762 4437,.CZ 67 4437],
.CX 4762 67,
.CX 4437 67,
.measureX 4437 [] [.CZ 4762 66,.CZ 4762 4436,.CZ 66 4436],
.CX 4762 66,
.CX 4436 66,
.measureX 4436 [] [.CZ 4762 65,.CZ 4762 4435,.CZ 65 4435],
.CX 4762 65,
.CX 4435 65,
.measureX 4435 [] [.CZ 4762 64,.CZ 4762 4434,.CZ 64 4434],
.CX 4762 64,
.CX 4434 64,
.measureX 4434 [] [.CZ 4762 63,.CZ 4762 4433,.CZ 63 4433],
.CX 4762 63,
.CX 4433 63,
.measureX 4433 [] [.CZ 4762 62,.CZ 4762 4432,.CZ 62 4432],
.CX 4762 62,
.CX 4432 62,
.measureX 4432 [] [.CZ 4762 61,.CZ 4762 4431,.CZ 61 4431],
.CX 4762 61,
.CX 4431 61,
.measureX 4431 [] [.CZ 4762 60,.CZ 4762 4430,.CZ 60 4430],
.CX 4762 60,
.CX 4430 60,
.measureX 4430 [] [.CZ 4762 59,.CZ 4762 4429,.CZ 59 4429],
.CX 4762 59,
.CX 4429 59,
.measureX 4429 [] [.CZ 4762 58,.CZ 4762 4428,.CZ 58 4428],
.CX 4762 58,
.CX 4428 58,
.measureX 4428 [] [.CZ 4762 57,.CZ 4762 4427,.CZ 57 4427],
.CX 4762 57,
.CX 4427 57,
.measureX 4427 [] [.CZ 4762 56,.CZ 4762 4426,.CZ 56 4426],
.CX 4762 56,
.CX 4426 56,
.measureX 4426 [] [.CZ 4762 55,.CZ 4762 4425,.CZ 55 4425],
.CX 4762 55,
.CX 4425 55,
.measureX 4425 [] [.CZ 4762 54,.CZ 4762 4424,.CZ 54 4424],
.CX 4762 54,
.CX 4424 54,
.measureX 4424 [] [.CZ 4762 53,.CZ 4762 4423,.CZ 53 4423],
.CX 4762 53,
.CX 4423 53,
.measureX 4423 [] [.CZ 4762 52,.CZ 4762 4422,.CZ 52 4422],
.CX 4762 52,
.CX 4422 52,
.measureX 4422 [] [.CZ 4762 51,.CZ 4762 4421,.CZ 51 4421],
.CX 4762 51,
.CX 4421 51,
.measureX 4421 [] [.CZ 4762 50,.CZ 4762 4420,.CZ 50 4420],
.CX 4762 50,
.CX 4420 50,
.measureX 4420 [] [.CZ 4762 49,.CZ 4762 4419,.CZ 49 4419],
.CX 4762 49,
.CX 4419 49,
.measureX 4419 [] [.CZ 4762 48,.CZ 4762 4418,.CZ 48 4418],
.CX 4762 48,
.CX 4418 48,
.measureX 4418 [] [.CZ 4762 47,.CZ 4762 4417,.CZ 47 4417],
.CX 4762 47,
.CX 4417 47,
.measureX 4417 [] [.CZ 4762 46,.CZ 4762 4416,.CZ 46 4416],
.CX 4762 46,
.CX 4416 46,
.measureX 4416 [] [.CZ 4762 45,.CZ 4762 4415,.CZ 45 4415],
.CX 4762 45,
.CX 4415 45,
.measureX 4415 [] [.CZ 4762 44,.CZ 4762 4414,.CZ 44 4414],
.CX 4762 44,
.CX 4414 44,
.measureX 4414 [] [.CZ 4762 43,.CZ 4762 4413,.CZ 43 4413],
.CX 4762 43,
.CX 4413 43,
.measureX 4413 [] [.CZ 4762 42,.CZ 4762 4412,.CZ 42 4412],
.CX 4762 42,
.CX 4412 42,
.measureX 4412 [] [.CZ 4762 41,.CZ 4762 4411,.CZ 41 4411],
.CX 4762 41,
.CX 4411 41,
.measureX 4411 [] [.CZ 4762 40,.CZ 4762 4410,.CZ 40 4410],
.CX 4762 40,
.CX 4410 40,
.measureX 4410 [] [.CZ 4762 39,.CZ 4762 4409,.CZ 39 4409],
.CX 4762 39,
.CX 4409 39,
.measureX 4409 [] [.CZ 4762 38,.CZ 4762 4408,.CZ 38 4408],
.CX 4762 38,
.CX 4408 38,
.measureX 4408 [] [.CZ 4762 37,.CZ 4762 4407,.CZ 37 4407],
.CX 4762 37,
.CX 4407 37,
.measureX 4407 [] [.CZ 4762 36,.CZ 4762 4406,.CZ 36 4406],
.CX 4762 36,
.CX 4406 36,
.measureX 4406 [] [.CZ 4762 35,.CZ 4762 4405,.CZ 35 4405],
.CX 4762 35,
.CX 4405 35,
.measureX 4405 [] [.CZ 34 4404],
.CX 4404 34,
.measureX 4404 [] [.CZ 4762 33,.CZ 4762 4403,.CZ 33 4403],
.CX 4762 33,
.CX 4403 33,
.measureX 4403 [] [.CZ 4762 32,.CZ 4762 4402,.CZ 32 4402],
.CX 4762 32,
.CX 4402 32,
.measureX 4402 [] [.CZ 4762 31,.CZ 4762 4401,.CZ 31 4401],
.CX 4762 31,
.CX 4401 31,
.measureX 4401 [] [.CZ 4762 30,.CZ 4762 4400,.CZ 30 4400],
.CX 4762 30,
.CX 4400 30,
.measureX 4400 [] [.CZ 4762 29,.CZ 4762 4399,.CZ 29 4399],
.CX 4762 29,
.CX 4399 29,
.measureX 4399 [] [.CZ 4762 28,.CZ 4762 4398,.CZ 28 4398],
.CX 4762 28,
.CX 4398 28,
.measureX 4398 [] [.CZ 4762 27,.CZ 4762 4397,.CZ 27 4397],
.CX 4762 27
]
def block34:Program:=[
.CX 4397 27,
.measureX 4397 [] [.CZ 4762 26,.CZ 4762 4396,.CZ 26 4396],
.CX 4762 26,
.CX 4396 26,
.measureX 4396 [] [.CZ 4762 25,.CZ 4762 4395,.CZ 25 4395],
.CX 4762 25,
.CX 4395 25,
.measureX 4395 [] [.CZ 4762 24,.CZ 4762 4394,.CZ 24 4394],
.CX 4762 24,
.CX 4394 24,
.measureX 4394 [] [.CZ 4762 23,.CZ 4762 4393,.CZ 23 4393],
.CX 4762 23,
.CX 4393 23,
.measureX 4393 [] [.CZ 4762 22,.CZ 4762 4392,.CZ 22 4392],
.CX 4762 22,
.CX 4392 22,
.measureX 4392 [] [.CZ 4762 21,.CZ 4762 4391,.CZ 21 4391],
.CX 4762 21,
.CX 4391 21,
.measureX 4391 [] [.CZ 4762 20,.CZ 4762 4390,.CZ 20 4390],
.CX 4762 20,
.CX 4390 20,
.measureX 4390 [] [.CZ 4762 19,.CZ 4762 4389,.CZ 19 4389],
.CX 4762 19,
.CX 4389 19,
.measureX 4389 [] [.CZ 4762 18,.CZ 4762 4388,.CZ 18 4388],
.CX 4762 18,
.CX 4388 18,
.measureX 4388 [] [.CZ 4762 17,.CZ 4762 4387,.CZ 17 4387],
.CX 4762 17,
.CX 4387 17,
.measureX 4387 [] [.CZ 4762 16,.CZ 4762 4386,.CZ 16 4386],
.CX 4762 16,
.CX 4386 16,
.measureX 4386 [] [.CZ 4762 15,.CZ 4762 4385,.CZ 15 4385],
.CX 4762 15,
.CX 4385 15,
.measureX 4385 [] [.CZ 4762 14,.CZ 4762 4384,.CZ 14 4384],
.CX 4762 14,
.CX 4384 14,
.measureX 4384 [] [.CZ 4762 13,.CZ 4762 4383,.CZ 13 4383],
.CX 4762 13,
.CX 4383 13,
.measureX 4383 [] [.CZ 4762 12,.CZ 4762 4382,.CZ 12 4382],
.CX 4762 12,
.CX 4382 12,
.measureX 4382 [] [.CZ 11 4381],
.CX 4381 11,
.measureX 4381 [] [.CZ 10 4380],
.CX 4380 10,
.measureX 4380 [] [.CZ 9 4379],
.CX 4379 9,
.measureX 4379 [] [.CZ 8 4378],
.CX 4378 8,
.measureX 4378 [] [.CZ 4762 7,.CZ 4762 4377,.CZ 7 4377],
.CX 4762 7,
.CX 4377 7,
.measureX 4377 [] [.CZ 6 4376],
.CX 4376 6,
.measureX 4376 [] [.CZ 4762 5,.CZ 4762 4375,.CZ 5 4375],
.CX 4762 5,
.CX 4375 5,
.measureX 4375 [] [.CZ 4762 4,.CZ 4762 4374,.CZ 4 4374],
.CX 4762 4,
.CX 4374 4,
.measureX 4374 [] [.CZ 4762 3,.CZ 4762 4373,.CZ 3 4373],
.CX 4762 3,
.CX 4373 3,
.measureX 4373 [] [.CZ 4762 2,.CZ 4762 4760,.CZ 2 4760],
.CX 4762 2,
.CX 4760 2,
.CX 4762 4758,
.X 4758,
.X 4762,
.X 2,
.CCX 2 4760 4373,
.X 2,
.X 3,
.CCX 3 4373 4374,
.X 3,
.X 4,
.CCX 4 4374 4375,
.X 4,
.X 5,
.CCX 5 4375 4376,
.X 5,
.X 6,
.CX 6 4505,
.CX 6 4376,
.CCX 4505 4376 4377,
.CX 6 4377,
.CX 6 4376,
.CX 6 4505,
.X 6,
.X 7,
.CX 7 4506,
.CX 7 4377,
.CCX 4506 4377 4378,
.CX 7 4378,
.CX 7 4377,
.CX 7 4506,
.X 7,
.X 8,
.CX 8 4507,
.CX 8 4378,
.CCX 4507 4378 4379,
.CX 8 4379,
.CX 8 4378,
.CX 8 4507,
.X 8,
.X 9,
.CX 9 4508,
.CX 9 4379,
.CCX 4508 4379 4380,
.CX 9 4380,
.CX 9 4379,
.CX 9 4508,
.X 9,
.X 10,
.CX 10 4509,
.CX 10 4380,
.CCX 4509 4380 4381,
.CX 10 4381,
.CX 10 4380,
.CX 10 4509,
.X 10,
.X 11
]
def block35:Program:=[
.CX 11 4510,
.CX 11 4381,
.CCX 4510 4381 4382,
.CX 11 4382,
.CX 11 4381,
.CX 11 4510,
.X 11,
.X 12,
.CX 12 4511,
.CX 12 4382,
.CCX 4511 4382 4383,
.CX 12 4383,
.CX 12 4382,
.CX 12 4511,
.X 12,
.X 13,
.CX 13 4512,
.CX 13 4383,
.CCX 4512 4383 4384,
.CX 13 4384,
.CX 13 4383,
.CX 13 4512,
.X 13,
.X 14,
.CX 14 4513,
.CX 14 4384,
.CCX 4513 4384 4385,
.CX 14 4385,
.CX 14 4384,
.CX 14 4513,
.X 14,
.X 15,
.CX 15 4514,
.CX 15 4385,
.CCX 4514 4385 4386,
.CX 15 4386,
.CX 15 4385,
.CX 15 4514,
.X 15,
.X 16,
.CX 16 4515,
.CX 16 4386,
.CCX 4515 4386 4387,
.CX 16 4387,
.CX 16 4386,
.CX 16 4515,
.X 16,
.X 17,
.CX 17 4516,
.CX 17 4387,
.CCX 4516 4387 4388,
.CX 17 4388,
.CX 17 4387,
.CX 17 4516,
.X 17,
.X 18,
.CX 18 4517,
.CX 18 4388,
.CCX 4517 4388 4389,
.CX 18 4389,
.CX 18 4388,
.CX 18 4517,
.X 18,
.X 19,
.CX 19 4518,
.CX 19 4389,
.CCX 4518 4389 4390,
.CX 19 4390,
.CX 19 4389,
.CX 19 4518,
.X 19,
.X 20,
.CX 20 4519,
.CX 20 4390,
.CCX 4519 4390 4391,
.CX 20 4391,
.CX 20 4390,
.CX 20 4519,
.X 20,
.X 21,
.CX 21 4520,
.CX 21 4391,
.CCX 4520 4391 4392,
.CX 21 4392,
.CX 21 4391,
.CX 21 4520,
.X 21,
.X 22,
.CX 22 4521,
.CX 22 4392,
.CCX 4521 4392 4393,
.CX 22 4393,
.CX 22 4392,
.CX 22 4521,
.X 22,
.X 23,
.CX 23 4522,
.CX 23 4393,
.CCX 4522 4393 4394,
.CX 23 4394,
.CX 23 4393,
.CX 23 4522,
.X 23,
.X 24,
.CX 24 4523,
.CX 24 4394,
.CCX 4523 4394 4395,
.CX 24 4395,
.CX 24 4394,
.CX 24 4523,
.X 24,
.X 25,
.CX 25 4524,
.CX 25 4395,
.CCX 4524 4395 4396,
.CX 25 4396,
.CX 25 4395,
.CX 25 4524,
.X 25,
.X 26,
.CX 26 4525,
.CX 26 4396,
.CCX 4525 4396 4397,
.CX 26 4397,
.CX 26 4396,
.CX 26 4525,
.X 26,
.X 27
]
def block36:Program:=[
.CX 27 4526,
.CX 27 4397,
.CCX 4526 4397 4398,
.CX 27 4398,
.CX 27 4397,
.CX 27 4526,
.X 27,
.X 28,
.CX 28 4527,
.CX 28 4398,
.CCX 4527 4398 4399,
.CX 28 4399,
.CX 28 4398,
.CX 28 4527,
.X 28,
.X 29,
.CX 29 4528,
.CX 29 4399,
.CCX 4528 4399 4400,
.CX 29 4400,
.CX 29 4399,
.CX 29 4528,
.X 29,
.X 30,
.CX 30 4529,
.CX 30 4400,
.CCX 4529 4400 4401,
.CX 30 4401,
.CX 30 4400,
.CX 30 4529,
.X 30,
.X 31,
.CX 31 4530,
.CX 31 4401,
.CCX 4530 4401 4402,
.CX 31 4402,
.CX 31 4401,
.CX 31 4530,
.X 31,
.X 32,
.CX 32 4531,
.CX 32 4402,
.CCX 4531 4402 4403,
.CX 32 4403,
.CX 32 4402,
.CX 32 4531,
.X 32,
.X 33,
.CX 33 4532,
.CX 33 4403,
.CCX 4532 4403 4404,
.CX 33 4404,
.CX 33 4403,
.CX 33 4532,
.X 33,
.X 34,
.CX 34 4533,
.CX 34 4404,
.CCX 4533 4404 4405,
.CX 34 4405,
.CX 34 4404,
.CX 34 4533,
.X 34,
.X 35,
.CX 35 4534,
.CX 35 4405,
.CCX 4534 4405 4406,
.CX 35 4406,
.CX 35 4405,
.CX 35 4534,
.X 35,
.X 36,
.CX 36 4535,
.CX 36 4406,
.CCX 4535 4406 4407,
.CX 36 4407,
.CX 36 4406,
.CX 36 4535,
.X 36,
.X 37,
.CX 37 4536,
.CX 37 4407,
.CCX 4536 4407 4408,
.CX 37 4408,
.CX 37 4407,
.CX 37 4536,
.X 37,
.X 38,
.CX 38 4537,
.CX 38 4408,
.CCX 4537 4408 4409,
.CX 38 4409,
.CX 38 4408,
.CX 38 4537,
.X 38,
.X 39,
.CX 39 4538,
.CX 39 4409,
.CCX 4538 4409 4410,
.CX 39 4410,
.CX 39 4409,
.CX 39 4538,
.X 39,
.X 40,
.CX 40 4539,
.CX 40 4410,
.CCX 4539 4410 4411,
.CX 40 4411,
.CX 40 4410,
.CX 40 4539,
.X 40,
.X 41,
.CX 41 4540,
.CX 41 4411,
.CCX 4540 4411 4412,
.CX 41 4412,
.CX 41 4411,
.CX 41 4540,
.X 41,
.X 42,
.CX 42 4541,
.CX 42 4412,
.CCX 4541 4412 4413,
.CX 42 4413,
.CX 42 4412,
.CX 42 4541,
.X 42,
.X 43
]
def block37:Program:=[
.CX 43 4542,
.CX 43 4413,
.CCX 4542 4413 4414,
.CX 43 4414,
.CX 43 4413,
.CX 43 4542,
.X 43,
.X 44,
.CX 44 4543,
.CX 44 4414,
.CCX 4543 4414 4415,
.CX 44 4415,
.CX 44 4414,
.CX 44 4543,
.X 44,
.X 45,
.CX 45 4544,
.CX 45 4415,
.CCX 4544 4415 4416,
.CX 45 4416,
.CX 45 4415,
.CX 45 4544,
.X 45,
.X 46,
.CX 46 4545,
.CX 46 4416,
.CCX 4545 4416 4417,
.CX 46 4417,
.CX 46 4416,
.CX 46 4545,
.X 46,
.X 47,
.CX 47 4546,
.CX 47 4417,
.CCX 4546 4417 4418,
.CX 47 4418,
.CX 47 4417,
.CX 47 4546,
.X 47,
.X 48,
.CX 48 4547,
.CX 48 4418,
.CCX 4547 4418 4419,
.CX 48 4419,
.CX 48 4418,
.CX 48 4547,
.X 48,
.X 49,
.CX 49 4548,
.CX 49 4419,
.CCX 4548 4419 4420,
.CX 49 4420,
.CX 49 4419,
.CX 49 4548,
.X 49,
.X 50,
.CX 50 4549,
.CX 50 4420,
.CCX 4549 4420 4421,
.CX 50 4421,
.CX 50 4420,
.CX 50 4549,
.X 50,
.X 51,
.CX 51 4550,
.CX 51 4421,
.CCX 4550 4421 4422,
.CX 51 4422,
.CX 51 4421,
.CX 51 4550,
.X 51,
.X 52,
.CX 52 4551,
.CX 52 4422,
.CCX 4551 4422 4423,
.CX 52 4423,
.CX 52 4422,
.CX 52 4551,
.X 52,
.X 53,
.CX 53 4552,
.CX 53 4423,
.CCX 4552 4423 4424,
.CX 53 4424,
.CX 53 4423,
.CX 53 4552,
.X 53,
.X 54,
.CX 54 4553,
.CX 54 4424,
.CCX 4553 4424 4425,
.CX 54 4425,
.CX 54 4424,
.CX 54 4553,
.X 54,
.X 55,
.CX 55 4554,
.CX 55 4425,
.CCX 4554 4425 4426,
.CX 55 4426,
.CX 55 4425,
.CX 55 4554,
.X 55,
.X 56,
.CX 56 4555,
.CX 56 4426,
.CCX 4555 4426 4427,
.CX 56 4427,
.CX 56 4426,
.CX 56 4555,
.X 56,
.X 57,
.CX 57 4556,
.CX 57 4427,
.CCX 4556 4427 4428,
.CX 57 4428,
.CX 57 4427,
.CX 57 4556,
.X 57,
.X 58,
.CX 58 4557,
.CX 58 4428,
.CCX 4557 4428 4429,
.CX 58 4429,
.CX 58 4428,
.CX 58 4557,
.X 58,
.X 59
]
def block38:Program:=[
.CX 59 4558,
.CX 59 4429,
.CCX 4558 4429 4430,
.CX 59 4430,
.CX 59 4429,
.CX 59 4558,
.X 59,
.X 60,
.CX 60 4559,
.CX 60 4430,
.CCX 4559 4430 4431,
.CX 60 4431,
.CX 60 4430,
.CX 60 4559,
.X 60,
.X 61,
.CX 61 4560,
.CX 61 4431,
.CCX 4560 4431 4432,
.CX 61 4432,
.CX 61 4431,
.CX 61 4560,
.X 61,
.X 62,
.CX 62 4561,
.CX 62 4432,
.CCX 4561 4432 4433,
.CX 62 4433,
.CX 62 4432,
.CX 62 4561,
.X 62,
.X 63,
.CX 63 4562,
.CX 63 4433,
.CCX 4562 4433 4434,
.CX 63 4434,
.CX 63 4433,
.CX 63 4562,
.X 63,
.X 64,
.CX 64 4563,
.CX 64 4434,
.CCX 4563 4434 4435,
.CX 64 4435,
.CX 64 4434,
.CX 64 4563,
.X 64,
.X 65,
.CX 65 4564,
.CX 65 4435,
.CCX 4564 4435 4436,
.CX 65 4436,
.CX 65 4435,
.CX 65 4564,
.X 65,
.X 66,
.CX 66 4565,
.CX 66 4436,
.CCX 4565 4436 4437,
.CX 66 4437,
.CX 66 4436,
.CX 66 4565,
.X 66,
.X 67,
.CX 67 4566,
.CX 67 4437,
.CCX 4566 4437 4438,
.CX 67 4438,
.CX 67 4437,
.CX 67 4566,
.X 67,
.X 68,
.CX 68 4567,
.CX 68 4438,
.CCX 4567 4438 4439,
.CX 68 4439,
.CX 68 4438,
.CX 68 4567,
.X 68,
.X 69,
.CX 69 4568,
.CX 69 4439,
.CCX 4568 4439 4440,
.CX 69 4440,
.CX 69 4439,
.CX 69 4568,
.X 69,
.X 70,
.CX 70 4569,
.CX 70 4440,
.CCX 4569 4440 4441,
.CX 70 4441,
.CX 70 4440,
.CX 70 4569,
.X 70,
.X 71,
.CX 71 4570,
.CX 71 4441,
.CCX 4570 4441 4442,
.CX 71 4442,
.CX 71 4441,
.CX 71 4570,
.X 71,
.X 72,
.CX 72 4571,
.CX 72 4442,
.CCX 4571 4442 4443,
.CX 72 4443,
.CX 72 4442,
.CX 72 4571,
.X 72,
.X 73,
.CX 73 4572,
.CX 73 4443,
.CCX 4572 4443 4444,
.CX 73 4444,
.CX 73 4443,
.CX 73 4572,
.X 73,
.X 74,
.CX 74 4573,
.CX 74 4444,
.CCX 4573 4444 4445,
.CX 74 4445,
.CX 74 4444,
.CX 74 4573,
.X 74,
.X 75
]
def block39:Program:=[
.CX 75 4574,
.CX 75 4445,
.CCX 4574 4445 4446,
.CX 75 4446,
.CX 75 4445,
.CX 75 4574,
.X 75,
.X 76,
.CX 76 4575,
.CX 76 4446,
.CCX 4575 4446 4447,
.CX 76 4447,
.CX 76 4446,
.CX 76 4575,
.X 76,
.X 77,
.CX 77 4576,
.CX 77 4447,
.CCX 4576 4447 4448,
.CX 77 4448,
.CX 77 4447,
.CX 77 4576,
.X 77,
.X 78,
.CX 78 4577,
.CX 78 4448,
.CCX 4577 4448 4449,
.CX 78 4449,
.CX 78 4448,
.CX 78 4577,
.X 78,
.X 79,
.CX 79 4578,
.CX 79 4449,
.CCX 4578 4449 4450,
.CX 79 4450,
.CX 79 4449,
.CX 79 4578,
.X 79,
.X 80,
.CX 80 4579,
.CX 80 4450,
.CCX 4579 4450 4451,
.CX 80 4451,
.CX 80 4450,
.CX 80 4579,
.X 80,
.X 81,
.CX 81 4580,
.CX 81 4451,
.CCX 4580 4451 4452,
.CX 81 4452,
.CX 81 4451,
.CX 81 4580,
.X 81,
.X 82,
.CX 82 4581,
.CX 82 4452,
.CCX 4581 4452 4453,
.CX 82 4453,
.CX 82 4452,
.CX 82 4581,
.X 82,
.X 83,
.CX 83 4582,
.CX 83 4453,
.CCX 4582 4453 4454,
.CX 83 4454,
.CX 83 4453,
.CX 83 4582,
.X 83,
.X 84,
.CX 84 4583,
.CX 84 4454,
.CCX 4583 4454 4455,
.CX 84 4455,
.CX 84 4454,
.CX 84 4583,
.X 84,
.X 85,
.CX 85 4584,
.CX 85 4455,
.CCX 4584 4455 4456,
.CX 85 4456,
.CX 85 4455,
.CX 85 4584,
.X 85,
.X 86,
.CX 86 4585,
.CX 86 4456,
.CCX 4585 4456 4457,
.CX 86 4457,
.CX 86 4456,
.CX 86 4585,
.X 86,
.X 87,
.CX 87 4586,
.CX 87 4457,
.CCX 4586 4457 4458,
.CX 87 4458,
.CX 87 4457,
.CX 87 4586,
.X 87,
.X 88,
.CX 88 4587,
.CX 88 4458,
.CCX 4587 4458 4459,
.CX 88 4459,
.CX 88 4458,
.CX 88 4587,
.X 88,
.X 89,
.CX 89 4588,
.CX 89 4459,
.CCX 4588 4459 4460,
.CX 89 4460,
.CX 89 4459,
.CX 89 4588,
.X 89,
.X 90,
.CX 90 4589,
.CX 90 4460,
.CCX 4589 4460 4461,
.CX 90 4461,
.CX 90 4460,
.CX 90 4589,
.X 90,
.X 91
]
def block40:Program:=[
.CX 91 4590,
.CX 91 4461,
.CCX 4590 4461 4462,
.CX 91 4462,
.CX 91 4461,
.CX 91 4590,
.X 91,
.X 92,
.CX 92 4591,
.CX 92 4462,
.CCX 4591 4462 4463,
.CX 92 4463,
.CX 92 4462,
.CX 92 4591,
.X 92,
.X 93,
.CX 93 4592,
.CX 93 4463,
.CCX 4592 4463 4464,
.CX 93 4464,
.CX 93 4463,
.CX 93 4592,
.X 93,
.X 94,
.CX 94 4593,
.CX 94 4464,
.CCX 4593 4464 4465,
.CX 94 4465,
.CX 94 4464,
.CX 94 4593,
.X 94,
.X 95,
.CX 95 4594,
.CX 95 4465,
.CCX 4594 4465 4466,
.CX 95 4466,
.CX 95 4465,
.CX 95 4594,
.X 95,
.X 96,
.CX 96 4595,
.CX 96 4466,
.CCX 4595 4466 4467,
.CX 96 4467,
.CX 96 4466,
.CX 96 4595,
.X 96,
.X 97,
.CX 97 4596,
.CX 97 4467,
.CCX 4596 4467 4468,
.CX 97 4468,
.CX 97 4467,
.CX 97 4596,
.X 97,
.X 98,
.CX 98 4597,
.CX 98 4468,
.CCX 4597 4468 4469,
.CX 98 4469,
.CX 98 4468,
.CX 98 4597,
.X 98,
.X 99,
.CX 99 4598,
.CX 99 4469,
.CCX 4598 4469 4470,
.CX 99 4470,
.CX 99 4469,
.CX 99 4598,
.X 99,
.X 100,
.CX 100 4599,
.CX 100 4470,
.CCX 4599 4470 4471,
.CX 100 4471,
.CX 100 4470,
.CX 100 4599,
.X 100,
.X 101,
.CX 101 4600,
.CX 101 4471,
.CCX 4600 4471 4472,
.CX 101 4472,
.CX 101 4471,
.CX 101 4600,
.X 101,
.X 102,
.CX 102 4601,
.CX 102 4472,
.CCX 4601 4472 4473,
.CX 102 4473,
.CX 102 4472,
.CX 102 4601,
.X 102,
.X 103,
.CX 103 4602,
.CX 103 4473,
.CCX 4602 4473 4474,
.CX 103 4474,
.CX 103 4473,
.CX 103 4602,
.X 103,
.X 104,
.CX 104 4603,
.CX 104 4474,
.CCX 4603 4474 4475,
.CX 104 4475,
.CX 104 4474,
.CX 104 4603,
.X 104,
.X 105,
.CX 105 4604,
.CX 105 4475,
.CCX 4604 4475 4476,
.CX 105 4476,
.CX 105 4475,
.CX 105 4604,
.X 105,
.X 106,
.CX 106 4605,
.CX 106 4476,
.CCX 4605 4476 4477,
.CX 106 4477,
.CX 106 4476,
.CX 106 4605,
.X 106,
.X 107
]
def block41:Program:=[
.CX 107 4606,
.CX 107 4477,
.CCX 4606 4477 4478,
.CX 107 4478,
.CX 107 4477,
.CX 107 4606,
.X 107,
.X 108,
.CX 108 4607,
.CX 108 4478,
.CCX 4607 4478 4479,
.CX 108 4479,
.CX 108 4478,
.CX 108 4607,
.X 108,
.X 109,
.CX 109 4608,
.CX 109 4479,
.CCX 4608 4479 4480,
.CX 109 4480,
.CX 109 4479,
.CX 109 4608,
.X 109,
.X 110,
.CX 110 4609,
.CX 110 4480,
.CCX 4609 4480 4481,
.CX 110 4481,
.CX 110 4480,
.CX 110 4609,
.X 110,
.X 111,
.CX 111 4610,
.CX 111 4481,
.CCX 4610 4481 4482,
.CX 111 4482,
.CX 111 4481,
.CX 111 4610,
.X 111,
.X 112,
.CX 112 4611,
.CX 112 4482,
.CCX 4611 4482 4483,
.CX 112 4483,
.CX 112 4482,
.CX 112 4611,
.X 112,
.X 113,
.CX 113 4612,
.CX 113 4483,
.CCX 4612 4483 4484,
.CX 113 4484,
.CX 113 4483,
.CX 113 4612,
.X 113,
.X 114,
.CX 114 4613,
.CX 114 4484,
.CCX 4613 4484 4485,
.CX 114 4485,
.CX 114 4484,
.CX 114 4613,
.X 114,
.X 115,
.CX 115 4614,
.CX 115 4485,
.CCX 4614 4485 4486,
.CX 115 4486,
.CX 115 4485,
.CX 115 4614,
.X 115,
.X 116,
.CX 116 4615,
.CX 116 4486,
.CCX 4615 4486 4487,
.CX 116 4487,
.CX 116 4486,
.CX 116 4615,
.X 116,
.X 117,
.CX 117 4616,
.CX 117 4487,
.CCX 4616 4487 4488,
.CX 117 4488,
.CX 117 4487,
.CX 117 4616,
.X 117,
.X 118,
.CX 118 4617,
.CX 118 4488,
.CCX 4617 4488 4489,
.CX 118 4489,
.CX 118 4488,
.CX 118 4617,
.X 118,
.X 119,
.CX 119 4618,
.CX 119 4489,
.CCX 4618 4489 4490,
.CX 119 4490,
.CX 119 4489,
.CX 119 4618,
.X 119,
.X 120,
.CX 120 4619,
.CX 120 4490,
.CCX 4619 4490 4491,
.CX 120 4491,
.CX 120 4490,
.CX 120 4619,
.X 120,
.X 121,
.CX 121 4620,
.CX 121 4491,
.CCX 4620 4491 4492,
.CX 121 4492,
.CX 121 4491,
.CX 121 4620,
.X 121,
.X 122,
.CX 122 4621,
.CX 122 4492,
.CCX 4621 4492 4493,
.CX 122 4493,
.CX 122 4492,
.CX 122 4621,
.X 122,
.X 123
]
def block42:Program:=[
.CX 123 4622,
.CX 123 4493,
.CCX 4622 4493 4494,
.CX 123 4494,
.CX 123 4493,
.CX 123 4622,
.X 123,
.X 124,
.CX 124 4623,
.CX 124 4494,
.CCX 4623 4494 4495,
.CX 124 4495,
.CX 124 4494,
.CX 124 4623,
.X 124,
.X 125,
.CX 125 4624,
.CX 125 4495,
.CCX 4624 4495 4496,
.CX 125 4496,
.CX 125 4495,
.CX 125 4624,
.X 125,
.X 126,
.CX 126 4625,
.CX 126 4496,
.CCX 4625 4496 4497,
.CX 126 4497,
.CX 126 4496,
.CX 126 4625,
.X 126,
.X 127,
.CX 127 4626,
.CX 127 4497,
.CCX 4626 4497 4498,
.CX 127 4498,
.CX 127 4497,
.CX 127 4626,
.X 127,
.X 128,
.CX 128 4627,
.CX 128 4498,
.CCX 4627 4498 4499,
.CX 128 4499,
.CX 128 4498,
.CX 128 4627,
.X 128,
.X 129,
.CX 129 4628,
.CX 129 4499,
.CCX 4628 4499 4500,
.CX 129 4500,
.CX 129 4499,
.CX 129 4628,
.X 129,
.X 130,
.CX 130 4629,
.CX 130 4500,
.CCX 4629 4500 4764,
.CX 130 4764,
.CX 130 4500,
.CX 130 4629,
.X 130,
.X 131,
.CX 131 4630,
.CX 131 4764,
.CCX 4630 4764 4765,
.CX 131 4765,
.CX 131 4764,
.CX 131 4630,
.X 131,
.X 132,
.CX 132 4631,
.CX 132 4765,
.CCX 4631 4765 4766,
.CX 132 4766,
.CX 132 4765,
.CX 132 4631,
.X 132,
.X 133,
.CX 133 4632,
.CX 133 4766,
.CCX 4632 4766 4767,
.CX 133 4767,
.CX 133 4766,
.CX 133 4632,
.X 133,
.X 134,
.CX 134 4633,
.CX 134 4767,
.CCX 4633 4767 4768,
.CX 134 4768,
.CX 134 4767,
.CX 134 4633,
.X 134,
.X 135,
.CX 135 4634,
.CX 135 4768,
.CCX 4634 4768 4769,
.CX 135 4769,
.CX 135 4768,
.CX 135 4634,
.X 135,
.X 136,
.CX 136 4635,
.CX 136 4769,
.CCX 4635 4769 4770,
.CX 136 4770,
.CX 136 4769,
.CX 136 4635,
.X 136,
.X 137,
.CX 137 4636,
.CX 137 4770,
.CCX 4636 4770 4771,
.CX 137 4771,
.CX 137 4770,
.CX 137 4636,
.X 137,
.X 138,
.CX 138 4637,
.CX 138 4771,
.CCX 4637 4771 4772,
.CX 138 4772,
.CX 138 4771,
.CX 138 4637,
.X 138,
.X 139
]
def block43:Program:=[
.CX 139 4638,
.CX 139 4772,
.CCX 4638 4772 4773,
.CX 139 4773,
.CX 139 4772,
.CX 139 4638,
.X 139,
.X 140,
.CX 140 4639,
.CX 140 4773,
.CCX 4639 4773 4774,
.CX 140 4774,
.CX 140 4773,
.CX 140 4639,
.X 140,
.X 141,
.CX 141 4640,
.CX 141 4774,
.CCX 4640 4774 4775,
.CX 141 4775,
.CX 141 4774,
.CX 141 4640,
.X 141,
.X 142,
.CX 142 4641,
.CX 142 4775,
.CCX 4641 4775 4776,
.CX 142 4776,
.CX 142 4775,
.CX 142 4641,
.X 142,
.X 143,
.CX 143 4642,
.CX 143 4776,
.CCX 4642 4776 4777,
.CX 143 4777,
.CX 143 4776,
.CX 143 4642,
.X 143,
.X 144,
.CX 144 4643,
.CX 144 4777,
.CCX 4643 4777 4778,
.CX 144 4778,
.CX 144 4777,
.CX 144 4643,
.X 144,
.X 145,
.CX 145 4644,
.CX 145 4778,
.CCX 4644 4778 4779,
.CX 145 4779,
.CX 145 4778,
.CX 145 4644,
.X 145,
.X 146,
.CX 146 4645,
.CX 146 4779,
.CCX 4645 4779 4780,
.CX 146 4780,
.CX 146 4779,
.CX 146 4645,
.X 146,
.X 147,
.CX 147 4646,
.CX 147 4780,
.CCX 4646 4780 4781,
.CX 147 4781,
.CX 147 4780,
.CX 147 4646,
.X 147,
.X 148,
.CX 148 4647,
.CX 148 4781,
.CCX 4647 4781 4782,
.CX 148 4782,
.CX 148 4781,
.CX 148 4647,
.X 148,
.X 149,
.CX 149 4648,
.CX 149 4782,
.CCX 4648 4782 4783,
.CX 149 4783,
.CX 149 4782,
.CX 149 4648,
.X 149,
.X 150,
.CX 150 4649,
.CX 150 4783,
.CCX 4649 4783 4784,
.CX 150 4784,
.CX 150 4783,
.CX 150 4649,
.X 150,
.X 151,
.CX 151 4650,
.CX 151 4784,
.CCX 4650 4784 4785,
.CX 151 4785,
.CX 151 4784,
.CX 151 4650,
.X 151,
.X 152,
.CX 152 4651,
.CX 152 4785,
.CCX 4651 4785 4786,
.CX 152 4786,
.CX 152 4785,
.CX 152 4651,
.X 152,
.X 153,
.CX 153 4652,
.CX 153 4786,
.CCX 4652 4786 4787,
.CX 153 4787,
.CX 153 4786,
.CX 153 4652,
.X 153,
.X 154,
.CX 154 4653,
.CX 154 4787,
.CCX 4653 4787 4788,
.CX 154 4788,
.CX 154 4787,
.CX 154 4653,
.X 154,
.X 155
]
def block44:Program:=[
.CX 155 4654,
.CX 155 4788,
.CCX 4654 4788 4789,
.CX 155 4789,
.CX 155 4788,
.CX 155 4654,
.X 155,
.X 156,
.CX 156 4655,
.CX 156 4789,
.CCX 4655 4789 4790,
.CX 156 4790,
.CX 156 4789,
.CX 156 4655,
.X 156,
.X 157,
.CX 157 4656,
.CX 157 4790,
.CCX 4656 4790 4791,
.CX 157 4791,
.CX 157 4790,
.CX 157 4656,
.X 157,
.X 158,
.CX 158 4657,
.CX 158 4791,
.CCX 4657 4791 4792,
.CX 158 4792,
.CX 158 4791,
.CX 158 4657,
.X 158,
.X 159,
.CX 159 4658,
.CX 159 4792,
.CCX 4658 4792 4793,
.CX 159 4793,
.CX 159 4792,
.CX 159 4658,
.X 159,
.X 160,
.CX 160 4659,
.CX 160 4793,
.CCX 4659 4793 4794,
.CX 160 4794,
.CX 160 4793,
.CX 160 4659,
.X 160,
.X 161,
.CX 161 4660,
.CX 161 4794,
.CCX 4660 4794 4795,
.CX 161 4795,
.CX 161 4794,
.CX 161 4660,
.X 161,
.X 162,
.CX 162 4661,
.CX 162 4795,
.CCX 4661 4795 4796,
.CX 162 4796,
.CX 162 4795,
.CX 162 4661,
.X 162,
.X 163,
.CCX 163 4796 4797,
.X 163,
.X 164,
.CCX 164 4797 4798,
.X 164,
.X 165,
.CCX 165 4798 4799,
.X 165,
.X 166,
.CCX 166 4799 4800,
.X 166,
.X 167,
.CCX 167 4800 4801,
.X 167,
.X 168,
.CCX 168 4801 4802,
.X 168,
.X 169,
.CCX 169 4802 4803,
.X 169,
.X 170,
.CCX 170 4803 4804,
.X 170,
.X 171,
.CCX 171 4804 4805,
.X 171,
.X 172,
.CCX 172 4805 4806,
.X 172,
.X 173,
.CCX 173 4806 4807,
.X 173,
.X 174,
.CCX 174 4807 4808,
.X 174,
.X 175,
.CCX 175 4808 4809,
.X 175,
.X 176,
.CCX 176 4809 4810,
.X 176,
.X 177,
.CCX 177 4810 4811,
.X 177,
.X 178,
.CCX 178 4811 4812,
.X 178,
.X 179,
.CCX 179 4812 4813,
.X 179,
.X 180,
.CCX 180 4813 4814,
.X 180,
.X 181,
.CCX 181 4814 4815,
.X 181,
.X 182,
.CCX 182 4815 4816,
.X 182,
.X 183,
.CCX 183 4816 4817,
.X 183,
.X 184,
.CCX 184 4817 4818
]
def block45:Program:=[
.X 184,
.X 185,
.CCX 185 4818 4819,
.X 185,
.X 186,
.CCX 186 4819 4820,
.X 186,
.X 187,
.CCX 187 4820 4821,
.X 187,
.X 188,
.CCX 188 4821 4822,
.X 188,
.X 189,
.CCX 189 4822 4823,
.X 189,
.X 190,
.CCX 190 4823 4824,
.X 190,
.X 191,
.CCX 191 4824 4825,
.X 191,
.X 192,
.CCX 192 4825 4826,
.X 192,
.X 193,
.CCX 193 4826 4827,
.X 193,
.X 194,
.CCX 194 4827 4828,
.X 194,
.X 195,
.CCX 195 4828 4829,
.X 195,
.X 196,
.CCX 196 4829 4830,
.X 196,
.X 197,
.CCX 197 4830 4831,
.X 197,
.X 198,
.CCX 198 4831 4832,
.X 198,
.X 199,
.CCX 199 4832 4833,
.X 199,
.X 200,
.CCX 200 4833 4834,
.X 200,
.X 201,
.CCX 201 4834 4835,
.X 201,
.X 202,
.CCX 202 4835 4836,
.X 202,
.X 203,
.CCX 203 4836 4837,
.X 203,
.X 204,
.CCX 204 4837 4838,
.X 204,
.X 205,
.CCX 205 4838 4839,
.X 205,
.X 206,
.CCX 206 4839 4840,
.X 206,
.X 207,
.CCX 207 4840 4841,
.X 207,
.X 208,
.CCX 208 4841 4842,
.X 208,
.X 209,
.CCX 209 4842 4843,
.X 209,
.X 210,
.CCX 210 4843 4844,
.X 210,
.X 211,
.CCX 211 4844 4845,
.X 211,
.X 212,
.CCX 212 4845 4846,
.X 212,
.X 213,
.CCX 213 4846 4847,
.X 213,
.X 214,
.CCX 214 4847 4848,
.X 214,
.X 215,
.CCX 215 4848 4849,
.X 215,
.X 216,
.CCX 216 4849 4850,
.X 216,
.X 217,
.CCX 217 4850 4851,
.X 217,
.X 218,
.CCX 218 4851 4852,
.X 218,
.X 219,
.CCX 219 4852 4853,
.X 219,
.X 220,
.CCX 220 4853 4854,
.X 220,
.X 221,
.CCX 221 4854 4855,
.X 221,
.X 222,
.CCX 222 4855 4856,
.X 222,
.X 223,
.CCX 223 4856 4857,
.X 223,
.X 224,
.CCX 224 4857 4858,
.X 224,
.X 225,
.CCX 225 4858 4859,
.X 225,
.X 226,
.CCX 226 4859 4860,
.X 226,
.X 227
]
def block46:Program:=[
.CCX 227 4860 4861,
.X 227,
.X 228,
.CCX 228 4861 4862,
.X 228,
.X 229,
.CCX 229 4862 4863,
.X 229,
.X 230,
.CCX 230 4863 4864,
.X 230,
.X 231,
.CCX 231 4864 4865,
.X 231,
.X 232,
.CCX 232 4865 4866,
.X 232,
.X 233,
.CCX 233 4866 4867,
.X 233,
.X 234,
.CCX 234 4867 4868,
.X 234,
.X 235,
.CCX 235 4868 4869,
.X 235,
.X 236,
.CCX 236 4869 4870,
.X 236,
.X 237,
.CCX 237 4870 4871,
.X 237,
.X 238,
.CCX 238 4871 4872,
.X 238,
.X 239,
.CCX 239 4872 4873,
.X 239,
.X 240,
.CCX 240 4873 4874,
.X 240,
.X 241,
.CCX 241 4874 4875,
.X 241,
.X 242,
.CCX 242 4875 4876,
.X 242,
.X 243,
.CCX 243 4876 4877,
.X 243,
.X 244,
.CCX 244 4877 4878,
.X 244,
.X 245,
.CCX 245 4878 4879,
.X 245,
.X 246,
.CCX 246 4879 4880,
.X 246,
.X 247,
.CCX 247 4880 4881,
.X 247,
.X 248,
.CCX 248 4881 4882,
.X 248,
.X 249,
.CCX 249 4882 4883,
.X 249,
.X 250,
.CCX 250 4883 4884,
.X 250,
.X 251,
.CCX 251 4884 4885,
.X 251,
.X 252,
.CCX 252 4885 4886,
.X 252,
.X 253,
.CCX 253 4886 4887,
.X 253,
.X 254,
.CCX 254 4887 4888,
.X 254,
.X 255,
.CCX 255 4888 4889,
.X 255,
.X 256,
.CCX 256 4889 4757,
.X 256,
.X 257,
.measureX 4762 [] [.CZ 257 4757],
.X 257,
.X 256,
.measureX 4757 [] [.CZ 256 4889],
.X 256,
.X 255,
.measureX 4889 [] [.CZ 255 4888],
.X 255,
.X 254,
.measureX 4888 [] [.CZ 254 4887],
.X 254,
.X 253,
.measureX 4887 [] [.CZ 253 4886],
.X 253,
.X 252,
.measureX 4886 [] [.CZ 252 4885],
.X 252,
.X 251,
.measureX 4885 [] [.CZ 251 4884],
.X 251,
.X 250,
.measureX 4884 [] [.CZ 250 4883],
.X 250,
.X 249,
.measureX 4883 [] [.CZ 249 4882],
.X 249,
.X 248,
.measureX 4882 [] [.CZ 248 4881],
.X 248,
.X 247,
.measureX 4881 [] [.CZ 247 4880],
.X 247,
.X 246,
.measureX 4880 [] [.CZ 246 4879],
.X 246,
.X 245,
.measureX 4879 [] [.CZ 245 4878],
.X 245
]
def block47:Program:=[
.X 244,
.measureX 4878 [] [.CZ 244 4877],
.X 244,
.X 243,
.measureX 4877 [] [.CZ 243 4876],
.X 243,
.X 242,
.measureX 4876 [] [.CZ 242 4875],
.X 242,
.X 241,
.measureX 4875 [] [.CZ 241 4874],
.X 241,
.X 240,
.measureX 4874 [] [.CZ 240 4873],
.X 240,
.X 239,
.measureX 4873 [] [.CZ 239 4872],
.X 239,
.X 238,
.measureX 4872 [] [.CZ 238 4871],
.X 238,
.X 237,
.measureX 4871 [] [.CZ 237 4870],
.X 237,
.X 236,
.measureX 4870 [] [.CZ 236 4869],
.X 236,
.X 235,
.measureX 4869 [] [.CZ 235 4868],
.X 235,
.X 234,
.measureX 4868 [] [.CZ 234 4867],
.X 234,
.X 233,
.measureX 4867 [] [.CZ 233 4866],
.X 233,
.X 232,
.measureX 4866 [] [.CZ 232 4865],
.X 232,
.X 231,
.measureX 4865 [] [.CZ 231 4864],
.X 231,
.X 230,
.measureX 4864 [] [.CZ 230 4863],
.X 230,
.X 229,
.measureX 4863 [] [.CZ 229 4862],
.X 229,
.X 228,
.measureX 4862 [] [.CZ 228 4861],
.X 228,
.X 227,
.measureX 4861 [] [.CZ 227 4860],
.X 227,
.X 226,
.measureX 4860 [] [.CZ 226 4859],
.X 226,
.X 225,
.measureX 4859 [] [.CZ 225 4858],
.X 225,
.X 224,
.measureX 4858 [] [.CZ 224 4857],
.X 224,
.X 223,
.measureX 4857 [] [.CZ 223 4856],
.X 223,
.X 222,
.measureX 4856 [] [.CZ 222 4855],
.X 222,
.X 221,
.measureX 4855 [] [.CZ 221 4854],
.X 221,
.X 220,
.measureX 4854 [] [.CZ 220 4853],
.X 220,
.X 219,
.measureX 4853 [] [.CZ 219 4852],
.X 219,
.X 218,
.measureX 4852 [] [.CZ 218 4851],
.X 218,
.X 217,
.measureX 4851 [] [.CZ 217 4850],
.X 217,
.X 216,
.measureX 4850 [] [.CZ 216 4849],
.X 216,
.X 215,
.measureX 4849 [] [.CZ 215 4848],
.X 215,
.X 214,
.measureX 4848 [] [.CZ 214 4847],
.X 214,
.X 213,
.measureX 4847 [] [.CZ 213 4846],
.X 213,
.X 212,
.measureX 4846 [] [.CZ 212 4845],
.X 212,
.X 211,
.measureX 4845 [] [.CZ 211 4844],
.X 211,
.X 210,
.measureX 4844 [] [.CZ 210 4843],
.X 210,
.X 209,
.measureX 4843 [] [.CZ 209 4842],
.X 209,
.X 208,
.measureX 4842 [] [.CZ 208 4841],
.X 208,
.X 207,
.measureX 4841 [] [.CZ 207 4840],
.X 207,
.X 206,
.measureX 4840 [] [.CZ 206 4839],
.X 206,
.X 205,
.measureX 4839 [] [.CZ 205 4838],
.X 205,
.X 204,
.measureX 4838 [] [.CZ 204 4837],
.X 204,
.X 203,
.measureX 4837 [] [.CZ 203 4836],
.X 203,
.X 202,
.measureX 4836 [] [.CZ 202 4835]
]
def block48:Program:=[
.X 202,
.X 201,
.measureX 4835 [] [.CZ 201 4834],
.X 201,
.X 200,
.measureX 4834 [] [.CZ 200 4833],
.X 200,
.X 199,
.measureX 4833 [] [.CZ 199 4832],
.X 199,
.X 198,
.measureX 4832 [] [.CZ 198 4831],
.X 198,
.X 197,
.measureX 4831 [] [.CZ 197 4830],
.X 197,
.X 196,
.measureX 4830 [] [.CZ 196 4829],
.X 196,
.X 195,
.measureX 4829 [] [.CZ 195 4828],
.X 195,
.X 194,
.measureX 4828 [] [.CZ 194 4827],
.X 194,
.X 193,
.measureX 4827 [] [.CZ 193 4826],
.X 193,
.X 192,
.measureX 4826 [] [.CZ 192 4825],
.X 192,
.X 191,
.measureX 4825 [] [.CZ 191 4824],
.X 191,
.X 190,
.measureX 4824 [] [.CZ 190 4823],
.X 190,
.X 189,
.measureX 4823 [] [.CZ 189 4822],
.X 189,
.X 188,
.measureX 4822 [] [.CZ 188 4821],
.X 188,
.X 187,
.measureX 4821 [] [.CZ 187 4820],
.X 187,
.X 186,
.measureX 4820 [] [.CZ 186 4819],
.X 186,
.X 185,
.measureX 4819 [] [.CZ 185 4818],
.X 185,
.X 184,
.measureX 4818 [] [.CZ 184 4817],
.X 184,
.X 183,
.measureX 4817 [] [.CZ 183 4816],
.X 183,
.X 182,
.measureX 4816 [] [.CZ 182 4815],
.X 182,
.X 181,
.measureX 4815 [] [.CZ 181 4814],
.X 181,
.X 180,
.measureX 4814 [] [.CZ 180 4813],
.X 180,
.X 179,
.measureX 4813 [] [.CZ 179 4812],
.X 179,
.X 178,
.measureX 4812 [] [.CZ 178 4811],
.X 178,
.X 177,
.measureX 4811 [] [.CZ 177 4810],
.X 177,
.X 176,
.measureX 4810 [] [.CZ 176 4809],
.X 176,
.X 175,
.measureX 4809 [] [.CZ 175 4808],
.X 175,
.X 174,
.measureX 4808 [] [.CZ 174 4807],
.X 174,
.X 173,
.measureX 4807 [] [.CZ 173 4806],
.X 173,
.X 172,
.measureX 4806 [] [.CZ 172 4805],
.X 172,
.X 171,
.measureX 4805 [] [.CZ 171 4804],
.X 171,
.X 170,
.measureX 4804 [] [.CZ 170 4803],
.X 170,
.X 169,
.measureX 4803 [] [.CZ 169 4802],
.X 169,
.X 168,
.measureX 4802 [] [.CZ 168 4801],
.X 168,
.X 167,
.measureX 4801 [] [.CZ 167 4800],
.X 167,
.X 166,
.measureX 4800 [] [.CZ 166 4799],
.X 166,
.X 165,
.measureX 4799 [] [.CZ 165 4798],
.X 165,
.X 164,
.measureX 4798 [] [.CZ 164 4797],
.X 164,
.X 163,
.measureX 4797 [] [.CZ 163 4796],
.X 163,
.X 162,
.measureX 4796 [] [.CZ 162 4661,.CZ 162 4795,.CZ 4661 4795],
.X 162,
.X 161,
.measureX 4795 [] [.CZ 161 4660,.CZ 161 4794,.CZ 4660 4794],
.X 161,
.X 160,
.measureX 4794 [] [.CZ 160 4659,.CZ 160 4793,.CZ 4659 4793],
.X 160,
.X 159
]
def block49:Program:=[
.measureX 4793 [] [.CZ 159 4658,.CZ 159 4792,.CZ 4658 4792],
.X 159,
.X 158,
.measureX 4792 [] [.CZ 158 4657,.CZ 158 4791,.CZ 4657 4791],
.X 158,
.X 157,
.measureX 4791 [] [.CZ 157 4656,.CZ 157 4790,.CZ 4656 4790],
.X 157,
.X 156,
.measureX 4790 [] [.CZ 156 4655,.CZ 156 4789,.CZ 4655 4789],
.X 156,
.X 155,
.measureX 4789 [] [.CZ 155 4654,.CZ 155 4788,.CZ 4654 4788],
.X 155,
.X 154,
.measureX 4788 [] [.CZ 154 4653,.CZ 154 4787,.CZ 4653 4787],
.X 154,
.X 153,
.measureX 4787 [] [.CZ 153 4652,.CZ 153 4786,.CZ 4652 4786],
.X 153,
.X 152,
.measureX 4786 [] [.CZ 152 4651,.CZ 152 4785,.CZ 4651 4785],
.X 152,
.X 151,
.measureX 4785 [] [.CZ 151 4650,.CZ 151 4784,.CZ 4650 4784],
.X 151,
.X 150,
.measureX 4784 [] [.CZ 150 4649,.CZ 150 4783,.CZ 4649 4783],
.X 150,
.X 149,
.measureX 4783 [] [.CZ 149 4648,.CZ 149 4782,.CZ 4648 4782],
.X 149,
.X 148,
.measureX 4782 [] [.CZ 148 4647,.CZ 148 4781,.CZ 4647 4781],
.X 148,
.X 147,
.measureX 4781 [] [.CZ 147 4646,.CZ 147 4780,.CZ 4646 4780],
.X 147,
.X 146,
.measureX 4780 [] [.CZ 146 4645,.CZ 146 4779,.CZ 4645 4779],
.X 146,
.X 145,
.measureX 4779 [] [.CZ 145 4644,.CZ 145 4778,.CZ 4644 4778],
.X 145,
.X 144,
.measureX 4778 [] [.CZ 144 4643,.CZ 144 4777,.CZ 4643 4777],
.X 144,
.X 143,
.measureX 4777 [] [.CZ 143 4642,.CZ 143 4776,.CZ 4642 4776],
.X 143,
.X 142,
.measureX 4776 [] [.CZ 142 4641,.CZ 142 4775,.CZ 4641 4775],
.X 142,
.X 141,
.measureX 4775 [] [.CZ 141 4640,.CZ 141 4774,.CZ 4640 4774],
.X 141,
.X 140,
.measureX 4774 [] [.CZ 140 4639,.CZ 140 4773,.CZ 4639 4773],
.X 140,
.X 139,
.measureX 4773 [] [.CZ 139 4638,.CZ 139 4772,.CZ 4638 4772],
.X 139,
.X 138,
.measureX 4772 [] [.CZ 138 4637,.CZ 138 4771,.CZ 4637 4771],
.X 138,
.X 137,
.measureX 4771 [] [.CZ 137 4636,.CZ 137 4770,.CZ 4636 4770],
.X 137,
.X 136,
.measureX 4770 [] [.CZ 136 4635,.CZ 136 4769,.CZ 4635 4769],
.X 136,
.X 135,
.measureX 4769 [] [.CZ 135 4634,.CZ 135 4768,.CZ 4634 4768],
.X 135,
.X 134,
.measureX 4768 [] [.CZ 134 4633,.CZ 134 4767,.CZ 4633 4767],
.X 134,
.X 133,
.measureX 4767 [] [.CZ 133 4632,.CZ 133 4766,.CZ 4632 4766],
.X 133,
.X 132,
.measureX 4766 [] [.CZ 132 4631,.CZ 132 4765,.CZ 4631 4765],
.X 132,
.X 131,
.measureX 4765 [] [.CZ 131 4630,.CZ 131 4764,.CZ 4630 4764],
.X 131,
.X 130,
.measureX 4764 [] [.CZ 130 4629,.CZ 130 4500,.CZ 4629 4500],
.X 130,
.X 129,
.measureX 4500 [] [.CZ 129 4628,.CZ 129 4499,.CZ 4628 4499],
.X 129,
.X 128,
.measureX 4499 [] [.CZ 128 4627,.CZ 128 4498,.CZ 4627 4498],
.X 128,
.X 127,
.measureX 4498 [] [.CZ 127 4626,.CZ 127 4497,.CZ 4626 4497],
.X 127,
.X 126,
.measureX 4497 [] [.CZ 126 4625,.CZ 126 4496,.CZ 4625 4496],
.X 126,
.X 125,
.measureX 4496 [] [.CZ 125 4624,.CZ 125 4495,.CZ 4624 4495],
.X 125,
.X 124,
.measureX 4495 [] [.CZ 124 4623,.CZ 124 4494,.CZ 4623 4494],
.X 124,
.X 123,
.measureX 4494 [] [.CZ 123 4622,.CZ 123 4493,.CZ 4622 4493],
.X 123,
.X 122,
.measureX 4493 [] [.CZ 122 4621,.CZ 122 4492,.CZ 4621 4492],
.X 122,
.X 121,
.measureX 4492 [] [.CZ 121 4620,.CZ 121 4491,.CZ 4620 4491],
.X 121,
.X 120,
.measureX 4491 [] [.CZ 120 4619,.CZ 120 4490,.CZ 4619 4490],
.X 120,
.X 119,
.measureX 4490 [] [.CZ 119 4618,.CZ 119 4489,.CZ 4618 4489],
.X 119,
.X 118,
.measureX 4489 [] [.CZ 118 4617,.CZ 118 4488,.CZ 4617 4488],
.X 118,
.X 117,
.measureX 4488 [] [.CZ 117 4616,.CZ 117 4487,.CZ 4616 4487],
.X 117
]
def block50:Program:=[
.X 116,
.measureX 4487 [] [.CZ 116 4615,.CZ 116 4486,.CZ 4615 4486],
.X 116,
.X 115,
.measureX 4486 [] [.CZ 115 4614,.CZ 115 4485,.CZ 4614 4485],
.X 115,
.X 114,
.measureX 4485 [] [.CZ 114 4613,.CZ 114 4484,.CZ 4613 4484],
.X 114,
.X 113,
.measureX 4484 [] [.CZ 113 4612,.CZ 113 4483,.CZ 4612 4483],
.X 113,
.X 112,
.measureX 4483 [] [.CZ 112 4611,.CZ 112 4482,.CZ 4611 4482],
.X 112,
.X 111,
.measureX 4482 [] [.CZ 111 4610,.CZ 111 4481,.CZ 4610 4481],
.X 111,
.X 110,
.measureX 4481 [] [.CZ 110 4609,.CZ 110 4480,.CZ 4609 4480],
.X 110,
.X 109,
.measureX 4480 [] [.CZ 109 4608,.CZ 109 4479,.CZ 4608 4479],
.X 109,
.X 108,
.measureX 4479 [] [.CZ 108 4607,.CZ 108 4478,.CZ 4607 4478],
.X 108,
.X 107,
.measureX 4478 [] [.CZ 107 4606,.CZ 107 4477,.CZ 4606 4477],
.X 107,
.X 106,
.measureX 4477 [] [.CZ 106 4605,.CZ 106 4476,.CZ 4605 4476],
.X 106,
.X 105,
.measureX 4476 [] [.CZ 105 4604,.CZ 105 4475,.CZ 4604 4475],
.X 105,
.X 104,
.measureX 4475 [] [.CZ 104 4603,.CZ 104 4474,.CZ 4603 4474],
.X 104,
.X 103,
.measureX 4474 [] [.CZ 103 4602,.CZ 103 4473,.CZ 4602 4473],
.X 103,
.X 102,
.measureX 4473 [] [.CZ 102 4601,.CZ 102 4472,.CZ 4601 4472],
.X 102,
.X 101,
.measureX 4472 [] [.CZ 101 4600,.CZ 101 4471,.CZ 4600 4471],
.X 101,
.X 100,
.measureX 4471 [] [.CZ 100 4599,.CZ 100 4470,.CZ 4599 4470],
.X 100,
.X 99,
.measureX 4470 [] [.CZ 99 4598,.CZ 99 4469,.CZ 4598 4469],
.X 99,
.X 98,
.measureX 4469 [] [.CZ 98 4597,.CZ 98 4468,.CZ 4597 4468],
.X 98,
.X 97,
.measureX 4468 [] [.CZ 97 4596,.CZ 97 4467,.CZ 4596 4467],
.X 97,
.X 96,
.measureX 4467 [] [.CZ 96 4595,.CZ 96 4466,.CZ 4595 4466],
.X 96,
.X 95,
.measureX 4466 [] [.CZ 95 4594,.CZ 95 4465,.CZ 4594 4465],
.X 95,
.X 94,
.measureX 4465 [] [.CZ 94 4593,.CZ 94 4464,.CZ 4593 4464],
.X 94,
.X 93,
.measureX 4464 [] [.CZ 93 4592,.CZ 93 4463,.CZ 4592 4463],
.X 93,
.X 92,
.measureX 4463 [] [.CZ 92 4591,.CZ 92 4462,.CZ 4591 4462],
.X 92,
.X 91,
.measureX 4462 [] [.CZ 91 4590,.CZ 91 4461,.CZ 4590 4461],
.X 91,
.X 90,
.measureX 4461 [] [.CZ 90 4589,.CZ 90 4460,.CZ 4589 4460],
.X 90,
.X 89,
.measureX 4460 [] [.CZ 89 4588,.CZ 89 4459,.CZ 4588 4459],
.X 89,
.X 88,
.measureX 4459 [] [.CZ 88 4587,.CZ 88 4458,.CZ 4587 4458],
.X 88,
.X 87,
.measureX 4458 [] [.CZ 87 4586,.CZ 87 4457,.CZ 4586 4457],
.X 87,
.X 86,
.measureX 4457 [] [.CZ 86 4585,.CZ 86 4456,.CZ 4585 4456],
.X 86,
.X 85,
.measureX 4456 [] [.CZ 85 4584,.CZ 85 4455,.CZ 4584 4455],
.X 85,
.X 84,
.measureX 4455 [] [.CZ 84 4583,.CZ 84 4454,.CZ 4583 4454],
.X 84,
.X 83,
.measureX 4454 [] [.CZ 83 4582,.CZ 83 4453,.CZ 4582 4453],
.X 83,
.X 82,
.measureX 4453 [] [.CZ 82 4581,.CZ 82 4452,.CZ 4581 4452],
.X 82,
.X 81,
.measureX 4452 [] [.CZ 81 4580,.CZ 81 4451,.CZ 4580 4451],
.X 81,
.X 80,
.measureX 4451 [] [.CZ 80 4579,.CZ 80 4450,.CZ 4579 4450],
.X 80,
.X 79,
.measureX 4450 [] [.CZ 79 4578,.CZ 79 4449,.CZ 4578 4449],
.X 79,
.X 78,
.measureX 4449 [] [.CZ 78 4577,.CZ 78 4448,.CZ 4577 4448],
.X 78,
.X 77,
.measureX 4448 [] [.CZ 77 4576,.CZ 77 4447,.CZ 4576 4447],
.X 77,
.X 76,
.measureX 4447 [] [.CZ 76 4575,.CZ 76 4446,.CZ 4575 4446],
.X 76,
.X 75,
.measureX 4446 [] [.CZ 75 4574,.CZ 75 4445,.CZ 4574 4445],
.X 75,
.X 74,
.measureX 4445 [] [.CZ 74 4573,.CZ 74 4444,.CZ 4573 4444]
]
def block51:Program:=[
.X 74,
.X 73,
.measureX 4444 [] [.CZ 73 4572,.CZ 73 4443,.CZ 4572 4443],
.X 73,
.X 72,
.measureX 4443 [] [.CZ 72 4571,.CZ 72 4442,.CZ 4571 4442],
.X 72,
.X 71,
.measureX 4442 [] [.CZ 71 4570,.CZ 71 4441,.CZ 4570 4441],
.X 71,
.X 70,
.measureX 4441 [] [.CZ 70 4569,.CZ 70 4440,.CZ 4569 4440],
.X 70,
.X 69,
.measureX 4440 [] [.CZ 69 4568,.CZ 69 4439,.CZ 4568 4439],
.X 69,
.X 68,
.measureX 4439 [] [.CZ 68 4567,.CZ 68 4438,.CZ 4567 4438],
.X 68,
.X 67,
.measureX 4438 [] [.CZ 67 4566,.CZ 67 4437,.CZ 4566 4437],
.X 67,
.X 66,
.measureX 4437 [] [.CZ 66 4565,.CZ 66 4436,.CZ 4565 4436],
.X 66,
.X 65,
.measureX 4436 [] [.CZ 65 4564,.CZ 65 4435,.CZ 4564 4435],
.X 65,
.X 64,
.measureX 4435 [] [.CZ 64 4563,.CZ 64 4434,.CZ 4563 4434],
.X 64,
.X 63,
.measureX 4434 [] [.CZ 63 4562,.CZ 63 4433,.CZ 4562 4433],
.X 63,
.X 62,
.measureX 4433 [] [.CZ 62 4561,.CZ 62 4432,.CZ 4561 4432],
.X 62,
.X 61,
.measureX 4432 [] [.CZ 61 4560,.CZ 61 4431,.CZ 4560 4431],
.X 61,
.X 60,
.measureX 4431 [] [.CZ 60 4559,.CZ 60 4430,.CZ 4559 4430],
.X 60,
.X 59,
.measureX 4430 [] [.CZ 59 4558,.CZ 59 4429,.CZ 4558 4429],
.X 59,
.X 58,
.measureX 4429 [] [.CZ 58 4557,.CZ 58 4428,.CZ 4557 4428],
.X 58,
.X 57,
.measureX 4428 [] [.CZ 57 4556,.CZ 57 4427,.CZ 4556 4427],
.X 57,
.X 56,
.measureX 4427 [] [.CZ 56 4555,.CZ 56 4426,.CZ 4555 4426],
.X 56,
.X 55,
.measureX 4426 [] [.CZ 55 4554,.CZ 55 4425,.CZ 4554 4425],
.X 55,
.X 54,
.measureX 4425 [] [.CZ 54 4553,.CZ 54 4424,.CZ 4553 4424],
.X 54,
.X 53,
.measureX 4424 [] [.CZ 53 4552,.CZ 53 4423,.CZ 4552 4423],
.X 53,
.X 52,
.measureX 4423 [] [.CZ 52 4551,.CZ 52 4422,.CZ 4551 4422],
.X 52,
.X 51,
.measureX 4422 [] [.CZ 51 4550,.CZ 51 4421,.CZ 4550 4421],
.X 51,
.X 50,
.measureX 4421 [] [.CZ 50 4549,.CZ 50 4420,.CZ 4549 4420],
.X 50,
.X 49,
.measureX 4420 [] [.CZ 49 4548,.CZ 49 4419,.CZ 4548 4419],
.X 49,
.X 48,
.measureX 4419 [] [.CZ 48 4547,.CZ 48 4418,.CZ 4547 4418],
.X 48,
.X 47,
.measureX 4418 [] [.CZ 47 4546,.CZ 47 4417,.CZ 4546 4417],
.X 47,
.X 46,
.measureX 4417 [] [.CZ 46 4545,.CZ 46 4416,.CZ 4545 4416],
.X 46,
.X 45,
.measureX 4416 [] [.CZ 45 4544,.CZ 45 4415,.CZ 4544 4415],
.X 45,
.X 44,
.measureX 4415 [] [.CZ 44 4543,.CZ 44 4414,.CZ 4543 4414],
.X 44,
.X 43,
.measureX 4414 [] [.CZ 43 4542,.CZ 43 4413,.CZ 4542 4413],
.X 43,
.X 42,
.measureX 4413 [] [.CZ 42 4541,.CZ 42 4412,.CZ 4541 4412],
.X 42,
.X 41,
.measureX 4412 [] [.CZ 41 4540,.CZ 41 4411,.CZ 4540 4411],
.X 41,
.X 40,
.measureX 4411 [] [.CZ 40 4539,.CZ 40 4410,.CZ 4539 4410],
.X 40,
.X 39,
.measureX 4410 [] [.CZ 39 4538,.CZ 39 4409,.CZ 4538 4409],
.X 39,
.X 38,
.measureX 4409 [] [.CZ 38 4537,.CZ 38 4408,.CZ 4537 4408],
.X 38,
.X 37,
.measureX 4408 [] [.CZ 37 4536,.CZ 37 4407,.CZ 4536 4407],
.X 37,
.X 36,
.measureX 4407 [] [.CZ 36 4535,.CZ 36 4406,.CZ 4535 4406],
.X 36,
.X 35,
.measureX 4406 [] [.CZ 35 4534,.CZ 35 4405,.CZ 4534 4405],
.X 35,
.X 34,
.measureX 4405 [] [.CZ 34 4533,.CZ 34 4404,.CZ 4533 4404],
.X 34,
.X 33,
.measureX 4404 [] [.CZ 33 4532,.CZ 33 4403,.CZ 4532 4403],
.X 33,
.X 32,
.measureX 4403 [] [.CZ 32 4531,.CZ 32 4402,.CZ 4531 4402],
.X 32,
.X 31
]
def block52:Program:=[
.measureX 4402 [] [.CZ 31 4530,.CZ 31 4401,.CZ 4530 4401],
.X 31,
.X 30,
.measureX 4401 [] [.CZ 30 4529,.CZ 30 4400,.CZ 4529 4400],
.X 30,
.X 29,
.measureX 4400 [] [.CZ 29 4528,.CZ 29 4399,.CZ 4528 4399],
.X 29,
.X 28,
.measureX 4399 [] [.CZ 28 4527,.CZ 28 4398,.CZ 4527 4398],
.X 28,
.X 27,
.measureX 4398 [] [.CZ 27 4526,.CZ 27 4397,.CZ 4526 4397],
.X 27,
.X 26,
.measureX 4397 [] [.CZ 26 4525,.CZ 26 4396,.CZ 4525 4396],
.X 26,
.X 25,
.measureX 4396 [] [.CZ 25 4524,.CZ 25 4395,.CZ 4524 4395],
.X 25,
.X 24,
.measureX 4395 [] [.CZ 24 4523,.CZ 24 4394,.CZ 4523 4394],
.X 24,
.X 23,
.measureX 4394 [] [.CZ 23 4522,.CZ 23 4393,.CZ 4522 4393],
.X 23,
.X 22,
.measureX 4393 [] [.CZ 22 4521,.CZ 22 4392,.CZ 4521 4392],
.X 22,
.X 21,
.measureX 4392 [] [.CZ 21 4520,.CZ 21 4391,.CZ 4520 4391],
.X 21,
.X 20,
.measureX 4391 [] [.CZ 20 4519,.CZ 20 4390,.CZ 4519 4390],
.X 20,
.X 19,
.measureX 4390 [] [.CZ 19 4518,.CZ 19 4389,.CZ 4518 4389],
.X 19,
.X 18,
.measureX 4389 [] [.CZ 18 4517,.CZ 18 4388,.CZ 4517 4388],
.X 18,
.X 17,
.measureX 4388 [] [.CZ 17 4516,.CZ 17 4387,.CZ 4516 4387],
.X 17,
.X 16,
.measureX 4387 [] [.CZ 16 4515,.CZ 16 4386,.CZ 4515 4386],
.X 16,
.X 15,
.measureX 4386 [] [.CZ 15 4514,.CZ 15 4385,.CZ 4514 4385],
.X 15,
.X 14,
.measureX 4385 [] [.CZ 14 4513,.CZ 14 4384,.CZ 4513 4384],
.X 14,
.X 13,
.measureX 4384 [] [.CZ 13 4512,.CZ 13 4383,.CZ 4512 4383],
.X 13,
.X 12,
.measureX 4383 [] [.CZ 12 4511,.CZ 12 4382,.CZ 4511 4382],
.X 12,
.X 11,
.measureX 4382 [] [.CZ 11 4510,.CZ 11 4381,.CZ 4510 4381],
.X 11,
.X 10,
.measureX 4381 [] [.CZ 10 4509,.CZ 10 4380,.CZ 4509 4380],
.X 10,
.X 9,
.measureX 4380 [] [.CZ 9 4508,.CZ 9 4379,.CZ 4508 4379],
.X 9,
.X 8,
.measureX 4379 [] [.CZ 8 4507,.CZ 8 4378,.CZ 4507 4378],
.X 8,
.X 7,
.measureX 4378 [] [.CZ 7 4506,.CZ 7 4377,.CZ 4506 4377],
.X 7,
.X 6,
.measureX 4377 [] [.CZ 6 4505,.CZ 6 4376,.CZ 4505 4376],
.X 6,
.X 5,
.measureX 4376 [] [.CZ 5 4375],
.X 5,
.X 4,
.measureX 4375 [] [.CZ 4 4374],
.X 4,
.X 3,
.measureX 4374 [] [.CZ 3 4373],
.X 3,
.X 2,
.measureX 4373 [] [.CZ 2 4760],
.X 2,
.CX 4113 4505,
.CX 4113 4506,
.CX 4113 4507,
.CX 4113 4508,
.CX 4113 4509,
.CX 4113 4510,
.CX 4113 4511,
.CX 4113 4512,
.CX 4113 4513,
.CX 4113 4514,
.CX 4113 4515,
.CX 4113 4516,
.CX 4113 4517,
.CX 4113 4518,
.CX 4113 4519,
.CX 4113 4520,
.CX 4113 4521,
.CX 4113 4522,
.CX 4113 4523,
.CX 4113 4524,
.CX 4113 4525,
.CX 4113 4526,
.CX 4113 4527,
.CX 4113 4528,
.CX 4113 4529,
.CX 4113 4530,
.CX 4113 4531,
.CX 4113 4532,
.CX 4113 4533,
.CX 4113 4534,
.CX 4113 4535,
.CX 4113 4536,
.CX 4113 4537,
.CX 4113 4538,
.CX 4113 4539,
.CX 4113 4540,
.CX 4113 4541,
.CX 4113 4542,
.CX 4113 4543
]
def block53:Program:=[
.CX 4113 4544,
.CX 4113 4545,
.CX 4113 4546,
.CX 4113 4547,
.CX 4113 4548,
.CX 4113 4549,
.CX 4113 4550,
.CX 4113 4551,
.CX 4113 4552,
.CX 4113 4553,
.CX 4113 4554,
.CX 4113 4555,
.CX 4113 4556,
.CX 4113 4557,
.CX 4113 4558,
.CX 4113 4559,
.CX 4113 4560,
.CX 4113 4561,
.CX 4113 4562,
.CX 4113 4563,
.CX 4113 4564,
.CX 4113 4565,
.CX 4113 4566,
.CX 4113 4567,
.CX 4113 4568,
.CX 4113 4569,
.CX 4113 4570,
.CX 4113 4571,
.CX 4113 4572,
.CX 4113 4573,
.CX 4113 4574,
.CX 4113 4575,
.CX 4113 4576,
.CX 4113 4577,
.CX 4113 4578,
.CX 4113 4579,
.CX 4113 4580,
.CX 4113 4581,
.CX 4113 4582,
.CX 4113 4583,
.CX 4113 4584,
.CX 4113 4585,
.CX 4113 4586,
.CX 4113 4587,
.CX 4113 4588,
.CX 4113 4589,
.CX 4113 4590,
.CX 4113 4591,
.CX 4113 4592,
.CX 4113 4593,
.CX 4113 4594,
.CX 4113 4595,
.CX 4113 4596,
.CX 4113 4597,
.CX 4113 4598,
.CX 4113 4599,
.CX 4113 4600,
.CX 4113 4601,
.CX 4113 4602,
.CX 4113 4603,
.CX 4113 4604,
.CX 4113 4605,
.CX 4113 4606,
.CX 4113 4607,
.CX 4113 4608,
.CX 4113 4609,
.CX 4113 4610,
.CX 4113 4611,
.CX 4113 4612,
.CX 4113 4613,
.CX 4113 4614,
.CX 4113 4615,
.CX 4113 4616,
.CX 4113 4617,
.CX 4113 4618,
.CX 4113 4619,
.CX 4113 4620,
.CX 4113 4621,
.CX 4113 4622,
.CX 4113 4623,
.CX 4113 4624,
.CX 4113 4625,
.CX 4113 4626,
.CX 4113 4627,
.CX 4113 4628,
.CX 4113 4629,
.CX 4113 4630,
.CX 4113 4631,
.CX 4113 4632,
.CX 4113 4633,
.CX 4113 4634,
.CX 4113 4635,
.CX 4113 4636,
.CX 4113 4637,
.CX 4113 4638,
.CX 4113 4639,
.CX 4113 4640,
.CX 4113 4641,
.CX 4113 4642,
.CX 4113 4643,
.CX 4113 4644,
.CX 4113 4645,
.CX 4113 4646,
.CX 4113 4647,
.CX 4113 4648,
.CX 4113 4649,
.CX 4113 4650,
.CX 4113 4651,
.CX 4113 4652,
.CX 4113 4653,
.CX 4113 4654,
.CX 4113 4655,
.CX 4113 4656,
.CX 4113 4657,
.CX 4113 4658,
.CX 4113 4659,
.CX 4113 4660,
.CX 4113 4661
]
def join1_3:Program:=block1++block2
def join0_3:Program:=block0++join1_3
def join4_6:Program:=block4++block5
def join3_6:Program:=block3++join4_6
def join0_6:Program:=join0_3++join3_6
def join7_9:Program:=block7++block8
def join6_9:Program:=block6++join7_9
def join9_11:Program:=block9++block10
def join11_13:Program:=block11++block12
def join9_13:Program:=join9_11++join11_13
def join6_13:Program:=join6_9++join9_13
def join0_13:Program:=join0_6++join6_13
def join14_16:Program:=block14++block15
def join13_16:Program:=block13++join14_16
def join16_18:Program:=block16++block17
def join18_20:Program:=block18++block19
def join16_20:Program:=join16_18++join18_20
def join13_20:Program:=join13_16++join16_20
def join21_23:Program:=block21++block22
def join20_23:Program:=block20++join21_23
def join23_25:Program:=block23++block24
def join25_27:Program:=block25++block26
def join23_27:Program:=join23_25++join25_27
def join20_27:Program:=join20_23++join23_27
def join13_27:Program:=join13_20++join20_27
def join0_27:Program:=join0_13++join13_27
def join28_30:Program:=block28++block29
def join27_30:Program:=block27++join28_30
def join31_33:Program:=block31++block32
def join30_33:Program:=block30++join31_33
def join27_33:Program:=join27_30++join30_33
def join34_36:Program:=block34++block35
def join33_36:Program:=block33++join34_36
def join36_38:Program:=block36++block37
def join38_40:Program:=block38++block39
def join36_40:Program:=join36_38++join38_40
def join33_40:Program:=join33_36++join36_40
def join27_40:Program:=join27_33++join33_40
def join41_43:Program:=block41++block42
def join40_43:Program:=block40++join41_43
def join43_45:Program:=block43++block44
def join45_47:Program:=block45++block46
def join43_47:Program:=join43_45++join45_47
def join40_47:Program:=join40_43++join43_47
def join48_50:Program:=block48++block49
def join47_50:Program:=block47++join48_50
def join50_52:Program:=block50++block51
def join52_54:Program:=block52++block53
def join50_54:Program:=join50_52++join52_54
def join47_54:Program:=join47_50++join50_54
def join40_54:Program:=join40_47++join47_54
def join27_54:Program:=join27_40++join40_54
def join0_54:Program:=join0_27++join27_54
def literal:Program:=join0_54

end ECDSAAdd.Entrant.KnownAMidStaged
end

section
-- Peak-memory helpers: evaluate a chunked `compileS?` one compile chunk per declaration.
namespace ECDSAAdd.Entrant.PeakChunkFL
open ECDSAAdd ZeroSetDevelop

theorem some_of_map {α β : Type} {o : Option α} {f : α → β} {b : β} (h : o.map f = some b) :
    ∃ a, o = some a ∧ f a = b := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

theorem out_sound {Q : List Wire} {p : Program} (o : Option (CheckedS Q p)) (T : Program)
    (h : o.elim false (fun cm => ParkAProgramBool.programEq cm.out T) = true) :
    o.map (fun cm => cm.out) = some T := by
  cases o with
  | none => cases h
  | some cm => exact congrArg some (ParkAProgramBool.programEq_sound _ _ h)

theorem split_out (Q : List Wire) (p : Program) (c : Nat) (rest : Unit → Option (CheckedS Q (p.drop c)))
    (o1 o2 : Program)
    (h1 : (compileFuelS Q (c+1) (p.take c)).map (fun cm => cm.out) = some o1)
    (h2 : (rest ()).map (fun cm => cm.out) = some o2) :
    (splitAt? Q p c rest).map (fun cm => cm.out) = some (o1 ++ o2) := by
  obtain ⟨a, ha, rfl⟩ := some_of_map h1
  obtain ⟨b, hb, rfl⟩ := some_of_map h2
  unfold splitAt?
  simp only [ha, hb, Option.map_some]

theorem step (Q : List Wire) (n : Nat) (p o1 o2 : Program) (hlen : ¬ p.length ≤ 1024)
    (h1 : (compileFuelS Q (1024+1) (p.take 1024)).map (fun cm => cm.out) = some o1)
    (h2 : (chunkFuelS Q n (p.drop 1024)).map (fun cm => cm.out) = some o2) :
    (chunkFuelS Q (n+1) p).map (fun cm => cm.out) = some (o1 ++ o2) := by
  obtain ⟨x, hx, hxo⟩ :=
    some_of_map (split_out Q p 1024 (fun _ => chunkFuelS Q n (p.drop 1024)) o1 o2 h1 h2)
  rw [chunkFuelS, if_neg hlen, hx]
  simp only [Option.orElse_some, Option.map_some, hxo]

theorem last (Q : List Wire) (n : Nat) (p o : Program) (hlen : p.length ≤ 1024)
    (h : (compileFuelS Q (p.length+1) p).map (fun cm => cm.out) = some o) :
    (chunkFuelS Q (n+1) p).map (fun cm => cm.out) = some o := by
  rw [chunkFuelS, if_pos hlen]
  exact h

theorem take_drop_app {α : Type} (l r : List α) (n : Nat) : l.take n ++ (l.drop n ++ r) = l ++ r := by
  rw [← List.append_assoc, List.take_append_drop]

theorem elim_of_map {Q : List Wire} {p : Program} (o : Option (CheckedS Q p)) (lit : Program)
    (h : o.map (fun cm => cm.out) = some lit) :
    o.elim false (fun c => ParkAProgramBool.programEq lit c.out) = true := by
  cases o with
  | none => cases h
  | some c =>
    have hc : c.out = lit := Option.some.inj h
    show ParkAProgramBool.programEq lit c.out = true
    rw [hc]
    exact (ParkAProgramBool.programEq_iff lit lit).mpr rfl

end ECDSAAdd.Entrant.PeakChunkFL
end

section
namespace ECDSAAdd.Entrant.A161Low4Facts

set_option maxRecDepth 100000
set_option maxHeartbeats 500000000

def hs99 := A161Facts.loans95 A161FixedFold.L++A161FixedFold.L.core.work.take 4

-- Peak memory: compileS? hs99 pLow, one declaration per compile chunk.
theorem peak_m99_len : List.length pLow = 7949 := by decide +kernel
section
attribute [local irreducible] pLow
theorem peak_m99_long0 : ¬ (List.length pLow) ≤ 1024 := by
  simp only [peak_m99_len]
  decide
theorem peak_m99_long1 : ¬ (List.length (List.drop 1024 pLow)) ≤ 1024 := by
  simp only [List.length_drop, peak_m99_len]
  decide
theorem peak_m99_long2 : ¬ (List.length (List.drop 1024 (List.drop 1024 pLow))) ≤ 1024 := by
  simp only [List.length_drop, peak_m99_len]
  decide
theorem peak_m99_long3 : ¬ (List.length (List.drop 1024 (List.drop 1024 (List.drop 1024 pLow)))) ≤ 1024 := by
  simp only [List.length_drop, peak_m99_len]
  decide
theorem peak_m99_long4 : ¬ (List.length (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 pLow))))) ≤ 1024 := by
  simp only [List.length_drop, peak_m99_len]
  decide
theorem peak_m99_long5 : ¬ (List.length (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 pLow)))))) ≤ 1024 := by
  simp only [List.length_drop, peak_m99_len]
  decide
theorem peak_m99_long6 : ¬ (List.length (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 pLow))))))) ≤ 1024 := by
  simp only [List.length_drop, peak_m99_len]
  decide
theorem peak_m99_short7 : (List.length (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 pLow)))))))) ≤ 1024 := by
  simp only [List.length_drop, peak_m99_len]
  decide
end
theorem peak_m99_seg0 : (ZeroSetDevelop.compileFuelS hs99 (1024+1) (List.take 1024 pLow)).map (fun cm => cm.out) =
  some (ECDSAAdd.Entrant.KnownAMidStaged.block0 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block1 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block2 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block3 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block4 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block5 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block6 ++ (List.take 119 ECDSAAdd.Entrant.KnownAMidStaged.block7)))))))) := by
  apply PeakChunkFL.out_sound
  decide +kernel
theorem peak_m99_seg1 : (ZeroSetDevelop.compileFuelS hs99 (1024+1) (List.take 1024 (List.drop 1024 pLow))).map (fun cm => cm.out) =
  some ((List.drop 119 ECDSAAdd.Entrant.KnownAMidStaged.block7) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block8 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block9 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block10 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block11 ++ (List.take 1 ECDSAAdd.Entrant.KnownAMidStaged.block12)))))) := by
  apply PeakChunkFL.out_sound
  decide +kernel
theorem peak_m99_seg2 : (ZeroSetDevelop.compileFuelS hs99 (1024+1) (List.take 1024 (List.drop 1024 (List.drop 1024 pLow)))).map (fun cm => cm.out) =
  some ((List.drop 1 ECDSAAdd.Entrant.KnownAMidStaged.block12) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block13 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block14 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block15 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block16 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block17 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block18 ++ (List.take 64 ECDSAAdd.Entrant.KnownAMidStaged.block19)))))))) := by
  apply PeakChunkFL.out_sound
  decide +kernel
theorem peak_m99_seg3 : (ZeroSetDevelop.compileFuelS hs99 (1024+1) (List.take 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 pLow))))).map (fun cm => cm.out) =
  some ((List.drop 64 ECDSAAdd.Entrant.KnownAMidStaged.block19) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block20 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block21 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block22 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block23 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block24 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block25 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block26 ++ (List.take 80 ECDSAAdd.Entrant.KnownAMidStaged.block27))))))))) := by
  apply PeakChunkFL.out_sound
  decide +kernel
theorem peak_m99_seg4 : (ZeroSetDevelop.compileFuelS hs99 (1024+1) (List.take 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 pLow)))))).map (fun cm => cm.out) =
  some ((List.drop 80 ECDSAAdd.Entrant.KnownAMidStaged.block27) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block28 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block29 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block30 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block31 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block32 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block33 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block34 ++ (List.take 63 ECDSAAdd.Entrant.KnownAMidStaged.block35))))))))) := by
  apply PeakChunkFL.out_sound
  decide +kernel
theorem peak_m99_seg5 : (ZeroSetDevelop.compileFuelS hs99 (1024+1) (List.take 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 pLow))))))).map (fun cm => cm.out) =
  some ((List.drop 63 ECDSAAdd.Entrant.KnownAMidStaged.block35) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block36 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block37 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block38 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block39 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block40 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block41 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block42 ++ (List.take 63 ECDSAAdd.Entrant.KnownAMidStaged.block43))))))))) := by
  apply PeakChunkFL.out_sound
  decide +kernel
theorem peak_m99_seg6 : (ZeroSetDevelop.compileFuelS hs99 (1024+1) (List.take 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 pLow)))))))).map (fun cm => cm.out) =
  some ((List.drop 63 ECDSAAdd.Entrant.KnownAMidStaged.block43) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block44 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block45 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block46 ++ (List.take 105 ECDSAAdd.Entrant.KnownAMidStaged.block47))))) := by
  apply PeakChunkFL.out_sound
  decide +kernel
theorem peak_m99_seg7 : (ZeroSetDevelop.compileFuelS hs99 ((List.length (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 pLow))))))))+1) (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 (List.drop 1024 pLow)))))))).map (fun cm => cm.out) =
  some ((List.drop 105 ECDSAAdd.Entrant.KnownAMidStaged.block47) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block48 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block49 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block50 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block51 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block52 ++ ECDSAAdd.Entrant.KnownAMidStaged.block53)))))) := by
  apply PeakChunkFL.out_sound
  decide +kernel
theorem peak_m99_map : (ZeroSetDevelop.compileS? hs99 pLow).map (fun cm => cm.out) =
  some ECDSAAdd.Entrant.KnownAMidStaged.literal := by
 have e : (ZeroSetDevelop.compileS? hs99 pLow).map (fun cm => cm.out) =
   some ((ECDSAAdd.Entrant.KnownAMidStaged.block0 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block1 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block2 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block3 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block4 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block5 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block6 ++ (List.take 119 ECDSAAdd.Entrant.KnownAMidStaged.block7)))))))) ++ (((List.drop 119 ECDSAAdd.Entrant.KnownAMidStaged.block7) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block8 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block9 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block10 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block11 ++ (List.take 1 ECDSAAdd.Entrant.KnownAMidStaged.block12)))))) ++ (((List.drop 1 ECDSAAdd.Entrant.KnownAMidStaged.block12) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block13 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block14 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block15 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block16 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block17 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block18 ++ (List.take 64 ECDSAAdd.Entrant.KnownAMidStaged.block19)))))))) ++ (((List.drop 64 ECDSAAdd.Entrant.KnownAMidStaged.block19) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block20 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block21 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block22 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block23 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block24 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block25 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block26 ++ (List.take 80 ECDSAAdd.Entrant.KnownAMidStaged.block27))))))))) ++ (((List.drop 80 ECDSAAdd.Entrant.KnownAMidStaged.block27) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block28 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block29 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block30 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block31 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block32 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block33 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block34 ++ (List.take 63 ECDSAAdd.Entrant.KnownAMidStaged.block35))))))))) ++ (((List.drop 63 ECDSAAdd.Entrant.KnownAMidStaged.block35) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block36 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block37 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block38 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block39 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block40 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block41 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block42 ++ (List.take 63 ECDSAAdd.Entrant.KnownAMidStaged.block43))))))))) ++ (((List.drop 63 ECDSAAdd.Entrant.KnownAMidStaged.block43) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block44 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block45 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block46 ++ (List.take 105 ECDSAAdd.Entrant.KnownAMidStaged.block47))))) ++ ((List.drop 105 ECDSAAdd.Entrant.KnownAMidStaged.block47) ++ (ECDSAAdd.Entrant.KnownAMidStaged.block48 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block49 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block50 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block51 ++ (ECDSAAdd.Entrant.KnownAMidStaged.block52 ++ ECDSAAdd.Entrant.KnownAMidStaged.block53))))))))))))) := by
  delta ZeroSetDevelop.compileS?
  rw [peak_m99_len]
  exact (PeakChunkFL.step _ 7949 _ _ _ peak_m99_long0 peak_m99_seg0
   (PeakChunkFL.step _ 7948 _ _ _ peak_m99_long1 peak_m99_seg1
   (PeakChunkFL.step _ 7947 _ _ _ peak_m99_long2 peak_m99_seg2
   (PeakChunkFL.step _ 7946 _ _ _ peak_m99_long3 peak_m99_seg3
   (PeakChunkFL.step _ 7945 _ _ _ peak_m99_long4 peak_m99_seg4
   (PeakChunkFL.step _ 7944 _ _ _ peak_m99_long5 peak_m99_seg5
   (PeakChunkFL.step _ 7943 _ _ _ peak_m99_long6 peak_m99_seg6
   (PeakChunkFL.last _ 7942 _ _ peak_m99_short7 peak_m99_seg7))))))))
 rw [e, Option.some.injEq]
 delta ECDSAAdd.Entrant.KnownAMidStaged.literal ECDSAAdd.Entrant.KnownAMidStaged.join1_3 ECDSAAdd.Entrant.KnownAMidStaged.join0_3 ECDSAAdd.Entrant.KnownAMidStaged.join4_6 ECDSAAdd.Entrant.KnownAMidStaged.join3_6 ECDSAAdd.Entrant.KnownAMidStaged.join0_6 ECDSAAdd.Entrant.KnownAMidStaged.join7_9 ECDSAAdd.Entrant.KnownAMidStaged.join6_9 ECDSAAdd.Entrant.KnownAMidStaged.join9_11 ECDSAAdd.Entrant.KnownAMidStaged.join11_13 ECDSAAdd.Entrant.KnownAMidStaged.join9_13 ECDSAAdd.Entrant.KnownAMidStaged.join6_13 ECDSAAdd.Entrant.KnownAMidStaged.join0_13 ECDSAAdd.Entrant.KnownAMidStaged.join14_16 ECDSAAdd.Entrant.KnownAMidStaged.join13_16 ECDSAAdd.Entrant.KnownAMidStaged.join16_18 ECDSAAdd.Entrant.KnownAMidStaged.join18_20 ECDSAAdd.Entrant.KnownAMidStaged.join16_20 ECDSAAdd.Entrant.KnownAMidStaged.join13_20 ECDSAAdd.Entrant.KnownAMidStaged.join21_23 ECDSAAdd.Entrant.KnownAMidStaged.join20_23 ECDSAAdd.Entrant.KnownAMidStaged.join23_25 ECDSAAdd.Entrant.KnownAMidStaged.join25_27 ECDSAAdd.Entrant.KnownAMidStaged.join23_27 ECDSAAdd.Entrant.KnownAMidStaged.join20_27 ECDSAAdd.Entrant.KnownAMidStaged.join13_27 ECDSAAdd.Entrant.KnownAMidStaged.join0_27 ECDSAAdd.Entrant.KnownAMidStaged.join28_30 ECDSAAdd.Entrant.KnownAMidStaged.join27_30 ECDSAAdd.Entrant.KnownAMidStaged.join31_33 ECDSAAdd.Entrant.KnownAMidStaged.join30_33 ECDSAAdd.Entrant.KnownAMidStaged.join27_33 ECDSAAdd.Entrant.KnownAMidStaged.join34_36 ECDSAAdd.Entrant.KnownAMidStaged.join33_36 ECDSAAdd.Entrant.KnownAMidStaged.join36_38 ECDSAAdd.Entrant.KnownAMidStaged.join38_40 ECDSAAdd.Entrant.KnownAMidStaged.join36_40 ECDSAAdd.Entrant.KnownAMidStaged.join33_40 ECDSAAdd.Entrant.KnownAMidStaged.join27_40 ECDSAAdd.Entrant.KnownAMidStaged.join41_43 ECDSAAdd.Entrant.KnownAMidStaged.join40_43 ECDSAAdd.Entrant.KnownAMidStaged.join43_45 ECDSAAdd.Entrant.KnownAMidStaged.join45_47 ECDSAAdd.Entrant.KnownAMidStaged.join43_47 ECDSAAdd.Entrant.KnownAMidStaged.join40_47 ECDSAAdd.Entrant.KnownAMidStaged.join48_50 ECDSAAdd.Entrant.KnownAMidStaged.join47_50 ECDSAAdd.Entrant.KnownAMidStaged.join50_52 ECDSAAdd.Entrant.KnownAMidStaged.join52_54 ECDSAAdd.Entrant.KnownAMidStaged.join50_54 ECDSAAdd.Entrant.KnownAMidStaged.join47_54 ECDSAAdd.Entrant.KnownAMidStaged.join40_54 ECDSAAdd.Entrant.KnownAMidStaged.join27_54 ECDSAAdd.Entrant.KnownAMidStaged.join0_54
 simp only [List.append_assoc, PeakChunkFL.take_drop_app]

theorem match99 : (ZeroSetDevelop.compileS? hs99 pLow).elim false
    (fun c => ParkAProgramBool.programEq ECDSAAdd.Entrant.KnownAMidStaged.literal c.out) = true :=
 PeakChunkFL.elim_of_map _ _ peak_m99_map

theorem compiled99 : (ZeroSetDevelop.compileS? hs99 pLow).isSome=true :=
 ECDSAAdd.Entrant.D1Opt.isSome_of_elim match99

end ECDSAAdd.Entrant.A161Low4Facts
end

-- Low4 component Plain
section
namespace ECDSAAdd.Entrant.A161Low4Fold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop
 ControlLoan1589BFFold ThirdSavedCarryDevelop ZeroReadDevelop A161Fold

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires
abbrev accReg := A161Fold.accReg
abbrev acc_lengths := A161Fold.acc_lengths
abbrev accReg_work := A161Fold.accReg_work
abbrev accReg_in := A161Fold.accReg_in
abbrev accReg_nodup := A161Fold.accReg_nodup
abbrev wTerms_fits := A161Fold.wTerms_fits
abbrev wBuild := A161Fold.wBuild
abbrev wUnbuild := A161Fold.wUnbuild

abbrev other_away := A161Fold.other_away
abbrev accReg_away := A161Fold.accReg_away
abbrev cFlipK := A161Low4Facts.Klow

def aMiddle (L:CuccaroStreamedSquareWideLayout) (g:Wire) : Program :=
 maskedConstant g (accReg L) cFlipK++(qprogTq L.measuredCore SquareReduction.p++maskedConstant g (accReg L) cFlipK)

theorem flip_run (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉accReg L) (s:State) (m:List Bool) (hz:regValue (accReg L) s.basis%16=0) :
 (run (maskedConstant g (accReg L) cFlipK) m s).phase=s.phase ∧
 (∀q,q∉accReg L → (run (maskedConstant g (accReg L) cFlipK) m s).basis q=s.basis q) ∧
 regValue (accReg L) (run (maskedConstant g (accReg L) cFlipK) m s).basis=
 (if s.basis g then cFlipK-regValue (accReg L) s.basis else regValue (accReg L) s.basis) :=
 A161Low4Facts.flip_run _ (acc_lengths L hw).1 (accReg_nodup L hn) g hg s m hz

theorem a_middle_good (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) (base : BasisState) (hc:L.PairClean base) (O : Nat) (hO:O<SquareReduction.p)
    (s : State) (m : List Bool) (hf:SquareFrame L.core.out base O s.basis) :
    let u:=middleState (wBuild L) (aMiddle L g) s m
    regValue (accReg L) u.basis=4294968272*regValue (hiReg L) s.basis ∧
    regValue (hiReg L) u.basis=regValue (hiReg L) s.basis ∧
    (∀w∈accZ L,u.basis w=false) ∧ (∀w∈accBank L,u.basis w=false) ∧ u.basis L.core.cin=false ∧
    (∀q,q∉accReg L → q∉L.core.out → u.basis q=s.basis q) := by
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
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := 4294968272*regValue (hiReg L) base
  have hH : regValue (hiReg L) base<2^128 := by
    have h := regValue_lt (hiReg L) base
    rwa [hiReg_length L hw] at h
  have hA : A<2^161 := by
    show 4294968272*regValue (hiReg L) base<2^161
    norm_num at hH ⊢
    omega
  have hAM : A%16=0 := by dsimp only [A];omega
  have hAK : A≤cFlipK := by unfold cFlipK A161Low4Facts.Klow;norm_num at hA ⊢;omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^161 := by
    simp only [A']; split
    · unfold cFlipK A161Low4Facts.Klow; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hhi : regValue (hiReg L) b0=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => agree0 q (hiReg_product L q hq))
  have hbuild : Triple (SquareFrame (accReg L) b0 0) (wBuild L) (SquareFrame (accReg L) b0 A) := by
    have h := A161NarrowAcc.build8_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) b0 hz hb clean.cin
    rw [hhi] at h
    exact h
  let mb := measurementCount (wBuild L)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (wBuild L) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc) (by rw [eu.2.1];exact hAM)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis
      else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 161) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 161) (L.core.work.drop 161) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 161) u1.basis=0 :=
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
  have hAM' : A'%16=0 := by
    dsimp only [A']
    split
    · exact A161Low4Facts.sub_mod16 A hAM
    · exact hAM
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc) (by rw [accV];exact hAM')
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis
      else regValue (accReg L) v.basis) at fl2
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
  have hhi2 : regValue (hiReg L) base2=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => (b2off q (prodNotOut q (hiReg_product L q hq))).trans
      (agree0 q (hiReg_product L q hq)))
  have offAcc (q : Wire) (hq:q∈hiReg L ∨ q∈L.foldPad ∨ q∈L.core.work.drop 161 ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉accReg L := by
    apply (other_away L hn q ?_).2.2
    tauto
  have source:regValue (hiReg L) v1.basis=regValue (hiReg L) base :=
    (regValue_congr _ _ _ (fun q hq=>frame2.2 q (offAcc q (Or.inl hq)))).trans hhi2
  have zv:∀q∈accZ L,v1.basis q=false := by
    intro q hq
    have na:q∉accReg L := by
      rcases accZ_mem L q hq with h|h
      · exact offAcc q (Or.inr (Or.inl h))
      · apply offAcc q
        have hd:(L.core.work.drop 161).drop 35=L.core.work.drop 196 := by simp [List.drop_drop]
        rw [←hd] at h
        exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h)))
    exact (frame2.2 q na).trans (hz2 q hq)
  have bv:∀q∈accBank L,v1.basis q=false := by
    intro q hq
    exact (frame2.2 q (offAcc q (Or.inr (Or.inl (List.mem_of_mem_take hq))))).trans (hb2 q hq)
  have iv:v1.basis L.core.cin=false :=
    (frame2.2 _ (offAcc _ (by simp))).trans hi2
  have midEq:middleState (wBuild L) (aMiddle L g) s m=v1 := by
    simp only [middleState,aMiddle,run_append,measurementCount_append,
      (maskedConstant_counts _ _ _).2,Nat.zero_add,Nat.add_zero,List.take_zero,List.drop_zero,List.drop_drop]
    dsimp only [v1,v,u1,u,m3,m2,m1,mc,mb,mk]
    simp only [(maskedConstant_counts _ _ _).2,List.take_zero,List.drop_zero,Nat.add_zero,List.take_take,Nat.min_self,List.drop_take,Nat.sub_self]
  rw [midEq]
  exact ⟨frame2.1.trans (by rw [hhi]),source.trans hhi.symm,zv,bv,iv,
    fun q ha ho=>(frame2.2 q ha).trans (b2off q ho)⟩


theorem plain_frame (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (O:Nat) (hO:O<SquareReduction.p) :
 Triple (SquareFrame L.core.out base O) ((wBuild L++aMiddle L g)++wUnbuild L)
  (SquareFrame L.core.out base
   (((if base g then cFlipK-4294968272*regValue (hiReg L) base else 4294968272*regValue (hiReg L) base)+
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
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := 4294968272*regValue (hiReg L) base
  have hH : regValue (hiReg L) base<2^128 := by
    have h := regValue_lt (hiReg L) base
    rwa [hiReg_length L hw] at h
  have hA : A<2^161 := by
    show 4294968272*regValue (hiReg L) base<2^161
    norm_num at hH ⊢
    omega
  have hAM : A%16=0 := by dsimp only [A];omega
  have hAK : A≤cFlipK := by unfold cFlipK A161Low4Facts.Klow;norm_num at hA ⊢;omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^161 := by
    simp only [A']; split
    · unfold cFlipK A161Low4Facts.Klow; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hhi : regValue (hiReg L) b0=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => agree0 q (hiReg_product L q hq))
  have hbuild : Triple (SquareFrame (accReg L) b0 0) (wBuild L) (SquareFrame (accReg L) b0 A) := by
    have h := A161NarrowAcc.build8_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) b0 hz hb clean.cin
    rw [hhi] at h
    exact h
  let mb := measurementCount (wBuild L)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (wBuild L) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc) (by rw [eu.2.1];exact hAM)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis
      else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 161) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 161) (L.core.work.drop 161) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 161) u1.basis=0 :=
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
  have hAM' : A'%16=0 := by
    dsimp only [A']
    split
    · exact A161Low4Facts.sub_mod16 A hAM
    · exact hAM
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc) (by rw [accV];exact hAM')
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis
      else regValue (accReg L) v.basis) at fl2
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
  have hhi2 : regValue (hiReg L) base2=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => (b2off q (prodNotOut q (hiReg_product L q hq))).trans
      (agree0 q (hiReg_product L q hq)))
  have offAcc (q : Wire) (hq:q∈hiReg L ∨ q∈L.foldPad ∨ q∈L.core.work.drop 161 ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉accReg L := by
    apply (other_away L hn q ?_).2.2
    itauto
  have source:regValue (hiReg L) v1.basis=regValue (hiReg L) base :=
    (regValue_congr _ _ _ (fun q hq=>frame2.2 q (offAcc q (Or.inl hq)))).trans hhi2
  have zv:∀q∈accZ L,v1.basis q=false := by
    intro q hq
    have na:q∉accReg L := by
      rcases accZ_mem L q hq with h|h
      · exact offAcc q (Or.inr (Or.inl h))
      · apply offAcc q
        have hd:(L.core.work.drop 161).drop 35=L.core.work.drop 196 := by simp [List.drop_drop]
        rw [←hd] at h
        exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h)))
    exact (frame2.2 q na).trans (hz2 q hq)
  have bv:∀q∈accBank L,v1.basis q=false := by
    intro q hq
    exact (frame2.2 q (offAcc q (Or.inr (Or.inl (List.mem_of_mem_take hq))))).trans (hb2 q hq)
  have iv:v1.basis L.core.cin=false :=
    (frame2.2 _ (offAcc _ (by simp))).trans hi2
  have midEq:middleState (wBuild L) (aMiddle L g) s m=v1 := by
    simp only [middleState,aMiddle,run_append,measurementCount_append,
      (maskedConstant_counts _ _ _).2,Nat.zero_add,Nat.add_zero,List.take_zero,List.drop_zero,List.drop_drop]
    dsimp only [v1,v,u1,u,m3,m2,m1,mc,mb,mk]
    simp only [(maskedConstant_counts _ _ _).2,List.take_zero,List.drop_zero,Nat.add_zero,List.take_take,Nat.min_self,List.drop_take,Nat.sub_self]
  let post := m.drop (measurementCount (wBuild L)+measurementCount (aMiddle L g))
  have pre2 : SquareFrame (accReg L) base2 (4294968272*regValue (hiReg L) base2) v1.basis := by
    simpa only [hhi2] using frame2
  have inv := A161SourceAdd.unbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) base2 hz2 hb2 hi2 v1 post pre2
  have valuev1 : regValue L.core.out v1.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p :=
    (regValue_congr _ _ _ (fun q hq => fl2.2.1 q (fun ha => accOut q ha hq))).trans ek.2.1
  have firstTwo : run (wBuild L++aMiddle L g) m s=middleState (wBuild L) (aMiddle L g) s m := by
    simp only [middleState,run_take]
    exact run_cat _ _ _ _
  have loop : run ((wBuild L++aMiddle L g)++wUnbuild L) m s=
    run (wUnbuild L) post (middleState (wBuild L) (aMiddle L g) s m) := by
    rw [run_cat (wBuild L++aMiddle L g) (wUnbuild L) m s,measurementCount_append,firstTwo]
  rw [loop,midEq]
  refine ⟨inv.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have agreeOut : ∀q∈L.core.out,(run (wUnbuild L) post v1).basis q=v1.basis q := by
      intro q hq
      exact (inv.2.2 q (fun ha => accOut q ha hq)).trans (by simp [base2,hq])
    exact (regValue_congr _ _ _ agreeOut).trans valuev1
  · intro q hq
    by_cases ha:q∈accReg L
    · have outZero := (regValue_zero _ _).mp inv.2.1 q ha
      have oldZero := (regValue_zero _ _).mp hc.work q (accReg_work L q ha)
      exact outZero.trans oldZero.symm
    · exact (inv.2.2 q ha).trans ((b2off q hq).trans (hf.2 q hq))



end ECDSAAdd.Entrant.A161Low4Fold
end

-- Low4 component GhostReady
section
namespace ECDSAAdd.Entrant.A161Low4Fold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold A161Low4Ghost A161Fold InverseCarryDevelop

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

theorem ghost_middle_good (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (O:Nat) (hO:O<SquareReduction.p)
 (s:State) (m:List Bool) (hf:SquareFrame L.core.out base O s.basis) :
 let u:=middleState (wBuild L) (aMiddle L g) s m
 regValue (ghostAcc L) u.basis=4294968272*regValue (hiReg L) s.basis ∧
 regValue (hiReg L) u.basis=regValue (hiReg L) s.basis ∧
 (∀w∈accZ L,u.basis w=false) ∧ (∀w∈accBank L,u.basis w=false) ∧ u.basis L.core.cin=false := by
 let u:=middleState (wBuild L) (aMiddle L g) s m
 have h:=a_middle_good L hw hn g hg base hc O hO s m hf
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have gz:∀q∈ghosts L,u.basis q=false := by
  intro q hq
  have na:q∉accReg L := fun bad=>ghosts_work_free L hn q hq (accReg_work L q bad)
  have no:=ghosts_out_free L hn q hq
  exact (h.2.2.2.2.2 q na no).trans (ghosts_clean L s.basis clean q hq)
 have val:regValue (reg L) u.basis=16*(268435517*regValue (hiReg L) s.basis) := by
  change regValue (accReg L) u.basis=16*(268435517*regValue (hiReg L) s.basis)
  rw [h.1]
  omega
 have eq:=ghostAcc_value L hw u.basis (268435517*regValue (hiReg L) s.basis) val gz
 exact ⟨eq.trans h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩

end ECDSAAdd.Entrant.A161Low4Fold
end

-- Low4 component GenericFold
section
namespace ECDSAAdd.Entrant.A161Low4GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop A161Low4Ghost

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run ECDSAAdd.measurementCount ECDSAAdd.toffoliCount

def domain (L : CuccaroStreamedSquareWideLayout) : List Wire :=
 L.core.cin::(hiReg L++ghostAcc L++FullPadDevelop.pad L++accBank L)

def Ready (L : CuccaroStreamedSquareWideLayout) (g : Wire) (hs : List Wire) : Prop :=
 g∉L.wires ∧ hs.length=100 ∧ hs.Nodup ∧
 (∀u∈hs,u∉domain L) ∧ (∀u∈hs,u≠L.core.sumCarry ∧ u≠eV L ∧ u≠spare L) ∧
 L.core.sumCarry∉domain L ∧ eV L∉domain L ∧ spare L∉domain L ∧
 eV L≠L.core.sumCarry ∧ spare L≠L.core.sumCarry ∧ spare L≠eV L ∧
 (∀u∈([L.core.sumCarry,eV L,spare L] : List Wire),
   u∉g::A161Fold.accReg L ∧ u∉L.measuredCore.wires ∧ u∉L.core.out)

def loop (L : CuccaroStreamedSquareWideLayout) (hs : List Wire) (middle : Program) : Program :=
 A161Carry.buildMany 100 (A161Fold.accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) hs
  L.core.sumCarry (eV L) (spare L)++middle++
 A161Carry.unbuildMany 100 (A161Fold.accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) hs
  L.core.sumCarry (eV L) (spare L)

theorem smallFit (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
 ∀f∈earlyHTerms (hiReg L),Acc.Fits (ghostAcc L) (FullPadDevelop.pad L) (accBank L) L.core.cin 161 f := by
 intro f hf
 have old:=A161GenericFold.smallFit L hw hn f hf
 have src:f.src=hiReg L := by
  simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> rfl
 exact {toFitsLen:=old.toFitsLen,nd:=by rw [src];exact A161Low4Domains.small_domain_nodup L hn}

theorem fullFit (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
 ∀f∈earlyHTerms (hiReg L),Acc.Fits (ghostAcc L) (accZ L) (accBank L) L.core.cin 161 f := by
 intro f hf
 have old:=A161Fold.wTerms_fits L hw hn f hf
 have src:f.src=hiReg L := by
  simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> rfl
 exact {toFitsLen:=old.toFitsLen,nd:=by rw [src];exact A161Low4Domains.full_domain_nodup L hn}

theorem loop_eq_ghost (L:CuccaroStreamedSquareWideLayout) (hs:List Wire) (P:Program) :
 loop L hs P=A161Carry.buildMany 100 (ghostAcc L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) hs
  L.core.sumCarry (eV L) (spare L)++P++
 A161Carry.unbuildMany 100 (ghostAcc L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) hs
  L.core.sumCarry (eV L) (spare L) := by
 unfold loop
 rw [←A161Low4Structural.buildMany_eq L 100,←A161Low4Structural.unbuildMany_eq L 100]

theorem free_middle (L : CuccaroStreamedSquareWideLayout) (g u : Wire)
 (ha:u∉g::A161Fold.accReg L) (hc:u∉L.measuredCore.wires) : u∉wires (A161Low4Fold.aMiddle L g) := by
 have hm : u∉wires (maskedConstant g (A161Fold.accReg L) A161Low4Facts.Klow) := by
  intro h
  exact ha (List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h))
 have hk : u∉wires (qprogTq L.measuredCore SquareReduction.p) := by
  have hc' : u∉L.measuredCore.wires.toFinset := by simpa only [List.mem_toFinset] using hc
  exact fun h => hc' (QCore.qprog_supportTq L.measuredCore SquareReduction.p h)
 intro h
 simp only [A161Low4Fold.aMiddle,wires_append,Finset.mem_union] at h
 exact h.elim hm (fun h => h.elim hk hm)























































































end ECDSAAdd.Entrant.A161Low4GenericFold
end

-- Low4 component FixedData
section
namespace ECDSAAdd.Entrant.A161Low4FixedFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
abbrev L:=A161FixedFold.L
abbrev g:=A161FixedFold.g
abbrev d:=A161FixedFold.d
abbrev q:=L.core.sumCarry
abbrev r:=eV L
abbrev p:=spare L
abbrev hs99:=A161Low4Facts.hs99
abbrev hs100:=hs99++[d]

theorem hw:L.Widths:=A161FixedFold.hw
theorem hn:L.wires.Nodup:=A161FixedFold.hn

def checked : ZeroSetDevelop.CheckedS hs99 A161Low4Facts.pLow :=
 (ZeroSetDevelop.compileS? hs99 A161Low4Facts.pLow).get A161Low4Facts.compiled99
attribute [local irreducible] checked

theorem cert99 : ZeroSetDevelop.SRewrites hs99 (A161Low4Fold.aMiddle L g) checked.out := by
 have h:=Eq.mp (congrArg (fun P:Program=>ZeroSetDevelop.SRewrites hs99 P checked.out) A161Low4Facts.input_eq) checked.proof
 simpa only [A161Low4Facts.middleLow,A161Low4Facts.acc161,A161Facts.acc161,
  A161Low4Fold.aMiddle,A161Low4Fold.accReg,A161Fold.accReg,A161Low4Fold.cFlipK] using h

theorem ready : A161Low4GenericFold.Ready L g hs100 := by
 rcases A161Low4Geometry.geometry with ⟨hg,hl,hnd,hfresh,hne,fq,fr,fp,rq,pq,pr,fmid,hwork⟩
 refine ⟨hg,hl,hnd,hfresh,hne,fq,fr,fp,rq,pq,pr,?_⟩
 intro u hu
 apply fmid u
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hu ⊢
 itauto

theorem cert100 : ZeroSetDevelop.SRewrites hs100 (A161Low4Fold.aMiddle L g) checked.out := by
 rcases A161Low4Geometry.geometry with ⟨_,_,_,_,_,_,_,_,_,_,_,fmid,_⟩
 have free:=fmid d (by simp)
 exact A161Extend.SRewrites_extend hs99 d _ checked.out cert99
  (A161Low4GenericFold.free_middle L g d free.1 free.2.1)

def fold100 : Program:=A161Low4GenericFold.loop L hs100 checked.out

theorem hostClean (base:BasisState) (hc:L.PairClean base) (hd:base d=false) :
 ∀u∈hs100,u∉L.core.out ∧ base u=false := by
 rcases A161Low4Geometry.geometry with ⟨_,_,_,_,_,_,_,_,_,_,_,fmid,hwork⟩
 intro u hu
 rcases List.mem_append.mp hu with hu|hu
 · have hw:u∈L.core.work:=hwork u hu
   exact ⟨(L.pairAuxAway hn u (by simp [hw])).2,(regValue_zero _ _).mp hc.work u hw⟩
 · have e:u=d:=by simpa only [List.mem_singleton] using hu
   subst u
   exact ⟨(fmid d (by simp)).2.2,hd⟩














end ECDSAAdd.Entrant.A161Low4FixedFold
end

-- Low4 component LoopResources
section
namespace ECDSAAdd.Entrant.A161Low4GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run

theorem physical (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (ready:Ready L g hs)
 (cert:ZeroSetDevelop.SRewrites hs (A161Low4Fold.aMiddle L g) newMiddle) :
 GatePhysical (loop L hs newMiddle) := by
  rw [loop_eq_ghost]
  let acc := A161Low4Ghost.ghostAcc L
  let pad := FullPadDevelop.pad L
  let bank := accBank L
  let src := hiReg L
  let q := L.core.sumCarry
  let r := eV L
  let p := spare L
  let middleProgram := A161Low4Fold.aMiddle L g
  have smallFit := smallFit L hw hn
  rcases ready with ⟨hg,hlen,hnd,hfresh,hne,fq,fr,fp,rq,pq,pr,fmid⟩
  have lens := A161Fold.acc_lengths L hw
  have haLen:acc.length=161:=A161Low4Ghost.ghostAcc_length L hw
  have hsrc := hiReg_length L hw
  have offq := A161Carry.wloop_original_off acc pad bank L.core.cin src q haLen hsrc smallFit fq
  have offr := A161Carry.wloop_original_off acc pad bank L.core.cin src r haLen hsrc smallFit fr
  have offp := A161Carry.wloop_original_off acc pad bank L.core.cin src p haLen hsrc smallFit fp
  have plen := FullPadDevelop.pad_length L hw
  have blen := lens.2.2.1
  have bd := A161Carry.buildDual_support acc pad bank L.core.cin src q r haLen hsrc (by change 5≤(FullPadDevelop.pad L).length; omega) (by change 132≤(accBank L).length; omega)
  have ud := A161Carry.unbuildDual_support acc pad bank L.core.cin src q r haLen hsrc (by change 132≤(accBank L).length; omega)
  have b0 := A161Carry.buildCached_support acc pad bank L.core.cin src q haLen hsrc (by change 5≤(FullPadDevelop.pad L).length; omega) (by change 132≤(accBank L).length; omega)
  have u0 := A161Carry.unbuildConsumed_support acc pad bank L.core.cin src q haLen hsrc (by change 132≤(accBank L).length; omega)
  have offpd : p∉wires (A161Carry.buildDual acc pad bank L.core.cin src q r) ∧
   p∉wires (A161Carry.unbuildDual acc pad bank L.core.cin src q r) := by
   constructor
   · intro h
     exact (Finset.mem_insert.mp (bd h)).elim pr (fun h => (Finset.mem_insert.mp (b0 h)).elim pq offp.1)
   · intro h
     exact (Finset.mem_insert.mp (ud h)).elim pr (fun h => (Finset.mem_insert.mp (u0 h)).elim pq offp.2)
  have pp := A161Carry.physical acc pad bank L.core.cin src q r p haLen hsrc smallFit rq
   offq.1 offq.2 offr.1 offr.2 offpd.1 offpd.2
  have coreNd : L.measuredCore.wires.Nodup :=
   (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have mc := maskedConstant_physical g (A161Fold.accReg L) A161Low4Facts.Klow (fun h => hg (A161Fold.accReg_in L g h))
  have mid : GatePhysical middleProgram := by
   simp only [middleProgram,A161Low4Fold.aMiddle,gatePhysical_append]
   exact ⟨mc,QCore.qprog_physicalTq L.measuredCore SquareReduction.p coreNd,mc⟩
  have fresh : ∀u∈hs,u∉bank := by
   intro u hu hb
   exact hfresh u hu (by simp [domain,bank,hb])
  have physical : GatePhysical (A161Carry.buildTriple acc pad bank L.core.cin src q r p++middleProgram++A161Carry.unbuildTriple acc pad bank L.core.cin src q r p) := by
   simp only [gatePhysical_append]
   exact ⟨⟨pp.1,mid⟩,pp.2⟩
  exact A161Carry.compiled_physical_set 100 acc pad bank L.core.cin src hs q r p middleProgram newMiddle
   haLen hsrc (by change 5≤(FullPadDevelop.pad L).length; omega)
   (by change 132≤(accBank L).length; omega) (by decide) fresh cert physical

def ambient (L : CuccaroStreamedSquareWideLayout) (g : Wire) (hs : List Wire) : List Wire :=
 g::spare L::eV L::L.core.sumCarry::(A161GenericFold.domain L++L.measuredCore.wires++hs)

theorem support (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program)
 (cert:ZeroSetDevelop.SRewrites hs (A161Low4Fold.aMiddle L g) newMiddle) :
 wires (loop L hs newMiddle)⊆(ambient L g hs).toFinset := by
 let acc := A161Fold.accReg L
 let pad := FullPadDevelop.pad L
 let bank := accBank L
 let src := hiReg L
 have lens := A161Fold.acc_lengths L hw
 have hsrc := hiReg_length L hw
 have plen := FullPadDevelop.pad_length L hw
 have hfit := A161GenericFold.smallFit L hw hn
 have tri := A161Carry.support acc pad bank L.core.cin src L.core.sumCarry (eV L) (spare L) lens.1 hsrc hfit
 have cmp := A161Carry.compiled_support_set 100 acc pad bank L.core.cin src hs L.core.sumCarry (eV L) (spare L)
  (A161Low4Fold.aMiddle L g) newMiddle lens.1 hsrc (by change 5≤(FullPadDevelop.pad L).length; omega)
  (by change 132≤(accBank L).length; omega) (by decide) cert
 have sub (u:Wire) (h:u∈(spare L::eV L::L.core.sumCarry::L.core.cin::(src++acc++pad++bank)).toFinset) :
  u∈(ambient L g hs).toFinset := by
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
  simp only [ambient,A161GenericFold.domain,List.mem_toFinset,List.mem_cons,List.mem_append]
  itauto
 intro u hu
 rcases Finset.mem_union.mp (cmp hu) with h|h
 · simp only [wires_append,Finset.mem_union] at h
   rcases h with (h|h)|h
   · exact sub u (tri.1 h)
   · simp only [A161Low4Fold.aMiddle,wires_append,Finset.mem_union] at h
     rcases h with h|(h|h)
     · have h := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
       simp only [List.mem_cons] at h
       simp only [ambient,A161GenericFold.domain,List.mem_toFinset,List.mem_cons,List.mem_append]
       itauto
     · have h := List.mem_toFinset.mp (QCore.qprog_supportTq L.measuredCore SquareReduction.p h)
       simp only [ambient,A161GenericFold.domain,List.mem_toFinset,List.mem_cons,List.mem_append]
       itauto
     · have h := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
       simp only [List.mem_cons] at h
       simp only [ambient,A161GenericFold.domain,List.mem_toFinset,List.mem_cons,List.mem_append]
       itauto
   · exact sub u (tri.2 h)
 · have h := List.mem_toFinset.mp h
   simp only [ambient,List.mem_toFinset,List.mem_cons,List.mem_append]
   itauto



end ECDSAAdd.Entrant.A161Low4GenericFold
end

-- Low4 component Counts
section
namespace ECDSAAdd.Entrant.A161Low4GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount

theorem counts (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (hl:hs.length=100)
 (cert:ZeroSetDevelop.SRewrites hs (A161Low4Fold.aMiddle L g) newMiddle) :
 toffoliCount (loop L hs newMiddle)≤1283 ∧ measurementCount (loop L hs newMiddle)=1543 := by
 let acc := A161Fold.accReg L
 let pad := FullPadDevelop.pad L
 let bank := accBank L
 let src := hiReg L
 let q := L.core.sumCarry
 let r := eV L
 let p := spare L
 have ha := (A161Fold.acc_lengths L hw).1
 have hb := (A161Fold.acc_lengths L hw).2.2.1
 have hsrc : src.length=128 := hiReg_length L hw
 have hz := FullPadDevelop.pad_length L hw
 have zp : 5≤pad.length := by change 5≤(FullPadDevelop.pad L).length; omega
 have bp : 132≤bank.length := by change 132≤(accBank L).length; omega
 have fit := A161GenericFold.smallFit L hw hn
 have b := A161KnownTail.build8_counts acc pad bank L.core.cin src ha (by omega) (fun f h => (fit f h).toFitsLen)
 rw [A161KnownTail.build8_eq] at b
 have u := A161SourceAdd.unbuild_resources acc pad bank L.core.cin src ha hsrc (fun f h => (fit f h).toFitsLen)
 have bc := A161Carry.buildCached_counts acc pad bank L.core.cin src q ha hsrc zp bp
 have uc := A161Carry.unbuildConsumed_counts acc pad bank L.core.cin src q ha hsrc bp
 have bd := A161Carry.buildDual_counts acc pad bank L.core.cin src q r ha hsrc zp bp
 have ud := A161Carry.unbuildDual_counts acc pad bank L.core.cin src q r ha hsrc bp
 have bt := A161Carry.buildTriple_counts acc pad bank L.core.cin src q r p ha hsrc zp bp
 have ut := A161Carry.unbuildTriple_counts acc pad bank L.core.cin src q r p ha hsrc bp
 have mid := QCore.qprog_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)
 have mask := maskedConstant_counts g (A161Fold.accReg L) A161Low4Facts.Klow
 have cm := A161Carry.compiled_counts_set 100 acc pad bank L.core.cin src hs q r p
  (A161Low4Fold.aMiddle L g) newMiddle ha hsrc zp bp (by decide) hl cert
 simp only [A161Low4Fold.aMiddle,toffoliCount_append,measurementCount_append,mask.1,mask.2,mid.1,mid.2] at cm
 simp only [loop,toffoliCount_append,measurementCount_append]
 dsimp only [acc,pad,bank,src,q,r,p] at *
 constructor <;> omega

end ECDSAAdd.Entrant.A161Low4GenericFold

namespace ECDSAAdd.Entrant.A161Low4GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] Challenge.gateSlots ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
theorem slots (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (hl:hs.length=100)
 (cert:ZeroSetDevelop.SRewrites hs (A161Low4Fold.aMiddle L g) newMiddle) :
 Challenge.gateSlots (loop L hs newMiddle)≤40000 := by
 let acc := A161Fold.accReg L
 let pad := FullPadDevelop.pad L
 let bank := accBank L
 let src := hiReg L
 let q := L.core.sumCarry
 let r := eV L
 let p := spare L
 have ha := (A161Fold.acc_lengths L hw).1
 have hb := (A161Fold.acc_lengths L hw).2.2.1
 have hsrc : src.length=128 := hiReg_length L hw
 have hz := FullPadDevelop.pad_length L hw
 have zp : 5≤pad.length := by change 5≤(FullPadDevelop.pad L).length; omega
 have bp : 132≤bank.length := by change 132≤(accBank L).length; omega
 have fit := A161GenericFold.smallFit L hw hn
 have b := A161KnownTail.build8_gateSlots acc pad bank L.core.cin src ha (by omega) (fun f h => (fit f h).toFitsLen)
 rw [A161KnownTail.build8_eq] at b
 have u := A161SourceAdd.unbuild_resources acc pad bank L.core.cin src ha hsrc (fun f h => (fit f h).toFitsLen)
 have bc := A161Carry.buildCached_counts acc pad bank L.core.cin src q ha hsrc zp bp
 have uc := A161Carry.unbuildConsumed_counts acc pad bank L.core.cin src q ha hsrc bp
 have bd := A161Carry.buildDual_counts acc pad bank L.core.cin src q r ha hsrc zp bp
 have ud := A161Carry.unbuildDual_counts acc pad bank L.core.cin src q r ha hsrc bp
 have bt := A161Carry.buildTriple_counts acc pad bank L.core.cin src q r p ha hsrc zp bp
 have ut := A161Carry.unbuildTriple_counts acc pad bank L.core.cin src q r p ha hsrc bp
 have mid := QCore.qprog_gateSlotsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw)
 have mask := Baselines.maskedConstant_gateSlots_le g (A161Fold.accReg L) A161Low4Facts.Klow
 have cm := A161Carry.compiled_counts_set 100 acc pad bank L.core.cin src hs q r p
  (A161Low4Fold.aMiddle L g) newMiddle ha hsrc zp bp (by decide) hl cert
 simp only [A161Low4Fold.aMiddle,A161Low4Fold.accReg,A161Low4Fold.cFlipK,Challenge.gateSlots_append] at cm
 simp only [loop,Challenge.gateSlots_append]
 dsimp only [acc,pad,bank,src,q,r,p] at *
 omega


end ECDSAAdd.Entrant.A161Low4GenericFold
end

-- Low4 component Offsets
section
namespace ECDSAAdd.Entrant.A161Low4Offsets
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

def delta : Nat := 3*2^161+15

theorem flip_decomposition : OwnDiagAll12Square.cFlipK=A161Low4Facts.Klow+delta := by
 norm_num [OwnDiagAll12Square.cFlipK,A161Low4Facts.Klow,delta]

-- The A body is reflected: reducing its complement decreases the reflected output,
-- and therefore increases the unreflected square offset.
def squareK : Nat := ControlLoan1589BFFold.K+delta




theorem squareK_cast : (squareK : ZMod SquareReduction.p)=
 (ControlLoan1589BFFold.K : ZMod SquareReduction.p)+(delta : ZMod SquareReduction.p) := by
 rw [squareK,Nat.cast_add]

def resAFlow (P O : Nat) (g : Bool) : Nat :=
 ofCast true (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-P-
   (if g then (A161Low4Facts.Klow : ZMod SquareReduction.p) else 0)))

theorem resAF_delta (P O : Nat) (g : Bool) : (resAFlow P O g : ZMod SquareReduction.p)=
 (resAF P O g : ZMod SquareReduction.p)-(if g then (delta : ZMod SquareReduction.p) else 0) := by
 haveI : NeZero SquareReduction.p := ⟨by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]⟩
 simp only [resAFlow,resAF,ofCast,if_true,ZMod.natCast_zmod_val]
 cases g
 · simp
 · simp only [if_true]
   rw [flip_decomposition,Nat.cast_add]
   ring









end ECDSAAdd.Entrant.A161Low4Offsets
end

-- Low4 component Body
section
namespace ECDSAAdd.Entrant.A161Low4Body
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold


set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem body_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hzero:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) (fold : Program)
    (foldFrame : ∀ O, O<SquareReduction.p →
      Triple (SquareFrame L.core.out base O) fold
       (SquareFrame L.core.out base
        (((if base c then A161Low4Facts.Klow-4294968272*regValue (hiReg L) base else 4294968272*regValue (hiReg L) base)+
         (SquareReduction.p-1-O))%SquareReduction.p))) :
    Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold)) (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base c))) := by
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
  have t3 := foldFrame O2 hO2
  rw [← hAeq] at t3
  have all := t1.seq (t2.seq t3)
  apply Triple.conseq (fun s h => h) all
  intro s hs
  refine ⟨hs.1.trans ?_,hs.2⟩
  let A := Acc.accVal base 0 (aAcc L).spec
  have hH : regValue (hiReg L) base<2^128 := by
    have h := regValue_lt (hiReg L) base
    rwa [hiReg_length L hw] at h
  have hA : A<2^161 := by
    change Acc.accVal base 0 (aAcc L).spec<2^161
    rw [hAeq]
    have bound:=A161Low4Math.accumulator_div16_bound _ hH
    norm_num at bound ⊢
    omega
  have hAM : A%16=0 := by
    change Acc.accVal base 0 (aAcc L).spec%16=0
    rw [hAeq]
    omega
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
  have bound : ((if base c then A161Low4Facts.Klow-A else A)+(SquareReduction.p-1-O2))%SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ pmod
  apply measuredOrientationCast_injective true _ _ bound (ofCast_lt true _)
  refine Eq.trans ?_ (cast_ofCast true (measuredOrientationCast false O+(((M^2 : Nat) : ZMod SquareReduction.p)*2^128-
    ((M^2 : Nat) : ZMod SquareReduction.p)-(if base c then (A161Low4Facts.Klow : ZMod SquareReduction.p) else 0)))).symm
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
    have hAle : A≤A161Low4Facts.Klow := by unfold A161Low4Facts.Klow;norm_num at hA ⊢;omega
    have hoff : ((A161Low4Facts.Klow-A : Nat) : ZMod SquareReduction.p)=(A161Low4Facts.Klow : ZMod SquareReduction.p)-
        (A : ZMod SquareReduction.p) := by
      rw [Nat.cast_sub hAle]
    rw [hoff]
    linear_combination hsum

end ECDSAAdd.Entrant.A161Low4Body
end

-- Low4 component FixedBody
section
namespace ECDSAAdd.Entrant.A161Low4FixedFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires checked List.toFinset

def body : Program := measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold100)

theorem ambient_sites : (A161Low4GenericFold.ambient L g hs100).toFinset⊆(d::g::L.wires).toFinset := by
 rcases A161Low4Geometry.geometry with ⟨_,_,_,_,_,_,_,_,_,_,_,_,hwork⟩
 exact A161GenericFold.ambient_sites_general L hw g d hs100 (A161GenericFold.append_hosts L hs99 d hwork)




theorem fold_support : wires fold100⊆(d::g::L.wires).toFinset :=
 (A161Low4GenericFold.support L hw hn g hs100 checked.out cert100).trans ambient_sites

theorem fold_physical : GatePhysical fold100 :=
 A161Low4GenericFold.physical L hw hn g hs100 checked.out ready cert100
















theorem body_support : wires body⊆(d::g::L.wires).toFinset := by
 have p1 := measuredFoldQ_supportTq L g (negP L) (by
  intro u hu
  exact List.mem_of_mem_take hu)
 have p2 := measuredFoldQ_supportTq L g (rot128F L) (by
  intro u hu
  rcases List.mem_append.mp hu with hu|hu
  · exact List.mem_of_mem_drop (List.mem_of_mem_take hu)
  · exact List.mem_of_mem_take hu)
 intro u hu
 simp only [body,wires_append,Finset.mem_union] at hu
 rcases hu with hu|(hu|hu)
 · exact List.mem_toFinset.mpr (List.mem_cons_of_mem d (List.mem_toFinset.mp (p1 hu)))
 · exact List.mem_toFinset.mpr (List.mem_cons_of_mem d (List.mem_toFinset.mp (p2 hu)))
 · exact fold_support hu













end ECDSAAdd.Entrant.A161Low4FixedFold
end
