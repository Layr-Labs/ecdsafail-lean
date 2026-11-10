import ECDSAAdd.Submission.Entrant.TerminalGraph
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagonalCarry5
open Arithmetic RecordedQuantum Challenge

/-- The majority of one chain cell; the topmost cell with a set literal bit has a dead Toffoli. -/
def majD (b last : Bool) (x cin c : Wire) : Program :=
  if last && b then [Instr.CX x c,Instr.CX cin c] else mappedMajority (bit b) x cin c

def chainD : List Bool→List Wire→List Wire→Wire→Wire→Wire→Program
  | b::bs,x::xs,c::cs,cin,ctl,target =>
      majD b bs.isEmpty x cin c++chainD bs xs cs c ctl target++mappedEraseCarry (bit b) x cin c
  | [],[],[],cin,ctl,target => [.CCX ctl cin target]
  | _,_,_,_,_,_ => []

theorem chainD_counts (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) (hlast : bs.getLast? = some true) :
    toffoliCount (chainD bs xs cs cin ctl target)+1=toffoliCount (chain bs xs cs cin ctl target) ∧
    measurementCount (chainD bs xs cs cin ctl target)=measurementCount (chain bs xs cs cin ctl target) := by
  induction bs generalizing xs cs cin with
  | nil => simp at hlast
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have one := mappedBit_counts (bit b) x cin c
        cases bs with
        | nil =>
          have hb : b = true := by simpa using hlast
          subst hb
          have ex : xs=[] := List.eq_nil_of_length_eq_zero (by simpa using hx)
          have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
          subst ex; subst ec
          simp only [chainD,chain,majD,toffoliCount_append,measurementCount_append,one.1,one.2.1,
            one.2.2.1,one.2.2.2.1,List.isEmpty_nil,Bool.and_self,if_true]
          simp [toffoliCount,measurementCount]
        | cons b' bs =>
          have h2 : (b'::bs).getLast? = some true := by
            simpa [List.getLast?_cons_cons] using hlast
          have rest := ih xs cs c (by simpa using hx) (by simpa using hc) h2
          simp only [chainD,chain,majD,List.isEmpty_cons,Bool.false_and,Bool.false_eq_true,if_false,
            toffoliCount_append,measurementCount_append,one.1,one.2.1,
            one.2.2.1,one.2.2.2.1,rest.2]
          exact ⟨by have := rest.1; omega, trivial⟩

theorem chainD_mc (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    measurementCount (chainD bs xs cs cin ctl target)=measurementCount (chain bs xs cs cin ctl target) := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    subst ex; subst ec; rfl
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have one := mappedBit_counts (bit b) x cin c
        have rest := ih xs cs c (by simpa using hx) (by simpa using hc)
        have zero : measurementCount (majD b bs.isEmpty x cin c)=0 := by
          unfold majD
          split
          · rfl
          · exact one.2.1
        simp only [chainD,chain,measurementCount_append,zero,one.2.1,rest]

private theorem reg_cons' (x : Wire) (xs : List Wire) (s : BasisState) :
    regValue (x::xs) s=(s x).toNat+2*regValue xs s := by
  cases h : s x <;> simp [regValue,h]

theorem carry_half (b a c : Bool) : 2*(carryBit b a c).toNat ≤ b.toNat+a.toNat+c.toNat := by
  cases b <;> cases a <;> cases c <;> simp [carryBit]

theorem chainD_run (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hn : (ctl::target::cin::(xs++cs)).Nodup)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length)
    (s : State) (m : List Bool) (clean : ∀q∈cs,s.basis q=false)
    (hb : 2*(regValue xs s.basis+value bs+(s.basis cin).toNat)<3*2^bs.length) :
    run (chainD bs xs cs cin ctl target) m s=run (chain bs xs cs cin ctl target) m s := by
  induction bs generalizing xs cs cin s m with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    subst ex; subst ec; rfl
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have cnt := List.nodup_iff_count.mp hn
        have loc : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have restND : (ctl::target::c::(xs++cs)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        have ccs : c∉cs := by
          intro h; have a := cnt c; have p := List.count_pos_iff.mpr h
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at a
          omega
        have xc : x≠c := fun h => (List.nodup_cons.mp loc).1 (by simp [h])
        have ic : cin≠c := fun h => (List.nodup_cons.mp (List.nodup_cons.mp loc).2).1 (by simp [h])
        have cxs : c∉xs := by
          intro h; have a := cnt c; have p := List.count_pos_iff.mpr h
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at a
          omega
        let C := carryBit b (s.basis x) (s.basis cin)
        let u : State := ⟨s.phase,writeBit s.basis c C⟩
        have first (rec : List Bool) : run (mappedMajority (bit b) x cin c) rec s=u := by
          rw [mappedMajority_correct _ _ _ _ loc (by simp [bit])]
          simp [u,bit,MappedBit.value,clean c (by simp),C]
        have uf (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,hq]
        have clean' : ∀q∈cs,u.basis q=false := by
          intro q hq
          rw [uf q (fun h => ccs (h ▸ hq))]
          exact clean q (by simp [hq])
        have word : regValue xs u.basis=regValue xs s.basis :=
          regValue_congr _ _ _ (fun q hq => uf q (fun h => cxs (h ▸ hq)))
        have uc : u.basis c=C := by simp [u,writeBit]
        have firstD (rec : List Bool) : run (majD b bs.isEmpty x cin c) rec s=u := by
          unfold majD
          split
          · rename_i hlb
            have hbb : bs.isEmpty = true ∧ b = true := by simpa using hlb
            have hbs : bs = [] := List.isEmpty_iff.mp hbb.1
            subst hbs
            have hbt := hbb.2
            subst hbt
            have dead : (s.basis x && s.basis cin)=false := by
              simp only [regValue,value,List.length_nil] at hb
              cases h1 : s.basis x <;> cases h2 : s.basis cin <;> simp_all
            simp only [run]
            apply congrArg (State.mk s.phase)
            funext q
            by_cases hq : q=c
            · subst hq
              simp only [writeBit,Function.update_self,u,C,clean q (by simp)]
              cases h1 : s.basis x <;> cases h2 : s.basis cin <;> simp_all [carryBit,bit,MappedBit.value]
            · simp [u,writeBit,Function.update,hq]
          · exact first rec
        have zeroM : measurementCount (mappedMajority (bit b) x cin c)=0 := (mappedBit_counts _ _ _ _).2.1
        have zeroD : measurementCount (majD b bs.isEmpty x cin c)=0 := by
          unfold majD
          split
          · rfl
          · exact zeroM
        have hb' : 2*(regValue xs u.basis+value bs+(u.basis c).toNat)<3*2^bs.length := by
          rw [word,uc]
          change 2*(regValue xs s.basis+value bs+(carryBit b (s.basis x) (s.basis cin)).toNat)<_
          have h1 := carry_half b (s.basis x) (s.basis cin)
          have hb2 := hb
          rw [List.length_cons,pow_succ,reg_cons'] at hb2
          simp only [value] at hb2
          omega
        have rest := ih xs cs c restND (by simpa using hx) (by simpa using hc) u
          (m.take (measurementCount (chain bs xs cs c ctl target))) clean' hb'
        have mcEq := chainD_mc bs xs cs c ctl target (by simpa using hx) (by simpa using hc)
        simp only [chainD,chain,List.append_assoc,run_append,measurementCount_append,zeroM,zeroD,
          List.take_zero,List.drop_zero,mcEq]
        rw [firstD,first]
        rw [rest]


/-! Dead-Toffoli deletion relation. -/
end ECDSAAdd.Entrant.DiagonalCarry5

namespace ECDSAAdd.Entrant.DeadCarry
open Arithmetic RecordedQuantum Challenge

/-- `Q` is `P` with one Toffoli whose two controls are already folded into its target by CXs removed. -/
def DropRel (P Q : Program) : Prop :=
  ∃ (A B : Program) (x y t : Wire),
    P = A ++ ([Instr.CX x t,Instr.CX y t,Instr.CCX x y t] ++ B) ∧
    Q = A ++ ([Instr.CX x t,Instr.CX y t] ++ B)

theorem DropRel.ctx {P Q : Program} (h : DropRel P Q) (U V : Program) : DropRel (U ++ (P ++ V)) (U ++ (Q ++ V)) := by
  obtain ⟨A,B,x,y,t,hp,hq⟩ := h
  refine ⟨U ++ A,B ++ V,x,y,t,?_,?_⟩
  · subst hp; simp
  · subst hq; simp

theorem DropRel.left {P Q : Program} (h : DropRel P Q) (V : Program) : DropRel (P ++ V) (Q ++ V) := by
  have := h.ctx [] V
  simpa using this

theorem DropRel.right {P Q : Program} (h : DropRel P Q) (U : Program) : DropRel (U ++ P) (U ++ Q) := by
  have := h.ctx U []
  simpa using this

theorem DropRel.rename {P Q : Program} (h : DropRel P Q) (f : Wire → Wire) :
    DropRel (renameProgram f P) (renameProgram f Q) := by
  obtain ⟨A,B,x,y,t,hp,hq⟩ := h
  refine ⟨renameProgram f A,renameProgram f B,f x,f y,f t,?_,?_⟩
  · subst hp; simp [renameProgram,renameInstr]
  · subst hq; simp [renameProgram,renameInstr]

theorem DropRel.toffoli {P Q : Program} (h : DropRel P Q) : toffoliCount Q+1=toffoliCount P := by
  obtain ⟨A,B,x,y,t,hp,hq⟩ := h
  subst hp; subst hq
  simp [toffoliCount_append,toffoliCount]; omega

theorem DropRel.meas {P Q : Program} (h : DropRel P Q) : measurementCount Q=measurementCount P := by
  obtain ⟨A,B,x,y,t,hp,hq⟩ := h
  subst hp; subst hq
  simp [measurementCount_append,measurementCount]

theorem DropRel.slots {P Q : Program} (h : DropRel P Q) : gateSlots Q+1=gateSlots P := by
  obtain ⟨A,B,x,y,t,hp,hq⟩ := h
  subst hp; subst hq
  simp [gateSlots_append,gateSlots,instructionSlots]; omega

theorem DropRel.wires {P Q : Program} (h : DropRel P Q) : ECDSAAdd.wires Q=ECDSAAdd.wires P := by
  obtain ⟨A,B,x,y,t,hp,hq⟩ := h
  subst hp; subst hq
  simp only [wires_append]
  have e : ECDSAAdd.wires ([Instr.CX x t,Instr.CX y t] : Program) = ECDSAAdd.wires ([Instr.CX x t,Instr.CX y t,Instr.CCX x y t] : Program) := by
    ext q
    simp [ECDSAAdd.wires,Instr.wires]
  rw [e]

theorem DropRel.physical {P Q : Program} (h : DropRel P Q) (hp : GatePhysical P) : GatePhysical Q := by
  obtain ⟨A,B,x,y,t,hP,hQ⟩ := h
  subst hP; subst hQ
  simp only [gatePhysical_append] at hp ⊢
  obtain ⟨hA,hm,hB⟩ := hp
  refine ⟨hA,?_,hB⟩
  intro i hi
  exact hm i (by simp at hi ⊢; tauto)

end ECDSAAdd.Entrant.DeadCarry

namespace ECDSAAdd.Entrant.DiagonalCarry5
open Arithmetic RecordedQuantum Challenge

theorem chain_drop (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) (hlast : bs.getLast? = some true) :
    DeadCarry.DropRel (chain bs xs cs cin ctl target) (chainD bs xs cs cin ctl target) := by
  induction bs generalizing xs cs cin with
  | nil => simp at hlast
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        cases bs with
        | nil =>
          have hb : b = true := by simpa using hlast
          subst hb
          have ex : xs=[] := List.eq_nil_of_length_eq_zero (by simpa using hx)
          have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
          subst ex; subst ec
          refine ⟨[],chain [] [] [] c ctl target ++ mappedEraseCarry (bit true) x cin c,x,cin,c,?_,?_⟩
          · simp [chain,mappedMajority,bit]
          · simp [chainD,majD,chain]
        | cons b' bs =>
          have h2 : (b'::bs).getLast? = some true := by
            simpa [List.getLast?_cons_cons] using hlast
          have rest := ih xs cs c (by simpa using hx) (by simpa using hc) h2
          have := rest.ctx (mappedMajority (bit b) x cin c) (mappedEraseCarry (bit b) x cin c)
          simpa [chain,chainD,majD,List.append_assoc] using this

end ECDSAAdd.Entrant.DiagonalCarry5

namespace ECDSAAdd.Entrant.DeadCarry
open Arithmetic RecordedQuantum Challenge BalancedCircuit BalancedField

def parityCarryD (L : Layout) (ctl : Wire) : Program :=
  DiagonalCarry5.chainD EntryHalf5.parityBits L.low (L.carry.take 255) L.lower ctl L.parity

theorem parityBits_last : EntryHalf5.parityBits.getLast? = some true := by
  unfold EntryHalf5.parityBits
  decide

theorem threshold_small : EntryHalf5.threshold+2<2^254 := by decide

theorem parityCarry_drop (L : Layout) (hw : L.Widths) (ctl : Wire) :
    DropRel (EntryHalf5.parityCarry L ctl) (parityCarryD L ctl) := by
  have w := BalancedCleanup.widths L.toLayout hw
  exact DiagonalCarry5.chain_drop EntryHalf5.parityBits L.low (L.carry.take 255) L.lower ctl L.parity
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,w.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2]) parityBits_last

/-- The range fact that makes the top majority Toffoli dead. -/
theorem parity_bound (R : Int) (hr : Centered R) (low : Nat) (lw : Bool)
    (hl : low=(magnitude R).toNat) (hlw : lw=negative R) :
    2*(low+DiagonalCarry5.value EntryHalf5.parityBits+lw.toNat)<3*2^EntryHalf5.parityBits.length := by
  have mb := magnitude_bounds R hr
  have z := Int.toNat_of_nonneg mb.1
  have thr := EntryHalf5.threshold_relation
  have tb := threshold_small
  have lv := DiagonalCarry5.literal_value 255 EntryHalf5.literalValue EntryHalf5.literal_bound
  have ln : EntryHalf5.parityBits.length=255 := by
    simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length]
  have vv : DiagonalCarry5.value EntryHalf5.parityBits=EntryHalf5.literalValue := lv
  have lt : lw.toNat ≤ 1 := by cases lw <;> simp
  rw [ln,vv]
  have lit : EntryHalf5.literalValue=2^255-1-EntryHalf5.threshold := rfl
  have p254 : (2:Nat)^255=2*2^254 := by rw [pow_succ]; omega
  have p254' : (2:Nat)^254>0 := Nat.two_pow_pos _
  subst hl
  omega

end ECDSAAdd.Entrant.DeadCarry

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Challenge Baselines RecordedQuantum
attribute [local irreducible] run

def positiveParityHD (L : Layout) (ctl : Wire) : Program :=
  EntryHalf5.prepareMagnitude L++(renameProgram (Equiv.swap (cAt L 248) L.rmsb)
    (DeadCarry.parityCarryD L ctl)++(EntryHalf5.prepareMagnitude L).reverse)

def recoverParityHD (L : Layout) (J : Wire) : Program :=
  [.X J]++positiveParityHD L J++[.X J]

def clearParityHD (L : Layout) (J : Wire) : Program :=
  [.CX (L.ylow.getD 0 0) L.parity]++recoverParityHD L J

def clearHD (L : Layout) (J : Wire) : Program :=
  renameProgram (Equiv.swap (cHi L) L.sign) (renameProgram (Equiv.swap (cLo L) L.one) (clearParityHD L J))

theorem positiveParityHD_counts (L : Layout) (hw : L.Widths) (ctl : Wire) :
    toffoliCount (positiveParityHD L ctl)+1=toffoliCount (positiveParityH L ctl) ∧
    measurementCount (positiveParityHD L ctl)=measurementCount (positiveParityH L ctl) := by
  have d := DeadCarry.parityCarry_drop L hw ctl
  have r := d.rename (Equiv.swap (cAt L 248) L.rmsb)
  have h1 := r.toffoli
  have h2 := r.meas
  simp only [positiveParityHD,positiveParityH,toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem positiveParityHD_drop (L : Layout) (hw : L.Widths) (ctl : Wire) :
    DeadCarry.DropRel (positiveParityH L ctl) (positiveParityHD L ctl) := by
  have d := DeadCarry.parityCarry_drop L hw ctl
  have r := (d.rename (Equiv.swap (cAt L 248) L.rmsb)).ctx (EntryHalf5.prepareMagnitude L)
    (EntryHalf5.prepareMagnitude L).reverse
  simpa only [positiveParityH,positiveParityHD,List.append_assoc] using r

theorem positiveParityHD_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (ctl : Wire) (hctl : ctl∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (positiveParityHD L ctl) m s=run (EntryHalf5.positiveParity L ctl) m s := by
  let c := run (EntryHalf5.prepareMagnitude L) [] s
  have pv := EntryHalf5.prepare_low_value L hw hn R hr s [] hR hz
  change regValue L.low c.basis=(magnitude R).toNat ∧ c.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → c.basis q=s.basis q) at pv
  have rz : c.basis L.rmsb=false := prepare_rmsb L hw hn R hr s [] hR hz
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have notLower (a : Wire) (ha : a∈L.carry) : a≠L.lower := fun e =>
    flagAway L hn L.lower (by simp) (by rw [←e];exact List.mem_append_right _ ha)
  have c248 : c.basis (cAt L 248)=false :=
    (pv.2.2 _ (carry_not_r L hn _ m248) (notLower _ m248)).trans (hc _ m248)
  have nd := EntryHalf5.carry_nodup L hn ctl hctl
  have clean : ∀a∈L.carry.take 255,c.basis a=false := by
    intro a ha
    have am := List.mem_of_mem_take ha
    exact (pv.2.2 a (carry_not_r L hn a am) (notLower a am)).trans (hc a am)
  have len := BalancedCleanup.widths L.toLayout hw
  have hx : L.low.length=EntryHalf5.parityBits.length := by
    simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1]
  have hcl : (L.carry.take 255).length=EntryHalf5.parityBits.length := by
    simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2]
  have one (t : List Bool) := DiagonalCarry5.correct EntryHalf5.parityBits L.low (L.carry.take 255)
    L.lower ctl L.parity nd hx hcl c t clean
  have bound := DeadCarry.parity_bound R hr (regValue L.low c.basis) (c.basis L.lower) pv.1 pv.2.1
  have dEq (t : List Bool) : run (DeadCarry.parityCarryD L ctl) t c=run (EntryHalf5.parityCarry L ctl) t c :=
    DiagonalCarry5.chainD_run EntryHalf5.parityBits L.low (L.carry.take 255) L.lower ctl L.parity nd
      hx hcl c t clean bound
  have pc : cAt L 248≠L.parity := fun e =>
    flagAway L hn L.parity (by simp) (by rw [←e];exact List.mem_append_right _ m248)
  have rmem : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have pr : L.rmsb≠L.parity := fun e =>
    flagAway L hn L.parity (by simp) (by rw [←e];simp [rmem])
  have host (t : List Bool) :
      run (renameProgram (Equiv.swap (cAt L 248) L.rmsb) (DeadCarry.parityCarryD L ctl)) t c=
        run (EntryHalf5.parityCarry L ctl) t c := by
    rw [← dEq t]
    apply rebind_swap_run _ _ _ c t c248 rz
    · rw [dEq t]; exact ((one t).2.1 _ pc).trans c248
    · rw [dEq t]; exact ((one t).2.1 _ pr).trans rz
  have pm := (EntryHalf5.prepare_counts L).2
  have rc := renameProgram_counts (Equiv.swap (cAt L 248) L.rmsb) (DeadCarry.parityCarryD L ctl)
  have mcD : measurementCount (DeadCarry.parityCarryD L ctl)=measurementCount (EntryHalf5.parityCarry L ctl) :=
    DiagonalCarry5.chainD_mc _ _ _ _ _ _ hx hcl
  rw [positiveParityHD,EntryHalf5.positiveParity,run_append,run_append (EntryHalf5.prepareMagnitude L),
    pm,List.take_zero,List.drop_zero,run_append,run_append (EntryHalf5.parityCarry L ctl),rc.2,mcD,host]

theorem recoverParityHD_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (recoverParityHD L J) m s=run (EntryHalf5.recoverParity L J) m s := by
  let u : State := ⟨s.phase,writeBit s.basis J (!s.basis J)⟩
  have away (q : Wire) (hq : q∈L.wires) : q≠J := fun e => hJ (e ▸ hq)
  have same (q : Wire) (hq : q∈L.wires) : u.basis q=s.basis q := by
    simp only [u,writeBit,Function.update_of_ne (away q hq)]
  have sameR : regValue L.r u.basis=encodeWord 256 R :=
    (regValue_congr _ _ _ (fun q hq => same q (by
      simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
        BalancedCleanup.Layout.low,List.mem_append,List.mem_cons,List.mem_singleton] at hq ⊢
      tauto))).trans hR
  have uz : u.basis L.lower=false := by
    rw [same _ (by simp [Layout.wires,BalancedCleanup.Layout.wires])];exact hz
  have uc : ∀q∈L.carry,u.basis q=false := fun q hq =>
    (same q (by simp [Layout.wires,BalancedCleanup.Layout.wires,hq])).trans (hc q hq)
  have first : run [.X J] [] s=u := by simp [u,run,writeBit]
  have cnt : measurementCount (positiveParityHD L J)=measurementCount (EntryHalf5.positiveParity L J) :=
    ((positiveParityHD_counts L hw J).2).trans (positiveParityH_counts L J).2
  have e := context_eq [.X J] (EntryHalf5.positiveParity L J) (positiveParityHD L J) [.X J] 0 s m rfl
    (by rw [cnt,Nat.zero_add])
    (by
      intro r
      rw [first,List.drop_zero]
      exact positiveParityHD_eq L hw hn J hJ R hr u r sameR uz uc)
  rw [recoverParityHD,EntryHalf5.recoverParity,e,List.drop_zero,cnt,List.take_append_drop]

theorem clearParityHD_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (clearParityHD L J) m s=run (clearParity L J) m s := by
  let u : State := ⟨s.phase,writeBit s.basis L.parity (s.basis L.parity ^^ s.basis (L.ylow.getD 0 0))⟩
  have pa := flagAway L hn L.parity (by simp)
  have away (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity := fun e => pa (e ▸ hq)
  have lp : L.lower≠L.parity := by
    have nd := List.nodup_iff_count.mp (scalarND L hn) L.lower
    intro e;simp [e,List.count_cons] at nd;omega
  have ur : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hR
    intro q hq
    simp [u,writeBit,away q (by simp [hq])]
  have uz : u.basis L.lower=false := by simpa [u,writeBit,lp] using hz
  have uc : ∀q∈L.carry,u.basis q=false := fun q hq => by
    simpa [u,writeBit,away q (by simp [hq])] using hc q hq
  have first : run [.CX (L.ylow.getD 0 0) L.parity] [] s=u := by simp [run,u]
  rw [clearParityHD,clearParity,run_append,run_append,
    show measurementCount [Instr.CX (L.ylow.getD 0 0) L.parity]=0 from rfl,List.take_zero,List.drop_zero,first]
  exact recoverParityHD_eq L hw hn J hJ R hr u m ur uz uc


theorem clearHD_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J : Wire) (hJ : J∉L.wires)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) (ho : s.basis L.one=false) (hs : s.basis L.sign=false) :
    run (clearHD L J) m s=run (clearParity L J) m s := by
  have dist := hosts_distinct L hw hn
  have lo : cLo L∈L.carry := carry_mem L hw 4 (by decide)
  have hi : cHi L∈L.carry := carry_mem L hw 254 (by decide)
  have base := clearParityHD_eq L hw hn J hJ R hr s m hR hl hc
  have cx := clear_xor L hw hn J hJ R hr s m hR hl hc
  have same (q : Wire) (hq : q≠L.parity) : (run (clearParityHD L J) m s).basis q=s.basis q := by
    rw [base,cx]; simp [writeBit,hq]
  have innerEq : run (renameProgram (Equiv.swap (cLo L) L.one) (clearParityHD L J)) m s=
      run (clearParityHD L J) m s :=
    rebind_swap_run _ _ _ s m (hc _ lo) ho
      ((same _ (Ne.symm dist.2.2.1)).trans (hc _ lo))
      ((same _ (Ne.symm dist.2.2.2.2.2.2.1)).trans ho)
  rw [clearHD,rebind_swap_run _ _ _ s m (hc _ hi) hs
    (by rw [innerEq];exact (same _ (Ne.symm dist.2.2.2.1)).trans (hc _ hi))
    (by rw [innerEq];exact (same _ (Ne.symm dist.2.2.2.2.2.2.2)).trans hs),innerEq,base]



def programHD (L : Layout) (J B : Wire) : Program :=
  clearHD L J++restoreAt L J B++affineH L J B++CleanInverse5.inverse (prepare L J B)

theorem inverseHD_forward (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    run (programHD L J B) m (run (EntryRetained5.program L J B) [] s)=s := by
  let a:=run (prepare L J B) [] s
  let b:=run (arithmetic L) [] a
  let c:=run (eraseScalarsAt L J B) [] b
  have prep:=prepare_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  change Prepared L J B Jv Bv Y s a at prep
  have pref:=prefix_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  have prefix_run : run (prefixProgram L J B) [] s=b := by
    simp only [prefixProgram,run_append,List.take_nil,List.drop_nil]
    rfl
  rw [prefix_run] at pref
  have dd : b.basis L.one=(b.basis L.parity && b.basis (lowY L)) := by
    rw [pref.parity,pref.u]
    exact pref.d
  have ee : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)) := by
    rw [pref.a,pref.u]
    exact pref.e
  have uu : b.basis (lowY L)=(b.basis J && b.basis B) := by rw [pref.u,pref.j,pref.b]
  have aa:=scalar_erase_relation L hw Jv Bv Y hy b.basis pref.target pref.parity pref.a pref.d
  have erased:=eraseScalarsAt_run L hw hn J B hJ hB hJB b [] ee aa dd uu
  change c=⟨b.phase,erasedBasis L.parity L.lower L.one L.sign (lowY L) J b.basis⟩ at erased
  have en:=erasePorts_nodup L hw hn J B hJ hB hJB
  have restore:=restoreScalars_inverse L.parity L.lower L.one L.sign (lowY L) J B L.rmsb en b
  have undoRestore (n : List Bool) : run (restoreAt L J B) n c=b := by
    rw [erased]
    exact restore n ee aa dd uu
  have nd:=allND L hn
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have data : (L.r++L.y++L.carry).Nodup := (List.nodup_append'.mp nd).2.1
  have ry : (L.r++L.y).Nodup := (List.nodup_append'.mp data).1
  have rdy := (List.nodup_append'.mp ry).2.2
  have dyc := (List.nodup_append'.mp data).2.2
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r++L.y++L.carry := by
    have mem : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢
      tauto
    exact flagAway L hn q mem
  have cSame (q : Wire) (hq : q∈L.r++L.carry) : c.basis q=b.basis q := by
    have qdata : q∈L.r++L.y++L.carry := by
      simp only [List.mem_append] at hq ⊢
      tauto
    have qu : q≠lowY L := by
      intro eq
      rcases List.mem_append.mp hq with qr|qc
      · exact List.disjoint_left.mp rdy qr (eq.symm ▸ y0)
      · exact List.disjoint_left.mp dyc (List.mem_append_right _ y0) (eq ▸ qc)
    have qf (f : Wire) (hf : f∈[L.parity,L.lower,L.one,L.sign]) : q≠f := fun e=>flag f hf (e ▸ qdata)
    rw [erased]
    exact erasedBasis_frame _ _ _ _ _ _ _ q (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      exact not_or_intro (qf _ (by simp)) (not_or_intro (qf _ (by simp))
        (not_or_intro (qf _ (by simp)) qu)))
  have cR : regValue L.r c.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) :=
    (regValue_congr _ _ _ (fun q hq=>cSame q (List.mem_append_left _ hq))).trans pref.target
  have cCarry : ∀q∈L.carry,c.basis q=false := fun q hq=>
    (cSame q (List.mem_append_right _ hq)).trans (pref.carry q hq)
  have ca : c.basis L.lower=false := by
    have ne : L.lower≠lowY L := by
      intro e;exact flag L.lower (by simp) (by simp [e,y0])
    have ad : L.lower≠L.one := by
      have h:=List.nodup_iff_count.mp en L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,ne,ad]
  have bounds:=signedY_bounds (Jv && Bv) Y hy
  have rc : Centered (halfResult (signedY (Jv && Bv) Y)) := by
    apply (halfResult_spec _ ?_).1
    have hp:=constants
    unfold Centered at bounds
    omega
  have undoClear (n : List Bool) :
      run (clearParity L J) n (run (clearParity L J) [] c)=c :=
    clear_involution L hw hn J hJ _ rc c [] n cR ca cCarry
  have undoAdd (n : List Bool) :
      run (affineSub (sources L) L.r (L.carry.take 255) (lowY L)) n b=a := by
    exact affineSub_inverse _ _ _ _ (arithmeticND L hw hn) (sources_away L hw hn)
      (by rw [sources_length,(BalancedCleanup.widths L.toLayout hw).2.1])
      (by simp [List.length_take,hw.2.2,(BalancedCleanup.widths L.toLayout hw).2.1]) a [] n
      (fun q hq=>prep.carry q (List.mem_of_mem_take hq)) (sources_valid L hn)
  have undoPrep (n : List Bool) : run (CleanInverse5.inverse (prepare L J B)) n a=s :=
    CleanInverse5.inverse_run _ _ (prepare_ready L hw hn J B hJ hB s hY hc hz) n
  have forward_run : run (EntryRetained5.program L J B) [] s=run (clearParity L J) [] c := by
    simp only [EntryRetained5.program,prefixProgram,run_append,List.take_nil,List.drop_nil]
    rfl
  have notU (q : Wire) (hq : q=L.one ∨ q=L.sign) : q≠lowY L := by
    intro e
    have f := flagAway L hn q (by rcases hq with rfl|rfl <;> simp)
    exact f (by rw [e];simp [y0])
  have cOne : c.basis L.one=false := by
    have ad : L.lower≠L.one := by
      have h:=List.nodup_iff_count.mp en L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,notU L.one (Or.inl rfl)]
  have cSign : c.basis L.sign=false := by
    have sa : L.sign≠L.lower := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    have sd : L.sign≠L.one := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,notU L.sign (Or.inr rfl),sa,sd]
  have undoClearH (n : List Bool) :
      run (clearHD L J) n (run (clearParity L J) [] c)=c := by
    have cx := clear_xor L hw hn J hJ _ rc c [] cR ca cCarry
    have po : L.parity∉L.r := fun h => flag L.parity (by simp) (by simp [h])
    have keepC (q : Wire) (hq : q≠L.parity) : (run (clearParity L J) [] c).basis q=c.basis q := by
      rw [cx];simp [writeBit,hq]
    have dist := hosts_distinct L hw hn
    have sc := scalarND L hn
    have lp : L.lower≠L.parity := by
      have h:=List.nodup_iff_count.mp sc L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [clearHD_eq L hw hn J hJ _ rc _ n
      ((regValue_congr _ _ _ (fun q hq => keepC q (fun e => po (e ▸ hq)))).trans cR)
      ((keepC _ lp).trans ca)
      (fun q hq => (keepC q (fun e => flag L.parity (by simp) (by rw [←e];simp [hq]))).trans (cCarry q hq))
      ((keepC _ (Ne.symm dist.2.2.2.2.2.2.1)).trans cOne)
      ((keepC _ (Ne.symm dist.2.2.2.2.2.2.2)).trans cSign)]
    exact undoClear n
  have undoAddH (n : List Bool) : run (affineH L J B) n b=a := by
    obtain ⟨m',h⟩ := affineH_eq L hw hn J B hJ hB hJB b n ee uu pref.carry
    rw [h]
    exact undoAdd m'
  rw [forward_run,programHD]
  simp only [List.append_assoc,run_append,run_take]
  rw [undoClearH,undoRestore,undoAddH,undoPrep]

theorem inverseHD_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hY : regValue L.y s.basis=encodeWord 256 (if Jv then Y else 0))
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    let out:=run (programHD L J B) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis (encodeWord 256 Y) 0 out.basis := by
  let t : State:=⟨s.phase,putWord L.r (encodeWord 256 Y) (putWord L.y 0 s.basis)⟩
  have len:=BalancedCleanup.widths L.toLayout hw
  have nd:=allND L hn
  have nr:=EntryHalf5.target_nodup L hn
  have ny : L.y.Nodup := by
    exact (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).1).2.1
  have dis : List.Disjoint L.r L.y :=
    (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).1).2.2
  have outside (q : Wire) (qr : q∉L.r) (qy : q∉L.y) : t.basis q=s.basis q := by
    simp only [t,putWord_outside _ _ _ q qr,putWord_outside _ _ _ q qy]
  have tr : regValue L.r t.basis=encodeWord 256 Y :=
    putWord_value L.r nr _ (by rw [len.2.1];exact encodeWord_bound 256 Y) _
  have ty : regValue L.y t.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (putWord_value L.y ny 0 (Nat.two_pow_pos _) s.basis)
    intro q hq
    apply putWord_outside
    exact fun bad=>List.disjoint_left.mp dis bad hq
  have noData (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (data_member L q (by simp [bad]))
    · exact hq (data_member L q (by simp [bad]))
  have workAway (q : Wire) (hq : q∈work L) : q∉L.r ∧ q∉L.y := by
    have n:=List.nodup_iff_count.mp nd q
    have w:=List.count_pos_iff.mpr hq
    constructor <;> intro bad <;> have b:=List.count_pos_iff.mpr bad
    all_goals
      simp only [work,List.count_append,List.count_cons,List.count_nil] at w
      simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.y,BalancedCleanup.Layout.low,
        List.count_append,List.count_cons,List.count_nil] at n b
      omega
  have tc : ∀q∈work L,t.basis q=false := fun q hq=>
    (outside q (workAway q hq).1 (workAway q hq).2).trans (hc q hq)
  have signAway : L.sign∉L.r ∧ L.sign∉L.y := by
    have h:=flagAway L hn L.sign (by simp)
    exact ⟨fun a=>h (by simp [a]),fun a=>h (by simp [a])⟩
  have tz : t.basis L.sign=false := (outside _ signAway.1 signAway.2).trans hz
  have tj : t.basis J=Jv := (outside J (noData J hJ).1 (noData J hJ).2).trans hj
  have tb : t.basis B=Bv := (outside B (noData B hB).1 (noData B hB).2).trans hb
  have f:=EntryRetained5.program_frame L hw hn J B hJ hB hJB Jv Bv Y hy t [] tr ty tc tz tj tb
  have ss : PairFrame L.r L.y t.basis
      (encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) s.basis :=
    ⟨hR,hY,fun q qr qy=>(outside q qr qy).symm⟩
  have eq : run (EntryRetained5.program L J B) [] t=s := by
    apply State.extensionality
    · exact f.1
    · exact PairFrame.unique _ _ _ _ _ _ _ f.2 ss
  have inv:=inverseHD_forward L hw hn J B hJ hB hJB Jv Bv Y hy t m tr ty tc tz tj tb
  rw [eq] at inv
  dsimp only
  rw [inv]
  exact ⟨rfl,tr,ty,outside⟩

end ECDSAAdd.Entrant.JointInverse1588


set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Secp256k1

def jointHD (L : BalancedCircuit.Layout) (J G : Wire) : Program :=
  [.X G] ++ programHD L J G ++ [.X G]

theorem outside_layoutHD (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q ∉ L.wires) : q ∉ L.r ∧ q ∉ L.y ∧ q ∉ BalancedCircuit.work L := by
  have zero := List.count_eq_zero.mpr hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    List.count_append,List.count_cons,List.count_nil] at zero
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at pos
    omega
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at pos
    omega
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at pos
    omega

/-- Read the first sign directly from its history wire and restore that wire.
The two record lists of a later old/new comparison can be independent. -/
theorem jointHD_frame (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J,G].Nodup)
    (Jv Gv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)))
    (hY : regValue L.y s.basis = encodeWord 256 (if Jv then Y else 0))
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false)
    (sign : s.basis L.sign=false) (j : s.basis J=Jv) (g : s.basis G=Gv) :
    let out := run (jointHD L J G) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis
      (encodeWord 256 Y) 0 out.basis := by
  have apart : J≠G := fun eq => (List.nodup_cons.mp hJG).1 (List.mem_singleton.mpr eq)
  have away := outside_layoutHD L G hG
  let a : State := ⟨s.phase,writeBit s.basis G (!s.basis G)⟩
  have head : run [Instr.X G] [] s=a := rfl
  have keep (q : Wire) (hq : q≠G) : a.basis q=s.basis q := by
    simp only [a,writeBit,Function.update_of_ne hq]
  have aR : regValue L.r a.basis=encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)) :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.1 (eq ▸ hq)))).trans hR
  have aY : regValue L.y a.basis=encodeWord 256 (if Jv then Y else 0) :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.2.1 (eq ▸ hq)))).trans hY
  have ac : ∀q∈BalancedCircuit.work L,a.basis q=false := by
    intro q hq
    exact (keep q (fun eq => away.2.2 (eq ▸ hq))).trans (clean q hq)
  have sign_mem : L.sign∈L.wires := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have sg : L.sign≠G := fun eq => hG (eq ▸ sign_mem)
  have aj : a.basis J=Jv := (keep J apart).trans j
  have ag : a.basis G= !Gv := by simp only [a,writeBit,Function.update_self,g]
  generalize ht : run (programHD L J G)
    (m.take (measurementCount (programHD L J G))) a=t
  have result := inverseHD_frame L hw hn J G hJ hG hJG Jv (!Gv) Y hy a
    (m.take (measurementCount (programHD L J G))) aR aY ac ((keep _ sg).trans sign) aj ag
  rw [ht] at result
  let v : State := ⟨t.phase,writeBit t.basis G (!t.basis G)⟩
  have shape : run (jointHD L J G) m s=v := by
    have xm : measurementCount [Instr.X G]=0 := rfl
    simp only [jointHD,run_append,measurementCount_append,xm,Nat.zero_add,
      List.take_zero,List.drop_zero,head,ht] <;> rfl
  dsimp only
  rw [shape]
  refine ⟨result.1,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.1
    intro q hq
    have qg : q≠G := fun eq => away.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.2.1
    intro q hq
    have qg : q≠G := fun eq => away.2.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · intro q hr hyq
    by_cases eq : q=G
    · subst q
      change (writeBit t.basis G (!t.basis G)) G=s.basis G
      simp only [writeBit,Function.update_self]
      rw [result.2.2.2 G away.1 away.2.1]
      simp only [a,writeBit,Function.update_self,Bool.not_not]
    · change (writeBit t.basis G (!t.basis G)) q=s.basis q
      rw [show (writeBit t.basis G (!t.basis G)) q=t.basis q by
        simp only [writeBit,Function.update_of_ne eq], result.2.2.2 q hr hyq,keep q eq]


theorem jointHD_pair (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (origin : BasisState) (clean : ∀q∈work L,origin q=false) (sign : origin L.sign=false)
    (Z : Fp) :
    Triple (PairFrame L.r L.y origin
      (centerWord ((if origin J && !origin G then -Z else Z)/2))
      (centerWord (if origin J then Z else 0))) (jointHD L J G)
      (PairFrame L.r L.y origin (centerWord Z) 0) := by
  have outside (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
  have sf:=flagAway L hn L.sign (by simp)
  have sa : L.sign∉L.r ∧ L.sign∉L.y :=
    ⟨fun bad=>sf (by simp [bad]),fun bad=>sf (by simp [bad])⟩
  intro s m h
  have hc : ∀q∈work L,s.basis q=false := fun q hq=>
    (h.2.2 q (work_no_data L hn q hq).1 (work_no_data L hn q hq).2).trans (clean q hq)
  have rr : regValue L.r s.basis=encodeWord 256
      (halfResult (signedY (origin J && !origin G) (centerFp Z))) := by
    rw [unary_half]
    exact h.1
  have yy : regValue L.y s.basis=encodeWord 256 (if origin J then centerFp Z else 0) := by
    rw [source_word]
    exact h.2.1
  have out:=jointHD_frame L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m rr yy hc ((h.2.2 _ sa.1 sa.2).trans sign)
    (h.2.2 _ (outside J hJ).1 (outside J hJ).2) (h.2.2 _ (outside G hG).1 (outside G hG).2)
  exact ⟨out.1,out.2.1,out.2.2.1,fun q qr qy=>(out.2.2.2 q qr qy).trans (h.2.2 q qr qy)⟩



end ECDSAAdd.Entrant.JointInverse1588

namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum
  EntryRetained5 FirstInverse5 Challenge Baselines
attribute [local irreducible] wires

theorem recoverParityHD_drop (L : Layout) (hw : L.Widths) (J : Wire) :
    DeadCarry.DropRel (recoverParityH L J) (recoverParityHD L J) := by
  have r := (positiveParityHD_drop L hw J).ctx [.X J] [.X J]
  simpa only [recoverParityH,recoverParityHD,List.append_assoc] using r

theorem clearParityHD_drop (L : Layout) (hw : L.Widths) (J : Wire) :
    DeadCarry.DropRel (clearParityH L J) (clearParityHD L J) :=
  (recoverParityHD_drop L hw J).right [.CX (L.ylow.getD 0 0) L.parity]

theorem clearHD_drop (L : Layout) (hw : L.Widths) (J : Wire) :
    DeadCarry.DropRel (clearH L J) (clearHD L J) :=
  ((clearParityHD_drop L hw J).rename (Equiv.swap (cLo L) L.one)).rename (Equiv.swap (cHi L) L.sign)

theorem programHD_drop (L : Layout) (hw : L.Widths) (J B : Wire) :
    DeadCarry.DropRel (programH L J B) (programHD L J B) := by
  have r := (clearHD_drop L hw J).left (restoreAt L J B++affineH L J B++CleanInverse5.inverse (prepare L J B))
  simpa only [programH,programHD,List.append_assoc] using r

theorem jointHD_drop (L : BalancedCircuit.Layout) (hw : L.Widths) (J G : Wire) :
    DeadCarry.DropRel (jointH L J G) (jointHD L J G) := by
  have r := (programHD_drop L hw J G).ctx [.X G] [.X G]
  simpa only [jointH,jointHD,List.append_assoc] using r

def kernelD : Program :=
  renameProgram (Equiv.swap (base 719) (base 1032)) (jointHD portsJ (base 1028) (base 1))

def paddedD : Program := kernelD++padding

theorem paddedD_drop : DeadCarry.DropRel padded paddedD := by
  have r := ((jointHD_drop portsJ portsJ_widths (base 1028) (base 1)).rename (Equiv.swap (base 719) (base 1032))).left padding
  exact r

theorem paddedD_counts : toffoliCount paddedD=517 ∧ measurementCount paddedD=1279 := by
  have h := paddedD_drop
  have c := padded_counts
  have a := h.toffoli
  have b := h.meas
  exact ⟨by omega,by omega⟩

theorem paddedD_slots : gateSlots paddedD≤10514 := by
  have h := paddedD_drop.slots
  have c := padded_slots
  omega

theorem paddedD_physical : GatePhysical paddedD := paddedD_drop.physical padded_physical

theorem paddedD_support : wires paddedD⊆kernelSites := by
  rw [paddedD_drop.wires]; exact padded_support

theorem paddedD_free (i : Nat) (hi : i=0 ∨ i=516 ∨ i=719 ∨ i=1541) : base i∉wires paddedD := by
  rw [paddedD_drop.wires]; exact padded_free i hi

theorem paddedD_760_free : base 760∉wires paddedD := by
  rw [paddedD_drop.wires]; exact padded_760_free

def savingD (divide : Bool) : Nat := if divide then 0 else 503

theorem paddedD_pair (st : BasisState) (clean : ∀q∈BalancedCircuit.work portsJ,st q=false)
    (sign : st (base 2409)=false) (hole : st (base 1032)=false) (Z : Fp) :
    Triple (PairFrame portsJ.r portsJ.y st
      (centerWord ((if st (base 1028) && !st (base 1) then -Z else Z)/2))
      (centerWord (if st (base 1028) then Z else 0))) paddedD
      (PairFrame portsJ.r portsJ.y st (centerWord Z) 0) := by
  have j := jointHD_pair portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup st clean
    (by simpa [portsJ_eq] using sign) Z
  intro s m input
  have a719 := off_data 719 (by omega) (by omega)
  have a1032 := off_data 1032 (by omega) (by omega)
  have a512 := off_data 512 (by omega) (by omega)
  let mk := m.take (measurementCount kernelD)
  have out := j s mk input
  have in719 : s.basis (base 719)=false :=
    (input.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have in1032 : s.basis (base 1032)=false := (input.2.2 _ a1032.1 a1032.2).trans hole
  have o719 : (run (jointHD portsJ (base 1028) (base 1)) mk s).basis (base 719)=false :=
    (out.2.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have o1032 : (run (jointHD portsJ (base 1028) (base 1)) mk s).basis (base 1032)=false :=
    (out.2.2.2 _ a1032.1 a1032.2).trans hole
  have k : run kernelD mk s=run (jointHD portsJ (base 1028) (base 1)) mk s :=
    rebind_swap_run _ _ _ s mk in719 in1032 o719 o1032
  have o512 : (run (jointHD portsJ (base 1028) (base 1)) mk s).basis (base 512)=false :=
    (out.2.2.2 _ a512.1 a512.2).trans (clean _ (carry_work 512 (by omega)))
  have shape : run paddedD m s=run (jointHD portsJ (base 1028) (base 1)) mk s := by
    rw [paddedD,run_append,k,padding]
    exact pad_run (base 512) 506 _ _ o512
  rw [shape]
  exact out

end ECDSAAdd.Entrant.JointInverse1588

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588
attribute [local irreducible] run

def clearFD (L : Layout) (J : Wire) : Program := JointInverse1588.clearHD L J

theorem clearF_eq_clearH (L : Layout) (J : Wire) : clearF L J = JointInverse1588.clearH L J := rfl

def programFD (L : Layout) (J B : Wire) : Program :=
  prepare L J B++arithH L J B++eraseScalarsAt L J B++clearFD L J

/-- The final parity clear with carries #4 and #254 on the cleared `one` and `sign` (and carry #248 on
`rmsb`) runs as the record's `clearParity` on every state reached by the forward prefix and the scalar
erasure. -/
theorem tail_eqD (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (t1 t2 n : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    run (clearFD L J) n (run (eraseScalarsAt L J B) t2 (run (prefixProgram L J B) t1 s))=
      run (clearParity L J) n (run (eraseScalarsAt L J B) t2 (run (prefixProgram L J B) t1 s)) := by
  have pref := prefix_spec L hw hn J B hJ hB hJB Jv Bv Y hy s t1 hR hY hc hz hj hb
  generalize hbdef : run (prefixProgram L J B) t1 s=b at pref ⊢
  have dd : b.basis L.one=(b.basis L.parity && b.basis (lowY L)) := by
    rw [pref.parity,pref.u]
    exact pref.d
  have ee : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)) := by
    rw [pref.a,pref.u]
    exact pref.e
  have uu : b.basis (lowY L)=(b.basis J && b.basis B) := by rw [pref.u,pref.j,pref.b]
  have aa:=scalar_erase_relation L hw Jv Bv Y hy b.basis pref.target pref.parity pref.a pref.d
  generalize hcdef : run (eraseScalarsAt L J B) t2 b=c
  have erased : c=⟨b.phase,erasedBasis L.parity L.lower L.one L.sign (lowY L) J b.basis⟩ := by
    rw [←hcdef]
    exact eraseScalarsAt_run L hw hn J B hJ hB hJB b t2 ee aa dd uu
  have en:=erasePorts_nodup L hw hn J B hJ hB hJB
  have nd:=allND L hn
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have data : (L.r++L.y++L.carry).Nodup := (List.nodup_append'.mp nd).2.1
  have ry : (L.r++L.y).Nodup := (List.nodup_append'.mp data).1
  have rdy := (List.nodup_append'.mp ry).2.2
  have dyc := (List.nodup_append'.mp data).2.2
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r++L.y++L.carry := by
    have mem : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢
      tauto
    exact flagAway L hn q mem
  have cSame (q : Wire) (hq : q∈L.r++L.carry) : c.basis q=b.basis q := by
    have qdata : q∈L.r++L.y++L.carry := by
      simp only [List.mem_append] at hq ⊢
      tauto
    have qu : q≠lowY L := by
      intro eq
      rcases List.mem_append.mp hq with qr|qc
      · exact List.disjoint_left.mp rdy qr (eq.symm ▸ y0)
      · exact List.disjoint_left.mp dyc (List.mem_append_right _ y0) (eq ▸ qc)
    have qf (f : Wire) (hf : f∈[L.parity,L.lower,L.one,L.sign]) : q≠f := fun e=>flag f hf (e ▸ qdata)
    rw [erased]
    exact erasedBasis_frame _ _ _ _ _ _ _ q (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      exact not_or_intro (qf _ (by simp)) (not_or_intro (qf _ (by simp))
        (not_or_intro (qf _ (by simp)) qu)))
  have cR : regValue L.r c.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) :=
    (regValue_congr _ _ _ (fun q hq=>cSame q (List.mem_append_left _ hq))).trans pref.target
  have cCarry : ∀q∈L.carry,c.basis q=false := fun q hq=>
    (cSame q (List.mem_append_right _ hq)).trans (pref.carry q hq)
  have ca : c.basis L.lower=false := by
    have ne : L.lower≠lowY L := by
      intro e;exact flag L.lower (by simp) (by simp [e,y0])
    have ad : L.lower≠L.one := by
      have h:=List.nodup_iff_count.mp en L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,ne,ad]
  have bounds:=signedY_bounds (Jv && Bv) Y hy
  have rc : Centered (halfResult (signedY (Jv && Bv) Y)) := by
    apply (halfResult_spec _ ?_).1
    have hp:=constants
    unfold Centered at bounds
    omega
  have notU (q : Wire) (hq : q=L.one ∨ q=L.sign) : q≠lowY L := by
    intro e
    have f := flagAway L hn q (by rcases hq with rfl|rfl <;> simp)
    exact f (by rw [e];simp [y0])
  have cOne : c.basis L.one=false := by
    rw [erased]
    simp [erasedBasis,writeBit,notU L.one (Or.inl rfl)]
  have cSign : c.basis L.sign=false := by
    have sa : L.sign≠L.lower := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    have sd : L.sign≠L.one := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,notU L.sign (Or.inr rfl),sa,sd]
  exact JointInverse1588.clearHD_eq L hw hn J hJ _ rc c n cR ca cCarry cOne cSign

/-- The hosted forward program runs as `EntryRetained5.program` on the entry frame, for a
re-aligned record list. -/
theorem programF_eqD (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    ∃m',run (programFD L J B) m s=run (EntryRetained5.program L J B) m' s := by
  let Pre := prepare L J B++pre4 L
  let Q := loanF L J B
  let Post := post4 L++eraseScalarsAt L J B++clearFD L J
  have shapeF : programFD L J B=Pre++Q++Post := by
    simp only [programFD,arithH,Pre,Q,Post,List.append_assoc]
  have prep := prepare_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  have pc := prepare_counts L hw J B
  have preRun : run Pre [] s=run (pre4 L) [] (run (prepare L J B) [] s) := by
    simp only [Pre,run_append,List.take_nil,List.drop_nil]
  have hpre : measurementCount Pre=0 := by
    simp only [Pre,measurementCount_append,pc.2,(pre4_counts L).2]
  have stepA := context_eq Pre (inner L) Q Post 3 s m hpre (loanF_counts L J B).2 (by
    intro r
    rw [preRun]
    exact loanF_run L hw hn J B hJ hB hJB _ r
      (by rw [prep.a,prep.u];exact prep.e)
      (by rw [prep.u,prep.j,prep.b])
      prep.carry)
  refine ⟨(m.drop 3).take (measurementCount (inner L))++m.drop (measurementCount Q),?_⟩
  rw [shapeF,stepA]
  generalize (m.drop 3).take (measurementCount (inner L))++m.drop (measurementCount Q)=n
  have shape1 : Pre++inner L++Post=(prefixProgram L J B++eraseScalarsAt L J B)++clearFD L J := by
    simp only [Pre,Post,prefixProgram,arithmetic,add_split L hw,List.append_assoc]
  have shape2 : EntryRetained5.program L J B=
      (prefixProgram L J B++eraseScalarsAt L J B)++clearParity L J := rfl
  rw [shape1,shape2,run_append,run_append (prefixProgram L J B++eraseScalarsAt L J B),
    run_append (prefixProgram L J B)]
  exact tail_eqD L hw hn J B hJ hB hJB Jv Bv Y hy s _ _ _ hR hY hc hz hj hb

end ECDSAAdd.Entrant.JointForward1588

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588 Secp256k1

def jointFD (L : BalancedCircuit.Layout) (J G : Wire) : Program :=
  [.X G]++programFD L J G++[.X G]


theorem outside_layoutFD (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q ∉ L.wires) : q ∉ L.r ∧ q ∉ L.y ∧ q ∉ BalancedCircuit.work L := by
  have zero := List.count_eq_zero.mpr hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    List.count_append,List.count_cons,List.count_nil] at zero
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at pos
    omega
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at pos
    omega
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at pos
    omega

/-- The hosted forward joint runs as `FrontierEntry.joint` on the entry frame. -/
theorem jointF_eqD (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J,G].Nodup)
    (Jv Gv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 Y)
    (hY : regValue L.y s.basis = 0)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false)
    (sign : s.basis L.sign=false) (j : s.basis J=Jv) (g : s.basis G=Gv) :
    ∃m',run (jointFD L J G) m s=run (FrontierEntry.joint L J G) m' s := by
  have apart : J≠G := fun eq => (List.nodup_cons.mp hJG).1 (List.mem_singleton.mpr eq)
  have away := outside_layoutFD L G hG
  let a : State := ⟨s.phase,writeBit s.basis G (!s.basis G)⟩
  have head : run [Instr.X G] [] s=a := rfl
  have keep (q : Wire) (hq : q≠G) : a.basis q=s.basis q := by
    simp only [a,writeBit,Function.update_of_ne hq]
  have aR : regValue L.r a.basis=encodeWord 256 Y :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.1 (eq ▸ hq)))).trans hR
  have aY : regValue L.y a.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.2.1 (eq ▸ hq)))).trans hY
  have ac : ∀q∈BalancedCircuit.work L,a.basis q=false := by
    intro q hq
    exact (keep q (fun eq => away.2.2 (eq ▸ hq))).trans (clean q hq)
  have sign_mem : L.sign∈L.wires := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have sg : L.sign≠G := fun eq => hG (eq ▸ sign_mem)
  have aj : a.basis J=Jv := (keep J apart).trans j
  have ag : a.basis G= !Gv := by simp only [a,writeBit,Function.update_self,g]
  obtain ⟨m',h⟩ := programF_eqD L hw hn J G hJ hG hJG Jv (!Gv) Y hy a m aR aY ac
    ((keep _ sg).trans sign) aj ag
  refine ⟨m',?_⟩
  rw [jointFD,xwrap_run,FrontierEntry.joint,xwrap_run,head,h]

/-- `(Z, 0) ↦ ((±Z)/2, J ? Z : 0)`: the first selector swap and the G1 half of the divide replay. -/
theorem jointF_pairD (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (origin : BasisState) (clean : ∀q∈work L,origin q=false) (sign : origin L.sign=false)
    (Z : Fp) :
    Triple (PairFrame L.r L.y origin (centerWord Z) 0) (jointFD L J G)
      (PairFrame L.r L.y origin
        (centerWord ((if origin J && !origin G then -Z else Z)/2))
        (centerWord (if origin J then Z else 0))) := by
  have outside (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
  have sf:=flagAway L hn L.sign (by simp)
  have sa : L.sign∉L.r ∧ L.sign∉L.y :=
    ⟨fun bad=>sf (by simp [bad]),fun bad=>sf (by simp [bad])⟩
  intro s m h
  have hc : ∀q∈work L,s.basis q=false := fun q hq=>
    (h.2.2 q (work_no_data L hn q hq).1 (work_no_data L hn q hq).2).trans (clean q hq)
  have ss : s.basis L.sign=false := (h.2.2 _ sa.1 sa.2).trans sign
  have sj : s.basis J=origin J := h.2.2 _ (outside J hJ).1 (outside J hJ).2
  have sg : s.basis G=origin G := h.2.2 _ (outside G hG).1 (outside G hG).2
  obtain ⟨m',eq⟩ := jointF_eqD L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m h.1 h.2.1 hc ss sj sg
  have out := FrontierEntry.joint_frame L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m' h.1 h.2.1 hc ss sj sg
  dsimp only at out
  rw [unary_half,source_word] at out
  rw [eq]
  exact ⟨out.1,out.2.1,out.2.2.1,fun q qr qy=>(out.2.2.2 q qr qy).trans (h.2.2 q qr qy)⟩

theorem clearFD_drop (L : Layout) (hw : L.Widths) (J : Wire) :
    DeadCarry.DropRel (clearF L J) (clearFD L J) := clearHD_drop L hw J

theorem programFD_drop (L : Layout) (hw : L.Widths) (J B : Wire) :
    DeadCarry.DropRel (programF L J B) (programFD L J B) := by
  have r := (clearFD_drop L hw J).right (prepare L J B++arithH L J B++eraseScalarsAt L J B)
  simpa only [programF,programFD,List.append_assoc] using r

theorem jointFD_drop (L : BalancedCircuit.Layout) (hw : L.Widths) (J G : Wire) :
    DeadCarry.DropRel (jointF L J G) (jointFD L J G) := by
  have r := (programFD_drop L hw J G).ctx [.X G] [.X G]
  simpa only [jointF,jointFD,List.append_assoc] using r

end ECDSAAdd.Entrant.JointForward1588
