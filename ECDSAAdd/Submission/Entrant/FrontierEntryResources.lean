import ECDSAAdd.Submission.Entrant.FrontierEntryLayoutHelpers
import ECDSAAdd.Baselines.SlotSignedSquare
import ECDSAAdd.Submission.Entrant.FrontierEntryLayout
import ECDSAAdd.Arithmetic.CompactWalkPhysical
import ECDSAAdd.Baselines.SlotNativeFirst
import ECDSAAdd.Baselines.SlotSignedInteger

set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic Challenge RecordedQuantum Baselines BalancedCircuit

namespace Affine

theorem fan_slots (qs : List Wire) (a : Wire) : gateSlots (fan qs a) = qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change 1 + gateSlots (fan qs a) = qs.length + 1
    rw [ih]
    omega

def slotCost : List Bit → Nat
  | [] => 0
  | [b] => b.terms.length+2
  | b::b'::bs => 5*b.terms.length+12+slotCost (b'::bs)

theorem local_slots (b : Bit) (y cin co : Wire) :
    gateSlots (majority b y cin co) = 2*b.terms.length+6 ∧
    gateSlots (erase b y cin co) = 2*b.terms.length+4 ∧
    gateSlots (sum b y cin) = b.terms.length+2 := by
  simp only [majority,erase,sum,view,gateSlots_append,reverse_gateSlots,fan_slots,
    Bit.wires,List.length_cons]
  norm_num [Arithmetic.majority,eraseCarry,gateSlots,instructionSlots]
  omega

theorem add_slots (bs : List Bit) (ys carry : List Wire) (cin : Wire)
    (hl : bs.length = ys.length) (hc : carry.length+1 = ys.length) :
    gateSlots (add bs ys carry cin) = slotCost bs := by
  induction bs generalizing ys carry cin with
  | nil => have h : ys = [] := List.eq_nil_of_length_eq_zero hl.symm; simp [add,h,slotCost,gateSlots]
  | cons b bs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      cases bs with
      | nil =>
        have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        subst ys
        simpa only [add,slotCost] using (local_slots b y cin cin).2.2
      | cons b' bs =>
        cases ys with
        | nil => simp at hl
        | cons y' ys =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have rest := ih (y'::ys) cs c (by simpa using hl) (by simpa using hc)
            simp only [add,gateSlots_append,slotCost] at rest ⊢
            rw [(local_slots b y cin c).1,(local_slots b y cin c).2.1,
              (local_slots b y cin c).2.2,rest]
            omega

def lengthCost : List Nat → Nat
  | [] => 0
  | [k] => k+2
  | k::k'::ks => 5*k+12+lengthCost (k'::ks)

theorem slotCost_lengths (bs : List Bit) :
    slotCost bs = lengthCost (bs.map (fun b => b.terms.length)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases bs with
    | nil => rfl
    | cons b' bs => simp only [slotCost,List.map_cons,lengthCost,ih]


theorem fan_support_to (qs : List Wire) (a : Wire) (W : Finset Wire)
    (ha : a ∈ W) (hs : ∀ q ∈ qs, q ∈ W) : wires (fan qs a) ⊆ W := by
  intro q hq
  have h := fan_support qs a hq
  simp only [List.mem_toFinset,List.mem_cons] at h
  rcases h with rfl | h
  · exact ha
  · exact hs q h

theorem local_support (b : Bit) (y cin co : Wire) (W : Finset Wire)
    (hs : ∀ q ∈ b.wires, q ∈ W) (hy : y ∈ W) (hc : cin ∈ W) (ho : co ∈ W) :
    wires (majority b y cin co) ⊆ W ∧ wires (erase b y cin co) ⊆ W ∧
      wires (sum b y cin) ⊆ W := by
  have ha := hs b.wire (by simp [Bit.wires])
  have hv := fan_support_to b.terms b.wire W ha (fun q hq => hs q (by simp [Bit.wires,hq]))
  have hm : wires (Arithmetic.majority b.wire y cin co) ⊆ W := by
    simp [Arithmetic.majority,wires,Instr.wires,Finset.union_subset_iff,
      Finset.insert_subset_iff,ha,hy,hc,ho]
  have he : wires (eraseCarry b.wire y cin co) ⊆ W := by
    simp [eraseCarry,wires,Instr.wires,correctionWires,Finset.union_subset_iff,
      Finset.insert_subset_iff,ha,hy,hc,ho]
  have hf := fan_support_to b.wires y W hy hs
  have cx : wires [Instr.CX cin y] ⊆ W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,hc,hy]
  simp only [majority,erase,sum,view,wires_append,wires_reverse,Finset.union_subset_iff]
  exact ⟨⟨⟨hv,hm⟩,hv⟩,⟨⟨hv,he⟩,hv⟩,⟨hf,cx⟩⟩

theorem add_support_to (bs : List Bit) (ys carry : List Wire) (cin : Wire)
    (W : Finset Wire) (hs : ∀ q ∈ sites bs, q ∈ W)
    (hy : ∀ q ∈ ys, q ∈ W) (hc : ∀ q ∈ carry, q ∈ W) (hi : cin ∈ W) :
    wires (add bs ys carry cin) ⊆ W := by
  induction bs generalizing ys carry cin with
  | nil => simp [add,wires]
  | cons b bs ih =>
    have head (q : Wire) (hq : q ∈ b.wires) : q ∈ W := hs q (head_mem b bs q hq)
    cases bs with
    | nil =>
      cases ys with
      | nil => simp [add,wires]
      | cons y ys =>
        cases ys with
        | nil => exact (local_support b y cin cin W head (hy y (by simp)) hi hi).2.2
        | cons y' ys => simp [add,wires]
    | cons b' bs =>
      cases ys with
      | nil => simp [add,wires]
      | cons y ys =>
        cases ys with
        | nil => simp [add,wires]
        | cons y' ys =>
          cases carry with
          | nil => simp [add,wires]
          | cons c cs =>
            have rest := ih (y'::ys) cs c
              (fun q hq => hs q (tail_mem b (b'::bs) q hq))
              (fun q hq => hy q (by simp [hq]))
              (fun q hq => hc q (by simp [hq])) (hc c (by simp))
            have stepRes := local_support b y cin c W head (hy y (by simp)) hi (hc c (by simp))
            simp only [add,wires_append,Finset.union_subset_iff]
            exact ⟨⟨⟨stepRes.1,rest⟩,stepRes.2.1⟩,stepRes.2.2⟩


theorem fan_physical (qs : List Wire) (a : Wire) (ha : a ∉ qs) : GatePhysical (fan qs a) := by
  intro i hi
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
  exact fun e => ha (e ▸ hq)

private theorem reverse_physical (p : Program) (hp : GatePhysical p) : GatePhysical p.reverse := by
  intro i hi
  exact hp i (List.mem_reverse.mp hi)

theorem local_physical (b : Bit) (hb : b.Valid) (y cin co : Wire)
    (hn : [y,cin,co].Nodup) (ha : ∀ q ∈ b.wires, q ∉ [y,cin,co]) :
    GatePhysical (majority b y cin co) ∧ GatePhysical (erase b y cin co) ∧
      GatePhysical (sum b y cin) := by
  have hv : GatePhysical (view b) := fan_physical b.terms b.wire hb
  have hr := reverse_physical (view b) hv
  have nd : [b.wire,y,cin,co].Nodup := List.nodup_cons.mpr
    ⟨ha b.wire (by simp [Bit.wires]),hn⟩
  have hc : cin ≠ y := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
  have hf := fan_physical b.wires y (fun h => ha y h (by simp))
  have cx : GatePhysical [Instr.CX cin y] := by simpa [GatePhysical,PhysicalInstr,ProperGate] using hc
  simp only [majority,erase,sum,gatePhysical_append]
  exact ⟨⟨⟨hv,majority_physical _ _ _ _ nd⟩,hr⟩,
    ⟨⟨hv,eraseCarry_physical _ _ _ _⟩,hr⟩,⟨hf,cx⟩⟩

theorem add_physical (bs : List Bit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin :: (ys ++ carry)).Nodup)
    (hs : ∀ q ∈ sites bs, q ∉ cin :: (ys ++ carry))
    (hv : ∀ b ∈ bs, b.Valid) : GatePhysical (add bs ys carry cin) := by
  induction bs generalizing ys carry cin with
  | nil => simp [add,GatePhysical]
  | cons b bs ih =>
    have hb := hv b (by simp)
    have head (q : Wire) (hq : q ∈ b.wires) := hs q (head_mem b bs q hq)
    cases bs with
    | nil =>
      cases ys with
      | nil => simp [add,GatePhysical]
      | cons y ys =>
        cases ys with
        | cons y' ys => simp [add,GatePhysical]
        | nil =>
          have ci : cin ≠ y := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
          have yf : y ∉ b.wires := fun h => head y h (by simp)
          simp only [add,sum,gatePhysical_append]
          exact ⟨fan_physical b.wires y yf,by simpa [GatePhysical,PhysicalInstr,ProperGate] using ci⟩
    | cons b' bs =>
      cases ys with
      | nil => simp [add,GatePhysical]
      | cons y ys =>
        cases ys with
        | nil => simp [add,GatePhysical]
        | cons y' ys =>
          cases carry with
          | nil => simp [add,GatePhysical]
          | cons c cs =>
            have nd : [y,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have away (q : Wire) (hq : q ∈ b.wires) (bad : q ∈ [y,cin,c]) : False := by
              apply head q hq
              simp only [List.mem_cons,List.not_mem_nil,or_false] at bad
              rcases bad with rfl | rfl | rfl <;> simp
            have nr : (c :: ((y'::ys) ++ cs)).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            have sr (q : Wire) (hq : q ∈ sites (b'::bs)) : q ∉ c :: ((y'::ys) ++ cs) := by
              intro bad
              apply hs q (tail_mem b (b'::bs) q hq)
              rcases List.mem_cons.mp bad with rfl | bad
              · simp
              · rcases List.mem_append.mp bad with hy | hc
                · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_cons_of_mem _ hy))
                · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hc))
            have rest := ih (y'::ys) cs c nr sr (fun k hk => hv k (by simp [hk]))
            have stepRes := local_physical b hb y cin c nd away
            simp only [add,gatePhysical_append]
            exact ⟨⟨⟨stepRes.1,rest⟩,stepRes.2.1⟩,stepRes.2.2⟩

end Affine

private def termLength (i : Nat) : Nat :=
  if i=3 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=31 ∨ i=255 then 2 else 1

private theorem source_lengths (L : Layout) :
    (sources L).map (fun b => b.terms.length) = (List.range 256).map termLength := by
  simp only [sources,List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply,source,termLength]
  split_ifs <;> simp_all
  all_goals omega

private theorem source_length_cost :
    Affine.lengthCost ((List.range 256).map termLength) = 4369 := by decide +kernel

theorem arithmetic_slots (L : Layout) (hw : L.Widths) : gateSlots (arithmetic L) = 4369 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h := Affine.add_slots (sources L) L.r (L.carry.take 255) (lowY L)
    (by rw [sources_length,len.2.1]) (by simp [List.length_take,hw.2.2,len.2.1])
  have cost : Affine.slotCost (sources L) = 4369 := by
    rw [Affine.slotCost_lengths,source_lengths]
    exact source_length_cost
  exact h.trans cost


def retSites (L : Layout) (J B : Wire) : Finset Wire :=
  (L.r ++ L.y ++ L.carry.take 255 ++ [L.parity,L.lower,L.one,L.sign,J,B]).toFinset

theorem program_support (L : Layout) (hw : L.Widths) (J B : Wire) :
    wires (program L J B) ⊆ retSites L J B := by
  let W := retSites L J B
  have data (q : Wire) (hq : q ∈ L.r ++ L.y ++ L.carry.take 255) : q ∈ W := by
    simp only [W,retSites,List.mem_toFinset,List.mem_append] at hq ⊢
    exact Or.inl hq
  have scalar (q : Wire) (hq : q ∈ [L.parity,L.lower,L.one,L.sign,J,B]) : q ∈ W := by
    exact List.mem_toFinset.mpr (List.mem_append_right _ hq)
  have hp := scalar L.parity (by simp)
  have ha := scalar L.lower (by simp)
  have hd := scalar L.one (by simp)
  have he := scalar L.sign (by simp)
  have hj := scalar J (by simp)
  have hb := scalar B (by simp)
  have r (q : Wire) (hq : q ∈ L.r) : q ∈ W := data q (by simp [hq])
  have y (q : Wire) (hq : q ∈ L.y) : q ∈ W := data q (by simp [hq])
  have c (q : Wire) (hq : q ∈ L.carry.take 255) : q ∈ W := data q (by simp [hq])
  have r0 := r L.r0 (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
  have rh := r L.rmsb (by simp [BalancedCleanup.Layout.r])
  have yu : lowY L ∈ L.y := by rw [y_cons L hw]; simp
  have u := y (lowY L) yu
  have ul : L.ylow[0]?.getD 0 ∈ W := u
  have len := BalancedCleanup.widths L.toLayout hw
  have idx : 254 < L.r.length := by rw [len.2.1]; decide
  have ri := r (L.r.getD 254 0) (by rw [List.getD_eq_getElem _ _ idx]; exact List.getElem_mem _)
  have riAlt : L.r[254]?.getD 0 ∈ W := ri
  have cp : wires (copyRegister (some J) L.r.tail L.y.tail) ⊆ W := by
    rw [copyRegister_wires _ _ _ (by simp [len.2.1,len.2.2.1])]
    split
    · exact Finset.empty_subset _
    · intro q hq
      simp only [List.mem_toFinset,List.mem_append,Option.toList_some,List.mem_singleton] at hq
      rcases hq with (rfl | hq) | hq
      · exact hj
      · exact r q (List.mem_of_mem_tail hq)
      · exact y q (List.mem_of_mem_tail hq)
  have rot : wires (rotateRight L.r) ⊆ W := by
    rw [(rotate_wires L.r).1,if_neg (by rw [len.2.1]; omega)]
    exact fun q hq => r q (List.mem_toFinset.mp hq)
  have comp (ctl : Wire) (hctl : ctl ∈ W) : wires (signComplement ctl L.r) ⊆ W := by
    intro q hq
    have h := signComplement_wires_subset ctl L.r hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with rfl | h
    · exact hctl
    · exact r q h
  have first : wires [Instr.CCX J B (lowY L)] ⊆ W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,hj,hb,u]
  have seeds : wires [Instr.CX L.r0 L.parity,Instr.CCX L.parity L.rmsb L.lower,
      Instr.CCX L.parity (lowY L) L.one,Instr.CCX L.lower (lowY L) L.sign,
      Instr.CX L.parity L.r0] ⊆ W := by
    simp [wires,Instr.wires,Finset.union_subset_iff,Finset.insert_subset_iff,r0,rh,hp,ha,hd,he,u]
  have extend : wires [Instr.CX (L.r.getD 254 0) L.rmsb] ⊆ W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,ri,riAlt,rh]
  have prep : wires (prepare L J B) ⊆ W := by
    simpa only [prepare,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro (And.intro (And.intro (And.intro first cp) seeds) rot) extend) (comp _ u)
  have arith : wires (arithmetic L) ⊆ W := Affine.add_support_to _ _ _ _ W
    (fun q hq => scalar q (by
      have h := sources_sites L q hq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      rcases h with rfl | rfl | rfl | rfl <;> simp)) r c u
  have erase : wires (eraseScalarsAt L J B) ⊆ W := by
    simp [eraseScalarsAt,eraseScalars,wires,Instr.wires,correctionWires,
      Finset.union_subset_iff,Finset.insert_subset_iff,hp,ha,hd,he,u,ul,hj,hb,rh,lowY]
  have mag : wires (EntryHalf5.prepareMagnitude L) ⊆ W := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,wires_append,
      Finset.union_subset_iff]
    exact ⟨by simp [wires,Instr.wires,Finset.insert_subset_iff,rh,ha],comp _ ha⟩
  have carry : wires (EntryHalf5.parityCarry L J) ⊆ W := by
    apply (DiagonalCarry5.support EntryHalf5.parityBits L.low (L.carry.take 255) L.lower J L.parity
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | hq | hq
    · exact hj
    · exact hp
    · exact ha
    · exact r q (List.mem_append_left _ hq)
    · exact c q hq
  have parity : wires (clearParity L J) ⊆ W := by
    simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,
      wires_append,wires_reverse,Finset.union_subset_iff]
    refine ⟨?_,⟨⟨?_,⟨mag,⟨carry,mag⟩⟩⟩,?_⟩⟩
    · simp [wires,Instr.wires,Finset.insert_subset_iff,u,ul,hp,lowY]
    · simp [wires,Instr.wires,Finset.insert_subset_iff,hj]
    · simp [wires,Instr.wires,Finset.insert_subset_iff,hj]
  simpa only [program,prefixProgram,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro prep arith) erase) parity


private theorem high_copy_ne (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.r.getD 254 0 ≠ L.rmsb := by
  have len := BalancedCleanup.widths L.toLayout hw
  have idx : 254 < L.r.length := by rw [len.2.1]; decide
  have split := List.take_succ_eq_append_getElem idx
  have take : L.r.take 255 = L.low := by
    change (L.low ++ [L.rmsb]).take 255 = L.low
    rw [←len.1,List.take_left]
  rw [show 254+1=255 from rfl,take] at split
  have member : L.r.getD 254 0 ∈ L.low := by
    rw [split,List.getD_eq_getElem _ _ idx]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have nd := EntryHalf5.target_nodup L hn
  have apart := (List.nodup_append'.mp nd).2.2
  exact fun e => List.disjoint_left.mp apart (e ▸ member) (by simp)

theorem program_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J,B].Nodup) :
    GatePhysical (program L J B) := by
  have nd := erasePorts_nodup L hw hn J B hJ hB hJB
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
    ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
  have uD : L.ylow[0]?.getD 0 ≠ L.one := Ne.symm dU
  have uE : L.ylow[0]?.getD 0 ≠ L.sign := Ne.symm eU
  have jU : J ≠ L.ylow[0]?.getD 0 := Ne.symm uJ
  have pUnorm : L.parity ≠ L.ylow[0]?.getD 0 := pU
  have r0mem : L.r0 ∈ L.r := by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
  have p0 : L.parity ≠ L.r0 := fun e => flagAway L hn L.parity (by simp)
    (by simp [e,r0mem])
  have uAway : lowY L ∉ L.r := fun h =>
    (List.nodup_cons.mp (arithmeticND L hw hn)).1 (List.mem_append_left _ h)
  have first : GatePhysical [Instr.CCX J B (lowY L)] := by
    simpa [GatePhysical,PhysicalInstr,ProperGate,lowY] using And.intro (Ne.symm uJ) (Ne.symm uB)
  have cp : GatePhysical (copyRegister (some J) L.r.tail L.y.tail) :=
    copyRegister_physical _ _ _ (copyND L hn) (by
      intro q hq hy
      have eq : J = q := by simpa using hq
      subst q
      exact hJ (data_member L J (by simp [List.mem_of_mem_tail hy])))
  have seeds : GatePhysical [Instr.CX L.r0 L.parity,Instr.CCX L.parity L.rmsb L.lower,
      Instr.CCX L.parity (lowY L) L.one,Instr.CCX L.lower (lowY L) L.sign,
      Instr.CX L.parity L.r0] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,lowY,Ne.symm p0,p0,pA,Ne.symm aH,
      pD,Ne.symm dU,aE,Ne.symm eU,uD,uE]
  have rot := (rotate_physical L.r (EntryHalf5.target_nodup L hn)).1
  have extend : GatePhysical [Instr.CX (L.r.getD 254 0) L.rmsb] := by
    have h : L.r[254]?.getD 0 ≠ L.rmsb := high_copy_ne L hw hn
    simpa [GatePhysical,PhysicalInstr,ProperGate] using h
  have comp := signComplement_physical (lowY L) L.r uAway
  have prep : GatePhysical (prepare L J B) := by
    simpa only [prepare,gatePhysical_append] using
      And.intro (And.intro (And.intro (And.intro (And.intro first cp) seeds) rot) extend) comp
  have arith : GatePhysical (arithmetic L) := Affine.add_physical _ _ _ _
    (arithmeticND L hw hn) (sources_away L hw hn) (sources_valid L hn)
  have erase : GatePhysical (eraseScalarsAt L J B) := by
    simp [eraseScalarsAt,eraseScalars,GatePhysical,PhysicalInstr,ProperGate,pU,Ne.symm uJ,jU,pUnorm]
  have la : L.lower ∉ L.r := fun h => flagAway L hn L.lower (by simp) (by simp [h])
  have mag : GatePhysical (EntryHalf5.prepareMagnitude L) := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,gatePhysical_append]
    exact ⟨by simpa [GatePhysical,PhysicalInstr,ProperGate] using Ne.symm aH,
      signComplement_physical L.lower L.r la⟩
  have magRev : GatePhysical (EntryHalf5.prepareMagnitude L).reverse := by
    intro i hi
    exact mag i (List.mem_reverse.mp hi)
  have len := BalancedCleanup.widths L.toLayout hw
  have carry : GatePhysical (EntryHalf5.parityCarry L J) :=
    DiagonalCarry5.physical _ _ _ _ _ _ (EntryHalf5.carry_nodup L hn J hJ)
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
  have x : GatePhysical [Instr.X J] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  have parity : GatePhysical (clearParity L J) := by
    simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,gatePhysical_append]
    exact ⟨by simpa [GatePhysical,PhysicalInstr,ProperGate] using Ne.symm pU,
      ⟨⟨x,⟨mag,⟨carry,magRev⟩⟩⟩,x⟩⟩
  simpa only [program,prefixProgram,gatePhysical_append] using
    And.intro (And.intro (And.intro prep arith) erase) parity


theorem prepare_slots_le (L : Layout) (hw : L.Widths) (J B : Wire) :
    gateSlots (prepare L J B) ≤ 1286 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have rot := (rotate_gateSlots_le L.r).1
  rw [len.2.1] at rot
  have value : gateSlots (prepare L J B) = gateSlots (rotateRight L.r)+518 := by
    simp only [prepare,gateSlots_append,copyRegister_gateSlots,signComplement_gateSlots,
      len.2.1,len.2.2.1,List.length_tail,gateSlots_cons,gateSlots_nil,instructionSlots]
    omega
  rw [value]
  omega

theorem clearParity_slots_le (L : Layout) (hw : L.Widths) (J : Wire) :
    gateSlots (clearParity L J) ≤ 2303 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have mag : gateSlots (EntryHalf5.prepareMagnitude L) = 257 := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,gateSlots_append,
      gateSlots_cons,gateSlots_nil,instructionSlots,signComplement_gateSlots,len.2.1]
  have carry := DiagonalCarry5.slots_le EntryHalf5.parityBits L.low (L.carry.take 255)
    L.lower J L.parity
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
  have carry_bound : gateSlots (EntryHalf5.parityCarry L J) ≤ 1786 := by
    simpa only [EntryHalf5.parityCarry,EntryHalf5.parityBits,DiagonalCarry5.literal_length] using carry
  simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,gateSlots_append,
    reverse_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,mag]
  omega

theorem program_slots_le (L : Layout) (hw : L.Widths) (J B : Wire) :
    gateSlots (program L J B) ≤ 8000 := by
  have prep := prepare_slots_le L hw J B
  have arith := arithmetic_slots L hw
  have parity := clearParity_slots_le L hw J
  have erase : gateSlots (eraseScalarsAt L J B) = 11 := rfl
  simp only [program,prefixProgram,gateSlots_append]
  omega

theorem retSites_omits (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (q : Wire)
    (hq : q ∈ [L.sourceGuard,L.cout,L.minus,L.plus,EntryHalf5.lastCarry L]) :
    q ∉ retSites L J B := by
  have splitND :
      ([L.sourceGuard,L.cout,L.minus,L.plus,EntryHalf5.lastCarry L] ++
        [L.parity,L.lower,L.one,L.sign]).Nodup := by
    apply List.nodup_iff_count.mpr
    intro r
    have h := List.nodup_iff_count.mp (EntryHalf5.scalarPortsND L hw hn) r
    simp only [EntryHalf5.scalarPorts,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have flagAway := List.disjoint_left.mp (List.nodup_append'.mp splitND).2.2 hq
  have scalar : q ∈ EntryHalf5.scalarPorts L := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [EntryHalf5.scalarPorts]
  have dataAway := EntryHalf5.scalarAway L hw hn q scalar
  have member : q ∈ L.wires := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · exact data_member L (EntryHalf5.lastCarry L) (by simp [EntryHalf5.lastCarry_mem L hw])
  have jAway : q ≠ J := fun eq => hJ (eq ▸ member)
  have bAway : q ≠ B := fun eq => hB (eq ▸ member)
  intro bad
  simp only [retSites,List.mem_toFinset,List.mem_append] at bad
  rcases bad with ((r | y) | c) | flags
  · exact dataAway (by simp [r])
  · exact dataAway (by simp [y])
  · exact dataAway (by simp [c])
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at flags
    rcases flags with rfl | rfl | rfl | rfl | j | b
    all_goals first | exact jAway j | exact bAway b | exact flagAway (by simp)

theorem program_omits (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (q : Wire)
    (hq : q ∈ [L.sourceGuard,L.cout,L.minus,L.plus,EntryHalf5.lastCarry L]) :
    q ∉ wires (program L J B) :=
  fun bad => retSites_omits L hw hn J B hJ hB q hq (program_support L hw J B bad)

end ECDSAAdd.Entrant.EntryRetained5
