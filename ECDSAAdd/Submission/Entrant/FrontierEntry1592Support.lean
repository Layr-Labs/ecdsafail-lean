import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalEnvironment
import ECDSAAdd.Arithmetic.MappedCompressedAllocationSites
import ECDSAAdd.Submission.Entrant.FrontierEntryJointProgram
import ECDSAAdd.Submission.Entrant.G0CarryLoan5

/-! First-trit G0 hosts the retained entry's extra carry. No Eff selector is used. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum
attribute [local irreducible] run wires joint EntryRetained5.program

def loanPorts1592 : BalancedCircuit.Layout :=
  { r0:=base 2056,rtail:=wireBlock base 2057 254,rmsb:=base 2311,
    ylow:=wireBlock base 770 255,ymsb:=base 1025,
    carry:=wireBlock base 512 253++[base 1540,base 1541,base 1026],
    sign:=base 2409,parity:=base 768,lower:=base 1797,one:=base 1027,
    sourceGuard:=base 765,cout:=base 2312,minus:=base 767,plus:=base 766 }

theorem loanPorts1592_widths : loanPorts1592.Widths := by
  simp [BalancedCircuit.Layout.Widths,BalancedCleanup.Layout.Widths,loanPorts1592,wireBlock]

private theorem not_block (i a n : Nat) (sep : i < a ∨ a + n ≤ i) : base i∉wireBlock base a n := by
  intro used
  obtain ⟨k,hk,eq⟩:=List.mem_map.mp used
  simp only [List.mem_range'_1] at hk
  have same:=base_injective eq
  omega

def joint1592 : Program := G0CarryLoan5.program (base 1028) (base 0) (base 1541)
  (joint loanPorts1592 (base 1028) (base 1))

private theorem joint_support_generic (L : BalancedCircuit.Layout) (hw : L.Widths)
    (J G : Wire) : wires (joint L J G)⊆
    (L.r++L.y++L.carry++[L.parity,L.lower,L.one,L.sign,J,G]).toFinset := by
  let W:=(L.r++L.y++L.carry++[L.parity,L.lower,L.one,L.sign,J,G]).toFinset
  have x : wires [Instr.X G]⊆W := by
    intro q used
    have eq : q=G := by simpa [wires,Instr.wires] using used
    subst q
    simp [W]
  have core : wires (EntryRetained5.program L J G)⊆W := by
    intro q used
    have member:=List.mem_toFinset.mp (EntryRetained5.program_support L hw J G used)
    simp only [List.mem_append] at member
    simp only [W,List.mem_toFinset,List.mem_append]
    rcases member with ((r|y)|c)|flags
    · exact Or.inl (Or.inl (Or.inl r))
    · exact Or.inl (Or.inl (Or.inr y))
    · exact Or.inl (Or.inr (List.mem_of_mem_take c))
    · exact Or.inr flags
  rw [joint,wires_append,wires_append]
  exact Finset.union_subset (Finset.union_subset x core) x

private theorem joint_off (i : Nat) (hi : i=0 ∨ i=2410) :
    base i∉wires (joint loanPorts1592 (base 1028) (base 1)) := by
  intro used
  have member:=List.mem_toFinset.mp (joint_support_generic loanPorts1592
    loanPorts1592_widths (base 1028) (base 1) used)
  simp only [loanPorts1592,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,wireBlock,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_map,List.mem_range'_1,or_false,base_injective.eq_iff] at member
  rcases hi with rfl|rfl <;> omega

private theorem data_away (i : Nat) (hi : i=0 ∨ i=1028 ∨ i=1541) :
    base i∉loanPorts1592.r ∧ base i∉loanPorts1592.y := by
  have one (k : Nat) : wireBlock base k 1=[base k] := by simp [wireBlock,List.range']
  have r : loanPorts1592.r=wireBlock base 2056 256 := by
    change [base 2056]++(wireBlock base 2057 254++[base 2311])=wireBlock base 2056 256
    rw [←one 2311,wireBlock_append,←one 2056,wireBlock_append]
  have y : loanPorts1592.y=wireBlock base 770 256 := by
    change wireBlock base 770 255++[base 1025]=wireBlock base 770 256
    rw [←one 1025,wireBlock_append]
  rw [r,y]
  exact ⟨not_block i 2056 256 (by rcases hi with rfl|rfl|rfl <;> omega),
    not_block i 770 256 (by rcases hi with rfl|rfl|rfl <;> omega)⟩

/-- Both first-trit premises must be discharged from the actual caller trace. -/
theorem joint1592_eq (origin : BasisState) (env : OffsetBorrowedCanonical.Env base origin)
    (I V A B : Nat)
    (legal : (origin (base 0)).toNat+2*(origin (base 1028)).toNat<3)
    (nonzero : origin (base 0)=true ∨ origin (base 1028)=true)
    (correct : Triple (PairFrame loanPorts1592.r loanPorts1592.y origin I V)
      (joint loanPorts1592 (base 1028) (base 1))
      (PairFrame loanPorts1592.r loanPorts1592.y origin A B))
    (s : State) (m : List Bool) (input : PairFrame loanPorts1592.r loanPorts1592.y origin I V s.basis) :
    run joint1592 m s=run (joint loanPorts1592 (base 1028) (base 1)) m s := by
  have clean : origin (base 1541)=false := by
    apply (regValue_zero _ _).mp env.1
    have member : base 1541∈wireBlock base 1540 257 :=
      List.mem_map.mpr ⟨1541,by simp [List.mem_range'_1],rfl⟩
    simp only [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl member)))
  exact G0CarryLoan5.pair_frame_eq _ _ origin I V A B _ _ _ _
    (by intro e; have:=base_injective e; omega)
    (by intro e; have:=base_injective e; omega)
    (data_away 1028 (by simp)) (data_away 0 (by simp)) (data_away 1541 (by simp))
    (joint_off 0 (Or.inl rfl)) clean legal nonzero correct s m input

theorem joint1592_frame (origin : BasisState) (env : OffsetBorrowedCanonical.Env base origin)
    (I V A B : Nat)
    (legal : (origin (base 0)).toNat+2*(origin (base 1028)).toNat<3)
    (nonzero : origin (base 0)=true ∨ origin (base 1028)=true)
    (correct : Triple (PairFrame loanPorts1592.r loanPorts1592.y origin I V)
      (joint loanPorts1592 (base 1028) (base 1))
      (PairFrame loanPorts1592.r loanPorts1592.y origin A B)) :
    Triple (PairFrame loanPorts1592.r loanPorts1592.y origin I V) joint1592
      (PairFrame loanPorts1592.r loanPorts1592.y origin A B) := by
  intro s m input
  rw [joint1592_eq origin env I V A B legal nonzero correct s m input]
  exact correct s m input

theorem joint1592_counts : toffoliCount joint1592=771 ∧ measurementCount joint1592=514 := by
  have new:=G0CarryLoan5.counts (base 1028) (base 0) (base 1541)
    (joint loanPorts1592 (base 1028) (base 1))
  have old:=joint_counts loanPorts1592 loanPorts1592_widths (base 1028) (base 1)
  exact ⟨new.1.trans old.1,new.2.trans old.2⟩

theorem joint1592_slots : Challenge.gateSlots joint1592≤8006 := by
  rw [joint1592,G0CarryLoan5.slots]
  exact Nat.add_le_add_right (joint_slots_le loanPorts1592 loanPorts1592_widths _ _) 4

theorem joint1592_support (S : Finset Wire)
    (old : wires (joint loanPorts1592 (base 1028) (base 1))⊆S)
    (sj : base 1028∈S) (sg : base 0∈S) : wires joint1592⊆S.erase (base 1541) :=
  G0CarryLoan5.support_to _ _ _ _ S old sj sg
    (by intro e; have:=base_injective e; omega)
    (by intro e; have:=base_injective e; omega) (joint_off 0 (Or.inl rfl))

theorem joint1592_free : base 1541∉wires joint1592 :=
  G0CarryLoan5.avoids_carry _ _ _ _
    (by intro e; have:=base_injective e; omega)
    (by intro e; have:=base_injective e; omega) (joint_off 0 (Or.inl rfl))

theorem joint1592_eff_free : base 2410∉wires joint1592 :=
  G0CarryLoan5.avoids_other _ _ _ _ _
    (by intro e; have:=base_injective e; omega)
    (by intro e; have:=base_injective e; omega)
    (by intro e; have:=base_injective e; omega) (joint_off 2410 (Or.inr rfl))

theorem joint1592_physical (hn : loanPorts1592.wires.Nodup) : GatePhysical joint1592 := by
  have hw:=loanPorts1592_widths
  have outside (i : Nat) (hi : i=1028 ∨ i=1) : base i∉loanPorts1592.wires := by
    simp only [loanPorts1592,BalancedCircuit.Layout.wires,
      BalancedCleanup.Layout.wires,wireBlock,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_map,List.mem_range'_1,
      or_false,base_injective.eq_iff]
    rcases hi with rfl|rfl <;> omega
  have core:=EntryRetained5.program_physical loanPorts1592 hw hn (base 1028) (base 1)
    (outside 1028 (Or.inl rfl)) (outside 1 (Or.inr rfl)) (by simp [base])
  have x : GatePhysical [Instr.X (base 1)] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  apply G0CarryLoan5.physical _ _ _ _ (by intro e; have:=base_injective e; omega)
  simpa only [joint,gatePhysical_append] using And.intro (And.intro x core) x

end ECDSAAdd.Entrant.FrontierEntry
