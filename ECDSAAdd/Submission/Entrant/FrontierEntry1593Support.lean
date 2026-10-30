import ECDSAAdd.Submission.Entrant.MainPre
import ECDSAAdd.Submission.Entrant.FrontierEntryJointFrame

/-! Loan the clean Eff selector to the new entry's last live carry.
The loan ends before the following S1 selected swap. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum
attribute [local irreducible] run wires

abbrev loanPorts : BalancedCircuit.Layout := OneBankCell5.ports base (base 2409)

def entryLoan : Equiv.Perm Wire := Equiv.swap (base 1541) (base 2410)

def joint1593 : Program :=
  renameProgram entryLoan (joint loanPorts (base 1028) (base 1))

private theorem joint_eff_free : base 2410∉wires (joint loanPorts (base 1028) (base 1)) := by
  have off : base 2410∉EntryRetained5.retSites loanPorts (base 1028) (base 1) := by decide +kernel
  have old := EntryRetained5.program_support loanPorts (OneBankCell5.ports_widths _ _) (base 1028) (base 1)
  have core : base 2410∉wires (EntryRetained5.program loanPorts (base 1028) (base 1)) :=
    fun used => off (old used)
  have x : base 2410∉wires [Instr.X (base 1)] := by simp [wires,Instr.wires,base]
  simpa only [joint,wires_append,Finset.mem_union,not_or] using And.intro (And.intro x core) x

private theorem work_data_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈BalancedCircuit.work L) : q∉L.r ∧ q∉L.y := by
  have count := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
  have work := List.count_pos_iff.mpr hq
  constructor <;> intro used <;> have data := List.count_pos_iff.mpr used
  all_goals
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at count work
    omega

/-- The actual caller frame supplies both clean sites; no new premise is added. -/
theorem joint1593_eq (origin : BasisState) (ctx : OneBankReplay5.Context origin)
    (Z : Fp) (s : State) (m : List Bool)
    (input : PairFrame loanPorts.r loanPorts.y origin (centerWord Z) 0 s.basis) :
    run joint1593 m s=run (joint loanPorts (base 1028) (base 1)) m s := by
  have hw := OneBankCell5.ports_widths base (base 2409)
  have hn := OneBankCell5.ports_nodup base (base 2409) ctx.hn
    (fun used => ctx.ho _ (by simp) (balancedSharedLayout_mapSubset base OneBankCell5.ids
      OneBankCell5.ids_bound used))
  have clean : ∀q∈BalancedCircuit.work loanPorts,s.basis q=false := by
    intro q hq
    have away := work_data_away loanPorts hn q hq
    exact (input.2.2 q away.1 away.2).trans
      (OneBankCell5.clean_of_env_work base (base 2409) origin ctx.env ctx.parity q hq)
  have outside (i : Nat) (hi : i=1028 ∨ i=1 ∨ i=2410 ∨ i=2409 ∨ i=1541) :
      base i∉loanPorts.r ∧ base i∉loanPorts.y := by
    rw [OneBankCell5.ports_r,OneBankCell5.ports_y,balancedSharedPorts_r,balancedSharedPorts_y]
    exact ⟨OwnPlusHost.not_block i 2056 256 (by rcases hi with rfl|rfl|rfl|rfl|rfl <;> omega),
      OwnPlusHost.not_block i 770 256 (by rcases hi with rfl|rfl|rfl|rfl|rfl <;> omega)⟩
  have j := outside 1028 (by simp)
  have g := outside 1 (by simp)
  have e := outside 2410 (by simp)
  have sign := outside 2409 (by simp)
  have carry := outside 1541 (by simp)
  have actual := joint_frame loanPorts hw hn (base 1028) (base 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (origin (base 1028)) (origin (base 1)) (centerFp Z) (centerFp_bounds Z) s m
    input.1 input.2.1 clean
    ((input.2.2 _ sign.1 sign.2).trans ctx.hg0)
    (input.2.2 _ j.1 j.2) (input.2.2 _ g.1 g.2)
  have cin : s.basis (base 1541)=false := clean _ (by decide +kernel)
  have eff : s.basis (base 2410)=false := (input.2.2 _ e.1 e.2).trans ctx.hs0
  have cout : (run (joint loanPorts (base 1028) (base 1)) m s).basis (base 1541)=false :=
    (actual.2.2.2 _ carry.1 carry.2).trans cin
  have eout : (run (joint loanPorts (base 1028) (base 1)) m s).basis (base 2410)=false :=
    (actual.2.2.2 _ e.1 e.2).trans eff
  exact FieldFrameOB5.rebind_swap_run _ _ _ s m cin eff cout eout

theorem joint1593_counts : toffoliCount joint1593=771 ∧ measurementCount joint1593=514 := by
  have renamed := renameProgram_counts entryLoan (joint loanPorts (base 1028) (base 1))
  have old := joint_counts loanPorts (OneBankCell5.ports_widths _ _) (base 1028) (base 1)
  exact ⟨renamed.1.trans old.1,renamed.2.trans old.2⟩

theorem joint1593_slots : Challenge.gateSlots joint1593≤8002 := by
  rw [joint1593,Baselines.rename_gateSlots]
  exact joint_slots_le loanPorts (OneBankCell5.ports_widths _ _) _ _

theorem joint1593_support (W : Finset Wire)
    (old : wires (joint loanPorts (base 1028) (base 1))⊆W) (eff : base 2410∈W) :
    wires joint1593⊆W := by
  intro q used
  rw [joint1593,renameProgram_support] at used
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp used
  by_cases work : a=base 1541
  · subst a; simpa only [entryLoan,Equiv.swap_apply_left] using eff
  have host : a≠base 2410 := fun eq => joint_eff_free (eq ▸ ha)
  simpa only [entryLoan,Equiv.swap_apply_of_ne_of_ne work host] using old ha

theorem joint1593_free : base 1541∉wires joint1593 := by
  intro used
  rw [joint1593,renameProgram_support] at used
  obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp used
  have same : a=base 2410 := entryLoan.injective
    (eq.trans (Equiv.swap_apply_right (base 1541) (base 2410)).symm)
  exact joint_eff_free (same ▸ ha)

theorem joint1593_avoids (q : Wire) (fix : entryLoan q=q)
    (old : q∉wires (joint loanPorts (base 1028) (base 1))) : q∉wires joint1593 := by
  intro used
  rw [joint1593,renameProgram_support] at used
  obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp used
  exact old (entryLoan.injective (eq.trans fix.symm) ▸ ha)

theorem joint1593_physical : GatePhysical joint1593 := by
  have hw := OneBankCell5.ports_widths base (base 2409)
  have hn := OneBankCell5.ports_nodup_injective base (base 2409) base_injective
    (by decide +kernel)
  have core := EntryRetained5.program_physical loanPorts hw hn (base 1028) (base 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have x : GatePhysical [Instr.X (base 1)] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  apply gatePhysical_rename _ entryLoan.injective
  simpa only [joint,gatePhysical_append] using And.intro (And.intro x core) x

/-- The retiring carry is unchanged by all three entry placement maps. -/
theorem retired_image : HostOB5.hostSwap (OB5.sig 511
    (shifted (Placement5.pi 0) (base 1541)))=base 1541 := by decide +kernel

/-- Eff is the already-retained terminal-sign host after outer selector hosting. -/
theorem eff_image : HostOB5.hostSwap (OB5.sig 511
    (shifted (Placement5.pi 0) (base 2410)))=base 1542 := by decide +kernel

end ECDSAAdd.Entrant.FrontierEntry
