import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Baselines.SlotMapped

/-! Complete-State transport from a clean work site to a clean, unused host.
The host cleanliness is a boundary fact; no assumption is made about other sites. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace ECDSAAdd.Entrant.ParityHostTransport5
open Arithmetic RecordedQuantum Challenge
attribute [local irreducible] run wires

def program (work host : Wire) (P : Program) : Program :=
  renameProgram (Equiv.swap work host) P

theorem pull_swap_clean (work host : Wire) (s : State)
    (hw : s.basis work=false) (hh : s.basis host=false) :
    pullState (Equiv.swap work host) s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (Equiv.swap work host q)=s.basis q
    by_cases qw : q=work
    · subst q; simp only [Equiv.swap_apply_left,hw,hh]
    by_cases qh : q=host
    · subst q; simp only [Equiv.swap_apply_right,hw,hh]
    rw [Equiv.swap_apply_of_ne_of_ne qw qh]

theorem pull_swap_invol (work host : Wire) (s : State) :
    pullState (Equiv.swap work host) (pullState (Equiv.swap work host) s)=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (Equiv.swap work host (Equiv.swap work host q))=s.basis q
    rw [Equiv.swap_apply_self]

/-- Renaming preserves the entire output, including phase, for each record tape. -/
theorem run_eq (work host : Wire) (P : Program) (s : State) (m : List Bool)
    (hw : s.basis work=false) (hh : s.basis host=false)
    (ow : (run P m s).basis work=false) (oh : host∉wires P) :
    run (program work host P) m s=run P m s := by
  have hostOut : (run P m s).basis host=false :=
    (run_preserves_outside P m s host oh).trans hh
  have same := ECDSAAdd.run_rename (Equiv.swap work host)
    (Equiv.swap work host).injective P m s
  rw [pull_swap_clean work host s hw hh,
    ←pull_swap_clean work host (run P m s) ow hostOut] at same
  have lifted := congrArg (pullState (Equiv.swap work host)) same
  simpa only [pull_swap_invol,program] using lifted

/-- Independent-record correctness is inherited from the original program. -/
theorem run_eq_independent (work host : Wire) (P : Program) (s : State)
    (m n : List Bool) (hw : s.basis work=false) (hh : s.basis host=false)
    (ow : (run P m s).basis work=false) (oh : host∉wires P)
    (records : run P m s=run P n s) :
    run (program work host P) m s=run P n s :=
  (run_eq work host P s m hw hh ow oh).trans records

theorem counts (work host : Wire) (P : Program) :
    toffoliCount (program work host P)=toffoliCount P ∧
      measurementCount (program work host P)=measurementCount P :=
  renameProgram_counts _ _

theorem slots (work host : Wire) (P : Program) :
    gateSlots (program work host P)=gateSlots P := Baselines.rename_gateSlots _ _

theorem physical (work host : Wire) (P : Program) (hp : GatePhysical P) :
    GatePhysical (program work host P) :=
  gatePhysical_rename _ (Equiv.swap work host).injective _ hp

theorem support (work host : Wire) (P : Program) :
    wires (program work host P)=(wires P).image (Equiv.swap work host) :=
  renameProgram_support _ _

theorem avoids_work (work host : Wire) (P : Program) (oh : host∉wires P) :
    work∉wires (program work host P) := by
  intro used
  rw [support] at used
  obtain ⟨old,mem,eq⟩ := Finset.mem_image.mp used
  have same : old=host := (Equiv.swap work host).injective
    (eq.trans (Equiv.swap_apply_right work host).symm)
  exact oh (same ▸ mem)

theorem support_subset (work host : Wire) (P : Program) (S : Finset Wire)
    (hp : wires P⊆S) (hh : host∈S) (oh : host∉wires P) :
    wires (program work host P)⊆S.erase work := by
  intro q hq
  have notWork : q≠work := fun eq => avoids_work work host P oh (eq ▸ hq)
  refine Finset.mem_erase.mpr ⟨notWork,?_⟩
  rw [support] at hq
  obtain ⟨old,mem,rfl⟩ := Finset.mem_image.mp hq
  by_cases ow : old=work
  · subst old; simpa only [Equiv.swap_apply_left] using hh
  have oh' : old≠host := fun eq => oh (eq ▸ mem)
  simpa only [Equiv.swap_apply_of_ne_of_ne ow oh'] using hp mem

end ECDSAAdd.Entrant.ParityHostTransport5
