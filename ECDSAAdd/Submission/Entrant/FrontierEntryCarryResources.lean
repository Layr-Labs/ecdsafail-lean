import ECDSAAdd.Submission.Entrant.FrontierEntryCarry

set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagonalCarry5
open Arithmetic RecordedQuantum Challenge

theorem support (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    wires (chain bs xs cs cin ctl target)⊆(ctl::target::cin::(xs++cs)).toFinset := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    simp [chain,ex,ec,wires,Instr.wires,Finset.subset_iff]
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have rest := ih xs cs c (by simpa using hx) (by simpa using hc)
        have cell := mappedBit_wires (bit b) x cin c
        have head : wires (mappedMajority (bit b) x cin c)⊆[x,cin,c].toFinset := by
          simpa [bit] using cell.1
        have tail : wires (mappedEraseCarry (bit b) x cin c)⊆[x,cin,c].toFinset := by
          simpa [bit] using cell.2.1
        intro q hq
        simp only [chain,wires_append,Finset.mem_union] at hq
        rcases hq with (h|h)|h
        · have hq := head h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
          tauto
        · have hq := rest h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
          tauto
        · have hq := tail h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
          tauto

theorem physical (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hn : (ctl::target::cin::(xs++cs)).Nodup)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    GatePhysical (chain bs xs cs cin ctl target) := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    subst xs cs
    have ot : ctl≠target := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have ct : cin≠target := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [h])
    simpa [chain,GatePhysical,PhysicalInstr,ProperGate] using And.intro ot ct
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have nd : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have nr : (ctl::target::c::(xs++cs)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        have r := ih xs cs c nr (by simpa using hx) (by simpa using hc)
        simp only [chain,gatePhysical_append]
        exact ⟨⟨mappedMajority_physical (bit b) x cin c nd (by simp [bit]),r⟩,
          mappedEraseCarry_physical (bit b) x cin c⟩

theorem slots_le (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    gateSlots (chain bs xs cs cin ctl target)≤7*bs.length+1 := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    simp [chain,ex,ec,gateSlots,instructionSlots]
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have r := ih xs cs c (by simpa using hx) (by simpa using hc)
        have cell : gateSlots (mappedMajority (bit b) x cin c)+gateSlots (mappedEraseCarry (bit b) x cin c)≤7 := by
          cases b <;> norm_num [bit,mappedMajority,mappedEraseCarry,gateSlots,instructionSlots]
        simp only [chain,gateSlots_append,List.length_cons]
        omega

end ECDSAAdd.Entrant.DiagonalCarry5
