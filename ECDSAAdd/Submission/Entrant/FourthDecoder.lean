import ECDSAAdd.Submission.Entrant.FrontierMain

namespace ECDSAAdd.Entrant.FourthDecoder
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines InputSentinel

def gateHead : Program := [.CCX 0 2 10, .X 1]

def canonical0 : Program := gateHead ++ [.CX 10 5] ++ OutputOpt.canonical0.drop 3
def canonical1 : Program := gateHead ++ [.CX 10 5] ++ OutputOpt.canonical1.drop 3
def canonical (delta : Bool) : Program := if delta then canonical1 else canonical0

theorem gateHead_eq (s : State) (m : List Bool) (hz : s.basis 10 = false)
    (hn : ((s.basis 0 && s.basis 1) && s.basis 2) = false) :
    run (gateHead ++ [.CX 10 5]) m s = run (gateHead ++ [.CCX 10 1 5]) m s := by
  have hbool : ((s.basis 0 && s.basis 2) && !s.basis 1) =
      (s.basis 0 && s.basis 2) := by
    cases h0 : s.basis 0 <;> cases h1 : s.basis 1 <;> cases h2 : s.basis 2 <;> simp_all
  simp only [gateHead, List.cons_append, List.nil_append, run, writeBit,
    Function.update_of_ne (by decide : (1 : Nat) ≠ 10),
    Function.update_of_ne (by decide : (10 : Nat) ≠ 1),
    Function.update_of_ne (by decide : (5 : Nat) ≠ 1),
    Function.update_of_ne (by decide : (5 : Nat) ≠ 10),
    Function.update_self, hz, Bool.false_xor, hbool]

theorem canonical_eq (delta : Bool) (s : State) (m : List Bool)
    (hz : s.basis 10 = false)
    (hn : ((s.basis 0 && s.basis 1) && s.basis 2) = false) :
    run (canonical delta) m s = run (OutputOpt.canonical delta) m s := by
  have hp : measurementCount (gateHead ++ [.CX 10 5]) = 0 := rfl
  have ho : measurementCount (gateHead ++ [.CCX 10 1 5]) = 0 := rfl
  have extend (tail : Program) :
      run ((gateHead ++ [.CX 10 5]) ++ tail) m s =
        run ((gateHead ++ [.CCX 10 1 5]) ++ tail) m s := by
    rw [ECDSAAdd.run_append (gateHead ++ [Instr.CX 10 5]) tail m s,
      ECDSAAdd.run_append (gateHead ++ [Instr.CCX 10 1 5]) tail m s, hp, ho,
      List.take_zero, List.drop_zero, gateHead_eq s [] hz hn]
  cases delta <;>
    simp only [canonical, OutputOpt.canonical, Bool.false_eq_true, if_false, if_true]
  · exact extend (OutputOpt.canonical0.drop 3)
  · exact extend (OutputOpt.canonical1.drop 3)

theorem canonical_counts (delta : Bool) :
    toffoliCount (canonical delta) = 2 ∧ measurementCount (canonical delta) = 8 := by
  cases delta <;> decide +kernel

theorem canonical_measurements_old (delta : Bool) :
    measurementCount (OutputOpt.canonical delta) = 8 := by
  cases delta <;> decide +kernel

theorem conjugated_eq (pre : Program) (hp : measurementCount pre = 0)
    (delta : Bool) (s : State) (m : List Bool)
    (hz : (run pre [] s).basis 10 = false)
    (hn : (((run pre [] s).basis 0 && (run pre [] s).basis 1) &&
      (run pre [] s).basis 2) = false) :
    run (pre ++ canonical delta ++ pre.reverse) m s =
      run (pre ++ OutputOpt.canonical delta ++ pre.reverse) m s := by
  simp only [List.append_assoc]
  rw [ECDSAAdd.run_append pre (canonical delta ++ pre.reverse) m s,
    ECDSAAdd.run_append pre (OutputOpt.canonical delta ++ pre.reverse) m s,
    hp, List.take_zero, List.drop_zero]
  rw [ECDSAAdd.run_append (canonical delta) pre.reverse m (run pre [] s),
    ECDSAAdd.run_append (OutputOpt.canonical delta) pre.reverse m (run pre [] s),
    (canonical_counts delta).2, canonical_measurements_old delta]
  rw [canonical_eq delta (run pre [] s) (m.take 8) hz hn]

def otail1 (a1 s2 b2 yc y2c : Bool) : Program :=
  OutputOpt.prep1 a1 s2 b2 yc ++ canonical (yc ^^ y2c) ++
    (OutputOpt.prep1 a1 s2 b2 yc).reverse

def otail2 (a1 s2 b2 yc y2c : Bool) : Program :=
  OutputOpt.prep2 a1 s2 b2 yc ++ canonical (yc ^^ y2c) ++
    (OutputOpt.prep2 a1 s2 b2 yc).reverse

theorem otail1_eq (a1 s2 b2 yc y2c : Bool) (s : State) (m : List Bool)
    (hz : (run (OutputOpt.prep1 a1 s2 b2 yc) [] s).basis 10 = false)
    (hn : (((run (OutputOpt.prep1 a1 s2 b2 yc) [] s).basis 0 &&
      (run (OutputOpt.prep1 a1 s2 b2 yc) [] s).basis 1) &&
      (run (OutputOpt.prep1 a1 s2 b2 yc) [] s).basis 2) = false) :
    run (otail1 a1 s2 b2 yc y2c) m s =
      run (OutputOpt.otail1 a1 s2 b2 yc y2c true) m s := by
  have hp : measurementCount (OutputOpt.prep1 a1 s2 b2 yc) = 0 := by
    cases a1 <;> cases s2 <;> cases b2 <;> cases yc <;> rfl
  exact conjugated_eq _ hp _ _ _ hz hn

theorem otail2_eq (a1 s2 b2 yc y2c : Bool) (s : State) (m : List Bool)
    (hz : (run (OutputOpt.prep2 a1 s2 b2 yc) [] s).basis 10 = false)
    (hn : (((run (OutputOpt.prep2 a1 s2 b2 yc) [] s).basis 0 &&
      (run (OutputOpt.prep2 a1 s2 b2 yc) [] s).basis 1) &&
      (run (OutputOpt.prep2 a1 s2 b2 yc) [] s).basis 2) = false) :
    run (otail2 a1 s2 b2 yc y2c) m s =
      run (OutputOpt.otail2 a1 s2 b2 yc y2c true) m s := by
  have hp : measurementCount (OutputOpt.prep2 a1 s2 b2 yc) = 0 := by
    cases a1 <;> cases s2 <;> cases b2 <;> cases yc <;> rfl
  exact conjugated_eq _ hp _ _ _ hz hn

theorem otail_resources (a1 s2 b2 yc y2c : Bool) :
    toffoliCount (otail1 a1 s2 b2 yc y2c) = 2 ∧
    toffoliCount (otail2 a1 s2 b2 yc y2c) = 2 ∧
    measurementCount (otail1 a1 s2 b2 yc y2c) = 8 ∧
    measurementCount (otail2 a1 s2 b2 yc y2c) = 8 ∧
    wires (otail1 a1 s2 b2 yc y2c) ⊆ wires (OutputOpt.otail1 a1 s2 b2 yc y2c true) ∧
    wires (otail2 a1 s2 b2 yc y2c) ⊆ wires (OutputOpt.otail2 a1 s2 b2 yc y2c true) := by
  cases a1 <;> cases s2 <;> cases b2 <;> cases yc <;> cases y2c <;> decide +kernel

theorem otail_physical (a1 s2 b2 yc y2c : Bool) :
    GatePhysical (otail1 a1 s2 b2 yc y2c) ∧ GatePhysical (otail2 a1 s2 b2 yc y2c) := by
  constructor <;> apply gatePhysical_of_all <;>
    cases a1 <;> cases s2 <;> cases b2 <;> cases yc <;> cases y2c <;> decide +kernel

end ECDSAAdd.Entrant.FourthDecoder
