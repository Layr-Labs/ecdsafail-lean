import ECDSAAdd.Arithmetic.RecordedRailApply258Forward
import ECDSAAdd.Arithmetic.RecordedRailApplyDebt

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply258
open RecordedRailRipple RecordedRailApply ECDSAAdd.Math.RecordedCarryWordMirror

private abbrev wordDebt := ECDSAAdd.Math.RecordedCarryWordMirror.debt

private theorem debt_none (n : Nat) (m cs : List Bool) :
    wordDebt (List.replicate n none) m cs=false := by
  induction n generalizing cs with
  | zero => rfl
  | succ n ih => cases cs <;> simp [List.replicate_succ,wordDebt,ECDSAAdd.Math.RecordedCarryWordMirror.debt,ih]

private theorem getD_drop (cs : List Bool) (n i : Nat) :
    (cs.drop n).getD i false=cs.getD (n+i) false := by
  induction n generalizing cs with
  | zero => simp
  | succ n ih =>
    cases cs with
    | nil => simp
    | cons b bs => simpa only [List.drop_succ_cons,List.getD_cons_succ,Nat.succ_add] using ih bs

private theorem debt_skip (n j : Nat) (slots : List (Option Nat)) (m cs : List Bool) :
    wordDebt (List.replicate n none++some j::slots) m cs=
      ((m.getD j false && cs.getD n false) ^^ wordDebt slots m (cs.drop (n+1))) := by
  induction n generalizing cs with
  | zero => cases cs <;> simp [wordDebt,ECDSAAdd.Math.RecordedCarryWordMirror.debt]
  | succ n ih =>
    cases cs with
    | nil => simp [List.replicate_succ,wordDebt,ECDSAAdd.Math.RecordedCarryWordMirror.debt]
    | cons b bs =>
      simpa only [List.replicate_succ,List.cons_append,wordDebt,ECDSAAdd.Math.RecordedCarryWordMirror.debt,List.getD_cons_succ,
        List.drop_succ_cons,Nat.succ_eq_add_one] using ih bs

/-- All seven actual saved outcomes weight the original carry word. None
slots are genuine absent corrections, never extra quantum inputs. -/
theorem sparse_debt (cursor : Nat) (m cs : List Bool) :
    wordDebt (oldSlots cursor) m cs=
      ((m.getD (cursor+62) false && cs.getD 31 false) ^^
      ((m.getD (cursor+94) false && cs.getD 63 false) ^^
      ((m.getD (cursor+126) false && cs.getD 95 false) ^^
      ((m.getD (cursor+158) false && cs.getD 127 false) ^^
      ((m.getD (cursor+190) false && cs.getD 159 false) ^^
      ((m.getD (cursor+222) false && cs.getD 191 false) ^^
      (m.getD (cursor+255) false && cs.getD 223 false))))))) := by
  simp only [oldSlots,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]
  rw [debt_skip,debt_skip,debt_skip,debt_skip,debt_skip,debt_skip,debt_skip,debt_none]
  simp only [getD_drop,List.drop_drop,Nat.reduceAdd,Bool.xor_false]

/-- Actual arithmetic carry bits agree with the original-prefix overflow
predicates used by the verified Defer phase contract. -/
theorem carry_original (a b : List Wire) (cin : Wire) (bits : BasisState)
    (width : a.length=b.length) (i : Nat) (hi : i<a.length) :
    (carryBits (a.map bits) (b.map bits) (bits cin)).getD i false=
      RecordedRailDefer.prefixCarry a b cin bits (i+1) := by
  rw [carry_overflow _ _ _ i (by simpa using width) (by simpa using hi)]
  simp only [←List.map_take,wordValue_map,RecordedRailDefer.prefixCarry]

/-- The required old phase is derived from the actual Defer debt, with every
classical ordinal relocated by the initial global cursor. -/
theorem debt_forward (a b mirrorBank : List Wire) (cin : Wire) (bits : BasisState)
    (m : List Bool) (cursor : Nat) (aw : a.length=258) (bw : b.length=258)
    (aligned : RecordedRailRipple.Aligned a b mirrorBank (oldSlots cursor)) :
    RecordedRailRipple.phaseDebt a b (bits cin) (oldSlots cursor) bits m=
      debt a b cin bits m cursor := by
  rw [RecordedRailRipple.phaseDebt_word a b mirrorBank (oldSlots cursor)
    (RecordedRailRipple.aligned_shape a b mirrorBank (oldSlots cursor) aligned)]
  change wordDebt (oldSlots cursor) m (carryBits (a.map bits) (b.map bits) (bits cin)) = _
  rw [sparse_debt]
  have widths : a.length=b.length := by omega
  rw [carry_original a b cin bits widths 31 (by omega),
    carry_original a b cin bits widths 63 (by omega),
    carry_original a b cin bits widths 95 (by omega),
    carry_original a b cin bits widths 127 (by omega),
    carry_original a b cin bits widths 159 (by omega),
    carry_original a b cin bits widths 191 (by omega),
    carry_original a b cin bits widths 223 (by omega)]
  simp only [debt,ordinals,RecordedRailDefer.positions,
    List.zip,List.zipWith,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
    Nat.reduceAdd,Bool.xor_false]

end ECDSAAdd.Arithmetic.RecordedRailApply258
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply258.sparse_debt
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply258.debt_forward
