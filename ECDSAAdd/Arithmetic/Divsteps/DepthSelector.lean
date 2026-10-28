import ECDSAAdd.Arithmetic.Divsteps.ShallowDecoder
import ECDSAAdd.Math.Divsteps.DepthBits

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Read five low bits (0..4), XOR the exact depth-2/3/4 predicates into
outputs 5..7, and restore clean scratch 8..10. No walk counter or active
flag is tested here; callers must additionally gate applicability. -/
def selectDepths (w : Fin 11 → Wire) : Program :=
  [.X (w 0), .X (w 1), .CCX (w 0) (w 1) (w 8), .X (w 1), .X (w 0),
   .X (w 2), .CCX (w 8) (w 2) (w 9), .X (w 2),
   .X (w 3), .CCX (w 9) (w 3) (w 10), .X (w 3),
   .CCX (w 8) (w 2) (w 5), .CCX (w 9) (w 3) (w 6),
   .CCX (w 10) (w 4) (w 7),
   .X (w 3), .CCX (w 9) (w 3) (w 10), .X (w 3),
   .X (w 2), .CCX (w 8) (w 2) (w 9), .X (w 2),
   .X (w 0), .X (w 1), .CCX (w 0) (w 1) (w 8), .X (w 1), .X (w 0)]

set_option maxHeartbeats 1000000 in
theorem selectDepths_run (w : Fin 11 → Wire) (hw : Function.Injective w)
    (s : State) (m : List Bool)
    (h8 : s.basis (w 8) = false) (h9 : s.basis (w 9) = false)
    (h10 : s.basis (w 10) = false) :
    run (selectDepths w) m s = ⟨s.phase,
      writeBit (writeBit (writeBit s.basis (w 5)
        (s.basis (w 5) ^^ (!s.basis (w 0) && !s.basis (w 1) && s.basis (w 2))))
        (w 6) (s.basis (w 6) ^^
          (!s.basis (w 0) && !s.basis (w 1) && !s.basis (w 2) && s.basis (w 3))))
        (w 7) (s.basis (w 7) ^^
          (!s.basis (w 0) && !s.basis (w 1) && !s.basis (w 2) &&
            !s.basis (w 3) && s.basis (w 4)))⟩ := by
  simp [selectDepths, run, writeBit, hw.eq_iff, h8, h9, h10]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all [hw.eq_iff]

theorem selectDepths_counts (w : Fin 11 → Wire) :
    toffoliCount (selectDepths w) = 9 ∧ measurementCount (selectDepths w) = 0 := by
  simp [selectDepths, toffoliCount, measurementCount]

theorem selectDepths_wires (w : Fin 11 → Wire) :
    wires (selectDepths w) = Finset.univ.image w := by
  ext i
  simp [selectDepths, wires, Instr.wires, Fin.exists_fin_succ]
  tauto

/-- A selected depth-2 flag establishes the actual integer valuation.
All-zero low bits select none of these shallow depths. -/
theorem selectDepths_depth2 (w : Fin 11 → Wire) (hw : Function.Injective w)
    (s : State) (m : List Bool) (n : Int)
    (h8 : s.basis (w 8) = false) (h9 : s.basis (w 9) = false)
    (h10 : s.basis (w 10) = false) (ht : s.basis (w 5) = false)
    (hb0 : s.basis (w 0) = decide (ECDSAAdd.Divsteps.bitk n 0 = 1))
    (hb1 : s.basis (w 1) = decide (ECDSAAdd.Divsteps.bitk n 1 = 1))
    (hb2 : s.basis (w 2) = decide (ECDSAAdd.Divsteps.bitk n 2 = 1))
    (hselected : (run (selectDepths w) m s).basis (w 5) = true) :
    padicValInt 2 n = 2 := by
  rw [selectDepths_run w hw s m h8 h9 h10] at hselected
  simp [writeBit, hw.eq_iff, ht] at hselected
  apply ECDSAAdd.Divsteps.depth2_of_bits n <;> simp_all

/-- A selected depth-3 flag establishes the actual integer valuation.
All-zero low bits select none of these shallow depths. -/
theorem selectDepths_depth3 (w : Fin 11 → Wire) (hw : Function.Injective w)
    (s : State) (m : List Bool) (n : Int)
    (h8 : s.basis (w 8) = false) (h9 : s.basis (w 9) = false)
    (h10 : s.basis (w 10) = false) (ht : s.basis (w 6) = false)
    (hb0 : s.basis (w 0) = decide (ECDSAAdd.Divsteps.bitk n 0 = 1))
    (hb1 : s.basis (w 1) = decide (ECDSAAdd.Divsteps.bitk n 1 = 1))
    (hb2 : s.basis (w 2) = decide (ECDSAAdd.Divsteps.bitk n 2 = 1))
    (hb3 : s.basis (w 3) = decide (ECDSAAdd.Divsteps.bitk n 3 = 1))
    (hselected : (run (selectDepths w) m s).basis (w 6) = true) :
    padicValInt 2 n = 3 := by
  rw [selectDepths_run w hw s m h8 h9 h10] at hselected
  simp [writeBit, hw.eq_iff, ht] at hselected
  apply ECDSAAdd.Divsteps.depth3_of_bits n <;> simp_all

/-- A selected depth-4 flag establishes the actual integer valuation.
All-zero low bits select none of these shallow depths. -/
theorem selectDepths_depth4 (w : Fin 11 → Wire) (hw : Function.Injective w)
    (s : State) (m : List Bool) (n : Int)
    (h8 : s.basis (w 8) = false) (h9 : s.basis (w 9) = false)
    (h10 : s.basis (w 10) = false) (ht : s.basis (w 7) = false)
    (hb0 : s.basis (w 0) = decide (ECDSAAdd.Divsteps.bitk n 0 = 1))
    (hb1 : s.basis (w 1) = decide (ECDSAAdd.Divsteps.bitk n 1 = 1))
    (hb2 : s.basis (w 2) = decide (ECDSAAdd.Divsteps.bitk n 2 = 1))
    (hb3 : s.basis (w 3) = decide (ECDSAAdd.Divsteps.bitk n 3 = 1))
    (hb4 : s.basis (w 4) = decide (ECDSAAdd.Divsteps.bitk n 4 = 1))
    (hselected : (run (selectDepths w) m s).basis (w 7) = true) :
    padicValInt 2 n = 4 := by
  rw [selectDepths_run w hw s m h8 h9 h10] at hselected
  simp [writeBit, ht] at hselected
  apply ECDSAAdd.Divsteps.depth4_of_bits n <;> simp_all

end ECDSAAdd.Arithmetic.Divsteps
