import ECDSAAdd.Arithmetic.Divsteps.Decoder
import ECDSAAdd.Math.Divsteps.ShallowRecovery

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Depth-three formula (paper (56b)), with an enable flag. -/
def decode3 (flag f2 q2 output : Wire) : Program :=
  [.CX flag output, .CCX flag f2 output, .CCX flag q2 output]

theorem decode3_run (flag f2 q2 output : Wire)
    (hf : flag ≠ output) (ha : f2 ≠ output) (hb : q2 ≠ output)
    (s : State) (m : List Bool) :
    run (decode3 flag f2 q2 output) m s =
      ⟨s.phase, writeBit s.basis output
        (s.basis output ^^ (s.basis flag &&
          (true ^^ s.basis f2 ^^ s.basis q2)))⟩ := by
  cases hflag : s.basis flag <;> cases hleft : s.basis f2 <;>
    cases hright : s.basis q2 <;> cases hout : s.basis output <;>
    simp [decode3, run, writeBit, Function.update, hf, ha, hb,
      hflag, hleft, hright, hout]

theorem decode3_counts (flag f2 q2 output : Wire) :
    toffoliCount (decode3 flag f2 q2 output) = 2 ∧
    measurementCount (decode3 flag f2 q2 output) = 0 := by
  simp [decode3, toffoliCount, measurementCount]

theorem decode3_wires (flag f2 q2 output : Wire) :
    wires (decode3 flag f2 q2 output) = {flag, f2, q2, output} := by
  ext w
  simp [decode3, wires, Instr.wires]
  tauto

/-- Direct depth-four formula (56c). Wires 0..7 are enable, f[1..3],
q[1..3], output; 8 is one clean reusable scratch bit. The input wires are temporarily
XORed and restored. This is not the
paper's optimized residue-selected implementation. -/
def decode4 (w : Fin 9 → Wire) : Program :=
  [.CX (w 0) (w 7),
   .CCX (w 0) (w 1) (w 7), .CCX (w 0) (w 2) (w 7),
   .CCX (w 0) (w 3) (w 7), .CCX (w 0) (w 4) (w 7),
   .CCX (w 0) (w 5) (w 7), .CCX (w 0) (w 6) (w 7),
   .CX (w 2) (w 1), .CX (w 5) (w 4),
   .CCX (w 1) (w 4) (w 8), .CCX (w 0) (w 8) (w 7),
   .CCX (w 1) (w 4) (w 8),
   .CX (w 5) (w 4), .CX (w 2) (w 1)]

theorem decode4_run (w : Fin 9 → Wire) (hw : Function.Injective w)
    (s : State) (m : List Bool)
    (h8 : s.basis (w 8) = false) :
    run (decode4 w) m s =
      ⟨s.phase, writeBit s.basis (w 7)
        (s.basis (w 7) ^^ (s.basis (w 0) &&
          (true ^^ s.basis (w 1) ^^ s.basis (w 2) ^^ s.basis (w 3) ^^
            s.basis (w 4) ^^ s.basis (w 5) ^^ s.basis (w 6) ^^
            ((s.basis (w 1) ^^ s.basis (w 2)) &&
             (s.basis (w 4) ^^ s.basis (w 5))))))⟩ := by
  simp [decode4, run, writeBit, hw.eq_iff, h8]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all [hw.eq_iff]
  cases h0 : s.basis (w 0) <;> cases h1 : s.basis (w 1) <;>
    cases h2 : s.basis (w 2) <;> cases h3 : s.basis (w 3) <;>
    cases h4 : s.basis (w 4) <;> cases h5 : s.basis (w 5) <;>
    cases h6 : s.basis (w 6) <;> cases h7 : s.basis (w 7) <;> simp_all

theorem decode4_counts (w : Fin 9 → Wire) :
    toffoliCount (decode4 w) = 9 ∧ measurementCount (decode4 w) = 0 := by
  simp [decode4, toffoliCount, measurementCount]

theorem decode4_wires (w : Fin 9 → Wire) :
    wires (decode4 w) = Finset.univ.image w := by
  ext i
  simp [decode4, wires, Instr.wires, Fin.exists_fin_succ]
  tauto

/-- Connect the physical depth-three gate formula to the modular-inverse
bit on all odd residues. The caller must still establish that these are
the residues of the actual walk state and that this is the active depth. -/
theorem decode3_residue (flag a b output : Wire)
    (hf : flag ≠ output) (ha : a ≠ output) (hb : b ≠ output)
    (s : State) (m : List Bool) (f q : Fin 4)
    (hfa : s.basis a = ECDSAAdd.Divsteps.SmallDecoders.bit
      (ECDSAAdd.Divsteps.SmallDecoders.oddValue f) 2)
    (hqb : s.basis b = ECDSAAdd.Divsteps.SmallDecoders.bit
      (ECDSAAdd.Divsteps.SmallDecoders.oddValue q) 2) :
    run (decode3 flag a b output) m s =
      ⟨s.phase, writeBit s.basis output (s.basis output ^^ (s.basis flag &&
        ECDSAAdd.Divsteps.SmallDecoders.bit
          (((7 : ZMod 8) * (((ECDSAAdd.Divsteps.SmallDecoders.oddValue f *
            ECDSAAdd.Divsteps.SmallDecoders.oddValue q : Nat) : ZMod 8))⁻¹).val) 2))⟩ := by
  rw [decode3_run flag a b output hf ha hb, hfa, hqb,
    ECDSAAdd.Divsteps.SmallDecoders.depth3]
  rfl

/-- Exact static wire count, including inputs, output, flag and the
single scratch bit. This is not a net saving for a complete walk. -/
theorem decode4_wireCount (w : Fin 9 → Wire) (hw : Function.Injective w) :
    (wires (decode4 w)).card = 9 := by
  rw [decode4_wires, Finset.card_image_of_injective _ hw]
  decide

/-- All odd residue pairs for depth four, with explicit physical-bit encoding.
This is a decoder contract, not a claim of whole-walk reachability. -/
theorem decode4_residue (w : Fin 9 → Wire) (hw : Function.Injective w)
    (s : State) (m : List Bool) (h8 : s.basis (w 8) = false) (f q : Fin 8)
    (h1 : s.basis (w 1) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue f) 1)
    (h2 : s.basis (w 2) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue f) 2)
    (h3 : s.basis (w 3) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue f) 3)
    (h4 : s.basis (w 4) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue q) 1)
    (h5 : s.basis (w 5) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue q) 2)
    (h6 : s.basis (w 6) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue q) 3) :
    run (decode4 w) m s =
      ⟨s.phase, writeBit s.basis (w 7) (s.basis (w 7) ^^ (s.basis (w 0) &&
        ECDSAAdd.Divsteps.SmallDecoders.bit
          (((15 : ZMod 16) * (((ECDSAAdd.Divsteps.SmallDecoders.oddValue f *
            ECDSAAdd.Divsteps.SmallDecoders.oddValue q : Nat) : ZMod 16))⁻¹).val) 3))⟩ := by
  rw [decode4_run w hw s m h8, h1, h2, h3, h4, h5, h6,
    ECDSAAdd.Divsteps.SmallDecoders.depth4]
  rfl

/-- Erase the actual branch bit at a reachable depth-three state, under
explicit residue and physical-bit encodings. Depth detection/layout is
not included in this local decoder. -/
theorem decode3_erase (flag a b output : Wire)
    (hfo : flag ≠ output) (hao : a ≠ output) (hbo : b ≠ output)
    (p : Int) (t : ECDSAAdd.Divsteps.ZState) (hinv : ECDSAAdd.Divsteps.Inv p t)
    (hp : p % 2 = 1) (hz : t.z < 0)
    (hd : padicValInt 2 (ECDSAAdd.Divsteps.zStep t).fv = 3)
    (f q : Fin 4) (hp8 : (p : ZMod 8) = 7)
    (hf : ((ECDSAAdd.Divsteps.zStep t).f : ZMod 8) = (ECDSAAdd.Divsteps.SmallDecoders.oddValue f : ZMod 8))
    (hq : (((ECDSAAdd.Divsteps.zStep t).fv / 8 : Int) : ZMod 8) = (ECDSAAdd.Divsteps.SmallDecoders.oddValue q : ZMod 8))
    (s : State) (m : List Bool) (henable : s.basis flag = true)
    (hfa : s.basis a = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue f) 2)
    (hqb : s.basis b = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue q) 2)
    (hout : s.basis output = decide (ECDSAAdd.Divsteps.bbit t = 1)) :
    run (decode3 flag a b output) m s = ⟨s.phase, writeBit s.basis output false⟩ := by
  rw [decode3_run flag a b output hfo hao hbo, henable, hfa, hqb, hout,
    ECDSAAdd.Divsteps.depth3_branch p t hinv hp hz hd f q hp8 hf hq]
  simp [ECDSAAdd.Divsteps.SmallDecoders.decode3]

/-- Depth-four branch erasure with one clean scratch bit, returned clean. -/
theorem decode4_erase (w : Fin 9 → Wire) (hw : Function.Injective w)
    (p : Int) (t : ECDSAAdd.Divsteps.ZState) (hinv : ECDSAAdd.Divsteps.Inv p t)
    (hp : p % 2 = 1) (hz : t.z < 0)
    (hd : padicValInt 2 (ECDSAAdd.Divsteps.zStep t).fv = 4)
    (f q : Fin 8) (hp16 : (p : ZMod 16) = 15)
    (hf : ((ECDSAAdd.Divsteps.zStep t).f : ZMod 16) = (ECDSAAdd.Divsteps.SmallDecoders.oddValue f : ZMod 16))
    (hq : (((ECDSAAdd.Divsteps.zStep t).fv / 16 : Int) : ZMod 16) = (ECDSAAdd.Divsteps.SmallDecoders.oddValue q : ZMod 16))
    (s : State) (m : List Bool) (henable : s.basis (w 0) = true)
    (h8 : s.basis (w 8) = false)
    (h1 : s.basis (w 1) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue f) 1)
    (h2 : s.basis (w 2) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue f) 2)
    (h3 : s.basis (w 3) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue f) 3)
    (h4 : s.basis (w 4) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue q) 1)
    (h5 : s.basis (w 5) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue q) 2)
    (h6 : s.basis (w 6) = ECDSAAdd.Divsteps.SmallDecoders.bit (ECDSAAdd.Divsteps.SmallDecoders.oddValue q) 3)
    (hout : s.basis (w 7) = decide (ECDSAAdd.Divsteps.bbit t = 1)) :
    run (decode4 w) m s = ⟨s.phase, writeBit s.basis (w 7) false⟩ := by
  rw [decode4_run w hw s m h8, henable, h1, h2, h3, h4, h5, h6, hout,
    ECDSAAdd.Divsteps.depth4_branch p t hinv hp hz hd f q hp16 hf hq]
  simp [ECDSAAdd.Divsteps.SmallDecoders.decode4]

end ECDSAAdd.Arithmetic.Divsteps
