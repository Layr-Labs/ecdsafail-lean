import ECDSAAdd.Arithmetic.CompressedSkywalkPrefix

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- A ghost raw state supplies the old exact integer invariant. Encoding is
an actual circuit program; the assertion equates the complete caller basis.
Incoming phase is unrestricted and is preserved separately by the Triple. -/
def CompressedIntegerStage (w : Nat → Wire) (x p i : Nat) (bits : BasisState) : Prop :=
  ∃ raw : State,
    SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i raw.basis ∧
    bits=(run (compressedEncodePrefix w i) [] raw).basis

attribute [local irreducible] run compressedEncodePrefix compressedSkywalkLoop
attribute [local irreducible] narrowSkywalkScheduledTick compressedHistoryEncode

private theorem xor_neutral (a b : Bool) (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem compressedIntegerStage_zero (w : Nat → Wire) (x p : Nat) (s : State)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis) :
    CompressedIntegerStage w x p 0 s.basis := by
  refine ⟨s,h,?_⟩
  simp only [compressedEncodePrefix,run]

theorem compressedIntegerStage_step (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hi : i < 512) :
    Triple (CompressedIntegerStage w x p i)
      (narrowSkywalkScheduledTick w i ++ compressedPackAfter w i)
      (CompressedIntegerStage w x p (i+1)) := by
  intro s m hs
  obtain ⟨raw,hraw,hbits⟩ := hs
  let tick := narrowSkywalkScheduledTick w i
  let mt := m.take (measurementCount tick)
  let me := m.drop (measurementCount tick)
  let actual := run tick mt s
  let next := run tick [] raw
  have step := narrowSkywalkRoutedStage_step w hn x p i hp0 hx0 hpo hp hx hc hi
  have hnxt := step raw [] hraw
  have hmt := step raw mt hraw
  have hd := (compressedPrefix_disjoint_tick w hn hlo i i (Nat.le_refl i) hi).1
  have read : ∀ q∈wires tick,s.basis q=raw.basis q := by
    intro q hq
    rw [hbits]
    apply run_preserves_outside
    exact fun he => Finset.disjoint_left.mp hd he hq
  have hl := run_local_increment tick s raw mt read
  have hphase : actual.phase=s.phase := by
    apply xor_neutral
    have hh := hl.1
    rw [hmt.1] at hh
    simpa only [Bool.xor_self] using hh
  have hcomm := run_disjoint_commute (compressedEncodePrefix w i) tick hd [] [] raw
  have hb0 := run_basis_records tick s (run (compressedEncodePrefix w i) [] raw) mt [] hbits
  have hb : actual.basis=(run (compressedEncodePrefix w i) [] next).basis :=
    hb0.trans (congrArg State.basis hcomm.symm)
  have hpackphase : (run (compressedPackAfter w i) me actual).phase=actual.phase := by
    cases he : compressedPackDue i
    · simp only [compressedPackAfter,he,Bool.false_eq_true,if_false,run]
    · have h3 := compressedPackDue_true i he
      have same (j : Fin 6) : actual.basis (compressedHistoryMap w (i-3) j)=
          next.basis (compressedHistoryMap w (i-3) j) := by
        rw [hb]
        exact compressedPrefix_raw_next w hn hlo i hi he next [] j
      have legal := compressedHistoryStage_legal w x p (i+1) (i-3) hp0 hpo (by omega) next.basis hnxt.2
      have actualLegal :
          (actual.basis (compressedHistoryMap w (i-3) 0) && actual.basis (compressedHistoryMap w (i-3) 1))=false ∧
          (actual.basis (compressedHistoryMap w (i-3) 2) && actual.basis (compressedHistoryMap w (i-3) 3))=false ∧
          (actual.basis (compressedHistoryMap w (i-3) 4) && actual.basis (compressedHistoryMap w (i-3) 5))=false := by
        rw [same 0,same 1,same 2,same 3,same 4,same 5]
        exact legal
      have cp := TranscriptCodec3.placement_correct (compressedHistoryMap w (i-3))
        (compressedHistoryMap_injective w hn (i-3) (by omega))
        (compressedHistoryMap_above w (i-3) (by omega) hlo) actual me actualLegal
      simpa only [compressedPackAfter,he,if_true,compressedHistoryEncode] using cp.1
  have hpackbits := run_basis_records (compressedPackAfter w i) actual
    (run (compressedEncodePrefix w i) [] next) me [] hb
  have hbnext : (run (compressedPackAfter w i) me actual).basis=
      (run (compressedEncodePrefix w (i+1)) [] next).basis := by
    rw [compressedEncodePrefix,run_append]
    simp only [List.take_nil,List.drop_nil]
    exact hpackbits
  rw [run_append]
  exact ⟨hpackphase.trans hphase,⟨next,hnxt.2,hbnext⟩⟩

/-- Complete forward composition for arbitrary records, including phase.
This theorem retains the exact original divisor and all 512 integer steps. -/
theorem compressedSkywalkLoop_spec (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p i n : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hi : i+n ≤ 512) :
    Triple (CompressedIntegerStage w x p i) (compressedSkywalkLoop w i n)
      (CompressedIntegerStage w x p (i+n)) := by
  induction n generalizing i with
  | zero =>
    rw [compressedSkywalkLoop,Nat.add_zero]
    intro s m h
    simpa only [run] using And.intro (rfl : s.phase=s.phase) h
  | succ n ih =>
    have hstep := compressedIntegerStage_step w hn hlo x p i hp0 hx0 hpo hp hx hc (by omega)
    have htail := ih (i+1) (by omega)
    have hall := hstep.seq htail
    have hindex : i+(n+1)=(i+1)+n := by omega
    rw [compressedSkywalkLoop,hindex]
    simpa only [List.append_assoc] using hall

end ECDSAAdd.Arithmetic
