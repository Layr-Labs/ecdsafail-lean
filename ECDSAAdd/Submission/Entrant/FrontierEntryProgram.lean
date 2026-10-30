import ECDSAAdd.Submission.Entrant.FrontierEntryAffine
import ECDSAAdd.Submission.Entrant.FrontierEntryErase

/-! Source bit zero is the temporary product U. Its copy is delayed until
all four measured products have been erased. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField

def lowY (L : Layout) : Wire := L.ylow.getD 0 0

def source (L : Layout) (i : Nat) : Affine.Bit :=
  if i=0 then ⟨L.parity,[L.lower]⟩ else if i=1 ∨ i=2 then ⟨L.one,[L.sign]⟩ else
    if i=3 then ⟨L.parity,[L.one,L.sign]⟩ else
      if i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=31 ∨ i=255 then ⟨L.parity,[L.one,L.lower]⟩
      else ⟨L.one,[L.lower]⟩

def sources (L : Layout) : List Affine.Bit := (List.range 256).map (source L)

def prepare (L : Layout) (J B : Wire) : Program :=
  [.CCX J B (lowY L)]++copyRegister (some J) L.r.tail L.y.tail++
    [.CX L.r0 L.parity,.CCX L.parity L.rmsb L.lower,
      .CCX L.parity (lowY L) L.one,.CCX L.lower (lowY L) L.sign,.CX L.parity L.r0]++
    rotateRight L.r++[.CX (L.r.getD 254 0) L.rmsb]++signComplement (lowY L) L.r

def arithmetic (L : Layout) : Program := Affine.add (sources L) L.r (L.carry.take 255) (lowY L)

def prefixProgram (L : Layout) (J B : Wire) : Program := prepare L J B++arithmetic L

def program (L : Layout) (J B : Wire) : Program :=
  prefixProgram L J B++eraseScalarsAt L J B++clearParity L J

theorem sources_length (L : Layout) : (sources L).length=256 := by simp [sources]

theorem prepare_counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (prepare L J B)=259 ∧ measurementCount (prepare L J B)=0 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have r : L.r.tail.length=255 := by simp [len.2.1]
  have y : L.y.tail.length=255 := by simp [len.2.2.1]
  have c := copyRegister_counts (some J) L.r.tail L.y.tail (r.trans y.symm)
  have rot := rotate_counts L.r
  have comp := signComplement_counts (lowY L) L.r
  simp only [prepare,toffoliCount_append,measurementCount_append,c.1,c.2,rot.1,rot.2.1,comp.1,comp.2,r]
  norm_num [toffoliCount,measurementCount]

theorem arithmetic_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (arithmetic L)=255 ∧ measurementCount (arithmetic L)=255 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h := Affine.add_counts (sources L) L.r (L.carry.take 255) (lowY L)
    (by rw [sources_length,len.2.1]) (by simp [List.length_take,hw.2.2,len.2.1])
  simpa only [arithmetic,len.2.1] using h

theorem prefix_counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (prefixProgram L J B)=514 ∧ measurementCount (prefixProgram L J B)=255 := by
  simp only [prefixProgram,toffoliCount_append,measurementCount_append,
    (prepare_counts L hw J B).1,(prepare_counts L hw J B).2,
    (arithmetic_counts L hw).1,(arithmetic_counts L hw).2]
  decide

theorem counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (program L J B)=771 ∧ measurementCount (program L J B)=514 := by
  have e := eraseScalars_counts L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J B L.rmsb
  simp only [program,eraseScalarsAt,toffoliCount_append,measurementCount_append,
    (prefix_counts L hw J B).1,(prefix_counts L hw J B).2,e.1,e.2,
    (clearParity_counts L hw J).1,(clearParity_counts L hw J).2]
  decide

theorem sources_value (L : Layout) (P H U : Bool) (s : BasisState)
    (hp : s L.parity=P) (ha : s L.lower=(P && H))
    (hd : s L.one=(P && U)) (he : s L.sign=((P && H) && U)) :
    Affine.value (sources L) s=EntryHalf5.virtualSource P H U := by
  have bit (i : Nat) : (source L i).value s=EntryHalf5.sourceBit i P H U := by
    simp only [source,EntryHalf5.sourceBit]
    split_ifs <;> simp [Affine.Bit.value,Affine.parity,hp,ha,hd,he,Bool.xor_assoc]
  have map (is : List Nat) : Affine.value (is.map (source L)) s=
      is.foldr (fun i acc => (EntryHalf5.sourceBit i P H U).toNat+2*acc) 0 := by
    induction is with
    | nil => rfl
    | cons i is ih => simp only [List.map_cons,Affine.value,List.foldr_cons,bit,ih]
  exact map (List.range 256)

end ECDSAAdd.Entrant.EntryRetained5
