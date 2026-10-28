import ECDSAAdd.Arithmetic.TranscriptCodecPlacement
import ECDSAAdd.Arithmetic.NarrowSkywalkRoutedLoop

namespace ECDSAAdd.Arithmetic

/-- Three adjacent (orientation, sign) history pairs, interleaved for the
six-site codec. These are actual integer-pool sites, not extra registers. -/
def compressedHistoryId (start : Nat) (q : Fin 6) : Nat :=
  if q.val%2=0 then start+q.val/2 else 1028+start+q.val/2

def compressedHistoryMap (w : Nat → Wire) (start : Nat) : Fin 6 → Wire :=
  fun q => w (compressedHistoryId start q)

/-- Only history labels need to avoid the local codec template labels.
The divisor rail may therefore occupy the caller's original X register. -/
def CompressedHistoryAbove (w : Nat → Wire) : Prop :=
  ∀ j,(j < 512 ∨ (1028 ≤ j ∧ j < 1540)) → 6 ≤ w j

theorem compressedHistoryId_region (start : Nat) (hs : start+3 ≤ 512) (q : Fin 6) :
    compressedHistoryId start q < 512 ∨
      (1028 ≤ compressedHistoryId start q ∧ compressedHistoryId start q < 1540) := by
  have hq := q.isLt
  unfold compressedHistoryId
  split
  · left; omega
  · right; constructor <;> omega

theorem compressedHistoryId_bound (start : Nat) (hs : start+3 ≤ 512) (q : Fin 6) :
    compressedHistoryId start q < 1798 := by
  have hq := q.isLt
  unfold compressedHistoryId
  split  <;> omega

theorem compressedHistoryMap_injective (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (start : Nat) (hs : start+3 ≤ 512) :
    Function.Injective (compressedHistoryMap w start) := by
  intro a b he
  have hid := skywalkPool_index_inj w hn _ _
    (compressedHistoryId_bound start hs a) (compressedHistoryId_bound start hs b) he
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  unfold compressedHistoryId at hid
  split_ifs at hid  <;> omega

theorem compressedHistoryMap_above (w : Nat → Wire) (start : Nat) (hs : start+3 ≤ 512)
    (hlo : CompressedHistoryAbove w) : ∀ q,6 ≤ compressedHistoryMap w start q :=
  fun q => hlo _ (compressedHistoryId_region start hs q)

theorem skywalkRecordedSymbol_legal (x p j : Nat) (hp0 : 0 < p) (hpo : p%2=1) :
    let c := SkywalkTrace.code (SkywalkTrace.next^[j]
      (SkywalkRails.encode false false (x:Int) (p:Int)))
    (c.1 && c.2)=false := by
  dsimp only
  let z := SkywalkNat.step^[j] (SkywalkNat.init x p)
  have hc := SkywalkTrace.iter_code_classified j false false (SkywalkNat.init x p) hp0 hpo
  dsimp only [SkywalkNat.init] at hc
  have hg : (SkywalkTrace.code (SkywalkTrace.next^[j]
      (SkywalkRails.encode false false (x:Int) (p:Int)))).1=decide (z.u%2=0) := hc.1
  rw [hg]
  by_cases he : z.u%2=0
  · have hs := hc.2.1 he
    simp only [hs,Bool.and_false]
  · simp only [he,decide_false,Bool.false_and]

def compressedHistoryEncode (w : Nat → Wire) (start : Nat) : Program :=
  TranscriptCodec3.encode (compressedHistoryMap w start)

def compressedHistoryDecode (w : Nat → Wire) (start : Nat) : Program :=
  TranscriptCodec3.decode (compressedHistoryMap w start)

/-- The real recorded integer-stage assertion supplies the codec's legal
input domain for every divisor; no sampled transcript premise is used. -/
theorem compressedHistoryStage_legal (w : Nat → Wire) (x p i start : Nat)
    (hp0 : 0 < p) (hpo : p%2=1) (hs : start+3 ≤ i) (s : BasisState)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s) :
    (s (compressedHistoryMap w start 0) && s (compressedHistoryMap w start 1))=false ∧
    (s (compressedHistoryMap w start 2) && s (compressedHistoryMap w start 3))=false ∧
    (s (compressedHistoryMap w start 4) && s (compressedHistoryMap w start 5))=false := by
  have tape := h.2.2.2.1
  have ternary (j : Nat) (hj : j < i) : (s (w j) && s (w (1028+j)))=false := by
    rw [(tape j hj).1,(tape j hj).2]
    exact skywalkRecordedSymbol_legal x p j hp0 hpo
  have h0 := ternary start (by omega)
  have h1 := ternary (start+1) (by omega)
  have h2 := ternary (start+2) (by omega)
  simpa [compressedHistoryMap,compressedHistoryId,Nat.add_assoc] using And.intro h0 (And.intro h1 h2)

theorem compressedHistoryEncode_correct (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p i start : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (hs : start+3 ≤ i) (hi : i ≤ 512) (s : State) (m : List Bool)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    (run (compressedHistoryEncode w start) m s).phase=s.phase ∧
    (run (compressedHistoryEncode w start) m s).basis (w (1028+start+1))=false ∧
    run (compressedHistoryEncode w start++compressedHistoryDecode w start) m s=s := by
  have hb : start+3 ≤ 512 := by omega
  have hc := TranscriptCodec3.placement_correct (compressedHistoryMap w start)
    (compressedHistoryMap_injective w hn start hb)
    (compressedHistoryMap_above w start hb hlo) s m
    (compressedHistoryStage_legal w x p i start hp0 hpo hs s.basis h)
  simpa [compressedHistoryEncode,compressedHistoryDecode,compressedHistoryMap,
    compressedHistoryId,Nat.add_assoc] using hc

theorem compressedHistory_counts (w : Nat → Wire) (start : Nat) :
    toffoliCount (compressedHistoryEncode w start)=3 ∧
    measurementCount (compressedHistoryEncode w start)=1 ∧
    toffoliCount (compressedHistoryDecode w start)=4 ∧
    measurementCount (compressedHistoryDecode w start)=0 :=
  TranscriptCodec3.placement_counts (compressedHistoryMap w start)

end ECDSAAdd.Arithmetic
