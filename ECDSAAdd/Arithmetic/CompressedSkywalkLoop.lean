import ECDSAAdd.Arithmetic.CompressedSkywalkLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- A group is packed one tick after its final orientation was consumed.
For 512 ticks the packed starts are 0,3,...,507; 510 and 511 stay raw. -/
def compressedPackDue (i : Nat) : Bool := decide (3 ≤ i ∧ i%3=0)

def compressedPackAfter (w : Nat → Wire) (i : Nat) : Program :=
  if compressedPackDue i then compressedHistoryEncode w (i-3) else []

def compressedDecodeBefore (w : Nat → Wire) (i : Nat) : Program :=
  if compressedPackDue i then compressedHistoryDecode w (i-3) else []

/-- Executable candidate. Complete compressed-state correctness and physical
scratch reuse are proved separately before selecting this in the point circuit. -/
def compressedSkywalkLoop (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => narrowSkywalkScheduledTick w i ++ compressedPackAfter w i ++
      compressedSkywalkLoop w (i+1) n

def compressedSkywalkUnloop (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => compressedSkywalkUnloop w (i+1) n ++
      compressedDecodeBefore w i ++ narrowSkywalkScheduledUntick w i

def compressedPackCount (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (if compressedPackDue i then 1 else 0)+compressedPackCount (i+1) n

theorem compressedPackAfter_counts (w : Nat → Wire) (i : Nat) :
    toffoliCount (compressedPackAfter w i)=3*(if compressedPackDue i then 1 else 0) ∧
    measurementCount (compressedPackAfter w i)=(if compressedPackDue i then 1 else 0) ∧
    toffoliCount (compressedDecodeBefore w i)=4*(if compressedPackDue i then 1 else 0) ∧
    measurementCount (compressedDecodeBefore w i)=0 := by
  have hc := compressedHistory_counts w (i-3)
  cases he : compressedPackDue i
  · simp [compressedPackAfter,compressedDecodeBefore,he,toffoliCount,measurementCount]
  · simpa [compressedPackAfter,compressedDecodeBefore,he] using hc

theorem compressedSkywalkLoop_counts (w : Nat → Wire) (i n : Nat) :
    toffoliCount (compressedSkywalkLoop w i n)=
      toffoliCount (narrowSkywalkRoutedLoop w i n)+3*compressedPackCount i n ∧
    measurementCount (compressedSkywalkLoop w i n)=
      measurementCount (narrowSkywalkRoutedLoop w i n)+compressedPackCount i n ∧
    toffoliCount (compressedSkywalkUnloop w i n)=
      toffoliCount (narrowSkywalkRoutedUnloop w i n)+4*compressedPackCount i n ∧
    measurementCount (compressedSkywalkUnloop w i n)=
      measurementCount (narrowSkywalkRoutedUnloop w i n) := by
  induction n generalizing i with
  | zero => simp [compressedSkywalkLoop,compressedSkywalkUnloop,compressedPackCount,
      narrowSkywalkRoutedLoop,narrowSkywalkRoutedUnloop,toffoliCount,measurementCount]
  | succ n ih =>
    have hc := compressedPackAfter_counts w i
    have ht := ih (i+1)
    simp only [compressedSkywalkLoop,compressedSkywalkUnloop,compressedPackCount,
      narrowSkywalkRoutedLoop,narrowSkywalkRoutedUnloop,toffoliCount_append,
      measurementCount_append,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,
      ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]
    and_intros <;> omega

theorem compressedSkywalk512_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (compressedSkywalkLoop w 0 512)=198142 ∧
    measurementCount (compressedSkywalkLoop w 0 512)=99113 ∧
    toffoliCount (compressedSkywalkUnloop w 0 512)=198312 ∧
    measurementCount (compressedSkywalkUnloop w 0 512)=98943 := by
  have hc : compressedPackCount 0 512=170 := by rfl
  have ho := narrowSkywalkRouted512_counts w hn
  have hh := compressedSkywalkLoop_counts w 0 512
  simpa only [hc,ho.1,ho.2.1,ho.2.2.1,ho.2.2.2,Nat.reduceMul,Nat.reduceAdd] using hh

end ECDSAAdd.Arithmetic
