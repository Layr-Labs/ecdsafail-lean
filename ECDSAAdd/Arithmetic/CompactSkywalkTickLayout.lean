import ECDSAAdd.Arithmetic.NarrowSkywalkRouteTick
import ECDSAAdd.Arithmetic.CompactSkywalkSignReleaseViews

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

def compactSkywalkTickPreWidth (i : Nat) : Nat := narrowSkywalkRouteWidth i
def compactSkywalkTickPostWidth (i : Nat) : Nat := narrowSkywalkWidth i

/-- All arithmetic ports are the current physical prefix, with a fresh clean
extension. No omitted 258-bit sign copies are reconstructed for this tick. -/
def compactSkywalkTickLayout (w : Nat → Wire) (i : Nat) : SkywalkIntegerLayout :=
  let n := compactSkywalkTickPreWidth i
  { a0:=w i,b0:=w 770,ext:=w (i+n),history:=w (1028+i),
    previous:=w (skywalkPoolPreviousId i),aSign:=w (i+n-1),bSign:=w (770+n-1),
    aMid:=wireBlock w (i+1) (n-2),bMid:=wireBlock w 771 (n-2),
    carry:=wireBlock w 1540 (n-1) }

theorem compactSkywalkTick_width_bounds (i : Nat) (hi : i < 512) :
    3 ≤ compactSkywalkTickPreWidth i ∧ 2 ≤ compactSkywalkTickPostWidth i ∧
    compactSkywalkTickPostWidth i ≤ compactSkywalkTickPreWidth i ∧
    compactSkywalkTickPreWidth i ≤ 258 ∧
    compactSkywalkTickPreWidth i ≤ 514-i ∧
    compactSkywalkTickPostWidth i = compactSkywalkTickPreWidth (i+1) := by
  have a := narrowSkywalkRouteWidth_bounds i hi
  have b := narrowSkywalkWidth_bounds i hi
  unfold compactSkywalkTickPreWidth compactSkywalkTickPostWidth
    narrowSkywalkRouteWidth narrowSkywalkWidth at *
  omega

private theorem blockLast (w : Nat → Wire) (start count : Nat) (hc : 0 < count) :
    wireBlock w start (count-1)++[w (start+count-1)] = wireBlock w start count := by
  have h := wireBlock_append w start (count-1) 1
  have one : wireBlock w (start+(count-1)) 1 = [w (start+(count-1))] := by
    simp [wireBlock,List.range']
  rw [one] at h
  simpa only [show start+(count-1) = start+count-1 by omega,
    show count-1+1 = count by omega] using h

theorem compactSkywalkTick_ah (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).ah = wireBlock w (i+1) (compactSkywalkTickPreWidth i-1) := by
  have hb := compactSkywalkTick_width_bounds i hi
  have h := blockLast w (i+1) (compactSkywalkTickPreWidth i-1) (by omega)
  change wireBlock w (i+1) (compactSkywalkTickPreWidth i-2)++
    [w (i+compactSkywalkTickPreWidth i-1)] = _
  simpa only [show (compactSkywalkTickPreWidth i-1)-1 = compactSkywalkTickPreWidth i-2 by omega,
    show (i+1)+(compactSkywalkTickPreWidth i-1)-1 = i+compactSkywalkTickPreWidth i-1 by omega] using h

theorem compactSkywalkTick_bh (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).bh = wireBlock w 771 (compactSkywalkTickPreWidth i-1) := by
  have hb := compactSkywalkTick_width_bounds i hi
  have h := blockLast w 771 (compactSkywalkTickPreWidth i-1) (by omega)
  change wireBlock w 771 (compactSkywalkTickPreWidth i-2)++
    [w (770+compactSkywalkTickPreWidth i-1)] = _
  simpa only [show (compactSkywalkTickPreWidth i-1)-1 = compactSkywalkTickPreWidth i-2 by omega,
    show 771+(compactSkywalkTickPreWidth i-1)-1 = 770+compactSkywalkTickPreWidth i-1 by omega] using h

private theorem blockFirst (w : Nat → Wire) (start count : Nat) (hc : 0 < count) :
    w start::wireBlock w (start+1) (count-1) = wireBlock w start count := by
  have h := wireBlock_append w start 1 (count-1)
  have one : wireBlock w start 1 = [w start] := by simp [wireBlock,List.range']
  rw [one] at h
  simpa only [show 1+(count-1) = count by omega,List.singleton_append] using h

theorem compactSkywalkTick_a (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).a = wireBlock w i (compactSkywalkTickPreWidth i) := by
  have hb := compactSkywalkTick_width_bounds i hi
  rw [SkywalkIntegerLayout.a,compactSkywalkTick_ah w i hi]
  exact blockFirst w i _ (by omega)

theorem compactSkywalkTick_b (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).b = wireBlock w 770 (compactSkywalkTickPreWidth i) := by
  have hb := compactSkywalkTick_width_bounds i hi
  rw [SkywalkIntegerLayout.b,compactSkywalkTick_bh w i hi]
  exact blockFirst w 770 _ (by omega)

theorem compactSkywalkTick_half (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).half = wireBlock w (i+1) (compactSkywalkTickPreWidth i) := by
  have hb := compactSkywalkTick_width_bounds i hi
  rw [SkywalkIntegerLayout.half,compactSkywalkTick_ah w i hi]
  change wireBlock w (i+1) (compactSkywalkTickPreWidth i-1)++
    [w (i+compactSkywalkTickPreWidth i)] = _
  have h := blockLast w (i+1) (compactSkywalkTickPreWidth i) (by omega)
  simpa only [show (i+1)+compactSkywalkTickPreWidth i-1 = i+compactSkywalkTickPreWidth i by omega] using h

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTick_half
