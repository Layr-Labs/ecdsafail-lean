import ECDSAAdd.Arithmetic.MappedSources
import ECDSAAdd.Arithmetic.ConstantBorrow

namespace ECDSAAdd.Arithmetic

/-- The exact canonical add core reuses one carry bank. Its source is already
canonical; normalization and source copy/unload are separate streamed steps. -/
structure MeasuredCanonicalModLayout where
  src : List Wire
  out : List Wire
  carry : List Wire
  high : Wire
  cin : Wire
  flag : Wire

namespace MeasuredCanonicalModLayout

def extended (L : MeasuredCanonicalModLayout) : List Wire := L.out++[L.high]
def wires (L : MeasuredCanonicalModLayout) : List Wire :=
  L.src++L.out++L.carry++[L.high,L.cin,L.flag]

structure Widths (L : MeasuredCanonicalModLayout) (n : Nat) : Prop where
  src : L.src.length=n
  out : L.out.length=n
  carry : L.carry.length=n

def sum (L : MeasuredCanonicalModLayout) : Program :=
  mappedAdd (mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)])
    L.extended L.carry L.cin

def program (L : MeasuredCanonicalModLayout) (c p : Nat) : Program :=
  L.sum++
    compareConstantGe L.out (L.carry.take (L.out.length-1)) L.cin L.flag p++
    [.CX L.high L.flag]++
    mappedConstAdd (some L.flag) L.extended L.carry L.cin c++
    [.CX L.flag L.high]++
    eraseLtChain L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag

theorem program_counts (L : MeasuredCanonicalModLayout) (n c p : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    toffoliCount (L.program c p)=4*n-1 ∧
    measurementCount (L.program c p)=4*n-1 := by
  have extendedLength : L.extended.length=n+1 := by simp [extended,hw.out]
  have sourceLength : (mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)]).length=n+1 := by
    simp [mappedRead,hw.src]
  have sumCounts := mappedAdd_counts (mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)])
    L.extended L.carry L.cin (sourceLength.trans extendedLength.symm)
    (by rw [hw.carry,extendedLength])
  have geCounts := compareConstantGe_counts L.out (L.carry.take (L.out.length-1))
    L.cin L.flag p (by simp [hw.carry,hw.out]; omega)
  have correction := mappedConstAdd_counts (some L.flag) L.extended L.carry L.cin c
    (by rw [hw.carry,extendedLength])
  have eraseCounts := eraseLtChain_counts L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag
    (hw.out.trans hw.src.symm) (by simp [hw.carry,hw.out,hw.src]; omega)
  constructor
  · simp only [program,sum,toffoliCount_append,toffoliCount]
    rw [sumCounts.1,geCounts.1,correction.1,eraseCounts.1,extendedLength,hw.out,hw.src]
    omega
  · simp only [program,sum,measurementCount_append,measurementCount]
    rw [sumCounts.2,geCounts.2,correction.2,eraseCounts.2,extendedLength,hw.out,hw.src]
    omega

theorem secp_program_counts (L : MeasuredCanonicalModLayout) (hw : L.Widths 256) (c p : Nat) :
    toffoliCount (L.program c p)=1023 ∧ measurementCount (L.program c p)=1023 := by
  simpa using L.program_counts 256 c p hw (by decide)

end MeasuredCanonicalModLayout
end ECDSAAdd.Arithmetic
