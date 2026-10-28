import ECDSAAdd.Arithmetic.MappedAdder
import ECDSAAdd.Arithmetic.LiteralSkywalkSeedPool
import ECDSAAdd.Arithmetic.Rotate

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open Secp256k1

def hConstant : Nat := (p+1)/2
def kConstant (inverse odd : Bool) : Nat :=
  if inverse then if odd then (p-1)/2 else 2^258-p
  else if odd then 2^258-(p-1)/2 else p

def hBits (w : Nat → Wire) (inverse : Bool) : List MappedBit :=
  (List.range 253).map (fun j =>
    if (if inverse then 2^256-hConstant else hConstant).testBit (j+3)
    then {wire:=some (w 1028),flip:=false} else {wire:=none,flip:=false})

def kBits (w : Nat → Wire) (inverse : Bool) : List MappedBit :=
  (List.range 257).map (fun j =>
    let a := (kConstant inverse false).testBit (j+1)
    let b := (kConstant inverse true).testBit (j+1)
    if a=b then {wire:=none,flip:=a}
    else {wire:=some (w 1028),flip:=a})

def hAdd (w : Nat → Wire) (inverse : Bool) : Program :=
  mappedAdd (hBits w inverse) (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797)

def kAdd (w : Nat → Wire) (inverse : Bool) : Program :=
  mappedAdd (kBits w inverse) (wireBlock w 771 257) (wireBlock w 1540 256) (w 770)++
    [.X (w 770)]

def lowCopy (w : Nat → Wire) : Program :=
  copyRegister none (wireBlock w 771 255) (wireBlock w 1 255)

def forward (w : Nat → Wire) : Program :=
  [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]++
  lowCopy w++hAdd w false++[.CX (w 1028) (w 770)]++
  rotateRight (wireBlock w 770 258)++kAdd w false

def inverse (w : Nat → Wire) : Program :=
  kAdd w true++rotateLeft (wireBlock w 770 258)++
  [.CX (w 1028) (w 770)]++hAdd w true++lowCopy w++
  [.X (w 0),.CX (w 1028) (w 0),.CX (w 770) (w 1028)]

theorem hBits_length (w : Nat → Wire) (inverse : Bool) :
    (hBits w inverse).length=253 := by simp [hBits]
theorem kBits_length (w : Nat → Wire) (inverse : Bool) :
    (kBits w inverse).length=257 := by simp [kBits]

theorem hAdd_counts (w : Nat → Wire) (inverse : Bool) :
    toffoliCount (hAdd w inverse)=252 ∧ measurementCount (hAdd w inverse)=252 := by
  have h := mappedAdd_counts (hBits w inverse) (wireBlock w 4 253)
    (wireBlock w 1540 252) (w 1797)
    (by simp [hBits_length,wireBlock_length]) (by simp [wireBlock_length])
  simpa [hAdd,wireBlock_length] using h

theorem kAdd_counts (w : Nat → Wire) (inverse : Bool) :
    toffoliCount (kAdd w inverse)=256 ∧ measurementCount (kAdd w inverse)=256 := by
  have h := mappedAdd_counts (kBits w inverse) (wireBlock w 771 257)
    (wireBlock w 1540 256) (w 770)
    (by simp [kBits_length,wireBlock_length]) (by simp [wireBlock_length])
  simp only [wireBlock_length] at h
  simp [kAdd,toffoliCount_append,measurementCount_append,h.1,h.2,toffoliCount,measurementCount]

theorem lowCopy_counts (w : Nat → Wire) :
    toffoliCount (lowCopy w)=0 ∧ measurementCount (lowCopy w)=0 := by
  have h := copyRegister_counts none (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length])
  simpa [lowCopy] using h

theorem forward_counts (w : Nat → Wire) :
    toffoliCount (forward w)=508 ∧ measurementCount (forward w)=508 := by
  have h := hAdd_counts w false
  have k := kAdd_counts w false
  have c := lowCopy_counts w
  have r := rotate_counts (wireBlock w 770 258)
  simp [forward,toffoliCount_append,measurementCount_append,h.1,h.2,k.1,k.2,
    c.1,c.2,r.1,r.2.1,toffoliCount,measurementCount]

theorem inverse_counts (w : Nat → Wire) :
    toffoliCount (inverse w)=508 ∧ measurementCount (inverse w)=508 := by
  have h := hAdd_counts w true
  have k := kAdd_counts w true
  have c := lowCopy_counts w
  have r := rotate_counts (wireBlock w 770 258)
  simp [inverse,toffoliCount_append,measurementCount_append,h.1,h.2,k.1,k.2,
    c.1,c.2,r.2.2.1,r.2.2.2,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.hAdd_counts
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kAdd_counts
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.lowCopy_counts
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.forward_counts
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.inverse_counts
