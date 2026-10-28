import ECDSAAdd.Arithmetic.BalancedFieldInverseParity
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroProgram
import ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCallerLayout
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedInverse
open BalancedField
attribute [local irreducible] toffoliCount measurementCount run

def recoverParity (w : Nat → Wire) (sign : Wire) : Program :=
  BalancedCleanupOffsetZero.program (OffsetCleanupBorrowedCaller.layout w sign)

/-- The replacement is the same XOR oracle for every target value and for
independent measurement streams. The caller must provide the actual clean
borrowed bank and canonical source extension, not a reversed measurement. -/
theorem recoverParity_equiv (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y)
    (s : State) (m n : List Bool)
    (hR : regValue (balancedSharedPorts w sign).r s.basis=encodeWord 256 R)
    (hY : regValue (balancedSharedPorts w sign).y s.basis=encodeWord 256 Y)
    (hS : s.basis sign=B) (hz : s.basis (w 1797)=false)
    (ho : s.basis (w 1027)=false) (hhigh : s.basis (w 1026)=false)
    (hc : ∀q∈(balancedSharedPorts w sign).carry,s.basis q=false)
    (hd : ∀q∈OffsetCleanupBorrowedCaller.carry w,s.basis q=false) :
    run (recoverParity w sign) m s=
      run (BalancedInverse.recoverParity (balancedSharedPorts w sign)) n s := by
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    apply hsOut
    simp only [skywalkSharedWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨i,by have bound := balancedSharedIds_bound i hi; omega,rfl⟩
  have nd := balancedSharedPorts_nodup w sign hn own
  have old := BalancedCleanupXor.xor_correct (balancedSharedPorts w sign).toLayout
    (balancedSharedPorts_widths w sign) (List.nodup_append'.mp nd).2.1
    R Y B hr hy s n hR hY hS hz ho hc
  have fresh := BalancedCleanupOffsetZero.xor_correct (OffsetCleanupBorrowedCaller.layout w sign)
    (OffsetCleanupBorrowedCaller.widths w sign) (OffsetCleanupBorrowedCaller.nodup w sign hn hsOut)
    R Y B hr hy s m hR hY hS hz ho hhigh hc hd
  exact fresh.trans old.symm

def tail (L : BalancedCircuit.Layout) : Program :=
  BalancedInverse.recoverSelectors L++rotateLeft (BalancedCircuit.rawTarget L)++
    BalancedInverse.undoFold L++BalancedInverse.undoPreparation L++
    BalancedInverse.rawSubtract L++(BalancedCircuit.seedViews L).reverse

/-- Independently measured inverse emission with the cheaper recovery oracle. -/
def program (w : Nat → Wire) (sign : Wire) : Program :=
  let L := balancedSharedPorts w sign
  [.CX L.ymsb L.sourceGuard]++recoverParity w sign++tail L

private theorem original_program_layout (L : BalancedCircuit.Layout) :
    BalancedInverse.program L=[.CX L.ymsb L.sourceGuard]++
      BalancedInverse.recoverParity L++tail L := by
  simp only [BalancedInverse.program,tail,List.append_assoc]

private theorem tail_counts (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (tail L)=513 ∧ measurementCount (tail L)=513 := by
  have full := BalancedInverse.counts L hw
  have old := BalancedCleanup.counts L.toLayout hw
  have layout := original_program_layout L
  rw [layout] at full
  simp only [BalancedInverse.recoverParity,toffoliCount_append,measurementCount_append,
    old.1,old.2,show toffoliCount [.CX L.ymsb L.sourceGuard]=0 by simp only [toffoliCount],
    show measurementCount [.CX L.ymsb L.sourceGuard]=0 by simp only [measurementCount]] at full
  omega

theorem counts (w : Nat → Wire) (sign : Wire) :
    toffoliCount (program w sign)=1023 ∧ measurementCount (program w sign)=1023 := by
  have fresh := BalancedCleanupOffsetZero.counts (OffsetCleanupBorrowedCaller.layout w sign)
    (OffsetCleanupBorrowedCaller.widths w sign)
  have old := tail_counts (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  simp only [program,recoverParity,toffoliCount_append,measurementCount_append,fresh.1,fresh.2,
    old.1,old.2,show toffoliCount [.CX (balancedSharedPorts w sign).ymsb
      (balancedSharedPorts w sign).sourceGuard]=0 by simp only [toffoliCount],
    show measurementCount [.CX (balancedSharedPorts w sign).ymsb
      (balancedSharedPorts w sign).sourceGuard]=0 by simp only [measurementCount]]
  norm_num

end ECDSAAdd.Arithmetic.OffsetBorrowedInverse
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedInverse.recoverParity_equiv
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedInverse.counts
