import ECDSAAdd.Arithmetic.BalancedCoreComposeProof
import ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCallerLayout
import ECDSAAdd.Arithmetic.TerminalParityOldSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedField

/-- Forward field emission. The second carry bank is supplied by
existing terminal-zero mask sites, deliberately excluding the live guard765. -/
def program (w : Nat → Wire) (sign : Wire) : Program :=
  BalancedCircuit.coreProgram (balancedSharedPorts w sign)++
    (TerminalParityOffset.program (OffsetCleanupBorrowedCaller.layout w sign)++
      [.CX (balancedSharedPorts w sign).ymsb (balancedSharedPorts w sign).sourceGuard])

/-- Every used clean bank/flag, including the canonical high source site
borrowed as the cleanup comparison carry-in. Ghost descriptor roles are absent. -/
def work (w : Nat → Wire) (sign : Wire) : List Wire :=
  BalancedCircuit.work (balancedSharedPorts w sign)++
    OffsetCleanupBorrowedCaller.carry w++[w 1026]

theorem core_counts (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (BalancedCircuit.coreProgram L)=513 ∧
    measurementCount (BalancedCircuit.coreProgram L)=513 := by
  have full := BalancedCircuit.counts L hw
  have cleanup := BalancedCleanup.counts L.toLayout hw
  rw [BalancedCircuit.program_eq_core] at full
  simp only [toffoliCount_append,measurementCount_append,cleanup.1,cleanup.2,
    show toffoliCount [.CX L.ymsb L.sourceGuard]=0 from rfl,
    show measurementCount [.CX L.ymsb L.sourceGuard]=0 from rfl,Nat.add_zero] at full
  omega

theorem counts (w : Nat → Wire) (sign : Wire) :
    toffoliCount (program w sign)=1022 ∧ measurementCount (program w sign)=1023 := by
  have c := core_counts (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  have o := TerminalParityOffset.counts (OffsetCleanupBorrowedCaller.layout w sign)
    (OffsetCleanupBorrowedCaller.widths w sign)
  simp only [program,toffoliCount_append,measurementCount_append,c.1,c.2,o.1,o.2]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.OffsetBorrowedField
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedField.counts
