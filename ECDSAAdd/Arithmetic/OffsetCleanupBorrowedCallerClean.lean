import ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCallerLayout
import ECDSAAdd.Arithmetic.BalancedCoreComposeProof
import ECDSAAdd.Arithmetic.BalancedSharedFraming
import ECDSAAdd.Arithmetic.DirectSkywalkInput

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller
open BalancedField Secp256k1 DirectSkywalk
attribute [local irreducible] run wires

private theorem core_support_sub (L : BalancedCircuit.Layout) :
    wires (BalancedCircuit.coreProgram L) ⊆ wires (BalancedCircuit.program L) := by
  intro q hq
  simp only [BalancedCircuit.program_eq_core,wires_append,Finset.mem_union]
  exact Or.inl (Or.inl hq)

private theorem wireNe (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i j : Nat) (hi : i < 2314) (hj : j < 2314) (hne : i ≠ j) : w i ≠ w j :=
  fun he => hne (skywalkShared_index_inj w hn i j hi hj he)

/-- This is the actual caller's existing field-work invariant. Past G
records occupy 0..511; the terminal-clear mask is 512..768. -/
theorem maskBit_zero (w : Nat → Wire) (s : BasisState)
    (hw : regValue (skywalkSharedField w).work s=0) (i : Nat)
    (hi0 : 512 ≤ i) (hi : i < 769) : s (w i)=false := by
  have hm := arith_mem w 512 257 i hi0 (by omega)
  exact (regValue_zero _ _).mp hw _ (by
    simp [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,hm])

theorem entryCarry_clean (w : Nat → Wire) (s : BasisState)
    (hw : regValue (skywalkSharedField w).work s=0) : ∀q∈carry w,s q=false := by
  intro q hq
  simp only [carry,List.mem_append] at hq
  rcases hq with hq|hq
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact maskBit_zero w s hw i (by omega) (by omega)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl
    all_goals exact maskBit_zero w s hw _ (by omega) (by omega)

/-- Every canonical original 257-bit source has zero extension; the
existing low-pair caller frame preserves that site throughout the replay. -/
theorem callerCout_clean (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (base current : BasisState) (Y : Fp) (X Z : Nat)
    (hy : regValue (skywalkSharedField w).a base=Y.val)
    (hframe : PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base X Z current) :
    current (w 1026)=false := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have a := wireBlock_append w 770 256 1
  have one : wireBlock w 1026 1=[w 1026] := by simp [wireBlock,List.range']
  have av : (skywalkSharedField w).a=wireBlock w 770 256++[w 1026] := by
    change wireBlock w 770 257=_
    simpa only [Nat.reduceAdd,one] using a.symm
  rw [av] at hy
  have high := (balancedCanonical_high_zero _ _ base Y.val
    (by rw [wireBlock_length]; exact (ZMod.val_lt Y).trans (by norm_num [p])) hy).2
  exact (hframe.2.2 _
    (arith_block_away w hn 1026 2056 256 (by omega) (by omega) (by omega))
    (arith_block_away w hn 1026 770 256 (by omega) (by omega) (by omega))).trans high

/-- At the actual forward-core cleanup boundary, the mask prefix is
preserved, and old Minus/Plus/Cout are clean by core_correct. The live
source guard at 765 is deliberately omitted. No extra clean-bank premise. -/
theorem forwardCarry_clean (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis sign=B)
    (hr : signedRegValue (balancedSharedPorts w sign).r s.basis=X)
    (hyr : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0) :
    ∀q∈carry w,(run (BalancedCircuit.coreProgram (balancedSharedPorts w sign)) m s).basis q=false := by
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have nd := balancedSharedPorts_nodup w sign hn own
  have native := BalancedCircuit.core_correct (balancedSharedPorts w sign)
    (balancedSharedPorts_widths w sign) nd B X Y hx hy s m hs hr hyr
    (balancedSharedPorts_clean w sign s.basis hw hu)
  intro q hq
  simp only [carry,List.mem_append] at hq
  rcases hq with hq|hq
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    have away : w i∉(balancedSharedPorts w sign).r := by
      rw [balancedSharedPorts_r]
      exact arith_block_away w hn i 2056 256 (by omega) (by omega) (by omega)
    have keep := native.2.2.2.2.2 (w i) away
      (wireNe w hn i 1796 (by omega) (by omega) (by omega))
      (wireNe w hn i 765 (by omega) (by omega) (by omega))
    exact keep.trans (maskBit_zero w s.basis hw i (by omega) (by omega))
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl
    all_goals exact native.2.2.2.2.1 _ (by simp [BalancedCircuit.coreClean,balancedSharedPorts])

/-- The native core never emits a gate on the canonical high source site.
Thus the derived caller high-zero property reaches active cleanup Cout. -/
theorem forwardCout_frame (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (s : State) (m : List Bool) :
    (run (BalancedCircuit.coreProgram (balancedSharedPorts w sign)) m s).basis (w 1026)=
      s.basis (w 1026) := by
  have own : w 1026∈skywalkSharedWires w := arith_mem w 0 2314 1026 (by omega) (by omega)
  have ns : w 1026 ≠ sign := fun e => hsOut (e ▸ own)
  have neq (j : Nat) (hj : j < 2314) (hne : 1026 ≠ j) : w 1026 ≠ w j :=
    wireNe w hn 1026 j (by omega) hj hne
  have rtail := arith_block_away w hn 1026 2057 254 (by omega) (by omega) (by omega)
  have ylow := arith_block_away w hn 1026 770 255 (by omega) (by omega) (by omega)
  have carryAway := arith_block_away w hn 1026 1540 256 (by omega) (by omega) (by omega)
  have away : w 1026∉(balancedSharedPorts w sign).wires := by
    simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,balancedSharedPorts,
      List.mem_append,List.mem_cons,List.not_mem_nil,rtail,ylow,carryAway,ns,
      neq 765 (by omega) (by omega),neq 768 (by omega) (by omega),
      neq 767 (by omega) (by omega),neq 766 (by omega) (by omega),
      neq 1796 (by omega) (by omega),neq 1797 (by omega) (by omega),
      neq 1027 (by omega) (by omega),neq 2311 (by omega) (by omega),
      neq 1025 (by omega) (by omega),neq 2056 (by omega) (by omega),
      or_false,not_false_eq_true]
  have sub := core_support_sub (balancedSharedPorts w sign)
  have support := balancedSharedPorts_support w sign
  have outside : w 1026∉wires (BalancedCircuit.coreProgram (balancedSharedPorts w sign)) := by
    intro hq
    exact away (List.mem_toFinset.mp (support (sub hq)))
  exact run_preserves_outside (BalancedCircuit.coreProgram (balancedSharedPorts w sign)) m s (w 1026) outside

/-- The proposed contiguous bank cannot be used unchanged at cleanup:
the actual retained guard is the source's sign and belongs to that bank. -/
theorem contiguous_guard_conflict (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).sourceGuard∈wireBlock w 512 256 := by
  exact arith_mem w 512 256 765 (by omega) (by omega)

end ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller
#print axioms ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller.callerCout_clean
#print axioms ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller.forwardCarry_clean
#print axioms ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller.forwardCout_frame
#print axioms ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller.contiguous_guard_conflict
