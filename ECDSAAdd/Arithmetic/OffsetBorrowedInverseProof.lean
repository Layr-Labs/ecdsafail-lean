import ECDSAAdd.Arithmetic.OffsetBorrowedInverseParity
import ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCallerClean
import ECDSAAdd.Arithmetic.BalancedInverseComposeProof

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedInverse
open BalancedField BalancedCircuit DirectSkywalk
attribute [local irreducible] run

private theorem lower_mem_work (L : BalancedCircuit.Layout) : L.lower∈BalancedCircuit.work L := by
  simp [BalancedCircuit.work]

private theorem one_mem_work (L : BalancedCircuit.Layout) : L.one∈BalancedCircuit.work L := by
  simp [BalancedCircuit.work]

private theorem carry_mem_work (L : BalancedCircuit.Layout) (a : Wire) (ha : a∈L.carry) :
    a∈BalancedCircuit.work L := List.mem_append_right _ ha

private theorem old_layout (L : BalancedCircuit.Layout) :
    BalancedInverse.program L=[.CX L.ymsb L.sourceGuard]++
      BalancedInverse.recoverParity L++tail L := by
  simp only [BalancedInverse.program,tail,List.append_assoc]

private theorem run_prefix (a b : Wire) (oracle rest : Program) (m : List Bool) (s : State) :
    run ([.CX a b]++oracle++rest) m s=
      run rest (m.drop (measurementCount oracle))
        (run oracle m (run [.CX a b] m s)) := by
  rw [List.append_assoc,run_append,run_take]
  change run (oracle++rest) m (run [.CX a b] m s)=_
  rw [run_append,run_take]

private theorem guard_records (a b : Wire) (m n : List Bool) (s : State) :
    run [.CX a b] m s=run [.CX a b] n s := by
  simp only [run]

private theorem index_ne (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i j : Nat) (hi : i<2314) (hj : j<2314) (hne : i≠j) : w i≠w j :=
  fun h => hne (skywalkShared_index_inj w hn i j hi hj h)

/-- The borrowed bank omits precisely the live source guard. -/
private theorem bank_guard_away (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (a : Wire) (ha : a∈OffsetCleanupBorrowedCaller.carry w) : a≠w 765 := by
  simp only [OffsetCleanupBorrowedCaller.carry,List.mem_append] at ha
  rcases ha with ha|ha
  · intro e
    exact arith_block_away w hn 765 512 253 (by omega) (by omega) (by omega) (e ▸ ha)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals exact index_ne w hn _ _ (by omega) (by omega) (by omega)

private theorem bank_target_away (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (a : Wire)
    (ha : a∈OffsetCleanupBorrowedCaller.carry w) : a∉(balancedSharedPorts w sign).r := by
  rw [balancedSharedPorts_r]
  simp only [OffsetCleanupBorrowedCaller.carry,List.mem_append] at ha
  rcases ha with ha|ha
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_range'_1] at hi
    exact arith_block_away w hn i 2056 256 (by omega) (by omega) (by omega)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals exact arith_block_away w hn _ 2056 256 (by omega) (by omega) (by omega)

/-- 254 padding records align the 764-record original recovery with the
510-record replacement. Their actual XOR outputs agree on independent records. -/
theorem program_equiv (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool)
    (hR : signedRegValue (balancedSharedPorts w sign).r s.basis=R)
    (hY : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hS : s.basis sign=B)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hhigh : s.basis (w 1026)=false) :
    run (program w sign) m s=
      run (BalancedInverse.program (balancedSharedPorts w sign))
        (List.replicate 254 false++m) s := by
  let L := balancedSharedPorts w sign
  let n := List.replicate 254 false++m
  let u := run [.CX L.ymsb L.sourceGuard] m s
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have nd := balancedSharedPorts_nodup w sign hn own
  have widths := balancedSharedPorts_widths w sign
  have clean := balancedSharedPorts_clean w sign s.basis hw hu
  have keep (a : Wire) (ha : a≠L.sourceGuard) : u.basis a=s.basis a := by
    simp only [u,run,writeBit,Function.update_of_ne ha]
  have dataAway (a : Wire) (ha : a∈L.r++L.y++L.carry) : a≠L.sourceGuard :=
    fun e => flagAway L nd L.sourceGuard (by simp) (e ▸ ha)
  have R₁ : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 (BalancedCleanup.widths L.toLayout widths).2.1 s.basis R hR)
    exact regValue_congr _ _ _ (fun a ha => keep a (dataAway a (by simp [ha])))
  have Y₁ : regValue L.y u.basis=encodeWord 256 Y := by
    apply Eq.trans _ (word_encoding L.y 256 (BalancedCleanup.widths L.toLayout widths).2.2.1 s.basis Y hY)
    exact regValue_congr _ _ _ (fun a ha => keep a (dataAway a (by simp [ha])))
  have scalar := scalarND L nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at scalar
  rcases scalar with ⟨⟨_,_,_,_,gSign,gLower,gOne,_,_,_⟩,_⟩
  have S₁ : u.basis sign=B := (keep L.sign (Ne.symm gSign)).trans hS
  have low₁ : u.basis (w 1797)=false :=
    (keep L.lower (Ne.symm gLower)).trans (clean L.lower (lower_mem_work L))
  have one₁ : u.basis (w 1027)=false :=
    (keep L.one (Ne.symm gOne)).trans (clean L.one (one_mem_work L))
  have high_ne : w 1026≠L.sourceGuard := by
    change w 1026≠w 765
    exact index_ne w hn 1026 765 (by omega) (by omega) (by omega)
  have high₁ : u.basis (w 1026)=false := (keep _ high_ne).trans hhigh
  have carry₁ : ∀a∈L.carry,u.basis a=false := by
    intro a ha
    exact (keep a (dataAway a (by simp [ha]))).trans (clean a (carry_mem_work L a ha))
  have bank₁ : ∀a∈OffsetCleanupBorrowedCaller.carry w,u.basis a=false := by
    intro a ha
    exact (keep a (by simpa only [L,balancedSharedPorts] using bank_guard_away w hn a ha)).trans
      (OffsetCleanupBorrowedCaller.entryCarry_clean w s.basis hw a ha)
  have oracle := recoverParity_equiv w sign hn hsOut R Y B hr hy u m n
    R₁ Y₁ S₁ low₁ one₁ high₁ carry₁ bank₁
  have oldCount : measurementCount (BalancedInverse.recoverParity L)=764 := by
    simpa only [BalancedInverse.recoverParity] using (BalancedCleanup.counts L.toLayout widths).2
  have freshCount : measurementCount (recoverParity w sign)=510 := by
    simpa only [recoverParity] using (BalancedCleanupOffsetZero.counts
      (OffsetCleanupBorrowedCaller.layout w sign) (OffsetCleanupBorrowedCaller.widths w sign)).2
  have align : n.drop 764=m.drop 510 := by simp [n,List.drop_append]
  have oldGuard : run [.CX L.ymsb L.sourceGuard] n s=u := guard_records _ _ n m s
  have freshRun : run (program w sign) m s=
      run (tail L) (m.drop 510) (run (recoverParity w sign) m u) := by
    rw [program,run_prefix,freshCount]
  have oldRun : run (BalancedInverse.program L) n s=
      run (tail L) (n.drop 764) (run (BalancedInverse.recoverParity L) n u) := by
    rw [old_layout,run_prefix,oldCount,oldGuard]
  rw [freshRun,oldRun,align,oracle]

/-- Complete cheaper inverse, from the actual caller invariant: phase,
centered result, native workspace, borrowed bank, and every outside-R bit. -/
theorem program_correct (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool)
    (hR : signedRegValue (balancedSharedPorts w sign).r s.basis=R)
    (hY : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hS : s.basis sign=B)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hhigh : s.basis (w 1026)=false) :
    let t := run (program w sign) m s
    t.phase=s.phase ∧
    regValue (balancedSharedPorts w sign).r t.basis=encodeWord 256 (BalancedInverse.result B R Y) ∧
    (∀a∈BalancedCircuit.work (balancedSharedPorts w sign),t.basis a=false) ∧
    (∀a∈OffsetCleanupBorrowedCaller.carry w,t.basis a=false) ∧
    t.basis (w 1026)=false ∧
    (∀a,a∉(balancedSharedPorts w sign).r → t.basis a=s.basis a) := by
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have native := BalancedInverse.program_correct (balancedSharedPorts w sign)
    (balancedSharedPorts_widths w sign) (balancedSharedPorts_nodup w sign hn own)
    B R Y hr hy s (List.replicate 254 false++m) hS hR hY
    (balancedSharedPorts_clean w sign s.basis hw hu)
  have eq := program_equiv w sign hn hsOut R Y B hr hy s m hR hY hS hw hu hhigh
  dsimp only
  rw [eq]
  refine ⟨native.1,native.2.1,native.2.2.1,?_,?_,native.2.2.2⟩
  · intro a ha
    exact (native.2.2.2 a (bank_target_away w sign hn a ha)).trans
      (OffsetCleanupBorrowedCaller.entryCarry_clean w s.basis hw a ha)
  · have high_away : w 1026∉(balancedSharedPorts w sign).r := by
      rw [balancedSharedPorts_r]
      exact arith_block_away w hn 1026 2056 256 (by omega) (by omega) (by omega)
    exact (native.2.2.2 _ high_away).trans hhigh

end ECDSAAdd.Arithmetic.OffsetBorrowedInverse
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedInverse.program_equiv
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedInverse.program_correct
