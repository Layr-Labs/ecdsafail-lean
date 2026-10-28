import ECDSAAdd.Arithmetic.OffsetBorrowedFieldProgram
import ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCallerClean
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroProgram
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedField
open BalancedField Secp256k1 DirectSkywalk
attribute [local irreducible] run BalancedCircuit.coreProgram TerminalParityOffset.program

private theorem scalarFacts (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.sourceGuard≠L.parity ∧ L.ymsb≠L.sourceGuard ∧ L.ymsb≠L.parity ∧
    L.sign≠L.parity ∧ L.sign≠L.sourceGuard := by
  have f := BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at f
  tauto

private theorem nativeWorkAway (L : BalancedCircuit.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈BalancedCircuit.work L) : q∉L.r := by
  intro qr
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr qr
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,BalancedCircuit.work,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.count_append,List.count_cons,List.count_nil] at h a b
  omega

private theorem offsetWorkAway (L : BalancedCleanupOffset.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.offsetCarry) : q∉L.r := by
  have data : (L.r++(L.y++(L.carry++L.offsetCarry))).Nodup := by
    simpa only [List.append_assoc] using (List.nodup_append'.mp (L.allND hn)).2.1
  have dis := (List.nodup_append'.mp data).2.2
  intro h
  exact List.disjoint_left.mp dis h (List.mem_append_right _ (List.mem_append_right _ hq))

/-- Exact forward kernel with the existing caller's clean-mask invariant.
The high-source zero is derived by callerCout_clean at public call sites.
All records preserve phase; both used carry banks and every outsider return. -/
theorem program_correct (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis sign=B)
    (hr : signedRegValue (balancedSharedPorts w sign).r s.basis=X)
    (hyr : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hhi : s.basis (w 1026)=false) :
    let t := run (program w sign) m s
    t.phase=s.phase ∧
    regValue (balancedSharedPorts w sign).r t.basis=encodeWord 256 (halfResult (rawSum B X Y)) ∧
    (∀q∈work w sign,t.basis q=false) ∧
    (∀q,q∉(balancedSharedPorts w sign).r → t.basis q=s.basis q) := by
  let L := balancedSharedPorts w sign
  let O := OffsetCleanupBorrowedCaller.layout w sign
  let R := halfResult (rawSum B X Y)
  let ms := m.drop (measurementCount (BalancedCircuit.coreProgram L))
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have nd : L.wires.Nodup := balancedSharedPorts_nodup w sign hn own
  have widths : L.Widths := balancedSharedPorts_widths w sign
  have clean : ∀q∈BalancedCircuit.work L,s.basis q=false :=
    balancedSharedPorts_clean w sign s.basis hw hu
  generalize ec : run (BalancedCircuit.coreProgram L) m s=c
  have core := BalancedCircuit.core_correct L widths nd B X Y hx hy s m hs hr hyr clean
  rw [ec] at core
  have facts := scalarFacts L nd
  have sgp := facts.1
  have ysg := facts.2.1
  have ypa := facts.2.2.1
  have qflag (q f : Wire) (hq : q∈L.y)
      (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : q≠f := by
    intro e
    have mem : f∈L.y := e ▸ hq
    exact BalancedCircuit.flagAway L nd f hf (by simp [mem])
  have yr (q : Wire) (hq : q∈L.y) : q∉L.r := by
    have a := BalancedCircuit.compose_raw_away L nd q (by simp [hq])
    exact fun h => a (by simp [BalancedCircuit.rawTarget,h])
  have cY : regValue L.y c.basis=encodeWord 256 Y :=
    (regValue_congr L.y c.basis s.basis (fun q hq => core.2.2.2.2.2 q (yr q hq)
      (qflag q L.parity hq (by simp)) (qflag q L.sourceGuard hq (by simp)))).trans
        (BalancedCircuit.word_encoding L.y 256 (BalancedCleanup.widths L.toLayout widths).2.2.1 s.basis Y hyr)
  have signAway : L.sign∉L.r := fun h => BalancedCircuit.flagAway L nd L.sign (by simp) (by simp [h])
  have cS : c.basis L.sign=B :=
    (core.2.2.2.2.2 L.sign signAway facts.2.2.2.1 facts.2.2.2.2).trans hs
  have extra := OffsetCleanupBorrowedCaller.forwardCarry_clean w sign hn hsOut B X Y hx hy
    s m hs hr hyr hw hu
  change ∀q∈OffsetCleanupBorrowedCaller.carry w,(run (BalancedCircuit.coreProgram L) m s).basis q=false at extra
  rw [ec] at extra
  have cout := OffsetCleanupBorrowedCaller.forwardCout_frame w sign hn hsOut s m
  change (run (BalancedCircuit.coreProgram L) m s).basis (w 1026)=s.basis (w 1026) at cout
  rw [ec] at cout
  have ccout : c.basis O.cout=false := cout.trans hhi
  have parity : originalParity (rawSum B X Y)=decide (q < |2*R-signedY B Y|) :=
    decide_eq_decide.mpr (halfResult_parity_interval B X Y hx hy)
  have oND : O.wires.Nodup := OffsetCleanupBorrowedCaller.nodup w sign hn hsOut
  have oWidths : O.Widths := OffsetCleanupBorrowedCaller.widths w sign
  have center : Centered R := (halfResult_spec _ (rawSum_bounds B X Y hx hy)).1
  have lower : c.basis O.lower=false := by
    change c.basis L.lower=false
    exact core.2.2.2.2.1 _ (by simp [BalancedCircuit.coreClean])
  have one : c.basis O.one=false := by
    change c.basis L.one=false
    exact core.2.2.2.2.1 _ (by simp [BalancedCircuit.coreClean])
  have ownCarry : ∀q∈O.carry,c.basis q=false := by
    change ∀q∈L.carry,c.basis q=false
    intro q hq
    exact core.2.2.2.2.1 q (by simp [BalancedCircuit.coreClean,hq])
  have oldcl := BalancedCleanupOffsetZero.correct O oWidths oND R Y B center hy c ms
    core.2.1 cY cS lower one ccout ownCarry extra
    (core.2.2.1.trans parity)
  have eqcl := TerminalParityOffset.correct O oWidths oND R Y B center hy c ms
    core.2.1 cY cS lower one ccout ownCarry extra
    (core.2.2.1.trans parity)
  have cl := eqcl.trans oldcl
  let d : State := ⟨c.phase,writeBit c.basis L.parity false⟩
  have dp : d.basis L.sourceGuard=s.basis L.ymsb :=
    (show d.basis L.sourceGuard=c.basis L.sourceGuard from by simp [d,writeBit,sgp]).trans core.2.2.2.1
  have dy : d.basis L.ymsb=s.basis L.ymsb := by
    have hy0 : L.ymsb∈L.y := by simp [BalancedCleanup.Layout.y]
    exact (show d.basis L.ymsb=c.basis L.ymsb from by simp [d,writeBit,ypa]).trans
      (core.2.2.2.2.2 L.ymsb (yr _ hy0) ypa ysg)
  let t : State := ⟨c.phase,writeBit d.basis L.sourceGuard false⟩
  have actual : run (program w sign) m s=t := by
    change run (BalancedCircuit.coreProgram L++(TerminalParityOffset.program O++[.CX L.ymsb L.sourceGuard])) m s=t
    rw [run_append,run_take,ec]
    change run (TerminalParityOffset.program O++[.CX L.ymsb L.sourceGuard]) ms c=t
    rw [run_append,run_take,cl]
    change run [.CX L.ymsb L.sourceGuard] _ d=t
    simp only [run]
    change ⟨c.phase,writeBit d.basis L.sourceGuard (d.basis L.sourceGuard ^^ d.basis L.ymsb)⟩=t
    rw [dp,dy,Bool.xor_self]
  have frame (q : Wire) (hq : q∉L.r) : t.basis q=s.basis q := by
    by_cases hp : q=L.parity
    · subst q
      simp only [t,d,writeBit,Function.update_of_ne (Ne.symm sgp),Function.update_self]
      exact (clean _ (by simp [BalancedCircuit.work])).symm
    by_cases hg : q=L.sourceGuard
    · subst q
      simp only [t,writeBit,Function.update_self]
      exact (clean _ (by simp [BalancedCircuit.work])).symm
    simp only [t,d,writeBit,Function.update_of_ne hg,Function.update_of_ne hp]
    exact core.2.2.2.2.2 q hq hp hg
  have nativeAway (q : Wire) (hq : q∈BalancedCircuit.work L) : q∉L.r := by
    exact nativeWorkAway L nd q hq
  have borrowedAway (q : Wire) (hq : q∈OffsetCleanupBorrowedCaller.carry w) : q∉L.r := by
    exact offsetWorkAway O oND q hq
  have highAway : w 1026∉L.r := by
    change w 1026∉(balancedSharedPorts w sign).r
    rw [balancedSharedPorts_r]
    exact arith_block_away w hn 1026 2056 256 (by omega) (by omega) (by omega)
  rw [actual]
  refine ⟨core.1,?_,?_,frame⟩
  · exact (regValue_congr L.r t.basis c.basis (by
      intro q hq
      have np : q≠L.parity := fun e => BalancedCircuit.flagAway L nd L.parity (by simp) (by simp [e ▸ hq])
      have ng : q≠L.sourceGuard := fun e => BalancedCircuit.flagAway L nd L.sourceGuard (by simp) (by simp [e ▸ hq])
      simp only [t,d,writeBit,Function.update_of_ne ng,Function.update_of_ne np])).trans core.2.1
  · intro q hq
    change q∈BalancedCircuit.work L++OffsetCleanupBorrowedCaller.carry w++[w 1026] at hq
    rcases List.mem_append.mp hq with hq|hq
    · rcases List.mem_append.mp hq with hq|hq
      · exact (frame q (nativeAway q hq)).trans (clean q hq)
      · exact (frame q (borrowedAway q hq)).trans (OffsetCleanupBorrowedCaller.entryCarry_clean w s.basis hw q hq)
    · have eq : q=w 1026 := by simpa using hq
      subst q
      exact (frame _ highAway).trans hhi


end ECDSAAdd.Arithmetic.OffsetBorrowedField
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedField.program_correct
