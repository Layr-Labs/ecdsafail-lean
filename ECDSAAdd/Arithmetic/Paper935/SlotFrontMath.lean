import ECDSAAdd.Arithmetic.Paper935.SlotInputValues

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

/-- Address-only conditions needed by the previously proved row/counter
semantics, in addition to the ordinary-gate checks. -/
structure SlotFront.MathChecks (P : SlotFront) (F : SlotRegisters) (w : RowWindow) : Prop where
  beforeApart : List.Disjoint (P.layout.active::P.layout.q::F.counter) (P.layout.before.rows.flatMap WindowRow.wires)
  afterApart : List.Disjoint (P.layout.active::P.layout.q::F.counter) (P.layout.after.rows.flatMap WindowRow.wires)
  exitApart : List.Disjoint F.counter (P.exitBank.rows.flatMap WindowRow.wires)
  counterView : F.counter=F.counter.dropLast++[F.counter.getLastD 0]
  tags : [F.frozen,P.layout.active,F.counter.getLastD 0,P.layout.glow,P.layout.parity,P.layout.q].Nodup
  preparation : ∀ q∈P.layout.u::P.layout.k::(P.layout.before.rows.flatMap WindowRow.wires++F.counter),
    q≠P.layout.active ∧ q≠P.layout.parity ∧ q≠P.layout.q
  swapAway : P.layout.q∉P.exitBank.rows.flatMap WindowRow.wires
  coefficientWidth : 1≤w.fv
  counterWidth : 2≤F.counter.length
  persistent : ∀ q∈F.one::F.frozen::F.work0::F.work1::F.offset,
    q∈P.addArena.live ∧ q∉P.layout.before.rows.flatMap WindowRow.wires ∧ q∉F.counter ∧
    q≠P.layout.active ∧ q≠P.layout.parity ∧ q≠P.layout.q

structure SlotRegisters.MidValues (F : SlotRegisters) (s : BasisState) (old : PinState) : Prop where
  one : s F.one=true
  frozen : s F.frozen=old.frozen
  parity : s F.parity=decide (ECDSAAdd.Divsteps.bbit old.rows=1)
  active : s F.active= !old.frozen
  swap : s F.swap=false
  work0 : s F.work0=false
  work1 : s F.work1=false
  counter : signedRegValue F.counter s=(if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows).z
  offset : regValue F.offset s=old.offset

/-- Actual prefix padding, routed arithmetic, exit resizing and measured
counter update implement the mathematical row step with phase preserved. -/
theorem SlotFront.Compiled.run_math (P : SlotFront) (A : Arena) (b : WindowBank)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (compiled : P.Compiled A b addWidth exitWidth F)
    (physical : P.PhysicalChecks F) (checks : P.MathChecks F exitWidth)
    (old : PinState) (s : State) (m : List Bool) (ready : A.Ready s.basis)
    (rows : b.Encodes s.basis old.rows) (prefit : addWidth.Fits old.rows)
    (values : F.Values s.basis old) (owned : F.wires.toFinset⊆A.live)
    (away : List.Disjoint F.wires (b.rows.flatMap WindowRow.wires))
    (p : Int) (inv : ECDSAAdd.Divsteps.Inv p old.rows) (odd : p%2=1) (fodd : old.rows.f%2=1)
    (frozenZero : old.frozen=true → old.rows.g=0)
    (gfit : old.frozen=false → PayloadFits (P.layout.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep old.rows).g))
    (gvfit : old.frozen=false → PayloadFits (P.layout.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep old.rows).gv)
    (fvfit : old.frozen=false → PayloadFits (P.layout.vmid.length+1) (ECDSAAdd.Divsteps.zStep old.rows).fv)
    (exitfit : exitWidth.Fits (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows))
    (zfit : PayloadFits (F.counter.length-1) (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows).z) :
    let t := run (P.program F) m s
    t.phase=s.phase ∧ P.exitArena.Ready t.basis ∧
    P.exitBank.Encodes t.basis (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows) ∧
    F.MidValues t.basis old := by
  let v := run P.padding m s
  let ms := m.drop (measurementCount P.padding)
  have padding := compiled.padding_state P A b addWidth exitWidth F old s m ready rows prefit values owned away
  rcases padding with ⟨vready,vrows,vvalues,vowned,vmeta⟩
  have layouts := compiled.layouts P A b addWidth exitWidth F physical.1
  obtain ⟨valid,view,qeq,beq,ueq,keq,aeq⟩ :=
    compileRoutedBank_contract F.swap F.parity F.work0 F.work1 F.active P.addBank P.layout compiled.routed
  have ownCounter : (P.layout.active::P.layout.q::F.counter).toFinset⊆P.addArena.live := by
    rw [aeq,qeq]
    intro q hq
    apply vmeta
    simp only [List.mem_toFinset,List.mem_cons] at hq
    rcases hq with rfl|rfl|hq
    · simp [SlotRegisters.wires]
    · simp [SlotRegisters.wires]
    · simp [SlotRegisters.wires,hq]
  have ownParity : P.layout.parity∈P.addArena.live := by
    rw [beq]
    exact vmeta (by simp [SlotRegisters.wires])
  have body := P.layout.retiredWindow_spec valid P.exitBank exitWidth P.addArena P.exitArena P.counterArena
    P.resizing layouts.2.2.2.1 F.counter P.zero P.carry physical.2.1 layouts.2.2.2.2.1 layouts.2.2.2.2.2.1
    vowned.2 ownCounter checks.beforeApart checks.afterApart checks.exitApart layouts.2.2.2.2.2.2
    F.frozen (F.counter.getLastD 0) F.counter.dropLast checks.counterView checks.tags ownParity checks.preparation
    checks.swapAway physical.2.2.2.2.1 checks.coefficientWidth p old.rows inv odd old.frozen fodd v ms
    vvalues.frozen vvalues.counter (by rw [ueq]; exact vvalues.work0) (by rw [keq]; exact vvalues.work1)
    (by rw [aeq]; exact vvalues.active) (by rw [qeq]; exact vvalues.swap) (by rw [beq]; exact vvalues.parity)
    vrows frozenZero gfit gvfit fvfit vready exitfit
  have keep (q : Wire) (hq : q∈F.one::F.frozen::F.work0::F.work1::F.offset) := by
    obtain ⟨ho,hr,hz,ha,hb,hq'⟩ := checks.persistent q hq
    exact body.2.2.2.2.2.2.2.2 q ho hr hz ha hb hq'
  have phase := b.resize_phase P.addBank addWidth A P.addArena P.padding layouts.1 s m
  dsimp only
  rw [SlotFront.program,run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,body.2.2.1,?_⟩
  constructor
  · exact (keep F.one (by simp)).trans vvalues.one
  · exact (keep F.frozen (by simp)).trans vvalues.frozen
  · rw [←beq]; exact body.2.2.2.2.2.2.2.1
  · rw [←aeq]; exact body.2.2.2.2.2.1
  · rw [←qeq]; exact body.2.2.2.2.2.2.1
  · exact (keep F.work0 (by simp)).trans vvalues.work0
  · exact (keep F.work1 (by simp)).trans vvalues.work1
  · change signedDecode F.counter.length (regValue F.counter _)=_
    rw [body.2.2.2.2.1]
    exact pinnedCounter_value old.rows old.frozen F.counter.length (regValue F.counter v.basis)
      checks.counterWidth (regValue_lt _ _) vvalues.counter frozenZero zfit
  · rw [regValue_congr F.offset _ v.basis (fun q hq => keep q (by simp [hq]))]
    exact vvalues.offset

end ECDSAAdd.Arithmetic.Paper935
