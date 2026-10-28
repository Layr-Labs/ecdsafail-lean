import ECDSAAdd.Arithmetic.Paper935.HistoryCompilerReady
import ECDSAAdd.Arithmetic.Paper935.TrajectoryFailures

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

def HistoryLayout.selected (H : HistoryLayout) (s : BasisState) : Bool :=
  !s H.frozen.input && !(!s H.sign && !decide (regValue (H.zb.map ZeroBit.input) s=0)) &&
    decide (regValue (H.low.map ZeroBit.input) s=0)

theorem compileGrowingHistory_run (A B D : Arena) (record work : List Wire) (capacity : Nat)
    (one zz pos sign output port frozen : Wire) (counter coeffBits : List Wire) (H : HistoryLayout)
    (h : compileGrowingHistory A record capacity one zz pos sign output port frozen counter coeffBits=
      some (B,D,work,H))
    (hn : record.Nodup) (ho : record.toFinset⊆A.live) (s : State) (ready : A.Ready s.basis)
    (hone : s.basis one=true) (hzz : s.basis zz=false) (hpos : s.basis pos=false) (hout : s.basis output=false)
    (fit : H.selected s.basis=true →
      2*regValue H.record s.basis+(s.basis H.port).toNat<2^H.record.length)
    (m : List Bool) (ordinal : Nat) :
    let segment := storePush H.one H.zz H.pos H.sign H.output H.port H.zb H.frozen H.positive H.low H.record
    let t := run segment (m.drop ordinal) s
    runWithTape H.program m ordinal s=
      ⟨s.phase ^^ (m.getD (ordinal+measurementCount segment) false && (!H.selected s.basis && s.basis H.port)),
        writeBit t.basis H.port false⟩ := by
  have hc := compileGrowingHistory_contract A B D record work capacity one zz pos sign output port frozen counter coeffBits H h
  have v := (compileHistory_contract one zz pos sign output port frozen counter coeffBits H.record work H hc.2.2).1
  obtain ⟨hz,hf,hsg,hp,hfr,hl,hw,hpush,houtaway,hstable⟩ := v
  have r := compileGrowingHistory_ready A B D record work capacity one zz pos sign output port frozen counter coeffBits H h hn ho s.basis ready hone hzz hpos hout
  exact storePushForget_run H.one H.zz H.pos H.sign H.output H.port H.zb H.frozen H.positive H.low H.record
    hz hf hsg hp hfr hl hw s m r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2
    hpush r.2.2.2.2.1 houtaway hstable fit ordinal

/-- The mathematical selector uses the actual compiled coefficient-prefix
length. In the frozen case no parity assumption is needed. -/
theorem compileHistory_selector (one zz pos sign output port frozen : Wire)
    (counter coeffBits record work : List Wire) (H : HistoryLayout)
    (h : compileHistory one zz pos sign output port frozen counter coeffBits record work=some H)
    (s : BasisState) (u : PinState) (vlow : Wire) (zlo tail : List Wire)
    (zview : counter=zlo++[sign]) (tailne : tail≠[])
    (zvalue : signedRegValue counter s=u.rows.z)
    (vvalue : signedRegValue (vlow::(coeffBits++tail)) s=u.rows.fv)
    (flag : s frozen=u.frozen) (even : u.frozen=false → u.rows.fv%2=0) :
    H.selected s=(!u.frozen && decide (u.rows.z≤0) && decide ((2:Int)^(coeffBits.length+1)∣u.rows.fv)) := by
  have hc := compileHistory_contract one zz pos sign output port frozen counter coeffBits record work H h
  have ids := compileHistory_identity one zz pos sign output port frozen counter coeffBits record work H h
  have len : H.low.length=coeffBits.length := by
    have he := congrArg List.length hc.2.2.1
    simpa only [List.length_map] using he
  by_cases frozenTrue : u.frozen=true
  · simp [HistoryLayout.selected,hc.2.2.2.2.2,flag,frozenTrue]
  · have hf : u.frozen=false := Bool.eq_false_iff.mpr frozenTrue
    have pred := historyPredicate_value H.sign H.frozen.input vlow H.zb H.low zlo tail s u.rows
      (by rw [hc.2.1,zview,ids.2.2.2.1]) tailne
      (by rw [ids.2.2.2.1,←zview]; exact zvalue)
      (by rw [hc.2.2.1]; exact vvalue) (even hf)
    simpa only [HistoryLayout.selected,hc.2.2.2.2.2,flag,len] using pred

/-- Numerical safety is transported through actual history allocation; the
capacity in the event must equal the grown register length. -/
theorem compileGrowingHistory_fit (A B D : Arena) (record work : List Wire) (request : Nat)
    (one zz pos sign output port frozen : Wire) (counter coeffBits : List Wire) (H : HistoryLayout)
    (h : compileGrowingHistory A record request one zz pos sign output port frozen counter coeffBits=
      some (B,D,work,H))
    (hn : record.Nodup) (ho : record.toFinset⊆A.live) (s : BasisState) (ready : A.Ready s)
    (tmin steps : Nat) (capacities : Nat → Nat) (p x : Int) (t : Nat) (ht : t<steps)
    (good : ¬HistoryFailure tmin (coeffBits.length+1) steps capacities p x)
    (capacity : capacities t=max request record.length)
    (selector : H.selected s=trajectoryStore tmin (coeffBits.length+1) p x t)
    (branch : s H.port=parityControl (pinWalk tmin p x t).rows)
    (history : regValue record s=trajectoryHistory tmin (coeffBits.length+1) p x t) :
    H.selected s=true → 2*regValue H.record s+(s H.port).toNat<2^H.record.length := by
  have grow := compileGrowingHistory_capacity A B D record work request one zz pos sign output port frozen counter coeffBits H h hn ho s ready
  rw [selector,grow.2.2.2,history,branch,grow.1,←capacity]
  exact (no_history_failure_iff tmin (coeffBits.length+1) steps capacities p x).mp good t ht

end ECDSAAdd.Arithmetic.Paper935
