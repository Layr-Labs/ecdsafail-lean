import ECDSAAdd.Arithmetic.DirectSkywalkArithmetic
import ECDSAAdd.Arithmetic.CompactSkywalkReverseFrame
import ECDSAAdd.Arithmetic.CompactSkywalkStageTerminal

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open DirectSkywalk
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop
attribute [local irreducible] compactSkywalkForward compactSkywalkReverse
attribute [local irreducible] run measurementCount
attribute [local irreducible] SkywalkTrace.next Nat.iterate SkywalkIntegerStage

/-- Both actual forward emitters reach the same complete terminal physical
State. All integer history and every outsider agree, with independent records. -/
theorem compactSkywalkCaller_forward_eq (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (x p : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (s : State) (mNew mOld : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis) :
    run (compactSkywalkForward w 0 512) mNew s = run (narrowSkywalkRoutedLoop w 0 512) mOld s := by
  have pool := skywalkShared_integer_nodup w hn
  have new := compactSkywalkForward_512 w pool x p hp0 hx0 hpo hp hx hc s mNew hin
  have old := narrowSkywalkRouted512_spec w pool x p hp0 hx0 hpo hp hx hc s mOld hin
  generalize eNew : run (compactSkywalkForward w 0 512) mNew s = newState at new ⊢
  generalize eOld : run (narrowSkywalkRoutedLoop w 0 512) mOld s = oldState at old ⊢
  have terminal := (compactSkywalkStage_terminal w pool x p hp0 hx0 hpo hp hx hc
    newState.basis new.2).2
  apply State.extensionality newState oldState
  · exact new.1.trans old.1.symm
  · funext q
    by_cases hq : q ∈ skywalkPoolWires w
    · exact skywalkIntegerStage_agrees w
        (SkywalkRails.encode false false (x : Int) (p : Int)) 512 (by decide)
        newState.basis oldState.basis terminal old.2 q hq
    · have frameNew := compactSkywalkForward_frame w pool 0 512 (by decide) s mNew q hq
      have frameOld := arith_record_outside w hn s mOld q hq
      rw [eNew] at frameNew
      rw [eOld] at frameOld
      exact frameNew.trans frameOld.symm

/-- The actual compact reverse accepts the same terminal pool contract as
the production restoration pass, even after a coexisting field update. -/
theorem compactSkywalkCaller_reverse_restore (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (x p : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (initial s : State) (m : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (hfinal : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 s.basis) :
    (run (compactSkywalkReverse w 0 512) m s).phase = s.phase ∧
    (∀q ∈ skywalkPoolWires w,(run (compactSkywalkReverse w 0 512) m s).basis q = initial.basis q) := by
  let start : State := ⟨s.phase,initial.basis⟩
  obtain ⟨f,hfwd⟩ : ∃ f : State,
      run (compactSkywalkForward w 0 512) [] start = f := ⟨_,rfl⟩
  have pool := skywalkShared_integer_nodup w hn
  have fw := compactSkywalkForward_512 w pool x p hp0 hx0 hpo hp hx hc start [] hinit
  rw [hfwd] at fw
  have physical := (compactSkywalkStage_terminal w pool x p hp0 hx0 hpo hp hx hc f.basis fw.2).2
  have bits : ∀q ∈ skywalkPoolWires w,s.basis q = f.basis q :=
    skywalkIntegerStage_agrees w
      (SkywalkRails.encode false false (x : Int) (p : Int)) 512 (by decide)
      s.basis f.basis hfinal physical
  have hphase : s.phase = (run (compactSkywalkForward w 0 512) [] start).phase := by
    rw [hfwd]
    exact fw.1.symm
  have hpool : ∀q ∈ skywalkPoolWires w,
      s.basis q = (run (compactSkywalkForward w 0 512) [] start).basis q := by
    rw [hfwd]
    exact bits
  have restore := compactSkywalkReverse_restore_after_outside w pool x p 0 512
    hp0 hx0 hpo hp hx hc (by decide) start s [] m
    ((compactSkywalkStage_zero_iff w
      (SkywalkRails.encode false false (x : Int) (p : Int)) start.basis).mpr hinit)
    hphase hpool
  exact ⟨restore.1,restore.2.1⟩

/-- Independent reverse streams have identical full physical outputs under
the existing seed/terminal contracts; field outsiders need not equal the seed. -/
theorem compactSkywalkCaller_reverse_eq (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (x p : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (initial s : State) (mNew mOld : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (hfinal : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 s.basis) :
    run (compactSkywalkReverse w 0 512) mNew s = run (narrowSkywalkRoutedUnloop w 0 512) mOld s := by
  have pool := skywalkShared_integer_nodup w hn
  have new := compactSkywalkCaller_reverse_restore w hn x p hp0 hx0 hpo hp hx hc initial s mNew hinit hfinal
  have old := narrowSkywalkRoutedUnloop_restore_pool w pool x p hp0 hx0 hpo hp hx hc initial s mOld hinit hfinal
  generalize eNew : run (compactSkywalkReverse w 0 512) mNew s = newState at new ⊢
  generalize eOld : run (narrowSkywalkRoutedUnloop w 0 512) mOld s = oldState at old ⊢
  apply State.extensionality newState oldState
  · exact new.1.trans old.1.symm
  · funext q
    by_cases hq : q ∈ skywalkPoolWires w
    · exact (new.2 q hq).trans (old.2 q hq).symm
    · have frameNew := compactSkywalkReverse_frame w pool 0 512 (by decide) s mNew q hq
      have frameOld := arith_unrecord_outside w hn s mOld q hq
      rw [eNew] at frameNew
      rw [eOld] at frameOld
      exact frameNew.trans frameOld.symm

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkCaller_forward_eq
#print axioms ECDSAAdd.Arithmetic.compactSkywalkCaller_reverse_eq
