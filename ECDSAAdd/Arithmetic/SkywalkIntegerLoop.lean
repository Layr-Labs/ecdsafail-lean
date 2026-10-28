import ECDSAAdd.Arithmetic.SkywalkIntegerLoopCore

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] skywalkIntegerTick skywalkIntegerUntick
attribute [local irreducible] skywalkIntegerLoop skywalkIntegerUnloop
attribute [local irreducible] SkywalkTrace.next Nat.iterate run SkywalkIntegerStage

/-- Reverse may be called after an external Y update. The complete pool-stage
assertion is sufficient; no equality of the caller's outside registers is required. -/
private theorem skywalkIntegerUnloop_restore_pool_n (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p n : Nat) (hp0 : 0<p) (hpo : p%2=1)
    (hsteps : n≤512)
    (initial s : State) (m : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 0 initial.basis)
    (hfinal : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) n s.basis) :
    (run (skywalkIntegerUnloop w 0 n) m s).phase=s.phase ∧
    ∀ q∈skywalkPoolWires w,
      (run (skywalkIntegerUnloop w 0 n) m s).basis q=initial.basis q := by
  let start : State := ⟨s.phase,initial.basis⟩
  obtain ⟨f,hfwd⟩ : ∃ f : State, run (skywalkIntegerLoop w 0 n) [] start=f := ⟨_,rfl⟩
  have hf := skywalkIntegerLoop_spec w hn x p 0 n hp0 hpo (by omega) start [] hinit
  rw [hfwd] at hf
  have hfn : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) n f.basis := by
    simpa only [Nat.zero_add] using hf.2
  have hrestore := skywalkIntegerLoop_roundtrip w hn x p 0 n hp0 hpo
    (by omega) start [] m hinit
  rw [hfwd] at hrestore
  have hsupport := (skywalkIntegerLoop_support w 0 n hn (by omega)).2
  have hbits : ∀ q∈(skywalkPoolWires w).toFinset,s.basis q=f.basis q := by
    intro q hq
    exact skywalkIntegerStage_agrees w _ n (by omega) s.basis f.basis hfinal hfn
      q (List.mem_toFinset.mp hq)
  have hr := pool_run_agrees (skywalkIntegerUnloop w 0 n) (skywalkPoolWires w).toFinset
    hsupport m s f hf.1.symm hbits
  have hphase : (run (skywalkIntegerUnloop w 0 n) m f).phase=start.phase :=
    congrArg State.phase hrestore
  refine ⟨hr.1.trans hphase,?_⟩
  intro q hq
  have hh := hr.2 q (List.mem_toFinset.mpr hq)
  rw [hrestore] at hh
  exact hh

/-- Full512 reverse restores the entire integer pool after external updates,
with an independent measurement record and the caller's current phase. -/
theorem skywalkIntegerUnloop_restore_pool (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p : Nat) (hp0 : 0<p) (hpo : p%2=1)
    (initial s : State) (m : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 0 initial.basis)
    (hfinal : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 512 s.basis) :
    (run (skywalkIntegerUnloop w 0 512) m s).phase=s.phase ∧
    ∀ q∈skywalkPoolWires w,
      (run (skywalkIntegerUnloop w 0 512) m s).basis q=initial.basis q := by
  exact skywalkIntegerUnloop_restore_pool_n w hn x p 512 hp0 hpo (by omega)
    initial s m hinit hfinal

theorem skywalkInteger512_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0<p) (hpo : p%2=1) :
    let r := SkywalkRails.encode false false (x : Int) (p : Int)
    Triple (SkywalkIntegerStage w r 0) (skywalkIntegerLoop w 0 512)
      (SkywalkIntegerStage w r 512) :=
  skywalkIntegerLoop_spec w hn x p 0 512 hp0 hpo (by omega)

/-- All512 stored controls are the actual signed transcript, including ties
and the possible final(1,0) orientation. -/
theorem skywalkInteger512_tape (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0<p) (hpo : p%2=1) (s : State) (m : List Bool)
    (hs : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 0 s.basis) :
    ∀ j,j<512 →
      (run (skywalkIntegerLoop w 0 512) m s).basis (w j)=
        (SkywalkTrace.code (SkywalkTrace.next^[j] (SkywalkRails.encode false false (x : Int) (p : Int)))).1 ∧
      (run (skywalkIntegerLoop w 0 512) m s).basis (w (1028+j))=
        (SkywalkTrace.code (SkywalkTrace.next^[j] (SkywalkRails.encode false false (x : Int) (p : Int)))).2 := by
  have h := skywalkInteger512_spec w hn x p hp0 hpo s m hs
  have hstage := h.2
  unfold SkywalkIntegerStage at hstage
  exact hstage.2.2.2.1

theorem skywalkInteger512_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (skywalkIntegerLoop w 0 512)=263168 ∧
    measurementCount (skywalkIntegerLoop w 0 512)=131584 ∧
    toffoliCount (skywalkIntegerUnloop w 0 512)=263168 ∧
    measurementCount (skywalkIntegerUnloop w 0 512)=131584 := by
  simpa using skywalkIntegerLoop_counts w 0 512 hn (by omega)

end ECDSAAdd.Arithmetic
