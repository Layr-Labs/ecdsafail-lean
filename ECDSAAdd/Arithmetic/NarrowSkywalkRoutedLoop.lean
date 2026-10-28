import ECDSAAdd.Arithmetic.NarrowSkywalkRoutedLoopCore

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] narrowSkywalkScheduledTick narrowSkywalkScheduledUntick
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop
attribute [local irreducible] SkywalkTrace.next Nat.iterate run SkywalkIntegerStage

/-- Reverse may be called after an external Y update. The complete pool-stage
assertion is sufficient; no equality of the caller's outside registers is required. -/
private theorem narrowSkywalkRoutedUnloop_restore_pool_n (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p n : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hx : x<p) (hc : x.Coprime p)
    (hsteps : n≤512)
    (initial s : State) (m : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 0 initial.basis)
    (hfinal : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) n s.basis) :
    (run (narrowSkywalkRoutedUnloop w 0 n) m s).phase=s.phase ∧
    ∀ q∈skywalkPoolWires w,
      (run (narrowSkywalkRoutedUnloop w 0 n) m s).basis q=initial.basis q := by
  let start : State := ⟨s.phase,initial.basis⟩
  obtain ⟨f,hfwd⟩ : ∃ f : State, run (narrowSkywalkRoutedLoop w 0 n) [] start=f := ⟨_,rfl⟩
  have hf := narrowSkywalkRoutedLoop_spec w hn x p 0 n hp0 hx0 hpo hp hx hc (by omega) start [] hinit
  rw [hfwd] at hf
  have hfn : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) n f.basis := by
    simpa only [Nat.zero_add] using hf.2
  have hrestore := narrowSkywalkRoutedLoop_roundtrip w hn x p 0 n hp0 hx0 hpo hp hx hc
    (by omega) start [] m hinit
  rw [hfwd] at hrestore
  have hsupport := (narrowSkywalkRoutedLoop_support w 0 n hn (by omega)).2
  have hbits : ∀ q∈(skywalkPoolWires w).toFinset,s.basis q=f.basis q := by
    intro q hq
    exact skywalkIntegerStage_agrees w _ n (by omega) s.basis f.basis hfinal hfn
      q (List.mem_toFinset.mp hq)
  have hr := pool_run_agrees (narrowSkywalkRoutedUnloop w 0 n) (skywalkPoolWires w).toFinset
    hsupport m s f hf.1.symm hbits
  have hphase : (run (narrowSkywalkRoutedUnloop w 0 n) m f).phase=start.phase :=
    congrArg State.phase hrestore
  refine ⟨hr.1.trans hphase,?_⟩
  intro q hq
  have hh := hr.2 q (List.mem_toFinset.mpr hq)
  rw [hrestore] at hh
  exact hh

/-- Full512 reverse restores the entire integer pool after external updates,
with an independent measurement record and the caller's current phase. -/
theorem narrowSkywalkRoutedUnloop_restore_pool (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hx : x<p) (hc : x.Coprime p)
    (initial s : State) (m : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 0 initial.basis)
    (hfinal : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 512 s.basis) :
    (run (narrowSkywalkRoutedUnloop w 0 512) m s).phase=s.phase ∧
    ∀ q∈skywalkPoolWires w,
      (run (narrowSkywalkRoutedUnloop w 0 512) m s).basis q=initial.basis q := by
  exact narrowSkywalkRoutedUnloop_restore_pool_n w hn x p 512 hp0 hx0 hpo hp hx hc (by omega)
    initial s m hinit hfinal

theorem narrowSkywalkRouted512_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hx : x<p) (hc : x.Coprime p) :
    let r := SkywalkRails.encode false false (x : Int) (p : Int)
    Triple (SkywalkIntegerStage w r 0) (narrowSkywalkRoutedLoop w 0 512)
      (SkywalkIntegerStage w r 512) :=
  narrowSkywalkRoutedLoop_spec w hn x p 0 512 hp0 hx0 hpo hp hx hc (by omega)

/-- All512 stored controls are the actual signed transcript, including ties
and the possible final(1,0) orientation. -/
theorem narrowSkywalkRouted512_tape (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hx : x<p) (hc : x.Coprime p) (s : State) (m : List Bool)
    (hs : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 0 s.basis) :
    ∀ j,j<512 →
      (run (narrowSkywalkRoutedLoop w 0 512) m s).basis (w j)=
        (SkywalkTrace.code (SkywalkTrace.next^[j] (SkywalkRails.encode false false (x : Int) (p : Int)))).1 ∧
      (run (narrowSkywalkRoutedLoop w 0 512) m s).basis (w (1028+j))=
        (SkywalkTrace.code (SkywalkTrace.next^[j] (SkywalkRails.encode false false (x : Int) (p : Int)))).2 := by
  have h := narrowSkywalkRouted512_spec w hn x p hp0 hx0 hpo hp hx hc s m hs
  have hstage := h.2
  unfold SkywalkIntegerStage at hstage
  exact hstage.2.2.2.1

theorem narrowSkywalkRouted512_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (narrowSkywalkRoutedLoop w 0 512)=197632 ∧
    measurementCount (narrowSkywalkRoutedLoop w 0 512)=98943 ∧
    toffoliCount (narrowSkywalkRoutedUnloop w 0 512)=197632 ∧
    measurementCount (narrowSkywalkRoutedUnloop w 0 512)=98943 := by
  have hadd : narrowSkywalkAdderCount 0 512=98688 := by rfl
  have hroute : narrowSkywalkRouteCount 0 512=98944 := by rfl
  have hcleanup : narrowSkywalkCleanupCount 0 512=255 := by rfl
  have h := narrowSkywalkRoutedLoop_counts w 0 512 hn (by omega)
  simpa only [hadd,hroute,hcleanup] using h

end ECDSAAdd.Arithmetic
