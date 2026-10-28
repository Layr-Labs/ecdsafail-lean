import ECDSAAdd.Arithmetic.Paper935.SlotDecoderResources
import ECDSAAdd.Arithmetic.Paper935.WindowControls

namespace ECDSAAdd.Arithmetic.Paper935

theorem decoder_zeroViews_work (xs ws : List Wire) (b : ZeroBit)
    (h : b∈List.zipWith ZeroBit.mk xs ws) : b.work∈ws := by
  induction xs generalizing ws with
  | nil => simp at h
  | cons x xs ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      simp only [List.zipWith_cons_cons,List.mem_cons] at h
      rcases h with rfl|h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih ws h)

/-- Offset-comparison scratch is restored before the depth lookup starts.
The three surviving control values occupy already-live, explicitly clean
registers, so reconstructing them preserves the arena's free-zero invariant. -/
theorem mintHistoryControls_ready (A : Arena) (frozen fire active second sigma : Wire)
    (rb : List ZeroBit) (k : Nat)
    (hn : [frozen,fire,active,second,sigma].Nodup)
    (hr : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length)
    (s : State) (m : List Bool) (ready : A.Ready s.basis)
    (hc : ∀ b∈rb,s.basis b.work=false)
    (hf : s.basis fire=false) (ha : s.basis active=false) (hs : s.basis sigma=false)
    (owned : ∀ q∈[fire,active,sigma],q∈A.live) :
    A.Ready (run (mintHistoryControls frozen fire active second sigma rb k) m s).basis := by
  intro q hq hfree
  rw [mintHistoryControls_run frozen fire active second sigma rb k hn hr hk s m hc hf ha hs]
  have nf : q≠fire := fun e => hfree (e ▸ owned fire (by simp))
  have na : q≠active := fun e => hfree (e ▸ owned active (by simp))
  have ns : q≠sigma := fun e => hfree (e ▸ owned sigma (by simp))
  simpa only [writeBit,Function.update_of_ne nf,Function.update_of_ne na,Function.update_of_ne ns]
    using ready q hq hfree

/-- All five stages can start directly after comparison using the same pool.
No second comparison pool and no assumption of decoder semantics is needed. -/
theorem compileBorrowedDepths_after_mint (A D : Arena) (one frozen output : Wire)
    (bank : WindowBank) (z work : List Wire) (layouts : List DepthLayout)
    (compiled : compileBorrowedDepths A one frozen output z bank.f.wires bank.fv.wires=some (D,work,layouts))
    (fire active second sigma : Wire) (offset : List Wire) (k : Nat)
    (hn : [frozen,fire,active,second,sigma].Nodup)
    (hr : (frozen::fire::(List.zipWith ZeroBit.mk offset work).flatMap ZeroBit.wires).Nodup)
    (hk : k<2^(List.zipWith ZeroBit.mk offset work).length)
    (owned : ∀ q∈[fire,active,sigma],q∈A.live)
    (away : ∀ q∈one::frozen::(z++bank.rows.flatMap WindowRow.wires),q≠fire ∧ q≠active ∧ q≠sigma)
    (st : ECDSAAdd.Divsteps.ZState) (s : State) (m : List Bool) (ready : A.Ready s.basis)
    (hone : s.basis one=true) (hf : s.basis fire=false) (ha : s.basis active=false) (hs : s.basis sigma=false)
    (rows : s.basis frozen=false → bank.Encodes s.basis (ECDSAAdd.Divsteps.zStep st))
    (counter : s.basis frozen=false → signedRegValue z s.basis=(ECDSAAdd.Divsteps.zStep st).z) :
    let t := run (mintHistoryControls frozen fire active second sigma
      (List.zipWith ZeroBit.mk offset work) k) m s
    A.Ready t.basis ∧ (∀ q∈work,t.basis q=false) ∧ ∀ L∈layouts,L.Available st t := by
  let rb := List.zipWith ZeroBit.mk offset work
  let t := run (mintHistoryControls frozen fire active second sigma rb k) m s
  have borrow := (compileBorrowedDepths_contract _ _ _ _ _ _ _ _ _ _ compiled).1
  have bc := A.borrowMany_contract D 11 work borrow
  have reserve := (A.reserve_success work.toFinset).mp ⟨D,bc.2.2⟩
  have poolFree (q : Wire) (hq : q∈work) : q∈arenaWires ∧ q∉A.live :=
    ⟨reserve.1 (List.mem_toFinset.mpr hq),fun hl => Finset.disjoint_left.mp reserve.2 hl (List.mem_toFinset.mpr hq)⟩
  have rbClean : ∀ b∈rb,s.basis b.work=false := by
    intro b hb
    have hw := decoder_zeroViews_work offset work b hb
    exact ready b.work (poolFree b.work hw).1 (poolFree b.work hw).2
  have ready' := mintHistoryControls_ready A frozen fire active second sigma rb k hn hr hk s m ready rbClean hf ha hs owned
  have keep (q : Wire) (hq : q∈one::frozen::(z++bank.rows.flatMap WindowRow.wires)) : t.basis q=s.basis q := by
    have sep := away q hq
    dsimp only [t]
    rw [mintHistoryControls_run frozen fire active second sigma rb k hn hr hk s m rbClean hf ha hs]
    simp only [writeBit,Function.update_of_ne sep.1,Function.update_of_ne sep.2.1,Function.update_of_ne sep.2.2]
  refine ⟨ready',fun q hq => ready' q (poolFree q hq).1 (poolFree q hq).2,?_⟩
  intro L hL
  obtain ⟨d,_,hd⟩ := compileBorrowedDepths_member _ _ _ _ _ _ _ _ _ _ compiled L hL
  apply compileBorrowedDepth_available A D one frozen output bank z work d L hd st t ready'
    ((keep one (by simp)).trans hone)
  · intro hfr
    apply bank.encodes_congr s.basis t.basis _ (rows ((keep frozen (by simp)).symm.trans hfr))
    intro q hq
    exact keep q (by simp only [List.mem_cons,List.mem_append]; tauto)
  · intro hfr
    unfold signedRegValue
    rw [regValue_congr z t.basis s.basis (fun q hq => keep q (by simp only [List.mem_cons,List.mem_append]; tauto))]
    exact counter ((keep frozen (by simp)).symm.trans hfr)

end ECDSAAdd.Arithmetic.Paper935
