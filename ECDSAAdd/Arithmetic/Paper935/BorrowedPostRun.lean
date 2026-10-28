import ECDSAAdd.Arithmetic.Paper935.PostCompilerReady

namespace ECDSAAdd.Arithmetic.Paper935

/-- The complete post-stage, including its offset comparison and control
cleanup, returns the shared probe/comparison pool clean. -/
theorem compileBorrowedPost_release (A D : Arena) (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (h : compileBorrowedPost A armed one zf frozen fire active inputs record width offset=some (D,work,P))
    (owned : (active::frozen::record).toFinset⊆A.live)
    (s : State) (m : List Bool) (ready : A.Ready s.basis)
    (hone : s.basis one=true) (hzf : s.basis zf=false) (hfire : s.basis fire=false)
    (activity : s.basis active= !s.basis frozen)
    (oldOffset : armed=true → regValue record s.basis<offset)
    (activeOffset : s.basis frozen=false → regValue record s.basis=0) :
    D.release work.toFinset (run P.program m s).basis=some A ∧ A.Ready (run P.program m s).basis := by
  have pair := compileBorrowedPost_contract A D armed one zf frozen fire active inputs record work width offset P h
  have hc := compilePost_contract armed one zf frozen fire active inputs record work width offset P pair.2
  have ids := compilePost_identity armed one zf frozen fire active inputs record work width offset P pair.2
  have hr := compileBorrowedPost_ready A D armed one zf frozen fire active inputs record work width offset P h
    s.basis ready hone hzf hfire activity oldOffset activeOffset
  have borrow := A.borrowMany_contract D _ work pair.1
  have reserve := (A.reserve_success work.toFinset).mp ⟨D,borrow.2.2⟩
  have clean := (A.reserve_ready D work.toFinset s.basis ready borrow.2.2).2
  have spec := P.run_spec hc.1 s m hr
  have noAlias (q : Wire) (hq : q∈work) : q∉active::frozen::record := by
    intro ho
    exact Finset.disjoint_left.mp reserve.2 (owned (List.mem_toFinset.mpr ho)) (List.mem_toFinset.mpr hq)
  constructor
  · apply historyGrowth_release A D work _ pair.1
    intro q hq
    have sep := noAlias q hq
    have ha : q≠P.active := by rw [ids.2.2.2.2.2.1]; intro he; exact sep (by simp [he])
    have hf : q≠P.frozen := by rw [ids.2.2.2.1]; intro he; exact sep (by simp [he])
    have hrec : q∉P.recordWires := by rw [hc.2.2.1]; intro hm; exact sep (by simp [hm])
    rw [spec.2.2.2.2.2.2 q ha hf hrec]
    exact clean q (List.mem_toFinset.mpr hq)
  · apply P.arena_ready_after hc.1 A s m hr ready
    intro q hq
    rw [ids.2.2.2.1,hc.2.2.1] at hq
    exact owned (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp hq)))

end ECDSAAdd.Arithmetic.Paper935
