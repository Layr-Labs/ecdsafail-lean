import ECDSAAdd.Arithmetic.Paper935.HistoryCompilerRun

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileGrowingHistory_spec (A B D : Arena) (record work : List Wire) (capacity : Nat)
    (one zz pos sign output port frozen : Wire) (counter coeffBits : List Wire) (H : HistoryLayout)
    (h : compileGrowingHistory A record capacity one zz pos sign output port frozen counter coeffBits=
      some (B,D,work,H))
    (hn : record.Nodup) (ho : record.toFinset⊆A.live) (s : State) (ready : A.Ready s.basis)
    (hone : s.basis one=true) (hzz : s.basis zz=false) (hpos : s.basis pos=false) (hout : s.basis output=false)
    (fit : H.selected s.basis=true →
      2*regValue H.record s.basis+(s.basis H.port).toNat<2^H.record.length)
    (m : List Bool) (ordinal : Nat) :
    let t := runWithTape H.program m ordinal s
    t.basis H.port=false ∧
    regValue H.record t.basis=(if H.selected s.basis then
      2*regValue record s.basis+(s.basis H.port).toNat else regValue record s.basis) ∧
    (∀ q,q∉H.port::H.record → t.basis q=s.basis q) := by
  have hc := compileGrowingHistory_contract A B D record work capacity one zz pos sign output port frozen counter coeffBits H h
  have v := (compileHistory_contract one zz pos sign output port frozen counter coeffBits H.record work H hc.2.2).1
  obtain ⟨hz,hf,hsg,hp,hfr,hl,hw,hpush,houtaway,hstable⟩ := v
  have r := compileGrowingHistory_ready A B D record work capacity one zz pos sign output port frozen counter coeffBits H h hn ho s.basis ready hone hzz hpos hout
  have spec := storePush_spec H.one H.zz H.pos H.sign H.output H.port H.zb H.frozen H.positive H.low H.record
    hz hf hsg hp hfr hl hw s (m.drop ordinal) r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2
    hpush r.2.2.2.2.1 houtaway hstable fit
  have run := compileGrowingHistory_run A B D record work capacity one zz pos sign output port frozen counter coeffBits H h hn ho s ready hone hzz hpos hout fit m ordinal
  have grow := compileGrowingHistory_capacity A B D record work capacity one zz pos sign output port frozen counter coeffBits H h hn ho s.basis ready
  have portAway := (List.nodup_cons.mp (List.nodup_cons.mp hpush).2).1
  dsimp only
  rw [run]
  refine ⟨by simp [writeBit],?_,?_⟩
  · have eqreg : ∀ b : BasisState,regValue H.record (writeBit b H.port false)=regValue H.record b := by
      intro b
      apply regValue_congr
      intro q hq
      exact Function.update_of_ne (fun (he : q=H.port) => portAway (he ▸ hq)) _ _
    rw [eqreg,spec.2.2.2.1,grow.2.2.2]
    rfl
  · intro q hq
    exact (Function.update_of_ne (fun he => hq (by simp [he])) _ _).trans (spec.2.2.2.2 q hq)

/-- Scratch is returned to the post-growth arena; the actual history remains
allocated. Its growth can only be undone later, after the matching reverse pop. -/
theorem compileGrowingHistory_release (A B D : Arena) (record work : List Wire) (capacity : Nat)
    (one zz pos sign output port frozen : Wire) (counter coeffBits : List Wire) (H : HistoryLayout)
    (h : compileGrowingHistory A record capacity one zz pos sign output port frozen counter coeffBits=
      some (B,D,work,H))
    (hn : record.Nodup) (ho : record.toFinset⊆A.live) (portOwned : port∈B.live)
    (s : State) (ready : A.Ready s.basis)
    (hone : s.basis one=true) (hzz : s.basis zz=false) (hpos : s.basis pos=false) (hout : s.basis output=false)
    (fit : H.selected s.basis=true →
      2*regValue H.record s.basis+(s.basis H.port).toNat<2^H.record.length)
    (m : List Bool) (ordinal : Nat) :
    D.release work.toFinset (runWithTape H.program m ordinal s).basis=some B ∧
    B.Ready (runWithTape H.program m ordinal s).basis := by
  have hc := compileGrowingHistory_contract A B D record work capacity one zz pos sign output port frozen counter coeffBits H h
  have ids := compileHistory_identity one zz pos sign output port frozen counter coeffBits H.record work H hc.2.2
  have grow := planHistoryGrow_correct A B record H.record capacity hc.1 hn ho s.basis ready
  have borrow := B.borrowMany_contract D _ work hc.2.1
  have reserve := (B.reserve_success work.toFinset).mp ⟨D,borrow.2.2⟩
  have clean := (B.reserve_ready D work.toFinset s.basis grow.2.2.2.1 borrow.2.2).2
  have spec := compileGrowingHistory_spec A B D record work capacity one zz pos sign output port frozen counter coeffBits H h hn ho s ready hone hzz hpos hout fit m ordinal
  have owned : ∀ q∈H.port::H.record,q∈B.live := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hq
    · rw [ids.2.2.2.2.2]; exact portOwned
    · exact grow.2.2.1 (List.mem_toFinset.mpr hq)
  constructor
  · apply historyGrowth_release B D work _ hc.2.1
    intro q hq
    rw [spec.2.2 q (fun hm => Finset.disjoint_left.mp reserve.2 (owned q hm) (List.mem_toFinset.mpr hq))]
    exact clean q (List.mem_toFinset.mpr hq)
  · intro q hqa hq
    rw [spec.2.2 q (fun hm => hq (owned q hm))]
    exact grow.2.2.2.1 q hqa hq

end ECDSAAdd.Arithmetic.Paper935
