import ECDSAAdd.Arithmetic.BalancedCoreFlagsProof

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField

theorem seed_data_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hc : ∀q∈work L,s.basis q=false) :
    ∀q∈L.r++L.y++L.carry,(run (seedViews L) m s).basis q=s.basis q := by
  have he := seedViews_run L hw hn s m (hc _ (by simp [work]))
    (hc _ (by simp [work])) (hc _ (by simp [work]))
  intro q hq
  have ng : q≠L.sourceGuard := fun e => flagAway L hn _ (by simp) (e ▸ hq)
  have no : q≠L.one := fun e => flagAway L hn _ (by simp) (e ▸ hq)
  have np : q≠L.parity := fun e => flagAway L hn _ (by simp) (e ▸ hq)
  rw [he]
  simp [writeBit,ng,no,np]

theorem seed_signed (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Int) (s : State) (m : List Bool)
    (hr : signedRegValue L.r s.basis=X) (hy : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    signedRegValue (rawTarget L) (run (seedViews L) m s).basis=X ∧
    signedRegValue (rawSource L) (run (seedViews L) m s).basis=Y ∧
    regValue L.carry (run (seedViews L) m s).basis=0 := by
  let t := run (seedViews L) m s
  have frame := seed_data_frame L hw hn s m hc
  have sameR : signedRegValue L.r t.basis=X := by
    unfold signedRegValue
    rw [regValue_congr L.r t.basis s.basis (fun q hq => frame q (by simp [hq]))]
    exact hr
  have sameY : signedRegValue L.y t.basis=Y := by
    unfold signedRegValue
    rw [regValue_congr L.y t.basis s.basis (fun q hq => frame q (by simp [hq]))]
    exact hy
  have eq := seedViews_run L hw hn s m (hc _ (by simp [work]))
    (hc _ (by simp [work])) (hc _ (by simp [work]))
  have flags := seedND L hw hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  rcases flags with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6⟩,⟨h2_3,h2_4,h2_5,h2_6⟩,⟨h3_4,h3_5,h3_6⟩,⟨h4_5,h4_6⟩,h5_6⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h0_5r := Ne.symm h0_5
  have h0_6r := Ne.symm h0_6
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h1_5r := Ne.symm h1_5
  have h1_6r := Ne.symm h1_6
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h2_5r := Ne.symm h2_5
  have h2_6r := Ne.symm h2_6
  have h3_4r := Ne.symm h3_4
  have h3_5r := Ne.symm h3_5
  have h3_6r := Ne.symm h3_6
  have h4_5r := Ne.symm h4_5
  have h4_6r := Ne.symm h4_6
  have h5_6r := Ne.symm h5_6
  have one : t.basis L.one=t.basis L.rmsb := by
    rw [show t=run (seedViews L) m s from rfl,eq]
    simp_all [writeBit,Function.update]
  have guard : t.basis L.sourceGuard=t.basis L.ymsb := by
    rw [show t=run (seedViews L) m s from rfl,eq]
    simp_all [writeBit,Function.update]
  refine ⟨(signed_extension L.low L.rmsb L.one t.basis one).trans sameR,
    (signed_extension L.ylow L.ymsb L.sourceGuard t.basis guard).trans sameY,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  exact (frame q (by simp [hq])).trans (hc q (by simp [work,hq]))

theorem seed_parity (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (s : State) (m : List Bool)
    (hr : signedRegValue L.r s.basis=X) (hy : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    (run (seedViews L) m s).basis L.parity=originalParity (rawSum B X Y) := by
  have rp : s.basis L.r0=originalParity X := word_parity L.r0 (L.rtail++[L.rmsb]) s.basis X hr
  have yp : s.basis (L.ylow.getD 0 0)=originalParity Y := by
    cases hy0 : L.ylow with
    | nil => have hw0 := hw.2.1; simp [hy0] at hw0
    | cons a as =>
      have he : signedRegValue (a::(as++[L.ymsb])) s.basis=Y := by simpa [BalancedCleanup.Layout.y,hy0] using hy
      simpa [hy0] using word_parity a (as++[L.ymsb]) s.basis Y he
  rw [seedViews_run L hw hn s m (hc _ (by simp [work]))
    (hc _ (by simp [work])) (hc _ (by simp [work]))]
  simp only [writeBit,Function.update_self,rp,yp]
  exact (raw_parity B X Y).symm

/-- Actual seed-view and signed-add composition, covering unrestricted
incoming phase and every record. No fold circuit premise is introduced. -/
theorem seed_raw_signed (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y) (s : State) (m : List Bool)
    (hs : s.basis L.sign=B) (hr : signedRegValue L.r s.basis=X)
    (hyr : signedRegValue L.y s.basis=Y) (hc : ∀q∈work L,s.basis q=false) :
    let t := run (seedViews L++rawAdd L) m s
    t.phase=s.phase ∧ signedRegValue (rawTarget L) t.basis=rawSum B X Y ∧
    signedRegValue (rawSource L) t.basis=Y ∧ regValue L.carry t.basis=0 := by
  let u := run (seedViews L) m s
  have seed := seed_signed L hw hn X Y s m hr hyr hc
  have data := seed_data_frame L hw hn s m hc
  have si : u.basis L.sign=B := by
    have eq := seedViews_run L hw hn s m (hc _ (by simp [work]))
      (hc _ (by simp [work])) (hc _ (by simp [work]))
    have flags : [L.sign,L.sourceGuard,L.one,L.parity].Nodup := by
      apply List.nodup_iff_count.mpr
      intro q; have h := List.nodup_iff_count.mp (scalarND L hn) q
      simp only [List.count_cons,List.count_nil] at h ⊢
      omega
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at flags
    rcases flags with ⟨⟨h0_1,h0_2,h0_3⟩,⟨h1_2,h1_3⟩,h2_3⟩
    have h0_1r := Ne.symm h0_1
    have h0_2r := Ne.symm h0_2
    have h0_3r := Ne.symm h0_3
    have h1_2r := Ne.symm h1_2
    have h1_3r := Ne.symm h1_3
    have h2_3r := Ne.symm h2_3
    rw [show u=run (seedViews L) m s from rfl,eq]
    simp_all [writeBit,Function.update]
  have raw := rawAdd_signed L hw hn B X Y hx hy u m ⟨si,seed.2.1,seed.1,seed.2.2⟩
  have phase : u.phase=s.phase := by
    rw [show u=run (seedViews L) m s from rfl,
      seedViews_run L hw hn s m (hc _ (by simp [work]))
        (hc _ (by simp [work])) (hc _ (by simp [work]))]
  simp only [run_append,run_take,show measurementCount (seedViews L)=0 from rfl,List.drop_zero]
  exact ⟨raw.1.trans phase,raw.2.2.2.1,raw.2.2.1,raw.2.2.2.2⟩

end ECDSAAdd.Arithmetic.BalancedCircuit
