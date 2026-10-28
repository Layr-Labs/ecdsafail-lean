import ECDSAAdd.Arithmetic.Paper935.PublicSlotPostMath

namespace ECDSAAdd.Arithmetic.Paper935

/-- Both selected post streams have a real inverse on independently chosen
measurement tapes; the unarmed inverse reverses only three proper gates. -/
theorem compileCheckedPublicSlot_post_roundtrip (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (probeWidth tmin index : Nat) (P : PublicSlot)
    (h : compileCheckedPublicSlot A b addWidth exitWidth F (decide (tmin≤ index)) probeWidth (index+1-tmin)=some P)
    (old : PinState) (s : State) (m n : List Bool) (ready : P.front.exitArena.Ready s.basis)
    (mid : F.MidValues s.basis old) (oldOffset : tmin≤ index → old.offset< index+1-tmin)
    (activeOffset : old.frozen=false → old.offset=0) :
    run (P.postInverse F) n (run (P.postProgram F) m s)=s := by
  have hc := compileCheckedPublicSlot_contract A b addWidth exitWidth F _ probeWidth (index+1-tmin) P h
  cases ha : decide (tmin≤ index) with
  | false =>
    have compile := hc.1
    rw [ha] at compile
    have post := (compilePublicSlot_unarmed A b addWidth exitWidth F probeWidth (index+1-tmin) P compile).1
    have checks := hc.2.2
    simp only [PublicSlot.PostChecks,post] at checks
    simp only [PublicSlot.postInverse,PublicSlot.postProgram,post]
    exact run_reverse_proper _ (unarmedPost_resources F checks.1 checks.2.1).1 s m n
  | true =>
    have compile := hc.1
    rw [ha] at compile
    obtain ⟨post,hpost,hcompile⟩ := compilePublicSlot_armed A b addWidth exitWidth F probeWidth (index+1-tmin) P compile
    have limit : true=true → regValue F.offset s.basis< index+1-tmin := by
      intro _
      rw [mid.offset]
      exact oldOffset (of_decide_eq_true ha)
    have zero : s.basis F.frozen=false → regValue F.offset s.basis=0 := by
      rw [mid.frozen,mid.offset]
      exact activeOffset
    have activity : s.basis F.active= !s.basis F.frozen := by rw [mid.active,mid.frozen]
    have postReady := compileBorrowedPost_ready P.front.exitArena P.postArena true F.one F.work0 F.frozen F.work1 F.active
      P.front.exitBank.g.wires F.offset P.postWork probeWidth (index+1-tmin) post hcompile s.basis
      ready mid.one mid.work0 mid.work1 activity limit zero
    have valid := compilePublicSlot_post_valid A b addWidth exitWidth F _ probeWidth (index+1-tmin) P hc.1 post hpost
    simpa only [PublicSlot.postInverse,PublicSlot.postProgram,hpost] using post.roundtrip valid s m n postReady

end ECDSAAdd.Arithmetic.Paper935
