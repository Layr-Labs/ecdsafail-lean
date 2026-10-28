import ECDSAAdd.Arithmetic.FusedInverseFlags

namespace ECDSAAdd.Arithmetic

/-- Independently emitted arithmetic undo. The carry measurements belong to
the new forward subtraction stream and receive a fresh arbitrary record. -/
def fusedCorrectionUndo (a j l m : Wire) (C R carry : List Wire) (cin : Wire)
    (P D N : Nat) : Program :=
  fusedCorrectionWordLoad a j l m C P D N ++ subInPlace C R carry cin ++
    fusedCorrectionWordLoad a j l m C P D N

private theorem inverse_sub_frame (x y carry : List Wire) (cin : Wire)
    (hn : (cin::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (s : State) (record : List Bool)
    (hi : s.basis cin=false) (hk : regValue carry s.basis=0)
    (w : Wire) (hw : w∉y) : (run (subInPlace x y carry cin) record s).basis w=s.basis w := by
  have h := (subInPlace_spec x y carry cin hn hx hc
    (regValue x s.basis) (regValue y s.basis) s record ⟨⟨⟨rfl,rfl⟩,hi⟩,hk⟩).2
  by_cases hxw : w∈x
  · exact (regValue_eq_iff x _ _).mp h.1.1.1 w hxw
  by_cases hcw : w∈carry
  · exact (regValue_eq_iff carry _ _).mp (h.2.trans hk.symm) w hcw
  by_cases he : w=cin
  · subst w; exact h.1.2.trans hi.symm
  apply run_preserves_outside
  rw [subInPlace_wires x y carry cin hx hc]
  simpa using (show w∉cin::(x++y++carry) by simp [he,hxw,hw,hcw])

theorem fusedCorrectionUndo_correct (a j l m : Wire) (C R carry : List Wire) (cin : Wire)
    (P D N : Nat) (hn : (cin::([a,j,l,m]++C++R++carry)).Nodup)
    (hCR : C.length=R.length) (hcarry : carry.length+1=R.length)
    (hP : P<2^C.length) (hD : D<2^C.length) (hN : N<2^C.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false) :
    (run (fusedCorrectionUndo a j l m C R carry cin P D N) record s).phase=s.phase ∧
    (∀ w,w∉R → (run (fusedCorrectionUndo a j l m C R carry cin P D N) record s).basis w=s.basis w) ∧
    regValue R (run (fusedCorrectionUndo a j l m C R carry cin P D N) record s).basis=
      (regValue R s.basis+2^R.length-fusedCorrectionWordValue (s.basis a) (s.basis j) (s.basis l) (s.basis m) P D N)%2^R.length := by
  have hload : ([a,j,l,m]++C).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at hh ⊢
    omega
  have hadd : (cin::(C++R++carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at hh ⊢
    omega
  have hpair := List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hadd).2).1
  have hd : C.Disjoint R := hpair.2.2
  have outside (w : Wire) (hw : w∈[a,j,l,m]++carry++[cin]) : w∉C ∧ w∉R := by
    have hh := List.nodup_iff_count.mp hn w
    have ho := List.count_pos_iff.mpr hw
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ho
    constructor <;> intro hm <;> have hh' := List.count_pos_iff.mpr hm <;> omega
  let F := fusedCorrectionWordValue (s.basis a) (s.basis j) (s.basis l) (s.basis m) P D N
  let Q := PairFrame C R s.basis
  have reads (A Z : Nat) (st : BasisState) (h : Q A Z st) :
      regValue carry st=0 ∧ st cin=false ∧
      fusedCorrectionWordValue (st a) (st j) (st l) (st m) P D N=F := by
    have he (w : Wire) (hw : w∈[a,j,l,m]++carry++[cin]) :=
      h.2.2 w (outside w hw).1 (outside w hw).2
    refine ⟨(regValue_congr _ _ _ (fun w hw => he w (by simp [hw]))).trans hk0,
      (he cin (by simp)).trans hi,?_⟩
    rw [he a (by simp),he j (by simp),he l (by simp),he m (by simp)]
  have load (A Z : Nat) : Triple (Q A Z) (fusedCorrectionWordLoad a j l m C P D N) (Q (A^^^F) Z) := by
    intro st ms h
    obtain ⟨hf,he,hv⟩ := fusedCorrectionWordLoad_correct a j l m C P D N hload hP hD hN st ms
    exact ⟨hf,PairFrame.update_temp C R _ _ _ A Z _ hd h he
      (by simpa only [h.1,(reads A Z st.basis h).2.2] using hv)⟩
  have sub (Z : Nat) : Triple (Q F Z) (subInPlace C R carry cin)
      (Q F ((Z+2^R.length-F)%2^R.length)) := by
    intro st ms h
    have hr := reads F Z st.basis h
    obtain ⟨hp,ho⟩ := subInPlace_spec C R carry cin hadd hCR hcarry F Z st ms
      ⟨⟨⟨h.1,h.2.1⟩,hr.2.1⟩,hr.1⟩
    have he := inverse_sub_frame C R carry cin hadd hCR hcarry st ms hr.2.1 hr.1
    exact ⟨hp,PairFrame.update_dst C R _ _ _ F Z _ hd h he ho.1.1.2⟩
  let Z := regValue R s.basis
  have h1 := load 0 Z
  have h2 := sub Z
  have h3 := load F ((Z+2^R.length-F)%2^R.length)
  simp only [Nat.zero_xor] at h1
  simp only [Nat.xor_self] at h3
  have hprog : Triple (Q 0 Z) (fusedCorrectionUndo a j l m C R carry cin P D N)
      (Q 0 ((Z+2^R.length-F)%2^R.length)) := by
    simpa only [fusedCorrectionUndo,List.append_assoc] using (h1.seq h2).seq h3
  obtain ⟨hf,hv⟩ := hprog s record ⟨hC0,rfl,fun _ _ _ => rfl⟩
  refine ⟨hf,?_,hv.2.1⟩
  intro w hw
  by_cases hc : w∈C
  · exact (regValue_eq_iff _ _ _).mp (hv.1.trans hC0.symm) w hc
  · exact hv.2.2 w hc hw


theorem fusedCorrectionUndo_counts (a j l m : Wire) (C R carry : List Wire) (cin : Wire)
    (P D N : Nat) (hCR : C.length=R.length) (hcarry : carry.length+1=R.length) :
    toffoliCount (fusedCorrectionUndo a j l m C R carry cin P D N)=R.length-1 ∧
    measurementCount (fusedCorrectionUndo a j l m C R carry cin P D N)=R.length-1 := by
  have hl := fusedCorrectionWordLoad_counts a j l m C P D N
  have hs := subInPlace_counts C R carry cin hCR hcarry
  simp only [fusedCorrectionUndo,toffoliCount_append,measurementCount_append,
    hl.1,hl.2,hs.1,hs.2,Nat.zero_add,Nat.add_zero]
  trivial

/-- A full-word selected correction is always representable. No carry window
or empirical modulus-tail assumption is used. -/
theorem fusedInverseCorrection_bound (w P : Nat) (hp : 0<P) (hfit : 2*P<2^w)
    (B A H : Bool) :
    fusedCorrectionWordValue A (B&&H) (A&&H) (A&&(B&&H)) P (2*P) (2^w-P)<2^w := by
  cases B <;> cases A <;> cases H <;> simp [fusedCorrectionWordValue_selector] <;> omega

private theorem inverse_add_sub_cancel (N U F : Nat) (hU : U<N) (hF : F<N) :
    ((U+F)%N+N-F)%N=U := by
  by_cases hh : U+F<N
  · rw [Nat.mod_eq_of_lt hh,show U+F+N-F=U+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hU]
  · have hlo : N≤U+F := by omega
    have hlt : U+F-N<N := by omega
    rw [Nat.mod_eq_sub_mod hlo,Nat.mod_eq_of_lt hlt,
      show U+F-N+N-F=U by omega,Nat.mod_eq_of_lt hU]

/-- Subtracting the selected correction from the exact even lift recovers the
full signed raw word, including its negative two's-complement cases. -/
theorem fusedCorrectionUndoMachine (w P X Y : Nat) (b : Bool)
    (hp : P%2=1) (hX : X<P) (hY : Y<P) (hwidth : 2*P<2^w) :
    (2*FusedSignedHalf.result P b X Y+2^w-
      fusedCorrectionWordValue (FusedSignedHalf.parity (FusedSignedHalf.signedSum b X Y))
        (b&&FusedSignedHalf.reduction P (FusedSignedHalf.signedSum b X Y))
        (FusedSignedHalf.parity (FusedSignedHalf.signedSum b X Y)&&
          FusedSignedHalf.reduction P (FusedSignedHalf.signedSum b X Y))
        (FusedSignedHalf.parity (FusedSignedHalf.signedSum b X Y)&&
          (b&&FusedSignedHalf.reduction P (FusedSignedHalf.signedSum b X Y)))
        P (2*P) (2^w-P))%2^w=signedWordValue w b Y X := by
  let F := fusedCorrectionWordValue (FusedSignedHalf.parity (FusedSignedHalf.signedSum b X Y))
    (b&&FusedSignedHalf.reduction P (FusedSignedHalf.signedSum b X Y))
    (FusedSignedHalf.parity (FusedSignedHalf.signedSum b X Y)&&
      FusedSignedHalf.reduction P (FusedSignedHalf.signedSum b X Y))
    (FusedSignedHalf.parity (FusedSignedHalf.signedSum b X Y)&&
      (b&&FusedSignedHalf.reduction P (FusedSignedHalf.signedSum b X Y))) P (2*P) (2^w-P)
  have hf : F<2^w := fusedInverseCorrection_bound w P (by omega) hwidth _ _ _
  have hu : signedWordValue w b Y X<2^w := by
    cases b <;> simp only [signedWordValue,Bool.false_eq_true,if_false,if_true]
    all_goals exact Nat.mod_lt _ (by positivity)
  have lift := fusedCorrectionMachine w P X Y b hp hX hY hwidth
  have hr := (FusedSignedHalf.result_spec P X Y b hp hX hY).2
  have hnat : (FusedSignedHalf.evenLift P b (FusedSignedHalf.signedSum b X Y)).toNat=
      2*FusedSignedHalf.result P b X Y := by
    rw [←hr]
    omega
  rw [hnat] at lift
  change (2*FusedSignedHalf.result P b X Y+2^w-F)%2^w=_
  rw [←lift]
  exact inverse_add_sub_cancel (2^w) _ F hu hf

/-- Fresh signed subtraction cancels the full signed addition word. -/
theorem fusedSignedWordInverse (w X Y : Nat) (b : Bool)
    (hX : X<2^w) (hY : Y<2^w) :
    signedWordValue w (!b) Y (signedWordValue w b Y X)=X := by
  cases b
  · simpa only [signedWordValue,Bool.not_false,Bool.false_eq_true,if_false,if_true]
      using inverse_add_sub_cancel (2^w) X Y hX hY
  · simp only [signedWordValue,Bool.not_true,Bool.false_eq_true,if_false,if_true]
    by_cases hle : Y≤X
    · rw [show X+2^w-Y=X-Y+2^w by omega,Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : X-Y<2^w),show X-Y+Y=X by omega,
        Nat.mod_eq_of_lt hX]
    · have hlt : X+2^w-Y<2^w := by omega
      rw [Nat.mod_eq_of_lt hlt,show X+2^w-Y+Y=X+2^w by omega,
        Nat.add_mod_right,Nat.mod_eq_of_lt hX]

end ECDSAAdd.Arithmetic
