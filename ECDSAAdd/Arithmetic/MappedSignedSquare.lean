import ECDSAAdd.Arithmetic.MappedDiagonal
import ECDSAAdd.Arithmetic.SignedSquareLeafSpec
import ECDSAAdd.Arithmetic.SignedTriangularSquareResources

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- The signed rows are unchanged; the diagonal reads the source directly
and therefore needs no additional mask register while the source mask is live. -/
def mappedSignedSquare (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  signedSquareRows xs dst pad carry++signedSquareTop xs dst++mappedDiagSub xs dst carry cin

def mappedSignedSquareClear (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  mappedDiagAdd xs dst carry cin++signedSquareTop xs dst++signedSquareRowsClear xs dst pad carry

theorem mappedSignedSquare_counts (xs dst pad carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length) :
    (toffoliCount (mappedSignedSquare xs dst pad carry cin)=
        signedSquareRowsCount xs.length+dst.length-1 ∧
      measurementCount (mappedSignedSquare xs dst pad carry cin)=
        signedSquareRowsCount xs.length+dst.length-1) ∧
    (toffoliCount (mappedSignedSquareClear xs dst pad carry cin)=
        signedSquareRowsCount xs.length+dst.length-1 ∧
      measurementCount (mappedSignedSquareClear xs dst pad carry cin)=
        signedSquareRowsCount xs.length+dst.length-1) := by
  have rows := signedSquareRows_counts xs dst pad carry hd (Or.inr hp) (by omega)
  have diag := mappedDiag_counts xs dst carry cin (by omega) hd hc
  simp only [mappedSignedSquare,mappedSignedSquareClear,toffoliCount_append,measurementCount_append,
    signedSquareTop_toffoliCount,signedSquareTop_measurementCount,rows.1.1,rows.1.2,
    rows.2.1,rows.2.2,diag.1.1,diag.1.2,diag.2.1,diag.2.2]
  constructor <;> constructor <;> omega

theorem mappedSignedSquare_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (mappedSignedSquare xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (mappedSignedSquare xs dst pad carry cin) records s).basis=(regValue xs s.basis)^2 ∧
    ∀q,q∉dst → (run (mappedSignedSquare xs dst pad carry cin) records s).basis q=s.basis q := by
  let rows := signedSquareRows xs dst pad carry
  let top := signedSquareTop xs dst
  let diag := mappedDiagSub xs dst carry cin
  let rest := records.drop (measurementCount rows)
  let u := run rows (records.take (measurementCount rows)) s
  let v := run top (rest.take (measurementCount top)) u
  let out := run diag (rest.drop (measurementCount top)) v
  have ndRows : (xs++dst++pad++carry).Nodup := (List.nodup_cons.mp hn).2
  have ndTop : (xs++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ndDiag : (cin::xs++dst++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have away (q : Wire) (hq : q∈cin::xs++pad++carry) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h a
    omega
  have high0 : regValue (dst.drop xs.length) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp h0 q (List.mem_of_mem_drop hq))
  have work0 : regValue (pad++carry) s.basis=0 := by simp [regValue_append,hp0,hc0]
  have rc := signedSquareRows_correct xs dst pad carry ndRows hd (Or.inr hp)
    (by omega) s (records.take (measurementCount rows)) 0 h0 high0 work0
  have tc := signedSquareTop_correct xs dst ndTop hd u (rest.take (measurementCount top)) rc.2.2.2.2
  have keepRows (q : Wire) (hq : q∉dst) : u.basis q=s.basis q := rc.2.2.1 q hq
  have keepTop (q : Wire) (hq : q∉dst) : v.basis q=u.basis q := tc.2.2.1 q hq
  have source : regValue xs v.basis=regValue xs s.basis :=
    regValue_congr _ _ _ (fun q hq => (keepTop q (away q (by simp [hq]))).trans
      (keepRows q (away q (by simp [hq]))))
  have carryV : regValue carry v.basis=0 := by
    rw [←hc0]
    apply regValue_congr
    intro q hq
    exact (keepTop q (away q (by simp [hq]))).trans (keepRows q (away q (by simp [hq])))
  have cin0 : v.basis cin=false :=
    ((keepTop cin (away cin (by simp))).trans (keepRows cin (away cin (by simp)))).trans hi0
  have topSame : signedTopTerm xs u.basis=signedTopTerm xs s.basis := by
    apply signedTopTerm_congr
    intro q hq
    exact keepRows q (away q (by simp [hq]))
  have raw : regValue dst v.basis=signedRawValue xs s.basis := by
    rw [tc.2.1,rc.2.1,topSame]
    simp only [Nat.zero_add]
    exact (signedRawValue_rows_top xs s.basis).symm
  have dc := mappedDiagSub_correct cin xs dst carry ndDiag (by omega) hd hc v
    (rest.drop (measurementCount top)) carryV cin0
  have final : out.phase=s.phase ∧ regValue dst out.basis=(regValue xs s.basis)^2 ∧
      ∀q,q∉dst → out.basis q=s.basis q := by
    refine ⟨dc.1.trans (tc.1.trans rc.1),?_,?_⟩
    · rw [dc.2.1,raw,source]
      have rawEq := signedRawValue_correct xs s.basis (List.ne_nil_of_length_pos (by omega))
      have bound := square_bound (regValue xs s.basis) xs.length (regValue_lt xs s.basis)
      rw [rawEq,hd]
      have eq : (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length+
          2^(2*xs.length)-signedDiagValue (regValue xs s.basis) xs.length=
          (regValue xs s.basis)^2+2^(2*xs.length) := by omega
      rw [eq,Nat.add_mod_right,Nat.mod_eq_of_lt bound]
    · intro q hq
      exact (dc.2.2 q hq).trans ((keepTop q hq).trans (keepRows q hq))
  simpa [mappedSignedSquare,rows,top,diag,rest,u,v,out,run_append] using final

theorem mappedSignedSquare_counts_128 (xs dst pad carry : List Wire) (cin : Wire)
    (hx : xs.length=128) (hd : dst.length=256) (hp : 1≤pad.length) (hc : 255≤carry.length) :
    (toffoliCount (mappedSignedSquare xs dst pad carry cin)=8383 ∧
      measurementCount (mappedSignedSquare xs dst pad carry cin)=8383) ∧
    (toffoliCount (mappedSignedSquareClear xs dst pad carry cin)=8383 ∧
      measurementCount (mappedSignedSquareClear xs dst pad carry cin)=8383) := by
  have h := mappedSignedSquare_counts xs dst pad carry cin (by omega) (by omega) hp (by omega)
  rw [hx,hd] at h
  norm_num [signedSquareRowsCount] at h
  exact h

theorem mappedSignedSquare_counts_129 (xs dst pad carry : List Wire) (cin : Wire)
    (hx : xs.length=129) (hd : dst.length=258) (hp : 1≤pad.length) (hc : 257≤carry.length) :
    (toffoliCount (mappedSignedSquare xs dst pad carry cin)=8513 ∧
      measurementCount (mappedSignedSquare xs dst pad carry cin)=8513) ∧
    (toffoliCount (mappedSignedSquareClear xs dst pad carry cin)=8513 ∧
      measurementCount (mappedSignedSquareClear xs dst pad carry cin)=8513) := by
  have h := mappedSignedSquare_counts xs dst pad carry cin (by omega) (by omega) hp (by omega)
  rw [hx,hd] at h
  norm_num [signedSquareRowsCount] at h
  exact h

private def mappedNormalizedRecords : Program → List Bool → List Bool
  | [], _ => []
  | .measureX _ _ _ :: p, [] => false::mappedNormalizedRecords p []
  | .measureX _ _ _ :: p, b::bs => b::mappedNormalizedRecords p bs
  | _::p, m => mappedNormalizedRecords p m

private theorem mapped_run_append_normalized (p q : Program) (m₁ m₂ : List Bool) (s : State) :
    run (p++q) (mappedNormalizedRecords p m₁++m₂) s=run q m₂ (run p m₁ s) := by
  induction p generalizing m₁ s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [mappedNormalizedRecords,List.cons_append,run]
    all_goals try exact ih m₁ _
    cases m₁ <;> simp [mappedNormalizedRecords,ih]

private theorem mapped_rows_roundtrip_separate (xs dst pad carry : List Wire)
    (hnd : (xs++dst++pad++carry).Nodup) (hd : dst.length=2*xs.length)
    (hp : xs.length≤1 ∨ 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m₁ m₂ : List Bool) (A : Nat) (hv : regValue dst s.basis=A)
    (hhi : regValue (dst.drop xs.length) s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) :
    run (signedSquareRowsClear xs dst pad carry) m₂
      (run (signedSquareRows xs dst pad carry) m₁ s)=s := by
  let rows := signedSquareRows xs dst pad carry
  let clear := signedSquareRowsClear xs dst pad carry
  have hr := signedSquareRows_roundtrip xs dst pad carry hnd hd hp hc s
    (mappedNormalizedRecords rows m₁++m₂) A hv hhi hw
  have he := mapped_run_append_normalized rows clear m₁ m₂ s
  rw [show signedSquareRows xs dst pad carry++signedSquareRowsClear xs dst pad carry=
    rows++clear by rfl,he] at hr
  let out := run clear m₂ (run rows m₁ s)
  have hp' : out.phase=s.phase := hr.1
  have hb' : out.basis=s.basis := hr.2
  calc
    run clear m₂ (run rows m₁ s) = ⟨out.phase,out.basis⟩ := rfl
    _ = ⟨s.phase,s.basis⟩ := by rw [hp',hb']
    _ = s := rfl

private theorem mapped_top_roundtrip_separate (xs dst : List Wire)
    (hnd : (xs++dst).Nodup) (s : State) (m₁ m₂ : List Bool) :
    run (signedSquareTop xs dst) m₂ (run (signedSquareTop xs dst) m₁ s)=s := by
  let top := signedSquareTop xs dst
  have hr := signedSquareTop_roundtrip xs dst hnd s (mappedNormalizedRecords top m₁++m₂)
  have he := mapped_run_append_normalized top top m₁ m₂ s
  simpa [top,he] using hr


theorem mappedSignedSquare_roundtrip (cin : Wire)
    (xs dst pad carry : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length)
    (s : State) (forwardRecords clearRecords : List Bool)
    (hd0 : regValue dst s.basis=0) (hp0 : regValue pad s.basis=0)
    (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    run (mappedSignedSquareClear xs dst pad carry cin) clearRecords
      (run (mappedSignedSquare xs dst pad carry cin) forwardRecords s)=s := by
  let rows := signedSquareRows xs dst pad carry
  let top := signedSquareTop xs dst
  let sub := mappedDiagSub xs dst carry cin
  let add := mappedDiagAdd xs dst carry cin
  let clearRows := signedSquareRowsClear xs dst pad carry
  let forwardRest := forwardRecords.drop (measurementCount rows)
  let clearRest := clearRecords.drop (measurementCount add)
  let u := run rows (forwardRecords.take (measurementCount rows)) s
  let v := run top (forwardRest.take (measurementCount top)) u
  let w := run sub (forwardRest.drop (measurementCount top)) v
  let a := run add (clearRecords.take (measurementCount add)) w
  let b := run top (clearRest.take (measurementCount top)) a
  let out := run clearRows (clearRest.drop (measurementCount top)) b
  have ndRows : (xs++dst++pad++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ndTop : (xs++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ndDiag : (cin::xs++dst++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have high0 : regValue (dst.drop xs.length) s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    exact (regValue_zero _ _).mp hd0 q (List.mem_of_mem_drop hq)
  have work0 : regValue (pad++carry) s.basis=0 := by
    simp [regValue_append,hp0,hc0]
  have rc := signedSquareRows_correct xs dst pad carry ndRows hd (Or.inr hp)
    (by omega) s (forwardRecords.take (measurementCount rows)) 0 hd0 high0 work0
  have tc := signedSquareTop_correct xs dst ndTop hd u
    (forwardRest.take (measurementCount top)) rc.2.2.2.2
  have keepR (q : Wire) (hq : q∉dst) : u.basis q=s.basis q := rc.2.2.1 q hq
  have keepT (q : Wire) (hq : q∉dst) : v.basis q=u.basis q := tc.2.2.1 q hq
  have away (q : Wire) (hq : q∈cin::xs++pad++carry) : q∉dst := by
    intro hdq
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hdq
    simp only [List.count_cons,List.count_append] at hn h1
    omega
  have carryV : regValue carry v.basis=0 := by
    rw [←hc0]
    apply regValue_congr; intro q hq
    exact (keepT q (away q (by simp [hq]))).trans (keepR q (away q (by simp [hq])))
  have cinV : v.basis cin=false :=
    ((keepT cin (away cin (by simp))).trans (keepR cin (away cin (by simp)))).trans hi0
  have diagRestore : a=v := mappedDiag_roundtrip cin xs dst carry ndDiag
    (by omega) hd hc v
    (forwardRest.drop (measurementCount top))
    (clearRecords.take (measurementCount add)) carryV cinV
  have topRestore : run top (clearRest.take (measurementCount top)) v=u := by
    exact mapped_top_roundtrip_separate xs dst ndTop u
      (forwardRest.take (measurementCount top)) (clearRest.take (measurementCount top))
  have rowsRestore : run clearRows (clearRest.drop (measurementCount top)) u=s := by
    exact mapped_rows_roundtrip_separate xs dst pad carry ndRows hd (Or.inr hp)
      (by omega) s (forwardRecords.take (measurementCount rows))
      (clearRest.drop (measurementCount top)) 0 hd0 high0 work0
  have staged : out=s := by
    change run clearRows (clearRest.drop (measurementCount top))
      (run top (clearRest.take (measurementCount top)) a)=s
    rw [diagRestore,topRestore,rowsRestore]
  simpa [mappedSignedSquare,mappedSignedSquareClear,rows,top,sub,add,
    clearRows,forwardRest,clearRest,u,v,w,a,b,out,run_append] using staged

/-- Cleanup applies to any matching square output, including after a fold
that changes unrelated coordinates. It uses fresh measurement outcomes. -/
theorem mappedSignedSquareClear_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (mappedSignedSquareClear xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (mappedSignedSquareClear xs dst pad carry cin) records s).basis=0 ∧
    ∀q,q∉dst → (run (mappedSignedSquareClear xs dst pad carry cin) records s).basis q=s.basis q := by
  let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
  have away (q : Wire) (hq : q∈cin::xs++pad++carry) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h a
    omega
  have regBase (r : List Wire) (hr : r=xs ∨ r=pad ∨ r=carry) :
      regValue r base.basis=regValue r s.basis := by
    apply regValue_congr
    intro q hq
    have ne : q∉dst := away q (by rcases hr with rfl|rfl|rfl <;> simp [hq])
    simp [base,ne]
  have d0 : regValue dst base.basis=0 := (regValue_zero _ _).mpr (fun q hq => by simp [base,hq])
  have p0 : regValue pad base.basis=0 := (regBase pad (Or.inr (Or.inl rfl))).trans hp0
  have c0 : regValue carry base.basis=0 := (regBase carry (Or.inr (Or.inr rfl))).trans hc0
  have i0 : base.basis cin=false := by simp [base,away cin (by simp),hi0]
  let u := run (mappedSignedSquare xs dst pad carry cin) [] base
  have forward := mappedSignedSquare_correct cin xs dst pad carry hn hx hd hp hc base [] d0 p0 c0 i0
  have same : u=s := by
    have phase : u.phase=s.phase := forward.1
    have value : regValue dst u.basis=regValue dst s.basis := by
      rw [forward.2.1,regBase xs (Or.inl rfl),hval]
    have basis : u.basis=s.basis := by
      funext q
      by_cases inDst : q∈dst
      · exact (regValue_eq_iff dst u.basis s.basis).mp value q inDst
      · exact (forward.2.2 q inDst).trans (by simp [base,inDst])
    calc
      u=⟨u.phase,u.basis⟩ := rfl
      _=⟨s.phase,s.basis⟩ := by rw [phase,basis]
      _=s := rfl
  have restore := mappedSignedSquare_roundtrip cin xs dst pad carry hn hx hd hp hc base [] records d0 p0 c0 i0
  change run (mappedSignedSquareClear xs dst pad carry cin) records u=base at restore
  rw [same] at restore
  rw [restore]
  refine ⟨rfl,d0,?_⟩
  intro q hq
  simp [base,hq]

end ECDSAAdd.Arithmetic
