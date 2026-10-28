import ECDSAAdd.Arithmetic.SignedWordBits
import ECDSAAdd.Arithmetic.SkywalkSign

namespace ECDSAAdd.Arithmetic

/-- Source, target and sign-history interface. The history flag is the temporary
arithmetic control between seed/finish; all carries are restored. -/
def SignedRecordValues (q : Wire) (x y carry : List Wire) (A B : Int) (T : Bool)
    (s : BasisState) : Prop :=
  s q=T ∧ signedRegValue x s=A ∧ signedRegValue y s=B ∧ regValue carry s=0

def signedRecordControl (A B : Int) : Bool := !(SkywalkRails.neg A ^^ SkywalkRails.neg B)
def signedRecordValue (A B : Int) : Int := signedIntegerValue (signedRecordControl A B) A B

/-- Executable record: seed same-sign control, update the target, then retain
only its actual old/new sign flip. No orientation bit is used or modified. -/
def signedRecord (sx sy q : Wire) (x y carry : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedAdd q x y carry ++ skywalkSignToggle sx sy q

/-- Executable forward cleanup: recover the old arithmetic control from history,
undo the signed target update, and clear the history flag. -/
def signedUnrecord (sx sy q : Wire) (x y carry : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedSub q x y carry ++ skywalkSignToggle sx sy q

private theorem signToggle_record_spec (xlo ylo : List Wire) (sx sy q : Wire)
    (carry : List Wire) (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (A B : Int) (T : Bool) :
    Triple (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A B T)
      (skywalkSignToggle sx sy q)
      (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A B
        ((!T) ^^ SkywalkRails.neg A ^^ SkywalkRails.neg B)) := by
  intro s m hin
  have hq := (List.nodup_cons.mp hn).1
  have hqx : q∉xlo++[sx] := fun hm => hq
    (List.mem_append_left carry (List.mem_append_left (ylo++[sy]) hm))
  have hqy : q∉ylo++[sy] := fun hm => hq
    (List.mem_append_left carry (List.mem_append_right (xlo++[sx]) hm))
  have hqc : q∉carry := fun hm => hq
    (List.mem_append_right ((xlo++[sx])++(ylo++[sy])) hm)
  have hsx : sx≠q := by
    intro h
    exact hqx (by simp [← h])
  have hsy : sy≠q := by
    intro h
    exact hqy (by simp [← h])
  have hA : s.basis sx=SkywalkRails.neg A := by
    have hh := signedRegValue_sign xlo sx s.basis
    rw [hin.2.1] at hh
    exact hh
  have hB : s.basis sy=SkywalkRails.neg B := by
    have hh := signedRegValue_sign ylo sy s.basis
    rw [hin.2.2.1] at hh
    exact hh
  rw [skywalkSignToggle_correct sx sy q hsx hsy s m]
  have keep (r : List Wire) (hr : q∉r) :
      regValue r (writeBit s.basis q ((!s.basis q) ^^ s.basis sx ^^ s.basis sy))=
        regValue r s.basis := by
    apply regValue_congr
    intro a ha
    have he : a≠q := fun h => hr (h ▸ ha)
    simp [writeBit,he]
  have keepSigned (r : List Wire) (hr : q∉r) :
      signedRegValue r (writeBit s.basis q ((!s.basis q) ^^ s.basis sx ^^ s.basis sy))=
        signedRegValue r s.basis := by
    unfold signedRegValue
    rw [keep r hr]
  refine ⟨rfl,?_,(keepSigned _ hqx).trans hin.2.1,
    (keepSigned _ hqy).trans hin.2.2.1,(keep _ hqc).trans hin.2.2.2⟩
  simp [writeBit,hin.1,hA,hB]

/-- Same-sign subtraction and opposite-sign addition cancel magnitudes and
cannot overflow when both input signed representatives fit the word. -/
private theorem signedRecord_range (H : Int) (A B : Int)
    (ha0 : -H≤A) (ha1 : A<H) (hb0 : -H≤B) (hb1 : B<H) :
    -H≤signedRecordValue A B ∧ signedRecordValue A B<H := by
  by_cases ha : A<0
  · by_cases hb : B<0
    · simp [signedRecordValue,signedRecordControl,SkywalkRails.neg,
        signedIntegerValue,ha,hb]
      omega
    · simp [signedRecordValue,signedRecordControl,SkywalkRails.neg,
        signedIntegerValue,ha,hb]
      omega
  · by_cases hb : B<0
    · simp [signedRecordValue,signedRecordControl,SkywalkRails.neg,
        signedIntegerValue,ha,hb]
      omega
    · simp [signedRecordValue,signedRecordControl,SkywalkRails.neg,
        signedIntegerValue,ha,hb]
      omega

private theorem signedIntegerValue_undo (Q : Bool) (A B : Int) :
    signedIntegerValue (!Q) A (signedIntegerValue Q A B)=B := by
  cases Q <;> simp [signedIntegerValue]

/-- Native forward record works for every physically representable input pair.
No additional range assumption or sampled history support is required. -/
theorem signedRecord_spec (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (A B : Int) :
    Triple (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A B false)
      (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry)
      (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A (signedRecordValue A B)
        (SkywalkRails.neg B ^^ SkywalkRails.neg (signedRecordValue A B))) := by
  intro s m hin
  let x := xlo++[sx]
  let y := ylo++[sy]
  let Q := signedRecordControl A B
  let R := signedRecordValue A B
  have hw : 0<y.length := by simp [y]
  have hA := signedDecode_range x.length (regValue x s.basis)
    (by simp [x]) (regValue_lt x s.basis)
  change -((2^(x.length-1):Nat):Int)≤signedRegValue x s.basis ∧
    signedRegValue x s.basis<((2^(x.length-1):Nat):Int) at hA
  rw [hin.2.1,hx] at hA
  have hB := signedDecode_range y.length (regValue y s.basis) hw (regValue_lt y s.basis)
  change -((2^(y.length-1):Nat):Int)≤signedRegValue y s.basis ∧
    signedRegValue y s.basis<((2^(y.length-1):Nat):Int) at hB
  rw [hin.2.2.1] at hB
  have hR := signedRecord_range ((2^(y.length-1):Nat):Int) A B
    hA.1 hA.2 hB.1 hB.2
  have h1 := signToggle_record_spec xlo ylo sx sy q carry hn A B false
  rw [skywalkSignToggle_seed] at h1
  have h2 := signedAdd_int_spec q x y carry hn hx hc Q A B hR.1 hR.2
  have h3 := signToggle_record_spec xlo ylo sx sy q carry hn A R Q
  dsimp only [Q,signedRecordControl] at h3
  rw [skywalkSignToggle_finish] at h3
  have hall := (h1.seq h2).seq h3
  simpa only [signedRecord,List.append_assoc] using hall s m hin

/-- Inverse expects a valid recorded image and the original target's signed
range. The latter is automatic for every forward physical input word. -/
theorem signedUnrecord_spec (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (A B : Int)
    (hb0 : -((2^((ylo++[sy]).length-1):Nat):Int)≤B)
    (hb1 : B<((2^((ylo++[sy]).length-1):Nat):Int)) :
    Triple (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A (signedRecordValue A B)
        (SkywalkRails.neg B ^^ SkywalkRails.neg (signedRecordValue A B)))
      (signedUnrecord sx sy q (xlo++[sx]) (ylo++[sy]) carry)
      (SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A B false) := by
  let x := xlo++[sx]
  let y := ylo++[sy]
  let Q := signedRecordControl A B
  let R := signedRecordValue A B
  have h1 := signToggle_record_spec xlo ylo sx sy q carry hn A R
    (SkywalkRails.neg B ^^ SkywalkRails.neg R)
  rw [skywalkSignToggle_recover] at h1
  have hundo : signedIntegerValue (!Q) A R=B := signedIntegerValue_undo Q A B
  have h2 := signedSub_int_spec q x y carry hn hx hc Q A R
    (by rw [hundo]; exact hb0) (by rw [hundo]; exact hb1)
  rw [hundo] at h2
  have h3 := signToggle_record_spec xlo ylo sx sy q carry hn A B Q
  dsimp only [Q,signedRecordControl] at h3
  rw [skywalkSignToggle_clear] at h3
  simpa only [signedUnrecord,List.append_assoc] using (h1.seq h2).seq h3

/-- The retained history is literally the XOR of old and new physical target MSBs. -/
theorem signedRecord_history (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (s : State) (m : List Bool)
    (hq : s.basis q=false) (hcarry : regValue carry s.basis=0) :
    (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis q=
      (s.basis sy ^^ (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis sy) := by
  let A := signedRegValue (xlo++[sx]) s.basis
  let B := signedRegValue (ylo++[sy]) s.basis
  obtain ⟨_,ho⟩ := signedRecord_spec xlo ylo sx sy q carry hn hx hc A B s m
    ⟨hq,rfl,rfl,hcarry⟩
  have hi := signedRegValue_sign ylo sy s.basis
  have hout := signedRegValue_sign ylo sy
    (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis
  rw [ho.2.2.1] at hout
  rw [ho.1,hi,hout]

/-- Signed representatives are injective on the physical word encodings.
Thus preserving a signed source value preserves every source bit. -/
theorem signedRegValue_eq_iff (r : List Wire) (s t : BasisState) :
    signedRegValue r s=signedRegValue r t ↔ ∀ a∈r,s a=t a := by
  constructor
  · intro h
    let w := r.length
    let X := regValue r s
    let Y := regValue r t
    let M : Int := (2^w:Nat)
    change signedDecode w X=signedDecode w Y at h
    have hm : (X:Int)%M=(Y:Int)%M := by
      calc
        (X:Int)%M = signedDecode w X%M := (signedDecode_emod w X).symm
        _ = signedDecode w Y%M := congrArg (fun a : Int => a%M) h
        _ = (Y:Int)%M := signedDecode_emod w Y
    have hx : (X:Int)<M := Int.ofNat_lt.mpr (regValue_lt r s)
    have hy : (Y:Int)<M := Int.ofNat_lt.mpr (regValue_lt r t)
    rw [Int.emod_eq_of_lt (by omega) hx,Int.emod_eq_of_lt (by omega) hy] at hm
    have he : X=Y := by omega
    exact (regValue_eq_iff r s t).mp he
  · intro h
    unfold signedRegValue
    rw [(regValue_eq_iff r s t).mpr h]

theorem signedRecord_source_restored (xlo ylo : List Wire) (sx sy q : Wire)
    (carry : List Wire) (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (s : State) (m : List Bool)
    (hq : s.basis q=false) (hcarry : regValue carry s.basis=0) :
    ∀ a∈xlo++[sx],
      (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis a=s.basis a := by
  obtain ⟨_,ho⟩ := signedRecord_spec xlo ylo sx sy q carry hn hx hc
    (signedRegValue (xlo++[sx]) s.basis) (signedRegValue (ylo++[sy]) s.basis)
    s m ⟨hq,rfl,rfl,hcarry⟩
  exact (signedRegValue_eq_iff _ _ _).mp ho.2.1

/-- Inverse source restoration also holds at the physical bit level. -/
theorem signedUnrecord_source_restored (xlo ylo : List Wire) (sx sy q : Wire)
    (carry : List Wire) (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (A B : Int)
    (hb0 : -((2^((ylo++[sy]).length-1):Nat):Int)≤B)
    (hb1 : B<((2^((ylo++[sy]).length-1):Nat):Int)) (s : State) (m : List Bool)
    (hin : SignedRecordValues q (xlo++[sx]) (ylo++[sy]) carry A (signedRecordValue A B)
      (SkywalkRails.neg B ^^ SkywalkRails.neg (signedRecordValue A B)) s.basis) :
    ∀ a∈xlo++[sx],
      (run (signedUnrecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis a=s.basis a := by
  obtain ⟨_,ho⟩ := signedUnrecord_spec xlo ylo sx sy q carry hn hx hc A B hb0 hb1 s m hin
  exact (signedRegValue_eq_iff _ _ _).mp (ho.2.1.trans hin.2.1.symm)

private theorem signedDecode_bit (n V : Nat) (b : Bool) (hn : 0<n) :
    signedDecode (n+1) (b.toNat+2*V)=2*signedDecode n V+(b.toNat:Nat) := by
  have hp : 2^n=2*2^(n-1) := by
    calc
      2^n = 2^((n-1)+1) := by congr 1; omega
      _ = 2^(n-1)*2 := pow_succ _ _
      _ = 2*2^(n-1) := Nat.mul_comm _ _
  have hb : b.toNat≤1 := by cases b <;> decide
  have hm : ((2^(n+1):Nat):Int)=2*((2^n:Nat):Int) := by
    have hh := congrArg (fun k : Nat => (k:Int)) (pow_succ (2:Nat) n)
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hh
    omega
  by_cases hv : V<2^(n-1)
  · have hf : b.toNat+2*V<2^n := by omega
    unfold signedDecode
    simp only [Nat.add_sub_cancel,if_pos hf,if_pos hv,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat]
    ring
  · have hf : ¬b.toNat+2*V<2^n := by omega
    unfold signedDecode
    simp only [Nat.add_sub_cancel,if_neg hf,if_neg hv,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat]
    omega

/-- Exact low-bit/high-word signed decomposition used by high-only Skywalk routing. -/
theorem signedRegValue_cons (low : Wire) (tail : List Wire) (s : BasisState)
    (ht : tail≠[]) :
    signedRegValue (low::tail) s=2*signedRegValue tail s+((s low).toNat:Nat) := by
  have hn : 0<tail.length := by cases tail <;> simp_all
  have hr : regValue (low::tail) s=(s low).toNat+2*regValue tail s := by
    cases hs : s low <;> simp [regValue,Bool.toNat,hs]
  unfold signedRegValue
  rw [List.length_cons,hr]
  exact signedDecode_bit tail.length (regValue tail s) (s low) hn

/-- The integer operation is exactly the post-half signed Skywalk rail update. -/
theorem signedRecordValue_rails (A B : Int) :
    signedRecordValue A B=(if SkywalkRails.sameSign A B then B-A else B+A) := by
  have he : signedRecordControl A B=SkywalkRails.sameSign A B := by
    unfold signedRecordControl SkywalkRails.sameSign
    cases SkywalkRails.neg A <;> cases SkywalkRails.neg B <;> rfl
  rw [signedRecordValue,he]
  rfl

theorem signedRecord_counts (sx sy q : Wire) (x y carry : List Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    toffoliCount (signedRecord sx sy q x y carry)=y.length-1 ∧
      measurementCount (signedRecord sx sy q x y carry)=y.length-1 ∧
      toffoliCount (signedUnrecord sx sy q x y carry)=y.length-1 ∧
      measurementCount (signedUnrecord sx sy q x y carry)=y.length-1 := by
  have ht := skywalkSignToggle_counts sx sy q
  have hw := signedWord_counts q x y carry hx hc
  simp [signedRecord,signedUnrecord,toffoliCount_append,measurementCount_append,
    ht.1,ht.2,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2]

/-- Sign rails are part of their words; the wrapper introduces no new support
beyond the record flag, source, target and carry workspace. -/
theorem signedRecord_wires (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) :
    wires (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry)=
      (q::((xlo++[sx])++(ylo++[sy])++carry)).toFinset ∧
    wires (signedUnrecord sx sy q (xlo++[sx]) (ylo++[sy]) carry)=
      (q::((xlo++[sx])++(ylo++[sy])++carry)).toFinset := by
  have ht := skywalkSignToggle_wires sx sy q
  have hw := signedWord_wires q (xlo++[sx]) (ylo++[sy]) carry hx hc
  constructor
  · simp only [signedRecord,wires_append,ht,hw.1]
    ext a
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false]
    tauto
  · simp only [signedUnrecord,wires_append,ht,hw.2]
    ext a
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false]
    tauto

/-- Previous orientation and any other caller wire outside the actual support
remain unchanged in both directions, for every record. -/
theorem signedRecord_frame (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (s : State) (m : List Bool)
    (a : Wire) (ha : a∉q::((xlo++[sx])++(ylo++[sy])++carry)) :
    (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis a=s.basis a ∧
      (run (signedUnrecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m s).basis a=s.basis a := by
  have hw := signedRecord_wires xlo ylo sx sy q carry hx hc
  constructor
  · apply run_preserves_outside
    rw [hw.1]
    simpa only [List.mem_toFinset] using ha
  · apply run_preserves_outside
    rw [hw.2]
    simpa only [List.mem_toFinset] using ha

/-- Strong gate inverse on the valid clean-history image. Measurement records
of the two directions are independent; phase and every physical bit restore. -/
theorem signedRecord_roundtrip (xlo ylo : List Wire) (sx sy q : Wire) (carry : List Wire)
    (hn : (q::((xlo++[sx])++(ylo++[sy])++carry)).Nodup)
    (hx : (xlo++[sx]).length=(ylo++[sy]).length)
    (hc : carry.length+1=(ylo++[sy]).length) (s : State) (m1 m2 : List Bool)
    (hq : s.basis q=false) (hcarry : regValue carry s.basis=0) :
    run (signedUnrecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m2
      (run (signedRecord sx sy q (xlo++[sx]) (ylo++[sy]) carry) m1 s)=s := by
  let x := xlo++[sx]
  let y := ylo++[sy]
  let A := signedRegValue x s.basis
  let B := signedRegValue y s.basis
  let t := run (signedRecord sx sy q x y carry) m1 s
  let u := run (signedUnrecord sx sy q x y carry) m2 t
  obtain ⟨hp,ht⟩ := signedRecord_spec xlo ylo sx sy q carry hn hx hc A B s m1
    ⟨hq,rfl,rfl,hcarry⟩
  have hb := signedDecode_range y.length (regValue y s.basis)
    (by simp [y]) (regValue_lt y s.basis)
  change -((2^(y.length-1):Nat):Int)≤B ∧ B<((2^(y.length-1):Nat):Int) at hb
  obtain ⟨hp',hu⟩ := signedUnrecord_spec xlo ylo sx sy q carry hn hx hc A B
    hb.1 hb.2 t m2 ht
  have hxs : ∀ a∈x,u.basis a=s.basis a := (signedRegValue_eq_iff _ _ _).mp hu.2.1
  have hys : ∀ a∈y,u.basis a=s.basis a := (signedRegValue_eq_iff _ _ _).mp hu.2.2.1
  have hcs : ∀ a∈carry,u.basis a=s.basis a :=
    (regValue_eq_iff _ _ _).mp (hu.2.2.2.trans hcarry.symm)
  change u=s
  apply congrArg₂ State.mk
  · exact hp'.trans hp
  · funext a
    by_cases haq : a=q
    · subst a
      exact hu.1.trans hq.symm
    by_cases hax : a∈x
    · exact hxs a hax
    by_cases hay : a∈y
    · exact hys a hay
    by_cases hac : a∈carry
    · exact hcs a hac
    have hout : a∉q::(x++y++carry) := by
      simp only [List.mem_cons,List.mem_append]
      tauto
    have hbefore := (signedRecord_frame xlo ylo sx sy q carry hx hc s m1 a hout).1
    have hafter := (signedRecord_frame xlo ylo sx sy q carry hx hc t m2 a hout).2
    exact hafter.trans hbefore

end ECDSAAdd.Arithmetic
