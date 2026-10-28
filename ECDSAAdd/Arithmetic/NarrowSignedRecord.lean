import ECDSAAdd.Arithmetic.SignedRecordProgram

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- A full word with an explicit retained MSB and discarded sign-padding tail.
The executable streams below still use take/drop of the full words. -/
structure NarrowSignedRecordLayout where
  xlo : List Wire
  ylo : List Wire
  sx : Wire
  sy : Wire
  q : Wire
  xhigh : List Wire
  yhigh : List Wire
  carryLow : List Wire
  carryHigh : List Wire

namespace NarrowSignedRecordLayout

def xp (L : NarrowSignedRecordLayout) := L.xlo++[L.sx]
def yp (L : NarrowSignedRecordLayout) := L.ylo++[L.sy]
def x (L : NarrowSignedRecordLayout) := L.xp++L.xhigh
def y (L : NarrowSignedRecordLayout) := L.yp++L.yhigh
def carry (L : NarrowSignedRecordLayout) := L.carryLow++L.carryHigh
def wires (L : NarrowSignedRecordLayout) := L.q::(L.x++L.y++L.carry)

structure Widths (L : NarrowSignedRecordLayout) (n : Nat) : Prop where
  x : L.xp.length=n
  y : L.yp.length=n
  carry : L.carryLow.length+1=n

theorem views (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) :
    L.x.take n=L.xp ∧ L.y.take n=L.yp ∧
    L.carry.take (n-1)=L.carryLow ∧ L.y.drop n=L.yhigh := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [←hw.x,x,List.take_left]
  · rw [←hw.y,y,List.take_left]
  · rw [←hw.carry,Nat.add_sub_cancel,carry,List.take_left]
  · rw [←hw.y,y,List.drop_left]

theorem short_nodup (L : NarrowSignedRecordLayout) (hn : L.wires.Nodup) :
    (L.q::(L.xp++L.yp++L.carryLow)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro a
  have h := List.nodup_iff_count.mp hn a
  simp only [wires,x,y,carry,List.count_cons,List.count_append] at h ⊢
  omega

theorem high_nodup (L : NarrowSignedRecordLayout) (hn : L.wires.Nodup) : L.yhigh.Nodup := by
  apply List.nodup_iff_count.mpr
  intro a
  have h := List.nodup_iff_count.mp hn a
  simp only [wires,x,y,carry,List.count_cons,List.count_append] at h
  omega

theorem q_high (L : NarrowSignedRecordLayout) (hn : L.wires.Nodup) : L.q∉L.yhigh := by
  intro hm
  have h := List.nodup_iff_count.mp hn L.q
  have hp := List.count_pos_iff.mpr hm
  simp only [wires,x,y,carry,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
  omega

theorem high_away_short (L : NarrowSignedRecordLayout) (hn : L.wires.Nodup)
    (a : Wire) (ha : a∈L.yhigh) : a∉L.q::(L.xp++L.yp++L.carryLow) := by
  intro hm
  have h := List.nodup_iff_count.mp hn a
  have hp := List.count_pos_iff.mpr ha
  have hs := List.count_pos_iff.mpr hm
  simp only [wires,x,y,carry,List.count_cons,List.count_append] at h hs
  omega

theorem rest_away_short (L : NarrowSignedRecordLayout) (hn : L.wires.Nodup)
    (a : Wire) (ha : a∈L.xhigh++L.yhigh++L.carryHigh) :
    a∉L.q::(L.xp++L.yp++L.carryLow) := by
  intro hm
  have h := List.nodup_iff_count.mp hn a
  have hp := List.count_pos_iff.mpr ha
  have hs := List.count_pos_iff.mpr hm
  simp only [wires,x,y,carry,List.count_cons,List.count_append] at h hs hp
  omega

theorem other_away_high (L : NarrowSignedRecordLayout) (hn : L.wires.Nodup)
    (a : Wire) (ha : a∈L.x++L.yp++L.carry) : a∉L.yhigh := by
  intro hm
  have h := List.nodup_iff_count.mp hn a
  have hp := List.count_pos_iff.mpr ha
  have hs := List.count_pos_iff.mpr hm
  simp only [wires,x,y,carry,List.count_cons,List.count_append] at h hp
  omega

end NarrowSignedRecordLayout

/-- Prefix arithmetic followed by Clifford extension of the retained sign flip. -/
def narrowSignedRecord (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  signedRecord L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1)) ++
    signComplement L.q (L.y.drop n)

/-- A new forward inverse stream, with its own measurement list. -/
def narrowSignedUnrecord (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  signComplement L.q (L.y.drop n) ++
    signedUnrecord L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1))

attribute [local irreducible] signedRecord signedUnrecord run

private theorem narrow_fanout_run (q : Wire) (r : List Wire) (hq : q∉r)
    (s : State) (m : List Bool) :
    run (signComplement q r) m s=if s.basis q then run (notRegister r) m s else s := by
  induction r generalizing s with
  | nil => cases s.basis q <;> simp [signComplement,run,notRegister]
  | cons a r ih =>
    have hqa : q≠a := fun h => hq (by simp [h])
    have hqr : q∉r := fun h => hq (List.mem_cons_of_mem _ h)
    simp only [signComplement,List.map_cons,run]
    change run (signComplement q r) m
      ⟨s.phase,writeBit s.basis a (s.basis a ^^ s.basis q)⟩=_
    rw [ih hqr]
    cases hs : s.basis q <;> simp [hs,writeBit,hqa,notRegister,run]

/-- Literal bit-level fanout, including its live control, outside frame and phase. -/
theorem narrow_fanout_correct (q : Wire) (r : List Wire) (hn : r.Nodup) (hq : q∉r)
    (s : State) (m : List Bool) :
    run (signComplement q r) m s=
      ⟨s.phase,fun a => if a∈r then s.basis a ^^ s.basis q else s.basis a⟩ := by
  rw [narrow_fanout_run q r hq]
  cases hs : s.basis q
  · apply congrArg (State.mk s.phase)
    funext a
    simp
  · rw [notRegister_correct r hn]
    simp

/-- Fanout reversal is Clifford and independent of both record lists. -/
theorem narrow_fanout_twice (q : Wire) (r : List Wire) (hn : r.Nodup) (hq : q∉r)
    (s : State) (m1 m2 : List Bool) :
    run (signComplement q r) m2 (run (signComplement q r) m1 s)=s := by
  rw [narrow_fanout_correct q r hn hq,narrow_fanout_correct q r hn hq]
  apply congrArg (State.mk s.phase)
  funext a
  by_cases ha : a∈r
  · simp only [ha,if_true,hq,if_false]
    cases s.basis a <;> cases s.basis q <;> rfl
  · simp [ha]

/-- Signed value of an appended nonempty high word. -/
theorem narrow_signed_append (lo hi : List Wire) (s : BasisState) (hh : hi≠[]) :
    signedRegValue (lo++hi) s=(regValue lo s:Int)+
      ((2^lo.length:Nat):Int)*signedRegValue hi s := by
  induction lo with
  | nil => simp [regValue]
  | cons a lo ih =>
    have ht : lo++hi≠[] := by simp [hh]
    rw [List.cons_append,signedRegValue_cons a (lo++hi) s ht,ih]
    cases ha : s a <;>
      simp [regValue,ha,List.length_cons,pow_succ,Nat.cast_add,Nat.cast_mul] <;> ring

private theorem narrow_false_value (r : List Wire) : signedRegValue r (fun _ => false)=0 := by
  have hz : regValue r (fun _ => false)=0 := (regValue_zero _ _).mpr (fun _ _ => rfl)
  unfold signedRegValue signedDecode
  rw [hz,if_pos (by positivity)]
  rfl

private theorem narrow_true_value (r : List Wire) (hr : r≠[]) :
    signedRegValue r (fun _ => true)= -1 := by
  induction r with
  | nil => contradiction
  | cons a r ih =>
    cases r with
    | nil => norm_num [signedRegValue,signedDecode,regValue]
    | cons b r =>
      rw [signedRegValue_cons a (b::r) _ (by simp),ih (by simp)]
      norm_num

/-- Exact prefix read and every discarded high bit, for a value that fits the
retained signed interval. The positive endpoint is deliberately strict. -/
theorem narrow_signed_prefix (lo hi : List Wire) (s : BasisState) (A : Int)
    (hn : 0 < lo.length) (hv : signedRegValue (lo++hi) s=A)
    (ha0 : -((2^(lo.length-1):Nat):Int) ≤ A)
    (ha1 : A < ((2^(lo.length-1):Nat):Int)) :
    signedRegValue lo s=A ∧ ∀ a∈hi,s a=SkywalkRails.neg A := by
  by_cases he : hi=[]
  · subst hi
    simp only [List.append_nil] at hv
    exact ⟨hv,by simp⟩
  let R : Int := regValue lo s
  let M : Int := (2^lo.length:Nat)
  let H : Int := (2^(lo.length-1):Nat)
  let T := signedRegValue hi s
  have hm : M=2*H := by
    have hp : 2^lo.length=2^(lo.length-1)*2 := by
      calc
        2^lo.length = 2^((lo.length-1)+1) := by congr 1; omega
        _ = 2^(lo.length-1)*2 := pow_succ _ _
    change ((2^lo.length:Nat):Int)=2*((2^(lo.length-1):Nat):Int)
    rw [hp,Nat.cast_mul]
    ring
  have hH : 0 < H := by dsimp [H]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R < M := Int.ofNat_lt.mpr (regValue_lt lo s)
  have hA0 : -H ≤ A := ha0
  have hA1 : A < H := ha1
  have hs := narrow_signed_append lo hi s he
  rw [hv] at hs
  change A=R+M*T at hs
  have hT0 : T ≤ 0 := by
    by_contra hnot
    have hp : 1 ≤ T := by omega
    nlinarith
  have hT1 : -1 ≤ T := by
    by_contra hnot
    have hp : T ≤ -2 := by omega
    nlinarith
  have hcases : T=0 ∨ T= -1 := by omega
  rcases hcases with ht|ht
  · have hA : A=R := by rw [ht] at hs; omega
    have hraw : regValue lo s < 2^(lo.length-1) := by
      have hh : (regValue lo s:Int) < ((2^(lo.length-1):Nat):Int) := by change R < H; omega
      exact_mod_cast hh
    have hsg : SkywalkRails.neg A=false := by simp [SkywalkRails.neg]; omega
    refine ⟨?_,?_⟩
    · unfold signedRegValue signedDecode
      rw [if_pos hraw]
      exact hA.symm
    · have ht' : signedRegValue hi s=signedRegValue hi (fun _ => false) := by
        rw [narrow_false_value]
        exact ht
      intro a ha
      rw [hsg]
      exact (signedRegValue_eq_iff hi _ _).mp ht' a ha
  · have hA : A=R-M := by rw [ht] at hs; nlinarith
    have hraw : ¬regValue lo s < 2^(lo.length-1) := by
      have hh : ¬(regValue lo s:Int) < ((2^(lo.length-1):Nat):Int) := by change ¬R < H; omega
      exact_mod_cast hh
    have hsg : SkywalkRails.neg A=true := by simp [SkywalkRails.neg]; omega
    refine ⟨?_,?_⟩
    · unfold signedRegValue signedDecode
      rw [if_neg hraw]
      exact hA.symm
    · have ht' : signedRegValue hi s=signedRegValue hi (fun _ => true) := by
        rw [narrow_true_value hi he]
        exact ht
      intro a ha
      rw [hsg]
      exact (signedRegValue_eq_iff hi _ _).mp ht' a ha

/-- Uniform high sign padding preserves the signed value of the prefix. -/
theorem narrow_signed_extend (lo hi : List Wire) (s : BasisState) (A : Int)
    (hn : 0 < lo.length) (hv : signedRegValue lo s=A)
    (hh : ∀ a∈hi,s a=SkywalkRails.neg A) : signedRegValue (lo++hi) s=A := by
  by_cases he : hi=[]
  · subst hi; simpa using hv
  have hp := signedDecode_range lo.length (regValue lo s) hn (regValue_lt lo s)
  change -((2^(lo.length-1):Nat):Int) ≤ signedRegValue lo s ∧
    signedRegValue lo s < ((2^(lo.length-1):Nat):Int) at hp
  have ha := narrow_signed_append lo hi s he
  by_cases hs : A < 0
  · have hb : signedRegValue hi s= -1 := by
      apply Eq.trans ((signedRegValue_eq_iff hi s (fun _ => true)).mpr ?_)
        (narrow_true_value hi he)
      intro a hmem
      rw [hh a hmem]
      simp [SkywalkRails.neg,hs]
    have hsig : ¬regValue lo s < 2^(lo.length-1) := by
      intro ht
      have hv' := hv
      unfold signedRegValue signedDecode at hv'
      rw [if_pos ht] at hv'
      omega
    rw [hb] at ha
    unfold signedRegValue signedDecode at hv
    rw [if_neg hsig] at hv
    nlinarith
  · have hb : signedRegValue hi s=0 := by
      apply Eq.trans ((signedRegValue_eq_iff hi s (fun _ => false)).mpr ?_)
        (narrow_false_value hi)
      intro a hmem
      rw [hh a hmem]
      simp [SkywalkRails.neg,hs]
    have hsig : regValue lo s < 2^(lo.length-1) := by
      by_contra ht
      have hv' := hv
      unfold signedRegValue signedDecode at hv'
      rw [if_neg ht] at hv'
      have hraw := regValue_lt lo s
      omega
    rw [hb] at ha
    unfold signedRegValue signedDecode at hv
    rw [if_pos hsig] at hv
    nlinarith

private theorem narrow_short_full (L : NarrowSignedRecordLayout) (A B : Int) (T : Bool)
    (s : BasisState) (h : SignedRecordValues L.q L.xp L.yp L.carryLow A B T s)
    (hx : ∀ a∈L.xhigh,s a=SkywalkRails.neg A)
    (hy : ∀ a∈L.yhigh,s a=SkywalkRails.neg B) (hc : regValue L.carryHigh s=0) :
    SignedRecordValues L.q L.x L.y L.carry A B T s := by
  refine ⟨h.1,?_,?_,?_⟩
  · exact narrow_signed_extend L.xp L.xhigh s A (by simp [NarrowSignedRecordLayout.xp]) h.2.1 hx
  · exact narrow_signed_extend L.yp L.yhigh s B (by simp [NarrowSignedRecordLayout.yp]) h.2.2.1 hy
  · simp only [NarrowSignedRecordLayout.carry,regValue_append,h.2.2.2,hc,Nat.mul_zero,Nat.add_zero]

private theorem narrow_full_to_short (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n)
    (A B : Int) (T : Bool) (s : BasisState)
    (h : SignedRecordValues L.q L.x L.y L.carry A B T s)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ B) (hb1 : B < ((2^(n-1):Nat):Int)) :
    SignedRecordValues L.q L.xp L.yp L.carryLow A B T s ∧
      (∀ a∈L.xhigh,s a=SkywalkRails.neg A) ∧
      (∀ a∈L.yhigh,s a=SkywalkRails.neg B) ∧ regValue L.carryHigh s=0 := by
  have hx := narrow_signed_prefix L.xp L.xhigh s A (by simp [NarrowSignedRecordLayout.xp])
    h.2.1 (by rw [hw.x]; exact ha0) (by rw [hw.x]; exact ha1)
  have hy := narrow_signed_prefix L.yp L.yhigh s B (by simp [NarrowSignedRecordLayout.yp])
    h.2.2.1 (by rw [hw.y]; exact hb0) (by rw [hw.y]; exact hb1)
  have hcl : regValue L.carryLow s=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    exact (regValue_zero _ _).mp h.2.2.2 a (List.mem_append_left _ ha)
  have hch : regValue L.carryHigh s=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    exact (regValue_zero _ _).mp h.2.2.2 a (List.mem_append_right _ ha)
  exact ⟨⟨h.1,hx.1,hy.1,hcl⟩,hx.2,hy.2,hch⟩

/-- Full-value semantics: both original inputs fit the retained signed interval;
all discarded bits are repaired to the new sign, not assumed zero. -/
theorem narrowSignedRecord_spec (L : NarrowSignedRecordLayout) (n : Nat)
    (hw : L.Widths n) (hn : L.wires.Nodup) (A B : Int)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ B) (hb1 : B < ((2^(n-1):Nat):Int)) :
    Triple (SignedRecordValues L.q L.x L.y L.carry A B false) (narrowSignedRecord L n)
      (SignedRecordValues L.q L.x L.y L.carry A (signedRecordValue A B)
        (SkywalkRails.neg B ^^ SkywalkRails.neg (signedRecordValue A B))) := by
  intro s m hin
  let R := signedRecordValue A B
  let T := SkywalkRails.neg B ^^ SkywalkRails.neg R
  have hv := L.views n hw
  simp only [narrowSignedRecord,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2]
  rw [run_append]
  generalize hr : run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow)
    (m.take (measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow))) s=mid
  generalize hf : run (signComplement L.q L.yhigh)
    (m.drop (measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow))) mid=out
  have hi := narrow_full_to_short L n hw A B false s.basis hin ha0 ha1 hb0 hb1
  have hh := signedRecord_spec L.xlo L.ylo L.sx L.sy L.q L.carryLow (L.short_nodup hn)
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm) A B s
    (m.take (measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow))) hi.1
  change (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) _ s).phase=s.phase ∧
    SignedRecordValues L.q L.xp L.yp L.carryLow A R T
      (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) _ s).basis at hh
  rw [hr] at hh
  have hfan := narrow_fanout_correct L.q L.yhigh (L.high_nodup hn) (L.q_high hn) mid
    (m.drop (measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow)))
  rw [hf] at hfan
  have fanbit (a : Wire) : out.basis a=(if a∈L.yhigh then mid.basis a ^^ mid.basis L.q else mid.basis a) :=
    congrArg (fun t : State => t.basis a) hfan
  have keep (a : Wire) (ha : a∈L.x++L.yp++L.carry) : out.basis a=mid.basis a := by
    rw [fanbit,if_neg (L.other_away_high hn a ha)]
  have keepRead (r : List Wire) (hsub : r⊆L.x++L.yp++L.carry) :
      regValue r out.basis=regValue r mid.basis :=
    regValue_congr _ _ _ (fun a ha => keep a (hsub ha))
  have keepSigned (r : List Wire) (hsub : r⊆L.x++L.yp++L.carry) :
      signedRegValue r out.basis=signedRegValue r mid.basis := by
    unfold signedRegValue
    rw [keepRead r hsub]
  have tailOld (a : Wire) (ha : a∈L.xhigh++L.yhigh++L.carryHigh) : mid.basis a=s.basis a := by
    have hb := (signedRecord_frame L.xlo L.ylo L.sx L.sy L.q L.carryLow
      (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm) s
      (m.take (measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow))) a
      (L.rest_away_short hn a ha)).1
    change (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) _ s).basis a=s.basis a at hb
    rw [hr] at hb
    exact hb
  have hqOut : out.basis L.q=T := by
    rw [fanbit,if_neg (L.q_high hn)]
    exact hh.2.1
  have hxOut : signedRegValue L.xp out.basis=A := by
    rw [keepSigned L.xp (by intro a ha; simp [NarrowSignedRecordLayout.x,ha])]
    exact hh.2.2.1
  have hyOut : signedRegValue L.yp out.basis=R := by
    rw [keepSigned L.yp (by intro a ha; simp [ha])]
    exact hh.2.2.2.1
  have hcOut : regValue L.carryLow out.basis=0 := by
    rw [keepRead L.carryLow (by intro a ha; simp [NarrowSignedRecordLayout.carry,ha])]
    exact hh.2.2.2.2
  refine ⟨(congrArg State.phase hfan).trans hh.1,narrow_short_full L A R T out.basis
    ⟨hqOut,hxOut,hyOut,hcOut⟩ ?_ ?_ ?_⟩
  · intro a ha
    rw [keep a (by simp [NarrowSignedRecordLayout.x,ha]),tailOld a (by simp [ha])]
    exact hi.2.1 a ha
  · intro a ha
    rw [fanbit,if_pos ha,hh.2.1,tailOld a (by simp [ha]),hi.2.2.1 a ha]
    dsimp only [T]
    cases SkywalkRails.neg B <;> cases SkywalkRails.neg R <;> rfl
  · apply Eq.trans (keepRead L.carryHigh (by intro a ha; simp [NarrowSignedRecordLayout.carry,ha]))
    apply Eq.trans (regValue_congr _ _ _ (fun a ha => tailOld a (by simp [ha]))) hi.2.2.2

private theorem narrow_result_range (H A B : Int)
    (ha0 : -H ≤ A) (ha1 : A < H) (hb0 : -H ≤ B) (hb1 : B < H) :
    -H ≤ signedRecordValue A B ∧ signedRecordValue A B < H := by
  by_cases ha : A < 0 <;> by_cases hb : B < 0 <;>
    simp [signedRecordValue,signedRecordControl,signedIntegerValue,SkywalkRails.neg,ha,hb] <;> omega

/-- Independently measured full-value inverse. The high sign repair is undone
BEFORE the history is cleared by signedUnrecord. -/
theorem narrowSignedUnrecord_spec (L : NarrowSignedRecordLayout) (n : Nat)
    (hw : L.Widths n) (hn : L.wires.Nodup) (A B : Int)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ B) (hb1 : B < ((2^(n-1):Nat):Int)) :
    Triple (SignedRecordValues L.q L.x L.y L.carry A (signedRecordValue A B)
        (SkywalkRails.neg B ^^ SkywalkRails.neg (signedRecordValue A B)))
      (narrowSignedUnrecord L n) (SignedRecordValues L.q L.x L.y L.carry A B false) := by
  intro s m hin
  let R := signedRecordValue A B
  let T := SkywalkRails.neg B ^^ SkywalkRails.neg R
  have hR := narrow_result_range ((2^(n-1):Nat):Int) A B ha0 ha1 hb0 hb1
  have hi := narrow_full_to_short L n hw A R T s.basis hin ha0 ha1 hR.1 hR.2
  have hv := L.views n hw
  have hm := signComplement_counts L.q L.yhigh
  simp only [narrowSignedUnrecord,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2]
  rw [run_append,hm.2]
  simp only [List.take_zero,List.drop_zero]
  generalize hf : run (signComplement L.q L.yhigh) [] s=mid
  generalize hr : run (signedUnrecord L.sx L.sy L.q L.xp L.yp L.carryLow) m mid=out
  have hfan := narrow_fanout_correct L.q L.yhigh (L.high_nodup hn) (L.q_high hn) s []
  rw [hf] at hfan
  have fanbit (a : Wire) : mid.basis a=(if a∈L.yhigh then s.basis a ^^ s.basis L.q else s.basis a) :=
    congrArg (fun t : State => t.basis a) hfan
  have keep (a : Wire) (ha : a∈L.x++L.yp++L.carry) : mid.basis a=s.basis a := by
    rw [fanbit,if_neg (L.other_away_high hn a ha)]
  have keepRead (r : List Wire) (hsub : r⊆L.x++L.yp++L.carry) :
      regValue r mid.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun a ha => keep a (hsub ha))
  have keepSigned (r : List Wire) (hsub : r⊆L.x++L.yp++L.carry) :
      signedRegValue r mid.basis=signedRegValue r s.basis := by
    unfold signedRegValue
    rw [keepRead r hsub]
  have hq : mid.basis L.q=T := by
    rw [fanbit,if_neg (L.q_high hn)]
    exact hin.1
  have hpre : SignedRecordValues L.q L.xp L.yp L.carryLow A R T mid.basis := by
    refine ⟨hq,?_,?_,?_⟩
    · exact (keepSigned L.xp (by intro a ha; simp [NarrowSignedRecordLayout.x,ha])).trans hi.1.2.1
    · exact (keepSigned L.yp (by intro a ha; simp [ha])).trans hi.1.2.2.1
    · exact (keepRead L.carryLow (by intro a ha; simp [NarrowSignedRecordLayout.carry,ha])).trans hi.1.2.2.2
  have hh := signedUnrecord_spec L.xlo L.ylo L.sx L.sy L.q L.carryLow (L.short_nodup hn)
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm) A B
    (by change -((2^(L.yp.length-1):Nat):Int) ≤ B; rw [hw.y]; exact hb0)
    (by change B < ((2^(L.yp.length-1):Nat):Int); rw [hw.y]; exact hb1) mid m hpre
  change (run (signedUnrecord L.sx L.sy L.q L.xp L.yp L.carryLow) m mid).phase=mid.phase ∧
    SignedRecordValues L.q L.xp L.yp L.carryLow A B false
      (run (signedUnrecord L.sx L.sy L.q L.xp L.yp L.carryLow) m mid).basis at hh
  rw [hr] at hh
  have tailOld (a : Wire) (ha : a∈L.xhigh++L.yhigh++L.carryHigh) : out.basis a=mid.basis a := by
    have hb := (signedRecord_frame L.xlo L.ylo L.sx L.sy L.q L.carryLow
      (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm) mid m a (L.rest_away_short hn a ha)).2
    change (run (signedUnrecord L.sx L.sy L.q L.xp L.yp L.carryLow) m mid).basis a=mid.basis a at hb
    rw [hr] at hb
    exact hb
  have hphaseFan : mid.phase=s.phase := by
    have hh := congrArg (fun st : State => st.phase) hfan
    exact hh
  refine ⟨hh.1.trans hphaseFan,narrow_short_full L A B false out.basis hh.2 ?_ ?_ ?_⟩
  · intro a ha
    rw [tailOld a (by simp [ha]),keep a (by simp [NarrowSignedRecordLayout.x,ha])]
    exact hi.2.1 a ha
  · intro a ha
    rw [tailOld a (by simp [ha]),fanbit,if_pos ha,hin.1,hi.2.2.1 a ha]
    cases SkywalkRails.neg B <;> cases SkywalkRails.neg R <;> rfl
  · apply Eq.trans (regValue_congr _ _ _ (fun a ha => tailOld a (by simp [ha])))
    apply Eq.trans (keepRead L.carryHigh (by intro a ha; simp [NarrowSignedRecordLayout.carry,ha])) hi.2.2.2

/-- Actual gate counts: discarded high-bit repair uses only CX. -/
theorem narrowSignedRecord_counts (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) :
    toffoliCount (narrowSignedRecord L n)=n-1 ∧ measurementCount (narrowSignedRecord L n)=n-1 ∧
    toffoliCount (narrowSignedUnrecord L n)=n-1 ∧ measurementCount (narrowSignedUnrecord L n)=n-1 := by
  have h := L.views n hw
  have hs := signedRecord_counts L.sx L.sy L.q L.xp L.yp L.carryLow
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  have hf := signComplement_counts L.q L.yhigh
  simp only [narrowSignedRecord,narrowSignedUnrecord,h.1,h.2.1,h.2.2.1,h.2.2.2,
    toffoliCount_append,measurementCount_append,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hf.1,hf.2,hw.y,
    Nat.add_zero,Nat.zero_add]
  simp

/-- Complete actual support, including every repaired high target bit. -/
theorem narrowSignedRecord_support (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) :
    wires (narrowSignedRecord L n)⊆L.wires.toFinset ∧
    wires (narrowSignedUnrecord L n)⊆L.wires.toFinset := by
  have hv := L.views n hw
  have hs := signedRecord_wires L.xlo L.ylo L.sx L.sy L.q L.carryLow
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  change wires (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow)=
      (L.q::(L.xp++L.yp++L.carryLow)).toFinset ∧
    wires (signedUnrecord L.sx L.sy L.q L.xp L.yp L.carryLow)=
      (L.q::(L.xp++L.yp++L.carryLow)).toFinset at hs
  have hf := signComplement_wires_subset L.q L.yhigh
  have small : (L.q::(L.xp++L.yp++L.carryLow)).toFinset⊆L.wires.toFinset := by
    intro a ha
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,NarrowSignedRecordLayout.wires,
      NarrowSignedRecordLayout.x,NarrowSignedRecordLayout.y,NarrowSignedRecordLayout.carry] at ha ⊢
    tauto
  have high : (L.q::L.yhigh).toFinset⊆L.wires.toFinset := by
    intro a ha
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,NarrowSignedRecordLayout.wires,
      NarrowSignedRecordLayout.x,NarrowSignedRecordLayout.y,NarrowSignedRecordLayout.carry] at ha ⊢
    tauto
  simp only [narrowSignedRecord,narrowSignedUnrecord,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2,
    wires_append,Finset.union_subset_iff,hs.1,hs.2]
  exact ⟨⟨small,hf.trans high⟩,⟨hf.trans high,small⟩⟩

/-- Previous orientation and every external control/caller site frame in both
forward and independently measured inverse streams. -/
theorem narrowSignedRecord_frame (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n)
    (s : State) (m : List Bool) (a : Wire) (ha : a∉L.wires) :
    (run (narrowSignedRecord L n) m s).basis a=s.basis a ∧
    (run (narrowSignedUnrecord L n) m s).basis a=s.basis a := by
  have hp := narrowSignedRecord_support L n hw
  constructor
  · exact run_preserves_outside _ m s a (fun h => ha (List.mem_toFinset.mp (hp.1 h)))
  · exact run_preserves_outside _ m s a (fun h => ha (List.mem_toFinset.mp (hp.2 h)))

/-- Strong full-State inverse, without reversing any measurement instruction.
The two record lists are independent. The signed fit assumptions needed for
full-value lifting are unnecessary for this stronger bit-level roundtrip. -/
theorem narrowSignedRecord_roundtrip (L : NarrowSignedRecordLayout) (n : Nat)
    (hw : L.Widths n) (hn : L.wires.Nodup) (s : State) (m1 m2 : List Bool)
    (hq : s.basis L.q=false) (hc : regValue L.carry s.basis=0) :
    run (narrowSignedUnrecord L n) m2 (run (narrowSignedRecord L n) m1 s)=s := by
  have hv := L.views n hw
  have hcarry : regValue L.carryLow s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    exact (regValue_zero _ _).mp hc a (List.mem_append_left _ ha)
  have hm := signComplement_counts L.q L.yhigh
  simp only [narrowSignedRecord,narrowSignedUnrecord,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2]
  rw [run_append,run_append,hm.2]
  simp only [List.take_zero,List.drop_zero]
  rw [narrow_fanout_twice L.q L.yhigh (L.high_nodup hn) (L.q_high hn)]
  exact signedRecord_roundtrip L.xlo L.ylo L.sx L.sy L.q L.carryLow
    (L.short_nodup hn) (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm) s _ m2 hq hcarry

private theorem narrow_values_frame (L : NarrowSignedRecordLayout) (s t : BasisState)
    (hx : signedRegValue L.x t=signedRegValue L.x s)
    (hc : regValue L.carry t=regValue L.carry s)
    (ho : ∀ a,a∉L.wires → t a=s a) :
    ∀ a,a≠L.q → a∉L.y → t a=s a := by
  have hxb := (signedRegValue_eq_iff L.x t s).mp hx
  have hcb := (regValue_eq_iff L.carry t s).mp hc
  intro a hq hy
  by_cases hX : a∈L.x
  · exact hxb a hX
  by_cases hC : a∈L.carry
  · exact hcb a hC
  apply ho a
  intro hm
  rcases List.mem_cons.mp hm with hq'|hr
  · exact hq hq'
  · simp only [List.mem_append,or_assoc] at hr
    rcases hr with hx'|hy'|hc'
    · exact hX hx'
    · exact hy hy'
    · exact hC hc'

/-- Strong full-word frame: source bits, every carry/work bit and every caller
control outside the target are restored; only the sign-history q is retained. -/
theorem narrowSignedRecord_full_frame (L : NarrowSignedRecordLayout) (n : Nat)
    (hw : L.Widths n) (hn : L.wires.Nodup) (A B : Int)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ B) (hb1 : B < ((2^(n-1):Nat):Int))
    (s : State) (m : List Bool) (hin : SignedRecordValues L.q L.x L.y L.carry A B false s.basis) :
    ∀ a,a≠L.q → a∉L.y → (run (narrowSignedRecord L n) m s).basis a=s.basis a := by
  generalize hout : run (narrowSignedRecord L n) m s=out
  have hh := narrowSignedRecord_spec L n hw hn A B ha0 ha1 hb0 hb1 s m hin
  rw [hout] at hh
  apply narrow_values_frame L s.basis out.basis
  · exact hh.2.2.1.trans hin.2.1.symm
  · exact hh.2.2.2.2.trans hin.2.2.2.symm
  · intro a ha
    have hx := (narrowSignedRecord_frame L n hw s m a ha).1
    rw [hout] at hx
    exact hx

/-- Full inverse frame, including the discarded source/sign padding and all
original carry sites, for an independently supplied measurement record. -/
theorem narrowSignedUnrecord_full_frame (L : NarrowSignedRecordLayout) (n : Nat)
    (hw : L.Widths n) (hn : L.wires.Nodup) (A B : Int)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ B) (hb1 : B < ((2^(n-1):Nat):Int))
    (s : State) (m : List Bool)
    (hin : SignedRecordValues L.q L.x L.y L.carry A (signedRecordValue A B)
      (SkywalkRails.neg B ^^ SkywalkRails.neg (signedRecordValue A B)) s.basis) :
    ∀ a,a≠L.q → a∉L.y → (run (narrowSignedUnrecord L n) m s).basis a=s.basis a := by
  generalize hout : run (narrowSignedUnrecord L n) m s=out
  have hh := narrowSignedUnrecord_spec L n hw hn A B ha0 ha1 hb0 hb1 s m hin
  rw [hout] at hh
  apply narrow_values_frame L s.basis out.basis
  · exact hh.2.2.1.trans hin.2.1.symm
  · exact hh.2.2.2.2.trans hin.2.2.2.symm
  · intro a ha
    have hx := (narrowSignedRecord_frame L n hw s m a ha).2
    rw [hout] at hx
    exact hx

end ECDSAAdd.Arithmetic
