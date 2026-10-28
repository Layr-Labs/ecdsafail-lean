import ECDSAAdd.Arithmetic.InPlaceAdder
import Mathlib.Data.Int.DivMod

namespace ECDSAAdd.Arithmetic

/-- Clifford source complement controlled by a live sign/control bit. -/
def signComplement (q : Wire) (x : List Wire) : Program := x.map (Instr.CX q)

private theorem signComplement_run (q : Wire) (x : List Wire) (hq : q∉x)
    (s : State) (m : List Bool) :
    run (signComplement q x) m s = if s.basis q then run (notRegister x) m s else s := by
  induction x generalizing s with
  | nil => cases s.basis q <;> rfl
  | cons a x ih =>
    have hqa : q≠a := fun h => hq (by simp [h])
    have hqt : q∉x := fun h => hq (List.mem_cons_of_mem _ h)
    simp only [signComplement,List.map_cons,run]
    change run (signComplement q x) m
      ⟨s.phase,writeBit s.basis a (s.basis a ^^ s.basis q)⟩ = _
    rw [ih hqt]
    cases hs : s.basis q <;> simp [hs,writeBit,hqa,notRegister,run]

/-- Exact source complement, with every outside bit and sign restored. -/
theorem signComplement_correct (q : Wire) (x : List Wire) (hn : x.Nodup)
    (hq : q∉x) (s : State) (m : List Bool) :
    (run (signComplement q x) m s).phase=s.phase ∧
      (∀ a,a∉x → (run (signComplement q x) m s).basis a=s.basis a) ∧
      regValue x (run (signComplement q x) m s).basis=
        if s.basis q then 2^x.length-1-regValue x s.basis else regValue x s.basis := by
  rw [signComplement_run q x hq]
  cases hs : s.basis q with
  | false => simp
  | true =>
    rw [notRegister_correct x hn]
    refine ⟨rfl,?_,?_⟩
    · intro a ha
      simp [ha]
    · change regValue x (fun a => if a∈x then !s.basis a else s.basis a)=_
      rw [regValue_congr x _ (fun a => !s.basis a) (by intro a ha; simp [ha]),
        regValue_complement]
      simp

theorem signComplement_counts (q : Wire) (x : List Wire) :
    toffoliCount (signComplement q x)=0 ∧ measurementCount (signComplement q x)=0 := by
  induction x with
  | nil => exact ⟨rfl,rfl⟩
  | cons a x ih => simpa [signComplement,toffoliCount,measurementCount] using ih

theorem signComplement_wires_subset (q : Wire) (x : List Wire) :
    wires (signComplement q x)⊆(q::x).toFinset := by
  induction x with
  | nil => simp [signComplement,wires]
  | cons a x ih =>
    intro b hb
    simp only [signComplement,List.map_cons,wires,Instr.wires,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with (rfl|rfl)|hb
    · simp
    · simp
    · have hh := ih hb
      simp only [List.mem_toFinset,List.mem_cons] at hh ⊢
      tauto

def signSourceValue (w : Nat) (Q : Bool) (X : Nat) : Nat :=
  if Q then 2^w-1-X else X

def signedWordValue (w : Nat) (Q : Bool) (X Y : Nat) : Nat :=
  if Q then (Y+2^w-X)%2^w else (Y+X)%2^w

private theorem signSource_twice (w : Nat) (Q : Bool) (X : Nat) (hX : X<2^w) :
    signSourceValue w Q (signSourceValue w Q X)=X := by
  cases Q with
  | false => rfl
  | true =>
    change 2^w-1-(2^w-1-X)=X
    omega

private theorem signSource_add (w : Nat) (Q : Bool) (X Y : Nat) (hX : X<2^w) :
    (signSourceValue w Q X+Y+Q.toNat)%2^w=signedWordValue w Q X Y := by
  cases Q with
  | false => simp [signSourceValue,signedWordValue,Nat.add_comm]
  | true =>
    change (2^w-1-X+Y+1)%2^w=(Y+2^w-X)%2^w
    congr 1
    omega

private theorem complementSource_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (Q : Bool) (X Y : Nat) :
    {{ q=Q,x=X,y=Y,carry=0 }} signComplement q x
    {{ q=Q,x=(signSourceValue x.length Q X),y=Y,carry=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hl := List.nodup_cons.mp hn
  have hx := (List.nodup_append'.mp (List.nodup_append'.mp hl.2).1).1
  have hq : q∉x := fun hm => hl.1 (by simp [hm])
  have hy : ∀ a∈y,a∉x := by
    intro a ha hm
    exact List.disjoint_left.mp (List.nodup_append'.mp
      (List.nodup_append'.mp hl.2).1).2.2 hm ha
  have hc : ∀ a∈carry,a∉x := by
    intro a ha hm
    exact List.disjoint_left.mp (List.nodup_append'.mp hl.2).2.2
      (List.mem_append_left _ hm) ha
  obtain ⟨hp,he,hv⟩ := signComplement_correct q x hx hq s m
  refine ⟨hp,⟨⟨⟨(he q hq).trans h.1.1.1,?_⟩,?_⟩,?_⟩⟩
  · simpa only [h.1.1.1,h.1.1.2,signSourceValue] using hv
  · exact (regValue_congr _ _ _ (fun a ha => he a (hy a ha))).trans h.1.2
  · exact (regValue_congr _ _ _ (fun a ha => he a (hc a ha))).trans h.2

private theorem signCore_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (X Y : Nat) :
    {{ q=Q,x=X,y=Y,carry=0 }} addInPlace x y carry q
    {{ q=Q,x=X,y=((X+Y+Q.toNat)%2^y.length),carry=0 }} := by
  intro s m h
  obtain ⟨hp,ho⟩ := addInPlace_spec x y carry q hn hx hc X Y Q s m
    ⟨⟨⟨h.1.1.2,h.1.2⟩,h.1.1.1⟩,h.2⟩
  exact ⟨hp,⟨⟨⟨ho.1.2,ho.1.1.1⟩,ho.1.1.2⟩,ho.2⟩⟩

/-- q=false adds source x; q=true subtracts x. Control q doubles as carry-in.
The source mask is never materialized. -/
def signedAdd (q : Wire) (x y carry : List Wire) : Program :=
  signComplement q x ++ addInPlace x y carry q ++ signComplement q x

/-- All-value modular signed add/sub with source/control/work and sign restored
for every measurement record. Bounds follow from the physical words. -/
theorem signedAdd_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (X Y : Nat) :
    {{ q=Q,x=X,y=Y,carry=0 }} signedAdd q x y carry
    {{ q=Q,x=X,y=(signedWordValue y.length Q X Y),carry=0 }} := by
  intro s m h
  have hX : X<2^y.length := by
    have hh := regValue_lt x s.basis
    rw [show regValue x s.basis=X from h.1.1.2,hx] at hh
    exact hh
  let V := signSourceValue y.length Q X
  have h1 := complementSource_spec q x y carry hn Q X Y
  rw [hx] at h1
  have h2 := signCore_spec q x y carry hn hx hc Q V Y
  have h3 := complementSource_spec q x y carry hn Q V ((V+Y+Q.toNat)%2^y.length)
  dsimp only [V] at h3
  rw [hx,signSource_twice y.length Q X hX] at h3
  have hall := (h1.seq h2).seq h3
  rw [signSource_add y.length Q X Y hX] at hall
  simpa only [signedAdd,List.append_assoc] using hall s m h

private theorem complementTarget_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (Q : Bool) (X Y : Nat) :
    {{ q=Q,x=X,y=Y,carry=0 }} notRegister y
    {{ q=Q,x=X,y=(2^y.length-1-Y),carry=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hl := List.nodup_cons.mp hn
  have hxy := List.nodup_append'.mp (List.nodup_append'.mp hl.2).1
  have hyc := List.nodup_append'.mp hl.2
  have hqy : q∉y := fun hm => hl.1 (by simp [hm])
  have hcx : ∀ a∈x,a∉y := fun a ha hm => List.disjoint_left.mp hxy.2.2 ha hm
  have hcy : ∀ a∈carry,a∉y := fun a ha hm =>
    List.disjoint_left.mp hyc.2.2 (List.mem_append_right _ hm) ha
  rw [notRegister_correct y hxy.2.1]
  refine ⟨rfl,⟨⟨⟨?_,?_⟩,?_⟩,?_⟩⟩
  · simp [hqy,h.1.1.1]
  · exact (regValue_congr _ _ _ (fun a ha => by simp [hcx a ha])).trans h.1.1.2
  · rw [regValue_congr y _ (fun a => !s.basis a) (by intro a ha; simp [ha]),
      regValue_complement,h.1.2]
  · exact (regValue_congr _ _ _ (fun a ha => by simp [hcy a ha])).trans h.2

private theorem complement_add_sub (N X Y : Nat) (hN : 0<N) (hX : X<N) (hY : Y<N) :
    N-1-((X+(N-1-Y))%N)=(Y+N-X)%N := by
  by_cases h : X≤Y
  · rw [Nat.mod_eq_of_lt (show X+(N-1-Y)<N by omega),
      show Y+N-X=(Y-X)+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show X+(N-1-Y)=(X-1-Y)+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show X-1-Y<N by omega),
      Nat.mod_eq_of_lt (show Y+N-X<N by omega)]
    omega

private theorem complement_sub_add (N X Y : Nat) (hN : 0<N) (hX : X<N) (hY : Y<N) :
    N-1-((N-1-Y+N-X)%N)=(Y+X)%N := by
  by_cases hs : Y+X<N
  · rw [show N-1-Y+N-X=(N-1-(Y+X))+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show N-1-(Y+X)<N by omega),Nat.mod_eq_of_lt hs]
    omega
  · rw [Nat.mod_eq_of_lt (show N-1-Y+N-X<N by omega),
      show Y+X=(Y+X-N)+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show Y+X-N<N by omega)]
    omega

private theorem signed_complement_inverse (w : Nat) (Q : Bool) (X Y : Nat)
    (hX : X<2^w) (hY : Y<2^w) :
    2^w-1-signedWordValue w Q X (2^w-1-Y)=signedWordValue w (!Q) X Y := by
  cases Q with
  | false =>
    simpa [signedWordValue,Nat.add_comm] using complement_add_sub (2^w) X Y
      (by positivity) hX hY
  | true =>
    simpa [signedWordValue] using complement_sub_add (2^w) X Y (by positivity) hX hY

/-- The inverse uses the identical signed core conjugated by target X gates.
This avoids assuming an unavailable arbitrary-cin subInPlace specification. -/
def signedSub (q : Wire) (x y carry : List Wire) : Program :=
  notRegister y ++ signedAdd q x y carry ++ notRegister y

theorem signedSub_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (X Y : Nat) :
    {{ q=Q,x=X,y=Y,carry=0 }} signedSub q x y carry
    {{ q=Q,x=X,y=(signedWordValue y.length (!Q) X Y),carry=0 }} := by
  intro s m h
  have hX : X<2^y.length := by
    have hh := regValue_lt x s.basis
    rw [show regValue x s.basis=X from h.1.1.2,hx] at hh
    exact hh
  have hY : Y<2^y.length := by
    have hh := regValue_lt y s.basis
    rw [show regValue y s.basis=Y from h.1.2] at hh
    exact hh
  have h1 := complementTarget_spec q x y carry hn Q X Y
  have h2 := signedAdd_spec q x y carry hn hx hc Q X (2^y.length-1-Y)
  have h3 := complementTarget_spec q x y carry hn Q X
    (signedWordValue y.length Q X (2^y.length-1-Y))
  rw [signed_complement_inverse y.length Q X Y hX hY] at h3
  have hall := (h1.seq h2).seq h3
  simpa only [signedSub,List.append_assoc] using hall s m h

/-- Full-support identities include all measurement correction wires. -/
theorem signedWord_wires (q : Wire) (x y carry : List Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    wires (signedAdd q x y carry)=(q::(x++y++carry)).toFinset ∧
      wires (signedSub q x y carry)=(q::(x++y++carry)).toFinset := by
  have ha := addInPlace_wires x y carry q hx hc
  have hs := signComplement_wires_subset q x
  have hfull : wires (signedAdd q x y carry)=(q::(x++y++carry)).toFinset := by
    simp only [signedAdd,wires_append,ha]
    ext a
    have ht : a∈wires (signComplement q x) → a∈(q::(x++y++carry)).toFinset := by
      intro hm
      have hh := hs hm
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
      tauto
    simp only [Finset.mem_union]
    tauto
  refine ⟨hfull,?_⟩
  simp only [signedSub,wires_append,hfull,notRegister_wires]
  ext a
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto

theorem signedWord_counts (q : Wire) (x y carry : List Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    toffoliCount (signedAdd q x y carry)=y.length-1 ∧
      measurementCount (signedAdd q x y carry)=y.length-1 ∧
      toffoliCount (signedSub q x y carry)=y.length-1 ∧
      measurementCount (signedSub q x y carry)=y.length-1 := by
  have hs := signComplement_counts q x
  have ha := addInPlace_counts x y carry q hx hc
  have hn := notRegister_counts y
  simp [signedAdd,signedSub,toffoliCount_append,measurementCount_append,
    hs.1,hs.2,ha.1,ha.2,hn.1,hn.2]

private theorem signedWord_frame_from_spec (q : Wire) (x y carry : List Wire)
    (p : Program) (_hn : (q::(x++y++carry)).Nodup)
    (hp : wires p=(q::(x++y++carry)).toFinset)
    (Q : Bool) (X Y Z : Nat) (hspec :
      {{ q=Q,x=X,y=Y,carry=0 }} p {{ q=Q,x=X,y=Z,carry=0 }})
    (s : State) (m : List Bool) (hq : s.basis q=Q)
    (hx : regValue x s.basis=X) (hy : regValue y s.basis=Y)
    (hc : regValue carry s.basis=0) (a : Wire) (ha : a∉y) :
    (run p m s).basis a=s.basis a := by
  obtain ⟨_,ho⟩ := hspec s m ⟨⟨⟨hq,hx⟩,hy⟩,hc⟩
  by_cases he : a=q
  · subst a
    exact ho.1.1.1.trans hq.symm
  by_cases hex : a∈x
  · exact (regValue_eq_iff _ _ _).mp (ho.1.1.2.trans hx.symm) a hex
  by_cases hec : a∈carry
  · exact (regValue_eq_iff _ _ _).mp (ho.2.trans hc.symm) a hec
  apply run_preserves_outside
  rw [hp]
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto

theorem signedWord_frame (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hxy : x.length=y.length)
    (hcarry : carry.length+1=y.length) (Q : Bool) (X Y : Nat)
    (s : State) (m : List Bool) (hq : s.basis q=Q)
    (hx : regValue x s.basis=X) (hy : regValue y s.basis=Y)
    (hc : regValue carry s.basis=0) (a : Wire) (ha : a∉y) :
    (run (signedAdd q x y carry) m s).basis a=s.basis a ∧
      (run (signedSub q x y carry) m s).basis a=s.basis a := by
  have hw := signedWord_wires q x y carry hxy hcarry
  exact ⟨signedWord_frame_from_spec q x y carry _ hn hw.1 Q X Y _
      (signedAdd_spec q x y carry hn hxy hcarry Q X Y) s m hq hx hy hc a ha,
    signedWord_frame_from_spec q x y carry _ hn hw.2 Q X Y _
      (signedSub_spec q x y carry hn hxy hcarry Q X Y) s m hq hx hy hc a ha⟩


/-- Standard two's-complement interpretation of a canonical unsigned word. -/
def signedDecode (w X : Nat) : Int :=
  if X<2^(w-1) then (X:Int) else (X:Int)-(2^w:Nat)

/-- Integer operation implemented by the same live control q. -/
def signedIntegerValue (Q : Bool) (A B : Int) : Int := if Q then B-A else B+A

private theorem word_modulus_double (w : Nat) (hw : 0<w) :
    2^w=2*2^(w-1) := by
  calc
    2^w = 2^((w-1)+1) := by congr 1; omega
    _ = 2^(w-1)*2 := pow_succ _ _
    _ = 2*2^(w-1) := Nat.mul_comm _ _

/-- Decode is a different representative of exactly the same modular word. -/
theorem signedDecode_emod (w X : Nat) :
    signedDecode w X % (2^w:Nat)=(X:Int)%(2^w:Nat) := by
  unfold signedDecode
  split_ifs with h
  · rfl
  · rw [Int.sub_emod]
    simp

/-- The decode interval is half-open, including the most negative value. -/
theorem signedDecode_range (w X : Nat) (hw : 0<w) (hX : X<2^w) :
    -((2^(w-1):Nat):Int)≤signedDecode w X ∧
      signedDecode w X<((2^(w-1):Nat):Int) := by
  have hp := word_modulus_double w hw
  unfold signedDecode
  split_ifs with h
  · omega
  · omega

/-- All canonical words satisfy the integer modular relation, without a
no-overflow hypothesis. Overflow is handled by the full physical word. -/
theorem signedWordValue_emod (w : Nat) (Q : Bool) (X Y : Nat) (hX : X<2^w) :
    (signedWordValue w Q X Y : Int)%(2^w:Nat)=
      signedIntegerValue Q (X:Int) (Y:Int)%(2^w:Nat) := by
  cases Q with
  | false =>
    simp only [signedWordValue,signedIntegerValue,Bool.false_eq_true,if_false]
    rw [Int.natCast_emod]
    simp only [Nat.cast_add,Int.emod_emod]
  | true =>
    simp only [signedWordValue,signedIntegerValue,if_true]
    rw [Int.natCast_emod,Int.emod_emod,
      Nat.cast_sub (show X≤Y+2^w by omega),Nat.cast_add]
    rw [show (Y:Int)+(2^w:Nat)-(X:Int)=((Y:Int)-(X:Int))+(2^w:Nat) by ring]
    rw [Int.add_emod]
    simp

/-- The same modular relation for signed source and target representatives. -/
theorem signedWordValue_decode_emod (w : Nat) (Q : Bool) (X Y : Nat)
    (hX : X<2^w) :
    signedDecode w (signedWordValue w Q X Y)%(2^w:Nat)=
      signedIntegerValue Q (signedDecode w X) (signedDecode w Y)%(2^w:Nat) := by
  rw [signedDecode_emod,signedWordValue_emod w Q X Y hX]
  cases Q with
  | false =>
    simp only [signedIntegerValue,Bool.false_eq_true,if_false]
    calc
      ((Y:Int)+(X:Int))%(2^w:Nat) =
          ((Y:Int)%(2^w:Nat)+(X:Int)%(2^w:Nat))%(2^w:Nat) := Int.add_emod _ _ _
      _ = (signedDecode w Y%(2^w:Nat)+signedDecode w X%(2^w:Nat))%(2^w:Nat) := by
        rw [signedDecode_emod,signedDecode_emod]
      _ = (signedDecode w Y+signedDecode w X)%(2^w:Nat) := (Int.add_emod _ _ _).symm
  | true =>
    simp only [signedIntegerValue,if_true]
    calc
      ((Y:Int)-(X:Int))%(2^w:Nat) =
          ((Y:Int)%(2^w:Nat)-(X:Int)%(2^w:Nat))%(2^w:Nat) := Int.sub_emod _ _ _
      _ = (signedDecode w Y%(2^w:Nat)-signedDecode w X%(2^w:Nat))%(2^w:Nat) := by
        rw [signedDecode_emod,signedDecode_emod]
      _ = (signedDecode w Y-signedDecode w X)%(2^w:Nat) := (Int.sub_emod _ _ _).symm

/-- A proved integer range converts modular gate correctness into exact signed
arithmetic. This internal range is to be discharged by the rail invariant. -/
theorem signedWordValue_lift (w : Nat) (Q : Bool) (X Y : Nat)
    (hw : 0<w) (hX : X<2^w)
    (hlo : -((2^(w-1):Nat):Int)≤
      signedIntegerValue Q (signedDecode w X) (signedDecode w Y))
    (hhi : signedIntegerValue Q (signedDecode w X) (signedDecode w Y)<
      ((2^(w-1):Nat):Int)) :
    signedDecode w (signedWordValue w Q X Y)=
      signedIntegerValue Q (signedDecode w X) (signedDecode w Y) := by
  let H : Int := (2^(w-1):Nat)
  let M : Int := (2^w:Nat)
  let D := signedDecode w (signedWordValue w Q X Y)
  let R := signedIntegerValue Q (signedDecode w X) (signedDecode w Y)
  have hZ : signedWordValue w Q X Y<2^w := by
    unfold signedWordValue
    split <;> exact Nat.mod_lt _ (by positivity)
  have hd := signedDecode_range w (signedWordValue w Q X Y) hw hZ
  have hm : D%M=R%M := signedWordValue_decode_emod w Q X Y hX
  have hpow := congrArg (fun a : Nat => (a:Int)) (word_modulus_double w hw)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hpow
  change -H≤D ∧ D<H at hd
  change -H≤R at hlo
  change R<H at hhi
  change M=2*H at hpow
  have hshift : (D+H)%M=(R+H)%M := by
    calc
      (D+H)%M = (D%M+H%M)%M := Int.add_emod _ _ _
      _ = (R%M+H%M)%M := congrArg (fun a => (a+H%M)%M) hm
      _ = (R+H)%M := (Int.add_emod _ _ _).symm
  have hd0 : 0≤D+H := by omega
  have hdlt : D+H<M := by omega
  have hr0 : 0≤R+H := by omega
  have hrlt : R+H<M := by omega
  rw [Int.emod_eq_of_lt hd0 hdlt,Int.emod_eq_of_lt hr0 hrlt] at hshift
  change D=R
  omega

end ECDSAAdd.Arithmetic
