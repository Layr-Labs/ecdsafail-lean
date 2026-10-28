import ECDSAAdd.Arithmetic.InPlaceAdder

namespace ECDSAAdd.Arithmetic

/-- The Cuccaro in-place majority.  The carry is written into `a`, so no
per-bit carry register is allocated. -/
def cuccaroMaj (a b cin : Wire) : Program := [.CX a b,.CX a cin,.CCX b cin a]

/-- Unmajority-and-add: restore `a` and `cin`, and write the sum bit to `b`. -/
def cuccaroUma (a b cin : Wire) : Program := [.CCX b cin a,.CX a cin,.CX cin b]

/-- Fixed-width in-place addition `b += a + cin (mod 2^n)` using the input
word itself for the carry ladder and no work register. -/
def cuccaroAdd : List Wire → List Wire → Wire → Program
  | [], [], _ => []
  | [a], [b], cin => [.CX a b,.CX cin b]
  | a::a'::as, b::b'::bs, cin =>
      cuccaroMaj a b cin ++ (cuccaroAdd (a'::as) (b'::bs) a ++ cuccaroUma a b cin)
  | _, _, _ => []

/-- Fixed-width subtraction by the complement-add-complement identity. -/
def cuccaroSub (a b : List Wire) (cin : Wire) : Program :=
  notRegister b++cuccaroAdd a b cin++notRegister b

@[simp] theorem cuccaroMaj_measurementCount (a b cin : Wire) :
    measurementCount (cuccaroMaj a b cin)=0 := rfl

@[simp] theorem cuccaroUma_measurementCount (a b cin : Wire) :
    measurementCount (cuccaroUma a b cin)=0 := rfl

@[simp] theorem cuccaroAdd_measurementCount (a b : List Wire) (cin : Wire) :
    measurementCount (cuccaroAdd a b cin)=0 := by
  induction b generalizing a cin with
  | nil =>
    cases a with
    | nil => rfl
    | cons x xs => cases xs <;> rfl
  | cons y ys ih =>
    cases a with
    | nil => rfl
    | cons x xs =>
      cases ys with
      | nil => cases xs <;> rfl
      | cons y' ys' =>
        cases xs with
        | nil => rfl
        | cons x' xs' => simp [cuccaroAdd,ih]

theorem cuccaroMaj_correct (a b cin : Wire) (hnd : [a,b,cin].Nodup)
    (s : State) (m : List Bool) :
    let out := run (cuccaroMaj a b cin) m s
    out.phase=s.phase ∧
      out.basis a=carryBit (s.basis a) (s.basis b) (s.basis cin) ∧
      out.basis b=(s.basis a^^s.basis b) ∧
      out.basis cin=(s.basis a^^s.basis cin) ∧
      ∀q,q∉[a,b,cin] → out.basis q=s.basis q := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hnd
  obtain ⟨⟨hab,hac⟩,hbc⟩ := hnd
  let out := run (cuccaroMaj a b cin) m s
  have hbits : out.basis a=carryBit (s.basis a) (s.basis b) (s.basis cin) ∧
      out.basis b=(s.basis a^^s.basis b) ∧ out.basis cin=(s.basis a^^s.basis cin) := by
    dsimp [out,cuccaroMaj,run]
    cases hA : s.basis a <;> cases hB : s.basis b <;> cases hC : s.basis cin <;>
      simp_all [writeBit,Ne.symm hab,Ne.symm hac,Ne.symm hbc,carryBit]
  change out.phase=s.phase ∧ _
  refine ⟨rfl,hbits.1,hbits.2.1,hbits.2.2,?_⟩
  · intro q hq
    apply run_preserves_outside
    simp [cuccaroMaj,wires,Instr.wires] at hq ⊢
    tauto

theorem cuccaroUma_restore (a b cin : Wire) (hnd : [a,b,cin].Nodup)
    (s : State) (m : List Bool) (A B C : Bool)
    (ha : s.basis a=carryBit A B C) (hb : s.basis b=(A^^B))
    (hc : s.basis cin=(A^^C)) :
    let out := run (cuccaroUma a b cin) m s
    out.phase=s.phase ∧ out.basis a=A ∧ out.basis b=sumBit A B C ∧
      out.basis cin=C ∧ ∀q,q∉[a,b,cin] → out.basis q=s.basis q := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hnd
  obtain ⟨⟨hab,hac⟩,hbc⟩ := hnd
  let out := run (cuccaroUma a b cin) m s
  have hbits : out.basis a=A ∧ out.basis b=sumBit A B C ∧ out.basis cin=C := by
    dsimp [out,cuccaroUma,run]
    cases hA : s.basis a <;> cases hB : s.basis b <;> cases hC : s.basis cin <;>
      cases A <;> cases B <;> cases C <;>
      simp_all [writeBit,Ne.symm hab,Ne.symm hac,Ne.symm hbc,
        carryBit,sumBit]
  change out.phase=s.phase ∧ _
  refine ⟨rfl,hbits.1,hbits.2.1,hbits.2.2,?_⟩
  · intro q hq
    apply run_preserves_outside
    simp [cuccaroUma,wires,Instr.wires] at hq ⊢
    tauto

theorem cuccaroAdd_correct (a b : List Wire) (cin : Wire)
    (hnd : (cin::a++b).Nodup) (hlen : a.length=b.length)
    (s : State) (m : List Bool) :
    let out := run (cuccaroAdd a b cin) m s
    out.phase=s.phase ∧ regValue a out.basis=regValue a s.basis ∧
      out.basis cin=s.basis cin ∧
      regValue b out.basis=
        (regValue a s.basis+regValue b s.basis+(s.basis cin).toNat)%2^b.length ∧
      ∀q,q∉cin::a++b → out.basis q=s.basis q := by
  induction b generalizing a cin s m with
  | nil =>
    have ha : a=[] := List.eq_nil_of_length_eq_zero hlen
    subst a
    simp [cuccaroAdd,run,regValue,Nat.mod_one]
  | cons y ys ih =>
    cases a with
    | nil => simp at hlen
    | cons x xs =>
      cases ys with
      | nil =>
        have hx : xs=[] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        subst xs
        have hcnt := List.nodup_iff_count.mp hnd
        have hxy : x≠y := by
          intro e; subst y
          have h := hcnt x
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hcy : cin≠y := by
          intro e; subst cin
          have h := hcnt y
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hcx : cin≠x := by
          intro e; subst cin
          have h := hcnt x
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        simp only [cuccaroAdd,run,regValue,List.foldr_cons,List.foldr_nil,
          List.length_cons,List.length_nil]
        refine ⟨True.intro,?_,?_,?_,?_⟩
        · simp [writeBit,hxy,hcy]
        · simp [writeBit,hcy]
        · simp [writeBit,hcy]
          cases s.basis x <;> cases s.basis y <;> cases s.basis cin <;> rfl
        · intro q hq
          simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false,not_or] at hq
          simp [writeBit,hq.2]
      | cons y' ys' =>
        cases xs with
        | nil => simp at hlen
        | cons x' xs' =>
          let aTail := x'::xs'
          let bTail := y'::ys'
          have htlen : aTail.length=bTail.length := by simpa [aTail,bTail] using hlen
          have cnt := List.nodup_iff_count.mp hnd
          have allN : (cin::(x::aTail)++(y::bTail)).Nodup := by
            simpa [aTail,bTail] using hnd
          have n0 := List.nodup_cons.mp allN
          have nap := List.nodup_append'.mp n0.2
          have nA := List.nodup_cons.mp nap.1
          have nB := List.nodup_cons.mp nap.2.1
          have dis := nap.2.2
          have yAway : y∉x::aTail++bTail := by
            intro hm
            rcases List.mem_append.mp hm with hm|hm
            · exact List.disjoint_left.mp dis hm (by simp)
            · exact nB.1 hm
          have cinAway : cin∉x::aTail++bTail := by
            intro hm
            apply n0.1
            rcases List.mem_append.mp hm with hm|hm
            · exact List.mem_append_left _ hm
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
          have sourceAway (q : Wire) (hq : q∈aTail) : q∉[x,y,cin] := by
            simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
            refine ⟨?_,?_,?_⟩
            · intro he; subst q; exact nA.1 hq
            · intro he; subst q
              exact List.disjoint_left.mp dis (List.mem_cons_of_mem x hq)
                (List.mem_cons_self)
            · intro he; subst q
              exact n0.1 (List.mem_append_left _ (List.mem_cons_of_mem x hq))
          have targetAway (q : Wire) (hq : q∈bTail) : q∉[x,y,cin] := by
            simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
            refine ⟨?_,?_,?_⟩
            · intro he; subst q
              exact List.disjoint_left.mp dis (List.mem_cons_self)
                (List.mem_cons_of_mem y hq)
            · intro he; subst q; exact nB.1 hq
            · intro he; subst q
              exact n0.1 (List.mem_append_right _ (List.mem_cons_of_mem y hq))
          have h3 : [x,y,cin].Nodup := by
            apply List.nodup_iff_count.mpr; intro q
            have h := cnt q
            simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
            omega
          have htail : (x::aTail++bTail).Nodup := by
            apply List.nodup_iff_count.mpr; intro q
            have h := cnt q
            simp only [aTail,bTail,List.count_cons,List.count_append] at h ⊢
            omega
          let u := run (cuccaroMaj x y cin) m s
          have maj := cuccaroMaj_correct x y cin h3 s m
          have hrec := ih aTail x htail htlen u m
          let v := run (cuccaroAdd aTail bTail x) m u
          have keepRec (q : Wire) (hq : q∉x::aTail++bTail) : v.basis q=u.basis q := hrec.2.2.2.2 q hq
          have xV : v.basis x=carryBit (s.basis x) (s.basis y) (s.basis cin) :=
            hrec.2.2.1.trans maj.2.1
          have yV : v.basis y=(s.basis x^^s.basis y) :=
            (keepRec y yAway).trans maj.2.2.1
          have cinV : v.basis cin=(s.basis x^^s.basis cin) :=
            (keepRec cin cinAway).trans maj.2.2.2.1
          have uma := cuccaroUma_restore x y cin h3 v m
            (s.basis x) (s.basis y) (s.basis cin) xV yV cinV
          let out := run (cuccaroUma x y cin) m v
          have tailSource : regValue aTail out.basis=regValue aTail s.basis := by
            calc
              regValue aTail out.basis = regValue aTail v.basis := regValue_congr _ _ _ (fun q hq =>
                uma.2.2.2.2 q (sourceAway q hq))
              _ = regValue aTail u.basis := hrec.2.1
              _ = regValue aTail s.basis := regValue_congr _ _ _ (fun q hq =>
                maj.2.2.2.2 q (sourceAway q hq))
          have tailTarget : regValue bTail out.basis=
              (regValue aTail s.basis+regValue bTail s.basis+
                (carryBit (s.basis x) (s.basis y) (s.basis cin)).toNat)%2^bTail.length := by
            calc
              regValue bTail out.basis = regValue bTail v.basis := regValue_congr _ _ _ (fun q hq =>
                uma.2.2.2.2 q (targetAway q hq))
              _ = (regValue aTail u.basis+regValue bTail u.basis+(u.basis x).toNat)%2^bTail.length := hrec.2.2.2.1
              _ = _ := by
                have ua := regValue_congr aTail u.basis s.basis
                  (fun q hq => maj.2.2.2.2 q (sourceAway q hq))
                have ub := regValue_congr bTail u.basis s.basis
                  (fun q hq => maj.2.2.2.2 q (targetAway q hq))
                rw [maj.2.1,ua,ub]
          have targetValue : regValue (y::bTail) out.basis=
              (regValue (x::aTail) s.basis+regValue (y::bTail) s.basis+
                (s.basis cin).toNat)%2^(y::bTail).length := by
            change (if out.basis y then 1 else 0)+2*regValue bTail out.basis=_
            rw [uma.2.2.1,tailTarget]
            simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,
              List.length_cons] using sum_value_step (s.basis x) (s.basis y)
                (s.basis cin) (regValue aTail s.basis) (regValue bTail s.basis)
                bTail.length
          have sourceValue : regValue (x::aTail) out.basis=regValue (x::aTail) s.basis := by
            change (if out.basis x then 1 else 0)+2*regValue aTail out.basis=
              (if s.basis x then 1 else 0)+2*regValue aTail s.basis
            rw [uma.2.1,tailSource]
          have outside (q : Wire) (hq : q∉cin::(x::aTail)++(y::bTail)) : out.basis q=s.basis q := by
            have hq' : q∉[x,y,cin] ∧ q∉x::aTail++bTail := by
              simp only [List.mem_cons,List.mem_append,not_or] at hq ⊢
              tauto
            exact (uma.2.2.2.2 q hq'.1).trans
              ((hrec.2.2.2.2 q hq'.2).trans (maj.2.2.2.2 q hq'.1))
          have exec : run (cuccaroAdd (x::aTail) (y::bTail) cin) m s=out := by
            change run (cuccaroMaj x y cin++
              (cuccaroAdd aTail bTail x++cuccaroUma x y cin)) m s=out
            rw [run_append,run_take,run_append,run_take]
            rfl
          rw [exec]
          exact ⟨uma.1.trans (hrec.1.trans maj.1),sourceValue,uma.2.2.2.1,
            targetValue,outside⟩

theorem cuccaroAdd_counts (a b : List Wire) (cin : Wire) (hlen : a.length=b.length) :
    toffoliCount (cuccaroAdd a b cin)=2*(b.length-1) ∧
      measurementCount (cuccaroAdd a b cin)=0 := by
  induction b generalizing a cin with
  | nil =>
    have ha : a=[] := List.eq_nil_of_length_eq_zero hlen
    subst a
    simp [cuccaroAdd,toffoliCount,measurementCount]
  | cons y ys ih =>
    cases a with
    | nil => simp at hlen
    | cons x xs =>
      cases ys with
      | nil =>
        have hx : xs=[] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        subst xs
        simp [cuccaroAdd,toffoliCount,measurementCount]
      | cons y' ys' =>
        cases xs with
        | nil => simp at hlen
        | cons x' xs' =>
          have h := ih (x'::xs') x (by simpa using hlen)
          simp [cuccaroAdd,cuccaroMaj,cuccaroUma,toffoliCount,measurementCount,h]
          omega

theorem cuccaroSub_counts (a b : List Wire) (cin : Wire) (hlen : a.length=b.length) :
    toffoliCount (cuccaroSub a b cin)=2*(b.length-1) ∧
      measurementCount (cuccaroSub a b cin)=0 := by
  have h := cuccaroAdd_counts a b cin hlen
  simp [cuccaroSub,toffoliCount_append,measurementCount_append,
    (notRegister_counts b).1,(notRegister_counts b).2,h.1,h.2]

private theorem cuccaro_complement_sub (A B N : Nat) (hN : 0<N)
    (hA : A<N) (hB : B<N) :
    N-1-((A+(N-1-B))%N)=(B+N-A)%N := by
  by_cases h : A≤B
  · rw [Nat.mod_eq_of_lt (show A+(N-1-B)<N by omega),
      show B+N-A=(B-A)+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show A+(N-1-B)=(A-1-B)+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show A-1-B<N by omega),
      Nat.mod_eq_of_lt (show B+N-A<N by omega)]
    omega

theorem cuccaroSub_correct (a b : List Wire) (cin : Wire)
    (hnd : (cin::a++b).Nodup) (hlen : a.length=b.length)
    (s : State) (m : List Bool) (hcin : s.basis cin=false) :
    let out := run (cuccaroSub a b cin) m s
    out.phase=s.phase ∧ regValue a out.basis=regValue a s.basis ∧
      out.basis cin=false ∧
      regValue b out.basis=
        (regValue b s.basis+2^b.length-regValue a s.basis)%2^b.length ∧
      ∀q,q∉cin::a++b → out.basis q=s.basis q := by
  have bN : b.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h
    omega
  have disA (q : Wire) (hq : q∈a) : q∉b := by
    intro hb
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hb
    simp only [List.count_cons,List.count_append] at h
    omega
  have cinAway : cin∉b := by
    intro hb
    have h := List.nodup_iff_count.mp hnd cin
    have h2 := List.count_pos_iff.mpr hb
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
    omega
  let u := run (notRegister b) m s
  have nu := notRegister_correct b bN s m
  have nu' : u=⟨s.phase,fun w => if w∈b then !s.basis w else s.basis w⟩ := nu
  have aU : regValue a u.basis=regValue a s.basis := regValue_congr _ _ _ (fun q hq => by
    rw [nu']
    simp [disA q hq])
  have bU : regValue b u.basis=2^b.length-1-regValue b s.basis := by
    rw [nu']
    change regValue b (fun q => if q∈b then !s.basis q else s.basis q)=_
    rw [regValue_congr b _ (fun q => !s.basis q) (by intro q hq; simp [hq]),regValue_complement]
  have cinU : u.basis cin=false := by rw [nu']; simpa [cinAway] using hcin
  let v := run (cuccaroAdd a b cin) m u
  have av := cuccaroAdd_correct a b cin hnd hlen u m
  have aV : regValue a v.basis=regValue a s.basis := av.2.1.trans aU
  have cinV : v.basis cin=false := av.2.2.1.trans cinU
  have bV : regValue b v.basis=
      (regValue a s.basis+(2^b.length-1-regValue b s.basis))%2^b.length := by
    rw [av.2.2.2.1,aU,bU,cinU]
    rfl
  let out := run (notRegister b) m v
  have nv := notRegister_correct b bN v m
  have nv' : out=⟨v.phase,fun w => if w∈b then !v.basis w else v.basis w⟩ := nv
  have aOut : regValue a out.basis=regValue a s.basis := by
    rw [nv']
    exact (regValue_congr _ _ _ (fun q hq => by simp [disA q hq])).trans aV
  have cinOut : out.basis cin=false := by rw [nv']; simpa [cinAway] using cinV
  have bOut : regValue b out.basis=
      (regValue b s.basis+2^b.length-regValue a s.basis)%2^b.length := by
    rw [nv']
    change regValue b (fun q => if q∈b then !v.basis q else v.basis q)=_
    rw [regValue_congr b _ (fun q => !v.basis q) (by intro q hq; simp [hq]),
      regValue_complement,bV]
    have hpow : 0<2^b.length := Nat.two_pow_pos _
    have ha := regValue_lt a s.basis
    rw [hlen] at ha
    have hb := regValue_lt b s.basis
    exact cuccaro_complement_sub _ _ _ hpow ha hb
  have outside (q : Wire) (hq : q∉cin::a++b) : out.basis q=s.basis q := by
    have hh0 : (q≠cin ∧ q∉a) ∧ q∉b := by
      simpa only [List.mem_cons,List.mem_append,not_or] using hq
    have hh : q≠cin ∧ q∉a ∧ q∉b := ⟨hh0.1.1,hh0.1.2,hh0.2⟩
    have hqb : q∉b := hh.2.2
    rw [nv']
    simp only [hqb,if_false]
    exact (av.2.2.2.2 q hq).trans (by rw [nu']; simp [hqb])
  have phaseOut : out.phase=s.phase := by rw [nv']; exact av.1.trans (by rw [nu'])
  have hnotS : run (notRegister b) [] s=run (notRegister b) m s := by
    have h := run_take (notRegister b) m s
    simpa only [(notRegister_counts b).2,List.take_zero] using h
  have haddU : run (cuccaroAdd a b cin) [] u=run (cuccaroAdd a b cin) m u := by
    have h := run_take (cuccaroAdd a b cin) m u
    simpa only [cuccaroAdd_measurementCount,List.take_zero] using h
  have exec : run (cuccaroSub a b cin) m s=out := by
    simp only [cuccaroSub,List.append_assoc,run_append,(notRegister_counts b).2,
      cuccaroAdd_measurementCount,List.take_zero,List.drop_zero]
    rw [hnotS,haddU]
  rw [exec]
  exact ⟨phaseOut,aOut,cinOut,bOut,outside⟩

theorem cuccaroAdd_wires_subset (a b : List Wire) (cin : Wire) :
    wires (cuccaroAdd a b cin)⊆(cin::a++b).toFinset := by
  induction a generalizing b cin with
  | nil => cases b <;> simp [cuccaroAdd,wires]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases b with
      | nil => simp [cuccaroAdd,wires]
      | cons y ys => cases ys <;> simp [cuccaroAdd,wires,Instr.wires]
    | cons x' xs' =>
      cases b with
      | nil => simp [cuccaroAdd,wires]
      | cons y ys =>
        cases ys with
        | nil => simp [cuccaroAdd,wires]
        | cons y' ys' =>
          intro q hq
          simp only [cuccaroAdd,wires_append,Finset.mem_union] at hq
          have hm : wires (cuccaroMaj x y cin)⊆{x,y,cin} := by
            intro w hw; simp [cuccaroMaj,wires,Instr.wires] at hw ⊢; tauto
          have hu : wires (cuccaroUma x y cin)⊆{x,y,cin} := by
            intro w hw; simp [cuccaroUma,wires,Instr.wires] at hw ⊢; tauto
          rcases hq with hq|(hq|hq)
          · have h := hm hq
            simp only [Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,
              List.mem_cons,List.mem_append] at h ⊢
            tauto
          · have h := ih (y'::ys') x hq
            simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
            tauto
          · have h := hu hq
            simp only [Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,
              List.mem_cons,List.mem_append] at h ⊢
            tauto

theorem cuccaroSub_wires_subset (a b : List Wire) (cin : Wire) :
    wires (cuccaroSub a b cin)⊆(cin::a++b).toFinset := by
  have hb : b.toFinset⊆(cin::a++b).toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    tauto
  simp only [cuccaroSub,wires_append,notRegister_wires]
  exact Finset.union_subset (Finset.union_subset hb (cuccaroAdd_wires_subset a b cin)) hb

end ECDSAAdd.Arithmetic
