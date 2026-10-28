import ECDSAAdd.Arithmetic.Paper935.FireCleanup

namespace ECDSAAdd.Arithmetic.Paper935

/-- The author's carry-in wrapper for the shared-carry path. -/
def rowAddCin (c cin k : Wire) (a b : List Wire) : Program :=
  [.CX cin k] ++ rowAdd c a b k ++ [.CX cin k]

theorem rowAddCin_run (c cin k : Wire) (a b : List Wire)
    (hn : (c::k::(a++b)).Nodup) (hl : a.length=b.length)
    (hik : cin≠k) (hic : c≠k) (hi : cin∉b) (hk : k∉a)
    (s : State) (m : List Bool) (hzero : s.basis k=false) :
    let t := run (rowAddCin c cin k a b) m s
    t.phase=s.phase ∧ (∀ q,q∉b → t.basis q=s.basis q) ∧
      regValue b t.basis=(if s.basis c then
        (regValue a s.basis+regValue b s.basis+(s.basis cin).toNat)%2^b.length
        else regValue b s.basis) := by
  let u : State := ⟨s.phase,writeBit s.basis k (s.basis cin)⟩
  have hu (n : List Bool) : run [.CX cin k] n s=u := by simp [run,u,writeBit,hzero]
  have hkb : k∉b := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 ∘ List.mem_append_right _
  have ha : regValue a u.basis=regValue a s.basis := by
    apply regValue_congr; intro q hq
    simp [u,writeBit,show q≠k from fun h => hk (h ▸ hq)]
  have hb : regValue b u.basis=regValue b s.basis := by
    apply regValue_congr; intro q hq
    simp [u,writeBit,show q≠k from fun h => hkb (h ▸ hq)]
  let v := run (rowAdd c a b k) m u
  have hv := rowAdd_run c k a b hn hl u m
  have hvk : v.basis k=s.basis cin := by rw [hv.2.1 k hkb]; simp [u,writeBit]
  have hvi : v.basis cin=s.basis cin := by rw [hv.2.1 cin hi]; simp [u,writeBit,hik]
  have hc : u.basis c=s.basis c := by simp [u,writeBit,hic]
  have he : run (rowAddCin c cin k a b) m s=run [.CX cin k] m v := by
    rw [rowAddCin,run_append,run_take,run_append,run_take]
    simp only [measurementCount_append,measurementCount,rowAdd_measurements,Nat.zero_add,List.drop_zero]
    rw [hu m]
  rw [he]
  refine ⟨hv.1,?_,?_⟩
  · intro q hq
    by_cases hqk : q=k
    · subst q; simp [run,writeBit,hvk,hvi,hzero]
    · change writeBit v.basis k (v.basis k ^^ v.basis cin) q=s.basis q
      simp only [writeBit,Function.update_of_ne hqk]
      rw [hv.2.1 q hq]
      simp [u,writeBit,hqk]
  · have hout : regValue b (run [.CX cin k] m v).basis=regValue b v.basis := by
      apply regValue_congr; intro q hq
      simp [run,writeBit,show q≠k from fun h => hkb (h ▸ hq)]
    rw [hout,hv.2.2,hc,ha,hb]
    simp [u,writeBit]

/-- F4 on a single padded row: retain the AND of swap/parity, complement
the target, add source plus carry-in, and retire that AND by measurement.
Only two clean transient wires are used (u and k); no width-sized mask. -/
def branchRow (swap parity u k : Wire) (a b : List Wire) : Program :=
  [.CCX swap parity u] ++ signComplement u b ++ rowAddCin parity u k a b ++
    eraseAnd swap parity u

def branchWord (w : Nat) (swap parity : Bool) (a b : Nat) : Nat :=
  if parity then (if swap then a+2^w-b else a+b)%2^w else b

theorem branchRow_run (q c u k : Wire) (a b : List Wire)
    (hn : (q::c::u::k::(a++b)).Nodup) (hl : a.length=b.length)
    (s : State) (m : List Bool) (hu : s.basis u=false) (hk : s.basis k=false) :
    let t := run (branchRow q c u k a b) m s
    t.phase=s.phase ∧ (∀ w,w∉b → t.basis w=s.basis w) ∧
      regValue b t.basis=branchWord b.length (s.basis q) (s.basis c)
        (regValue a s.basis) (regValue b s.basis) := by
  have nd := hn
  simp only [List.nodup_cons,List.mem_cons,not_or] at nd
  have hqc : q≠c := nd.1.1
  have hqu : q≠u := nd.1.2.1
  have hqk : q≠k := nd.1.2.2.1
  have hcu : c≠u := nd.2.1.1
  have hck : c≠k := nd.2.1.2.1
  have huk : u≠k := nd.2.2.1.1
  have hqa : q∉a++b := nd.1.2.2.2
  have hca : c∉a++b := nd.2.1.2.2
  have hua : u∉a++b := nd.2.2.1.2
  have hka : k∉a++b := nd.2.2.2.1
  have hab : (a++b).Nodup := nd.2.2.2.2
  have hbn : b.Nodup := (List.nodup_append.mp hab).2.1
  have hdis := (List.nodup_append'.mp hab).2.2
  have qb : q∉b := fun h => hqa (List.mem_append_right _ h)
  have cb : c∉b := fun h => hca (List.mem_append_right _ h)
  have ub : u∉b := fun h => hua (List.mem_append_right _ h)
  have kb : k∉b := fun h => hka (List.mem_append_right _ h)
  have hnd : (c::k::(a++b)).Nodup := by
    simp only [List.nodup_cons,List.mem_cons,not_or]
    exact ⟨⟨hck,hca⟩,hka,hab⟩
  let t : State := ⟨s.phase,writeBit s.basis u (s.basis q && s.basis c)⟩
  have ht (n : List Bool) : run [.CCX q c u] n s=t := by simp [run,t,hu]
  have tc : t.basis c=s.basis c := by simp [t,writeBit,hcu]
  have tq : t.basis q=s.basis q := by simp [t,writeBit,hqu]
  have tu : t.basis u=(s.basis q && s.basis c) := by simp [t,writeBit]
  have tk : t.basis k=false := by simp [t,writeBit,Ne.symm huk,hk]
  have ta : regValue a t.basis=regValue a s.basis := by
    apply regValue_congr; intro w hw
    simp [t,writeBit,show w≠u from fun h => hua (List.mem_append_left _ (h ▸ hw))]
  have tb : regValue b t.basis=regValue b s.basis := by
    apply regValue_congr; intro w hw
    simp [t,writeBit,show w≠u from fun h => ub (h ▸ hw)]
  let v := run (signComplement u b) m t
  have hv := signComplement_correct u b hbn ub t m
  have va : regValue a v.basis=regValue a s.basis := by
    rw [regValue_congr a v.basis t.basis (fun w hw => hv.2.1 w (List.disjoint_left.mp hdis hw)),ta]
  have vc : v.basis c=s.basis c := (hv.2.1 c cb).trans tc
  have vu : v.basis u=(s.basis q && s.basis c) := (hv.2.1 u ub).trans tu
  have vk : v.basis k=false := (hv.2.1 k kb).trans tk
  let r := run (rowAddCin c u k a b) m v
  have hr := rowAddCin_run c u k a b hnd hl huk hck ub
    (fun h => hka (List.mem_append_left _ h)) v m vk
  have rp : r.basis u=(r.basis q && r.basis c) := by
    rw [hr.2.1 u ub,hr.2.1 q qb,hr.2.1 c cb,hv.2.1 u ub,hv.2.1 q qb,hv.2.1 c cb,tu,tq,tc]
  have he : run (branchRow q c u k a b) m s =
      run (eraseAnd q c u) m r := by
    have hm : measurementCount (rowAddCin c u k a b)=0 := by
      simp [rowAddCin,measurementCount_append,measurementCount]
    rw [branchRow,run_append,run_take,run_append,run_take,run_append,run_take]
    simp only [measurementCount_append,measurementCount,(signComplement_counts u b).2,
      hm,Nat.zero_add,List.drop_zero]
    rw [ht m]
  rw [he,eraseAnd_run q c u hqu hcu r m rp]
  refine ⟨hr.1.trans hv.1,?_,?_⟩
  · intro w hw
    by_cases hwu : w=u
    · subst w; simp [writeBit,hu]
    · change writeBit r.basis u false w=s.basis w
      simp only [writeBit,Function.update_of_ne hwu]
      rw [hr.2.1 w hw,hv.2.1 w hw]
      simp [t,writeBit,hwu]
  · have ho : regValue b (writeBit r.basis u false)=regValue b r.basis := by
      apply regValue_congr; intro w hw
      simp [writeBit,show w≠u from fun h => ub (h ▸ hw)]
    rw [ho,hr.2.2,vc,va,vu,hv.2.2,tu,tb]
    have hb := regValue_lt b s.basis
    cases hq : s.basis q <;> cases hc : s.basis c <;>
      simp [branchWord,Bool.toNat]
    congr 1
    omega

/-- Integer operation of F4 in post-swap row names. -/
def branchInt (swap parity : Bool) (a b : Int) : Int :=
  if parity then (if swap then a-b else b+a) else b

theorem branchWord_lift (w : Nat) (q c : Bool) (a b : Nat)
    (hw : 0<w) (ha : a<2^w) (hb : b<2^w)
    (hlo : -((2^(w-1):Nat):Int)≤branchInt q c (signedDecode w a) (signedDecode w b))
    (hhi : branchInt q c (signedDecode w a) (signedDecode w b)<((2^(w-1):Nat):Int)) :
    signedDecode w (branchWord w q c a b)=branchInt q c (signedDecode w a) (signedDecode w b) := by
  cases c with
  | false => rfl
  | true =>
    cases q with
    | false =>
      simpa [branchWord,branchInt,signedWordValue,signedIntegerValue,Nat.add_comm] using
        signedWordValue_lift w false a b hw ha hlo hhi
    | true =>
      simpa [branchWord,branchInt,signedWordValue,signedIntegerValue] using
        signedWordValue_lift w true b a hw hb hlo hhi

theorem branchRow_signed (q c u k : Wire) (a b : List Wire)
    (hn : (q::c::u::k::(a++b)).Nodup) (hl : a.length=b.length) (hw : 0<b.length)
    (s : State) (m : List Bool) (hu : s.basis u=false) (hk : s.basis k=false)
    (hlo : -((2^(b.length-1):Nat):Int) ≤
      branchInt (s.basis q) (s.basis c) (signedRegValue a s.basis) (signedRegValue b s.basis))
    (hhi : branchInt (s.basis q) (s.basis c) (signedRegValue a s.basis)
      (signedRegValue b s.basis)<((2^(b.length-1):Nat):Int)) :
    let t := run (branchRow q c u k a b) m s
    t.phase=s.phase ∧ (∀ w,w∉b → t.basis w=s.basis w) ∧
      signedRegValue b t.basis=branchInt (s.basis q) (s.basis c)
        (signedRegValue a s.basis) (signedRegValue b s.basis) := by
  have ht := branchRow_run q c u k a b hn hl s m hu hk
  refine ⟨ht.1,ht.2.1,?_⟩
  unfold signedRegValue
  rw [ht.2.2,hl]
  exact branchWord_lift b.length _ _ _ _ hw (by simpa [hl] using regValue_lt a s.basis)
    (regValue_lt b s.basis) (by simpa [signedRegValue,hl] using hlo)
    (by simpa [signedRegValue,hl] using hhi)

theorem branchRow_counts (q c u k : Wire) (a b : List Wire) (hl : a.length=b.length) :
    toffoliCount (branchRow q c u k a b)=1+(3*b.length-2) ∧
      measurementCount (branchRow q c u k a b)=1 := by
  simp [branchRow,rowAddCin,toffoliCount_append,measurementCount_append,
    signComplement_counts,rowAdd_toffolis c k a b hl,eraseAnd,toffoliCount,measurementCount]

theorem branchRow_support (q c u k : Wire) (a b : List Wire) :
    wires (branchRow q c u k a b) ⊆ (q::c::u::k::(a++b)).toFinset := by
  have ha := rowAdd_support c k a b
  have hs := signComplement_wires_subset u b
  intro w hw
  simp only [branchRow,rowAddCin,wires_append,Finset.mem_union] at hw
  rcases hw with ((h | h) | ((h | h) | h)) | h
  · simp [wires,Instr.wires] at h
    simp only [List.mem_toFinset,List.mem_cons]
    tauto
  · have h := hs h
    simp only [List.mem_toFinset,List.mem_cons] at h ⊢
    simp only [List.mem_append]
    tauto
  · simp [wires,Instr.wires] at h
    simp only [List.mem_toFinset,List.mem_cons]
    tauto
  · have hh := ha h
    simp only [List.mem_toFinset,List.mem_cons] at hh ⊢
    tauto
  · simp [wires,Instr.wires] at h
    simp only [List.mem_toFinset,List.mem_cons]
    tauto
  · simp [eraseAnd,wires,Instr.wires,correctionWires] at h
    simp only [List.mem_toFinset,List.mem_cons]
    tauto

/-- The two F4 row operations share the same clean carry and AND scratch. -/
def branchPair (q c u k : Wire) (a b x y : List Wire) : Program :=
  branchRow q c u k a b ++ branchRow q c u k x y

private theorem signed_frame (a : List Wire) (s t : BasisState)
    (h : ∀ w∈a,s w=t w) : signedRegValue a s=signedRegValue a t := by
  unfold signedRegValue
  rw [regValue_congr a s t h]

theorem branchPair_signed (q c u k : Wire) (a b x y : List Wire)
    (hn1 : (q::c::u::k::(a++b)).Nodup) (hn2 : (q::c::u::k::(x++y)).Nodup)
    (hsep : List.Disjoint b (x++y)) (hl1 : a.length=b.length) (hl2 : x.length=y.length)
    (hw1 : 0<b.length) (hw2 : 0<y.length) (s : State) (m : List Bool)
    (hu : s.basis u=false) (hk : s.basis k=false)
    (hlo1 : -((2^(b.length-1):Nat):Int) ≤
      branchInt (s.basis q) (s.basis c) (signedRegValue a s.basis) (signedRegValue b s.basis))
    (hhi1 : branchInt (s.basis q) (s.basis c) (signedRegValue a s.basis)
      (signedRegValue b s.basis)<((2^(b.length-1):Nat):Int))
    (hlo2 : -((2^(y.length-1):Nat):Int) ≤
      branchInt (s.basis q) (s.basis c) (signedRegValue x s.basis) (signedRegValue y s.basis))
    (hhi2 : branchInt (s.basis q) (s.basis c) (signedRegValue x s.basis)
      (signedRegValue y s.basis)<((2^(y.length-1):Nat):Int)) :
    let t := run (branchPair q c u k a b x y) m s
    t.phase=s.phase ∧ (∀ w,w∉b++y → t.basis w=s.basis w) ∧
      signedRegValue b t.basis=branchInt (s.basis q) (s.basis c)
        (signedRegValue a s.basis) (signedRegValue b s.basis) ∧
      signedRegValue y t.basis=branchInt (s.basis q) (s.basis c)
        (signedRegValue x s.basis) (signedRegValue y s.basis) := by
  let v := run (branchRow q c u k a b) m s
  have hv := branchRow_signed q c u k a b hn1 hl1 hw1 s m hu hk hlo1 hhi1
  have hctrl (w : Wire) (hw : w∈[q,c,u,k]) : w∉b := by
    intro hb
    have count := List.nodup_iff_count.mp hn1 w
    have hc := List.count_pos_iff.mpr hw
    have hbc := List.count_pos_iff.mpr hb
    simp only [List.count_cons,List.count_append,List.count_nil] at count hc
    omega
  have vq : v.basis q=s.basis q := hv.2.1 q (hctrl q (by simp))
  have vc : v.basis c=s.basis c := hv.2.1 c (hctrl c (by simp))
  have vu : v.basis u=false := (hv.2.1 u (hctrl u (by simp))).trans hu
  have vk : v.basis k=false := (hv.2.1 k (hctrl k (by simp))).trans hk
  have keep (w : Wire) (hw : w∈x++y) : v.basis w=s.basis w :=
    hv.2.1 w (fun hb => List.disjoint_left.mp hsep hb hw)
  have vx : signedRegValue x v.basis=signedRegValue x s.basis :=
    signed_frame x _ _ (fun w hw => keep w (List.mem_append_left _ hw))
  have vy : signedRegValue y v.basis=signedRegValue y s.basis :=
    signed_frame y _ _ (fun w hw => keep w (List.mem_append_right _ hw))
  have hlov : -((2^(y.length-1):Nat):Int) ≤
      branchInt (v.basis q) (v.basis c) (signedRegValue x v.basis) (signedRegValue y v.basis) := by
    rwa [vq,vc,vx,vy]
  have hhiv : branchInt (v.basis q) (v.basis c) (signedRegValue x v.basis)
      (signedRegValue y v.basis)<((2^(y.length-1):Nat):Int) := by rwa [vq,vc,vx,vy]
  have ht := branchRow_signed q c u k x y hn2 hl2 hw2 v
    (m.drop (measurementCount (branchRow q c u k a b))) vu vk hlov hhiv
  simp only [branchPair,run_append,run_take]
  refine ⟨ht.1.trans hv.1,?_,?_,?_⟩
  · intro w hw
    have hb : w∉b := fun h => hw (List.mem_append_left _ h)
    have hy : w∉y := fun h => hw (List.mem_append_right _ h)
    exact (ht.2.1 w hy).trans (hv.2.1 w hb)
  · exact (signed_frame b _ _ (fun w hw => ht.2.1 w
      (fun hy => List.disjoint_left.mp hsep hw (List.mem_append_right _ hy)))).trans hv.2.2
  · simpa only [vq,vc,vx,vy] using ht.2.2

theorem branchPair_counts (q c u k : Wire) (a b x y : List Wire)
    (hl1 : a.length=b.length) (hl2 : x.length=y.length) :
    toffoliCount (branchPair q c u k a b x y)=
      (1+(3*b.length-2))+(1+(3*y.length-2)) ∧
      measurementCount (branchPair q c u k a b x y)=2 := by
  simp [branchPair,toffoliCount_append,measurementCount_append,
    branchRow_counts q c u k a b hl1,branchRow_counts q c u k x y hl2]

theorem branchPair_in_arena (q c u k : Wire) (a b x y : List Wire)
    (h1 : (q::c::u::k::(a++b)).toFinset⊆arenaWires)
    (h2 : (q::c::u::k::(x++y)).toFinset⊆arenaWires) :
    wires (branchPair q c u k a b x y)⊆arenaWires := by
  rw [branchPair,wires_append]
  exact Finset.union_subset ((branchRow_support q c u k a b).trans h1)
    ((branchRow_support q c u k x y).trans h2)

/-- Algebraic connection of the routed F4 integer row to the actual divstep
numerator. The physical shift by two is a separate following stage. -/
theorem branchInt_divstep_g (st : ECDSAAdd.Divsteps.ZState) (hf : st.f%2=1) :
    branchInt (decide (0≤st.z ∧ st.g%2=1))
      (decide (ECDSAAdd.Divsteps.bbit st=1))
      (if 0≤st.z ∧ st.g%2=1 then st.g else st.f)
      (if 0≤st.z ∧ st.g%2=1 then st.f else st.g) =
      2*(ECDSAAdd.Divsteps.zStep st).g := by
  have hg0 : 0≤st.g%2 := Int.emod_nonneg _ (by omega)
  have hg2 : st.g%2<2 := Int.emod_lt_of_pos _ (by omega)
  by_cases h : 0≤st.z ∧ st.g%2=1
  · rw [show decide (0≤st.z ∧ st.g%2=1)=true from decide_eq_true h]
    simp only [ECDSAAdd.Divsteps.bbit,ECDSAAdd.Divsteps.zStep,if_pos h,hf,
      decide_true,branchInt,if_true]
    have he : (st.g-st.f)%2=0 := by rw [Int.sub_emod,h.2,hf]; decide
    have hd := Int.mul_ediv_add_emod (st.g-st.f) 2
    omega
  · rw [show decide (0≤st.z ∧ st.g%2=1)=false from decide_eq_false h]
    simp only [ECDSAAdd.Divsteps.bbit,ECDSAAdd.Divsteps.zStep,if_neg h,
      branchInt,Bool.false_eq_true,if_false]
    by_cases hg : st.g%2=1
    · simp only [hg,decide_true,if_true,one_mul]
      have he : (st.g+st.f)%2=0 := by rw [Int.add_emod,hg,hf]; decide
      have hd := Int.mul_ediv_add_emod (st.g+st.f) 2
      omega
    · have hg : st.g%2=0 := by omega
      simp [hg]
      have hd := Int.mul_ediv_add_emod st.g 2
      omega

theorem branchInt_divstep_gv (st : ECDSAAdd.Divsteps.ZState) (hf : st.f%2=1) :
    branchInt (decide (0≤st.z ∧ st.g%2=1))
      (decide (ECDSAAdd.Divsteps.bbit st=1))
      (if 0≤st.z ∧ st.g%2=1 then st.gv else st.fv)
      (if 0≤st.z ∧ st.g%2=1 then st.fv else st.gv) =
      (ECDSAAdd.Divsteps.zStep st).gv := by
  have hg0 : 0≤st.g%2 := Int.emod_nonneg _ (by omega)
  have hg2 : st.g%2<2 := Int.emod_lt_of_pos _ (by omega)
  by_cases h : 0≤st.z ∧ st.g%2=1
  · rw [show decide (0≤st.z ∧ st.g%2=1)=true from decide_eq_true h]
    simp only [ECDSAAdd.Divsteps.bbit,ECDSAAdd.Divsteps.zStep,if_pos h,hf,
      decide_true,branchInt,if_true]
  · rw [show decide (0≤st.z ∧ st.g%2=1)=false from decide_eq_false h]
    simp only [ECDSAAdd.Divsteps.bbit,ECDSAAdd.Divsteps.zStep,if_neg h,
      branchInt,Bool.false_eq_true,if_false]
    by_cases hg : st.g%2=1
    · simp [hg]
    · have hg : st.g%2=0 := by omega
      simp [hg]

/-- Actual two-row F4 gates produce the next integer g numerator and gv.
Routing/control generation, g halving, fv doubling and z update are separate
stages; the hypotheses expose exactly their boundary. -/
theorem branchPair_divstep (q c u k : Wire) (a b x y : List Wire)
    (hn1 : (q::c::u::k::(a++b)).Nodup) (hn2 : (q::c::u::k::(x++y)).Nodup)
    (hsep : List.Disjoint b (x++y)) (hl1 : a.length=b.length) (hl2 : x.length=y.length)
    (hw1 : 0<b.length) (hw2 : 0<y.length) (st : ECDSAAdd.Divsteps.ZState)
    (hf : st.f%2=1) (s : State) (m : List Bool) (hu : s.basis u=false) (hk : s.basis k=false)
    (hq : s.basis q=decide (0≤st.z ∧ st.g%2=1))
    (hc : s.basis c=decide (ECDSAAdd.Divsteps.bbit st=1))
    (ha : signedRegValue a s.basis=if 0≤st.z ∧ st.g%2=1 then st.g else st.f)
    (hb : signedRegValue b s.basis=if 0≤st.z ∧ st.g%2=1 then st.f else st.g)
    (hx : signedRegValue x s.basis=if 0≤st.z ∧ st.g%2=1 then st.gv else st.fv)
    (hy : signedRegValue y s.basis=if 0≤st.z ∧ st.g%2=1 then st.fv else st.gv)
    (hlo1 : -((2^(b.length-1):Nat):Int)≤2*(ECDSAAdd.Divsteps.zStep st).g)
    (hhi1 : 2*(ECDSAAdd.Divsteps.zStep st).g<((2^(b.length-1):Nat):Int))
    (hlo2 : -((2^(y.length-1):Nat):Int)≤(ECDSAAdd.Divsteps.zStep st).gv)
    (hhi2 : (ECDSAAdd.Divsteps.zStep st).gv<((2^(y.length-1):Nat):Int)) :
    let t := run (branchPair q c u k a b x y) m s
    t.phase=s.phase ∧ (∀ w,w∉b++y → t.basis w=s.basis w) ∧
      signedRegValue b t.basis=2*(ECDSAAdd.Divsteps.zStep st).g ∧
      signedRegValue y t.basis=(ECDSAAdd.Divsteps.zStep st).gv := by
  have h1 : branchInt (s.basis q) (s.basis c) (signedRegValue a s.basis)
      (signedRegValue b s.basis)=2*(ECDSAAdd.Divsteps.zStep st).g := by
    rw [hq,hc,ha,hb]
    exact branchInt_divstep_g st hf
  have h2 : branchInt (s.basis q) (s.basis c) (signedRegValue x s.basis)
      (signedRegValue y s.basis)=(ECDSAAdd.Divsteps.zStep st).gv := by
    rw [hq,hc,hx,hy]
    exact branchInt_divstep_gv st hf
  have ht := branchPair_signed q c u k a b x y hn1 hn2 hsep hl1 hl2 hw1 hw2 s m hu hk
    (by rwa [h1]) (by rwa [h1]) (by rwa [h2]) (by rwa [h2])
  exact ⟨ht.1,ht.2.1,ht.2.2.1.trans h1,ht.2.2.2.trans h2⟩

end ECDSAAdd.Arithmetic.Paper935
