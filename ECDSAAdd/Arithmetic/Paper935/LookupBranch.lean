import ECDSAAdd.Arithmetic.Lookup
import ECDSAAdd.Arithmetic.Divsteps.DeferredDecoder

namespace ECDSAAdd.Arithmetic.Paper935

private theorem state_eq {a b : State} (h : a.phase=b.phase) (hb : a.basis=b.basis) : a=b := by
  cases a; cases b; simp_all

private theorem single_value (w : Wire) (s : BasisState) : regValue [w] s=(s w).toNat := by
  cases h : s w <;> simp [regValue,h]

private theorem bool_nat_inj {a b : Bool} (h : a.toNat=b.toNat) : a=b := by
  cases a <;> cases b <;> simp_all

/-- A finite ten-bit residue decoder with an enable control. Both lookups
are the same measured program; their clean scratch and phase are restored. -/
def lookupBranch (flag address tmp output : Wire) (controls scratch : List Wire)
    (table : Nat → Bool) : Program :=
  lookup address controls scratch [tmp] (fun d => (table d).toNat) ++
    ([.CCX flag tmp output] ++ lookup address controls scratch [tmp] (fun d => (table d).toNat))

theorem lookupBranch_run (flag address tmp output : Wire) (controls scratch : List Wire)
    (table : Nat → Bool) (hn : (flag::output::address::(controls++scratch++[tmp])).Nodup)
    (hc : controls.length=9) (hs : scratch.length=9)
    (s : State) (m : List Bool) (ht : s.basis tmp=false)
    (hz : ∀ w∈scratch,s.basis w=false) :
    run (lookupBranch flag address tmp output controls scratch table) m s=
      ⟨s.phase,writeBit s.basis output
        (s.basis output ^^ (s.basis flag && table (regValue (address::controls) s.basis)))⟩ := by
  have hnf := (List.nodup_cons.mp hn).1
  have hno := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  have hna := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2
  have offt : output≠tmp := fun he => hno (by simp [he])
  have fft : flag≠tmp := fun he => hnf (by simp [he])
  let P := lookup address controls scratch [tmp] (fun d => (table d).toNat)
  let t := run P m s
  have hb : ∀ d<1024,(table d).toNat<2^([tmp]:List Wire).length := by
    intro d _; cases table d <;> simp
  have h1 := lookup10_correct address controls scratch [tmp] (fun d => (table d).toNat) hna hc hs hb s m hz
  have tbit : t.basis tmp=table (regValue (address::controls) s.basis) := by
    apply bool_nat_inj
    have h := h1.2.2
    rw [single_value,single_value,ht] at h
    simpa only [Bool.toNat_false,Nat.zero_xor] using h
  have ta : t.basis flag=s.basis flag := h1.2.1 flag (by simpa using fft)
  have tout : t.basis output=s.basis output := h1.2.1 output (by simpa using offt)
  let val := s.basis output ^^ (s.basis flag && table (regValue (address::controls) s.basis))
  let u : State := ⟨t.phase,writeBit t.basis output val⟩
  have ukeep (w : Wire) (hw : w≠output) : u.basis w=t.basis w := Function.update_of_ne hw _ _
  have outAway (w : Wire) (hw : w∈address::(controls++scratch++[tmp])) : w≠output :=
    fun he => hno (he ▸ hw)
  have utmp : u.basis tmp=table (regValue (address::controls) s.basis) :=
    (ukeep tmp (Ne.symm offt)).trans tbit
  have uwork : ∀ w∈scratch,u.basis w=false := by
    intro w hw
    have hwt : w≠tmp := by
      intro he
      have hdis := (List.nodup_append'.mp (List.nodup_cons.mp hna).2).2.2
      exact List.disjoint_left.mp hdis (List.mem_append_right controls hw) (by simp [he])
    exact (ukeep w (outAway w (by simp [hw]))).trans ((h1.2.1 w (by simpa using hwt)).trans (hz w hw))
  have uaddr : regValue (address::controls) u.basis=regValue (address::controls) s.basis := by
    apply regValue_congr
    intro w hw
    have hwt : w≠tmp := by
      intro he
      have hdis := (List.nodup_append'.mp (show ((address::controls)++scratch++[tmp]).Nodup by simpa using hna)).2.2
      exact List.disjoint_left.mp hdis (List.mem_append_left _ (he ▸ hw)) (by simp)
    have hmem : w∈address::(controls++scratch++[tmp]) := by
      rcases List.mem_cons.mp hw with he | hh
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hh))
    exact (ukeep w (outAway w hmem)).trans (h1.2.1 w (by simpa using hwt))
  let ms := m.drop (measurementCount P)
  have h2 := lookup10_correct address controls scratch [tmp] (fun d => (table d).toNat) hna hc hs hb u ms uwork
  have vbit : (run P ms u).basis tmp=false := by
    apply bool_nat_inj
    have h := h2.2.2
    rw [single_value,single_value,uaddr,utmp,Nat.xor_self] at h
    exact h
  have hmid (tape : List Bool) : run [.CCX flag tmp output] tape t=u := by
    simp [run,u,val,ta,tout,tbit]
  rw [lookupBranch,run_append,run_take,run_append,run_take,hmid]
  change run P ms u=⟨s.phase,writeBit s.basis output val⟩
  have hp : (run P ms u).phase=s.phase := h2.1.trans h1.1
  apply state_eq
  · exact hp
  funext w
  by_cases hw : w=tmp
  · subst w; simpa [writeBit,Ne.symm offt,ht] using vbit
  · have hkeep := h2.2.1 w (by simpa using hw)
    by_cases ho : w=output
    · subst w; simpa [u,writeBit] using hkeep
    · change (run P ms u).basis w=writeBit s.basis output val w
      rw [show writeBit s.basis output val w=s.basis w from Function.update_of_ne ho _ _]
      exact hkeep.trans ((ukeep w ho).trans (h1.2.1 w (by simpa using hw)))


theorem lookupBranch_counts (flag address tmp output : Wire) (controls scratch : List Wire)
    (table : Nat → Bool) (hc : controls.length=9) (hs : scratch.length=9) :
    toffoliCount (lookupBranch flag address tmp output controls scratch table)=2045 ∧
    measurementCount (lookupBranch flag address tmp output controls scratch table)=2044 := by
  have h := lookup10_counts address controls scratch [tmp] (fun d => (table d).toNat) hc hs
  simp [lookupBranch,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,h.1,h.2]

theorem lookupBranch_support (flag address tmp output : Wire) (controls scratch : List Wire)
    (table : Nat → Bool) :
    wires (lookupBranch flag address tmp output controls scratch table) ⊆
      (flag::output::address::(controls++scratch++[tmp])).toFinset := by
  have h := lookup_wires_subset address controls scratch [tmp] (fun d => (table d).toNat)
  intro w hw
  simp only [lookupBranch,wires_append,wires,Instr.wires,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hw
  rcases hw with hw | hw | hw
  · have hh := h hw
    simp only [List.mem_toFinset,List.cons_append,List.mem_cons,List.mem_append] at hh ⊢
    tauto
  · simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  · have hh := h hw
    simp only [List.mem_toFinset,List.cons_append,List.mem_cons,List.mem_append] at hh ⊢
    tauto

theorem lookupBranch_wireBound (flag address tmp output : Wire) (controls scratch : List Wire)
    (table : Nat → Bool) (hc : controls.length=9) (hs : scratch.length=9) :
    (wires (lookupBranch flag address tmp output controls scratch table)).card≤22 := by
  have h := Finset.card_le_card (lookupBranch_support flag address tmp output controls scratch table)
  have hl := List.toFinset_card_le (flag::output::address::(controls++scratch++[tmp]))
  simp only [List.length_cons,List.length_append,List.length_nil,hc,hs] at hl
  omega

theorem lookupBranch_recover (flag address tmp output : Wire) (controls scratch : List Wire)
    (table : Nat → Bool) (hn : (flag::output::address::(controls++scratch++[tmp])).Nodup)
    (hc : controls.length=9) (hs : scratch.length=9)
    (s : State) (m : List Bool) (ht : s.basis tmp=false)
    (hz : ∀ w∈scratch,s.basis w=false) (henable : s.basis flag=true)
    (hout : s.basis output=false) (ordinal cursor : Nat) (phase : Bool)
    (hphase : s.phase=(phase ^^ (m.getD ordinal false && table (regValue (address::controls) s.basis)))) :
    runWithTape (ECDSAAdd.Arithmetic.Divsteps.recoverBranch
      (lookupBranch flag address tmp output controls scratch table) output ordinal) m cursor s=
      ⟨phase,writeBit s.basis output (table (regValue (address::controls) s.basis))⟩ := by
  apply ECDSAAdd.Arithmetic.Divsteps.recoverBranch_cancel _ _ _ _ _ _ _ _ hphase
  rw [lookupBranch_run flag address tmp output controls scratch table hn hc hs s (m.drop cursor) ht hz,
    henable,hout]
  simp

end ECDSAAdd.Arithmetic.Paper935
