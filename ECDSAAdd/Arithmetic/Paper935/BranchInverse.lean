import ECDSAAdd.Arithmetic.Paper935.BranchRow
import ECDSAAdd.Arithmetic.Paper935.RowInverse

namespace ECDSAAdd.Arithmetic.Paper935

private theorem state_eq {s t : State} (hp : s.phase=t.phase) (hb : s.basis=t.basis) : s=t := by
  cases s; cases t; simp_all

private theorem remint_and (q c u : Wire) (hq : q≠u) (hc : c≠u)
    (s : State) (m n : List Bool) (h : s.basis u=(s.basis q && s.basis c)) :
    run [.CCX q c u] n (run (eraseAnd q c u) m s)=s := by
  rw [eraseAnd_run q c u hq hc s m h]
  apply state_eq
  · rfl
  · funext w
    by_cases hw : w=u
    · subst w; simp [run,writeBit,hq,hc,h]
    · simp [run,writeBit,hw]

/-- Reverse only the proper core; remint the retired AND and perform a fresh
measurement with its own correction. This is valid for unrelated tapes. -/
theorem measuredAnd_roundtrip (q c u : Wire) (hq : q≠u) (hc : c≠u)
    (core : Program) (hcore : ProperProgram core) (s : State) (m n : List Bool)
    (hz : s.basis u=false)
    (hkeep : let t := run core m (run [.CCX q c u] m s)
      t.basis u=(t.basis q && t.basis c)) :
    run ([.CCX q c u]++core.reverse++eraseAnd q c u) n
      (run ([.CCX q c u]++core++eraseAnd q c u) m s)=s := by
  have hm := properProgram_measurementCount core hcore
  have hmr : measurementCount core.reverse=0 := by rw [measurementCount_reverse,hm]
  simp only [run_append,run_take]
  simp only [measurementCount_append,measurementCount,hm,hmr,
    Nat.zero_add,List.drop_zero]
  rw [remint_and q c u hq hc _ m n hkeep]
  rw [run_reverse_proper core hcore (run [.CCX q c u] m s) m n]
  have hmint : (run [.CCX q c u] m s).basis u =
      ((run [.CCX q c u] m s).basis q && (run [.CCX q c u] m s).basis c) := by
    simp [run,writeBit,hq,hc,hz]
  rw [eraseAnd_run q c u hq hc _ n hmint]
  apply state_eq
  · rfl
  · funext w
    by_cases hw : w=u
    · subst w; simp [writeBit,hz]
    · simp [run,writeBit,hw]

def branchCore (c u k : Wire) (a b : List Wire) : Program :=
  signComplement u b ++ rowAddCin c u k a b

theorem branchCore_proper (c u k : Wire) (a b : List Wire)
    (hn : (c::u::k::(a++b)).Nodup) : ProperProgram (branchCore c u k a b) := by
  have nd := hn
  simp only [List.nodup_cons,List.mem_cons,not_or] at nd
  have huk : u≠k := nd.2.1.1
  have hub : u∉b := fun h => nd.2.1.2 (List.mem_append_right _ h)
  have hadd : (c::k::(a++b)).Nodup := by
    simp only [List.nodup_cons,List.mem_cons,not_or]
    exact ⟨⟨nd.1.2.1,nd.1.2.2⟩,nd.2.2⟩
  rw [branchCore,properProgram_append]
  constructor
  · intro i hi
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
    exact fun he => hub (he ▸ hw)
  · simp only [rowAddCin,properProgram_append]
    exact ⟨⟨by simpa [ProperProgram,ProperGate] using huk,
      rowAdd_proper c k a b hadd⟩,by simpa [ProperProgram,ProperGate] using huk⟩

theorem branchCore_frame (c u k : Wire) (a b : List Wire)
    (hn : (c::u::k::(a++b)).Nodup) (hl : a.length=b.length)
    (s : State) (m : List Bool) (hk : s.basis k=false) :
    ∀ w,w∉b → (run (branchCore c u k a b) m s).basis w=s.basis w := by
  have nd := hn
  simp only [List.nodup_cons,List.mem_cons,not_or] at nd
  have huk : u≠k := nd.2.1.1
  have hub : u∉b := fun h => nd.2.1.2 (List.mem_append_right _ h)
  have hkb : k∉b := fun h => nd.2.2.1 (List.mem_append_right _ h)
  have hka : k∉a := fun h => nd.2.2.1 (List.mem_append_left _ h)
  have hbn := (List.nodup_append.mp nd.2.2.2).2.1
  have hadd : (c::k::(a++b)).Nodup := by
    simp only [List.nodup_cons,List.mem_cons,not_or]
    exact ⟨⟨nd.1.2.1,nd.1.2.2⟩,nd.2.2⟩
  let t := run (signComplement u b) m s
  have ht := signComplement_correct u b hbn hub s m
  have ha := rowAddCin_run c u k a b hadd hl huk nd.1.2.1 hub hka t m
    ((ht.2.1 k hkb).trans hk)
  rw [branchCore,run_append,run_take,(signComplement_counts u b).2,List.drop_zero]
  intro w hw
  exact (ha.2.1 w hw).trans (ht.2.1 w hw)

def branchRowInverse (q c u k : Wire) (a b : List Wire) : Program :=
  [.CCX q c u] ++ (branchCore c u k a b).reverse ++ eraseAnd q c u

theorem branchRow_roundtrip (q c u k : Wire) (a b : List Wire)
    (hn : (q::c::u::k::(a++b)).Nodup) (hl : a.length=b.length)
    (s : State) (m n : List Bool) (hu : s.basis u=false) (hk : s.basis k=false) :
    run (branchRowInverse q c u k a b) n (run (branchRow q c u k a b) m s)=s := by
  have ht := (List.nodup_cons.mp hn).2
  have nd := hn
  simp only [List.nodup_cons,List.mem_cons,not_or] at nd
  have hqu : q≠u := nd.1.2.1
  have hcu : c≠u := nd.2.1.1
  have huk : u≠k := nd.2.2.1.1
  have qb : q∉b := fun h => nd.1.2.2.2 (List.mem_append_right _ h)
  have cb : c∉b := fun h => nd.2.1.2.2 (List.mem_append_right _ h)
  have ub : u∉b := fun h => nd.2.2.1.2 (List.mem_append_right _ h)
  have he : branchRow q c u k a b =
      [.CCX q c u]++branchCore c u k a b++eraseAnd q c u := by
    simp [branchRow,branchCore,List.append_assoc]
  rw [he,branchRowInverse]
  apply measuredAnd_roundtrip q c u hqu hcu _ (branchCore_proper c u k a b ht) s m n hu
  have hmintk : (run [.CCX q c u] m s).basis k=false := by
    simp [run,writeBit,Ne.symm huk,hk]
  have frame := branchCore_frame c u k a b ht hl (run [.CCX q c u] m s) m hmintk
  dsimp only
  rw [frame u ub,frame q qb,frame c cb]
  simp [run,writeBit,hqu,hcu,hu]

theorem branchRowInverse_counts (q c u k : Wire) (a b : List Wire) (hl : a.length=b.length) :
    toffoliCount (branchRowInverse q c u k a b)=3*b.length-2+1 ∧
    measurementCount (branchRowInverse q c u k a b)=1 := by
  have hc : toffoliCount (branchCore c u k a b)=3*b.length-2 := by
    simp [branchCore,rowAddCin,toffoliCount_append,(signComplement_counts u b).1,
      rowAdd_toffolis c k a b hl,toffoliCount]
  have hm : measurementCount (branchCore c u k a b)=0 := by
    simp [branchCore,rowAddCin,measurementCount_append,measurementCount,(signComplement_counts u b).2]
  simp [branchRowInverse,toffoliCount_append,measurementCount_append,
    toffoliCount_reverse,measurementCount_reverse,hc,hm,toffoliCount,measurementCount,
    eraseAnd,Nat.add_comm]

def branchPairInverse (q c u k : Wire) (a b x y : List Wire) : Program :=
  branchRowInverse q c u k x y ++ branchRowInverse q c u k a b

theorem branchPair_roundtrip (q c u k : Wire) (a b x y : List Wire)
    (hn1 : (q::c::u::k::(a++b)).Nodup)
    (hn2 : (q::c::u::k::(x++y)).Nodup)
    (hl1 : a.length=b.length) (hl2 : x.length=y.length)
    (s : State) (m n : List Bool) (hu : s.basis u=false) (hk : s.basis k=false) :
    run (branchPairInverse q c u k a b x y) n
      (run (branchPair q c u k a b x y) m s)=s := by
  have nd := hn1
  simp only [List.nodup_cons,List.mem_cons,not_or] at nd
  have ub : u∉b := fun h => nd.2.2.1.2 (List.mem_append_right _ h)
  have kb : k∉b := fun h => nd.2.2.2.1 (List.mem_append_right _ h)
  have frame := (branchRow_run q c u k a b hn1 hl1 s m hu hk).2.1
  rw [branchPair,branchPairInverse,run_append,run_take,run_append,run_take]
  rw [branchRow_roundtrip q c u k x y hn2 hl2 _ _ n
    ((frame u ub).trans hu) ((frame k kb).trans hk)]
  exact branchRow_roundtrip q c u k a b hn1 hl1 s m _ hu hk

end ECDSAAdd.Arithmetic.Paper935
