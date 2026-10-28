import ECDSAAdd.Arithmetic.MeasuredSourceNormalize

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def measuredFoldNormalize (K : MeasuredCanonicalModLayout) (flag : Wire) : MeasuredSourceNormalizeLayout :=
  {word:=K.src,carry:=K.carry.take (K.src.length-1),cin:=K.cin,flag:=flag}

def measuredFoldKernel (K : MeasuredCanonicalModLayout) (flag : Wire)
    (canonical : Bool) (c p : Nat) : Program :=
  (if canonical then [] else (measuredFoldNormalize K flag).normalize p c)++
    K.program c p++
    (if canonical then [] else (measuredFoldNormalize K flag).restore p)

/-- The reusable fold kernel accepts any n-bit source, normalizes it when
needed, adds it to the canonical output, and restores the raw source and all
workspace. Its exact guarantee includes every measurement record. -/
theorem measuredFoldKernel_correct (K : MeasuredCanonicalModLayout) (flag : Wire)
    (n c p : Nat) (hw : K.Widths n) (hn : (flag::K.wires).Nodup)
    (npos : 0<n) (hpc : p+c=2^n) (hcpos : 0<c) (hcp : c<p)
    (canonical : Bool) (S O : Nat) (hcanonical : canonical=true → S<p) (hO : O<p)
    (s : State) (records : List Bool) (hs : regValue K.src s.basis=S)
    (ho : regValue K.out s.basis=O) (hf : s.basis flag=false)
    (hhigh : s.basis K.high=false) (hmod : s.basis K.flag=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) (hcin : s.basis K.cin=false) :
    (run (measuredFoldKernel K flag canonical c p) records s).phase=s.phase ∧
    regValue K.out (run (measuredFoldKernel K flag canonical c p) records s).basis=(S+O)%p ∧
    ∀q,q∉K.out → (run (measuredFoldKernel K flag canonical c p) records s).basis q=s.basis q := by
  let N := measuredFoldNormalize K flag
  let preProg := if canonical then [] else N.normalize p c
  let postProg := if canonical then [] else N.restore p
  let rest := records.drop (measurementCount preProg)
  let u := run preProg (records.take (measurementCount preProg)) s
  let v := run (K.program c p) (rest.take (measurementCount (K.program c p))) u
  let out := run postProg (rest.drop (measurementCount (K.program c p))) v
  let A := if canonical then S else S%p
  let D := if canonical then false else decide (p≤S)
  have coreNd : K.wires.Nodup := (List.nodup_cons.mp hn).2
  have nd : N.wires.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := (List.take_sublist (K.src.length-1) K.carry).count_le q
    simp only [N,measuredFoldNormalize,MeasuredSourceNormalizeLayout.wires,
      MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have length : N.carry.length+1=N.word.length := by
    simp [N,measuredFoldNormalize,hw.src,hw.carry]
    omega
  have modulus : p+c=2^N.word.length := by simpa [N,measuredFoldNormalize,hw.src] using hpc
  have bound : S<2^N.word.length := by
    simpa only [N,measuredFoldNormalize,hs] using regValue_lt K.src s.basis
  have nclean : ∀q∈N.carry,s.basis q=false := by
    intro q hq
    exact hcarry q (List.mem_of_mem_take hq)
  have protect (q : Wire) (hq : q∈K.out++K.carry++[K.high,K.cin,K.flag]) : q∉N.mutable := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [N,measuredFoldNormalize,MeasuredSourceNormalizeLayout.mutable,
      MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a b
    omega
  have srcAway (q : Wire) (hq : q∈K.src) : q∉K.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
    omega
  have flagAway : flag∉K.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [MeasuredCanonicalModLayout.wires,bad])
  have before : u.phase=s.phase ∧ regValue K.src u.basis=A ∧ u.basis flag=D ∧
      ∀q,q∉N.mutable → u.basis q=s.basis q := by
    cases h : canonical
    · have init : N.Frame s.basis S false s.basis := ⟨hs,hf,fun _ _ => rfl⟩
      have result := N.normalize_frame nd length p c S modulus hcpos hcp bound s.basis nclean hcin
        s (records.take (measurementCount preProg)) init
      simpa only [u,preProg,h,if_false,A,D] using result
    · simp [u,preProg,h,A,D,run,hs,hf]
  have aBound : A<p := by
    cases h : canonical
    · simpa [A,h] using Nat.mod_lt S (show 0<p by omega)
    · simpa [A,h] using hcanonical h
  have carryU : ∀q∈K.carry,u.basis q=false := by
    intro q hq
    exact (before.2.2.2 q (protect q (by simp [hq]))).trans (hcarry q hq)
  have cinU : u.basis K.cin=false :=
    (before.2.2.2 K.cin (protect K.cin (by simp))).trans hcin
  have highU : u.basis K.high=false :=
    (before.2.2.2 K.high (protect K.high (by simp))).trans hhigh
  have modU : u.basis K.flag=false :=
    (before.2.2.2 K.flag (protect K.flag (by simp))).trans hmod
  have outU : regValue K.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => before.2.2.2 q (protect q (by simp [hq])))).trans ho
  have core := K.program_correct n c p hw coreNd npos hpc hcpos A O aBound hO
    u (rest.take (measurementCount (K.program c p))) before.2.1 outU highU modU carryU cinU
  have srcV : regValue K.src v.basis=A :=
    (regValue_congr _ _ _ (fun q hq => core.2.2 q (srcAway q hq))).trans before.2.1
  have flagV : v.basis flag=D := (core.2.2 flag flagAway).trans before.2.2.1
  have carryV : ∀q∈N.carry,v.basis q=false := by
    intro q hq
    have inCarry : q∈K.carry := List.mem_of_mem_take hq
    have notOut : q∉K.out := by
      intro bad
      have h := List.nodup_iff_count.mp hn q
      have a := List.count_pos_iff.mpr inCarry
      have b := List.count_pos_iff.mpr bad
      simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
      omega
    exact (core.2.2 q notOut).trans (carryU q inCarry)
  have cinAway : K.cin∉K.out := (K.flags_away coreNd).2.2.1 ∘ List.mem_append_left _
  have cinV : v.basis K.cin=false := (core.2.2 K.cin cinAway).trans cinU
  have after : out.phase=v.phase ∧ regValue K.src out.basis=S ∧ out.basis flag=false ∧
      ∀q,q∉N.mutable → out.basis q=v.basis q := by
    cases h : canonical
    · have init : N.Frame v.basis (S%p) (decide (p≤S)) v.basis := by
        exact ⟨by simpa [A,h] using srcV,by simpa [D,h] using flagV,fun _ _ => rfl⟩
      have result := N.restore_frame nd length p c S modulus hcpos hcp bound v.basis carryV cinV
        v (rest.drop (measurementCount (K.program c p))) init
      simpa only [out,postProg,h,if_false] using result
    · simpa only [out,postProg,h,if_true,run] using
        (show v.phase=v.phase ∧ regValue K.src v.basis=S ∧ v.basis flag=false ∧
          ∀q,q∉N.mutable → v.basis q=v.basis q from
          ⟨rfl,by simpa [A,h] using srcV,by simpa [D,h] using flagV,fun _ _ => rfl⟩)
  have finalValue : regValue K.out out.basis=(S+O)%p := by
    have value := (regValue_congr _ _ _ (fun q hq => after.2.2.2 q (protect q (by simp [hq])))).trans core.2.1
    have eq : (A+O)%p=(S+O)%p := by
      cases h : canonical
      · simp [A,h,Nat.add_mod]
      · simp [A,h]
    exact value.trans eq
  have final : out.phase=s.phase ∧ regValue K.out out.basis=(S+O)%p ∧
      ∀q,q∉K.out → out.basis q=s.basis q := by
    refine ⟨after.1.trans (core.1.trans before.1),finalValue,?_⟩
    intro q hq
    by_cases src : q∈K.src
    · exact (regValue_eq_iff K.src out.basis s.basis).mp (after.2.1.trans hs.symm) q src
    by_cases fl : q=flag
    · subst q; exact after.2.2.1.trans hf.symm
    have notMutable : q∉N.mutable := by
      simpa only [N,measuredFoldNormalize,MeasuredSourceNormalizeLayout.mutable,List.mem_append,
        List.mem_cons,List.not_mem_nil,or_false,not_or] using And.intro src fl
    exact (after.2.2.2 q notMutable).trans ((core.2.2 q hq).trans (before.2.2.2 q notMutable))
  simpa [measuredFoldKernel,N,preProg,postProg,rest,u,v,out,run_append] using final

end ECDSAAdd.Arithmetic
