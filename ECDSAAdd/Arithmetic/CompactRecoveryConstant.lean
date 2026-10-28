import ECDSAAdd.Arithmetic.MeasuredCanonicalModProof
import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Arithmetic.MaskedConstant

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def compactRecoveryConstant (K : MeasuredCanonicalModLayout) (control : Wire) (c p k : Nat) : Program :=
  maskedConstant control K.src k++K.program c p++maskedConstant control K.src k

theorem compactRecoveryConstant_correct (K : MeasuredCanonicalModLayout) (control : Wire)
    (n c p k : Nat) (hw : K.Widths n) (hn : (control::K.wires).Nodup)
    (npos : 0<n) (hpc : p+c=2^n) (hcpos : 0<c) (hk : k<p)
    (X : Nat) (hX : X<p) (s : State) (records : List Bool)
    (hs : regValue K.src s.basis=0) (hx : regValue K.out s.basis=X)
    (hh : s.basis K.high=false) (hf : s.basis K.flag=false)
    (hc : ∀q∈K.carry,s.basis q=false) (hi : s.basis K.cin=false) :
    (run (compactRecoveryConstant K control c p k) records s).phase=s.phase ∧
    regValue K.out (run (compactRecoveryConstant K control c p k) records s).basis=
      (X+(if s.basis control then k else 0))%p ∧
    ∀q,q∉K.out → (run (compactRecoveryConstant K control c p k) records s).basis q=s.basis q := by
  let load := maskedConstant control K.src k
  let u := run load [] s
  let v := run (K.program c p) (records.take (measurementCount (K.program c p))) u
  let out := run load (records.drop (measurementCount (K.program c p))) v
  let A := if s.basis control then k else 0
  have coreNd := (List.nodup_cons.mp hn).2
  have srcNd : K.src.Nodup := by
    apply List.nodup_iff_count.mpr;intro q;have h := List.nodup_iff_count.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
    omega
  have ctrlSrc : control∉K.src := by
    intro bad;exact (List.nodup_cons.mp hn).1 (by simp [MeasuredCanonicalModLayout.wires,bad])
  have protect (q : Wire) (hq : q∈control::K.out++K.carry++[K.high,K.cin,K.flag]) : q∉K.src := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have notOut (q : Wire) (hq : q∈control::K.src++K.carry++[K.high,K.cin,K.flag]) : q∉K.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have kb : k<2^K.src.length := by rw [hw.src];omega
  have loaded := maskedConstant_correct control K.src k srcNd ctrlSrc kb s []
  have srcU : regValue K.src u.basis=A := by simpa [hs,A] using loaded.2.2
  have ctrlU : u.basis control=s.basis control := loaded.2.1 control ctrlSrc
  have outU : regValue K.out u.basis=X :=
    (regValue_congr _ _ _ (fun q hq => loaded.2.1 q (protect q (by simp [hq])))).trans hx
  have highU : u.basis K.high=false := (loaded.2.1 K.high (protect K.high (by simp))).trans hh
  have flagU : u.basis K.flag=false := (loaded.2.1 K.flag (protect K.flag (by simp))).trans hf
  have cinU : u.basis K.cin=false := (loaded.2.1 K.cin (protect K.cin (by simp))).trans hi
  have carryU : ∀q∈K.carry,u.basis q=false := by
    intro q hq;exact (loaded.2.1 q (protect q (by simp [hq]))).trans (hc q hq)
  have ab : A<p := by dsimp [A];split;exact hk;omega
  have core := K.program_correct n c p hw coreNd npos hpc hcpos A X ab hX u
    (records.take (measurementCount (K.program c p))) srcU outU highU flagU carryU cinU
  have srcV : regValue K.src v.basis=A :=
    (regValue_congr _ _ _ (fun q hq => core.2.2 q (notOut q (by simp [hq])))).trans srcU
  have ctrlV : v.basis control=s.basis control := (core.2.2 control (notOut control (by simp))).trans ctrlU
  have unloaded := maskedConstant_correct control K.src k srcNd ctrlSrc kb v
    (records.drop (measurementCount (K.program c p)))
  have srcOut : regValue K.src out.basis=0 := by
    simpa [srcV,ctrlV,A] using unloaded.2.2
  have value : regValue K.out out.basis=(X+A)%p := by
    have h := (regValue_congr _ _ _ (fun q hq => unloaded.2.1 q (protect q (by simp [hq])))).trans core.2.1
    simpa [Nat.add_comm] using h
  have final : out.phase=s.phase ∧ regValue K.out out.basis=(X+A)%p ∧
      ∀q,q∉K.out → out.basis q=s.basis q := by
    refine ⟨unloaded.1.trans (core.1.trans loaded.1),value,?_⟩
    intro q hq
    by_cases source : q∈K.src
    · exact ((regValue_zero _ _).mp srcOut q source).trans ((regValue_zero _ _).mp hs q source).symm
    · exact (unloaded.2.1 q source).trans ((core.2.2 q hq).trans (loaded.2.1 q source))
  have lm := (maskedConstant_counts control K.src k).2
  simpa [compactRecoveryConstant,load,u,v,out,A,run_append,lm] using final

theorem compactRecoveryConstant_counts (K : MeasuredCanonicalModLayout) (control : Wire)
    (n c p k : Nat) (hw : K.Widths n) (npos : 0<n) :
    toffoliCount (compactRecoveryConstant K control c p k)=4*n-1 ∧
    measurementCount (compactRecoveryConstant K control c p k)=4*n-1 := by
  have h := K.program_counts n c p hw npos
  have mask := maskedConstant_counts control K.src k
  simp [compactRecoveryConstant,h.1,h.2,mask.1,mask.2]

theorem compactRecoveryConstant_support (K : MeasuredCanonicalModLayout) (control : Wire) (c p k : Nat) :
    wires (compactRecoveryConstant K control c p k)⊆(control::K.wires).toFinset := by
  have mask := maskedConstant_wires_subset control K.src k
  have core := K.program_wires_subset c p
  have e1 : (control::K.src).toFinset⊆(control::K.wires).toFinset := by
    intro q hq;simp [MeasuredCanonicalModLayout.wires] at hq ⊢;tauto
  have e2 : K.wires.toFinset⊆(control::K.wires).toFinset := by intro q hq;simp [hq]
  have a := mask.trans e1
  have b := core.trans e2
  simpa only [compactRecoveryConstant,wires_append,Finset.union_subset_iff] using And.intro (And.intro a b) a

end ECDSAAdd.Arithmetic
