import ECDSAAdd.Arithmetic.MeasuredCopySlice

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def measuredCopiedFold (K : MeasuredCanonicalModLayout) (flag : Wire)
    (src : List Wire) (shift : Nat) (canonical : Bool) (c p : Nat) : Program :=
  copySlice src K.src shift++measuredFoldKernel K flag canonical c p++copySlice src K.src shift

/-- Complete exact fold, including source load and unload. Only the output
register changes; all copied source bits, carries, flags and phase return. -/
theorem measuredCopiedFold_correct (K : MeasuredCanonicalModLayout) (flag : Wire)
    (n c p : Nat) (hw : K.Widths n) (src : List Wire) (shift : Nat)
    (hn : (src++flag::K.wires).Nodup) (hlen : shift+src.length≤n)
    (npos : 0<n) (hpc : p+c=2^n) (hcpos : 0<c) (hcp : c<p)
    (canonical : Bool) (O : Nat) (hO : O<p)
    (s : State) (records : List Bool)
    (hcanonical : canonical=true → regValue src s.basis*2^shift<p)
    (hzero : regValue K.src s.basis=0) (ho : regValue K.out s.basis=O)
    (hf : s.basis flag=false) (hhigh : s.basis K.high=false) (hmod : s.basis K.flag=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) (hcin : s.basis K.cin=false) :
    (run (measuredCopiedFold K flag src shift canonical c p) records s).phase=s.phase ∧
    regValue K.out (run (measuredCopiedFold K flag src shift canonical c p) records s).basis=
      (regValue src s.basis*2^shift+O)%p ∧
    ∀q,q∉K.out → (run (measuredCopiedFold K flag src shift canonical c p) records s).basis q=s.basis q := by
  let dst := (K.src.drop shift).take src.length
  let cp := copySlice src K.src shift
  let kernel := measuredFoldKernel K flag canonical c p
  let S := regValue src s.basis*2^shift
  let u := run cp [] s
  let v := run kernel (records.take (measurementCount kernel)) u
  let out := run cp (records.drop (measurementCount kernel)) v
  have coreNd : (flag::K.wires).Nodup := (List.nodup_append'.mp hn).2.1
  have nd : (src++K.src).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have bound : shift+src.length≤K.src.length := by simpa [hw.src] using hlen
  have len : dst.length=src.length := by simp [dst];omega
  have dstSub (q : Wire) (hq : q∈dst) : q∈K.src :=
    List.mem_of_mem_drop (List.mem_of_mem_take hq)
  have notWork (q : Wire) (hq : q∈src++[flag]++K.out++K.carry++[K.high,K.cin,K.flag]) : q∉K.src := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have notDst (q : Wire) (hq : q∈src++[flag]++K.out++K.carry++[K.high,K.cin,K.flag]) : q∉dst :=
    fun bad => notWork q hq (dstSub q bad)
  have notOut (q : Wire) (hq : q∈src++[flag]++K.src++K.carry++[K.high,K.cin,K.flag]) : q∉K.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h a
    omega
  have copy := copySlice_zero_correct src K.src shift nd bound s [] hzero
  have first : u.phase=s.phase ∧ regValue K.src u.basis=S ∧
      ∀q,q∉dst → u.basis q=s.basis q := copy
  have cleanCarry : ∀q∈K.carry,u.basis q=false := by
    intro q hq
    exact (first.2.2 q (notDst q (by simp [hq]))).trans (hcarry q hq)
  have keep (q : Wire) (hq : q∈[flag]++K.out++[K.high,K.cin,K.flag]) : u.basis q=s.basis q :=
    first.2.2 q (notDst q (by simp only [List.mem_append] at hq ⊢; tauto))
  have outU : regValue K.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans ho
  have body := measuredFoldKernel_correct K flag n c p hw coreNd npos hpc hcpos hcp canonical S O
    hcanonical hO u (records.take (measurementCount kernel)) first.2.1 outU
    ((keep flag (by simp)).trans hf) ((keep K.high (by simp)).trans hhigh)
    ((keep K.flag (by simp)).trans hmod) cleanCarry ((keep K.cin (by simp)).trans hcin)
  have nd2 : (src++dst).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp nd q
    have ht := (List.take_sublist src.length (K.src.drop shift)).count_le q
    have hd := (List.drop_sublist shift K.src).count_le q
    simp only [List.count_append] at h ⊢
    dsimp only [dst]
    omega
  have dst0 : regValue dst s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hzero q (dstSub q hq))
  have copied := copyRegister_correct none src dst len.symm nd2 (by simp) s []
  have dstU : regValue dst u.basis=regValue src s.basis := by
    simpa [u,cp,copySlice,dst0,copyValue] using copied.2.2
  have dstV : regValue dst v.basis=regValue src s.basis :=
    (regValue_congr _ _ _ (fun q hq => body.2.2 q (notOut q (by simp [dstSub q hq])))).trans dstU
  have srcV : regValue src v.basis=regValue src s.basis := by
    apply regValue_congr
    intro q hq
    exact (body.2.2 q (notOut q (by simp [hq]))).trans (first.2.2 q (notDst q (by simp [hq])))
  have last := copyRegister_correct none src dst len.symm nd2 (by simp) v (records.drop (measurementCount kernel))
  have lastValue : regValue dst out.basis=0 := by
    simpa [out,cp,copySlice,dstV,srcV,copyValue] using last.2.2
  have finalValue : regValue K.out out.basis=(S+O)%p :=
    (regValue_congr _ _ _ (fun q hq => last.2.1 q (notDst q (by simp [hq])))).trans body.2.1
  have final : out.phase=s.phase ∧ regValue K.out out.basis=(S+O)%p ∧
      ∀q,q∉K.out → out.basis q=s.basis q := by
    refine ⟨last.1.trans (body.1.trans first.1),finalValue,?_⟩
    intro q hq
    by_cases inside : q∈dst
    · exact ((regValue_zero _ _).mp lastValue q inside).trans ((regValue_zero _ _).mp dst0 q inside).symm
    · exact (last.2.1 q inside).trans ((body.2.2 q hq).trans (first.2.2 q inside))
  have cm : measurementCount cp=0 := (copyNone_free src dst).2
  simpa [measuredCopiedFold,cp,kernel,u,v,out,S,run_append,cm] using final

end ECDSAAdd.Arithmetic
