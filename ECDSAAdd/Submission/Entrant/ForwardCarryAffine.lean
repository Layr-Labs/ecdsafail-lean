import ECDSAAdd.Submission.Entrant.HighOutputTailStructuredDraft
import ECDSAAdd.Submission.Entrant.AdderSpineBridgeDraft
import ECDSAAdd.Submission.Entrant.KAddCallerStructureDraft
import ECDSAAdd.Submission.Entrant.E1CallerValueFactsDraft
import ECDSAAdd.Submission.Entrant.ExitMerge

/-! Forward carry-tail integration from submission 17b41c81, retaining the promoted inverse. -/

-- Reused source module: AffineCarryTail52Draft

/-! Private finite four-bit tail52 source draft. No258-bit splice, MF or score claim.
The preceding low prefix has254 bits0..253. Its carry253 is1793; the three
initially-clean work targets are1794/1795/1796. No phase restriction is imposed. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.AffineCarryTail52Research
open Arithmetic Challenge

structure Ports where
  a0 : Wire
  a1 : Wire
  a2 : Wire
  a3 : Wire
  b0 : Wire
  b1 : Wire
  b2 : Wire
  b3 : Wire
  cin : Wire
  z0 : Wire
  z1 : Wire
  z2 : Wire

def wireList (p : Ports) : List Wire :=
  [p.a0,p.a1,p.a2,p.a3,p.b0,p.b1,p.b2,p.b3,p.cin,p.z0,p.z1,p.z2]
def xs (p : Ports) : List Wire := [p.a0,p.a1,p.a2,p.a3]
def ys (p : Ports) : List Wire := [p.b0,p.b1,p.b2,p.b3]
def zs (p : Ports) : List Wire := [p.z0,p.z1,p.z2]
def Clean (p : Ports) (b : BasisState) : Prop :=
  b p.z0=false ∧ b p.z1=false ∧ b p.z2=false

/-- Exact physical port map, not a new low-prefix or pool-injectivity theorem. -/
def actualPorts (w : Nat → Wire) : Ports :=
  ⟨w 254,w 255,w 256,w 257,w 1024,w 1025,w 1026,w 1027,w 1793,w 1794,w 1795,w 1796⟩
def actualFlag (w : Nat → Wire) : Wire := w 1028

def oldPrefix (p : Ports) : Program :=
  majority p.a0 p.b0 p.cin p.z0 ++ majority p.a1 p.b1 p.z0 p.z1 ++
    majority p.a2 p.b2 p.z1 p.z2

def clone255 (p : Ports) (flag : Wire) : Program :=
  [.CX p.z0 p.z1,.CX p.a1 p.z1,.CX p.b1 p.z1,.CX p.a2 p.z1,
    .CX p.b2 p.z1,.CX flag p.z1,.X p.z1]
def clone256 (p : Ports) (flag : Wire) : Program :=
  [.CX p.a3 p.z2,.CX p.b3 p.z2,.CX flag p.z2]
def forwardPrefix (p : Ports) (flag : Wire) : Program :=
  majority p.a0 p.b0 p.cin p.z0 ++ clone255 p flag ++ clone256 p flag

def exitPrefix (p : Ports) : Program :=
  [.CX p.a1 p.z0,.CX p.b1 p.z0] ++ [.CX p.a2 p.z1,.CX p.b2 p.z1] ++
    [.CX p.a3 p.z2,.CX p.b3 p.z2]

/-- Unchanged descending measurements z2,z1,z0 and unchanged sum gates. -/
def commonSuffix (p : Ports) : Program :=
  [.CX p.a3 p.b3,.CX p.z2 p.b3] ++
    eraseCarry p.a2 p.b2 p.z1 p.z2 ++ [.CX p.a2 p.b2,.CX p.z1 p.b2] ++
    eraseCarry p.a1 p.b1 p.z0 p.z1 ++ [.CX p.a1 p.b1,.CX p.z0 p.b1] ++
    eraseCarry p.a0 p.b0 p.cin p.z0 ++ [.CX p.a0 p.b0,.CX p.cin p.b0]

def oldTail (p : Ports) : Program := oldPrefix p ++ commonSuffix p
def forwardTail (p : Ports) (flag : Wire) : Program := forwardPrefix p flag ++ commonSuffix p
def exitTail (p : Ports) : Program := exitPrefix p ++ commonSuffix p

/-- Promise about the ACTUAL OLD tail output, not an assumed carry/input predicate. -/
def ForwardPromise (p : Ports) (par : Bool) (s : State) : Prop :=
  (run (oldTail p) [] s).basis p.b3=par ∧
  ((run (oldTail p) [] s).basis p.b2 ^^ (run (oldTail p) [] s).basis p.b1)=!par

def ExitPromise (p : Ports) (s : State) : Prop :=
  (run (oldTail p) [] s).basis p.b1=false ∧
  (run (oldTail p) [] s).basis p.b2=false ∧
  (run (oldTail p) [] s).basis p.b3=false

private theorem run_cat (p q : Program) (m : List Bool) (s : State) :
    run (p++q) m s=run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append,run_take]

private theorem majority_nd (p : Ports) (nd : (wireList p).Nodup) :
    [p.a0,p.b0,p.cin,p.z0].Nodup ∧ [p.a1,p.b1,p.z0,p.z1].Nodup ∧
      [p.a2,p.b2,p.z1,p.z2].Nodup := by
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd ⊢
  tauto

private theorem scratch_ne (p : Ports) (nd : (wireList p).Nodup) :
    p.z1≠p.z0 ∧ p.z2≠p.z0 ∧ p.z2≠p.z1 := by
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true,ne_comm] at nd ⊢
  tauto

private theorem adder_nd (p : Ports) (nd : (wireList p).Nodup) :
    (p.cin :: (xs p ++ ys p ++ zs p)).Nodup := by
  simp only [wireList,xs,ys,zs,List.cons_append,List.nil_append,List.nodup_cons,
    List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true,ne_comm] at nd ⊢
  tauto

private theorem work_outside (p : Ports) (nd : (wireList p).Nodup) :
    p.z0∉ys p ∧ p.z1∉ys p ∧ p.z2∉ys p := by
  simp only [wireList,ys,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true,ne_comm] at nd ⊢
  tauto

private theorem flag_outside (p : Ports) (flag : Wire) (nd : (flag::wireList p).Nodup) :
    flag∉ys p := by
  simp only [wireList,ys,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd ⊢
  tauto

private def c0 (p : Ports) (b : BasisState) : Bool := carryBit (b p.a0) (b p.b0) (b p.cin)
private def c1 (p : Ports) (b : BasisState) : Bool := carryBit (b p.a1) (b p.b1) (c0 p b)
private def c2 (p : Ports) (b : BasisState) : Bool := carryBit (b p.a2) (b p.b2) (c1 p b)
private def paint (p : Ports) (b : BasisState) (k0 k1 k2 : Bool) : BasisState :=
  writeBit (writeBit (writeBit b p.z0 k0) p.z1 k1) p.z2 k2
private def oldPost (p : Ports) (s : State) : State :=
  ⟨s.phase,paint p s.basis (c0 p s.basis) (c1 p s.basis) (c2 p s.basis)⟩
private def affine255 (p : Ports) (b : BasisState) (par : Bool) : Bool :=
  !((((((c0 p b ^^ b p.a1) ^^ b p.b1) ^^ b p.a2) ^^ b p.b2) ^^ par))
private def affine256 (p : Ports) (b : BasisState) (par : Bool) : Bool :=
  (b p.a3 ^^ b p.b3) ^^ par
private def forwardPost (p : Ports) (flag : Wire) (s : State) : State :=
  ⟨s.phase,paint p s.basis (c0 p s.basis)
    (affine255 p s.basis (s.basis flag)) (affine256 p s.basis (s.basis flag))⟩
private def exitPost (p : Ports) (s : State) : State :=
  ⟨s.phase,paint p s.basis (s.basis p.a1 ^^ s.basis p.b1)
    (s.basis p.a2 ^^ s.basis p.b2) (s.basis p.a3 ^^ s.basis p.b3)⟩

private theorem cx2 (a b z : Wire) (ha : a≠z) (hb : b≠z) (s : State) (m : List Bool) :
    run [.CX a z,.CX b z] m s =
      ⟨s.phase,writeBit s.basis z ((s.basis z ^^ s.basis a) ^^ s.basis b)⟩ := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=z <;> simp_all [writeBit,Function.update]

private theorem cx3 (a b c z : Wire) (ha : a≠z) (hb : b≠z) (hc : c≠z)
    (s : State) (m : List Bool) :
    run [.CX a z,.CX b z,.CX c z] m s =
      ⟨s.phase,writeBit s.basis z (((s.basis z ^^ s.basis a) ^^ s.basis b) ^^ s.basis c)⟩ := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=z <;> simp_all [writeBit,Function.update]

private theorem cx6x (a b c d e f z : Wire)
    (ha : a≠z) (hb : b≠z) (hc : c≠z) (hd : d≠z) (he : e≠z) (hf : f≠z)
    (s : State) (m : List Bool) :
    run [.CX a z,.CX b z,.CX c z,.CX d z,.CX e z,.CX f z,.X z] m s =
      ⟨s.phase,writeBit s.basis z
        (!(((((((s.basis z ^^ s.basis a) ^^ s.basis b) ^^ s.basis c) ^^ s.basis d) ^^ s.basis e) ^^ s.basis f)))⟩ := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=z <;> simp_all [writeBit,Function.update]

private theorem old_prefix_run (p : Ports) (nd : (wireList p).Nodup)
    (s : State) (m : List Bool) (clean : Clean p s.basis) :
    run (oldPrefix p) m s=oldPost p s := by
  obtain ⟨n0,n1,n2⟩ := majority_nd p nd
  obtain ⟨hz10,hz20,hz21⟩ := scratch_ne p nd
  have nn := nd
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nn
  let t0 : State := ⟨s.phase,writeBit s.basis p.z0 (c0 p s.basis)⟩
  let t1 : State := ⟨s.phase,writeBit (writeBit s.basis p.z0 (c0 p s.basis)) p.z1 (c1 p s.basis)⟩
  have read1 : t0.basis p.z1=false := by
    change (Function.update s.basis p.z0 (c0 p s.basis)) p.z1=false
    rw [Function.update_of_ne hz10]
    exact clean.2.1
  have read2 : t1.basis p.z2=false := by
    change (Function.update (Function.update s.basis p.z0 (c0 p s.basis)) p.z1 (c1 p s.basis)) p.z2=false
    rw [Function.update_of_ne hz21,Function.update_of_ne hz20]
    exact clean.2.2
  have first (r : List Bool) : run (majority p.a0 p.b0 p.cin p.z0) r s=t0 := by
    rw [majority_correct _ _ _ _ n0]
    simp_all [t0,c0,Clean]
  have second (r : List Bool) : run (majority p.a1 p.b1 p.z0 p.z1) r t0=t1 := by
    rw [majority_correct _ _ _ _ n1]
    rw [read1,Bool.false_xor]
    simp_all [hz10,hz20,hz21,t0,t1,c0,c1,Clean,writeBit,Function.update,ne_comm]
  have third (r : List Bool) : run (majority p.a2 p.b2 p.z1 p.z2) r t1=oldPost p s := by
    rw [majority_correct _ _ _ _ n2]
    rw [read2,Bool.false_xor]
    simp_all [hz10,hz20,hz21,t0,t1,oldPost,paint,c0,c1,c2,Clean,writeBit,Function.update,ne_comm]
  simp only [oldPrefix,run_cat,first,second,third]


private theorem forward_prefix_run (p : Ports) (flag : Wire) (nd : (flag::wireList p).Nodup)
    (s : State) (m : List Bool) (clean : Clean p s.basis) :
    run (forwardPrefix p flag) m s=forwardPost p flag s := by
  have n0 := (majority_nd p (List.nodup_cons.mp nd).2).1
  obtain ⟨hz10,hz20,hz21⟩ := scratch_ne p (List.nodup_cons.mp nd).2
  have nn := nd
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nn
  let t0 : State := ⟨s.phase,writeBit s.basis p.z0 (c0 p s.basis)⟩
  let t1 : State := ⟨s.phase,writeBit (writeBit s.basis p.z0 (c0 p s.basis)) p.z1
    (affine255 p s.basis (s.basis flag))⟩
  have read1 : t0.basis p.z1=false := by
    change (Function.update s.basis p.z0 (c0 p s.basis)) p.z1=false
    rw [Function.update_of_ne hz10]
    exact clean.2.1
  have read2 : t1.basis p.z2=false := by
    change (Function.update (Function.update s.basis p.z0 (c0 p s.basis)) p.z1 (affine255 p s.basis (s.basis flag))) p.z2=false
    rw [Function.update_of_ne hz21,Function.update_of_ne hz20]
    exact clean.2.2
  have first (r : List Bool) : run (majority p.a0 p.b0 p.cin p.z0) r s=t0 := by
    rw [majority_correct _ _ _ _ n0]
    simp_all [t0,c0,Clean]
  have second (r : List Bool) : run (clone255 p flag) r t0=t1 := by
    rw [clone255,cx6x p.z0 p.a1 p.b1 p.a2 p.b2 flag p.z1
      (by simp_all [ne_comm]) (by simp_all [ne_comm]) (by simp_all [ne_comm])
      (by simp_all [ne_comm]) (by simp_all [ne_comm]) (by simp_all [ne_comm])]
    rw [read1,Bool.false_xor]
    simp_all [hz10,hz20,hz21,t0,t1,affine255,c0,Clean,writeBit,Function.update,ne_comm]
  have third (r : List Bool) : run (clone256 p flag) r t1=forwardPost p flag s := by
    rw [clone256,cx3 p.a3 p.b3 flag p.z2
      (by simp_all [ne_comm]) (by simp_all [ne_comm]) (by simp_all [ne_comm])]
    rw [read2,Bool.false_xor]
    simp_all [hz10,hz20,hz21,t0,t1,forwardPost,paint,affine256,Clean,writeBit,Function.update,ne_comm]
  simp only [forwardPrefix,run_cat,first,second,third]


private theorem exit_prefix_run (p : Ports) (nd : (wireList p).Nodup)
    (s : State) (m : List Bool) (clean : Clean p s.basis) :
    run (exitPrefix p) m s=exitPost p s := by
  obtain ⟨hz10,hz20,hz21⟩ := scratch_ne p nd
  have nn := nd
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nn
  let t0 : State := ⟨s.phase,writeBit s.basis p.z0 (s.basis p.a1 ^^ s.basis p.b1)⟩
  let t1 : State := ⟨s.phase,writeBit (writeBit s.basis p.z0 (s.basis p.a1 ^^ s.basis p.b1))
    p.z1 (s.basis p.a2 ^^ s.basis p.b2)⟩
  have read1 : t0.basis p.z1=false := by
    change (Function.update s.basis p.z0 (s.basis p.a1 ^^ s.basis p.b1)) p.z1=false
    rw [Function.update_of_ne hz10]
    exact clean.2.1
  have read2 : t1.basis p.z2=false := by
    change (Function.update (Function.update s.basis p.z0 (s.basis p.a1 ^^ s.basis p.b1)) p.z1 (s.basis p.a2 ^^ s.basis p.b2)) p.z2=false
    rw [Function.update_of_ne hz21,Function.update_of_ne hz20]
    exact clean.2.2
  have first (r : List Bool) : run [.CX p.a1 p.z0,.CX p.b1 p.z0] r s=t0 := by
    rw [cx2 p.a1 p.b1 p.z0 (by simp_all [ne_comm]) (by simp_all [ne_comm])]
    simp_all [t0,Clean]
  have second (r : List Bool) : run [.CX p.a2 p.z1,.CX p.b2 p.z1] r t0=t1 := by
    rw [cx2 p.a2 p.b2 p.z1 (by simp_all [ne_comm]) (by simp_all [ne_comm])]
    rw [read1,Bool.false_xor]
    simp_all [hz10,hz20,hz21,t0,t1,Clean,writeBit,Function.update,ne_comm]
  have third (r : List Bool) : run [.CX p.a3 p.z2,.CX p.b3 p.z2] r t1=exitPost p s := by
    rw [cx2 p.a3 p.b3 p.z2 (by simp_all [ne_comm]) (by simp_all [ne_comm])]
    rw [read2,Bool.false_xor]
    simp_all [hz10,hz20,hz21,t0,t1,exitPost,paint,Clean,writeBit,Function.update,ne_comm]
  simp only [exitPrefix,run_cat,first,second,third]

/-- Corrections change phase only: the measured carry is the sole basis write. -/

private theorem erase_basis (a b c z : Wire) (s : State) (m : List Bool) :
    (run (eraseCarry a b c z) m s).basis=writeBit s.basis z false := by
  simp only [eraseCarry,run,measureAndCorrect,correct_basis]

private def finish (a b c z : Wire) : Program :=
  eraseCarry a b c z ++ [.CX a b,.CX c b]

private theorem finish_basis (a b c z : Wire) (nd : [a,b,c,z].Nodup)
    (s : State) (m : List Bool) :
    (run (finish a b c z) m s).basis=
      writeBit (writeBit s.basis z false) b ((s.basis b ^^ s.basis a) ^^ s.basis c) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haz⟩,⟨hbc,hbz⟩,hcz⟩ := nd
  rw [finish,run_cat,cx2 a c b hab (Ne.symm hbc)]
  simp only [erase_basis]
  simp [writeBit,haz,hbz,hcz]


private theorem finish_keep (a b c z : Wire) (nd : [a,b,c,z].Nodup)
    (q : Wire) (hqb : q≠b) (hqz : q≠z) (s : State) (m : List Bool) :
    (run (finish a b c z) m s).basis q=s.basis q := by
  rw [finish_basis a b c z nd]
  simp only [writeBit,Function.update_of_ne hqb,Function.update_of_ne hqz]

private theorem finish_sum (a b c z : Wire) (nd : [a,b,c,z].Nodup)
    (s : State) (m : List Bool) :
    (run (finish a b c z) m s).basis b=((s.basis b ^^ s.basis a) ^^ s.basis c) := by
  rw [finish_basis a b c z nd]
  simp only [writeBit,Function.update_self]

/-- The actual suffix basis outputs, for arbitrary record, before any carry promise. -/
private theorem suffix_bits (p : Ports) (nd : (wireList p).Nodup) (t : State) (m : List Bool) :
    (run (commonSuffix p) m t).basis p.b1=((t.basis p.b1 ^^ t.basis p.a1) ^^ t.basis p.z0) ∧
    (run (commonSuffix p) m t).basis p.b2=((t.basis p.b2 ^^ t.basis p.a2) ^^ t.basis p.z1) ∧
    (run (commonSuffix p) m t).basis p.b3=((t.basis p.b3 ^^ t.basis p.a3) ^^ t.basis p.z2) := by
  obtain ⟨n0,n1,n2⟩ := majority_nd p nd
  have nn := nd
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nn
  obtain ⟨⟨n01,n02,n03,n04,n05,n06,n07,n08,n09,n010,n011⟩,
    ⟨n12,n13,n14,n15,n16,n17,n18,n19,n110,n111⟩,
    ⟨n23,n24,n25,n26,n27,n28,n29,n210,n211⟩,
    ⟨n34,n35,n36,n37,n38,n39,n310,n311⟩,
    ⟨n45,n46,n47,n48,n49,n410,n411⟩,
    ⟨n56,n57,n58,n59,n510,n511⟩,
    ⟨n67,n68,n69,n610,n611⟩,
    ⟨n78,n79,n710,n711⟩,
    ⟨n89,n810,n811⟩,⟨n910,n911⟩,n1011⟩ := nn
  let top : Program := [.CX p.a3 p.b3,.CX p.z2 p.b3]
  let f2 := finish p.a2 p.b2 p.z1 p.z2
  let f1 := finish p.a1 p.b1 p.z0 p.z1
  let f0 := finish p.a0 p.b0 p.cin p.z0
  let r2 := m.drop (measurementCount top)
  let r1 := r2.drop (measurementCount f2)
  let r0 := r1.drop (measurementCount f1)
  have decomposition : commonSuffix p=top++(f2++(f1++f0)) := by
    simp only [commonSuffix,top,f2,f1,f0,finish,List.append_assoc]
  have chain : run (commonSuffix p) m t=
      run f0 r0 (run f1 r1 (run f2 r2 (run top m t))) := by
    rw [decomposition,run_cat top (f2++(f1++f0)),run_cat f2 (f1++f0),run_cat f1 f0]
  let tTop := run top m t
  let t2 := run f2 r2 tTop
  let t1 := run f1 r1 t2
  have k0 (q : Wire) (hb : q≠p.b0) (hz : q≠p.z0) :
      (run f0 r0 t1).basis q=t1.basis q :=
    finish_keep p.a0 p.b0 p.cin p.z0 n0 q hb hz t1 r0
  have k1 (q : Wire) (hb : q≠p.b1) (hz : q≠p.z1) :
      t1.basis q=t2.basis q := finish_keep p.a1 p.b1 p.z0 p.z1 n1 q hb hz t2 r1
  have s1 : t1.basis p.b1=((t2.basis p.b1 ^^ t2.basis p.a1) ^^ t2.basis p.z0) :=
    finish_sum p.a1 p.b1 p.z0 p.z1 n1 t2 r1
  have k2 (q : Wire) (hb : q≠p.b2) (hz : q≠p.z2) :
      t2.basis q=tTop.basis q := finish_keep p.a2 p.b2 p.z1 p.z2 n2 q hb hz tTop r2
  have s2 : t2.basis p.b2=((tTop.basis p.b2 ^^ tTop.basis p.a2) ^^ tTop.basis p.z1) :=
    finish_sum p.a2 p.b2 p.z1 p.z2 n2 tTop r2
  have top_bits : tTop.basis=writeBit t.basis p.b3 ((t.basis p.b3 ^^ t.basis p.a3) ^^ t.basis p.z2) := by
    dsimp only [tTop,top]
    rw [cx2 p.a3 p.z2 p.b3 n37 (Ne.symm n711)]
  have kt (q : Wire) (hb : q≠p.b3) : tTop.basis q=t.basis q := by
    rw [top_bits]
    simp only [writeBit,Function.update_of_ne hb]
  have st : tTop.basis p.b3=((t.basis p.b3 ^^ t.basis p.a3) ^^ t.basis p.z2) := by
    rw [top_bits]
    simp only [writeBit,Function.update_self]
  rw [chain]
  change (run f0 r0 t1).basis p.b1=_ ∧ (run f0 r0 t1).basis p.b2=_ ∧ (run f0 r0 t1).basis p.b3=_
  refine ⟨?_,?_,?_⟩
  · rw [k0 p.b1 (Ne.symm n45) n59,s1,
      k2 p.b1 n56 n511,k2 p.a1 n16 n111,k2 p.z0 (Ne.symm n69) n911,
      kt p.b1 n57,kt p.a1 n17,kt p.z0 (Ne.symm n79)]
  · rw [k0 p.b2 (Ne.symm n46) n69,k1 p.b2 (Ne.symm n56) n610,s2,
      kt p.b2 n67,kt p.a2 n27,kt p.z1 (Ne.symm n710)]
  · rw [k0 p.b3 (Ne.symm n47) n79,k1 p.b3 (Ne.symm n57) n710,
      k2 p.b3 (Ne.symm n67) n711,st]

private def out1 (p : Ports) (b : BasisState) : Bool := (b p.b1 ^^ b p.a1) ^^ c0 p b
private def out2 (p : Ports) (b : BasisState) : Bool := (b p.b2 ^^ b p.a2) ^^ c1 p b
private def out3 (p : Ports) (b : BasisState) : Bool := (b p.b3 ^^ b p.a3) ^^ c2 p b
private theorem old_prefix_m (p : Ports) : measurementCount (oldPrefix p)=0 := rfl
private theorem forward_prefix_m (p : Ports) (flag : Wire) : measurementCount (forwardPrefix p flag)=0 := rfl
private theorem exit_prefix_m (p : Ports) : measurementCount (exitPrefix p)=0 := rfl

/-- Proven connection between actual OLD output bits and the three computed carries. -/

private theorem old_output_bits (p : Ports) (nd : (wireList p).Nodup)
    (s : State) (clean : Clean p s.basis) :
    (run (oldTail p) [] s).basis p.b1=out1 p s.basis ∧
    (run (oldTail p) [] s).basis p.b2=out2 p s.basis ∧
    (run (oldTail p) [] s).basis p.b3=out3 p s.basis := by
  have nn := nd
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nn
  have joined : run (oldTail p) [] s=run (commonSuffix p) [] (oldPost p s) := by
    change run (oldPrefix p ++ commonSuffix p) [] s=_
    rw [run_cat (oldPrefix p) (commonSuffix p) [] s,old_prefix_m,List.drop_zero,
      old_prefix_run p nd s [] clean]
  have h := suffix_bits p nd (oldPost p s) []
  simp only [joined]
  simp_all [oldPost,paint,out1,out2,out3,writeBit,Function.update,ne_comm]


private theorem solve_sum (a b c v : Bool) (h : ((b ^^ a) ^^ c)=v) : c=((a ^^ b) ^^ v) := by
  cases a <;> cases b <;> cases c <;> cases v <;> simp_all

private theorem solve_adjacent (u v k0 k1 par : Bool)
    (h : ((v ^^ k1) ^^ (u ^^ k0))=!par) : k1=!(((k0 ^^ u) ^^ v) ^^ par) := by
  cases u <;> cases v <;> cases k0 <;> cases k1 <;> cases par <;> simp_all

/-- Pure prefixes have IDENTICAL complete State, including arbitrary initial phase/exterior. -/
theorem forward_prefix_eq_old (p : Ports) (flag : Wire) (nd : (flag::wireList p).Nodup)
    (s : State) (clean : Clean p s.basis) (par : Bool) (flagIn : s.basis flag=par)
    (promise : ForwardPromise p par s) (m n : List Bool) :
    run (forwardPrefix p flag) m s=run (oldPrefix p) n s := by
  have nd12 := (List.nodup_cons.mp nd).2
  have bits := old_output_bits p nd12 s clean
  simp only [ForwardPromise] at promise
  rw [bits.2.2,bits.2.1,bits.1] at promise
  have h1 : c1 p s.basis=affine255 p s.basis par := by
    have h := solve_adjacent (s.basis p.b1 ^^ s.basis p.a1) (s.basis p.b2 ^^ s.basis p.a2)
      (c0 p s.basis) (c1 p s.basis) par promise.2
    simpa only [affine255,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm] using h
  have h2 : c2 p s.basis=affine256 p s.basis par :=
    solve_sum (s.basis p.a3) (s.basis p.b3) (c2 p s.basis) par promise.1
  simp only [forward_prefix_run p flag nd s m clean,old_prefix_run p nd12 s n clean,
    forwardPost,oldPost,flagIn,←h1,←h2]

theorem exit_prefix_eq_old (p : Ports) (nd : (wireList p).Nodup)
    (s : State) (clean : Clean p s.basis) (promise : ExitPromise p s) (m n : List Bool) :
    run (exitPrefix p) m s=run (oldPrefix p) n s := by
  have bits := old_output_bits p nd s clean
  simp only [ExitPromise] at promise
  rw [bits.1,bits.2.1,bits.2.2] at promise
  have h0 : c0 p s.basis=(s.basis p.a1 ^^ s.basis p.b1) := by
    simpa only [Bool.xor_false] using solve_sum (s.basis p.a1) (s.basis p.b1) (c0 p s.basis) false promise.1
  have h1 : c1 p s.basis=(s.basis p.a2 ^^ s.basis p.b2) := by
    simpa only [Bool.xor_false] using solve_sum (s.basis p.a2) (s.basis p.b2) (c1 p s.basis) false promise.2.1
  have h2 : c2 p s.basis=(s.basis p.a3 ^^ s.basis p.b3) := by
    simpa only [Bool.xor_false] using solve_sum (s.basis p.a3) (s.basis p.b3) (c2 p s.basis) false promise.2.2
  simp only [exit_prefix_run p nd s m clean,old_prefix_run p nd s n clean,
    exitPost,oldPost,←h0,←h1,←h2]

/-- Same three measured ordinals and literally the same suffix, for every record. -/
theorem forward_tail_eq_old (p : Ports) (flag : Wire) (nd : (flag::wireList p).Nodup)
    (s : State) (clean : Clean p s.basis) (par : Bool) (flagIn : s.basis flag=par)
    (promise : ForwardPromise p par s) (m : List Bool) :
    run (forwardTail p flag) m s=run (oldTail p) m s := by
  have left := run_cat (forwardPrefix p flag) (commonSuffix p) m s
  have right := run_cat (oldPrefix p) (commonSuffix p) m s
  rw [forward_prefix_m,List.drop_zero] at left
  rw [old_prefix_m,List.drop_zero] at right
  exact left.trans ((congrArg (fun t => run (commonSuffix p) m t)
    (forward_prefix_eq_old p flag nd s clean par flagIn promise m m)).trans right.symm)

theorem exit_tail_eq_old (p : Ports) (nd : (wireList p).Nodup)
    (s : State) (clean : Clean p s.basis) (promise : ExitPromise p s) (m : List Bool) :
    run (exitTail p) m s=run (oldTail p) m s := by
  have left := run_cat (exitPrefix p) (commonSuffix p) m s
  have right := run_cat (oldPrefix p) (commonSuffix p) m s
  rw [exit_prefix_m,List.drop_zero] at left
  rw [old_prefix_m,List.drop_zero] at right
  exact left.trans ((congrArg (fun t => run (commonSuffix p) m t)
    (exit_prefix_eq_old p nd s clean promise m m)).trans right.symm)


private theorem old_tail_add (p : Ports) :
    oldTail p=addInPlace (xs p) (ys p) (zs p) p.cin := by rfl

private theorem old_tail_frame (p : Ports) (nd : (wireList p).Nodup) (s : State)
    (clean : Clean p s.basis) (m : List Bool) :
    (run (oldTail p) m s).phase=s.phase ∧ Clean p (run (oldTail p) m s).basis ∧
    (∀q,q∉ys p → (run (oldTail p) m s).basis q=s.basis q) := by
  have hc : ∀q∈zs p,s.basis q=false := by
    intro q hq
    simp only [zs,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact clean.1
    · exact clean.2.1
    · exact clean.2.2
  have spec := addInPlace_correct (xs p) (ys p) (zs p) p.cin (adder_nd p nd)
    (by rfl) (by rfl) s m hc
  have phase : (run (oldTail p) m s).phase=s.phase := by simpa only [old_tail_add] using spec.1
  have frame : ∀q,q∉ys p → (run (oldTail p) m s).basis q=s.basis q := by
    simpa only [old_tail_add] using spec.2.1
  have outside := work_outside p nd
  exact ⟨phase,⟨(frame _ outside.1).trans clean.1,(frame _ outside.2.1).trans clean.2.1,
    (frame _ outside.2.2).trans clean.2.2⟩,frame⟩

/-- Full old/new State equality, restored three scratch bits, unchanged flag/source/exterior and phase. -/
theorem forward_full (p : Ports) (flag : Wire) (nd : (flag::wireList p).Nodup)
    (s : State) (clean : Clean p s.basis) (par : Bool) (flagIn : s.basis flag=par)
    (promise : ForwardPromise p par s) (m : List Bool) :
    run (forwardTail p flag) m s=run (oldTail p) m s ∧
    (run (forwardTail p flag) m s).phase=s.phase ∧ Clean p (run (forwardTail p flag) m s).basis ∧
    (run (forwardTail p flag) m s).basis flag=s.basis flag ∧
    (∀q,q∉ys p → (run (forwardTail p flag) m s).basis q=s.basis q) := by
  have eq := forward_tail_eq_old p flag nd s clean par flagIn promise m
  have old := old_tail_frame p (List.nodup_cons.mp nd).2 s clean m
  refine ⟨eq,?_,?_,?_,?_⟩
  all_goals rw [eq]
  · exact old.1
  · exact old.2.1
  · exact old.2.2 flag (flag_outside p flag nd)
  · exact old.2.2

theorem exit_full (p : Ports) (nd : (wireList p).Nodup)
    (s : State) (clean : Clean p s.basis) (promise : ExitPromise p s) (m : List Bool) :
    run (exitTail p) m s=run (oldTail p) m s ∧
    (run (exitTail p) m s).phase=s.phase ∧ Clean p (run (exitTail p) m s).basis ∧
    (∀q,q∉ys p → (run (exitTail p) m s).basis q=s.basis q) := by
  have eq := exit_tail_eq_old p nd s clean promise m
  have old := old_tail_frame p nd s clean m
  refine ⟨eq,?_,?_,?_⟩
  all_goals rw [eq]
  · exact old.1
  · exact old.2.1
  · exact old.2.2

private theorem majority_t (a b c z : Wire) : toffoliCount (majority a b c z)=1 := by rfl
private theorem majority_m (a b c z : Wire) : measurementCount (majority a b c z)=0 := by rfl
private theorem majority_s (a b c z : Wire) : gateSlots (majority a b c z)=6 := by rfl

private theorem erase_t (a b c z : Wire) : toffoliCount (eraseCarry a b c z)=0 := by rfl
private theorem erase_m (a b c z : Wire) : measurementCount (eraseCarry a b c z)=1 := by rfl
private theorem erase_s (a b c z : Wire) : gateSlots (eraseCarry a b c z)=4 := by rfl

private theorem pair_t (a b c z : Wire) : toffoliCount (([.CX a b,.CX c z] : Program))=0 := by rfl
private theorem pair_m (a b c z : Wire) : measurementCount (([.CX a b,.CX c z] : Program))=0 := by rfl
private theorem pair_s (a b c z : Wire) : gateSlots (([.CX a b,.CX c z] : Program))=2 := by rfl

private theorem clone255_t (p : Ports) (flag : Wire) : toffoliCount (clone255 p flag)=0 := by rfl
private theorem clone255_m (p : Ports) (flag : Wire) : measurementCount (clone255 p flag)=0 := by rfl
private theorem clone255_s (p : Ports) (flag : Wire) : gateSlots (clone255 p flag)=7 := by rfl

private theorem clone256_t (p : Ports) (flag : Wire) : toffoliCount (clone256 p flag)=0 := by rfl
private theorem clone256_m (p : Ports) (flag : Wire) : measurementCount (clone256 p flag)=0 := by rfl
private theorem clone256_s (p : Ports) (flag : Wire) : gateSlots (clone256 p flag)=3 := by rfl

private theorem suffix_t (p : Ports) : toffoliCount (commonSuffix p)=0 := by
  simp only [commonSuffix,toffoliCount_append,erase_t,pair_t]

private theorem suffix_m (p : Ports) : measurementCount (commonSuffix p)=3 := by
  simp only [commonSuffix,measurementCount_append,erase_m,pair_m]

private theorem suffix_s (p : Ports) : gateSlots (commonSuffix p)=20 := by
  simp only [commonSuffix,gateSlots_append,erase_s,pair_s]

/-- Exact syntax resources; all three work wires remain measured and are NOT retired. -/
theorem old_costs (p : Ports) :
    toffoliCount (oldTail p)=3 ∧ measurementCount (oldTail p)=3 ∧ gateSlots (oldTail p)=38 := by
  refine ⟨?_,?_,?_⟩
  · simp only [oldTail,oldPrefix,toffoliCount_append,majority_t,suffix_t]
  · simp only [oldTail,oldPrefix,measurementCount_append,majority_m,suffix_m]
  · simp only [oldTail,oldPrefix,gateSlots_append,majority_s,suffix_s]

theorem forward_costs (p : Ports) (flag : Wire) :
    toffoliCount (forwardTail p flag)=1 ∧ measurementCount (forwardTail p flag)=3 ∧
      gateSlots (forwardTail p flag)=36 := by
  refine ⟨?_,?_,?_⟩
  · simp only [forwardTail,forwardPrefix,toffoliCount_append,majority_t,clone255_t,clone256_t,suffix_t]
  · simp only [forwardTail,forwardPrefix,measurementCount_append,majority_m,clone255_m,clone256_m,suffix_m]
  · simp only [forwardTail,forwardPrefix,gateSlots_append,majority_s,clone255_s,clone256_s,suffix_s]

theorem exit_costs (p : Ports) :
    toffoliCount (exitTail p)=0 ∧ measurementCount (exitTail p)=3 ∧ gateSlots (exitTail p)=26 := by
  refine ⟨?_,?_,?_⟩
  · simp only [exitTail,exitPrefix,toffoliCount_append,pair_t,suffix_t]
  · simp only [exitTail,exitPrefix,measurementCount_append,pair_m,suffix_m]
  · simp only [exitTail,exitPrefix,gateSlots_append,pair_s,suffix_s]

#print axioms forward_prefix_eq_old
#print axioms exit_prefix_eq_old
#print axioms forward_full
#print axioms exit_full
end ECDSAAdd.Entrant.AffineCarryTail52Research

-- Reused source module: E1CarrySplice52Draft

/-! SOURCE ONLY. Exact syntax/footprint bridge at the254-bit boundary.
No MF, phase replacement, complete-candidate or resource claim is made here.
The imported tail52 source has its own separate qualification obligation. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1CarrySplice52Research
open Arithmetic RecordedQuantum Challenge AdderSpineBridgeResearch
open KAddCallerBridgeResearch HighOutputTailStructuredResearch AffineCarryTail52Research

attribute [local irreducible] ECDSAAdd.wires

def lowPrefix52 (w : Nat → Wire) : Program :=
  adderPrefix (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797)

def lowSuffix52 (w : Nat → Wire) : Program :=
  adderSuffix (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797)

def lowPorts52 (w : Nat → Wire) : List Wire :=
  spinePorts (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797)

private theorem lastCarry_append52 (xs ys : List Wire) (cin : Wire) :
    lastCarry (xs++ys) cin=lastCarry ys (lastCarry xs cin) := by
  induction xs generalizing cin with
  | nil => rfl
  | cons x xs ih => exact ih x

private theorem prefix_append52 (xs ys cs tx ty tc : List Wire) (cin : Wire)
    (hy : xs.length=ys.length) (hc : xs.length=cs.length) :
    adderPrefix (xs++tx) (ys++ty) (cs++tc) cin=
      adderPrefix xs ys cs cin++adderPrefix tx ty tc (lastCarry cs cin) := by
  induction xs generalizing ys cs cin with
  | nil =>
      have ey : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy.symm)
      have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc.symm)
      subst ys;subst cs
      rfl
  | cons a xs ih =>
      cases ys with
      | nil => simp at hy
      | cons b ys =>
          cases cs with
          | nil => simp at hc
          | cons z cs =>
              have hy' : xs.length=ys.length := by simpa using hy
              have hc' : xs.length=cs.length := by simpa using hc
              simp only [List.cons_append,adderPrefix,lastCarry,
                ih ys cs z hy' hc',List.append_assoc]

private theorem suffix_append52 (xs ys cs tx ty tc : List Wire) (cin : Wire)
    (hy : xs.length=ys.length) (hc : xs.length=cs.length) :
    adderSuffix (xs++tx) (ys++ty) (cs++tc) cin=
      adderSuffix tx ty tc (lastCarry cs cin)++adderSuffix xs ys cs cin := by
  induction xs generalizing ys cs cin with
  | nil =>
      have ey : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy.symm)
      have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc.symm)
      subst ys;subst cs
      simp only [List.nil_append,lastCarry,adderSuffix,List.append_nil]
  | cons a xs ih =>
      cases ys with
      | nil => simp at hy
      | cons b ys =>
          cases cs with
          | nil => simp at hc
          | cons z cs =>
              have hy' : xs.length=ys.length := by simpa using hy
              have hc' : xs.length=cs.length := by simpa using hc
              simp only [List.cons_append,adderSuffix,lastCarry,
                ih ys cs z hy' hc',List.append_assoc]

/-- Only four finite data bits are unfolded. No private tail-module theorem is used. -/
private theorem old_tail_add52 (p : Ports) :
    oldTail p=addInPlace (xs p) (ys p) (zs p) p.cin := by rfl

/-- Derive the four-bit cut by factoring the CHECKED two-bit add_split.
The prefix and measured suffix lists stay symbolic throughout this proof. -/
theorem add_split_four52 (lx ly lc : List Wire) (cin : Wire) (p : Ports)
    (hy : lx.length=ly.length) (hc : lx.length=lc.length)
    (hcin : lastCarry lc cin=p.cin) :
    addInPlace (lx++xs p) (ly++ys p) (lc++zs p) cin=
      adderPrefix lx ly lc cin++oldTail p++adderSuffix lx ly lc cin := by
  have last2 : lastCarry (lc++[p.z0,p.z1]) cin=p.z1 := by
    rw [lastCarry_append52]
    rfl
  have middle :
      adderPrefix [p.a0,p.a1] [p.b0,p.b1] [p.z0,p.z1] p.cin++
        oldLeafAt p.a2 p.b2 p.z1 p.a3 p.b3 p.z2++
        adderSuffix [p.a0,p.a1] [p.b0,p.b1] [p.z0,p.z1] p.cin=oldTail p := by
    symm
    rw [old_tail_add52]
    simpa only [xs,ys,zs,lastCarry] using add_split
      [p.a0,p.a1] [p.b0,p.b1] [p.z0,p.z1] p.cin p.a2 p.a3 p.b2 p.b3 p.z2 rfl rfl
  have h := add_split (lx++[p.a0,p.a1]) (ly++[p.b0,p.b1]) (lc++[p.z0,p.z1])
    cin p.a2 p.a3 p.b2 p.b3 p.z2
    (by simp only [List.length_append,List.length_cons,List.length_nil];omega)
    (by simp only [List.length_append,List.length_cons,List.length_nil];omega)
  rw [prefix_append52 lx ly lc [p.a0,p.a1] [p.b0,p.b1] [p.z0,p.z1] cin hy hc,
    suffix_append52 lx ly lc [p.a0,p.a1] [p.b0,p.b1] [p.z0,p.z1] cin hy hc,
    last2,hcin] at h
  rw [←middle]
  simpa only [xs,ys,zs,List.append_assoc] using h

/-- The actual incoming tail carry is bit253 at1793, never bit252 or1792. -/
theorem lastCarry_low25452 (w : Nat → Wire) :
    lastCarry (wireBlock w 1540 254) (w 1797)=w 1793 := by
  have block : wireBlock w 1540 254=wireBlock w 1540 253++[w 1793] := by
    rw [←wireBlock_append w 1540 253 1]
    rfl
  rw [block,lastCarry_append52]
  rfl

/-- Literal read_add258, with actual four-bit ports and unchanged measured unwind. -/
theorem literal_split_four52 (w : Nat → Wire) :
    literalKAdd w=lowPrefix52 w++oldTail (actualPorts w)++lowSuffix52 w := by
  have hx : wireBlock w 0 258=wireBlock w 0 254++xs (actualPorts w) := by
    rw [←wireBlock_append w 0 254 4]
    rfl
  have hy : wireBlock w 770 258=wireBlock w 770 254++ys (actualPorts w) := by
    rw [←wireBlock_append w 770 254 4]
    rfl
  have hc : wireBlock w 1540 257=wireBlock w 1540 254++zs (actualPorts w) := by
    rw [←wireBlock_append w 1540 254 3]
    rfl
  rw [literalKAdd,read_add,hx,hy,hc]
  simpa only [lowPrefix52,lowSuffix52] using add_split_four52
    (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254)
    (w 1797) (actualPorts w) (by simp [wireBlock_length]) (by simp [wireBlock_length])
    (by simpa only [actualPorts] using lastCarry_low25452 w)

theorem lowPrefix_records52 (w : Nat → Wire) : measurementCount (lowPrefix52 w)=0 := by
  exact prefix_records _ _ _ _

/-- Finite pool Nodup suffices; global injectivity of the placement is not assumed. -/
theorem lowPorts_avoid_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : (254 ≤ i ∧ i < 258) ∨ (1024 ≤ i ∧ i < 1029) ∨ (1794 ≤ i ∧ i < 1797)) :
    w i∉lowPorts52 w := by
  have ir : i<1798 := by omega
  intro h
  simp only [lowPorts52,spinePorts,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h
  · have e := skywalkPool_index_inj w hn i 1797 ir (by decide) h
    omega
  all_goals
    obtain ⟨j,hj,hji⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have jr : j<1798 := by omega
    have e := skywalkPool_index_inj w hn j i jr ir hji
    omega

theorem lowPrefix_avoid_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : (254 ≤ i ∧ i < 258) ∨ (1024 ≤ i ∧ i < 1029) ∨ (1794 ≤ i ∧ i < 1797)) :
    w i∉wires (lowPrefix52 w) := by
  intro h
  exact lowPorts_avoid_pool52 w hn i hi
    (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

/-- Stronger than no-write: the measured low suffix does not touch these ports. -/
theorem lowSuffix_avoid_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : (254 ≤ i ∧ i < 258) ∨ (1024 ≤ i ∧ i < 1029) ∨ (1794 ≤ i ∧ i < 1797)) :
    w i∉wires (lowSuffix52 w) := by
  intro h
  exact lowPorts_avoid_pool52 w hn i hi
    (List.mem_toFinset.mp (suffix_support _ _ _ _ h))

theorem lowPrefix_keeps_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : (254 ≤ i ∧ i < 258) ∨ (1024 ≤ i ∧ i < 1029) ∨ (1794 ≤ i ∧ i < 1797))
    (s : State) (m : List Bool) :
    (run (lowPrefix52 w) m s).basis (w i)=s.basis (w i) := by
  apply run_preserves_outside
  exact lowPrefix_avoid_pool52 w hn i hi

/-- In particular b255..257 (indices1025..1027) survive the whole low unwind. -/
theorem lowSuffix_keeps_high_sum52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (j : Nat) (hj : 255 ≤ j ∧ j < 258) (s : State) (m : List Bool) :
    (run (lowSuffix52 w) m s).basis (w (770+j))=s.basis (w (770+j)) := by
  apply run_preserves_outside
  exact lowSuffix_avoid_pool52 w hn (770+j) (Or.inr (Or.inl ⟨by omega,by omega⟩))

end ECDSAAdd.Entrant.E1CarrySplice52Research

-- Reused source module: E1WholeKAdd52Draft

/-! Private SOURCE-ONLY whole258-bit affine tail bridge.
Only high carry254/255/256 (physical1794/1795/1796) start clean. The real
old literal program supplies the high-output promise; no MF/postWord,
all257-carry clean premise, or global wire-map injectivity is assumed. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1WholeKAdd52Research
open Arithmetic RecordedQuantum Challenge AdderSpineBridgeResearch
open KAddCallerBridgeResearch AffineCarryTail52Research E1CarrySplice52Research

/-- Low prefix is exactly254 bits0..253; its final carry is1793. -/
def flagKAdd52 (w : Nat → Wire) : Program :=
  lowPrefix52 w++forwardTail (actualPorts w) (w 1028)++lowSuffix52 w

def zeroKAdd52 (w : Nat → Wire) : Program :=
  lowPrefix52 w++exitTail (actualPorts w)++lowSuffix52 w

def highCarryClean52 (w : Nat → Wire) (b : BasisState) : Prop :=
  b (w 1794)=false ∧ b (w 1795)=false ∧ b (w 1796)=false

/-- A promise about the actual OLD full literal258 run, with an empty tape. -/
def ForwardOldOutputs52 (w : Nat → Wire) (par : Bool) (s : State) : Prop :=
  (run (literalKAdd w) [] s).basis (w 1027)=par ∧
  ((run (literalKAdd w) [] s).basis (w 1026) ^^
    (run (literalKAdd w) [] s).basis (w 1025))=!par

def ExitOldOutputs52 (w : Nat → Wire) (s : State) : Prop :=
  (run (literalKAdd w) [] s).basis (w 1025)=false ∧
  (run (literalKAdd w) [] s).basis (w 1026)=false ∧
  (run (literalKAdd w) [] s).basis (w 1027)=false

private def prefixState52 (w : Nat → Wire) (s : State) : State :=
  run (lowPrefix52 w) [] s

private theorem run_cat52 (p q : Program) (m : List Bool) (s : State) :
    run (p++q) m s=run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append,run_take]

private theorem zero_records52 (p : Program) (h : measurementCount p=0)
    (s : State) (m : List Bool) : run p m s=run p [] s := by
  simpa only [h,List.take_zero] using (run_take p m s).symm

/- Explicit interpreter lemmas are used below; never delta-reduce258 gates
while matching an output bit or rewriting one of the three splice states. -/
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.toffoliCount
  ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots

private theorem run_splice52 (p t r : Program) (hp : measurementCount p=0)
    (ht : measurementCount t=3) (s : State) (m : List Bool) :
    run (p++t++r) m s=run r (m.drop 3) (run t m (run p [] s)) := by
  have pre := zero_records52 p hp s m
  simp only [List.append_assoc,run_cat52,hp,List.drop_zero,ht,pre]

private theorem old_normal_form52 (w : Nat → Wire) (s : State) (m : List Bool) :
    run (literalKAdd w) m s=run (lowSuffix52 w) (m.drop 3)
      (run (oldTail (actualPorts w)) m (prefixState52 w s)) := by
  rw [literal_split_four52]
  exact run_splice52 (lowPrefix52 w) (oldTail (actualPorts w)) (lowSuffix52 w)
    (lowPrefix_records52 w) (old_costs (actualPorts w)).2.1 s m

private theorem flag_normal_form52 (w : Nat → Wire) (s : State) (m : List Bool) :
    run (flagKAdd52 w) m s=run (lowSuffix52 w) (m.drop 3)
      (run (forwardTail (actualPorts w) (w 1028)) m (prefixState52 w s)) := by
  exact run_splice52 (lowPrefix52 w) (forwardTail (actualPorts w) (w 1028)) (lowSuffix52 w)
    (lowPrefix_records52 w) (forward_costs (actualPorts w) (w 1028)).2.1 s m

private theorem zero_normal_form52 (w : Nat → Wire) (s : State) (m : List Bool) :
    run (zeroKAdd52 w) m s=run (lowSuffix52 w) (m.drop 3)
      (run (exitTail (actualPorts w)) m (prefixState52 w s)) := by
  exact run_splice52 (lowPrefix52 w) (exitTail (actualPorts w)) (lowSuffix52 w)
    (lowPrefix_records52 w) (exit_costs (actualPorts w)).2.1 s m

/-- Only bounded pool injectivity is used, at these13 exact indices. -/
private theorem tail_nd13_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    ((w 1028)::wireList (actualPorts w)).Nodup := by
  have neq (i j : Nat) (hi : i < 1798) (hj : j < 1798) (hne : i≠j) : w i≠w j := by
    intro he
    exact hne (skywalkPool_index_inj w hn i j hi hj he)
  simp only [wireList,actualPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals exact neq _ _ (by decide) (by decide) (by decide)

private theorem prefix_high_clean52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (clean : highCarryClean52 w s.basis) :
    Clean (actualPorts w) (prefixState52 w s).basis := by
  have h0 := lowPrefix_keeps_pool52 w hn 1794 (Or.inr (Or.inr ⟨by decide,by decide⟩)) s []
  have h1 := lowPrefix_keeps_pool52 w hn 1795 (Or.inr (Or.inr ⟨by decide,by decide⟩)) s []
  have h2 := lowPrefix_keeps_pool52 w hn 1796 (Or.inr (Or.inr ⟨by decide,by decide⟩)) s []
  change (prefixState52 w s).basis (w 1794)=false ∧
    (prefixState52 w s).basis (w 1795)=false ∧ (prefixState52 w s).basis (w 1796)=false
  exact ⟨h0.trans clean.1,h1.trans clean.2.1,h2.trans clean.2.2⟩

private theorem prefix_flag52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (par : Bool) (flagIn : s.basis (w 1028)=par) :
    (prefixState52 w s).basis (w 1028)=par := by
  exact (lowPrefix_keeps_pool52 w hn 1028 (Or.inr (Or.inl ⟨by decide,by decide⟩)) s []).trans flagIn

/-- The measured low unwind has no high-b support, so OLD full output at[]
is exactly the old four-bit tail output after the actual low prefix. -/
private theorem literal_high_output52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (j : Nat) (hj : 255 ≤ j ∧ j < 258) :
    (run (literalKAdd w) [] s).basis (w (770+j))=
      (run (oldTail (actualPorts w)) [] (prefixState52 w s)).basis (w (770+j)) := by
  rw [old_normal_form52 w s []]
  simpa only [List.drop_nil] using lowSuffix_keeps_high_sum52 w hn j hj
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) []

/-- Normalize an index with abstract State variables, not a concrete258 run. -/
private theorem bit_index52 (w : Nat → Wire) (u v : State) (j k : Nat)
    (hk : 770+j=k)
    (h : u.basis (w (770+j))=v.basis (w (770+j))) :
    u.basis (w k)=v.basis (w k) := by
  simpa only [hk] using h

private theorem forward_code52 (u v : State) (p : Ports) (q1 q2 q3 : Wire) (par : Bool)
    (p1 : p.b1=q1) (p2 : p.b2=q2) (p3 : p.b3=q3)
    (b1 : u.basis q1=v.basis q1) (b2 : u.basis q2=v.basis q2) (b3 : u.basis q3=v.basis q3)
    (promise : u.basis q3=par ∧ ((u.basis q2 ^^ u.basis q1)=!par)) :
    v.basis p.b3=par ∧ ((v.basis p.b2 ^^ v.basis p.b1)=!par) := by
  rw [p1,p2,p3]
  exact ⟨b3.symm.trans promise.1,
    (congrArg₂ (fun a b : Bool => a^^b) b2.symm b1.symm).trans promise.2⟩

private theorem exit_code52 (u v : State) (p : Ports) (q1 q2 q3 : Wire)
    (p1 : p.b1=q1) (p2 : p.b2=q2) (p3 : p.b3=q3)
    (b1 : u.basis q1=v.basis q1) (b2 : u.basis q2=v.basis q2) (b3 : u.basis q3=v.basis q3)
    (promise : u.basis q1=false ∧ u.basis q2=false ∧ u.basis q3=false) :
    v.basis p.b1=false ∧ v.basis p.b2=false ∧ v.basis p.b3=false := by
  rw [p1,p2,p3]
  exact ⟨b1.symm.trans promise.1,b2.symm.trans promise.2.1,b3.symm.trans promise.2.2⟩

private theorem forward_promise_after_prefix52 (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (par : Bool)
    (promise : ForwardOldOutputs52 w par s) :
    ForwardPromise (actualPorts w) par (prefixState52 w s) := by
  have b1 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 255 1025 rfl
    (literal_high_output52 w hn s 255 ⟨by decide,by decide⟩)
  have b2 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 256 1026 rfl
    (literal_high_output52 w hn s 256 ⟨by decide,by decide⟩)
  have b3 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 257 1027 rfl
    (literal_high_output52 w hn s 257 ⟨by decide,by decide⟩)
  exact forward_code52 (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s))
    (actualPorts w) (w 1025) (w 1026) (w 1027) par rfl rfl rfl b1 b2 b3 promise

private theorem exit_promise_after_prefix52 (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (promise : ExitOldOutputs52 w s) :
    ExitPromise (actualPorts w) (prefixState52 w s) := by
  have b1 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 255 1025 rfl
    (literal_high_output52 w hn s 255 ⟨by decide,by decide⟩)
  have b2 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 256 1026 rfl
    (literal_high_output52 w hn s 256 ⟨by decide,by decide⟩)
  have b3 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 257 1027 rfl
    (literal_high_output52 w hn s 257 ⟨by decide,by decide⟩)
  exact exit_code52 (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s))
    (actualPorts w) (w 1025) (w 1026) (w 1027) rfl rfl rfl b1 b2 b3 promise

/-- Complete actual258 program State equality, for every full/short/empty tape.
Only the high three initially-clean carry bits and the actual OLD output code
are required; every low carry may have an arbitrary initial value. -/
theorem flag_run_eq52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (clean : highCarryClean52 w s.basis)
    (par : Bool) (flagIn : s.basis (w 1028)=par) (promise : ForwardOldOutputs52 w par s) :
    run (flagKAdd52 w) m s=run (literalKAdd w) m s := by
  have localEq := forward_tail_eq_old (actualPorts w) (w 1028) (tail_nd13_pool52 w hn)
    (prefixState52 w s) (prefix_high_clean52 w hn s clean) par
    (prefix_flag52 w hn s par flagIn) (forward_promise_after_prefix52 w hn s par promise) m
  rw [flag_normal_form52 w s m,old_normal_form52 w s m]
  exact congrArg (fun t => run (lowSuffix52 w) (m.drop 3) t) localEq

theorem zero_run_eq52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (clean : highCarryClean52 w s.basis)
    (promise : ExitOldOutputs52 w s) :
    run (zeroKAdd52 w) m s=run (literalKAdd w) m s := by
  have nd12 := (List.nodup_cons.mp (tail_nd13_pool52 w hn)).2
  have localEq := exit_tail_eq_old (actualPorts w) nd12 (prefixState52 w s)
    (prefix_high_clean52 w hn s clean) (exit_promise_after_prefix52 w hn s promise) m
  rw [zero_normal_form52 w s m,old_normal_form52 w s m]
  exact congrArg (fun t => run (lowSuffix52 w) (m.drop 3) t) localEq

private theorem splice_counts52 (p old new r : Program) (dt ds : Nat)
    (ht : toffoliCount new+dt=toffoliCount old)
    (hm : measurementCount new=measurementCount old)
    (hs : gateSlots new+ds=gateSlots old) :
    toffoliCount (p++new++r)+dt=toffoliCount (p++old++r) ∧
    measurementCount (p++new++r)=measurementCount (p++old++r) ∧
    gateSlots (p++new++r)+ds=gateSlots (p++old++r) := by
  refine ⟨?_,?_,?_⟩
  · simp only [toffoliCount_append]
    omega
  · simp only [measurementCount_append]
    omega
  · simp only [gateSlots_append]
    omega

private theorem flag_tail_deltas52 (p : Ports) (flag : Wire) :
    toffoliCount (forwardTail p flag)+2=toffoliCount (oldTail p) ∧
    measurementCount (forwardTail p flag)=measurementCount (oldTail p) ∧
    gateSlots (forwardTail p flag)+2=gateSlots (oldTail p) := by
  have old := old_costs p
  have new := forward_costs p flag
  refine ⟨?_,?_,?_⟩
  · rw [new.1,old.1]
  · exact new.2.1.trans old.2.1.symm
  · rw [new.2.2,old.2.2]

private theorem zero_tail_deltas52 (p : Ports) :
    toffoliCount (exitTail p)+3=toffoliCount (oldTail p) ∧
    measurementCount (exitTail p)=measurementCount (oldTail p) ∧
    gateSlots (exitTail p)+12=gateSlots (oldTail p) := by
  have old := old_costs p
  have new := exit_costs p
  refine ⟨?_,?_,?_⟩
  · rw [new.1,old.1]
  · exact new.2.1.trans old.2.1.symm
  · rw [new.2.2,old.2.2]

/-- Exact whole-adder syntax deltas; these do not assert a caller/candidate score. -/
theorem flag_counts52 (w : Nat → Wire) :
    toffoliCount (flagKAdd52 w)+2=toffoliCount (literalKAdd w) ∧
    measurementCount (flagKAdd52 w)=measurementCount (literalKAdd w) ∧
    gateSlots (flagKAdd52 w)+2=gateSlots (literalKAdd w) := by
  have delta := flag_tail_deltas52 (actualPorts w) (w 1028)
  have h := splice_counts52 (lowPrefix52 w) (oldTail (actualPorts w))
    (forwardTail (actualPorts w) (w 1028)) (lowSuffix52 w) 2 2 delta.1 delta.2.1 delta.2.2
  exact ⟨h.1.trans (congrArg toffoliCount (literal_split_four52 w)).symm,
    h.2.1.trans (congrArg measurementCount (literal_split_four52 w)).symm,
    h.2.2.trans (congrArg gateSlots (literal_split_four52 w)).symm⟩

theorem zero_counts52 (w : Nat → Wire) :
    toffoliCount (zeroKAdd52 w)+3=toffoliCount (literalKAdd w) ∧
    measurementCount (zeroKAdd52 w)=measurementCount (literalKAdd w) ∧
    gateSlots (zeroKAdd52 w)+12=gateSlots (literalKAdd w) := by
  have delta := zero_tail_deltas52 (actualPorts w)
  have h := splice_counts52 (lowPrefix52 w) (oldTail (actualPorts w))
    (exitTail (actualPorts w)) (lowSuffix52 w) 3 12 delta.1 delta.2.1 delta.2.2
  exact ⟨h.1.trans (congrArg toffoliCount (literal_split_four52 w)).symm,
    h.2.1.trans (congrArg measurementCount (literal_split_four52 w)).symm,
    h.2.2.trans (congrArg gateSlots (literal_split_four52 w)).symm⟩

#print axioms flag_run_eq52
#print axioms zero_run_eq52
#print axioms flag_counts52
#print axioms zero_counts52
end ECDSAAdd.Entrant.E1WholeKAdd52Research

-- Reused source module: E1ResourceBridge52Draft

/-! SOURCE-ONLY resource transport for the actual four-bit tail52 splice.
This file has not been compiled or replayed. It leaves every imported ancestor
unchanged and keeps the254-bit prefix/suffix opaque. The three descending
measurements are retained. No qubit-retirement or whole-candidate claim. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1ResourceBridge52Research
open Arithmetic RecordedQuantum Challenge
open KAddCallerBridgeResearch AffineCarryTail52Research
open E1CarrySplice52Research E1WholeKAdd52Research

attribute [local irreducible] ECDSAAdd.wires

/-- Only the finite old four-bit tail is unfolded. Its12 ports all remain live. -/
theorem old_tail_support52 (p : Ports) :
    wires (oldTail p)=(wireList p).toFinset := by
  ext q
  simp [oldTail,oldPrefix,commonSuffix,majority,eraseCarry,wireList,
    wires,Instr.wires,correctionWires,or_assoc,or_left_comm,or_comm]

/-- The forward tail adds only the actual parity flag; all three carry
measurement targets still occur in commonSuffix. No alias premise is needed. -/
theorem forward_tail_support52 (p : Ports) (flag : Wire) :
    wires (forwardTail p flag)=(wireList p).toFinset ∪ {flag} := by
  ext q
  simp [forwardTail,forwardPrefix,clone255,clone256,commonSuffix,
    majority,eraseCarry,wireList,wires,Instr.wires,correctionWires,
    or_assoc,or_left_comm,or_comm]

theorem exit_tail_support52 (p : Ports) :
    wires (exitTail p)=(wireList p).toFinset := by
  ext q
  simp [exitTail,exitPrefix,commonSuffix,eraseCarry,wireList,
    wires,Instr.wires,correctionWires,or_assoc,or_left_comm,or_comm]

private theorem splice_support52 (pre old new post : Program) (extra : Finset Wire)
    (localSupport : wires new ⊆ wires old ∪ extra) :
    wires (pre++new++post) ⊆ wires (pre++old++post) ∪ extra := by
  simp only [wires_append]
  intro q h
  rcases Finset.mem_union.mp h with hLeft | hPost
  · rcases Finset.mem_union.mp hLeft with hPre | hNew
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hPre))
    · rcases Finset.mem_union.mp (localSupport hNew) with hOld | hExtra
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_right _ hOld))
      · exact Finset.mem_union_right _ hExtra
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hPost)

/-- Whole-program support needs no pool injectivity or arithmetic promise. -/
theorem flag_support52 (w : Nat → Wire) :
    wires (flagKAdd52 w) ⊆ wires (literalKAdd w) ∪ {w 1028} := by
  have localSupport : wires (forwardTail (actualPorts w) (w 1028)) ⊆
      wires (oldTail (actualPorts w)) ∪ {w 1028} := by
    rw [forward_tail_support52,old_tail_support52]
  have h := splice_support52 (lowPrefix52 w) (oldTail (actualPorts w))
    (forwardTail (actualPorts w) (w 1028)) (lowSuffix52 w) {w 1028} localSupport
  exact (congrArg (fun s : Finset Wire => wires (flagKAdd52 w) ⊆ s ∪ {w 1028})
    (congrArg ECDSAAdd.wires (literal_split_four52 w))).mpr h

theorem zero_support52 (w : Nat → Wire) :
    wires (zeroKAdd52 w) ⊆ wires (literalKAdd w) := by
  have localSupport : wires (exitTail (actualPorts w)) ⊆
      wires (oldTail (actualPorts w)) ∪ (∅ : Finset Wire) := by
    rw [exit_tail_support52,old_tail_support52,Finset.union_empty]
  have h := splice_support52 (lowPrefix52 w) (oldTail (actualPorts w))
    (exitTail (actualPorts w)) (lowSuffix52 w) ∅ localSupport
  have hs : wires (zeroKAdd52 w) ⊆
      wires (lowPrefix52 w++oldTail (actualPorts w)++lowSuffix52 w) := by
    simpa only [Finset.union_empty] using h
  exact (congrArg (fun s : Finset Wire => wires (zeroKAdd52 w) ⊆ s)
    (congrArg ECDSAAdd.wires (literal_split_four52 w))).mpr hs

/-- Strong Contract validity checks distinct CCX controls and each CZ in
both correction branches. Only the finite12-port old tail is unfolded. -/
theorem old_tail_contract_valid52 (p : Ports) (nd : (wireList p).Nodup) :
    ∀ i ∈ oldTail p, instructionValid i := by
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
  simp_all [oldTail,oldPrefix,commonSuffix,majority,eraseCarry,
    instructionValid,correctionValid,ne_comm]

/-- The only extra finite distinctness requirement is flag versus the12
actual ports. No global injectivity of the placement is assumed. -/
theorem forward_tail_contract_valid52 (p : Ports) (flag : Wire)
    (nd : (flag::wireList p).Nodup) :
    ∀ i ∈ forwardTail p flag, instructionValid i := by
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
  simp_all [forwardTail,forwardPrefix,clone255,clone256,commonSuffix,
    majority,eraseCarry,instructionValid,correctionValid,ne_comm]

theorem exit_tail_contract_valid52 (p : Ports) (nd : (wireList p).Nodup) :
    ∀ i ∈ exitTail p, instructionValid i := by
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
  simp_all [exitTail,exitPrefix,commonSuffix,eraseCarry,
    instructionValid,correctionValid,ne_comm]

/-- Strong-to-weak is valid. The opposite implication is deliberately absent:
GatePhysical admits measurements without checking their CZ correction lists. -/
private theorem instruction_physical52 (i : Instr) (h : instructionValid i) :
    PhysicalInstr (.gate i) := by
  cases i <;> simp_all [instructionValid,PhysicalInstr,ProperGate]

private theorem program_physical52 (p : Program)
    (h : ∀ i ∈ p, instructionValid i) : GatePhysical p := by
  intro i hi
  exact instruction_physical52 i (h i hi)

theorem old_tail_gatePhysical52 (p : Ports) (nd : (wireList p).Nodup) :
    GatePhysical (oldTail p) :=
  program_physical52 _ (old_tail_contract_valid52 p nd)

theorem forward_tail_gatePhysical52 (p : Ports) (flag : Wire)
    (nd : (flag::wireList p).Nodup) : GatePhysical (forwardTail p flag) :=
  program_physical52 _ (forward_tail_contract_valid52 p flag nd)

theorem exit_tail_gatePhysical52 (p : Ports) (nd : (wireList p).Nodup) :
    GatePhysical (exitTail p) :=
  program_physical52 _ (exit_tail_contract_valid52 p nd)

/-- Pointwise transport extracts unchanged prefix/suffix obligations from
exactly the old property V. It never unfolds either254-bit list. -/
private theorem splice_valid52 (V : Instr → Prop) (pre old new post : Program)
    (oldValid : ∀ i ∈ pre++old++post, V i)
    (newValid : ∀ i ∈ new, V i) : ∀ i ∈ pre++new++post, V i := by
  intro i hi
  rcases List.mem_append.mp hi with hLeft | hPost
  · rcases List.mem_append.mp hLeft with hPre | hNew
    · exact oldValid i (List.mem_append_left post (List.mem_append_left old hPre))
    · exact newValid i hNew
  · exact oldValid i (List.mem_append_right (pre++old) hPost)

/-- The whole weak property is inherited only as a weak property. -/
theorem flag_gatePhysical52 (w : Nat → Wire)
    (nd : ((w 1028)::wireList (actualPorts w)).Nodup)
    (oldPhysical : GatePhysical (literalKAdd w)) : GatePhysical (flagKAdd52 w) := by
  have old := (congrArg GatePhysical (literal_split_four52 w)).mp oldPhysical
  exact splice_valid52 (fun i => PhysicalInstr (.gate i)) (lowPrefix52 w)
    (oldTail (actualPorts w)) (forwardTail (actualPorts w) (w 1028)) (lowSuffix52 w)
    old (forward_tail_gatePhysical52 (actualPorts w) (w 1028) nd)

theorem zero_gatePhysical52 (w : Nat → Wire)
    (nd : (wireList (actualPorts w)).Nodup)
    (oldPhysical : GatePhysical (literalKAdd w)) : GatePhysical (zeroKAdd52 w) := by
  have old := (congrArg GatePhysical (literal_split_four52 w)).mp oldPhysical
  exact splice_valid52 (fun i => PhysicalInstr (.gate i)) (lowPrefix52 w)
    (oldTail (actualPorts w)) (exitTail (actualPorts w)) (lowSuffix52 w)
    old (exit_tail_gatePhysical52 (actualPorts w) nd)

/-- Strong whole-program validity requires an OLD STRONG premise. The weak
GatePhysical premise from the preceding theorems cannot replace this premise. -/
theorem flag_contract_valid52 (w : Nat → Wire)
    (nd : ((w 1028)::wireList (actualPorts w)).Nodup)
    (oldValid : ∀ i ∈ literalKAdd w, instructionValid i) :
    ∀ i ∈ flagKAdd52 w, instructionValid i := by
  have old := (congrArg (fun p : Program => ∀ i ∈ p, instructionValid i)
    (literal_split_four52 w)).mp oldValid
  exact splice_valid52 instructionValid (lowPrefix52 w) (oldTail (actualPorts w))
    (forwardTail (actualPorts w) (w 1028)) (lowSuffix52 w) old
    (forward_tail_contract_valid52 (actualPorts w) (w 1028) nd)

theorem zero_contract_valid52 (w : Nat → Wire)
    (nd : (wireList (actualPorts w)).Nodup)
    (oldValid : ∀ i ∈ literalKAdd w, instructionValid i) :
    ∀ i ∈ zeroKAdd52 w, instructionValid i := by
  have old := (congrArg (fun p : Program => ∀ i ∈ p, instructionValid i)
    (literal_split_four52 w)).mp oldValid
  exact splice_valid52 instructionValid (lowPrefix52 w) (oldTail (actualPorts w))
    (exitTail (actualPorts w)) (lowSuffix52 w) old
    (exit_tail_contract_valid52 (actualPorts w) nd)

/-- Pool-level convenience uses bounded index injectivity only at these13
indices; it is independent of the private whole-adder nodup helper. -/
theorem actual_flag_ports_nodup52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    ((w 1028)::wireList (actualPorts w)).Nodup := by
  have neq (i j : Nat) (hi : i < 1798) (hj : j < 1798) (hne : i≠j) : w i≠w j := by
    intro he
    exact hne (skywalkPool_index_inj w hn i j hi hj he)
  simp only [wireList,actualPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals exact neq _ _ (by decide) (by decide) (by decide)

theorem actual_ports_nodup52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    (wireList (actualPorts w)).Nodup :=
  (List.nodup_cons.mp (actual_flag_ports_nodup52 w hn)).2

theorem flag_gatePhysical_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (oldPhysical : GatePhysical (literalKAdd w)) : GatePhysical (flagKAdd52 w) :=
  flag_gatePhysical52 w (actual_flag_ports_nodup52 w hn) oldPhysical

theorem zero_gatePhysical_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (oldPhysical : GatePhysical (literalKAdd w)) : GatePhysical (zeroKAdd52 w) :=
  zero_gatePhysical52 w (actual_ports_nodup52 w hn) oldPhysical

theorem flag_contract_valid_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (oldValid : ∀ i ∈ literalKAdd w, instructionValid i) :
    ∀ i ∈ flagKAdd52 w, instructionValid i :=
  flag_contract_valid52 w (actual_flag_ports_nodup52 w hn) oldValid

theorem zero_contract_valid_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (oldValid : ∀ i ∈ literalKAdd w, instructionValid i) :
    ∀ i ∈ zeroKAdd52 w, instructionValid i :=
  zero_contract_valid52 w (actual_ports_nodup52 w hn) oldValid

#print axioms flag_support52
#print axioms zero_support52
#print axioms forward_tail_contract_valid52
#print axioms exit_tail_contract_valid52
#print axioms flag_gatePhysical52
#print axioms zero_gatePhysical52
#print axioms flag_contract_valid52
#print axioms zero_contract_valid52
end ECDSAAdd.Entrant.E1ResourceBridge52Research

-- Reused source module: E1CallerAffineFacts52

/-! SOURCE ONLY in this independent import context. Existing39 ValueFacts remains
byte-identical. The new proof bodies are copied from separately qualified v7. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.E1CallerValueFactsResearch
open Arithmetic NativeFirstDirect

/-- SOURCE DRAFT 52: the actual canonical caller fixes the top three-bit word.
The odd branch still needs the real parity premise; par=true,D=p-1 would wrap. -/
theorem Kword_high_div255 (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool)
    (hp : par=decide (D%2=1)) :
    (par=false → (Kword D par)/2^255=1 ∨ (Kword D par)/2^255=2) ∧
      (par=true → (Kword D par)/2^255=7) := by
  cases par <;> norm_num [Kword,kConstant,ECDSAAdd.p] at * <;> omega

private theorem testBit_of_quotient_flag52 (N i : Nat) (flag : Bool)
    (h : N/2^i=flag.toNat) : N.testBit i=flag := by
  rw [Nat.testBit_eq_decide_div_mod_eq,h]
  cases flag <;> decide

/-- SOURCE DRAFT 52: only the two affine relations needed by the forward tail.
This states a Nat/Bool value fact, not a physical-port or program equivalence. -/
theorem Kword_top_affine (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool)
    (hp : par=decide (D%2=1)) :
    (Kword D par).testBit 257=par ∧
      ((Kword D par).testBit 256 ^^ (Kword D par).testBit 255)=(!par) := by
  have high := Kword_high_div D hD par hp
  have high257 : (Kword D par)/2^257=par.toNat := high.2.1
  have top3 := Kword_high_div255 D hD par hp
  have div256 : (Kword D par)/2^256=((Kword D par)/2^255)/2 := by
    norm_num [Nat.div_div_eq_div_mul]
  refine ⟨?_,?_⟩
  · exact testBit_of_quotient_flag52 (Kword D par) 257 par high257
  · rcases top3 with ⟨evenTop,oddTop⟩
    cases par with
    | false =>
        rcases evenTop rfl with h | h
        · (simp only [Nat.testBit_eq_decide_div_mod_eq,div256,h]; decide)
        · (simp only [Nat.testBit_eq_decide_div_mod_eq,div256,h]; decide)
    | true =>
        have h := oddTop rfl
        (simp only [Nat.testBit_eq_decide_div_mod_eq,div256,h]; decide)

end ECDSAAdd.Entrant.E1CallerValueFactsResearch

-- Reused source module: E1ActualMF52Draft

/-! SOURCE ONLY: ordinary E1Merge actual-MF semantic wrappers for tail52.
No caller instantiation, resource propagation, strong physicality, or candidate
qualification is asserted. H/X are the real MF register values, not D/2 aliases. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.ActualMF52Research
open Arithmetic RecordedQuantum KAddCallerBridgeResearch
open E1CallerValueFactsResearch E1WholeKAdd52Research

-- Use named interpreter/register lemmas; never unfold258 gates or a258-bit fold.
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.regValue

theorem kAdd_literal52 (w : Nat → Wire) : E1Merge.kAddM w=literalKAdd w := by rfl

private theorem carry_clean_at52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (s : BasisState)
    (hs : E1Merge.MF w b0 H X T par f gp fp s)
    (i : Nat) (hi : 1794 ≤ i ∧ i < 1797) : s (w i)=false := by
  have away : w i∉E1Merge.mutL w := by
    simp only [E1Merge.mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨E1Merge.nb w hn i 0 258 (by omega) (by omega) (by omega),
      E1Merge.nb w hn i 770 258 (by omega) (by omega) (by omega)⟩,
      E1Merge.nb w hn i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩
    all_goals exact E1Merge.w_ne w hn _ _ (by omega) (by omega) (by omega)
  have member : w i∈E1Merge.aC w := by
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [List.mem_range'_1]
    omega
  exact (hs.2.2.2.2.2.2.2 _ away).trans (hc _ member)

/-- The three new clean inputs are derived from the OLD MF frame and bank premise. -/
theorem highCarryClean_from_MF52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (s : BasisState)
    (hs : E1Merge.MF w b0 H X T par f gp fp s) : highCarryClean52 w s := by
  change s (w 1794)=false ∧ s (w 1795)=false ∧ s (w 1796)=false
  exact ⟨carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1794 ⟨by decide,by decide⟩,
    carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1795 ⟨by decide,by decide⟩,
    carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1796 ⟨by decide,by decide⟩⟩

private theorem register_get_bit52 (r : List Wire) (b : BasisState) (j : Nat)
    (hj : j<r.length) : b (r.getD j 0)=(regValue r b).testBit j := by
  have h := regValue_bit r j 0 b hj
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases hb : b (r.getD j 0) <;>
    simp only [hb,Bool.toNat_false,Bool.toNat_true] at h ⊢ <;> simp [←h]

private theorem block_getD52 (w : Nat → Wire) (start count j : Nat) (hj : j<count) :
    (wireBlock w start count).getD j 0=w (start+j) := by
  simp [wireBlock,List.getD_eq_getElem?_getD,hj]

/-- Generic index keeps every division/testBit rewrite symbolic, including at257. -/
private theorem postWord_bit52 (w : Nat → Wire) (b : BasisState) (W : Nat)
    (postWord : regValue (wireBlock w 770 258) b=W) (j : Nat) (hj : j<258) :
    b (w (770+j))=W.testBit j := by
  have h := register_get_bit52 (wireBlock w 770 258) b j
    (by simpa only [wireBlock_length] using hj)
  rw [block_getD52 w 770 258 j hj] at h
  exact h.trans (congrArg (fun n : Nat => n.testBit j) postWord)

/-- All port/index conversions happen while the basis parameter is abstract. -/
private theorem forward_bits_from_postWord52 (w : Nat → Wire) (b : BasisState)
    (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool) (hp : par=decide (D%2=1))
    (postWord : regValue (wireBlock w 770 258) b=Kword D par) :
    b (w 1027)=par ∧ (b (w 1026) ^^ b (w 1025))=!par := by
  have b1 := postWord_bit52 w b (Kword D par) postWord 255 (by decide)
  have b2 := postWord_bit52 w b (Kword D par) postWord 256 (by decide)
  have b3 := postWord_bit52 w b (Kword D par) postWord 257 (by decide)
  have facts := Kword_top_affine D hD par hp
  exact ⟨b3.trans facts.1,(congrArg₂ (fun a c : Bool => a^^c) b2 b1).trans facts.2⟩

private theorem exit_bits_from_postWord52 (w : Nat → Wire) (b : BasisState)
    (Y : Nat) (hY : Y<ECDSAAdd.p)
    (postWord : regValue (wireBlock w 770 258) b=Y/2) :
    b (w 1025)=false ∧ b (w 1026)=false ∧ b (w 1027)=false := by
  have b1 := postWord_bit52 w b (Y/2) postWord 255 (by decide)
  have b2 := postWord_bit52 w b (Y/2) postWord 256 (by decide)
  have b3 := postWord_bit52 w b (Y/2) postWord 257 (by decide)
  have facts := E1CallerValueFactsResearch.exit_top3 Y hY
  exact ⟨b1.trans facts.1,b2.trans facts.2.1,b3.trans facts.2.2⟩

/-- Promise uses the actual OLD complete run and the actual canonical D/parity. -/
theorem forward_outputs_from_postWord52 (w : Nat → Wire) (s : State)
    (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool) (hp : par=decide (D%2=1))
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Kword D par) :
    ForwardOldOutputs52 w par s := by
  exact forward_bits_from_postWord52 w (run (literalKAdd w) [] s).basis D hD par hp postWord

/-- Exit needs the real old Y/2 word and Y<p; no arbitrary intermediate is canonical. -/
theorem exit_outputs_from_postWord52 (w : Nat → Wire) (s : State)
    (Y : Nat) (hY : Y<ECDSAAdd.p)
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Y/2) :
    ExitOldOutputs52 w s := by
  exact exit_bits_from_postWord52 w (run (literalKAdd w) [] s).basis Y hY postWord

/-- Ordinary actual MF Triple, transported from the ORIGINAL stepKAdd.
The caller must still prove its actual word and parity equations. -/
theorem stepKAddFlag52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (hcin : b0 (w 1797)=false)
    (D : Nat) (hD : D<ECDSAAdd.p) (hp : par=decide (D%2=1))
    (hWord : (H+X)%2^258=Kword D par) :
    Triple (E1Merge.MF w b0 H X T par f gp fp) (flagKAdd52 w)
      (E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m hs
  have old := E1Merge.stepKAdd w hn b0 H X T par f gp fp hc hcin
  rw [kAdd_literal52] at old
  have oldEmpty := old s [] hs
  have postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Kword D par :=
    oldEmpty.2.2.1.trans hWord
  have clean := highCarryClean_from_MF52 w hn b0 H X T par f gp fp hc s.basis hs
  have outputs := forward_outputs_from_postWord52 w s D hD par hp postWord
  have equal := flag_run_eq52 w hn s m clean par hs.2.2.2.1 outputs
  exact (congrArg (fun t : State => t.phase=s.phase ∧
    E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp t.basis) equal).mpr (old s m hs)

/-- Ordinary-MF exit wrapper. Actual exit arithmetic proving hWord and hY is still a caller task. -/
theorem stepKAddZero52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (hcin : b0 (w 1797)=false)
    (Y : Nat) (hY : Y<ECDSAAdd.p) (hWord : (H+X)%2^258=Y/2) :
    Triple (E1Merge.MF w b0 H X T par f gp fp) (zeroKAdd52 w)
      (E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m hs
  have old := E1Merge.stepKAdd w hn b0 H X T par f gp fp hc hcin
  rw [kAdd_literal52] at old
  have oldEmpty := old s [] hs
  have postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Y/2 :=
    oldEmpty.2.2.1.trans hWord
  have clean := highCarryClean_from_MF52 w hn b0 H X T par f gp fp hc s.basis hs
  have outputs := exit_outputs_from_postWord52 w s Y hY postWord
  have equal := zero_run_eq52 w hn s m clean outputs
  exact (congrArg (fun t : State => t.phase=s.phase ∧
    E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp t.basis) equal).mpr (old s m hs)

end ECDSAAdd.Entrant.ActualMF52Research

-- Reused source module: E1AffineEndpoints52Draft

/-! SOURCE-ONLY actual ordinary/exit endpoints. Old39 ancestors are unchanged.
Only the selected kAdd sites use the checked52 whole program and real ordinary MF bridge.
Proofs have not been elaborated in this new module; no reflected/global certificate claim. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1AffineEndpoints52Research
open Arithmetic NativeFirstDirect RecordedQuantum Challenge
open E1WholeKAdd52Research

attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

namespace Forward
open E1Merge

private def pre (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  comparePart w g k++(parGates w g k++rotateRight (kR w))++prodPart w g++loadK w g k

private def post (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  loadK w g k++[.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]

/-- The only runtime substitution is old39 flagKAdd → checked whole flagKAdd52. -/
def merged (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  pre w g k++flagKAdd52 w++post w g k

private theorem base_split (w : Nat → Wire) (g : Wire) (k : Nat) :
    E1Merge.merged w g k=pre w g k++KAddCallerBridgeResearch.flagKAdd w++post w g k := by
  simp only [E1Merge.merged,pre,post,List.append_assoc]

section Semantics
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

set_option exponentiation.threshold 400 in
private theorem merged_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let f := decide (2^256-1-(if G then 2^256-p+k else 0)<X)
    let dx := (X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    Triple (MF w b0 0 X 0 false false false false) (merged w g k)
      (MF w b0 (2*H+(!par).toNat) K 0 par false false false) := by
  intro G f dx par K H
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX G
  change decide (X%2=1)=E1Merge.x0 k G f par at a1
  change (X/2+tk k G f par)%2^258=K at a2
  change H=dx/2+(if par then hConstant else 0) at a3
  change f=decide (H<thr k G par) at a4
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hpar : (decide (X%2=1) ^^ (G && decide (k%2=1)) ^^ f)=par := by
    have e : decide (X%2=1)=E1Merge.x0 k G f par := a1
    rw [e]; unfold E1Merge.x0 E1Merge.ksel0
    generalize (G && decide (k%2=1))=a
    cases par <;> cases a <;> cases f <;> rfl
  have hfg : f=true → G=true := by
    intro hf; cases hG : G
    · have : f=false := by
        simp only [f,hG,Bool.false_eq_true,if_false,decide_eq_false_iff_not]; rw [p_val] at hX; omega
      rw [this] at hf; exact absurd hf (by simp)
    · rfl
  have fC : decide (2^256-1-(if b0 g then cmpC+k else 0)<X)=f := by simp [f,G,cmpC]
  have s1 := stepCompareMF w g hn b0 k X (by unfold cmpC; rw [p_val] at hk ⊢; omega) (by rw [p_val] at hX; omega)
    hc hcin (g_out w hn g hg 0 256 (by omega)) (g_ne w hn g hg 514 (by omega)) gm
  rw [fC] at s1
  have s2 := stepPar w g hn b0 k X f hg
  rw [show (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f)=par from hpar] at s2
  have s3 := stepRot w hn b0 X par f false false
  have s4a := stepCCX w hn b0 0 (X/2) 0 par f false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s4a
  have s4b := stepCCX w hn b0 0 (X/2) 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s4b
  have s5 := stepLoadK w g hn b0 k 0 (X/2) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkv_eq k G f par hfg] at s5
  have kWord : (tk k G f par+X/2)%2^258=K := by rw [Nat.add_comm]; exact a2
  have s6 := ActualMF52Research.stepKAddFlag52 w hn b0 (tk k G f par) (X/2) 0 par f (G && par) (f && par) hac h1797
    dx (Nat.mod_lt _ (by rw [p_val]; norm_num)) rfl (by exact kWord)
  rw [kWord] at s6
  have s7 := stepLoadK w g hn b0 k (tk k G f par) K 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkv_eq k G f par hfg,Nat.xor_self] at s7
  have s8 := stepMeasFp w hn b0 0 K 0 par f (G && par)
  have s9 := stepCopy w hn b0 K 0 par f (G && par) false
  have hHlt : 2*H+(!par).toNat<2^257 := by
    have dxl : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
    rw [a3]; rw [p_val] at dxl
    cases par <;>
      simp only [hC_val,Bool.not_true,Bool.not_false,Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,if_true,if_false] <;>
      omega
  have hH10 : (delta par+K%2^257)%2^257<2^256 := by
    rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]]
    have h2 := hHlt
    have h3 := Bool.toNat_le (!par)
    rw [show (2:Nat)^257=2*2^256 by exact (Nat.pow_succ 2 256).trans (Nat.mul_comm _ _)] at h2
    omega
  have s10 := stepHAddT w hn b0 (K%2^257) K 0 par f (G && par) false (Nat.mod_lt _ (by positivity)) hac h1797 hH10
  rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]] at s10
  have s11 := stepW0 w hn b0 H K 0 par f (G && par) false
  have s12 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K 0 hk par f (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltv_eq] at s12
  have s13 := stepErase w hn b0 (2*H+(!par).toNat) K (thr k G par) par f (G && par) false hac h1797 hHlt
    (by rw [show (2*H+(!par).toNat)/2=H by cases par <;> simp; omega]; exact a4)
  have s14 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K (thr k G par) hk par false (G && par) false hg
  rw [show b0 g=G from rfl,ltv_eq,Nat.xor_self] at s14
  have s15 := stepMeasGp w g hn b0 (2*H+(!par).toNat) K 0 par false false gm (g_ne w hn g hg 721 (by omega))
  have t := s1.seq (s2.seq (s3.seq (s4a.seq (s4b.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq (s13.seq (s14.seq s15))))))))))))))
  unfold merged pre post prodPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

theorem merged_eq_forward (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (t u : State) (m m' : List Bool)
    (tk0 : regValue (kR w) t.basis=X) (th0 : regValue (hR w) t.basis=0) (tt0 : regValue (tR w) t.basis=0)
    (t1028 : t.basis (w 1028)=false) (t514 : t.basis (w 514)=false) (t515 : t.basis (w 721)=false)
    (t516 : t.basis (w 722)=false)
    (hc : ∀ i, 258 ≤ i → i < 512 → t.basis (w i) = false) (hcin : t.basis (w 513)=false)
    (hac : ∀q∈aC w,t.basis q=false) (h1797 : t.basis (w 1797)=false)
    (hu : u.phase=t.phase) (hu2 : ∀q,q∉kR w → u.basis q=t.basis q)
    (hu3 : regValue (kR w) u.basis=(X+(if t.basis g then k else 0))%p) :
    run (merged w g k) m t=run (NativeFirstDirect.forward w) m' u := by
  have mf0 : MF w t.basis 0 X 0 false false false false t.basis :=
    ⟨th0,tk0,tt0,t1028,t514,t515,t516,fun _ _ => rfl⟩
  have tri := merged_triple w g hn hg k hk t.basis X hX hc hcin hac h1797 t m mf0
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX (t.basis g)
  generalize hG : t.basis g=G at tri a1 a2 a3 a4 a5 hu3
  generalize hdx : (X+(if G then k else 0))%p=dx at tri a1 a2 a3 a4 a5 hu3
  generalize hpar : decide (dx%2=1)=par at tri a1 a2 a3 a4 a5
  generalize hK : (dx/2+kConstant false par)%2^258=K at tri a1 a2 a3 a4 a5
  generalize hH : (K%2^257+delta par)%2^257=H at tri a1 a2 a3 a4 a5
  obtain ⟨lp,l1,l2,l3,l4,l5,l6,l7,l8⟩ := tri
  have dxlt : dx<p := by rw [←hdx]; exact Nat.mod_lt _ (by rw [p_val]; norm_num)
  have kh : ∀q∈hR w,q∉kR w := kR_hR w hn
  have kt : ∀q∈tR w,q∉kR w := kR_tR w hn
  have hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 dx u.basis := by
    constructor
    · change regValue (wireBlock w 0 258) u.basis=0
      rw [show wireBlock w 0 258=hR w from rfl,regValue_congr _ _ t.basis (fun q hq => hu2 q (kh q hq)),th0]
    · change regValue (wireBlock w 770 258) u.basis=dx
      exact hu3
    · change regValue (wireBlock w 1540 257) u.basis=0
      apply (regValue_zero _ _).mpr
      intro q hq
      rw [hu2 q (fun h' => List.disjoint_left.mp (blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)) h' hq)]
      exact hac q hq
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
    · change u.basis (w 1028)=false
      rw [hu2 _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact t1028
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec w hn dx dxlt u m' hin
  have e770 : u.basis (w 770)=par := by
    have sp := kR_split w hn u.basis
    rw [hu3] at sp
    rw [←hpar]
    cases hb : u.basis (w 770) <;> simp [hb] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  rw [hK] at zk
  have hv : 2*(dx/2+(if par then hConstant else 0))+(!par).toNat=2*H+(!par).toNat := by rw [a3]
  rw [hv] at zh
  apply State.extensionality
  · rw [lp,zp,hu]
  · funext q
    by_cases qh : q∈hR w
    · exact (regValue_eq_iff (hR w) _ _).mp (l1.trans zh.symm) q qh
    by_cases qk : q∈kR w
    · exact (regValue_eq_iff (kR w) _ _).mp (l2.trans zk.symm) q qk
    by_cases q1 : q=w 1028
    · rw [q1,l4,z1028]
    have nmut : q∉NativeFirstDirect.mutable w := by
      simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
      exact ⟨⟨fun h' => qh (blk_sub w 0 257 0 258 (by omega) (by omega) q h'),qk⟩,q1⟩
    rw [zrest q nmut,hu2 q qk]
    by_cases qt : q∈tR w
    · rw [(regValue_zero _ _).mp l3 q qt,(regValue_zero _ _).mp tt0 q qt]
    by_cases q4 : q=w 514
    · rw [q4,l5,t514]
    by_cases q5 : q=w 721
    · rw [q5,l6,t515]
    by_cases q6 : q=w 722
    · rw [q6,l7,t516]
    apply l8
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,qk⟩,qt⟩,q1,q4,q5,q6⟩

end Semantics

theorem merged_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (merged w g k)⊆(mSites w g).toFinset := by
  have B := blk_mSites w g
  have I := in_mSites w g
  have G := g_mSites w g
  have mskH (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have mskS (v : Nat) : wires (maskedConstant g (srcR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset g (srcR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 0 256 (by omega) q hq))
  have notS : wires (notRegister (srcR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]; exact lsub w g _ (B 0 256 (by omega))
  have cmp : wires (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (srcR w) (xR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,xR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 0 256 (by omega) q hq
    · exact B 770 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mSites w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mskS _,notS⟩,cmp⟩,notS⟩,mskS _⟩
  have cx (a b : Nat) (ha : a < 515 ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have hP : wires (parGates w g k)⊆(mSites w g).toFinset := by
    unfold parGates
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hR' : wires (rotateRight (kR w))⊆(mSites w g).toFinset := by
    rw [(rotate_wires (kR w)).1]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub w g _ (B 770 258 (by omega))
  have hPr : wires (prodPart w g)⊆(mSites w g).toFinset := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub <;> intro q hq <;>
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hL : wires (loadK w g k)⊆(mSites w g).toFinset := by
    simp only [loadK,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub w g _ (B 0 258 (by omega)))
  have hKOld : wires (kAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hK : wires (E1WholeKAdd52Research.flagKAdd52 w)⊆(mSites w g).toFinset := by
    apply (E1ResourceBridge52Research.flag_support52 w).trans
    simp only [Finset.union_subset_iff]
    constructor
    · simpa only [←kAdd_literal] using hKOld
    · intro q hq
      have eq : q=w 1028 := Finset.mem_singleton.mp hq
      rw [eq]
      exact List.mem_toFinset.mpr (I 1028 (by omega))
  have hM1 : wires [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hM2 : wires [.measureX (w 721) [] [.CZ g (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl
    · exact I _ (by omega)
    · exact G
    · exact I _ (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mSites w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hH : wires (hAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · rw [dBits_wire w q hq]; exact I 1028 (by omega)
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mSites w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hT : wires (loadT w g k)⊆(mSites w g).toFinset := by
    simp only [loadT,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have hE : wires (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hHT : wires (hAddT w)⊆(mSites w g).toFinset := (hAddT_wires w).trans hH
  simp only [merged,pre,post,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨hC,⟨hP,hR'⟩⟩,hPr⟩,hL⟩,hK⟩,⟨⟨⟨⟨⟨⟨⟨⟨hL,hM1⟩,hCp⟩,hHT⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩⟩

theorem merged_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (merged w g k)=1022 ∧ measurementCount (merged w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (srcR w)
  have c1' := compareLt_counts none (srcR w) (xR w) (cR w) (w 513) (w 514)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,xR,wireBlock_length])
  have r1 := rotate_counts (kR w)
  have k1 := mappedAdd_counts (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length])
  have h1 := mappedAdd_counts (dBits w) (hpR w) (hC2 w) (w 1797)
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length])
  have e1 := eraseLtChain_counts (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length])
  have cp1 := copyRegister_counts none (wireBlock w 770 257) (hpR w) (by simp [hpR,wireBlock_length])
  have pg : toffoliCount (parGates w g k)=0 ∧ measurementCount (parGates w g k)=0 := by
    unfold parGates; split_ifs <;> simp [toffoliCount,measurementCount]
  have lx : (xR w).length=256 := by simp [xR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  rw [lx] at c1'
  rw [lk] at k1
  have kOld : toffoliCount (KAddCallerBridgeResearch.literalKAdd w)=257 ∧
      measurementCount (KAddCallerBridgeResearch.literalKAdd w)=257 := k1
  have kDelta := E1WholeKAdd52Research.flag_counts52 w
  have kNew : toffoliCount (E1WholeKAdd52Research.flagKAdd52 w)=255 ∧
      measurementCount (E1WholeKAdd52Research.flagKAdd52 w)=257 := by omega
  rw [lh] at h1
  rw [lt] at e1
  have hT := hAddT_counts w
  rw [hAddM,h1.1,h1.2] at hT
  have hT' : toffoliCount (hAddT w)=254 ∧ measurementCount (hAddT w)=256 := by omega
  simp only [merged,pre,post,comparePart,prodPart,loadK,kNew.1,kNew.2,hT'.1,hT'.2,loadT,toffoliCount_append,
    measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,n1.1,n1.2,c1'.1,c1'.2.1,
    r1.1,r1.2.1,h1.1,h1.2,e1.1,e1.2,cp1.1,cp1.2,pg.1,pg.2]
  simp [toffoliCount,measurementCount]

section Phys
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_physical (k : Nat) : GatePhysical (merged w g k) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j := w_ne w hn i j hi hj h
  have gn (i : Nat) (hi : i<1798) : g≠w i := g_ne w hn g hg i hi
  have cxp (a b : Wire) (h : a≠b) : GatePhysical [.CX a b] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h]
  have ccxp (a b c : Wire) (h1 : a≠c) (h2 : b≠c) : GatePhysical [.CCX a b c] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h1,h2]
  have mp (c : Wire) (c' : Wire) : GatePhysical [.measureX c [] [.CZ c' c]] ∧
      GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by
    simp [GatePhysical,PhysicalInstr]
  have gS : g∉srcR w := g_out w hn g hg 0 256 (by omega)
  have gH : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have cmpP : GatePhysical (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
      have l1 : (srcR w++xR w).Nodup := List.nodup_append'.mpr ⟨src_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
      have l2 : (srcR w++xR w++cR w).Nodup := by
        apply List.nodup_append'.mpr
        refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
        apply List.disjoint_left.mpr
        intro q hq hc'
        rcases List.mem_append.mp hq with h1|h1
        · exact List.disjoint_left.mp a2 h1 hc'
        · exact List.disjoint_left.mp a3 h1 hc'
      simp only [List.cons_append,List.append_assoc] at l2 ⊢
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,by simpa [List.append_assoc] using l2⟩⟩
      · simp only [List.mem_cons,List.mem_append,not_or]
        exact ⟨ne 514 513 (by omega) (by omega) (by omega),nb w hn 514 0 256 (by omega) (by omega) (by omega),
          nb w hn 514 770 256 (by omega) (by omega) (by omega),nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 513 0 256 (by omega) (by omega) (by omega),nb w hn 513 770 256 (by omega) (by omega) (by omega),
          nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
    · simp
  have kPOld : GatePhysical (kAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      refine ⟨?_,?_,?_⟩
      · intro e; exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq')
      · exact fun h' => hR_kR w hn _ h' hq'
      · exact fun h' => List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq' h'
  have kP : GatePhysical (E1WholeKAdd52Research.flagKAdd52 w) :=
    E1ResourceBridge52Research.flag_gatePhysical_pool52 w hn (by simpa only [←kAdd_literal] using kPOld)
  have hP : GatePhysical (hAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      have : q∈mappedWires (dBits w) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [dBits_wire w q this,List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne 1028 1797 (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
        nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have eP : GatePhysical (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)) := by
    apply eraseLtChain_physical
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    rw [List.cons_append,List.cons_append]
    refine List.nodup_cons.mpr ⟨?_,l2⟩
    simp only [List.mem_append,not_or]
    exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cpP : GatePhysical (copyRegister none (wireBlock w 770 257) (hpR w)) :=
    copyRegister_physical none _ _ (List.nodup_append'.mpr ⟨blk_nd w hn 770 257 (by omega),
      blk_nd w hn 1 257 (by omega),blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩) (by simp)
  have parP : GatePhysical (parGates w g k) := by
    unfold parGates
    split_ifs <;> simp only [gatePhysical_append] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first
        | exact cxp _ _ (ne _ _ (by omega) (by omega) (by omega))
        | exact cxp _ _ (gn _ (by omega))
        | simp [GatePhysical]
  have rotP := (rotate_physical (kR w) (kR_nd w hn)).1
  have prodP : GatePhysical (prodPart w g) := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,gatePhysical_append]
    exact ⟨ccxp _ _ _ (gn _ (by omega)) (ne _ _ (by omega) (by omega) (by omega)),
      ccxp _ _ _ (ne _ _ (by omega) (by omega) (by omega)) (ne _ _ (by omega) (by omega) (by omega))⟩
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h1286 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h1287 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t1286 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  have lkP : GatePhysical (loadK w g k) := by
    simp only [loadK,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨xorConstant_physical _ _,maskedConstant_physical _ _ _ gH⟩,maskedConstant_physical _ _ _ h514⟩,
      maskedConstant_physical _ _ _ h1028⟩,maskedConstant_physical _ _ _ h1286⟩,maskedConstant_physical _ _ _ h1287⟩
  have ltP : GatePhysical (loadT w g k) := by
    simp only [loadT,gatePhysical_append]
    exact ⟨maskedConstant_physical _ _ _ gT,maskedConstant_physical _ _ _ t1286⟩
  have w0P : GatePhysical [.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,ne 1028 0 (by omega) (by omega) (by omega)]
  have cP : GatePhysical (comparePart w g k) := by
    simp only [comparePart,gatePhysical_append]
    exact ⟨⟨⟨⟨maskedConstant_physical _ _ _ gS,notRegister_physical _⟩,cmpP⟩,notRegister_physical _⟩,
      maskedConstant_physical _ _ _ gS⟩
  have m1 : GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have m2 : GatePhysical [.measureX (w 721) [] [.CZ g (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have hPT : GatePhysical (hAddT w) := hAddT_physical w hn hP
  simp only [merged,pre,post,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨cP,⟨parP,rotP⟩⟩,prodP⟩,lkP⟩,kP⟩,⟨⟨⟨⟨⟨⟨⟨⟨lkP,m1⟩,cpP⟩,hPT⟩,w0P⟩,ltP⟩,eP⟩,ltP⟩,m2⟩⟩

end Phys

theorem merged_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (merged w g k)≤25000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (srcR w) (xR w) (cR w) (w 513) (w 514)
  have r1 := (Baselines.rotate_gateSlots_le (kR w)).1
  have k1 := Baselines.mappedAdd_gateSlots_le (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
  have h1 := Baselines.mappedAdd_gateSlots_le (dBits w) (hpR w) (hC2 w) (w 1797)
  have e1 := Baselines.eraseLt_gateSlots_le (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
  have pg : Challenge.gateSlots (parGates w g k)≤6 := by
    unfold parGates; split_ifs <;> simp [Challenge.gateSlots,Challenge.instructionSlots]
  have pr : Challenge.gateSlots (prodPart w g)=2 := by simp [prodPart,Challenge.gateSlots,Challenge.instructionSlots]
  have w0 : Challenge.gateSlots [.CX (w 1028) (w 0),.X (w 0)]=2 := by simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q1 : Challenge.gateSlots [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q2 : Challenge.gateSlots [.measureX (w 721) [] [.CZ g (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have lK : Challenge.gateSlots (loadK w g k)≤6*258 := by
    simp only [loadK,Challenge.gateSlots_append]
    have := x1 (hR w) (c1 k); have := m1 g (hR w) (cg k); have := m1 (w 514) (hR w) (cf k)
    have := m1 (w 1028) (hR w) (cp k); have := m1 (w 721) (hR w) (cgp k); have := m1 (w 722) (hR w) (cfp k)
    simp only [hR,wireBlock_length] at *
    omega
  have lT : Challenge.gateSlots (loadT w g k)≤2*256 := by
    simp only [loadT,Challenge.gateSlots_append]
    have := m1 g (tR w) (thrA k); have := m1 (w 721) (tR w) (thrB k)
    simp only [tR,wireBlock_length] at *
    omega
  have cP : Challenge.gateSlots (comparePart w g k)≤4*256+12*256+4 := by
    simp only [comparePart,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
    have := m1 g (srcR w) (cmpC+k)
    simp only [srcR,xR,wireBlock_length] at *
    omega
  have cp : Challenge.gateSlots (copyRegister none (wireBlock w 770 257) (hpR w))=257 := by
    simp [hpR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hp8 w).length=256 := by simp [hp8,wireBlock_length]
  have lhR : (hR w).length=258 := by simp [hR,wireBlock_length]
  rw [lk] at r1
  rw [mappedRead_length,lhR] at k1
  have kOld : Challenge.gateSlots (KAddCallerBridgeResearch.literalKAdd w)≤17*258 := k1
  have kNew : Challenge.gateSlots (E1WholeKAdd52Research.flagKAdd52 w)+2≤17*258 := by
    rw [(E1WholeKAdd52Research.flag_counts52 w).2.2]
    exact kOld
  rw [dBits_length] at h1
  rw [lh] at e1
  have hS := hAddT_slots w
  rw [hAddM] at hS
  simp only [merged,pre,post,Challenge.gateSlots_append,pr,w0,q1,q2,cp]
  omega

end Forward

end ECDSAAdd.Entrant.E1AffineEndpoints52Research
