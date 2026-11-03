import ECDSAAdd.Submission.Entrant.HighOutputTailStructuredDraft
import ECDSAAdd.Submission.Entrant.AdderSpineBridgeDraft

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
