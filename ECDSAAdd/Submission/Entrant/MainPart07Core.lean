import ECDSAAdd.Submission.Entrant.TerminalGraph
import ECDSAAdd.Submission.Entrant.ExitMerge
import ECDSAAdd.Submission.Entrant.MainPart04


-- Consolidated source module: ForwardCarryAffine
section

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























/-- The only extra finite distinctness requirement is flag versus the12
actual ports. No global injectivity of the placement is assumed. -/
theorem forward_tail_contract_valid52 (p : Ports) (flag : Wire)
    (nd : (flag::wireList p).Nodup) :
    ∀ i ∈ forwardTail p flag, instructionValid i := by
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
  simp_all [forwardTail,forwardPrefix,clone255,clone256,commonSuffix,
    majority,eraseCarry,instructionValid,correctionValid,ne_comm]








/-- Strong-to-weak is valid. The opposite implication is deliberately absent:
GatePhysical admits measurements without checking their CZ correction lists. -/
private theorem instruction_physical52 (i : Instr) (h : instructionValid i) :
    PhysicalInstr (.gate i) := by
  cases i <;> simp_all [instructionValid,PhysicalInstr,ProperGate]

private theorem program_physical52 (p : Program)
    (h : ∀ i ∈ p, instructionValid i) : GatePhysical p := by
  intro i hi
  exact instruction_physical52 i (h i hi)





theorem forward_tail_gatePhysical52 (p : Ports) (flag : Wire)
    (nd : (flag::wireList p).Nodup) : GatePhysical (forwardTail p flag) :=
  program_physical52 _ (forward_tail_contract_valid52 p flag nd)





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





theorem flag_gatePhysical_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (oldPhysical : GatePhysical (literalKAdd w)) : GatePhysical (flagKAdd52 w) :=
  flag_gatePhysical52 w (actual_flag_ports_nodup52 w hn) oldPhysical























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











/-- Promise uses the actual OLD complete run and the actual canonical D/parity. -/
theorem forward_outputs_from_postWord52 (w : Nat → Wire) (s : State)
    (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool) (hp : par=decide (D%2=1))
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Kword D par) :
    ForwardOldOutputs52 w par s := by
  exact forward_bits_from_postWord52 w (run (literalKAdd w) [] s).basis D hD par hp postWord








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
end


-- Consolidated source module: MainPart07
section

set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.E1QubitPlacement =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Prefix1590Point
-- consolidated import: import ECDSAAdd.Submission.Entrant.FrontierEntry1591Native
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1Merge

/-! Research source. Complete proof bodies, adapted from the pinned accepted
E1 placement proof to a different bijection. No sorry/axiom/certificate.
Not elaborated or replayed in this environment. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1QubitPlacement
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk

/-! Complete zero-cost placement for E1 on the old Q1588 rolling route.
The global bijection first moves three E1-only scratch locations:
  compare carry511 ->725, product721 ->723, product722 ->724.
It then hosts native cin1797 at511 and applies the three rolling phase hosts.
No two live values are aliased. All added destinations are already-counted
ordinary field carry sites. This file has NOT been Lean-checked here. -/

def nativeSwap : Equiv.Perm Wire := Equiv.swap (base 1797) (base 511)
def phaseHost : Equiv.Perm Wire :=
  (Equiv.swap (base 1026) (base 721)).trans
    ((Equiv.swap (base 1541) (base 722)).trans
      (Equiv.swap (base 1542) (base 720)))
def sig (q : Wire) : Wire := phaseHost (nativeSwap q)
def pmap (L : ControlledPointLayout) (q : Wire) : Wire := wireFn2 L (sig q)

def sw (i : Nat) : Nat :=
  if i=1797 then 511 else if i=511 then 1797 else
  if i=1026 then 721 else if i=721 then 1026 else
  if i=1541 then 722 else if i=722 then 1541 else
  if i=1542 then 720 else if i=720 then 1542 else i

theorem swap_base (a b i : Nat) :
    Equiv.swap (base a) (base b) (base i)=base (if i=a then b else if i=b then a else i) := by
  rw [Equiv.swap_apply_def]
  by_cases h1 : i=a
  · subst h1; simp
  · have n1 : base i≠base a := fun e => h1 (base_injective e)
    by_cases h2 : i=b
    · subst h2; simp [n1,h1]
    · have n2 : base i≠base b := fun e => h2 (base_injective e)
      simp [n1,n2,h1,h2]

theorem sig_base (i : Nat) : sig (base i)=base (sw i) := by
  unfold sig phaseHost nativeSwap
  simp only [Equiv.trans_apply,swap_base]
  congr 1
  unfold sw
  split_ifs <;> omega

theorem sig_injective : Function.Injective sig :=
  phaseHost.injective.comp nativeSwap.injective

/-- The label set of the merged circuit. -/
def S : Finset Wire := (E1Merge.mSites base (base 2400)).toFinset

theorem S_cases (q : Wire) (hq : q∈S) : ∃ i, q=base i ∧
    (i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722 ∨ i = 2400) := by
  simp only [S,E1Merge.mSites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false] at hq
  rcases hq with ((h|h)|h)|h|h|h
  all_goals first
    | (obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
       simp only [List.mem_range'_1] at hi
       exact ⟨i,rfl,by omega⟩)
    | exact ⟨_,h,by omega⟩

/-- Label range of the merged circuit after the scratch relocation `rho`. -/
abbrev Rng (i : Nat) : Prop :=
  (i < 515 ∧ i ≠ 511) ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 723 ∨ i = 724 ∨ i = 725 ∨ i = 2400

theorem sw_slot (i : Nat) (hi : Rng i) : base (sw i)∈slots.toFinset := by
  apply slot_mem
  · unfold live sw; split_ifs <;> omega
  · unfold CompressedAllocation.omitted sw; split_ifs <;> omega

theorem sw_logical (i : Nat) (hi : Rng i) : base (sw i)∈OB5Support.logicalSites := by
  simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
  refine ⟨sw i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  unfold sw; split_ifs <;> omega

/-- Three disjoint E1 scratch relocations. The direct tick omits all six ports. -/
def rho : Equiv.Perm Wire :=
  (Equiv.swap (base 511) (base 725)).trans
    ((Equiv.swap (base 721) (base 723)).trans (Equiv.swap (base 722) (base 724)))
def rhoN (i : Nat) : Nat :=
  if i=511 then 725 else if i=725 then 511 else
  if i=721 then 723 else if i=723 then 721 else
  if i=722 then 724 else if i=724 then 722 else i

theorem rho_base (i : Nat) : rho (base i)=base (rhoN i) := by
  unfold rho rhoN
  simp only [Equiv.trans_apply,swap_base]
  congr 1
  split_ifs <;> omega

theorem rho_injective : Function.Injective rho := rho.injective

theorem rhoN_range (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722 ∨ i = 2400) :
    Rng (rhoN i) := by
  unfold Rng rhoN; split_ifs <;> omega

/-- Placement of the merged circuit: relocation, the four relabelings, the layout map. -/
def pmapR (L : ControlledPointLayout) (q : Wire) : Wire := pmap L (rho q)


theorem sig_rho_x (i : Nat) (hi : 770≤ i ∧ i<1026) :
    sig (rho (base i))=base i := by
  have hr : rhoN i=i := by unfold rhoN;split_ifs <;> omega
  have hs : sw i=i := by unfold sw;split_ifs <;> omega
  rw [rho_base,hr,sig_base,hs]

section Place
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pmap_inj : ∀a∈S,∀b∈S,pmapR L a=pmapR L b → a=b := by
  intro a ha b hb e
  obtain ⟨i,rfl,hi⟩ := S_cases a ha
  obtain ⟨j,rfl,hj⟩ := S_cases b hb
  have pl := placement2 L hw hn
  unfold pmapR pmap at e
  rw [rho_base,rho_base,sig_base,sig_base] at e
  have := pl.injectiveOnSlots _ (sw_slot _ (rhoN_range i hi)) _ (sw_slot _ (rhoN_range j hj)) e
  rw [←sig_base,←sig_base] at this
  have := sig_injective this
  rw [←rho_base,←rho_base] at this
  exact rho_injective this

theorem pmap_x : (wireBlock base 770 256).map (pmapR L)=L.point.x := by
  have pl := placement2 L hw hn
  rw [←pl.divisorMap]
  apply List.map_congr_left
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  change wireFn2 L (sig (rho (base i)))=wireFn2 L (base i)
  rw [sig_rho_x i (by omega)]

theorem pmap_g : pmapR L (base 2400)=L.core.generic := by
  have pl := placement2 L hw hn
  unfold pmapR pmap; rw [rho_base,sig_base]
  have : sw (rhoN 2400)=2400 := by unfold sw rhoN; simp
  rw [this]; exact pl.controlMap

theorem pmap_pool (q : Wire) (hq : q∈S) (hx : q∉wireBlock base 770 256) (hg : q≠base 2400) :
    pmapR L q∈L.dialogPool := by
  obtain ⟨i,rfl,hi⟩ := S_cases q hq
  have pl := placement2 L hw hn
  let j:=sw (rhoN i)
  have indexEq : sig (rho (base i))=base j := by rw [rho_base,sig_base]
  have injective:=sig_injective.comp rho_injective
  have fixedG : sig (rho (base 2400))=base 2400 := by decide +kernel
  have jRange : j<1798 ∨ j=2400 := by
    have range:=rhoN_range i hi
    dsimp [j]
    generalize rhoN i=v at range ⊢
    unfold Rng at range
    unfold sw
    split_ifs <;> omega
  have jNotG : j≠2400 := by
    intro e
    apply hg
    exact injective (indexEq.trans ((congrArg base e).trans fixedG.symm))
  have jlt : j<1798 := by omega
  have jNotX : ¬(770≤ j ∧ j<1026) := by
    intro bounds
    have equal:=injective (indexEq.trans (sig_rho_x j bounds).symm)
    have same:=base_injective equal
    apply hx
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1];omega,rfl⟩
  change wireFn2 L (sig (rho (base i)))∈L.dialogPool
  rw [indexEq]
  apply pl.sharedWork
  · exact List.mem_map.mpr ⟨j,by simp only [skywalkSharedWires,List.mem_range'_1];omega,rfl⟩
  · exact sw_slot _ (rhoN_range i hi)
  · intro h
    obtain ⟨v,hv,e⟩:=List.mem_map.mp h
    have same:=base_injective e
    simp only [List.mem_range'_1] at hv
    exact jNotX (by omega)
  · intro h
    obtain ⟨v,hv,e⟩:=List.mem_map.mp h
    have same:=base_injective e
    simp only [List.mem_range'_1] at hv
    omega

end Place


def tickF (L : ControlledPointLayout) : Program := renameProgram (pmapR L) (NativeFirstDirect.forward base)
def entryM (L : ControlledPointLayout) (k : Fp) : Program :=
  renameProgram (pmapR L) (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val)

theorem regValue_pull (f : Wire → Wire) (r : List Wire) (s : BasisState) :
    regValue r (fun q => s (f q))=regValue (r.map f) s := by
  induction r with
  | nil => rfl
  | cons a rs ih =>
    change (if s (f a) then 1 else 0)+2*regValue rs (fun q => s (f q))=
      (if s (f a) then 1 else 0)+2*regValue (rs.map f) s
    rw [ih]

theorem g2400 : base 2400∉skywalkPoolWires base := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hi
  have := base_injective e; omega

theorem merged_S (k : Nat) : wires (E1AffineEndpoints52Research.Forward.merged base (base 2400) k)⊆S :=
  E1AffineEndpoints52Research.Forward.merged_support base (base 2400) k

theorem prefix_S : (NativeFirstDirect.prefixSites base).toFinset⊆S := by
  intro q h
  rw [List.mem_toFinset] at h
  simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at h
  simp only [S,List.mem_toFinset]
  rcases h with ((h|h)|h)|h|h
  · exact E1Merge.blk_mSites base (base 2400) 0 257 (by omega) q h
  · exact E1Merge.blk_mSites base (base 2400) 770 258 (by omega) q h
  · exact E1Merge.blk_mSites base (base 2400) 1540 256 (by omega) q h
  · rw [h]; exact E1Merge.in_mSites base (base 2400) 1028 (by omega)
  · rw [h]; exact E1Merge.in_mSites base (base 2400) 1797 (by omega)

theorem forward_S : wires (NativeFirstDirect.forward base)⊆S :=
  Finset.Subset.trans (NativeFirstDirect.prefix_support base).1 prefix_S

section Entry
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

/-- Physical form: the merged entry equals the compare-first constant addition followed by the
renamed direct first tick, on every pair of measurement records. -/
theorem entry_eq (k : Fp) (s : State) (X : Nat) (hX : X<p) (G : Bool)
    (hx : regValue L.point.x s.basis=X) (hg : s.basis L.core.generic=G)
    (hc : regValue L.dialogPool s.basis=0) (m1 m2 : List Bool) :
    run (entryM L k) m1 s=run (fastConstAdd L L.point.x k++tickF L) m2 s := by
  have inj := pmap_inj L hw hn
  have pool := pmap_pool L hw hn
  have hzero := (regValue_zero _ _).mp hc
  let F := pmapR L
  let t : State := pullState F s
  have clean (q : Wire) (hq : q∈S) (h1 : q∉wireBlock base 770 256) (h2 : q≠base 2400) :
      t.basis q=false := hzero _ (pool q hq h1 h2)
  have inS (i : Nat) (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      base i∈S := List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i hi)
  have notx (i : Nat) (hi : ¬ (770 ≤ i ∧ i < 1026)) : base i∉wireBlock base 770 256 := by
    intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj; have := base_injective e; omega
  have ne2400 (i : Nat) (hi : i≠2400) : base i≠base 2400 := fun e => hi (base_injective e)
  have cl (i : Nat) (hi : i < 515 ∨ (1026 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      t.basis (base i)=false :=
    clean _ (inS i (by omega)) (notx i (by omega)) (ne2400 i (by omega))
  have blkz (a n : Nat) (h : a + n ≤ 515 ∨ (1026 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
      regValue (wireBlock base a n) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (by omega)
  have xval : regValue (wireBlock base 770 256) t.basis=X := by
    change regValue (wireBlock base 770 256) (fun q => s.basis (F q))=X
    rw [regValue_pull,pmap_x L hw hn,hx]
  have tk0 : regValue (E1Merge.kR base) t.basis=X := by
    rw [E1Merge.kR_x base base_pool_nodup,show E1Merge.xR base=wireBlock base 770 256 from rfl,xval,
      blkz 1026 2 (by omega)]
    simp
  have tg : t.basis (base 2400)=G := by
    change s.basis (pmapR L (base 2400))=G
    rw [pmap_g L hw hn,hg]
  -- old side
  have fca := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX s
    (m2.take (measurementCount (fastConstAdd L L.point.x k))) hg hx hc
  generalize hs1 : run (fastConstAdd L L.point.x k) (m2.take (measurementCount (fastConstAdd L L.point.x k))) s=s1 at fca
  obtain ⟨p1,x1,o1⟩ := fca
  let u : State := ⟨t.phase,fun q => if q∈E1Merge.kR base then s1.basis (F q) else t.basis q⟩
  have hu2 : ∀q,q∉E1Merge.kR base → u.basis q=t.basis q := by
    intro q hq; simp [u,hq]
  have xS : ∀q∈L.point.x,∃a∈S,F a=q ∧ a∈wireBlock base 770 256 := by
    intro q hq
    rw [←pmap_x L hw hn] at hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    refine ⟨a,?_,rfl,ha⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_range'_1] at hi
    exact inS i (by omega)
  have hu3 : regValue (E1Merge.kR base) u.basis=(X+(if t.basis (base 2400) then k.val else 0))%p := by
    rw [tg,E1Merge.kR_x base base_pool_nodup]
    have e1 : regValue (E1Merge.xR base) u.basis=regValue L.point.x s1.basis := by
      rw [←pmap_x L hw hn,←regValue_pull]
      apply regValue_congr
      intro q hq
      have : q∈E1Merge.kR base := E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) q hq
      simp only [u,this,if_true]
      rfl
    have e2 : regValue (wireBlock base 1026 2) u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      have kq : base i∈E1Merge.kR base := E1Merge.blk_sub base 1026 2 770 258 (by omega) (by omega) _ hq
      have outx : F (base i)∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha (base i) (inS i (by omega)) ea
        subst this
        exact notx i (by omega) ax
      simp only [u,kq,if_true]
      rw [o1 _ outx]
      exact cl i (by omega)
    rw [e1,e2,x1]; simp
  have t1 := (regValue_zero _ _).mp (blkz 0 258 (by omega))
  have eqL := E1AffineEndpoints52Research.Forward.merged_eq_forward base (base 2400) base_pool_nodup g2400 k.val k.isLt X hX t u m1
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) tk0 (blkz 0 258 (by omega))
    (blkz 1029 256 (by omega)) (cl 1028 (by omega)) (cl 514 (by omega)) (cl 721 (by omega)) (cl 722 (by omega))
    (fun i h1 h2 => cl i (by omega)) (cl 513 (by omega))
    (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact cl i (by omega)) (cl 1797 (by omega)) rfl hu2 hu3
  -- transport both sides
  have hS : ∀q∈S,t.basis q=s.basis (F q) := fun q _ => rfl
  have newSide := run_rename_pool F S inj _ (merged_S k.val) m1 t s rfl hS
  have uS : ∀q∈S,u.basis q=s1.basis (F q) := by
    intro q hq
    by_cases kq : q∈E1Merge.kR base
    · simp [u,kq]
    · simp only [u,kq,if_false]
      change s.basis (F q)=s1.basis (F q)
      have outx : F q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha q hq ea
        subst this
        exact kq (E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) _ ax)
      rw [o1 _ outx]
  have oldSide := run_rename_pool F S inj _ forward_S
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) u s1 (by simp [u,t,pullState,p1]) uS
  have rhs : run (fastConstAdd L L.point.x k++tickF L) m2 s=
      run (tickF L) (m2.drop (measurementCount (fastConstAdd L L.point.x k))) s1 := by
    rw [run_append,hs1]
  rw [rhs]
  apply State.extensionality
  · rw [entryM,newSide.1,eqL,tickF,oldSide.1]
  · funext q
    by_cases im : q∈S.image F
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp im
      rw [entryM,newSide.2 a ha,eqL,tickF,oldSide.2 a ha]
    · rw [entryM,run_rename_pool_outside F S _ (merged_S k.val) m1 s q im,tickF,
        run_rename_pool_outside F S _ forward_S _ s1 q im]
      have outx : q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,_⟩ := xS _ hm
        exact im (Finset.mem_image.mpr ⟨a,ha,ea⟩)
      rw [o1 q outx]

end Entry

/-- Replace a prefix whose final state agrees with an old prefix on every record. -/
theorem tri_transfer {P Q : BasisState → Prop} {A B R : Program}
    (h : ∀s : State,P s.basis → ∀ m1 m2 : List Bool,run A m1 s=run B m2 s)
    (t : Triple P (B++R) Q) : Triple P (A++R) Q := by
  intro s m hs
  have := t s (List.replicate (measurementCount B) false++m.drop (measurementCount A)) hs
  rw [run_append] at this ⊢
  have e1 : (List.replicate (measurementCount B) false++m.drop (measurementCount A)).take
      (measurementCount B)=List.replicate (measurementCount B) false := by simp
  have e2 : (List.replicate (measurementCount B) false++m.drop (measurementCount A)).drop
      (measurementCount B)=m.drop (measurementCount A) := by simp
  rw [e1,e2] at this
  rw [h s hs (m.take (measurementCount A)) (List.replicate (measurementCount B) false)]
  exact this

section Entry1
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

-- Keep the inherited width argument for existing callers.
set_option linter.unusedSectionVars false in
theorem lay (q : Wire) :
    (q∈L.point.x → q∉L.point.y) ∧ (q∈L.dialogPool → q∉L.point.x ∧ q∉L.point.y) ∧
    (q=L.core.generic → q∉L.point.x ∧ q∉L.point.y) := by
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  refine ⟨fun hx hy => ?_,fun hp => ⟨fun hx => ?_,fun hy => ?_⟩,fun hg => ⟨fun hx => ?_,fun hy => ?_⟩⟩
  all_goals
    first
    | (have h1 := List.count_pos_iff.mpr hx; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (have h1 := List.count_pos_iff.mpr hp; have h2 := List.count_pos_iff.mpr hx
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (have h1 := List.count_pos_iff.mpr hp; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (subst hg; have h2 := List.count_pos_iff.mpr hx
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
       omega)
    | (subst hg; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
       omega)

/-- The y-side fused offset commutes with the x-side constant addition, so the merged x entry
can run after it. -/
theorem entry1_eq (k ky : Fp) (s : State) (X : Nat) (hX : X<p) (Y : Fp) (G : Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (hg : s.basis L.core.generic=G) (hc : regValue L.dialogPool s.basis=0) (m1 m2 : List Bool) :
    run (EntryFuse.fusedY L ky++entryM L k) m1 s=
      run (fastConstAdd L L.point.x k++EntryFuse.fusedY L ky++tickF L) m2 s := by
  have xy (q : Wire) (h : q∈L.point.x) : q∉L.point.y := (lay L hw hn q).1 h
  have px (q : Wire) (h : q∈L.dialogPool) : q∉L.point.x := ((lay L hw hn q).2.1 h).1
  have py (q : Wire) (h : q∈L.dialogPool) : q∉L.point.y := ((lay L hw hn q).2.1 h).2
  have gx : L.core.generic∉L.point.x := ((lay L hw hn _).2.2 rfl).1
  have gy : L.core.generic∉L.point.y := ((lay L hw hn _).2.2 rfl).2
  -- left: fusedY then merged entry
  have fy := EntryFuse.fusedY_correct L hw hn Y ky s (m1.take (measurementCount (EntryFuse.fusedY L ky))) hy hc
  generalize hsy : run (EntryFuse.fusedY L ky) (m1.take (measurementCount (EntryFuse.fusedY L ky))) s=sy at fy
  obtain ⟨py1,py2,py3⟩ := fy
  have syx : regValue L.point.x sy.basis=X := by
    rw [regValue_congr _ _ s.basis (fun q hq => py3 q (xy q hq)),hx]
  have syg : sy.basis L.core.generic=G := (py3 _ gy).trans hg
  have syc : regValue L.dialogPool sy.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq => py3 q (py q hq)),hc]
  -- commutation of the two constant steps
  have comm (r0 r1 r2 : List Bool) : run (fastConstAdd L L.point.x k) r0 sy=
      run (EntryFuse.fusedY L ky) r2 (run (fastConstAdd L L.point.x k) r1 s) := by
    have fa := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX sy r0 syg syx syc
    have fc := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX s r1 hg hx hc
    generalize ha : run (fastConstAdd L L.point.x k) r0 sy=a at fa
    generalize hcc : run (fastConstAdd L L.point.x k) r1 s=c at fc
    obtain ⟨a1,a2,a3⟩ := fa
    obtain ⟨c1,c2,c3⟩ := fc
    have cy : regValue L.point.y c.basis=Y.val := by
      rw [regValue_congr _ _ s.basis (fun q hq => c3 q (fun h => xy q h hq)),hy]
    have cc : regValue L.dialogPool c.basis=0 := by
      rw [regValue_congr _ _ s.basis (fun q hq => c3 q (px q hq)),hc]
    have fb := EntryFuse.fusedY_correct L hw hn Y ky c r2 cy cc
    generalize hb : run (EntryFuse.fusedY L ky) r2 c=b at fb
    obtain ⟨b1,b2,b3⟩ := fb
    have cg : c.basis L.core.generic=s.basis L.core.generic := c3 _ gx
    apply State.extensionality
    · rw [a1,b1,c1,py1]
    · funext q
      by_cases qx : q∈L.point.x
      · have e : regValue L.point.x a.basis=regValue L.point.x b.basis := by
          rw [a2,regValue_congr _ _ c.basis (fun q hq => b3 q (xy q hq)),c2]
        exact (regValue_eq_iff _ _ _).mp e q qx
      by_cases qy : q∈L.point.y
      · have e : regValue L.point.y a.basis=regValue L.point.y b.basis := by
          rw [regValue_congr _ _ sy.basis (fun q hq => a3 q (fun h => xy q h hq)),py2,b2,cg]
        exact (regValue_eq_iff _ _ _).mp e q qy
      rw [a3 q qx,b3 q qy,c3 q qx,py3 q qy]
  -- assemble
  let nA := measurementCount (fastConstAdd L L.point.x k)
  let nY := measurementCount (EntryFuse.fusedY L ky)
  let M := List.replicate nA false++m2.drop (nA+nY)
  have lhs : run (EntryFuse.fusedY L ky++entryM L k) m1 s=
      run (tickF L) (m2.drop (nA+nY)) (run (fastConstAdd L L.point.x k) (List.replicate nA false) sy) := by
    rw [run_append,hsy,entry_eq L hw hn k sy X hX G syx syg syc _ M,run_append]
    have t1 : M.take nA=List.replicate nA false := List.take_left' (by simp)
    have t2 : M.drop nA=m2.drop (nA+nY) := List.drop_left' (by simp)
    rw [t1,t2]
  have rhs : run (fastConstAdd L L.point.x k++EntryFuse.fusedY L ky++tickF L) m2 s=
      run (tickF L) (m2.drop (nA+nY)) (run (EntryFuse.fusedY L ky) ((m2.take (nA+nY)).drop nA)
        (run (fastConstAdd L L.point.x k) ((m2.take (nA+nY)).take nA) s)) := by
    rw [run_append,run_append,measurementCount_append]
  rw [lhs,rhs,comm]

end Entry1

/-! Resource and support facts are independent of the point-level caller. -/
section Resources
open Challenge
attribute [local irreducible] wires

def logicalEntry (k : Nat) : Program :=
  renameProgram sig (renameProgram rho (E1AffineEndpoints52Research.Forward.merged base (base 2400) k))

theorem entryM_eq (L : ControlledPointLayout) (k : Fp) :
    entryM L k=renameProgram (wireFn2 L) (logicalEntry k.val) := by
  simp only [entryM,logicalEntry,renameProgram_comp]
  rfl

private theorem renamed_twice_labels (f h : Wire→Wire) (P : Program) (U : Finset Wire)
    (sub : wires P⊆U) (q : Wire) (hq : q∈wires (renameProgram f (renameProgram h P))) :
    ∃b∈U,q=f (h b) := by
  rw [renameProgram_support,renameProgram_support] at hq
  obtain ⟨a,ha,ea⟩:=Finset.mem_image.mp hq
  obtain ⟨b,hb,eb⟩:=Finset.mem_image.mp ha
  refine ⟨b,sub hb,?_⟩
  rw [←ea,←eb]


theorem merged_labels (k : Nat) (q : Wire) (hq : q∈wires (logicalEntry k)) :
    ∃ j, q=base (sw (rhoN j)) ∧
      (j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨
        j=721 ∨ j=722 ∨ j=2400) := by
  obtain ⟨b,hb,eq⟩:=renamed_twice_labels sig rho
    (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) S (merged_S k) q hq
  obtain ⟨j,rfl,hj⟩:=S_cases b hb
  refine ⟨j,?_,hj⟩
  rw [eq,rho_base,sig_base]

theorem logicalM (k : Nat) : wires (logicalEntry k)⊆OB5Support.logicalSites := by
  intro q hq
  obtain ⟨j,rfl,hj⟩ := merged_labels k q hq
  exact sw_logical _ (rhoN_range j hj)

theorem sw_avoid (j : Nat)
    (hj : j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨
      j=721 ∨ j=722 ∨ j=2400) :
    sw (rhoN j)∉[2312,766,765,767,1026,1541,1542,1797,768,718,719] := by
  have range:=rhoN_range j hj
  generalize rhoN j=i at range ⊢
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  unfold Rng at range
  unfold sw
  split_ifs <;> omega

theorem merged_omits (k i : Nat)
    (hi : i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719]) :
    base i∉wires (logicalEntry k) := by
  intro h
  obtain ⟨j,e,hj⟩ := merged_labels k (base i) h
  have eq := base_injective e
  exact sw_avoid j hj (eq ▸ hi)

theorem entryM_counts (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (entryM L k)=1022 ∧ measurementCount (entryM L k)=1027 := by
  have r := renameProgram_counts (pmapR L) (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val)
  have c := E1AffineEndpoints52Research.Forward.merged_counts base (base 2400) k.val
  rw [entryM,r.1,r.2]; exact c

theorem tickF_counts (L : ControlledPointLayout) :
    toffoliCount (tickF L)=508 ∧ measurementCount (tickF L)=508 := by
  have r := renameProgram_counts (pmapR L) (NativeFirstDirect.forward base)
  have c := NativeFirstDirect.forward_counts base
  rw [tickF,r.1,r.2]; exact c

theorem entryM_slots (L : ControlledPointLayout) (k : Fp) :
    gateSlots (entryM L k)≤25000 := by
  simpa only [entryM,Baselines.rename_gateSlots] using
    E1AffineEndpoints52Research.Forward.merged_slots base (base 2400) k.val

theorem entryM_sites (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryM L k)⊆(OB5Support.sites L).toFinset := by
  rw [entryM_eq]
  exact OB5Support.placed_support_logical L hw _ (logicalM k.val)

theorem entryM_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (entryM L k) := by
  rw [entryM]
  exact gatePhysical_rename_support (pmapR L) (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val)
    (fun a ha b hb e => pmap_inj L hw hn a (merged_S k.val ha) b (merged_S k.val hb) e)
    (E1AffineEndpoints52Research.Forward.merged_physical base (base 2400) base_pool_nodup g2400 k.val)

theorem prefix_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (entryM L k)+252=
      toffoliCount (fastConstAdd L L.point.x k++tickF L) ∧
    measurementCount (entryM L k)+248=
      measurementCount (fastConstAdd L L.point.x k++tickF L) := by
  have a := fastConstAdd_counts L hw L.point.x (Or.inl rfl) k
  have e := entryM_counts L k
  have t := tickF_counts L
  simp only [toffoliCount_append,measurementCount_append]
  constructor <;> omega

end Resources

/-- All pre-relocated ports are absent from the actual direct first tick. -/
theorem rho_fix (f : Wire → Wire) :
    renameProgram (fun q => f (rho q)) (NativeFirstDirect.forward base)=
      renameProgram f (NativeFirstDirect.forward base) := by
  have fix (P : Program) (support : wires P⊆(NativeFirstDirect.prefixSites base).toFinset) :
      renameProgram (fun q => f (rho q)) P=renameProgram f P := by
    apply renameProgram_congr_support
    intro q hq
    have h := support hq
    rw [List.mem_toFinset] at h
    simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at h
    have e : ∃ i, q=base i ∧
        (i<257 ∨ (770≤ i ∧ i<1028) ∨ (1540≤ i ∧ i<1796) ∨ i=1028 ∨ i=1797) := by
      rcases h with ((h|h)|h)|h|h
      all_goals first
        | (obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
           simp only [List.mem_range'_1] at hi
           exact ⟨i,rfl,by omega⟩)
        | exact ⟨_,h,by omega⟩
    obtain ⟨i,rfl,hi⟩ := e
    rw [rho_base]
    have fixed : rhoN i=i := by unfold rhoN; split_ifs <;> omega
    rw [fixed]
  exact fix (NativeFirstDirect.forward base) (NativeFirstDirect.prefix_support base).1

/-- The new merged entry has exactly the old rolling native tick boundary. -/
theorem tick_eq (L : ControlledPointLayout) :
    renameProgram (wireFn2 L)
      (renameProgram phaseHost (FrontierEntry1591Native.forward base))=tickF L := by
  rw [tickF,show pmapR L=fun q => pmap L (rho q) from rfl,rho_fix]
  simp only [FrontierEntry1591Native.forward,FrontierEntry1591Native.Transport.program,
    renameProgram_comp]
  rfl

end ECDSAAdd.Entrant.E1QubitPlacement
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.E1Reflected =====
section
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectForwardProof
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectValues
-- consolidated import: import ECDSAAdd.Arithmetic.Compare
-- consolidated import: import ECDSAAdd.Arithmetic.ComparePhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MaskedConstant
-- consolidated import: import ECDSAAdd.Arithmetic.MappedSources
-- consolidated import: import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.Copy
-- consolidated import: import ECDSAAdd.Arithmetic.Rotate
-- consolidated import: import ECDSAAdd.Arithmetic.Reduction
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredGateSupport
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectSupport
-- consolidated import: import ECDSAAdd.Baselines.SlotAlgebra
-- consolidated import: import ECDSAAdd.Baselines.SlotMapped
-- consolidated import: import ECDSAAdd.Baselines.SlotNativeFirst

set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Research adaptation of pinned accepted E1Merge. Reflects canonical input
unconditionally, then performs its controlled constant addition and first tick.
Full proof bodies are supplied; this module has NOT been Lean-checked here.
Input/output contract remains full State and every measurement record. -/
namespace ECDSAAdd.Entrant.E1Reflected
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum

/-! ### Arithmetic of the merged first tick -/

theorem p_val : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [ECDSAAdd.p]

/-- bit 0 of the selected constant `g·k − f·p`. -/
def ksel0 (k : Nat) (G f : Bool) : Bool := (G && decide (k%2=1)) ^^ f
/-- low bit of the input implied by `(g,f,par)`. -/
def x0 (k : Nat) (G f par : Bool) : Bool := par ^^ ksel0 k G f

/-- Constant added to the complemented 258-bit `x>>1` bank to obtain the direct first-tick `K` word. -/
def tk (k : Nat) (G f par : Bool) : Nat :=
  if f then
    if G then (kConstant false par+1+(k-1-(x0 k G f par).toNat-par.toNat)/2)%2^258
    else 0
  else (kConstant false par+1+
    (p-1-(x0 k G f par).toNat+(if G then k else 0)-par.toNat)/2)%2^258

def delta (par : Bool) : Nat := if par then p else 2^257-p

def thr (k : Nat) (G par : Bool) : Nat := if G then (if par then (k+p+1)/2 else (k+1)/2) else 0

theorem hC_val : hConstant = 57896044618658097711785492504343953926634992332820282019728792003954417335832 := by
  norm_num [hConstant, ECDSAAdd.p]
theorem kC_val (par : Bool) : kConstant false par =
    if par then 405272312330606683982498447530407677486444946329741974138101544027698101223913
    else 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  cases par <;> norm_num [kConstant, ECDSAAdd.p]


theorem arith (k X : Nat) (hk : k<p) (hX : X<p) (G : Bool) :
    let f := decide (X<(if G then k else 0))
    let dx := (p-1-X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    decide (X%2=1)=x0 k G f par ∧
    (2^258-1-X/2+tk k G f par)%2^258=K ∧
    H=dx/2+(if par then hConstant else 0) ∧
    f=decide (H<thr k G par) ∧
    tk k G f par<2^258 := by
  intro f dx par K H
  rw [p_val] at hk hX
  simp only [f,dx,par,K,H,tk,delta,thr,x0,ksel0,kC_val,hC_val,p_val,Nat.reducePow]
  clear H K par dx f
  cases G
  · have e1 : (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+0)%115792089237316195423570985008687907853269984665640564039457584007908834671663=115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X :=
      Nat.mod_eq_of_lt (by omega)
    simp only [if_false,Bool.false_eq_true,Nat.not_lt_zero,decide_false,
      e1,Bool.false_and,Bool.false_xor,Bool.xor_false]
    rcases Nat.mod_two_eq_zero_or_one (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X) with h|h <;>
      simp only [h,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),
        by (first | exact True.intro | omega),by (first | exact True.intro | omega),
        by (first | exact True.intro | (rw [eq_comm,decide_eq_true_iff]; omega) |
          (rw [eq_comm,decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
  · simp only [if_true,Bool.true_and]
    by_cases hf : X<k
    · have e1 : (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=k-1-X := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
        omega
      have e2 : decide (X<k)=true := by simp [hf]
      simp only [e1,e2,Bool.xor_true]
      rcases Nat.mod_two_eq_zero_or_one (k-1-X) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),
        by (first | exact True.intro | omega),by (first | exact True.intro | omega),
        by (first | exact True.intro | (rw [eq_comm,decide_eq_true_iff]; omega) |
          (rw [eq_comm,decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
    · have e1 : (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k := Nat.mod_eq_of_lt (by omega)
      have e2 : decide (X<k)=false := by simp [hf]
      simp only [e1,e2,Bool.xor_false]
      rcases Nat.mod_two_eq_zero_or_one (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),
        by (first | exact True.intro | omega),by (first | exact True.intro | omega),
        by (first | exact True.intro | (rw [eq_comm,decide_eq_true_iff]; omega) |
          (rw [eq_comm,decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩

/-! ### Circuit -/

def cmpC : Nat := 2^256-p

def srcR (w : Nat → Wire) : List Wire := wireBlock w 0 256
def xR (w : Nat → Wire) : List Wire := wireBlock w 770 256
def cR (w : Nat → Wire) : List Wire := wireBlock w 256 256
def hR (w : Nat → Wire) : List Wire := wireBlock w 0 258
def kR (w : Nat → Wire) : List Wire := wireBlock w 770 258
def tR (w : Nat → Wire) : List Wire := wireBlock w 1029 256
def hpR (w : Nat → Wire) : List Wire := wireBlock w 1 257
def aC (w : Nat → Wire) : List Wire := wireBlock w 1540 257
def hC2 (w : Nat → Wire) : List Wire := wireBlock w 1540 256
def hp8 (w : Nat → Wire) : List Wire := wireBlock w 1 256
def hC3 (w : Nat → Wire) : List Wire := wireBlock w 1540 255

def comparePart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (srcR w) k++
  compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514)++
  maskedConstant g (srcR w) k

def parGates (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  [.CX (w 770) (w 1028)]++(if k%2=1 then [.CX g (w 1028)] else [])++[.CX (w 514) (w 1028)]++
  [.CX (w 1028) (w 770)]++(if k%2=1 then [.CX g (w 770)] else [])++[.CX (w 514) (w 770)]

def prodPart (w : Nat → Wire) (g : Wire) : Program :=
  [.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)]

def c1 (k : Nat) : Nat := tk k false false false
def cg (k : Nat) : Nat := tk k true false false ^^^ tk k false false false
def cf (k : Nat) : Nat := tk k true true false ^^^ tk k true false false
def cp (k : Nat) : Nat := tk k false false true ^^^ tk k false false false
def cgp (k : Nat) : Nat :=
  tk k true false true ^^^ tk k true false false ^^^ tk k false false true ^^^ tk k false false false
def cfp (k : Nat) : Nat :=
  tk k true true true ^^^ tk k true true false ^^^ tk k true false true ^^^ tk k true false false

def loadK (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  xorConstant (hR w) (c1 k)++maskedConstant g (hR w) (cg k)++maskedConstant (w 514) (hR w) (cf k)++
  maskedConstant (w 1028) (hR w) (cp k)++maskedConstant (w 721) (hR w) (cgp k)++
  maskedConstant (w 722) (hR w) (cfp k)

def kAddM (w : Nat → Wire) : Program := mappedAdd (mappedRead (hR w) false) (kR w) (aC w) (w 1797)

def dBits (w : Nat → Wire) : List MappedBit := (List.range 257).map (fun j =>
  let a := (2^257-p).testBit j
  let b := p.testBit j
  if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some (w 1028),flip:=a})

def hAddM (w : Nat → Wire) : Program := mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)

/-- `hAddM` with its first carry trimmed. The first mapped bit is the literal `1`
(`2^257-p` and `p` are both odd) and the carry-in `w 1797` is clean, so the first
majority's Toffoli `CCX (w 1) (w 1797) (w 1540)` never fires; it is dropped. -/
def hPost (w : Nat → Wire) : Program :=
  mappedAdd (dBits w).tail (hpR w).tail (hC2 w).tail (w 1540) ++
    mappedEraseCarry {wire:=none,flip:=true} (w 1) (w 1797) (w 1540) ++
    mappedSum {wire:=none,flip:=true} (w 1) (w 1797)

def hAddT1 (w : Nat → Wire) : Program := [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ hPost w

/-- `hAddT1` with its last carry trimmed as well (see `MappedTopZero`). -/
def hAddT (w : Nat → Wire) : Program := MappedTopZero.topT (dBits w) w (w 1028)


def thrA (k : Nat) : Nat := (k+1)/2
def thrB (k : Nat) : Nat := (k+1)/2 ^^^ (k+p+1)/2

def loadT (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (thrA k)++maskedConstant (w 721) (tR w) (thrB k)

/-- Unconditional canonical reflection followed by controlled constant addition, merged into the direct first tick. -/
def merged (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  comparePart w g k++(parGates w g k++rotateRight (kR w)++notRegister (kR w))++prodPart w g++loadK w g k++E1WholeKAdd52Research.flagKAdd52 w++loadK w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]

/-! ### Layout facts -/

section Layout
variable (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
include hn

theorem mem_blk (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) :
    w i ∈ wireBlock w a n ↔ a ≤ i ∧ i < a + n := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := skywalkPool_index_inj w hn i j hi (by omega) he.symm
    omega
  · intro h
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem w_ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j :=
  index_ne w hn i j hi hj h

omit hn in
theorem blk_sub (a n b m : Nat) (h1 : b≤a) (h2 : a+n≤b+m) : ∀q∈wireBlock w a n,q∈wireBlock w b m := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem blk_nd (a n : Nat) (ha : a+n≤1798) : (wireBlock w a n).Nodup := block_nodup w hn a n ha

theorem blk_dis (a n b m : Nat) (ha : a+n≤1798) (hb : b+m≤1798) (sep : a+n≤b ∨ b+m≤a) :
    List.Disjoint (wireBlock w a n) (wireBlock w b m) := block_disjoint w hn a n b m ha hb sep

theorem g_out (g : Wire) (hg : g∉skywalkPoolWires w) (a n : Nat) (ha : a+n≤1798) : g∉wireBlock w a n :=
  fun h => hg (blk_sub w a n 0 1798 (by omega) (by omega) g h)

theorem g_ne (g : Wire) (hg : g∉skywalkPoolWires w) (i : Nat) (hi : i<1798) : g≠w i := by
  intro e; apply hg; rw [e]
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

end Layout


/-! ### Frame -/

def mutL (w : Nat → Wire) : List Wire := hR w++kR w++tR w++[w 1028,w 514,w 721,w 722]

def MF (w : Nat → Wire) (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState) : Prop :=
  regValue (hR w) s=H ∧ regValue (kR w) s=X ∧ regValue (tR w) s=T ∧
  s (w 1028)=par ∧ s (w 514)=f ∧ s (w 721)=gp ∧ s (w 722)=fp ∧ ∀q,q∉mutL w → s q=b0 q

theorem keep (R : List Wire) (s t : BasisState) (hf : ∀q,q∉R → t q=s q) (C : List Wire)
    (hC : ∀q∈C,q∉R) : regValue C t=regValue C s :=
  regValue_congr C t s (fun q hq => hf q (hC q hq))

section Steps
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem hR_nd : (hR w).Nodup := blk_nd w hn 0 258 (by omega)
theorem kR_nd : (kR w).Nodup := blk_nd w hn 770 258 (by omega)
theorem tR_nd : (tR w).Nodup := blk_nd w hn 1029 256 (by omega)

theorem hR_kR : ∀q∈kR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 770 258 (by omega) (by omega) (by omega)) h hq
theorem hR_tR : ∀q∈tR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem kR_hR : ∀q∈hR w,q∉kR w := fun q hq h => hR_kR w hn q h hq
theorem kR_tR : ∀q∈tR w,q∉kR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 770 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem tR_hR : ∀q∈hR w,q∉tR w := fun q hq h => hR_tR w hn q h hq
theorem tR_kR : ∀q∈kR w,q∉tR w := fun q hq h => kR_tR w hn q h hq

theorem nb (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) (sep : i < a ∨ a + n ≤ i) : w i ∉ wireBlock w a n :=
  block_not_mem w hn i a n hi ha sep

theorem out_of_mut (R : List Wire) (hR' : ∀q∈R,q∈mutL w) (q : Wire) (hq : q∉mutL w) : q∉R :=
  fun h => hq (hR' q h)

theorem hR_mut : ∀q∈hR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem kR_mut : ∀q∈kR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem tR_mut : ∀q∈tR w,q∈mutL w := fun q hq => by simp [mutL,hq]

/-- An operation that changes only the `H` block. -/
theorem stepH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉hR w → t.basis q=s.basis q) (H' : Nat)
    (hv : regValue (hR w) t.basis=H') : MF w b0 H' X T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨hv,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (hR_kR w hn)]; exact h2
  · rw [keep _ _ _ hf _ (hR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 0 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 0 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 0 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 0 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (hR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the `K` block. -/
theorem stepK (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉kR w → t.basis q=s.basis q) (X' : Nat)
    (hv : regValue (kR w) t.basis=X') : MF w b0 H X' T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,hv,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (kR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (kR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 770 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 770 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 770 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (kR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the threshold block. -/
theorem stepT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉tR w → t.basis q=s.basis q) (T' : Nat)
    (hv : regValue (tR w) t.basis=T') : MF w b0 H X T' par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,?_,hv,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (tR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (tR_kR w hn)]; exact h2
  · rw [hf _ (nb w hn 1028 1029 256 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 1029 256 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 1029 256 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 1029 256 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (tR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes one scalar wire `w j` of the frame. -/
theorem stepBit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State) (j : Nat)
    (hj : j=1028 ∨ j=514 ∨ j=721 ∨ j=722)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q≠w j → t.basis q=s.basis q) :
    MF w b0 H X T (if j=1028 then t.basis (w j) else par) (if j=514 then t.basis (w j) else f)
      (if j=721 then t.basis (w j) else gp) (if j=722 then t.basis (w j) else fp) t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have hjr : j<1798 := by omega
  have nh : w j∉hR w := nb w hn j 0 258 hjr (by omega) (by omega)
  have nk : w j∉kR w := nb w hn j 770 258 hjr (by omega) (by omega)
  have nt : w j∉tR w := nb w hn j 1029 256 hjr (by omega) (by omega)
  have ne (i : Nat) (hi : i<1798) (hij : i≠j) : w i≠w j := w_ne w hn i j hi hjr hij
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nh (e ▸ hq)))]; exact h1
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nk (e ▸ hq)))]; exact h2
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nt (e ▸ hq)))]; exact h3
  · by_cases e : j=1028
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 1028 (by omega) (Ne.symm e))]; exact h4
  · by_cases e : j=514
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 514 (by omega) (Ne.symm e))]; exact h5
  · by_cases e : j=721
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 721 (by omega) (Ne.symm e))]; exact h6
  · by_cases e : j=722
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 722 (by omega) (Ne.symm e))]; exact h7
  · intro q hq
    have : q≠w j := by
      intro e; apply hq; rw [e]
      rcases hj with rfl|rfl|rfl|rfl <;> simp [mutL]
    rw [hf q this]; exact h8 q hq

end Steps


/-! ### Concrete steps -/

theorem run_cx (a b : Wire) (m : List Bool) (s : State) :
    run [.CX a b] m s=⟨s.phase,writeBit s.basis b (s.basis b ^^ s.basis a)⟩ := rfl
theorem run_ccx (a b c : Wire) (m : List Bool) (s : State) :
    run [.CCX a b c] m s=⟨s.phase,writeBit s.basis c (s.basis c ^^ (s.basis a && s.basis b))⟩ := rfl



theorem run_meas_and (t a b : Wire) (m : List Bool) (s : State) (ha : a≠t) (hb : b≠t)
    (ht : s.basis t=(s.basis a && s.basis b)) :
    run [.measureX t [] [.CZ a b]] m s=⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [run,measureAndCorrect]
  cases m.headD false <;> simp [correct,writeBit,Function.update_of_ne ha,Function.update_of_ne hb,ht]

section Concrete
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem kR_split (s : BasisState) :
    regValue (kR w) s=(s (w 770)).toNat+2*regValue (wireBlock w 771 257) s := by
  have e : kR w=w 770::wireBlock w 771 257 := by
    simp [kR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 770) <;> simp [regValue,h]

theorem hR_split (s : BasisState) :
    regValue (hR w) s=(s (w 0)).toNat+2*regValue (hpR w) s := by
  have e : hR w=w 0::hpR w := by
    simp [hR,hpR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 0) <;> simp [regValue,h]

theorem hR_src (s : BasisState) :
    regValue (hR w) s=regValue (srcR w) s+2^256*regValue (wireBlock w 256 2) s := by
  have e : hR w=srcR w++wireBlock w 256 2 := by
    rw [hR,srcR,wireBlock_append]
  rw [e,regValue_append,srcR,wireBlock_length]

theorem kR_x (s : BasisState) :
    regValue (kR w) s=regValue (xR w) s+2^256*regValue (wireBlock w 1026 2) s := by
  have e : kR w=xR w++wireBlock w 1026 2 := by
    rw [kR,xR,wireBlock_append]
  rw [e,regValue_append,xR,wireBlock_length]

theorem kR_low (s : BasisState) :
    regValue (kR w) s=regValue (wireBlock w 770 257) s+2^257*regValue (wireBlock w 1027 1) s := by
  have e : kR w=wireBlock w 770 257++wireBlock w 1027 1 := by
    rw [kR,wireBlock_append]
  rw [e,regValue_append,wireBlock_length]

/-- A CX targeting the parity wire. -/
theorem stepParCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 1028) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) :
    Triple (MF w b0 H X T par f gp fp) [.CX c (w 1028)] (MF w b0 H X T (par ^^ cv) f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 1028)
    (s.basis (w 1028) ^^ s.basis c)⟩ 1028 (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit,h.2.2.2.1,hcv s.basis h] using this

/-- A CX targeting bit 0 of the K block. -/
theorem stepLowCX (b0 : BasisState) (H Y T : Nat) (b par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 770) (hcv : ∀s : BasisState,MF w b0 H (2*Y+b.toNat) T par f gp fp s → s c=cv) :
    Triple (MF w b0 H (2*Y+b.toNat) T par f gp fp) [.CX c (w 770)]
      (MF w b0 H (2*Y+(b ^^ cv).toNat) T par f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have m770 : w 770∈kR w := (mem_blk w hn 770 770 258 (by omega) (by omega)).mpr (by omega)
  have rest : ∀q∈wireBlock w 771 257,q≠w 770 := fun q hq e =>
    nb w hn 770 771 257 (by omega) (by omega) (by omega) (e ▸ hq)
  apply stepK w hn b0 H _ T par f gp fp s _ h
  · intro q hq; have : q≠w 770 := fun e => hq (e ▸ m770)
    simp [writeBit,Function.update_of_ne this]
  · have sp := kR_split w hn s.basis
    have sp2 := kR_split w hn (writeBit s.basis (w 770) (s.basis (w 770) ^^ s.basis c))
    rw [h.2.1] at sp
    rw [sp2,regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,Function.update_of_ne (rest q hq)])]
    rw [hcv s.basis h]
    simp only [writeBit,Function.update_self]
    cases hb : s.basis (w 770) <;> cases b <;> cases cv <;> simp [hb] at sp ⊢ <;> omega

end Concrete


section Concrete2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepXorH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (xorConstant (hR w) v) (MF w b0 (H^^^v) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := xorConstant_correct (hR w) (hR_nd w hn) v (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1])⟩

theorem stepMaskH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉hR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (hR w) v)
      (MF w b0 (H^^^(if cv then v else 0)) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (hR w) v (hR_nd w hn) hc
    (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1,hcv s.basis h])⟩

theorem stepMaskT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉tR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^256) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (tR w) v)
      (MF w b0 H X (T^^^(if cv then v else 0)) par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (tR w) v (tR_nd w hn) hc
    (by simpa [tR,wireBlock_length] using hv) s m
  exact ⟨hp,stepT w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.2.2.1,hcv s.basis h])⟩

theorem stepCCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (a b : Wire) (j : Nat)
    (hj : j=721 ∨ j=722) (av bv : Bool) (ha : a≠w j) (hb : b≠w j)
    (hav : ∀s : BasisState,MF w b0 H X T par f gp fp s → s a=av)
    (hbv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s b=bv) :
    Triple (MF w b0 H X T par f gp fp) [.CCX a b (w j)]
      (MF w b0 H X T par f (if j=721 then gp ^^ (av && bv) else gp)
        (if j=722 then fp ^^ (av && bv) else fp)) := by
  intro s m h
  rw [run_ccx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w j)
    (s.basis (w j) ^^ (s.basis a && s.basis b))⟩ j (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  rcases hj with rfl|rfl
  · simpa [writeBit,h.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this
  · simpa [writeBit,h.2.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this

theorem stepKAdd (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 H X T par f gp fp) (kAddM w) (MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m h
  have caway : ∀q∈aC w,q∉mutL w := by
    intro q hq hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
    · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
    all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm
  have m1797 : w 1797∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have nd : (w 1797::(kR w++aC w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),
      blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
  have src : ∀q∈mappedWires (mappedRead (hR w) false),q∉w 1797::(kR w++aC w) := by
    rw [mappedRead_wires]
    intro q hq hm
    simp only [List.mem_cons,List.mem_append] at hm
    rcases hm with e|e|e
    · exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq)
    · exact hR_kR w hn q e hq
    · exact List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq e
  have cl : ∀q∈aC w,s.basis q=false := fun q hq => (h.2.2.2.2.2.2.2 q (caway q hq)).trans (hc q hq)
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (mappedRead (hR w) false) (kR w) (aC w) (w 1797) nd src
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length]) s m cl
  refine ⟨hp,stepK w hn b0 H X T par f gp fp s _ h he _ ?_⟩
  rw [hval,mappedRead_value,h.1,h.2.1,(h.2.2.2.2.2.2.2 _ m1797).trans hcin]
  simp [kR,wireBlock_length]

end Concrete2

/-- Literal identity for this reflected namespace, without changing the generic adder. -/
theorem kAdd_literal (w : Nat → Wire) : E1Reflected.kAddM w = KAddCallerBridgeResearch.literalKAdd w := rfl






































/-! Checked reflected own-MF52 proof body, inlined to avoid a MainPart05 import cycle. -/
namespace Tail52
open Arithmetic RecordedQuantum KAddCallerBridgeResearch
open E1CallerValueFactsResearch E1WholeKAdd52Research

attribute [local irreducible] ECDSAAdd.run ECDSAAdd.regValue

private theorem carry_clean_at52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Reflected.aC w,b0 q=false) (s : BasisState)
    (hs : E1Reflected.MF w b0 H X T par f gp fp s)
    (i : Nat) (hi : 1794 ≤ i ∧ i < 1797) : s (w i)=false := by
  have away : w i∉E1Reflected.mutL w := by
    simp only [E1Reflected.mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨E1Reflected.nb w hn i 0 258 (by omega) (by omega) (by omega),
      E1Reflected.nb w hn i 770 258 (by omega) (by omega) (by omega)⟩,
      E1Reflected.nb w hn i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩
    all_goals exact E1Reflected.w_ne w hn _ _ (by omega) (by omega) (by omega)
  have member : w i∈E1Reflected.aC w := by
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [List.mem_range'_1]
    omega
  exact (hs.2.2.2.2.2.2.2 _ away).trans (hc _ member)

/-- The real reflected MF exterior frame supplies all three clean tail carries. -/
theorem highCarryClean_from_MF52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Reflected.aC w,b0 q=false) (s : BasisState)
    (hs : E1Reflected.MF w b0 H X T par f gp fp s) : highCarryClean52 w s := by
  change s (w 1794)=false ∧ s (w 1795)=false ∧ s (w 1796)=false
  exact ⟨carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1794 ⟨by decide,by decide⟩,
    carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1795 ⟨by decide,by decide⟩,
    carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1796 ⟨by decide,by decide⟩⟩

/-- Reflected flag replacement from its OWN old stepKAdd and actual MF.
H/X remain the caller's physical register values; hWord and parity stay explicit. -/
theorem stepKAddFlag52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Reflected.aC w,b0 q=false) (hcin : b0 (w 1797)=false)
    (D : Nat) (hD : D<ECDSAAdd.p) (hp : par=decide (D%2=1))
    (hWord : (H+X)%2^258=Kword D par) :
    Triple (E1Reflected.MF w b0 H X T par f gp fp) (flagKAdd52 w)
      (E1Reflected.MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m hs
  have old := E1Reflected.stepKAdd w hn b0 H X T par f gp fp hc hcin
  rw [E1Reflected.kAdd_literal] at old
  have oldEmpty := old s [] hs
  have postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Kword D par :=
    oldEmpty.2.2.1.trans hWord
  have clean := highCarryClean_from_MF52 w hn b0 H X T par f gp fp hc s.basis hs
  have outputs := ActualMF52Research.forward_outputs_from_postWord52 w s D hD par hp postWord
  have equal := flag_run_eq52 w hn s m clean par hs.2.2.2.1 outputs
  exact (congrArg (fun t : State => t.phase=s.phase ∧
    E1Reflected.MF w b0 H ((H+X)%2^258) T par f gp fp t.basis) equal).mpr (old s m hs)

end Tail52

def CF (w : Nat → Wire) (b0 : BasisState) (S : Nat) (F : Bool) (s : BasisState) : Prop :=
  regValue (srcR w) s=S ∧ s (w 514)=F ∧ ∀q,q∉srcR w → q≠w 514 → s q=b0 q

section Compare
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem src_nd : (srcR w).Nodup := blk_nd w hn 0 256 (by omega)
theorem w514_src : w 514∉srcR w := nb w hn 514 0 256 (by omega) (by omega) (by omega)

theorem cfMask (b0 : BasisState) (S : Nat) (F : Bool) (c : Wire) (hc : c∉srcR w) (hc' : c≠w 514)
    (v : Nat) (hv : v<2^256) :
    Triple (CF w b0 S F) (maskedConstant c (srcR w) v) (CF w b0 (S^^^(if b0 c then v else 0)) F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (srcR w) v (src_nd w hn) hc
    (by simpa [srcR,wireBlock_length] using hv) s m
  refine ⟨hp,?_,?_,?_⟩
  · rw [hval,h.1,h.2.2 c hc hc']
  · rw [he _ (w514_src w hn)]; exact h.2.1
  · intro q h1 h2; rw [he q h1]; exact h.2.2 q h1 h2
















theorem cfCmp (b0 : BasisState) (S : Nat) (F : Bool) (X : Nat) (hx : regValue (xR w) b0=X)
    (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false) :
    Triple (CF w b0 S F) (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514))
      (CF w b0 S (F ^^ decide (X<S))) := by
  intro s m h
  have xs : ∀q∈xR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)) h' hq
  have x514 : ∀q∈xR w,q≠w 514 := fun q hq e => nb w hn 514 770 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have cs : ∀q∈cR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)) h' hq
  have c514 : ∀q∈cR w,q≠w 514 := fun q hq e => nb w hn 514 256 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have n513 : w 513∉srcR w := nb w hn 513 0 256 (by omega) (by omega) (by omega)
  have e513 : w 513≠w 514 := w_ne w hn 513 514 (by omega) (by omega) (by omega)
  have nd : (w 514::w 513::(xR w++srcR w++cR w)).Nodup := by
    have a1 := blk_dis w hn 770 256 0 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
    have l1 : (xR w++srcR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 770 256 (by omega),src_nd w hn,a1⟩
    have l2 : (xR w++srcR w++cR w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨e513.symm,⟨nb w hn 514 770 256 (by omega) (by omega) (by omega),w514_src w hn⟩,
        nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 513 770 256 (by omega) (by omega) (by omega),n513⟩,
        nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hv⟩ := compareLt_correct none (xR w) (srcR w) (cR w) (w 513) (w 514) nd (by simp)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,srcR,xR,wireBlock_length]) s m
    ((h.2.2 _ n513 e513).trans hcin) (fun q hq => (h.2.2 q (cs q hq) (c514 q hq)).trans (hc q hq))
  refine ⟨hp,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => he q (fun e => w514_src w hn (e ▸ hq)))]; exact h.1
  · rw [hv,h.2.1,h.1,regValue_congr _ _ b0 (fun q hq => h.2.2 q (xs q hq) (x514 q hq)),hx]
    simp [controlValue]
  · intro q h1 h2; rw [he q h2]; exact h.2.2 q h1 h2

theorem cfCompare (b0 : BasisState) (F : Bool) (k X : Nat) (hk : k<2^256)
    (hx : regValue (xR w) b0=X) (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) :
    Triple (CF w b0 0 F) (comparePart w g k)
      (CF w b0 0 (F ^^ decide (X<(if b0 g then k else 0)))) := by
  have t := ((cfMask w hn b0 0 F g gs g514 k hk).seq
    (cfCmp w hn b0 _ F X hx hc hcin)).seq
    (cfMask w hn b0 _ _ g gs g514 k hk)
  simpa only [comparePart,Nat.zero_xor,Nat.xor_self] using t

end Compare


def dScalar (par : Bool) : Nat :=
  (List.range 257).foldr (fun j acc => (if par then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0

theorem dScalar_value (par : Bool) : dScalar par=delta par := by
  cases par <;> decide

private theorem selected_bit_value (flag : Wire) (a b : Bool) (s : BasisState) :
    (if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a}).value s=if s flag then b else a := by
  cases a <;> cases b <;> cases hf : s flag <;> simp [MappedBit.value,hf]

private theorem d_list_value (is : List Nat) (flag : Wire) (s : BasisState) :
    mappedValue (is.map (fun j =>
      let a := (2^257-p).testBit j
      let b := p.testBit j
      if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some flag,flip:=a})) s=
      is.foldr (fun j acc => (if s flag then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih,selected_bit_value]

theorem dBits_value (w : Nat → Wire) (s : BasisState) : mappedValue (dBits w) s=delta (s (w 1028)) := by
  rw [dBits,d_list_value]
  exact dScalar_value (s (w 1028))

theorem dBits_length (w : Nat → Wire) : (dBits w).length=257 := by simp [dBits]

theorem dBits_cons (w : Nat → Wire) :
    ∃ b' bs, dBits w = {wire:=none,flip:=true} :: b' :: bs := by
  have e : List.range 257 = 0 :: 1 :: List.range' 2 255 := by
    rw [List.range_eq_range']; rfl
  have t1 : (2^257-p).testBit 0 = true := by rw [p_val]; decide
  have t2 : p.testBit 0 = true := by rw [p_val]; decide
  rw [dBits, e, List.map_cons, List.map_cons]
  simp only [t1, t2, ite_true]
  exact ⟨_, _, rfl⟩

theorem hpR_cons (w : Nat → Wire) : ∃ y' ys, hpR w = w 1 :: y' :: ys :=
  ⟨w 2, (List.range' 3 255).map w, by
    rw [hpR, wireBlock, show (257:Nat) = 255+1+1 from rfl, List.range'_succ, List.range'_succ]; rfl⟩

theorem hC2_cons (w : Nat → Wire) : ∃ cs, hC2 w = w 1540 :: cs :=
  ⟨(List.range' 1541 255).map w, by
    rw [hC2, wireBlock, show (256:Nat) = 255+1 from rfl, List.range'_succ]; rfl⟩

theorem hAddM_split (w : Nat → Wire) :
    hAddM w = [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ [.CCX (w 1) (w 1797) (w 1540)] ++ hPost w := by
  obtain ⟨b', bs, hD⟩ := dBits_cons w
  obtain ⟨y', ys, hY⟩ := hpR_cons w
  obtain ⟨cs, hC⟩ := hC2_cons w
  simp only [hAddM, hPost, hD, hY, hC, List.tail_cons, mappedAdd, mappedMajority, List.append_assoc,
    List.cons_append, List.nil_append, if_true]

/-- Dropping a Toffoli whose second control is false after a measurement-free prefix. -/
theorem run_drop_ccx (P Q : Program) (a b t : Wire) (m : List Bool) (s : State)
    (hP : measurementCount P = 0) (hb : (run P [] s).basis b = false) :
    run (P ++ [.CCX a b t] ++ Q) m s = run (P ++ Q) m s := by
  rw [List.append_assoc, run_append, run_append P Q, hP]
  simp only [List.take_zero, List.drop_zero, List.cons_append, List.nil_append, run, hb,
    Bool.and_false, Bool.xor_false, writeBit, Function.update_eq_self]

theorem hAddT1_run (w : Nat → Wire) (h17 : w 1797 ≠ w 1540) (m : List Bool) (s : State)
    (hc : s.basis (w 1797) = false) : run (hAddT1 w) m s = run (hAddM w) m s := by
  rw [hAddM_split, hAddT1, run_drop_ccx]
  · rfl
  · simp only [run, writeBit, Function.update_of_ne h17, hc]

theorem hAddT1_counts (w : Nat → Wire) :
    toffoliCount (hAddT1 w) + 1 = toffoliCount (hAddM w) ∧
      measurementCount (hAddT1 w) = measurementCount (hAddM w) := by
  rw [hAddM_split, hAddT1]
  simp only [toffoliCount_append, measurementCount_append]
  constructor
  · simp [toffoliCount]; omega
  · simp [measurementCount]

theorem hAddT1_wires (w : Nat → Wire) : wires (hAddT1 w) ⊆ wires (hAddM w) := by
  rw [hAddM_split, hAddT1]
  simp only [wires_append]
  exact Finset.union_subset_union (Finset.subset_union_left) (Finset.Subset.refl _)

theorem hAddT1_physical (w : Nat → Wire) (h : GatePhysical (hAddM w)) : GatePhysical (hAddT1 w) := by
  rw [hAddM_split] at h
  rw [hAddT1]
  simp only [gatePhysical_append] at h ⊢
  exact ⟨h.1.1, h.2⟩

theorem hAddT1_slots (w : Nat → Wire) :
    Challenge.gateSlots (hAddT1 w) + 1 = Challenge.gateSlots (hAddM w) := by
  rw [hAddM_split, hAddT1]
  simp only [Challenge.gateSlots_append]
  simp [Challenge.gateSlots, Challenge.instructionSlots]
  omega


theorem dBits_wire (w : Nat → Wire) (q : Wire) (hq : q∈mappedWires (dBits w)) : q=w 1028 := by
  simp only [dBits,mappedWires,List.mem_flatMap,List.mem_map] at hq
  obtain ⟨b,⟨j,_,rfl⟩,hb⟩ := hq
  split at hb <;> simp_all


/-! ### Last-carry trim of `hAddT1`: the output `H < p < 2^256`, so its top bit is zero -/

theorem hAddT1_eq (w : Nat → Wire) : hAddT1 w = MappedTopZero.oldT (dBits w) w := rfl

theorem hAddT_eq (w : Nat → Wire) : hAddT w = MappedTopZero.topT (dBits w) w (w 1028) := rfl

theorem dBits_drop (w : Nat → Wire) :
    (dBits w).drop 255 = [MappedTopZero.lowBit (w 1028), MappedTopZero.highBit (w 1028)] := by
  have e : (List.range 257).drop 255 = [255,256] := by decide
  have t1 : (2^257-p).testBit 255 = false := by rw [p_val]; decide
  have t2 : p.testBit 255 = true := by rw [p_val]; decide
  have t3 : (2^257-p).testBit 256 = true := by rw [p_val]; decide
  have t4 : p.testBit 256 = false := by rw [p_val]; decide
  rw [dBits, ← List.map_drop, e]
  simp only [List.map_cons, List.map_nil, t1, t2, t3, t4, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, MappedTopZero.lowBit, MappedTopZero.highBit]

theorem hAddT_counts (w : Nat → Wire) :
    toffoliCount (hAddT w) + 2 = toffoliCount (hAddM w) ∧
      measurementCount (hAddT w) = measurementCount (hAddM w) := by
  have a := hAddT1_counts w
  have b : toffoliCount (hAddT w)+1=toffoliCount (hAddT1 w) ∧
      measurementCount (hAddT w)=measurementCount (hAddT1 w) ∧
      Challenge.gateSlots (hAddT w)+7=Challenge.gateSlots (hAddT1 w) :=
    MappedTopZero.topT_counts (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)
  exact ⟨by omega, by omega⟩

section HTopWires
-- Keep elaboration from expanding the whole 257-bit adder's wire set.
attribute [local irreducible] ECDSAAdd.wires

theorem hAddT_wires (w : Nat → Wire) : wires (hAddT w) ⊆ wires (hAddM w) := by
  have b : wires (hAddT w) ⊆ wires (hAddT1 w) :=
    MappedTopZero.topT_wires (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)
  exact Finset.Subset.trans b (hAddT1_wires w)

end HTopWires

theorem hAddT_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (h : GatePhysical (hAddM w)) : GatePhysical (hAddT w) := by
  have nd : [w 1028,w 256,w 1794,w 257].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]
    exact ⟨⟨w_ne w hn _ _ (by omega) (by omega) (by omega),w_ne w hn _ _ (by omega) (by omega) (by omega),
      w_ne w hn _ _ (by omega) (by omega) (by omega)⟩,
      ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),w_ne w hn _ _ (by omega) (by omega) (by omega)⟩,
      w_ne w hn _ _ (by omega) (by omega) (by omega)⟩
  have b : GatePhysical (hAddT1 w) → GatePhysical (hAddT w) :=
    MappedTopZero.topT_physical (dBits w) w (w 1028) (dBits_length w) (dBits_drop w) nd
  exact b (hAddT1_physical w h)

theorem hAddT_slots (w : Nat → Wire) :
    Challenge.gateSlots (hAddT w) + 8 = Challenge.gateSlots (hAddM w) := by
  have a := hAddT1_slots w
  have b : Challenge.gateSlots (hAddT w)+7=Challenge.gateSlots (hAddT1 w) :=
    (MappedTopZero.topT_counts (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)).2.2
  omega

section Rest
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepCompareMF (b0 : BasisState) (k X : Nat) (hk : k<2^256) (hX : X<2^256)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) (gm : g∉mutL w) :
    Triple (MF w b0 0 X 0 false false false false) (comparePart w g k)
      (MF w b0 0 X 0 false (decide (X<(if b0 g then k else 0))) false false) := by
  intro s m h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have sp := hR_src w hn s.basis
  have kx := kR_x w hn s.basis
  have xl := regValue_lt (xR w) s.basis
  have sl := regValue_lt (srcR w) s.basis
  simp only [xR,srcR,wireBlock_length] at xl sl
  rw [h1] at sp; rw [h2] at kx
  have hx : regValue (xR w) s.basis=X := by
    have : regValue (wireBlock w 1026 2) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 1026 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 1026 2) s.basis := Nat.le_mul_of_pos_right _ this
      omega
    omega
  have src0 : regValue (srcR w) s.basis=0 := by omega
  have top0 : regValue (wireBlock w 256 2) s.basis=0 := by
    by_contra hne; have : 1≤regValue (wireBlock w 256 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
    have : 2^256≤2^256*regValue (wireBlock w 256 2) s.basis := Nat.le_mul_of_pos_right _ this
    omega
  have hzero := (regValue_zero _ _).mp h1
  have cc : ∀q∈cR w,s.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    by_cases hi2 : i<258
    · exact hzero _ ((mem_blk w hn i 0 258 (by omega) (by omega)).mpr (by omega))
    · rw [h8 _ ?_]; exact hc i (by omega) (by omega)
      simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
      refine ⟨⟨⟨nb w hn i 0 258 (by omega) (by omega) (by omega),nb w hn i 770 258 (by omega) (by omega) (by omega)⟩,
        nb w hn i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
        exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have m513 : w 513∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 513 0 258 (by omega) (by omega) (by omega),nb w hn 513 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 513 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have cfr := cfCompare w g hn s.basis false k X hk hx cc ((h8 _ m513).trans hcin) gs g514 s m
    ⟨src0,h5,fun _ _ _ => rfl⟩
  obtain ⟨tp,c1',c2',c3'⟩ := cfr
  refine ⟨tp,?_⟩
  simp only [Bool.false_xor] at c2'
  have gv : s.basis g=b0 g := h8 g gm
  rw [gv] at c2'
  have same : ∀q,q∉srcR w → q≠w 514 → (run (comparePart w g k) m s).basis q=s.basis q := c3'
  have srcm : ∀q∈srcR w,q∈mutL w := fun q hq => hR_mut w hn q (blk_sub w 0 256 0 258 (by omega) (by omega) q hq)
  have m514 : w 514∈mutL w := by simp [mutL]
  refine ⟨?_,?_,?_,?_,c2',?_,?_,?_⟩
  · rw [hR_src w hn,c1',regValue_congr _ _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 256 2 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 256 2 (by omega) (by omega) (by omega) (e ▸ hq))),top0]; simp
  · rw [regValue_congr (kR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 770 258 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 770 258 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h2
  · rw [regValue_congr (tR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 1029 256 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 1029 256 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h3
  · rw [same _ (nb w hn 1028 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h4
  · rw [same _ (nb w hn 721 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h6
  · rw [same _ (nb w hn 722 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h7
  · intro q hq
    rw [same q (fun h' => hq (srcm q h')) (fun e => hq (e ▸ m514))]; exact h8 q hq

theorem stepMeasFp (b0 : BasisState) (H X T : Nat) (par f gp : Bool) :
    Triple (MF w b0 H X T par f gp (f && par)) [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]
      (MF w b0 H X T par f gp false) := by
  intro s m h
  rw [run_meas_and (w 722) (w 514) (w 1028) m s (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.2.1,h.2.2.2.2.1,h.2.2.2.1])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp (f && par) s ⟨s.phase,writeBit s.basis (w 722) false⟩ 722
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepMeasGp (b0 : BasisState) (H X T : Nat) (par f fp : Bool) (gm : g∉mutL w)
    (g515 : g≠w 721) :
    Triple (MF w b0 H X T par f (b0 g && par) fp) [.measureX (w 721) [] [.CZ g (w 1028)]]
      (MF w b0 H X T par f false fp) := by
  intro s m h
  rw [run_meas_and (w 721) g (w 1028) m s g515
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.1,h.2.2.2.1,h.2.2.2.2.2.2.2 g gm])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f (b0 g && par) fp s ⟨s.phase,writeBit s.basis (w 721) false⟩ 721
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepCopy (b0 : BasisState) (X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 X T par f gp fp) (copyRegister none (wireBlock w 770 257) (hpR w))
      (MF w b0 (2*(X%2^257)) X T par f gp fp) := by
  intro s m h
  have nd : (wireBlock w 770 257++hpR w).Nodup := List.nodup_append'.mpr
    ⟨blk_nd w hn 770 257 (by omega),blk_nd w hn 1 257 (by omega),
      blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hval⟩ := copyRegister_correct none (wireBlock w 770 257) (hpR w)
    (by simp [hpR,wireBlock_length]) nd (by simp) s m
  refine ⟨hp,stepH w hn b0 0 X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (copyRegister none (wireBlock w 770 257) (hpR w)) m s).basis
    have kl := kR_low w hn s.basis
    have ll := regValue_lt (wireBlock w 770 257) s.basis
    simp only [wireBlock_length] at ll
    rw [h.1] at sp; rw [h.2.1] at kl
    rw [sp2,hval,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega))]
    simp only [copyValue]
    have e0 : regValue (hpR w) s.basis=0 := by omega
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    rw [e0,b0',Nat.zero_xor]
    have : regValue (wireBlock w 770 257) s.basis=X%2^257 := by omega
    rw [this]; simp

end Rest


section Rest2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem aC_out : ∀q∈aC w,q∉mutL w := by
  intro q hq hm
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
  · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
  all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm

theorem w1797_out : w 1797∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
    nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
    exact w_ne w hn _ _ (by omega) (by omega) (by omega)

theorem stepHAdd (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddM w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  rw [hAddM]
  have nd : (w 1797::(hpR w++hC2 w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),
      blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
  have srcw : ∀q∈mappedWires (dBits w),q∉w 1797::(hpR w++hC2 w) := by
    intro q hq
    rw [dBits_wire w q hq]
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
      nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC2 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 256 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (dBits w) (hpR w) (hC2 w) (w 1797) nd srcw
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length]) s m cl
  refine ⟨hp,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)) m s).basis
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have e0 : regValue (hpR w) s.basis=Y := by rw [b0'] at sp; simp at sp; omega
    rw [sp2,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega)),b0',hval,dBits_value,e0,
      h.2.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin]
    simp [hpR,wireBlock_length]

theorem stepHAddT (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hH : (delta par+Y)%2^257<2^256) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddT w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  have h17 : w 1797 ≠ w 1540 := w_ne w hn 1797 1540 (by omega) (by omega) (by omega)
  have c17 : s.basis (w 1797)=false := (h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin
  have m95 : w 1795∈aC w := (mem_blk w hn 1795 1540 257 (by omega) (by omega)).mpr (by omega)
  have c95 : s.basis (w 1795)=false := (h.2.2.2.2.2.2.2 _ (aC_out w hn _ m95)).trans (hc _ m95)
  have post := (stepHAdd w hn b0 Y X T par f gp fp hY hc hcin s [] h).2
  have top : (run (MappedTopZero.oldT (dBits w) w) [] s).basis (w 257)=false := by
    rw [← hAddT1_eq, hAddT1_run w h17 [] s c17]
    have bit := regValue_bit (hR w) 257 0 (run (hAddM w) [] s).basis (by simp [hR,wireBlock_length])
    have port : (hR w).getD 257 0=w 257 := rfl
    rw [port,post.1] at bit
    have lt : 2*((delta par+Y)%2^257)<2^257 := by
      rw [show (2:Nat)^257=2*2^256 by norm_num]; omega
    rw [Nat.div_eq_of_lt lt] at bit
    cases hb : (run (hAddM w) [] s).basis (w 257) <;> simp_all
  have inj : ∀ i j,i<1798 → j<1798 → w i=w j → i=j :=
    fun i j hi hj e => skywalkPool_index_inj w hn i j hi hj e
  have eq := MappedTopZero.topT_run (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)
    (fun q hq => dBits_wire w q hq) inj rfl s m c95 top
  rw [hAddT_eq,eq,← hAddT1_eq,hAddT1_run w h17 m s c17]
  exact stepHAdd w hn b0 Y X T par f gp fp hY hc hcin s m h

theorem stepW0 (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 (2*Y) X T par f gp fp) [.CX (w 1028) (w 0),.X (w 0)]
      (MF w b0 (2*Y+(!par).toNat) X T par f gp fp) := by
  intro s m h
  have e : run [.CX (w 1028) (w 0),.X (w 0)] m s=⟨s.phase,writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028)))⟩ := by
    simp [run,writeBit]
  rw [e]
  refine ⟨rfl,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq
    have : q≠w 0 := fun e' => hq (e' ▸ (mem_blk w hn 0 0 258 (by omega) (by omega)).mpr (by omega))
    simp [writeBit,Function.update_of_ne this]
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have rest : regValue (hpR w) (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))=
        regValue (hpR w) s.basis := regValue_congr _ _ _ (fun q hq => by
      have : q≠w 0 := fun e' => nb w hn 0 1 257 (by omega) (by omega) (by omega) (e' ▸ hq)
      simp [writeBit,Function.update_of_ne this])
    rw [sp2,rest,b0',h.2.2.2.1]
    rw [b0'] at sp
    simp [writeBit] at sp ⊢
    omega

theorem stepErase (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hH : H<2^257) (hf : f=decide (H/2<T)) :
    Triple (MF w b0 H X T par f gp fp) (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))
      (MF w b0 H X T par false gp fp) := by
  intro s m h
  have nd : (w 514::w 1797::(hp8 w++tR w++hC3 w)).Nodup := by
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
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),⟨nb w hn 514 1 256 (by omega) (by omega) (by omega),
        nb w hn 514 1029 256 (by omega) (by omega) (by omega)⟩,nb w hn 514 1540 255 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC3 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 255 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have sp := hR_split w hn s.basis
  rw [h.1] at sp
  have e8 : hpR w=hp8 w++wireBlock w 257 1 := by rw [hpR,hp8,wireBlock_append]
  have sp8 := regValue_append (hp8 w) (wireBlock w 257 1) s.basis
  rw [←e8] at sp8
  have l8 := regValue_lt (hp8 w) s.basis
  simp only [hp8,wireBlock_length] at sp8 l8
  have hpv : regValue (hp8 w) s.basis=H/2 := by
    have : regValue (wireBlock w 257 1) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 257 1) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 257 1) s.basis := Nat.le_mul_of_pos_right _ this
      cases hb : s.basis (w 0) <;> simp [hb] at sp <;> omega
    cases hb : s.basis (w 0) <;> simp [hb] at sp <;> simp only [hp8] at * <;> omega
  have r := eraseLtChain_correct (hp8 w) (tR w) (hC3 w) (w 1797) (w 514) nd
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length]) s m cl
    (by rw [h.2.2.2.2.1,hpv,h.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin,hf]; simp)
  rw [r]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 514) false⟩ 514
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

end Rest2


section Compose
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem g_mut (hg : g∉skywalkPoolWires w) : g∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨g_out w hn g hg 0 258 (by omega),g_out w hn g hg 770 258 (by omega)⟩,g_out w hn g hg 1029 256 (by omega)⟩,
    g_ne w hn g hg 1028 (by omega),g_ne w hn g hg 514 (by omega),g_ne w hn g hg 721 (by omega),g_ne w hn g hg 722 (by omega)⟩

theorem low_bit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState)
    (h : MF w b0 H X T par f gp fp s) : s (w 770)=decide (X%2=1) := by
  have sp := kR_split w hn s
  rw [h.2.1] at sp
  cases hb : s (w 770) <;> simp [hb] at sp ⊢ <;> omega

omit hn in
theorem xor_clear (a b c : Bool) : (((a ^^ (((false ^^ a) ^^ b) ^^ c)) ^^ b) ^^ c)=false := by
  cases a <;> cases b <;> cases c <;> rfl
omit hn in
theorem xor_clear2 (a c : Bool) : ((a ^^ ((false ^^ a) ^^ c)) ^^ c)=false := by
  cases a <;> cases c <;> rfl

theorem stepPar (b0 : BasisState) (k X : Nat) (f : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 0 X 0 false f false false) (parGates w g k)
      (MF w b0 0 (2*(X/2)) 0 (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f) f false false) := by
  have gm := g_mut w g hn hg
  have g1028 : g≠w 1028 := g_ne w hn g hg 1028 (by omega)
  have g770 : g≠w 770 := g_ne w hn g hg 770 (by omega)
  have e1 : w 770≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e2 : w 514≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e3 : w 1028≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e4 : w 514≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have gv (H X T : Nat) (par f gp fp : Bool) : ∀s : BasisState,MF w b0 H X T par f gp fp s → s g=b0 g :=
    fun s h => h.2.2.2.2.2.2.2 g gm
  have xs : X=2*(X/2)+(decide (X%2=1)).toNat := by
    rcases Nat.mod_two_eq_zero_or_one X with hx|hx <;> simp [hx] <;> omega
  apply Triple.conseq (fun s h => by rw [xs] at h; exact h) ?_ (fun s h => h)
  by_cases hk : k%2=1
  · rw [parGates,if_pos hk,if_pos hk]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false g (b0 g) g1028 (gv _ _ _ _ _ _ _)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 _ _ f false false g (b0 g) g770 (gv _ _ _ _ _ _ _)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear] at h
    simpa [hk] using h
  · rw [parGates,if_neg hk,if_neg hk]
    try simp only [List.nil_append]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear2] at h
    simpa [hk] using h

theorem stepRot (b0 : BasisState) (X : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 (2*(X/2)) 0 par f gp fp) (rotateRight (kR w)) (MF w b0 0 (X/2) 0 par f gp fp) := by
  intro s m h
  have r := rotateRight_spec (kR w) (kR_nd w hn) (2*(X/2)) (by omega) s m h.2.1
  have fr := rotate_frame (kR w) s m
  refine ⟨r.1,stepK w hn b0 0 _ 0 par f gp fp s _ h fr.2.1 _ ?_⟩
  have := r.2
  change regValue (kR w) _=_ at this
  rw [this]; omega

end Compose


/-- Complement the entire 258-bit K bank after shifting the original input. -/
theorem stepNotK (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 H X T par f gp fp) (notRegister (kR w))
      (MF w b0 H (2^258-1-X) T par f gp fp) := by
  intro s m hs
  rw [notRegister_correct (kR w) (kR_nd w hn)]
  refine ⟨rfl,?_⟩
  apply stepK w hn b0 H X T par f gp fp s _ hs
  · intro q hq
    change (if q∈kR w then !s.basis q else s.basis q)=s.basis q
    simp only [if_neg hq]
  · change regValue (kR w) (fun q => if q∈kR w then !s.basis q else s.basis q)=_
    rw [regValue_congr (kR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,hs.2.1]
    simp [kR,wireBlock_length]




theorem tk_lt (k : Nat) (G f par : Bool) : tk k G f par<2^258 := by
  unfold tk
  split_ifs <;> first | exact Nat.mod_lt _ (by norm_num) | norm_num

theorem xlt (a b : Nat) (ha : a<2^258) (hb : b<2^258) : a^^^b<2^258 := Nat.xor_lt_two_pow ha hb

theorem c1_lt (k : Nat) : c1 k<2^258 := tk_lt k _ _ _
theorem cg_lt (k : Nat) : cg k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cf_lt (k : Nat) : cf k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cp_lt (k : Nat) : cp k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cgp_lt (k : Nat) : cgp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)
theorem cfp_lt (k : Nat) : cfp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)

def lkv (k : Nat) (G f par gp fp : Bool) : Nat :=
  c1 k ^^^ (if G then cg k else 0) ^^^ (if f then cf k else 0) ^^^ (if par then cp k else 0) ^^^
    (if gp then cgp k else 0) ^^^ (if fp then cfp k else 0)

theorem lkv_eq (k : Nat) (G f par : Bool) (hfg : f=true → G=true) :
    lkv k G f par (G && par) (f && par)=tk k G f par := by
  cases G <;> cases f <;> cases par <;> simp at hfg <;>
    simp [lkv,c1,cg,cf,cp,cgp,cfp,Nat.xor_assoc,Nat.xor_comm,Nat.xor_left_comm,Nat.xor_self]

def ltv (k : Nat) (G gp : Bool) : Nat := (if G then thrA k else 0) ^^^ (if gp then thrB k else 0)

theorem ltv_eq (k : Nat) (G par : Bool) : ltv k G (G && par)=thr k G par := by
  cases G <;> cases par <;> simp [ltv,thr,thrA,thrB,Nat.xor_assoc,Nat.xor_self]

section Compose2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepLoadK (b0 : BasisState) (k H X T : Nat) (par f gp fp : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadK w g k)
      (MF w b0 (H^^^lkv k (b0 g) f par gp fp) X T par f gp fp) := by
  have gm := g_mut w g hn hg
  have gh : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h515 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h516 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t := (stepXorH w hn b0 H X T par f gp fp (c1 k) (c1_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp g (b0 g) gh (fun s h => h.2.2.2.2.2.2.2 g gm) (cg k) (cg_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 514) f h514 (fun s h => h.2.2.2.2.1) (cf k) (cf_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 1028) par h1028 (fun s h => h.2.2.2.1) (cp k) (cp_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (cgp k) (cgp_lt k)).seq
    (stepMaskH w hn b0 _ X T par f gp fp (w 722) fp h516 (fun s h => h.2.2.2.2.2.2.1) (cfp k) (cfp_lt k))))))
  unfold loadK
  simp only [List.append_assoc]
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have e : H^^^c1 k^^^(if b0 g then cg k else 0)^^^(if f then cf k else 0)^^^(if par then cp k else 0)^^^
      (if gp then cgp k else 0)^^^(if fp then cfp k else 0)=H^^^lkv k (b0 g) f par gp fp := by
    simp only [lkv,Nat.xor_assoc]
  rw [e] at h; exact h

theorem stepLoadT (b0 : BasisState) (k H X T : Nat) (hk : k<p) (par f gp fp : Bool)
    (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadT w g k)
      (MF w b0 H X (T^^^ltv k (b0 g) gp) par f gp fp) := by
  have gm := g_mut w g hn hg
  have gt : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have h515 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  rw [p_val] at hk
  have la : thrA k<2^256 := by unfold thrA; omega
  have lb : thrB k<2^256 := Nat.xor_lt_two_pow la (by rw [p_val]; omega)
  have t := (stepMaskT w hn b0 H X T par f gp fp g (b0 g) gt (fun s h => h.2.2.2.2.2.2.2 g gm) (thrA k) la).seq
    (stepMaskT w hn b0 H X _ par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (thrB k) lb)
  unfold loadT
  apply Triple.conseq (fun _ h => h) t
  intro s h
  simpa only [ltv,Nat.xor_assoc] using h

end Compose2


section Main
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let f := decide (X<(if G then k else 0))
    let dx := (p-1-X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    Triple (MF w b0 0 X 0 false false false false) (merged w g k)
      (MF w b0 (2*H+(!par).toNat) K 0 par false false false) := by
  intro G f dx par K H
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX G
  change decide (X%2=1)=x0 k G f par at a1
  change (2^258-1-X/2+tk k G f par)%2^258=K at a2
  change H=dx/2+(if par then hConstant else 0) at a3
  change f=decide (H<thr k G par) at a4
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hpar : (decide (X%2=1) ^^ (G && decide (k%2=1)) ^^ f)=par := by
    have e : decide (X%2=1)=x0 k G f par := a1
    rw [e]; unfold x0 ksel0
    generalize (G && decide (k%2=1))=a
    cases par <;> cases a <;> cases f <;> rfl
  have hfg : f=true → G=true := by
    intro hf; cases hG : G
    · have : f=false := by
        simp only [f,hG,Bool.false_eq_true,if_false,decide_eq_false_iff_not]; rw [p_val] at hX; omega
      rw [this] at hf; exact absurd hf (by simp)
    · rfl
  have fC : decide (X<(if b0 g then k else 0))=f := by simp [f,G,cmpC]
  have s1 := stepCompareMF w g hn b0 k X (by rw [p_val] at hk; omega) (by rw [p_val] at hX; omega)
    hc hcin (g_out w hn g hg 0 256 (by omega)) (g_ne w hn g hg 514 (by omega)) gm
  rw [fC] at s1
  have s2 := stepPar w g hn b0 k X f hg
  rw [show (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f)=par from hpar] at s2
  have s3 := stepRot w hn b0 X par f false false
  have s3n := stepNotK w hn b0 0 (X/2) 0 par f false false
  have s4a := stepCCX w hn b0 0 (2^258-1-X/2) 0 par f false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s4a
  have s4b := stepCCX w hn b0 0 (2^258-1-X/2) 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s4b
  have s5 := stepLoadK w g hn b0 k 0 (2^258-1-X/2) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkv_eq k G f par hfg] at s5
  have hdx : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
  have hK : (tk k G f par+(2^258-1-X/2))%2^258=K := by
    rw [Nat.add_comm]
    exact a2
  have hWord : (tk k G f par+(2^258-1-X/2))%2^258=
      E1CallerValueFactsResearch.Kword dx par := by
    simpa only [K,E1CallerValueFactsResearch.Kword] using hK
  have s6 := Tail52.stepKAddFlag52 w hn b0 (tk k G f par) (2^258-1-X/2) 0 par f
    (G && par) (f && par) hac h1797 dx hdx rfl hWord
  rw [hK] at s6
  have s7 := stepLoadK w g hn b0 k (tk k G f par) K 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkv_eq k G f par hfg,Nat.xor_self] at s7
  have s8 := stepMeasFp w hn b0 0 K 0 par f (G && par)
  have s9 := stepCopy w hn b0 K 0 par f (G && par) false
  have hHlt : 2*H+(!par).toNat<2^257 := by
    have dxl : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
    rw [a3]; rw [p_val] at dxl
    cases par <;> simp [hC_val] <;> omega
  have hH10 : (delta par+K%2^257)%2^257<2^256 := by
    rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]]
    have h2 := hHlt
    have h3 := Bool.toNat_le (!par)
    rw [show (2:Nat)^257=2*2^256 by norm_num] at h2
    omega
  have s10 := stepHAddT w hn b0 (K%2^257) K 0 par f (G && par) false (Nat.mod_lt _ (by norm_num)) hac h1797 hH10
  rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]] at s10
  have s11 := stepW0 w hn b0 H K 0 par f (G && par) false
  have s12 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K 0 hk par f (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltv_eq] at s12
  have s13 := stepErase w hn b0 (2*H+(!par).toNat) K (thr k G par) par f (G && par) false hac h1797 hHlt
    (by rw [show (2*H+(!par).toNat)/2=H by cases par <;> simp <;> omega]; exact a4)
  have s14 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K (thr k G par) hk par false (G && par) false hg
  rw [show b0 g=G from rfl,ltv_eq,Nat.xor_self] at s14
  have s15 := stepMeasGp w g hn b0 (2*H+(!par).toNat) K 0 par false false gm (g_ne w hn g hg 721 (by omega))
  have t := s1.seq (s2.seq ((s3.seq s3n).seq (s4a.seq (s4b.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq (s13.seq (s14.seq s15))))))))))))))
  unfold merged prodPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

end Main


section Final
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

/-- The reflected-input merged circuit leaves exactly the direct-first-tick state for
`(p-1-X+g*k) mod p`, on every measurement record. -/
theorem merged_eq_forward (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (t u : State) (m m' : List Bool)
    (tk0 : regValue (kR w) t.basis=X) (th0 : regValue (hR w) t.basis=0) (tt0 : regValue (tR w) t.basis=0)
    (t1028 : t.basis (w 1028)=false) (t514 : t.basis (w 514)=false) (t515 : t.basis (w 721)=false)
    (t516 : t.basis (w 722)=false)
    (hc : ∀ i, 258 ≤ i → i < 512 → t.basis (w i) = false) (hcin : t.basis (w 513)=false)
    (hac : ∀q∈aC w,t.basis q=false) (h1797 : t.basis (w 1797)=false)
    (hu : u.phase=t.phase) (hu2 : ∀q,q∉kR w → u.basis q=t.basis q)
    (hu3 : regValue (kR w) u.basis=(p-1-X+(if t.basis g then k else 0))%p) :
    run (merged w g k) m t=run (NativeFirstDirect.forward w) m' u := by
  have mf0 : MF w t.basis 0 X 0 false false false false t.basis :=
    ⟨th0,tk0,tt0,t1028,t514,t515,t516,fun _ _ => rfl⟩
  have tri := merged_triple w g hn hg k hk t.basis X hX hc hcin hac h1797 t m mf0
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX (t.basis g)
  generalize hG : t.basis g=G at tri a1 a2 a3 a4 a5 hu3
  generalize hdx : (p-1-X+(if G then k else 0))%p=dx at tri a1 a2 a3 a4 a5 hu3
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

end Final


/-! ### Resources -/

def mSites (w : Nat → Wire) (g : Wire) : List Wire :=
  wireBlock w 0 515++wireBlock w 770 515++wireBlock w 1540 258++[w 721,w 722,g]

theorem in_mSites (w : Nat → Wire) (g : Wire) (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) : w i∈mSites w g := by
  simp only [mSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hi with h|h|h|h|h
  · exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩))
  · subst h; exact Or.inr (Or.inl rfl)
  · subst h; exact Or.inr (Or.inr (Or.inl rfl))

theorem blk_mSites (w : Nat → Wire) (g : Wire) (a n : Nat)
    (h : a + n ≤ 515 ∨ (770 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
    ∀q∈wireBlock w a n,q∈mSites w g := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact in_mSites w g i (by omega)

theorem g_mSites (w : Nat → Wire) (g : Wire) : g∈mSites w g := by simp [mSites]



theorem lsub (w : Nat → Wire) (g : Wire) (l : List Wire) (h : ∀q∈l,q∈mSites w g) :
    l.toFinset⊆(mSites w g).toFinset := by
  intro q hq; exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem gate_sub (w : Nat → Wire) (g : Wire) (i : Instr) (h : ∀q∈i.wires,q∈mSites w g) :
    wires [i]⊆(mSites w g).toFinset := by
  intro q hq
  simp only [wires,Finset.union_empty] at hq
  exact List.mem_toFinset.mpr (h q hq)

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
  have cmp : wires (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (xR w) (srcR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,srcR,xR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 770 256 (by omega) q hq
    · exact B 0 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mSites w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨mskS _,cmp⟩,mskS _⟩
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
  have hNot : wires (notRegister (kR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]
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
    have sub := E1ResourceBridge52Research.flag_support52 w
    rw [← kAdd_literal w] at sub
    apply sub.trans
    refine Finset.union_subset hKOld ?_
    exact Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr (I 1028 (by omega)))
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
  simp only [merged,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hC,⟨hP,hR'⟩,hNot⟩,hPr⟩,hL⟩,hK⟩,hL⟩,hM1⟩,hCp⟩,hHT⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩


theorem merged_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (merged w g k)=1022 ∧ measurementCount (merged w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (kR w)
  have c1' := compareLt_counts none (xR w) (srcR w) (cR w) (w 513) (w 514)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,srcR,xR,wireBlock_length])
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
  have lx : (srcR w).length=256 := by simp [srcR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  rw [lx] at c1'
  rw [lk] at k1
  have kc := E1WholeKAdd52Research.flag_counts52 w
  have kT : toffoliCount (E1WholeKAdd52Research.flagKAdd52 w)=255 := by
    have oldT := k1.1
    change toffoliCount (KAddCallerBridgeResearch.literalKAdd w)=257 at oldT
    omega
  have kM : measurementCount (E1WholeKAdd52Research.flagKAdd52 w)=257 := by
    have oldM := k1.2
    change measurementCount (KAddCallerBridgeResearch.literalKAdd w)=257 at oldM
    omega
  rw [lh] at h1
  rw [lt] at e1
  have hT := hAddT_counts w
  rw [hAddM,h1.1,h1.2] at hT
  have hT' : toffoliCount (hAddT w)=254 ∧ measurementCount (hAddT w)=256 := by omega
  simp only [merged,comparePart,prodPart,loadK,hT'.1,hT'.2,loadT,toffoliCount_append,
    measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,n1.1,n1.2,c1'.1,c1'.2.1,
    r1.1,r1.2.1,kT,kM,h1.1,h1.2,e1.1,e1.2,cp1.1,cp1.2,pg.1,pg.2]
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
  have cmpP : GatePhysical (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 770 256 0 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
      have l1 : (xR w++srcR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 770 256 (by omega),src_nd w hn,a1⟩
      have l2 : (xR w++srcR w++cR w).Nodup := by
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
        exact ⟨ne 514 513 (by omega) (by omega) (by omega),nb w hn 514 770 256 (by omega) (by omega) (by omega),
          nb w hn 514 0 256 (by omega) (by omega) (by omega),nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 513 770 256 (by omega) (by omega) (by omega),nb w hn 513 0 256 (by omega) (by omega) (by omega),
          nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
    · simp
  have kOldP : GatePhysical (kAddM w) := by
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
  have kP : GatePhysical (E1WholeKAdd52Research.flagKAdd52 w) := by
    apply E1ResourceBridge52Research.flag_gatePhysical_pool52 w hn
    simpa only [← kAdd_literal w] using kOldP
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
    exact ⟨⟨maskedConstant_physical _ _ _ gS,cmpP⟩,maskedConstant_physical _ _ _ gS⟩
  have m1 : GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have m2 : GatePhysical [.measureX (w 721) [] [.CZ g (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have hPT : GatePhysical (hAddT w) := hAddT_physical w hn hP
  simp only [merged,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cP,⟨parP,rotP⟩,notRegister_physical _⟩,prodP⟩,lkP⟩,kP⟩,lkP⟩,m1⟩,cpP⟩,hPT⟩,w0P⟩,ltP⟩,eP⟩,ltP⟩,m2⟩

end Phys




theorem merged_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (merged w g k)≤25000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (xR w) (srcR w) (cR w) (w 513) (w 514)
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
  have cP : Challenge.gateSlots (comparePart w g k)≤2*256+12*256+4 := by
    simp only [comparePart,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
    have := m1 g (srcR w) k
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
  have nk : Challenge.gateSlots (notRegister (kR w))=258 := by
    simp [Baselines.notRegister_gateSlots,kR,wireBlock_length]
  have hS := hAddT_slots w
  rw [hAddM] at hS
  simp only [merged,Challenge.gateSlots_append,pr,w0,q1,q2,cp,nk]
  omega

end ECDSAAdd.Entrant.E1Reflected

end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.E1ReflectedPlacement =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1QubitPlacement
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1Reflected

/-! Full all-record physical transfer for the reflected-input merged entry.
Research source, NOT elaborated here. The r-state relation is the internal
boundary supplied by the removed square output reflection, not a new external
point-addition premise. All clean scratch values are derived from dialogPool0.
-/
namespace ECDSAAdd.Entrant.E1ReflectedPlacement
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement

def entryR (L : ControlledPointLayout) (k : Fp) : Program :=
  renameProgram (pmapR L) (E1Reflected.merged base (base 2400) k.val)

theorem mergedR_S (k : Nat) : wires (E1Reflected.merged base (base 2400) k)⊆S :=
  E1Reflected.merged_support base (base 2400) k

section Entry
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem entryR_eq (k : Fp) (s r : State) (X : Nat) (hX : X<p) (G : Bool)
    (hx : regValue L.point.x s.basis=X) (hg : s.basis L.core.generic=G)
    (hc : regValue L.dialogPool s.basis=0)
    (rphase : r.phase=s.phase)
    (rx : regValue L.point.x r.basis=p-1-X)
    (rout : ∀q,q∉L.point.x → r.basis q=s.basis q) (m1 m2 : List Bool) :
    run (entryR L k) m1 s=run (fastConstAdd L L.point.x k++E1QubitPlacement.tickF L) m2 r := by
  have inj := pmap_inj L hw hn
  have pool := pmap_pool L hw hn
  have hzero := (regValue_zero _ _).mp hc
  let F := pmapR L
  let t : State := pullState F s
  have clean (q : Wire) (hq : q∈S) (h1 : q∉wireBlock base 770 256) (h2 : q≠base 2400) :
      t.basis q=false := hzero _ (pool q hq h1 h2)
  have inS (i : Nat) (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      base i∈S := List.mem_toFinset.mpr (E1Reflected.in_mSites base (base 2400) i hi)
  have notx (i : Nat) (hi : ¬ (770 ≤ i ∧ i < 1026)) : base i∉wireBlock base 770 256 := by
    intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj; have := base_injective e; omega
  have ne2400 (i : Nat) (hi : i≠2400) : base i≠base 2400 := fun e => hi (base_injective e)
  have cl (i : Nat) (hi : i < 515 ∨ (1026 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      t.basis (base i)=false :=
    clean _ (inS i (by omega)) (notx i (by omega)) (ne2400 i (by omega))
  have blkz (a n : Nat) (h : a + n ≤ 515 ∨ (1026 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
      regValue (wireBlock base a n) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (by omega)
  have xval : regValue (wireBlock base 770 256) t.basis=X := by
    change regValue (wireBlock base 770 256) (fun q => s.basis (F q))=X
    rw [regValue_pull,pmap_x L hw hn,hx]
  have tk0 : regValue (E1Reflected.kR base) t.basis=X := by
    rw [E1Reflected.kR_x base base_pool_nodup,show E1Reflected.xR base=wireBlock base 770 256 from rfl,xval,
      blkz 1026 2 (by omega)]
    simp
  have tg : t.basis (base 2400)=G := by
    change s.basis (pmapR L (base 2400))=G
    rw [pmap_g L hw hn,hg]
  -- The reflected comparison state differs only on x; no new scratch premise.
  have gx : L.core.generic∉L.point.x := ((E1QubitPlacement.lay L hw hn _).2.2 rfl).1
  have px (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    ((E1QubitPlacement.lay L hw hn q).2.1 hq).1
  have rg : r.basis L.core.generic=G := (rout _ gx).trans hg
  have rc : regValue L.dialogPool r.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq => rout q (px q hq)),hc]
  have xrlt : p-1-X<p := by
    rw [E1Reflected.p_val] at hX ⊢
    omega
  have fca := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k (p-1-X) G xrlt r
    (m2.take (measurementCount (fastConstAdd L L.point.x k))) rg rx rc
  generalize hs1 : run (fastConstAdd L L.point.x k) (m2.take (measurementCount (fastConstAdd L L.point.x k))) r=s1 at fca
  obtain ⟨p1r,x1,o1r⟩ := fca
  have p1 : s1.phase=s.phase := p1r.trans rphase
  have o1 (q : Wire) (hq : q∉L.point.x) : s1.basis q=s.basis q := (o1r q hq).trans (rout q hq)
  let u : State := ⟨t.phase,fun q => if q∈E1Reflected.kR base then s1.basis (F q) else t.basis q⟩
  have hu2 : ∀q,q∉E1Reflected.kR base → u.basis q=t.basis q := by
    intro q hq; simp [u,hq]
  have xS : ∀q∈L.point.x,∃a∈S,F a=q ∧ a∈wireBlock base 770 256 := by
    intro q hq
    rw [←pmap_x L hw hn] at hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    refine ⟨a,?_,rfl,ha⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_range'_1] at hi
    exact inS i (by omega)
  have hu3 : regValue (E1Reflected.kR base) u.basis=(p-1-X+(if t.basis (base 2400) then k.val else 0))%p := by
    rw [tg,E1Reflected.kR_x base base_pool_nodup]
    have e1 : regValue (E1Reflected.xR base) u.basis=regValue L.point.x s1.basis := by
      rw [←pmap_x L hw hn,←regValue_pull]
      apply regValue_congr
      intro q hq
      have : q∈E1Reflected.kR base := E1Reflected.blk_sub base 770 256 770 258 (by omega) (by omega) q hq
      simp only [u,this,if_true]
      rfl
    have e2 : regValue (wireBlock base 1026 2) u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      have kq : base i∈E1Reflected.kR base := E1Reflected.blk_sub base 1026 2 770 258 (by omega) (by omega) _ hq
      have outx : F (base i)∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha (base i) (inS i (by omega)) ea
        subst this
        exact notx i (by omega) ax
      simp only [u,kq,if_true]
      rw [o1 _ outx]
      exact cl i (by omega)
    rw [e1,e2,x1]; simp
  have t1 := (regValue_zero _ _).mp (blkz 0 258 (by omega))
  have eqL := E1Reflected.merged_eq_forward base (base 2400) base_pool_nodup g2400 k.val k.isLt X hX t u m1
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) tk0 (blkz 0 258 (by omega))
    (blkz 1029 256 (by omega)) (cl 1028 (by omega)) (cl 514 (by omega)) (cl 721 (by omega)) (cl 722 (by omega))
    (fun i h1 h2 => cl i (by omega)) (cl 513 (by omega))
    (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact cl i (by omega)) (cl 1797 (by omega)) rfl hu2 hu3
  -- transport both sides
  have hS : ∀q∈S,t.basis q=s.basis (F q) := fun q _ => rfl
  have newSide := run_rename_pool F S inj _ (mergedR_S k.val) m1 t s rfl hS
  have uS : ∀q∈S,u.basis q=s1.basis (F q) := by
    intro q hq
    by_cases kq : q∈E1Reflected.kR base
    · simp [u,kq]
    · simp only [u,kq,if_false]
      change s.basis (F q)=s1.basis (F q)
      have outx : F q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha q hq ea
        subst this
        exact kq (E1Reflected.blk_sub base 770 256 770 258 (by omega) (by omega) _ ax)
      rw [o1 _ outx]
  have oldSide := run_rename_pool F S inj _ forward_S
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) u s1 (by simp [u,t,pullState,p1]) uS
  have rhs : run (fastConstAdd L L.point.x k++E1QubitPlacement.tickF L) m2 r=
      run (E1QubitPlacement.tickF L) (m2.drop (measurementCount (fastConstAdd L L.point.x k))) s1 := by
    rw [run_append,hs1]
  rw [rhs]
  apply State.extensionality
  · rw [entryR,newSide.1,eqL,E1QubitPlacement.tickF,oldSide.1]
  · funext q
    by_cases im : q∈S.image F
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp im
      rw [entryR,newSide.2 a ha,eqL,E1QubitPlacement.tickF,oldSide.2 a ha]
    · rw [entryR,run_rename_pool_outside F S _ (mergedR_S k.val) m1 s q im,E1QubitPlacement.tickF,
        run_rename_pool_outside F S _ forward_S _ s1 q im]
      have outx : q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,_⟩ := xS _ hm
        exact im (Finset.mem_image.mpr ⟨a,ha,ea⟩)
      rw [o1 q outx]

end Entry

open Challenge
attribute [local irreducible] wires

theorem entryR_counts (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (entryR L k)=1022 ∧ measurementCount (entryR L k)=1027 := by
  have r := renameProgram_counts (pmapR L) (E1Reflected.merged base (base 2400) k.val)
  have c := E1Reflected.merged_counts base (base 2400) k.val
  rw [entryR,r.1,r.2]; exact c

theorem entryR_slots (L : ControlledPointLayout) (k : Fp) : gateSlots (entryR L k)≤25000 := by
  simpa only [entryR,Baselines.rename_gateSlots] using
    E1Reflected.merged_slots base (base 2400) k.val

theorem entryR_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (entryR L k) := by
  rw [entryR]
  exact gatePhysical_rename_support (pmapR L) (E1Reflected.merged base (base 2400) k.val)
    (fun a ha b hb e => pmap_inj L hw hn a (mergedR_S k.val ha) b (mergedR_S k.val hb) e)
    (E1Reflected.merged_physical base (base 2400) base_pool_nodup g2400 k.val)

theorem entryR_sites (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryR L k)⊆(OB5Support.sites L).toFinset := by
  have hlog : wires (renameProgram sig (renameProgram rho
      (E1Reflected.merged base (base 2400) k.val)))⊆OB5Support.logicalSites := by
    intro q hq
    simp only [renameProgram_support,Finset.mem_image] at hq
    obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩ := hq
    obtain ⟨j,rfl,hj⟩ := S_cases b (mergedR_S k.val hb)
    rw [rho_base,sig_base]
    exact sw_logical _ (rhoN_range j hj)
  have h := OB5Support.placed_support_logical L hw _ hlog
  simpa only [entryR,renameProgram_comp,pmapR,pmap,Function.comp_def] using h

/-- Both the ordinary and reflected E1 programs have the same support envelope. -/
theorem logicalR_omits (k i : Nat)
    (hi : i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719]) :
    base i∉wires (renameProgram sig (renameProgram rho
      (E1Reflected.merged base (base 2400) k))) := by
  intro h
  simp only [renameProgram_support,Finset.mem_image] at h
  obtain ⟨a,⟨b,hb,rfl⟩,eq⟩ := h
  obtain ⟨j,rfl,hj⟩ := S_cases b (mergedR_S k hb)
  rw [rho_base,sig_base] at eq
  have e := base_injective eq
  exact sw_avoid j hj (e.symm ▸ hi)

end ECDSAAdd.Entrant.E1ReflectedPlacement
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Entry =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588BFFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Square
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1ReflectedPlacement

/-! Both merged entries retain the complete rolling inverse phases. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires

def tailP (a : Bool) : Program := Rolling1588.stackForward a++skywalkArithmeticClear base

def restE (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (tailP true)++
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))

def restX (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (tailP false)++
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))

def entryStage (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky++E1QubitPlacement.entryM L kx++restE L

def squareEntry (L : ControlledPointLayout) (k : Fp) : Program :=
  ReflectionE1Square.program L++E1ReflectedPlacement.entryR L k

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  squareEntry L k++restX L++exitY L cy

theorem entry_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry Rolling1588.entryKernel L=E1QubitPlacement.tickF L++restE L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,Rolling1588.entryKernel,Rolling1588.firstPhase,restE,tailP,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem exit_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.exit Rolling1588.exitKernel L=E1QubitPlacement.tickF L++restX L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,Rolling1588.exitKernel,Rolling1588.firstPhase,restX,tailP,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem entryStage_step (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStage L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  have add:=fastStep_addX L hw hn X Y G origin kx
  have divide:=division_step Rolling1588.entryKernel Rolling1588.entryKernel_support
    Rolling1588.entry_correct L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior:=add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky++E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx++fusedY L ky++E1QubitPlacement.tickF L)
    (R:=restE L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryStage,division,entry_split,List.append_assoc] using prior

/-- The deleted reflection and changed entry use independent record lists.
The equality ends before the common suffix, so no suffix tape equality is assumed. -/
theorem squareEntry_eq (k : Fp) (X Y : Fp) (G : Bool) (origin : BasisState)
    (s : State) (m1 m2 : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (squareEntry L k) m1 s=
      run (SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++
        E1QubitPlacement.tickF L) m2 s := by
  let n1:=measurementCount (ReflectionE1Square.program L)
  let n2:=measurementCount (SquareCarryLoan719BF.program L)
  obtain ⟨a,ha⟩ : ∃a : State,run (ReflectionE1Square.program L) (m1.take n1) s=a := ⟨_,rfl⟩
  obtain ⟨r,hr⟩ : ∃r : State,run (SquareCarryLoan719BF.program L) (m2.take n2) s=r := ⟨_,rfl⟩
  have fresh:=ReflectionE1Square.boundary L hw hn X Y G origin s (m1.take n1) v
  have prior:=SquareCarryLoan719BF.step L hw hn X Y G origin s (m2.take n2) v
  rw [ha] at fresh
  rw [hr] at prior
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  let R:=p-1-Z.val
  have ppos : 0<p := by norm_num [p]
  have rp : R<p := by
    change p-1-Z.val<p
    omega
  have ax : regValue L.point.x a.basis=R:=fresh.2.1
  have ag : a.basis L.core.generic=G :=
    (fresh.2.2 _ (((E1QubitPlacement.lay L hw hn _).2.2 rfl).1)).trans v.generic
  have ac : regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ s.basis
      (fun q hq=>fresh.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).1)),v.clean]
  have involution (n : Nat) (bound : n<p) : n=p-1-(p-1-n) := by omega
  have rx : regValue L.point.x r.basis=p-1-R := by
    have value : regValue L.point.x r.basis=Z.val:=prior.2.x
    exact value.trans (involution Z.val Z.isLt)
  have outside (q : Wire) (hq : q∉L.point.x) : r.basis q=a.basis q := by
    have oldFrame : r.basis q=s.basis q := by
      by_cases hy : q∈L.point.y
      · exact (regValue_eq_iff _ _ _).mp (prior.2.y.trans v.y.symm) q hy
      · have away : q∉L.point.x++L.point.y:=by simp only [List.mem_append,not_or];exact ⟨hq,hy⟩
        exact (prior.2.rest q away).trans (v.rest q away).symm
    exact oldFrame.trans (fresh.2.2 q hq).symm
  have eq:=E1ReflectedPlacement.entryR_eq L hw hn k a r R rp G ax ag ac
    (prior.1.trans fresh.1.symm) rx outside (m1.drop n1) (m2.drop n2)
  simpa only [squareEntry,run_append,n1,n2,ha,hr,List.append_assoc] using eq

theorem secondStage_step (X Y k cy : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStage L k cy)
      (PointDialogValues L Z (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=fusedMultiply_step L hw hn (FrontierEntry1591Callers.exit Rolling1588.exitKernel L)
    (exit_correct Rolling1588.exitKernel Rolling1588.exitKernel_support Rolling1588.exit_correct L hw hn)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStage,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=restX L++exitY L cy)
  · intro s v m1 m2
    exact squareEntry_eq L hw hn k X Y G origin s m1 m2 v
  · simpa only [secondStage,fusedMultiply,exit_split,List.append_assoc,Z] using prior

end Correct
end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Generic =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Entry

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5
  EntryFuse EntryFuseFinite ExitFusionResearch
attribute [local irreducible] run wires

def correction (cx : Fp) : Fp := 3*cx-(SquareCarryLoan719BF.K:Nat)

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStage L (-cx) (-cy)++secondStage L (correction cx) cy++fastConstNeg L cx

def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clrF L++renameProgram (swapF L) (generic L cx cy)++clrF L

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  zrep L++mid L cx cy++zrep L

theorem gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    gen L cx cy=GenericQ5Geometry.wrapG L (generic L cx cy) := rfl

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStage_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold correction
    ring
  have second:=secondStage_step L hw hn (X-cx) a (correction cx) cy true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  have finish:=fastStep_negX L hw hn d (a*d-cy) true origin cx
  simp only [if_true] at finish
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at finish
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at second finish
  exact (first.seq second).seq finish





































































































end Correct
end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Resources =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Generic

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] wires toffoliCount measurementCount gateSlots

abbrev baselineGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ControlLoan1589BFFinal.Offset.generic L (division Rolling1588.entryKernel L)
    (SquareCarryLoan719BF.program L) (FrontierEntry1591Callers.exit Rolling1588.exitKernel L) cx cy

private theorem envelopes_of_shapes (A0 Y T E S R A1 X EY N M RF New Old : Program)
    (newShape : New=(Y++M++E)++(S++RF++X++EY)++N)
    (oldShape : Old=A0++(Y++(T++E))++(S++R)++A1++(T++X)++EY++N) :
    New⊆Old++M++RF ∧ wires New⊆wires Old∪wires M∪wires RF := by
  rw [newShape,oldShape]
  constructor
  · intro i hi
    simp only [List.mem_append] at hi ⊢
    tauto
  · intro q hq
    simp only [wires_append,Finset.mem_union] at hq ⊢
    tauto

private theorem envelopes (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy⊆baselineGeneric L cx cy++E1QubitPlacement.entryM L (-cx)++
      E1ReflectedPlacement.entryR L (correction cx) ∧
    wires (generic L cx cy)⊆wires (baselineGeneric L cx cy)∪
      wires (E1QubitPlacement.entryM L (-cx))∪
        wires (E1ReflectedPlacement.entryR L (correction cx)) := by
  apply envelopes_of_shapes
    (fastConstAdd L L.point.x (-cx)) (fusedY L (-cy)) (E1QubitPlacement.tickF L)
    (restE L) (ReflectionE1Square.program L) (ReflectionE1Square.reflectedTail L)
    (fastConstAdd L L.point.x (3*cx-(ControlLoan1589BFFinal.Offset.K:Nat)))
    (restX L) (exitY L cy) (fastConstNeg L cx) (E1QubitPlacement.entryM L (-cx))
    (E1ReflectedPlacement.entryR L (correction cx))
  · rfl
  · simp only [baselineGeneric,ControlLoan1589BFFinal.Offset.generic,division,
      entry_split,exit_split,ReflectionE1Square.program_split]

theorem instructions_subset (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy⊆baselineGeneric L cx cy++E1QubitPlacement.entryM L (-cx)++
      E1ReflectedPlacement.entryR L (correction cx) :=
  (envelopes L cx cy).1

theorem support_envelope (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (baselineGeneric L cx cy)∪
      wires (E1QubitPlacement.entryM L (-cx))∪
        wires (E1ReflectedPlacement.entryR L (correction cx)) :=
  (envelopes L cx cy).2

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (support_envelope L cx cy).trans (Finset.union_subset
    (Finset.union_subset (Rolling1588BFFinal.generic_support L hw hn cx cy)
      (E1QubitPlacement.entryM_sites L hw (-cx)))
    (E1ReflectedPlacement.entryR_sites L hw (correction cx)))

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old:=ControlLoan1589BFFinal.Offset.generic_physical L hw hn
    (division Rolling1588.entryKernel L) (SquareCarryLoan719BF.program L)
    (FrontierEntry1591Callers.exit Rolling1588.exitKernel L)
    (division_physical Rolling1588.entryKernel Rolling1588.entryKernel_support
      Rolling1588.entryKernel_physical L hw hn)
    (SquareCarryLoan719BF.physical L hw hn)
    (placed_physical Rolling1588.exitKernel Rolling1588.exitKernel_support
      Rolling1588.exitKernel_physical L hw hn) cx cy
  have full : GatePhysical (baselineGeneric L cx cy++E1QubitPlacement.entryM L (-cx)++
      E1ReflectedPlacement.entryR L (correction cx)) := by
    rw [gatePhysical_append,gatePhysical_append]
    exact ⟨⟨old,E1QubitPlacement.entryM_physical L hw hn (-cx)⟩,
      E1ReflectedPlacement.entryR_physical L hw hn (correction cx)⟩
  intro i hi
  exact full i (instructions_subset L cx cy hi)

private def logicalTarget (i : Nat) : Nat :=
  if i=1800 then 2312 else if i=770 then 1026 else if i=1285 then 1541 else
    if i=1286 then 1542 else if i=769 then 1797 else i

private theorem target_facts (L : ControlledPointLayout) (i : Nat)
    (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    wireFn2 L (base (logicalTarget i))=L.core.poolWire i ∧
    base (logicalTarget i)∈OB5Support.logicalSites ∧
    logicalTarget i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals refine ⟨rfl,?_,by decide⟩
  all_goals
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨_,?_,rfl⟩
    simp only [logicalTarget,OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    norm_num

private theorem placed_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (support : wires P⊆OB5Support.logicalSites) (i : Nat)
    (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719])
    (free : base (logicalTarget i)∉wires P) :
    L.core.poolWire i∉wires (renameProgram (wireFn2 L) P) := by
  obtain ⟨map,logical,_⟩:=target_facts L i hi
  rw [renameProgram_support]
  intro used
  obtain ⟨q,hq,eq⟩:=Finset.mem_image.mp used
  have same : wireFn2 L q=wireFn2 L (base (logicalTarget i)):=eq.trans map.symm
  have back:=(placement2 L hw hn).injectiveOnSlots q
    (ArithmeticOB5.logical_sub_old (support hq)) (base (logicalTarget i))
    (ArithmeticOB5.logical_sub_old logical) same
  exact free (back ▸ hq)

private theorem entry_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (E1QubitPlacement.entryM L k) := by
  rw [E1QubitPlacement.entryM_eq]
  exact placed_free L hw hn _ (E1QubitPlacement.logicalM k.val) i hi
    (E1QubitPlacement.merged_omits k.val _ (target_facts L i hi).2.2)

private theorem reflected_logical (k : Nat) :
    wires (renameProgram E1QubitPlacement.sig (renameProgram E1QubitPlacement.rho
      (E1Reflected.merged base (base 2400) k)))⊆OB5Support.logicalSites := by
  intro q hq
  simp only [renameProgram_support,Finset.mem_image] at hq
  obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩:=hq
  obtain ⟨j,rfl,hj⟩:=E1QubitPlacement.S_cases b (E1ReflectedPlacement.mergedR_S k hb)
  rw [E1QubitPlacement.rho_base,E1QubitPlacement.sig_base]
  exact E1QubitPlacement.sw_logical _ (E1QubitPlacement.rhoN_range j hj)

private theorem reflected_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (E1ReflectedPlacement.entryR L k) := by
  have h:=placed_free L hw hn _ (reflected_logical k.val) i hi
    (E1ReflectedPlacement.logicalR_omits k.val _ (target_facts L i hi).2.2)
  simpa only [E1ReflectedPlacement.entryR,renameProgram_comp,E1QubitPlacement.pmapR,
    E1QubitPlacement.pmap,Function.comp_def] using h

private theorem kernel_free (entrySide : Bool) (i : Nat)
    (hi : i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719]) :
    base i∉wires (if entrySide then Rolling1588.entryKernel else Rolling1588.exitKernel) := by
  by_cases a : i=768
  · subst i;cases entrySide
    · exact Rolling1588.exitKernel_768_free
    · exact Rolling1588.entryKernel_768_free
  by_cases b : i=718
  · subst i;cases entrySide
    · exact Rolling1588.exitKernel_718_free
    · exact Rolling1588.entryKernel_718_free
  by_cases c : i=719
  · subst i;cases entrySide
    · exact Rolling1588.exitKernel_719_free
    · exact Rolling1588.entryKernel_719_free
  have old : i∈logicalOmissions := by
    simp only [logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
  cases entrySide
  · exact Rolling1588.exitKernel_free i old
  · exact Rolling1588.entryKernel_free i old

theorem baseline_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (baselineGeneric L cx cy) := by
  have bounds : 515≤ i ∧ i<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega
  have en:=placed_free L hw hn _ Rolling1588.entryKernel_support i hi
    (kernel_free true _ (target_facts L i hi).2.2)
  have ex:=placed_free L hw hn _ Rolling1588.exitKernel_support i hi
    (kernel_free false _ (target_facts L i hi).2.2)
  have sq : L.core.poolWire i∉wires (SquareCarryLoan719BF.program L) := by
    by_cases h : i=719
    · subst i;exact SquareCarryLoan719BF.retired_free719 L hw hn
    · apply SquareCarryLoan719BF.square_free L hw hn i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;tauto
  apply ControlLoan1589BFFinal.Offset.generic_free L hw hn
    (division Rolling1588.entryKernel L) (SquareCarryLoan719BF.program L)
    (FrontierEntry1591Callers.exit Rolling1588.exitKernel L) i bounds _ sq ex cx cy
  intro k
  have constant:=ExitGenericQ5.constant_ports_avoid_large L hw hn i bounds L.point.y (Or.inr rfl)
  simp only [division,FrontierEntry1591Callers.entry,wires_append,Finset.mem_union,not_or]
  exact ⟨fun used=>constant (fusedY_support L hw k used),en⟩

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) := by
  intro used
  have member:=support_envelope L cx cy used
  simp only [Finset.mem_union] at member
  rcases member with (old|ordinary)|reflected
  · exact baseline_free L hw hn cx cy i hi old
  · exact entry_free L hw hn (-cx) i hi ordinary
  · exact reflected_free L hw hn (correction cx) i hi reflected

theorem generic_counts_delta (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (generic L cx cy)+759=toffoliCount (baselineGeneric L cx cy) ∧
    measurementCount (generic L cx cy)+751=measurementCount (baselineGeneric L cx cy) := by
  have first:=E1QubitPlacement.prefix_counts L hw (-cx)
  have second:=E1QubitPlacement.prefix_counts L hw (correction cx)
  have ordinary:=E1QubitPlacement.entryM_counts L (correction cx)
  have reflected:=E1ReflectedPlacement.entryR_counts L (correction cx)
  have square:=ReflectionE1Square.counts_delta L hw
  simp only [generic,entryStage,secondStage,squareEntry,baselineGeneric,
    ControlLoan1589BFFinal.Offset.generic,division,entry_split,exit_split,
    toffoliCount_append,measurementCount_append,correction,SquareCarryLoan719BF.K,
    ControlLoan1589BFFinal.Offset.K,ControlLoan1589BFSquare.K] at first second ordinary reflected square ⊢
  constructor <;> omega

theorem generic_slots_delta (L : ControlledPointLayout) (cx cy : Fp) :
    gateSlots (generic L cx cy)≤ gateSlots (baselineGeneric L cx cy)+50000 := by
  have first:=E1QubitPlacement.entryM_slots L (-cx)
  have second:=E1ReflectedPlacement.entryR_slots L (correction cx)
  simp only [generic,entryStage,secondStage,squareEntry,baselineGeneric,
    ControlLoan1589BFFinal.Offset.generic,division,entry_split,exit_split,
    ReflectionE1Square.program_split,gateSlots_append]
  omega

private theorem baseline_gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    Rolling1588BFFinal.gen L cx cy=GenericQ5Geometry.wrapG L (baselineGeneric L cx cy) := by
  simp only [Rolling1588BFFinal.gen,ControlLoan1589BFFinal.Offset.gen_shape,baselineGeneric]

private theorem wrap_counts_delta (L : ControlledPointLayout) (A B : Program)
    (h : toffoliCount A+759=toffoliCount B ∧ measurementCount A+751=measurementCount B) :
    toffoliCount (GenericQ5Geometry.wrapG L A)+759=toffoliCount (GenericQ5Geometry.wrapG L B) ∧
    measurementCount (GenericQ5Geometry.wrapG L A)+751=measurementCount (GenericQ5Geometry.wrapG L B) := by
  simp only [GenericQ5Geometry.wrapG,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem gen_counts_delta (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+759=toffoliCount (Rolling1588BFFinal.gen L cx cy) ∧
    measurementCount (gen L cx cy)+751=measurementCount (Rolling1588BFFinal.gen L cx cy) := by
  rw [gen_shape,baseline_gen_shape]
  exact wrap_counts_delta L _ _ (generic_counts_delta L hw cx cy)

theorem gen_slots_delta (L : ControlledPointLayout) (cx cy : Fp) :
    gateSlots (gen L cx cy)≤ gateSlots (Rolling1588BFFinal.gen L cx cy)+50000 := by
  have d:=generic_slots_delta L cx cy
  rw [gen_shape,baseline_gen_shape]
  simp only [GenericQ5Geometry.wrapG,gateSlots_append,rename_gateSlots]
  omega

























theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (generic_sites L hw hn cx cy)


private theorem wrapper_counts_delta (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (A B : Program) (h : toffoliCount A+759=toffoliCount B ∧ measurementCount A+751=measurementCount B) :
    toffoliCount (Edges.wrapper L C cy A)+759=toffoliCount (Edges.wrapper L C cy B) ∧
    measurementCount (Edges.wrapper L C cy A)+751=measurementCount (Edges.wrapper L C cy B) := by
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2151444 := by
  have diff:=(wrapper_counts_delta layout (.some hc) cy _ _
    (gen_counts_delta layout layout_widths cx cy)).1
  have old:=Rolling1588BFFinal.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1499214 := by
  have diff:=(wrapper_counts_delta layout (.some hc) cy _ _
    (gen_counts_delta layout layout_widths cx cy)).2
  have old:=Rolling1588BFFinal.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50189199+Rolling1588.slotGrowth := by
  have diff:=gen_slots_delta layout cx cy
  have old:=Rolling1588BFFinal.wrapper_slots C cx cy
  have lift : gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤
      gateSlots (Edges.wrapper layout C cy (Rolling1588BFFinal.gen layout cx cy))+50000 := by
    simp only [Edges.wrapper,Edges.finiteProgram,gateSlots_append,rename_gateSlots]
    omega
  omega

end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Final =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Resources

/-! Current Q1588 BF point with both E1 entries and one deleted reflection. -/
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151444,1499214,1588,50189199+Rolling1588.slotGrowth⟩
















theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151444 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc






































end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- Selected checked E1+TickGap branch follows; merged entries, reflected square and inverse phases are preserved.

-- ===== ECDSAAdd.Submission.Entrant.TickGap1591Arithmetic =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.OneFlag

/-! TickGap arithmetic from public frontier8764679c, MainPre.lean.
The copied proof bodies and circuit definitions are unchanged.
The new-codec forward and phase transports are separate modules. -/

section
-- ===== TickGapBudget =====
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TickGap

theorem scaled_budget (p x i : Nat) (hx : x  ≤  p) :
    ∃ j k : Nat, j+k=i  ∧
      (SkywalkNat.step^[i] (SkywalkNat.init x p)).u * 2^j  ≤  p  ∧
      (SkywalkNat.step^[i] (SkywalkNat.init x p)).v * 2^k  ≤  p := by
  induction i with
  | zero => exact ⟨0,0,rfl,by simpa [SkywalkNat.init] using hx,by simp [SkywalkNat.init]⟩
  | succ i ih =>
    obtain ⟨j,k,hjk,hu,hv⟩ := ih
    rw [Function.iterate_succ_apply']
    generalize SkywalkNat.step^[i] (SkywalkNat.init x p)=z at hu hv ⊢
    by_cases hz : z.u=0
    · refine ⟨j+1,k,by omega,?_,?_⟩
      · simp [SkywalkNat.step,hz]
      · simpa [SkywalkNat.step,hz] using hv
    · by_cases he : z.u%2=0
      · refine ⟨j+1,k,by omega,?_,?_⟩
        · simp only [SkywalkNat.step,if_neg hz,if_pos he,pow_succ]
          have hhalf : z.u/2*2 ≤ z.u := by omega
          nlinarith [Nat.mul_le_mul_right (2^j) hhalf]
        · simpa [SkywalkNat.step,hz,he] using hv
      · by_cases hle : z.v ≤ z.u
        · refine ⟨j+1,k,by omega,?_,?_⟩
          · simp only [SkywalkNat.step,if_neg hz,if_neg he,if_pos hle,pow_succ]
            have hhalf : (z.u-z.v)/2*2 ≤ z.u := by omega
            nlinarith [Nat.mul_le_mul_right (2^j) hhalf]
          · simpa [SkywalkNat.step,hz,he,hle] using hv
        · refine ⟨k+1,j,by omega,?_,?_⟩
          · simp only [SkywalkNat.step,if_neg hz,if_neg he,if_neg hle,pow_succ]
            have hhalf : (z.v-z.u)/2*2 ≤ z.v := by omega
            nlinarith [Nat.mul_le_mul_right (2^k) hhalf]
          · simpa [SkywalkNat.step,hz,he,hle] using hu

private theorem two_pow_sum (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    2^a+2^b ≤ 2^(a+b-1) := by
  obtain ⟨c,rfl⟩ : ∃ c, a=c+2 := ⟨a-2,by omega⟩
  obtain ⟨d,rfl⟩ : ∃ d, b=d+2 := ⟨b-2,by omega⟩
  have he : c+2+(d+2)-1=c+d+3 := by omega
  rw [he, pow_add, pow_add, pow_add]
  norm_num
  rw [pow_add]
  have hc : 1 ≤ 2^c := Nat.one_le_two_pow
  have hd : 1 ≤ 2^d := Nat.one_le_two_pow
  nlinarith [Nat.mul_le_mul hc hd]

private theorem scaled_lt (u p j : Nat) (hp : p < 2^256) (hu : u*2^j ≤ p) (hj : j ≤ 256) :
    u < 2^(256-j) := by
  have he : 2^(256-j)*2^j=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
  by_contra h
  have hle := Nat.mul_le_mul_right (2^j) (Nat.le_of_not_gt h)
  omega

/-- A strict fixed-modulus sum cap across the late 32-stage band. -/
theorem strict_sum_band (x p i : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p)
    (cop : x.Coprime p) (hi : 256 ≤ i  ∧  i ≤ 287) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
    z.u+z.v < 2^(511-i) := by
  dsimp only
  obtain ⟨j,k,hjk,hu,hv⟩ := scaled_budget p x i (Nat.le_of_lt hx)
  have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) hp0 hpo
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  change z.u*2^j ≤ p at hu
  change z.v*2^k ≤ p at hv
  change 0 < z.v  ∧  z.v%2=1  ∧  z.u.gcd z.v=x.gcd p at valid
  change z.u+z.v < _
  by_cases hz : z.u=0
  · have hv1 : z.v=1 := by
      have hg := valid.2.2.trans cop
      rw [hz,Nat.gcd_zero_left] at hg
      exact hg
    have hi' : 1 ≤ 511-i := by omega
    have pow := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) hi'
    simp only [pow_one] at pow
    omega
  have hu0 : 1 ≤ z.u := by omega
  have hv0 : 1 ≤ z.v := by omega
  have hj : j ≤ 255 := by
    by_contra h
    have hpw := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) (show 256 ≤ j by omega)
    nlinarith
  have hk : k ≤ 255 := by
    by_contra h
    have hpw := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) (show 256 ≤ k by omega)
    nlinarith
  have ju := scaled_lt z.u p j hp hu (by omega)
  have kv := scaled_lt z.v p k hp hv (by omega)
  by_cases hje : j=255
  · have ue : z.u=1 := by simp only [hje] at ju; norm_num at ju; omega
    have kk : k=i-255 := by omega
    have kp : k ≤ 32 := by omega
    have kp32 := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) kp
    have ep : 2^(256-k)*2^k=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
    have ek : 511-i=256-k := by omega
    rw [ue,ek]
    by_contra h
    have hbig : 2^(256-k) ≤ z.v+1 := by omega
    have mul := Nat.mul_le_mul_right (2^k) hbig
    nlinarith
  · by_cases hke : k=255
    · have ve : z.v=1 := by simp only [hke] at kv; norm_num at kv; omega
      have jj : j=i-255 := by omega
      have jp : j ≤ 32 := by omega
      have jp32 := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) jp
      have ep : 2^(256-j)*2^j=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
      have ek : 511-i=256-j := by omega
      rw [ve,ek]
      by_contra h
      have hbig : 2^(256-j) ≤ z.u+1 := by omega
      have mul := Nat.mul_le_mul_right (2^j) hbig
      nlinarith
    · have a : 2 ≤ 256-j := by omega
      have b : 2 ≤ 256-k := by omega
      have bound := two_pow_sum (256-j) (256-k) a b
      have e : (256-j)+(256-k)-1=511-i := by omega
      rw [e] at bound
      omega
end ECDSAAdd.Entrant.TickGap

end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def signedAddTop (q : Wire) (x y carry : List Wire) : Program :=
  signComplement q x ++ TopCarry.addInPlaceTop x y carry q ++ signComplement q x

def Shape (n V : Nat) : Prop := V < 2^n ∨ 3*2^n ≤ V

theorem shape_complement (n V : Nat) (hv : V < 2^(n+2)) (h : Shape n V) :
    Shape n (2^(n+2)-1-V) := by
  have pow : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  unfold Shape at *
  omega

theorem shape_of_signed (n V : Nat) (hv : V < 2^(n+2))
    (lo : -((2^n:Nat):Int) ≤ signedDecode (n+2) V)
    (hi : signedDecode (n+2) V < ((2^n:Nat):Int)) : Shape n V := by
  have p2 : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  have p1 : 2^(n+2-1) = 2*2^n := by rw [show n+2-1=n+1 by omega,pow_succ]; ring
  unfold signedDecode at lo hi
  split_ifs at lo hi <;> unfold Shape <;> omega

theorem signedAddTop_eq (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (clean : ∀ w ∈ cs, s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Shape n (regValue y (run (signedAdd q x y cs) [] s).basis)) :
    run (signedAddTop q x y cs) m s=run (signedAdd q x y cs) m s := by
  have hxnd : x.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1).1
  have qx : q∉x := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have dis : List.Disjoint x (y++cs) := by
    have h : (x++(y++cs)).Nodup := by simpa only [List.append_assoc] using (List.nodup_cons.mp hn).2
    exact (List.nodup_append'.mp h).2.2
  have zx := (signComplement_counts q x).2
  let u := run (signComplement q x) [] s
  have fan := signComplement_correct q x hxnd qx s []
  have ux : Shape n (regValue x u.basis) := by
    change Shape n (regValue x (run (signComplement q x) [] s).basis)
    rw [fan.2.2]
    cases hs : s.basis q
    · exact source
    · simpa only [hx,if_true] using shape_complement n _ (by simpa [hx] using regValue_lt x s.basis) source
  have clean' : ∀ w ∈ cs, u.basis w=false := by
    intro w hw
    exact (fan.2.1 w (fun h => List.disjoint_left.mp dis h (List.mem_append_right _ hw))).trans (clean w hw)
  have out (r : List Bool) :
      regValue y (run (signComplement q x) r (run (addInPlace x y cs q) r u)).basis =
      regValue y (run (addInPlace x y cs q) r u).basis := by
    have h := signComplement_correct q x hxnd qx (run (addInPlace x y cs q) r u) r
    apply regValue_congr
    intro w hw
    exact h.2.1 w (fun hxw => List.disjoint_left.mp dis hxw (List.mem_append_left _ hw))
  have old : regValue y (run (signedAdd q x y cs) [] s).basis =
      regValue y (run (addInPlace x y cs q) [] u).basis := by
    simp only [signedAdd,List.append_assoc]
    rw [TopCarry.run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have add := addInPlace_correct x y cs q hn (hx.trans hy.symm) hc u [] clean'
  have us : Shape n ((regValue x u.basis+regValue y u.basis+(u.basis q).toNat)%2^(n+2)) := by
    rw [old,add.2.2,hy] at sum
    exact sum
  have eq (r : List Bool) := TopCarry.addInPlaceTop_eq n x y cs q hy (hx.trans hy.symm)
    hc hn u r clean' ux us
  simp only [signedAddTop,signedAdd,List.append_assoc]
  rw [TopCarry.run_zero_head _ _ m s zx,TopCarry.run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq]
  have mc := TopCarry.addInPlaceTop_counts n x y cs q hy (hx.trans hy.symm) hc
  have mo := addInPlace_counts x y cs q (hx.trans hy.symm) hc
  rw [mc.2,mo.2,hy]
  rfl
end ECDSAAdd.Entrant.TickGap
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def recordTop (sx sy q : Wire) (x y cs : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedAddTop q x y cs ++ skywalkSignToggle sx sy q

theorem signedAddTop_counts (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length) :
    toffoliCount (signedAddTop q x y cs)=n ∧ measurementCount (signedAddTop q x y cs)=n+1 := by
  have h := TopCarry.addInPlaceTop_counts n x y cs q hy (hx.trans hy.symm) hc
  simp only [signedAddTop,toffoliCount_append,measurementCount_append,
    (signComplement_counts q x).1,(signComplement_counts q x).2,h.1,h.2]
  exact ⟨by omega,by omega⟩

theorem toggle_frame (sx sy q : Wire) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (w : Wire) (hw : w≠q) :
    (run (skywalkSignToggle sx sy q) m s).basis w=s.basis w := by
  rw [skywalkSignToggle_correct sx sy q hqx hqy]
  simp [writeBit,hw]

theorem recordTop_eq (n : Nat) (sx sy q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (clean : ∀w∈cs,s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Shape n (regValue y (run (signedRecord sx sy q x y cs) [] s).basis)) :
    run (recordTop sx sy q x y cs) m s=run (signedRecord sx sy q x y cs) m s := by
  have qrest := (List.nodup_cons.mp hn).1
  have away (w : Wire) (hw : w∈x++y++cs) : w≠q := by
    intro he; subst w; exact qrest hw
  let u := run (skywalkSignToggle sx sy q) [] s
  have ut (w : Wire) (hw : w≠q) : u.basis w=s.basis w := toggle_frame sx sy q hqx hqy s [] w hw
  have ux : regValue x u.basis=regValue x s.basis :=
    regValue_congr _ _ _ (fun w hw => ut w (away w (by simp [hw])))
  have uc : ∀w∈cs,u.basis w=false := by
    intro w hw
    exact (ut w (away w (by simp [hw]))).trans (clean w hw)
  have zx := (skywalkSignToggle_counts sx sy q).2
  have out (r : List Bool) :
      regValue y (run (skywalkSignToggle sx sy q) r (run (signedAdd q x y cs) r u)).basis =
      regValue y (run (signedAdd q x y cs) r u).basis :=
    regValue_congr _ _ _ (fun w hw => toggle_frame sx sy q hqx hqy _ r w (away w (by simp [hw])))
  have old : regValue y (run (signedRecord sx sy q x y cs) [] s).basis =
      regValue y (run (signedAdd q x y cs) [] u).basis := by
    simp only [signedRecord,List.append_assoc]
    rw [TopCarry.run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  rw [old] at sum
  have eq (r : List Bool) := signedAddTop_eq n q x y cs hx hy hc hn u r uc (ux ▸ source) sum
  have mc := (signedAddTop_counts n q x y cs hx hy hc).2
  have mo := (signedWord_counts q x y cs (hx.trans hy.symm) hc).2.1
  simp only [recordTop,signedRecord,List.append_assoc]
  rw [TopCarry.run_zero_head _ _ m s zx,TopCarry.run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq,mc,mo,hy]
  rfl
end ECDSAAdd.Entrant.TickGap
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def narrowTop (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  recordTop L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1)) ++
    signComplement L.q (L.y.drop n)

theorem record_source (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0) :
    regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) m s).basis = regValue L.xp s.basis := by
  have h := signedRecord_spec L.xlo L.ylo L.sx L.sy L.q L.carryLow (L.short_nodup hn)
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
    (signedRegValue L.xp s.basis) (signedRegValue L.yp s.basis) s m ⟨hq,rfl,rfl,clean⟩
  have eq := (signedRegValue_eq_iff L.xp _ _).mp h.2.2.1
  exact regValue_congr _ _ _ eq

theorem narrowTop_eq (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) (s : State) (m : List Bool)
    (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0)
    (source : Shape n (regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis))
    (sum : Shape n (regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis)) :
    run (narrowTop L (n+2)) m s=run (narrowSignedRecord L (n+2)) m s := by
  have views := L.views (n+2) hw
  have clean' : ∀w∈L.carryLow,s.basis w=false := (regValue_zero _ _).mp clean
  have qx : L.sx≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have fan (r : List Wire) (hr : ∀w∈r,w∉L.yhigh) (v : State) (record : List Bool) :
      regValue r (run (signComplement L.q L.yhigh) record v).basis=regValue r v.basis := by
    have f := signComplement_correct L.q L.yhigh (L.high_nodup hn) (L.q_high hn) v record
    exact regValue_congr _ _ _ (fun w hw => f.2.1 w (hr w hw))
  have xaway : ∀w∈L.xp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp only [NarrowSignedRecordLayout.x,List.mem_append] at *; tauto)
  have yaway : ∀w∈L.yp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp [hw'])
  have outx : regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.xp xaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  have outy : regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.yp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.yp yaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  rw [outx,record_source L (n+2) hw hn s [] hq clean] at source
  rw [outy] at sum
  have eq (r : List Bool) := recordTop_eq n L.sx L.sy L.q L.xp L.yp L.carryLow
    hw.x hw.y (hw.carry.trans hw.y.symm) (L.short_nodup hn) qx qy s r clean' source sum
  have mc := signedAddTop_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have rz := (skywalkSignToggle_counts L.sx L.sy L.q).2
  have old := (signedWord_counts L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)).2.1
  have counts : measurementCount (recordTop L.sx L.sy L.q L.xp L.yp L.carryLow)=
      measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) := by
    simp only [recordTop,signedRecord,measurementCount_append,rz,mc.2,old,hw.y]
    omega
  simp only [narrowTop,narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
  rw [run_append,run_append,run_take,run_take,eq,counts]
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic Baselines Challenge RecordedQuantum

theorem signedAddTop_support (q : Wire) (x y cs : List Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    wires (signedAddTop q x y cs) ⊆ wires (signedAdd q x y cs) := by
  rw [(signedWord_wires q x y cs hx hc).1]
  have fan : wires (signComplement q x) ⊆ (q::(x++y++cs)).toFinset := by
    intro w hw
    have h := signComplement_wires_subset q x hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  simp only [signedAddTop,wires_append,Finset.union_subset_iff]
  exact ⟨⟨fan,TopCarry.addInPlaceTop_wires x y cs q⟩,fan⟩

theorem narrowTop_counts (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    toffoliCount (narrowTop L (n+2))+1=toffoliCount (narrowSignedRecord L (n+2)) ∧
      measurementCount (narrowTop L (n+2))=measurementCount (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have h := signedAddTop_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have old := narrowSignedRecord_counts L (n+2) hw
  have z := skywalkSignToggle_counts L.sx L.sy L.q
  have f := signComplement_counts L.q L.yhigh
  simp only [narrowTop,recordTop,v.1,v.2.1,v.2.2.1,v.2.2.2,
    toffoliCount_append,measurementCount_append,z.1,z.2,h.1,h.2,f.1,f.2,old.1,old.2.1]
  exact ⟨by omega,by omega⟩

theorem narrowTop_support (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    wires (narrowTop L (n+2)) ⊆ wires (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have sub := signedAddTop_support L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  simp only [narrowTop,narrowSignedRecord,recordTop,signedRecord,v.1,v.2.1,v.2.2.1,v.2.2.2,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) sub)
    (Finset.Subset.refl _)) (Finset.Subset.refl _)

theorem signedAddTop_physical (q : Wire) (x y cs : List Wire) (hn : (q::(x++y++cs)).Nodup) :
    GatePhysical (signedAddTop q x y cs) := by
  have qx : q∉x := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
  have fan := signComplement_physical q x qx
  have top := TopCarry.addInPlaceTop_physical x y cs q hn
  simp only [signedAddTop,gatePhysical_append]
  exact ⟨⟨fan,top⟩,fan⟩

theorem narrowTop_physical (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) : GatePhysical (narrowTop L (n+2)) := by
  have v := L.views (n+2) hw
  have nd := L.short_nodup hn
  have qx : L.sx≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have toggle : GatePhysical (skywalkSignToggle L.sx L.sy L.q) := by
    simp [skywalkSignToggle,GatePhysical,PhysicalInstr,ProperGate,qx,qy]
  have top := signedAddTop_physical L.q L.xp L.yp L.carryLow nd
  have fan := signComplement_physical L.q L.yhigh (L.q_high hn)
  simp only [narrowTop,recordTop,v.1,v.2.1,v.2.2.1,v.2.2.2,gatePhysical_append]
  exact ⟨⟨⟨toggle,top⟩,toggle⟩,fan⟩

theorem top_slots_le_old (x y cs : List Wire) (c : Wire) :
    gateSlots (TopCarry.addInPlaceTop x y cs c) ≤ gateSlots (addInPlace x y cs c) := by
  induction x generalizing y cs c with
  | nil => simp [TopCarry.addInPlaceTop,addInPlace]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [TopCarry.addInPlaceTop,addInPlace]
      | cons b bs => cases bs <;> simp [TopCarry.addInPlaceTop,addInPlace]
    | cons a' as =>
      cases y with
      | nil => simp [TopCarry.addInPlaceTop,addInPlace]
      | cons b bs =>
        cases bs with
        | nil => simp [TopCarry.addInPlaceTop,addInPlace]
        | cons b' bs =>
          cases cs with
          | nil => simp [TopCarry.addInPlaceTop,addInPlace]
          | cons d ds =>
            have h := ih (b'::bs) ds d
            simp only [TopCarry.addInPlaceTop,addInPlace,gateSlots_append] at h ⊢
            split_ifs <;> simp only [majority_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots] at h ⊢ <;> omega

theorem narrowTop_slots (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    gateSlots (narrowTop L (n+2)) ≤ gateSlots (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have top := top_slots_le_old L.xp L.yp L.carryLow L.q
  simp only [narrowTop,narrowSignedRecord,recordTop,signedRecord,signedAddTop,signedAdd,
    v.1,v.2.1,v.2.2.1,v.2.2.2,gateSlots_append]
  omega
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

/-- The two post-tick signed values fit below the strict late-stage cap. -/
theorem band_step_values (x p i : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p)
    (hi : 255 ≤ i  ∧  i ≤ 286) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int));
    let n := W.compactSkywalkTickPostWidth i-2;
    -((2^n:Nat):Int)  ≤  (SkywalkRails.step r).h  ∧  (SkywalkRails.step r).h  <  ((2^n:Nat):Int)  ∧
    -((2^n:Nat):Int)  ≤  (SkywalkRails.step r).k  ∧  (SkywalkRails.step r).k  <  ((2^n:Nat):Int) := by
  dsimp only
  have nw : W.compactSkywalkTickPostWidth i-2=510-i := by
    unfold W.compactSkywalkTickPostWidth W.narrowSkywalkWidth
    omega
  rw [nw]
  have cap := strict_sum_band x p (i+1) hp0 hpo hp gap hx cop (by omega)
  obtain ⟨G,S,enc⟩ := SkywalkTrace.iter_encoded (i+1) false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at enc
  rw [Function.iterate_succ_apply'] at enc
  let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
  let z := SkywalkNat.step^[i+1] (SkywalkNat.init x p)
  change SkywalkTrace.next r=SkywalkRails.encode G S (z.u:Int) (z.v:Int) at enc
  change z.u+z.v < 2^(511-(i+1)) at cap
  have exp : 511-(i+1)=510-i := by omega
  rw [exp] at cap
  have abs := SkywalkRails.encode_abs_sum_bound G S z.u z.v (z.u+z.v) (Nat.le_refl _)
  rw [←enc] at abs
  change |(SkywalkRails.step r).h|  ≤  ((z.u+z.v:Nat):Int)  ∧
    |(SkywalkRails.step r).k|  ≤  ((z.u+z.v:Nat):Int) at abs
  have cap' : ((z.u+z.v:Nat):Int) < ((2^(510-i):Nat):Int) := by exact_mod_cast cap
  have ah := abs_le.mp abs.1
  have ak := abs_le.mp abs.2
  dsimp only [r] at ah ak
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem repaired_output_shape (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p)
    (hi : 255 ≤ i  ∧  i ≤ 286) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let L := W.compactSkywalkTickLayout w i;
    let n := W.compactSkywalkTickPostWidth i;
    Shape (n-2) (regValue (L.half.take n) (run (W.repairedTick w i) m s).basis)  ∧
      Shape (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis) := by
  dsimp only
  have hgap : p+2^32 ≤ 2^256 := Nat.le_of_lt gap
  rw [W.repairedTick_eq w hn x p i hp0 hx0 hpo hp hgap hx cop (by omega) s m hs]
  have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hgap hx cop (by omega) s hs
  have fit := W.narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp hgap hx cop (by omega)
  have out := W.compactSkywalkTickOutput_spec w i (by omega) hn _ _ _ fit.1 fit.2.1 fit.2.2.1 fit.2.2.2.1 fit.2.2.2.2 s [] input
  have bounds := band_step_values x p i hp0 hpo hp gap hx cop hi
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have ns : n-2+2=n := by
    have width := W.compactSkywalkTick_width_bounds i (by omega)
    dsimp only [n]
    omega
  have lenA : n ≤ L.half.length := by
    rw [W.compactSkywalkTick_half w i (by omega),wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i (by omega)).2.2.1
  have lenB : n ≤ L.b.length := by
    rw [W.compactSkywalkTick_b w i (by omega),wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i (by omega)).2.2.1
  have aview : (W.compactSkywalkTickARelease w i).retained=L.half.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenA
  have bview : (W.compactSkywalkTickBRelease w i).retained=L.b.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenB
  have a := out.2.1
  have b := out.2.2.1
  rw [aview] at a
  rw [bview] at b
  have lenA' : (L.half.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenA]
  have lenB' : (L.b.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenB]
  unfold signedRegValue at a b
  rw [lenA'] at a
  rw [lenB'] at b
  change Shape (n-2) (regValue (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis) ∧
    Shape (n-2) (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
  constructor
  · apply shape_of_signed (n-2) _ (by simpa [ns,lenA'] using regValue_lt (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis)
    · rw [ns,a]; exact bounds.1
    · rw [ns,a]; exact bounds.2.1
  · apply shape_of_signed (n-2) _ (by simpa [ns,lenB'] using regValue_lt (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
    · rw [ns,b]; exact bounds.2.2.1
    · rw [ns,b]; exact bounds.2.2.2
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def head (w : Nat → Wire) (i : Nat) : Program :=
  let L := W.compactSkywalkTickLayout w i
  (if i=224 ∨ (255 ≤ i  ∧  i ≤ 509) then W.repairedRoute L
    else skywalkRoute L.a0 L.b0 L.ah L.bh) ++ skywalkSignedHalf L.aSign L.ext

def tail (w : Nat → Wire) (i : Nat) : Program :=
  [.CX (W.compactSkywalkTickLayout w i).previous (W.compactSkywalkTickLayout w i).a0] ++
    W.compactSkywalkTickCleanup w i

def tick (w : Nat → Wire) (i : Nat) : Program :=
  if 255 ≤ i  ∧  i ≤ 286 then
    head w i ++ narrowTop (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
      (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i
  else W.repairedTick w i

theorem old_split (w : Nat → Wire) (i : Nat) (band : 255 ≤ i  ∧  i ≤ 286) :
    W.repairedTick w i = head w i ++
      narrowSignedRecord (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
        (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i := by
  have nf : ¬ W.fwdTrim i := by unfold W.fwdTrim; omega
  simp only [W.repairedTick,if_neg nf,W.repairedTick0,head,tail,W.compactSkywalkTick,narrowSkywalkTick]
  split_ifs  <;> simp only [List.append_assoc]

theorem repairedRoute_small_support (L : SkywalkIntegerLayout) (hv : L.Valid) (hpos : 0 < L.bMid.length) :
    wires (W.repairedRoute L) ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
  have lo := swapRegisters_wires L.a0 L.aMid L.bMid hv.mids
  have tm : L.bMid.getD (L.bMid.length-1) 0∈L.bMid := W.repair_member_getD _ _ (by omega)
  have ls : wires (swapRegisters L.a0 L.aMid L.bMid) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    have h := lo hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh] at h ⊢
    tauto
  have ss : wires (W.signRepair L.aSign L.bSign L.previous (L.bMid.getD (L.bMid.length-1) 0)) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [W.signRepair,wires,Instr.wires,correctionWires,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh,
      List.not_mem_nil,or_false]
    have ht : q=L.bMid.getD (L.bMid.length-1) 0 → q∈L.bMid := fun he => he ▸ tm
    tauto
  have cx : wires [.CX L.a0 L.b0] ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  simp only [W.repairedRoute,W.repairedSwap,wires_append,Finset.union_subset_iff]
  exact ⟨⟨ls,ss⟩,cx⟩

theorem head_aux (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).history::(W.compactSkywalkTickLayout w i).carry) :
    (run (head w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have hpos : 0 < L.bMid.length := by
    change 0 < (wireBlock w 771 (W.compactSkywalkTickPreWidth i-2)).length
    rw [wireBlock_length]
    have width := W.compactSkywalkTick_width_bounds i hi
    omega
  have dis : List.Disjoint (L.history::L.carry) (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)) := by
    have nd : ((L.history::L.carry)++(L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh))).Nodup := by
      apply List.nodup_iff_count.mpr
      intro a
      have h := List.nodup_iff_count.mp hv.nodup a
      simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at h ⊢
      omega
    exact (List.nodup_append'.mp nd).2.2
  have qaway : q∉L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh) := List.disjoint_left.mp dis hq
  have sup : wires (head w i) ⊆ (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    have inc : (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [List.mem_toFinset,List.mem_cons] at ha ⊢
      tauto
    have repair := (repairedRoute_small_support L hv hpos).trans inc
    have full : wires (skywalkRoute L.a0 L.b0 L.ah L.bh) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      have h := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
      tauto
    have half : wires (skywalkSignedHalf L.aSign L.ext) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [skywalkSignedHalf,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.notMem_empty,or_false] at ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,List.mem_singleton]
      tauto
    simp only [head,wires_append,Finset.union_subset_iff]
    split_ifs  <;> exact ⟨by assumption,half⟩
  exact run_preserves_outside _ _ _ _ (fun h => qaway (List.mem_toFinset.mp (sup h)))

theorem tail_prefix (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).half.take (W.compactSkywalkTickPostWidth i) ++
      (W.compactSkywalkTickLayout w i).b.take (W.compactSkywalkTickPostWidth i)) :
    (run (tail w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have words := W.compactSkywalkTick_words_disjoint w i hi hn
  have nd := (List.nodup_cons.mp (L.record_nodup hv)).2
  have wa : L.half.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).1
  have wb : L.b.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1
  have adot : List.Disjoint (L.half.take n) (L.half.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wa
  have bdot : List.Disjoint (L.b.take n) (L.b.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wb
  have apart : q∉L.half.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact List.disjoint_left.mp adot hqa
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_drop h) (List.mem_of_mem_take hqb)
  have bpart : q∉L.b.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_take hqa) (List.mem_of_mem_drop h)
    · exact List.disjoint_left.mp bdot hqb
  have q0 : q≠L.a0 := by
    have qm : q∈L.half++L.b := by
      rcases List.mem_append.mp hq with hqa|hqb
      · exact List.mem_append_left _ (List.mem_of_mem_take hqa)
      · exact List.mem_append_right _ (List.mem_of_mem_take hqb)
    intro he
    subst q
    have h := List.nodup_iff_count.mp hv.nodup L.a0
    have hq' := List.count_pos_iff.mpr qm
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,List.count_nil,List.count_cons,List.count_append,
      List.count_singleton] at h hq'
    simp only [beq_self_eq_true,if_true] at h
    omega
  have valid := W.compactSkywalkTick_release_valid w i hi hn
  have af (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickARelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.1 v r).2.1 q apart
  have bf (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickBRelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.2 v r).2.1 q bpart
  simp only [tail,W.compactSkywalkTickCleanup,run_append,run_take]
  rw [bf,af]
  change Function.update s.basis L.a0 (s.basis L.a0 ^^ s.basis L.previous) q = s.basis q
  exact Function.update_of_ne q0 _ _
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

theorem tick_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p) (hi : i < 512)
    (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (tick w i) m s=run (W.repairedTick w i) m s := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    let P := head w i
    let Q := narrowSignedRecord R n
    let E := tail w i
    let u := run P (m.take (measurementCount P)) s
    let v := run Q (m.drop (measurementCount P)) u
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have width := W.compactSkywalkTick_width_bounds i hi
    have npos : 2 ≤ n := width.2.1
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have nd : R.wires.Nodup := narrowSkywalkRecord_nodup L hv n (by omega) nlen
    have n2 : n-2+2=n := by omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have whole : run (W.repairedTick w i) m s=
        run E ((m.drop (measurementCount P)).drop (measurementCount Q)) v := by
      rw [old_split _ _ band,List.append_assoc,run_append,run_take,run_append,run_take]
      simp only [P,Q,E,u,v,run_take]
      rfl
    have sizes := repaired_output_shape w hn x p i hp0 hx0 hpo hp gap hx cop band s m hs
    have keep (r : List Wire) (hr : r⊆L.half.take n++L.b.take n) :
        regValue r (run (W.repairedTick w i) m s).basis=regValue r v.basis := by
      rw [whole]
      apply regValue_congr
      intro q hq
      exact tail_prefix w i hi hn v _ q (hr hq)
    have shapeX : Shape (n-2) (regValue (L.half.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_left _ hq)]
      exact sizes.1
    have shapeY : Shape (n-2) (regValue (L.b.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_right _ hq)]
      exact sizes.2
    have record0 : (run Q [] u).basis=v.basis := run_basis_records Q u u [] (m.drop (measurementCount P)) rfl
    have orig := narrowSkywalkRecord_views L hv n (by omega) nlen
    have views := R.views n hw
    have xx : R.xp=L.half.take n := by rw [←views.1]; rw [orig.1]
    have yy : R.yp=L.b.take n := by rw [←views.2.1]; rw [orig.2.1]
    have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp (Nat.le_of_lt gap) hx cop hi s hs
    have uq : u.basis R.q=false := by
      apply (head_aux w i hi hn s _ L.history (List.mem_cons_self)).trans
      exact input.2.2.2.2.1
    have clean : regValue R.carryLow u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have qm : q∈L.carry := List.mem_of_mem_take hq
      apply (head_aux w i hi hn s _ q (List.mem_cons_of_mem _ qm)).trans
      exact (regValue_zero _ _).mp input.2.2.2.2.2 q qm
    have eq (r : List Bool) : run (narrowTop R n) r u=run Q r u := by
      have a : Shape (n-2) (regValue R.xp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,xx,record0]
        exact shapeX
      have b : Shape (n-2) (regValue R.yp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,yy,record0]
        exact shapeY
      simpa only [n2] using narrowTop_eq (n-2) R hw' nd u r uq clean a b
    have counts : measurementCount (narrowTop R n)=measurementCount Q := by
      simpa only [n2] using (narrowTop_counts (n-2) R hw').2
    simp only [tick,if_pos band]
    rw [old_split _ _ band]
    change run ((P++narrowTop R n)++E) m s=run ((P++Q)++E) m s
    conv_lhs => rw [List.append_assoc,run_append P (narrowTop R n++E)]
    conv_rhs => rw [List.append_assoc,run_append P (Q++E)]
    change run (narrowTop R n++E) (m.drop (measurementCount P)) u = run (Q++E) (m.drop (measurementCount P)) u
    rw [run_append (narrowTop R n) E,run_append Q E]
    rw [run_take (narrowTop R n),run_take Q,eq,counts]
  · simp only [tick,if_neg band]

def due (i : Nat) : Nat := if 255 ≤ i  ∧  i ≤ 286 then 1 else 0

theorem tick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (tick w i)+due i=toffoliCount (W.repairedTick w i)  ∧
    measurementCount (tick w i)=measurementCount (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_counts (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,due,if_pos band,toffoliCount_append,measurementCount_append]
    exact ⟨by omega,by omega⟩
  · simp only [tick,if_neg band,due,if_neg band,Nat.add_zero,and_self]

theorem tick_support (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    wires (tick w i) ⊆ wires (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_support (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)
  · simp only [tick,if_neg band]
    exact Finset.Subset.refl _

theorem tick_slots (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    Challenge.gateSlots (tick w i)  ≤  Challenge.gateSlots (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_slots (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,Challenge.gateSlots_append]
    omega
  · simp only [tick,if_neg band]
    exact Nat.le_refl _

theorem tick_physical (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (tick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_physical (n-2) R hw' (narrowSkywalkRecord_nodup L hv n (by omega) nlen)
    simp only [n2] at h
    dsimp only [R,n,L] at h
    have old := W.repairedTick_physical w i hi hn
    rw [old_split _ _ band] at old
    simp only [tick,if_pos band,gatePhysical_append] at old ⊢
    exact ⟨⟨old.1.1,h⟩,old.2⟩
  · simpa only [tick,if_neg band] using W.repairedTick_physical w i hi hn
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic MappedCompressed Secp256k1 History5 OB5

















end ECDSAAdd.Entrant.TickGap
end
end -- original module boundary


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end


set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== IntegerTickRanges (ArthurOstapenko baaabf50, ported) =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TickRanges

def H : Nat := 2^255

theorem classify (x p i : Nat) (hx0 : 0<x) (hx : x<p) (hpodd : p%2=1)
    (hp : p<2^256) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
    z.u+z.v < H   ∨
    (z.v=p   ∧   z.u*2^i=x)   ∨
    (∃ t r : Nat, t+r=i   ∧   1  ≤  r   ∧   z.v*2^t=x   ∧   z.u*2^r+z.v=p   ∧   z.u+z.v<p) := by
  induction i with
  | zero =>
    exact Or.inr (Or.inl ⟨rfl,by simp [SkywalkNat.init]⟩)
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    generalize heq : SkywalkNat.step^[i] (SkywalkNat.init x p)=z at ih ⊢
    rcases ih with hs | hno | hone
    · exact Or.inl ((SkywalkNat.step_sum_nonincrease z).trans_lt hs)
    · obtain ⟨hv,hu⟩ := hno
      have hz : z.u  ≠  0 := by intro h; simp [h] at hu; omega
      have hul : z.u<p := by
        have hi : 1  ≤  2^i := Nat.one_le_two_pow
        nlinarith
      by_cases he : z.u%2=0
      · right; left
        refine ⟨by simp [SkywalkNat.step,hz,he,hv],?_⟩
        simp only [SkywalkNat.step,if_neg hz,if_pos he,pow_succ]
        have hh : z.u/2*2=z.u := by omega
        calc
          _ = (z.u/2*2)*2^i := by ring
          _ = x := by rw [hh,hu]
      · right; right
        have hodd : z.u%2=1 := by omega
        have hdiff : (p-z.u)/2*2=p-z.u := by omega
        refine ⟨i,1,by omega,by omega,?_,?_,?_⟩
        all_goals simp only [SkywalkNat.step,if_neg hz,if_neg he,hv,
          if_neg (show   ¬  p  ≤  z.u by omega)]
        · exact hu
        · norm_num; omega
        · omega
    · obtain ⟨t,r,htr,hr,hv,hu,hs⟩ := hone
      have vz : z.v  ≤  x := by
        have ht : 1  ≤  2^t := Nat.one_le_two_pow
        nlinarith
      have hz : z.u  ≠  0 := by intro h; simp [h] at hu; omega
      have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) (show 0<p from by omega) hpodd
      rw [heq] at valid
      have vo : z.v%2=1 := valid.2.1
      by_cases he : z.u%2=0
      · right; right
        refine ⟨t,r+1,by omega,by omega,?_,?_,?_⟩
        all_goals simp only [SkywalkNat.step,if_neg hz,if_pos he]
        · exact hv
        · rw [pow_succ]
          have hh : z.u/2*2=z.u := by omega
          calc
            _ = (z.u/2*2)*2^r+z.v := by ring
            _ = p := by rw [hh,hu]
        · omega
      · left
        unfold SkywalkNat.step
        rw [if_neg hz,if_neg he]
        have hpH : p<2*H := by simpa [H,pow_succ] using hp
        split_ifs <;> dsimp only <;> omega

theorem early_gap (x i : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (hi : 225  ≤  i   ∧   i  ≤  254) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)
    z.u+z.v < H   ∨   H  ≤  z.v := by
  have hp : ECDSAAdd.p<2^256 := by norm_num [ECDSAAdd.p]
  have hpodd : ECDSAAdd.p%2=1 := by norm_num [ECDSAAdd.p]
  have hpe : ECDSAAdd.p+(2^32+977)=2*H := by norm_num [ECDSAAdd.p,H]
  obtain hs | hno | hone := classify x ECDSAAdd.p i hx0 hx hpodd hp
  · exact Or.inl hs
  · exact Or.inr (by rw [hno.1]; norm_num [ECDSAAdd.p,H])
  · obtain ⟨t,r,htr,hr,hv,hu,_⟩ := hone
    by_cases ht : 2  ≤  t
    · by_cases hr2 : 2  ≤  r
      · left
        have tp : 4  ≤  2^t := by simpa using Nat.pow_le_pow_right (by decide : 1  ≤  (2:Nat)) ht
        have rp : 4  ≤  2^r := by simpa using Nat.pow_le_pow_right (by decide : 1  ≤  (2:Nat)) hr2
        have hsmall : 4*((SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).u+
            (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v)<2*ECDSAAdd.p := by nlinarith
        nlinarith
      · have re : r=1 := by omega
        have tt : 224  ≤  t := by omega
        have tp : 2^224  ≤  2^t := Nat.pow_le_pow_right (by decide) tt
        left
        rw [re] at hu
        norm_num at hu
        have vle : (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v<2^32 := by
          by_contra hh
          have vv : 2^32  ≤  (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v := by omega
          have mul := Nat.mul_le_mul vv tp
          norm_num at mul
          nlinarith
        nlinarith
    · have rr : 224  ≤  r := by omega
      have rle : r  ≤  254 := by omega
      have rp : 2^224  ≤  2^r := Nat.pow_le_pow_right (by decide) rr
      have rpbig : 2^32+977<2^r := by
        calc
          2^32+977 < 2^224 := by norm_num
          _   ≤   2^r := rp
      have ep : 2^(256-r)*2^r=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
      have exp : 256-r  ≤  32 := by omega
      have sm : 2^(256-r)  ≤  2^32 := Nat.pow_le_pow_right (by decide) exp
      let z := SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)
      change z.v*2^t=x at hv
      change z.u*2^r+z.v=ECDSAAdd.p at hu
      change z.u+z.v<H   ∨   H  ≤  z.v
      have ucap : z.u<2^32 := by
        have ub : z.u<2^(256-r) := by
          by_contra h
          have mm := Nat.mul_le_mul_right (2^r) (Nat.le_of_not_gt h)
          nlinarith
        omega
      by_cases vb : H  ≤  z.v
      · exact Or.inr vb
      · left
        by_contra ns
        have vl : z.v<H := by omega
        have vt : H<z.v+(2^32+977) := by omega
        have hm : 2^(255-r)*2^r=H := by
          rw [←pow_add]
          change 2^(255-r+r)=(2:Nat)^255
          congr 1
          omega
        have um : z.u<2^(255-r) := by
          by_contra hh
          have mm := Nat.mul_le_mul_right (2^r) (Nat.le_of_not_gt hh)
          nlinarith
        have mm := Nat.mul_le_mul_right (2^r) (show z.u+1  ≤  2^(255-r) by omega)
        nlinarith
end ECDSAAdd.Entrant.TickRanges
namespace ECDSAAdd.Entrant.TickRanges

def Outside (v : Int) : Prop := v< -(H:Int)  ∨  (H:Int) ≤ v

theorem encode_boundary (g s : Bool) (u v : Int) (hu : 0 ≤ u) (hv : 0<v)
    (hvo : v%2=1) (hb : u+v<2*(H:Int)) (gap : u+v<(H:Int)  ∨  (H:Int) ≤ v) :
    let r := SkywalkRails.encode g s u v
    let eo := SkywalkRails.route r.a r.b;
    - (H:Int)  ≤  (SkywalkRails.step r).h  ∧  (SkywalkRails.step r).h<(H:Int)  ∧
      (Outside eo.2 ↔ Outside (SkywalkRails.step r).k) := by
  have hp : 0<(H:Int) := by norm_num [H]
  have ucap : u<(H:Int) := by omega
  by_cases he : u%2=0
  · have step := SkywalkRails.step_encode_even g s u v hu hv hvo he
    have hl : (u+v)%2 ≠ 0 := by omega
    have hn : (-u)%2=0 := by omega
    have hneg : (-u)/2= -(u/2) := by omega
    cases g <;> cases s <;>
      simp only [SkywalkRails.encode,SkywalkRails.route,SkywalkRails.odd,
        SkywalkRails.signed,Bool.false_eq_true,if_false,if_true,hl,hn,he,
        ne_eq,not_false_eq_true,not_true_eq_false,decide_true,decide_false] at step ⊢ <;>
      rw [step] <;> dsimp only <;> unfold Outside <;> omega
  · have step := SkywalkRails.step_encode_odd g s u v hu hv hvo he
    have hl : (u+v)%2=0 := by omega
    have hn : (-u)%2 ≠ 0 := by omega
    cases g <;> cases s <;>
      simp only [SkywalkRails.encode,SkywalkRails.route,SkywalkRails.odd,
        SkywalkRails.signed,Bool.false_eq_true,if_false,if_true,hl,hn,he,
        ne_eq,not_false_eq_true,not_true_eq_false,decide_true,decide_false] at step ⊢ <;>
      rw [step] <;> dsimp only <;> unfold Outside <;> omega
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
theorem run_mid_congr (M X X' E : Program) (m : List Bool) (s : State)
    (hM : measurementCount M = 0) (hc : measurementCount X = measurementCount X')
    (h : ∀ r, run X r (run M [] s) = run X' r (run M [] s)) :
    run (M ++ X ++ E) m s = run (M ++ X' ++ E) m s := by
  rw [List.append_assoc, List.append_assoc, run_append M (X ++ E), run_append M (X' ++ E), hM,
    List.take_zero, List.drop_zero, run_append X E, run_append X' E, hc, h]

theorem run_zero_head (M R : Program) (m : List Bool) (s : State) (hM : measurementCount M = 0) :
    run (M ++ R) m s = run R m (run M [] s) := by
  rw [run_append, hM, List.take_zero, List.drop_zero]






theorem run_head_congr (P P' E : Program) (m : List Bool) (s : State)
    (hP : measurementCount P = 0) (hP' : measurementCount P' = 0)
    (h : run P [] s = run P' [] s) :
    run (P ++ E) m s = run (P' ++ E) m s := by
  rw [run_append P E, run_append P' E, hP, hP', List.take_zero, List.drop_zero, h]

def addCopy : List Wire → List Wire → List Wire → Wire → Program
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, cin =>
      (if as = [] then [.CX cin c] else majority a b cin c) ++
        addCopy (a' :: as) (b' :: bs) cs c ++ eraseCarry a b cin c ++ [.CX a b, .CX cin b]
  | [a], [b], _, cin => [.CX a b, .CX cin b]
  | _, _, _, _ => []

theorem shape_two {x y carry : List Wire} (hy : y.length = 0 + 2) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) :
    ∃ a a' b b' c, x = [a, a'] ∧ y = [b, b'] ∧ carry = [c] := by
  rcases y with _ | ⟨b, _ | ⟨b', _ | ⟨b'', ys⟩⟩⟩ <;> simp at hy
  rcases x with _ | ⟨a, _ | ⟨a', _ | ⟨a'', xs⟩⟩⟩ <;> simp at hx
  rcases carry with _ | ⟨c, _ | ⟨c', cs⟩⟩ <;> simp at hc
  exact ⟨a, a', b, b', c, rfl, rfl, rfl⟩

theorem shape_succ {n : Nat} {x y carry : List Wire} (hy : y.length = n + 1 + 2)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    ∃ a a' a'' as b b' b'' bs c cs, x = a :: a' :: a'' :: as ∧ y = b :: b' :: b'' :: bs ∧
      carry = c :: cs := by
  rcases y with _ | ⟨b, _ | ⟨b', _ | ⟨b'', ys⟩⟩⟩ <;> simp at hy
  rcases x with _ | ⟨a, _ | ⟨a', _ | ⟨a'', xs⟩⟩⟩ <;> simp at hx
  rcases carry with _ | ⟨c, cs⟩ <;> simp at hc
  exact ⟨a, a', a'', xs, b, b', b'', ys, c, cs, rfl, rfl, rfl⟩

theorem regValue_nil' (st : BasisState) : regValue [] st = 0 := rfl

theorem addCopy_counts : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    toffoliCount (addCopy x y carry cin) = n ∧
    measurementCount (addCopy x y carry cin) = n + 1 := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    simp [addCopy, eraseCarry, toffoliCount, measurementCount]
  | succ n ih =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have h := ih (a' :: a'' :: as) (b' :: b'' :: bs) cs c (by simpa using hy)
        (by simpa using hx) (by simpa using hc)
    simp only [addCopy, List.cons_ne_nil, if_false, toffoliCount_append,
        measurementCount_append, h.1, h.2, majority, eraseCarry, toffoliCount, measurementCount]
    omega

theorem regValue_cons' (a : Wire) (r : List Wire) (st : BasisState) :
    regValue (a :: r) st = (st a).toNat + 2 * regValue r st := by
  cases h : st a <;> simp [regValue, h]

theorem copy_affine (A A' B B' C : Bool)
    (hX : A.toNat + 2*A'.toNat < 1 ∨ 3 ≤ A.toNat + 2*A'.toNat)
    (hS : (1 ≤ B.toNat+2*B'.toNat ∧ B.toNat+2*B'.toNat < 3) ↔
      (1 ≤ (A.toNat+2*A'.toNat+(B.toNat+2*B'.toNat)+C.toNat)%4 ∧
      (A.toNat+2*A'.toNat+(B.toNat+2*B'.toNat)+C.toNat)%4 < 3)) :
    carryBit A B C = C := by
  revert hX hS
  cases A <;> cases A' <;> cases B <;> cases B' <;> cases C <;> decide
theorem addCopy_eq : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    (cin :: (x ++ y ++ carry)).Nodup → ∀ (s : State) (m : List Bool),
    (∀ w ∈ carry, s.basis w = false) →
    (regValue x s.basis < 2^n ∨ 3 * 2^n ≤ regValue x s.basis) →
    ((2^n ≤ regValue y s.basis ∧ regValue y s.basis < 3*2^n) ↔
      (2^n ≤ (regValue x s.basis+regValue y s.basis+(s.basis cin).toNat)%2^(n+2) ∧
        (regValue x s.basis+regValue y s.basis+(s.basis cin).toNat)%2^(n+2) < 3*2^n)) →
    run (addCopy x y carry cin) m s = run (addInPlace x y carry cin) m s := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc hnd s m hclean hX hS
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have hbc : b ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hb'c : b' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hcc : cin ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hzero : s.basis c = false := hclean c (by simp)
    have hK : carryBit (s.basis a) (s.basis b) (s.basis cin) =
        (s.basis cin) := by
      apply copy_affine _ (s.basis a') _ _ _
      · simpa [regValue_cons', regValue_nil'] using hX
      · simpa [regValue_cons', regValue_nil'] using hS
    have hm1 : measurementCount ([.CX cin c] : Program) = 0 := rfl
    have hm2 : measurementCount (majority a b cin c) = 0 := rfl
    have hmid : run ([.CX cin c] : Program) [] s = run (majority a b cin c) [] s := by
      rw [majority_correct _ _ _ _ h4]
      simp only [run]
      apply State.extensionality
      · rfl
      · funext w
        simp only [writeBit, Function.update]
        by_cases hwc : w = c
        · subst hwc
          simp [hbc, hb'c, hcc, hzero, hK]
        · simp [hwc]
    simp only [addCopy, addInPlace, if_pos (rfl : ([] : List Wire) = []), List.append_assoc]
    exact run_head_congr _ _ _ m s hm1 hm2 hmid
  | succ n ih =>
    intro x y carry cin hy hx hc hnd s m hclean hX hS
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have hnd' : (c :: ((a' :: a'' :: as) ++ (b' :: b'' :: bs) ++ cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append] at this ⊢; omega
    have hcx : c ∉ a' :: a'' :: as := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hcy : c ∉ b' :: b'' :: bs := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hccs : c ∉ cs := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hzero : s.basis c = false := hclean c (by simp)
    let A := s.basis a
    let B := s.basis b
    let C := s.basis cin
    let s1 : State := ⟨s.phase, writeBit s.basis c (carryBit A B C)⟩
    have hfirst (record : List Bool) : run (majority a b cin c) record s = s1 := by
      rw [majority_correct _ _ _ _ h4]; simp [s1, hzero, A, B, C]
    have hs1 (w : Wire) (hw : w ≠ c) : s1.basis w = s.basis w := by simp [s1, writeBit, hw]
    have hclean' : ∀ d ∈ cs, s1.basis d = false := by
      intro d hd; rw [hs1 d (fun h => hccs (h ▸ hd))]; exact hclean d (by simp [hd])
    have hxs : regValue (a' :: a'' :: as) s1.basis = regValue (a' :: a'' :: as) s.basis :=
      regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcx (h ▸ hw)))
    have hys : regValue (b' :: b'' :: bs) s1.basis = regValue (b' :: b'' :: bs) s.basis :=
      regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcy (h ▸ hw)))
    have hc1 : s1.basis c = carryBit A B C := by simp [s1, writeBit]
    have hp1 : 2^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
    have hp3 : 2^(n+1+2) = 2 * 2^(n+2) := by rw [show n+1+2 = (n+2)+1 by omega, pow_succ]; ring
    rw [regValue_cons' a, regValue_cons' b] at hS
    rw [regValue_cons' a] at hX
    have step := sum_value_step A B C (regValue (a' :: a'' :: as) s.basis)
      (regValue (b' :: b'' :: bs) s.basis) (n+2)
    have hsb : (sumBit A B C).toNat ≤ 1 := by cases sumBit A B C <;> decide
    have hA : (s.basis a).toNat ≤ 1 := by cases s.basis a <;> decide
    have hX' : regValue (a' :: a'' :: as) s1.basis < 2^n ∨
        3 * 2^n ≤ regValue (a' :: a'' :: as) s1.basis := by
      rw [hxs]; omega
    have hB : (s.basis b).toNat ≤ 1 := by cases s.basis b <;> decide
    have hS' :
        (2^n ≤ regValue (b' :: b'' :: bs) s1.basis ∧
          regValue (b' :: b'' :: bs) s1.basis < 3*2^n) ↔
        (2^n ≤ (regValue (a' :: a'' :: as) s1.basis + regValue (b' :: b'' :: bs) s1.basis +
          (s1.basis c).toNat) % 2^(n+2) ∧
          (regValue (a' :: a'' :: as) s1.basis + regValue (b' :: b'' :: bs) s1.basis +
          (s1.basis c).toNat) % 2^(n+2) < 3*2^n) := by
      rw [hxs,hys,hc1]
      change (sumBit A B C).toNat + 2 * ((regValue (a' :: a'' :: as) s.basis +
        regValue (b' :: b'' :: bs) s.basis + (carryBit A B C).toNat) % 2^(n+2)) =
        ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
          (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+2+1) at step
      rw [show n+2+1 = n+1+2 by omega] at step
      generalize (regValue (a' :: a'' :: as) s.basis + regValue (b' :: b'' :: bs) s.basis +
        (carryBit A B C).toNat) % 2^(n+2) = S' at step ⊢
      generalize ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
        (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+1+2) = S at step hS
      omega
    have hmc : measurementCount (addCopy (a' :: a'' :: as) (b' :: b'' :: bs) cs c) =
        measurementCount (addInPlace (a' :: a'' :: as) (b' :: b'' :: bs) cs c) := by
      rw [(addCopy_counts n _ _ _ c (by simpa using hy) (by simpa using hx)
          (by simpa using hc)).2,
        (addInPlace_counts _ _ _ c (by simpa using hx) (by simpa using hc)).2]
      simp only [List.length_cons] at hy ⊢
      omega
    have hm0 : measurementCount (majority a b cin c) = 0 := rfl
    simp only [addCopy, addInPlace, List.cons_ne_nil, if_false]
    rw [List.append_assoc (majority a b cin c ++ _), List.append_assoc (majority a b cin c ++ _)]
    apply run_mid_congr _ _ _ _ m s hm0 hmc
    intro record
    rw [hfirst]
    exact ih _ _ _ c (by simpa using hy) (by simpa using hx) (by simpa using hc) hnd' s1 record
      hclean' hX' hS'

end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
def signedAddCopy (q : Wire) (x y carry : List Wire) : Program :=
  signComplement q x ++ addCopy x y carry q ++ signComplement q x

def Shape (n V : Nat) : Prop := V < 2^n ∨ 3*2^n ≤ V
def Band (n V : Nat) : Prop := 2^n ≤ V ∧ V<3*2^n

theorem shape_complement (n V : Nat) (hv : V < 2^(n+2)) (h : Shape n V) :
    Shape n (2^(n+2)-1-V) := by
  have pow : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  unfold Shape at *
  omega

theorem shape_of_signed (n V : Nat) (hv : V < 2^(n+2))
    (lo : -((2^n:Nat):Int) ≤ signedDecode (n+2) V)
    (hi : signedDecode (n+2) V < ((2^n:Nat):Int)) : Shape n V := by
  have p2 : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  have p1 : 2^(n+2-1) = 2*2^n := by rw [show n+2-1=n+1 by omega,pow_succ]; ring
  unfold signedDecode at lo hi
  split_ifs at lo hi <;> unfold Shape <;> omega

theorem signedAddCopy_eq (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (clean : ∀ w ∈ cs, s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Band n (regValue y s.basis) ↔ Band n (regValue y (run (signedAdd q x y cs) [] s).basis)) :
    run (signedAddCopy q x y cs) m s=run (signedAdd q x y cs) m s := by
  have hxnd : x.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1).1
  have qx : q∉x := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have dis : List.Disjoint x (y++cs) := by
    have h : (x++(y++cs)).Nodup := by simpa only [List.append_assoc] using (List.nodup_cons.mp hn).2
    exact (List.nodup_append'.mp h).2.2
  have zx := (signComplement_counts q x).2
  let u := run (signComplement q x) [] s
  have fan := signComplement_correct q x hxnd qx s []
  have ux : Shape n (regValue x u.basis) := by
    change Shape n (regValue x (run (signComplement q x) [] s).basis)
    rw [fan.2.2]
    cases hs : s.basis q
    · exact source
    · simpa only [hx,if_true] using shape_complement n _ (by simpa [hx] using regValue_lt x s.basis) source
  have clean' : ∀ w ∈ cs, u.basis w=false := by
    intro w hw
    exact (fan.2.1 w (fun h => List.disjoint_left.mp dis h (List.mem_append_right _ hw))).trans (clean w hw)
  have out (r : List Bool) :
      regValue y (run (signComplement q x) r (run (addInPlace x y cs q) r u)).basis =
      regValue y (run (addInPlace x y cs q) r u).basis := by
    have h := signComplement_correct q x hxnd qx (run (addInPlace x y cs q) r u) r
    apply regValue_congr
    intro w hw
    exact h.2.1 w (fun hxw => List.disjoint_left.mp dis hxw (List.mem_append_left _ hw))
  have old : regValue y (run (signedAdd q x y cs) [] s).basis =
      regValue y (run (addInPlace x y cs q) [] u).basis := by
    simp only [signedAdd,List.append_assoc]
    rw [run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have add := addInPlace_correct x y cs q hn (hx.trans hy.symm) hc u [] clean'
  have uy : regValue y u.basis=regValue y s.basis := by
    exact regValue_congr _ _ _ (fun w hw => fan.2.1 w
      (fun hxw => List.disjoint_left.mp dis hxw (List.mem_append_left _ hw)))
  have us : Band n (regValue y u.basis) ↔
      Band n ((regValue x u.basis+regValue y u.basis+(u.basis q).toNat)%2^(n+2)) := by
    rw [←uy,old,add.2.2,hy] at sum
    exact sum
  have eq (r : List Bool) := addCopy_eq n x y cs q hy (hx.trans hy.symm)
    hc hn u r clean' ux us
  simp only [signedAddCopy,signedAdd,List.append_assoc]
  rw [run_zero_head _ _ m s zx,run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq]
  have mc := addCopy_counts n x y cs q hy (hx.trans hy.symm) hc
  have mo := addInPlace_counts x y cs q (hx.trans hy.symm) hc
  rw [mc.2,mo.2,hy]
  rfl
def recordCopy (sx sy q : Wire) (x y cs : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedAddCopy q x y cs ++ skywalkSignToggle sx sy q

theorem signedAddCopy_counts (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length) :
    toffoliCount (signedAddCopy q x y cs)=n ∧ measurementCount (signedAddCopy q x y cs)=n+1 := by
  have h := addCopy_counts n x y cs q hy (hx.trans hy.symm) hc
  simp only [signedAddCopy,toffoliCount_append,measurementCount_append,
    (signComplement_counts q x).1,(signComplement_counts q x).2,h.1,h.2]
  exact ⟨by omega,by omega⟩

theorem toggle_frame (sx sy q : Wire) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (w : Wire) (hw : w≠q) :
    (run (skywalkSignToggle sx sy q) m s).basis w=s.basis w := by
  rw [skywalkSignToggle_correct sx sy q hqx hqy]
  simp [writeBit,hw]

theorem recordCopy_eq (n : Nat) (sx sy q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (clean : ∀w∈cs,s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Band n (regValue y s.basis) ↔ Band n (regValue y (run (signedRecord sx sy q x y cs) [] s).basis)) :
    run (recordCopy sx sy q x y cs) m s=run (signedRecord sx sy q x y cs) m s := by
  have qrest := (List.nodup_cons.mp hn).1
  have away (w : Wire) (hw : w∈x++y++cs) : w≠q := by
    intro he; subst w; exact qrest hw
  let u := run (skywalkSignToggle sx sy q) [] s
  have ut (w : Wire) (hw : w≠q) : u.basis w=s.basis w := toggle_frame sx sy q hqx hqy s [] w hw
  have ux : regValue x u.basis=regValue x s.basis :=
    regValue_congr _ _ _ (fun w hw => ut w (away w (by simp [hw])))
  have uc : ∀w∈cs,u.basis w=false := by
    intro w hw
    exact (ut w (away w (by simp [hw]))).trans (clean w hw)
  have zx := (skywalkSignToggle_counts sx sy q).2
  have out (r : List Bool) :
      regValue y (run (skywalkSignToggle sx sy q) r (run (signedAdd q x y cs) r u)).basis =
      regValue y (run (signedAdd q x y cs) r u).basis :=
    regValue_congr _ _ _ (fun w hw => toggle_frame sx sy q hqx hqy _ r w (away w (by simp [hw])))
  have old : regValue y (run (signedRecord sx sy q x y cs) [] s).basis =
      regValue y (run (signedAdd q x y cs) [] u).basis := by
    simp only [signedRecord,List.append_assoc]
    rw [run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have uy : regValue y u.basis=regValue y s.basis :=
    regValue_congr _ _ _ (fun w hw => ut w (away w (by simp [hw])))
  rw [←uy,old] at sum
  have eq (r : List Bool) := signedAddCopy_eq n q x y cs hx hy hc hn u r uc (ux ▸ source) sum
  have mc := (signedAddCopy_counts n q x y cs hx hy hc).2
  have mo := (signedWord_counts q x y cs (hx.trans hy.symm) hc).2.1
  simp only [recordCopy,signedRecord,List.append_assoc]
  rw [run_zero_head _ _ m s zx,run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq,mc,mo,hy]
  rfl
def narrowCopy (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  recordCopy L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1)) ++
    signComplement L.q (L.y.drop n)

theorem record_source (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0) :
    regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) m s).basis = regValue L.xp s.basis := by
  have h := signedRecord_spec L.xlo L.ylo L.sx L.sy L.q L.carryLow (L.short_nodup hn)
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
    (signedRegValue L.xp s.basis) (signedRegValue L.yp s.basis) s m ⟨hq,rfl,rfl,clean⟩
  have eq := (signedRegValue_eq_iff L.xp _ _).mp h.2.2.1
  exact regValue_congr _ _ _ eq

theorem narrowCopy_eq (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) (s : State) (m : List Bool)
    (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0)
    (source : Shape n (regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis))
    (sum : Band n (regValue L.yp s.basis) ↔ Band n (regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis)) :
    run (narrowCopy L (n+2)) m s=run (narrowSignedRecord L (n+2)) m s := by
  have views := L.views (n+2) hw
  have clean' : ∀w∈L.carryLow,s.basis w=false := (regValue_zero _ _).mp clean
  have qx : L.sx≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have fan (r : List Wire) (hr : ∀w∈r,w∉L.yhigh) (v : State) (record : List Bool) :
      regValue r (run (signComplement L.q L.yhigh) record v).basis=regValue r v.basis := by
    have f := signComplement_correct L.q L.yhigh (L.high_nodup hn) (L.q_high hn) v record
    exact regValue_congr _ _ _ (fun w hw => f.2.1 w (hr w hw))
  have xaway : ∀w∈L.xp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp only [NarrowSignedRecordLayout.x,List.mem_append] at *; tauto)
  have yaway : ∀w∈L.yp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp [hw'])
  have outx : regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.xp xaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  have outy : regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.yp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.yp yaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  rw [outx,record_source L (n+2) hw hn s [] hq clean] at source
  rw [outy] at sum
  have eq (r : List Bool) := recordCopy_eq n L.sx L.sy L.q L.xp L.yp L.carryLow
    hw.x hw.y (hw.carry.trans hw.y.symm) (L.short_nodup hn) qx qy s r clean' source sum
  have mc := signedAddCopy_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have rz := (skywalkSignToggle_counts L.sx L.sy L.q).2
  have old := (signedWord_counts L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)).2.1
  have counts : measurementCount (recordCopy L.sx L.sy L.q L.xp L.yp L.carryLow)=
      measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) := by
    simp only [recordCopy,signedRecord,measurementCount_append,rz,mc.2,old,hw.y]
    omega
  simp only [narrowCopy,narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
  rw [run_append,run_append,run_take,run_take,eq,counts]
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic Baselines Challenge RecordedQuantum
theorem addCopy_wires (x y carry : List Wire) (cin : Wire) :
    wires (addCopy x y carry cin) ⊆ (cin :: (x ++ y ++ carry)).toFinset := by
  induction x generalizing y carry cin with
  | nil => simp [addCopy, wires]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [addCopy, wires]
      | cons b bs =>
        cases bs with
        | nil =>
          intro w hw
          simp only [addCopy, wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, Finset.notMem_empty, or_false] at hw
          simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
          tauto
        | cons b' bs => simp [addCopy, wires]
    | cons a' as =>
      cases y with
      | nil => simp [addCopy, wires]
      | cons b bs =>
        cases bs with
        | nil => simp [addCopy, wires]
        | cons b' bs =>
          cases carry with
          | nil => simp [addCopy, wires]
          | cons c cs =>
            have hr := ih (b' :: bs) cs c
            have hm : wires (majority a b cin c) = {a, b, cin, c} := by
              ext w; simp [majority, wires, Instr.wires]; tauto
            have he := eraseCarry_wires a b cin c
            intro w hw
            simp only [addCopy, wires_append, Finset.mem_union, he] at hw
            simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
            rcases hw with ((h | h) | h) | h
            · split_ifs at h
              · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
                  Finset.mem_singleton, Finset.notMem_empty, or_false] at h
                tauto
              · rw [hm] at h
                simp only [Finset.mem_insert, Finset.mem_singleton] at h
                tauto
            · have := hr h
              simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at this
              tauto
            · simp only [Finset.mem_insert, Finset.mem_singleton] at h
              tauto
            · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
                Finset.mem_singleton, Finset.notMem_empty, or_false] at h
              tauto

theorem addCopy_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: x ++ y ++ carry).Nodup) : GatePhysical (addCopy x y carry cin) := by
  induction x generalizing y carry cin with
  | nil => simp [addCopy, GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases y with
      | nil => simp [addCopy, GatePhysical]
      | cons b ys =>
        cases ys with
        | cons b' ys => simp [addCopy, GatePhysical]
        | nil =>
          have hab : a ≠ b := by
            intro e; subst b
            have h := List.nodup_iff_count.mp hn a
            simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at h
            omega
          have hcb : cin ≠ b := by
            intro e; subst cin
            have h := List.nodup_iff_count.mp hn b
            simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at h
            omega
          simp [addCopy, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hab, hcb]
    | cons a' xs =>
      cases y with
      | nil => simp [addCopy, GatePhysical]
      | cons b ys =>
        cases ys with
        | nil => simp [addCopy, GatePhysical]
        | cons b' ys =>
          cases carry with
          | nil => simp [addCopy, GatePhysical]
          | cons k ks =>
            have hs : [a,b,cin,k,b'].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons, List.count_append, List.count_nil] at h ⊢; omega
            have ht : (k :: (a'::xs) ++ (b'::ys) ++ ks).Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons, List.count_append] at h ⊢; omega
            have hs4 : [a,b,cin,k].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hs q
              simp only [List.count_cons, List.count_nil] at h ⊢; omega
            have htail := ih (b'::ys) ks k ht
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
              not_or, not_false_eq_true, and_true] at hs
            rw [addCopy]
            simp only [gatePhysical_append]
            refine ⟨⟨⟨?_, htail⟩, eraseCarry_physical _ _ _ _⟩, ?_⟩
            · split_ifs
              · simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hs.2.1.2.1, hs.2.2.1.1,
                  Ne.symm hs.2.2.2]
              · exact majority_physical _ _ _ _ hs4
            · have hcb : cin ≠ b := Ne.symm hs.2.1.1
              simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hs.1.1, hcb]

theorem signedAddCopy_support (q : Wire) (x y cs : List Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    wires (signedAddCopy q x y cs) ⊆ wires (signedAdd q x y cs) := by
  rw [(signedWord_wires q x y cs hx hc).1]
  have fan : wires (signComplement q x) ⊆ (q::(x++y++cs)).toFinset := by
    intro w hw
    have h := signComplement_wires_subset q x hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  simp only [signedAddCopy,wires_append,Finset.union_subset_iff]
  exact ⟨⟨fan,addCopy_wires x y cs q⟩,fan⟩

theorem narrowCopy_counts (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    toffoliCount (narrowCopy L (n+2))+1=toffoliCount (narrowSignedRecord L (n+2)) ∧
      measurementCount (narrowCopy L (n+2))=measurementCount (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have h := signedAddCopy_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have old := narrowSignedRecord_counts L (n+2) hw
  have z := skywalkSignToggle_counts L.sx L.sy L.q
  have f := signComplement_counts L.q L.yhigh
  simp only [narrowCopy,recordCopy,v.1,v.2.1,v.2.2.1,v.2.2.2,
    toffoliCount_append,measurementCount_append,z.1,z.2,h.1,h.2,f.1,f.2,old.1,old.2.1]
  exact ⟨by omega,by omega⟩

theorem narrowCopy_support (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    wires (narrowCopy L (n+2)) ⊆ wires (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have sub := signedAddCopy_support L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  simp only [narrowCopy,narrowSignedRecord,recordCopy,signedRecord,v.1,v.2.1,v.2.2.1,v.2.2.2,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) sub)
    (Finset.Subset.refl _)) (Finset.Subset.refl _)

theorem signedAddCopy_physical (q : Wire) (x y cs : List Wire) (hn : (q::(x++y++cs)).Nodup) :
    GatePhysical (signedAddCopy q x y cs) := by
  have qx : q∉x := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
  have fan := signComplement_physical q x qx
  have top := addCopy_physical x y cs q hn
  simp only [signedAddCopy,gatePhysical_append]
  exact ⟨⟨fan,top⟩,fan⟩

theorem narrowCopy_physical (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) : GatePhysical (narrowCopy L (n+2)) := by
  have v := L.views (n+2) hw
  have nd := L.short_nodup hn
  have qx : L.sx≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have toggle : GatePhysical (skywalkSignToggle L.sx L.sy L.q) := by
    simp [skywalkSignToggle,GatePhysical,PhysicalInstr,ProperGate,qx,qy]
  have top := signedAddCopy_physical L.q L.xp L.yp L.carryLow nd
  have fan := signComplement_physical L.q L.yhigh (L.q_high hn)
  simp only [narrowCopy,recordCopy,v.1,v.2.1,v.2.2.1,v.2.2.2,gatePhysical_append]
  exact ⟨⟨⟨toggle,top⟩,toggle⟩,fan⟩

theorem top_slots_le_old (x y cs : List Wire) (c : Wire) :
    gateSlots (addCopy x y cs c) ≤ gateSlots (addInPlace x y cs c) := by
  induction x generalizing y cs c with
  | nil => simp [addCopy,addInPlace]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [addCopy,addInPlace]
      | cons b bs => cases bs <;> simp [addCopy,addInPlace]
    | cons a' as =>
      cases y with
      | nil => simp [addCopy,addInPlace]
      | cons b bs =>
        cases bs with
        | nil => simp [addCopy,addInPlace]
        | cons b' bs =>
          cases cs with
          | nil => simp [addCopy,addInPlace]
          | cons d ds =>
            have h := ih (b'::bs) ds d
            simp only [addCopy,addInPlace,gateSlots_append] at h ⊢
            split_ifs <;> simp only [majority_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots] at h ⊢ <;> omega

theorem narrowCopy_slots (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    gateSlots (narrowCopy L (n+2)) ≤ gateSlots (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have top := top_slots_le_old L.xp L.yp L.carryLow L.q
  simp only [narrowCopy,narrowSignedRecord,recordCopy,signedRecord,signedAddCopy,signedAdd,
    v.1,v.2.1,v.2.2.1,v.2.2.2,gateSlots_append]
  omega
end ECDSAAdd.Entrant.TickRanges
end

section
set_option exponentiation.threshold 512
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
def head (w : Nat → Wire) (i : Nat) : Program :=
  let L := W.compactSkywalkTickLayout w i
  (if i=224 ∨ (255 ≤ i  ∧  i ≤ 509) then W.repairedRoute L
    else skywalkRoute L.a0 L.b0 L.ah L.bh) ++ skywalkSignedHalf L.aSign L.ext

def tail (w : Nat → Wire) (i : Nat) : Program :=
  [.CX (W.compactSkywalkTickLayout w i).previous (W.compactSkywalkTickLayout w i).a0] ++
    W.compactSkywalkTickCleanup w i

def tick (w : Nat → Wire) (i : Nat) : Program :=
  if 225 ≤ i ∧ i ≤ 254 then
    head w i ++ narrowCopy (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
      (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i
  else TickGap.tick w i

theorem old_split (w : Nat → Wire) (i : Nat) (band : 225 ≤ i  ∧  i ≤ 254) :
    W.repairedTick w i = head w i ++
      narrowSignedRecord (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
        (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i := by
  have nf : ¬ W.fwdTrim i := by unfold W.fwdTrim; omega
  simp only [W.repairedTick,if_neg nf,W.repairedTick0,head,tail,W.compactSkywalkTick,narrowSkywalkTick]
  split_ifs  <;> simp only [List.append_assoc]

theorem repairedRoute_small_support (L : SkywalkIntegerLayout) (hv : L.Valid) (hpos : 0 < L.bMid.length) :
    wires (W.repairedRoute L) ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
  have lo := swapRegisters_wires L.a0 L.aMid L.bMid hv.mids
  have tm : L.bMid.getD (L.bMid.length-1) 0∈L.bMid := W.repair_member_getD _ _ (by omega)
  have ls : wires (swapRegisters L.a0 L.aMid L.bMid) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    have h := lo hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh] at h ⊢
    tauto
  have ss : wires (W.signRepair L.aSign L.bSign L.previous (L.bMid.getD (L.bMid.length-1) 0)) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [W.signRepair,wires,Instr.wires,correctionWires,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh,
      List.not_mem_nil,or_false]
    have ht : q=L.bMid.getD (L.bMid.length-1) 0 → q∈L.bMid := fun he => he ▸ tm
    tauto
  have cx : wires [.CX L.a0 L.b0] ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  simp only [W.repairedRoute,W.repairedSwap,wires_append,Finset.union_subset_iff]
  exact ⟨⟨ls,ss⟩,cx⟩

theorem head_aux (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).history::(W.compactSkywalkTickLayout w i).carry) :
    (run (head w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have hpos : 0 < L.bMid.length := by
    change 0 < (wireBlock w 771 (W.compactSkywalkTickPreWidth i-2)).length
    rw [wireBlock_length]
    have width := W.compactSkywalkTick_width_bounds i hi
    omega
  have dis : List.Disjoint (L.history::L.carry) (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)) := by
    have nd : ((L.history::L.carry)++(L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh))).Nodup := by
      apply List.nodup_iff_count.mpr
      intro a
      have h := List.nodup_iff_count.mp hv.nodup a
      simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at h ⊢
      omega
    exact (List.nodup_append'.mp nd).2.2
  have qaway : q∉L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh) := List.disjoint_left.mp dis hq
  have sup : wires (head w i) ⊆ (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    have inc : (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [List.mem_toFinset,List.mem_cons] at ha ⊢
      tauto
    have repair := (repairedRoute_small_support L hv hpos).trans inc
    have full : wires (skywalkRoute L.a0 L.b0 L.ah L.bh) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      have h := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
      tauto
    have half : wires (skywalkSignedHalf L.aSign L.ext) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [skywalkSignedHalf,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.notMem_empty,or_false] at ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,List.mem_singleton]
      tauto
    simp only [head,wires_append,Finset.union_subset_iff]
    split_ifs  <;> exact ⟨by assumption,half⟩
  exact run_preserves_outside _ _ _ _ (fun h => qaway (List.mem_toFinset.mp (sup h)))

theorem tail_prefix (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).half.take (W.compactSkywalkTickPostWidth i) ++
      (W.compactSkywalkTickLayout w i).b.take (W.compactSkywalkTickPostWidth i)) :
    (run (tail w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have words := W.compactSkywalkTick_words_disjoint w i hi hn
  have nd := (List.nodup_cons.mp (L.record_nodup hv)).2
  have wa : L.half.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).1
  have wb : L.b.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1
  have adot : List.Disjoint (L.half.take n) (L.half.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wa
  have bdot : List.Disjoint (L.b.take n) (L.b.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wb
  have apart : q∉L.half.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact List.disjoint_left.mp adot hqa
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_drop h) (List.mem_of_mem_take hqb)
  have bpart : q∉L.b.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_take hqa) (List.mem_of_mem_drop h)
    · exact List.disjoint_left.mp bdot hqb
  have q0 : q≠L.a0 := by
    have qm : q∈L.half++L.b := by
      rcases List.mem_append.mp hq with hqa|hqb
      · exact List.mem_append_left _ (List.mem_of_mem_take hqa)
      · exact List.mem_append_right _ (List.mem_of_mem_take hqb)
    intro he
    subst q
    have h := List.nodup_iff_count.mp hv.nodup L.a0
    have hq' := List.count_pos_iff.mpr qm
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,List.count_nil,List.count_cons,List.count_append,
      List.count_singleton] at h hq'
    simp only [beq_self_eq_true,if_true] at h
    omega
  have valid := W.compactSkywalkTick_release_valid w i hi hn
  have af (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickARelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.1 v r).2.1 q apart
  have bf (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickBRelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.2 v r).2.1 q bpart
  simp only [tail,W.compactSkywalkTickCleanup,run_append,run_take]
  rw [bf,af]
  change Function.update s.basis L.a0 (s.basis L.a0 ^^ s.basis L.previous) q = s.basis q
  exact Function.update_of_ne q0 _ _
theorem route_aux_frame (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈L.previous::L.history::L.ext::L.carry) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis q=s.basis q := by
  have hn : ((L.previous::L.history::L.ext::L.carry)++
      (L.a0::L.b0::(L.ah++L.bh))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hv.nodup w
    simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  apply run_preserves_outside
  intro hm
  have hh := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) hm
  exact List.disjoint_left.mp hd hq (List.mem_toFinset.mp hh)

theorem route_int_values (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int)
    (hp : (A+B)%2=1) (s : State) (m : List Bool)
    (ha : signedRegValue L.a s.basis=A) (hb : signedRegValue L.b s.basis=B)
    (hext : s.basis L.ext=false) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).phase=s.phase ∧
    signedRegValue (L.ext::L.ah) (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).1 ∧
    signedRegValue L.b (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).2 ∧
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis L.a0=SkywalkRails.odd A := by
  have hna : L.ah≠[] := by simp [SkywalkIntegerLayout.ah]
  have hnb : L.bh≠[] := by simp [SkywalkIntegerLayout.bh]
  have hA := ha.symm.trans (signedRegValue_cons L.a0 L.ah s.basis hna)
  have hB := hb.symm.trans (signedRegValue_cons L.b0 L.bh s.basis hnb)
  have hpar : s.basis L.b0=(!s.basis L.a0) := by
    cases hca : s.basis L.a0 with
    | false =>
      cases hcb : s.basis L.b0 with
      | false =>
        simp [hca,hcb] at hA hB
        omega
      | true => rfl
    | true =>
      cases hcb : s.basis L.b0 with
      | false => rfl
      | true =>
        simp [hca,hcb] at hA hB
        omega
  have hctrl : s.basis L.a0=SkywalkRails.odd A := by
    cases hc : s.basis L.a0 with
    | false =>
      have he : A%2=0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
    | true =>
      have he : A%2≠0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s
  obtain ⟨hf,_,hctl,hlo,hrawA,hrawB⟩ := skywalkRoute_correct L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv) s m hpar
  have he0 : t.basis L.ext=false :=
    (route_aux_frame L hv s m L.ext (by simp)).trans hext
  have hsa : signedRegValue L.ah t.basis=
      if s.basis L.a0 then signedRegValue L.bh s.basis else signedRegValue L.ah s.basis := by
    have hh := congrArg (signedDecode L.ah.length) hrawA
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  have hsb : signedRegValue L.bh t.basis=
      if s.basis L.a0 then signedRegValue L.ah s.basis else signedRegValue L.bh s.basis := by
    have hh := congrArg (signedDecode L.bh.length) hrawB
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  refine ⟨hf,?_,?_,hctl.trans hctrl⟩
  · rw [signedRegValue_cons L.ext L.ah t.basis hna,he0,hsa]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega

  · change signedRegValue (L.b0::L.bh) t.basis=_
    rw [signedRegValue_cons L.b0 L.bh t.basis hnb,hlo,hsb]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega


theorem head_odd_value (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int)
    (par : (A+B)%2=1) (s : State) (m : List Bool)
    (ha : signedRegValue L.a s.basis=A) (hb : signedRegValue L.b s.basis=B)
    (he : s.basis L.ext=false) :
    signedRegValue L.b (run (skywalkRoute L.a0 L.b0 L.ah L.bh ++
      skywalkSignedHalf L.aSign L.ext) m s).basis=(SkywalkRails.route A B).2 := by
  have route := (route_int_values L hv A B par s [] ha hb he).2.2.1
  have zero := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh (L.high_lengths hv) (L.route_nodup hv)).2
  rw [run_append,zero,List.take_zero,List.drop_zero]
  have extaway (q : Wire) (hq : q∈L.b) : q≠L.ext := by
    intro hh
    subst q
    have cnt := List.nodup_iff_count.mp hv.nodup L.ext
    have mem := List.count_pos_iff.mpr hq
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.b,List.count_cons,List.count_append,
      List.count_nil,List.count_singleton,beq_self_eq_true,if_true] at cnt mem
    omega
  apply Eq.trans (show signedRegValue L.b _=signedRegValue L.b
      (run (skywalkRoute L.a0 L.b0 L.ah L.bh) [] s).basis from ?_) route
  unfold signedRegValue
  congr 1
  exact regValue_congr _ _ _ (fun q hq =>
    (skywalkSignedHalf_frame L.aSign L.ext _ m).2 q (extaway q hq))

theorem band_signed (n V : Nat) (hv : V<2^(n+2)) :
    Band n V ↔ signedDecode (n+2) V< -((2^n:Nat):Int) ∨
      ((2^n:Nat):Int)≤signedDecode (n+2) V := by
  have p2 : 2^(n+2)=4*2^n := by rw [pow_add]; norm_num; ring
  have p1 : 2^(n+2-1)=2*2^n := by rw [show n+2-1=n+1 by omega,pow_succ]; ring
  unfold Band signedDecode
  split_ifs <;> omega

theorem repaired_output_info (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat) (hx0 : 0<x) (hx : x<p) (cop : x.Coprime p)
    (band : 225 ≤ i ∧ i ≤ 254) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    Shape (n-2) (regValue (L.half.take n) (run (W.repairedTick w i) m s).basis) ∧
      (Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
        Band (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis)) := by
  dsimp only
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have hi : i<512 := by omega
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) hp0 hpo
  have cap := W.iter_sum_late x p i hx0 hpo hp gap hx (by omega)
  have early := early_gap x i hx0 hx band
  obtain ⟨G,S,enc⟩ := SkywalkTrace.iter_encoded i false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at enc
  change r=SkywalkRails.encode G S (z.u:Int) (z.v:Int) at enc
  have u0 : 0 ≤ (z.u:Int) := by omega
  have v0 : 0 < (z.v:Int) := by exact_mod_cast valid.1
  have vo : (z.v:Int)%2=1 := by exact_mod_cast valid.2.1
  have cp : (z.u:Int)+(z.v:Int)<2*(H:Int) := by
    change z.u+z.v<2^256 at cap
    have : 2^256=2*H := by norm_num [H]
    exact_mod_cast (this ▸ cap)
  have eg : (z.u:Int)+(z.v:Int)<(H:Int) ∨ (H:Int) ≤ (z.v:Int) := by
    change z.u+z.v<H ∨ H≤z.v at early
    exact_mod_cast early
  have bounds := encode_boundary G S (z.u:Int) (z.v:Int) u0 v0 vo cp eg
  rw [←enc] at bounds
  have par : (r.a+r.b)%2=1 := by rw [enc]; exact SkywalkRails.encode_odd_sum G S _ _ vo
  have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp gap hx cop hi s hs
  have fit := W.narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp gap hx cop hi
  have out := W.compactSkywalkTickOutput_spec w i hi hn _ _ _ fit.1 fit.2.1 fit.2.2.1 fit.2.2.2.1 fit.2.2.2.2 s [] input
  have nw : n=257 := by unfold n W.compactSkywalkTickPostWidth W.narrowSkywalkWidth; omega
  have lenA : n ≤ L.half.length := by
    rw [W.compactSkywalkTick_half w i hi,wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i hi).2.2.1
  have lenB : L.b.length=n := by
    rw [W.compactSkywalkTick_b w i hi,wireBlock_length]
    unfold n W.compactSkywalkTickPostWidth W.compactSkywalkTickPreWidth
      W.narrowSkywalkRouteWidth W.narrowSkywalkWidth
    omega
  have av : (W.compactSkywalkTickARelease w i).retained=L.half.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenA
  have bv : (W.compactSkywalkTickBRelease w i).retained=L.b.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) (by change n ≤ L.b.length; omega)
  have a := out.2.1
  have b := out.2.2.1
  rw [av] at a
  rw [bv] at b
  have lenA' : (L.half.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenA]
  have lenB' : (L.b.take n).length=n := by simp [List.length_take,lenB]
  have old : run (W.repairedTick w i) m s=run (W.compactSkywalkTick w i) [] s :=
    W.repairedTick_eq w hn x p i hp0 hx0 hpo hp gap hx cop hi s m hs
  have valO : signedRegValue (L.b.take n) (run (head w i) m s).basis=
      (SkywalkRails.route r.a r.b).2 := by
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have he : ¬(i=224 ∨ (255 ≤ i ∧ i ≤ 509)) := by omega
    change signedRegValue _ (run _ m s).basis=_
    rw [head,if_neg he,List.take_of_length_le (by omega : L.b.length≤n)]
    exact head_odd_value L hv r.a r.b par s m input.1 input.2.1 input.2.2.2.1
  have rawShape : Shape (n-2) (regValue (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis) := by
    unfold signedRegValue at a
    rw [lenA'] at a
    rw [nw] at a ⊢
    apply shape_of_signed 255 _ (by have h := regValue_lt (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis; rw [lenA',nw] at h; exact h)
    · rw [a]; exact bounds.1
    · rw [a]; exact bounds.2.1
  refine ⟨old ▸ rawShape,?_⟩
  rw [old]
  have oy : Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
      Outside (SkywalkRails.route r.a r.b).2 := by
    have hh := band_signed 255 (regValue (L.b.take n) (run (head w i) m s).basis)
      (by have h := regValue_lt (L.b.take n) (run (head w i) m s).basis; rw [lenB',nw] at h; simpa only [nw] using h)
    unfold signedRegValue at valO
    rw [lenB',nw] at valO
    simpa only [nw,Nat.reduceSub,valO,Outside,H] using hh
  have ky : Band (n-2) (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis) ↔
      Outside (SkywalkRails.step r).k := by
    have hh := band_signed 255 (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
      (by have h := regValue_lt (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis; rw [lenB',nw] at h; simpa only [nw] using h)
    unfold signedRegValue at b
    rw [lenB',nw] at b
    simpa only [nw,Nat.reduceSub,b,Outside,H] using hh
  exact oy.trans (bounds.2.2.trans ky.symm)
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
theorem tick_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat) (hx0 : 0 < x) (hx : x < p) (cop : x.Coprime p) (hi : i < 512)
    (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (tick w i) m s=run (W.repairedTick w i) m s := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    let P := head w i
    let Q := narrowSignedRecord R n
    let E := tail w i
    let u := run P (m.take (measurementCount P)) s
    let v := run Q (m.drop (measurementCount P)) u
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have width := W.compactSkywalkTick_width_bounds i hi
    have npos : 2 ≤ n := width.2.1
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have nd : R.wires.Nodup := narrowSkywalkRecord_nodup L hv n (by omega) nlen
    have n2 : n-2+2=n := by omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have whole : run (W.repairedTick w i) m s=
        run E ((m.drop (measurementCount P)).drop (measurementCount Q)) v := by
      rw [old_split _ _ band,List.append_assoc,run_append,run_take,run_append,run_take]
      simp only [P,Q,E,u,v,run_take]
      rfl
    have sizes := repaired_output_info w hn x i hx0 hx cop band s m hs
    have keep (r : List Wire) (hr : r⊆L.half.take n++L.b.take n) :
        regValue r (run (W.repairedTick w i) m s).basis=regValue r v.basis := by
      rw [whole]
      apply regValue_congr
      intro q hq
      exact tail_prefix w i hi hn v _ q (hr hq)
    have shapeX : Shape (n-2) (regValue (L.half.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_left _ hq)]
      exact sizes.1
    have bandY : Band (n-2) (regValue (L.b.take n) u.basis) ↔
        Band (n-2) (regValue (L.b.take n) v.basis) := by
      have yu : run (head w i) m s=u := by dsimp only [u,P]; rw [run_take]
      have yv := keep (L.b.take n) (by intro q hq; exact List.mem_append_right _ hq)
      have sy : Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
          Band (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis) := sizes.2
      rw [yu,yv] at sy
      exact sy
    have record0 : (run Q [] u).basis=v.basis := run_basis_records Q u u [] (m.drop (measurementCount P)) rfl
    have orig := narrowSkywalkRecord_views L hv n (by omega) nlen
    have views := R.views n hw
    have xx : R.xp=L.half.take n := by rw [←views.1]; rw [orig.1]
    have yy : R.yp=L.b.take n := by rw [←views.2.1]; rw [orig.2.1]
    have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp gap hx cop hi s hs
    have uq : u.basis R.q=false := by
      apply (head_aux w i hi hn s _ L.history (List.mem_cons_self)).trans
      exact input.2.2.2.2.1
    have clean : regValue R.carryLow u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have qm : q∈L.carry := List.mem_of_mem_take hq
      apply (head_aux w i hi hn s _ q (List.mem_cons_of_mem _ qm)).trans
      exact (regValue_zero _ _).mp input.2.2.2.2.2 q qm
    have eq (r : List Bool) : run (narrowCopy R n) r u=run Q r u := by
      have a : Shape (n-2) (regValue R.xp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,xx,record0]
        exact shapeX
      have b : Band (n-2) (regValue R.yp u.basis) ↔
          Band (n-2) (regValue R.yp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,yy,record0]
        exact bandY
      simpa only [n2] using narrowCopy_eq (n-2) R hw' nd u r uq clean a b
    have counts : measurementCount (narrowCopy R n)=measurementCount Q := by
      simpa only [n2] using (narrowCopy_counts (n-2) R hw').2
    simp only [tick,if_pos band]
    rw [old_split _ _ band]
    change run ((P++narrowCopy R n)++E) m s=run ((P++Q)++E) m s
    conv_lhs => rw [List.append_assoc,run_append P (narrowCopy R n++E)]
    conv_rhs => rw [List.append_assoc,run_append P (Q++E)]
    change run (narrowCopy R n++E) (m.drop (measurementCount P)) u = run (Q++E) (m.drop (measurementCount P)) u
    rw [run_append (narrowCopy R n) E,run_append Q E]
    rw [run_take (narrowCopy R n),run_take Q,eq,counts]
  · simpa only [tick,if_neg band] using
      TickGap.tick_eq w hn x p i hp0 hx0 hpo hp (by norm_num [p]) hx cop hi s m hs

def due (i : Nat) : Nat := if 225 ≤ i ∧ i ≤ 254 then 1 else TickGap.due i

theorem tick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (tick w i)+due i=toffoliCount (W.repairedTick w i)  ∧
    measurementCount (tick w i)=measurementCount (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_counts (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,due,if_pos band,toffoliCount_append,measurementCount_append]
    exact ⟨by omega,by omega⟩
  · simpa only [tick,if_neg band,due,if_neg band] using TickGap.tick_counts w i hi hn

theorem tick_support (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    wires (tick w i) ⊆ wires (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_support (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)
  · simpa only [tick,if_neg band] using TickGap.tick_support w i hi hn

theorem tick_slots (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    Challenge.gateSlots (tick w i)  ≤  Challenge.gateSlots (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_slots (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,Challenge.gateSlots_append]
    omega
  · simpa only [tick,if_neg band] using TickGap.tick_slots w i hi hn

theorem tick_physical (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (tick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_physical (n-2) R hw' (narrowSkywalkRecord_nodup L hv n (by omega) nlen)
    simp only [n2] at h
    dsimp only [R,n,L] at h
    have old := W.repairedTick_physical w i hi hn
    rw [old_split _ _ band] at old
    simp only [tick,if_pos band,gatePhysical_append] at old ⊢
    exact ⟨⟨old.1.1,h⟩,old.2⟩
  · simpa only [tick,if_neg band] using TickGap.tick_physical w i hi hn
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic MappedCompressed Secp256k1 History5 OB5

theorem tick_eq5 (x : Nat) (hx0 : 0 < x) (hx : x < p) (i : Nat) (hi : i < 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (tick base i) m s=run (W.repairedTick base i) m s := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  have dis := Stack5.prefix_disjoint_layout base base_pool_nodup i i (Nat.le_refl i) hi
  have read : ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset,s.basis q=raw.basis q := by
    intro q hq
    rw [hbits]
    exact run_preserves_outside _ _ _ q (fun he => Finset.disjoint_left.mp dis he hq)
  have old := W.repairedTick_support base i hi base_pool_nodup
  have fresh := (tick_support base i hi base_pool_nodup).trans old
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 < 2^256 := by norm_num [p]
  exact Stack5.local_replace _ _ _ fresh old s raw m m read
    (tick_eq base base_pool_nodup x i hx0 hx cop hi raw m hraw)

theorem block_eq (x : Nat) (hx0 : 0 < x) (hx : x < p) (i : Nat) (hi : i < 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (tick base i++FirstNonzeroCodec.pack8first base i) m s=run (W.repairedTick base i++FirstNonzeroCodec.pack8first base i) m s := by
  rw [run_append (tick base i),run_append (W.repairedTick base i),run_take (tick base i),run_take (W.repairedTick base i)]
  rw [tick_eq5 x hx0 hx i hi s m hs,(tick_counts base i hi base_pool_nodup).2]

def forward (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)++forward (i+1) n

/-- The replacement forward prefix has exactly the existing logical trajectory. -/
theorem forward_gen (x : Nat) (hx0 : 0 < x) (hx : x < p) (n : Nat) :
    ∀ i, 1 ≤ i → i+n ≤ 512 → ∀(s : State)(m : List Bool),
    W.CompressedCompactStage5 base x p i s.basis →
    run (forward i n) m (pullState (sig (i-1)) s)=
      pullState (sig (i+n-1)) (run (Stack5.forward5 base i n) m s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  induction n with
  | zero => intro i _ _ s m _; simp only [forward,Stack5.forward5,run,Nat.add_zero]
  | succ n ih =>
    intro i h1 hb s m hs
    have hi : i ≤ 511 := by omega
    have z := StackOB5.stage_zero x i (by omega) s.basis hs
    rw [pull_step i hi s z.1 z.2]
    have cnt : measurementCount (renameProgram (sig i) (tick base i++FirstNonzeroCodec.pack8first base i))=
        measurementCount (W.repairedTick base i++FirstNonzeroCodec.pack8first base i) := by
      rw [(renameProgram_counts (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)).2]
      simp only [measurementCount_append,(tick_counts base i (by omega) base_pool_nodup).2]
    rw [forward,Stack5.forward5,run_append _ (forward (i+1) n),run_append _ (Stack5.forward5 base (i+1) n),cnt,StackOB5.forward_step_records,OB5.run_rename i hi]
    rw [block_eq x hx0 hx i (by omega) s _ hs]
    rw [StackOB5.forward_step_eq base base_pool_nodup x p i hp0 hx0 hpo hp hpGap hx cop _ _ hs]
    have next := (Stack5.step_spec base base_pool_nodup StackOB5.historyAbove x p i hp0 hx0 hpo hp hpGap hx
      cop (by omega) s (m.take (measurementCount (W.repairedTick base i++History5.packAfter base i))) hs).2
    have step := ih (i+1) (by omega) (by omega) _ (m.drop (measurementCount (W.repairedTick base i++History5.packAfter base i))) next
    rw [show i+1-1=i by omega] at step
    rw [step,show i+1+n-1=i+(n+1)-1 by omega]






def count (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => due i+count (i+1) n

theorem forward_metrics (i n : Nat) (hi : i+n ≤ 512) :
    toffoliCount (forward i n)+count i n=toffoliCount (StackOB5.forward i n)  ∧
    measurementCount (forward i n)=measurementCount (StackOB5.forward i n)  ∧
    Challenge.gateSlots (forward i n) ≤ Challenge.gateSlots (StackOB5.forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,StackOB5.forward,count]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have stepCounts := tick_counts base i (by omega) base_pool_nodup
    have slots := tick_slots base i (by omega) base_pool_nodup
    have a := renameProgram_counts (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)
    have b := renameProgram_counts (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    have c := Baselines.rename_gateSlots (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)
    have d := Baselines.rename_gateSlots (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    simp only [forward,StackOB5.forward,count,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at a b c d ⊢
    exact ⟨by omega,by omega,by omega⟩
















theorem forward_physical (i n : Nat) (hi : i+n ≤ 512) : GatePhysical (forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,GatePhysical]
  | succ n ih =>
    have stepPhysical := tick_physical base i (by omega) base_pool_nodup
    have codec := (FirstNonzeroCodec.packet_physical base base_pool_nodup i (by omega)).1
    have ren := gatePhysical_rename (sig i) (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr ⟨stepPhysical,codec⟩)
    simp only [forward,gatePhysical_append]
    exact ⟨ren,ih (i+1) (by omega)⟩


end ECDSAAdd.Entrant.TickRanges
end

namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 History5

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- Return the final basis integer when both measurement outcomes preserve phase at every step. -/
def phaseClean508 : Program → Nat → Option Nat
  | [], b => some b
  | .X t :: p, b => phaseClean508 p (b ^^^ 2^t)
  | .CX c t :: p, b => phaseClean508 p (flipN_t8 b t (b.testBit c))
  | .CCX a c t :: p, b => phaseClean508 p (flipN_t8 b t (b.testBit a && b.testBit c))
  | .measureX t c₀ c₁ :: p, b =>
    let d := flipN_t8 b t (b.testBit t)
    if corrP_t8 c₀ false d = false ∧ corrP_t8 c₁ (b.testBit t) d = false then
      phaseClean508 p d
    else none

theorem phaseClean508_sound (p : Program) (b v : Nat) (h : phaseClean508 p b = some v) (m : List Bool) :
    runN_t8 p m (false,b) = (false,v) := by
  induction p generalizing b m with
  | nil =>
    simp [phaseClean508] at h
    simp [runN_t8,h]
  | cons g p ih =>
    cases g with
    | X t => exact ih _ h m
    | CX c t => exact ih _ h m
    | CCX a c t => exact ih _ h m
    | measureX t c₀ c₁ =>
      simp only [phaseClean508] at h
      split at h
      · rename_i clean
        obtain ⟨h0,h1⟩ := clean
        have suffix :=  ih _ h m.tail
        cases m with
        | nil => simpa [runN_t8,List.headD,h0,h1] using suffix
        | cons z ms => cases z <;> simpa [runN_t8,List.headD,h0,h1] using suffix
      · contradiction

def agree508 (p q : Program) (b : Nat) : Bool :=
  match phaseClean508 q b with
  | none => false
  | some v => decide (phaseClean508 p b = some v)

theorem agree508_sound (p q : Program) (b : Nat) (h : agree508 p q b = true) (m : List Bool) :
    runN_t8 p m (false,b) = runN_t8 q m (false,b) := by
  cases hq : phaseClean508 q b with
  | none => simp [agree508,hq] at h
  | some v =>
    have hp : phaseClean508 p b = some v := by simpa [agree508,hq] using h
    rw [phaseClean508_sound p b v hp, phaseClean508_sound q b v hq]

def forward6 : Program :=
  [.CX 525 790,
   .CX 789 790,
   .CX 527 528,
   .CX 787 528,
   .CCX 790 528 786,
   .CX 525 788,
   .CX 526 788,
   .CX 787 788,
   .CCX 788 524 1556,
   .CX 790 787,
   .CCX 787 786 1553,
   .CX 524 527,
   .CX 786 527,
   .CX 789 527,
   .CX 790 787,
   .CX 1553 787,
   .CCX 527 787 1554,
   .CX 525 526,
   .CX 1554 526,
   .CX 1556 526,
   .CX 523 1554,
   .CX 524 1554,
   .CX 525 1554,
   .CX 527 1554,
   .CX 1553 1554,
   .CCX 526 1554 529,
   .CX 523 1553,
   .CX 525 1553,
   .CX 786 1553,
   .CX 788 1553,
   .CCX 1553 526 1552,
   .CX 523 524,
   .CX 525 787,
   .CX 525 790,
   .CX 1554 1557,
   .CX 1552 1558,
   .CX 524 525,
   .CX 787 525,
   .CX 523 1553,
   .CX 524 1553,
   .CX 527 1553,
   .CX 786 1553,
   .CX 1552 1553,
   .CX 1554 1553,
   .CX 523 1554,
   .CX 524 1554,
   .CX 527 1554,
   .CX 529 1554,
   .CX 786 1554,
   .CX 1552 1554,
   .CX 523 1552,
   .CX 528 1552,
   .CX 786 1552,
   .CX 787 1552,
   .CX 788 1552,
   .CX 790 1552,
   .CX 1554 1552,
   .CX 1557 1552,
   .CX 524 528,
   .CX 527 528,
   .CX 529 528,
   .CX 787 528,
   .CX 788 528,
   .CX 790 528,
   .CX 1552 528,
   .X 527,
   .CX 523 527,
   .CX 524 527,
   .CX 525 527,
   .CX 526 527,
   .CX 529 527,
   .CX 786 527,
   .CX 1554 527,
   .CX 1557 527,
   .CX 1558 527,
   .CX 525 526,
   .measureX 787 [] [.Z 1552, .Z 523, .Z 529, .Z 1556, .Z 789, .CZ 1554 524, .CZ 1554 523, .CZ 1554 529, .CZ 1554 789, .CZ 1554 790, .CZ 1554 786, .CZ 1553 523, .CZ 1553 529, .CZ 1553 788, .CZ 1553 789, .CZ 527 789, .CZ 1552 789, .CZ 525 1556, .CZ 525 789, .CZ 524 523, .CZ 524 1556, .CZ 524 789, .CZ 523 529],
   .X 786,
   .measureX 786 [] [.Z 1553, .Z 1552, .Z 525, .Z 523, .Z 529, .Z 1558, .Z 788, .CZ 1554 524, .CZ 1553 524, .CZ 527 1552],
   .measureX 790 [] [.CZ 523 789],
   .measureX 789 [] [.Z 1554, .Z 1553, .Z 1552, .CZ 1554 523, .CZ 523 529, .CZ 523 1558, .CZ 523 1557],
   .measureX 1557 [] [.Z 527, .Z 1552, .CZ 1554 524, .CZ 527 524, .CZ 527 529, .CZ 527 788, .CZ 524 529],
   .measureX 1556 [] [.CZ 523 788, .CZ 524 788],
   .measureX 788 [] [.Z 1553, .Z 525, .Z 1558, .CZ 1554 524, .CZ 525 524, .CZ 524 529, .CZ 524 1558],
   .measureX 1558 [] [.Z 1553, .Z 529, .CZ 1554 525, .CZ 1553 527],
   .measureX 529 [] [.Z 1552, .CZ 1554 525, .CZ 527 1552, .CZ 1552 525],
   .CX 526 786]




theorem forward6_wires : wires forward6 ⊆ sitesT8.toFinset := by decide +kernel




abbrev previousForward508 : Program := tick508ExF ++ tickMF

def forward6_pair (uv : Nat × Nat) : Bool :=
  [false,true].all fun g => [false,true].all fun s =>
    agree508 forward6 previousForward508 (encN_t8 (pre508 g s uv.1 uv.2) sitesT8)

theorem forward6_table : pairs508.all forward6_pair = true := by decide +kernel

theorem forward6_forced (g s : Bool) (uv : Nat × Nat) (member : uv ∈ pairs508) (m : List Bool) :
    run forward6 m ⟨false,pre508 g s uv.1 uv.2⟩ = run previousForward508 m ⟨false,pre508 g s uv.1 uv.2⟩ := by
  have table := forward6_table
  simp only [List.all_eq_true] at table
  have row := table uv member
  simp only [forward6_pair,List.all_eq_true] at row
  have h := row g (by cases g <;> simp) s (by cases s <;> simp)
  have eqr := agree508_sound _ _ _ h m
  rw [tb_enc_t8 (pre508 g s uv.1 uv.2) sitesT8 (pre508_supp g s uv.1 uv.2)]
  simp only [run_sim_t8,eqr]






theorem forward6_on_site (g s : Bool) (uv : Nat × Nat) (h : uv ∈ pairs508)
    (st : State) (bits : ∀ q ∈ sitesT8, st.basis q = pre508 g s uv.1 uv.2 q) (m : List Bool) :
    run forward6 m st = run previousForward508 m st := by
  apply forced_eqN forward6 previousForward508 sitesT8 (pre508 g s uv.1 uv.2) 9
    (recsUpTo 9) (take_recsUpTo 9) forward6_wires (by decide +kernel)
    (by decide +kernel) (by decide +kernel) _ st bits m
  intro r _
  rw [forward6_forced g s uv h r]
  exact ⟨rfl, fun _ _ => rfl⟩

end ECDSAAdd.Entrant

namespace ECDSAAdd.Entrant.ForwardSixPlacement
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 History5 OB5
open Rolling1588.Integer
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem at_stage (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (hs : Stage base isA x p 508 a.basis) (r : List Bool) :
    run forward6 r a = run (tick508ExF ++ tickMF) r a := by
  obtain ⟨g,s,uv,huv,bits⟩ := stage508_bitsT_new isA x hx0 hx a hs
  exact forward6_on_site g s uv huv a bits r

theorem place (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 508 a.basis) (r : List Bool) :
    run (renameProgram (sig 510) forward6) r (pullState (sig 507) a) =
    run (renameProgram (sig 508) tick508ExF ++ renameProgram (sig 510) tickMF)
      r (pullState (sig 507) a) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have z8 := stage_zero_gen isA x 508 508 (by omega) (by omega) a.basis stage
  have z9 := stage_zero_gen isA x 508 509 (by omega) (by omega) a.basis stage
  have z10 := stage_zero_gen isA x 508 510 (by omega) (by omega) a.basis stage
  have m8 : pullState (sig 507) a = pullState (sig 508) a := OB5.pull_step 508 (by omega) a z8.1 z8.2
  have m9 : pullState (sig 508) a = pullState (sig 509) a := OB5.pull_step 509 (by omega) a z9.1 z9.2
  have m10 : pullState (sig 509) a = pullState (sig 510) a := OB5.pull_step 510 (by omega) a z10.1 z10.2
  let b := run tick508ExF (r.take (measurementCount tick508ExF)) a
  have s9 : Stage base isA x p 509 b.basis := by
    have step := (Rolling1588.Integer.step_spec base isA base_pool_nodup StackOB5.historyAbove x p 508
      hp0 hx0 hpo hp gap hx cop (by omega) a (r.take (measurementCount tick508ExF)) stage).2
    simpa only [pack508 isA, List.append_nil, tick508ExF_explicit, b] using step
  have b9 := stage_zero_gen isA x 509 509 (by omega) (by omega) b.basis s9
  have b10 := stage_zero_gen isA x 509 510 (by omega) (by omega) b.basis s9
  have align : pullState (sig 508) b = pullState (sig 510) b :=
    (OB5.pull_step 509 (by omega) b b9.1 b9.2).trans (OB5.pull_step 510 (by omega) b b10.1 b10.2)
  rw [m8, run_append, (renameProgram_counts _ _).2, OB5.run_rename 508 (by omega)]
  change run (renameProgram (sig 510) forward6) r (pullState (sig 508) a) =
    run (renameProgram (sig 510) tickMF) (r.drop (measurementCount tick508ExF)) (pullState (sig 508) b)
  rw [align, m9, m10, OB5.run_rename 510 (by omega), OB5.run_rename 510 (by omega),
    at_stage isA x hx0 hx a stage, run_append]

end ECDSAAdd.Entrant.ForwardSixPlacement

namespace ECDSAAdd.Entrant.ForwardSixPlacement
open Arithmetic MappedCompressed Secp256k1 History5 OB5
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward Rolling1588.Integer.regularForward

def prior : Program := renameProgram (sig 508) tick508ExF ++ renameProgram (sig 510) tickMF
def merged : Program := renameProgram (sig 510) forward6
def after (isA : Bool) : Program :=
  renameProgram (sig 510) (Rolling1588.packAtTick isA 510) ++ renameProgram (sig 511) tickF









theorem previous_shape (isA : Bool) :
    Rolling1588.stackForward isA = Rolling1588.forward isA 1 507 ++ (prior ++ after isA) := by
  have snoc := Rolling1588.Integer.forward_snoc isA 1 507
  have pack : Rolling1588.Integer.packFirst base isA 508=[] := by
    simp only [Rolling1588.Integer.packFirst,show ¬(508:Nat)=5 from by decide,if_false,
      Rolling1588.Integer.pack508 isA]
  rw [show (1:Nat)+507=508 by rfl,pack,List.append_nil,Rolling1588.Integer.forward_eq_packets,
    Rolling1588.Integer.forward_eq_packets,tick508ExF_explicit] at snoc
  rw [Rolling1588.stackForward,snoc]
  simp only [prior,after,renameProgram,List.map_append,List.append_assoc]

theorem prior_at_prefix (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis)
    (u r : List Bool) :
    run merged r (run (Rolling1588.forward isA 1 507) u s) =
    run prior r (run (Rolling1588.forward isA 1 507) u s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have init := Rolling1588.Integer.stage_one base isA x p s first
  have st := ((Rolling1588.Integer.regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p
    1 507 hp0 hx0 hpo hp gap hx cop (by omega)) s u init).2
  have start : pullState (sig (1-1)) s=s := by
    apply State.extensionality
    · rfl
    · funext q
      change s.basis (sig 0 q)=s.basis q
      rw [sig_zero]
  have pre := Rolling1588.Integer.forward_gen isA x hx0 hx 507 1 (by omega) (by omega) s u init
  rw [start,Rolling1588.Integer.forward_eq_packets] at pre
  rw [pre]
  exact place isA x hx0 hx _ st r









end ECDSAAdd.Entrant.ForwardSixPlacement

namespace ECDSAAdd.Entrant.MorningFour
open Arithmetic MappedCompressed Secp256k1 History5
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
set_option exponentiation.threshold 2048

def tick507 : Program :=
  [.CX 787 524,
   .CX 788 525,
   .CX 789 526,
   .CX 790 527,
   .CCX 523 524 787,
   .CCX 523 525 788,
   .CCX 523 526 789,
   .CCX 523 527 790,
   .CX 787 524,
   .CX 788 525,
   .CX 789 526,
   .CX 790 527,
   .CX 528 791,
   .measureX 528 [] [.CZ 522 791],
   .CX 791 528,
   .CX 528 791,
   .CX 790 791,
   .CX 790 528,
   .CX 523 786,
   .CX 528 529,
   .X 1551,
   .CX 528 1551,
   .CX 790 1551,
   .CX 1551 524,
   .CX 1551 525,
   .CX 1551 526,
   .CX 1551 527,
   .CX 1551 528,
   .CX 524 786,
   .CX 524 1551,
   .CCX 786 1551 1556,
   .CX 524 1556,
   .CX 524 1551,
   .CX 524 786,
   .CX 525 787,
   .CX 525 1556,
   .CCX 787 1556 1557,
   .CX 525 1557,
   .CX 525 1556,
   .CX 525 787,
   .CX 526 788,
   .CX 526 1557,
   .CCX 788 1557 1558,
   .CX 526 1558,
   .CX 526 1557,
   .CX 526 788,
   .CX 527 789,
   .CX 527 1558,
   .CCX 789 1558 1559,
   .CX 527 1559,
   .CX 527 1558,
   .CX 527 789,
   .CX 528 790,
   .CX 1559 790,
   .measureX 1559 [] [.CZ 527 789, .CZ 527 1558, .CZ 789 1558],
   .CX 527 789,
   .CX 1558 789,
   .measureX 1558 [] [.CZ 526 788, .CZ 526 1557, .CZ 788 1557],
   .CX 526 788,
   .CX 1557 788,
   .measureX 1557 [] [.CZ 525 787, .CZ 525 1556, .CZ 787 1556],
   .CX 525 787,
   .CX 1556 787,
   .measureX 1556 [] [.CZ 524 786, .CZ 524 1551, .CZ 786 1551],
   .CX 524 786,
   .CX 1551 786,
   .CX 1551 524,
   .CX 1551 525,
   .CX 1551 526,
   .CX 1551 527,
   .CX 1551 528,
   .X 1551,
   .CX 528 1551,
   .CX 790 1551,
   .CX 1551 791,
   .CX 522 523,
   .CX 528 529,
   .CX 790 791]

abbrev incumbent6 : Program := ECDSAAdd.Entrant.forward6

def forward13 : Program :=
  [.CX 787 524,
   .CX 788 525,
   .CX 789 526,
   .CCX 523 524 787,
   .CCX 523 525 788,
   .CCX 523 526 789,
   .CX 787 524,
   .CX 788 525,
   .CX 789 526,
   .CX 528 791,
   .measureX 528 [] [.CZ 522 791],
   .CX 791 528,
   .CX 528 791,
   .CX 790 791,
   .CX 790 528,
   .CX 523 786,
   .CX 528 529,
   .X 1551,
   .CX 528 1551,
   .CX 790 1551,
   .CX 1551 524,
   .CX 1551 525,
   .CX 1551 526,
   .CX 1551 527,
   .CX 1551 528,
   .CX 524 786,
   .CX 524 1551,
   .CCX 786 1551 1556,
   .CX 524 1556,
   .CX 524 1551,
   .CX 524 786,
   .CX 525 787,
   .CX 525 1556,
   .CCX 787 1556 1557,
   .CX 525 1557,
   .CX 525 1556,
   .CX 525 787,
   .CX 526 788,
   .CX 526 1557,
   .CCX 788 1557 1558,
   .CX 526 1558,
   .CX 526 1557,
   .CX 526 788,
   .CX 527 789,
   .CX 527 1558,
   .CX 523 522,
   .CX 1558 789,
   .CCX 522 789 1554,
   .CX 1558 789,
   .CX 523 522,
   .X 1554,
   .CX 522 1554,
   .CX 523 1554,
   .CX 789 1554,
   .CX 1558 1554,
   .CX 527 1554,
   .CX 527 1558,
   .CX 528 790,
   .CX 1554 790,
   .X 1554,
   .measureX 1554 [] [.CZ 786 790],
   .CX 1558 789,
   .measureX 1558 [] [.CZ 526 788, .CZ 526 1557, .CZ 788 1557],
   .CX 526 788,
   .CX 1557 788,
   .measureX 1557 [] [.CZ 525 787, .CZ 525 1556, .CZ 787 1556],
   .CX 525 787,
   .CX 1556 787,
   .measureX 1556 [] [.CZ 524 786, .CZ 524 1551, .CZ 786 1551],
   .CX 524 786,
   .CX 1551 786,
   .CX 1551 524,
   .CX 1551 525,
   .CX 1551 526,
   .CX 1551 527,
   .CX 1551 528,
   .X 1551,
   .CX 528 1551,
   .CX 790 1551,
   .CX 1551 791,
   .CX 522 523,
   .CX 528 529,
   .CX 790 791,
   .CX 525 790,
   .CX 789 790,
   .CX 527 528,
   .CX 787 528,
   .CCX 790 528 786,
   .CX 525 788,
   .CX 526 788,
   .CX 787 788,
   .CCX 788 524 1556,
   .CX 790 787,
   .CCX 787 786 1553,
   .CX 524 527,
   .CX 786 527,
   .CX 789 527,
   .CX 790 787,
   .CX 1553 787,
   .CCX 527 787 1554,
   .CX 525 526,
   .CX 1554 526,
   .CX 1556 526,
   .CX 523 1554,
   .CX 524 1554,
   .CX 525 1554,
   .CX 527 1554,
   .CX 1553 1554,
   .CCX 526 1554 529,
   .CX 523 1553,
   .CX 525 1553,
   .CX 786 1553,
   .CX 788 1553,
   .CCX 1553 526 1552,
   .CX 523 524,
   .CX 525 787,
   .CX 525 790,
   .CX 1554 1557,
   .CX 1552 1558,
   .CX 524 525,
   .CX 787 525,
   .CX 523 1553,
   .CX 524 1553,
   .CX 527 1553,
   .CX 786 1553,
   .CX 1552 1553,
   .CX 1554 1553,
   .CX 523 1554,
   .CX 524 1554,
   .CX 527 1554,
   .CX 529 1554,
   .CX 786 1554,
   .CX 1552 1554,
   .CX 523 1552,
   .CX 528 1552,
   .CX 786 1552,
   .CX 787 1552,
   .CX 788 1552,
   .CX 790 1552,
   .CX 1554 1552,
   .CX 1557 1552,
   .CX 524 528,
   .CX 527 528,
   .CX 529 528,
   .CX 787 528,
   .CX 788 528,
   .CX 790 528,
   .CX 1552 528,
   .X 527,
   .CX 523 527,
   .CX 524 527,
   .CX 525 527,
   .CX 526 527,
   .CX 529 527,
   .CX 786 527,
   .CX 1554 527,
   .CX 1557 527,
   .CX 1558 527,
   .CX 525 526,
   .measureX 789 [] [.Z 790, .Z 1552, .Z 1553, .Z 1554, .CZ 522 529, .CZ 522 790, .CZ 522 1551, .CZ 522 1554, .CZ 522 1557, .CZ 522 1558],
   .measureX 790 [] [.CZ 523 529, .CZ 523 1552, .CZ 523 1553, .CZ 523 1557, .CZ 523 1558],
   .measureX 1556 [] [.CZ 523 788, .CZ 524 788],
   .measureX 787 [] [.Z 523, .Z 524, .CZ 523 525, .CZ 523 529, .CZ 523 786, .CZ 523 788, .CZ 523 1553, .CZ 523 1554, .CZ 524 525, .CZ 524 786],
   .measureX 1557 [] [.Z 527, .Z 1552, .CZ 1554 524, .CZ 527 524, .CZ 527 529, .CZ 527 788, .CZ 524 529],
   .measureX 788 [] [.Z 1553, .Z 525, .Z 1558, .CZ 1554 524, .CZ 525 524, .CZ 524 529, .CZ 524 1558],
   .X 786,
   .measureX 786 [] [.Z 523, .CZ 524 525, .CZ 524 529, .CZ 524 1553, .CZ 524 1558, .CZ 525 1552, .CZ 525 1554],
   .measureX 529 [] [.Z 1552, .CZ 1554 525, .CZ 527 1552, .CZ 1552 525],
   .measureX 1558 [] [.CZ 525 1552, .CZ 526 1552, .CZ 526 1553],
   .CX 526 786]

def prior : Program := tick507 ++ incumbent6

def sites : List Wire := [522, 523, 524, 525, 526, 527, 528, 529, 786, 787, 788, 789, 790, 791, 1551, 1552, 1553, 1554, 1556, 1557, 1558, 1559]

def pairs : List (Nat × Nat) := [(0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (8, 1), (9, 1), (10, 1), (11, 1), (12, 1), (13, 1), (14, 1), (15, 1), (1, 3), (2, 3), (4, 3), (5, 3), (7, 3), (10, 3), (13, 3), (1, 5), (2, 5), (3, 5), (6, 5), (7, 5), (11, 5), (1, 7), (2, 7), (3, 7), (5, 7), (9, 7), (1, 9), (7, 9), (1, 11), (5, 11), (1, 13), (3, 13), (1, 15)]

def pre507 (g s : Bool) (u v : Nat) : BasisState := fun q =>
  if q = 522 then g
  else if q = 523 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 1 % 2 = 1)
  else if q = 524 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 2 % 2 = 1)
  else if q = 525 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 4 % 2 = 1)
  else if q = 526 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 8 % 2 = 1)
  else if q = 527 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 16 % 2 = 1)
  else if q = 528 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a < 0)
  else if q = 786 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 1 % 2 = 1)
  else if q = 787 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 2 % 2 = 1)
  else if q = 788 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 4 % 2 = 1)
  else if q = 789 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 8 % 2 = 1)
  else if q = 790 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 16 % 2 = 1)
  else if q = 791 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b < 0)
  else false

theorem explicit507 : W.repairedTick base 507 = tick507 := by decide +kernel





theorem support : wires forward13 ⊆ sites.toFinset ∧ wires prior ⊆ sites.toFinset := by decide +kernel




theorem pre_supp (g s : Bool) (u v : Nat) : ∀ q, q ∉ sites → pre507 g s u v q = false := by
  intro q h
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  simp_all [pre507]

def checkPair (uv : Nat × Nat) : Bool :=
  [false,true].all fun g => [false,true].all fun s =>
    agree508 forward13 prior (encN_t8 (pre507 g s uv.1 uv.2) sites)
theorem table : pairs.all checkPair = true := by decide +kernel

theorem on_site (g s : Bool) (uv : Nat × Nat) (member : uv ∈ pairs) (st : State)
    (bits : ∀ q ∈ sites, st.basis q = pre507 g s uv.1 uv.2 q) (m : List Bool) :
    run forward13 m st = run prior m st := by
  have ht := table
  simp only [List.all_eq_true] at ht
  have row := ht uv member
  simp only [checkPair,List.all_eq_true] at row
  have h := row g (by cases g <;> simp) s (by cases s <;> simp)
  apply forced_eqN forward13 prior sites (pre507 g s uv.1 uv.2) 14
    (recsUpTo 14) (take_recsUpTo 14) support.1 support.2
    (by decide +kernel) (by decide +kernel) _ st bits m
  intro tape _
  have eqr := agree508_sound _ _ _ h tape
  have supp : ∀ q : Wire, pre507 g s uv.1 uv.2 q = true → q ∈ sites := by
    intro q hq
    by_contra hn
    rw [pre_supp g s uv.1 uv.2 q hn] at hq
    contradiction
  have same : run forward13 tape ⟨false,pre507 g s uv.1 uv.2⟩ =
      run prior tape ⟨false,pre507 g s uv.1 uv.2⟩ := by
    rw [tb_enc_t8 (pre507 g s uv.1 uv.2) sites supp]
    simp only [run_sim_t8,eqr]
  rw [same]
  exact ⟨rfl, fun _ _ => rfl⟩

end ECDSAAdd.Entrant.MorningFour

namespace ECDSAAdd.Entrant.MorningFour
open Arithmetic MappedCompressed Secp256k1 History5
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

theorem signed6_cases (a b c d e f : Wire) (s : BasisState) (v : Int)
    (h : signedRegValue [a,b,c,d,e,f] s = v) :
    s a = decide (v % 2 = 1) ∧ s b = decide (v / 2 % 2 = 1) ∧ s c = decide (v / 4 % 2 = 1) ∧
      s d = decide (v / 8 % 2 = 1) ∧ s e = decide (v / 16 % 2 = 1) ∧ s f = decide (v < 0) := by
  unfold signedRegValue signedDecode at h
  simp only [regValue,List.length] at h
  cases ha : s a <;> cases hb : s b <;> cases hc : s c <;> cases hd : s d <;> cases he : s e <;> cases hf : s f <;>
    simp [ha,hb,hc,hd,he,hf] at h <;> subst h <;> decide

theorem pairs_of (z : SkywalkNat.State) (hs : z.u+z.v≤16) (h0 : 0<z.v) (h1 : z.v%2=1)
    (hg : z.u.gcd z.v=1) (ht : (SkywalkNat.step^[4] z).u=0) : (z.u,z.v)∈pairs := by
  obtain ⟨u,v⟩ := z
  simp only at hs h0 h1 hg ht ⊢
  have hv : v=1 ∨ v=3 ∨ v=5 ∨ v=7 ∨ v=9 ∨ v=11 ∨ v=13 ∨ v=15 := by omega
  have hu : u ≤ 16-v := by omega
  clear hs h0 h1
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num at hu <;>
    interval_cases u <;> revert hg ht <;> decide

theorem retainedA507 : (W.compactSkywalkSignPoolA base 507).retained =
    [base 507,base 508,base 509,base 510,base 511,base 512] := by decide +kernel
theorem retainedB507 : (W.compactSkywalkSignPoolB base 507).retained =
    [base 770,base 771,base 772,base 773,base 774,base 775] := by decide +kernel
theorem releasedA507 : base 513 ∈ (W.compactSkywalkSignPoolA base 507).released := by decide +kernel

attribute [local irreducible] run W.compactSkywalkStageVirtual SkywalkTrace.next Nat.iterate
  W.compactSkywalkTick History5.encodePrefix

theorem raw507 (x : Nat) (hx0 : 0<x) (hx : x<p) (raw : State)
    (hraw : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 507 raw.basis) :
    ∃ g s : Bool, ∃ uv∈pairs, ∀ q∈sites, raw.basis q = pre507 g s uv.1 uv.2 q := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := (StackOB5.prime_facts x hx0 hx).2.2.2
  have fields := (W.compactSkywalkStage_fields_iff base _ 507 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨readA, readB, prev, -, future, carry, -, cleanA, -⟩ := fields
  obtain ⟨G, S, encoded⟩ := SkywalkTrace.iter_encoded 507 false false (SkywalkNat.init x p) hp0 hpo
  have sum := W.iter_sum_width x p 507 hp0 hx0 hpo hp hx cop (by omega)
  have valid := SkywalkNat.iter_valid 507 (SkywalkNat.init x p) hp0 hpo
  have term := (SkywalkNat.terminates_511 p x hp0 hx0 hpo hp hx cop).1
  have split : SkywalkNat.step^[511] (SkywalkNat.init x p) =
      SkywalkNat.step^[4] (SkywalkNat.step^[507] (SkywalkNat.init x p)) := by
    rw [← Function.iterate_add_apply]
  rw [split] at term
  change (SkywalkNat.step^[507] (SkywalkNat.init x p)).u+
    (SkywalkNat.step^[507] (SkywalkNat.init x p)).v ≤ 2^(511-507) at sum
  change SkywalkTrace.next^[507] (SkywalkRails.encode false false (x : Int) (p : Int)) =
    SkywalkRails.encode G S ((SkywalkNat.step^[507] (SkywalkNat.init x p)).u : Int)
      ((SkywalkNat.step^[507] (SkywalkNat.init x p)).v : Int) at encoded
  generalize SkywalkNat.step^[507] (SkywalkNat.init x p) = z at encoded sum valid term
  have sixteen : (2:Nat)^(511-507) = 16 := by norm_num
  rw [sixteen] at sum
  have mem := pairs_of z sum valid.1 valid.2.1 (valid.2.2.trans cop) term
  rw [encoded, retainedA507] at readA
  rw [encoded, retainedB507] at readB
  rw [encoded] at prev
  have bA := signed6_cases _ _ _ _ _ _ raw.basis _ readA
  have bB := signed6_cases _ _ _ _ _ _ raw.basis _ readB
  have f7 := future 507 (le_refl _) (by omega)
  have f8 := future 508 (by omega) (by omega)
  have f9 := future 509 (by omega) (by omega)
  have f10 := future 510 (by omega) (by omega)
  have c1540 : raw.basis (base 1540) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1540, by simp, rfl⟩)
  have c1541 : raw.basis (base 1541) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1541, by simp, rfl⟩)
  have c1542 : raw.basis (base 1542) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1542, by simp, rfl⟩)
  have c1543 : raw.basis (base 1543) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1543, by simp, rfl⟩)
  have c513 : raw.basis (base 513) = false := cleanA _ releasedA507
  have prev' : raw.basis (base 506) = G := by
    have h : skywalkPoolPreviousId 507 = 506 := rfl
    rw [h] at prev
    cases G <;> simpa [SkywalkRails.encode] using prev
  refine ⟨G,S,_,mem,?_⟩
  intro q hq
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prev'
  · simpa [pre507] using bA.1
  · exact bA.2.1
  · exact bA.2.2.1
  · exact bA.2.2.2.1
  · exact bA.2.2.2.2.1
  · exact bA.2.2.2.2.2
  · exact c513
  · simpa [pre507] using bB.1
  · exact bB.2.1
  · exact bB.2.2.1
  · exact bB.2.2.2.1
  · exact bB.2.2.2.2.1
  · exact bB.2.2.2.2.2
  · exact f7.2
  · exact f8.2
  · exact f9.2
  · exact f10.2
  · exact c1540
  · exact c1541
  · exact c1542
  · exact c1543

end ECDSAAdd.Entrant.MorningFour

namespace ECDSAAdd.Entrant.Forward12Research
open Arithmetic MappedCompressed
set_option exponentiation.threshold 2048
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
def safe15 : Program → Nat → Bool
  | [], _ => true
  | (.measureX t c0 c1)::rest, b =>
    let b' := flipN_t8 b t (b.testBit t)
    c0.isEmpty && (corrP_t8 c1 false b' == b.testBit t) && safe15 rest b'
  | i::rest, b => safe15 rest (runN_t8 [i] [] (false,b)).2


theorem corr_add (cs : List Correction) (ph : Bool) (b : Nat) :
    corrP_t8 cs ph b = (ph ^^ corrP_t8 cs false b) := by
  induction cs generalizing ph with
  | nil => cases ph <;> rfl
  | cons c cs ih =>
    cases c with
    | Z t => cases ph <;> cases hb : b.testBit t <;> simp only [corrP_t8, hb, Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false] <;> (first | rfl | (rw [ih true]; cases corrP_t8 cs false b <;> rfl))
    | CZ x y => cases ph <;> cases hx : b.testBit x <;> cases hy : b.testBit y <;> simp only [corrP_t8, hx, hy, Bool.false_and, Bool.true_and, Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false] <;> (first | rfl | (rw [ih true]; cases corrP_t8 cs false b <;> rfl))

theorem safe_sound (P : Program) (b : Nat) (h : safe15 P b = true) (m : List Bool) (ph : Bool) :
  runN_t8 P m (ph,b) = (ph, (runN_t8 P [] (false,b)).2) := by
  induction P generalizing b m ph with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | X t => simp only [safe15,runN_t8,Prod.snd] at h ⊢; exact ih _ h _ _
    | CX c t => simp only [safe15,runN_t8,Prod.snd] at h ⊢; exact ih _ h _ _
    | CCX a b' t => simp only [safe15,runN_t8,Prod.snd] at h ⊢; exact ih _ h _ _
    | measureX t c0 c1 =>
      simp only [safe15,Bool.and_eq_true,beq_iff_eq] at h
      obtain ⟨⟨hc0,hc1⟩,hr⟩ := h
      have hz : c0 = [] := by simpa using hc0
      subst c0
      cases m with
      | nil => simpa [runN_t8, corrP_t8] using ih _ hr [] ph
      | cons z zs =>
        cases z with
        | false => simpa [runN_t8, corrP_t8] using ih _ hr zs ph
        | true =>
          have eq : corrP_t8 c1 (ph ^^ b.testBit t) (flipN_t8 b t (b.testBit t)) = ph := by
            rw [corr_add, hc1]
            cases ph <;> cases b.testBit t <;> rfl
          simpa [runN_t8, corrP_t8, eq] using ih _ hr zs ph




def candidate : Program := [
  .X 786,
  .CX 523 786,
  .CX 527 524,
  .CX 528 524,
  .CX 787 524,
  .CCX 523 524 529,
  .X 524,
  .CX 523 524,
  .CX 525 524,
  .CX 527 524,
  .CX 528 524,
  .CX 788 524,
  .CCX 523 524 786,
  .CX 526 525,
  .CX 527 525,
  .CX 528 525,
  .CX 788 525,
  .CX 789 525,
  .CCX 523 525 1551,
  .X 523,
  .CX 527 523,
  .CX 524 523,
  .CX 526 523,
  .CX 790 527,
  .CX 525 523,
  .CX 789 523,
  .CX 528 523,
  .CX 523 527,
  .CX 529 523,
  .CX 787 523,
  .CCX 523 527 1552,
  .CX 527 523,
  .CX 529 523,
  .CX 787 523,
  .CX 526 525,
  .CX 528 525,
  .CX 529 525,
  .CX 786 525,
  .CX 788 525,
  .CX 789 525,
  .CX 790 525,
  .CX 1552 525,
  .CCX 523 525 1553,
  .CX 527 525,
  .CX 529 525,
  .CX 525 529,
  .CX 1553 529,
  .CX 787 525,
  .CCX 525 529 1554,
  .CX 527 523,
  .CX 525 523,
  .CX 1554 525,
  .CX 1553 523,
  .CX 788 525,
  .CX 787 525,
  .CX 786 525,
  .CX 523 525,
  .CX 1552 525,
  .CX 529 523,
  .CCX 523 525 1556,
  .X 526,
  .CX 528 526,
  .CX 788 526,
  .CX 791 526,
  .CX 1551 526,
  .X 523,
  .CX 527 523,
  .CX 528 523,
  .CX 786 523,
  .CX 787 523,
  .CX 788 523,
  .CX 791 523,
  .CX 1553 523,
  .CX 1554 523,
  .CCX 526 523 789,
  .CX 528 525,
  .CX 523 522,
  .CX 1553 525,
  .CX 527 525,
  .CX 787 525,
  .CX 529 522,
  .CX 525 522,
  .CX 788 522,
  .CX 1554 525,
  .CX 790 525,
  .CX 789 525,
  .CX 786 525,
  .CX 786 522,
  .CX 524 522,
  .CX 1551 525,
  .CX 1552 525,
  .CX 791 522,
  .CCX 522 525 1557,
  .CX 789 788,
  .CX 1551 788,
  .X 523,
  .CX 525 523,
  .CX 529 523,
  .CX 786 523,
  .CX 787 523,
  .CX 789 523,
  .CX 790 523,
  .CX 791 523,
  .CX 1551 523,
  .CX 1554 523,
  .CCX 788 523 1558,
  .CX 1552 524,
  .CX 1552 525,
  .CX 1552 790,
  .CX 1552 1554,
  .measureX 1552 [] [.Z 1554, .CZ 523 529],
  .X 523,
  .X 522,
  .CX 791 523,
  .CX 791 522,
  .CX 786 523,
  .CX 527 523,
  .CX 789 523,
  .CX 788 523,
  .CX 787 523,
  .CX 523 522,
  .CX 1558 523,
  .CX 1553 523,
  .CX 1553 522,
  .CX 1556 523,
  .CX 1554 523,
  .CX 1551 523,
  .CX 1551 522,
  .CX 528 523,
  .CX 526 523,
  .CCX 523 522 1552,
  .CX 788 527,
  .CX 788 786,
  .CX 788 787,
  .CX 788 790,
  .CX 788 1551,
  .CX 788 1552,
  .CX 788 1553,
  .CX 788 1556,
  .CX 788 1557,
  .CX 788 1558,
  .measureX 788 [] [.Z 1552, .CZ 522 523],
  .CX 523 522,
  .CX 525 522,
  .CX 528 522,
  .CX 786 522,
  .CX 787 522,
  .CX 789 522,
  .CX 790 522,
  .CX 1551 522,
  .CX 1558 522,
  .CCX 523 522 788,
  .X 1553,
  .X 789,
  .X 787,
  .X 525,
  .X 524,
  .CX 789 1551,
  .CX 523 1557,
  .CX 523 1556,
  .CX 523 1551,
  .CX 523 790,
  .CX 523 788,
  .CX 523 787,
  .CX 523 786,
  .CX 523 522,
  .CX 525 1556,
  .CX 525 790,
  .CX 525 526,
  .CX 525 523,
  .CX 523 525,
  .CX 525 523,
  .CX 1558 1557,
  .CX 1558 1554,
  .CX 1558 1552,
  .CX 1558 790,
  .CX 1558 787,
  .CX 1558 786,
  .CX 1558 529,
  .CX 1558 789,
  .CX 789 1558,
  .CX 1558 789,
  .CX 522 1553,
  .CX 522 791,
  .CX 522 790,
  .CX 522 529,
  .CX 522 527,
  .CX 522 526,
  .CX 522 789,
  .CX 789 522,
  .CX 522 789,
  .CX 1554 1558,
  .CX 1554 1556,
  .CX 1554 522,
  .CX 529 1558,
  .CX 529 1557,
  .CX 529 1552,
  .CX 529 790,
  .CX 529 786,
  .CX 529 523,
  .CX 788 1558,
  .CX 788 1553,
  .CX 788 1552,
  .CX 788 787,
  .CX 788 527,
  .CX 788 526,
  .CX 788 524,
  .CX 788 522,
  .CX 788 523,
  .CX 523 788,
  .CX 788 523,
  .CX 524 1558,
  .CX 524 1551,
  .CX 524 789,
  .CX 524 526,
  .CX 524 529,
  .CX 529 524,
  .CX 524 529,
  .CX 1551 1558,
  .CX 1551 788,
  .CX 1551 786,
  .CX 1551 523,
  .CX 523 1551,
  .CX 1551 523,
  .CX 528 791,
  .CX 528 790,
  .CX 528 789,
  .CX 789 528,
  .CX 528 789,
  .CX 791 1556,
  .CX 791 1554,
  .CX 791 788,
  .CX 791 522,
  .CX 522 791,
  .CX 791 522,
  .CX 787 1556,
  .CX 787 1553,
  .CX 787 791,
  .CX 787 786,
  .CX 787 527,
  .CX 787 526,
  .CX 787 523,
  .CX 787 789,
  .CX 789 787,
  .CX 787 789,
  .CX 527 1553,
  .CX 527 791,
  .CX 527 789,
  .CX 527 788,
  .CX 527 786,
  .CX 527 529,
  .CX 527 528,
  .CX 527 526,
  .CX 527 523,
  .CX 527 522,
  .CX 522 527,
  .CX 527 522,
  .CX 1553 1554,
  .CX 1553 791,
  .CX 1553 789,
  .CX 1553 528,
  .CX 1553 527,
  .CX 1553 526,
  .CX 1553 522,
  .CX 1553 523,
  .CX 523 1553,
  .CX 1553 523,
  .CX 1557 1558,
  .CX 1557 528,
  .CX 1557 527,
  .CX 786 1557,
  .CX 786 529,
  .CX 786 528,
  .CX 786 526,
  .CX 786 522,
  .CX 786 1551,
  .CX 1551 786,
  .CX 786 1551,
  .CX 1556 1557,
  .CX 1556 788,
  .CX 1556 526,
  .CX 790 1557,
  .CX 790 1553,
  .CX 790 1551,
  .CX 790 791,
  .CX 790 789,
  .CX 790 788,
  .CX 790 528,
  .CX 790 523,
  .CX 790 522,
  .CX 790 786,
  .CX 786 790,
  .CX 790 786,
  .CX 1552 786,
  .CX 1552 529,
  .CX 1552 788,
  .CX 788 1552,
  .CX 1552 788,
  .CX 526 1554,
  .CX 526 1552,
  .CX 526 1551,
  .CX 526 791,
  .CX 526 789,
  .CX 526 788,
  .CX 526 528,
  .CX 526 527,
  .CX 526 525,
  .CX 526 523,
  .measureX 1558 [] [.Z 791, .Z 1557, .CZ 522 523, .CZ 522 528, .CZ 522 788, .CZ 522 1552, .CZ 522 1557, .CZ 523 525, .CZ 523 529, .CZ 523 787, .CZ 523 788, .CZ 523 790, .CZ 523 1552, .CZ 524 527, .CZ 524 1557, .CZ 525 790, .CZ 525 1551, .CZ 525 1557, .CZ 526 787, .CZ 527 791, .CZ 528 1551, .CZ 528 1556, .CZ 529 789, .CZ 529 791, .CZ 529 1552, .CZ 529 1553, .CZ 787 1552, .CZ 787 1553, .CZ 788 790, .CZ 789 1552, .CZ 789 1557, .CZ 790 791, .CZ 790 1552, .CZ 790 1553, .CZ 790 1556, .CZ 790 1557, .CZ 1551 1552, .CZ 1551 1557, .CZ 1552 1553, .CZ 1552 1556],
  .measureX 1557 [] [.Z 788, .Z 789, .Z 791, .Z 1551, .Z 1554, .Z 1556, .CZ 522 526, .CZ 524 525, .CZ 524 526, .CZ 525 526, .CZ 525 528, .CZ 526 788, .CZ 526 791, .CZ 526 1551, .CZ 526 1552, .CZ 526 1553, .CZ 526 1556],
  .measureX 1556 [] [.Z 791, .Z 1552, .CZ 522 523, .CZ 522 524, .CZ 522 525, .CZ 522 526, .CZ 522 786, .CZ 522 788, .CZ 522 791, .CZ 522 1553, .CZ 522 1554, .CZ 523 524, .CZ 523 791, .CZ 523 1553, .CZ 524 529, .CZ 524 788, .CZ 524 789, .CZ 524 790, .CZ 525 791, .CZ 526 528],
  .measureX 1554 [] [.CZ 523 526, .CZ 523 786, .CZ 524 526, .CZ 524 789, .CZ 525 526, .CZ 525 527, .CZ 525 791, .CZ 525 1552, .CZ 525 1553, .CZ 526 529, .CZ 526 788, .CZ 526 789, .CZ 526 790, .CZ 526 1552, .CZ 526 1553, .CZ 527 791, .CZ 790 791],
  .measureX 1553 [] [.Z 1552, .CZ 523 525, .CZ 523 529, .CZ 523 786, .CZ 523 789, .CZ 524 525, .CZ 524 789, .CZ 524 791, .CZ 525 528, .CZ 525 788, .CZ 525 791],
  .measureX 1552 [] [.Z 789, .Z 790, .Z 791, .CZ 522 524, .CZ 522 529, .CZ 522 786, .CZ 522 790, .CZ 523 525, .CZ 523 791, .CZ 523 1551, .CZ 524 525, .CZ 524 787, .CZ 524 791, .CZ 524 1551, .CZ 525 787],
  .measureX 1551 [] [.CZ 522 523, .CZ 522 786, .CZ 522 788, .CZ 523 786, .CZ 523 787, .CZ 523 788, .CZ 523 789, .CZ 523 790, .CZ 525 787],
  .measureX 791 [] [.CZ 523 524, .CZ 523 786, .CZ 523 788, .CZ 523 789, .CZ 523 790, .CZ 524 525, .CZ 524 789, .CZ 524 790],
  .measureX 790 [] [.CZ 525 528, .CZ 525 786, .CZ 526 528],
  .measureX 789 [] [.CZ 523 528, .CZ 523 529, .CZ 523 786, .CZ 524 527, .CZ 526 528],
  .measureX 788 [] [.CZ 524 527, .CZ 525 527, .CZ 525 786, .CZ 526 529],
  .measureX 787 [] [.CZ 522 527, .CZ 522 528, .CZ 522 529, .CZ 522 786],
  .CX 529 1553,
  .CX 786 1554,
  .CX 1553 529,
  .CX 527 1551,
  .CX 528 1552,
  .CX 1552 528,
  .CX 526 786,
  .CX 1554 786,
  .X 527,
  .CX 526 527,
  .CX 1551 527
]
def checkPair (uv : Nat × Nat) : Bool :=
  [false,true].all fun g => [false,true].all fun s =>
    let e := encN_t8 (MorningFour.pre507 g s uv.1 uv.2) MorningFour.sites
    safe15 candidate e && safe15 MorningFour.forward13 e &&
    ((runN_t8 candidate [] (false,e)).2 == (runN_t8 MorningFour.forward13 [] (false,e)).2)



























end ECDSAAdd.Entrant.Forward12Research



-- Verified MorningProduct
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.MorningProduct
open Arithmetic MappedCompressed Secp256k1 History5 MorningFour

def pairs : List (Nat × Nat) := MorningFour.pairs.filter (fun uv=>decide (uv.1*uv.2<32))


theorem product507 (x : Nat) (hx : x<p) :
    (SkywalkNat.step^[507] (SkywalkNat.init x p)).u *
      (SkywalkNat.step^[507] (SkywalkNat.init x p)).v <32 := by
  have hp0 : 0<p := by norm_num [p]
  have hb:=SkywalkNat.iter_product_bound 507 (SkywalkNat.init x p)
  change 2^507*((SkywalkNat.step^[507] (SkywalkNat.init x p)).u*
    (SkywalkNat.step^[507] (SkywalkNat.init x p)).v)≤x*p at hb
  have hxp : x*p<2^512 := (Nat.mul_lt_mul_of_pos_right hx hp0).trans (by norm_num [p])
  have power : (2:Nat)^507*32=2^512 := by norm_num
  rw [←power] at hxp
  exact Nat.lt_of_mul_lt_mul_left (hb.trans_lt hxp)

attribute [local irreducible] run W.compactSkywalkStageVirtual SkywalkTrace.next Nat.iterate
  W.compactSkywalkTick History5.encodePrefix

theorem raw507 (x : Nat) (hx0 : 0<x) (hx : x<p) (raw : State)
    (hraw : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 507 raw.basis) :
    ∃ g s : Bool, ∃ uv∈pairs, ∀ q∈sites, raw.basis q = pre507 g s uv.1 uv.2 q := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := (StackOB5.prime_facts x hx0 hx).2.2.2
  have fields := (W.compactSkywalkStage_fields_iff base _ 507 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨readA, readB, prev, -, future, carry, -, cleanA, -⟩ := fields
  obtain ⟨G, S, encoded⟩ := SkywalkTrace.iter_encoded 507 false false (SkywalkNat.init x p) hp0 hpo
  have sum := W.iter_sum_width x p 507 hp0 hx0 hpo hp hx cop (by omega)
  have valid := SkywalkNat.iter_valid 507 (SkywalkNat.init x p) hp0 hpo
  have term := (SkywalkNat.terminates_511 p x hp0 hx0 hpo hp hx cop).1
  have split : SkywalkNat.step^[511] (SkywalkNat.init x p) =
      SkywalkNat.step^[4] (SkywalkNat.step^[507] (SkywalkNat.init x p)) := by
    rw [← Function.iterate_add_apply]
  rw [split] at term
  change (SkywalkNat.step^[507] (SkywalkNat.init x p)).u+
    (SkywalkNat.step^[507] (SkywalkNat.init x p)).v ≤ 2^(511-507) at sum
  change SkywalkTrace.next^[507] (SkywalkRails.encode false false (x : Int) (p : Int)) =
    SkywalkRails.encode G S ((SkywalkNat.step^[507] (SkywalkNat.init x p)).u : Int)
      ((SkywalkNat.step^[507] (SkywalkNat.init x p)).v : Int) at encoded
  have product := product507 x hx
  generalize SkywalkNat.step^[507] (SkywalkNat.init x p) = z at encoded sum valid term product
  have sixteen : (2:Nat)^(511-507) = 16 := by norm_num
  rw [sixteen] at sum
  have oldmem := MorningFour.pairs_of z sum valid.1 valid.2.1 (valid.2.2.trans cop) term
  have mem : (z.u,z.v)∈pairs := by
    simp only [pairs,List.mem_filter]
    exact ⟨oldmem,by simpa using product⟩
  rw [encoded, retainedA507] at readA
  rw [encoded, retainedB507] at readB
  rw [encoded] at prev
  have bA := signed6_cases _ _ _ _ _ _ raw.basis _ readA
  have bB := signed6_cases _ _ _ _ _ _ raw.basis _ readB
  have f7 := future 507 (le_refl _) (by omega)
  have f8 := future 508 (by omega) (by omega)
  have f9 := future 509 (by omega) (by omega)
  have f10 := future 510 (by omega) (by omega)
  have c1540 : raw.basis (base 1540) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1540, by simp, rfl⟩)
  have c1541 : raw.basis (base 1541) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1541, by simp, rfl⟩)
  have c1542 : raw.basis (base 1542) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1542, by simp, rfl⟩)
  have c1543 : raw.basis (base 1543) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1543, by simp, rfl⟩)
  have c513 : raw.basis (base 513) = false := cleanA _ releasedA507
  have prev' : raw.basis (base 506) = G := by
    have h : skywalkPoolPreviousId 507 = 506 := rfl
    rw [h] at prev
    cases G <;> simpa [SkywalkRails.encode] using prev
  refine ⟨G,S,_,mem,?_⟩
  intro q hq
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prev'
  · simpa [pre507] using bA.1
  · exact bA.2.1
  · exact bA.2.2.1
  · exact bA.2.2.2.1
  · exact bA.2.2.2.2.1
  · exact bA.2.2.2.2.2
  · exact c513
  · simpa [pre507] using bB.1
  · exact bB.2.1
  · exact bB.2.2.1
  · exact bB.2.2.2.1
  · exact bB.2.2.2.2.1
  · exact bB.2.2.2.2.2
  · exact f7.2
  · exact f8.2
  · exact f9.2
  · exact f10.2
  · exact c1540
  · exact c1541
  · exact c1542
  · exact c1543

end ECDSAAdd.Entrant.MorningProduct

-- Verified MorningOrientation
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.MorningOrientation
open Arithmetic MappedCompressed Secp256k1




















































open History5 MorningFour
attribute [local irreducible] run W.compactSkywalkStageVirtual SkywalkTrace.next Nat.iterate
  W.compactSkywalkTick History5.encodePrefix



















































































end ECDSAAdd.Entrant.MorningOrientation

-- Verified MorningWidth
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.MorningWidth
open Arithmetic MappedCompressed Secp256k1

theorem iter_budget : ∀ (i a b : Nat) (z : SkywalkNat.State),
    0<z.v → z.v%2=1 → z.u.Coprime z.v → z.u<2^a → z.v<2^b → i+1≤a+b →
    ∃ a' b', a'+b'+i=a+b ∧ (SkywalkNat.step^[i] z).u<2^a' ∧
      (SkywalkNat.step^[i] z).v<2^b' := by
  intro i
  induction i with
  | zero =>
    intro a b z _ _ _ hu hv _
    exact ⟨a,b,by omega,hu,hv⟩
  | succ i ih =>
    intro a b z hv hvo hc hu hb hi
    by_cases hz : z.u=0
    · have h1 : z.v=1 := by
        have h:=hc
        change Nat.gcd z.u z.v=1 at h
        simpa [hz] using h
      refine ⟨0,a+b-(i+1),by omega,?_,?_⟩
      · rw [SkywalkNat.iter_fixed_of_u_zero _ _ hz,hz]; norm_num
      · rw [SkywalkNat.iter_fixed_of_u_zero _ _ hz,h1]
        have h : 1≤a+b-(i+1) := by omega
        exact lt_of_lt_of_le (by norm_num : 1<(2:Nat)^1) (Nat.pow_le_pow_right (by norm_num) h)
    · obtain ⟨a',b',he,ha',hb'⟩:=SkywalkNat.step_exponent_budget z a b (Nat.pos_of_ne_zero hz) hv hu hb
      have v:=SkywalkNat.step_v_odd_pos z hv hvo
      obtain ⟨aa,bb,he',haa,hbb⟩:=ih a' b' (SkywalkNat.step z) v.1 v.2
        (SkywalkNat.step_coprime z hvo hc) ha' hb' (by omega)
      refine ⟨aa,bb,by omega,?_,?_⟩ <;> rw [Function.iterate_succ_apply] <;> assumption

theorem width507 (x : Nat) (hx0 : 0<x) (hx : x<p) :
    ∃ a b : Nat, a+b=5 ∧
      (SkywalkNat.step^[507] (SkywalkNat.init x p)).u<2^a ∧
      (SkywalkNat.step^[507] (SkywalkNat.init x p)).v<2^b := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := (StackOB5.prime_facts x hx0 hx).2.2.2
  obtain ⟨a,b,h,ha,hb⟩:=iter_budget 507 256 256 (SkywalkNat.init x p) hp0 hpo cop (hx.trans hp) hp (by omega)
  exact ⟨a,b,by omega,ha,hb⟩


theorem odd_width (z : SkywalkNat.State) (ho : z.u%2≠0) (hv : z.v%2=1)
    (a b : Nat) (hu : z.u<2^a) (hb : z.v<2^b) :
    ∃ aa bb, aa+bb=a+b ∧ (SkywalkNat.step z).v<2^aa ∧
      2*(SkywalkNat.step z).u+(SkywalkNat.step z).v<2^bb := by
  have hz : z.u≠0 := by omega
  simp only [SkywalkNat.step,if_neg hz,if_neg ho]
  split_ifs with h
  · refine ⟨b,a,by omega,hb,?_⟩
    dsimp; omega
  · refine ⟨a,b,rfl,hu,?_⟩
    dsimp; omega

theorem orientation_width (x : Nat) (hx0 : 0<x) (hx : x<p) (g s : Bool)
    (henc : SkywalkTrace.next^[507] (SkywalkRails.encode false false (x:Int) (p:Int)) =
      SkywalkRails.encode g s ((SkywalkNat.step^[507] (SkywalkNat.init x p)).u:Int)
        ((SkywalkNat.step^[507] (SkywalkNat.init x p)).v:Int))
    (hg : g=false) :
    let z:=SkywalkNat.step^[507] (SkywalkNat.init x p)
    ∃ a b, a+b=6 ∧ z.v<2^a ∧ 2*z.u+z.v<2^b := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  obtain ⟨G,S,he⟩:=SkywalkTrace.iter_encoded 506 false false (SkywalkNat.init x p) hp0 hpo
  change SkywalkTrace.next^[506] (SkywalkRails.encode false false (x:Int) (p:Int)) = _ at he
  have hv:=SkywalkNat.iter_valid 506 (SkywalkNat.init x p) hp0 hpo
  have hc:=SkywalkTrace.code_classified G S (SkywalkNat.step^[506] (SkywalkNat.init x p)) hv.1 hv.2.1
  have hge:=congrArg SkywalkRails.State.g henc
  rw [show (507:Nat)=506+1 from rfl,Function.iterate_succ_apply',he] at hge
  have eg (g s : Bool) (u v : Int) : (SkywalkRails.encode g s u v).g=g := by cases g <;> rfl
  simp only [SkywalkTrace.next,SkywalkRails.railsOf,eg] at hge
  change (SkywalkRails.step (SkywalkRails.encode G S
    ((SkywalkNat.step^[506] (SkywalkNat.init x p)).u:Int)
    ((SkywalkNat.step^[506] (SkywalkNat.init x p)).v:Int))).g=g at hge
  have ho : (SkywalkNat.step^[506] (SkywalkNat.init x p)).u%2≠0 := by
    have hh : decide ((SkywalkNat.step^[506] (SkywalkNat.init x p)).u%2=0)=false := by
      exact hc.1.symm.trans (hge.trans hg)
    simpa using hh
  have hp : p<2^256 := by norm_num [p]
  have cop := (StackOB5.prime_facts x hx0 hx).2.2.2
  obtain ⟨a,b,h,ha,hb⟩:=iter_budget 506 256 256 (SkywalkNat.init x p) hp0 hpo cop (hx.trans hp) hp (by omega)
  obtain ⟨aa,bb,he,haa,hbb⟩:=odd_width _ ho hv.2.1 a b ha hb
  dsimp only
  rw [show (507:Nat)=506+1 from rfl,Function.iterate_succ_apply']
  exact ⟨aa,bb,by omega,haa,hbb⟩



open History5 MorningFour
attribute [local irreducible] run W.compactSkywalkStageVirtual SkywalkTrace.next Nat.iterate
  W.compactSkywalkTick History5.encodePrefix

theorem raw507 (x : Nat) (hx0 : 0<x) (hx : x<p) (raw : State)
    (hraw : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 507 raw.basis) :
    ∃ g s : Bool, ∃ uv∈MorningProduct.pairs,
      (∃ a b : Nat, a+b=5 ∧ uv.1<2^a ∧ uv.2<2^b) ∧
      (g=false → ∃ a b : Nat, a+b=6 ∧ uv.2<2^a ∧ 2*uv.1+uv.2<2^b) ∧ ∀ q∈sites, raw.basis q = pre507 g s uv.1 uv.2 q := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := (StackOB5.prime_facts x hx0 hx).2.2.2
  have fields := (W.compactSkywalkStage_fields_iff base _ 507 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨readA, readB, prev, -, future, carry, -, cleanA, -⟩ := fields
  obtain ⟨G, S, encoded⟩ := SkywalkTrace.iter_encoded 507 false false (SkywalkNat.init x p) hp0 hpo
  have sum := W.iter_sum_width x p 507 hp0 hx0 hpo hp hx cop (by omega)
  have valid := SkywalkNat.iter_valid 507 (SkywalkNat.init x p) hp0 hpo
  have term := (SkywalkNat.terminates_511 p x hp0 hx0 hpo hp hx cop).1
  have split : SkywalkNat.step^[511] (SkywalkNat.init x p) =
      SkywalkNat.step^[4] (SkywalkNat.step^[507] (SkywalkNat.init x p)) := by
    rw [← Function.iterate_add_apply]
  rw [split] at term
  change (SkywalkNat.step^[507] (SkywalkNat.init x p)).u+
    (SkywalkNat.step^[507] (SkywalkNat.init x p)).v ≤ 2^(511-507) at sum
  change SkywalkTrace.next^[507] (SkywalkRails.encode false false (x : Int) (p : Int)) =
    SkywalkRails.encode G S ((SkywalkNat.step^[507] (SkywalkNat.init x p)).u : Int)
      ((SkywalkNat.step^[507] (SkywalkNat.init x p)).v : Int) at encoded
  have product := MorningProduct.product507 x hx
  have width := width507 x hx0 hx
  have oriented := orientation_width x hx0 hx G S encoded
  generalize SkywalkNat.step^[507] (SkywalkNat.init x p) = z at encoded sum valid term product oriented width
  have sixteen : (2:Nat)^(511-507) = 16 := by norm_num
  rw [sixteen] at sum
  have oldmem := MorningFour.pairs_of z sum valid.1 valid.2.1 (valid.2.2.trans cop) term
  have mem : (z.u,z.v)∈MorningProduct.pairs := by
    simp only [MorningProduct.pairs,List.mem_filter]
    exact ⟨oldmem,by simpa using product⟩
  rw [encoded, retainedA507] at readA
  rw [encoded, retainedB507] at readB
  rw [encoded] at prev
  have bA := signed6_cases _ _ _ _ _ _ raw.basis _ readA
  have bB := signed6_cases _ _ _ _ _ _ raw.basis _ readB
  have f7 := future 507 (le_refl _) (by omega)
  have f8 := future 508 (by omega) (by omega)
  have f9 := future 509 (by omega) (by omega)
  have f10 := future 510 (by omega) (by omega)
  have c1540 : raw.basis (base 1540) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1540, by simp, rfl⟩)
  have c1541 : raw.basis (base 1541) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1541, by simp, rfl⟩)
  have c1542 : raw.basis (base 1542) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1542, by simp, rfl⟩)
  have c1543 : raw.basis (base 1543) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1543, by simp, rfl⟩)
  have c513 : raw.basis (base 513) = false := cleanA _ releasedA507
  have prev' : raw.basis (base 506) = G := by
    have h : skywalkPoolPreviousId 507 = 506 := rfl
    rw [h] at prev
    cases G <;> simpa [SkywalkRails.encode] using prev
  refine ⟨G,S,_,mem,width,oriented,?_⟩
  intro q hq
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prev'
  · simpa [pre507] using bA.1
  · exact bA.2.1
  · exact bA.2.2.1
  · exact bA.2.2.2.1
  · exact bA.2.2.2.2.1
  · exact bA.2.2.2.2.2
  · exact c513
  · simpa [pre507] using bB.1
  · exact bB.2.1
  · exact bB.2.2.1
  · exact bB.2.2.2.1
  · exact bB.2.2.2.2.1
  · exact bB.2.2.2.2.2
  · exact f7.2
  · exact f8.2
  · exact f9.2
  · exact f10.2
  · exact c1540
  · exact c1541
  · exact c1542
  · exact c1543



end ECDSAAdd.Entrant.MorningWidth

-- Verified Forward11Physical
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.Forward11Width
set_option linter.unusedSimpArgs false
open Arithmetic MappedCompressed Secp256k1 History5

def widthPair (u v n : Nat) : Bool :=
 (List.range (n+1)).any fun a=>decide (u<2^a ∧ v<2^(n-a))
def legal (uv : Nat × Nat) (g : Bool) : Bool :=
 widthPair uv.1 uv.2 5 && (g || widthPair uv.2 (2*uv.1+uv.2) 6)

theorem widthPair_of (u v n a b : Nat) (he : a+b=n) (hu : u<2^a) (hv : v<2^b) :
 widthPair u v n=true := by
 unfold widthPair
 apply List.any_eq_true.mpr
 refine ⟨a,List.mem_range.mpr (by omega),?_⟩
 have hb : n-a=b := by omega
 simp only [hb,decide_eq_true_eq]
 exact ⟨hu,hv⟩

theorem legal_of (uv : Nat × Nat) (g : Bool)
 (hw : ∃ a b : Nat,a+b=5 ∧ uv.1<2^a ∧ uv.2<2^b)
 (hg : g=false → ∃ a b : Nat,a+b=6 ∧ uv.2<2^a ∧ 2*uv.1+uv.2<2^b) : legal uv g=true := by
 obtain ⟨a,b,he,hu,hv⟩:=hw
 have h:=widthPair_of _ _ _ a b he hu hv
 unfold legal
 rw [h,Bool.true_and]
 cases g
 · obtain ⟨a,b,he,hu,hv⟩:=hg rfl
   exact widthPair_of _ _ _ a b he hu hv
 · rfl

def block0 : Program := [
 .X 786,
 .CX 523 786,
 .CX 787 528,
 .CX 528 787,
 .CX 528 527,
 .CX 527 528,
 .CX 526 527,
 .CX 527 526,
 .CX 526 527,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 524 791,
 .CX 524 790,
 .CX 524 789,
 .CX 524 788,
 .CX 524 787,
 .CX 524 528,
 .CX 524 527,
 .CX 524 526,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 525,
 .CX 525 522,
 .CX 522 525,
 .CCX 522 523 524,
 .CX 788 787,
 .CX 787 788,
 .CX 787 528,
 .CX 528 787
]
def block1 : Program := [
 .CX 528 523,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 526 791,
 .CX 526 790,
 .CX 526 789,
 .CX 526 788,
 .CX 526 787,
 .CX 526 528,
 .CX 526 527,
 .CX 526 523,
 .CX 525 527,
 .CX 527 525,
 .CX 525 527,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 525,
 .CX 522 523,
 .X 523,
 .CCX 522 523 524,
 .X 523,
 .CX 789 528,
 .CX 788 789,
 .CX 789 788,
 .CX 788 789,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 528 787,
 .CX 528 525
]
def block2 : Program := [
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 526 527,
 .CX 527 526,
 .CX 526 527,
 .CX 525 526,
 .CX 525 523,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 524,
 .CX 522 523,
 .CCX 522 523 529,
 .CX 522 523,
 .CX 523 524,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 525 523,
 .CX 525 526,
 .CX 526 527,
 .CX 527 526,
 .CX 526 527,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 528 525,
 .CX 528 787,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788
]
def block3 : Program := [
 .CX 788 789,
 .CX 789 788,
 .CX 788 789,
 .CX 789 528,
 .CX 790 788,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 788 789,
 .CX 788 525,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 528 787,
 .CX 787 528,
 .CX 528 787,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 525 527,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 786,
 .CX 522 524,
 .CX 524 522
]
def block4 : Program := [
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 525 527,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 528 787,
 .CX 787 528,
 .CX 528 787,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 788 525,
 .CX 788 789,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 790 788,
 .CX 786 526,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 791 529,
 .CX 529 791,
 .CX 791 529,
 .CX 790 788,
 .CX 789 791
]
def block5 : Program := [
 .CX 791 789,
 .CX 789 791,
 .CX 788 790,
 .CX 788 789,
 .CX 789 788,
 .CX 788 789,
 .CX 787 789,
 .CX 789 787,
 .CX 787 789,
 .CX 528 788,
 .CX 788 528,
 .CX 528 788,
 .CX 527 787,
 .CX 787 527,
 .CX 527 787,
 .CX 526 528,
 .CX 526 524,
 .CX 525 527,
 .CX 527 525,
 .CX 525 527,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 1551,
 .CX 522 524
]
def block6 : Program := [
 .CX 524 522,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 525 527,
 .CX 527 525,
 .CX 525 527,
 .CX 526 524,
 .CX 526 528,
 .CX 527 787,
 .CX 787 527,
 .CX 527 787,
 .CX 528 788,
 .CX 788 528,
 .CX 528 788,
 .CX 787 789,
 .CX 789 787,
 .CX 787 789,
 .CX 788 789,
 .CX 789 788,
 .CX 788 789,
 .CX 788 790,
 .CX 789 791,
 .CX 791 789,
 .CX 789 791,
 .CX 790 788,
 .CX 791 529
]
def block7 : Program := [
 .CX 529 791,
 .CX 791 529,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 786 526,
 .CX 1551 790,
 .CX 786 524,
 .CX 529 1551,
 .CX 1551 529,
 .CX 529 1551,
 .CX 791 786,
 .CX 786 791,
 .CX 791 786,
 .CX 790 529,
 .CX 790 788,
 .CX 789 791,
 .CX 791 789,
 .CX 789 791,
 .CX 788 790,
 .CX 788 526,
 .CX 787 789,
 .CX 789 787,
 .CX 787 789,
 .CX 528 788,
 .CX 788 528,
 .CX 528 788,
 .CX 527 787,
 .CX 787 527,
 .CX 527 787,
 .CX 526 528,
 .CX 526 525
]
def block8 : Program := [
 .CX 526 527,
 .CX 527 526,
 .CX 526 527,
 .CX 525 527,
 .CX 524 526,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 1552,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 526,
 .CX 525 527,
 .CX 526 527,
 .CX 527 526,
 .CX 526 527,
 .CX 526 525,
 .CX 526 528,
 .CX 527 787,
 .CX 787 527,
 .CX 527 787,
 .CX 528 788,
 .CX 788 528,
 .CX 528 788,
 .CX 787 789
]
def block9 : Program := [
 .CX 789 787,
 .CX 787 789,
 .CX 788 526,
 .CX 788 790,
 .CX 789 791,
 .CX 791 789,
 .CX 789 791,
 .CX 790 788,
 .CX 790 529,
 .CX 791 786,
 .CX 786 791,
 .CX 791 786,
 .CX 529 1551,
 .CX 1551 529,
 .CX 529 1551,
 .CX 786 524,
 .CX 1551 790,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1551 523,
 .CX 786 1551,
 .CX 1551 786,
 .CX 786 1551,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 791 790,
 .CX 791 529,
 .CX 529 791,
 .CX 791 529,
 .CX 790 529,
 .CX 790 788
]
def block10 : Program := [
 .CX 789 791,
 .CX 791 789,
 .CX 789 791,
 .CX 788 790,
 .CX 788 787,
 .CX 788 789,
 .CX 789 788,
 .CX 788 789,
 .CX 787 789,
 .CX 787 526,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 528 788,
 .CX 788 528,
 .CX 528 788,
 .CX 527 787,
 .CX 787 527,
 .CX 527 787,
 .CX 526 528,
 .CX 525 527,
 .CX 527 525,
 .CX 525 527,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 525,
 .CX 523 522,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 522 524
]
def block11 : Program := [
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CCX 522 523 1553,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CX 522 524,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 523 522,
 .CX 523 525,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 525 527,
 .CX 527 525,
 .CX 525 527,
 .CX 526 528,
 .CX 527 787,
 .CX 787 527,
 .CX 527 787,
 .CX 528 788,
 .CX 788 528,
 .CX 528 788,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 787 526,
 .CX 787 789,
 .CX 788 789
]
def block12 : Program := [
 .CX 789 788,
 .CX 788 789,
 .CX 788 787,
 .CX 788 790,
 .CX 789 791,
 .CX 791 789,
 .CX 789 791,
 .CX 790 788,
 .CX 790 529,
 .CX 791 529,
 .CX 529 791,
 .CX 791 529,
 .CX 791 790,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 786 1551,
 .CX 1551 786,
 .CX 786 1551,
 .CX 1551 523,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1551 529,
 .CX 786 1551,
 .CX 786 529,
 .CX 786 528,
 .CX 529 1551,
 .CX 529 790
]
def block13 : Program := [
 .CX 791 786,
 .CX 786 791,
 .CX 791 786,
 .CX 790 529,
 .CX 790 789,
 .CX 790 791,
 .CX 791 790,
 .CX 790 791,
 .CX 789 791,
 .CX 789 790,
 .CX 789 787,
 .CX 789 528,
 .CX 788 790,
 .CX 790 788,
 .CX 788 790,
 .CX 787 789,
 .CX 787 788,
 .CX 787 528,
 .CX 787 526,
 .CX 528 788,
 .CX 528 527,
 .CX 528 787,
 .CX 787 528,
 .CX 528 787,
 .CX 527 787,
 .CX 527 524,
 .CX 526 528,
 .CX 526 527,
 .CX 527 526,
 .CX 526 527,
 .CX 525 527,
 .CX 527 525
]
def block14 : Program := [
 .CX 525 527,
 .CX 524 526,
 .CX 524 522,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 522 523,
 .CCX 522 523 1554,
 .CX 522 523,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 522,
 .CX 524 526,
 .CX 525 527,
 .CX 527 525,
 .CX 525 527,
 .CX 526 527,
 .CX 527 526,
 .CX 526 527,
 .CX 526 528,
 .CX 527 524,
 .CX 527 787,
 .CX 528 787,
 .CX 787 528,
 .CX 528 787,
 .CX 528 527,
 .CX 528 788,
 .CX 787 526,
 .CX 787 528
]
def block15 : Program := [
 .CX 787 788,
 .CX 787 789,
 .CX 788 790,
 .CX 790 788,
 .CX 788 790,
 .CX 789 528,
 .CX 789 787,
 .CX 789 790,
 .CX 789 791,
 .CX 790 791,
 .CX 791 790,
 .CX 790 791,
 .CX 790 789,
 .CX 790 529,
 .CX 791 786,
 .CX 786 791,
 .CX 791 786,
 .CX 529 790,
 .CX 529 1551,
 .CX 786 528,
 .CX 786 529,
 .CX 786 1551,
 .CX 1551 529,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1552 1551
]
def block16 : Program := [
 .CX 1552 786,
 .CX 1551 1552,
 .CX 1551 786,
 .CX 1551 529,
 .CX 786 1552,
 .CX 786 1551,
 .CX 786 529,
 .CX 786 527,
 .CX 529 1551,
 .CX 529 787,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 791 786,
 .CX 786 791,
 .CX 791 786,
 .CX 790 529,
 .CX 529 790,
 .CX 790 529,
 .CX 789 791,
 .CX 791 789,
 .CX 789 791,
 .CX 788 790,
 .CX 790 788,
 .CX 788 790,
 .CX 787 789,
 .CX 787 524,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 528 788,
 .CX 788 528
]
def block17 : Program := [
 .CX 528 788,
 .CX 527 787,
 .CX 527 528,
 .CX 527 525,
 .CX 527 524,
 .CX 526 528,
 .CX 528 526,
 .CX 526 528,
 .CX 525 527,
 .CX 525 523,
 .CX 524 526,
 .CX 524 522,
 .CX 523 525,
 .CX 523 524,
 .CX 523 522,
 .CX 522 524,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CCX 522 523 1556,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CX 522 524,
 .CX 523 522,
 .CX 523 524,
 .CX 523 525,
 .CX 524 522,
 .CX 524 526,
 .CX 525 523,
 .CX 525 527,
 .CX 526 528
]
def block18 : Program := [
 .CX 528 526,
 .CX 526 528,
 .CX 527 524,
 .CX 527 525,
 .CX 527 528,
 .CX 527 787,
 .CX 528 788,
 .CX 788 528,
 .CX 528 788,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 787 524,
 .CX 787 789,
 .CX 788 790,
 .CX 790 788,
 .CX 788 790,
 .CX 789 791,
 .CX 791 789,
 .CX 789 791,
 .CX 790 529,
 .CX 529 790,
 .CX 790 529,
 .CX 791 786,
 .CX 786 791,
 .CX 791 786,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 529 787,
 .CX 529 1551,
 .CX 786 527
]
def block19 : Program := [
 .CX 786 529,
 .CX 786 1551,
 .CX 786 1552,
 .CX 1551 529,
 .CX 1551 786,
 .CX 1551 1552,
 .CX 1552 786,
 .CX 1552 1551,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1552 786,
 .CX 1551 529,
 .CX 786 1552,
 .CX 786 527,
 .CX 529 1551,
 .CX 529 787,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 791 786,
 .CX 786 791,
 .CX 791 786,
 .CX 790 529,
 .CX 529 790,
 .CX 790 529,
 .CX 789 791
]
def block20 : Program := [
 .CX 791 789,
 .CX 789 791,
 .CX 788 790,
 .CX 790 788,
 .CX 788 790,
 .CX 787 789,
 .CX 787 526,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 528 788,
 .CX 788 528,
 .CX 528 788,
 .CX 527 787,
 .CX 527 522,
 .CX 526 528,
 .CX 526 524,
 .CX 525 527,
 .CX 527 525,
 .CX 525 527,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CCX 522 523 1557
]
def block21 : Program := [
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 525 527,
 .CX 527 525,
 .CX 525 527,
 .CX 526 524,
 .CX 526 528,
 .CX 527 522,
 .CX 527 787,
 .CX 528 788,
 .CX 788 528,
 .CX 528 788,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 787 526,
 .CX 787 789,
 .CX 788 790,
 .CX 790 788,
 .CX 788 790,
 .CX 789 791,
 .CX 791 789,
 .CX 789 791
]
def block22 : Program := [
 .CX 790 529,
 .CX 529 790,
 .CX 790 529,
 .CX 791 786,
 .CX 786 791,
 .CX 791 786,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 529 787,
 .CX 529 1551,
 .CX 786 527,
 .CX 786 1552,
 .CX 1551 529,
 .CX 1552 786,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1557 1553,
 .CX 1556 1557,
 .CX 1557 1556,
 .CX 1556 1557,
 .CX 1554 1556,
 .CX 1556 1554,
 .CX 1554 1556,
 .CX 1553 1554,
 .CX 1553 1551,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552
]
def block23 : Program := [
 .CX 1551 786,
 .CX 786 1551,
 .CX 786 790,
 .CX 529 791,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 791 786,
 .CX 791 529,
 .CX 791 790,
 .CX 791 789,
 .CX 790 529,
 .CX 790 791,
 .CX 790 789,
 .CX 790 788,
 .CX 789 791,
 .CX 789 528,
 .CX 788 790,
 .CX 788 787,
 .CX 788 789,
 .CX 789 788,
 .CX 788 789,
 .CX 787 789,
 .CX 787 788,
 .CX 787 528,
 .CX 528 788,
 .CX 528 527,
 .CX 528 787,
 .CX 787 528,
 .CX 528 787,
 .CX 527 787,
 .CX 527 522
]
def block24 : Program := [
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 526 528,
 .CX 528 526,
 .CX 526 528,
 .CX 525 527,
 .CX 527 525,
 .CX 525 527,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 522 523,
 .CCX 522 523 1558,
 .CX 522 523,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 525 527,
 .CX 527 525,
 .CX 525 527,
 .CX 526 528,
 .CX 528 526,
 .CX 526 528
]
def block25 : Program := [
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 527 522,
 .CX 527 787,
 .CX 528 787,
 .CX 787 528,
 .CX 528 787,
 .CX 528 527,
 .CX 528 788,
 .CX 787 528,
 .CX 787 788,
 .CX 787 789,
 .CX 788 789,
 .CX 789 788,
 .CX 788 789,
 .CX 788 787,
 .CX 788 790,
 .CX 789 528,
 .CX 789 791,
 .CX 790 788,
 .CX 790 789,
 .CX 790 791,
 .CX 790 529,
 .CX 791 789,
 .CX 791 790,
 .CX 791 529,
 .CX 791 786,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 529 791
]
def block26 : Program := [
 .CX 786 790,
 .CX 786 1551,
 .CX 1551 786,
 .CX 1551 1552,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1553 1551,
 .CX 1553 1554,
 .CX 1554 1556,
 .CX 1556 1554,
 .CX 1554 1556,
 .CX 1556 1557,
 .CX 1557 1556,
 .CX 1556 1557,
 .CX 1557 1553,
 .CX 1558 1556,
 .CX 1558 1554,
 .CX 1558 790,
 .CX 1558 787,
 .CX 1558 525,
 .CX 1557 790,
 .CX 1556 1558,
 .CX 1556 1557,
 .CX 1556 791,
 .CX 1556 788,
 .CX 1556 525,
 .CX 1554 529,
 .CX 1554 789,
 .CX 1554 528,
 .CX 1554 1556,
 .CX 1556 1554
]
def block27 : Program := [
 .CX 1554 1556,
 .CX 1553 529,
 .CX 1553 789,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1552 1557,
 .CX 1552 1556,
 .CX 1552 1554,
 .CX 1552 1553,
 .CX 1552 791,
 .CX 1552 790,
 .CX 1552 788,
 .CX 1552 787,
 .CX 1552 528,
 .CX 1551 1553,
 .CX 1551 791,
 .CX 1551 788,
 .CX 1551 787,
 .CX 786 1556,
 .CX 786 1554,
 .CX 786 1553,
 .CX 786 791,
 .CX 786 788,
 .CX 786 787,
 .CX 786 528,
 .CX 786 524,
 .CX 786 523,
 .CX 529 1558,
 .CX 529 1557,
 .CX 529 1556,
 .CX 529 791
]
def block28 : Program := [
 .CX 529 789,
 .CX 529 787,
 .CX 529 528,
 .CX 529 525,
 .CX 529 1551,
 .CX 1551 529,
 .CX 529 1551,
 .CX 791 1556,
 .CX 791 1554,
 .CX 791 1551,
 .CX 791 528,
 .CX 791 529,
 .CX 529 791,
 .CX 791 529,
 .CX 790 1557,
 .CX 790 1554,
 .CX 790 789,
 .CX 790 1551,
 .CX 1551 790,
 .CX 790 1551,
 .CX 789 1558,
 .CX 789 1557,
 .CX 789 1556,
 .CX 789 1553,
 .CX 789 1551,
 .CX 789 529,
 .CX 789 788,
 .CX 789 528,
 .CX 789 525,
 .CX 788 1558,
 .CX 788 1557,
 .CX 788 1556
]
def block29 : Program := [
 .CX 788 1554,
 .CX 788 1553,
 .CX 788 529,
 .CX 788 528,
 .CX 788 525,
 .CX 787 1558,
 .CX 787 1557,
 .CX 787 1556,
 .CX 787 1554,
 .CX 787 786,
 .CX 787 528,
 .CX 787 526,
 .CX 787 525,
 .CX 787 524,
 .CX 787 523,
 .CX 787 790,
 .CX 790 787,
 .CX 787 790,
 .CX 528 1558,
 .CX 528 1557,
 .CX 528 1556,
 .CX 528 1554,
 .CX 528 1553,
 .CX 528 529,
 .CX 528 525,
 .CX 528 790,
 .CX 790 528,
 .CX 528 790,
 .CX 527 522,
 .CX 527 789,
 .CX 789 527,
 .CX 527 789
]
def block30 : Program := [
 .CX 526 1558,
 .CX 526 1557,
 .CX 526 1553,
 .CX 526 786,
 .CX 526 529,
 .CX 526 790,
 .CX 526 787,
 .CX 526 528,
 .CX 526 527,
 .CX 526 525,
 .CX 526 524,
 .CX 526 523,
 .CX 525 1558,
 .CX 525 1557,
 .CX 525 1553,
 .CX 525 790,
 .CX 525 787,
 .CX 525 528,
 .CX 528 525,
 .CX 525 528,
 .CX 524 786,
 .CX 524 529,
 .CX 524 528,
 .CX 524 527,
 .CX 524 523,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 786,
 .CX 523 529,
 .CX 523 789,
 .CX 789 523
]
def block31 : Program := [
 .CX 523 789,
 .CX 522 788,
 .CX 522 787,
 .CX 522 525,
 .CX 522 524,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .measureX 1558 [] [.Z 527, .Z 528, .Z 787, .Z 788, .Z 790, .Z 1553, .Z 1557, .CZ 522 527, .CZ 522 528, .CZ 522 787, .CZ 522 788, .CZ 522 1553, .CZ 522 1557],
 .X 1557,
 .measureX 1557 [] [.Z 522, .Z 527, .Z 788, .Z 790, .Z 529, .Z 786, .Z 1551, .Z 1552, .Z 1554, .CZ 522 523, .CZ 522 524, .CZ 522 527, .CZ 522 528, .CZ 522 787, .CZ 522 788, .CZ 522 790, .CZ 522 786, .CZ 523 525, .CZ 523 526, .CZ 523 790, .CZ 523 1551, .CZ 523 1554, .CZ 524 789, .CZ 524 791, .CZ 526 527, .CZ 526 1554],
 .measureX 1556 [] [.Z 523, .Z 524, .Z 789, .Z 790, .Z 786, .Z 1551, .Z 1553, .Z 1554, .CZ 522 527, .CZ 522 528, .CZ 522 787, .CZ 522 788, .CZ 522 1554, .CZ 523 1554],
 .measureX 1554 [] [.Z 523, .Z 525, .Z 526, .Z 789, .Z 786, .Z 1551, .CZ 522 523, .CZ 523 525, .CZ 523 789, .CZ 523 790, .CZ 523 791, .CZ 523 1552, .CZ 524 525],
 .measureX 1553 [] [.Z 522, .Z 524, .Z 789, .Z 790, .Z 786, .CZ 522 527, .CZ 522 528, .CZ 522 787, .CZ 522 788, .CZ 522 790, .CZ 522 786, .CZ 523 790, .CZ 523 786],
 .X 1552,
 .measureX 1552 [] [.Z 522, .Z 523, .Z 524, .Z 528, .Z 787, .Z 788, .Z 789, .Z 790, .Z 791, .CZ 522 523, .CZ 523 525, .CZ 523 789, .CZ 523 790, .CZ 524 525, .CZ 524 526, .CZ 524 787, .CZ 524 788, .CZ 524 789, .CZ 524 790, .CZ 524 529],
 .measureX 1551 [] [.Z 522, .Z 523, .Z 525, .Z 526, .Z 528, .Z 789, .Z 790, .CZ 522 524, .CZ 522 525, .CZ 522 527, .CZ 522 528, .CZ 523 524, .CZ 523 525, .CZ 523 787, .CZ 523 788, .CZ 523 790, .CZ 524 787, .CZ 524 788, .CZ 524 789, .CZ 524 790, .CZ 525 789, .CZ 526 527, .CZ 527 528, .CZ 527 789, .CZ 528 789],
 .X 786,
 .measureX 786 [] [.Z 522, .Z 523, .Z 524, .Z 526, .Z 528, .Z 787, .Z 788, .Z 789, .Z 790, .Z 791, .Z 529, .CZ 522 523, .CZ 523 524, .CZ 523 525, .CZ 523 789, .CZ 524 787, .CZ 524 788, .CZ 524 790],
 .measureX 529 [] [.Z 522, .Z 523, .Z 525, .Z 526, .Z 787, .CZ 523 528, .CZ 523 787, .CZ 523 788, .CZ 525 527, .CZ 525 788, .CZ 526 528, .CZ 526 787],
 .measureX 791 [] [.CZ 523 528, .CZ 523 787, .CZ 523 788, .CZ 525 527, .CZ 525 528, .CZ 525 788],
 .X 790,
 .measureX 790 [] [.Z 523, .Z 788, .CZ 523 528, .CZ 523 787, .CZ 523 788, .CZ 524 527, .CZ 525 528, .CZ 526 787],
 .measureX 789 [] [.Z 522, .Z 523, .Z 524, .Z 525, .Z 787, .CZ 524 527, .CZ 525 527, .CZ 525 528, .CZ 526 528, .CZ 526 787],
 .CX 527 1551,
 .CX 1551 527,
 .CX 527 1551,
 .CX 528 1552,
 .CX 1552 528,
 .CX 528 1552,
 .CX 787 1553,
 .CX 1553 787
]
def block32 : Program := [
 .CX 787 1553,
 .CX 788 1554,
 .CX 1554 788,
 .CX 788 1554,
 .X 527,
 .CX 526 527,
 .CX 526 786,
 .measureX 529 [] [],
 .measureX 529 [] []
]
def candidate : Program := block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20 ++ block21 ++ block22 ++ block23 ++ block24 ++ block25 ++ block26 ++ block27 ++ block28 ++ block29 ++ block30 ++ block31 ++ block32

theorem counts0 : toffoliCount block0=1 ∧ measurementCount block0=0 ∧ Challenge.gateSlots block0=32 := by decide +kernel
theorem support0 : wires block0⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts1 : toffoliCount block1=1 ∧ measurementCount block1=0 ∧ Challenge.gateSlots block1=32 := by decide +kernel
theorem support1 : wires block1⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts2 : toffoliCount block2=1 ∧ measurementCount block2=0 ∧ Challenge.gateSlots block2=32 := by decide +kernel
theorem support2 : wires block2⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts3 : toffoliCount block3=1 ∧ measurementCount block3=0 ∧ Challenge.gateSlots block3=32 := by decide +kernel
theorem support3 : wires block3⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts4 : toffoliCount block4=0 ∧ measurementCount block4=0 ∧ Challenge.gateSlots block4=32 := by decide +kernel
theorem support4 : wires block4⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts5 : toffoliCount block5=1 ∧ measurementCount block5=0 ∧ Challenge.gateSlots block5=32 := by decide +kernel
theorem support5 : wires block5⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts6 : toffoliCount block6=0 ∧ measurementCount block6=0 ∧ Challenge.gateSlots block6=32 := by decide +kernel
theorem support6 : wires block6⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts7 : toffoliCount block7=0 ∧ measurementCount block7=0 ∧ Challenge.gateSlots block7=32 := by decide +kernel
theorem support7 : wires block7⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts8 : toffoliCount block8=1 ∧ measurementCount block8=0 ∧ Challenge.gateSlots block8=32 := by decide +kernel
theorem support8 : wires block8⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts9 : toffoliCount block9=0 ∧ measurementCount block9=0 ∧ Challenge.gateSlots block9=32 := by decide +kernel
theorem support9 : wires block9⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts10 : toffoliCount block10=0 ∧ measurementCount block10=0 ∧ Challenge.gateSlots block10=32 := by decide +kernel
theorem support10 : wires block10⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts11 : toffoliCount block11=1 ∧ measurementCount block11=0 ∧ Challenge.gateSlots block11=32 := by decide +kernel
theorem support11 : wires block11⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts12 : toffoliCount block12=0 ∧ measurementCount block12=0 ∧ Challenge.gateSlots block12=32 := by decide +kernel
theorem support12 : wires block12⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts13 : toffoliCount block13=0 ∧ measurementCount block13=0 ∧ Challenge.gateSlots block13=32 := by decide +kernel
theorem support13 : wires block13⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts14 : toffoliCount block14=1 ∧ measurementCount block14=0 ∧ Challenge.gateSlots block14=32 := by decide +kernel
theorem support14 : wires block14⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts15 : toffoliCount block15=0 ∧ measurementCount block15=0 ∧ Challenge.gateSlots block15=32 := by decide +kernel
theorem support15 : wires block15⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts16 : toffoliCount block16=0 ∧ measurementCount block16=0 ∧ Challenge.gateSlots block16=32 := by decide +kernel
theorem support16 : wires block16⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts17 : toffoliCount block17=1 ∧ measurementCount block17=0 ∧ Challenge.gateSlots block17=32 := by decide +kernel
theorem support17 : wires block17⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts18 : toffoliCount block18=0 ∧ measurementCount block18=0 ∧ Challenge.gateSlots block18=32 := by decide +kernel
theorem support18 : wires block18⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts19 : toffoliCount block19=0 ∧ measurementCount block19=0 ∧ Challenge.gateSlots block19=32 := by decide +kernel
theorem support19 : wires block19⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts20 : toffoliCount block20=1 ∧ measurementCount block20=0 ∧ Challenge.gateSlots block20=32 := by decide +kernel
theorem support20 : wires block20⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts21 : toffoliCount block21=0 ∧ measurementCount block21=0 ∧ Challenge.gateSlots block21=32 := by decide +kernel
theorem support21 : wires block21⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts22 : toffoliCount block22=0 ∧ measurementCount block22=0 ∧ Challenge.gateSlots block22=32 := by decide +kernel
theorem support22 : wires block22⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts23 : toffoliCount block23=0 ∧ measurementCount block23=0 ∧ Challenge.gateSlots block23=32 := by decide +kernel
theorem support23 : wires block23⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts24 : toffoliCount block24=1 ∧ measurementCount block24=0 ∧ Challenge.gateSlots block24=32 := by decide +kernel
theorem support24 : wires block24⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts25 : toffoliCount block25=0 ∧ measurementCount block25=0 ∧ Challenge.gateSlots block25=32 := by decide +kernel
theorem support25 : wires block25⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts26 : toffoliCount block26=0 ∧ measurementCount block26=0 ∧ Challenge.gateSlots block26=32 := by decide +kernel
theorem support26 : wires block26⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts27 : toffoliCount block27=0 ∧ measurementCount block27=0 ∧ Challenge.gateSlots block27=32 := by decide +kernel
theorem support27 : wires block27⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts28 : toffoliCount block28=0 ∧ measurementCount block28=0 ∧ Challenge.gateSlots block28=32 := by decide +kernel
theorem support28 : wires block28⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts29 : toffoliCount block29=0 ∧ measurementCount block29=0 ∧ Challenge.gateSlots block29=32 := by decide +kernel
theorem support29 : wires block29⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts30 : toffoliCount block30=0 ∧ measurementCount block30=0 ∧ Challenge.gateSlots block30=32 := by decide +kernel
theorem support30 : wires block30⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts31 : toffoliCount block31=0 ∧ measurementCount block31=12 ∧ Challenge.gateSlots block31=210 := by decide +kernel
theorem support31 : wires block31⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem counts32 : toffoliCount block32=0 ∧ measurementCount block32=2 ∧ Challenge.gateSlots block32=9 := by decide +kernel
theorem support32 : wires block32⊆MorningFour.sites.toFinset.erase 1559 := by decide +kernel
theorem resources : toffoliCount candidate=11 ∧ measurementCount candidate=14 ∧ Challenge.gateSlots candidate=1211 := by
 simp only [candidate,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,counts0.1,counts0.2.1,counts0.2.2,counts1.1,counts1.2.1,counts1.2.2,counts2.1,counts2.2.1,counts2.2.2,counts3.1,counts3.2.1,counts3.2.2,counts4.1,counts4.2.1,counts4.2.2,counts5.1,counts5.2.1,counts5.2.2,counts6.1,counts6.2.1,counts6.2.2,counts7.1,counts7.2.1,counts7.2.2,counts8.1,counts8.2.1,counts8.2.2,counts9.1,counts9.2.1,counts9.2.2,counts10.1,counts10.2.1,counts10.2.2,counts11.1,counts11.2.1,counts11.2.2,counts12.1,counts12.2.1,counts12.2.2,counts13.1,counts13.2.1,counts13.2.2,counts14.1,counts14.2.1,counts14.2.2,counts15.1,counts15.2.1,counts15.2.2,counts16.1,counts16.2.1,counts16.2.2,counts17.1,counts17.2.1,counts17.2.2,counts18.1,counts18.2.1,counts18.2.2,counts19.1,counts19.2.1,counts19.2.2,counts20.1,counts20.2.1,counts20.2.2,counts21.1,counts21.2.1,counts21.2.2,counts22.1,counts22.2.1,counts22.2.2,counts23.1,counts23.2.1,counts23.2.2,counts24.1,counts24.2.1,counts24.2.2,counts25.1,counts25.2.1,counts25.2.2,counts26.1,counts26.2.1,counts26.2.2,counts27.1,counts27.2.1,counts27.2.2,counts28.1,counts28.2.1,counts28.2.2,counts29.1,counts29.2.1,counts29.2.2,counts30.1,counts30.2.1,counts30.2.2,counts31.1,counts31.2.1,counts31.2.2,counts32.1,counts32.2.1,counts32.2.2]

 decide +kernel

theorem support : wires candidate⊆MorningFour.sites.toFinset.erase 1559 := by
 simp only [candidate,wires_append,Finset.union_subset_iff]
 exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨support0,support1⟩,support2⟩,support3⟩,support4⟩,support5⟩,support6⟩,support7⟩,support8⟩,support9⟩,support10⟩,support11⟩,support12⟩,support13⟩,support14⟩,support15⟩,support16⟩,support17⟩,support18⟩,support19⟩,support20⟩,support21⟩,support22⟩,support23⟩,support24⟩,support25⟩,support26⟩,support27⟩,support28⟩,support29⟩,support30⟩,support31⟩,support32⟩
theorem support_all : wires candidate⊆MorningFour.sites.toFinset := support.trans (Finset.erase_subset _ _)
def physB : Instr → Bool
 | .X _=>true
 | .CX a t=>decide (a≠t)
 | .CCX a b t=>decide (a≠t ∧ b≠t)
 | .measureX _ _ _=>true
theorem physical_of_all (P : Program) (h : P.all physB=true) : GatePhysical P := by
 intro i hi
 have v:=List.all_eq_true.mp h i hi
 cases i <;> simp_all [physB,RecordedQuantum.PhysicalInstr,ProperGate]





































end ECDSAAdd.Entrant.Forward11Width

section -- compact forward proof scope

-- Verified CompactCertificates
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.CompactCertificates
open Arithmetic MappedCompressed

def lastValue (b : Nat) : List Nat → Nat
 | []=>b
 | c::cs=>lastValue c cs

def checkTrace : List Program → List Nat → Bool
 | [],[_]=>true
 | P::Ps,b::c::cs=>(phaseClean508 P b == some c) && checkTrace Ps (c::cs)
 | _,_=>false

theorem checked_run (P : Program) (b c : Nat) (h : phaseClean508 P b=some c) (m : List Bool) :
 run P m ⟨false,tbN_t8 b⟩=⟨false,tbN_t8 c⟩ := by
 rw [run_sim_t8,phaseClean508_sound P b c h m]

theorem trace_sound (Ps : List Program) (b : Nat) (rs : List Nat)
 (h : checkTrace Ps (b::rs)=true) (m : List Bool) :
 run Ps.flatten m ⟨false,tbN_t8 b⟩=⟨false,tbN_t8 (lastValue b rs)⟩ := by
 induction Ps generalizing b rs m with
 | nil=>
   cases rs with
   | nil=>rfl
   | cons c cs=>simp [checkTrace] at h
 | cons P Ps ih=>
   cases rs with
   | nil=>simp [checkTrace] at h
   | cons c cs=>
     simp only [checkTrace,Bool.and_eq_true,beq_iff_eq] at h
     rw [List.flatten_cons,run_append,checked_run P b c h.1]
     exact ih c cs h.2 _

theorem pull_injective (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
 intro s t h
 apply State.extensionality
 · simpa only [pullState] using congrArg (fun x : State=>x.phase) h
 · funext q
   have v:=congrArg (fun x : State=>x.basis (e.symm q)) h
   simpa only [pullState,Equiv.apply_symm_apply] using v

theorem pull_cancel (e : Equiv.Perm Wire) (s : State) :
 pullState e (pullState e.symm s)=s := by
 apply State.extensionality
 · rfl
 · funext q
   simp only [pullState,Equiv.symm_apply_apply]

theorem run_push (e : Equiv.Perm Wire) (P : Program) (m : List Bool) (s : State) :
 run (renameProgram e P) m (pullState e.symm s)=pullState e.symm (run P m s) := by
 apply pull_injective e
 rw [ECDSAAdd.run_rename e e.injective,pull_cancel,pull_cancel]

theorem rename_id (P : Program) : renameProgram (fun q=>q) P=P := by
 have hc : renameCorrection (fun q=>q)=(id : Correction→Correction) := by
  funext c
  cases c <;> rfl
 have hi : renameInstr (fun q=>q)=(id : Instr→Instr) := by
  funext i
  cases i <;> simp only [renameInstr,hc,List.map_id,id_eq]
 unfold renameProgram
 rw [hi,List.map_id]

theorem rename_inverse (e : Equiv.Perm Wire) (P : Program) :
 renameProgram e (renameProgram e.symm P)=P := by
 rw [renameProgram_comp]
 have h : (e ∘ e.symm : Wire→Wire)=(fun q=>q) := by funext q;exact e.apply_symm_apply q
 rw [h,rename_id]

theorem rename_flatten (f : Wire→Wire) (Ps : List Program) :
 renameProgram f Ps.flatten=(Ps.map (renameProgram f)).flatten := by
 induction Ps with
 | nil=>rfl
 | cons P Ps ih=>simp only [List.flatten_cons,List.map_cons,renameProgram,List.map_append] at ih ⊢;rw [ih]
end ECDSAAdd.Entrant.CompactCertificates

-- Verified CompactForward11
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.CompactForward11
open Arithmetic MappedCompressed Secp256k1 History5 CompactCertificates
def perm : Equiv.Perm Wire := Equiv.swap (0:Wire) 522 * Equiv.swap (1:Wire) 523 * Equiv.swap (2:Wire) 524 * Equiv.swap (3:Wire) 525 * Equiv.swap (4:Wire) 526 * Equiv.swap (5:Wire) 527 * Equiv.swap (6:Wire) 528 * Equiv.swap (7:Wire) 529 * Equiv.swap (8:Wire) 786 * Equiv.swap (9:Wire) 787 * Equiv.swap (10:Wire) 788 * Equiv.swap (11:Wire) 789 * Equiv.swap (12:Wire) 790 * Equiv.swap (13:Wire) 791 * Equiv.swap (14:Wire) 1551 * Equiv.swap (15:Wire) 1552 * Equiv.swap (16:Wire) 1553 * Equiv.swap (17:Wire) 1554 * Equiv.swap (18:Wire) 1556 * Equiv.swap (19:Wire) 1557 * Equiv.swap (20:Wire) 1558 * Equiv.swap (21:Wire) 1559
def block0 : Program := [
 .X 8,
 .CX 1 8,
 .CX 9 6,
 .CX 6 9,
 .CX 6 5,
 .CX 5 6,
 .CX 4 5,
 .CX 5 4,
 .CX 4 5,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 2 13,
 .CX 2 12,
 .CX 2 11,
 .CX 2 10,
 .CX 2 9,
 .CX 2 6,
 .CX 2 5,
 .CX 2 4,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 3,
 .CX 3 0,
 .CX 0 3,
 .CCX 0 1 2,
 .CX 10 9,
 .CX 9 10,
 .CX 9 6,
 .CX 6 9
]
theorem placement0 : renameProgram perm block0=Forward11Width.block0 := by decide +kernel
def block1 : Program := [
 .CX 6 1,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 4 13,
 .CX 4 12,
 .CX 4 11,
 .CX 4 10,
 .CX 4 9,
 .CX 4 6,
 .CX 4 5,
 .CX 4 1,
 .CX 3 5,
 .CX 5 3,
 .CX 3 5,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 3,
 .CX 0 1,
 .X 1,
 .CCX 0 1 2,
 .X 1,
 .CX 11 6,
 .CX 10 11,
 .CX 11 10,
 .CX 10 11,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 6 9,
 .CX 6 3
]
theorem placement1 : renameProgram perm block1=Forward11Width.block1 := by decide +kernel
def block2 : Program := [
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 4 5,
 .CX 5 4,
 .CX 4 5,
 .CX 3 4,
 .CX 3 1,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 2,
 .CX 0 1,
 .CCX 0 1 7,
 .CX 0 1,
 .CX 1 2,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 3 1,
 .CX 3 4,
 .CX 4 5,
 .CX 5 4,
 .CX 4 5,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 6 3,
 .CX 6 9,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10
]
theorem placement2 : renameProgram perm block2=Forward11Width.block2 := by decide +kernel
def block3 : Program := [
 .CX 10 11,
 .CX 11 10,
 .CX 10 11,
 .CX 11 6,
 .CX 12 10,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 10 11,
 .CX 10 3,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 6 9,
 .CX 9 6,
 .CX 6 9,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 3 5,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 8,
 .CX 0 2,
 .CX 2 0
]
theorem placement3 : renameProgram perm block3=Forward11Width.block3 := by decide +kernel
def block4 : Program := [
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 3 5,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 6 9,
 .CX 9 6,
 .CX 6 9,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 10 3,
 .CX 10 11,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 12 10,
 .CX 8 4,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 13 7,
 .CX 7 13,
 .CX 13 7,
 .CX 12 10,
 .CX 11 13
]
theorem placement4 : renameProgram perm block4=Forward11Width.block4 := by decide +kernel
def block5 : Program := [
 .CX 13 11,
 .CX 11 13,
 .CX 10 12,
 .CX 10 11,
 .CX 11 10,
 .CX 10 11,
 .CX 9 11,
 .CX 11 9,
 .CX 9 11,
 .CX 6 10,
 .CX 10 6,
 .CX 6 10,
 .CX 5 9,
 .CX 9 5,
 .CX 5 9,
 .CX 4 6,
 .CX 4 2,
 .CX 3 5,
 .CX 5 3,
 .CX 3 5,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 14,
 .CX 0 2
]
theorem placement5 : renameProgram perm block5=Forward11Width.block5 := by decide +kernel
def block6 : Program := [
 .CX 2 0,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 3 5,
 .CX 5 3,
 .CX 3 5,
 .CX 4 2,
 .CX 4 6,
 .CX 5 9,
 .CX 9 5,
 .CX 5 9,
 .CX 6 10,
 .CX 10 6,
 .CX 6 10,
 .CX 9 11,
 .CX 11 9,
 .CX 9 11,
 .CX 10 11,
 .CX 11 10,
 .CX 10 11,
 .CX 10 12,
 .CX 11 13,
 .CX 13 11,
 .CX 11 13,
 .CX 12 10,
 .CX 13 7
]
theorem placement6 : renameProgram perm block6=Forward11Width.block6 := by decide +kernel
def block7 : Program := [
 .CX 7 13,
 .CX 13 7,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 8 4,
 .CX 14 12,
 .CX 8 2,
 .CX 7 14,
 .CX 14 7,
 .CX 7 14,
 .CX 13 8,
 .CX 8 13,
 .CX 13 8,
 .CX 12 7,
 .CX 12 10,
 .CX 11 13,
 .CX 13 11,
 .CX 11 13,
 .CX 10 12,
 .CX 10 4,
 .CX 9 11,
 .CX 11 9,
 .CX 9 11,
 .CX 6 10,
 .CX 10 6,
 .CX 6 10,
 .CX 5 9,
 .CX 9 5,
 .CX 5 9,
 .CX 4 6,
 .CX 4 3
]
theorem placement7 : renameProgram perm block7=Forward11Width.block7 := by decide +kernel
def block8 : Program := [
 .CX 4 5,
 .CX 5 4,
 .CX 4 5,
 .CX 3 5,
 .CX 2 4,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 15,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 4,
 .CX 3 5,
 .CX 4 5,
 .CX 5 4,
 .CX 4 5,
 .CX 4 3,
 .CX 4 6,
 .CX 5 9,
 .CX 9 5,
 .CX 5 9,
 .CX 6 10,
 .CX 10 6,
 .CX 6 10,
 .CX 9 11
]
theorem placement8 : renameProgram perm block8=Forward11Width.block8 := by decide +kernel
def block9 : Program := [
 .CX 11 9,
 .CX 9 11,
 .CX 10 4,
 .CX 10 12,
 .CX 11 13,
 .CX 13 11,
 .CX 11 13,
 .CX 12 10,
 .CX 12 7,
 .CX 13 8,
 .CX 8 13,
 .CX 13 8,
 .CX 7 14,
 .CX 14 7,
 .CX 7 14,
 .CX 8 2,
 .CX 14 12,
 .CX 15 14,
 .CX 14 15,
 .CX 14 1,
 .CX 8 14,
 .CX 14 8,
 .CX 8 14,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 13 12,
 .CX 13 7,
 .CX 7 13,
 .CX 13 7,
 .CX 12 7,
 .CX 12 10
]
theorem placement9 : renameProgram perm block9=Forward11Width.block9 := by decide +kernel
def block10 : Program := [
 .CX 11 13,
 .CX 13 11,
 .CX 11 13,
 .CX 10 12,
 .CX 10 9,
 .CX 10 11,
 .CX 11 10,
 .CX 10 11,
 .CX 9 11,
 .CX 9 4,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 6 10,
 .CX 10 6,
 .CX 6 10,
 .CX 5 9,
 .CX 9 5,
 .CX 5 9,
 .CX 4 6,
 .CX 3 5,
 .CX 5 3,
 .CX 3 5,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 3,
 .CX 1 0,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 0 2
]
theorem placement10 : renameProgram perm block10=Forward11Width.block10 := by decide +kernel
def block11 : Program := [
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CCX 0 1 16,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CX 0 2,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 1 0,
 .CX 1 3,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 3 5,
 .CX 5 3,
 .CX 3 5,
 .CX 4 6,
 .CX 5 9,
 .CX 9 5,
 .CX 5 9,
 .CX 6 10,
 .CX 10 6,
 .CX 6 10,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 9 4,
 .CX 9 11,
 .CX 10 11
]
theorem placement11 : renameProgram perm block11=Forward11Width.block11 := by decide +kernel
def block12 : Program := [
 .CX 11 10,
 .CX 10 11,
 .CX 10 9,
 .CX 10 12,
 .CX 11 13,
 .CX 13 11,
 .CX 11 13,
 .CX 12 10,
 .CX 12 7,
 .CX 13 7,
 .CX 7 13,
 .CX 13 7,
 .CX 13 12,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 8 14,
 .CX 14 8,
 .CX 8 14,
 .CX 14 1,
 .CX 14 15,
 .CX 15 14,
 .CX 16 15,
 .CX 15 16,
 .CX 15 14,
 .CX 14 15,
 .CX 14 7,
 .CX 8 14,
 .CX 8 7,
 .CX 8 6,
 .CX 7 14,
 .CX 7 12
]
theorem placement12 : renameProgram perm block12=Forward11Width.block12 := by decide +kernel
def block13 : Program := [
 .CX 13 8,
 .CX 8 13,
 .CX 13 8,
 .CX 12 7,
 .CX 12 11,
 .CX 12 13,
 .CX 13 12,
 .CX 12 13,
 .CX 11 13,
 .CX 11 12,
 .CX 11 9,
 .CX 11 6,
 .CX 10 12,
 .CX 12 10,
 .CX 10 12,
 .CX 9 11,
 .CX 9 10,
 .CX 9 6,
 .CX 9 4,
 .CX 6 10,
 .CX 6 5,
 .CX 6 9,
 .CX 9 6,
 .CX 6 9,
 .CX 5 9,
 .CX 5 2,
 .CX 4 6,
 .CX 4 5,
 .CX 5 4,
 .CX 4 5,
 .CX 3 5,
 .CX 5 3
]
theorem placement13 : renameProgram perm block13=Forward11Width.block13 := by decide +kernel
def block14 : Program := [
 .CX 3 5,
 .CX 2 4,
 .CX 2 0,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 0 1,
 .CCX 0 1 17,
 .CX 0 1,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 0,
 .CX 2 4,
 .CX 3 5,
 .CX 5 3,
 .CX 3 5,
 .CX 4 5,
 .CX 5 4,
 .CX 4 5,
 .CX 4 6,
 .CX 5 2,
 .CX 5 9,
 .CX 6 9,
 .CX 9 6,
 .CX 6 9,
 .CX 6 5,
 .CX 6 10,
 .CX 9 4,
 .CX 9 6
]
theorem placement14 : renameProgram perm block14=Forward11Width.block14 := by decide +kernel
def block15 : Program := [
 .CX 9 10,
 .CX 9 11,
 .CX 10 12,
 .CX 12 10,
 .CX 10 12,
 .CX 11 6,
 .CX 11 9,
 .CX 11 12,
 .CX 11 13,
 .CX 12 13,
 .CX 13 12,
 .CX 12 13,
 .CX 12 11,
 .CX 12 7,
 .CX 13 8,
 .CX 8 13,
 .CX 13 8,
 .CX 7 12,
 .CX 7 14,
 .CX 8 6,
 .CX 8 7,
 .CX 8 14,
 .CX 14 7,
 .CX 14 15,
 .CX 15 14,
 .CX 15 16,
 .CX 16 15,
 .CX 17 16,
 .CX 16 17,
 .CX 16 15,
 .CX 15 16,
 .CX 15 14
]
theorem placement15 : renameProgram perm block15=Forward11Width.block15 := by decide +kernel
def block16 : Program := [
 .CX 15 8,
 .CX 14 15,
 .CX 14 8,
 .CX 14 7,
 .CX 8 15,
 .CX 8 14,
 .CX 8 7,
 .CX 8 5,
 .CX 7 14,
 .CX 7 9,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 13 8,
 .CX 8 13,
 .CX 13 8,
 .CX 12 7,
 .CX 7 12,
 .CX 12 7,
 .CX 11 13,
 .CX 13 11,
 .CX 11 13,
 .CX 10 12,
 .CX 12 10,
 .CX 10 12,
 .CX 9 11,
 .CX 9 2,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 6 10,
 .CX 10 6
]
theorem placement16 : renameProgram perm block16=Forward11Width.block16 := by decide +kernel
def block17 : Program := [
 .CX 6 10,
 .CX 5 9,
 .CX 5 6,
 .CX 5 3,
 .CX 5 2,
 .CX 4 6,
 .CX 6 4,
 .CX 4 6,
 .CX 3 5,
 .CX 3 1,
 .CX 2 4,
 .CX 2 0,
 .CX 1 3,
 .CX 1 2,
 .CX 1 0,
 .CX 0 2,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CCX 0 1 18,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CX 0 2,
 .CX 1 0,
 .CX 1 2,
 .CX 1 3,
 .CX 2 0,
 .CX 2 4,
 .CX 3 1,
 .CX 3 5,
 .CX 4 6
]
theorem placement17 : renameProgram perm block17=Forward11Width.block17 := by decide +kernel
def block18 : Program := [
 .CX 6 4,
 .CX 4 6,
 .CX 5 2,
 .CX 5 3,
 .CX 5 6,
 .CX 5 9,
 .CX 6 10,
 .CX 10 6,
 .CX 6 10,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 9 2,
 .CX 9 11,
 .CX 10 12,
 .CX 12 10,
 .CX 10 12,
 .CX 11 13,
 .CX 13 11,
 .CX 11 13,
 .CX 12 7,
 .CX 7 12,
 .CX 12 7,
 .CX 13 8,
 .CX 8 13,
 .CX 13 8,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 7 9,
 .CX 7 14,
 .CX 8 5
]
theorem placement18 : renameProgram perm block18=Forward11Width.block18 := by decide +kernel
def block19 : Program := [
 .CX 8 7,
 .CX 8 14,
 .CX 8 15,
 .CX 14 7,
 .CX 14 8,
 .CX 14 15,
 .CX 15 8,
 .CX 15 14,
 .CX 15 16,
 .CX 16 15,
 .CX 16 17,
 .CX 17 16,
 .CX 17 16,
 .CX 16 17,
 .CX 16 15,
 .CX 15 16,
 .CX 15 8,
 .CX 14 7,
 .CX 8 15,
 .CX 8 5,
 .CX 7 14,
 .CX 7 9,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 13 8,
 .CX 8 13,
 .CX 13 8,
 .CX 12 7,
 .CX 7 12,
 .CX 12 7,
 .CX 11 13
]
theorem placement19 : renameProgram perm block19=Forward11Width.block19 := by decide +kernel
def block20 : Program := [
 .CX 13 11,
 .CX 11 13,
 .CX 10 12,
 .CX 12 10,
 .CX 10 12,
 .CX 9 11,
 .CX 9 4,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 6 10,
 .CX 10 6,
 .CX 6 10,
 .CX 5 9,
 .CX 5 0,
 .CX 4 6,
 .CX 4 2,
 .CX 3 5,
 .CX 5 3,
 .CX 3 5,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CCX 0 1 19
]
theorem placement20 : renameProgram perm block20=Forward11Width.block20 := by decide +kernel
def block21 : Program := [
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 3 5,
 .CX 5 3,
 .CX 3 5,
 .CX 4 2,
 .CX 4 6,
 .CX 5 0,
 .CX 5 9,
 .CX 6 10,
 .CX 10 6,
 .CX 6 10,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 9 4,
 .CX 9 11,
 .CX 10 12,
 .CX 12 10,
 .CX 10 12,
 .CX 11 13,
 .CX 13 11,
 .CX 11 13
]
theorem placement21 : renameProgram perm block21=Forward11Width.block21 := by decide +kernel
def block22 : Program := [
 .CX 12 7,
 .CX 7 12,
 .CX 12 7,
 .CX 13 8,
 .CX 8 13,
 .CX 13 8,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 7 9,
 .CX 7 14,
 .CX 8 5,
 .CX 8 15,
 .CX 14 7,
 .CX 15 8,
 .CX 15 16,
 .CX 16 15,
 .CX 16 17,
 .CX 17 16,
 .CX 19 16,
 .CX 18 19,
 .CX 19 18,
 .CX 18 19,
 .CX 17 18,
 .CX 18 17,
 .CX 17 18,
 .CX 16 17,
 .CX 16 14,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15
]
theorem placement22 : renameProgram perm block22=Forward11Width.block22 := by decide +kernel
def block23 : Program := [
 .CX 14 8,
 .CX 8 14,
 .CX 8 12,
 .CX 7 13,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 13 8,
 .CX 13 7,
 .CX 13 12,
 .CX 13 11,
 .CX 12 7,
 .CX 12 13,
 .CX 12 11,
 .CX 12 10,
 .CX 11 13,
 .CX 11 6,
 .CX 10 12,
 .CX 10 9,
 .CX 10 11,
 .CX 11 10,
 .CX 10 11,
 .CX 9 11,
 .CX 9 10,
 .CX 9 6,
 .CX 6 10,
 .CX 6 5,
 .CX 6 9,
 .CX 9 6,
 .CX 6 9,
 .CX 5 9,
 .CX 5 0
]
theorem placement23 : renameProgram perm block23=Forward11Width.block23 := by decide +kernel
def block24 : Program := [
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 4 6,
 .CX 6 4,
 .CX 4 6,
 .CX 3 5,
 .CX 5 3,
 .CX 3 5,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 0 1,
 .CCX 0 1 20,
 .CX 0 1,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 3 5,
 .CX 5 3,
 .CX 3 5,
 .CX 4 6,
 .CX 6 4,
 .CX 4 6
]
theorem placement24 : renameProgram perm block24=Forward11Width.block24 := by decide +kernel
def block25 : Program := [
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 5 0,
 .CX 5 9,
 .CX 6 9,
 .CX 9 6,
 .CX 6 9,
 .CX 6 5,
 .CX 6 10,
 .CX 9 6,
 .CX 9 10,
 .CX 9 11,
 .CX 10 11,
 .CX 11 10,
 .CX 10 11,
 .CX 10 9,
 .CX 10 12,
 .CX 11 6,
 .CX 11 13,
 .CX 12 10,
 .CX 12 11,
 .CX 12 13,
 .CX 12 7,
 .CX 13 11,
 .CX 13 12,
 .CX 13 7,
 .CX 13 8,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 7 13
]
theorem placement25 : renameProgram perm block25=Forward11Width.block25 := by decide +kernel
def block26 : Program := [
 .CX 8 12,
 .CX 8 14,
 .CX 14 8,
 .CX 14 15,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 16 14,
 .CX 16 17,
 .CX 17 18,
 .CX 18 17,
 .CX 17 18,
 .CX 18 19,
 .CX 19 18,
 .CX 18 19,
 .CX 19 16,
 .CX 20 18,
 .CX 20 17,
 .CX 20 12,
 .CX 20 9,
 .CX 20 3,
 .CX 19 12,
 .CX 18 20,
 .CX 18 19,
 .CX 18 13,
 .CX 18 10,
 .CX 18 3,
 .CX 17 7,
 .CX 17 11,
 .CX 17 6,
 .CX 17 18,
 .CX 18 17
]
theorem placement26 : renameProgram perm block26=Forward11Width.block26 := by decide +kernel
def block27 : Program := [
 .CX 17 18,
 .CX 16 7,
 .CX 16 11,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 15 19,
 .CX 15 18,
 .CX 15 17,
 .CX 15 16,
 .CX 15 13,
 .CX 15 12,
 .CX 15 10,
 .CX 15 9,
 .CX 15 6,
 .CX 14 16,
 .CX 14 13,
 .CX 14 10,
 .CX 14 9,
 .CX 8 18,
 .CX 8 17,
 .CX 8 16,
 .CX 8 13,
 .CX 8 10,
 .CX 8 9,
 .CX 8 6,
 .CX 8 2,
 .CX 8 1,
 .CX 7 20,
 .CX 7 19,
 .CX 7 18,
 .CX 7 13
]
theorem placement27 : renameProgram perm block27=Forward11Width.block27 := by decide +kernel
def block28 : Program := [
 .CX 7 11,
 .CX 7 9,
 .CX 7 6,
 .CX 7 3,
 .CX 7 14,
 .CX 14 7,
 .CX 7 14,
 .CX 13 18,
 .CX 13 17,
 .CX 13 14,
 .CX 13 6,
 .CX 13 7,
 .CX 7 13,
 .CX 13 7,
 .CX 12 19,
 .CX 12 17,
 .CX 12 11,
 .CX 12 14,
 .CX 14 12,
 .CX 12 14,
 .CX 11 20,
 .CX 11 19,
 .CX 11 18,
 .CX 11 16,
 .CX 11 14,
 .CX 11 7,
 .CX 11 10,
 .CX 11 6,
 .CX 11 3,
 .CX 10 20,
 .CX 10 19,
 .CX 10 18
]
theorem placement28 : renameProgram perm block28=Forward11Width.block28 := by decide +kernel
def block29 : Program := [
 .CX 10 17,
 .CX 10 16,
 .CX 10 7,
 .CX 10 6,
 .CX 10 3,
 .CX 9 20,
 .CX 9 19,
 .CX 9 18,
 .CX 9 17,
 .CX 9 8,
 .CX 9 6,
 .CX 9 4,
 .CX 9 3,
 .CX 9 2,
 .CX 9 1,
 .CX 9 12,
 .CX 12 9,
 .CX 9 12,
 .CX 6 20,
 .CX 6 19,
 .CX 6 18,
 .CX 6 17,
 .CX 6 16,
 .CX 6 7,
 .CX 6 3,
 .CX 6 12,
 .CX 12 6,
 .CX 6 12,
 .CX 5 0,
 .CX 5 11,
 .CX 11 5,
 .CX 5 11
]
theorem placement29 : renameProgram perm block29=Forward11Width.block29 := by decide +kernel
def block30 : Program := [
 .CX 4 20,
 .CX 4 19,
 .CX 4 16,
 .CX 4 8,
 .CX 4 7,
 .CX 4 12,
 .CX 4 9,
 .CX 4 6,
 .CX 4 5,
 .CX 4 3,
 .CX 4 2,
 .CX 4 1,
 .CX 3 20,
 .CX 3 19,
 .CX 3 16,
 .CX 3 12,
 .CX 3 9,
 .CX 3 6,
 .CX 6 3,
 .CX 3 6,
 .CX 2 8,
 .CX 2 7,
 .CX 2 6,
 .CX 2 5,
 .CX 2 1,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 8,
 .CX 1 7,
 .CX 1 11,
 .CX 11 1
]
theorem placement30 : renameProgram perm block30=Forward11Width.block30 := by decide +kernel
def block31 : Program := [
 .CX 1 11,
 .CX 0 10,
 .CX 0 9,
 .CX 0 3,
 .CX 0 2,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .measureX 20 [] [.Z 5, .Z 6, .Z 9, .Z 10, .Z 12, .Z 16, .Z 19, .CZ 0 5, .CZ 0 6, .CZ 0 9, .CZ 0 10, .CZ 0 16, .CZ 0 19],
 .X 19,
 .measureX 19 [] [.Z 0, .Z 5, .Z 10, .Z 12, .Z 7, .Z 8, .Z 14, .Z 15, .Z 17, .CZ 0 1, .CZ 0 2, .CZ 0 5, .CZ 0 6, .CZ 0 9, .CZ 0 10, .CZ 0 12, .CZ 0 8, .CZ 1 3, .CZ 1 4, .CZ 1 12, .CZ 1 14, .CZ 1 17, .CZ 2 11, .CZ 2 13, .CZ 4 5, .CZ 4 17],
 .measureX 18 [] [.Z 1, .Z 2, .Z 11, .Z 12, .Z 8, .Z 14, .Z 16, .Z 17, .CZ 0 5, .CZ 0 6, .CZ 0 9, .CZ 0 10, .CZ 0 17, .CZ 1 17],
 .measureX 17 [] [.Z 1, .Z 3, .Z 4, .Z 11, .Z 8, .Z 14, .CZ 0 1, .CZ 1 3, .CZ 1 11, .CZ 1 12, .CZ 1 13, .CZ 1 15, .CZ 2 3],
 .measureX 16 [] [.Z 0, .Z 2, .Z 11, .Z 12, .Z 8, .CZ 0 5, .CZ 0 6, .CZ 0 9, .CZ 0 10, .CZ 0 12, .CZ 0 8, .CZ 1 12, .CZ 1 8],
 .X 15,
 .measureX 15 [] [.Z 0, .Z 1, .Z 2, .Z 6, .Z 9, .Z 10, .Z 11, .Z 12, .Z 13, .CZ 0 1, .CZ 1 3, .CZ 1 11, .CZ 1 12, .CZ 2 3, .CZ 2 4, .CZ 2 9, .CZ 2 10, .CZ 2 11, .CZ 2 12, .CZ 2 7],
 .measureX 14 [] [.Z 0, .Z 1, .Z 3, .Z 4, .Z 6, .Z 11, .Z 12, .CZ 0 2, .CZ 0 3, .CZ 0 5, .CZ 0 6, .CZ 1 2, .CZ 1 3, .CZ 1 9, .CZ 1 10, .CZ 1 12, .CZ 2 9, .CZ 2 10, .CZ 2 11, .CZ 2 12, .CZ 3 11, .CZ 4 5, .CZ 5 6, .CZ 5 11, .CZ 6 11],
 .X 8,
 .measureX 8 [] [.Z 0, .Z 1, .Z 2, .Z 4, .Z 6, .Z 9, .Z 10, .Z 11, .Z 12, .Z 13, .Z 7, .CZ 0 1, .CZ 1 2, .CZ 1 3, .CZ 1 11, .CZ 2 9, .CZ 2 10, .CZ 2 12],
 .measureX 7 [] [.Z 0, .Z 1, .Z 3, .Z 4, .Z 9, .CZ 1 6, .CZ 1 9, .CZ 1 10, .CZ 3 5, .CZ 3 10, .CZ 4 6, .CZ 4 9],
 .measureX 13 [] [.CZ 1 6, .CZ 1 9, .CZ 1 10, .CZ 3 5, .CZ 3 6, .CZ 3 10],
 .X 12,
 .measureX 12 [] [.Z 1, .Z 10, .CZ 1 6, .CZ 1 9, .CZ 1 10, .CZ 2 5, .CZ 3 6, .CZ 4 9],
 .measureX 11 [] [.Z 0, .Z 1, .Z 2, .Z 3, .Z 9, .CZ 2 5, .CZ 3 5, .CZ 3 6, .CZ 4 6, .CZ 4 9],
 .CX 5 14,
 .CX 14 5,
 .CX 5 14,
 .CX 6 15,
 .CX 15 6,
 .CX 6 15,
 .CX 9 16,
 .CX 16 9
]
theorem placement31 : renameProgram perm block31=Forward11Width.block31 := by decide +kernel
def block32 : Program := [
 .CX 9 16,
 .CX 10 17,
 .CX 17 10,
 .CX 10 17,
 .X 5,
 .CX 4 5,
 .CX 4 8,
 .measureX 7 [] [],
 .measureX 7 [] []
]
theorem placement32 : renameProgram perm block32=Forward11Width.block32 := by decide +kernel
def blocks : List Program := [block0,block1,block2,block3,block4,block5,block6,block7,block8,block9,block10,block11,block12,block13,block14,block15,block16,block17,block18,block19,block20,block21,block22,block23,block24,block25,block26,block27,block28,block29,block30,block31,block32]
def candidate : Program := blocks.flatten
theorem placement : renameProgram perm candidate=Forward11Width.candidate := by
 rw [candidate,rename_flatten]
 simp only [blocks,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,placement0,placement1,placement2,placement3,placement4,placement5,placement6,placement7,placement8,placement9,placement10,placement11,placement12,placement13,placement14,placement15,placement16,placement17,placement18,placement19,placement20,placement21,placement22,placement23,placement24,placement25,placement26,placement27,placement28,placement29,placement30,placement31,placement32,List.append_nil,Forward11Width.candidate,List.append_assoc]
def reference : Program := renameProgram perm.symm MorningFour.forward13
theorem reference_placement : renameProgram perm reference=MorningFour.forward13 := rename_inverse _ _
def trace0 : List Nat := [2, 1, 3, 3, 13, 3, 12, 3, 3, 3, 3, 12, 3, 3, 3, 131075, 49155, 1095, 262231, 278659, 266275, 262156, 266275, 786435, 786435, 1835011, 1835011, 1053195, 1053195, 1773251, 1644029, 3985, 30, 286]
theorem checked0 : checkTrace blocks trace0=true := by decide +kernel
theorem old0 : phaseClean508 reference 2=some 286 := by decide +kernel
theorem row0 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2⟩=run reference n ⟨false,tbN_t8 2⟩ := by
 have h:=trace_sound blocks 2 [1, 3, 3, 13, 3, 12, 3, 3, 3, 3, 12, 3, 3, 3, 131075, 49155, 1095, 262231, 278659, 266275, 262156, 266275, 786435, 786435, 1835011, 1835011, 1053195, 1053195, 1773251, 1644029, 3985, 30, 286] checked0 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old0 n]
 rfl
def trace1 : List Nat := [2, 1, 3, 3, 13, 3, 12, 3, 3, 3, 3, 12, 3, 3, 3, 131075, 49155, 1095, 262231, 278659, 266275, 262156, 266275, 786435, 786435, 1835011, 1835011, 1053195, 1053195, 1773251, 1644029, 3985, 30, 286]
theorem checked1 : checkTrace blocks trace1=true := by decide +kernel
theorem old1 : phaseClean508 reference 2=some 286 := by decide +kernel
theorem row1 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2⟩=run reference n ⟨false,tbN_t8 2⟩ := by
 have h:=trace_sound blocks 2 [1, 3, 3, 13, 3, 12, 3, 3, 3, 3, 12, 3, 3, 3, 131075, 49155, 1095, 262231, 278659, 266275, 262156, 266275, 786435, 786435, 1835011, 1835011, 1053195, 1053195, 1773251, 1644029, 3985, 30, 286] checked1 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old1 n]
 rfl
def trace2 : List Nat := [257, 8, 32, 32, 64, 32, 512, 32, 512, 32, 32, 512, 32, 32, 532, 131104, 49184, 1124, 262696, 278688, 266240, 262656, 266240, 786464, 786977, 1835585, 1835040, 1053224, 1053224, 1773280, 1646079, 3603, 31, 287]
theorem checked2 : checkTrace blocks trace2=true := by decide +kernel
theorem old2 : phaseClean508 reference 257=some 287 := by decide +kernel
theorem row2 (m n : List Bool) : run candidate m ⟨false,tbN_t8 257⟩=run reference n ⟨false,tbN_t8 257⟩ := by
 have h:=trace_sound blocks 257 [8, 32, 32, 64, 32, 512, 32, 512, 32, 32, 512, 32, 32, 532, 131104, 49184, 1124, 262696, 278688, 266240, 262656, 266240, 786464, 786977, 1835585, 1835040, 1053224, 1053224, 1773280, 1646079, 3603, 31, 287] checked2 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old2 n]
 rfl
def trace3 : List Nat := [257, 8, 32, 32, 64, 32, 512, 32, 512, 32, 32, 512, 32, 32, 532, 131104, 49184, 1124, 262696, 278688, 266240, 262656, 266240, 786464, 786977, 1835585, 1835040, 1053224, 1053224, 1773280, 1646079, 3603, 31, 287]
theorem checked3 : checkTrace blocks trace3=true := by decide +kernel
theorem old3 : phaseClean508 reference 257=some 287 := by decide +kernel
theorem row3 (m n : List Bool) : run candidate m ⟨false,tbN_t8 257⟩=run reference n ⟨false,tbN_t8 257⟩ := by
 have h:=trace_sound blocks 257 [8, 32, 32, 64, 32, 512, 32, 512, 32, 32, 512, 32, 32, 532, 131104, 49184, 1124, 262696, 278688, 266240, 262656, 266240, 786464, 786977, 1835585, 1835040, 1053224, 1053224, 1773280, 1646079, 3603, 31, 287] checked3 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old3 n]
 rfl
def trace4 : List Nat := [260, 15990, 30, 30, 318, 8206, 122, 8334, 114, 2586, 16414, 16507, 81950, 350, 90, 1118, 180510, 164414, 426034, 426270, 426014, 426104, 426014, 672030, 671774, 671774, 671774, 2041110, 11216, 393688, 1642768, 1642780, 28, 284]
theorem checked4 : checkTrace blocks trace4=true := by decide +kernel
theorem old4 : phaseClean508 reference 260=some 284 := by decide +kernel
theorem row4 (m n : List Bool) : run candidate m ⟨false,tbN_t8 260⟩=run reference n ⟨false,tbN_t8 260⟩ := by
 have h:=trace_sound blocks 260 [15990, 30, 30, 318, 8206, 122, 8334, 114, 2586, 16414, 16507, 81950, 350, 90, 1118, 180510, 164414, 426034, 426270, 426014, 426104, 426014, 672030, 671774, 671774, 671774, 2041110, 11216, 393688, 1642768, 1642780, 28, 284] checked4 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old4 n]
 rfl
def trace5 : List Nat := [16132, 1588, 12382, 13398, 12574, 7302, 24799, 30726, 8698, 11154, 59540, 57562, 60564, 47446, 41466, 42454, 30998, 42450, 303506, 325782, 302006, 827867, 834486, 571670, 582102, 582070, 583958, 1461534, 1527128, 682384, 680368, 680380, 16412, 16668]
theorem checked5 : checkTrace blocks trace5=true := by decide +kernel
theorem old5 : phaseClean508 reference 16132=some 16668 := by decide +kernel
theorem row5 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16132⟩=run reference n ⟨false,tbN_t8 16132⟩ := by
 have h:=trace_sound blocks 16132 [1588, 12382, 13398, 12574, 7302, 24799, 30726, 8698, 11154, 59540, 57562, 60564, 47446, 41466, 42454, 30998, 42450, 303506, 325782, 302006, 827867, 834486, 571670, 582102, 582070, 583958, 1461534, 1527128, 682384, 680368, 680380, 16412, 16668] checked5 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old5 n]
 rfl
def trace6 : List Nat := [515, 15, 61, 61, 371, 8237, 630, 8365, 625, 2617, 16445, 17015, 81981, 381, 589, 1149, 180541, 164381, 426573, 426301, 426045, 426612, 426045, 672061, 672316, 672348, 671805, 2041141, 11251, 393723, 1644818, 1642654, 29, 285]
theorem checked6 : checkTrace blocks trace6=true := by decide +kernel
theorem old6 : phaseClean508 reference 515=some 285 := by decide +kernel
theorem row6 (m n : List Bool) : run candidate m ⟨false,tbN_t8 515⟩=run reference n ⟨false,tbN_t8 515⟩ := by
 have h:=trace_sound blocks 515 [15, 61, 61, 371, 8237, 630, 8365, 625, 2617, 16445, 17015, 81981, 381, 589, 1149, 180541, 164381, 426573, 426301, 426045, 426612, 426045, 672061, 672316, 672348, 671805, 2041141, 11251, 393723, 1644818, 1642654, 29, 285] checked6 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old6 n]
 rfl
def trace7 : List Nat := [639, 14413, 12413, 13429, 12627, 7333, 25299, 30757, 9209, 11185, 59575, 58070, 60599, 47477, 41965, 42485, 31029, 42481, 304109, 325813, 301973, 828375, 834453, 571701, 582644, 582644, 583989, 1461565, 1527163, 682419, 682418, 679998, 16413, 16669]
theorem checked7 : checkTrace blocks trace7=true := by decide +kernel
theorem old7 : phaseClean508 reference 639=some 16669 := by decide +kernel
theorem row7 (m n : List Bool) : run candidate m ⟨false,tbN_t8 639⟩=run reference n ⟨false,tbN_t8 639⟩ := by
 have h:=trace_sound blocks 639 [14413, 12413, 13429, 12627, 7333, 25299, 30757, 9209, 11185, 59575, 58070, 60599, 47477, 41965, 42485, 31029, 42481, 304109, 325813, 301973, 828375, 834453, 571701, 582644, 582644, 583989, 1461565, 1527163, 682419, 682418, 679998, 16413, 16669] checked7 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old7 n]
 rfl
def trace8 : List Nat := [518, 15989, 23, 23, 25, 23, 92, 23, 95, 32791, 8213, 95, 68629, 65559, 65647, 65559, 196631, 196631, 458823, 458775, 458775, 458846, 458775, 737303, 720983, 720951, 725271, 2073631, 572127, 363551, 1676351, 34709, 26, 282]
theorem checked8 : checkTrace blocks trace8=true := by decide +kernel
theorem old8 : phaseClean508 reference 518=some 282 := by decide +kernel
theorem row8 (m n : List Bool) : run candidate m ⟨false,tbN_t8 518⟩=run reference n ⟨false,tbN_t8 518⟩ := by
 have h:=trace_sound blocks 518 [15989, 23, 23, 25, 23, 92, 23, 95, 32791, 8213, 95, 68629, 65559, 65647, 65559, 196631, 196631, 458823, 458775, 458775, 458846, 458775, 737303, 720983, 720951, 725271, 2073631, 572127, 363551, 1676351, 34709, 26, 282] checked8 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old8 n]
 rfl
def trace9 : List Nat := [15878, 1589, 12377, 13393, 12547, 7297, 8385, 14337, 8677, 12165, 18577, 24775, 90257, 14673, 8701, 9681, 194833, 172977, 434621, 440593, 436625, 958919, 952721, 669969, 680401, 680369, 682257, 1510681, 525279, 613855, 673591, 673493, 32794, 33050]
theorem checked9 : checkTrace blocks trace9=true := by decide +kernel
theorem old9 : phaseClean508 reference 15878=some 33050 := by decide +kernel
theorem row9 (m n : List Bool) : run candidate m ⟨false,tbN_t8 15878⟩=run reference n ⟨false,tbN_t8 15878⟩ := by
 have h:=trace_sound blocks 15878 [1589, 12377, 13393, 12547, 7297, 8385, 14337, 8677, 12165, 18577, 24775, 90257, 14673, 8701, 9681, 194833, 172977, 434621, 440593, 436625, 958919, 952721, 669969, 680401, 680369, 682257, 1510681, 525279, 613855, 673591, 673493, 32794, 33050] checked9 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old9 n]
 rfl
def trace10 : List Nat := [773, 15996, 52, 52, 84, 52, 592, 52, 604, 32820, 8246, 595, 68662, 65588, 66168, 65588, 196660, 196660, 459320, 458804, 458804, 459346, 458804, 737332, 721525, 721525, 725300, 2073660, 572156, 363580, 1678397, 34327, 27, 283]
theorem checked10 : checkTrace blocks trace10=true := by decide +kernel
theorem old10 : phaseClean508 reference 773=some 283 := by decide +kernel
theorem row10 (m n : List Bool) : run candidate m ⟨false,tbN_t8 773⟩=run reference n ⟨false,tbN_t8 773⟩ := by
 have h:=trace_sound blocks 773 [15996, 52, 52, 84, 52, 592, 52, 604, 32820, 8246, 595, 68662, 65588, 66168, 65588, 196660, 196660, 459320, 458804, 458804, 459346, 458804, 737332, 721525, 721525, 725300, 2073660, 572156, 363580, 1678397, 34327, 27, 283] checked10 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old10 n]
 rfl
def trace11 : List Nat := [893, 14412, 12410, 13426, 12622, 7330, 8909, 14370, 9190, 12198, 18610, 25291, 90290, 14706, 9194, 9714, 194866, 172946, 435138, 440626, 436658, 959435, 952754, 670002, 680947, 680947, 682290, 1510714, 525308, 613884, 675637, 673623, 32795, 33051]
theorem checked11 : checkTrace blocks trace11=true := by decide +kernel
theorem old11 : phaseClean508 reference 893=some 33051 := by decide +kernel
theorem row11 (m n : List Bool) : run candidate m ⟨false,tbN_t8 893⟩=run reference n ⟨false,tbN_t8 893⟩ := by
 have h:=trace_sound blocks 893 [14412, 12410, 13426, 12622, 7330, 8909, 14370, 9190, 12198, 18610, 25291, 90290, 14706, 9194, 9714, 194866, 172946, 435138, 440626, 436658, 959435, 952754, 670002, 680947, 680947, 682290, 1510714, 525308, 613884, 675637, 673623, 32795, 33051] checked11 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old11 n]
 rfl
def trace12 : List Nat := [776, 18, 15884, 15884, 15922, 15052, 15538, 7884, 15756, 47564, 11982, 15537, 13518, 77516, 81316, 212364, 81484, 80328, 343512, 343628, 339916, 343472, 331724, 867916, 867757, 1916365, 1916492, 1092676, 2071044, 1425924, 1364434, 1366040, 24, 280]
theorem checked12 : checkTrace blocks trace12=true := by decide +kernel
theorem old12 : phaseClean508 reference 776=some 280 := by decide +kernel
theorem row12 (m n : List Bool) : run candidate m ⟨false,tbN_t8 776⟩=run reference n ⟨false,tbN_t8 776⟩ := by
 have h:=trace_sound blocks 776 [18, 15884, 15884, 15922, 15052, 15538, 7884, 15756, 47564, 11982, 15537, 13518, 77516, 81316, 212364, 81484, 80328, 343512, 343628, 339916, 343472, 331724, 867916, 867757, 1916365, 1916492, 1092676, 2071044, 1425924, 1364434, 1366040, 24, 280] checked12 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old12 n]
 rfl
def trace13 : List Nat := [15624, 14416, 3660, 2628, 3602, 1604, 23575, 17988, 7172, 6212, 42566, 39953, 37958, 38596, 39940, 171012, 34372, 7716, 269432, 280516, 275556, 793619, 799844, 820804, 826405, 1875013, 1869380, 1590348, 1663564, 2044556, 1979226, 469208, 32792, 33048]
theorem checked13 : checkTrace blocks trace13=true := by decide +kernel
theorem old13 : phaseClean508 reference 15624=some 33048 := by decide +kernel
theorem row13 (m n : List Bool) : run candidate m ⟨false,tbN_t8 15624⟩=run reference n ⟨false,tbN_t8 15624⟩ := by
 have h:=trace_sound blocks 15624 [14416, 3660, 2628, 3602, 1604, 23575, 17988, 7172, 6212, 42566, 39953, 37958, 38596, 39940, 171012, 34372, 7716, 269432, 280516, 275556, 793619, 799844, 820804, 826405, 1875013, 1869380, 1590348, 1663564, 2044556, 1979226, 469208, 32792, 33048] checked13 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old13 n]
 rfl
def trace14 : List Nat := [1031, 15931, 47, 175, 255, 303, 830, 303, 16911, 49199, 8493, 829, 3373, 81967, 82483, 213039, 65711, 83051, 344615, 327855, 352815, 344636, 352815, 852143, 852559, 852527, 852143, 1748071, 1219111, 1622567, 1694160, 1694106, 25, 281]
theorem checked14 : checkTrace blocks trace14=true := by decide +kernel
theorem old14 : phaseClean508 reference 1031=some 281 := by decide +kernel
theorem row14 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1031⟩=run reference n ⟨false,tbN_t8 1031⟩ := by
 have h:=trace_sound blocks 1031 [15931, 47, 175, 255, 303, 830, 303, 16911, 49199, 8493, 829, 3373, 81967, 82483, 213039, 65711, 83051, 344615, 327855, 352815, 344636, 352815, 852143, 852559, 852527, 852143, 1748071, 1219111, 1622567, 1694160, 1694106, 25, 281] checked14 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old14 n]
 rfl
def trace15 : List Nat := [1147, 1657, 12399, 13543, 12511, 15783, 25499, 22951, 25479, 24999, 43429, 41885, 44453, 63527, 58259, 188839, 47271, 25479, 287623, 293159, 293255, 811935, 809351, 833703, 828359, 828327, 833703, 1197167, 1335919, 1192623, 1260376, 665946, 32793, 33049]
theorem checked15 : checkTrace blocks trace15=true := by decide +kernel
theorem old15 : phaseClean508 reference 1147=some 33049 := by decide +kernel
theorem row15 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1147⟩=run reference n ⟨false,tbN_t8 1147⟩ := by
 have h:=trace_sound blocks 1147 [1657, 12399, 13543, 12511, 15783, 25499, 22951, 25479, 24999, 43429, 41885, 44453, 63527, 58259, 188839, 47271, 25479, 287623, 293159, 293255, 811935, 809351, 833703, 828359, 828327, 833703, 1197167, 1335919, 1192623, 1260376, 665946, 32793, 33049] checked15 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old15 n]
 rfl
def trace16 : List Nat := [1034, 81, 15879, 15879, 15901, 15047, 15518, 7879, 15751, 14791, 3783, 15516, 14535, 15943, 15791, 16327, 15943, 14787, 15827, 15943, 12231, 15774, 4039, 15943, 15782, 15814, 15943, 15943, 15943, 1070727, 870225, 870169, 22, 278]
theorem checked16 : checkTrace blocks trace16=true := by decide +kernel
theorem old16 : phaseClean508 reference 1034=some 278 := by decide +kernel
theorem row16 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1034⟩=run reference n ⟨false,tbN_t8 1034⟩ := by
 have h:=trace_sound blocks 1034 [81, 15879, 15879, 15901, 15047, 15518, 7879, 15751, 14791, 3783, 15516, 14535, 15943, 15791, 16327, 15943, 14787, 15827, 15943, 12231, 15774, 4039, 15943, 15782, 15814, 15943, 15943, 15943, 1070727, 870225, 870169, 22, 278] checked16 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old16 n]
 rfl
def trace17 : List Nat := [15370, 14417, 3663, 2759, 3743, 1863, 23835, 18247, 23559, 22599, 42821, 40221, 38213, 50759, 56367, 56903, 18119, 24103, 23675, 1991, 17991, 23582, 17991, 50887, 39943, 1088519, 1087431, 686087, 810503, 1730055, 484817, 484761, 65558, 65814]
theorem checked17 : checkTrace blocks trace17=true := by decide +kernel
theorem old17 : phaseClean508 reference 15370=some 65814 := by decide +kernel
theorem row17 (m n : List Bool) : run candidate m ⟨false,tbN_t8 15370⟩=run reference n ⟨false,tbN_t8 15370⟩ := by
 have h:=trace_sound blocks 15370 [14417, 3663, 2759, 3743, 1863, 23835, 18247, 23559, 22599, 42821, 40221, 38213, 50759, 56367, 56903, 18119, 24103, 23675, 1991, 17991, 23582, 17991, 50887, 39943, 1088519, 1087431, 686087, 810503, 1730055, 484817, 484761, 65558, 65814] checked17 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old17 n]
 rfl
def trace18 : List Nat := [1289, 88, 15908, 15908, 15952, 15076, 16018, 7908, 16260, 14820, 3812, 16016, 14564, 15972, 16312, 16356, 15972, 14816, 16300, 15972, 12260, 16274, 4068, 15972, 16260, 16260, 15972, 15972, 15972, 1070756, 872275, 870043, 23, 279]
theorem checked18 : checkTrace blocks trace18=true := by decide +kernel
theorem old18 : phaseClean508 reference 1289=some 279 := by decide +kernel
theorem row18 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1289⟩=run reference n ⟨false,tbN_t8 1289⟩ := by
 have h:=trace_sound blocks 1289 [88, 15908, 15908, 15952, 15076, 16018, 7908, 16260, 14820, 3812, 16016, 14564, 15972, 16312, 16356, 15972, 14816, 16300, 15972, 12260, 16274, 4068, 15972, 16260, 16260, 15972, 15972, 15972, 1070756, 872275, 870043, 23, 279] checked18 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old18 n]
 rfl
def trace19 : List Nat := [1401, 1656, 12396, 13412, 12370, 15524, 25239, 22692, 9092, 8612, 43174, 41617, 44198, 43172, 41912, 41956, 30756, 9092, 9092, 14628, 2980, 9106, 11172, 63524, 41957, 41957, 43300, 30756, 89636, 1533476, 683475, 680987, 65559, 65815]
theorem checked19 : checkTrace blocks trace19=true := by decide +kernel
theorem old19 : phaseClean508 reference 1401=some 65815 := by decide +kernel
theorem row19 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1401⟩=run reference n ⟨false,tbN_t8 1401⟩ := by
 have h:=trace_sound blocks 1401 [1656, 12396, 13412, 12370, 15524, 25239, 22692, 9092, 8612, 43174, 41617, 44198, 43172, 41912, 41956, 30756, 9092, 9092, 14628, 2980, 9106, 11172, 63524, 41957, 41957, 43300, 30756, 89636, 1533476, 683475, 680987, 65559, 65815] checked19 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old19 n]
 rfl
def trace20 : List Nat := [1292, 15910, 15898, 15898, 16174, 6858, 15592, 15946, 15862, 13278, 20186, 31979, 96474, 16154, 15862, 146330, 147290, 180154, 179638, 196570, 180218, 179690, 172026, 425818, 425403, 1474011, 1474138, 985434, 1050524, 874908, 869308, 1333652, 20, 276]
theorem checked20 : checkTrace blocks trace20=true := by decide +kernel
theorem old20 : phaseClean508 reference 1292=some 276 := by decide +kernel
theorem row20 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1292⟩=run reference n ⟨false,tbN_t8 1292⟩ := by
 have h:=trace_sound blocks 1292 [15910, 15898, 15898, 16174, 6858, 15592, 15946, 15862, 13278, 20186, 31979, 96474, 16154, 15862, 146330, 147290, 180154, 179638, 196570, 180218, 179690, 172026, 425818, 425403, 1474011, 1474138, 985434, 1050524, 874908, 869308, 1333652, 20, 276] checked20 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old20 n]
 rfl
def trace21 : List Nat := [15116, 1636, 3674, 2642, 3854, 9794, 7245, 9922, 7270, 5702, 18002, 23627, 88146, 1810, 7254, 137746, 132946, 171570, 171070, 182226, 169586, 171082, 169586, 411474, 416819, 1465427, 1459794, 995666, 1064852, 67924, 1970620, 461716, 65556, 65812]
theorem checked21 : checkTrace blocks trace21=true := by decide +kernel
theorem old21 : phaseClean508 reference 15116=some 65812 := by decide +kernel
theorem row21 (m n : List Bool) : run candidate m ⟨false,tbN_t8 15116⟩=run reference n ⟨false,tbN_t8 15116⟩ := by
 have h:=trace_sound blocks 15116 [1636, 3674, 2642, 3854, 9794, 7245, 9922, 7270, 5702, 18002, 23627, 88146, 1810, 7254, 137746, 132946, 171570, 171070, 182226, 169586, 171082, 169586, 411474, 416819, 1465427, 1459794, 995666, 1064852, 67924, 1970620, 461716, 65556, 65812] checked21 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old21 n]
 rfl
def trace22 : List Nat := [1547, 95, 15929, 15929, 16227, 6889, 16100, 15977, 16373, 13309, 20217, 32487, 96505, 16185, 16353, 146361, 147321, 180121, 180169, 196601, 180185, 180198, 171993, 425849, 425881, 1474457, 1474169, 985465, 1050559, 874943, 871358, 1333270, 21, 277]
theorem checked22 : checkTrace blocks trace22=true := by decide +kernel
theorem old22 : phaseClean508 reference 1547=some 277 := by decide +kernel
theorem row22 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1547⟩=run reference n ⟨false,tbN_t8 1547⟩ := by
 have h:=trace_sound blocks 1547 [95, 15929, 15929, 16227, 6889, 16100, 15977, 16373, 13309, 20217, 32487, 96505, 16185, 16353, 146361, 147321, 180121, 180169, 196601, 180185, 180198, 171993, 425849, 425881, 1474457, 1474169, 985465, 1050559, 874943, 871358, 1333270, 21, 277] checked22 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old22 n]
 rfl
def trace23 : List Nat := [1655, 14365, 3705, 2673, 3907, 9825, 7745, 9953, 7781, 5733, 18033, 24135, 88177, 1841, 7745, 137777, 132977, 171537, 171585, 182257, 169553, 171590, 169553, 411505, 417297, 1465873, 1459825, 995697, 1064887, 67959, 1972670, 461334, 65557, 65813]
theorem checked23 : checkTrace blocks trace23=true := by decide +kernel
theorem old23 : phaseClean508 reference 1655=some 65813 := by decide +kernel
theorem row23 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1655⟩=run reference n ⟨false,tbN_t8 1655⟩ := by
 have h:=trace_sound blocks 1655 [14365, 3705, 2673, 3907, 9825, 7745, 9953, 7781, 5733, 18033, 24135, 88177, 1841, 7745, 137777, 132977, 171537, 171585, 182257, 169553, 171590, 169553, 411505, 417297, 1465873, 1459825, 995697, 1064887, 67959, 1972670, 461334, 65557, 65813] checked23 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old23 n]
 rfl
def trace24 : List Nat := [1550, 15909, 15891, 15891, 15881, 15059, 15566, 7891, 15835, 14803, 3795, 15566, 14547, 15955, 15811, 147411, 65107, 15763, 15811, 32467, 16371, 15820, 8179, 278099, 277938, 277970, 278099, 276115, 1578643, 939099, 870035, 872221, 18, 274]
theorem checked24 : checkTrace blocks trace24=true := by decide +kernel
theorem old24 : phaseClean508 reference 1550=some 274 := by decide +kernel
theorem row24 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1550⟩=run reference n ⟨false,tbN_t8 1550⟩ := by
 have h:=trace_sound blocks 1550 [15909, 15891, 15891, 15881, 15059, 15566, 7891, 15835, 14803, 3795, 15566, 14547, 15955, 15811, 147411, 65107, 15763, 15811, 32467, 16371, 15820, 8179, 278099, 277938, 277970, 278099, 276115, 1578643, 939099, 870035, 872221, 18, 274] checked24 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old24 n]
 rfl
def trace25 : List Nat := [14862, 1637, 3677, 2645, 3859, 9797, 23635, 26309, 7289, 4689, 58967, 56406, 54359, 34581, 40017, 170517, 34645, 38993, 39953, 34389, 42069, 40022, 42069, 313173, 318516, 318548, 312917, 282517, 1994707, 271835, 468243, 470173, 65554, 65810]
theorem checked25 : checkTrace blocks trace25=true := by decide +kernel
theorem old25 : phaseClean508 reference 14862=some 65810 := by decide +kernel
theorem row25 (m n : List Bool) : run candidate m ⟨false,tbN_t8 14862⟩=run reference n ⟨false,tbN_t8 14862⟩ := by
 have h:=trace_sound blocks 14862 [1637, 3677, 2645, 3859, 9797, 23635, 26309, 7289, 4689, 58967, 56406, 54359, 34581, 40017, 170517, 34645, 38993, 39953, 34389, 42069, 40022, 42069, 313173, 318516, 318548, 312917, 282517, 1994707, 271835, 468243, 470173, 65554, 65810] checked25 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old25 n]
 rfl
def trace26 : List Nat := [1805, 15916, 15920, 15920, 15940, 15088, 16066, 7920, 16344, 14832, 3824, 16066, 14576, 15984, 16340, 147440, 65136, 15792, 16316, 32496, 16336, 16320, 8144, 278128, 278416, 278416, 278128, 276144, 1578672, 939128, 872081, 872095, 19, 275]
theorem checked26 : checkTrace blocks trace26=true := by decide +kernel
theorem old26 : phaseClean508 reference 1805=some 275 := by decide +kernel
theorem row26 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1805⟩=run reference n ⟨false,tbN_t8 1805⟩ := by
 have h:=trace_sound blocks 1805 [15916, 15920, 15920, 15940, 15088, 16066, 7920, 16344, 14832, 3824, 16066, 14576, 15984, 16340, 147440, 65136, 15792, 16316, 32496, 16336, 16320, 8144, 278128, 278416, 278416, 278128, 276144, 1578672, 939128, 872081, 872095, 19, 275] checked26 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old26 n]
 rfl
def trace27 : List Nat := [1909, 14364, 3710, 2678, 3934, 9830, 24159, 26342, 7802, 4722, 58996, 56922, 54388, 34614, 40518, 170550, 34678, 39026, 40558, 34422, 42102, 40538, 42102, 313206, 318998, 318998, 312950, 282550, 1994736, 271864, 470289, 470303, 65555, 65811]
theorem checked27 : checkTrace blocks trace27=true := by decide +kernel
theorem old27 : phaseClean508 reference 1909=some 65811 := by decide +kernel
theorem row27 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1909⟩=run reference n ⟨false,tbN_t8 1909⟩ := by
 have h:=trace_sound blocks 1909 [14364, 3710, 2678, 3934, 9830, 24159, 26342, 7802, 4722, 58996, 56922, 54388, 34614, 40518, 170550, 34678, 39026, 40558, 34422, 42102, 40538, 42102, 313206, 318998, 318998, 312950, 282550, 1994736, 271864, 470289, 470303, 65555, 65811] checked27 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old27 n]
 rfl
def trace28 : List Nat := [1808, 98, 576, 72, 546, 72, 1056, 72, 1032, 72, 72, 1056, 72, 72, 1076, 131144, 49224, 76, 1116, 16584, 4200, 1058, 4200, 262216, 263209, 1311817, 1310792, 931400, 603720, 1579584, 394110, 2035856, 16, 272]
theorem checked28 : checkTrace blocks trace28=true := by decide +kernel
theorem old28 : phaseClean508 reference 1808=some 272 := by decide +kernel
theorem row28 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1808⟩=run reference n ⟨false,tbN_t8 1808⟩ := by
 have h:=trace_sound blocks 1808 [98, 576, 72, 546, 72, 1056, 72, 1032, 72, 72, 1056, 72, 72, 1076, 131144, 49224, 76, 1116, 16584, 4200, 1058, 4200, 262216, 263209, 1311817, 1310792, 931400, 603720, 1579584, 394110, 2035856, 16, 272] checked28 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old28 n]
 rfl
def trace29 : List Nat := [14608, 14368, 12800, 13312, 12802, 15552, 9349, 6336, 9624, 9680, 2240, 9344, 8384, 14400, 9620, 139712, 63552, 8644, 9684, 30912, 14816, 9602, 6624, 276544, 271777, 1320385, 1325120, 921152, 593472, 1329800, 1397118, 803472, 65552, 65808]
theorem checked29 : checkTrace blocks trace29=true := by decide +kernel
theorem old29 : phaseClean508 reference 14608=some 65808 := by decide +kernel
theorem row29 (m n : List Bool) : run candidate m ⟨false,tbN_t8 14608⟩=run reference n ⟨false,tbN_t8 14608⟩ := by
 have h:=trace_sound blocks 14608 [14368, 12800, 13312, 12802, 15552, 9349, 6336, 9624, 9680, 2240, 9344, 8384, 14400, 9620, 139712, 63552, 8644, 9684, 30912, 14816, 9602, 6624, 276544, 271777, 1320385, 1325120, 921152, 593472, 1329800, 1397118, 803472, 65552, 65808] checked29 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old29 n]
 rfl
def trace30 : List Nat := [2063, 13931, 15971, 14955, 11887, 4843, 7852, 5867, 8075, 6635, 1771, 7852, 6379, 13931, 8119, 7595, 13931, 6639, 8099, 13931, 2027, 8109, 2027, 13931, 8106, 8138, 13931, 13931, 13931, 1120867, 985980, 1446162, 17, 273]
theorem checked30 : checkTrace blocks trace30=true := by decide +kernel
theorem old30 : phaseClean508 reference 2063=some 273 := by decide +kernel
theorem row30 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2063⟩=run reference n ⟨false,tbN_t8 2063⟩ := by
 have h:=trace_sound blocks 2063 [13931, 15971, 14955, 11887, 4843, 7852, 5867, 8075, 6635, 1771, 7852, 6379, 13931, 8119, 7595, 13931, 6639, 8099, 13931, 2027, 8109, 2027, 13931, 8106, 8138, 13931, 13931, 13931, 1120867, 985980, 1446162, 17, 273] checked30 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old30 n]
 rfl
def trace31 : List Nat := [2163, 3625, 3619, 3619, 7759, 11875, 15881, 3683, 15899, 15475, 3683, 15884, 14435, 3683, 15895, 15395, 3683, 14439, 15915, 3683, 11875, 15885, 3683, 3683, 15906, 15938, 3683, 3683, 3683, 1919659, 1857916, 344850, 65553, 65809]
theorem checked31 : checkTrace blocks trace31=true := by decide +kernel
theorem old31 : phaseClean508 reference 2163=some 65809 := by decide +kernel
theorem row31 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2163⟩=run reference n ⟨false,tbN_t8 2163⟩ := by
 have h:=trace_sound blocks 2163 [3625, 3619, 3619, 7759, 11875, 15881, 3683, 15899, 15475, 3683, 15884, 14435, 3683, 15895, 15395, 3683, 14439, 15915, 3683, 11875, 15885, 3683, 3683, 15906, 15938, 3683, 3683, 3683, 1919659, 1857916, 344850, 65553, 65809] checked31 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old31 n]
 rfl
def trace32 : List Nat := [2066, 2081, 515, 1027, 4621, 10307, 9228, 2115, 9219, 8259, 2115, 9228, 8259, 2115, 9279, 8707, 2115, 9219, 9219, 2115, 10307, 9230, 2115, 2115, 9219, 1057795, 1050691, 669315, 1119875, 480331, 280195, 282369, 14, 46]
theorem checked32 : checkTrace blocks trace32=true := by decide +kernel
theorem old32 : phaseClean508 reference 2066=some 46 := by decide +kernel
theorem row32 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2066⟩=run reference n ⟨false,tbN_t8 2066⟩ := by
 have h:=trace_sound blocks 2066 [2081, 515, 1027, 4621, 10307, 9228, 2115, 9219, 8259, 2115, 9228, 8259, 2115, 9279, 8707, 2115, 9219, 9219, 2115, 10307, 9230, 2115, 2115, 9219, 1057795, 1050691, 669315, 1119875, 480331, 280195, 282369, 14, 46] checked32 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old32 n]
 rfl
def trace33 : List Nat := [14354, 14369, 12803, 13315, 12815, 15555, 9353, 6339, 9627, 9683, 2243, 9356, 8387, 14403, 9623, 8643, 14403, 9603, 9603, 14403, 10691, 9614, 2499, 14403, 9634, 9666, 14403, 14403, 14403, 807043, 803459, 805633, 1038, 131118]
theorem checked33 : checkTrace blocks trace33=true := by decide +kernel
theorem old33 : phaseClean508 reference 14354=some 131118 := by decide +kernel
theorem row33 (m n : List Bool) : run candidate m ⟨false,tbN_t8 14354⟩=run reference n ⟨false,tbN_t8 14354⟩ := by
 have h:=trace_sound blocks 14354 [14369, 12803, 13315, 12815, 15555, 9353, 6339, 9627, 9683, 2243, 9356, 8387, 14403, 9623, 8643, 14403, 9603, 9603, 14403, 10691, 9614, 2499, 14403, 9634, 9666, 14403, 14403, 14403, 807043, 803459, 805633, 1038, 131118] checked33 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old33 n]
 rfl
def trace34 : List Nat := [2321, 2088, 544, 1056, 4672, 10336, 9728, 2144, 9728, 8288, 2144, 9728, 8288, 2144, 9768, 8736, 2144, 9248, 9852, 2144, 10336, 9730, 2144, 2144, 9761, 1058369, 1050720, 669344, 1119904, 480360, 282241, 282243, 15, 47]
theorem checked34 : checkTrace blocks trace34=true := by decide +kernel
theorem old34 : phaseClean508 reference 2321=some 47 := by decide +kernel
theorem row34 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2321⟩=run reference n ⟨false,tbN_t8 2321⟩ := by
 have h:=trace_sound blocks 2321 [2088, 544, 1056, 4672, 10336, 9728, 2144, 9728, 8288, 2144, 9728, 8288, 2144, 9768, 8736, 2144, 9248, 9852, 2144, 10336, 9730, 2144, 2144, 9761, 1058369, 1050720, 669344, 1119904, 480360, 282241, 282243, 15, 47] checked34 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old34 n]
 rfl
def trace35 : List Nat := [2417, 3624, 3616, 3616, 7746, 11872, 15877, 3680, 15896, 15472, 3680, 15872, 14432, 3680, 15892, 146464, 52832, 15392, 15996, 20192, 15936, 15873, 7744, 265824, 278049, 1326657, 1314400, 931936, 604256, 348320, 346753, 346755, 1039, 131119]
theorem checked35 : checkTrace blocks trace35=true := by decide +kernel
theorem old35 : phaseClean508 reference 2417=some 131119 := by decide +kernel
theorem row35 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2417⟩=run reference n ⟨false,tbN_t8 2417⟩ := by
 have h:=trace_sound blocks 2417 [3624, 3616, 3616, 7746, 11872, 15877, 3680, 15896, 15472, 3680, 15872, 14432, 3680, 15892, 146464, 52832, 15392, 15996, 20192, 15936, 15873, 7744, 265824, 278049, 1326657, 1314400, 931936, 604256, 348320, 346753, 346755, 1039, 131119] checked35 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old35 n]
 rfl
def trace36 : List Nat := [2324, 13910, 542, 1054, 4926, 2126, 9338, 10446, 9330, 10842, 18526, 25723, 90206, 2334, 9318, 140894, 133470, 172666, 173158, 182750, 178302, 173178, 170110, 411998, 418846, 418846, 411742, 328094, 77656, 1727312, 279150, 1921420, 12, 44]
theorem checked36 : checkTrace blocks trace36=true := by decide +kernel
theorem old36 : phaseClean508 reference 2324=some 44 := by decide +kernel
theorem row36 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2324⟩=run reference n ⟨false,tbN_t8 2324⟩ := by
 have h:=trace_sound blocks 2324 [13910, 542, 1054, 4926, 2126, 9338, 10446, 9330, 10842, 18526, 25723, 90206, 2334, 9318, 140894, 133470, 172666, 173158, 182750, 178302, 173178, 170110, 411998, 418846, 418846, 411742, 328094, 77656, 1727312, 279150, 1921420, 12, 44] checked36 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old36 n]
 rfl
def trace37 : List Nat := [14100, 3604, 12894, 12374, 8990, 13510, 17631, 28742, 1530, 3026, 57556, 50394, 52436, 45334, 34246, 165846, 45398, 34198, 34246, 45142, 41942, 34265, 41942, 323926, 312726, 312726, 323670, 293270, 1989072, 1392592, 1521390, 926988, 1036, 131116]
theorem checked37 : checkTrace blocks trace37=true := by decide +kernel
theorem old37 : phaseClean508 reference 14100=some 131116 := by decide +kernel
theorem row37 (m n : List Bool) : run candidate m ⟨false,tbN_t8 14100⟩=run reference n ⟨false,tbN_t8 14100⟩ := by
 have h:=trace_sound blocks 14100 [3604, 12894, 12374, 8990, 13510, 17631, 28742, 1530, 3026, 57556, 50394, 52436, 45334, 34246, 165846, 45398, 34198, 34246, 45142, 41942, 34265, 41942, 323926, 312726, 312726, 323670, 293270, 1989072, 1392592, 1521390, 926988, 1036, 131116] checked37 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old37 n]
 rfl
def trace38 : List Nat := [2579, 2095, 573, 1085, 4979, 2157, 9846, 10477, 9841, 10873, 18557, 26231, 90237, 2365, 9841, 140925, 133501, 172633, 173593, 182781, 178269, 173686, 170077, 412029, 419388, 419420, 411773, 328125, 77691, 1727347, 281196, 1921038, 13, 45]
theorem checked38 : checkTrace blocks trace38=true := by decide +kernel
theorem old38 : phaseClean508 reference 2579=some 45 := by decide +kernel
theorem row38 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2579⟩=run reference n ⟨false,tbN_t8 2579⟩ := by
 have h:=trace_sound blocks 2579 [2095, 573, 1085, 4979, 2157, 9846, 10477, 9841, 10873, 18557, 26231, 90237, 2365, 9841, 140925, 133501, 172633, 173593, 182781, 178269, 173686, 170077, 412029, 419388, 419420, 411773, 328125, 77691, 1727347, 281196, 1921038, 13, 45] checked38 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old38 n]
 rfl
def trace39 : List Nat := [2671, 12397, 12925, 12405, 9043, 13541, 18131, 28773, 2041, 3057, 57591, 50902, 52471, 45365, 34769, 165877, 45429, 34229, 34745, 45173, 41973, 34773, 41973, 323957, 313268, 313300, 323701, 293301, 1989107, 1392627, 1523436, 926862, 1037, 131117]
theorem checked39 : checkTrace blocks trace39=true := by decide +kernel
theorem old39 : phaseClean508 reference 2671=some 131117 := by decide +kernel
theorem row39 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2671⟩=run reference n ⟨false,tbN_t8 2671⟩ := by
 have h:=trace_sound blocks 2671 [12397, 12925, 12405, 9043, 13541, 18131, 28773, 2041, 3057, 57591, 50902, 52471, 45365, 34769, 165877, 45429, 34229, 34745, 45173, 41973, 34773, 41973, 323957, 313268, 313300, 323701, 293301, 1989107, 1392627, 1523436, 926862, 1037, 131117] checked39 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old39 n]
 rfl
def trace40 : List Nat := [2582, 13909, 535, 1047, 4633, 10327, 9308, 2135, 9311, 41047, 10325, 9311, 76885, 67671, 74835, 205335, 247895, 204883, 205843, 215255, 211063, 205916, 202871, 477271, 468055, 468023, 465239, 360599, 638551, 1693335, 313153, 313093, 10, 42]
theorem checked40 : checkTrace blocks trace40=true := by decide +kernel
theorem old40 : phaseClean508 reference 2582=some 42 := by decide +kernel
theorem row40 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2582⟩=run reference n ⟨false,tbN_t8 2582⟩ := by
 have h:=trace_sound blocks 2582 [13909, 535, 1047, 4633, 10327, 9308, 2135, 9311, 41047, 10325, 9311, 76885, 67671, 74835, 205335, 247895, 204883, 205843, 215255, 211063, 205916, 202871, 477271, 468055, 468023, 465239, 360599, 638551, 1693335, 313153, 313093, 10, 42] checked40 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old40 n]
 rfl
def trace41 : List Nat := [13846, 3605, 12889, 12369, 8963, 13505, 1217, 12353, 1509, 4037, 16593, 17607, 82129, 12561, 1473, 133073, 143697, 164853, 165353, 192977, 168433, 165317, 168433, 422225, 411025, 1459601, 1470545, 984913, 1051031, 1053535, 918081, 918021, 1034, 131114]
theorem checked41 : checkTrace blocks trace41=true := by decide +kernel
theorem old41 : phaseClean508 reference 13846=some 131114 := by decide +kernel
theorem row41 (m n : List Bool) : run candidate m ⟨false,tbN_t8 13846⟩=run reference n ⟨false,tbN_t8 13846⟩ := by
 have h:=trace_sound blocks 13846 [3605, 12889, 12369, 8963, 13505, 1217, 12353, 1509, 4037, 16593, 17607, 82129, 12561, 1473, 133073, 143697, 164853, 165353, 192977, 168433, 165317, 168433, 422225, 411025, 1459601, 1470545, 984913, 1051031, 1053535, 918081, 918021, 1034, 131114] checked41 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old41 n]
 rfl
def trace42 : List Nat := [2837, 13916, 564, 1076, 4692, 10356, 9808, 2164, 9820, 41076, 10358, 9811, 76918, 67700, 75332, 205364, 247924, 204912, 206444, 215284, 211028, 206416, 202836, 477300, 468597, 468597, 465268, 360628, 638580, 1693364, 315203, 312967, 11, 43]
theorem checked42 : checkTrace blocks trace42=true := by decide +kernel
theorem old42 : phaseClean508 reference 2837=some 43 := by decide +kernel
theorem row42 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2837⟩=run reference n ⟨false,tbN_t8 2837⟩ := by
 have h:=trace_sound blocks 2837 [13916, 564, 1076, 4692, 10356, 9808, 2164, 9820, 41076, 10358, 9811, 76918, 67700, 75332, 205364, 247924, 204912, 206444, 215284, 211028, 206416, 202836, 477300, 468597, 468597, 465268, 360628, 638580, 1693364, 315203, 312967, 11, 43] checked42 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old42 n]
 rfl
def trace43 : List Nat := [2925, 12396, 12922, 12402, 9038, 13538, 1741, 12386, 2022, 4070, 16626, 18123, 82162, 12594, 2006, 133106, 143730, 164822, 165782, 193010, 168402, 165833, 168402, 422258, 411571, 1460179, 1470578, 984946, 1051060, 1053564, 920131, 918407, 1035, 131115]
theorem checked43 : checkTrace blocks trace43=true := by decide +kernel
theorem old43 : phaseClean508 reference 2925=some 131115 := by decide +kernel
theorem row43 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2925⟩=run reference n ⟨false,tbN_t8 2925⟩ := by
 have h:=trace_sound blocks 2925 [12396, 12922, 12402, 9038, 13538, 1741, 12386, 2022, 4070, 16626, 18123, 82162, 12594, 2006, 133106, 143730, 164822, 165782, 193010, 168402, 165833, 168402, 422258, 411571, 1460179, 1470578, 984946, 1051060, 1053564, 920131, 918407, 1035, 131115] checked43 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old43 n]
 rfl
def trace44 : List Nat := [2840, 2098, 15372, 14860, 11314, 4748, 6322, 5772, 6540, 39308, 9870, 6321, 5262, 75404, 72088, 73612, 128524, 72076, 72076, 95884, 71596, 72114, 71596, 79372, 72109, 1120717, 1127948, 690380, 2006668, 628876, 623276, 1087624, 8, 40]
theorem checked44 : checkTrace blocks trace44=true := by decide +kernel
theorem old44 : phaseClean508 reference 2840=some 40 := by decide +kernel
theorem row44 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2840⟩=run reference n ⟨false,tbN_t8 2840⟩ := by
 have h:=trace_sound blocks 2840 [2098, 15372, 14860, 11314, 4748, 6322, 5772, 6540, 39308, 9870, 6321, 5262, 75404, 72088, 73612, 128524, 72076, 72076, 95884, 71596, 72114, 71596, 79372, 72109, 1120717, 1127948, 690380, 2006668, 628876, 623276, 1087624, 8, 40] checked44 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old44 n]
 rfl
def trace45 : List Nat := [13592, 12400, 3148, 3652, 7186, 11780, 30743, 19972, 14340, 14340, 44550, 47121, 46086, 40580, 47160, 48644, 19972, 15968, 14380, 3844, 3076, 14353, 11268, 52740, 47205, 47205, 40708, 19972, 92164, 424972, 1734188, 224264, 1032, 131112]
theorem checked45 : checkTrace blocks trace45=true := by decide +kernel
theorem old45 : phaseClean508 reference 13592=some 131112 := by decide +kernel
theorem row45 (m n : List Bool) : run candidate m ⟨false,tbN_t8 13592⟩=run reference n ⟨false,tbN_t8 13592⟩ := by
 have h:=trace_sound blocks 13592 [12400, 3148, 3652, 7186, 11780, 30743, 19972, 14340, 14340, 44550, 47121, 46086, 40580, 47160, 48644, 19972, 15968, 14380, 3844, 3076, 14353, 11268, 52740, 47205, 47205, 40708, 19972, 92164, 424972, 1734188, 224264, 1032, 131112] checked45 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old45 n]
 rfl
def trace46 : List Nat := [3095, 13851, 559, 1199, 4863, 10607, 10046, 2415, 26127, 57455, 10605, 10045, 11629, 84079, 91663, 90671, 116975, 91183, 91763, 84079, 88655, 91710, 96847, 67823, 75343, 75311, 67823, 35055, 1285807, 301231, 297646, 1939722, 9, 41]
theorem checked46 : checkTrace blocks trace46=true := by decide +kernel
theorem old46 : phaseClean508 reference 3095=some 41 := by decide +kernel
theorem row46 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3095⟩=run reference n ⟨false,tbN_t8 3095⟩ := by
 have h:=trace_sound blocks 3095 [13851, 559, 1199, 4863, 10607, 10046, 2415, 26127, 57455, 10605, 10045, 11629, 84079, 91663, 90671, 116975, 91183, 91763, 84079, 88655, 91710, 96847, 67823, 75343, 75311, 67823, 35055, 1285807, 301231, 297646, 1939722, 9, 41] checked46 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old46 n]
 rfl
def trace47 : List Nat := [3179, 3673, 12911, 12519, 8927, 5607, 18331, 20967, 18311, 16871, 41445, 34717, 36325, 61543, 51119, 50087, 28903, 17347, 18387, 12775, 16871, 18333, 16871, 61671, 34695, 1083271, 1090023, 675367, 813095, 752687, 1539630, 945546, 1033, 131113]
theorem checked47 : checkTrace blocks trace47=true := by decide +kernel
theorem old47 : phaseClean508 reference 3179=some 131113 := by decide +kernel
theorem row47 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3179⟩=run reference n ⟨false,tbN_t8 3179⟩ := by
 have h:=trace_sound blocks 3179 [3673, 12911, 12519, 8927, 5607, 18331, 20967, 18311, 16871, 41445, 34717, 36325, 61543, 51119, 50087, 28903, 17347, 18387, 12775, 16871, 18333, 16871, 61671, 34695, 1083271, 1090023, 675367, 813095, 752687, 1539630, 945546, 1033, 131113] checked47 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old47 n]
 rfl
def trace48 : List Nat := [3098, 2161, 15367, 14855, 11293, 4743, 6302, 5767, 6535, 6535, 1671, 6300, 6279, 13831, 6547, 138695, 62983, 6535, 268679, 292487, 268199, 268700, 268199, 800263, 792998, 793030, 800263, 1710799, 80591, 789519, 1053743, 591753, 6, 38]
theorem checked48 : checkTrace blocks trace48=true := by decide +kernel
theorem old48 : phaseClean508 reference 3098=some 38 := by decide +kernel
theorem row48 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3098⟩=run reference n ⟨false,tbN_t8 3098⟩ := by
 have h:=trace_sound blocks 3098 [2161, 15367, 14855, 11293, 4743, 6302, 5767, 6535, 6535, 1671, 6300, 6279, 13831, 6547, 138695, 62983, 6535, 268679, 292487, 268199, 268700, 268199, 800263, 792998, 793030, 800263, 1710799, 80591, 789519, 1053743, 591753, 6, 38] checked48 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old48 n]
 rfl
def trace49 : List Nat := [13338, 12401, 3151, 3783, 7327, 12039, 31003, 20231, 30727, 30727, 44805, 47389, 46341, 52743, 63507, 195655, 36487, 32355, 30767, 20231, 32295, 30748, 24103, 315015, 309255, 1357831, 1351559, 948359, 1343111, 337991, 1716399, 205577, 1030, 131110]
theorem checked49 : checkTrace blocks trace49=true := by decide +kernel
theorem old49 : phaseClean508 reference 13338=some 131110 := by decide +kernel
theorem row49 (m n : List Bool) : run candidate m ⟨false,tbN_t8 13338⟩=run reference n ⟨false,tbN_t8 13338⟩ := by
 have h:=trace_sound blocks 13338 [12401, 3151, 3783, 7327, 12039, 31003, 20231, 30727, 30727, 44805, 47389, 46341, 52743, 63507, 195655, 36487, 32355, 30767, 20231, 32295, 30748, 24103, 315015, 309255, 1357831, 1351559, 948359, 1343111, 337991, 1716399, 205577, 1030, 131110] checked49 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old49 n]
 rfl
def trace50 : List Nat := [3353, 2168, 15396, 14884, 11344, 4772, 6802, 5796, 7044, 6564, 1700, 6800, 6308, 13860, 7044, 138724, 63012, 6564, 269304, 292516, 268164, 269200, 268164, 800292, 793476, 793476, 800292, 1710828, 80620, 789548, 1055789, 591371, 7, 39]
theorem checked50 : checkTrace blocks trace50=true := by decide +kernel
theorem old50 : phaseClean508 reference 3353=some 39 := by decide +kernel
theorem row50 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3353⟩=run reference n ⟨false,tbN_t8 3353⟩ := by
 have h:=trace_sound blocks 3353 [2168, 15396, 14884, 11344, 4772, 6802, 5796, 7044, 6564, 1700, 6800, 6308, 13860, 7044, 138724, 63012, 6564, 269304, 292516, 268164, 269200, 268164, 800292, 793476, 793476, 800292, 1710828, 80620, 789548, 1055789, 591371, 7, 39] checked50 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old50 n]
 rfl
def trace51 : List Nat := [3433, 3672, 12908, 12388, 8786, 5348, 18071, 20708, 1924, 484, 41190, 34449, 36070, 41188, 34692, 164324, 45156, 960, 2000, 29156, 13252, 1936, 13252, 323684, 296933, 296933, 303460, 293028, 1670820, 534628, 1521837, 926347, 1031, 131111]
theorem checked51 : checkTrace blocks trace51=true := by decide +kernel
theorem old51 : phaseClean508 reference 3433=some 131111 := by decide +kernel
theorem row51 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3433⟩=run reference n ⟨false,tbN_t8 3433⟩ := by
 have h:=trace_sound blocks 3433 [3672, 12908, 12388, 8786, 5348, 18071, 20708, 1924, 484, 41190, 34449, 36070, 41188, 34692, 164324, 45156, 960, 2000, 29156, 13252, 1936, 13252, 323684, 296933, 296933, 303460, 293028, 1670820, 534628, 1521837, 926347, 1031, 131111] checked51 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old51 n]
 rfl
def trace52 : List Nat := [3356, 13830, 15386, 14874, 11566, 12938, 6376, 13834, 6646, 5022, 18074, 22763, 88218, 14170, 6602, 6554, 194330, 172030, 432610, 440090, 427930, 432616, 427930, 685850, 678331, 1726939, 1734170, 1387986, 1114900, 1114900, 1052866, 1054980, 4, 36]
theorem checked52 : checkTrace blocks trace52=true := by decide +kernel
theorem old52 : phaseClean508 reference 3356=some 36 := by decide +kernel
theorem row52 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3356⟩=run reference n ⟨false,tbN_t8 3356⟩ := by
 have h:=trace_sound blocks 3356 [13830, 15386, 14874, 11566, 12938, 6376, 13834, 6646, 5022, 18074, 22763, 88218, 14170, 6602, 6554, 194330, 172030, 432610, 440090, 427930, 432616, 427930, 685850, 678331, 1726939, 1734170, 1387986, 1114900, 1114900, 1052866, 1054980, 4, 36] checked52 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old52 n]
 rfl
def trace53 : List Nat := [13084, 3652, 3162, 3666, 7438, 3586, 14413, 11906, 14438, 13830, 19986, 30795, 96274, 3922, 14442, 14354, 184082, 179830, 178282, 167698, 175634, 178248, 167442, 151314, 161843, 1210451, 1199634, 733650, 532244, 1984276, 214210, 216324, 1028, 131108]
theorem checked53 : checkTrace blocks trace53=true := by decide +kernel
theorem old53 : phaseClean508 reference 13084=some 131108 := by decide +kernel
theorem row53 (m n : List Bool) : run candidate m ⟨false,tbN_t8 13084⟩=run reference n ⟨false,tbN_t8 13084⟩ := by
 have h:=trace_sound blocks 13084 [3652, 3162, 3666, 7438, 3586, 14413, 11906, 14438, 13830, 19986, 30795, 96274, 3922, 14442, 14354, 184082, 179830, 178282, 167698, 175634, 178248, 167442, 151314, 161843, 1210451, 1199634, 733650, 532244, 1984276, 214210, 216324, 1028, 131108] checked53 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old53 n]
 rfl
def trace54 : List Nat := [3611, 2175, 15417, 14905, 11619, 12969, 6884, 13865, 7157, 5053, 18105, 23271, 88249, 14201, 7133, 6585, 194361, 171997, 433053, 440121, 427961, 433124, 427961, 685881, 678809, 1727385, 1734201, 1388017, 1114935, 1114935, 1054912, 1054854, 5, 37]
theorem checked54 : checkTrace blocks trace54=true := by decide +kernel
theorem old54 : phaseClean508 reference 3611=some 37 := by decide +kernel
theorem row54 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3611⟩=run reference n ⟨false,tbN_t8 3611⟩ := by
 have h:=trace_sound blocks 3611 [2175, 15417, 14905, 11619, 12969, 6884, 13865, 7157, 5053, 18105, 23271, 88249, 14201, 7133, 6585, 194361, 171997, 433053, 440121, 427961, 433124, 427961, 685881, 678809, 1727385, 1734201, 1388017, 1114935, 1114935, 1054912, 1054854, 5, 37] checked54 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old54 n]
 rfl
def trace55 : List Nat := [3687, 12349, 3193, 3697, 7491, 3617, 14913, 11937, 14949, 13861, 20017, 31303, 96305, 3953, 14973, 14385, 184113, 179797, 178709, 167729, 175665, 178756, 167473, 151345, 162321, 1210897, 1199665, 733681, 532279, 1984311, 216256, 216198, 1029, 131109]
theorem checked55 : checkTrace blocks trace55=true := by decide +kernel
theorem old55 : phaseClean508 reference 3687=some 131109 := by decide +kernel
theorem row55 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3687⟩=run reference n ⟨false,tbN_t8 3687⟩ := by
 have h:=trace_sound blocks 3687 [12349, 3193, 3697, 7491, 3617, 14913, 11937, 14949, 13861, 20017, 31303, 96305, 3953, 14973, 14385, 184113, 179797, 178709, 167729, 175665, 178756, 167473, 151345, 162321, 1210897, 1199665, 733681, 532279, 1984311, 216256, 216198, 1029, 131109] checked55 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old55 n]
 rfl
def trace56 : List Nat := [3614, 13829, 15379, 14867, 11273, 4755, 6350, 5779, 6619, 6547, 1683, 6350, 6291, 13843, 6655, 7635, 13843, 7639, 268695, 275987, 264083, 268750, 264083, 538131, 530866, 530898, 538131, 1970715, 1643035, 1183443, 1054189, 593805, 2, 34]
theorem checked56 : checkTrace blocks trace56=true := by decide +kernel
theorem old56 : phaseClean508 reference 3614=some 34 := by decide +kernel
theorem row56 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3614⟩=run reference n ⟨false,tbN_t8 3614⟩ := by
 have h:=trace_sound blocks 3614 [13829, 15379, 14867, 11273, 4755, 6350, 5779, 6619, 6547, 1683, 6350, 6291, 13843, 6655, 7635, 13843, 7639, 268695, 275987, 264083, 268750, 264083, 538131, 530866, 530898, 538131, 1970715, 1643035, 1183443, 1054189, 593805, 2, 34] checked56 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old56 n]
 rfl
def trace57 : List Nat := [12830, 3653, 3165, 3669, 7443, 3589, 30803, 28293, 14457, 12817, 60951, 63574, 62487, 36693, 47213, 47125, 20245, 47125, 47173, 52885, 39989, 47188, 48181, 53013, 63540, 63572, 52757, 20245, 413523, 1797019, 1732717, 223757, 1026, 131106]
theorem checked57 : checkTrace blocks trace57=true := by decide +kernel
theorem old57 : phaseClean508 reference 12830=some 131106 := by decide +kernel
theorem row57 (m n : List Bool) : run candidate m ⟨false,tbN_t8 12830⟩=run reference n ⟨false,tbN_t8 12830⟩ := by
 have h:=trace_sound blocks 12830 [3653, 3165, 3669, 7443, 3589, 30803, 28293, 14457, 12817, 60951, 63574, 62487, 36693, 47213, 47125, 20245, 47125, 47173, 52885, 39989, 47188, 48181, 53013, 63540, 63572, 52757, 20245, 413523, 1797019, 1732717, 223757, 1026, 131106] checked57 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old57 n]
 rfl
def trace58 : List Nat := [3869, 13836, 15408, 14896, 11332, 4784, 6850, 5808, 7128, 6576, 1712, 6850, 6320, 13872, 7144, 7664, 13872, 7668, 269288, 276016, 264112, 269250, 264112, 538160, 531344, 531344, 538160, 1970744, 1643064, 1183472, 1056239, 593423, 3, 35]
theorem checked58 : checkTrace blocks trace58=true := by decide +kernel
theorem old58 : phaseClean508 reference 3869=some 35 := by decide +kernel
theorem row58 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3869⟩=run reference n ⟨false,tbN_t8 3869⟩ := by
 have h:=trace_sound blocks 3869 [13836, 15408, 14896, 11332, 4784, 6850, 5808, 7128, 6576, 1712, 6850, 6320, 13872, 7144, 7664, 13872, 7668, 269288, 276016, 264112, 269250, 264112, 538160, 531344, 531344, 538160, 1970744, 1643064, 1183472, 1056239, 593423, 3, 35] checked58 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old58 n]
 rfl
def trace59 : List Nat := [3941, 12348, 3198, 3702, 7518, 3622, 31327, 28326, 14970, 12850, 60980, 64090, 62516, 36726, 47738, 47158, 20278, 47158, 47674, 52918, 39958, 47704, 48150, 53046, 64022, 64022, 52790, 20278, 413552, 1797048, 1734767, 224143, 1027, 131107]
theorem checked59 : checkTrace blocks trace59=true := by decide +kernel
theorem old59 : phaseClean508 reference 3941=some 131107 := by decide +kernel
theorem row59 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3941⟩=run reference n ⟨false,tbN_t8 3941⟩ := by
 have h:=trace_sound blocks 3941 [12348, 3198, 3702, 7518, 3622, 31327, 28326, 14970, 12850, 60980, 64090, 62516, 36726, 47738, 47158, 20278, 47158, 47674, 52918, 39958, 47704, 48150, 53046, 64022, 64022, 52790, 20278, 413552, 1797048, 1734767, 224143, 1027, 131107] checked59 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old59 n]
 rfl
def trace60 : List Nat := [3872, 2560, 1096, 1600, 5120, 10752, 10240, 2560, 10240, 10240, 2560, 10242, 8704, 2560, 10260, 142400, 51712, 10240, 10240, 19072, 14880, 534531, 530976, 281088, 272384, 272384, 269056, 791232, 1061568, 1851592, 217088, 217088, 0, 32]
theorem checked60 : checkTrace blocks trace60=true := by decide +kernel
theorem old60 : phaseClean508 reference 3872=some 32 := by decide +kernel
theorem row60 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3872⟩=run reference n ⟨false,tbN_t8 3872⟩ := by
 have h:=trace_sound blocks 3872 [2560, 1096, 1600, 5120, 10752, 10240, 2560, 10240, 10240, 2560, 10242, 8704, 2560, 10260, 142400, 51712, 10240, 10240, 19072, 14880, 534531, 530976, 281088, 272384, 272384, 269056, 791232, 1061568, 1851592, 217088, 217088, 0, 32] checked60 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old60 n]
 rfl
def trace61 : List Nat := [12576, 12866, 13320, 12808, 9248, 5768, 2213, 4744, 2448, 3480, 648, 2210, 648, 12808, 2484, 134600, 61960, 2440, 264584, 291464, 267176, 788899, 791464, 815624, 788872, 788872, 795400, 1183424, 601792, 1246408, 1049600, 1049600, 1024, 131104]
theorem checked61 : checkTrace blocks trace61=true := by decide +kernel
theorem old61 : phaseClean508 reference 12576=some 131104 := by decide +kernel
theorem row61 (m n : List Bool) : run candidate m ⟨false,tbN_t8 12576⟩=run reference n ⟨false,tbN_t8 12576⟩ := by
 have h:=trace_sound blocks 12576 [12866, 13320, 12808, 9248, 5768, 2213, 4744, 2448, 3480, 648, 2210, 648, 12808, 2484, 134600, 61960, 2440, 264584, 291464, 267176, 788899, 791464, 815624, 788872, 788872, 795400, 1183424, 601792, 1246408, 1049600, 1049600, 1024, 131104] checked61 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old61 n]
 rfl
def trace62 : List Nat := [4127, 11851, 11363, 11883, 15469, 11947, 15017, 3755, 15123, 15675, 6699, 14894, 12843, 11819, 15139, 146795, 60971, 14635, 277367, 290475, 278283, 801583, 794379, 814635, 801578, 801610, 802603, 1184483, 602851, 344299, 1726466, 1724802, 1, 33]
theorem checked62 : checkTrace blocks trace62=true := by decide +kernel
theorem old62 : phaseClean508 reference 4127=some 33 := by decide +kernel
theorem row62 (m n : List Bool) : run candidate m ⟨false,tbN_t8 4127⟩=run reference n ⟨false,tbN_t8 4127⟩ := by
 have h:=trace_sound blocks 4127 [11851, 11363, 11883, 15469, 11947, 15017, 3755, 15123, 15675, 6699, 14894, 12843, 11819, 15139, 146795, 60971, 14635, 277367, 290475, 278283, 801583, 794379, 814635, 801578, 801610, 802603, 1184483, 602851, 344299, 1726466, 1724802, 1, 33] checked62 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old62 n]
 rfl
def trace63 : List Nat := [4195, 5641, 7203, 6691, 3149, 4643, 6668, 5667, 6787, 6307, 4771, 6798, 4771, 5667, 6787, 138467, 54819, 6307, 6911, 22179, 5763, 531087, 530051, 284195, 268962, 268994, 263971, 790243, 1060579, 656619, 592898, 591234, 1025, 131105]
theorem checked63 : checkTrace blocks trace63=true := by decide +kernel
theorem old63 : phaseClean508 reference 4195=some 131105 := by decide +kernel
theorem row63 (m n : List Bool) : run candidate m ⟨false,tbN_t8 4195⟩=run reference n ⟨false,tbN_t8 4195⟩ := by
 have h:=trace_sound blocks 4195 [5641, 7203, 6691, 3149, 4643, 6668, 5667, 6787, 6307, 4771, 6798, 4771, 5667, 6787, 138467, 54819, 6307, 6911, 22179, 5763, 531087, 530051, 284195, 268962, 268994, 263971, 790243, 1060579, 656619, 592898, 591234, 1025, 131105] checked63 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old63 n]
 rfl
def trace64 : List Nat := [264, 16, 15878, 15878, 15896, 15046, 15514, 7878, 15750, 14790, 3782, 15513, 14534, 15942, 15790, 16326, 15942, 14786, 277970, 278086, 274374, 277912, 266182, 540230, 540071, 1588679, 1588806, 1320078, 525454, 1399438, 1332088, 868728, 49176, 49432]
theorem checked64 : checkTrace blocks trace64=true := by decide +kernel
theorem old64 : phaseClean508 reference 264=some 49432 := by decide +kernel
theorem row64 (m n : List Bool) : run candidate m ⟨false,tbN_t8 264⟩=run reference n ⟨false,tbN_t8 264⟩ := by
 have h:=trace_sound blocks 264 [16, 15878, 15878, 15896, 15046, 15514, 7878, 15750, 14790, 3782, 15513, 14534, 15942, 15790, 16326, 15942, 14786, 277970, 278086, 274374, 277912, 266182, 540230, 540071, 1588679, 1588806, 1320078, 525454, 1399438, 1332088, 868728, 49176, 49432] checked64 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old64 n]
 rfl
def trace65 : List Nat := [16136, 14418, 3654, 2638, 3640, 1614, 23615, 17998, 7182, 38990, 34382, 39993, 38990, 99918, 105486, 106062, 99918, 73262, 334962, 346062, 341102, 859195, 865390, 624206, 629807, 1678415, 1672782, 1887366, 982214, 2075142, 2011632, 2011576, 16408, 16664]
theorem checked65 : checkTrace blocks trace65=true := by decide +kernel
theorem old65 : phaseClean508 reference 16136=some 16664 := by decide +kernel
theorem row65 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16136⟩=run reference n ⟨false,tbN_t8 16136⟩ := by
 have h:=trace_sound blocks 16136 [14418, 3654, 2638, 3640, 1614, 23615, 17998, 7182, 38990, 34382, 39993, 38990, 99918, 105486, 106062, 99918, 73262, 334962, 346062, 341102, 859195, 865390, 624206, 629807, 1678415, 1672782, 1887366, 982214, 2075142, 2011632, 2011576, 16408, 16664] checked65 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old65 n]
 rfl
def trace66 : List Nat := [1027, 73, 37, 165, 213, 293, 790, 293, 16901, 16421, 293, 789, 293, 20645, 16953, 16997, 165, 17505, 279085, 262309, 287269, 279060, 287269, 524453, 524869, 524837, 524453, 1975469, 328877, 1596077, 1661818, 16634, 49177, 49433]
theorem checked66 : checkTrace blocks trace66=true := by decide +kernel
theorem old66 : phaseClean508 reference 1027=some 49433 := by decide +kernel
theorem row66 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1027⟩=run reference n ⟨false,tbN_t8 1027⟩ := by
 have h:=trace_sound blocks 1027 [73, 37, 165, 213, 293, 790, 293, 16901, 16421, 293, 789, 293, 20645, 16953, 16997, 165, 17505, 279085, 262309, 287269, 279060, 287269, 524453, 524869, 524837, 524453, 1975469, 328877, 1596077, 1661818, 16634, 49177, 49433] checked66 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old66 n]
 rfl
def trace67 : List Nat := [1151, 14347, 12389, 13549, 12533, 15789, 25523, 22957, 25485, 57773, 35245, 41909, 41389, 125101, 123801, 123885, 112813, 91021, 353165, 358701, 358797, 877495, 874893, 637101, 631757, 631725, 637101, 1494181, 261349, 1223205, 1292786, 1290298, 16409, 16665]
theorem checked67 : checkTrace blocks trace67=true := by decide +kernel
theorem old67 : phaseClean508 reference 1151=some 16665 := by decide +kernel
theorem row67 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1151⟩=run reference n ⟨false,tbN_t8 1151⟩ := by
 have h:=trace_sound blocks 1151 [14347, 12389, 13549, 12533, 15789, 25523, 22957, 25485, 57773, 35245, 41909, 41389, 125101, 123801, 123885, 112813, 91021, 353165, 358701, 358797, 877495, 874893, 637101, 631757, 631725, 637101, 1494181, 261349, 1223205, 1292786, 1290298, 16409, 16665] checked67 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old67 n]
 rfl
def trace68 : List Nat := [522, 23, 15903, 16031, 16315, 7119, 15870, 16207, 32243, 29659, 20447, 32254, 31199, 32543, 32243, 162719, 65503, 65471, 64947, 49119, 52703, 65022, 60895, 278495, 294303, 1342879, 1339359, 920031, 1183641, 922961, 853913, 1316317, 98322, 98578]
theorem checked68 : checkTrace blocks trace68=true := by decide +kernel
theorem old68 : phaseClean508 reference 522=some 98578 := by decide +kernel
theorem row68 (m n : List Bool) : run candidate m ⟨false,tbN_t8 522⟩=run reference n ⟨false,tbN_t8 522⟩ := by
 have h:=trace_sound blocks 522 [23, 15903, 16031, 16315, 7119, 15870, 16207, 32243, 29659, 20447, 32254, 31199, 32543, 32243, 162719, 65503, 65471, 64947, 49119, 52703, 65022, 60895, 278495, 294303, 1342879, 1339359, 920031, 1183641, 922961, 853913, 1316317, 98322, 98578] checked68 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old68 n]
 rfl
def trace69 : List Nat := [15882, 14423, 3665, 2777, 3745, 1881, 23907, 18265, 23633, 22617, 42843, 40294, 38235, 50777, 56417, 187993, 34521, 23165, 23649, 18265, 22137, 23652, 22137, 313049, 302105, 1350681, 1349593, 946393, 1341145, 287953, 484377, 1996381, 32786, 33042]
theorem checked69 : checkTrace blocks trace69=true := by decide +kernel
theorem old69 : phaseClean508 reference 15882=some 33042 := by decide +kernel
theorem row69 (m n : List Bool) : run candidate m ⟨false,tbN_t8 15882⟩=run reference n ⟨false,tbN_t8 15882⟩ := by
 have h:=trace_sound blocks 15882 [14423, 3665, 2777, 3745, 1881, 23907, 18265, 23633, 22617, 42843, 40294, 38235, 50777, 56417, 187993, 34521, 23165, 23649, 18265, 22137, 23652, 22137, 313049, 302105, 1350681, 1349593, 946393, 1341145, 287953, 484377, 1996381, 32786, 33042] checked69 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old69 n]
 rfl
def trace70 : List Nat := [1285, 15934, 60, 60, 374, 8236, 626, 8364, 624, 2616, 16444, 17010, 16444, 4604, 612, 132668, 49468, 33308, 33356, 33084, 32828, 33394, 32828, 262460, 279165, 279165, 282940, 264700, 2035642, 202098, 3995, 1643615, 98323, 98579]
theorem checked70 : checkTrace blocks trace70=true := by decide +kernel
theorem old70 : phaseClean508 reference 1285=some 98579 := by decide +kernel
theorem row70 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1285⟩=run reference n ⟨false,tbN_t8 1285⟩ := by
 have h:=trace_sound blocks 1285 [15934, 60, 60, 374, 8236, 626, 8364, 624, 2616, 16444, 17010, 16444, 4604, 612, 132668, 49468, 33308, 33356, 33084, 32828, 33394, 32828, 262460, 279165, 279165, 282940, 264700, 2035642, 202098, 3995, 1643615, 98323, 98579] checked70 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old70 n]
 rfl
def trace71 : List Nat := [1405, 14350, 12402, 13434, 12396, 15546, 25327, 22714, 9170, 8634, 43192, 41706, 44216, 43194, 41974, 173050, 47162, 10206, 9118, 31162, 7066, 9192, 15258, 325690, 304123, 304123, 305466, 291066, 1668858, 615666, 683035, 1275871, 32787, 33043]
theorem checked71 : checkTrace blocks trace71=true := by decide +kernel
theorem old71 : phaseClean508 reference 1405=some 33043 := by decide +kernel
theorem row71 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1405⟩=run reference n ⟨false,tbN_t8 1405⟩ := by
 have h:=trace_sound blocks 1405 [14350, 12402, 13434, 12396, 15546, 25327, 22714, 9170, 8634, 43192, 41706, 44216, 43194, 41974, 173050, 47162, 10206, 9118, 31162, 7066, 9192, 15258, 325690, 304123, 304123, 305466, 291066, 1668858, 615666, 683035, 1275871, 32787, 33043] checked71 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old71 n]
 rfl
def trace72 : List Nat := [1038, 15907, 15885, 15885, 15927, 15053, 15542, 7885, 15757, 47565, 11983, 15540, 13519, 77517, 81317, 81293, 130637, 81293, 343437, 360141, 344045, 343476, 335853, 605773, 605612, 605644, 605773, 2005573, 1485829, 907277, 901677, 1366025, 66566, 196646]
theorem checked72 : checkTrace blocks trace72=true := by decide +kernel
theorem old72 : phaseClean508 reference 1038=some 196646 := by decide +kernel
theorem row72 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1038⟩=run reference n ⟨false,tbN_t8 1038⟩ := by
 have h:=trace_sound blocks 1038 [15907, 15885, 15885, 15927, 15053, 15542, 7885, 15757, 47565, 11983, 15540, 13519, 77517, 81317, 81293, 130637, 81293, 343437, 360141, 344045, 343476, 335853, 605773, 605612, 605644, 605773, 2005573, 1485829, 907277, 901677, 1366025, 66566, 196646] checked72 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old72 n]
 rfl
def trace73 : List Nat := [15374, 1571, 3653, 2765, 3765, 1869, 23859, 18253, 23565, 55373, 34637, 40245, 39245, 120525, 121893, 121869, 100045, 88681, 89125, 83789, 87661, 89140, 87661, 116429, 105485, 1154061, 1152973, 718861, 256077, 326725, 517805, 2030729, 65542, 65574]
theorem checked73 : checkTrace blocks trace73=true := by decide +kernel
theorem old73 : phaseClean508 reference 15374=some 65574 := by decide +kernel
theorem row73 (m n : List Bool) : run candidate m ⟨false,tbN_t8 15374⟩=run reference n ⟨false,tbN_t8 15374⟩ := by
 have h:=trace_sound blocks 15374 [1571, 3653, 2765, 3765, 1869, 23859, 18253, 23565, 55373, 34637, 40245, 39245, 120525, 121893, 121869, 100045, 88681, 89125, 83789, 87661, 89140, 87661, 116429, 105485, 1154061, 1152973, 718861, 256077, 326725, 517805, 2030729, 65542, 65574] checked73 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old73 n]
 rfl
def trace74 : List Nat := [1801, 90, 15918, 15918, 15994, 15086, 16058, 7918, 16270, 47598, 12012, 16056, 13548, 77550, 81842, 81326, 130670, 81326, 344050, 360174, 344014, 343992, 335822, 605806, 606094, 606094, 605806, 2005606, 1485862, 907310, 903727, 1366411, 66567, 196647]
theorem checked74 : checkTrace blocks trace74=true := by decide +kernel
theorem old74 : phaseClean508 reference 1801=some 196647 := by decide +kernel
theorem row74 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1801⟩=run reference n ⟨false,tbN_t8 1801⟩ := by
 have h:=trace_sound blocks 1801 [90, 15918, 15918, 15994, 15086, 16058, 7918, 16270, 47598, 12012, 16056, 13548, 77550, 81842, 81326, 130670, 81326, 344050, 360174, 344014, 343992, 335822, 605806, 606094, 606094, 605806, 2005606, 1485862, 907310, 903727, 1366411, 66567, 196647] checked74 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old74 n]
 rfl
def trace75 : List Nat := [1913, 1658, 12390, 13422, 12408, 15534, 25279, 22702, 9102, 41390, 34990, 41657, 41134, 112686, 107442, 106926, 112686, 75722, 74714, 96686, 72590, 74680, 80782, 129070, 107503, 107503, 108846, 63534, 977006, 654438, 716463, 1309963, 65543, 65575]
theorem checked75 : checkTrace blocks trace75=true := by decide +kernel
theorem old75 : phaseClean508 reference 1913=some 65575 := by decide +kernel
theorem row75 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1913⟩=run reference n ⟨false,tbN_t8 1913⟩ := by
 have h:=trace_sound blocks 1913 [1658, 12390, 13422, 12408, 15534, 25279, 22702, 9102, 41390, 34990, 41657, 41134, 112686, 107442, 106926, 112686, 75722, 74714, 96686, 72590, 74680, 80782, 129070, 107503, 107503, 108846, 63534, 977006, 654438, 716463, 1309963, 65543, 65575] checked75 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old75 n]
 rfl
def trace76 : List Nat := [1296, 96, 586, 66, 520, 66, 1032, 66, 1026, 66, 66, 1033, 66, 66, 1046, 131138, 49218, 70, 1110, 16578, 4194, 1034, 4194, 262210, 263203, 1311811, 1310786, 931394, 603714, 1579594, 394100, 396112, 98320, 98576]
theorem checked76 : checkTrace blocks trace76=true := by decide +kernel
theorem old76 : phaseClean508 reference 1296=some 98576 := by decide +kernel
theorem row76 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1296⟩=run reference n ⟨false,tbN_t8 1296⟩ := by
 have h:=trace_sound blocks 1296 [96, 586, 66, 520, 66, 1032, 66, 1026, 66, 66, 1033, 66, 66, 1046, 131138, 49218, 70, 1110, 16578, 4194, 1034, 4194, 262210, 263203, 1311811, 1310786, 931394, 603714, 1579594, 394100, 396112, 98320, 98576] checked76 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old76 n]
 rfl
def trace77 : List Nat := [15120, 14370, 12810, 13322, 12840, 15562, 9389, 6346, 9618, 9690, 2250, 9385, 8394, 14410, 9654, 139722, 63562, 8654, 9694, 30922, 14826, 9642, 6634, 276554, 271787, 1320395, 1325130, 921162, 593482, 1329794, 1397108, 1399120, 32784, 33040]
theorem checked77 : checkTrace blocks trace77=true := by decide +kernel
theorem old77 : phaseClean508 reference 15120=some 33040 := by decide +kernel
theorem row77 (m n : List Bool) : run candidate m ⟨false,tbN_t8 15120⟩=run reference n ⟨false,tbN_t8 15120⟩ := by
 have h:=trace_sound blocks 15120 [14370, 12810, 13322, 12840, 15562, 9389, 6346, 9618, 9690, 2250, 9385, 8394, 14410, 9654, 139722, 63562, 8654, 9694, 30922, 14826, 9642, 6634, 276554, 271787, 1320395, 1325130, 921162, 593482, 1329794, 1397108, 1399120, 32784, 33040] checked77 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old77 n]
 rfl
def trace78 : List Nat := [2059, 2073, 15977, 14945, 11845, 4833, 7812, 5857, 8065, 6625, 1761, 7813, 6369, 13921, 8085, 7585, 13921, 6629, 8105, 13921, 2017, 8069, 2017, 13921, 8096, 8128, 13921, 13921, 13921, 1120873, 985974, 985810, 98321, 98577]
theorem checked78 : checkTrace blocks trace78=true := by decide +kernel
theorem old78 : phaseClean508 reference 2059=some 98577 := by decide +kernel
theorem row78 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2059⟩=run reference n ⟨false,tbN_t8 2059⟩ := by
 have h:=trace_sound blocks 2059 [2073, 15977, 14945, 11845, 4833, 7812, 5857, 8065, 6625, 1761, 7813, 6369, 13921, 8085, 7585, 13921, 6629, 8105, 13921, 2017, 8069, 2017, 13921, 8096, 8128, 13921, 13921, 13921, 1120873, 985974, 985810, 98321, 98577] checked78 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old78 n]
 rfl
def trace79 : List Nat := [2167, 12379, 3625, 3625, 7781, 11881, 15905, 3689, 15889, 15481, 3689, 15909, 14441, 3689, 15925, 15401, 3689, 14445, 15905, 3689, 11881, 15909, 3689, 3689, 15912, 15944, 3689, 3689, 3689, 1919649, 1857910, 1857746, 32785, 33041]
theorem checked79 : checkTrace blocks trace79=true := by decide +kernel
theorem old79 : phaseClean508 reference 2167=some 33041 := by decide +kernel
theorem row79 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2167⟩=run reference n ⟨false,tbN_t8 2167⟩ := by
 have h:=trace_sound blocks 2167 [12379, 3625, 3625, 7781, 11881, 15905, 3689, 15889, 15481, 3689, 15909, 14441, 3689, 15925, 15401, 3689, 14445, 15905, 3689, 11881, 15909, 3689, 3689, 15912, 15944, 3689, 3689, 3689, 1919649, 1857910, 1857746, 32785, 33041] checked79 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old79 n]
 rfl
def trace80 : List Nat := [2575, 13933, 15997, 14965, 11857, 4853, 7892, 5877, 8157, 39413, 9975, 7894, 5367, 75509, 73681, 204789, 79477, 72177, 335853, 341621, 329717, 335829, 329717, 865909, 860084, 860116, 865909, 1743549, 953597, 1218101, 1019842, 1017350, 66565, 196645]
theorem checked80 : checkTrace blocks trace80=true := by decide +kernel
theorem old80 : phaseClean508 reference 2575=some 196645 := by decide +kernel
theorem row80 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2575⟩=run reference n ⟨false,tbN_t8 2575⟩ := by
 have h:=trace_sound blocks 2575 [13933, 15997, 14965, 11857, 4853, 7892, 5877, 8157, 39413, 9975, 7894, 5367, 75509, 73681, 204789, 79477, 72177, 335853, 341621, 329717, 335829, 329717, 865909, 860084, 860116, 865909, 1743549, 953597, 1218101, 1019842, 1017350, 66565, 196645] checked80 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old80 n]
 rfl
def trace81 : List Nat := [2675, 3631, 3645, 3645, 7793, 11901, 15985, 3709, 15949, 48237, 11903, 15990, 13439, 73469, 81521, 212605, 69245, 79993, 81509, 69245, 77437, 81525, 69245, 331389, 343612, 343644, 331389, 296637, 1544445, 1954357, 1891266, 1888774, 65541, 65573]
theorem checked81 : checkTrace blocks trace81=true := by decide +kernel
theorem old81 : phaseClean508 reference 2675=some 65573 := by decide +kernel
theorem row81 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2675⟩=run reference n ⟨false,tbN_t8 2675⟩ := by
 have h:=trace_sound blocks 2675 [3631, 3645, 3645, 7793, 11901, 15985, 3709, 15949, 48237, 11903, 15990, 13439, 73469, 81521, 212605, 69245, 79993, 81509, 69245, 77437, 81525, 69245, 331389, 343612, 343644, 331389, 296637, 1544445, 1954357, 1891266, 1888774, 65541, 65573] checked81 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old81 n]
 rfl
def trace82 : List Nat := [268, 15974, 15896, 15896, 16166, 6856, 15584, 15944, 15860, 13276, 20184, 31970, 30936, 12184, 15836, 14808, 16216, 49080, 48564, 65496, 49144, 48610, 40952, 16216, 32249, 32249, 28504, 16216, 465182, 868638, 868638, 1331892, 81940, 82196]
theorem checked82 : checkTrace blocks trace82=true := by decide +kernel
theorem old82 : phaseClean508 reference 268=some 82196 := by decide +kernel
theorem row82 (m n : List Bool) : run candidate m ⟨false,tbN_t8 268⟩=run reference n ⟨false,tbN_t8 268⟩ := by
 have h:=trace_sound blocks 268 [15974, 15896, 15896, 16166, 6856, 15584, 15944, 15860, 13276, 20184, 31970, 30936, 12184, 15836, 14808, 16216, 49080, 48564, 65496, 49144, 48610, 40952, 16216, 32249, 32249, 28504, 16216, 465182, 868638, 868638, 1331892, 81940, 82196] checked82 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old82 n]
 rfl
def trace83 : List Nat := [16140, 1572, 3672, 2640, 3846, 9792, 7237, 9920, 7268, 5700, 18000, 23618, 22608, 6032, 7292, 6224, 1872, 40496, 39996, 51152, 38512, 40002, 38512, 1872, 23665, 23665, 22352, 1872, 467222, 70102, 1970974, 458932, 16404, 16660]
theorem checked83 : checkTrace blocks trace83=true := by decide +kernel
theorem old83 : phaseClean508 reference 16140=some 16660 := by decide +kernel
theorem row83 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16140⟩=run reference n ⟨false,tbN_t8 16140⟩ := by
 have h:=trace_sound blocks 16140 [1572, 3672, 2640, 3846, 9792, 7237, 9920, 7268, 5700, 18000, 23618, 22608, 6032, 7292, 6224, 1872, 40496, 39996, 51152, 38512, 40002, 38512, 1872, 23665, 23665, 22352, 1872, 467222, 70102, 1970974, 458932, 16404, 16660] checked83 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old83 n]
 rfl
def trace84 : List Nat := [1539, 79, 59, 187, 491, 8491, 876, 8619, 17015, 19007, 16699, 17262, 16699, 16763, 16971, 17531, 443, 49691, 49739, 49467, 61979, 49774, 61979, 443, 16923, 1065499, 1069499, 671611, 661821, 16701, 18716, 1659702, 81941, 82197]
theorem checked84 : checkTrace blocks trace84=true := by decide +kernel
theorem old84 : phaseClean508 reference 1539=some 82197 := by decide +kernel
theorem row84 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1539⟩=run reference n ⟨false,tbN_t8 1539⟩ := by
 have h:=trace_sound blocks 1539 [79, 59, 187, 491, 8491, 876, 8619, 17015, 19007, 16699, 17262, 16699, 16763, 16971, 17531, 443, 49691, 49739, 49467, 61979, 49774, 61979, 443, 16923, 1065499, 1069499, 671611, 661821, 16701, 18716, 1659702, 81941, 82197] checked84 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old84 n]
 rfl
def trace85 : List Nat := [1663, 14349, 12411, 13555, 12747, 7587, 9161, 14627, 25575, 28583, 18867, 25550, 25011, 31091, 25579, 26099, 14771, 58259, 58307, 63795, 56211, 58318, 64403, 14771, 25491, 1074067, 1075635, 657267, 663861, 791029, 1252124, 655670, 16405, 16661]
theorem checked85 : checkTrace blocks trace85=true := by decide +kernel
theorem old85 : phaseClean508 reference 1663=some 16661 := by decide +kernel
theorem row85 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1663⟩=run reference n ⟨false,tbN_t8 1663⟩ := by
 have h:=trace_sound blocks 1663 [14349, 12411, 13555, 12747, 7587, 9161, 14627, 25575, 28583, 18867, 25550, 25011, 31091, 25579, 26099, 14771, 58259, 58307, 63795, 56211, 58318, 64403, 14771, 25491, 1074067, 1075635, 657267, 663861, 791029, 1252124, 655670, 16405, 16661] checked85 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old85 n]
 rfl
def trace86 : List Nat := [1797, 15932, 54, 54, 92, 54, 600, 54, 606, 32822, 8244, 602, 3124, 69814, 66130, 66166, 114742, 66674, 66158, 82102, 69654, 66136, 69654, 65590, 66103, 1114711, 1114166, 704246, 2009270, 1606334, 1677641, 35655, 33803, 163883]
theorem checked86 : checkTrace blocks trace86=true := by decide +kernel
theorem old86 : phaseClean508 reference 1797=some 163883 := by decide +kernel
theorem row86 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1797⟩=run reference n ⟨false,tbN_t8 1797⟩ := by
 have h:=trace_sound blocks 1797 [15932, 54, 54, 92, 54, 600, 54, 606, 32822, 8244, 602, 3124, 69814, 66130, 66166, 114742, 66674, 66158, 82102, 69654, 66136, 69654, 65590, 66103, 1114711, 1114166, 704246, 2009270, 1606334, 1677641, 35655, 33803, 163883] checked86 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old86 n]
 rfl
def trace87 : List Nat := [1917, 14348, 12408, 13424, 12614, 7328, 8901, 14368, 9188, 12196, 18608, 25282, 24752, 10736, 9152, 10160, 14640, 42964, 41876, 63920, 47504, 41921, 39312, 14640, 25585, 25585, 26928, 14640, 466806, 1132406, 1268809, 675399, 32779, 32811]
theorem checked87 : checkTrace blocks trace87=true := by decide +kernel
theorem old87 : phaseClean508 reference 1917=some 32811 := by decide +kernel
theorem row87 (m n : List Bool) : run candidate m ⟨false,tbN_t8 1917⟩=run reference n ⟨false,tbN_t8 1917⟩ := by
 have h:=trace_sound blocks 1917 [14348, 12408, 13424, 12614, 7328, 8901, 14368, 9188, 12196, 18608, 25282, 24752, 10736, 9152, 10160, 14640, 42964, 41876, 63920, 47504, 41921, 39312, 14640, 25585, 25585, 26928, 14640, 466806, 1132406, 1268809, 675399, 32779, 32811] checked87 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old87 n]
 rfl
def trace88 : List Nat := [2055, 13947, 97, 1257, 4327, 10537, 8996, 2345, 25097, 24617, 2345, 8997, 8489, 22697, 25141, 24617, 2217, 25709, 25121, 2217, 18985, 25125, 27177, 2217, 8808, 8808, 2217, 2217, 1845417, 1704609, 1775958, 1775858, 49169, 49425]
theorem checked88 : checkTrace blocks trace88=true := by decide +kernel
theorem old88 : phaseClean508 reference 2055=some 49425 := by decide +kernel
theorem row88 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2055⟩=run reference n ⟨false,tbN_t8 2055⟩ := by
 have h:=trace_sound blocks 2055 [13947, 97, 1257, 4327, 10537, 8996, 2345, 25097, 24617, 2345, 8997, 8489, 22697, 25141, 24617, 2217, 25709, 25121, 2217, 18985, 25125, 27177, 2217, 8808, 8808, 2217, 2217, 1845417, 1704609, 1775958, 1775858, 49169, 49425] checked88 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old88 n]
 rfl
def trace89 : List Nat := [2171, 3641, 12321, 12449, 8391, 5537, 897, 4513, 17305, 17841, 417, 901, 417, 24737, 17301, 16801, 12449, 17893, 17321, 12449, 25505, 17285, 25505, 12449, 992, 992, 12449, 12449, 1839265, 1462889, 543574, 543474, 114705, 114961]
theorem checked89 : checkTrace blocks trace89=true := by decide +kernel
theorem old89 : phaseClean508 reference 2171=some 114961 := by decide +kernel
theorem row89 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2171⟩=run reference n ⟨false,tbN_t8 2171⟩ := by
 have h:=trace_sound blocks 2171 [3641, 12321, 12449, 8391, 5537, 897, 4513, 17305, 17841, 417, 901, 417, 24737, 17301, 16801, 12449, 17893, 17321, 12449, 25505, 17285, 25505, 12449, 992, 992, 12449, 12449, 1839265, 1462889, 543574, 543474, 114705, 114961] checked89 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old89 n]
 rfl
def trace90 : List Nat := [2051, 2057, 107, 1251, 4301, 10531, 8972, 2339, 25091, 24611, 2339, 8972, 8483, 22691, 25111, 24611, 2211, 25703, 25131, 2211, 18979, 25101, 27171, 2211, 8802, 8802, 2211, 2211, 1845411, 1704619, 1775964, 131890, 81937, 82193]
theorem checked90 : checkTrace blocks trace90=true := by decide +kernel
theorem old90 : phaseClean508 reference 2051=some 82193 := by decide +kernel
theorem row90 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2051⟩=run reference n ⟨false,tbN_t8 2051⟩ := by
 have h:=trace_sound blocks 2051 [2057, 107, 1251, 4301, 10531, 8972, 2339, 25091, 24611, 2339, 8972, 8483, 22691, 25111, 24611, 2211, 25703, 25131, 2211, 18979, 25101, 27171, 2211, 8802, 8802, 2211, 2211, 1845411, 1704619, 1775964, 131890, 81937, 82193] checked90 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old90 n]
 rfl
def trace91 : List Nat := [2175, 12363, 12331, 12459, 8429, 5547, 937, 4523, 17299, 17851, 427, 940, 427, 24747, 17335, 16811, 12459, 17903, 17315, 12459, 25515, 17325, 25515, 12459, 1002, 1002, 12459, 12459, 1839275, 1462883, 543580, 1134898, 16401, 16657]
theorem checked91 : checkTrace blocks trace91=true := by decide +kernel
theorem old91 : phaseClean508 reference 2175=some 16657 := by decide +kernel
theorem row91 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2175⟩=run reference n ⟨false,tbN_t8 2175⟩ := by
 have h:=trace_sound blocks 2175 [12363, 12331, 12459, 8429, 5547, 937, 4523, 17299, 17851, 427, 940, 427, 24747, 17335, 16811, 12459, 17903, 17315, 12459, 25515, 17325, 25515, 12459, 1002, 1002, 12459, 12459, 1839275, 1462883, 543580, 1134898, 16401, 16657] checked91 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old91 n]
 rfl
def trace92 : List Nat := [2309, 13950, 118, 1150, 4478, 2094, 8826, 10414, 8818, 10810, 18494, 25211, 90174, 2430, 8806, 140862, 133438, 173658, 172570, 182718, 178206, 172664, 170014, 411966, 418334, 418334, 411710, 328190, 77624, 1727280, 1792743, 1792847, 33795, 163875]
theorem checked92 : checkTrace blocks trace92=true := by decide +kernel
theorem old92 : phaseClean508 reference 2309=some 163875 := by decide +kernel
theorem row92 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2309⟩=run reference n ⟨false,tbN_t8 2309⟩ := by
 have h:=trace_sound blocks 2309 [13950, 118, 1150, 4478, 2094, 8826, 10414, 8818, 10810, 18494, 25211, 90174, 2430, 8806, 140862, 133438, 173658, 172570, 182718, 178206, 172664, 170014, 411966, 418334, 418334, 411710, 328190, 77624, 1727280, 1792743, 1792847, 33795, 163875] checked92 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old92 n]
 rfl
def trace93 : List Nat := [2429, 12366, 12344, 12344, 8292, 5304, 17127, 20664, 976, 440, 41146, 33507, 101562, 45112, 33780, 164856, 159800, 131992, 394184, 405816, 402360, 394210, 402360, 962616, 951192, 951192, 962616, 1793264, 1995376, 1261176, 1130343, 1130191, 32771, 32803]
theorem checked93 : checkTrace blocks trace93=true := by decide +kernel
theorem old93 : phaseClean508 reference 2429=some 32803 := by decide +kernel
theorem row93 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2429⟩=run reference n ⟨false,tbN_t8 2429⟩ := by
 have h:=trace_sound blocks 2429 [12366, 12344, 12344, 8292, 5304, 17127, 20664, 976, 440, 41146, 33507, 101562, 45112, 33780, 164856, 159800, 131992, 394184, 405816, 402360, 394210, 402360, 962616, 951192, 951192, 962616, 1793264, 1995376, 1261176, 1130343, 1130191, 32771, 32803] checked93 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old93 n]
 rfl
def trace94 : List Nat := [2567, 13949, 127, 1271, 4313, 10551, 9052, 2359, 25183, 57399, 10549, 9055, 77109, 88247, 90747, 90167, 198839, 222323, 221807, 198839, 215607, 221789, 223799, 215223, 205366, 205398, 203191, 100535, 898679, 1874559, 166752, 166694, 81925, 81957]
theorem checked94 : checkTrace blocks trace94=true := by decide +kernel
theorem old94 : phaseClean508 reference 2567=some 81957 := by decide +kernel
theorem row94 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2567⟩=run reference n ⟨false,tbN_t8 2567⟩ := by
 have h:=trace_sound blocks 2567 [13949, 127, 1271, 4313, 10551, 9052, 2359, 25183, 57399, 10549, 9055, 77109, 88247, 90747, 90167, 198839, 222323, 221807, 198839, 215607, 221789, 223799, 215223, 205366, 205398, 203191, 100535, 898679, 1874559, 166752, 166694, 81925, 81957] checked94 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old94 n]
 rfl
def trace95 : List Nat := [2683, 3647, 12351, 12479, 8441, 5567, 1017, 4543, 17359, 50607, 8637, 1023, 69053, 90303, 82907, 82367, 209087, 214523, 476135, 471231, 484287, 476157, 484287, 749759, 721854, 721886, 729535, 2069687, 1354359, 1302143, 1171296, 1171238, 82949, 213029]
theorem checked95 : checkTrace blocks trace95=true := by decide +kernel
theorem old95 : phaseClean508 reference 2683=some 213029 := by decide +kernel
theorem row95 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2683⟩=run reference n ⟨false,tbN_t8 2683⟩ := by
 have h:=trace_sound blocks 2683 [3647, 12351, 12479, 8441, 5567, 1017, 4543, 17359, 50607, 8637, 1023, 69053, 90303, 82907, 82367, 209087, 214523, 476135, 471231, 484287, 476157, 484287, 749759, 721854, 721886, 729535, 2069687, 1354359, 1302143, 1171296, 1171238, 82949, 213029] checked95 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old95 n]
 rfl
def trace96 : List Nat := [2563, 2063, 117, 1277, 4595, 2349, 9078, 10669, 25201, 27193, 18749, 25463, 90429, 23037, 25165, 25725, 182717, 190041, 188953, 166333, 182845, 189045, 191037, 149949, 156284, 156284, 149693, 68029, 337787, 2037691, 134732, 1774638, 17421, 147501]
theorem checked96 : checkTrace blocks trace96=true := by decide +kernel
theorem old96 : phaseClean508 reference 2563=some 147501 := by decide +kernel
theorem row96 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2563⟩=run reference n ⟨false,tbN_t8 2563⟩ := by
 have h:=trace_sound blocks 2563 [2063, 117, 1277, 4595, 2349, 9078, 10669, 25201, 27193, 18749, 25463, 90429, 23037, 25165, 25725, 182717, 190041, 188953, 166333, 182845, 189045, 191037, 149949, 156284, 156284, 149693, 68029, 337787, 2037691, 134732, 1774638, 17421, 147501] checked96 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old96 n]
 rfl
def trace97 : List Nat := [2687, 12365, 12341, 12469, 8659, 13733, 17363, 28965, 17401, 19377, 57783, 50134, 52663, 57845, 50157, 50677, 29109, 49589, 50105, 61493, 53653, 50134, 53653, 61877, 50164, 50164, 61621, 29109, 1724915, 1078075, 1145548, 549038, 16397, 16429]
theorem checked97 : checkTrace blocks trace97=true := by decide +kernel
theorem old97 : phaseClean508 reference 2687=some 16429 := by decide +kernel
theorem row97 (m n : List Bool) : run candidate m ⟨false,tbN_t8 2687⟩=run reference n ⟨false,tbN_t8 2687⟩ := by
 have h:=trace_sound blocks 2687 [12365, 12341, 12469, 8659, 13733, 17363, 28965, 17401, 19377, 57783, 50134, 52663, 57845, 50157, 50677, 29109, 49589, 50105, 61493, 53653, 50134, 53653, 61877, 50164, 50164, 61621, 29109, 1724915, 1078075, 1145548, 549038, 16397, 16429] checked97 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old97 n]
 rfl
def trace98 : List Nat := [3075, 2121, 109, 1125, 4181, 10277, 8726, 2085, 8709, 8229, 2085, 8725, 8229, 2085, 8761, 8805, 2085, 8229, 8825, 2085, 10277, 8725, 2085, 2085, 8709, 1057285, 1050661, 669413, 1119973, 480301, 1793548, 148522, 17417, 147497]
theorem checked98 : checkTrace blocks trace98=true := by decide +kernel
theorem old98 : phaseClean508 reference 3075=some 147497 := by decide +kernel
theorem row98 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3075⟩=run reference n ⟨false,tbN_t8 3075⟩ := by
 have h:=trace_sound blocks 3075 [2121, 109, 1125, 4181, 10277, 8726, 2085, 8709, 8229, 2085, 8725, 8229, 2085, 8761, 8805, 2085, 8229, 8825, 2085, 10277, 8725, 2085, 2085, 8709, 1057285, 1050661, 669413, 1119973, 480301, 1793548, 148522, 17417, 147497] checked98 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old98 n]
 rfl
def trace99 : List Nat := [3199, 12299, 12333, 12333, 8309, 5293, 17075, 20653, 909, 33197, 32941, 33461, 32941, 110637, 99225, 99309, 110637, 67529, 66521, 94637, 78733, 66486, 78733, 127021, 99277, 99245, 106797, 61485, 974957, 569517, 567948, 1159338, 16393, 16425]
theorem checked99 : checkTrace blocks trace99=true := by decide +kernel
theorem old99 : phaseClean508 reference 3199=some 16425 := by decide +kernel
theorem row99 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3199⟩=run reference n ⟨false,tbN_t8 3199⟩ := by
 have h:=trace_sound blocks 3199 [12299, 12333, 12333, 8309, 5293, 17075, 20653, 909, 33197, 32941, 33461, 32941, 110637, 99225, 99309, 110637, 67529, 66521, 94637, 78733, 66486, 78733, 127021, 99277, 99245, 106797, 61485, 974957, 569517, 567948, 1159338, 16393, 16425] checked99 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old99 n]
 rfl
def trace100 : List Nat := [3587, 2127, 115, 1147, 4459, 2091, 8812, 10411, 8823, 10815, 18491, 25198, 24635, 6651, 8779, 9339, 2363, 42591, 41503, 51643, 47131, 565871, 563227, 18747, 25115, 1073691, 1067067, 141307, 1974717, 1658749, 1793122, 1791398, 17413, 147493]
theorem checked100 : checkTrace blocks trace100=true := by decide +kernel
theorem old100 : phaseClean508 reference 3587=some 147493 := by decide +kernel
theorem row100 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3587⟩=run reference n ⟨false,tbN_t8 3587⟩ := by
 have h:=trace_sound blocks 3587 [2127, 115, 1147, 4459, 2091, 8812, 10411, 8823, 10815, 18491, 25198, 24635, 6651, 8779, 9339, 2363, 42591, 41503, 51643, 47131, 565871, 563227, 18747, 25115, 1073691, 1067067, 141307, 1974717, 1658749, 1793122, 1791398, 17413, 147493] checked100 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old100 n]
 rfl
def trace101 : List Nat := [3711, 12301, 12339, 12339, 8523, 13475, 713, 12323, 999, 4007, 16563, 17102, 16563, 8691, 1003, 1523, 12595, 34775, 295831, 324019, 299411, 820175, 823699, 553267, 541587, 1590163, 1601587, 1850363, 474557, 1444733, 526434, 524710, 16389, 16421]
theorem checked101 : checkTrace blocks trace101=true := by decide +kernel
theorem old101 : phaseClean508 reference 3711=some 16421 := by decide +kernel
theorem row101 (m n : List Bool) : run candidate m ⟨false,tbN_t8 3711⟩=run reference n ⟨false,tbN_t8 3711⟩ := by
 have h:=trace_sound blocks 3711 [12301, 12339, 12339, 8523, 13475, 713, 12323, 999, 4007, 16563, 17102, 16563, 8691, 1003, 1523, 12595, 34775, 295831, 324019, 299411, 820175, 823699, 553267, 541587, 1590163, 1601587, 1850363, 474557, 1444733, 526434, 524710, 16389, 16421] checked101 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old101 n]
 rfl
def trace102 : List Nat := [4099, 4105, 4131, 4131, 79, 5155, 521, 4131, 667, 1203, 5283, 654, 2723, 4131, 703, 739, 4131, 163, 767, 4131, 163, 652, 163, 4131, 738, 738, 4131, 4131, 4131, 724203, 527394, 525730, 17409, 147489]
theorem checked102 : checkTrace blocks trace102=true := by decide +kernel
theorem old102 : phaseClean508 reference 4099=some 147489 := by decide +kernel
theorem row102 (m n : List Bool) : run candidate m ⟨false,tbN_t8 4099⟩=run reference n ⟨false,tbN_t8 4099⟩ := by
 have h:=trace_sound blocks 4099 [4105, 4131, 4131, 79, 5155, 521, 4131, 667, 1203, 5283, 654, 2723, 4131, 703, 739, 4131, 163, 767, 4131, 163, 652, 163, 4131, 738, 738, 4131, 4131, 4131, 724203, 527394, 525730, 17409, 147489] checked102 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old102 n]
 rfl
def trace103 : List Nat := [4223, 10315, 8291, 9323, 12399, 10411, 8876, 2219, 8971, 8491, 7211, 8750, 10795, 10283, 8991, 9067, 10283, 8491, 271223, 272427, 272683, 271148, 264491, 534571, 533354, 533354, 534571, 1969187, 1641507, 280811, 1792034, 1790370, 16385, 16417]
theorem checked103 : checkTrace blocks trace103=true := by decide +kernel
theorem old103 : phaseClean508 reference 4223=some 16417 := by decide +kernel
theorem row103 (m n : List Bool) : run candidate m ⟨false,tbN_t8 4223⟩=run reference n ⟨false,tbN_t8 4223⟩ := by
 have h:=trace_sound blocks 4223 [10315, 8291, 9323, 12399, 10411, 8876, 2219, 8971, 8491, 7211, 8750, 10795, 10283, 8991, 9067, 10283, 8491, 271223, 272427, 272683, 271148, 264491, 534571, 533354, 533354, 534571, 1969187, 1641507, 280811, 1792034, 1790370, 16385, 16417] checked103 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old103 n]
 rfl
end ECDSAAdd.Entrant.CompactForward11

-- Verified CompactForwardFinal
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.CompactForward11
open Arithmetic MappedCompressed Secp256k1 History5 CompactCertificates
attribute [local irreducible] run candidate reference Forward11Width.candidate MorningFour.forward13
def rowInputs : List Nat := [2,2,257,257,260,16132,515,639,518,15878,773,893,776,15624,1031,1147,1034,15370,1289,1401,1292,15116,1547,1655,1550,14862,1805,1909,1808,14608,2063,2163,2066,14354,2321,2417,2324,14100,2579,2671,2582,13846,2837,2925,2840,13592,3095,3179,3098,13338,3353,3433,3356,13084,3611,3687,3614,12830,3869,3941,3872,12576,4127,4195,264,16136,1027,1151,522,15882,1285,1405,1038,15374,1801,1913,1296,15120,2059,2167,2575,2675,268,16140,1539,1663,1797,1917,2055,2171,2051,2175,2309,2429,2567,2683,2563,2687,3075,3199,3587,3711,4099,4223]
theorem allRows (b : Nat) (h : b∈rowInputs) (m n : List Bool) :
 run candidate m ⟨false,tbN_t8 b⟩=run reference n ⟨false,tbN_t8 b⟩ := by
 simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at h
 rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact row0 m n
 · exact row1 m n
 · exact row2 m n
 · exact row3 m n
 · exact row4 m n
 · exact row5 m n
 · exact row6 m n
 · exact row7 m n
 · exact row8 m n
 · exact row9 m n
 · exact row10 m n
 · exact row11 m n
 · exact row12 m n
 · exact row13 m n
 · exact row14 m n
 · exact row15 m n
 · exact row16 m n
 · exact row17 m n
 · exact row18 m n
 · exact row19 m n
 · exact row20 m n
 · exact row21 m n
 · exact row22 m n
 · exact row23 m n
 · exact row24 m n
 · exact row25 m n
 · exact row26 m n
 · exact row27 m n
 · exact row28 m n
 · exact row29 m n
 · exact row30 m n
 · exact row31 m n
 · exact row32 m n
 · exact row33 m n
 · exact row34 m n
 · exact row35 m n
 · exact row36 m n
 · exact row37 m n
 · exact row38 m n
 · exact row39 m n
 · exact row40 m n
 · exact row41 m n
 · exact row42 m n
 · exact row43 m n
 · exact row44 m n
 · exact row45 m n
 · exact row46 m n
 · exact row47 m n
 · exact row48 m n
 · exact row49 m n
 · exact row50 m n
 · exact row51 m n
 · exact row52 m n
 · exact row53 m n
 · exact row54 m n
 · exact row55 m n
 · exact row56 m n
 · exact row57 m n
 · exact row58 m n
 · exact row59 m n
 · exact row60 m n
 · exact row61 m n
 · exact row62 m n
 · exact row63 m n
 · exact row64 m n
 · exact row65 m n
 · exact row66 m n
 · exact row67 m n
 · exact row68 m n
 · exact row69 m n
 · exact row70 m n
 · exact row71 m n
 · exact row72 m n
 · exact row73 m n
 · exact row74 m n
 · exact row75 m n
 · exact row76 m n
 · exact row77 m n
 · exact row78 m n
 · exact row79 m n
 · exact row80 m n
 · exact row81 m n
 · exact row82 m n
 · exact row83 m n
 · exact row84 m n
 · exact row85 m n
 · exact row86 m n
 · exact row87 m n
 · exact row88 m n
 · exact row89 m n
 · exact row90 m n
 · exact row91 m n
 · exact row92 m n
 · exact row93 m n
 · exact row94 m n
 · exact row95 m n
 · exact row96 m n
 · exact row97 m n
 · exact row98 m n
 · exact row99 m n
 · exact row100 m n
 · exact row101 m n
 · exact row102 m n
 · exact row103 m n
def localSites : List Wire := List.range 22
def encodedInput (g s : Bool) (uv : Nat×Nat) : Nat :=
 encN_t8 (fun q=>MorningFour.pre507 g s uv.1 uv.2 (perm q)) localSites
def checkInput (uv : Nat×Nat) : Bool :=
 [false,true].all fun g=>[false,true].all fun s=>
  if Forward11Width.legal uv g then decide (encodedInput g s uv∈rowInputs) else true
theorem inputTable : MorningFour.pairs.all checkInput=true := by decide +kernel
theorem sitesTable : MorningFour.sites.all (fun q=>decide (perm.symm q < 22))=true := by decide +kernel
theorem sample_run (g s : Bool) (uv : Nat×Nat) (h : uv∈MorningFour.pairs)
 (hl : Forward11Width.legal uv g=true) (m n : List Bool) :
 run Forward11Width.candidate m ⟨false,MorningFour.pre507 g s uv.1 uv.2⟩=
 run MorningFour.forward13 n ⟨false,MorningFour.pre507 g s uv.1 uv.2⟩ := by
 have ht:=inputTable
 simp only [List.all_eq_true] at ht
 have row:=ht uv h
 simp only [checkInput,List.all_eq_true] at row
 have mem:=row g (by cases g <;> simp) s (by cases s <;> simp)
 simp only [hl,if_true,decide_eq_true_eq] at mem
 have supp : ∀q : Wire,MorningFour.pre507 g s uv.1 uv.2 (perm q)=true → q∈localSites := by
  intro q yes
  have hg : perm q∈MorningFour.sites := by
   by_contra no
   rw [MorningFour.pre_supp g s uv.1 uv.2 (perm q) no] at yes
   contradiction
  have tab:=sitesTable
  simp only [List.all_eq_true,decide_eq_true_eq] at tab
  have z:=tab (perm q) hg
  simpa only [localSites,List.mem_range,Equiv.symm_apply_apply] using z
 apply pull_injective perm
 rewrite [←placement,←reference_placement,ECDSAAdd.run_rename perm perm.injective,
  ECDSAAdd.run_rename perm perm.injective]
 dsimp only [pullState]
 rewrite [tb_enc_t8 _ localSites supp]
 have hh:=allRows (encodedInput g s uv) mem m n
 dsimp only [encodedInput] at hh
 exact hh
end ECDSAAdd.Entrant.CompactForward11

-- Verified CompactForwardBridge
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.Forward11Width
open Arithmetic MappedCompressed Secp256k1 History5
attribute [local irreducible] run candidate MorningFour.forward13
theorem on_site (g s : Bool) (uv : Nat × Nat) (mem : uv∈MorningFour.pairs)
 (hl : legal uv g=true) (st : State)
 (bits : ∀q∈MorningFour.sites,st.basis q=MorningFour.pre507 g s uv.1 uv.2 q)
 (m n : List Bool) : run candidate m st=run MorningFour.forward13 n st := by
 apply Stack5.local_replace candidate MorningFour.forward13 MorningFour.sites.toFinset
  support_all MorningFour.support.1 st ⟨false,MorningFour.pre507 g s uv.1 uv.2⟩ m n
 · intro q hq
   exact bits q (List.mem_toFinset.mp hq)
 · exact CompactForward11.sample_run g s uv mem hl m n
end ECDSAAdd.Entrant.Forward11Width

end -- compact forward proof scope
namespace ECDSAAdd.Entrant.MorningPlacement
open Arithmetic MappedCompressed Secp256k1 History5 OB5 Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000

def prior : Program := renameProgram (sig 507) MorningFour.tick507 ++ ForwardSixPlacement.prior
def merged : Program := renameProgram (sig 510) Forward11Width.candidate

theorem prior_resources : toffoliCount merged+5=toffoliCount prior ∧
    measurementCount merged=measurementCount prior ∧ Challenge.gateSlots merged ≤ Challenge.gateSlots prior+975 := by
  have fresh:=Forward11Width.resources
  have old : toffoliCount prior=16 ∧ measurementCount prior=14 ∧ 236≤Challenge.gateSlots prior := by decide +kernel
  simp only [merged,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem prior_support : wires merged ⊆ wires prior := by
  have cells : ((MorningFour.sites.toFinset.erase 1559).image (sig 510))⊆wires prior := by decide +kernel
  rw [merged,renameProgram_support]
  exact (Finset.image_mono (sig 510) Forward11Width.support).trans cells

theorem pack507 (isA : Bool) : Rolling1588.Integer.packAfter base isA 507=[] := by
  simp only [Rolling1588.Integer.packAfter, show History5.packDue 507=false from by decide,Bool.false_eq_true,if_false]

theorem first507 (isA : Bool) : packFirst base isA 507=[] := by
  simp only [packFirst,show ¬(507:Nat)=5 from by decide,if_false,pack507 isA]

attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward Rolling1588.Integer.regularForward

theorem previous_shape (isA : Bool) :
    Rolling1588.stackForward isA = Rolling1588.forward isA 1 506 ++ (prior ++ ForwardSixPlacement.after isA) := by
  have snoc := Rolling1588.Integer.forward_snoc isA 1 506
  rw [show (1:Nat)+506=507 by rfl,first507,List.append_nil,Rolling1588.Integer.forward_eq_packets,
    Rolling1588.Integer.forward_eq_packets,MorningFour.explicit507] at snoc
  rw [ForwardSixPlacement.previous_shape,snoc]
  simp only [prior,List.append_assoc]

theorem layouts : ∀ q ∈ MorningFour.sites,
    q∈(W.compactSkywalkTickLayout base 507).wires.toFinset ∨
    q∈(W.compactSkywalkTickLayout base 508).wires.toFinset ∨
    q∈(W.compactSkywalkTickLayout base 509).wires.toFinset ∨
    q∈(W.compactSkywalkTickLayout base 510).wires.toFinset := by decide +kernel

theorem at_stage (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (hs : Stage base isA x p 507 a.basis) (r : List Bool) :
    run Forward11Width.candidate r a = run MorningFour.prior r a := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  obtain ⟨g,s,uv,mem,width,oriented,reads⟩ := MorningWidth.raw507 x hx0 hx raw hraw
  have oldmem : uv∈MorningFour.pairs := (List.mem_filter.mp mem).1
  have hl:=Forward11Width.legal_of uv g width oriented
  have bits : ∀ q ∈ MorningFour.sites, a.basis q=MorningFour.pre507 g s uv.1 uv.2 q := by
    intro q hq
    rw [hbits,←reads q hq]
    apply run_preserves_outside
    rcases layouts q hq with h|h|h|h
    all_goals
      exact fun hh => Finset.disjoint_left.mp
        (prefix_disjoint_layout base isA base_pool_nodup 507 _ (by omega) (by omega)) hh h
  exact (Forward11Width.on_site g s uv oldmem hl a bits r r).trans (MorningFour.on_site g s uv oldmem a bits r)

theorem place (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 507 a.basis) (r : List Bool) :
    run merged r (pullState (sig 506) a) = run prior r (pullState (sig 506) a) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  let k := measurementCount MorningFour.tick507
  let b := run MorningFour.tick507 (r.take k) a
  have s8 : Stage base isA x p 508 b.basis := by
    have next := (Rolling1588.Integer.step_spec base isA base_pool_nodup StackOB5.historyAbove x p 507
      hp0 hx0 hpo hp gap hx cop (by omega) a (r.take k) stage).2
    simpa only [pack507 isA,List.append_nil,MorningFour.explicit507,b] using next
  have p7 : pullState (sig 506) a = pullState (sig 507) a :=
    OB5.pull_step 507 (by omega) a (stage_zero_gen isA x 507 507 (by omega) (by omega) a.basis stage).1
      (stage_zero_gen isA x 507 507 (by omega) (by omega) a.basis stage).2
  have align (v : State) (i : Nat) (hi : i ≤ 508) (h : Stage base isA x p i v.basis) :
      pullState (sig 507) v = pullState (sig 510) v := by
    have z8 := stage_zero_gen isA x i 508 hi (by omega) v.basis h
    have z9 := stage_zero_gen isA x i 509 (by omega) (by omega) v.basis h
    have z10 := stage_zero_gen isA x i 510 (by omega) (by omega) v.basis h
    exact (OB5.pull_step 508 (by omega) v z8.1 z8.2).trans
      ((OB5.pull_step 509 (by omega) v z9.1 z9.2).trans (OB5.pull_step 510 (by omega) v z10.1 z10.2))
  rw [p7,prior,run_append,(renameProgram_counts _ _).2,OB5.run_rename 507 (by omega)]
  change run merged r (pullState (sig 507) a) =
    run ForwardSixPlacement.prior (r.drop k) (pullState (sig 507) b)
  rw [ForwardSixPlacement.prior,←ForwardSixPlacement.place isA x hx0 hx b s8,align b 508 (by omega) s8,
    align a 507 (by omega) stage,merged,OB5.run_rename 510 (by omega),
    OB5.run_rename 510 (by omega),at_stage isA x hx0 hx a stage,MorningFour.prior,run_append]

theorem prior_at_prefix (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis)
    (u r : List Bool) :
    run merged r (run (Rolling1588.forward isA 1 506) u s) =
    run prior r (run (Rolling1588.forward isA 1 506) u s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have init := Rolling1588.Integer.stage_one base isA x p s first
  have st := ((Rolling1588.Integer.regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p
    1 506 hp0 hx0 hpo hp gap hx cop (by omega)) s u init).2
  have start : pullState (sig (1-1)) s=s := by
    apply State.extensionality
    · rfl
    · funext q
      change s.basis (sig 0 q)=s.basis q
      rw [sig_zero]
  have pre := Rolling1588.Integer.forward_gen isA x hx0 hx 506 1 (by omega) (by omega) s u init
  rw [start,Rolling1588.Integer.forward_eq_packets] at pre
  rw [pre]
  exact place isA x hx0 hx _ st r

theorem replace_at_prefix (P Q R : Program) (s : State) (m : List Bool)
    (counts : measurementCount P=measurementCount Q)
    (prefixSame : ∀ u, run P u s=run Q u s)
    (same : ∀ u v, run merged v (run Q u s)=run prior v (run Q u s)) :
    run (P ++ (merged ++ R)) m s = run (Q ++ (prior ++ R)) m s := by
  simp only [run_append P,run_append Q,run_append merged,run_append prior,counts,prior_resources.2.1]
  rw [prefixSame,same]

end ECDSAAdd.Entrant.MorningPlacement

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588TickGapWalk =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.TickGap1591Arithmetic
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Integer

/-! Forward TickGap on the checked A/B integer stage. The packet programs,
the three terminal ticks, and the complete reverse walk stay unchanged. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.SlotSavings
open Arithmetic MappedCompressed Challenge
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem copy_top (n : Nat) (x y cs : List Wire) (c : Wire)
    (hy : y.length=n+2) (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    gateSlots (TickRanges.addCopy x y cs c)+5=gateSlots (addInPlace x y cs c) := by
  induction n generalizing x y cs c with
  | zero =>
    obtain ⟨a,a',b,b',d,rfl,rfl,rfl⟩ := TickRanges.shape_two hy hx hc
    simp [TickRanges.addCopy,addInPlace,gateSlots, instructionSlots,majority,eraseCarry]
  | succ n ih =>
    obtain ⟨a,a',a'',as,b,b',b'',bs,d,ds,rfl,rfl,rfl⟩ := TickRanges.shape_succ hy hx hc
    have hy' : (b'::b''::bs).length=n+2 := by simp only [List.length_cons] at hy ⊢; omega
    have hx' : (a'::a''::as).length=(b'::b''::bs).length := by simp only [List.length_cons] at hx ⊢; omega
    have hc' : ds.length+1=(b'::b''::bs).length := by simp only [List.length_cons] at hc ⊢; omega
    have v := ih (a'::a''::as) (b'::b''::bs) ds d hy' hx' hc'
    simp only [TickRanges.addCopy,addInPlace,List.cons_ne_nil,if_false,gateSlots_append] at v ⊢
    omega

theorem normal_top (n : Nat) (x y cs : List Wire) (c : Wire)
    (hy : y.length=n+2) (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    gateSlots (TopCarry.addInPlaceTop x y cs c)+3=gateSlots (addInPlace x y cs c) := by
  induction n generalizing x y cs c with
  | zero =>
    obtain ⟨a,a',b,b',d,rfl,rfl,rfl⟩ := TickRanges.shape_two hy hx hc
    simp [TopCarry.addInPlaceTop,addInPlace,gateSlots,instructionSlots,majority,eraseCarry]
  | succ n ih =>
    obtain ⟨a,a',a'',as,b,b',b'',bs,d,ds,rfl,rfl,rfl⟩ := TickRanges.shape_succ hy hx hc
    have hy' : (b'::b''::bs).length=n+2 := by simp only [List.length_cons] at hy ⊢; omega
    have hx' : (a'::a''::as).length=(b'::b''::bs).length := by simp only [List.length_cons] at hx ⊢; omega
    have hc' : ds.length+1=(b'::b''::bs).length := by simp only [List.length_cons] at hc ⊢; omega
    have v := ih (a'::a''::as) (b'::b''::bs) ds d hy' hx' hc'
    simp only [TopCarry.addInPlaceTop,addInPlace,List.cons_ne_nil,if_false,gateSlots_append] at v ⊢
    omega
theorem narrow_copy (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    gateSlots (TickRanges.narrowCopy L (n+2))+5=gateSlots (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have top := copy_top n L.xp L.yp L.carryLow L.q hw.y (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  simp only [TickRanges.narrowCopy,narrowSignedRecord,TickRanges.recordCopy,signedRecord,
    TickRanges.signedAddCopy,signedAdd,v.1,v.2.1,v.2.2.1,v.2.2.2,gateSlots_append]
  omega

theorem narrow_top (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    gateSlots (TickGap.narrowTop L (n+2))+3=gateSlots (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have top := normal_top n L.xp L.yp L.carryLow L.q hw.y (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  simp only [TickGap.narrowTop,narrowSignedRecord,TickGap.recordTop,signedRecord,
    TickGap.signedAddTop,signedAdd,v.1,v.2.1,v.2.2.1,v.2.2.2,gateSlots_append]
  omega
def gain (i : Nat) : Nat := if (225 ≤ i ∧ i ≤ 254) then 5 else if (255 ≤ i ∧ i ≤ 286) then 3 else 0

theorem tick_gain (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    gateSlots (TickRanges.tick w i)+gain i ≤ gateSlots (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrow_copy (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [TickRanges.old_split _ _ band]
    simp only [TickRanges.tick,if_pos band,gain,gateSlots_append]
    omega
  · by_cases gap : 255 ≤ i ∧ i ≤ 286
    · let L := W.compactSkywalkTickLayout w i
      let n := W.compactSkywalkTickPostWidth i
      let R := narrowSkywalkRecordLayout L n
      have width := W.compactSkywalkTick_width_bounds i hi
      have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
      have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
      have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
      have n2 : n-2+2=n := by dsimp only [n]; omega
      have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
      have h := narrow_top (n-2) R hw'
      simp only [n2] at h
      dsimp only [R,n,L] at h
      rw [TickGap.old_split _ _ gap]
      simp only [TickRanges.tick,if_neg band,TickGap.tick,if_pos gap,gain,gateSlots_append]
      omega
    · simp only [TickRanges.tick,if_neg band,TickGap.tick,if_neg gap,gain,Nat.add_zero,Nat.le_refl]

def sumGain (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => gain i+sumGain (i+1) n

theorem saved : sumGain 1 506=246 := by decide +kernel
end ECDSAAdd.Entrant.SlotSavings


namespace ECDSAAdd.Entrant.Rolling1588TickGap
open Arithmetic MappedCompressed Secp256k1 OB5
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

theorem tick_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i : Nat) (hi : i<512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (TickRanges.tick base i) m s=run (W.repairedTick base i) m s := by
  obtain ⟨raw,oldStage,read⟩ := Rolling1588.Integer.old_stage_local
    base isA base_pool_nodup x p i hi s stage
  have old := W.repairedTick_support base i hi base_pool_nodup
  have fresh := (TickRanges.tick_support base i hi base_pool_nodup).trans old
  exact Stack5.local_replace _ _ _ fresh old s raw m m read
    (TickRanges.tick_eq5 x hx0 hx i hi raw m oldStage)

theorem block_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i : Nat) (hi : i<512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i) m s=
      run (W.repairedTick base i++Rolling1588.Integer.packFirst base isA i) m s := by
  rw [run_append (TickRanges.tick base i),run_append (W.repairedTick base i),
    run_take (TickRanges.tick base i),run_take (W.repairedTick base i),
    tick_run_eq isA x hx0 hx i hi s m stage,
    (TickRanges.tick_counts base i hi base_pool_nodup).2]

def forward (isA : Bool) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (sig i)
      (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)++
        forward isA (i+1) n

theorem forward_slots_strong (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    Challenge.gateSlots (Rolling1588TickGap.forward isA i n)+SlotSavings.sumGain i n ≤
      Challenge.gateSlots (Rolling1588.Integer.forward isA i n) := by
  induction n generalizing i with
  | zero => simp [Rolling1588TickGap.forward,Rolling1588.Integer.forward,SlotSavings.sumGain,Challenge.gateSlots]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have step := SlotSavings.tick_gain base i (by omega) base_pool_nodup
    simp only [Rolling1588TickGap.forward,Rolling1588.Integer.forward,SlotSavings.sumGain,Challenge.gateSlots_append,
      Baselines.rename_gateSlots]
    omega


def count (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => TickRanges.due i+count (i+1) n

def stackForward0 (isA : Bool) : Program :=
  forward isA 1 506 ++ (MorningPlacement.merged ++ ForwardSixPlacement.after isA)

attribute [local irreducible] forward stackForward0 Rolling1588.forward
  Rolling1588.Integer.forward Rolling1588.stackForward

theorem forward_gen (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (n : Nat) :
    ∀i,1 ≤ i → i+n ≤ 512 → ∀(s : State)(m : List Bool),
      Rolling1588.Integer.Stage base isA x p i s.basis →
      run (forward isA i n) m (pullState (sig (i-1)) s)=
        pullState (sig (i+n-1)) (run (Rolling1588.Integer.regularForward base isA i n) m s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  induction n with
  | zero =>
    intro i _ _ s m _
    simp only [forward,Rolling1588.Integer.regularForward,run,Nat.add_zero]
  | succ n ih =>
    intro i h1 bound s m stage
    have hi : i ≤ 511 := by omega
    have zero := Rolling1588.Integer.stage_zero isA x i (by omega) s.basis stage
    rw [pull_step i hi s zero.1 zero.2]
    have mapped := (renameProgram_counts (sig i)
      (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)).2
    have records :
        measurementCount (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)=
          measurementCount (W.repairedTick base i++Rolling1588.Integer.packAfter base isA i) := by
      rw [measurementCount_append,measurementCount_append,
        (TickRanges.tick_counts base i (by omega) base_pool_nodup).2,
        Rolling1588.Integer.packFirst_records]
    rw [forward,Rolling1588.Integer.regularForward,run_append,run_append,mapped,records,
      OB5.run_rename i hi,block_run_eq isA x hx0 hx i (by omega) s _ stage,
      Rolling1588.Integer.forward_step_eq base isA base_pool_nodup x p i
        hp0 hx0 hpo hp gap hx cop _ _ stage]
    have next := (Rolling1588.Integer.step_spec base isA base_pool_nodup
      StackOB5.historyAbove x p i hp0 hx0 hpo hp gap hx cop (by omega) s
        (m.take (measurementCount (W.repairedTick base i++
          Rolling1588.Integer.packAfter base isA i))) stage).2
    have rest := ih (i+1) (by omega) (by omega) _
      (m.drop (measurementCount (W.repairedTick base i++
        Rolling1588.Integer.packAfter base isA i))) next
    rw [show i+1-1=i by omega,show i+1+n-1=i+(n+1)-1 by omega] at rest
    exact rest

theorem forward_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i n : Nat) (h1 : 1 ≤ i) (bound : i+n ≤ 512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (forward isA i n) m (pullState (sig (i-1)) s)=
      run (Rolling1588.forward isA i n) m (pullState (sig (i-1)) s) := by
  rw [←Rolling1588.Integer.forward_eq_packets]
  rw [forward_gen isA x hx0 hx n i h1 bound s m stage,
    Rolling1588.Integer.forward_gen isA x hx0 hx n i h1 bound s m stage]

theorem forward_first_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (n : Nat) (bound : 1+n ≤ 512) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (forward isA 1 n) m s=run (Rolling1588.forward isA 1 n) m s := by
  have same := forward_run_eq isA x hx0 hx 1 n (Nat.le_refl 1) bound s m
    (Rolling1588.Integer.stage_one base isA x p s first)
  have start : pullState (sig (1-1)) s=s := by
    apply State.extensionality
    · rfl
    · funext q
      change s.basis (sig 0 q)=s.basis q
      rw [sig_zero]
  rwa [start] at same

private theorem forward_integer_metrics (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    toffoliCount (forward isA i n)+count i n=
        toffoliCount (Rolling1588.Integer.forward isA i n) ∧
      measurementCount (forward isA i n)=measurementCount (Rolling1588.Integer.forward isA i n) ∧
      Challenge.gateSlots (forward isA i n) ≤
        Challenge.gateSlots (Rolling1588.Integer.forward isA i n) := by
  induction n generalizing i with
  | zero =>
    simp [forward,Rolling1588.Integer.forward,count,toffoliCount,measurementCount,Challenge.gateSlots]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have step := TickRanges.tick_counts base i (by omega) base_pool_nodup
    have slots := TickRanges.tick_slots base i (by omega) base_pool_nodup
    simp only [forward,Rolling1588.Integer.forward,count,toffoliCount_append,
      measurementCount_append,Challenge.gateSlots_append,
      (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
      Baselines.rename_gateSlots]
    exact ⟨by omega,by omega,by omega⟩

theorem forward_metrics (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    toffoliCount (forward isA i n)+count i n=toffoliCount (Rolling1588.forward isA i n) ∧
      measurementCount (forward isA i n)=measurementCount (Rolling1588.forward isA i n) ∧
      Challenge.gateSlots (forward isA i n) ≤ Challenge.gateSlots (Rolling1588.forward isA i n) := by
  simpa only [Rolling1588.Integer.forward_eq_packets] using
    forward_integer_metrics isA i n bound



theorem stackForward0_metrics (isA : Bool) :
    toffoliCount (stackForward0 isA)+67=toffoliCount (Rolling1588.stackForward isA) ∧
      measurementCount (stackForward0 isA)=measurementCount (Rolling1588.stackForward isA) ∧
      Challenge.gateSlots (stackForward0 isA) ≤ Challenge.gateSlots (Rolling1588.stackForward isA)+729 := by
  have head := forward_metrics isA 1 506 (by omega)
  have savings := forward_slots_strong isA 1 506 (by omega)
  rw [SlotSavings.saved,Rolling1588.Integer.forward_eq_packets] at savings
  have c : count 1 506=62 := by decide +kernel
  rw [c] at head
  have tail := MorningPlacement.prior_resources
  rw [stackForward0,MorningPlacement.previous_shape]
  simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem forward_integer_support (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    wires (forward isA i n)⊆wires (Rolling1588.Integer.forward isA i n) := by
  induction n generalizing i with
  | zero => simp [forward,Rolling1588.Integer.forward,wires]
  | succ n ih =>
    have block : wires (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)⊆
        wires (W.repairedTick base i++Rolling1588.Integer.packFirst base isA i) := by
      rw [wires_append,wires_append]
      exact Finset.union_subset_union
        (TickRanges.tick_support base i (by omega) base_pool_nodup) (Finset.Subset.refl _)
    have placed := Finset.image_mono (sig i) block
    rw [←renameProgram_support,←renameProgram_support] at placed
    simp only [forward,Rolling1588.Integer.forward,wires_append]
    exact Finset.union_subset_union placed (ih (i+1) (by omega))

theorem forward_support (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    wires (forward isA i n)⊆wires (Rolling1588.forward isA i n) := by
  simpa only [Rolling1588.Integer.forward_eq_packets] using
    forward_integer_support isA i n bound

theorem stackForward0_support (isA : Bool) :
    wires (stackForward0 isA)⊆wires (Rolling1588.stackForward isA) := by
  rw [stackForward0,MorningPlacement.previous_shape]
  simp only [wires_append]
  exact Finset.union_subset_union (forward_support isA 1 506 (by omega))
    (Finset.union_subset_union MorningPlacement.prior_support (Finset.Subset.refl _))







theorem stackForward0_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward0 isA) m s=run (Rolling1588.stackForward isA) m s := by
  rw [stackForward0,MorningPlacement.previous_shape]
  exact MorningPlacement.replace_at_prefix _ _ _ s m
    (forward_metrics isA 1 506 (by omega)).2.1
    (fun r => forward_first_run_eq isA x hx0 hx 506 (by omega) s r first)
    (MorningPlacement.prior_at_prefix isA x hx0 hx s first)





















end ECDSAAdd.Entrant.Rolling1588TickGap
end -- original module boundary


-- ===== Five506: five-tick forward window (tick 506 + ticks 507..510) =====
section

/-! Five-tick forward window (tick 506 + ticks 507..510) re-synthesized jointly on the reachable
stage-506 domain: 20 Toffolis instead of 10 + 11. Ancillas 793..803 are released (clean)
pool-B wires at stage 506; earlier ticks already use them. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.Five506
open Arithmetic MappedCompressed Secp256k1 History5

def tick506 : Program := [
  .CX 787 523,
  .CX 788 524,
  .CX 789 525,
  .CX 790 526,
  .CX 791 527,
  .CCX 522 523 787,
  .CCX 522 524 788,
  .CCX 522 525 789,
  .CCX 522 526 790,
  .CCX 522 527 791,
  .CX 787 523,
  .CX 788 524,
  .CX 789 525,
  .CX 790 526,
  .CX 791 527,
  .CX 528 792,
  .measureX 528 [] [.CZ 521 792],
  .CX 792 528,
  .CX 528 792,
  .CX 791 792,
  .CX 791 528,
  .CX 522 786,
  .CX 528 529,
  .X 1550,
  .CX 528 1550,
  .CX 791 1550,
  .CX 1550 523,
  .CX 1550 524,
  .CX 1550 525,
  .CX 1550 526,
  .CX 1550 527,
  .CX 1550 528,
  .CX 523 786,
  .CX 523 1550,
  .CCX 786 1550 1556,
  .CX 523 1556,
  .CX 523 1550,
  .CX 523 786,
  .CX 524 787,
  .CX 524 1556,
  .CCX 787 1556 1557,
  .CX 524 1557,
  .CX 524 1556,
  .CX 524 787,
  .CX 525 788,
  .CX 525 1557,
  .CCX 788 1557 1558,
  .CX 525 1558,
  .CX 525 1557,
  .CX 525 788,
  .CX 526 789,
  .CX 526 1558,
  .CCX 789 1558 1559,
  .CX 526 1559,
  .CX 526 1558,
  .CX 526 789,
  .CX 527 790,
  .CX 527 1559,
  .CCX 790 1559 1560,
  .CX 527 1560,
  .CX 527 1559,
  .CX 527 790,
  .CX 528 791,
  .CX 1560 791,
  .measureX 1560 [] [.CZ 527 790, .CZ 527 1559, .CZ 790 1559],
  .CX 527 790,
  .CX 1559 790,
  .measureX 1559 [] [.CZ 526 789, .CZ 526 1558, .CZ 789 1558],
  .CX 526 789,
  .CX 1558 789,
  .measureX 1558 [] [.CZ 525 788, .CZ 525 1557, .CZ 788 1557],
  .CX 525 788,
  .CX 1557 788,
  .measureX 1557 [] [.CZ 524 787, .CZ 524 1556, .CZ 787 1556],
  .CX 524 787,
  .CX 1556 787,
  .measureX 1556 [] [.CZ 523 786, .CZ 523 1550, .CZ 786 1550],
  .CX 523 786,
  .CX 1550 786,
  .CX 1550 523,
  .CX 1550 524,
  .CX 1550 525,
  .CX 1550 526,
  .CX 1550 527,
  .CX 1550 528,
  .X 1550,
  .CX 528 1550,
  .CX 791 1550,
  .CX 1550 792,
  .CX 521 522,
  .CX 528 529,
  .CX 791 792]

def block0 : Program := [
  .CX 787 523,
  .CCX 522 523 529,
  .CX 523 521,
  .CX 529 521,
  .CX 787 521,
  .CX 792 521,
  .CX 791 528,
  .CCX 521 528 793,
  .CX 525 789,
  .CX 791 786,
  .CX 792 786,
  .CX 788 524,
  .CX 789 524,
  .CCX 786 524 525,
  .CX 791 786,
  .CX 792 786,
  .CX 527 526,
  .CX 790 526,
  .CX 791 526,
  .CCX 786 526 1550,
  .CX 529 528,
  .CX 786 528,
  .CX 787 528,
  .CX 791 528,
  .CX 792 528,
  .CX 529 523,
  .CX 786 523,
  .CX 787 523,
  .CCX 528 523 1551,
  .CX 528 1551,
  .CX 790 1550,
  .CX 526 524]
def block1 : Program := [
  .CX 527 524,
  .CX 789 524,
  .CX 791 524,
  .CCX 786 524 790,
  .CX 527 522,
  .CX 528 522,
  .CX 793 522,
  .CX 792 522,
  .CX 529 527,
  .CX 788 527,
  .CX 790 527,
  .CX 792 527,
  .CX 1550 527,
  .CX 1551 527,
  .CCX 522 527 1552,
  .CX 524 522,
  .CX 525 522,
  .CX 526 522,
  .CX 529 522,
  .CX 793 522,
  .CX 787 522,
  .CX 788 522,
  .CX 789 522,
  .CX 526 524,
  .CX 528 524,
  .CX 786 524,
  .CX 787 524,
  .CX 788 524,
  .CX 790 524,
  .CX 1550 524,
  .CX 1551 524,
  .CX 1552 524]
def block2 : Program := [
  .CCX 522 524 1553,
  .CX 527 525,
  .CX 529 525,
  .CX 788 525,
  .CX 791 525,
  .CX 792 525,
  .CX 1550 525,
  .CX 1551 525,
  .CX 529 527,
  .CX 788 527,
  .CX 789 527,
  .CX 790 527,
  .CX 791 527,
  .CX 792 527,
  .CX 1550 527,
  .CX 1551 527,
  .CX 1553 527,
  .CCX 525 527 1554,
  .CX 522 521,
  .CX 523 521,
  .CX 524 521,
  .CX 525 521,
  .CX 529 521,
  .CX 789 521,
  .CX 791 521,
  .CX 1550 521,
  .CX 1551 521,
  .CX 1552 521,
  .CX 527 526,
  .CX 1554 526,
  .CCX 521 526 1556,
  .CX 786 523]
def block3 : Program := [
  .CX 525 522,
  .CX 793 522,
  .CX 787 522,
  .CX 789 522,
  .CX 791 522,
  .CX 792 522,
  .CX 1550 522,
  .CX 1551 522,
  .CX 1552 522,
  .CCX 523 522 1557,
  .CX 523 1557,
  .CX 527 524,
  .CX 791 524,
  .CX 792 524,
  .CCX 523 524 1558,
  .CX 527 523,
  .CX 529 523,
  .CX 788 523,
  .CX 789 523,
  .CX 790 523,
  .CX 791 523,
  .CX 792 523,
  .CX 1550 523,
  .CX 1551 523,
  .CX 1553 523,
  .CX 527 526,
  .CX 528 526,
  .CX 793 526,
  .CX 786 526,
  .CX 789 526,
  .CX 791 526,
  .CX 792 526]
def block4 : Program := [
  .CX 1553 526,
  .CCX 523 526 802,
  .CX 527 526,
  .CX 529 526,
  .CX 793 526,
  .CX 787 526,
  .CX 789 526,
  .CX 791 526,
  .CX 792 526,
  .CX 1553 526,
  .CX 525 523,
  .CX 527 523,
  .CX 788 523,
  .CX 790 523,
  .CX 1553 523,
  .CX 1557 523,
  .CX 802 523,
  .CCX 526 523 803,
  .CX 527 525,
  .CX 788 525,
  .CX 790 525,
  .CX 1553 525,
  .CX 1557 525,
  .CX 802 525,
  .CX 526 523,
  .CX 527 523,
  .CX 529 523,
  .CX 793 523,
  .CX 787 523,
  .CX 789 523,
  .CX 791 523,
  .CX 792 523]
def block5 : Program := [
  .CX 1553 523,
  .CX 803 523,
  .CCX 525 523 794,
  .CX 525 794,
  .CX 525 523,
  .CX 526 523,
  .CX 528 523,
  .CX 793 523,
  .CX 786 523,
  .CX 791 523,
  .CX 792 523,
  .CX 1556 523,
  .CX 803 523,
  .CX 527 524,
  .CX 529 524,
  .CX 793 524,
  .CX 787 524,
  .CX 791 524,
  .CX 792 524,
  .CX 803 524,
  .CX 794 524,
  .CCX 523 524 795,
  .CX 523 521,
  .CX 525 521,
  .CX 528 521,
  .CX 786 521,
  .CX 787 521,
  .CX 788 521,
  .CX 790 521,
  .CX 792 521,
  .CX 1551 521,
  .CX 1556 521]
def block6 : Program := [
  .CX 525 523,
  .CX 526 523,
  .CX 788 523,
  .CX 789 523,
  .CX 790 523,
  .CX 1553 523,
  .CX 1556 523,
  .CX 1557 523,
  .CX 1558 523,
  .CX 803 523,
  .CX 794 523,
  .CX 795 523,
  .CCX 521 523 796,
  .CX 521 796,
  .CX 524 521,
  .CX 525 521,
  .CX 527 521,
  .CX 529 521,
  .CX 793 521,
  .CX 787 521,
  .CX 789 521,
  .CX 792 521,
  .CX 1550 521,
  .CX 1553 521,
  .CX 802 521,
  .CX 794 521,
  .CX 527 524,
  .CX 529 524,
  .CX 793 524,
  .CX 787 524,
  .CX 788 524,
  .CX 789 524]
def block7 : Program := [
  .CX 790 524,
  .CX 792 524,
  .CX 1550 524,
  .CX 1553 524,
  .CX 1557 524,
  .CX 1558 524,
  .CX 802 524,
  .CX 803 524,
  .CX 795 524,
  .CX 796 524,
  .CCX 521 524 797,
  .CX 789 1550,
  .CX 789 1551,
  .CX 789 1552,
  .CX 789 1553,
  .CX 789 1554,
  .CX 789 1558,
  .CX 789 794,
  .CX 789 796,
  .CX 525 523,
  .CX 526 523,
  .CX 527 523,
  .CX 528 523,
  .CX 529 523,
  .CX 786 523,
  .CX 787 523,
  .CX 791 523,
  .CX 1550 523,
  .CX 794 523,
  .CX 795 523,
  .CX 524 521,
  .CX 788 521]
def block8 : Program := [
  .CX 790 521,
  .CX 791 521,
  .CX 1550 521,
  .CX 1557 521,
  .CX 1558 521,
  .CX 802 521,
  .CX 803 521,
  .CCX 523 521 789,
  .CX 525 521,
  .CX 526 521,
  .CX 788 521,
  .CX 790 521,
  .CX 791 521,
  .CX 1550 521,
  .CX 1553 521,
  .CX 1556 521,
  .CX 1557 521,
  .CX 1558 521,
  .CX 794 521,
  .CX 795 521,
  .CX 796 521,
  .CX 528 527,
  .CX 529 527,
  .CX 786 527,
  .CX 787 527,
  .CX 789 527,
  .CX 1553 527,
  .CX 1556 527,
  .CX 1558 527,
  .CX 802 527,
  .CX 803 527,
  .CX 795 527]
def block9 : Program := [
  .CCX 521 527 798,
  .CX 521 798,
  .CX 792 1550,
  .CX 792 1553,
  .CX 792 1554,
  .CX 792 1558,
  .CX 792 802,
  .CX 792 798,
  .measureX 792 [] [.Z 521, .Z 798, .CZ 521 527],
  .CX 1554 1557,
  .CX 1554 802,
  .CX 1554 803,
  .CX 1554 794,
  .CX 1554 796,
  .CX 1554 798,
  .measureX 1554 [] [.Z 523, .Z 528, .Z 786, .Z 787, .Z 1551, .Z 1558, .Z 803, .CZ 522 523, .CZ 522 528, .CZ 522 786, .CZ 522 787, .CZ 522 1551, .CZ 522 1557, .CZ 522 1558, .CZ 522 803],
  .CX 1557 802,
  .CX 1557 803,
  .CX 1557 794,
  .CX 1557 796,
  .CX 1557 798,
  .measureX 1557 [] [.Z 522, .Z 523, .Z 526, .Z 527, .Z 528, .Z 529, .Z 793, .Z 786, .Z 787, .Z 788, .Z 790, .Z 791, .Z 1550, .Z 1552, .Z 1553, .Z 802, .Z 794, .CZ 521 529, .CZ 521 793, .CZ 521 787, .CZ 521 788, .CZ 521 790, .CZ 521 1550, .CZ 521 1558, .CZ 521 802, .CZ 521 803, .CZ 521 794, .CZ 522 523, .CZ 522 524, .CZ 522 525, .CZ 522 528, .CZ 522 529, .CZ 522 793, .CZ 522 786, .CZ 522 788, .CZ 522 790, .CZ 522 1551, .CZ 522 1558, .CZ 522 803, .CZ 523 526, .CZ 523 793, .CZ 523 787, .CZ 523 788, .CZ 523 790, .CZ 523 791, .CZ 523 1551, .CZ 523 1556, .CZ 523 797, .CZ 524 526, .CZ 524 528, .CZ 524 529, .CZ 524 786, .CZ 524 787, .CZ 524 791, .CZ 524 1553, .CZ 525 526, .CZ 525 787, .CZ 525 789, .CZ 525 791, .CZ 525 1551, .CZ 525 1552, .CZ 526 527, .CZ 526 788, .CZ 526 790, .CZ 527 529, .CZ 527 793, .CZ 527 787, .CZ 527 788, .CZ 527 790, .CZ 527 791, .CZ 527 1550, .CZ 527 802, .CZ 528 793, .CZ 793 791],
  .CX 793 789,
  .CX 793 791,
  .CX 793 1551,
  .CX 793 1552,
  .CX 793 1558,
  .CX 793 794,
  .CX 793 796,
  .measureX 793 [] [.Z 521, .Z 523, .Z 524, .Z 525, .Z 526, .Z 527, .Z 528, .Z 786, .Z 789, .Z 791, .Z 1552, .Z 1553, .Z 1556, .Z 803, .Z 794, .Z 795, .CZ 521 522, .CZ 521 528, .CZ 521 529, .CZ 521 786, .CZ 521 788, .CZ 521 789, .CZ 521 790, .CZ 521 791, .CZ 521 1550, .CZ 521 1551, .CZ 521 1552, .CZ 521 1553, .CZ 521 1558, .CZ 521 794, .CZ 522 523, .CZ 522 525, .CZ 522 527, .CZ 522 528, .CZ 522 786, .CZ 522 787, .CZ 522 788, .CZ 522 789, .CZ 522 790, .CZ 522 1551, .CZ 522 1553, .CZ 522 802, .CZ 522 803, .CZ 522 798, .CZ 523 526, .CZ 523 528, .CZ 523 786, .CZ 523 788, .CZ 523 789, .CZ 523 790, .CZ 523 791, .CZ 523 1556, .CZ 523 802, .CZ 523 803, .CZ 523 794, .CZ 524 525, .CZ 524 526, .CZ 524 528, .CZ 524 786, .CZ 524 788, .CZ 524 789, .CZ 524 790, .CZ 524 791, .CZ 524 1553, .CZ 524 1558, .CZ 524 802, .CZ 525 526, .CZ 525 527, .CZ 525 528, .CZ 525 529, .CZ 525 786, .CZ 525 787, .CZ 525 789, .CZ 527 788, .CZ 527 789, .CZ 527 790, .CZ 527 791, .CZ 527 1550, .CZ 527 798],
  .CX 789 1550,
  .CX 789 1551]
def block10 : Program := [
  .CX 789 1552,
  .CX 789 1558,
  .CX 789 794,
  .CX 789 796,
  .measureX 789 [] [.Z 522, .Z 523, .Z 524, .Z 525, .Z 526, .Z 786, .Z 787, .Z 791, .Z 1550, .Z 1553, .Z 1556, .Z 802, .Z 794, .Z 798, .CZ 521 523, .CZ 521 526, .CZ 521 527, .CZ 521 791, .CZ 521 1558, .CZ 521 803, .CZ 521 794, .CZ 522 523, .CZ 522 526, .CZ 522 527, .CZ 522 528, .CZ 522 786, .CZ 522 1552, .CZ 522 1558, .CZ 522 803, .CZ 522 798, .CZ 523 524, .CZ 523 528, .CZ 523 788, .CZ 523 790, .CZ 523 791, .CZ 523 1553, .CZ 523 1556, .CZ 523 794, .CZ 523 797, .CZ 524 526, .CZ 524 527, .CZ 524 528, .CZ 524 786, .CZ 525 527, .CZ 525 528, .CZ 525 529, .CZ 525 786, .CZ 525 787, .CZ 526 787, .CZ 526 788, .CZ 526 790, .CZ 526 791, .CZ 526 1551, .CZ 527 528, .CZ 527 786, .CZ 527 788, .CZ 527 790, .CZ 527 791, .CZ 527 1558, .CZ 527 794, .CZ 528 529, .CZ 528 786, .CZ 528 788, .CZ 528 790, .CZ 528 1551, .CZ 528 1558, .CZ 528 803, .CZ 786 788, .CZ 786 790],
  .CX 526 1550,
  .CX 526 1551,
  .CX 526 1552,
  .CX 526 1556,
  .CX 526 1558,
  .CX 526 794,
  .CX 526 796,
  .measureX 526 [] [.Z 523, .Z 524, .Z 525, .Z 528, .Z 786, .Z 787, .Z 791, .Z 1550, .Z 1551, .Z 1553, .Z 1558, .Z 802, .Z 798, .CZ 521 522, .CZ 521 524, .CZ 521 525, .CZ 521 528, .CZ 521 786, .CZ 521 1550, .CZ 521 1553, .CZ 521 803, .CZ 521 798, .CZ 522 523, .CZ 522 524, .CZ 522 525, .CZ 522 787, .CZ 522 1550, .CZ 522 1551, .CZ 522 1558, .CZ 522 803, .CZ 522 794, .CZ 523 524, .CZ 523 527, .CZ 523 528, .CZ 523 786, .CZ 523 791, .CZ 523 1553, .CZ 523 802, .CZ 523 803, .CZ 523 794, .CZ 523 798],
  .CX 521 523,
  .CX 521 524,
  .CX 521 1551,
  .CX 521 1552,
  .CX 521 1558,
  .CX 521 794,
  .CX 521 797,
  .CX 521 798,
  .measureX 521 [] [.Z 524, .Z 527, .Z 786, .Z 787, .Z 788, .Z 1550, .Z 1551, .Z 1552, .Z 1558, .Z 802, .Z 803, .Z 795, .Z 798, .CZ 522 527, .CZ 522 528, .CZ 522 786, .CZ 522 791, .CZ 522 1550, .CZ 522 1553, .CZ 522 803, .CZ 522 794, .CZ 522 795, .CZ 523 524, .CZ 523 525, .CZ 523 786, .CZ 523 788, .CZ 523 790, .CZ 523 791, .CZ 523 1550, .CZ 523 802, .CZ 523 803, .CZ 523 794, .CZ 523 795, .CZ 524 527, .CZ 524 787, .CZ 524 1551, .CZ 524 802, .CZ 524 794, .CZ 524 795, .CZ 524 797, .CZ 525 527, .CZ 525 528, .CZ 525 529, .CZ 525 786, .CZ 525 787, .CZ 525 788, .CZ 525 790, .CZ 525 1550, .CZ 525 1553, .CZ 525 1556, .CZ 525 795, .CZ 525 798, .CZ 527 529, .CZ 527 787, .CZ 527 788, .CZ 527 790, .CZ 527 1553, .CZ 527 1556, .CZ 527 1558, .CZ 527 794, .CZ 528 529, .CZ 528 786, .CZ 528 788, .CZ 528 790, .CZ 528 1552, .CZ 528 1558, .CZ 528 803, .CZ 529 794, .CZ 786 788, .CZ 786 791, .CZ 786 1550, .CZ 786 1552, .CZ 787 794, .CZ 787 797, .CZ 791 797, .CZ 1551 797],
  .CX 524 527,
  .CX 524 790,
  .CX 524 1550,
  .CX 524 1551,
  .CX 524 1552,
  .CX 524 794,
  .CX 524 796,
  .CX 524 797,
  .CX 524 798,
  .measureX 524 [] [.Z 525, .Z 527, .Z 786, .Z 788, .Z 790, .Z 791, .Z 1550, .Z 1553, .Z 802, .Z 794, .Z 798, .CZ 522 523, .CZ 522 525, .CZ 522 528, .CZ 522 788, .CZ 522 790, .CZ 522 791, .CZ 522 1551, .CZ 522 1553, .CZ 522 1556, .CZ 522 802, .CZ 522 803, .CZ 522 794, .CZ 523 527, .CZ 523 529, .CZ 523 787, .CZ 523 788, .CZ 523 1551, .CZ 523 1556, .CZ 523 1558, .CZ 523 795, .CZ 525 527, .CZ 525 528, .CZ 525 529, .CZ 525 786, .CZ 525 791, .CZ 525 1550, .CZ 525 1551, .CZ 525 1558, .CZ 525 802, .CZ 525 803, .CZ 525 795, .CZ 527 529, .CZ 527 787, .CZ 527 788, .CZ 528 787, .CZ 528 790, .CZ 528 1550, .CZ 528 1551, .CZ 528 1552, .CZ 528 1558, .CZ 529 790, .CZ 529 791, .CZ 529 1550, .CZ 529 1558, .CZ 529 803, .CZ 529 794, .CZ 786 788, .CZ 786 790, .CZ 786 1550, .CZ 786 1558, .CZ 787 1551, .CZ 787 1552, .CZ 787 794, .CZ 788 791, .CZ 788 1551, .CZ 788 1553, .CZ 788 802, .CZ 788 795, .CZ 790 791, .CZ 790 1553, .CZ 790 1556]]
def block11 : Program := [
  .CX 522 527,
  .CX 522 790,
  .CX 522 1550,
  .CX 522 1552,
  .CX 522 1553,
  .CX 522 1558,
  .CX 522 803,
  .CX 522 794,
  .CX 522 795,
  .measureX 522 [] [.Z 523, .Z 525, .Z 527, .Z 528, .Z 529, .Z 787, .Z 788, .Z 790, .Z 1550, .Z 1551, .Z 1552, .Z 1553, .Z 1556, .Z 1558, .Z 795, .Z 797, .CZ 523 527, .CZ 523 529, .CZ 523 790, .CZ 523 1550, .CZ 523 1552, .CZ 523 802, .CZ 525 528, .CZ 525 786, .CZ 525 791, .CZ 525 1552, .CZ 525 1553, .CZ 525 1556, .CZ 525 1558, .CZ 525 803, .CZ 525 794, .CZ 525 795, .CZ 527 528, .CZ 527 529, .CZ 527 786, .CZ 527 790, .CZ 527 1551, .CZ 527 1552, .CZ 527 1556, .CZ 527 802, .CZ 527 798, .CZ 528 786, .CZ 528 788, .CZ 528 791, .CZ 528 1550, .CZ 528 1552, .CZ 528 1553, .CZ 528 1558, .CZ 528 802, .CZ 528 803, .CZ 529 787, .CZ 529 788, .CZ 529 1550, .CZ 529 1551, .CZ 529 1553, .CZ 529 1558, .CZ 529 803, .CZ 786 787, .CZ 786 788, .CZ 786 1550, .CZ 786 1552, .CZ 786 1553, .CZ 786 1558, .CZ 786 802, .CZ 786 803, .CZ 787 1553, .CZ 788 1550, .CZ 788 1553, .CZ 788 1558, .CZ 788 802, .CZ 788 803, .CZ 790 1550, .CZ 790 1551, .CZ 790 1553, .CZ 790 1556, .CZ 790 1558, .CZ 790 803, .CZ 790 795, .CZ 791 1550, .CZ 791 1551, .CZ 791 1552, .CZ 791 1553, .CZ 791 1558, .CZ 791 795, .CZ 1550 1556, .CZ 1551 1552],
  .CX 523 527,
  .CX 523 1553,
  .CX 523 802,
  .CX 523 803,
  .CX 523 794,
  .CX 523 795,
  .CX 523 796,
  .measureX 523 [] [.Z 525, .Z 527, .Z 528, .Z 529, .Z 786, .Z 787, .Z 790, .Z 1550, .Z 1556, .Z 1558, .Z 803, .Z 794, .Z 797, .CZ 525 787, .CZ 525 788, .CZ 525 790, .CZ 525 791, .CZ 525 1551, .CZ 525 1552, .CZ 525 1553, .CZ 525 1558, .CZ 525 803, .CZ 525 794, .CZ 525 798, .CZ 527 786, .CZ 527 787, .CZ 527 1550, .CZ 527 1551, .CZ 527 1552, .CZ 527 1553, .CZ 527 1558, .CZ 527 803, .CZ 527 798, .CZ 528 787, .CZ 528 788, .CZ 528 791, .CZ 528 1551, .CZ 528 1556, .CZ 528 794, .CZ 528 795, .CZ 528 798, .CZ 529 787, .CZ 529 791, .CZ 529 1552, .CZ 529 802, .CZ 529 803, .CZ 529 798, .CZ 786 787, .CZ 786 788, .CZ 786 790, .CZ 786 1550, .CZ 786 1558, .CZ 786 802, .CZ 786 803, .CZ 786 794, .CZ 786 798, .CZ 787 790, .CZ 787 1550, .CZ 787 794, .CZ 788 791, .CZ 788 1552, .CZ 788 1553, .CZ 788 1556, .CZ 788 1558, .CZ 788 802, .CZ 788 803, .CZ 788 794, .CZ 788 795, .CZ 790 791, .CZ 790 1552, .CZ 790 1553, .CZ 790 1556, .CZ 790 1558, .CZ 790 802, .CZ 790 803, .CZ 790 794, .CZ 790 795, .CZ 791 1550, .CZ 791 1552, .CZ 791 1553, .CZ 791 1556, .CZ 791 1558, .CZ 791 803, .CZ 791 794, .CZ 791 798, .CZ 1550 1553, .CZ 1550 1556, .CZ 1550 1558, .CZ 1550 802, .CZ 1550 803, .CZ 1550 794, .CZ 1551 1552, .CZ 1551 1558, .CZ 1551 802, .CZ 1551 794, .CZ 1551 798, .CZ 1552 1556, .CZ 1552 1558, .CZ 1552 803],
  .CX 527 1558,
  .CX 527 802,
  .CX 527 803,
  .CX 527 794,
  .CX 527 796,
  .measureX 527 [] [.Z 525, .Z 528, .Z 529, .Z 786, .Z 787, .Z 788, .Z 791, .Z 1553, .Z 1556, .Z 803, .Z 797, .Z 798, .CZ 525 529, .CZ 525 788, .CZ 525 790, .CZ 525 791, .CZ 525 1550, .CZ 525 1551, .CZ 528 529, .CZ 528 787, .CZ 528 790, .CZ 528 791, .CZ 528 1551, .CZ 528 1552, .CZ 528 1556, .CZ 528 1558, .CZ 528 802, .CZ 528 795, .CZ 528 798, .CZ 529 787, .CZ 529 1551, .CZ 529 1553, .CZ 529 802, .CZ 786 787, .CZ 786 791, .CZ 786 1550, .CZ 786 1552, .CZ 786 803, .CZ 786 798, .CZ 787 790, .CZ 787 1550, .CZ 787 1551, .CZ 787 1553, .CZ 787 798, .CZ 788 1552, .CZ 788 1556, .CZ 788 802, .CZ 788 803, .CZ 788 794, .CZ 790 1552, .CZ 790 1556, .CZ 790 802, .CZ 790 803, .CZ 790 794, .CZ 791 1551, .CZ 791 1552, .CZ 791 798, .CZ 1550 1553, .CZ 1550 1556, .CZ 1550 802, .CZ 1550 798, .CZ 1551 1558, .CZ 1551 802, .CZ 1551 803, .CZ 1551 798, .CZ 1552 1553, .CZ 1552 1556, .CZ 1552 802, .CZ 1552 803, .CZ 1553 1556, .CZ 1553 795],
  .CX 1558 802,
  .CX 1558 803,
  .CX 1558 795,
  .CX 1558 796,
  .CX 1558 798,
  .measureX 1558 [] [.Z 525, .Z 528, .Z 788, .Z 1550, .Z 803, .Z 794, .Z 795, .Z 797, .CZ 525 787, .CZ 525 1551, .CZ 525 1556, .CZ 525 794, .CZ 525 795, .CZ 525 798, .CZ 528 786, .CZ 528 787, .CZ 528 1552, .CZ 528 1553, .CZ 528 802, .CZ 528 794, .CZ 528 795, .CZ 529 787, .CZ 529 1550, .CZ 529 1551, .CZ 529 1552, .CZ 529 1553, .CZ 529 1556, .CZ 529 803, .CZ 529 794, .CZ 786 790, .CZ 786 791, .CZ 786 1550, .CZ 786 1551, .CZ 786 1552, .CZ 786 1553, .CZ 786 1556, .CZ 786 803, .CZ 786 794, .CZ 787 788, .CZ 787 790, .CZ 787 1556, .CZ 787 794, .CZ 788 1550, .CZ 788 1551, .CZ 788 1552, .CZ 788 1556, .CZ 788 802, .CZ 788 803, .CZ 788 798, .CZ 790 1550, .CZ 790 1551, .CZ 790 1552, .CZ 790 1556, .CZ 790 802, .CZ 790 803, .CZ 790 798, .CZ 791 1550, .CZ 791 1552, .CZ 791 803, .CZ 791 794, .CZ 791 795, .CZ 791 798, .CZ 1550 1551, .CZ 1550 1552, .CZ 1550 1553, .CZ 1550 802, .CZ 1550 803, .CZ 1551 1552, .CZ 1551 1553, .CZ 1551 1556, .CZ 1551 802, .CZ 1551 803, .CZ 1551 795, .CZ 1552 803, .CZ 1552 795, .CZ 1552 798, .CZ 1553 794, .CZ 1553 795, .CZ 1553 798],
  .CX 788 790,
  .measureX 788 [] [.Z 528, .Z 529, .Z 787, .Z 790, .Z 791, .Z 1550, .Z 1551, .Z 1556, .Z 802, .Z 803, .Z 795, .CZ 525 528, .CZ 525 529, .CZ 525 786, .CZ 525 787, .CZ 528 790, .CZ 528 1550, .CZ 528 1551, .CZ 528 1553, .CZ 528 795, .CZ 529 790, .CZ 529 1550, .CZ 529 1553, .CZ 529 1556, .CZ 529 802, .CZ 786 787, .CZ 786 791, .CZ 786 1551, .CZ 786 1552, .CZ 786 1553, .CZ 786 1556, .CZ 786 802, .CZ 786 803, .CZ 787 790, .CZ 787 1550, .CZ 787 1551, .CZ 787 1553, .CZ 787 795]]
def block12 : Program := [
  .CX 1550 1552,
  .CX 1550 1553,
  .CX 1550 803,
  .CX 1550 794,
  .CX 1550 796,
  .measureX 1550 [] [.Z 525, .Z 528, .Z 786, .Z 790, .Z 1553, .Z 1556, .Z 803, .CZ 525 528, .CZ 525 786, .CZ 525 791, .CZ 525 1553, .CZ 525 803, .CZ 525 794, .CZ 786 791, .CZ 790 791, .CZ 791 803, .CZ 1553 1556, .CZ 1553 802, .CZ 1553 803],
  .CX 790 1551,
  .CX 790 1552,
  .CX 790 802,
  .CX 790 803,
  .CX 790 794,
  .CX 790 796,
  .CX 790 798,
  .measureX 790 [] [.Z 525, .Z 529, .Z 1553, .CZ 525 528, .CZ 525 529, .CZ 525 786, .CZ 525 787, .CZ 525 791, .CZ 525 1556, .CZ 525 802, .CZ 525 803, .CZ 528 787, .CZ 528 1553, .CZ 528 1556, .CZ 528 798, .CZ 529 787, .CZ 529 791, .CZ 529 1553, .CZ 529 1556, .CZ 529 802, .CZ 529 803, .CZ 786 787, .CZ 786 1553, .CZ 786 1556, .CZ 786 798, .CZ 787 1551, .CZ 787 1553, .CZ 787 1556, .CZ 787 795, .CZ 787 798, .CZ 791 1551, .CZ 791 1552, .CZ 791 1553, .CZ 791 797, .CZ 791 798, .CZ 1551 1556, .CZ 1551 803, .CZ 1551 798, .CZ 1552 803, .CZ 1552 798, .CZ 1553 803, .CZ 1553 797, .CZ 1556 803, .CZ 802 794],
  .CX 529 787,
  .CX 529 1551,
  .measureX 529 [] [.Z 528, .Z 1551, .Z 1556, .Z 802, .Z 795, .CZ 528 786, .CZ 786 1551, .CZ 786 1556, .CZ 786 802, .CZ 786 795],
  .CX 528 787,
  .CX 528 1552,
  .CX 528 1553,
  .CX 528 802,
  .CX 528 794,
  .CX 528 795,
  .CX 528 797,
  .X 528,
  .measureX 528 [] [.Z 791, .Z 1553, .Z 1556, .Z 803, .Z 794, .Z 797, .CZ 525 1556, .CZ 525 803, .CZ 525 798, .CZ 786 787, .CZ 786 794, .CZ 786 795, .CZ 787 1556, .CZ 791 1556, .CZ 791 795, .CZ 1551 1556, .CZ 1553 794, .CZ 1553 795, .CZ 1556 802, .CZ 1556 803, .CZ 802 794, .CZ 802 795, .CZ 794 795],
  .CX 1551 1553,
  .CX 1551 802,
  .CX 1551 797,
  .measureX 1551 [] [.Z 787, .Z 791, .Z 1553, .Z 795, .Z 798, .CZ 525 786, .CZ 525 787, .CZ 525 1556, .CZ 525 803, .CZ 525 798, .CZ 786 787, .CZ 786 791, .CZ 786 1553, .CZ 786 795, .CZ 786 798, .CZ 787 1553, .CZ 787 795, .CZ 791 1556, .CZ 791 794, .CZ 791 795, .CZ 791 798, .CZ 1553 1556, .CZ 1553 803, .CZ 1556 802, .CZ 1556 803, .CZ 1556 798, .CZ 802 803, .CZ 803 794, .CZ 803 795, .CZ 795 798],
  .measureX 1552 [] [.Z 786, .Z 791, .Z 802, .CZ 525 1556, .CZ 786 787, .CZ 786 803, .CZ 787 803],
  .CX 791 802]
def block13 : Program := [
  .CX 791 803,
  .CX 791 795,
  .CX 791 796,
  .CX 791 797,
  .measureX 791 [] [.Z 787, .CZ 525 786, .CZ 525 787, .CZ 786 787, .CZ 786 1553, .CZ 786 1556, .CZ 786 802, .CZ 787 1553, .CZ 787 1556, .CZ 787 802],
  .CX 801 800,
  .CX 801 799,
  .CX 801 798,
  .CX 801 796,
  .CX 801 794,
  .CX 801 787,
  .CX 801 786,
  .CX 800 801,
  .CX 800 799,
  .CX 800 798,
  .CX 800 796,
  .CX 800 794,
  .CX 800 787,
  .CX 800 786,
  .CX 801 800,
  .CX 799 801,
  .CX 799 798,
  .CX 799 796,
  .CX 799 794,
  .CX 799 787,
  .CX 799 786,
  .CX 801 799,
  .CX 798 801,
  .CX 798 796,
  .CX 798 794,
  .CX 798 787,
  .CX 798 786]
def block14 : Program := [
  .CX 801 798,
  .CX 797 801,
  .CX 797 796,
  .CX 797 795,
  .CX 797 803,
  .CX 797 1558,
  .CX 797 1553,
  .CX 797 792,
  .CX 797 789,
  .CX 797 787,
  .CX 797 786,
  .CX 797 529,
  .CX 797 523,
  .CX 796 801,
  .CX 796 797,
  .CX 796 795,
  .CX 796 803,
  .CX 796 1558,
  .CX 796 1557,
  .CX 796 1556,
  .CX 796 1550,
  .CX 796 792,
  .CX 796 791,
  .CX 796 789,
  .CX 796 788,
  .CX 796 529,
  .CX 796 528,
  .CX 796 523,
  .CX 796 522,
  .CX 795 796,
  .CX 795 794,
  .CX 795 802]
def block15 : Program := [
  .CX 795 1557,
  .CX 795 1554,
  .CX 795 1553,
  .CX 795 1550,
  .CX 795 791,
  .CX 795 788,
  .CX 795 786,
  .CX 795 528,
  .CX 795 522,
  .CX 794 801,
  .CX 794 797,
  .CX 794 796,
  .CX 794 802,
  .CX 794 1558,
  .CX 794 1557,
  .CX 794 1556,
  .CX 794 1553,
  .CX 794 1552,
  .CX 794 1551,
  .CX 794 1550,
  .CX 794 792,
  .CX 794 791,
  .CX 794 790,
  .CX 794 789,
  .CX 794 788,
  .CX 794 787,
  .CX 794 786,
  .CX 794 793,
  .CX 794 529,
  .CX 794 528,
  .CX 794 527,
  .CX 794 526]
def block16 : Program := [
  .CX 794 524,
  .CX 794 523,
  .CX 794 522,
  .CX 794 521,
  .CX 803 797,
  .CX 803 796,
  .CX 803 795,
  .CX 803 794,
  .CX 803 802,
  .CX 803 1558,
  .CX 803 1557,
  .CX 803 1556,
  .CX 803 1554,
  .CX 803 1552,
  .CX 803 1550,
  .CX 803 792,
  .CX 803 791,
  .CX 803 789,
  .CX 803 788,
  .CX 803 529,
  .CX 803 528,
  .CX 803 527,
  .CX 803 526,
  .CX 803 525,
  .CX 803 523,
  .CX 803 522,
  .CX 803 521,
  .CX 794 803,
  .CX 802 796,
  .CX 802 1557,
  .CX 802 1556,
  .CX 802 791]
def block17 : Program := [
  .CX 802 788,
  .CX 802 786,
  .CX 802 528,
  .CX 802 522,
  .CX 796 802,
  .CX 1558 797,
  .CX 797 1558,
  .CX 1557 796,
  .CX 796 1557,
  .CX 1556 801,
  .CX 1556 795,
  .CX 1556 794,
  .CX 1556 803,
  .CX 1556 1554,
  .CX 1556 1552,
  .CX 1556 1551,
  .CX 1556 787,
  .CX 1556 527,
  .CX 1556 526,
  .CX 1556 525,
  .CX 1556 521,
  .CX 803 1556,
  .CX 1554 795,
  .CX 795 1554,
  .CX 1553 801,
  .CX 1553 794,
  .CX 1553 803,
  .CX 1553 802,
  .CX 1553 1557,
  .CX 1553 1552,
  .CX 1553 1551,
  .CX 1553 1550]
def block18 : Program := [
  .CX 1553 791,
  .CX 1553 788,
  .CX 1553 786,
  .CX 1553 528,
  .CX 1553 527,
  .CX 1553 526,
  .CX 1553 525,
  .CX 1553 522,
  .CX 1553 521,
  .CX 1557 1553,
  .CX 1552 794,
  .CX 794 1552,
  .CX 1551 803,
  .CX 803 1551,
  .CX 1550 802,
  .CX 802 1550,
  .CX 792 1558,
  .CX 1558 792,
  .CX 791 1557,
  .CX 1557 791,
  .CX 790 1556,
  .CX 1556 790,
  .CX 789 792,
  .CX 792 789,
  .CX 788 791,
  .CX 791 788,
  .CX 787 801,
  .CX 787 1553,
  .CX 787 1552,
  .CX 787 786,
  .CX 1552 787,
  .CX 786 801]
def block19 : Program := [
  .CX 786 1553,
  .CX 786 1552,
  .CX 786 1550,
  .CX 786 788,
  .CX 786 787,
  .CX 786 528,
  .CX 786 527,
  .CX 786 522,
  .CX 786 521,
  .CX 787 786,
  .CX 793 790,
  .CX 790 793,
  .CX 529 789,
  .CX 789 529,
  .CX 528 788,
  .CX 788 528,
  .CX 527 787,
  .CX 787 527,
  .CX 526 786,
  .CX 786 526,
  .CX 525 793,
  .CX 525 529,
  .CX 525 528,
  .CX 525 527,
  .CX 525 526,
  .CX 525 524,
  .CX 525 523,
  .CX 525 522,
  .CX 525 521,
  .CX 526 525,
  .CX 524 793,
  .CX 793 524]
def block20 : Program := [
  .CX 523 529,
  .CX 529 523,
  .CX 522 528,
  .CX 528 522,
  .CX 521 527,
  .CX 527 521,
  .X 801,
  .CX 526 527,
  .X 527,
  .CX 526 786]
def cand : Program := block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20

def sites : List Wire := [521, 522, 523, 524, 525, 526, 527, 528, 529, 793, 794, 795, 796, 797, 798, 799, 800, 801, 786, 787, 788, 789, 790, 791, 792, 1550, 1551, 1552, 1553, 1554, 1556, 1557, 1558, 1559, 1560, 802, 803]

/-- The sites the new window touches: the old window's scratch carries 1559/1560 are not used. -/
def candSites : List Wire := sites.filter (fun q => decide (q ≠ 1559 ∧ q ≠ 1560))

def rows0 : List (Bool × Bool × Nat × Nat) := [(false, false, 0, 1), (false, false, 1, 1), (false, false, 2, 1), (false, false, 3, 1), (false, false, 4, 1), (false, false, 5, 1), (false, false, 6, 1), (false, false, 7, 1), (false, false, 8, 1), (false, false, 9, 1), (false, false, 10, 1), (false, false, 11, 1), (false, false, 12, 1), (false, false, 13, 1), (false, false, 14, 1), (false, false, 15, 1), (false, false, 16, 1), (false, false, 17, 1), (false, false, 18, 1), (false, false, 19, 1), (false, false, 20, 1), (false, false, 21, 1), (false, false, 22, 1), (false, false, 23, 1)]
def rows1 : List (Bool × Bool × Nat × Nat) := [(false, false, 24, 1), (false, false, 25, 1), (false, false, 26, 1), (false, false, 27, 1), (false, false, 28, 1), (false, false, 29, 1), (false, false, 30, 1), (false, false, 31, 1), (false, false, 1, 3), (false, false, 2, 3), (false, false, 4, 3), (false, false, 5, 3), (false, false, 7, 3), (false, false, 8, 3), (false, false, 10, 3), (false, false, 11, 3), (false, false, 13, 3), (false, false, 14, 3), (false, false, 1, 5), (false, false, 2, 5), (false, false, 3, 5), (false, false, 4, 5), (false, false, 6, 5), (false, false, 7, 5)]
def rows2 : List (Bool × Bool × Nat × Nat) := [(false, false, 1, 7), (false, false, 2, 7), (false, false, 3, 7), (false, false, 4, 7), (false, false, 5, 7), (false, false, 6, 7), (false, false, 1, 9), (false, false, 2, 9), (false, false, 1, 11), (false, false, 2, 11), (false, false, 3, 11), (false, false, 1, 13), (false, false, 2, 13), (false, false, 3, 13), (false, false, 1, 15), (false, false, 2, 15), (false, false, 1, 17), (false, false, 1, 19), (false, false, 1, 21), (false, false, 1, 23), (false, false, 1, 25), (false, false, 1, 27), (false, false, 1, 29), (false, false, 1, 31)]
def rows3 : List (Bool × Bool × Nat × Nat) := [(false, true, 0, 1), (false, true, 1, 1), (false, true, 2, 1), (false, true, 3, 1), (false, true, 4, 1), (false, true, 5, 1), (false, true, 6, 1), (false, true, 7, 1), (false, true, 8, 1), (false, true, 9, 1), (false, true, 10, 1), (false, true, 11, 1), (false, true, 12, 1), (false, true, 13, 1), (false, true, 14, 1), (false, true, 15, 1), (false, true, 16, 1), (false, true, 17, 1), (false, true, 18, 1), (false, true, 19, 1), (false, true, 20, 1), (false, true, 21, 1), (false, true, 22, 1), (false, true, 23, 1)]
def rows4 : List (Bool × Bool × Nat × Nat) := [(false, true, 24, 1), (false, true, 25, 1), (false, true, 26, 1), (false, true, 27, 1), (false, true, 28, 1), (false, true, 29, 1), (false, true, 30, 1), (false, true, 31, 1), (false, true, 1, 3), (false, true, 2, 3), (false, true, 4, 3), (false, true, 5, 3), (false, true, 7, 3), (false, true, 8, 3), (false, true, 10, 3), (false, true, 11, 3), (false, true, 13, 3), (false, true, 14, 3), (false, true, 1, 5), (false, true, 2, 5), (false, true, 3, 5), (false, true, 4, 5), (false, true, 6, 5), (false, true, 7, 5)]
def rows5 : List (Bool × Bool × Nat × Nat) := [(false, true, 1, 7), (false, true, 2, 7), (false, true, 3, 7), (false, true, 4, 7), (false, true, 5, 7), (false, true, 6, 7), (false, true, 1, 9), (false, true, 2, 9), (false, true, 1, 11), (false, true, 2, 11), (false, true, 3, 11), (false, true, 1, 13), (false, true, 2, 13), (false, true, 3, 13), (false, true, 1, 15), (false, true, 2, 15), (false, true, 1, 17), (false, true, 1, 19), (false, true, 1, 21), (false, true, 1, 23), (false, true, 1, 25), (false, true, 1, 27), (false, true, 1, 29), (false, true, 1, 31)]
def rows6 : List (Bool × Bool × Nat × Nat) := [(true, false, 0, 1), (true, false, 1, 1), (true, false, 2, 1), (true, false, 3, 1), (true, false, 4, 1), (true, false, 5, 1), (true, false, 6, 1), (true, false, 7, 1), (true, false, 8, 1), (true, false, 9, 1), (true, false, 10, 1), (true, false, 11, 1), (true, false, 12, 1), (true, false, 13, 1), (true, false, 14, 1), (true, false, 15, 1), (true, false, 16, 1), (true, false, 17, 1), (true, false, 18, 1), (true, false, 19, 1), (true, false, 20, 1), (true, false, 21, 1), (true, false, 22, 1), (true, false, 23, 1)]
def rows7 : List (Bool × Bool × Nat × Nat) := [(true, false, 24, 1), (true, false, 25, 1), (true, false, 26, 1), (true, false, 27, 1), (true, false, 28, 1), (true, false, 29, 1), (true, false, 30, 1), (true, false, 31, 1), (true, false, 1, 3), (true, false, 2, 3), (true, false, 4, 3), (true, false, 5, 3), (true, false, 7, 3), (true, false, 8, 3), (true, false, 10, 3), (true, false, 11, 3), (true, false, 13, 3), (true, false, 14, 3), (true, false, 1, 5), (true, false, 2, 5), (true, false, 3, 5), (true, false, 4, 5), (true, false, 6, 5), (true, false, 7, 5)]
def rows8 : List (Bool × Bool × Nat × Nat) := [(true, false, 1, 7), (true, false, 2, 7), (true, false, 3, 7), (true, false, 4, 7), (true, false, 5, 7), (true, false, 6, 7), (true, false, 1, 9), (true, false, 2, 9), (true, false, 1, 11), (true, false, 2, 11), (true, false, 3, 11), (true, false, 1, 13), (true, false, 2, 13), (true, false, 3, 13), (true, false, 1, 15), (true, false, 2, 15), (true, false, 1, 17), (true, false, 1, 19), (true, false, 1, 21), (true, false, 1, 23), (true, false, 1, 25), (true, false, 1, 27), (true, false, 1, 29), (true, false, 1, 31)]
def rows9 : List (Bool × Bool × Nat × Nat) := [(true, true, 0, 1), (true, true, 1, 1), (true, true, 2, 1), (true, true, 3, 1), (true, true, 4, 1), (true, true, 5, 1), (true, true, 6, 1), (true, true, 7, 1), (true, true, 8, 1), (true, true, 9, 1), (true, true, 10, 1), (true, true, 11, 1), (true, true, 12, 1), (true, true, 13, 1), (true, true, 14, 1), (true, true, 15, 1), (true, true, 16, 1), (true, true, 17, 1), (true, true, 18, 1), (true, true, 19, 1), (true, true, 20, 1), (true, true, 21, 1), (true, true, 22, 1), (true, true, 23, 1)]
def rows10 : List (Bool × Bool × Nat × Nat) := [(true, true, 24, 1), (true, true, 25, 1), (true, true, 26, 1), (true, true, 27, 1), (true, true, 28, 1), (true, true, 29, 1), (true, true, 30, 1), (true, true, 31, 1), (true, true, 1, 3), (true, true, 2, 3), (true, true, 4, 3), (true, true, 5, 3), (true, true, 7, 3), (true, true, 8, 3), (true, true, 10, 3), (true, true, 11, 3), (true, true, 13, 3), (true, true, 14, 3), (true, true, 1, 5), (true, true, 2, 5), (true, true, 3, 5), (true, true, 4, 5), (true, true, 6, 5), (true, true, 7, 5)]
def rows11 : List (Bool × Bool × Nat × Nat) := [(true, true, 1, 7), (true, true, 2, 7), (true, true, 3, 7), (true, true, 4, 7), (true, true, 5, 7), (true, true, 6, 7), (true, true, 1, 9), (true, true, 2, 9), (true, true, 1, 11), (true, true, 2, 11), (true, true, 3, 11), (true, true, 1, 13), (true, true, 2, 13), (true, true, 3, 13), (true, true, 1, 15), (true, true, 2, 15), (true, true, 1, 17), (true, true, 1, 19), (true, true, 1, 21), (true, true, 1, 23), (true, true, 1, 25), (true, true, 1, 27), (true, true, 1, 29), (true, true, 1, 31)]
def rows : List (Bool × Bool × Nat × Nat) := rows0 ++ rows1 ++ rows2 ++ rows3 ++ rows4 ++ rows5 ++ rows6 ++ rows7 ++ rows8 ++ rows9 ++ rows10 ++ rows11

def pre506 (g s : Bool) (u v : Nat) : BasisState := fun q =>
  if q = 521 then g
  else if q = 522 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 1 % 2 = 1)
  else if q = 523 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 2 % 2 = 1)
  else if q = 524 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 4 % 2 = 1)
  else if q = 525 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 8 % 2 = 1)
  else if q = 526 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 16 % 2 = 1)
  else if q = 527 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 32 % 2 = 1)
  else if q = 528 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a < 0)
  else if q = 786 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 1 % 2 = 1)
  else if q = 787 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 2 % 2 = 1)
  else if q = 788 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 4 % 2 = 1)
  else if q = 789 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 8 % 2 = 1)
  else if q = 790 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 16 % 2 = 1)
  else if q = 791 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 32 % 2 = 1)
  else if q = 792 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b < 0)
  else false

theorem explicit506 : W.repairedTick base 506 = tick506 := by decide +kernel

def ref : Program := tick506 ++ Forward11Width.candidate

/-- Table reference: tick 506 followed by the base's 13-Toffoli four-tick block, which
`Forward11Width.on_site` proves equal to `Forward11Width.candidate` on every legal stage-507 state. -/
def ref2 : Program := tick506 ++ MorningFour.forward13

def enc (r : Bool × Bool × Nat × Nat) : Nat := encN_t8 (pre506 r.1 r.2.1 r.2.2.1 r.2.2.2) sites

def checkRow (r : Bool × Bool × Nat × Nat) : Bool := agree508 cand ref2 (enc r)

theorem table0 : rows0.all checkRow = true := by decide +kernel
theorem table1 : rows1.all checkRow = true := by decide +kernel
theorem table2 : rows2.all checkRow = true := by decide +kernel
theorem table3 : rows3.all checkRow = true := by decide +kernel
theorem table4 : rows4.all checkRow = true := by decide +kernel
theorem table5 : rows5.all checkRow = true := by decide +kernel
theorem table6 : rows6.all checkRow = true := by decide +kernel
theorem table7 : rows7.all checkRow = true := by decide +kernel
theorem table8 : rows8.all checkRow = true := by decide +kernel
theorem table9 : rows9.all checkRow = true := by decide +kernel
theorem table10 : rows10.all checkRow = true := by decide +kernel
theorem table11 : rows11.all checkRow = true := by decide +kernel

theorem table : rows.all checkRow = true := by
  simp only [rows, List.all_append, table0, table1, table2, table3, table4, table5, table6, table7, table8, table9, table10, table11, Bool.and_self]

theorem tick_counts : toffoliCount tick506 = 10 ∧ measurementCount tick506 = 6 ∧
    Challenge.gateSlots tick506 = 108 := by decide +kernel

theorem cand_counts : toffoliCount cand = 20 ∧ measurementCount cand = 20 ∧
    Challenge.gateSlots cand = 1595 := by
  simp only [cand, toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
  decide +kernel

theorem resources : toffoliCount cand = 20 ∧ toffoliCount ref = 21 ∧
    measurementCount cand = 20 ∧ measurementCount ref = 20 := by
  have c := cand_counts
  have t := tick_counts
  have f := Forward11Width.resources
  simp only [ref, toffoliCount_append, measurementCount_append]
  omega

theorem bsupport0 : wires block0 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical0 : GatePhysical block0 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport1 : wires block1 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical1 : GatePhysical block1 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport2 : wires block2 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical2 : GatePhysical block2 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport3 : wires block3 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical3 : GatePhysical block3 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport4 : wires block4 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical4 : GatePhysical block4 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport5 : wires block5 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical5 : GatePhysical block5 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport6 : wires block6 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical6 : GatePhysical block6 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport7 : wires block7 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical7 : GatePhysical block7 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport8 : wires block8 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical8 : GatePhysical block8 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport9 : wires block9 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical9 : GatePhysical block9 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport10 : wires block10 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical10 : GatePhysical block10 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport11 : wires block11 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical11 : GatePhysical block11 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport12 : wires block12 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical12 : GatePhysical block12 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport13 : wires block13 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical13 : GatePhysical block13 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport14 : wires block14 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical14 : GatePhysical block14 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport15 : wires block15 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical15 : GatePhysical block15 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport16 : wires block16 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical16 : GatePhysical block16 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport17 : wires block17 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical17 : GatePhysical block17 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport18 : wires block18 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical18 : GatePhysical block18 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport19 : wires block19 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical19 : GatePhysical block19 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem bsupport20 : wires block20 ⊆ candSites.toFinset := by decide +kernel
theorem bphysical20 : GatePhysical block20 := Forward11Width.physical_of_all _ (by decide +kernel)

theorem tick_support0 : wires tick506 ⊆ sites.toFinset := by decide +kernel
theorem morning_sub0 : MorningFour.sites.toFinset ⊆ sites.toFinset := by decide +kernel

theorem csupport : wires cand ⊆ candSites.toFinset := by
  simp only [cand, wires_append, Finset.union_subset_iff, bsupport0, bsupport1, bsupport2, bsupport3, bsupport4, bsupport5, bsupport6, bsupport7, bsupport8, bsupport9, bsupport10, bsupport11, bsupport12, bsupport13, bsupport14, bsupport15, bsupport16, bsupport17, bsupport18, bsupport19, bsupport20, and_self]

theorem cand_sub : candSites.toFinset ⊆ sites.toFinset := by
  intro q hq
  exact List.mem_toFinset.mpr (List.mem_of_mem_filter (List.mem_toFinset.mp hq))

theorem support : wires cand ⊆ sites.toFinset ∧ wires ref ⊆ sites.toFinset := by
  constructor
  · exact csupport.trans cand_sub
  · simp only [ref, wires_append, Finset.union_subset_iff]
    exact ⟨tick_support0, Forward11Width.support_all.trans morning_sub0⟩

theorem support2 : wires ref2 ⊆ sites.toFinset := by
  simp only [ref2, wires_append, Finset.union_subset_iff]
  exact ⟨tick_support0, MorningFour.support.1.trans morning_sub0⟩

theorem physical : GatePhysical cand := by
  simp only [cand, gatePhysical_append, bphysical0, bphysical1, bphysical2, bphysical3, bphysical4, bphysical5, bphysical6, bphysical7, bphysical8, bphysical9, bphysical10, bphysical11, bphysical12, bphysical13, bphysical14, bphysical15, bphysical16, bphysical17, bphysical18, bphysical19, bphysical20, and_self]

theorem pre_supp (g s : Bool) (u v : Nat) : ∀ q, pre506 g s u v q = true → q ∈ sites := by
  intro q h
  by_contra hn
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  simp_all [pre506]

theorem sample (r : Bool × Bool × Nat × Nat) (hr : r ∈ rows) (m n : List Bool) :
    run cand m ⟨false,pre506 r.1 r.2.1 r.2.2.1 r.2.2.2⟩ = run ref2 n ⟨false,pre506 r.1 r.2.1 r.2.2.1 r.2.2.2⟩ := by
  have ht := table
  rw [List.all_eq_true] at ht
  have h := ht r hr
  unfold checkRow agree508 at h
  rw [tb_enc_t8 (pre506 r.1 r.2.1 r.2.2.1 r.2.2.2) sites (pre_supp _ _ _ _)]
  change run cand m ⟨false,tbN_t8 (enc r)⟩ = run ref2 n ⟨false,tbN_t8 (enc r)⟩
  cases hq : phaseClean508 ref2 (enc r) with
  | none => simp [hq] at h
  | some v =>
    simp only [hq,decide_eq_true_eq] at h
    rw [CompactCertificates.checked_run cand _ v h m,CompactCertificates.checked_run ref2 _ v hq n]

theorem on_site (r : Bool × Bool × Nat × Nat) (hr : r ∈ rows) (st : State)
    (bits : ∀ q ∈ sites, st.basis q = pre506 r.1 r.2.1 r.2.2.1 r.2.2.2 q) (m n : List Bool) :
    run cand m st = run ref2 n st :=
  Stack5.local_replace cand ref2 sites.toFinset support.1 support2 st
    ⟨false,pre506 r.1 r.2.1 r.2.2.1 r.2.2.2⟩ m n (fun q hq => bits q (List.mem_toFinset.mp hq)) (sample r hr m n)

end ECDSAAdd.Entrant.Five506
namespace ECDSAAdd.Entrant.Five506
open Arithmetic MappedCompressed Secp256k1 History5
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

theorem signed7_cases (a b c d e f g : Wire) (s : BasisState) (v : Int)
    (h : signedRegValue [a,b,c,d,e,f,g] s = v) :
    s a = decide (v % 2 = 1) ∧ s b = decide (v / 2 % 2 = 1) ∧ s c = decide (v / 4 % 2 = 1) ∧
      s d = decide (v / 8 % 2 = 1) ∧ s e = decide (v / 16 % 2 = 1) ∧ s f = decide (v / 32 % 2 = 1) ∧
      s g = decide (v < 0) := by
  unfold signedRegValue signedDecode at h
  simp only [regValue,List.length] at h
  cases ha : s a <;> cases hb : s b <;> cases hc : s c <;> cases hd : s d <;> cases he : s e <;>
    cases hf : s f <;> cases hg : s g <;>
    simp [ha,hb,hc,hd,he,hf,hg] at h <;> subst h <;> decide

theorem retainedA506 : (W.compactSkywalkSignPoolA base 506).retained =
    [base 506,base 507,base 508,base 509,base 510,base 511,base 512] := by decide +kernel
theorem retainedB506 : (W.compactSkywalkSignPoolB base 506).retained =
    [base 770,base 771,base 772,base 773,base 774,base 775,base 776] := by decide +kernel
theorem releasedA506 : ∀ q ∈ [base 513, base 514, base 515, base 516, base 517, base 518, base 519, base 520, base 521, base 522], q ∈ (W.compactSkywalkSignPoolA base 506).released := by decide +kernel
theorem releasedB506 : ∀ q ∈ ([793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803] : List Wire), q ∈ (W.compactSkywalkSignPoolB base 506).released := by decide +kernel

theorem raw506 (x : Nat) (hx0 : 0<x) (hx : x<p) (raw : State)
    (hraw : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 506 raw.basis) :
    ∃ G S : Bool, ∃ u v : Nat, u+v ≤ 32 ∧ 0 < v ∧ v%2=1 ∧ u.gcd v = 1 ∧
      ∀ q∈sites, raw.basis q = pre506 G S u v q := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := (StackOB5.prime_facts x hx0 hx).2.2.2
  have fields := (W.compactSkywalkStage_fields_iff base _ 506 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨readA, readB, prev, -, future, carry, -, cleanA, cleanB⟩ := fields
  obtain ⟨G, S, encoded⟩ := SkywalkTrace.iter_encoded 506 false false (SkywalkNat.init x p) hp0 hpo
  have sum := W.iter_sum_width x p 506 hp0 hx0 hpo hp hx cop (by omega)
  have valid := SkywalkNat.iter_valid 506 (SkywalkNat.init x p) hp0 hpo
  change (SkywalkNat.step^[506] (SkywalkNat.init x p)).u+
    (SkywalkNat.step^[506] (SkywalkNat.init x p)).v ≤ 2^(511-506) at sum
  change SkywalkTrace.next^[506] (SkywalkRails.encode false false (x : Int) (p : Int)) =
    SkywalkRails.encode G S ((SkywalkNat.step^[506] (SkywalkNat.init x p)).u : Int)
      ((SkywalkNat.step^[506] (SkywalkNat.init x p)).v : Int) at encoded
  generalize SkywalkNat.step^[506] (SkywalkNat.init x p) = z at encoded sum valid
  have thirtytwo : (2:Nat)^(511-506) = 32 := by norm_num
  rw [thirtytwo] at sum
  rw [encoded, retainedA506] at readA
  rw [encoded, retainedB506] at readB
  rw [encoded] at prev
  have bA := signed7_cases _ _ _ _ _ _ _ raw.basis _ readA
  have bB := signed7_cases _ _ _ _ _ _ _ raw.basis _ readB
  have cK : ∀ k, k < 257 → raw.basis (base (1540+k)) = false := fun k hk =>
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1540+k, by simp; omega, rfl⟩)
  have rel : ∀ q ∈ [base 513, base 514, base 515, base 516, base 517, base 518, base 519, base 520, base 521, base 522], raw.basis q = false := fun q hq => cleanA q (releasedA506 q hq)
  have relB : ∀ q ∈ ([793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803] : List Wire), raw.basis q = false := fun q hq => cleanB q (releasedB506 q hq)
  have prev' : raw.basis (base 505) = G := by
    have h : skywalkPoolPreviousId 506 = 505 := rfl
    rw [h] at prev
    cases G <;> simpa [SkywalkRails.encode] using prev
  refine ⟨G,S,z.u,z.v,sum,valid.1,valid.2.1,valid.2.2.trans cop,?_⟩
  intro q hq
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prev'
  · simpa [pre506] using bA.1
  · exact bA.2.1
  · exact bA.2.2.1
  · exact bA.2.2.2.1
  · exact bA.2.2.2.2.1
  · exact bA.2.2.2.2.2.1
  · exact bA.2.2.2.2.2.2
  · exact rel (base 513) (by decide)
  · exact relB 793 (by decide)
  · exact relB 794 (by decide)
  · exact relB 795 (by decide)
  · exact relB 796 (by decide)
  · exact relB 797 (by decide)
  · exact relB 798 (by decide)
  · exact relB 799 (by decide)
  · exact relB 800 (by decide)
  · exact relB 801 (by decide)
  · simpa [pre506] using bB.1
  · exact bB.2.1
  · exact bB.2.2.1
  · exact bB.2.2.2.1
  · exact bB.2.2.2.2.1
  · exact bB.2.2.2.2.2.1
  · exact bB.2.2.2.2.2.2
  · exact (future 506 (by omega) (by omega)).2
  · exact (future 507 (by omega) (by omega)).2
  · exact (future 508 (by omega) (by omega)).2
  · exact (future 509 (by omega) (by omega)).2
  · exact (future 510 (by omega) (by omega)).2
  · exact cK 0 (by omega)
  · exact cK 1 (by omega)
  · exact cK 2 (by omega)
  · exact cK 3 (by omega)
  · exact cK 4 (by omega)
  · exact relB 802 (by decide)
  · exact relB 803 (by decide)

end ECDSAAdd.Entrant.Five506

namespace ECDSAAdd.Entrant.Five506
open Arithmetic MappedCompressed Secp256k1 History5 OB5 Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward Rolling1588.Integer.regularForward
  Rolling1588TickGap.forward tick506 cand MorningPlacement.merged Forward11Width.candidate

theorem encN_congr (f g : BasisState) (l : List Wire) (h : ∀ q ∈ l, f q = g q) :
    encN_t8 f l = encN_t8 g l := by
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [encN_t8, foldl_tb_t8, Nat.zero_testBit, Bool.false_or]
  by_cases hq : q ∈ l
  · simp [hq, h q hq]
  · simp [hq]

def legalCodes : List Nat := [27459190640522438859927603196325572869077741200573221637577853836742172733590624208490238562645818219909185245565923432148487951998866575250296113164460228608, 406983302788077043095694079023514269845261128071039316430435657456301100941017596219917109865196132279654253838655162593429242965695252692757689614514762183867716890353291000549678697629232525681989817904613609417521679593703338900717568, 406983302788077043095694079023514269845261128071039316430435657456301100941017637408703070648854422171059048327014466210041043825527709059538444727773862569804029625711134969277008561407100874567138040636541607717384555037873085591060480, 406983302788077043095694079023514269845261128071039316430435657456301100941017692327084351693732142026265440978160204365523444971970984215246118212119329751052446606188260260913448379777592006414002337612445605450535055630099414511517696, 406983302788077043095694079023514269845261128071039316430435657456301100941017747245465632738609861881471833629305942521005846118414259370953791696464796932300863586665385552549888198148083138260866634588349603183685556222325743431974912, 813966605576154086191388158047028539690522256142078632860871314912602201882035206169429539991611694523110105840096759725729086218001324174442297600115891163047538025825863324008467349851087834325695710053203218268330984335463260031549440, 813966605576154086191388158047028539690522256142078632860871314912602201882035247358215500775269984414514900328456063342340887077833780541223052713374991548983850761183707292735797213628956183210843932785131216568193859779633006721892352, 813966605576154086191388158047028539690522256142078632860871314912602201882035302276596781820147704269721292979601801497823288224277055696930726197720458730232267741660832584372237031999447315057708229761035214301344360371859335642349568, 813966605576154086191388158047028539690522256142078632860871314912602201882036908639249252382821010034508278025614642545683521757742854001380175614825373781748464420616747364738101719336312921578488916306227147995996502694479456565723136, 1220949908364231129287082237070542809535783384213117949291306972368903302823052816118941970118027256766565957841538356858028929470307395656126905585717020142227359161298435647467256002072943142969401602201792827119140289077223181162381312, 1220949908364231129287082237070542809535783384213117949291306972368903302823052857307727930901685546657970752329897660474640730330139852022907660698976120528163671896656279616194585865850811491854549824933720825419003164521392927852724224, 1220949908364231129287082237070542809535783384213117949291306972368903302823054463670380401464358852422757737375910501522500963863605650327357110116081035579679868575612194396560450553187677098375330511478912759113655306844013048776097792, 1627933211152308172382776316094057079381044512284157265721742629825204403764070371150073119199565099154815417191834215834846371576170191982103840086972681940158763316293882679289604835924307319766243197374478438236799093226756773372755968, 1627933211152308172382776316094057079381044512284157265721742629825204403764070426068454400244442819010021809842979953990328772722613467137811513571318149121407180296771007970926044654294798451613107494350382435969949593818983102293213184, 1627933211152308172382776316094057079381044512284157265721742629825204403764070467257240361028101108901426604331339257606940573582445923504592268684577249507343493032128851939653374518072666800498255717082310434269812469263152848983556096, 1627933211152308172382776316094057079381044512284157265721742629825204403764070522175621642072978828756632996982484995762422974728889198660299942168922716688591910012605977231289814336443157932345120014058214432002962969855379177904013312, 1627933211152308172382776316094057079381044512284157265721742629825204403764072018701511550545896694811007196726206360499318405969468446653334044617336697377611272730607641428382799387039041275172172106651598370231314110993546640986472448, 1627933211152308172382776316094057079381044512284157265721742629825204403764072073619892831590774414666213589377352098654800807115911721809041718101682164558859689711084766720019239205409532407019036403627502367964464611585772969906929664, 2034916513940385215478470395117571349226305640355196582152178287281505504705087981099585549325980661398271269193275812967146214828476263463788448072573810919338584451766455002748393488146162628409949089523068047087608397968516694503587840, 2034916513940385215478470395117571349226305640355196582152178287281505504705088036017966830370858381253477661844421551122628615974919538619496121556919278100587001432243580294384833306516653760256813386498972044820758898560743023424045056, 2034916513940385215478470395117571349226305640355196582152178287281505504705088077206752791154516671144882456332780854739240416834751994986276876670178378486523314167601424263112163170294522109141961609230900043120621774004912770114387968, 2034916513940385215478470395117571349226305640355196582152178287281505504705088132125134072199394391000088848983926592894722817981195270141984550154523845667771731148078549554748602988665013240988825906206804040853772274597139099034845184, 2034916513940385215478470395117571349226305640355196582152178287281505504705089573732642699627434537199256656076502219476135848075331242979310979118592359175542676885603088460205148220890405451969013701824283981348972915143080233196847104, 2034916513940385215478470395117571349226305640355196582152178287281505504705089628651023980672312257054463048727647957631618249221774518135018652602937826356791093866080213751841588039260896583815877998800187979082123415735306562117304320, 2441899816728462258574164474141085619071566768426235898582613944737806605646105536130716698407518503786520728543571671943963656934339059789765382573829472717269988606761902034570742321997526805206790684695753658205267202118050286713962496, 2441899816728462258574164474141085619071566768426235898582613944737806605646105645967479260497273943496933513845863148254928459227225610101180729542520407079766822567716152617843621958738509068900519278647561653671568203302502944554876928, 2441899816728462258574164474141085619071566768426235898582613944737806605646105687156265221280932233388338308334222451871540260087058066467961484655779507465703135303073996586570951822516377417785667501379489651971431078746672691245219840, 2441899816728462258574164474141085619071566768426235898582613944737806605646107128763773848708972379587506115426798078452953290181194039305287913619848020973474081040598535492027497054741769628765855296996969592466631719292613825407221760, 2441899816728462258574164474141085619071566768426235898582613944737806605646107238600536410798727819297918900729089554763918092474080589616703260588538955335970915001552786075300376691482751892459583890948777587932932720477066483248136192, 2848883119516539301669858553164599888916827896497275215013049602194107706587123146080229128533934066029976580545013269076263500186645131271449990559430601696449809742234474358029530974219382113850496576844343267056076506859810207844794368, 2848883119516539301669858553164599888916827896497275215013049602194107706587123200998610409578811785885182973196159007231745901333088406427157664043776068877698226722711599649665970792589873245697360873820247264789227007452036536765251584, 2848883119516539301669858553164599888916827896497275215013049602194107706587123255916991690623689505740389365847304745387228302479531681582865337528121536058946643703188724941302410610960364377544225170796151262522377508044262865685708800, 2848883119516539301669858553164599888916827896497275215013049602194107706587123297105777651407347795631794160335664049003840103339364137949646092641380636444882956438546568910029740474738232726429373393528079260822240383488432612376051712, 2848883119516539301669858553164599888916827896497275215013049602194107706587124683794904997790510221975755574777093937429770732287056835631264848121103682771405485195593982523849845888593133805562696892169655203584290523442147417617596416, 2848883119516539301669858553164599888916827896497275215013049602194107706587124738713286278835387941830961967428239675585253133433500110786972521605449149952653902176071107815486285706963624937409561189145559201317441024034373746538053632, 2848883119516539301669858553164599888916827896497275215013049602194107706587124793631667559880265661686168360079385413740735534579943385942680195089794617133902319156548233107122725525334116069256425486121463199050591524626600075458510848, 3255866422304616344765552632188114158762089024568314531443485259650408807528140701111360277615471908418226039895309128053080942292507927597426925060686263494381213897229921389851879808070746290647338172017028878173735311009343800055169024, 3255866422304616344765552632188114158762089024568314531443485259650408807528140756029741558660349628273432432546454866208563343438951202753134598545031730675629630877707046681488319626441237422494202468992932875906885811601570128975626240, 3255866422304616344765552632188114158762089024568314531443485259650408807528140810948122839705227348128638825197600604364045744585394477908842272029377197856878047858184171973124759444811728554341066765968836873640036312193796457896083456, 3255866422304616344765552632188114158762089024568314531443485259650408807528140865866504120750105067983845217848746342519528145731837753064549945513722665038126464838661297264761199263182219686187931062944740871373186812786022786816540672, 3255866422304616344765552632188114158762089024568314531443485259650408807528140907055290081533763357875250012337105646136139946591670209431330700626981765424062777574019141233488529126960088035073079285676668869673049688230192533506883584, 3255866422304616344765552632188114158762089024568314531443485259650408807528142238826036146872048064364005034127389796406588174392919631957241782622359344569336889350589429555672194722444497982359538487342340814701949327591681009827971072, 3255866422304616344765552632188114158762089024568314531443485259650408807528142293744417427916925784219211426778535534562070575539362907112949456106704811750585306331066554847308634540814989114206402784318244812435099828183907338748428288, 3255866422304616344765552632188114158762089024568314531443485259650408807528142348662798708961803504074417819429681272717552976685806182268657129591050278931833723311543680138945074359185480246053267081294148810168250328776133667668885504, 3255866422304616344765552632188114158762089024568314531443485259650408807528142403581179990006681223929624212080827010873035377832249457424364803075395746113082140292020805430581514177555971377900131378270052807901400829368359996589342720, 3662849725092693387861246711211628428607350152639353847873920917106709908469158311060872707741887470661681891896750725185380785544813999079111533046287392473561035032702493713310668460292601599291044064165618487024544615751103721186000896, 3662849725092693387861246711211628428607350152639353847873920917106709908469158475816016550876520630227301069850187939651827988984143824546234553499323794017306285974133869588219987915404074994831636955093330480223996117527782707947372544, 3662849725092693387861246711211628428607350152639353847873920917106709908469158517004802511660178920118705864338547243268439789843976280913015308612582894403242598709491713556947317779181943343716785177825258478523858992971952454637715456, 3662849725092693387861246711211628428607350152639353847873920917106709908469159793857167295953585906752254493477685655383405616498782428283218717123615006367268293505584876587494543556295862159156380082515026425819608131741214602038345728, 3662849725092693387861246711211628428607350152639353847873920917106709908469159958612311139088219066317873671431122869849852819938112253750341737576651407911013544447016252462403863011407335554696972973442738419019059633517893588799717376, 4069833027880770430956940790235142698452611280710393164304356574563011009410175866092003856823425313049931351247046584162198227650676795405088467547543054271492439187697940745133017294143965776087885659338304098142203419900637313396375552, 4069833027880770430956940790235142698452611280710393164304356574563011009410175921010385137868303032905137743898192322317680628797120070560796141031888521452740856168175066036769457112514456907934749956314208095875353920492863642316832768, 4069833027880770430956940790235142698452611280710393164304356574563011009410176030847147699958058472615550529200483798628645431090006620872211488000579455815237690129129316620042336749255439171628478550266016091341654921677316300157747200, 4069833027880770430956940790235142698452611280710393164304356574563011009410176085765528981002936192470756921851629536784127832236449896027919161484924922996486107109606441911678776567625930303475342847241920089074805422269542629078204416, 4069833027880770430956940790235142698452611280710393164304356574563011009410176126954314941786594482362161716339988840400739633096282352394699916598184023382422419844964285880406106431403798652360491069973848087374668297713712375768547328, 4069833027880770430956940790235142698452611280710393164304356574563011009410177348888298445035123749140503952827981514360223058604645224609195651624870668165199697660580323619316892390147226335953221677687712036937266935890748194248720384, 4069833027880770430956940790235142698452611280710393164304356574563011009410177403806679726080001468995710345479127252515705459751088499764903325109216135346448114641057448910953332208517717467800085974663616034670417436482974523169177600, 4069833027880770430956940790235142698452611280710393164304356574563011009410177513643442288169756908706123130781418728826670262043975050076318672077907069708944948602011699494226211845258699731493814568615424030136718437667427181010092032, 4069833027880770430956940790235142698452611280710393164304356574563011009410177568561823569214634628561329523432564466982152663190418325232026345562252536890193365582488824785862651663629190863340678865591328027869868938259653509930549248, 4476816330668847474052634869258656968297872408781432480734792232019312110351193695715041411129351754714212773853071133916427675488755967509603769470526051975665928245079014235137565219847785612119048739390509697925614727011302550209036288, 4476816330668847474052634869258656968297872408781432480734792232019312110351193736903827371913010044605617568341430437533039476348588423876384524583785152361602240980436858203864895083625653961004196962122437696225477602455472296899379200, 4476816330668847474052634869258656968297872408781432480734792232019312110351194903919429594116661591528753412178277373337040500710508020935172586126126329963131101815575770651139241223998590512750063272860397648054925740040281786459095040, 4883799633456924517148328948282171238143133536852471797165227889475613211292211031072647436031378717681636662598784040271315513008845663212750010034399845048603664478165960100414154780217185261528433146659579318110671528791930826737582080, 4883799633456924517148328948282171238143133536852471797165227889475613211292211305664553841255767316957668625854512731048727518741062038991288377456127180954845749380551586558596353872069640920762754631539099306776424031753062471339868160, 4883799633456924517148328948282171238143133536852471797165227889475613211292211346853339802039425606849073420342872034665339319600894495358069132569386281340782062115909430527323683735847509269647902854271027305076286907197232218030211072, 4883799633456924517148328948282171238143133536852471797165227889475613211292212458950560743198199433917002871528573232313857942816370817261149520627381991761062505970571217682961590057849954689546904868033083259172584544189815378669469696, 4883799633456924517148328948282171238143133536852471797165227889475613211292212733542467148422588033193034834784301923091269948548587193039687888049109327667304590872956844141143789149702410348781226352912603247838337047150947023271755776, 5290782936245001560244023027305685507988394664923511113595663546931914312233228915614066271382182879201124477855954328181027361993368110472972985441728309934025570516024158882055142524291496229406460523687688915627233336494822392470700032, 5290782936245001560244023027305685507988394664923511113595663546931914312233228956802852232165841169092529272344313631797639162853200566839753740554987410319961883251382002850782472388069364578291608746419616913927096211938992139161042944, 5290782936245001560244023027305685507988394664923511113595663546931914312233230013981691892279737276305252330878869091290675384922233613587126455128637653558993910125566664714783938891701318866343746463205768870290243348339348970879844352, 5697766239033078603339717106329199777833655792994550430026099204388215413174246196053291015239332122313341973950521496380432798367014531020411552521256635825714889768633979455695292266290404746968980633980854538079139637683224340078788608, 5697766239033078603339717106329199777833655792994550430026099204388215413174246525563578701508598441444580329857395925313327205245674181954657593427329438913205391651496731205513931176513351538050166415836278524478042641236582313601531904, 5697766239033078603339717106329199777833655792994550430026099204388215413174246566752364662292256731335985124345755228929939006105506638321438348540588539299141704386854575174241261040291219886935314638568206522777905516680752060291874816, 5697766239033078603339717106329199777833655792994550430026099204388215413174247569012823041361275118693501790229164950267492827028096409913103389629893315356925314280562111746606287725552683043140588058378454481407902152488882563090219008, 5697766239033078603339717106329199777833655792994550430026099204388215413174247898523110727630541437824740146136039379200387233906756060847349430535966118444415816163424863496424926635775629834221773840233878467806805156042240536612962304, 6104749541821155646435411185352714047678916921065589746456534861844516514115264135513091131635014003688036181858837522445627048497980253436342201412930567892385212786969303528972719828735206846693872307984868133328851945978342234732363776, 6104749541821155646435411185352714047678916921065589746456534861844516514115264176701877092418672293579440976347196826062238849357812709803122956526189668278321525522327147497700049692513075195579020530716796131628714821422511981422706688, 6104749541821155646435411185352714047678916921065589746456534861844516514115265124043954190442812961081751249579460809244310269133959206239080324131148977154856718435557558778428636559404047219937429653551140092525560956638416155300593664, 6511732844609232689531105264376228317524178049136629062886970519300817615056281361033934594447285526945047285302258952489550083725183398828073095008113426602826115059101998810976429752363624232409528121302129758047607746574517853419995136, 6511732844609232689531105264376228317524178049136629062886970519300817615056281745462603561761429565931492033860279119577926891750286324918026809398531696871565033922441875852431508480957062155337578200133457742179661250720102155863195648, 6511732844609232689531105264376228317524178049136629062886970519300817615056282679075085339524350803470000708929756668221127711239822002565057258632404638952788122590553005810250985393255411396734271248723825703643219760787949747510968320, 6511732844609232689531105264376228317524178049136629062886970519300817615056283063503754306838494842456445457487776835309504519264924928655010973022822909221527041453892882851706064121848849319662321327555153687775273264933534049954168832, 19942181836615775111689009872152199222417795275480926505091347215358753946109861981372817938953880172318431269326733579917232700446683462533369178802755111489212355460283476537479386955757806448068327815178474871092672672574501708223217664, 20349165139403852154784703951175713492263056403551965821521782872815055047050879536403949088035418014706680728677029438894050142552546258859346113304010773287143759615278923569301735789609170624865169410351160482210331476724035300433592320, 20756148442191929197880398030199227762108317531623005137952218530271356147991897091435080237116955857094930188027325297870867584658409055185323047805266435085075163770274370601124084623460534801662011005523846093327990280873568892643966976, 21163131744980006240976092109222742031953578659694044454382654187727657248932914646466211386198493699483179647377621156847685026764271851511299982306522096883006567925269817632946433457311898978458852600696531704445649085023102484854341632, 21570115047768083284071786188246256301798839787765083770813089845183958349873932201497342535280031541871429106727917015824502468870134647837276916807777758680937972080265264664768782291163263155255694195869217315563307889172636077064716288, 21977098350556160327167480267269770571644100915836123087243525502640259450814949756528473684361569384259678566078212874801319910975997444163253851309033420478869376235260711696591131125014627332052535791041902926680966693322169669275090944, 22384081653344237370263174346293284841489362043907162403673961160096560551755967311559604833443107226647928025428508733778137353081860240489230785810289082276800780390256158728413479958865991508849377386214588537798625497471703261485465600, 22791064956132314413358868425316799111334623171978201720104396817552861652696984866590735982524645069036177484778804592754954795187723036815207720311544744074732184545251605760235828792717355685646218981387274148916284301621236853695840256, 23198048258920391456454562504340313381179884300049241036534832475009162753638002421621867131606182911424426944129100451731772237293585833141184654812800405872663588700247052792058177626568719862443060576559959760033943105770770445906214912, 23605031561708468499550256583363827651025145428120280352965268132465463854579019976652998280687720753812676403479396310708589679399448629467161589314056067670594992855242499823880526460420084039239902171732645371151601909920304038116589568, 24012014864496545542645950662387341920870406556191319669395703789921764955520037531684129429769258596200925862829692169685407121505311425793138523815311729468526397010237946855702875294271448216036743766905330982269260714069837630326964224, 24012014864496545542645950662387341920870406556191319669395703789921764955520037586602510710814136316056132255480837907840889522651754700948846197299657196649774813990715072147339315112641939347883608063881234980002411214662063959247421440, 24418998167284622585741644741410856190715667684262358985826139447378066056461055086715260578850796438589175322179988028662224563611174222119115458316567391266457801165233393887525224128122812392833585362078016593386919518219371222537338880, 24418998167284622585741644741410856190715667684262358985826139447378066056461055141633641859895674158444381714831133766817706964757617497274823131800912858447706218145710519179161663946493303524680449659053920591120070018811597551457796096, 24825981470072699628837338820434370460560928812333398302256575104834367157402072641746391727932334280977424781530283887639042005717037018445092392817823053064389205320228840919347572961974176569630426957250702204504578322368904814747713536, 25232964772860776671933032899457884730406189940404437618687010762290668258343090196777522877013872123365674240880579746615859447822899814771069327319078714862320609475224287951169921795825540746427268552423387815622237126518438406958088192, 25232964772860776671933032899457884730406189940404437618687010762290668258343090251695904158058749843220880633531725484771341848969343089926777000803424182043569026455701413242806361614196031878274132849399291813355387627110664735878545408, 25639948075648853715028726978481399000251451068475476935117446419746969359284107751808654026095409965753923700230875605592676889928762611097046261820334376660252013630219734982992270629676904923224110147596073426739895930667971999168462848, 25639948075648853715028726978481399000251451068475476935117446419746969359284107806727035307140287685609130092882021343748159291075205886252753935304679843841500430610696860274628710448047396055070974444571977424473046431260198328088920064, 25639948075648853715028726978481399000251451068475476935117446419746969359284107861645416588185165405464336485533167081903641692221649161408461608789025311022748847591173985566265150266417887186917838741547881422206196931852424657009377280]

theorem legal_codes_spec : ∀ g s : Bool, ∀ uv ∈ MorningFour.pairs, Forward11Width.legal uv g = true →
    encN_t8 (MorningFour.pre507 g s uv.1 uv.2) MorningFour.sites ∈ legalCodes := by decide +kernel

def goodRow (r : Bool × Bool × Nat × Nat) : Bool :=
  decide (encN_t8 (tbN_t8 (runN_t8 tick506 [] (false, enc r)).2) MorningFour.sites ∈ legalCodes)

def cv (v : Nat) : Bool :=
  (List.range 33).all fun u => [false, true].all fun g => [false, true].all fun s =>
    !(decide (u+v ≤ 32) && decide (v%2=1) && decide (u.gcd v = 1) && goodRow (g,s,u,v)) || decide ((g,s,u,v) ∈ rows)

theorem cv0 : cv 0 = true := by decide +kernel
theorem cv1 : cv 1 = true := by decide +kernel
theorem cv2 : cv 2 = true := by decide +kernel
theorem cv3 : cv 3 = true := by decide +kernel
theorem cv4 : cv 4 = true := by decide +kernel
theorem cv5 : cv 5 = true := by decide +kernel
theorem cv6 : cv 6 = true := by decide +kernel
theorem cv7 : cv 7 = true := by decide +kernel
theorem cv8 : cv 8 = true := by decide +kernel
theorem cv9 : cv 9 = true := by decide +kernel
theorem cv10 : cv 10 = true := by decide +kernel
theorem cv11 : cv 11 = true := by decide +kernel
theorem cv12 : cv 12 = true := by decide +kernel
theorem cv13 : cv 13 = true := by decide +kernel
theorem cv14 : cv 14 = true := by decide +kernel
theorem cv15 : cv 15 = true := by decide +kernel
theorem cv16 : cv 16 = true := by decide +kernel
theorem cv17 : cv 17 = true := by decide +kernel
theorem cv18 : cv 18 = true := by decide +kernel
theorem cv19 : cv 19 = true := by decide +kernel
theorem cv20 : cv 20 = true := by decide +kernel
theorem cv21 : cv 21 = true := by decide +kernel
theorem cv22 : cv 22 = true := by decide +kernel
theorem cv23 : cv 23 = true := by decide +kernel
theorem cv24 : cv 24 = true := by decide +kernel
theorem cv25 : cv 25 = true := by decide +kernel
theorem cv26 : cv 26 = true := by decide +kernel
theorem cv27 : cv 27 = true := by decide +kernel
theorem cv28 : cv 28 = true := by decide +kernel
theorem cv29 : cv 29 = true := by decide +kernel
theorem cv30 : cv 30 = true := by decide +kernel
theorem cv31 : cv 31 = true := by decide +kernel
theorem cv32 : cv 32 = true := by decide +kernel

theorem rows_complete : ∀ v, v < 33 → ∀ u, u < 33 → ∀ g s : Bool,
    (u+v ≤ 32 ∧ v%2=1 ∧ u.gcd v = 1 ∧ goodRow (g,s,u,v) = true) → (g,s,u,v) ∈ rows := by
  intro v hv u hu g s h
  have c1 : cv v = true := by
    interval_cases v <;> simp only [cv0, cv1, cv2, cv3, cv4, cv5, cv6, cv7, cv8, cv9, cv10, cv11, cv12, cv13, cv14, cv15, cv16, cv17, cv18, cv19, cv20, cv21, cv22, cv23, cv24, cv25, cv26, cv27, cv28, cv29, cv30, cv31, cv32]
  simp only [cv, List.all_eq_true, List.mem_range] at c1
  have c2 := c1 u hu g (by cases g <;> simp) s (by cases s <;> simp)
  obtain ⟨h1, h2, h3, h4⟩ := h
  simpa [h1, h2, h3, h4] using c2

theorem tick_support : wires tick506 ⊆ sites.toFinset := by decide +kernel
theorem morning_sub : ∀ q ∈ MorningFour.sites, q ∈ sites := by decide +kernel

theorem pack506 (isA : Bool) : Rolling1588.Integer.packAfter base isA 506 = [] := by
  simp only [Rolling1588.Integer.packAfter, show History5.packDue 506 = false from by decide, Bool.false_eq_true, if_false]

theorem prefix_avoids (isA : Bool) : ∀ n, n ≤ 506 → ∀ q ∈ sites, q ∉ wires (encodePrefix base isA n) := by
  intro n hn q hq hw
  rw [prefix_support_eq] at hw
  induction n with
  | zero => simp [History5.encodePrefix, wires] at hw
  | succ n ih =>
    simp only [History5.encodePrefix, wires_append, Finset.mem_union] at hw
    rcases hw with hw | hw
    · exact ih (by omega) hw
    · cases due : History5.packDue n
      · simp [History5.packAfter, due, wires] at hw
      · simp only [History5.packAfter, due, if_true] at hw
        obtain ⟨j, rfl⟩ := History5.history_gate_mem base (n-5) _ (Or.inl rfl) _ hw
        have b := History5.packDue_true n due
        simp only [sites, List.mem_cons, List.not_mem_nil, or_false] at hq
        fin_cases j <;> simp [History5.historyMap, History5.historyId, base] at hq <;> omega

theorem post507 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (a : State)
    (hs : Stage base isA x p 506 a.basis) (m : List Bool) :
    ∃ g' s' : Bool, ∃ uv' : Nat × Nat, uv' ∈ MorningFour.pairs ∧ Forward11Width.legal uv' g' = true ∧
      ∀ q ∈ MorningFour.sites, (run tick506 m a).basis q = MorningFour.pre507 g' s' uv'.1 uv'.2 q := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have next := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 506
    hp0 hx0 hpo hp gap hx cop (by omega) a m hs).2
  rw [explicit506, pack506 isA, List.append_nil] at next
  obtain ⟨raw7,hraw7,hbits7⟩ := next
  obtain ⟨g',s',uv',mem',width,oriented,reads7⟩ := MorningWidth.raw507 x hx0 hx raw7 hraw7
  refine ⟨g', s', uv', (List.mem_filter.mp mem').1, Forward11Width.legal_of uv' g' width oriented, ?_⟩
  intro q hq
  rw [hbits7, ←reads7 q hq]
  apply run_preserves_outside
  rcases MorningPlacement.layouts q hq with h|h|h|h
  all_goals
    exact fun hh => Finset.disjoint_left.mp
      (prefix_disjoint_layout base isA base_pool_nodup 507 _ (by omega) (by omega)) hh h

theorem at_stage5 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (a : State)
    (hs : Stage base isA x p 506 a.basis) (r : List Bool) :
    run cand r a = run ref r a := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have hs0 := hs
  obtain ⟨raw,hraw,hbits⟩ := hs
  obtain ⟨G,S,u,v,hsum,hv0,hvo,hg,reads⟩ := raw506 x hx0 hx raw hraw
  have bits : ∀ q ∈ sites, a.basis q = pre506 G S u v q := by
    intro q hq
    rw [hbits, ←reads q hq]
    exact run_preserves_outside _ _ _ q (prefix_avoids isA 506 (le_refl _) q hq)
  have mem : (G,S,u,v) ∈ rows := by
    have next := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 506
      hp0 hx0 hpo hp gap hx cop (by omega) a [] hs0).2
    rw [explicit506, pack506 isA, List.append_nil] at next
    obtain ⟨raw7,hraw7,hbits7⟩ := next
    obtain ⟨g',s',uv',mem',width,oriented,reads7⟩ := MorningWidth.raw507 x hx0 hx raw7 hraw7
    have hl := Forward11Width.legal_of uv' g' width oriented
    have oldmem : uv' ∈ MorningFour.pairs := (List.mem_filter.mp mem').1
    have b7 : ∀ q ∈ MorningFour.sites, (run tick506 [] a).basis q = MorningFour.pre507 g' s' uv'.1 uv'.2 q := by
      intro q hq
      rw [hbits7, ←reads7 q hq]
      apply run_preserves_outside
      rcases MorningPlacement.layouts q hq with h|h|h|h
      all_goals
        exact fun hh => Finset.disjoint_left.mp
          (prefix_disjoint_layout base isA base_pool_nodup 507 _ (by omega) (by omega)) hh h
    have s7 : ∀ q ∈ MorningFour.sites, (run tick506 [] a).basis q =
        (run tick506 [] ⟨false, pre506 G S u v⟩).basis q := fun q hq =>
      site_run tick506 sites tick_support a ⟨false, pre506 G S u v⟩ bits [] q (morning_sub q hq)
    have good : goodRow (G,S,u,v) = true := by
      unfold goodRow
      rw [decide_eq_true_eq]
      have e1 : tbN_t8 (runN_t8 tick506 [] (false, enc (G,S,u,v))).2 =
          (run tick506 [] ⟨false, pre506 G S u v⟩).basis := by
        rw [tb_enc_t8 (pre506 G S u v) sites (pre_supp G S u v), run_sim_t8]
        rfl
      rw [e1, encN_congr _ (MorningFour.pre507 g' s' uv'.1 uv'.2) _
        (fun q hq => (s7 q hq).symm.trans (b7 q hq))]
      exact legal_codes_spec g' s' uv' oldmem hl
    exact rows_complete v (by omega) u (by omega) G S ⟨hsum, hvo, hg, good⟩
  rw [on_site (G,S,u,v) mem a bits r r, ref2, ref, run_append, run_append]
  obtain ⟨g',s',uv',om,hl',b7'⟩ := post507 isA x hx0 hx a hs0 (r.take (measurementCount tick506))
  rw [Forward11Width.on_site g' s' uv' om hl' _ b7' (r.drop (measurementCount tick506))
    (r.drop (measurementCount tick506))]

end ECDSAAdd.Entrant.Five506

namespace ECDSAAdd.Entrant.Five506
open Arithmetic MappedCompressed Secp256k1 History5 OB5 Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward Rolling1588.Integer.regularForward
  Rolling1588TickGap.forward tick506 cand MorningPlacement.merged Forward11Width.candidate

def merged5 : Program := renameProgram (sig 510) cand
def prior5 : Program := renameProgram (sig 506) tick506 ++ MorningPlacement.merged

theorem tick_ranges506 : TickRanges.tick base 506 = tick506 := by
  rw [← explicit506]
  unfold TickRanges.tick TickGap.tick
  simp only [show ¬(225 ≤ (506:Nat) ∧ (506:Nat) ≤ 254) from by decide,
    show ¬(255 ≤ (506:Nat) ∧ (506:Nat) ≤ 286) from by decide, if_false]

theorem packFirst506 (isA : Bool) : packFirst base isA 506 = [] := by
  simp only [packFirst, show ¬(506:Nat) = 5 from by decide, if_false, pack506 isA]

theorem forward_snoc (isA : Bool) (i n : Nat) :
    Rolling1588TickGap.forward isA i (n+1) = Rolling1588TickGap.forward isA i n ++
      renameProgram (sig (i+n)) (TickRanges.tick base (i+n) ++ packFirst base isA (i+n)) := by
  induction n generalizing i with
  | zero => simp [Rolling1588TickGap.forward]
  | succ n ih =>
    rw [Rolling1588TickGap.forward, ih (i+1), Rolling1588TickGap.forward]
    simp only [List.append_assoc, show i+1+n = i+(n+1) by omega]

theorem shape (isA : Bool) : Rolling1588TickGap.stackForward0 isA =
    Rolling1588TickGap.forward isA 1 505 ++ (prior5 ++ ForwardSixPlacement.after isA) := by
  rw [Rolling1588TickGap.stackForward0, show (506:Nat) = 505+1 from rfl, forward_snoc]
  simp only [show (1:Nat)+505 = 506 from rfl, tick_ranges506, packFirst506, List.append_nil,
    prior5, List.append_assoc]

theorem place5 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 506 a.basis) (r : List Bool) :
    run merged5 r (pullState (sig 505) a) = run prior5 r (pullState (sig 505) a) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have z6 := stage_zero_gen isA x 506 506 (le_refl _) (by omega) a.basis stage
  have p6 : pullState (sig 505) a = pullState (sig 506) a := OB5.pull_step 506 (by omega) a z6.1 z6.2
  have align (v : State) (i : Nat) (hi : i ≤ 507) (h : Stage base isA x p i v.basis) :
      pullState (sig 506) v = pullState (sig 510) v := by
    have z7 := stage_zero_gen isA x i 507 hi (by omega) v.basis h
    have z8 := stage_zero_gen isA x i 508 (by omega) (by omega) v.basis h
    have z9 := stage_zero_gen isA x i 509 (by omega) (by omega) v.basis h
    have z10 := stage_zero_gen isA x i 510 (by omega) (by omega) v.basis h
    exact (OB5.pull_step 507 (by omega) v z7.1 z7.2).trans
      ((OB5.pull_step 508 (by omega) v z8.1 z8.2).trans
        ((OB5.pull_step 509 (by omega) v z9.1 z9.2).trans (OB5.pull_step 510 (by omega) v z10.1 z10.2)))
  let k := measurementCount tick506
  let b := run tick506 (r.take k) a
  have s7 : Stage base isA x p 507 b.basis := by
    have next := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 506
      hp0 hx0 hpo hp gap hx cop (by omega) a (r.take k) stage).2
    simpa only [explicit506, pack506 isA, List.append_nil, b] using next
  rw [p6, prior5, run_append, (renameProgram_counts _ _).2, OB5.run_rename 506 (by omega)]
  change run merged5 r (pullState (sig 506) a) = run MorningPlacement.merged (r.drop k) (pullState (sig 506) b)
  rw [align b 507 (le_refl _) s7, align a 506 (by omega) stage, merged5, MorningPlacement.merged,
    OB5.run_rename 510 (by omega), OB5.run_rename 510 (by omega), at_stage5 isA x hx0 hx a stage r,
    ref, run_append]

def stackForward5 (isA : Bool) : Program :=
  Rolling1588TickGap.forward isA 1 505 ++ (merged5 ++ ForwardSixPlacement.after isA)

theorem counts5 : measurementCount merged5 = measurementCount prior5 ∧
    toffoliCount merged5 + 1 = toffoliCount prior5 := by
  have r := resources
  have mp := MorningPlacement.prior_resources
  have f := Forward11Width.resources
  simp only [merged5, prior5, MorningPlacement.merged, toffoliCount_append, measurementCount_append,
    (renameProgram_counts _ _).1, (renameProgram_counts _ _).2]
  have t := tick_counts
  simp only [ref, toffoliCount_append, measurementCount_append] at r
  omega

theorem stackForward5_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward5 isA) m s = run (Rolling1588TickGap.stackForward0 isA) m s := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  rw [shape, stackForward5]
  simp only [run_append (Rolling1588TickGap.forward isA 1 505), run_append merged5, run_append prior5,
    counts5.1]
  generalize hK : measurementCount (Rolling1588TickGap.forward isA 1 505) = K
  have init := stage_one base isA x p s first
  have st := ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p
    1 505 hp0 hx0 hpo hp gap hx cop (by omega)) s (m.take K) init).2
  have start : pullState (sig (1-1)) s = s := by
    apply State.extensionality
    · rfl
    · funext q
      change s.basis (sig 0 q) = s.basis q
      rw [sig_zero]
  have pre := Rolling1588TickGap.forward_gen isA x hx0 hx 505 1 (le_refl _) (by omega) s (m.take K) init
  rw [start] at pre
  rw [pre]
  rw [place5 isA x hx0 hx _ st]

end ECDSAAdd.Entrant.Five506

namespace ECDSAAdd.Entrant.Five506
open Arithmetic MappedCompressed Secp256k1 History5 OB5 Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

theorem slotsC : Challenge.gateSlots cand = 1595 ∧ Challenge.gateSlots tick506 = 108 :=
  ⟨cand_counts.2.2, tick_counts.2.2⟩

theorem slots5 : Challenge.gateSlots merged5 = Challenge.gateSlots prior5 + 276 := by
  have f := Forward11Width.resources
  have s := slotsC
  simp only [merged5, prior5, MorningPlacement.merged, Challenge.gateSlots_append,
    Baselines.rename_gateSlots]
  omega

/-- Non-ancilla sites whose placed image the old tick 506 already touches. -/
def t506Sites : List Wire :=
  candSites.filter (fun q : Wire =>
    decide ((((q : Nat) < 793) ∨ (803 < (q : Nat))) ∧ (q : Nat) ≠ 1551 ∧ (q : Nat) ≠ 1552))

theorem t506_used : ∀ q ∈ t506Sites, sig 510 q ∈ wires (renameProgram (sig 506) tick506) := by
  decide +kernel

theorem f11_used (w : Nat) (h : w = 1551 ∨ w = 1552) : sig 510 w ∈ wires MorningPlacement.merged := by
  have b : 1551 ∈ wires Forward11Width.block9 ∧ 1552 ∈ wires Forward11Width.block9 := by
    decide +kernel
  have c : wires Forward11Width.block9 ⊆ wires Forward11Width.candidate := by
    unfold Forward11Width.candidate
    simp only [wires_append]
    intro q hq
    simp only [Finset.mem_union, hq, true_or, or_true]
  rw [MorningPlacement.merged, renameProgram_support]
  apply Finset.mem_image.mpr
  rcases h with rfl | rfl
  · exact ⟨1551, c b.1, rfl⟩
  · exact ⟨1552, c b.2, rfl⟩

theorem tick_in_forward (isA : Bool) (i n k : Nat) (hk : i ≤ k) (hkn : k < i + n) :
    wires (renameProgram (sig k) (TickRanges.tick base k ++ packFirst base isA k)) ⊆
      wires (Rolling1588TickGap.forward isA i n) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [Rolling1588TickGap.forward, wires_append]
    by_cases e : k = i
    · subst e
      exact Finset.subset_union_left
    · exact (ih (i+1) (by omega) (by omega)).trans Finset.subset_union_right

theorem cleanup_in_tick (k : Nat) (hk : 287 ≤ k ∧ k ≤ 509) :
    wires (W.compactSkywalkTickCleanup base k) ⊆ wires (TickRanges.tick base k) := by
  unfold TickRanges.tick TickGap.tick
  simp only [show ¬(225 ≤ k ∧ k ≤ 254) from by omega, show ¬(255 ≤ k ∧ k ≤ 286) from by omega, if_false]
  unfold W.repairedTick W.repairedTick0
  simp only [show ¬ W.fwdTrim k from by unfold W.fwdTrim; omega,
    show (k = 224 ∨ (255 ≤ k ∧ k ≤ 509)) from Or.inr ⟨by omega, hk.2⟩, if_false, if_true, wires_append]
  exact Finset.subset_union_right

/-- Pool-B wire `793 + j` is released by the cleanup of tick `505 - j`. -/
theorem cleanup_uses : ∀ j, j < 11 → 793 + j ∈ wires (W.compactSkywalkTickCleanup base (505 - j)) := by
  decide +kernel

theorem sig_low (i : Nat) (w : Nat) (hi : i ≤ 600) (h : w < 1301) : sig i w = w := by
  rw [OB5.sig_nat]
  unfold OB5.sigNat
  split_ifs with hc
  · omega
  · rfl

theorem anc_used (isA : Bool) (w : Nat) (h : 793 ≤ w ∧ w ≤ 803) :
    sig 510 w ∈ wires (Rolling1588TickGap.forward isA 1 505 ++ (prior5 ++ ForwardSixPlacement.after isA)) := by
  rw [wires_append]
  apply Finset.mem_union_left
  have hj := cleanup_uses (w - 793) (by omega)
  rw [show 793 + (w - 793) = w by omega] at hj
  apply tick_in_forward isA 1 505 (505 - (w - 793)) (by omega) (by omega)
  rw [renameProgram_support, wires_append]
  apply Finset.mem_image.mpr
  refine ⟨w, Finset.mem_union_left _ (cleanup_in_tick _ ⟨by omega, by omega⟩ hj), ?_⟩
  rw [sig_low _ w (by omega) (by omega), sig_low 510 w (by omega) (by omega)]

theorem site_used (isA : Bool) (n : Nat) (hn : n ∈ candSites) :
    sig 510 n ∈ wires (Rolling1588TickGap.forward isA 1 505 ++ (prior5 ++ ForwardSixPlacement.after isA)) := by
  by_cases ha : 793 ≤ n ∧ n ≤ 803
  · exact anc_used isA n ha
  rw [wires_append, wires_append]
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  rw [prior5, wires_append]
  by_cases hf : n = 1551 ∨ n = 1552
  · exact Finset.mem_union_right _ (f11_used n hf)
  · apply Finset.mem_union_left
    apply t506_used n
    simp only [t506Sites, List.mem_filter, decide_eq_true_eq]
    refine ⟨hn, ?_⟩
    show ((n < 793) ∨ (803 < n)) ∧ n ≠ 1551 ∧ n ≠ 1552
    omega

theorem merged_in (isA : Bool) : ∀ q ∈ wires merged5,
    q ∈ wires (Rolling1588TickGap.forward isA 1 505 ++ (prior5 ++ ForwardSixPlacement.after isA)) := by
  intro q hq
  rw [merged5, renameProgram_support] at hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  exact site_used isA w (List.mem_toFinset.mp (csupport hw))

theorem support5 (isA : Bool) :
    wires (stackForward5 isA) ⊆ wires (Rolling1588TickGap.stackForward0 isA) := by
  rw [shape]
  intro q hq
  rw [stackForward5, wires_append, wires_append] at hq
  rcases Finset.mem_union.mp hq with h | h
  · rw [wires_append]
    exact Finset.mem_union_left _ h
  · rcases Finset.mem_union.mp h with h | h
    · exact merged_in isA q h
    · rw [wires_append, wires_append]
      exact Finset.mem_union_right _ (Finset.mem_union_right _ h)

end ECDSAAdd.Entrant.Five506

end -- Five506

