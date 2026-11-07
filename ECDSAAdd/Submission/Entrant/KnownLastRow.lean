import ECDSAAdd.Submission.Entrant.KnownLastCarry
import ECDSAAdd.Submission.Entrant.KnownFirstRow
import ECDSAAdd.Arithmetic.SignedTriangularSquareProof
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareProof

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KnownLastRow
open Arithmetic

def normalizedRecords : Program → List Bool → List Bool
  | [], _ => []
  | .measureX _ _ _ :: p, [] => false::normalizedRecords p []
  | .measureX _ _ _ :: p, b::bs => b::normalizedRecords p bs
  | _::p, m => normalizedRecords p m

theorem run_append_normalized (p q : Program) (m₁ m₂ : List Bool) (s : State) :
    run (p++q) (normalizedRecords p m₁++m₂) s=run q m₂ (run p m₁ s) := by
  induction p generalizing m₁ s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [normalizedRecords,List.cons_append,run]
    all_goals try exact ih m₁ _
    cases m₁ <;> simp [normalizedRecords,ih]

theorem signedRow_restore (control : Wire) (xs dst pad carry : List Wire)
    (hn : (control::xs++dst++pad++carry).Nodup) (hd : dst.length=xs.length+1)
    (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (s : State) (bound : regValue dst s.basis<2^xs.length)
    (work : regValue (pad++carry) s.basis=0) (forward backward : List Bool) :
    run (signedSquareRowClear control xs dst pad carry) backward
      (run (signedSquareRow control xs dst pad carry) forward s)=s := by
  let F := signedSquareRow control xs dst pad carry
  let B := signedSquareRowClear control xs dst pad carry
  have round := signedSquareRow_roundtrip control xs dst pad carry hn hd hp hc s.basis work _
    bound s (normalizedRecords F forward++backward)
    (And.intro rfl (fun _ _ => rfl))
  rw [run_append_normalized F B forward backward s] at round
  apply State.extensionality
  · exact round.1
  · funext q
    by_cases mem : q∈dst
    · exact (regValue_eq_iff dst _ _).mp round.2.1 q mem
    · exact round.2.2 q mem

theorem post_recovers_top (control top : Wire) (low : List Wire) (s : State)
    (hn : (low++[top]).Nodup) (hc : control∉low++[top])
    (hz : (run (KnownFirstRow.rowPost control low top) [] s).basis top=false) :
    s.basis top=true := by
  have hl : low.Nodup := (List.nodup_append.mp hn).1
  have ht : top∉low := by
    have h := (List.nodup_append.mp hn).2.2
    exact fun hq => h top hq top (by simp) rfl
  have hcl : control∉low := fun hq => hc (by simp [hq])
  simp only [KnownFirstRow.rowPost,run_append,List.take_nil,List.drop_nil] at hz
  rw [notRegister_correct _ hn,xorWhenFalse_correct control low hl hcl] at hz
  simp only [xorFalseBasis,if_neg ht,show top∈low++[top] from by simp,if_pos] at hz
  simpa using hz

/-- Last-carry receiver in an otherwise ordinary inverse signed row. -/
def rowClear (control : Wire) (xs dst pad carry : List Wire) : Program :=
  xorWhenFalse control dst ++ (notRegister dst ++
    (KnownLastCarry.program (xs++pad.take 1) dst (carry.take xs.length) control ++
      (notRegister dst ++ xorWhenFalse control (dst.take xs.length))))

theorem adder_restore_of_top (xs low carry : List Wire) (top cin : Wire)
    (hn : (cin::xs++(low++[top])++carry).Nodup)
    (hl : xs.length=(low++[top]).length) (hc : carry.length+1=(low++[top]).length)
    (s target : State) (clean : ∀q∈carry,s.basis q=false)
    (targetTop : target.basis top=false)
    (restore : ∀r,run (addInPlace xs (low++[top]) carry cin++KnownFirstRow.rowPost cin low top) r s=target)
    (m : List Bool) :
    run (KnownLastCarry.program xs (low++[top]) carry cin++KnownFirstRow.rowPost cin low top) m s=target := by
  have nd : (low++[top]).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have away : cin∉low++[top] := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (List.mem_append_left carry (List.mem_append_right xs bad))
  have zero : (run (KnownFirstRow.rowPost cin low top) []
      (run (addInPlace xs (low++[top]) carry cin) [] s)).basis top=false := by
    have h := (congrArg (fun t : State => t.basis top) (restore [])).trans targetTop
    simpa only [run_append,List.take_nil,List.drop_nil] using h
  have topKnown := post_recovers_top cin top low _ nd away zero
  have eq (r : List Bool) := KnownLastCarry.program_eq_of_top_output xs low carry top cin hn hl hc s r clean topKnown
  have old := (addInPlace_counts xs (low++[top]) carry cin hl hc).2
  have new := (KnownLastCarry.program_counts xs (low++[top]) carry cin hl hc).2
  have result := restore m
  simp only [run_append,old] at result
  simpa only [run_append,new,eq] using result

theorem rowClear_on_image (control top pad : Wire) (xs low carry : List Wire)
    (hn : (control::xs++(low++[top])++[pad]++carry).Nodup)
    (hl : low.length=xs.length) (hc : carry.length=xs.length)
    (s : State) (topZero : s.basis top=false)
    (work : regValue ([pad]++carry) s.basis=0) (forward backward : List Bool) :
    run (rowClear control xs (low++[top]) [pad] carry) backward
      (run (signedSquareRow control xs (low++[top]) [pad] carry) forward s)=s := by
  let D := low++[top]
  let F := signedSquareRow control xs D [pad] carry
  let Pre := xorWhenFalse control D++notRegister D
  let Post := KnownFirstRow.rowPost control low top
  let f := run F forward s
  let u := run Pre [] f
  have cnt (q : Wire) := List.nodup_iff_count.mp hn q
  have hd : D.length=xs.length+1 := by simp [D,hl]
  have ndD : D.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := cnt q
    simp only [D,List.count_cons,List.count_append] at h ⊢
    omega
  have ctl : control∉D := by
    intro bad
    have h := cnt control
    have p := List.count_pos_iff.mpr bad
    simp only [D,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h p
    omega
  have away (q : Wire) (hq : q∈carry) : q∉D := by
    intro bad
    have h := cnt q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [D,List.count_cons,List.count_append] at h b
    omega
  have bound : regValue D s.basis<2^xs.length := by
    have b := regValue_lt low s.basis
    simpa [D,regValue_append,regValue,topZero,hl] using b
  have frame := signedSquareRow_frame control xs D [pad] carry hn hd (by simp) hc.ge
    s.basis (s.basis control) rfl work (regValue D s.basis) (regValue_lt D s.basis)
    s forward (And.intro rfl (fun _ _ => rfl))
  have fKeep (q : Wire) (hq : q∉D) : f.basis q=s.basis q := frame.2.2 q hq
  have uKeep (q : Wire) (hq : q∉D) : u.basis q=s.basis q := by
    dsimp only [u,Pre]
    rw [run_append]
    simp only [List.take_nil,List.drop_nil]
    rw [xorWhenFalse_correct control D ndD ctl,notRegister_correct D ndD]
    simp only [if_neg hq,xorFalseBasis,if_neg hq]
    exact fKeep q hq
  have clean : ∀q∈carry,u.basis q=false := by
    intro q hq
    rw [uKeep q (away q hq)]
    exact (regValue_zero _ _).mp work q (List.mem_append_right [pad] hq)
  have preM : measurementCount Pre=0 := by
    simp [Pre,measurementCount_append,xorWhenFalse_measurementCount,(notRegister_counts D).2]
  have takeC : carry.take xs.length=carry := by rw [←hc];exact List.take_length
  have takeD : D.take xs.length=low := by rw [←hl];exact List.take_left
  have oldShape : signedSquareRowClear control xs D [pad] carry=
      Pre++(addInPlace (xs++[pad]) D carry control++Post) := by
    simp [signedSquareRowClear,Pre,Post,KnownFirstRow.rowPost,takeC,takeD,List.append_assoc,D]
  have newShape : rowClear control xs D [pad] carry=
      Pre++(KnownLastCarry.program (xs++[pad]) D carry control++Post) := by
    simp [rowClear,Pre,Post,KnownFirstRow.rowPost,takeC,takeD,List.append_assoc,D]
  have restore (r : List Bool) : run (addInPlace (xs++[pad]) D carry control++Post) r u=s := by
    have h := signedRow_restore control xs D [pad] carry hn hd (by simp) hc.ge s bound work forward r
    rw [oldShape,run_append,preM,List.take_zero,List.drop_zero] at h
    exact h
  have ndReceiver : (control::(xs++[pad])++D++carry).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := cnt q
    simp only [D,List.count_cons,List.count_append] at h ⊢
    omega
  have result := adder_restore_of_top (xs++[pad]) low carry top control ndReceiver
    (by simp [hl]) (by simp [hc,hl]) u s clean topZero restore backward
  rw [newShape,run_append,preM,List.take_zero,List.drop_zero]
  exact result

theorem rowClear_resources (control : Wire) (xs dst pad carry : List Wire)
    (hx : 1≤xs.length) (hd : dst.length=xs.length+1)
    (hp : 1≤pad.length) (hc : xs.length≤carry.length) :
    toffoliCount (rowClear control xs dst pad carry)+1=toffoliCount (signedSquareRowClear control xs dst pad carry) ∧
    measurementCount (rowClear control xs dst pad carry)=measurementCount (signedSquareRowClear control xs dst pad carry) ∧
    wires (rowClear control xs dst pad carry) ⊆ wires (signedSquareRowClear control xs dst pad carry) ∧
    Challenge.gateSlots (rowClear control xs dst pad carry)≤Challenge.gateSlots (signedSquareRowClear control xs dst pad carry) := by
  have hl : (xs++pad.take 1).length=dst.length := by
    simp only [List.length_append,List.length_take,Nat.min_eq_left hp]
    omega
  have hcl : (carry.take xs.length).length+1=dst.length := by
    simp only [List.length_take,Nat.min_eq_left hc]
    omega
  have n := KnownLastCarry.program_counts (xs++pad.take 1) dst (carry.take xs.length) control hl hcl
  have o := addInPlace_counts (xs++pad.take 1) dst (carry.take xs.length) control hl hcl
  have side := KnownLastCarry.program_resources (xs++pad.take 1) dst (carry.take xs.length) control hl hcl
  have nt (r : List Wire) := (notRegister_counts r).1
  have nm (r : List Wire) := (notRegister_counts r).2
  refine ⟨?_,?_,?_,?_⟩
  · simp only [rowClear,signedSquareRowClear,toffoliCount_append,
      xorWhenFalse_toffoliCount,nt,n.1,o.1,Nat.zero_add,Nat.add_zero]
    omega
  · simp only [rowClear,signedSquareRowClear,measurementCount_append,
      xorWhenFalse_measurementCount,nm,n.2,o.2]
  · simp only [rowClear,signedSquareRowClear,wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union
      (Finset.Subset.refl _) (Finset.union_subset_union side.1 (Finset.Subset.refl _)))
  · simp only [rowClear,signedSquareRowClear,Challenge.gateSlots_append]
    have le := side.2
    omega

theorem rowClear_physical (control : Wire) (xs dst pad carry : List Wire)
    (hn : (control::xs++dst++pad++carry).Nodup)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (old : GatePhysical (signedSquareRowClear control xs dst pad carry)) :
    GatePhysical (rowClear control xs dst pad carry) := by
  have hl : (xs++pad.take 1).length=dst.length := by
    simp only [List.length_append,List.length_take,Nat.min_eq_left hp]
    omega
  have hcl : (carry.take xs.length).length+1=dst.length := by
    simp only [List.length_take,Nat.min_eq_left hc]
    omega
  have nd : (control::(xs++pad.take 1)++dst++carry.take xs.length).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have p := (List.take_sublist 1 pad).count_le q
    have c := (List.take_sublist xs.length carry).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have receiver := KnownLastCarry.program_physical (xs++pad.take 1) dst (carry.take xs.length) control nd hl hcl
  simp only [rowClear,signedSquareRowClear,gatePhysical_append] at old ⊢
  tauto

theorem rowClear_on_image_general (control top : Wire) (xs low pad carry : List Wire)
    (hn : (control::xs++(low++[top])++pad++carry).Nodup)
    (hl : low.length=xs.length) (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (s : State) (topZero : s.basis top=false)
    (work : regValue (pad++carry) s.basis=0) (forward backward : List Bool) :
    run (rowClear control xs (low++[top]) pad carry) backward
      (run (signedSquareRow control xs (low++[top]) pad carry) forward s)=s := by
  obtain ⟨p,ps,rfl⟩ : ∃p ps,pad=p::ps := by
    match pad,hp with
    | p::ps,_ => exact ⟨p,ps,rfl⟩
    | [],h => simp at h
  let cy := carry.take xs.length
  have cylen : cy.length=xs.length := by
    simp only [cy,List.length_take,Nat.min_eq_left hc]
  have takeC : cy.take xs.length=cy := by rw [←cylen];exact List.take_length
  have nd : (control::xs++(low++[top])++[p]++cy).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have le := (List.take_sublist xs.length carry).count_le q
    simp only [cy,List.count_cons,List.count_append,List.count_nil] at h le ⊢
    omega
  have localWork : regValue ([p]++cy) s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    apply (regValue_zero _ _).mp work q
    rcases List.mem_append.mp hq with first | second
    · have eq : q=p := by simpa using first
      subst q
      exact List.mem_append_left carry (by simp : p∈p::ps)
    · exact List.mem_append_right (p::ps) (List.mem_of_mem_take second)
  have front : signedSquareRow control xs (low++[top]) (p::ps) carry=
      signedSquareRow control xs (low++[top]) [p] cy := by
    simp only [signedSquareRow,takeC,List.take_succ_cons,List.take_zero]
    rfl
  have back : rowClear control xs (low++[top]) (p::ps) carry=
      rowClear control xs (low++[top]) [p] cy := by
    simp only [rowClear,takeC,List.take_succ_cons,List.take_zero]
    rfl
  rw [back,front]
  exact rowClear_on_image control top p xs low cy nd hl cylen s topZero localWork forward backward

theorem row_value_bound (dst : List Wire) (n : Nat) (hn : 1≤n)
    (hd : dst.length=2*n) (s : BasisState)
    (hhi : regValue (dst.drop n) s=0) :
    regValue ((dst.drop 1).take n) s<2^(n-1) := by
  have cap : n≤dst.length := by omega
  have capDrop : n≤(dst.drop 1).length := by simp only [List.length_drop];omega
  have split := regValue_append (dst.take n) (dst.drop n) s
  rw [List.take_append_drop,hhi,Nat.mul_zero,Nat.add_zero] at split
  have b := regValue_lt (dst.take n) s
  rw [List.length_take,Nat.min_eq_left cap] at b
  have full : regValue dst s<2^n := by omega
  have pow : 2^n=2^(n-1)*2 := by
    conv_lhs => rw [show n=(n-1)+1 by omega,Nat.pow_succ]
  have small : regValue dst s/2<2^(n-1) := by omega
  rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ capDrop,
    CuccaroStreamedSquareWideLayout.regValue_drop_div dst 1 (by omega)]
  exact (Nat.mod_le _ _).trans_lt small

theorem top_zero_of_bound (low : List Wire) (top : Wire) (s : BasisState)
    (bound : regValue (low++[top]) s<2^low.length) : s top=false := by
  cases h : s top with
  | false => rfl
  | true =>
    rw [regValue_append] at bound
    have one : regValue [top] s=1 := by simp [regValue,h]
    rw [one,Nat.mul_one] at bound
    omega

theorem split_last (r : List Wire) (h : r≠[]) : ∃ low top,r=low++[top] := by
  induction r with
  | nil => exact False.elim (h rfl)
  | cons a r ih =>
    cases r with
    | nil => exact ⟨[],a,rfl⟩
    | cons b r =>
      obtain ⟨low,top,eq⟩ := ih (by simp)
      exact ⟨a::low,top,by rw [eq];rfl⟩

theorem rowClear_on_image_of_bound (control : Wire) (xs dst pad carry : List Wire)
    (hn : (control::xs++dst++pad++carry).Nodup)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (s : State) (bound : regValue dst s.basis<2^xs.length)
    (work : regValue (pad++carry) s.basis=0) (forward backward : List Bool) :
    run (rowClear control xs dst pad carry) backward
      (run (signedSquareRow control xs dst pad carry) forward s)=s := by
  have nonempty : dst≠[] := by intro eq;simp [eq] at hd
  obtain ⟨low,top,rfl⟩ := split_last dst nonempty
  have len : low.length=xs.length := by simpa using hd
  exact rowClear_on_image_general control top xs low pad carry hn len hp hc s
    (top_zero_of_bound low top s.basis (by simpa only [len] using bound)) work forward backward

end ECDSAAdd.Entrant.KnownLastRow
#print axioms ECDSAAdd.Entrant.KnownLastRow.signedRow_restore
#print axioms ECDSAAdd.Entrant.KnownLastRow.post_recovers_top

#print axioms ECDSAAdd.Entrant.KnownLastRow.adder_restore_of_top

#print axioms ECDSAAdd.Entrant.KnownLastRow.rowClear_on_image

#print axioms ECDSAAdd.Entrant.KnownLastRow.rowClear_resources

#print axioms ECDSAAdd.Entrant.KnownLastRow.rowClear_physical

#print axioms ECDSAAdd.Entrant.KnownLastRow.rowClear_on_image_general

#print axioms ECDSAAdd.Entrant.KnownLastRow.row_value_bound

#print axioms ECDSAAdd.Entrant.KnownLastRow.rowClear_on_image_of_bound
