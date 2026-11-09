import ECDSAAdd.Submission.Entrant.ParkAThird

set_option Elab.async false

-- A carry8 stored on an existing work wire, released by a certified zero-source circuit rewrite.

section
-- ZeroReadPrimitives
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroReadDevelop
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def keepCorrection (q:Wire):Correction→Bool
 | .Z t=>t != q
 | .CZ a b=>a != q && b != q

def pruneCorrections (q:Wire) (cs:List Correction):List Correction:=cs.filter (keepCorrection q)

theorem prune_correct (q:Wire) (cs:List Correction) (s:State) (hz:s.basis q=false):
 correct (pruneCorrections q cs) s=correct cs s:=by
 induction cs generalizing s with
 | nil=>rfl
 | cons c cs ih=>
  cases c with
  | Z t=>
   by_cases h:t=q
   · subst t
     simpa[pruneCorrections,keepCorrection,correct,hz]using ih s hz
   · simpa[pruneCorrections,keepCorrection,correct,h]using
      ih ⟨s.phase ^^ s.basis t,s.basis⟩ hz
  | CZ a b=>
   by_cases ha:a=q
   · subst a
     simpa[pruneCorrections,keepCorrection,correct,hz]using ih s hz
   by_cases hb:b=q
   · subst b
     simpa[pruneCorrections,keepCorrection,correct,hz]using ih s hz
   · simpa[pruneCorrections,keepCorrection,correct,ha,hb]using
      ih ⟨s.phase ^^ (s.basis a && s.basis b),s.basis⟩ hz

theorem majority_zero_second (a q c d:Wire) (hn:[a,q,c,d].Nodup)
 (s:State) (m:List Bool) (hz:s.basis q=false):
 run (majority a q c d) m s=run [Instr.CCX a c d] m s:=by
 rw[majority_correct a q c d hn s m]
 simp[hz,carryBit,run]

theorem majority_zero_first (q b c d:Wire) (hn:[q,b,c,d].Nodup)
 (s:State) (m:List Bool) (hz:s.basis q=false):
 run (majority q b c d) m s=run [Instr.CCX b c d] m s:=by
 rw[majority_correct q b c d hn s m]
 simp[hz,carryBit,run]
#print axioms prune_correct
#print axioms majority_zero_second
end ZeroReadDevelop

end -- isolated A work loan component

section
-- ZeroReadProgram
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroReadDevelop
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def targetOf:Instr→Wire
 | .X t=>t
 | .CX _ t=>t
 | .CCX _ _ t=>t
 | .measureX t _ _=>t

def eraseInstr (q:Wire):Instr→Program
 | .X t=>[.X t]
 | .CX a t=>if a=q then [] else [.CX a t]
 | .CCX a b t=>if a=q ∨ b=q then [] else [.CCX a b t]
 | .measureX t c0 c1=>[.measureX t (pruneCorrections q c0) (pruneCorrections q c1)]

def eraseReads (q:Wire) (p:Program):Program:=p.flatMap (eraseInstr q)

def noTargets (q:Wire) (p:Program):Prop:=∀i∈p,targetOf i≠q

theorem eraseInstr_M (q:Wire) (i:Instr):measurementCount (eraseInstr q i)=measurementCount [i]:=by
 cases i <;> simp[eraseInstr,measurementCount]
 all_goals split <;> rfl

theorem eraseInstr_run (q:Wire) (i:Instr) (s:State) (m:List Bool)
 (hz:s.basis q=false) (ht:targetOf i≠q):
 run (eraseInstr q i) m s=run [i] m s:=by
 cases i with
 | X t=>rfl
 | CX a t=>
  by_cases h:a=q
  · subst a;simp[eraseInstr,run,hz,writeBit]
  · simp[eraseInstr,h]
 | CCX a b t=>
  by_cases ha:a=q
  · subst a;simp[eraseInstr,run,hz,writeBit]
  by_cases hb:b=q
  · subst b;simp[eraseInstr,run,hz,writeBit]
  · simp[eraseInstr,ha,hb]
 | measureX t c0 c1=>
  have hz':(writeBit s.basis t false) q=false:=by
   change t≠q at ht
   simpa[writeBit,Ne.symm ht]using hz
  simp only[eraseInstr,run,measureAndCorrect]
  split <;> exact prune_correct q _ _ hz'

theorem single_target_preserves (q:Wire) (i:Instr) (s:State) (m:List Bool) (ht:targetOf i≠q):
 (run [i] m s).basis q=s.basis q:=by
 cases i <;> simp only[targetOf]at ht <;>
  simp[run,measureAndCorrect,writeBit,Ne.symm ht]

theorem eraseReads_M (q:Wire) (p:Program):measurementCount (eraseReads q p)=measurementCount p:=by
 induction p with
 | nil=>rfl
 | cons i p ih=>
  rw[eraseReads,List.flatMap_cons,measurementCount_append,eraseInstr_M]
  change measurementCount [i]+measurementCount (eraseReads q p)=_
  rw[ih]
  cases i <;> simp[measurementCount]

theorem run_cat (p r:Program) (m:List Bool) (s:State):
 run (p++r) m s=run r (m.drop (measurementCount p)) (run p m s):=by
 rw[run_append,run_take]

theorem eraseReads_run (q:Wire) (p:Program) (ht:noTargets q p) (s:State) (m:List Bool)
 (hz:s.basis q=false):run (eraseReads q p) m s=run p m s:=by
 induction p generalizing s m with
 | nil=>rfl
 | cons i p ih=>
  have hi:targetOf i≠q:=ht i (by simp)
  have hp:noTargets q p:=fun j hj=>ht j (List.mem_cons_of_mem i hj)
  change run (eraseInstr q i++eraseReads q p) m s=run ([i]++p) m s
  rw[run_cat,run_cat,eraseInstr_M,eraseInstr_run q i s m hz hi]
  exact ih hp _ _ ((single_target_preserves q i s m hi).trans hz)
#print axioms eraseReads_run
#print axioms eraseReads_M
end ZeroReadDevelop

end -- isolated A work loan component

section
-- ZeroReadRewrite
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroReadDevelop
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

inductive Rewrites (q:Wire):Program→Program→Prop
 | nil:Rewrites q [] []
 | normal (i:Instr) (p r:Program) (ht:targetOf i≠q) (tail:Rewrites q p r):
   Rewrites q (i::p) (eraseInstr q i++r)
 | zeroMajority (a c d:Wire) (p r:Program) (hn:[a,q,c,d].Nodup) (tail:Rewrites q p r):
   Rewrites q (majority a q c d++p) ([Instr.CCX a c d]++r)

theorem Rewrites.run_eq (q:Wire) (p r:Program) (h:Rewrites q p r) (s:State) (m:List Bool)
 (hz:s.basis q=false):run r m s=run p m s:=by
 induction h generalizing s m with
 | nil=>rfl
 | normal i p r ht tail ih=>
  change run (eraseInstr q i++r) m s=run ([i]++p) m s
  rw[run_cat,run_cat,eraseInstr_M,eraseInstr_run q i s m hz ht]
  exact ih _ _ ((single_target_preserves q i s m ht).trans hz)
 | zeroMajority a c d p r hn tail ih=>
  have dm:d≠q:=by intro e;subst d;simp at hn
  have mm:measurementCount (majority a q c d)=0:=by simp[majority,measurementCount]
  rw[run_cat,run_cat,mm]
  simp only[measurementCount,List.drop_zero]
  rw[majority_zero_second a q c d hn s m hz]
  exact ih _ _ ((single_target_preserves q (.CCX a c d) s m dm).trans hz)

theorem Rewrites.measurements (q:Wire) (p r:Program) (h:Rewrites q p r):
 measurementCount r=measurementCount p:=by
 induction h with
 | nil=>rfl
 | normal i p r ht tail ih=>
  rw[measurementCount_append,eraseInstr_M,ih]
  cases i <;> simp[measurementCount]
 | zeroMajority a c d p r hn tail ih=>
  simpa[measurementCount_append,majority,measurementCount]using ih

structure CheckedRewrite (q:Wire) (p:Program) where
 out:Program
 proof:Rewrites q p out

def normalStep (q:Wire) (i:Instr) (p:Program) (tail:Option (CheckedRewrite q p)):
 Option (CheckedRewrite q (i::p)):=
 if ht:targetOf i≠q then
  tail.map (fun r=>⟨eraseInstr q i++r.out,Rewrites.normal i p r.out ht r.proof⟩)
 else none
#print axioms Rewrites.run_eq
#print axioms Rewrites.measurements
end ZeroReadDevelop

end -- isolated A work loan component

section
-- ZeroReadCompiler
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def compile? (q:Wire) (p:Program):Option (CheckedRewrite q p):=
 match p with
 | []=>some ⟨[],Rewrites.nil⟩
 | .CX a b::.CX c d::.CCX e f g::i3::i4::i5::rest=>
  let tail:=.CX c d::.CCX e f g::i3::i4::i5::rest
  let full:=.CX a b::tail
  let fallback:=normalStep q (.CX a b) tail (compile? q tail)
  if hm:full.take 6=majority a q d g then
   if hn:[a,q,d,g].Nodup then
    match compile? q rest with
    | none=>none
    | some r=>some ⟨[.CCX a d g]++r.out,by
       have hp:full=majority a q d g++rest:=by
        calc
         full=full.take 6++full.drop 6:=(List.take_append_drop 6 full).symm
         _=majority a q d g++rest:=by rw[hm];rfl
       have h:=Rewrites.zeroMajority a d g rest r.out hn r.proof
       simpa only[←hp]using h⟩
   else fallback
  else fallback
 | i::rest=>normalStep q i rest (compile? q rest)
termination_by p.length
 decreasing_by all_goals (simp_wf <;> omega)

def optimized (q:Wire) (p:Program):Program:=
 match compile? q p with
 | none=>p
 | some r=>r.out

theorem optimized_run (q:Wire) (p:Program) (s:State) (m:List Bool) (hz:s.basis q=false):
 run (optimized q p) m s=run p m s:=by
 unfold optimized
 split
 · rfl
 · rename_i r he
   exact r.proof.run_eq q p r.out s m hz

theorem optimized_M (q:Wire) (p:Program):measurementCount (optimized q p)=measurementCount p:=by
 unfold optimized
 split
 · rfl
 · rename_i r he
   exact r.proof.measurements q p r.out
#print axioms optimized_run
#print axioms optimized_M
end ZeroReadDevelop

end -- isolated A work loan component

section
-- ZeroReadResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroReadDevelop
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem prune_support (q:Wire) (cs:List Correction):
 correctionWires (pruneCorrections q cs) ⊆ (correctionWires cs).erase q:=by
 induction cs with
 | nil=>simp[pruneCorrections,correctionWires]
 | cons c cs ih=>
  intro x hx
  have ihx: x∈correctionWires (pruneCorrections q cs) → x≠q ∧ x∈correctionWires cs:=by
   intro hh;exact Finset.mem_erase.mp (ih hh)
  cases c with
  | Z t=>
   by_cases h:t=q <;>
    (simp_all[pruneCorrections,keepCorrection,correctionWires] <;> aesop)
  | CZ a b=>
   by_cases ha:a=q <;> by_cases hb:b=q <;>
    (simp_all[pruneCorrections,keepCorrection,correctionWires] <;> aesop)

theorem eraseInstr_T (q:Wire) (i:Instr):toffoliCount (eraseInstr q i)≤toffoliCount [i]:=by
 cases i <;> simp only[eraseInstr]
 all_goals first | (split <;> simp[toffoliCount]) | simp[toffoliCount]

theorem eraseInstr_support (q:Wire) (i:Instr) (ht:targetOf i≠q):
 wires (eraseInstr q i) ⊆ i.wires.erase q:=by
 cases i with
 | X t=>simpa[eraseInstr,wires,Instr.wires,targetOf]using ht
 | CX a t=>
  by_cases h:a=q
  · simp[eraseInstr,h,wires]
  · intro x hx;simp_all[eraseInstr,wires,Instr.wires,targetOf] <;> aesop
 | CCX a b t=>
  by_cases ha:a=q
  · simp[eraseInstr,ha,wires]
  by_cases hb:b=q
  · simp[eraseInstr,hb,wires]
  · intro x hx;simp_all[eraseInstr,wires,Instr.wires,targetOf] <;> aesop
 | measureX t c0 c1=>
  have h0:=prune_support q c0
  have h1:=prune_support q c1
  simp only[eraseInstr,wires,Finset.union_empty,Instr.wires]
  intro x hx
  simp only[Finset.mem_union,Finset.mem_singleton]at hx
  rcases hx with (rfl|hx)|hx
  · simpa[targetOf]using ht
  · have :=h0 hx;simp_all
  · have :=h1 hx;simp_all

theorem Rewrites.toffoli (q:Wire) (p r:Program) (h:Rewrites q p r):
 toffoliCount r≤toffoliCount p:=by
 induction h with
 | nil=>rfl
 | normal i p r ht tail ih=>
  have hi:=eraseInstr_T q i
  rw[toffoliCount_append]
  have hh:toffoliCount (i::p)=toffoliCount [i]+toffoliCount p:=by cases i <;> simp[toffoliCount]
  rw[hh];omega
 | zeroMajority a c d p r hn tail ih=>
  simpa[majority,toffoliCount]using ih

theorem Rewrites.support (q:Wire) (p r:Program) (h:Rewrites q p r):
 wires r⊆(wires p).erase q:=by
 induction h with
 | nil=>simp[wires]
 | normal i p r ht tail ih=>
  have hi:=eraseInstr_support q i ht
  simp only[wires_append,wires]
  intro x hx
  rcases Finset.mem_union.mp hx with hx|hx
  · have :=hi hx;simp_all
  · have :=ih hx;simp_all
 | zeroMajority a c d p r hn tail ih=>
  simp only[wires_append,wires,Instr.wires,Finset.union_empty]
  intro x hx
  have ihx: x∈wires r → x≠q ∧ x∈wires p:=fun hx=>Finset.mem_erase.mp (ih hx)
  simp_all[majority,wires,Instr.wires]
  aesop
#print axioms Rewrites.toffoli
#print axioms Rewrites.support
end ZeroReadDevelop

end -- isolated A work loan component

section
-- ZeroReadPhysical
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.RecordedQuantum
namespace ZeroReadDevelop
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem eraseInstr_physical (q:Wire) (i:Instr) (h:PhysicalInstr (.gate i)):
 GatePhysical (eraseInstr q i):=by
 cases i <;> simp only[eraseInstr]
 all_goals first
  | (split <;> simp_all[GatePhysical,PhysicalInstr,ProperGate])
  | simp_all[GatePhysical,PhysicalInstr,ProperGate]

theorem Rewrites.physical (q:Wire) (p r:Program) (h:Rewrites q p r)
 (hp:GatePhysical p):GatePhysical r:=by
 induction h with
 | nil=>simp[GatePhysical]
 | normal i p r ht tail ih=>
  have hi:PhysicalInstr (.gate i):=hp i (by simp)
  have ht:GatePhysical p:=fun j hj=>hp j (by simp[hj])
  rw[gatePhysical_append]
  exact ⟨eraseInstr_physical q i hi,ih ht⟩
 | zeroMajority a c d p r hn tail ih=>
  have ht:GatePhysical p:=fun j hj=>hp j (List.mem_append_right _ hj)
  rw[gatePhysical_append]
  constructor
  · simp[GatePhysical,PhysicalInstr,ProperGate]
    simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or]at hn
    aesop
  · exact ih ht
#print axioms Rewrites.physical
end ZeroReadDevelop

end -- isolated A work loan component

section
-- ZeroReadMany
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroReadDevelop
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

inductive ManyRewrites:List Wire→Program→Program→Prop
 | nil (p:Program):ManyRewrites [] p p
 | cons (q:Wire) (qs:List Wire) (p r t:Program) (head:Rewrites q p r)
   (tail:ManyRewrites qs r t):ManyRewrites (q::qs) p t

theorem ManyRewrites.run_eq (qs:List Wire) (p r:Program) (h:ManyRewrites qs p r)
 (s:State) (m:List Bool) (hz:∀q∈qs,s.basis q=false):run r m s=run p m s:=by
 induction h with
 | nil=>rfl
 | cons q qs p r t head tail ih=>
  rw[ih (fun w hw=>hz w (by simp[hw]))]
  exact head.run_eq q p r s m (hz q (by simp))

theorem ManyRewrites.measurements (qs:List Wire) (p r:Program) (h:ManyRewrites qs p r):
 measurementCount r=measurementCount p:=by
 induction h with
 | nil=>rfl
 | cons q qs p r t head tail ih=>exact ih.trans (head.measurements q p r)

theorem ManyRewrites.toffoli (qs:List Wire) (p r:Program) (h:ManyRewrites qs p r):
 toffoliCount r≤toffoliCount p:=by
 induction h with
 | nil=>rfl
 | cons q qs p r t head tail ih=>exact ih.trans (head.toffoli q p r)

theorem ManyRewrites.support (qs:List Wire) (p r:Program) (h:ManyRewrites qs p r):
 wires r⊆wires p ∧ ∀q∈qs,q∉wires r:=by
 induction h with
 | nil=>simp
 | cons q qs p r t head tail ih=>
  have hh:=head.support q p r
  constructor
  · exact ih.1.trans (hh.trans (Finset.erase_subset q (wires p)))
  · intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · intro bad;have bad:=hh (ih.1 bad);exact (Finset.mem_erase.mp bad).1 rfl
    · exact ih.2 w hw

theorem ManyRewrites.physical (qs:List Wire) (p r:Program) (h:ManyRewrites qs p r)
 (hp:GatePhysical p):GatePhysical r:=by
 induction h with
 | nil=>exact hp
 | cons q qs p r t head tail ih=>exact ih (head.physical q p r hp)

structure CheckedMany (qs:List Wire) (p:Program) where
 out:Program
 proof:ManyRewrites qs p out

def compileMany? (qs:List Wire) (p:Program):Option (CheckedMany qs p):=
 match qs with
 | []=>some ⟨p,ManyRewrites.nil p⟩
 | q::qs=>do
  let first←compile? q p
  let rest←compileMany? qs first.out
  pure ⟨rest.out,ManyRewrites.cons q qs p first.out rest.out first.proof rest.proof⟩
#print axioms ManyRewrites.run_eq
#print axioms ManyRewrites.support
#print axioms ManyRewrites.physical
end ZeroReadDevelop

end -- isolated A work loan component

section
-- ZeroReadChunked
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem Rewrites.append (q:Wire) (p r p' r':Program) (h:Rewrites q p r) (h':Rewrites q p' r'):
 Rewrites q (p++p') (r++r'):=by
 induction h with
 | nil=>simpa using h'
 | normal i p r ht tail ih=>
  simpa only[List.cons_append,List.append_assoc]using Rewrites.normal i (p++p') (r++r') ht ih
 | zeroMajority a c d p r hn tail ih=>
  simpa only[List.append_assoc]using Rewrites.zeroMajority a c d (p++p') (r++r') hn ih

def compileChunked? (q:Wire) (p:Program):Option (CheckedRewrite q p):=
 if hp:p.length≤1024 then compile? q p
 else do
  let a←compile? q (p.take 1024)
  let b←compileChunked? q (p.drop 1024)
  pure ⟨a.out++b.out,by
   have h:=Rewrites.append q (p.take 1024) a.out (p.drop 1024) b.out a.proof b.proof
   simpa only[List.take_append_drop]using h⟩
termination_by p.length
 decreasing_by simp_wf;omega

def compileManyChunked? (qs:List Wire) (p:Program):Option (CheckedMany qs p):=
 match qs with
 | []=>some ⟨p,ManyRewrites.nil p⟩
 | q::qs=>do
  let first←compileChunked? q p
  let rest←compileManyChunked? qs first.out
  pure ⟨rest.out,ManyRewrites.cons q qs p first.out rest.out first.proof rest.proof⟩
#print axioms Rewrites.append
end ZeroReadDevelop

end -- isolated A work loan component

section
-- ZeroReadMiddle
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroReadDevelop
open InverseCarryDevelop
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem ManyRewrites.middle_eq (qs:List Wire) (old new:Program) (h:ManyRewrites qs old new)
 (pre:Program) (s:State) (m:List Bool) (hz:∀q∈qs,s.basis q=false)
 (off:∀q∈qs,q∉wires pre):middleState pre new s m=middleState pre old s m:=by
 unfold middleState
 rw[h.measurements qs old new]
 apply h.run_eq
 intro q hq
 exact (run_preserves_outside pre _ s q (off q hq)).trans (hz q hq)

theorem ManyRewrites.surround_eq (qs:List Wire) (old new:Program) (h:ManyRewrites qs old new)
 (pre post:Program) (s:State) (m:List Bool) (hz:∀q∈qs,s.basis q=false)
 (off:∀q∈qs,q∉wires pre):run ((pre++new)++post) m s=run ((pre++old)++post) m s:=by
 rw[run_cat (pre++new) post,run_cat (pre++old) post]
 rw[measurementCount_append,measurementCount_append,h.measurements qs old new]
 rw[run_cat pre new,run_cat pre old]
 have he:run new (m.drop (measurementCount pre)) (run pre m s)=run old (m.drop (measurementCount pre)) (run pre m s):=by
  apply h.run_eq
  intro q hq
  exact (run_preserves_outside pre m s q (off q hq)).trans (hz q hq)
 rw[he]
#print axioms ManyRewrites.middle_eq
#print axioms ManyRewrites.surround_eq
end ZeroReadDevelop

end -- isolated A work loan component

section
-- ZeroReadSlots
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroReadDevelop
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem prune_length (q:Wire) (cs:List Correction):(pruneCorrections q cs).length≤cs.length:=List.length_filter_le _ _

theorem eraseInstr_slots (q:Wire) (i:Instr):Challenge.gateSlots (eraseInstr q i)≤Challenge.gateSlots [i]:=by
 cases i with
 | X t=>rfl
 | CX a t=>simp only[eraseInstr];split <;> simp[Challenge.gateSlots,Challenge.instructionSlots]
 | CCX a b t=>simp only[eraseInstr];split <;> simp[Challenge.gateSlots,Challenge.instructionSlots]
 | measureX t c0 c1=>
  have h0:=prune_length q c0
  have h1:=prune_length q c1
  simp only[eraseInstr,Challenge.gateSlots,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Challenge.instructionSlots]
  omega

theorem Rewrites.slots (q:Wire) (p r:Program) (h:Rewrites q p r):Challenge.gateSlots r≤Challenge.gateSlots p:=by
 induction h with
 | nil=>rfl
 | normal i p r ht tail ih=>
  have hi:=eraseInstr_slots q i
  rw[Challenge.gateSlots_append]
  have hh:Challenge.gateSlots (i::p)=Challenge.gateSlots [i]+Challenge.gateSlots p:=by simp[Challenge.gateSlots]
  rw[hh];omega
 | zeroMajority a c d p r hn tail ih=>
  simp only[Challenge.gateSlots_append]at *
  have hs:Challenge.gateSlots (majority a q c d)=6:=by simp[majority,Challenge.gateSlots,Challenge.instructionSlots]
  have ht:Challenge.gateSlots [Instr.CCX a c d]=1:=by rfl
  rw[hs,ht];omega

theorem ManyRewrites.slots (qs:List Wire) (p r:Program) (h:ManyRewrites qs p r):Challenge.gateSlots r≤Challenge.gateSlots p:=by
 induction h with
 | nil=>rfl
 | cons q qs p r t head tail ih=>exact ih.trans (head.slots q p r)
#print axioms ManyRewrites.slots
end ZeroReadDevelop

end -- isolated A work loan component

section
-- FourthACarryNumbers
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def cacheBit8 (H:Nat):Bool:=decide ((1040*H/64)%256<H%256)
theorem cacheBit8_value (H:Nat):(cacheBit8 H).toNat=(if (1040*H/64)%256<H%256 then 1 else 0):=by
 by_cases h:(1040*H/64)%256<H%256 <;> simp[cacheBit8,h]
theorem carry_return256 (X A:Nat) (hX:X<256) (hA:A<256):
 (X+(A+256-X)%256)/256=(if A<X then 1 else 0):=by split_ifs <;> omega
theorem carry_return8_w64 (H:Nat):
 (H%256+(976*H/64)%256)/256=(if (1040*H/64)%256<H%256 then 1 else 0):=by
 have sum:H+976*H/64=1040*H/64:=by omega
 have back:((1040*H/64)%256+256-H%256)%256=(976*H/64)%256:=by omega
 rw[←back]
 exact carry_return256 _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
theorem sub_add_carry8_w64 (H:Nat):
 (H%256+(255-(1040*H/64)%256))/256=(H%256+(976*H/64)%256)/256:=by
 have sub:(H%256+(255-(1040*H/64)%256))/256=(if (1040*H/64)%256<H%256 then 1 else 0):=by split_ifs <;> omega
 exact sub.trans (carry_return8_w64 H).symm
#print axioms carry_return8_w64
#print axioms sub_add_carry8_w64


end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryPrefix
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem shape8 (xs:List Wire) (hlen:8≤xs.length):∃a b c d e f g h tail,xs=a::b::c::d::e::f::g::h::tail:=by
 obtain ⟨a,b,c,d,e,f,g,tail,rfl⟩:=shape7 xs (by omega)
 cases tail with
 | nil=>simp at hlen
 | cons h tail=>exact ⟨a,b,c,d,e,f,g,h,tail,rfl⟩
def word8 (a0 a1 a2 a3 a4 a5 a6 a7:Bool):Nat:=word7 a0 a1 a2 a3 a4 a5 a6+128*a7.toNat
def carry8 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7:Bool):Bool:=carryBit a7 b7 (carry7 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6)
theorem carry8_value (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7:Bool):
 (carry8 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7).toNat=(word8 a0 a1 a2 a3 a4 a5 a6 a7+word8 b0 b1 b2 b3 b4 b5 b6 b7)/256:=by
 rw[carry8,carry_bit_nat,carry7_value]
 unfold word8
 omega
theorem carryPrefix_eight (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 cin:Wire) (as bs cs:List Wire)
 (hn:(cin::(([a0,a1,a2,a3,a4,a5,a6,a7]++as)++([b0,b1,b2,b3,b4,b5,b6,b7]++bs)++([c0,c1,c2,c3,c4,c5,c6,c7]++cs))).Nodup) (s:State) (m:List Bool)
 (hz:∀q∈[c0,c1,c2,c3,c4,c5,c6,c7],s.basis q=false) (hi:s.basis cin=false):
 (run (carryPrefix 8 ([a0,a1,a2,a3,a4,a5,a6,a7]++as) ([b0,b1,b2,b3,b4,b5,b6,b7]++bs) ([c0,c1,c2,c3,c4,c5,c6,c7]++cs) cin) m s).basis c7=carry8 (s.basis a0) (s.basis a1) (s.basis a2) (s.basis a3) (s.basis a4) (s.basis a5) (s.basis a6) (s.basis a7) (s.basis b0) (s.basis b1) (s.basis b2) (s.basis b3) (s.basis b4) (s.basis b5) (s.basis b6) (s.basis b7) :=by
 rw[carryPrefix_run 8 ([a0,a1,a2,a3,a4,a5,a6,a7]++as) ([b0,b1,b2,b3,b4,b5,b6,b7]++bs) ([c0,c1,c2,c3,c4,c5,c6,c7]++cs) cin hn s m]
 have hzc0:s.basis c0=false:=hz c0 (by simp)
 have hzc1:s.basis c1=false:=hz c1 (by simp)
 have hzc2:s.basis c2=false:=hz c2 (by simp)
 have hzc3:s.basis c3=false:=hz c3 (by simp)
 have hzc4:s.basis c4=false:=hz c4 (by simp)
 have hzc5:s.basis c5=false:=hz c5 (by simp)
 have hzc6:s.basis c6=false:=hz c6 (by simp)
 have hzc7:s.basis c7=false:=hz c7 (by simp)
 have small:[a0,a1,a2,a3,a4,a5,a6,a7,b0,b1,b2,b3,b4,b5,b6,b7,c0,c1,c2,c3,c4,c5,c6,c7,cin].Nodup:=by
  apply List.nodup_iff_count_le_one.mpr
  intro w
  have h:=List.nodup_iff_count_le_one.mp hn w
  simp only[List.count_cons,List.count_append,List.count_nil]at h ⊢
  omega
 have getNe (i j:Nat) (hi:i<25) (hj:j<25) (hne:i≠j):
  ([a0,a1,a2,a3,a4,a5,a6,a7,b0,b1,b2,b3,b4,b5,b6,b7,c0,c1,c2,c3,c4,c5,c6,c7,cin][i]'hi)≠([a0,a1,a2,a3,a4,a5,a6,a7,b0,b1,b2,b3,b4,b5,b6,b7,c0,c1,c2,c3,c4,c5,c6,c7,cin][j]'hj):=by
  intro e
  exact hne ((List.Nodup.getElem_inj_iff small).mp e)
 have ne0_16:a0≠c0:=getNe 0 16 (by decide) (by decide) (by decide)
 have ne0_17:a0≠c1:=getNe 0 17 (by decide) (by decide) (by decide)
 have ne0_18:a0≠c2:=getNe 0 18 (by decide) (by decide) (by decide)
 have ne0_19:a0≠c3:=getNe 0 19 (by decide) (by decide) (by decide)
 have ne0_20:a0≠c4:=getNe 0 20 (by decide) (by decide) (by decide)
 have ne0_21:a0≠c5:=getNe 0 21 (by decide) (by decide) (by decide)
 have ne0_22:a0≠c6:=getNe 0 22 (by decide) (by decide) (by decide)
 have ne0_23:a0≠c7:=getNe 0 23 (by decide) (by decide) (by decide)
 have ne1_16:a1≠c0:=getNe 1 16 (by decide) (by decide) (by decide)
 have ne1_17:a1≠c1:=getNe 1 17 (by decide) (by decide) (by decide)
 have ne1_18:a1≠c2:=getNe 1 18 (by decide) (by decide) (by decide)
 have ne1_19:a1≠c3:=getNe 1 19 (by decide) (by decide) (by decide)
 have ne1_20:a1≠c4:=getNe 1 20 (by decide) (by decide) (by decide)
 have ne1_21:a1≠c5:=getNe 1 21 (by decide) (by decide) (by decide)
 have ne1_22:a1≠c6:=getNe 1 22 (by decide) (by decide) (by decide)
 have ne1_23:a1≠c7:=getNe 1 23 (by decide) (by decide) (by decide)
 have ne2_16:a2≠c0:=getNe 2 16 (by decide) (by decide) (by decide)
 have ne2_17:a2≠c1:=getNe 2 17 (by decide) (by decide) (by decide)
 have ne2_18:a2≠c2:=getNe 2 18 (by decide) (by decide) (by decide)
 have ne2_19:a2≠c3:=getNe 2 19 (by decide) (by decide) (by decide)
 have ne2_20:a2≠c4:=getNe 2 20 (by decide) (by decide) (by decide)
 have ne2_21:a2≠c5:=getNe 2 21 (by decide) (by decide) (by decide)
 have ne2_22:a2≠c6:=getNe 2 22 (by decide) (by decide) (by decide)
 have ne2_23:a2≠c7:=getNe 2 23 (by decide) (by decide) (by decide)
 have ne3_16:a3≠c0:=getNe 3 16 (by decide) (by decide) (by decide)
 have ne3_17:a3≠c1:=getNe 3 17 (by decide) (by decide) (by decide)
 have ne3_18:a3≠c2:=getNe 3 18 (by decide) (by decide) (by decide)
 have ne3_19:a3≠c3:=getNe 3 19 (by decide) (by decide) (by decide)
 have ne3_20:a3≠c4:=getNe 3 20 (by decide) (by decide) (by decide)
 have ne3_21:a3≠c5:=getNe 3 21 (by decide) (by decide) (by decide)
 have ne3_22:a3≠c6:=getNe 3 22 (by decide) (by decide) (by decide)
 have ne3_23:a3≠c7:=getNe 3 23 (by decide) (by decide) (by decide)
 have ne4_16:a4≠c0:=getNe 4 16 (by decide) (by decide) (by decide)
 have ne4_17:a4≠c1:=getNe 4 17 (by decide) (by decide) (by decide)
 have ne4_18:a4≠c2:=getNe 4 18 (by decide) (by decide) (by decide)
 have ne4_19:a4≠c3:=getNe 4 19 (by decide) (by decide) (by decide)
 have ne4_20:a4≠c4:=getNe 4 20 (by decide) (by decide) (by decide)
 have ne4_21:a4≠c5:=getNe 4 21 (by decide) (by decide) (by decide)
 have ne4_22:a4≠c6:=getNe 4 22 (by decide) (by decide) (by decide)
 have ne4_23:a4≠c7:=getNe 4 23 (by decide) (by decide) (by decide)
 have ne5_16:a5≠c0:=getNe 5 16 (by decide) (by decide) (by decide)
 have ne5_17:a5≠c1:=getNe 5 17 (by decide) (by decide) (by decide)
 have ne5_18:a5≠c2:=getNe 5 18 (by decide) (by decide) (by decide)
 have ne5_19:a5≠c3:=getNe 5 19 (by decide) (by decide) (by decide)
 have ne5_20:a5≠c4:=getNe 5 20 (by decide) (by decide) (by decide)
 have ne5_21:a5≠c5:=getNe 5 21 (by decide) (by decide) (by decide)
 have ne5_22:a5≠c6:=getNe 5 22 (by decide) (by decide) (by decide)
 have ne5_23:a5≠c7:=getNe 5 23 (by decide) (by decide) (by decide)
 have ne6_16:a6≠c0:=getNe 6 16 (by decide) (by decide) (by decide)
 have ne6_17:a6≠c1:=getNe 6 17 (by decide) (by decide) (by decide)
 have ne6_18:a6≠c2:=getNe 6 18 (by decide) (by decide) (by decide)
 have ne6_19:a6≠c3:=getNe 6 19 (by decide) (by decide) (by decide)
 have ne6_20:a6≠c4:=getNe 6 20 (by decide) (by decide) (by decide)
 have ne6_21:a6≠c5:=getNe 6 21 (by decide) (by decide) (by decide)
 have ne6_22:a6≠c6:=getNe 6 22 (by decide) (by decide) (by decide)
 have ne6_23:a6≠c7:=getNe 6 23 (by decide) (by decide) (by decide)
 have ne7_16:a7≠c0:=getNe 7 16 (by decide) (by decide) (by decide)
 have ne7_17:a7≠c1:=getNe 7 17 (by decide) (by decide) (by decide)
 have ne7_18:a7≠c2:=getNe 7 18 (by decide) (by decide) (by decide)
 have ne7_19:a7≠c3:=getNe 7 19 (by decide) (by decide) (by decide)
 have ne7_20:a7≠c4:=getNe 7 20 (by decide) (by decide) (by decide)
 have ne7_21:a7≠c5:=getNe 7 21 (by decide) (by decide) (by decide)
 have ne7_22:a7≠c6:=getNe 7 22 (by decide) (by decide) (by decide)
 have ne7_23:a7≠c7:=getNe 7 23 (by decide) (by decide) (by decide)
 have ne8_16:b0≠c0:=getNe 8 16 (by decide) (by decide) (by decide)
 have ne8_17:b0≠c1:=getNe 8 17 (by decide) (by decide) (by decide)
 have ne8_18:b0≠c2:=getNe 8 18 (by decide) (by decide) (by decide)
 have ne8_19:b0≠c3:=getNe 8 19 (by decide) (by decide) (by decide)
 have ne8_20:b0≠c4:=getNe 8 20 (by decide) (by decide) (by decide)
 have ne8_21:b0≠c5:=getNe 8 21 (by decide) (by decide) (by decide)
 have ne8_22:b0≠c6:=getNe 8 22 (by decide) (by decide) (by decide)
 have ne8_23:b0≠c7:=getNe 8 23 (by decide) (by decide) (by decide)
 have ne9_16:b1≠c0:=getNe 9 16 (by decide) (by decide) (by decide)
 have ne9_17:b1≠c1:=getNe 9 17 (by decide) (by decide) (by decide)
 have ne9_18:b1≠c2:=getNe 9 18 (by decide) (by decide) (by decide)
 have ne9_19:b1≠c3:=getNe 9 19 (by decide) (by decide) (by decide)
 have ne9_20:b1≠c4:=getNe 9 20 (by decide) (by decide) (by decide)
 have ne9_21:b1≠c5:=getNe 9 21 (by decide) (by decide) (by decide)
 have ne9_22:b1≠c6:=getNe 9 22 (by decide) (by decide) (by decide)
 have ne9_23:b1≠c7:=getNe 9 23 (by decide) (by decide) (by decide)
 have ne10_16:b2≠c0:=getNe 10 16 (by decide) (by decide) (by decide)
 have ne10_17:b2≠c1:=getNe 10 17 (by decide) (by decide) (by decide)
 have ne10_18:b2≠c2:=getNe 10 18 (by decide) (by decide) (by decide)
 have ne10_19:b2≠c3:=getNe 10 19 (by decide) (by decide) (by decide)
 have ne10_20:b2≠c4:=getNe 10 20 (by decide) (by decide) (by decide)
 have ne10_21:b2≠c5:=getNe 10 21 (by decide) (by decide) (by decide)
 have ne10_22:b2≠c6:=getNe 10 22 (by decide) (by decide) (by decide)
 have ne10_23:b2≠c7:=getNe 10 23 (by decide) (by decide) (by decide)
 have ne11_16:b3≠c0:=getNe 11 16 (by decide) (by decide) (by decide)
 have ne11_17:b3≠c1:=getNe 11 17 (by decide) (by decide) (by decide)
 have ne11_18:b3≠c2:=getNe 11 18 (by decide) (by decide) (by decide)
 have ne11_19:b3≠c3:=getNe 11 19 (by decide) (by decide) (by decide)
 have ne11_20:b3≠c4:=getNe 11 20 (by decide) (by decide) (by decide)
 have ne11_21:b3≠c5:=getNe 11 21 (by decide) (by decide) (by decide)
 have ne11_22:b3≠c6:=getNe 11 22 (by decide) (by decide) (by decide)
 have ne11_23:b3≠c7:=getNe 11 23 (by decide) (by decide) (by decide)
 have ne12_16:b4≠c0:=getNe 12 16 (by decide) (by decide) (by decide)
 have ne12_17:b4≠c1:=getNe 12 17 (by decide) (by decide) (by decide)
 have ne12_18:b4≠c2:=getNe 12 18 (by decide) (by decide) (by decide)
 have ne12_19:b4≠c3:=getNe 12 19 (by decide) (by decide) (by decide)
 have ne12_20:b4≠c4:=getNe 12 20 (by decide) (by decide) (by decide)
 have ne12_21:b4≠c5:=getNe 12 21 (by decide) (by decide) (by decide)
 have ne12_22:b4≠c6:=getNe 12 22 (by decide) (by decide) (by decide)
 have ne12_23:b4≠c7:=getNe 12 23 (by decide) (by decide) (by decide)
 have ne13_16:b5≠c0:=getNe 13 16 (by decide) (by decide) (by decide)
 have ne13_17:b5≠c1:=getNe 13 17 (by decide) (by decide) (by decide)
 have ne13_18:b5≠c2:=getNe 13 18 (by decide) (by decide) (by decide)
 have ne13_19:b5≠c3:=getNe 13 19 (by decide) (by decide) (by decide)
 have ne13_20:b5≠c4:=getNe 13 20 (by decide) (by decide) (by decide)
 have ne13_21:b5≠c5:=getNe 13 21 (by decide) (by decide) (by decide)
 have ne13_22:b5≠c6:=getNe 13 22 (by decide) (by decide) (by decide)
 have ne13_23:b5≠c7:=getNe 13 23 (by decide) (by decide) (by decide)
 have ne14_16:b6≠c0:=getNe 14 16 (by decide) (by decide) (by decide)
 have ne14_17:b6≠c1:=getNe 14 17 (by decide) (by decide) (by decide)
 have ne14_18:b6≠c2:=getNe 14 18 (by decide) (by decide) (by decide)
 have ne14_19:b6≠c3:=getNe 14 19 (by decide) (by decide) (by decide)
 have ne14_20:b6≠c4:=getNe 14 20 (by decide) (by decide) (by decide)
 have ne14_21:b6≠c5:=getNe 14 21 (by decide) (by decide) (by decide)
 have ne14_22:b6≠c6:=getNe 14 22 (by decide) (by decide) (by decide)
 have ne14_23:b6≠c7:=getNe 14 23 (by decide) (by decide) (by decide)
 have ne15_16:b7≠c0:=getNe 15 16 (by decide) (by decide) (by decide)
 have ne15_17:b7≠c1:=getNe 15 17 (by decide) (by decide) (by decide)
 have ne15_18:b7≠c2:=getNe 15 18 (by decide) (by decide) (by decide)
 have ne15_19:b7≠c3:=getNe 15 19 (by decide) (by decide) (by decide)
 have ne15_20:b7≠c4:=getNe 15 20 (by decide) (by decide) (by decide)
 have ne15_21:b7≠c5:=getNe 15 21 (by decide) (by decide) (by decide)
 have ne15_22:b7≠c6:=getNe 15 22 (by decide) (by decide) (by decide)
 have ne15_23:b7≠c7:=getNe 15 23 (by decide) (by decide) (by decide)
 have ne16_17:c0≠c1:=getNe 16 17 (by decide) (by decide) (by decide)
 have ne16_18:c0≠c2:=getNe 16 18 (by decide) (by decide) (by decide)
 have ne16_19:c0≠c3:=getNe 16 19 (by decide) (by decide) (by decide)
 have ne16_20:c0≠c4:=getNe 16 20 (by decide) (by decide) (by decide)
 have ne16_21:c0≠c5:=getNe 16 21 (by decide) (by decide) (by decide)
 have ne16_22:c0≠c6:=getNe 16 22 (by decide) (by decide) (by decide)
 have ne16_23:c0≠c7:=getNe 16 23 (by decide) (by decide) (by decide)
 have ne17_16:c1≠c0:=getNe 17 16 (by decide) (by decide) (by decide)
 have ne17_18:c1≠c2:=getNe 17 18 (by decide) (by decide) (by decide)
 have ne17_19:c1≠c3:=getNe 17 19 (by decide) (by decide) (by decide)
 have ne17_20:c1≠c4:=getNe 17 20 (by decide) (by decide) (by decide)
 have ne17_21:c1≠c5:=getNe 17 21 (by decide) (by decide) (by decide)
 have ne17_22:c1≠c6:=getNe 17 22 (by decide) (by decide) (by decide)
 have ne17_23:c1≠c7:=getNe 17 23 (by decide) (by decide) (by decide)
 have ne18_16:c2≠c0:=getNe 18 16 (by decide) (by decide) (by decide)
 have ne18_17:c2≠c1:=getNe 18 17 (by decide) (by decide) (by decide)
 have ne18_19:c2≠c3:=getNe 18 19 (by decide) (by decide) (by decide)
 have ne18_20:c2≠c4:=getNe 18 20 (by decide) (by decide) (by decide)
 have ne18_21:c2≠c5:=getNe 18 21 (by decide) (by decide) (by decide)
 have ne18_22:c2≠c6:=getNe 18 22 (by decide) (by decide) (by decide)
 have ne18_23:c2≠c7:=getNe 18 23 (by decide) (by decide) (by decide)
 have ne19_16:c3≠c0:=getNe 19 16 (by decide) (by decide) (by decide)
 have ne19_17:c3≠c1:=getNe 19 17 (by decide) (by decide) (by decide)
 have ne19_18:c3≠c2:=getNe 19 18 (by decide) (by decide) (by decide)
 have ne19_20:c3≠c4:=getNe 19 20 (by decide) (by decide) (by decide)
 have ne19_21:c3≠c5:=getNe 19 21 (by decide) (by decide) (by decide)
 have ne19_22:c3≠c6:=getNe 19 22 (by decide) (by decide) (by decide)
 have ne19_23:c3≠c7:=getNe 19 23 (by decide) (by decide) (by decide)
 have ne20_16:c4≠c0:=getNe 20 16 (by decide) (by decide) (by decide)
 have ne20_17:c4≠c1:=getNe 20 17 (by decide) (by decide) (by decide)
 have ne20_18:c4≠c2:=getNe 20 18 (by decide) (by decide) (by decide)
 have ne20_19:c4≠c3:=getNe 20 19 (by decide) (by decide) (by decide)
 have ne20_21:c4≠c5:=getNe 20 21 (by decide) (by decide) (by decide)
 have ne20_22:c4≠c6:=getNe 20 22 (by decide) (by decide) (by decide)
 have ne20_23:c4≠c7:=getNe 20 23 (by decide) (by decide) (by decide)
 have ne21_16:c5≠c0:=getNe 21 16 (by decide) (by decide) (by decide)
 have ne21_17:c5≠c1:=getNe 21 17 (by decide) (by decide) (by decide)
 have ne21_18:c5≠c2:=getNe 21 18 (by decide) (by decide) (by decide)
 have ne21_19:c5≠c3:=getNe 21 19 (by decide) (by decide) (by decide)
 have ne21_20:c5≠c4:=getNe 21 20 (by decide) (by decide) (by decide)
 have ne21_22:c5≠c6:=getNe 21 22 (by decide) (by decide) (by decide)
 have ne21_23:c5≠c7:=getNe 21 23 (by decide) (by decide) (by decide)
 have ne22_16:c6≠c0:=getNe 22 16 (by decide) (by decide) (by decide)
 have ne22_17:c6≠c1:=getNe 22 17 (by decide) (by decide) (by decide)
 have ne22_18:c6≠c2:=getNe 22 18 (by decide) (by decide) (by decide)
 have ne22_19:c6≠c3:=getNe 22 19 (by decide) (by decide) (by decide)
 have ne22_20:c6≠c4:=getNe 22 20 (by decide) (by decide) (by decide)
 have ne22_21:c6≠c5:=getNe 22 21 (by decide) (by decide) (by decide)
 have ne22_23:c6≠c7:=getNe 22 23 (by decide) (by decide) (by decide)
 have ne23_16:c7≠c0:=getNe 23 16 (by decide) (by decide) (by decide)
 have ne23_17:c7≠c1:=getNe 23 17 (by decide) (by decide) (by decide)
 have ne23_18:c7≠c2:=getNe 23 18 (by decide) (by decide) (by decide)
 have ne23_19:c7≠c3:=getNe 23 19 (by decide) (by decide) (by decide)
 have ne23_20:c7≠c4:=getNe 23 20 (by decide) (by decide) (by decide)
 have ne23_21:c7≠c5:=getNe 23 21 (by decide) (by decide) (by decide)
 have ne23_22:c7≠c6:=getNe 23 22 (by decide) (by decide) (by decide)
 have ne24_16:cin≠c0:=getNe 24 16 (by decide) (by decide) (by decide)
 have ne24_17:cin≠c1:=getNe 24 17 (by decide) (by decide) (by decide)
 have ne24_18:cin≠c2:=getNe 24 18 (by decide) (by decide) (by decide)
 have ne24_19:cin≠c3:=getNe 24 19 (by decide) (by decide) (by decide)
 have ne24_20:cin≠c4:=getNe 24 20 (by decide) (by decide) (by decide)
 have ne24_21:cin≠c5:=getNe 24 21 (by decide) (by decide) (by decide)
 have ne24_22:cin≠c6:=getNe 24 22 (by decide) (by decide) (by decide)
 have ne24_23:cin≠c7:=getNe 24 23 (by decide) (by decide) (by decide)
 clear hn small getNe hz
 simp_all[prefixState,writeBit,Function.update,carry8,carry7,carry6]
theorem carryPrefix_value8 (xs ys cs : List Wire) (cin : Wire)
    (hx:8≤xs.length) (hy:8≤ys.length) (hc:8≤cs.length)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State) (m : List Bool)
    (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false) :
    ((run (carryPrefix 8 xs ys cs cin) m s).basis (cs.getD 7 0)).toNat=
      (regValue (xs.take 8) s.basis+regValue (ys.take 8) s.basis)/256 := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,as,rfl⟩:=shape8 xs hx
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,bs,rfl⟩:=shape8 ys hy
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,cs,rfl⟩:=shape8 cs hc
  have zeros:∀q∈[c0,c1,c2,c3,c4,c5,c6,c7],s.basis q=false := by
    intro q hq
    apply hz q
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have v:=congrArg Bool.toNat (carryPrefix_eight a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 cin as bs cs hn s m zeros hi)
  rw [carry8_value] at v
  simpa [regValue,word8,word7,word6,Bool.toNat,Bool.cond_eq_ite,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] using v

def subPre8 (xs ys cs : List Wire) (cin : Wire) : Program :=
  notRegister ys++carryPrefix 8 xs ys cs cin

theorem subPre8_value8 (xs ys cs : List Wire) (cin : Wire)
    (hx:8≤xs.length) (hy:8≤ys.length) (hc:8≤cs.length)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State)
    (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false) :
    ((run (subPre8 xs ys cs cin) [] s).basis (cs.getD 7 0)).toNat=
      (regValue (xs.take 8) s.basis+(255-regValue (ys.take 8) s.basis))/256 := by
  have nd:=List.nodup_cons.mp hn
  have split:=List.nodup_append'.mp nd.2
  have xy:=List.nodup_append'.mp split.1
  have xAway:∀q∈xs,q∉ys := by
    intro q hq bad
    exact List.disjoint_left.mp xy.2.2 hq bad
  have cAway:∀q∈cs,q∉ys := by
    intro q hq bad
    exact List.disjoint_left.mp split.2.2 (List.mem_append_right _ bad) hq
  have cinAway:cin∉ys := by
    intro bad
    exact nd.1 (List.mem_append_left _ (List.mem_append_right _ bad))
  let t:=run (notRegister ys) [] s
  have nr:=notRegister_correct ys xy.2.1 s []
  have zt:∀q∈cs,t.basis q=false := by
    intro q hq
    change (run (notRegister ys) [] s).basis q=false
    rw [nr]
    simpa [cAway q hq] using hz q hq
  have it:t.basis cin=false := by
    change (run (notRegister ys) [] s).basis cin=false
    rw [nr]
    simpa [cinAway] using hi
  have xv:regValue (xs.take 8) t.basis=regValue (xs.take 8) s.basis := by
    apply regValue_congr
    intro q hq
    change (run (notRegister ys) [] s).basis q=s.basis q
    rw [nr]
    simp [xAway q (List.mem_of_mem_take hq)]
  have yv:regValue (ys.take 8) t.basis=255-regValue (ys.take 8) s.basis := by
    have e:regValue (ys.take 8) t.basis=regValue (ys.take 8) (fun q=>!s.basis q) := by
      apply regValue_congr
      intro q hq
      change (run (notRegister ys) [] s).basis q= !s.basis q
      rw [nr]
      simp [List.mem_of_mem_take hq]
    rw [e,regValue_complement]
    have len:(ys.take 8).length=8 := by simp [hy]
    rw [len]
    norm_num
  have val:=carryPrefix_value8 xs ys cs cin hx hy hc hn t [] zt it
  rw [xv,yv] at val
  have count:measurementCount (notRegister ys)=0 := (notRegister_counts ys).2
  simpa only [subPre8,run_append,count,List.take_zero,List.drop_zero] using val

#print axioms carryPrefix_value8
#print axioms subPre8_value8
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarrySplits
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def eighthMajority (xs ys cs:List Wire):Program:=
 majority (xs.getD 7 0) (ys.getD 7 0) (cs.getD 6 0) (cs.getD 7 0)
def subPost8 (xs ys cs:List Wire) (cin:Wire):Program:=addKTSuffix true 8 xs ys cs cin++notRegister ys

theorem carryPrefix_split8 (xs ys cs:List Wire) (cin:Wire) (hx:8≤xs.length) (hy:8≤ys.length) (hc:8≤cs.length):
 carryPrefix 8 xs ys cs cin=carryPrefix 7 xs ys cs cin++eighthMajority xs ys cs:=by
 obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,as,rfl⟩:=shape8 xs hx
 obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,bs,rfl⟩:=shape8 ys hy
 obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,cs,rfl⟩:=shape8 cs hc
 simp[carryPrefix,eighthMajority,List.append_assoc]

theorem subPre8_split (xs ys cs:List Wire) (cin:Wire) (hx:8≤xs.length) (hy:8≤ys.length) (hc:8≤cs.length):
 subPre8 xs ys cs cin=subPre7 xs ys cs cin++eighthMajority xs ys cs:=by
 simp only[subPre8,subPre7,carryPrefix_split8 xs ys cs cin hx hy hc,List.append_assoc]

theorem subPost7_split8 (xs ys cs:List Wire) (cin:Wire) (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:10≤ys.length):
 subPost7 xs ys cs cin=eighthMajority xs ys cs++subPost8 xs ys cs cin:=by
 have a:=addKT_split true 7 xs ys cs cin hx hc (by omega)
 have b:=addKT_split true 8 xs ys cs cin hx hc hy
 rw[carryPrefix_split8 xs ys cs cin (by omega) (by omega) (by omega),List.append_assoc]at b
 have eq:carryPrefix 7 xs ys cs cin++addKTSuffix true 7 xs ys cs cin=
  carryPrefix 7 xs ys cs cin++(eighthMajority xs ys cs++addKTSuffix true 8 xs ys cs cin):=a.symm.trans b
 have tail:=List.append_cancel_left eq
 simp only[subPost7,subPost8,tail,List.append_assoc]

def preTriple (xs ys cs:List Wire) (cin q r t:Wire):Program:=
 secondCopy (subPre xs ys cs cin) (sixthMajority xs ys cs) (seventhMajority xs ys cs)
  (cs.getD 4 0) (cs.getD 5 0) q r++[.CX (cs.getD 6 0) t]

def cachedSubQuad (xs ys cs:List Wire) (cin q r t u:Wire):Program:=
 insertCopy (preTriple xs ys cs cin q r t++eighthMajority xs ys cs) (subPost8 xs ys cs cin) (cs.getD 7 0) u

theorem cachedSubTriple_split8 (xs ys cs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:10≤ys.length):
 cachedSubTriple xs ys cs cin q r t=
 (preTriple xs ys cs cin q r t++eighthMajority xs ys cs)++subPost8 xs ys cs cin:=by
 rw[cachedSubTriple,subPost7_split8 xs ys cs cin hx hc hy]
 simp only[preTriple,insertCopy,List.append_assoc]

theorem source_suffix_four_heads (src Z ys carry:List Wire) (cin:Wire)
 (hs:10≤src.length) (hy:ys.length=src.length+5) (hc:8≤carry.length):
 (knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin).take 24=
 majority ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0)++
 sixthMajority (src++Z.take 5) ys carry++seventhMajority (src++Z.take 5) ys carry++eighthMajority (src++Z.take 5) ys carry:=by
 obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,as,rfl⟩:=shape8 src (by omega)
 cases as with
 | nil=>simp only[List.length_cons,List.length_nil]at hs;omega
 | cons a8 as=>
  cases as with
  | nil=>simp only[List.length_cons,List.length_nil]at hs;omega
  | cons a9 as=>
   obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,bs,rfl⟩:=shape8 ys (by simp only[List.length_cons]at hy;omega)
   cases bs with
   | nil=>simp only[List.length_cons,List.length_nil]at hy;omega
   | cons b8 bs=>
    cases bs with
    | nil=>simp only[List.length_cons,List.length_nil]at hy;omega
    | cons b9 bs=>
     obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,cs,rfl⟩:=shape8 carry hc
     change _=majority a4 b4 c3 c4++majority a5 b5 c4 c5++majority a6 b6 c5 c6++majority a7 b7 c6 c7
     simp[knownSuffix,desired,mappedRead,mappedAdd,mappedMajority,majority,List.append_assoc]

def addPost4 (src Z ys carry:List Wire) (cin:Wire):Program:=
 (knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin).drop 24

theorem addPost3_split8 (src Z ys carry:List Wire) (cin:Wire)
 (hs:10≤src.length) (hy:ys.length=src.length+5) (hc:8≤carry.length):
 addPost3 src Z ys carry cin=eighthMajority (src++Z.take 5) ys carry++addPost4 src Z ys carry cin:=by
 let suffix:=knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin
 have split:=List.take_append_drop 24 suffix
 rw[source_suffix_four_heads src Z ys carry cin hs hy hc]at split
 have eq:=congrArg (List.drop 18) split.symm
 simpa only[addPost3,addPost4,eighthMajority,seventhMajority,sixthMajority,majority,List.append_assoc,List.drop_succ_cons,List.drop_zero,List.nil_append]using eq

def consumedAddQuad (src Z ys carry:List Wire) (cin q r t u:Wire):Program:=
 (((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0))++move t (carry.getD 6 0))++move u (carry.getD 7 0)++addPost4 src Z ys carry cin

theorem consumedAddTriple_split8 (src Z ys carry:List Wire) (cin q r t:Wire)
 (hs:10≤src.length) (hy:ys.length=src.length+5) (hc:8≤carry.length):
 consumedAddTriple src Z ys carry cin q r t=
 (((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0))++move t (carry.getD 6 0))++eighthMajority (src++Z.take 5) ys carry++addPost4 src Z ys carry cin:=by
 rw[consumedAddTriple,addPost3_split8 src Z ys carry cin hs hy hc]
 simp only[List.append_assoc]
#print axioms cachedSubTriple_split8
#print axioms consumedAddTriple_split8
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryCopy
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem thirdCopy_value (pre next next2 post:Program) (c d e q r t w:Wire)
 (hqpre:q∉wires pre) (hqnext:q∉wires next) (hqnext2:q∉wires next2) (hqpost:q∉wires post)
 (hrpre:r∉wires (insertCopy pre next c q)) (hrnext2:r∉wires next2) (hrpost:r∉wires post)
 (htpre:t∉wires (secondCopy pre next next2 c d q r)) (htpost:t∉wires post)
 (mp:measurementCount pre=0) (mn:measurementCount next=0)
 (dq:d≠q) (wq:w≠q) (wr:w≠r) (wt:w≠t)
 (s:State) (hq:s.basis q=false) (hr:s.basis r=false) (ht:s.basis t=false):
 (run (insertCopy (secondCopy pre next next2 c d q r) post e t) [] s).basis w=
 (run (pre++next++next2++post) [] s).basis w:=by
 rw[insertCopy_correct _ _ _ _ htpre htpost s [] ht]
 simp only[writeBit,Function.update_of_ne wt]
 have hqp:q∉wires (next2++post):=by simp only[wires_append,Finset.mem_union,not_or];exact ⟨hqnext2,hqpost⟩
 have hrp:r∉wires (next2++post):=by simp only[wires_append,Finset.mem_union,not_or];exact ⟨hrnext2,hrpost⟩
 have h:=secondCopy_value pre next (next2++post) c d q r w hqpre hqnext hqp hrpre hrp mp mn dq wq wr s hq hr
 simpa only[secondCopy,insertCopy,List.append_assoc]using h

theorem cachedSubQuad_frame (xs ys cs:List Wire) (cin q r t u:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:10≤ys.length)
 (off:u∉wires (cachedSubTriple xs ys cs cin q r t))
 (s:State) (m:List Bool) (hu:s.basis u=false):
 run (cachedSubQuad xs ys cs cin q r t u) m s=
 ⟨(run (cachedSubTriple xs ys cs cin q r t) m s).phase,
 writeBit (run (cachedSubTriple xs ys cs cin q r t) m s).basis u
 ((run (preTriple xs ys cs cin q r t++eighthMajority xs ys cs) [] s).basis (cs.getD 7 0))⟩:=by
 have split:=cachedSubTriple_split8 xs ys cs cin q r t hx hc hy
 rw[split,wires_append,Finset.mem_union,not_or]at off
 have mp:measurementCount (preTriple xs ys cs cin q r t++eighthMajority xs ys cs)=0:=by
  simp[preTriple,secondCopy,insertCopy,subPre,sixthMajority,seventhMajority,eighthMajority,majority,measurementCount_append,
   (notRegister_counts ys).2,carryPrefix_measurements,measurementCount]
 rw[cachedSubQuad,insertCopy_correct _ _ _ _ off.1 off.2 s m hu,mp,List.take_zero,←split]
#print axioms thirdCopy_value
#print axioms cachedSubQuad_frame
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryKnown
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem cachedSubQuad_known_frame (xs ys cs:List Wire) (cin q r t u:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:10≤ys.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (s:State) (m:List Bool)
 (hz:∀w∈cs,s.basis w=false) (hi:s.basis cin=false)
 (qoff:q∉wires (CodexNarrowSub.program xs ys cs cin))
 (roff:r∉wires (CodexNarrowSub.program xs ys cs cin)) (rq:r≠q)
 (toff:t∉wires (cachedSubDual xs ys cs cin q r))
 (off:u∉wires (cachedSubTriple xs ys cs cin q r t))
 (hq:s.basis q=false) (hr:s.basis r=false) (ht:s.basis t=false) (hu:s.basis u=false)
 (H:Nat) (source:regValue xs s.basis=H) (target:regValue ys s.basis=1040*H/64):
 run (cachedSubQuad xs ys cs cin q r t u) m s=
 ⟨(run (cachedSubTriple xs ys cs cin q r t) m s).phase,
 writeBit (run (cachedSubTriple xs ys cs cin q r t) m s).basis u (cacheBit8 H)⟩:=by
 have split:subPre xs ys cs cin++(sixthMajority xs ys cs++(seventhMajority xs ys cs++(eighthMajority xs ys cs++subPost8 xs ys cs cin)))=
  CodexNarrowSub.program xs ys cs cin:=by
  rw[←subPost7_split8 xs ys cs cin hx hc hy,←subPost6_split7 xs ys cs cin hx hc (by omega),←subPost_split6 xs ys cs cin hx hc (by omega)]
  exact sub_split xs ys cs cin hx hc (by omega)
 have qo:=qoff
 have ro:=roff
 rw[←split]at qo ro
 simp only[wires_append,Finset.mem_union,not_or]at qo ro
 have rfirst:r∉wires (cachedSub xs ys cs cin q):=by
  intro h
  have h:=Finset.mem_insert.mp (cachedSub_support xs ys cs cin q hx hc (by omega) h)
  exact h.elim rq roff
 rw[cachedSub_first_split xs ys cs cin q hx hc (by omega),firstCopy_split,wires_append,Finset.mem_union,not_or]at rfirst
 have tfree:=toff
 rw[cachedSubDual_split7 xs ys cs cin q r hx hc (by omega),subPost7_split8 xs ys cs cin hx hc hy]at tfree
 simp only[wires_append,Finset.mem_union,not_or]at tfree
 have dq:cs.getD 5 0≠q:=by
  intro e;apply qo.2.1
  simp[sixthMajority,majority,wires,Instr.wires,←e]
 have wq:cs.getD 7 0≠q:=by
  intro e;apply qo.2.2.2.1
  simp[eighthMajority,majority,wires,Instr.wires,←e]
 have wr:cs.getD 7 0≠r:=by
  intro e;apply ro.2.2.2.1
  simp[eighthMajority,majority,wires,Instr.wires,←e]
 have wt:cs.getD 7 0≠t:=by
  intro e;apply tfree.2.1
  simp[eighthMajority,majority,wires,Instr.wires,←e]
 have mp:measurementCount (subPre xs ys cs cin)=0:=by
  simp only[subPre,measurementCount_append,(notRegister_counts ys).2,carryPrefix_measurements,Nat.zero_add]
 have value:=thirdCopy_value (subPre xs ys cs cin) (sixthMajority xs ys cs) (seventhMajority xs ys cs) (eighthMajority xs ys cs)
  (cs.getD 4 0) (cs.getD 5 0) (cs.getD 6 0) q r t (cs.getD 7 0)
  qo.1 qo.2.1 qo.2.2.1 qo.2.2.2.1 rfirst.1 ro.2.2.1 ro.2.2.2.1 tfree.1 tfree.2.1 mp rfl dq wq wr wt s hq hr ht
 have pref:subPre xs ys cs cin++sixthMajority xs ys cs++seventhMajority xs ys cs++eighthMajority xs ys cs=subPre8 xs ys cs cin:=by
  rw[←subPre6_split xs ys cs cin (by omega) (by omega) (by omega),←subPre7_split xs ys cs cin (by omega) (by omega) (by omega),←subPre8_split xs ys cs cin (by omega) (by omega) (by omega)]
 rw[pref]at value
 have v:=subPre8_value8 xs ys cs cin (by omega) (by omega) (by omega) hn s hz hi
 rw[Arithmetic.CuccaroStreamedSquareWideLayout.regValue_take_mod xs 8 (by omega) s.basis,Arithmetic.CuccaroStreamedSquareWideLayout.regValue_take_mod ys 8 (by omega) s.basis,source,target]at v
 norm_num only[show 2^8=256 by decide]at v
 rw[sub_add_carry8_w64 H,carry_return8_w64 H]at v
 have known:(run (subPre8 xs ys cs cin) [] s).basis (cs.getD 7 0)=cacheBit8 H:=
  bool_nat_injective _ _ (v.trans (cacheBit8_value H).symm)
 have value':(run (preTriple xs ys cs cin q r t++eighthMajority xs ys cs) [] s).basis (cs.getD 7 0)=cacheBit8 H:=by
  simpa only[preTriple,insertCopy,List.append_assoc]using value.trans known
 rw[cachedSubQuad_frame xs ys cs cin q r t u hx hc hy off s m hu,value']
#print axioms cachedSubQuad_known_frame
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryNext
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem carryPrefix_next_value8 (xs ys carry : List Wire) (cin : Wire)
    (hx:8≤xs.length) (hy:8≤ys.length) (hc:8≤carry.length)
    (hn:(cin::(xs++ys++carry)).Nodup) (s : State)
    (hz:∀q∈carry,s.basis q=false) (hi:s.basis cin=false) :
    (carryBit
      ((run (carryPrefix 7 xs ys carry cin) [] s).basis (xs.getD 7 0))
      ((run (carryPrefix 7 xs ys carry cin) [] s).basis (ys.getD 7 0))
      ((run (carryPrefix 7 xs ys carry cin) [] s).basis (carry.getD 6 0))).toNat=
      (regValue (xs.take 8) s.basis+regValue (ys.take 8) s.basis)/256 := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,as,rfl⟩:=shape8 xs hx
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,bs,rfl⟩:=shape8 ys hy
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,cs,rfl⟩:=shape8 carry hc
  let xs:=a0::a1::a2::a3::a4::a5::a6::a7::as
  let ys:=b0::b1::b2::b3::b4::b5::b6::b7::bs
  let carry:=c0::c1::c2::c3::c4::c5::c6::c7::cs
  let t:=run (carryPrefix 7 xs ys carry cin) [] s
  have nd4:[a7,b7,c6,c7].Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro w
    have h:=List.nodup_iff_count_le_one.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ndcs:carry.Nodup := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
  have off:c7∉carry.take 7 := by
    change c7∉[c0,c1,c2,c3,c4,c5,c6]
    intro mem
    have pos:=List.count_pos_iff.mpr mem
    have bound:=List.nodup_iff_count_le_one.mp ndcs c7
    simp only [carry,List.count_cons,List.count_nil] at pos bound
    simp only [beq_self_eq_true,if_true] at bound
    omega
  have clean:t.basis c7=false :=
    (carryPrefix_preserves 7 xs ys carry cin hn s [] c7 off).trans (hz c7 (by simp))
  have split:carryPrefix 8 xs ys carry cin=carryPrefix 7 xs ys carry cin++majority a7 b7 c6 c7 := by
    simp [xs,ys,carry,carryPrefix,List.append_assoc]
  have run7:run (carryPrefix 8 xs ys carry cin) [] s=run (majority a7 b7 c6 c7) [] t := by
    rw [split,run_append]
    simp only [List.take_nil,List.drop_nil,t]
  have v:=carryPrefix_value8 xs ys carry cin hx hy hc hn s [] hz hi
  rw [run7,majority_correct a7 b7 c6 c7 nd4 t [],clean] at v
  change (carryBit (t.basis a7) (t.basis b7) (t.basis c6)).toNat=_
  have get:carry.getD 7 0=c7 := rfl
  rw [get] at v
  simpa only [writeBit,Function.update_self,Bool.false_xor] using v

#print axioms carryPrefix_next_value8
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryConsumePrefix
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem source_prefix_consumed_eq7 (src Z ys carry:List Wire) (cin q r t:Wire)
 (hs:9≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5) (hc:carry.length+1=ys.length)
 (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
 (s:State) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
 (hcin:s.basis cin=false) (H:Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64)
 (fresh:q∉(src++Z.take 5)++ys++carry) (rfresh:r∉(src++Z.take 5)++ys++carry) (rq:r≠q)
 (tfresh:t∉carry) (tq:t≠q) (tr:t≠r)
 (saved:s.basis q=cacheBit H) (savedR:s.basis r=cacheBit6 H) (savedT:s.basis t=cacheBit7 H):
 run (((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0))++move t (carry.getD 6 0)) [] s=
 setWire (setWire (setWire (run (carryPrefix 7 (src++Z.take 5) ys carry cin) [] s) q false) r false) t false:=by
 let xs:=src++Z.take 5
 let pre:=(addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0)
 have xlen:7≤xs.length:=by dsimp[xs];simp only[List.length_append];omega
 have enough:7≤carry.length:=by omega
 have nd:=seventh_majority_nd xs ys carry cin xlen (by omega) enough hn
 have ne:t≠carry.getD 6 0:=by intro e;exact tfresh (e.symm ▸ DiagSq.getD_in carry 6 (by omega))
 have ready:=source_third_consume_ready src Z ys carry cin q r t hs hzl hy hc hn s hz hclean hcin H hsrc hys fresh rfresh rq tfresh tq tr saved savedR savedT
 have rf:r∉carry:=by intro h;exact rfresh (by simp[h])
 have eq6:run pre [] s=setWire (setWire (run (carryPrefix 6 xs ys carry cin) [] s) q false) r false:=
  source_prefix_consumed_eq6 src Z ys carry cin q r (by omega) hzl hy hc hn s hz hclean hcin H hsrc hys fresh rf rq saved savedR
 have result:=secondConsume_correct pre [] (xs.getD 6 0) (ys.getD 6 0) (carry.getD 5 0) (carry.getD 6 0) t
  nd ne (by simp[wires]) s []
  (by simpa only[List.take_nil]using ready.1) (by simpa only[List.take_nil]using ready.2)
 simp only[List.append_nil]at result
 have away (w:Wire) (hw:w∉xs++ys++carry):w∉wires (seventhMajority xs ys carry):=by
  have na:w≠xs.getD 6 0:=by intro e;exact hw (e.symm ▸ List.mem_append_left _ (List.mem_append_left _ (DiagSq.getD_in xs 6 (by omega))))
  have nb:w≠ys.getD 6 0:=by intro e;exact hw (e.symm ▸ List.mem_append_left _ (List.mem_append_right _ (DiagSq.getD_in ys 6 (by omega))))
  have nc:w≠carry.getD 5 0:=by intro e;exact hw (e.symm ▸ List.mem_append_right _ (DiagSq.getD_in carry 5 (by omega)))
  have nd:w≠carry.getD 6 0:=by intro e;exact hw (e.symm ▸ List.mem_append_right _ (DiagSq.getD_in carry 6 (by omega)))
  simp only[List.getD_eq_getElem?_getD]at na nb nc nd
  simp[seventhMajority,majority,wires,Instr.wires,na,nb,nc,nd]
 have qo:=away q fresh
 have ro:=away r rfresh
 have old7:run (pre++seventhMajority xs ys carry) [] s=
  setWire (setWire (run (carryPrefix 7 xs ys carry cin) [] s) q false) r false:=by
  rw[run_append,List.take_nil,List.drop_nil,eq6]
  have commute (w:Wire) (hw:w∉wires (seventhMajority xs ys carry)) (v:State):
   run (seventhMajority xs ys carry) [] (setWire v w false)=setWire (run (seventhMajority xs ys carry) [] v) w false:=by
   exact run_update_outside _ w false hw v []
  rw[commute r ro,commute q qo]
  have ce:=carryPrefix_split7 xs ys carry cin xlen (by omega) enough
  rw[ce,run_append,List.take_nil,List.drop_nil]
 change run (pre++move t (carry.getD 6 0)) [] s=_
 rw[result]
 change setWire (run (pre++seventhMajority xs ys carry) [] s) t false=_
 rw[old7]
#print axioms source_prefix_consumed_eq7
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryReady
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem eighth_not_take7 (carry:List Wire) (hc:8≤carry.length) (hn:carry.Nodup):
 carry.getD 7 0∉carry.take 7:=by
 obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,cs,rfl⟩:=shape8 carry hc
 change c7∉[c0,c1,c2,c3,c4,c5,c6]
 intro mem
 have pos:=List.count_pos_iff.mpr mem
 have bound:=List.nodup_iff_count_le_one.mp hn c7
 simp only[List.count_cons,List.count_nil]at pos bound
 simp only[beq_self_eq_true,if_true]at bound
 omega

theorem eighth_majority_nd (xs ys carry:List Wire) (cin:Wire)
 (hx:8≤xs.length) (hy:8≤ys.length) (hc:8≤carry.length)
 (hn:(cin::(xs++ys++carry)).Nodup):
 [xs.getD 7 0,ys.getD 7 0,carry.getD 6 0,carry.getD 7 0].Nodup:=by
 obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,as,rfl⟩:=shape8 xs hx
 obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,bs,rfl⟩:=shape8 ys hy
 obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,cs,rfl⟩:=shape8 carry hc
 change [a7,b7,c6,c7].Nodup
 apply List.nodup_iff_count_le_one.mpr
 intro w
 have h:=List.nodup_iff_count_le_one.mp hn w
 simp only[List.count_cons,List.count_append,List.count_nil]at h ⊢
 omega

theorem source_fourth_consume_ready (src Z ys carry:List Wire) (cin q r t u:Wire)
 (hs:10≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5) (hc:carry.length+1=ys.length)
 (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
 (s:State) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
 (hcin:s.basis cin=false) (H:Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64)
 (fresh:q∉(src++Z.take 5)++ys++carry) (rfresh:r∉(src++Z.take 5)++ys++carry) (rq:r≠q)
 (tfresh:t∉(src++Z.take 5)++ys++carry) (tq:t≠q) (tr:t≠r)
 (ufresh:u∉carry) (uq:u≠q) (ur:u≠r) (ut:u≠t)
 (saved:s.basis q=cacheBit H) (savedR:s.basis r=cacheBit6 H) (savedT:s.basis t=cacheBit7 H) (savedU:s.basis u=cacheBit8 H):
 let v:=run (((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0))++move t (carry.getD 6 0)) [] s
 v.basis (carry.getD 7 0)=false ∧
 v.basis u=carryBit (v.basis ((src++Z.take 5).getD 7 0)) (v.basis (ys.getD 7 0)) (v.basis (carry.getD 6 0)):=by
 let xs:=src++Z.take 5
 let base:=run (carryPrefix 7 xs ys carry cin) [] s
 let v:=run (((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0))++move t (carry.getD 6 0)) [] s
 have enough:8≤carry.length:=by omega
 have xlen:8≤xs.length:=by dsimp[xs];simp only[List.length_append];omega
 have tf:t∉carry:=by intro h;exact tfresh (by simp[h])
 have eq:v=setWire (setWire (setWire base q false) r false) t false:=
  source_prefix_consumed_eq7 src Z ys carry cin q r t (by omega) hzl hy hc hn s hz hclean hcin H hsrc hys fresh rfresh rq tf tq tr saved savedR savedT
 have outside (w:Wire) (hw:w∈xs++ys++carry):v.basis w=base.basis w:=by
  have wq:w≠q:=by intro e;exact fresh (e ▸ hw)
  have wr:w≠r:=by intro e;exact rfresh (e ▸ hw)
  have wt:w≠t:=by intro e;exact tfresh (e ▸ hw)
  rw[eq]
  simp only[setWire,writeBit,Function.update_of_ne wt,Function.update_of_ne wr,Function.update_of_ne wq]
 have ndcs:carry.Nodup:=(List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
 have clean:v.basis (carry.getD 7 0)=false:=
  (outside _ (List.mem_append_right _ (DiagSq.getD_in carry 7 (by omega)))).trans
  ((carryPrefix_preserves 7 xs ys carry cin hn s [] _ (eighth_not_take7 carry enough ndcs)).trans
   (hclean _ (DiagSq.getD_in carry 7 (by omega))))
 have kept:v.basis u=cacheBit8 H:=by
  rw[eq]
  simp only[setWire,writeBit,Function.update_of_ne ut,Function.update_of_ne ur,Function.update_of_ne uq]
  exact (carryPrefix_preserves 7 xs ys carry cin hn s [] u (fun h=>ufresh (List.mem_of_mem_take h))).trans savedU
 have val:=carryPrefix_next_value8 xs ys carry cin xlen (by omega) enough hn s hclean hcin
 have xvalue:regValue xs s.basis=H:=by
  have zv:regValue (Z.take 5) s.basis=0:=(regValue_zero _ _).mpr (fun w hw=>hz w (List.mem_of_mem_take hw))
  simp only[xs,regValue_append,zv,hsrc,Nat.mul_zero,Nat.add_zero]
 rw[Arithmetic.CuccaroStreamedSquareWideLayout.regValue_take_mod xs 8 xlen s.basis,
  Arithmetic.CuccaroStreamedSquareWideLayout.regValue_take_mod ys 8 (by omega) s.basis,xvalue,hys]at val
 norm_num only[show 2^8=256 by decide]at val
 rw[carry_return8_w64 H]at val
 have known:carryBit (base.basis (xs.getD 7 0)) (base.basis (ys.getD 7 0)) (base.basis (carry.getD 6 0))=cacheBit8 H:=
  bool_nat_injective _ _ (val.trans (cacheBit8_value H).symm)
 refine ⟨clean,?_⟩
 change v.basis u=carryBit (v.basis (xs.getD 7 0)) (v.basis (ys.getD 7 0)) (v.basis (carry.getD 6 0))
 rw[outside _ (List.mem_append_left _ (List.mem_append_left _ (DiagSq.getD_in xs 7 (by omega)))),
  outside _ (List.mem_append_left _ (List.mem_append_right _ (DiagSq.getD_in ys 7 (by omega)))),
  outside _ (List.mem_append_right _ (DiagSq.getD_in carry 6 (by omega))),known]
 exact kept
#print axioms source_fourth_consume_ready
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop SourceAddFourDevelop
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem cachedSubQuad_counts (xs ys cs:List Wire) (cin q r t u:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:10≤ys.length):
 toffoliCount (cachedSubQuad xs ys cs cin q r t u)=toffoliCount (cachedSubTriple xs ys cs cin q r t) ∧
 measurementCount (cachedSubQuad xs ys cs cin q r t u)=measurementCount (cachedSubTriple xs ys cs cin q r t) ∧
 Challenge.gateSlots (cachedSubQuad xs ys cs cin q r t u)=Challenge.gateSlots (cachedSubTriple xs ys cs cin q r t)+1:=by
 rw[cachedSubTriple_split8 xs ys cs cin q r t hx hc hy]
 simp[cachedSubQuad,insertCopy,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,toffoliCount,measurementCount,Challenge.gateSlots,Challenge.instructionSlots] <;> omega

theorem consumedAddQuad_counts (src Z ys carry:List Wire) (cin q r t u:Wire)
 (hs:10≤src.length) (hy:ys.length=src.length+5) (hc:8≤carry.length):
 toffoliCount (consumedAddQuad src Z ys carry cin q r t u)+1=toffoliCount (consumedAddTriple src Z ys carry cin q r t) ∧
 measurementCount (consumedAddQuad src Z ys carry cin q r t u)=measurementCount (consumedAddTriple src Z ys carry cin q r t) ∧
 Challenge.gateSlots (consumedAddQuad src Z ys carry cin q r t u)+4=Challenge.gateSlots (consumedAddTriple src Z ys carry cin q r t):=by
 rw[consumedAddTriple_split8 src Z ys carry cin q r t hs hy hc]
 simp[consumedAddQuad,move,eighthMajority,majority,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,toffoliCount,measurementCount,Challenge.gateSlots,Challenge.instructionSlots] <;> omega
#print axioms cachedSubQuad_counts
#print axioms consumedAddQuad_counts
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryConsume
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem consumedAddQuad_frame (src Z ys carry:List Wire) (cin q r t u:Wire)
 (hs:10≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5) (hc:carry.length+1=ys.length)
 (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
 (hcin:s.basis cin=false) (H:Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64)
 (fresh:q∉(src++Z.take 5)++ys++carry) (rfresh:r∉(src++Z.take 5)++ys++carry) (rq:r≠q)
 (tfresh:t∉(src++Z.take 5)++ys++carry) (tq:t≠q) (tr:t≠r)
 (ufresh:u∉carry) (uq:u≠q) (ur:u≠r) (ut:u≠t)
 (off:u∉wires (consumedAddTriple src Z ys carry cin q r t))
 (saved:s.basis q=cacheBit H) (savedR:s.basis r=cacheBit6 H) (savedT:s.basis t=cacheBit7 H) (savedU:s.basis u=cacheBit8 H):
 run (consumedAddQuad src Z ys carry cin q r t u) m s=
 setWire (run (consumedAddTriple src Z ys carry cin q r t) m s) u false:=by
 have enough:8≤carry.length:=by omega
 have xlen:8≤(src++Z.take 5).length:=by simp only[List.length_append];omega
 have nd:=eighth_majority_nd (src++Z.take 5) ys carry cin xlen (by omega) enough hn
 have ne:u≠carry.getD 7 0:=by intro e;exact ufresh (e.symm ▸ DiagSq.getD_in carry 7 (by omega))
 have off':=off
 rw[consumedAddTriple_split8 src Z ys carry cin q r t hs hy enough]at off'
 simp only[wires_append,Finset.mem_union,not_or]at off'
 have ready:=source_fourth_consume_ready src Z ys carry cin q r t u hs hzl hy hc hn s hz hclean hcin H hsrc hys fresh rfresh rq tfresh tq tr ufresh uq ur ut saved savedR savedT savedU
 let pre:=(((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0))++move t (carry.getD 6 0))
 have preM:measurementCount pre=0:=by
  have h:=(knownPrefix_counts (src.getD 0 0) (mappedRead (src++Z.take 5) false) (desired src) ys carry cin).2
  change measurementCount (addPre src Z ys carry cin)=0 at h
  simp only[pre,measurementCount_append,h,show measurementCount (move q (carry.getD 4 0))=0 from rfl,
   show measurementCount (move r (carry.getD 5 0))=0 from rfl,show measurementCount (move t (carry.getD 6 0))=0 from rfl,Nat.zero_add]
 have result:=secondConsume_correct pre (addPost4 src Z ys carry cin)
  ((src++Z.take 5).getD 7 0) (ys.getD 7 0) (carry.getD 6 0) (carry.getD 7 0) u
  nd ne off'.2 s m (by simpa only[preM,List.take_zero]using ready.1)
  (by simpa only[preM,List.take_zero]using ready.2)
 have split:=consumedAddTriple_split8 src Z ys carry cin q r t hs hy enough
 rw[eighthMajority]at split
 rw[←split]at result
 simpa only[consumedAddQuad,pre]using result
#print axioms consumedAddQuad_frame
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryBuild
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold Arithmetic.CuccaroStreamedSquareWideLayout
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def buildQuad (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire):Program:=
 buildPre acc Z bank cin src++cachedSubQuad (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r p u++buildPost acc Z bank cin src
theorem buildQuad_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p u : Wire)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (hq:s.basis q=false) (hr:s.basis r=false)
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (NarrowAcc.build8 acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (rq:r≠q)
    (hp:s.basis p=false) (freshP:p∉cin::(src++acc++Z++bank))
    (offP:p∉wires (buildDual acc Z bank cin src q r))
    (hu:s.basis u=false) (freshU:u∉cin::(src++acc++Z++bank))
    (offU:u∉wires (buildTriple acc Z bank cin src q r p)) :
    run (buildQuad acc Z bank cin src q r p u) m s=
      setWire (run (buildTriple acc Z bank cin src q r p) m s) u (cacheBit8 (regValue src s.basis)) := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (buildPre acc Z bank cin src) (m.take (measurementCount (buildPre acc Z bank cin src))) s
  have preFrame:=buildPre_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s
    (m.take (measurementCount (buildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have len:(acc.take 139).length=139 := by simp [hacc]
  have lens:=Acc.fits_lengths (acc.take 139) Z bank cin 139 f len fit.toFitsLen
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have window:(Acc.ty (acc.take 139) f).length=133 := by simpa [f,Acc.earlyTerm] using lens.2.2
  have xv:regValue (Acc.tx Z 139 f) t.basis=H := by
    have zero:regValue (Z.take (139-f.shift-f.src.length)) t.basis=0 := (regValue_zero _ _).mpr (by
      intro w hw
      exact (same w (Or.inl (by simp [List.mem_of_mem_take hw]))).trans (hz w (List.mem_of_mem_take hw)))
    have srcv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
    change regValue (src++Z.take (139-6-src.length)) t.basis=H
    change regValue (Z.take (139-6-src.length)) t.basis=0 at zero
    rw [regValue_append,srcv,zero,Nat.mul_zero,Nat.add_zero]
  have pref:=regValue_take_drop_of_lt acc 139 (1040*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue (Acc.ty (acc.take 139) f) t.basis=1040*H/64 := by
    rw [Acc.ty,regValue_drop_div _ _ (by simp [f,Acc.earlyTerm,len]),pref.1]
    simp [f,Acc.earlyTerm]
  have clean:∀w∈Acc.tc bank 139 f,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=false := (preFrame.2.2 q qacc).trans hq
  have pieces:=off
  rw [build_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=false := (preFrame.2.2 r racc).trans hr
  have piecesR:=offR
  rw [build_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have pacc:p∉acc:=by intro bad;exact freshP (by simp[bad])
  have pt:t.basis p=false:=(preFrame.2.2 p pacc).trans hp
  have piecesP:=offP
  rw[buildDual]at piecesP
  simp only[wires_append,Finset.mem_union,not_or]at piecesP
  have uacc:u∉acc:=by intro bad;exact freshU (by simp[bad])
  have ut:t.basis u=false:=(preFrame.2.2 u uacc).trans hu
  have piecesU:=offU
  rw[buildTriple]at piecesU
  simp only[wires_append,Finset.mem_union,not_or]at piecesU
  have count:=cachedSubQuad_counts (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p u lens.1 lens.2.1 (by omega)
  have changed:=cachedSubQuad_known_frame (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p u
   lens.1 lens.2.1 (by omega) nd t
   ((m.drop (measurementCount (buildPre acc Z bank cin src))).take
    (measurementCount (cachedSubTriple (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p)))
   clean iv pieces.1.2 piecesR.1.2 rq piecesP.1.2 piecesU.1.2 qt rt pt ut H xv yv
  have result:=modify_inside (buildPre acc Z bank cin src)
   (cachedSubTriple (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p)
   (cachedSubQuad (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p u)
   (buildPost acc Z bank cin src) u (cacheBit8 H) count.2.1 piecesU.2 s m changed
  simpa only[buildQuad,buildTriple,f]using result
#print axioms buildQuad_frame
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryUnbuild
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold Arithmetic.CuccaroStreamedSquareWideLayout
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def unbuildQuad (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire):Program:=
 unbuildPre acc Z bank cin src++consumedAddQuad src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p u++unbuildPost acc Z bank cin src
theorem unbuildQuad_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p u : Wire)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=4294968272*regValue src s.basis)
    (saved:s.basis q=cacheBit (regValue src s.basis)) (savedR:s.basis r=cacheBit6 (regValue src s.basis))
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src)) (rq:r≠q)
    (savedP:s.basis p=cacheBit7 (regValue src s.basis)) (freshP:p∉cin::(src++acc++Z++bank))
    (offP:p∉wires (unbuildDual acc Z bank cin src q r)) (pq:p≠q) (pr:p≠r)
    (savedU:s.basis u=cacheBit8 (regValue src s.basis)) (freshU:u∉cin::(src++acc++Z++bank))
    (offU:u∉wires (unbuildTriple acc Z bank cin src q r p)) (uq:u≠q) (ur:u≠r) (up:u≠p) :
    run (unbuildQuad acc Z bank cin src q r p u) m s=
      setWire (run (unbuildTriple acc Z bank cin src q r p) m s) u false := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (unbuildPre acc Z bank cin src) (m.take (measurementCount (unbuildPre acc Z bank cin src))) s
  have preFrame:=unbuildPre_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s
    (m.take (measurementCount (unbuildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have nd0:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd:(cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa only [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd0
  have bankLen:132≤bank.length := by
    have h:=hf6.bankLen
    norm_num [f,Acc.earlyTerm] at h
    omega
  have zlen:5≤Z.length := by
    have h:=hf6.zpad
    norm_num [f,Acc.earlyTerm,hsrc] at h
    omega
  have sv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
  have pref:=regValue_take_drop_of_lt acc 139 (976*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue ((acc.take 139).drop 6) t.basis=976*H/64 := by
    rw [regValue_drop_div _ 6 (by simp [hacc]),pref.1]
    norm_num
  have zt:∀w∈Z,t.basis w=false := by
    intro w hw
    exact (same w (Or.inl (by simp [hw]))).trans (hz w hw)
  have clean:∀w∈bank.take 132,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=cacheBit H := (preFrame.2.2 q qacc).trans saved
  have qbank:q∉bank.take 132 := by intro bad;exact fresh (by simp [List.mem_of_mem_take bad])
  have pieces:=off
  rw [unbuild_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [hacc,hsrc]
  have hc:(bank.take 132).length+1=((acc.take 139).drop 6).length := by simp [hacc,Nat.min_eq_left bankLen]
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=cacheBit6 H := (preFrame.2.2 r racc).trans savedR
  have rbank:r∉bank.take 132 := by intro bad;exact freshR (by simp [List.mem_of_mem_take bad])
  have freshQ:q∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132 := by
    intro bad
    simp only [List.mem_append] at bad
    rcases bad with ((h|h)|h)|h
    · exact fresh (by simp [h])
    · exact fresh (by simp [List.mem_of_mem_take h])
    · exact fresh (by simp [List.mem_of_mem_take (List.mem_of_mem_drop h)])
    · exact fresh (by simp [List.mem_of_mem_take h])
  have piecesR:=offR
  rw [unbuild_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have pacc:p∉acc:=by intro bad;exact freshP (by simp[bad])
  have pt:t.basis p=cacheBit7 H:=(preFrame.2.2 p pacc).trans savedP
  have freshP':p∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132:=by
   intro bad
   simp only[List.mem_append]at bad
   rcases bad with ((h|h)|h)|h
   · exact freshP (by simp[h])
   · exact freshP (by simp[List.mem_of_mem_take h])
   · exact freshP (by simp[List.mem_of_mem_take (List.mem_of_mem_drop h)])
   · exact freshP (by simp[List.mem_of_mem_take h])
  have uacc:u∉acc:=by intro bad;exact freshU (by simp[bad])
  have ut:t.basis u=cacheBit8 H:=(preFrame.2.2 u uacc).trans savedU
  have ubank:u∉bank.take 132:=by intro bad;exact freshU (by simp[List.mem_of_mem_take bad])
  have freshR':r∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132:=by
   intro bad
   simp only[List.mem_append]at bad
   rcases bad with ((h|h)|h)|h
   · exact freshR (by simp[h])
   · exact freshR (by simp[List.mem_of_mem_take h])
   · exact freshR (by simp[List.mem_of_mem_take (List.mem_of_mem_drop h)])
   · exact freshR (by simp[List.mem_of_mem_take h])
  have piecesU:=offU
  rw[unbuildTriple]at piecesU
  simp only[wires_append,Finset.mem_union,not_or]at piecesU
  have count:=consumedAddQuad_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p u
   (by omega) hy (by simp[Nat.min_eq_left bankLen])
  have changed:=consumedAddQuad_frame src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p u
   (by omega) zlen hy hc nd t
   ((m.drop (measurementCount (unbuildPre acc Z bank cin src))).take
    (measurementCount (consumedAddTriple src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p)))
   zt clean iv H sv yv freshQ freshR' rq freshP' pq pr ubank uq ur up piecesU.1.2 qt rt pt ut
  have result:=modify_inside (unbuildPre acc Z bank cin src)
   (consumedAddTriple src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p)
   (consumedAddQuad src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p u) (unbuildPost acc Z bank cin src)
   u false count.2.1 piecesU.2 s m changed
  simpa only[unbuildQuad,unbuildTriple]using result
#print axioms unbuildQuad_frame
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryLoopCounts
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem buildQuad_counts (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire)
 (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length):
 toffoliCount (buildQuad acc Z bank cin src q r p u)=toffoliCount (buildTriple acc Z bank cin src q r p) ∧
 measurementCount (buildQuad acc Z bank cin src q r p u)=measurementCount (buildTriple acc Z bank cin src q r p) ∧
 Challenge.gateSlots (buildQuad acc Z bank cin src q r p u)=Challenge.gateSlots (buildTriple acc Z bank cin src q r p)+1:=by
 have len:=sub6_lengths acc Z bank src ha hs hz hb
 have count:=cachedSubQuad_counts (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r p u
  (by omega) (by omega) (by omega)
 simp only[buildQuad,buildTriple,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

theorem unbuildQuad_counts (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire)
 (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length):
 toffoliCount (unbuildQuad acc Z bank cin src q r p u)+1=toffoliCount (unbuildTriple acc Z bank cin src q r p) ∧
 measurementCount (unbuildQuad acc Z bank cin src q r p u)=measurementCount (unbuildTriple acc Z bank cin src q r p) ∧
 Challenge.gateSlots (unbuildQuad acc Z bank cin src q r p u)+4=Challenge.gateSlots (unbuildTriple acc Z bank cin src q r p):=by
 have hy:((acc.take 139).drop 6).length=src.length+5:=by simp[ha,hs]
 have hc:8≤(bank.take 132).length:=by simp[Nat.min_eq_left hb]
 have count:=consumedAddQuad_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p u (by omega) hy hc
 simp only[unbuildQuad,unbuildTriple,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩
#print axioms buildQuad_counts
#print axioms unbuildQuad_counts
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryLoop
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem cached_wloop_quad_eq (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire) (middle:Program)
 (hacc:acc.length=163) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false) (zeroU:s.basis u=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (freshU:u∉cin::(src++acc++Z++bank)) (uq:u≠q) (ur:u≠r) (up:u≠p)
 (offF:q∉wires (NarrowAcc.build8 acc Z bank cin src)) (offI:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (offIR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (offFU:u∉wires (buildTriple acc Z bank cin src q r p)) (offMU:u∉wires middle)
 (offIU:u∉wires (unbuildTriple acc Z bank cin src q r p))
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (buildTriple acc Z bank cin src q r p) middle s m))
 (savedQ:(middleState (buildTriple acc Z bank cin src q r p) middle s m).basis q=cacheBit (regValue src s.basis))
 (savedR:(middleState (buildTriple acc Z bank cin src q r p) middle s m).basis r=cacheBit6 (regValue src s.basis))
 (savedP:(middleState (buildTriple acc Z bank cin src q r p) middle s m).basis p=cacheBit7 (regValue src s.basis)):
 run (buildQuad acc Z bank cin src q r p u++middle++unbuildQuad acc Z bank cin src q r p u) m s=
 run (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) m s:=by
 let H:=regValue src s.basis
 have hf6:=hf _ (NarrowAcc.terms_mem src).2.2.1
 have zl:5≤Z.length:=by have h:=hf6.zpad;norm_num[Acc.earlyTerm,hsrc]at h;omega
 have bl:132≤bank.length:=by have h:=hf6.bankLen;norm_num[Acc.earlyTerm]at h;omega
 have tc:=buildQuad_counts acc Z bank cin src q r p u hacc hsrc zl bl
 let t3:=middleState (buildTriple acc Z bank cin src q r p) middle s m
 let t4:=setWire t3 u (cacheBit8 H)
 have ready4:WReady acc Z bank cin src H t4:=WReady.setWire acc Z bank cin src H t3 u (cacheBit8 H) freshU good
 have saved1:t4.basis q=cacheBit (regValue src t4.basis):=by
  rw[ready4.2.1]
  exact (setWire_basis_outside t3 u q (cacheBit8 H) (Ne.symm uq)).trans savedQ
 have saved2:t4.basis r=cacheBit6 (regValue src t4.basis):=by
  rw[ready4.2.1]
  exact (setWire_basis_outside t3 u r (cacheBit8 H) (Ne.symm ur)).trans savedR
 have saved3:t4.basis p=cacheBit7 (regValue src t4.basis):=by
  rw[ready4.2.1]
  exact (setWire_basis_outside t3 u p (cacheBit8 H) (Ne.symm up)).trans savedP
 have saved4:t4.basis u=cacheBit8 (regValue src t4.basis):=by
  rw[ready4.2.1]
  simp only[t4,setWire,writeBit,Function.update_self]
 have av:regValue acc t4.basis=4294968272*regValue src t4.basis:=by rw[ready4.2.1];exact ready4.1
 have forward:=buildQuad_frame acc Z bank cin src q r p u hacc hsrc hf s
  (m.take (measurementCount (buildTriple acc Z bank cin src q r p))) hz hb hi ha zero zeroR fresh offF freshR offFR rq zeroP freshP offFP zeroU freshU offFU
 have inverse:=unbuildQuad_frame acc Z bank cin src q r p u hacc hsrc hf t4
  (m.drop (measurementCount (buildTriple acc Z bank cin src q r p)+measurementCount middle))
  ready4.2.2.1 ready4.2.2.2.1 ready4.2.2.2.2 av saved1 saved2 fresh offI freshR offIR rq saved3 freshP offIP pq pr saved4 freshU offIU uq ur up
 exact cached_pair_eq (buildTriple acc Z bank cin src q r p) (buildQuad acc Z bank cin src q r p u) middle
  (unbuildTriple acc Z bank cin src q r p) (unbuildQuad acc Z bank cin src q r p u) u (cacheBit8 H)
  tc.2.1 offFU offMU offIU s m zeroU forward inverse
#print axioms cached_wloop_quad_eq
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryPrimitiveSupport
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem cachedSubQuad_used (xs ys cs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:10≤ys.length):
 cs.getD 7 0∈wires (cachedSubTriple xs ys cs cin q r t):=by
 rw[cachedSubTriple_split8 xs ys cs cin q r t hx hc hy]
 simp[eighthMajority,majority,wires_append,wires,Instr.wires]

theorem cachedSubQuad_support (xs ys cs:List Wire) (cin q r t u:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:10≤ys.length):
 wires (cachedSubQuad xs ys cs cin q r t u)⊆insert u (wires (cachedSubTriple xs ys cs cin q r t)):=by
 have split:=cachedSubTriple_split8 xs ys cs cin q r t hx hc hy
 have used:=cachedSubQuad_used xs ys cs cin q r t hx hc hy
 rw[split]at used ⊢
 exact insertCopy_support _ _ _ _ used

theorem cachedSubQuad_physical (xs ys cs:List Wire) (cin q r t u:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:10≤ys.length)
 (off:u∉wires (cachedSubTriple xs ys cs cin q r t)) (physical:GatePhysical (cachedSubTriple xs ys cs cin q r t)):
 GatePhysical (cachedSubQuad xs ys cs cin q r t u):=by
 have split:=cachedSubTriple_split8 xs ys cs cin q r t hx hc hy
 have used:=cachedSubQuad_used xs ys cs cin q r t hx hc hy
 have ne:cs.getD 7 0≠u:=by intro e;exact off (e ▸ used)
 rw[split,gatePhysical_append]at physical
 exact insertCopy_physical _ _ _ _ physical.1 physical.2 ne

theorem consumedAddQuad_support (src Z ys carry:List Wire) (cin q r t u:Wire)
 (hs:10≤src.length) (hy:ys.length=src.length+5) (hc:8≤carry.length):
 wires (consumedAddQuad src Z ys carry cin q r t u)⊆insert u (wires (consumedAddTriple src Z ys carry cin q r t)):=by
 let pre:=(((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0))++move t (carry.getD 6 0))
 have split:=consumedAddTriple_split8 src Z ys carry cin q r t hs hy hc
 rw[split]
 change wires ((pre++move u (carry.getD 7 0))++addPost4 src Z ys carry cin)⊆insert u (wires ((pre++eighthMajority (src++Z.take 5) ys carry)++addPost4 src Z ys carry cin))
 intro w hw
 by_cases eq:w=u
 · exact Finset.mem_insert.mpr (Or.inl eq)
 apply Finset.mem_insert_of_mem
 simp only[wires_append,Finset.mem_union]at hw ⊢
 rcases hw with (hw|hw)|hw
 · exact Or.inl (Or.inl hw)
 · have h:=Finset.mem_insert.mp (consume_support ((src++Z.take 5).getD 7 0) (ys.getD 7 0) (carry.getD 6 0) (carry.getD 7 0) u hw)
   exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
 · exact Or.inr hw

theorem consumedAddQuad_physical (src Z ys carry:List Wire) (cin q r t u:Wire)
 (hs:10≤src.length) (hy:ys.length=src.length+5) (hc:8≤carry.length)
 (off:u∉wires (consumedAddTriple src Z ys carry cin q r t)) (physical:GatePhysical (consumedAddTriple src Z ys carry cin q r t)):
 GatePhysical (consumedAddQuad src Z ys carry cin q r t u):=by
 have split:=consumedAddTriple_split8 src Z ys carry cin q r t hs hy hc
 have used:carry.getD 7 0∈wires (consumedAddTriple src Z ys carry cin q r t):=by
  rw[split]
  simp[eighthMajority,majority,wires_append,wires,Instr.wires]
 have ne:u≠carry.getD 7 0:=by intro e;exact off (e.symm ▸ used)
 rw[split,gatePhysical_append,gatePhysical_append]at physical
 rw[consumedAddQuad,gatePhysical_append,gatePhysical_append]
 refine ⟨⟨physical.1.1,?_⟩,physical.2⟩
 simp only[move,GatePhysical,List.mem_cons,List.not_mem_nil,or_false]
 intro i hi
 rcases hi with rfl|rfl
 · exact ne
 · exact Ne.symm ne
#print axioms cachedSubQuad_support
#print axioms cachedSubQuad_physical
#print axioms consumedAddQuad_support
#print axioms consumedAddQuad_physical
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryLoopSupport
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem buildQuad_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p u : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    wires (buildQuad acc Z bank cin src q r p u)⊆insert u (wires (buildTriple acc Z bank cin src q r p)) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have sub:=cachedSubQuad_support (Acc.tx Z 139 (Acc.earlyTerm src true 6))
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r p u
    (by omega) (by omega) (by omega)
  intro w hw
  by_cases eq:w=u
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [buildQuad,wires_append,Finset.mem_union] at hw
  simp only [buildTriple,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

theorem unbuildQuad_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p u : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length) :
    wires (unbuildQuad acc Z bank cin src q r p u)⊆insert u (wires (unbuildTriple acc Z bank cin src q r p)) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:8≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have sub:=consumedAddQuad_support src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p u (by omega) hy hc
  intro w hw
  by_cases eq:w=u
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [unbuildQuad,wires_append,Finset.mem_union] at hw
  simp only [unbuildTriple,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

theorem buildQuad_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p u : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length)
    (off:u∉wires (buildTriple acc Z bank cin src q r p)) (physical:GatePhysical (buildTriple acc Z bank cin src q r p)) :
    GatePhysical (buildQuad acc Z bank cin src q r p u) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  rw [buildTriple,gatePhysical_append,gatePhysical_append] at physical
  have midOff:u∉wires (cachedSubTriple (Acc.tx Z 139 (Acc.earlyTerm src true 6))
      (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r p) := by
    intro h;apply off
    simp only [buildTriple,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=cachedSubQuad_physical _ _ _ cin q r p u (by omega) (by omega) (by omega) midOff physical.1.2
  simp only [buildQuad,gatePhysical_append]
  exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

theorem unbuildQuad_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p u : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length)
    (off:u∉wires (unbuildTriple acc Z bank cin src q r p)) (physical:GatePhysical (unbuildTriple acc Z bank cin src q r p)) :
    GatePhysical (unbuildQuad acc Z bank cin src q r p u) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:8≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  rw [unbuildTriple,gatePhysical_append,gatePhysical_append] at physical
  have midOff:u∉wires (consumedAddTriple src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p) := by
    intro h;apply off
    simp only [unbuildTriple,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=consumedAddQuad_physical src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p u (by omega) hy hc midOff physical.1.2
  simp only [unbuildQuad,gatePhysical_append]
  exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

#print axioms buildQuad_support
#print axioms unbuildQuad_support
#print axioms buildQuad_physical
#print axioms unbuildQuad_physical
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryTripleMiddle
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem triple_middle_ready (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire) (middle:Program)
 (hacc:acc.length=163) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (offF:q∉wires (NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
 (offI:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (offMR:r∉wires middle)
 (offIR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offMP:p∉wires middle)
 (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (NarrowAcc.build8 acc Z bank cin src) middle s m)):
 let t:=middleState (buildTriple acc Z bank cin src q r p) middle s m
 WReady acc Z bank cin src (regValue src s.basis) t ∧
 t.basis q=cacheBit (regValue src s.basis) ∧ t.basis r=cacheBit6 (regValue src s.basis) ∧ t.basis p=cacheBit7 (regValue src s.basis):=by
 let H:=regValue src s.basis
 have hf6:=hf _ (NarrowAcc.terms_mem src).2.2.1
 have zl:5≤Z.length:=by have h:=hf6.zpad;norm_num[Acc.earlyTerm,hsrc]at h;omega
 have bl:132≤bank.length:=by have h:=hf6.bankLen;norm_num[Acc.earlyTerm]at h;omega
 have bc:=buildCached_counts acc Z bank cin src q hacc hsrc zl bl
 have dc:=buildDual_counts acc Z bank cin src q r hacc hsrc zl bl
 have tc:=buildTriple_counts acc Z bank cin src q r p hacc hsrc zl bl
 let u:=middleState (NarrowAcc.build8 acc Z bank cin src) middle s m
 let t1:=middleState (buildCached acc Z bank cin src q) middle s m
 let t2:=middleState (buildDual acc Z bank cin src q r) middle s m
 let t3:=middleState (buildTriple acc Z bank cin src q r p) middle s m
 have eq1:t1=setWire u q (cacheBit H):=
  middleState_frame_copy _ _ middle q (cacheBit H) bc.2.1 offM s m
   (fun tape=>buildCached_frame acc Z bank cin src q hacc hsrc hf s tape hz hb hi ha zero fresh offF)
 have eq2:t2=setWire t1 r (cacheBit6 H):=
  middleState_frame_copy _ _ middle r (cacheBit6 H) dc.2.1 offMR s m
   (fun tape=>buildDual_frame acc Z bank cin src q r hacc hsrc hf s tape hz hb hi ha zero zeroR fresh offF freshR offFR rq)
 have eq3:t3=setWire t2 p (cacheBit7 H):=
  middleState_frame_copy _ _ middle p (cacheBit7 H) tc.2.1 offMP s m
   (fun tape=>buildTriple_frame acc Z bank cin src q r p hacc hsrc hf s tape hz hb hi ha zero zeroR fresh offF freshR offFR rq zeroP freshP offFP)
 have ready1:WReady acc Z bank cin src H t1:=by
  rw[eq1]
  exact WReady.setWire acc Z bank cin src H u q (cacheBit H) fresh good
 have ready2:WReady acc Z bank cin src H t2:=by
  rw[eq2]
  exact WReady.setWire acc Z bank cin src H t1 r (cacheBit6 H) freshR ready1
 have ready3:WReady acc Z bank cin src H t3:=by
  rw[eq3]
  exact WReady.setWire acc Z bank cin src H t2 p (cacheBit7 H) freshP ready2
 have atq:t2.basis q=cacheBit H:=by
  rw[eq2]
  rw[setWire_basis_outside t1 r q (cacheBit6 H) (Ne.symm rq)]
  rw[eq1]
  simp only[setWire,writeBit,Function.update_self]
 have atr:t2.basis r=cacheBit6 H:=by
  rw[eq2]
  simp only[setWire,writeBit,Function.update_self]
 have saved1:t3.basis q=cacheBit (regValue src t3.basis):=by
  rw[ready3.2.1]
  rw[eq3]
  exact (setWire_basis_outside t2 p q (cacheBit7 H) (Ne.symm pq)).trans atq
 have saved2:t3.basis r=cacheBit6 (regValue src t3.basis):=by
  rw[ready3.2.1]
  rw[eq3]
  exact (setWire_basis_outside t2 p r (cacheBit7 H) (Ne.symm pr)).trans atr
 have saved3:t3.basis p=cacheBit7 (regValue src t3.basis):=by
  rw[ready3.2.1]
  rw[eq3]
  simp only[setWire,writeBit,Function.update_self]
 exact ⟨ready3,by simpa only[ready3.2.1]using saved1,by simpa only[ready3.2.1]using saved2,by simpa only[ready3.2.1]using saved3⟩
#print axioms triple_middle_ready
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryCompiledLoop
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem compiled_wloop_quad_eq (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire) (middle newMiddle:Program)
 (hacc:acc.length=163) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (offF:q∉wires (NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
 (offI:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (offMR:r∉wires middle)
 (offIR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offMP:p∉wires middle)
 (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (zeroU:s.basis u=false) (freshU:u∉cin::(src++acc++Z++bank)) (uq:u≠q) (ur:u≠r) (up:u≠p)
 (offFU:u∉wires (buildTriple acc Z bank cin src q r p))
 (offIU:u∉wires (unbuildTriple acc Z bank cin src q r p))
 (cert:ManyRewrites [u] middle newMiddle)
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (NarrowAcc.build8 acc Z bank cin src) middle s m)):
 run (buildQuad acc Z bank cin src q r p u++newMiddle++unbuildQuad acc Z bank cin src q r p u) m s=
 run (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) m s:=by
 have ready:=triple_middle_ready acc Z bank cin src q r p middle hacc hsrc hf s m hz hb hi ha zero zeroR zeroP
  fresh freshR rq freshP pq pr offF offM offI offFR offMR offIR offFP offMP offIP good
 have middleEq:=cert.middle_eq [u] middle newMiddle (buildTriple acc Z bank cin src q r p) s m
  (by intro w hw;simp only[List.mem_singleton] at hw;subst w;exact zeroU) (by intro w hw;simp only[List.mem_singleton] at hw;subst w;exact offFU)
 rw[←middleEq]at ready
 have newOff:u∉wires newMiddle:=cert.support [u] middle newMiddle |>.2 u (by simp)
 have eq:=cached_wloop_quad_eq acc Z bank cin src q r p u newMiddle hacc hsrc hf s m hz hb hi ha zero zeroR zeroP zeroU
  fresh freshR rq freshP pq pr freshU uq ur up offF offI offFR offIR offFP offIP offFU newOff offIU
  ready.1 ready.2.1 ready.2.2.1 ready.2.2.2
 have replaced:=cert.surround_eq [u] middle newMiddle (buildTriple acc Z bank cin src q r p) (unbuildTriple acc Z bank cin src q r p) s m
  (by intro w hw;simp only[List.mem_singleton] at hw;subst w;exact zeroU) (by intro w hw;simp only[List.mem_singleton] at hw;subst w;exact offFU)
 exact eq.trans replaced
#print axioms compiled_wloop_quad_eq
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryCompiledResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop ZeroReadDevelop
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem compiled_counts (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire) (middle newMiddle:Program)
 (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length)
 (cert:ManyRewrites [u] middle newMiddle):
 toffoliCount (buildQuad acc Z bank cin src q r p u++newMiddle++unbuildQuad acc Z bank cin src q r p u)+1≤
 toffoliCount (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) ∧
 measurementCount (buildQuad acc Z bank cin src q r p u++newMiddle++unbuildQuad acc Z bank cin src q r p u)=
 measurementCount (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p):=by
 have b:=buildQuad_counts acc Z bank cin src q r p u ha hs hz hb
 have i:=unbuildQuad_counts acc Z bank cin src q r p u ha hs hb
 have t:=cert.toffoli [u] middle newMiddle
 have m:=cert.measurements [u] middle newMiddle
 simp only[toffoliCount_append,measurementCount_append]
 exact ⟨by omega,by omega⟩

theorem compiled_support (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire) (middle newMiddle:Program)
 (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length)
 (cert:ManyRewrites [u] middle newMiddle):
 wires (buildQuad acc Z bank cin src q r p u++newMiddle++unbuildQuad acc Z bank cin src q r p u)⊆
 insert u (wires (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p)):=by
 have b:=buildQuad_support acc Z bank cin src q r p u ha hs hz hb
 have i:=unbuildQuad_support acc Z bank cin src q r p u ha hs hb
 have mid:=(cert.support [u] middle newMiddle).1
 intro w hw
 simp only[wires_append,Finset.mem_union]at hw ⊢
 rcases hw with (hw|hw)|hw
 · have h:=Finset.mem_insert.mp (b hw)
   rcases h with rfl|h
   · simp
   · apply Finset.mem_insert_of_mem;simp only[Finset.mem_union];exact Or.inl (Or.inl h)
 · apply Finset.mem_insert_of_mem;simp only[Finset.mem_union];exact Or.inl (Or.inr (mid hw))
 · have h:=Finset.mem_insert.mp (i hw)
   rcases h with rfl|h
   · simp
   · apply Finset.mem_insert_of_mem;simp only[Finset.mem_union];exact Or.inr h

theorem compiled_physical (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire) (middle newMiddle:Program)
 (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length)
 (cert:ManyRewrites [u] middle newMiddle)
 (offF:u∉wires (buildTriple acc Z bank cin src q r p)) (offI:u∉wires (unbuildTriple acc Z bank cin src q r p))
 (physical:GatePhysical (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p)):
 GatePhysical (buildQuad acc Z bank cin src q r p u++newMiddle++unbuildQuad acc Z bank cin src q r p u):=by
 rw[gatePhysical_append,gatePhysical_append]at physical ⊢
 exact ⟨⟨buildQuad_physical acc Z bank cin src q r p u ha hs hz hb offF physical.1.1,
 cert.physical [u] middle newMiddle physical.1.2⟩,
 unbuildQuad_physical acc Z bank cin src q r p u ha hs hb offI physical.2⟩
#print axioms compiled_counts
#print axioms compiled_support
#print axioms compiled_physical
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryFresh
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] ECDSAAdd.wires

theorem fresh_off_triple (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire)
 (ha:acc.length=163) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (fresh:u∉cin::(src++acc++Z++bank)) (uq:u≠q) (ur:u≠r) (up:u≠p):
 u∉wires (buildTriple acc Z bank cin src q r p) ∧ u∉wires (unbuildTriple acc Z bank cin src q r p):=by
 have hf6:=hf _ (NarrowAcc.terms_mem src).2.2.1
 have zl:5≤Z.length:=by have h:=hf6.zpad;norm_num[Acc.earlyTerm,hs]at h;omega
 have bl:132≤bank.length:=by have h:=hf6.bankLen;norm_num[Acc.earlyTerm]at h;omega
 have off:=wloop_original_off acc Z bank cin src u ha hs hf fresh
 have bc:=buildCached_support acc Z bank cin src q ha hs zl bl
 have uc:=unbuildConsumed_support acc Z bank cin src q ha hs bl
 have bd:=buildDual_support acc Z bank cin src q r ha hs zl bl
 have ud:=unbuildDual_support acc Z bank cin src q r ha hs bl
 have bt:=buildTriple_support acc Z bank cin src q r p ha hs zl bl
 have ut:=unbuildTriple_support acc Z bank cin src q r p ha hs bl
 constructor
 · intro h
   rcases Finset.mem_insert.mp (bt h)with e|h
   · exact up e
   rcases Finset.mem_insert.mp (bd h)with e|h
   · exact ur e
   exact (Finset.mem_insert.mp (bc h)).elim uq off.1
 · intro h
   rcases Finset.mem_insert.mp (ut h)with e|h
   · exact up e
   rcases Finset.mem_insert.mp (ud h)with e|h
   · exact ur e
   exact (Finset.mem_insert.mp (uc h)).elim uq off.2
#print axioms fresh_off_triple
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryAFold
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop ZeroReadDevelop Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def aFoldQuad (L:CuccaroStreamedSquareWideLayout) (g u:Wire) (middle:Program):Program:=
 buildQuad (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L) u++middle++
 unbuildQuad (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L) u
theorem aFoldQuad_eq (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g u : Wire) (newMiddle:Program) (hg:g∉L.wires)
    (work:u∈L.core.work) (freshU:u∉L.core.cin::(hiReg L++accReg L++accZ L++accBank L))
    (uq:u≠L.core.sumCarry) (ur:u≠eV L) (up:u≠spare L)
    (cert:ManyRewrites [u] (aMiddle L g) newMiddle) (base : BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false) (hV:base (eV L)=false) (hP:base (spare L)=false)
    (O : Nat) (hO:O<SquareReduction.p) (s : State) (m : List Bool) (hf:SquareFrame L.core.out base O s.basis) :
    run (aFoldQuad L g u newMiddle) m s=run (aFoldTriple L g) m s := by
  have clean:=L.squareFrame_clean hn base s.basis O hf hc
  have lens:=acc_lengths L hw
  have hz:∀q∈accZ L,s.basis q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact (regValue_zero _ _).mp clean.pad q h
    · exact (regValue_zero _ _).mp clean.work q (List.mem_of_mem_drop h)
  have hb:∀q∈accBank L,s.basis q=false := fun q hq =>
    (regValue_zero _ _).mp clean.pad q (List.mem_of_mem_take hq)
  have ha:regValue (accReg L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp clean.work q (accReg_work L q hq))
  have away:=ParkCarryDevelop.sumCarry_off_regs L hn
  have zero:s.basis L.core.sumCarry=false := (hf.2 _ away.1).trans hsum
  have off:=a_wloop_sumCarry_free L hw hn g hg
  have zeroR:s.basis (eV L)=false :=
    (hf.2 _ (eReg_away L hn _ (eK_mem L hw).2.2.1).1).trans hV
  have freshR:=eV_fresh_domain L hw hn
  have offR:=wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (eV L)
    lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) freshR
  have zeroP:s.basis (spare L)=false:=
   (hf.2 _ (eReg_away L hn _ (spare_mem_eReg L hw)).1).trans hP
  have offP:=spare_off_dual L hw hn
  have zeroU:s.basis u=false:=(regValue_zero _ _).mp clean.work u work
  have offU:=fresh_off_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
   L.core.sumCarry (eV L) (spare L) u lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) freshU uq ur up
  have eq:=compiled_wloop_quad_eq (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
   L.core.sumCarry (eV L) (spare L) u (aMiddle L g) newMiddle
   lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) s m hz hb clean.cin ha zero zeroR zeroP
   (sumCarry_fresh_domain L hn) freshR (eV_ne_sumCarry L hw hn)
   (spare_fresh_domain L hw hn) (spare_ne_sumCarry L hw hn) (spare_ne_eV L hw hn)
   off.1 off.2.1 off.2.2 offR.1 (eV_off_amiddle L hw hn g hg) offR.2
   offP.1 (spare_off_amiddle L hw hn g hg) offP.2 zeroU freshU uq ur up offU.1 offU.2 cert (a_middle_good L hw hn g hg base hc O hO s m hf)
  simpa only[aFoldQuad,aFoldTriple]using eq

#print axioms aFoldQuad_eq
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarrySelector
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def loan (L:CuccaroStreamedSquareWideLayout):Wire:=L.core.work.getD 163 0

def hasWire (p:Program) (q:Wire):Bool:=p.any (fun i=>decide (q∈i.wires))
theorem hasWire_iff (p:Program) (q:Wire):hasWire p q=true ↔ q∈wires p:=by
 induction p with
 | nil=>simp[hasWire,ECDSAAdd.wires]
 | cons i p ih=>simp_all[hasWire,ECDSAAdd.wires]

def LoanReady (L:CuccaroStreamedSquareWideLayout) (g u:Wire):Prop:=
 u∈L.core.work ∧ u∉L.core.cin::(hiReg L++accReg L++accZ L++accBank L) ∧
 u≠L.core.sumCarry ∧ u≠eV L ∧ u≠spare L ∧ hasWire (aBodyTriple L g) u=true
instance (L:CuccaroStreamedSquareWideLayout) (g u:Wire):Decidable (LoanReady L g u):=by
 unfold LoanReady
 infer_instance

def aFoldSelected (L:CuccaroStreamedSquareWideLayout) (g:Wire):Program:=
 let u:=loan L
 if hr:LoanReady L g u then
  match compileManyChunked? [u] (aMiddle L g) with
  | none=>aFoldTriple L g
  | some cm=>aFoldQuad L g u cm.out
 else aFoldTriple L g

theorem aFoldSelected_eq (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
 (hV:base (eV L)=false) (hP:base (spare L)=false) (O:Nat) (hO:O<SquareReduction.p)
 (s:State) (m:List Bool) (hf:SquareFrame L.core.out base O s.basis):
 run (aFoldSelected L g) m s=run (aFoldTriple L g) m s:=by
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:compileManyChunked? [loan L] (aMiddle L g) with
   | none=>rfl
   | some cm=>
    exact aFoldQuad_eq L hw hn g (loan L) cm.out hg hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 cm.proof base hc hsum hV hP O hO s m hf
 · rfl
#print axioms aFoldSelected_eq
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarrySelectedFrame
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem aFoldSelected_frame (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
 (hV:base (eV L)=false) (hP:base (spare L)=false) (O:Nat) (hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (aFoldSelected L g)
  (SquareFrame L.core.out base (((if base g then OwnDiagAll12Square.cFlipK-4294968272*regValue (hiReg L) base
   else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hs
 rw[aFoldSelected_eq L hw hn g hg base hc hsum hV hP O hO s m hs]
 exact aFoldTriple_frame L hw hn g hg base hc hsum hV hP O hO s m hs

#print axioms aFoldSelected_frame
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryABody
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def aBodySelected (L:CuccaroStreamedSquareWideLayout) (c:Wire):Program:=
 measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++aFoldSelected L c)
theorem aBodySelected_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hzero:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (aBodySelected L c) (SquareFrame L.core.out base (resAF (M^2) O (base c))) := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have vZero:base (eV L)=false := eV_zero_of_product_lt L hw base (by rw [hP];exact hb)
  let P := M^2
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have v3 : AccView L base (aAcc L) := views (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frameTq L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have hAeq : Acc.accVal base 0 (aAcc L).spec=4294968272*regValue (hiReg L) base := by
    rw [show (aAcc L).spec=earlyHTerms (L.core.product.drop 128) from rfl,accVal_earlyH]
    congr 1
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb,hP]
  have t3 := aFoldSelected_frame L hw hn c hcw base hc hzero vZero (spare_zero L hw base M hP) O2 hO2
  rw [← hAeq] at t3
  have all := t1.seq (t2.seq t3)
  apply Triple.conseq (fun s h => h) all
  intro s hs
  refine ⟨hs.1.trans ?_,hs.2⟩
  -- value
  let A := Acc.accVal base 0 (aAcc L).spec
  have hA : A<2^163 := Acc.accVal_lt base 163 (aAcc L).spec 0 (by norm_num) v3.specValid
  have hsum := (accA_mixSum L hw base).trans (L.measuredA_sum hw base (M^2) hP hb)
  have n1 : mixNeg (.inl (rot128F L) : MixItem)=false := rfl
  have n2 : mixNeg (.inr (aAcc L) : MixItem)=false := rfl
  have n3 : mixNeg (.inl (negP L) : MixItem)=true := rfl
  have e : accAMix L=[.inl (rot128F L),.inr (aAcc L),.inl (negP L)] := rfl
  rw [e] at hsum
  simp only [mixSignedSum,mixSignedPayload,n1,n2,n3,Bool.false_eq_true,if_false,if_true,mixPayload,add_zero,
    pay1,pay2] at hsum
  change ((((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
    (((A : Nat) : ZMod SquareReduction.p)+-((P : Nat) : ZMod SquareReduction.p)))=
      ((P : Nat) : ZMod SquareReduction.p)*2^128-(P : ZMod SquareReduction.p) at hsum
  have bound : ((if base c then OwnDiagAll12Square.cFlipK-A else A)+(SquareReduction.p-1-O2))%SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ pmod
  apply measuredOrientationCast_injective true _ _ bound (ofCast_lt true _)
  refine Eq.trans ?_ (cast_ofCast true (measuredOrientationCast false O+(((M^2 : Nat) : ZMod SquareReduction.p)*2^128-
    ((M^2 : Nat) : ZMod SquareReduction.p)-(if base c then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)))).symm
  simp only [measuredOrientationCast,if_true,Bool.false_eq_true,if_false]
  have c0 := measuredReflection_zmod O hO
  have c1 := measuredReflection_zmod O1 hO1
  have c2 := measuredReflection_zmod O2 hO2
  have k1 : (O1 : ZMod SquareReduction.p)=(P : ZMod SquareReduction.p)+(-1-(O : ZMod SquareReduction.p)) := by
    simp only [O1,ZMod.natCast_mod,Nat.cast_add,c0]
  have k2 : (O2 : ZMod SquareReduction.p)=(((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
      (-1-(O1 : ZMod SquareReduction.p)) := by
    rw [show O2=((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p from rfl,
      ZMod.natCast_mod,Nat.cast_add,c1]
  rw [ZMod.natCast_mod,Nat.cast_add,c2,k2,k1]
  cases hgv : base c
  · have M0 := hg hgv
    have P0 : P=0 := by show M^2=0; rw [M0]; norm_num
    have R0 : (((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)=0 := by rw [P0]; simp
    rw [R0,P0] at hsum
    simp only [Bool.false_eq_true,if_false]
    rw [R0,P0]
    have hM2 : ((M^2 : Nat) : ZMod SquareReduction.p)=0 := by rw [M0]; simp
    rw [hM2]
    simp at hsum ⊢
    linear_combination -hsum
  · simp only [if_true]
    have hAle : A≤OwnDiagAll12Square.cFlipK := by simp only [OwnDiagAll12Square.cFlipK]; omega
    have hoff : ((OwnDiagAll12Square.cFlipK-A : Nat) : ZMod SquareReduction.p)=(OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p)-
        (A : ZMod SquareReduction.p) := by
      rw [Nat.cast_sub hAle]
    rw [hoff]
    linear_combination hsum

#print axioms aBodySelected_frame
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarrySelectedResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem aFoldQuad_resources (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g u:Wire) (middle:Program)
 (cert:ManyRewrites [u] (aMiddle L g) middle):
 toffoliCount (aFoldQuad L g u middle)+1≤toffoliCount (aFoldTriple L g) ∧
 measurementCount (aFoldQuad L g u middle)=measurementCount (aFoldTriple L g) ∧
 Challenge.gateSlots (aFoldQuad L g u middle)+3≤Challenge.gateSlots (aFoldTriple L g):=by
 have lens:=acc_lengths L hw
 have h:=compiled_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L) u
  (aMiddle L g) middle lens.1 (hiReg_length L hw) (by omega) (by omega) cert
 have b:=buildQuad_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L) u
  lens.1 (hiReg_length L hw) (by omega) (by omega)
 have i:=unbuildQuad_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L) u
  lens.1 (hiReg_length L hw) (by omega)
 have mid:=cert.slots [u] (aMiddle L g) middle
 refine ⟨h.1,h.2,?_⟩
 simp only[aFoldQuad,aFoldTriple,Challenge.gateSlots_append]
 omega

theorem aFoldSelected_resources (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 toffoliCount (aFoldSelected L g)≤toffoliCount (aFoldTriple L g) ∧
 measurementCount (aFoldSelected L g)=measurementCount (aFoldTriple L g) ∧
 Challenge.gateSlots (aFoldSelected L g)≤Challenge.gateSlots (aFoldTriple L g):=by
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:compileManyChunked? [loan L] (aMiddle L g) with
   | none=>exact ⟨le_rfl,rfl,le_rfl⟩
   | some cm=>
    dsimp only
    have h:=aFoldQuad_resources L hw g (loan L) cm.out cm.proof
    exact ⟨by omega,h.2.1,by omega⟩
 · exact ⟨le_rfl,rfl,le_rfl⟩
#print axioms aFoldQuad_resources
#print axioms aFoldSelected_resources
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarrySelectedSupport
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem aFoldSelected_support (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 wires (aFoldSelected L g)⊆insert (loan L) (wires (aFoldTriple L g)):=by
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:compileManyChunked? [loan L] (aMiddle L g) with
   | none=>exact Finset.subset_insert _ _
   | some cm=>
    have lens:=acc_lengths L hw
    exact compiled_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L) (loan L)
     (aMiddle L g) cm.out lens.1 (hiReg_length L hw) (by omega) (by omega) cm.proof
 · exact Finset.subset_insert _ _

theorem aFoldSelected_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) (g:Wire)
 (physical:GatePhysical (aFoldTriple L g)):GatePhysical (aFoldSelected L g):=by
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:compileManyChunked? [loan L] (aMiddle L g) with
   | none=>exact physical
   | some cm=>
    have lens:=acc_lengths L hw
    have off:=fresh_off_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
     L.core.sumCarry (eV L) (spare L) (loan L) lens.1 (hiReg_length L hw) (wTerms_fits L hw hn)
     hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1
    exact compiled_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L) (loan L)
     (aMiddle L g) cm.out lens.1 (hiReg_length L hw) (by omega) (by omega) cm.proof off.1 off.2 physical
 · exact physical

theorem aBodySelected_subset (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 wires (aBodySelected L g)⊆wires (aBodyTriple L g):=by
 have oldfold:wires (aFoldTriple L g)⊆wires (aBodyTriple L g):=by
  intro w hw
  simp only[aBodyTriple,wires_append,Finset.mem_union]
  exact Or.inr (Or.inr hw)
 have fold:wires (aFoldSelected L g)⊆wires (aBodyTriple L g):=by
  by_cases hr:LoanReady L g (loan L)
  · have live:loan L∈wires (aBodyTriple L g):=(hasWire_iff _ _).mp hr.2.2.2.2.2
    intro w hwire
    rcases Finset.mem_insert.mp (aFoldSelected_support L hw g hwire)with e|h
    · exact e ▸ live
    · exact oldfold h
  · simpa only[aFoldSelected,dif_neg hr]using oldfold
 intro w hw
 simp only[aBodySelected,wires_append,Finset.mem_union]at hw
 rcases hw with hw|(hw|hw)
 · simp only[aBodyTriple,wires_append,Finset.mem_union];exact Or.inl hw
 · simp only[aBodyTriple,wires_append,Finset.mem_union];exact Or.inr (Or.inl hw)
 · exact fold hw

theorem aBodySelected_resources (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 toffoliCount (aBodySelected L g)≤2915 ∧ measurementCount (aBodySelected L g)=3077 ∧
 Challenge.gateSlots (aBodySelected L g)≤Challenge.gateSlots (aBodyTriple L g):=by
 have old:=aBodyTriple_counts L hw g
 have h:=aFoldSelected_resources L hw g
 simp only[aBodySelected,aBodyTriple,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]at old ⊢
 exact ⟨by omega,by omega,by omega⟩

theorem aBodySelected_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire)
 (hn:(g::L.wires).Nodup):GatePhysical (aBodySelected L g):=by
 have old:=aBodyTriple_physical L hw g hn
 simp only[aBodyTriple,gatePhysical_append]at old
 have fold:=aFoldSelected_physical L hw (List.nodup_cons.mp hn).2 g old.2.2
 simp only[aBodySelected,gatePhysical_append]
 exact ⟨old.1,old.2.1,fold⟩
#print axioms aBodySelected_subset
#print axioms aBodySelected_resources
#print axioms aBodySelected_physical
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryHosting
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ParkCarryDevelop
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def hostedASelected (L:CuccaroStreamedSquareWideLayout) (rho:Equiv.Perm Wire) (c:Wire):Program:=aBodySelected (hostLayout L rho) c

theorem hostedASelected_eq (L:CuccaroStreamedSquareWideLayout) (rho:Equiv.Perm Wire) (c:Wire)
 (h:rho L.core.sumCarry=L.core.sumCarry):hostedASelected L rho c=aBodySelected L c:=by
 rw[hostedASelected,host_eq L rho h]

theorem hostedASelected_subset (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho:Equiv.Perm Wire) (c:Wire):
 wires (hostedASelected L rho c)⊆wires (hostedATriple L rho c):=
 aBodySelected_subset (hostLayout L rho) (host_widths L hw rho) c

theorem hostedASelected_resources (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho:Equiv.Perm Wire) (c:Wire):
 toffoliCount (hostedASelected L rho c)≤toffoliCount (hostedATriple L rho c) ∧
 measurementCount (hostedASelected L rho c)=measurementCount (hostedATriple L rho c) ∧
 Challenge.gateSlots (hostedASelected L rho c)≤Challenge.gateSlots (hostedATriple L rho c):=by
 have h:=aBodySelected_resources (hostLayout L rho) (host_widths L hw rho) c
 have o:=aBodyTriple_counts (hostLayout L rho) (host_widths L hw rho) c
 exact ⟨by simpa only[hostedASelected,hostedATriple,o.1]using h.1,
  by simp only[hostedASelected,hostedATriple,h.2.1,o.2],h.2.2⟩
#print axioms hostedASelected_subset
#print axioms hostedASelected_resources
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryAliases
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop
set_option linter.unusedSimpArgs false

theorem aBodySelected_refined (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 wires (aBodySelected L c)⊆insert (spare L) (wires (InverseCarryDevelop.aBodyDual L c)):=
 (aBodySelected_subset L hw c).trans (aBodyTriple_refined L hw c)

theorem aBodySelected_support (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) (c:Wire):
 wires (aBodySelected L c)⊆(c::L.wires).toFinset:=
 (aBodySelected_subset L hw c).trans (aBodyTriple_support L hw hn c)
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryOldFoldFast
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop ControlLoan1589BFFold
set_option maxHeartbeats 6000000
attribute [local irreducible] ECDSAAdd.toffoliCount

theorem old_fold_T_fast (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):toffoliCount (aFoldTriple L g)=1383:=by
 have old:=(aBodyTriple_counts L hw g).1
 have q1:=(measuredFoldQ_countsTq L hw (negP L)).1
 have q2:=(measuredFoldQ_countsTq L hw (rot128F L)).1
 simp only[aBodyTriple,toffoliCount_append]at old
 omega
#print axioms old_fold_T_fast
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryClosed
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.toffoliCount

theorem gain_of_success (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire)
 (ready:LoanReady L g (loan L)) (success:(compileManyChunked? [loan L] (aMiddle L g)).isSome=true):
 toffoliCount (aFoldSelected L g)+1≤toffoliCount (aFoldTriple L g):=by
 unfold aFoldSelected
 dsimp only
 rw[dif_pos ready]
 cases he:compileManyChunked? [loan L] (aMiddle L g) with
 | none=>simp[he]at success
 | some cm=>exact (aFoldQuad_resources L hw g (loan L) cm.out cm.proof).1

theorem actual_ready:LoanReady Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic
 (loan Baselines.layout.dialogStreamedSquareWide):=by decide +kernel

theorem actual_compiled:
 (compileManyChunked? [loan Baselines.layout.dialogStreamedSquareWide]
  (aMiddle Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)).isSome=true:=by decide +kernel

theorem actual_fold_gain:
 toffoliCount (aFoldSelected Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)+1≤
 toffoliCount (aFoldTriple Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic):=
 gain_of_success _ (ControlledPointLayout.dialogStreamedSquareWide_widths Baselines.layout Baselines.layout_widths) _ actual_ready actual_compiled
#print axioms actual_ready
#print axioms actual_compiled
#print axioms actual_fold_gain
end FourthASavedCarryDevelop

end -- isolated A work loan component

section
-- FourthACarryClosedBody
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount

theorem body_gain (L:CuccaroStreamedSquareWideLayout) (g:Wire)
 (h:toffoliCount (aFoldSelected L g)+1≤toffoliCount (aFoldTriple L g)):
 toffoliCount (aBodySelected L g)+1≤toffoliCount (aBodyTriple L g):=by
 simp only[aBodySelected,aBodyTriple,toffoliCount_append]
 omega

theorem bound2914 (a b:Nat) (h:a+1≤b) (hb:b=2915):a≤2914:=by omega

theorem actual_body_T_le:
 toffoliCount (aBodySelected Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)≤2914:=
 bound2914 _ _ (body_gain _ _ actual_fold_gain)
  (aBodyTriple_counts _ (ControlledPointLayout.dialogStreamedSquareWide_widths Baselines.layout Baselines.layout_widths) _).1
#print axioms actual_body_T_le
end FourthASavedCarryDevelop

end -- isolated A work loan component

