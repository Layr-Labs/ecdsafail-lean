import ECDSAAdd.Submission.Entrant.ParkAWorkLoan

set_option Elab.async false

/-! One-pass zero-read rewriting for a whole set of loan wires.

`ZeroReadDevelop` (ParkAWorkLoan) frees one zero wire per pass over the program. This file frees a
list `Q` of zero wires in a single pass: reads of any wire of `Q` are erased, and a majority whose
second input is in `Q` becomes one Toffoli (itself erased when one of its controls is in `Q`). -/

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroSetDevelop
open ZeroReadDevelop
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def keepS (Q:List Wire):Correction→Bool
 | .Z t=>!decide (t∈Q)
 | .CZ a b=>!decide (a∈Q) && !decide (b∈Q)

def pruneS (Q:List Wire) (cs:List Correction):List Correction:=cs.filter (keepS Q)

theorem pruneS_correct (Q:List Wire) (cs:List Correction) (s:State) (hz:∀q∈Q,s.basis q=false):
 correct (pruneS Q cs) s=correct cs s:=by
 induction cs generalizing s with
 | nil=>rfl
 | cons c cs ih=>
  cases c with
  | Z t=>
   by_cases h:t∈Q
   · have z:=hz t h
     simpa[pruneS,keepS,correct,h,z]using ih s hz
   · simpa[pruneS,keepS,correct,h]using ih ⟨s.phase ^^ s.basis t,s.basis⟩ hz
  | CZ a b=>
   by_cases ha:a∈Q
   · have z:=hz a ha
     simpa[pruneS,keepS,correct,ha,z]using ih s hz
   by_cases hb:b∈Q
   · have z:=hz b hb
     simpa[pruneS,keepS,correct,ha,hb,z]using ih s hz
   · simpa[pruneS,keepS,correct,ha,hb]using ih ⟨s.phase ^^ (s.basis a && s.basis b),s.basis⟩ hz

def eraseS (Q:List Wire):Instr→Program
 | .X t=>[.X t]
 | .CX a t=>if a∈Q then [] else [.CX a t]
 | .CCX a b t=>if a∈Q ∨ b∈Q then [] else [.CCX a b t]
 | .measureX t c0 c1=>[.measureX t (pruneS Q c0) (pruneS Q c1)]

theorem eraseS_M (Q:List Wire) (i:Instr):measurementCount (eraseS Q i)=measurementCount [i]:=by
 cases i <;> simp[eraseS,measurementCount]
 all_goals split <;> rfl

theorem eraseS_run (Q:List Wire) (i:Instr) (s:State) (m:List Bool)
 (hz:∀q∈Q,s.basis q=false) (ht:targetOf i∉Q):
 run (eraseS Q i) m s=run [i] m s:=by
 cases i with
 | X t=>rfl
 | CX a t=>
  by_cases h:a∈Q
  · have z:=hz a h
    simp[eraseS,run,h,z,writeBit]
  · simp[eraseS,h]
 | CCX a b t=>
  by_cases ha:a∈Q
  · have z:=hz a ha
    simp[eraseS,run,ha,z,writeBit]
  by_cases hb:b∈Q
  · have z:=hz b hb
    simp[eraseS,run,ha,hb,z,writeBit]
  · simp[eraseS,ha,hb]
 | measureX t c0 c1=>
  have hz':∀q∈Q,(writeBit s.basis t false) q=false:=by
   intro q hq
   have ne:t≠q:=by
    intro e
    apply ht
    simpa[targetOf,e]using hq
   simpa[writeBit,Ne.symm ne]using hz q hq
  simp only[eraseS,run,measureAndCorrect]
  split <;> exact pruneS_correct Q _ _ hz'

theorem single_preserves (Q:List Wire) (i:Instr) (s:State) (m:List Bool) (ht:targetOf i∉Q)
 (q:Wire) (hq:q∈Q):(run [i] m s).basis q=s.basis q:=by
 apply single_target_preserves q i s m
 intro e
 apply ht
 rw[e]
 exact hq

inductive SRewrites (Q:List Wire):Program→Program→Prop
 | nil:SRewrites Q [] []
 | normal (i:Instr) (p r:Program) (ht:targetOf i∉Q) (tail:SRewrites Q p r):
   SRewrites Q (i::p) (eraseS Q i++r)
 | zeroMajority (a q c d:Wire) (p r:Program) (hq:q∈Q) (hd:d∉Q) (hn:[a,q,c,d].Nodup)
   (tail:SRewrites Q p r):
   SRewrites Q (majority a q c d++p) (eraseS Q (Instr.CCX a c d)++r)

theorem SRewrites.run_eq (Q:List Wire) (p r:Program) (h:SRewrites Q p r) (s:State) (m:List Bool)
 (hz:∀q∈Q,s.basis q=false):run r m s=run p m s:=by
 induction h generalizing s m with
 | nil=>rfl
 | normal i p r ht tail ih=>
  change run (eraseS Q i++r) m s=run ([i]++p) m s
  rw[run_cat,run_cat,eraseS_M,eraseS_run Q i s m hz ht]
  exact ih _ _ (fun q hq=>(single_preserves Q i s m ht q hq).trans (hz q hq))
 | zeroMajority a q c d p r hq hd hn tail ih=>
  have mm:measurementCount (majority a q c d)=0:=by simp[majority,measurementCount]
  have e0:measurementCount [Instr.CCX a c d]=0:=by simp[measurementCount]
  have td:targetOf (Instr.CCX a c d)∉Q:=hd
  rw[run_cat,run_cat,mm,eraseS_M,e0,eraseS_run Q (Instr.CCX a c d) s m hz td,
   majority_zero_second a q c d hn s m (hz q hq)]
  exact ih _ _ (fun w hw=>(single_preserves Q (Instr.CCX a c d) s m td w hw).trans (hz w hw))

theorem SRewrites.measurements (Q:List Wire) (p r:Program) (h:SRewrites Q p r):
 measurementCount r=measurementCount p:=by
 induction h with
 | nil=>rfl
 | normal i p r ht tail ih=>
  rw[measurementCount_append,eraseS_M,ih]
  cases i <;> simp[measurementCount]
 | zeroMajority a q c d p r hq hd hn tail ih=>
  rw[measurementCount_append,measurementCount_append,eraseS_M,ih]
  simp[majority,measurementCount]

#print axioms SRewrites.run_eq
#print axioms SRewrites.measurements
end ZeroSetDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroSetDevelop
open ZeroReadDevelop
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem eraseS_T (Q:List Wire) (i:Instr):toffoliCount (eraseS Q i)≤toffoliCount [i]:=by
 cases i <;> simp only[eraseS]
 all_goals first | (split <;> simp[toffoliCount]) | simp[toffoliCount]

theorem SRewrites.toffoli (Q:List Wire) (p r:Program) (h:SRewrites Q p r):
 toffoliCount r≤toffoliCount p:=by
 induction h with
 | nil=>rfl
 | normal i p r ht tail ih=>
  have hi:=eraseS_T Q i
  rw[toffoliCount_append]
  have hh:toffoliCount (i::p)=toffoliCount [i]+toffoliCount p:=by cases i <;> simp[toffoliCount]
  rw[hh];omega
 | zeroMajority a q c d p r hq hd hn tail ih=>
  have hi:=eraseS_T Q (Instr.CCX a c d)
  have e1:toffoliCount [Instr.CCX a c d]=1:=by simp[toffoliCount]
  have e2:toffoliCount (majority a q c d)=1:=by simp[majority,toffoliCount]
  rw[toffoliCount_append,toffoliCount_append,e2]
  omega

theorem pruneS_length (Q:List Wire) (cs:List Correction):(pruneS Q cs).length≤cs.length:=
 List.length_filter_le _ _

theorem eraseS_slots (Q:List Wire) (i:Instr):Challenge.gateSlots (eraseS Q i)≤Challenge.gateSlots [i]:=by
 cases i with
 | X t=>rfl
 | CX a t=>simp only[eraseS];split <;> simp[Challenge.gateSlots,Challenge.instructionSlots]
 | CCX a b t=>simp only[eraseS];split <;> simp[Challenge.gateSlots,Challenge.instructionSlots]
 | measureX t c0 c1=>
  have h0:=pruneS_length Q c0
  have h1:=pruneS_length Q c1
  simp only[eraseS,Challenge.gateSlots,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Challenge.instructionSlots]
  omega

theorem SRewrites.slots (Q:List Wire) (p r:Program) (h:SRewrites Q p r):
 Challenge.gateSlots r≤Challenge.gateSlots p:=by
 induction h with
 | nil=>rfl
 | normal i p r ht tail ih=>
  have hi:=eraseS_slots Q i
  rw[Challenge.gateSlots_append]
  have hh:Challenge.gateSlots (i::p)=Challenge.gateSlots [i]+Challenge.gateSlots p:=by simp[Challenge.gateSlots]
  rw[hh];omega
 | zeroMajority a q c d p r hq hd hn tail ih=>
  have hi:=eraseS_slots Q (Instr.CCX a c d)
  have hs:Challenge.gateSlots (majority a q c d)=6:=by simp[majority,Challenge.gateSlots,Challenge.instructionSlots]
  have ht:Challenge.gateSlots [Instr.CCX a c d]=1:=by rfl
  rw[Challenge.gateSlots_append,Challenge.gateSlots_append,hs]
  omega

theorem pruneS_support (Q:List Wire) (cs:List Correction) (x:Wire)
 (hx:x∈correctionWires (pruneS Q cs)):x∉Q ∧ x∈correctionWires cs:=by
 induction cs with
 | nil=>simp[pruneS,correctionWires]at hx
 | cons c cs ih=>
  cases c with
  | Z t=>
   by_cases h:t∈Q
   · have hx':x∈correctionWires (pruneS Q cs):=by simpa[pruneS,keepS,h]using hx
     have r:=ih hx'
     exact ⟨r.1,by simp[correctionWires,r.2]⟩
   · have hx':x=t ∨ x∈correctionWires (pruneS Q cs):=by
      simpa[pruneS,keepS,h,correctionWires]using hx
     rcases hx' with rfl|hx'
     · exact ⟨h,by simp[correctionWires]⟩
     · have r:=ih hx'
       exact ⟨r.1,by simp[correctionWires,r.2]⟩
  | CZ a b=>
   by_cases ha:a∈Q
   · have hx':x∈correctionWires (pruneS Q cs):=by simpa[pruneS,keepS,ha]using hx
     have r:=ih hx'
     exact ⟨r.1,by simp[correctionWires,r.2]⟩
   by_cases hb:b∈Q
   · have hx':x∈correctionWires (pruneS Q cs):=by simpa[pruneS,keepS,ha,hb]using hx
     have r:=ih hx'
     exact ⟨r.1,by simp[correctionWires,r.2]⟩
   · have hx':x=a ∨ x=b ∨ x∈correctionWires (pruneS Q cs):=by
      simpa[pruneS,keepS,ha,hb,correctionWires]using hx
     rcases hx' with rfl|rfl|hx'
     · exact ⟨ha,by simp[correctionWires]⟩
     · exact ⟨hb,by simp[correctionWires]⟩
     · have r:=ih hx'
       exact ⟨r.1,by simp[correctionWires,r.2]⟩

theorem eraseS_support (Q:List Wire) (i:Instr) (ht:targetOf i∉Q) (x:Wire)
 (hx:x∈wires (eraseS Q i)):x∉Q ∧ x∈i.wires:=by
 cases i with
 | X t=>
  have e:x=t:=by simpa[eraseS,wires,Instr.wires]using hx
  subst e
  exact ⟨ht,by simp[Instr.wires]⟩
 | CX a t=>
  by_cases h:a∈Q
  · simp[eraseS,h,wires]at hx
  · have e:x=a ∨ x=t:=by simpa[eraseS,h,wires,Instr.wires]using hx
    rcases e with rfl|rfl
    · exact ⟨h,by simp[Instr.wires]⟩
    · exact ⟨ht,by simp[Instr.wires]⟩
 | CCX a b t=>
  by_cases ha:a∈Q
  · simp[eraseS,ha,wires]at hx
  by_cases hb:b∈Q
  · simp[eraseS,ha,hb,wires]at hx
  · have e:x=a ∨ x=b ∨ x=t:=by simpa[eraseS,ha,hb,wires,Instr.wires]using hx
    rcases e with rfl|rfl|rfl
    · exact ⟨ha,by simp[Instr.wires]⟩
    · exact ⟨hb,by simp[Instr.wires]⟩
    · exact ⟨ht,by simp[Instr.wires]⟩
 | measureX t c0 c1=>
  have e:x=t ∨ x∈correctionWires (pruneS Q c0) ∨ x∈correctionWires (pruneS Q c1):=by
   simpa[eraseS,wires,Instr.wires]using hx
  rcases e with rfl|e|e
  · exact ⟨ht,by simp[Instr.wires]⟩
  · have r:=pruneS_support Q c0 x e
    exact ⟨r.1,by simp[Instr.wires,r.2]⟩
  · have r:=pruneS_support Q c1 x e
    exact ⟨r.1,by simp[Instr.wires,r.2]⟩

theorem SRewrites.support_mem (Q:List Wire) (p r:Program) (h:SRewrites Q p r) (x:Wire)
 (hx:x∈wires r):x∉Q ∧ x∈wires p:=by
 induction h with
 | nil=>simp[wires]at hx
 | normal i p r ht tail ih=>
  rw[wires_append]at hx
  rcases Finset.mem_union.mp hx with hx|hx
  · have e:=eraseS_support Q i ht x hx
    exact ⟨e.1,by simp[wires,e.2]⟩
  · have e:=ih hx
    exact ⟨e.1,by simp[wires,e.2]⟩
 | zeroMajority a q c d p r hq hd hn tail ih=>
  rw[wires_append]at hx
  rcases Finset.mem_union.mp hx with hx|hx
  · have e:=eraseS_support Q (Instr.CCX a c d) hd x hx
    refine ⟨e.1,?_⟩
    rw[wires_append]
    apply Finset.mem_union_left
    have m:x=a ∨ x=c ∨ x=d:=by simpa[Instr.wires]using e.2
    rcases m with rfl|rfl|rfl <;> simp[majority,wires,Instr.wires]
  · have e:=ih hx
    exact ⟨e.1,by rw[wires_append];exact Finset.mem_union_right _ e.2⟩

theorem SRewrites.support (Q:List Wire) (p r:Program) (h:SRewrites Q p r):
 wires r⊆wires p ∧ ∀q∈Q,q∉wires r:=
 ⟨fun x hx=>(h.support_mem Q p r x hx).2,fun q hq bad=>(h.support_mem Q p r q bad).1 hq⟩

#print axioms SRewrites.toffoli
#print axioms SRewrites.slots
#print axioms SRewrites.support
end ZeroSetDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.RecordedQuantum
namespace ZeroSetDevelop
open ZeroReadDevelop
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem eraseS_physical (Q:List Wire) (i:Instr) (h:PhysicalInstr (.gate i)):
 GatePhysical (eraseS Q i):=by
 cases i <;> simp only[eraseS]
 all_goals first
  | (split <;> simp_all[GatePhysical,PhysicalInstr,ProperGate])
  | simp_all[GatePhysical,PhysicalInstr,ProperGate]

theorem SRewrites.physical (Q:List Wire) (p r:Program) (h:SRewrites Q p r)
 (hp:GatePhysical p):GatePhysical r:=by
 induction h with
 | nil=>simp[GatePhysical]
 | normal i p r ht tail ih=>
  have hi:PhysicalInstr (.gate i):=hp i (by simp)
  have ht:GatePhysical p:=fun j hj=>hp j (by simp[hj])
  rw[gatePhysical_append]
  exact ⟨eraseS_physical Q i hi,ih ht⟩
 | zeroMajority a q c d p r hq hd hn tail ih=>
  have ht:GatePhysical p:=fun j hj=>hp j (List.mem_append_right _ hj)
  rw[gatePhysical_append]
  constructor
  · apply eraseS_physical
    simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or]at hn
    simp only[PhysicalInstr,ProperGate]
    exact ⟨hn.1.2.2,hn.2.2.1⟩
  · exact ih ht
#print axioms SRewrites.physical
end ZeroSetDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ZeroSetDevelop
open ZeroReadDevelop InverseCarryDevelop
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem SRewrites.append (Q:List Wire) (p r p' r':Program) (h:SRewrites Q p r) (h':SRewrites Q p' r'):
 SRewrites Q (p++p') (r++r'):=by
 induction h with
 | nil=>simpa using h'
 | normal i p r ht tail ih=>
  simpa only[List.cons_append,List.append_assoc]using SRewrites.normal i (p++p') (r++r') ht ih
 | zeroMajority a q c d p r hq hd hn tail ih=>
  simpa only[List.append_assoc]using SRewrites.zeroMajority a q c d (p++p') (r++r') hq hd hn ih

theorem SRewrites.middle_eq (Q:List Wire) (old new:Program) (h:SRewrites Q old new)
 (pre:Program) (s:State) (m:List Bool) (hz:∀q∈Q,s.basis q=false)
 (off:∀q∈Q,q∉wires pre):middleState pre new s m=middleState pre old s m:=by
 unfold middleState
 rw[h.measurements Q old new]
 apply h.run_eq
 intro q hq
 exact (run_preserves_outside pre _ s q (off q hq)).trans (hz q hq)

theorem SRewrites.surround_eq (Q:List Wire) (old new:Program) (h:SRewrites Q old new)
 (pre post:Program) (s:State) (m:List Bool) (hz:∀q∈Q,s.basis q=false)
 (off:∀q∈Q,q∉wires pre):run ((pre++new)++post) m s=run ((pre++old)++post) m s:=by
 rw[run_cat (pre++new) post,run_cat (pre++old) post]
 rw[measurementCount_append,measurementCount_append,h.measurements Q old new]
 rw[run_cat pre new,run_cat pre old]
 have he:run new (m.drop (measurementCount pre)) (run pre m s)=run old (m.drop (measurementCount pre)) (run pre m s):=by
  apply h.run_eq
  intro q hq
  exact (run_preserves_outside pre m s q (off q hq)).trans (hz q hq)
 rw[he]

structure CheckedS (Q:List Wire) (p:Program) where
 out:Program
 proof:SRewrites Q p out

def normalStepS (Q:List Wire) (i:Instr) (p:Program) (tail:Option (CheckedS Q p)):
 Option (CheckedS Q (i::p)):=
 if ht:targetOf i∉Q then
  tail.map (fun r=>⟨eraseS Q i++r.out,SRewrites.normal i p r.out ht r.proof⟩)
 else none

def compileFuelS (Q:List Wire):Nat→(p:Program)→Option (CheckedS Q p)
 | 0,_=>none
 | _+1,[]=>some ⟨[],SRewrites.nil⟩
 | n+1,.CX a b::.CX c d::.CCX e f g::i3::i4::i5::rest=>
  if hm:(Instr.CX a b::.CX c d::.CCX e f g::i3::i4::i5::rest).take 6=majority a b d g ∧ b∈Q ∧ g∉Q ∧
    [a,b,d,g].Nodup then
   match compileFuelS Q n rest with
   | none=>none
   | some r=>some ⟨eraseS Q (Instr.CCX a d g)++r.out,by
      have hp:(Instr.CX a b::.CX c d::.CCX e f g::i3::i4::i5::rest)=majority a b d g++rest:=by
       calc
        (Instr.CX a b::.CX c d::.CCX e f g::i3::i4::i5::rest)=
          (Instr.CX a b::.CX c d::.CCX e f g::i3::i4::i5::rest).take 6++
          (Instr.CX a b::.CX c d::.CCX e f g::i3::i4::i5::rest).drop 6:=(List.take_append_drop 6 _).symm
        _=majority a b d g++rest:=by rw[hm.1];rfl
      have h:=SRewrites.zeroMajority a b d g rest r.out hm.2.1 hm.2.2.1 hm.2.2.2 r.proof
      simpa only[←hp]using h⟩
  else normalStepS Q (.CX a b) (.CX c d::.CCX e f g::i3::i4::i5::rest)
    (compileFuelS Q n (.CX c d::.CCX e f g::i3::i4::i5::rest))
 | n+1,i::rest=>normalStepS Q i rest (compileFuelS Q n rest)

/-- Compile the first `c` instructions and the rest separately. -/
def splitAt? (Q:List Wire) (p:Program) (c:Nat) (rest:Unit→Option (CheckedS Q (p.drop c))):
 Option (CheckedS Q p):=
 match compileFuelS Q (c+1) (p.take c) with
 | none=>none
 | some a=>
  match rest () with
  | none=>none
  | some b=>some ⟨a.out++b.out,by
     have h:=SRewrites.append Q (p.take c) a.out (p.drop c) b.out a.proof b.proof
     simpa only[List.take_append_drop]using h⟩

/-- Chunked compilation. A chunk boundary must not cut a majority whose second input is a loan,
so each boundary may move back by up to five instructions. -/
def chunkFuelS (Q:List Wire):Nat→(p:Program)→Option (CheckedS Q p)
 | 0,_=>none
 | n+1,p=>
  if p.length≤1024 then compileFuelS Q (p.length+1) p
  else
   (splitAt? Q p 1024 (fun _=>chunkFuelS Q n (p.drop 1024))).orElse fun _=>
   (splitAt? Q p 1023 (fun _=>chunkFuelS Q n (p.drop 1023))).orElse fun _=>
   (splitAt? Q p 1022 (fun _=>chunkFuelS Q n (p.drop 1022))).orElse fun _=>
   (splitAt? Q p 1021 (fun _=>chunkFuelS Q n (p.drop 1021))).orElse fun _=>
   (splitAt? Q p 1020 (fun _=>chunkFuelS Q n (p.drop 1020))).orElse fun _=>
   splitAt? Q p 1019 (fun _=>chunkFuelS Q n (p.drop 1019))

def compileS? (Q:List Wire) (p:Program):Option (CheckedS Q p):=chunkFuelS Q (p.length+1) p

#print axioms SRewrites.append
#print axioms SRewrites.middle_eq
#print axioms SRewrites.surround_eq
end ZeroSetDevelop

end

/-! Fast proof-local constructors of the measured core (from i34-9's ParkAInputFast, without its
literal data): the kernel evaluates these instead of the left-nested originals. -/

section
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant

/-! Proof-local constructors. The selected runtime definitions remain unchanged. -/
namespace ParkAInputFast

/-- Append the caller's suffix while constructing each recursive output only once. -/
def mappedAddTail : List MappedBit → List Wire → List Wire → Wire → Program → Program
  | b::b'::bits, y::y'::ys, c::cs, cin, tail =>
      mappedMajority b y cin c ++
        mappedAddTail (b'::bits) (y'::ys) cs c
          (mappedEraseCarry b y cin c ++ (mappedSum b y cin ++ tail))
  | [b], [y], _, cin, tail => mappedSum b y cin ++ tail
  | _, _, _, _, tail => tail

/-- Exact syntax equality, including every malformed-length fallback. -/
theorem mappedAddTail_eq (bits : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (tail : Program) :
    mappedAddTail bits ys carry cin tail = mappedAdd bits ys carry cin ++ tail := by
  induction bits generalizing ys carry cin tail with
  | nil => cases ys <;> cases carry <;> rfl
  | cons b bits ih =>
      cases bits with
      | nil =>
          cases ys with
          | nil => rfl
          | cons y ys => cases ys <;> rfl
      | cons b' bits =>
          cases ys with
          | nil => rfl
          | cons y ys =>
              cases ys with
              | nil => rfl
              | cons y' ys =>
                  cases carry with
                  | nil => rfl
                  | cons c cs =>
                      change mappedMajority b y cin c ++
                        mappedAddTail (b'::bits) (y'::ys) cs c
                          (mappedEraseCarry b y cin c ++ (mappedSum b y cin ++ tail)) =
                        (((mappedMajority b y cin c ++ mappedAdd (b'::bits) (y'::ys) cs c) ++
                          mappedEraseCarry b y cin c) ++ mappedSum b y cin) ++ tail
                      rw [ih]
                      simp only [List.append_assoc]

def eraseLtTail : List Wire → List Wire → List Wire → Wire → Wire → Program → Program
  | a::a'::as, b::b'::bs, c::cs, cin, target, tail =>
      borrowMajority a b cin c ++
        eraseLtTail (a'::as) (b'::bs) cs c target (eraseBorrow a b cin c ++ tail)
  | [a], [b], _, cin, target, tail => eraseBorrow a b cin target ++ tail
  | _, _, _, _, _, tail => tail

theorem eraseLtTail_eq (xs ys carry : List Wire) (cin target : Wire) (tail : Program) :
    eraseLtTail xs ys carry cin target tail = eraseLtChain xs ys carry cin target ++ tail := by
  induction xs generalizing ys carry cin target tail with
  | nil => cases ys <;> cases carry <;> rfl
  | cons a xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => rfl
          | cons b ys => cases ys <;> rfl
      | cons a' xs =>
          cases ys with
          | nil => rfl
          | cons b ys =>
              cases ys with
              | nil => rfl
              | cons b' ys =>
                  cases carry with
                  | nil => rfl
                  | cons c cs =>
                      change borrowMajority a b cin c ++
                        eraseLtTail (a'::xs) (b'::ys) cs c target (eraseBorrow a b cin c ++ tail) =
                        ((borrowMajority a b cin c ++
                          eraseLtChain (a'::xs) (b'::ys) cs c target) ++ eraseBorrow a b cin c) ++ tail
                      rw [ih]
                      simp only [List.append_assoc]

/-- The original qprogTq syntax with only its three recursive constructors replaced. -/
def qprogFast (K : MeasuredCanonicalModLayout) (p : Nat) : Program :=
  notRegister K.out ++
    mappedAddTail (mappedRead K.src false ++ [({wire := none, flip := false} : MappedBit)])
      K.extended K.carry K.cin [] ++
    [.CX K.high K.flag, .X K.flag] ++
    mappedAddTail (mappedConstant (some K.flag) K.out.length p) K.out
      (K.carry.take (K.out.length - 1)) K.cin [] ++
    [.CX K.flag K.high] ++ [.X K.high, .X K.flag] ++
    eraseLtTail K.out K.src (K.carry.take (K.out.length - 1)) K.cin K.flag []

theorem qprogFast_eq (K : MeasuredCanonicalModLayout) (p : Nat) :
    qprogFast K p = qprogTq K p := by
  simp only [qprogFast, mappedAddTail_eq, eraseLtTail_eq, List.append_nil,
    qprogTq, MeasuredCanonicalModLayout.sum, mappedConstAdd]

def aMiddleFast (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK ++
    (qprogFast L.measuredCore SquareReduction.p ++
      maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK)

theorem aMiddleFast_eq (L : CuccaroStreamedSquareWideLayout) (g : Wire) :
    aMiddleFast L g = InverseCarryDevelop.aMiddle L g := by
  rw [aMiddleFast, qprogFast_eq, InverseCarryDevelop.aMiddle]

end ParkAInputFast

end
