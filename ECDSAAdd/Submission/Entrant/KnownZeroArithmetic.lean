import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Arithmetic.PairFrameUnique
import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical
import ECDSAAdd.Arithmetic.NarrowSignedRecord
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.ExactBorrowErase
import ECDSAAdd.Arithmetic.MeasuredCanonicalMod
import ECDSAAdd.Arithmetic.DisjointPrograms
import ECDSAAdd.Challenge.Contract
import Mathlib.Tactic.FinCases
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareProof
import ECDSAAdd.Submission.Entrant.Fold98

-- Rebalanced closed source chunks; all ordinary declarations and circuit literals retained.
section
open ECDSAAdd
namespace ECDSAAdd.Entrant.A161SupportCover
open Arithmetic FourthASavedCarryDevelop A161FixedFold

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] ECDSAAdd.wires
theorem used11 : (((A161GenericFold.ambient L g hs96).drop 880).take 80).all cover=true := owChunk 880
theorem used12 : (((A161GenericFold.ambient L g hs96).drop 960).take 80).all cover=true := owChunk 960
theorem used13 : (((A161GenericFold.ambient L g hs96).drop 1040).take 80).all cover=true := owChunk 1040
theorem used14 : (((A161GenericFold.ambient L g hs96).drop 1120).take 80).all cover=true := owChunk 1120
theorem used15 : (((A161GenericFold.ambient L g hs96).drop 1200).take 80).all cover=true := owChunk 1200
theorem used16 : (((A161GenericFold.ambient L g hs96).drop 1280).take 80).all cover=true := owChunk 1280
theorem partition : A161GenericFold.ambient L g hs96 = (((A161GenericFold.ambient L g hs96).drop 0).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 80).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 160).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 240).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 320).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 400).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 480).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 560).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 640).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 720).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 800).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 880).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 960).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 1040).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 1120).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 1200).take 80) ++ (((A161GenericFold.ambient L g hs96).drop 1280).take 80) := by decide +kernel
theorem all_cover : (A161GenericFold.ambient L g hs96).all cover=true := by
 rw [partition]
 simp only [List.all_append,used0,used1,used2,used3,used4,used5,used6,used7,used8,used9,used10,used11,used12,used13,used14,used15,used16,Bool.true_and]


end ECDSAAdd.Entrant.A161SupportCover

section
namespace ECDSAAdd.Entrant.A161FineSupport
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 FourthASavedCarryDevelop A161FixedFold

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run List.toFinset

theorem middle_in_body (L:CuccaroStreamedSquareWideLayout) (g:Wire) :
 wires (aMiddle L g)⊆wires (aBodyTriple L g) := by
 intro u hu
 simp only [aBodyTriple,aFoldTriple,wires_append,Finset.mem_union]
 exact Or.inr (Or.inr (Or.inl (Or.inr hu)))

theorem ambient_fine : (A161GenericFold.ambient L g hs96).toFinset⊆insert d (wires (aBodyTriple L g)) := by
 intro u hu
 have hh := List.all_eq_true.mp A161SupportCover.all_cover u (List.mem_toFinset.mp hu)
 simp only [A161SupportCover.cover,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at hh
 rcases hh with (hd|hdomain)|hmid
 · exact Finset.mem_insert.mpr (Or.inl hd)
 · exact Finset.mem_insert_of_mem ((hasWire_iff _ _).mp (FullPadSupport.actual_support_ready u hdomain))
 · have hm : u∈wires ParkAData.p0 := A161SupportCover.witness_support ((A161SupportCover.touched_spec _ _).mp hmid)
   have e := congrArg ECDSAAdd.wires ParkAStagedProof.input_eq
   have hn : u∈wires (aMiddle L g) := e ▸ hm
   exact Finset.mem_insert_of_mem (middle_in_body L g hn)

















end ECDSAAdd.Entrant.A161FineSupport
end

section
namespace ECDSAAdd.Entrant.A161Low4Fine
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ControlLoan1589BFFold

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run List.toFinset

theorem ambient_subset (L:CuccaroStreamedSquareWideLayout) (g d:Wire) (hs:List Wire) :
 (A161Low4GenericFold.ambient L g ((hs++L.core.work.take 4)++[d])).toFinset⊆
 (A161GenericFold.ambient L g (hs++[d])).toFinset := by
 intro u hu
 have low:∀u∈L.core.work.take 4,u∈A161GenericFold.domain L := by
  intro u hu
  have sub:(L.core.work.take 4).Sublist (A161Fold.accReg L) := by
   have h:=List.take_sublist 4 (L.core.work.take 161)
   simpa only [A161Fold.accReg,List.take_take,show min 4 161=4 by decide] using h
  have acc:=sub.subset hu
  simp only [A161GenericFold.domain,List.mem_cons,List.mem_append]
  tauto
 simp only [A161Low4GenericFold.ambient,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hu
 simp only [A161GenericFold.ambient,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
 rcases hu with h|h|h|h|((h|h)|h)
 · tauto
 · tauto
 · tauto
 · tauto
 · tauto
 · tauto
 · have hLow:u∈L.core.work.take 4→u∈A161GenericFold.domain L:=low u
   tauto

open A161Low4FixedFold

theorem ambient_fine : (A161Low4GenericFold.ambient L g hs100).toFinset⊆insert d (wires (aBodyTriple L g)) :=
 (ambient_subset L g d (A161Facts.loans95 L)).trans A161FineSupport.ambient_fine

theorem fold_fine : wires fold100⊆insert d (wires (aBodyTriple L g)) :=
 (A161Low4GenericFold.support L hw hn g hs100 checked.out cert100).trans ambient_fine

theorem body_fine : wires body⊆insert d (wires (aBodyTriple L g)) := by
 intro u hu
 simp only [A161Low4FixedFold.body,wires_append,Finset.mem_union] at hu
 rcases hu with hu|(hu|hu)
 · apply Finset.mem_insert_of_mem
   simp only [aBodyTriple,wires_append,Finset.mem_union]
   exact Or.inl hu
 · apply Finset.mem_insert_of_mem
   simp only [aBodyTriple,wires_append,Finset.mem_union]
   exact Or.inr (Or.inl hu)
 · exact fold_fine hu


end ECDSAAdd.Entrant.A161Low4Fine

end

end
section
















section
open ECDSAAdd

-- Verified component KnownSparseFold
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.KnownSparseFold
open Arithmetic ZeroReadDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

def Zero (K:List Wire)(s:State):Prop:=∀q∈K,s.basis q=false
def remove (K:List Wire)(t:Wire):List Wire:=K.filter (fun q=>decide (q≠t))
def tracked:List Wire:=[4760,4373,4374,4375,4376]
def next (K:List Wire):Instr→List Wire
 | .X t=>remove K t
 | .CX a t=>if a∈K then K else remove K t
 | .CCX a b t=>if a∈K ∨ b∈K then K else remove K t
 | .measureX t _ _=>if t∈tracked then t::remove K t else remove K t

def emit (K:List Wire):Instr→Program
 | .CCX a b t=>if a∈K ∨ b∈K then [] else [.CCX a b t]
 | i=>[i]

theorem zero_remove(K:List Wire)(i:Instr)(s:State)(m:List Bool)(hz:Zero K s):
 Zero (remove K (targetOf i)) (run [i] m s):=by
 intro q hq
 have h:=List.mem_filter.mp hq
 exact (single_target_preserves q i s m (by simpa using Ne.symm (of_decide_eq_true h.2))).trans (hz q h.1)

theorem cx_zero(a t:Wire)(s:State)(m:List Bool)(hz:s.basis a=false):
 run [.CX a t] m s=s:=by simp [run,hz,writeBit]
theorem ccx_zero(a b t:Wire)(s:State)(m:List Bool)(hz:s.basis a=false ∨ s.basis b=false):
 run [.CCX a b t] m s=s:=by rcases hz with hz|hz <;> simp [run,hz,writeBit]

theorem next_zero(K:List Wire)(i:Instr)(s:State)(m:List Bool)(hz:Zero K s):
 Zero (next K i) (run [i] m s):=by
 cases i with
 | X t=>simpa only [next,targetOf] using zero_remove K (.X t) s m hz
 | CX a t=>
  by_cases ha:a∈K
  · simp only [next,if_pos ha]
    rw [cx_zero a t s m (hz a ha)]
    exact hz
  · simpa only [next,if_neg ha] using zero_remove K (.CX a t) s m hz
 | CCX a b t=>
  by_cases h:a∈K ∨ b∈K
  · simp only [next,if_pos h]
    rw [ccx_zero a b t s m (h.elim (fun h=>Or.inl (hz a h)) (fun h=>Or.inr (hz b h)))]
    exact hz
  · simpa only [next,if_neg h] using zero_remove K (.CCX a b t) s m hz
 | measureX t c0 c1=>
  by_cases ht:t∈tracked
  · intro q hq
    simp only [next,if_pos ht,List.mem_cons] at hq
    rcases hq with rfl|hq
    · simp [run,measureAndCorrect,writeBit]
    · exact zero_remove K (.measureX t c0 c1) s m hz q hq
  · simpa only [next,if_neg ht] using zero_remove K (.measureX t c0 c1) s m hz

theorem emit_eq(K:List Wire)(i:Instr)(s:State)(m:List Bool)(hz:Zero K s):
 run (emit K i) m s=run [i] m s:=by
 cases i with
 | X t=>rfl
 | CX a t=>rfl
 | measureX t c0 c1=>rfl
 | CCX a b t=>
  by_cases h:a∈K ∨ b∈K
  · simp only [emit,if_pos h,run]
    exact (ccx_zero a b t s m (h.elim (fun h=>Or.inl (hz a h)) (fun h=>Or.inr (hz b h)))).symm
  · simp only [emit,if_neg h]

theorem majority_zero(K:List Wire)(a b c d:Wire)(nd:[a,b,c,d].Nodup)
 (s:State)(m:List Bool)(hz:Zero K s):Zero (remove K d) (run (majority a b c d) m s):=by
 rw [majority_correct a b c d nd s m]
 intro q hq
 have h:=List.mem_filter.mp hq
 simpa [writeBit,Function.update_apply,of_decide_eq_true h.2,Ne.symm (of_decide_eq_true h.2)] using hz q h.1




end ECDSAAdd.Entrant.KnownSparseFold

end

-- Verified component KnownSparseCert
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.KnownSparseFold
open Arithmetic ZeroReadDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

def removed(K:List Wire):Instr→Nat
 | .CCX a b _=>if a∈K ∨ b∈K then 1 else 0
 | _=>0

theorem emit_counts(K:List Wire)(i:Instr):
 toffoliCount (emit K i)+removed K i=toffoliCount [i] ∧
 measurementCount (emit K i)=measurementCount [i]:=by
 cases i with
 | X t=>exact ⟨rfl,rfl⟩
 | CX a t=>exact ⟨rfl,rfl⟩
 | measureX t c0 c1=>exact ⟨rfl,rfl⟩
 | CCX a b t=>by_cases h:a∈K ∨ b∈K <;> simp [emit,removed,h,toffoliCount,measurementCount]

theorem emit_sublist(K:List Wire)(i:Instr):(emit K i).Sublist [i]:=by
 cases i with
 | X t=>exact List.Sublist.refl _
 | CX a t=>exact List.Sublist.refl _
 | measureX t c0 c1=>exact List.Sublist.refl _
 | CCX a b t=>by_cases h:a∈K ∨ b∈K <;> simp [emit,h]

inductive Cert : List Wire→Program→Program→List Wire→Nat→Prop
 | nil(K):Cert K [] [] K 0
 | normal(K)(i)(p r)(Kf)(n)(tail:Cert (next K i) p r Kf n):
  Cert K (i::p) (emit K i++r) Kf (removed K i+n)
 | maj(K)(a b c d)(p r)(Kf)(n)(nd:[a,b,c,d].Nodup)
  (tail:Cert (remove K d) p r Kf n):
  Cert K (majority a b c d++p) (majority a b c d++r) Kf n

theorem Cert.correct(K:List Wire)(p r:Program)(Kf:List Wire)(n:Nat)(h:Cert K p r Kf n)
 (s:State)(m:List Bool)(hz:Zero K s):run r m s=run p m s ∧ Zero Kf (run p m s):=by
 induction h generalizing s m with
 | nil K=>exact ⟨rfl,hz⟩
 | normal K i p r Kf n tail ih=>
  have z:=next_zero K i s m hz
  have hi:=ih (run [i] m s) (m.drop (measurementCount [i])) z
  have mm:measurementCount (emit K i)=measurementCount [i]:=(emit_counts K i).2
  constructor
  · change run (emit K i++r) m s=run ([i]++p) m s
    rw [run_cat,run_cat,mm,emit_eq K i s m hz]
    exact hi.1
  · change Zero Kf (run ([i]++p) m s)
    rw [run_cat]
    exact hi.2
 | maj K a b c d p r Kf n nd tail ih=>
  have z:=majority_zero K a b c d nd s m hz
  have hi:=ih (run (majority a b c d) m s) (m.drop (measurementCount (majority a b c d))) z
  constructor
  · rw [run_cat,run_cat]
    exact hi.1
  · rw [run_cat]
    exact hi.2

theorem Cert.counts(K:List Wire)(p r:Program)(Kf:List Wire)(n:Nat)(h:Cert K p r Kf n):
 toffoliCount r+n=toffoliCount p ∧ measurementCount r=measurementCount p:=by
 induction h with
 | nil K=>exact ⟨rfl,rfl⟩
 | normal K i p r Kf n tail ih=>
  have e:=emit_counts K i
  change toffoliCount (emit K i++r)+(removed K i+n)=toffoliCount ([i]++p) ∧
   measurementCount (emit K i++r)=measurementCount ([i]++p)
  simp only [toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩
 | maj K a b c d p r Kf n nd tail ih=>
  simp only [toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem Cert.sublist(K:List Wire)(p r:Program)(Kf:List Wire)(n:Nat)(h:Cert K p r Kf n):r.Sublist p:=by
 induction h with
 | nil K=>exact List.Sublist.refl _
 | normal K i p r Kf n tail ih=>exact (emit_sublist K i).append ih
 | maj K a b c d p r Kf n nd tail ih=>exact (List.Sublist.refl _).append ih

theorem Cert.append(K Kmid Kf:List Wire)(p r p' r':Program)(n n':Nat)
 (h:Cert K p r Kmid n)(h':Cert Kmid p' r' Kf n'):
 Cert K (p++p') (r++r') Kf (n+n'):=by
 induction h with
 | nil K=>simpa using h'
 | normal K i p r Kmid n tail ih=>
  simpa only [List.cons_append,List.append_assoc,Nat.add_assoc] using Cert.normal K i (p++p') (r++r') Kf (n+n') (ih h')
 | maj K a b c d p r Kmid n nd tail ih=>
  simpa only [List.append_assoc] using Cert.maj K a b c d (p++p') (r++r') Kf (n+n') nd (ih h')





end ECDSAAdd.Entrant.KnownSparseFold

end

-- Verified component KnownSparseCompiler
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.KnownSparseFold
open Arithmetic ZeroReadDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

structure Checked(K:List Wire)(p:Program) where
 out:Program
 final:List Wire
 saved:Nat
 proof:Cert K p out final saved

def normal(K:List Wire)(i:Instr)(p:Program)(r:Option (Checked (next K i) p)):
 Option (Checked K (i::p)):=r.map (fun v=>⟨emit K i++v.out,v.final,removed K i+v.saved,Cert.normal K i p v.out v.final v.saved v.proof⟩)

def compileFuel(K:List Wire):Nat→(p:Program)→Option (Checked K p)
 | 0,_=>none
 | _+1,[]=>some ⟨[],K,0,Cert.nil K⟩
 | n+1,.CX a b::.CX aa c::.CCX bb cc d::i3::i4::i5::rest=>
  if hm:(Instr.CX a b::.CX aa c::.CCX bb cc d::i3::i4::i5::rest).take 6=majority a b c d ∧ [a,b,c,d].Nodup then
   match compileFuel (remove K d) n rest with
   | none=>none
   | some r=>some ⟨majority a b c d++r.out,r.final,r.saved,by
      have hp:(Instr.CX a b::.CX aa c::.CCX bb cc d::i3::i4::i5::rest)=majority a b c d++rest:=by
       calc
        _=(Instr.CX a b::.CX aa c::.CCX bb cc d::i3::i4::i5::rest).take 6++
          (Instr.CX a b::.CX aa c::.CCX bb cc d::i3::i4::i5::rest).drop 6:=(List.take_append_drop 6 _).symm
        _=majority a b c d++rest:=by rw [hm.1];rfl
      simpa only [←hp] using Cert.maj K a b c d rest r.out r.final r.saved hm.2 r.proof⟩
  else normal K (.CX a b) (.CX aa c::.CCX bb cc d::i3::i4::i5::rest)
   (compileFuel (next K (.CX a b)) n (.CX aa c::.CCX bb cc d::i3::i4::i5::rest))
 | n+1,i::rest=>normal K i rest (compileFuel (next K i) n rest)

def majorityHead:Program→Bool
 | .CX a b::.CX aa c::.CCX bb cc d::i3::i4::i5::_=>
  decide (([Instr.CX a b,.CX aa c,.CCX bb cc d,i3,i4,i5]:Program)=majority a b c d ∧ [a,b,c,d].Nodup)
 | _=>false

def cutAux:Nat→Nat→Program→Nat
 | 0,n,_=>n
 | _+1,n,[]=>n
 | fuel+1,n,p=>
  let step:=if majorityHead p then 6 else 1
  if 1024<n+step then n else cutAux fuel (n+step) (p.drop step)


















end ECDSAAdd.Entrant.KnownSparseFold

end

-- Verified component KnownSparseApply
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.KnownSparseFold
open Arithmetic
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000


























end ECDSAAdd.Entrant.KnownSparseFold

end

-- Verified component KnownSparseResult
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.KnownSparseFold
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

theorem result_isSome {α β:Type}(o:Option α)(f:α→β)(v:β)(h:o.map f=some v):o.isSome=true:=by
 cases o with
 | none=>simp at h
 | some a=>rfl

def fromResult {α β:Type}(o:Option α)(f:α→β)(v:β)(h:o.map f=some v):α:=
 o.get (result_isSome o f v h)

theorem fromResult_eq {α β:Type}(o:Option α)(f:α→β)(v:β)(h:o.map f=some v):
 f (fromResult o f v h)=v:=by
 cases o with
 | none=>simp at h
 | some a=>exact Option.some.inj h

structure ExactChecked(K:List Wire)(p:Program)(Kf:List Wire)(n:Nat) where
 out:Program
 proof:Cert K p out Kf n

def normalize(K:List Wire)(p:Program)(Kf:List Wire)(n:Nat)(o:Option (Checked K p))
 (h:o.map (fun r=>(r.saved,r.final))=some (n,Kf)):ExactChecked K p Kf n:=
 let r:=fromResult o (fun r=>(r.saved,r.final)) (n,Kf) h
 have he:(r.saved,r.final)=(n,Kf):=fromResult_eq o (fun r=>(r.saved,r.final)) (n,Kf) h
 ⟨r.out,by
   have hs:r.saved=n:=congrArg Prod.fst he
   have hf:r.final=Kf:=congrArg Prod.snd he
   simpa only [hs,hf] using r.proof⟩

def ExactChecked.append(K Km Kf:List Wire)(p q:Program)(n m:Nat)
 (a:ExactChecked K p Km n)(b:ExactChecked Km q Kf m):ExactChecked K (p++q) Kf (n+m):=
 ⟨a.out++b.out,Cert.append K Km Kf p a.out q b.out n m a.proof b.proof⟩

end ECDSAAdd.Entrant.KnownSparseFold

end

-- Verified component KnownCMidStaged
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.KnownCMidStaged
open Arithmetic KnownSparseFold
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
def known0:List Wire:=[4373,4374,4375,4376,4760]
def known1:List Wire:=[4760]
def known2:List Wire:=[4760]
def known3:List Wire:=[4373,4374,4375,4376,4760]
def known4:List Wire:=[4373,4374,4375,4376,4760]
def known5:List Wire:=[4373,4374,4375,4376,4760]
def known6:List Wire:=[4373,4374,4375,4376,4760]
def known7:List Wire:=[4373,4374,4375,4376,4760]
def known8:List Wire:=[4373,4374,4375,4376,4760]
def known9:List Wire:=[4373,4374,4375,4376,4760]
def known10:List Wire:=[4373,4374,4375,4376,4760]
def known11:List Wire:=[4373,4374,4375,4376,4760]
def known12:List Wire:=[4373,4374,4375,4376,4760]
def known13:List Wire:=[4373,4374,4375,4376,4760]
def known14:List Wire:=[4373,4374,4375,4376,4760]
def known15:List Wire:=[4373,4374,4375,4376,4760]
def known16:List Wire:=[4373,4374,4375,4376,4760]
def known17:List Wire:=[4373,4374,4375,4376,4760]
def known18:List Wire:=[4373,4374,4375,4376,4760]
def known19:List Wire:=[4373,4374,4375,4376,4760]
def known20:List Wire:=[4760]
def known21:List Wire:=[4760]
def known22:List Wire:=[4760]
def known23:List Wire:=[4760]
def known24:List Wire:=[4760]
def known25:List Wire:=[4760]
def known26:List Wire:=[4760]
def known27:List Wire:=[4760]
def known28:List Wire:=[4760]
def known29:List Wire:=[4760]
def known30:List Wire:=[4760]
def known31:List Wire:=[4760]
def known32:List Wire:=[4760]
def known33:List Wire:=[4760]
def known34:List Wire:=[4760]
def known35:List Wire:=[4760]
def known36:List Wire:=[4760]
def known37:List Wire:=[4760]
def known38:List Wire:=[4373,4374,4375,4376,4760]
def known39:List Wire:=[4373,4374,4375,4376,4760]
def known40:List Wire:=[4373,4374,4375,4376,4760]
def known41:List Wire:=[4373,4374,4375,4376,4760]
def known42:List Wire:=[4373,4374,4375,4376,4760]
def known43:List Wire:=[4373,4374,4375,4376,4760]
def known44:List Wire:=[4373,4374,4375,4376,4760]
def known45:List Wire:=[4373,4374,4375,4376,4760]
def known46:List Wire:=[4373,4374,4375,4376,4760]
def known47:List Wire:=[4373,4374,4375,4376,4760]
def known48:List Wire:=[4373,4374,4375,4376,4760]
def known49:List Wire:=[4373,4374,4375,4376,4760]
def known50:List Wire:=[4373,4374,4375,4376,4760]
def known51:List Wire:=[4373,4374,4375,4376,4760]
def known52:List Wire:=[4373,4374,4375,4376,4760]
def known53:List Wire:=[4373,4374,4375,4376,4760]
def known54:List Wire:=[4373,4374,4375,4376,4760]
def known55:List Wire:=[4373,4374,4375,4376,4760]
def known56:List Wire:=[4373,4374,4375,4376,4760]
def known57:List Wire:=[4376,4760]
def known58:List Wire:=[4760]
def known59:List Wire:=[4760]
def known60:List Wire:=[4373,4374,4375,4376,4760]
theorem result0:(compileFuel known0 127 block0).map (fun r=>(r.saved,r.final))=some (0,known1):=by decide +kernel
def opt0:ExactChecked known0 block0 known1 0:=normalize _ _ _ _ _ result0
theorem result1:(compileFuel known1 129 block1).map (fun r=>(r.saved,r.final))=some (0,known2):=by decide +kernel
def opt1:ExactChecked known1 block1 known2 0:=normalize _ _ _ _ _ result1
theorem result2:(compileFuel known2 129 block2).map (fun r=>(r.saved,r.final))=some (0,known3):=by decide +kernel
def opt2:ExactChecked known2 block2 known3 0:=normalize _ _ _ _ _ result2
theorem result3:(compileFuel known3 129 block3).map (fun r=>(r.saved,r.final))=some (0,known4):=by decide +kernel
def opt3:ExactChecked known3 block3 known4 0:=normalize _ _ _ _ _ result3
theorem result4:(compileFuel known4 129 block4).map (fun r=>(r.saved,r.final))=some (0,known5):=by decide +kernel
def opt4:ExactChecked known4 block4 known5 0:=normalize _ _ _ _ _ result4
theorem result5:(compileFuel known5 126 block5).map (fun r=>(r.saved,r.final))=some (4,known6):=by decide +kernel
def opt5:ExactChecked known5 block5 known6 4:=normalize _ _ _ _ _ result5
theorem result6:(compileFuel known6 127 block6).map (fun r=>(r.saved,r.final))=some (0,known7):=by decide +kernel
def opt6:ExactChecked known6 block6 known7 0:=normalize _ _ _ _ _ result6
theorem result7:(compileFuel known7 127 block7).map (fun r=>(r.saved,r.final))=some (0,known8):=by decide +kernel
def opt7:ExactChecked known7 block7 known8 0:=normalize _ _ _ _ _ result7
theorem result8:(compileFuel known8 127 block8).map (fun r=>(r.saved,r.final))=some (0,known9):=by decide +kernel
def opt8:ExactChecked known8 block8 known9 0:=normalize _ _ _ _ _ result8
theorem result9:(compileFuel known9 127 block9).map (fun r=>(r.saved,r.final))=some (0,known10):=by decide +kernel
def opt9:ExactChecked known9 block9 known10 0:=normalize _ _ _ _ _ result9
theorem result10:(compileFuel known10 127 block10).map (fun r=>(r.saved,r.final))=some (0,known11):=by decide +kernel
def opt10:ExactChecked known10 block10 known11 0:=normalize _ _ _ _ _ result10
theorem result11:(compileFuel known11 127 block11).map (fun r=>(r.saved,r.final))=some (0,known12):=by decide +kernel
def opt11:ExactChecked known11 block11 known12 0:=normalize _ _ _ _ _ result11
theorem result12:(compileFuel known12 127 block12).map (fun r=>(r.saved,r.final))=some (0,known13):=by decide +kernel
def opt12:ExactChecked known12 block12 known13 0:=normalize _ _ _ _ _ result12
theorem result13:(compileFuel known13 129 block13).map (fun r=>(r.saved,r.final))=some (0,known14):=by decide +kernel
def opt13:ExactChecked known13 block13 known14 0:=normalize _ _ _ _ _ result13
theorem result14:(compileFuel known14 129 block14).map (fun r=>(r.saved,r.final))=some (0,known15):=by decide +kernel
def opt14:ExactChecked known14 block14 known15 0:=normalize _ _ _ _ _ result14
theorem result15:(compileFuel known15 129 block15).map (fun r=>(r.saved,r.final))=some (0,known16):=by decide +kernel
def opt15:ExactChecked known15 block15 known16 0:=normalize _ _ _ _ _ result15
theorem result16:(compileFuel known16 129 block16).map (fun r=>(r.saved,r.final))=some (0,known17):=by decide +kernel
def opt16:ExactChecked known16 block16 known17 0:=normalize _ _ _ _ _ result16
theorem result17:(compileFuel known17 129 block17).map (fun r=>(r.saved,r.final))=some (0,known18):=by decide +kernel
def opt17:ExactChecked known17 block17 known18 0:=normalize _ _ _ _ _ result17
theorem result18:(compileFuel known18 129 block18).map (fun r=>(r.saved,r.final))=some (0,known19):=by decide +kernel
def opt18:ExactChecked known18 block18 known19 0:=normalize _ _ _ _ _ result18
theorem result19:(compileFuel known19 125 block19).map (fun r=>(r.saved,r.final))=some (0,known20):=by decide +kernel
def opt19:ExactChecked known19 block19 known20 0:=normalize _ _ _ _ _ result19
theorem result20:(compileFuel known20 128 block20).map (fun r=>(r.saved,r.final))=some (0,known21):=by decide +kernel
def opt20:ExactChecked known20 block20 known21 0:=normalize _ _ _ _ _ result20
theorem result21:(compileFuel known21 127 block21).map (fun r=>(r.saved,r.final))=some (0,known22):=by decide +kernel
def opt21:ExactChecked known21 block21 known22 0:=normalize _ _ _ _ _ result21
theorem result22:(compileFuel known22 127 block22).map (fun r=>(r.saved,r.final))=some (0,known23):=by decide +kernel
def opt22:ExactChecked known22 block22 known23 0:=normalize _ _ _ _ _ result22
theorem result23:(compileFuel known23 127 block23).map (fun r=>(r.saved,r.final))=some (0,known24):=by decide +kernel
def opt23:ExactChecked known23 block23 known24 0:=normalize _ _ _ _ _ result23
theorem result24:(compileFuel known24 127 block24).map (fun r=>(r.saved,r.final))=some (0,known25):=by decide +kernel
def opt24:ExactChecked known24 block24 known25 0:=normalize _ _ _ _ _ result24
theorem result25:(compileFuel known25 127 block25).map (fun r=>(r.saved,r.final))=some (0,known26):=by decide +kernel
def opt25:ExactChecked known25 block25 known26 0:=normalize _ _ _ _ _ result25
theorem result26:(compileFuel known26 127 block26).map (fun r=>(r.saved,r.final))=some (0,known27):=by decide +kernel
def opt26:ExactChecked known26 block26 known27 0:=normalize _ _ _ _ _ result26
theorem result27:(compileFuel known27 127 block27).map (fun r=>(r.saved,r.final))=some (0,known28):=by decide +kernel
def opt27:ExactChecked known27 block27 known28 0:=normalize _ _ _ _ _ result27
theorem result28:(compileFuel known28 127 block28).map (fun r=>(r.saved,r.final))=some (0,known29):=by decide +kernel
def opt28:ExactChecked known28 block28 known29 0:=normalize _ _ _ _ _ result28
theorem result29:(compileFuel known29 127 block29).map (fun r=>(r.saved,r.final))=some (0,known30):=by decide +kernel
def opt29:ExactChecked known29 block29 known30 0:=normalize _ _ _ _ _ result29
theorem result30:(compileFuel known30 127 block30).map (fun r=>(r.saved,r.final))=some (0,known31):=by decide +kernel
def opt30:ExactChecked known30 block30 known31 0:=normalize _ _ _ _ _ result30
theorem result31:(compileFuel known31 129 block31).map (fun r=>(r.saved,r.final))=some (0,known32):=by decide +kernel
def opt31:ExactChecked known31 block31 known32 0:=normalize _ _ _ _ _ result31
theorem result32:(compileFuel known32 129 block32).map (fun r=>(r.saved,r.final))=some (0,known33):=by decide +kernel
def opt32:ExactChecked known32 block32 known33 0:=normalize _ _ _ _ _ result32
theorem result33:(compileFuel known33 129 block33).map (fun r=>(r.saved,r.final))=some (0,known34):=by decide +kernel
def opt33:ExactChecked known33 block33 known34 0:=normalize _ _ _ _ _ result33
theorem result34:(compileFuel known34 129 block34).map (fun r=>(r.saved,r.final))=some (0,known35):=by decide +kernel
def opt34:ExactChecked known34 block34 known35 0:=normalize _ _ _ _ _ result34
theorem result35:(compileFuel known35 129 block35).map (fun r=>(r.saved,r.final))=some (0,known36):=by decide +kernel
def opt35:ExactChecked known35 block35 known36 0:=normalize _ _ _ _ _ result35
theorem result36:(compileFuel known36 129 block36).map (fun r=>(r.saved,r.final))=some (0,known37):=by decide +kernel
def opt36:ExactChecked known36 block36 known37 0:=normalize _ _ _ _ _ result36
theorem result37:(compileFuel known37 129 block37).map (fun r=>(r.saved,r.final))=some (4,known38):=by decide +kernel
def opt37:ExactChecked known37 block37 known38 4:=normalize _ _ _ _ _ result37
theorem result38:(compileFuel known38 129 block38).map (fun r=>(r.saved,r.final))=some (0,known39):=by decide +kernel
def opt38:ExactChecked known38 block38 known39 0:=normalize _ _ _ _ _ result38
theorem result39:(compileFuel known39 129 block39).map (fun r=>(r.saved,r.final))=some (0,known40):=by decide +kernel
def opt39:ExactChecked known39 block39 known40 0:=normalize _ _ _ _ _ result39
theorem result40:(compileFuel known40 129 block40).map (fun r=>(r.saved,r.final))=some (0,known41):=by decide +kernel
def opt40:ExactChecked known40 block40 known41 0:=normalize _ _ _ _ _ result40
theorem result41:(compileFuel known41 129 block41).map (fun r=>(r.saved,r.final))=some (0,known42):=by decide +kernel
def opt41:ExactChecked known41 block41 known42 0:=normalize _ _ _ _ _ result41
theorem result42:(compileFuel known42 129 block42).map (fun r=>(r.saved,r.final))=some (0,known43):=by decide +kernel
def opt42:ExactChecked known42 block42 known43 0:=normalize _ _ _ _ _ result42
theorem result43:(compileFuel known43 129 block43).map (fun r=>(r.saved,r.final))=some (0,known44):=by decide +kernel
def opt43:ExactChecked known43 block43 known44 0:=normalize _ _ _ _ _ result43
theorem result44:(compileFuel known44 129 block44).map (fun r=>(r.saved,r.final))=some (0,known45):=by decide +kernel
def opt44:ExactChecked known44 block44 known45 0:=normalize _ _ _ _ _ result44
theorem result45:(compileFuel known45 129 block45).map (fun r=>(r.saved,r.final))=some (0,known46):=by decide +kernel
def opt45:ExactChecked known45 block45 known46 0:=normalize _ _ _ _ _ result45
theorem result46:(compileFuel known46 129 block46).map (fun r=>(r.saved,r.final))=some (0,known47):=by decide +kernel
def opt46:ExactChecked known46 block46 known47 0:=normalize _ _ _ _ _ result46
theorem result47:(compileFuel known47 129 block47).map (fun r=>(r.saved,r.final))=some (0,known48):=by decide +kernel
def opt47:ExactChecked known47 block47 known48 0:=normalize _ _ _ _ _ result47
theorem result48:(compileFuel known48 129 block48).map (fun r=>(r.saved,r.final))=some (0,known49):=by decide +kernel
def opt48:ExactChecked known48 block48 known49 0:=normalize _ _ _ _ _ result48
theorem result49:(compileFuel known49 129 block49).map (fun r=>(r.saved,r.final))=some (0,known50):=by decide +kernel
def opt49:ExactChecked known49 block49 known50 0:=normalize _ _ _ _ _ result49
theorem result50:(compileFuel known50 129 block50).map (fun r=>(r.saved,r.final))=some (0,known51):=by decide +kernel
def opt50:ExactChecked known50 block50 known51 0:=normalize _ _ _ _ _ result50
theorem result51:(compileFuel known51 129 block51).map (fun r=>(r.saved,r.final))=some (0,known52):=by decide +kernel
def opt51:ExactChecked known51 block51 known52 0:=normalize _ _ _ _ _ result51
theorem result52:(compileFuel known52 129 block52).map (fun r=>(r.saved,r.final))=some (0,known53):=by decide +kernel
def opt52:ExactChecked known52 block52 known53 0:=normalize _ _ _ _ _ result52
theorem result53:(compileFuel known53 129 block53).map (fun r=>(r.saved,r.final))=some (0,known54):=by decide +kernel
def opt53:ExactChecked known53 block53 known54 0:=normalize _ _ _ _ _ result53
theorem result54:(compileFuel known54 129 block54).map (fun r=>(r.saved,r.final))=some (0,known55):=by decide +kernel
def opt54:ExactChecked known54 block54 known55 0:=normalize _ _ _ _ _ result54
theorem result55:(compileFuel known55 129 block55).map (fun r=>(r.saved,r.final))=some (0,known56):=by decide +kernel
def opt55:ExactChecked known55 block55 known56 0:=normalize _ _ _ _ _ result55
theorem result56:(compileFuel known56 129 block56).map (fun r=>(r.saved,r.final))=some (0,known57):=by decide +kernel
def opt56:ExactChecked known56 block56 known57 0:=normalize _ _ _ _ _ result56
theorem result57:(compileFuel known57 127 block57).map (fun r=>(r.saved,r.final))=some (0,known58):=by decide +kernel
def opt57:ExactChecked known57 block57 known58 0:=normalize _ _ _ _ _ result57
theorem result58:(compileFuel known58 129 block58).map (fun r=>(r.saved,r.final))=some (0,known59):=by decide +kernel
def opt58:ExactChecked known58 block58 known59 0:=normalize _ _ _ _ _ result58
theorem result59:(compileFuel known59 72 block59).map (fun r=>(r.saved,r.final))=some (0,known60):=by decide +kernel
def opt59:ExactChecked known59 block59 known60 0:=normalize _ _ _ _ _ result59
def join1_3Opt:ExactChecked known1 join1_3 known3 0:=ExactChecked.append _ _ _ _ _ _ _ opt1 opt2
def join0_3Opt:ExactChecked known0 join0_3 known3 0:=ExactChecked.append _ _ _ _ _ _ _ opt0 join1_3Opt
def join3_5Opt:ExactChecked known3 join3_5 known5 0:=ExactChecked.append _ _ _ _ _ _ _ opt3 opt4
def join5_7Opt:ExactChecked known5 join5_7 known7 4:=ExactChecked.append _ _ _ _ _ _ _ opt5 opt6
def join3_7Opt:ExactChecked known3 join3_7 known7 4:=ExactChecked.append _ _ _ _ _ _ _ join3_5Opt join5_7Opt
def join0_7Opt:ExactChecked known0 join0_7 known7 4:=ExactChecked.append _ _ _ _ _ _ _ join0_3Opt join3_7Opt
def join7_9Opt:ExactChecked known7 join7_9 known9 0:=ExactChecked.append _ _ _ _ _ _ _ opt7 opt8
def join9_11Opt:ExactChecked known9 join9_11 known11 0:=ExactChecked.append _ _ _ _ _ _ _ opt9 opt10
def join7_11Opt:ExactChecked known7 join7_11 known11 0:=ExactChecked.append _ _ _ _ _ _ _ join7_9Opt join9_11Opt
def join11_13Opt:ExactChecked known11 join11_13 known13 0:=ExactChecked.append _ _ _ _ _ _ _ opt11 opt12
def join13_15Opt:ExactChecked known13 join13_15 known15 0:=ExactChecked.append _ _ _ _ _ _ _ opt13 opt14
def join11_15Opt:ExactChecked known11 join11_15 known15 0:=ExactChecked.append _ _ _ _ _ _ _ join11_13Opt join13_15Opt
def join7_15Opt:ExactChecked known7 join7_15 known15 0:=ExactChecked.append _ _ _ _ _ _ _ join7_11Opt join11_15Opt
def join0_15Opt:ExactChecked known0 join0_15 known15 4:=ExactChecked.append _ _ _ _ _ _ _ join0_7Opt join7_15Opt
def join16_18Opt:ExactChecked known16 join16_18 known18 0:=ExactChecked.append _ _ _ _ _ _ _ opt16 opt17
def join15_18Opt:ExactChecked known15 join15_18 known18 0:=ExactChecked.append _ _ _ _ _ _ _ opt15 join16_18Opt
def join18_20Opt:ExactChecked known18 join18_20 known20 0:=ExactChecked.append _ _ _ _ _ _ _ opt18 opt19
def join20_22Opt:ExactChecked known20 join20_22 known22 0:=ExactChecked.append _ _ _ _ _ _ _ opt20 opt21
def join18_22Opt:ExactChecked known18 join18_22 known22 0:=ExactChecked.append _ _ _ _ _ _ _ join18_20Opt join20_22Opt
def join15_22Opt:ExactChecked known15 join15_22 known22 0:=ExactChecked.append _ _ _ _ _ _ _ join15_18Opt join18_22Opt
def join22_24Opt:ExactChecked known22 join22_24 known24 0:=ExactChecked.append _ _ _ _ _ _ _ opt22 opt23
def join24_26Opt:ExactChecked known24 join24_26 known26 0:=ExactChecked.append _ _ _ _ _ _ _ opt24 opt25
def join22_26Opt:ExactChecked known22 join22_26 known26 0:=ExactChecked.append _ _ _ _ _ _ _ join22_24Opt join24_26Opt
def join26_28Opt:ExactChecked known26 join26_28 known28 0:=ExactChecked.append _ _ _ _ _ _ _ opt26 opt27
def join28_30Opt:ExactChecked known28 join28_30 known30 0:=ExactChecked.append _ _ _ _ _ _ _ opt28 opt29
def join26_30Opt:ExactChecked known26 join26_30 known30 0:=ExactChecked.append _ _ _ _ _ _ _ join26_28Opt join28_30Opt
def join22_30Opt:ExactChecked known22 join22_30 known30 0:=ExactChecked.append _ _ _ _ _ _ _ join22_26Opt join26_30Opt
def join15_30Opt:ExactChecked known15 join15_30 known30 0:=ExactChecked.append _ _ _ _ _ _ _ join15_22Opt join22_30Opt
def join0_30Opt:ExactChecked known0 join0_30 known30 4:=ExactChecked.append _ _ _ _ _ _ _ join0_15Opt join15_30Opt
def join31_33Opt:ExactChecked known31 join31_33 known33 0:=ExactChecked.append _ _ _ _ _ _ _ opt31 opt32
def join30_33Opt:ExactChecked known30 join30_33 known33 0:=ExactChecked.append _ _ _ _ _ _ _ opt30 join31_33Opt
def join33_35Opt:ExactChecked known33 join33_35 known35 0:=ExactChecked.append _ _ _ _ _ _ _ opt33 opt34
def join35_37Opt:ExactChecked known35 join35_37 known37 0:=ExactChecked.append _ _ _ _ _ _ _ opt35 opt36
def join33_37Opt:ExactChecked known33 join33_37 known37 0:=ExactChecked.append _ _ _ _ _ _ _ join33_35Opt join35_37Opt
def join30_37Opt:ExactChecked known30 join30_37 known37 0:=ExactChecked.append _ _ _ _ _ _ _ join30_33Opt join33_37Opt
def join37_39Opt:ExactChecked known37 join37_39 known39 4:=ExactChecked.append _ _ _ _ _ _ _ opt37 opt38
def join39_41Opt:ExactChecked known39 join39_41 known41 0:=ExactChecked.append _ _ _ _ _ _ _ opt39 opt40
def join37_41Opt:ExactChecked known37 join37_41 known41 4:=ExactChecked.append _ _ _ _ _ _ _ join37_39Opt join39_41Opt
def join41_43Opt:ExactChecked known41 join41_43 known43 0:=ExactChecked.append _ _ _ _ _ _ _ opt41 opt42
def join43_45Opt:ExactChecked known43 join43_45 known45 0:=ExactChecked.append _ _ _ _ _ _ _ opt43 opt44
def join41_45Opt:ExactChecked known41 join41_45 known45 0:=ExactChecked.append _ _ _ _ _ _ _ join41_43Opt join43_45Opt
def join37_45Opt:ExactChecked known37 join37_45 known45 4:=ExactChecked.append _ _ _ _ _ _ _ join37_41Opt join41_45Opt
def join30_45Opt:ExactChecked known30 join30_45 known45 4:=ExactChecked.append _ _ _ _ _ _ _ join30_37Opt join37_45Opt
def join46_48Opt:ExactChecked known46 join46_48 known48 0:=ExactChecked.append _ _ _ _ _ _ _ opt46 opt47
def join45_48Opt:ExactChecked known45 join45_48 known48 0:=ExactChecked.append _ _ _ _ _ _ _ opt45 join46_48Opt
def join48_50Opt:ExactChecked known48 join48_50 known50 0:=ExactChecked.append _ _ _ _ _ _ _ opt48 opt49
def join50_52Opt:ExactChecked known50 join50_52 known52 0:=ExactChecked.append _ _ _ _ _ _ _ opt50 opt51
def join48_52Opt:ExactChecked known48 join48_52 known52 0:=ExactChecked.append _ _ _ _ _ _ _ join48_50Opt join50_52Opt
def join45_52Opt:ExactChecked known45 join45_52 known52 0:=ExactChecked.append _ _ _ _ _ _ _ join45_48Opt join48_52Opt
def join52_54Opt:ExactChecked known52 join52_54 known54 0:=ExactChecked.append _ _ _ _ _ _ _ opt52 opt53
def join54_56Opt:ExactChecked known54 join54_56 known56 0:=ExactChecked.append _ _ _ _ _ _ _ opt54 opt55
def join52_56Opt:ExactChecked known52 join52_56 known56 0:=ExactChecked.append _ _ _ _ _ _ _ join52_54Opt join54_56Opt
def join56_58Opt:ExactChecked known56 join56_58 known58 0:=ExactChecked.append _ _ _ _ _ _ _ opt56 opt57
def join58_60Opt:ExactChecked known58 join58_60 known60 0:=ExactChecked.append _ _ _ _ _ _ _ opt58 opt59
def join56_60Opt:ExactChecked known56 join56_60 known60 0:=ExactChecked.append _ _ _ _ _ _ _ join56_58Opt join58_60Opt
def join52_60Opt:ExactChecked known52 join52_60 known60 0:=ExactChecked.append _ _ _ _ _ _ _ join52_56Opt join56_60Opt
def join45_60Opt:ExactChecked known45 join45_60 known60 0:=ExactChecked.append _ _ _ _ _ _ _ join45_52Opt join52_60Opt
def join30_60Opt:ExactChecked known30 join30_60 known60 4:=ExactChecked.append _ _ _ _ _ _ _ join30_45Opt join45_60Opt
def join0_60Opt:ExactChecked known0 join0_60 known60 8:=ExactChecked.append _ _ _ _ _ _ _ join0_30Opt join30_60Opt
def body:Program:=join0_60Opt.out
-- D1 (gate margin): the compiler output is stated once, in Fold98 (`bank_match`).
theorem literal_verified:ParkAProgramBool.programEq literal (C163Low4Middle.bankChecked.out)=true:=by
 unfold C163Low4Middle.bankChecked
 exact ECDSAAdd.Entrant.D1Opt.get_of_elim C163Low4Middle.bank_match C163Low4Middle.compiled_bank
theorem literal_eq:literal=C163Low4Middle.bankChecked.out:=ParkAProgramBool.programEq_sound _ _ literal_verified
theorem cert:Cert known0 (C163Low4Middle.bankChecked.out) body known60 8:=
 Eq.mp (congrArg (fun P:Program=>Cert known0 P body known60 8) literal_eq) join0_60Opt.proof

end ECDSAAdd.Entrant.KnownCMidStaged

end

-- Verified component KnownAMidStaged
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.KnownAMidStaged
open Arithmetic KnownSparseFold
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
def known0:List Wire:=[4373,4374,4375,4376,4760]
def known1:List Wire:=[4373,4374,4375,4376,4760]
def known2:List Wire:=[4373,4374,4375,4376,4760]
def known3:List Wire:=[4373,4374,4375,4376,4760]
def known4:List Wire:=[4373,4374,4375,4376,4760]
def known5:List Wire:=[4373,4374,4375,4376,4760]
def known6:List Wire:=[4373,4374,4375,4376,4760]
def known7:List Wire:=[4373,4374,4375,4376,4760]
def known8:List Wire:=[4373,4374,4375,4376,4760]
def known9:List Wire:=[4373,4374,4375,4376,4760]
def known10:List Wire:=[4373,4374,4375,4376,4760]
def known11:List Wire:=[4373,4374,4375,4376,4760]
def known12:List Wire:=[4373,4374,4375,4376,4760]
def known13:List Wire:=[4373,4374,4375,4376,4760]
def known14:List Wire:=[4373,4374,4375,4376,4760]
def known15:List Wire:=[4373,4374,4375,4376,4760]
def known16:List Wire:=[4373,4374,4375,4376,4760]
def known17:List Wire:=[4760]
def known18:List Wire:=[4760]
def known19:List Wire:=[4760]
def known20:List Wire:=[4760]
def known21:List Wire:=[4760]
def known22:List Wire:=[4760]
def known23:List Wire:=[4760]
def known24:List Wire:=[4760]
def known25:List Wire:=[4760]
def known26:List Wire:=[4760]
def known27:List Wire:=[4760]
def known28:List Wire:=[4760]
def known29:List Wire:=[4760]
def known30:List Wire:=[4760]
def known31:List Wire:=[4760]
def known32:List Wire:=[4760]
def known33:List Wire:=[4760]
def known34:List Wire:=[4760]
def known35:List Wire:=[4373,4374,4375,4376,4760]
def known36:List Wire:=[4373,4374,4375,4376,4760]
def known37:List Wire:=[4373,4374,4375,4376,4760]
def known38:List Wire:=[4373,4374,4375,4376,4760]
def known39:List Wire:=[4373,4374,4375,4376,4760]
def known40:List Wire:=[4373,4374,4375,4376,4760]
def known41:List Wire:=[4373,4374,4375,4376,4760]
def known42:List Wire:=[4373,4374,4375,4376,4760]
def known43:List Wire:=[4373,4374,4375,4376,4760]
def known44:List Wire:=[4373,4374,4375,4376,4760]
def known45:List Wire:=[4373,4374,4375,4376,4760]
def known46:List Wire:=[4373,4374,4375,4376,4760]
def known47:List Wire:=[4373,4374,4375,4376,4760]
def known48:List Wire:=[4373,4374,4375,4376,4760]
def known49:List Wire:=[4373,4374,4375,4376,4760]
def known50:List Wire:=[4373,4374,4375,4376,4760]
def known51:List Wire:=[4373,4374,4375,4376,4760]
def known52:List Wire:=[4373,4374,4375,4376,4760]
def known53:List Wire:=[4373,4374,4375,4376,4760]
def known54:List Wire:=[4373,4374,4375,4376,4760]
theorem result0:(compileFuel known0 129 block0).map (fun r=>(r.saved,r.final))=some (0,known1):=by decide +kernel
def opt0:ExactChecked known0 block0 known1 0:=normalize _ _ _ _ _ result0
theorem result1:(compileFuel known1 129 block1).map (fun r=>(r.saved,r.final))=some (0,known2):=by decide +kernel
def opt1:ExactChecked known1 block1 known2 0:=normalize _ _ _ _ _ result1
theorem result2:(compileFuel known2 129 block2).map (fun r=>(r.saved,r.final))=some (0,known3):=by decide +kernel
def opt2:ExactChecked known2 block2 known3 0:=normalize _ _ _ _ _ result2
theorem result3:(compileFuel known3 124 block3).map (fun r=>(r.saved,r.final))=some (4,known4):=by decide +kernel
def opt3:ExactChecked known3 block3 known4 4:=normalize _ _ _ _ _ result3
theorem result4:(compileFuel known4 127 block4).map (fun r=>(r.saved,r.final))=some (0,known5):=by decide +kernel
def opt4:ExactChecked known4 block4 known5 0:=normalize _ _ _ _ _ result4
theorem result5:(compileFuel known5 127 block5).map (fun r=>(r.saved,r.final))=some (0,known6):=by decide +kernel
def opt5:ExactChecked known5 block5 known6 0:=normalize _ _ _ _ _ result5
theorem result6:(compileFuel known6 127 block6).map (fun r=>(r.saved,r.final))=some (0,known7):=by decide +kernel
def opt6:ExactChecked known6 block6 known7 0:=normalize _ _ _ _ _ result6
theorem result7:(compileFuel known7 127 block7).map (fun r=>(r.saved,r.final))=some (0,known8):=by decide +kernel
def opt7:ExactChecked known7 block7 known8 0:=normalize _ _ _ _ _ result7
theorem result8:(compileFuel known8 127 block8).map (fun r=>(r.saved,r.final))=some (0,known9):=by decide +kernel
def opt8:ExactChecked known8 block8 known9 0:=normalize _ _ _ _ _ result8
theorem result9:(compileFuel known9 127 block9).map (fun r=>(r.saved,r.final))=some (0,known10):=by decide +kernel
def opt9:ExactChecked known9 block9 known10 0:=normalize _ _ _ _ _ result9
theorem result10:(compileFuel known10 129 block10).map (fun r=>(r.saved,r.final))=some (0,known11):=by decide +kernel
def opt10:ExactChecked known10 block10 known11 0:=normalize _ _ _ _ _ result10
theorem result11:(compileFuel known11 129 block11).map (fun r=>(r.saved,r.final))=some (0,known12):=by decide +kernel
def opt11:ExactChecked known11 block11 known12 0:=normalize _ _ _ _ _ result11
theorem result12:(compileFuel known12 129 block12).map (fun r=>(r.saved,r.final))=some (0,known13):=by decide +kernel
def opt12:ExactChecked known12 block12 known13 0:=normalize _ _ _ _ _ result12
theorem result13:(compileFuel known13 129 block13).map (fun r=>(r.saved,r.final))=some (0,known14):=by decide +kernel
def opt13:ExactChecked known13 block13 known14 0:=normalize _ _ _ _ _ result13
theorem result14:(compileFuel known14 129 block14).map (fun r=>(r.saved,r.final))=some (0,known15):=by decide +kernel
def opt14:ExactChecked known14 block14 known15 0:=normalize _ _ _ _ _ result14
theorem result15:(compileFuel known15 129 block15).map (fun r=>(r.saved,r.final))=some (0,known16):=by decide +kernel
def opt15:ExactChecked known15 block15 known16 0:=normalize _ _ _ _ _ result15
theorem result16:(compileFuel known16 129 block16).map (fun r=>(r.saved,r.final))=some (0,known17):=by decide +kernel
def opt16:ExactChecked known16 block16 known17 0:=normalize _ _ _ _ _ result16
theorem result17:(compileFuel known17 129 block17).map (fun r=>(r.saved,r.final))=some (0,known18):=by decide +kernel
def opt17:ExactChecked known17 block17 known18 0:=normalize _ _ _ _ _ result17
theorem result18:(compileFuel known18 128 block18).map (fun r=>(r.saved,r.final))=some (0,known19):=by decide +kernel
def opt18:ExactChecked known18 block18 known19 0:=normalize _ _ _ _ _ result18
theorem result19:(compileFuel known19 127 block19).map (fun r=>(r.saved,r.final))=some (0,known20):=by decide +kernel
def opt19:ExactChecked known19 block19 known20 0:=normalize _ _ _ _ _ result19
theorem result20:(compileFuel known20 127 block20).map (fun r=>(r.saved,r.final))=some (0,known21):=by decide +kernel
def opt20:ExactChecked known20 block20 known21 0:=normalize _ _ _ _ _ result20
theorem result21:(compileFuel known21 127 block21).map (fun r=>(r.saved,r.final))=some (0,known22):=by decide +kernel
def opt21:ExactChecked known21 block21 known22 0:=normalize _ _ _ _ _ result21
theorem result22:(compileFuel known22 127 block22).map (fun r=>(r.saved,r.final))=some (0,known23):=by decide +kernel
def opt22:ExactChecked known22 block22 known23 0:=normalize _ _ _ _ _ result22
theorem result23:(compileFuel known23 127 block23).map (fun r=>(r.saved,r.final))=some (0,known24):=by decide +kernel
def opt23:ExactChecked known23 block23 known24 0:=normalize _ _ _ _ _ result23
theorem result24:(compileFuel known24 127 block24).map (fun r=>(r.saved,r.final))=some (0,known25):=by decide +kernel
def opt24:ExactChecked known24 block24 known25 0:=normalize _ _ _ _ _ result24
theorem result25:(compileFuel known25 127 block25).map (fun r=>(r.saved,r.final))=some (0,known26):=by decide +kernel
def opt25:ExactChecked known25 block25 known26 0:=normalize _ _ _ _ _ result25
theorem result26:(compileFuel known26 127 block26).map (fun r=>(r.saved,r.final))=some (0,known27):=by decide +kernel
def opt26:ExactChecked known26 block26 known27 0:=normalize _ _ _ _ _ result26
theorem result27:(compileFuel known27 127 block27).map (fun r=>(r.saved,r.final))=some (0,known28):=by decide +kernel
def opt27:ExactChecked known27 block27 known28 0:=normalize _ _ _ _ _ result27
theorem result28:(compileFuel known28 129 block28).map (fun r=>(r.saved,r.final))=some (0,known29):=by decide +kernel
def opt28:ExactChecked known28 block28 known29 0:=normalize _ _ _ _ _ result28
theorem result29:(compileFuel known29 129 block29).map (fun r=>(r.saved,r.final))=some (0,known30):=by decide +kernel
def opt29:ExactChecked known29 block29 known30 0:=normalize _ _ _ _ _ result29
theorem result30:(compileFuel known30 129 block30).map (fun r=>(r.saved,r.final))=some (0,known31):=by decide +kernel
def opt30:ExactChecked known30 block30 known31 0:=normalize _ _ _ _ _ result30
theorem result31:(compileFuel known31 129 block31).map (fun r=>(r.saved,r.final))=some (0,known32):=by decide +kernel
def opt31:ExactChecked known31 block31 known32 0:=normalize _ _ _ _ _ result31
theorem result32:(compileFuel known32 129 block32).map (fun r=>(r.saved,r.final))=some (0,known33):=by decide +kernel
def opt32:ExactChecked known32 block32 known33 0:=normalize _ _ _ _ _ result32
theorem result33:(compileFuel known33 129 block33).map (fun r=>(r.saved,r.final))=some (0,known34):=by decide +kernel
def opt33:ExactChecked known33 block33 known34 0:=normalize _ _ _ _ _ result33
theorem result34:(compileFuel known34 128 block34).map (fun r=>(r.saved,r.final))=some (4,known35):=by decide +kernel
def opt34:ExactChecked known34 block34 known35 4:=normalize _ _ _ _ _ result34
theorem result35:(compileFuel known35 129 block35).map (fun r=>(r.saved,r.final))=some (0,known36):=by decide +kernel
def opt35:ExactChecked known35 block35 known36 0:=normalize _ _ _ _ _ result35
theorem result36:(compileFuel known36 129 block36).map (fun r=>(r.saved,r.final))=some (0,known37):=by decide +kernel
def opt36:ExactChecked known36 block36 known37 0:=normalize _ _ _ _ _ result36
theorem result37:(compileFuel known37 129 block37).map (fun r=>(r.saved,r.final))=some (0,known38):=by decide +kernel
def opt37:ExactChecked known37 block37 known38 0:=normalize _ _ _ _ _ result37
theorem result38:(compileFuel known38 129 block38).map (fun r=>(r.saved,r.final))=some (0,known39):=by decide +kernel
def opt38:ExactChecked known38 block38 known39 0:=normalize _ _ _ _ _ result38
theorem result39:(compileFuel known39 129 block39).map (fun r=>(r.saved,r.final))=some (0,known40):=by decide +kernel
def opt39:ExactChecked known39 block39 known40 0:=normalize _ _ _ _ _ result39
theorem result40:(compileFuel known40 129 block40).map (fun r=>(r.saved,r.final))=some (0,known41):=by decide +kernel
def opt40:ExactChecked known40 block40 known41 0:=normalize _ _ _ _ _ result40
theorem result41:(compileFuel known41 129 block41).map (fun r=>(r.saved,r.final))=some (0,known42):=by decide +kernel
def opt41:ExactChecked known41 block41 known42 0:=normalize _ _ _ _ _ result41
theorem result42:(compileFuel known42 129 block42).map (fun r=>(r.saved,r.final))=some (0,known43):=by decide +kernel
def opt42:ExactChecked known42 block42 known43 0:=normalize _ _ _ _ _ result42
theorem result43:(compileFuel known43 129 block43).map (fun r=>(r.saved,r.final))=some (0,known44):=by decide +kernel
def opt43:ExactChecked known43 block43 known44 0:=normalize _ _ _ _ _ result43
theorem result44:(compileFuel known44 129 block44).map (fun r=>(r.saved,r.final))=some (0,known45):=by decide +kernel
def opt44:ExactChecked known44 block44 known45 0:=normalize _ _ _ _ _ result44
theorem result45:(compileFuel known45 129 block45).map (fun r=>(r.saved,r.final))=some (0,known46):=by decide +kernel
def opt45:ExactChecked known45 block45 known46 0:=normalize _ _ _ _ _ result45
theorem result46:(compileFuel known46 129 block46).map (fun r=>(r.saved,r.final))=some (0,known47):=by decide +kernel
def opt46:ExactChecked known46 block46 known47 0:=normalize _ _ _ _ _ result46
theorem result47:(compileFuel known47 129 block47).map (fun r=>(r.saved,r.final))=some (0,known48):=by decide +kernel
def opt47:ExactChecked known47 block47 known48 0:=normalize _ _ _ _ _ result47
theorem result48:(compileFuel known48 129 block48).map (fun r=>(r.saved,r.final))=some (0,known49):=by decide +kernel
def opt48:ExactChecked known48 block48 known49 0:=normalize _ _ _ _ _ result48
theorem result49:(compileFuel known49 129 block49).map (fun r=>(r.saved,r.final))=some (0,known50):=by decide +kernel
def opt49:ExactChecked known49 block49 known50 0:=normalize _ _ _ _ _ result49
theorem result50:(compileFuel known50 129 block50).map (fun r=>(r.saved,r.final))=some (0,known51):=by decide +kernel
def opt50:ExactChecked known50 block50 known51 0:=normalize _ _ _ _ _ result50
theorem result51:(compileFuel known51 129 block51).map (fun r=>(r.saved,r.final))=some (0,known52):=by decide +kernel
def opt51:ExactChecked known51 block51 known52 0:=normalize _ _ _ _ _ result51
theorem result52:(compileFuel known52 129 block52).map (fun r=>(r.saved,r.final))=some (0,known53):=by decide +kernel
def opt52:ExactChecked known52 block52 known53 0:=normalize _ _ _ _ _ result52
theorem result53:(compileFuel known53 119 block53).map (fun r=>(r.saved,r.final))=some (0,known54):=by decide +kernel
def opt53:ExactChecked known53 block53 known54 0:=normalize _ _ _ _ _ result53
def join1_3Opt:ExactChecked known1 join1_3 known3 0:=ExactChecked.append _ _ _ _ _ _ _ opt1 opt2
def join0_3Opt:ExactChecked known0 join0_3 known3 0:=ExactChecked.append _ _ _ _ _ _ _ opt0 join1_3Opt
def join4_6Opt:ExactChecked known4 join4_6 known6 0:=ExactChecked.append _ _ _ _ _ _ _ opt4 opt5
def join3_6Opt:ExactChecked known3 join3_6 known6 4:=ExactChecked.append _ _ _ _ _ _ _ opt3 join4_6Opt
def join0_6Opt:ExactChecked known0 join0_6 known6 4:=ExactChecked.append _ _ _ _ _ _ _ join0_3Opt join3_6Opt
def join7_9Opt:ExactChecked known7 join7_9 known9 0:=ExactChecked.append _ _ _ _ _ _ _ opt7 opt8
def join6_9Opt:ExactChecked known6 join6_9 known9 0:=ExactChecked.append _ _ _ _ _ _ _ opt6 join7_9Opt
def join9_11Opt:ExactChecked known9 join9_11 known11 0:=ExactChecked.append _ _ _ _ _ _ _ opt9 opt10
def join11_13Opt:ExactChecked known11 join11_13 known13 0:=ExactChecked.append _ _ _ _ _ _ _ opt11 opt12
def join9_13Opt:ExactChecked known9 join9_13 known13 0:=ExactChecked.append _ _ _ _ _ _ _ join9_11Opt join11_13Opt
def join6_13Opt:ExactChecked known6 join6_13 known13 0:=ExactChecked.append _ _ _ _ _ _ _ join6_9Opt join9_13Opt
def join0_13Opt:ExactChecked known0 join0_13 known13 4:=ExactChecked.append _ _ _ _ _ _ _ join0_6Opt join6_13Opt
def join14_16Opt:ExactChecked known14 join14_16 known16 0:=ExactChecked.append _ _ _ _ _ _ _ opt14 opt15
def join13_16Opt:ExactChecked known13 join13_16 known16 0:=ExactChecked.append _ _ _ _ _ _ _ opt13 join14_16Opt
def join16_18Opt:ExactChecked known16 join16_18 known18 0:=ExactChecked.append _ _ _ _ _ _ _ opt16 opt17
def join18_20Opt:ExactChecked known18 join18_20 known20 0:=ExactChecked.append _ _ _ _ _ _ _ opt18 opt19
def join16_20Opt:ExactChecked known16 join16_20 known20 0:=ExactChecked.append _ _ _ _ _ _ _ join16_18Opt join18_20Opt
def join13_20Opt:ExactChecked known13 join13_20 known20 0:=ExactChecked.append _ _ _ _ _ _ _ join13_16Opt join16_20Opt
def join21_23Opt:ExactChecked known21 join21_23 known23 0:=ExactChecked.append _ _ _ _ _ _ _ opt21 opt22
def join20_23Opt:ExactChecked known20 join20_23 known23 0:=ExactChecked.append _ _ _ _ _ _ _ opt20 join21_23Opt
def join23_25Opt:ExactChecked known23 join23_25 known25 0:=ExactChecked.append _ _ _ _ _ _ _ opt23 opt24
def join25_27Opt:ExactChecked known25 join25_27 known27 0:=ExactChecked.append _ _ _ _ _ _ _ opt25 opt26
def join23_27Opt:ExactChecked known23 join23_27 known27 0:=ExactChecked.append _ _ _ _ _ _ _ join23_25Opt join25_27Opt
def join20_27Opt:ExactChecked known20 join20_27 known27 0:=ExactChecked.append _ _ _ _ _ _ _ join20_23Opt join23_27Opt
def join13_27Opt:ExactChecked known13 join13_27 known27 0:=ExactChecked.append _ _ _ _ _ _ _ join13_20Opt join20_27Opt
def join0_27Opt:ExactChecked known0 join0_27 known27 4:=ExactChecked.append _ _ _ _ _ _ _ join0_13Opt join13_27Opt
def join28_30Opt:ExactChecked known28 join28_30 known30 0:=ExactChecked.append _ _ _ _ _ _ _ opt28 opt29
def join27_30Opt:ExactChecked known27 join27_30 known30 0:=ExactChecked.append _ _ _ _ _ _ _ opt27 join28_30Opt
def join31_33Opt:ExactChecked known31 join31_33 known33 0:=ExactChecked.append _ _ _ _ _ _ _ opt31 opt32
def join30_33Opt:ExactChecked known30 join30_33 known33 0:=ExactChecked.append _ _ _ _ _ _ _ opt30 join31_33Opt
def join27_33Opt:ExactChecked known27 join27_33 known33 0:=ExactChecked.append _ _ _ _ _ _ _ join27_30Opt join30_33Opt
def join34_36Opt:ExactChecked known34 join34_36 known36 4:=ExactChecked.append _ _ _ _ _ _ _ opt34 opt35
def join33_36Opt:ExactChecked known33 join33_36 known36 4:=ExactChecked.append _ _ _ _ _ _ _ opt33 join34_36Opt
def join36_38Opt:ExactChecked known36 join36_38 known38 0:=ExactChecked.append _ _ _ _ _ _ _ opt36 opt37
def join38_40Opt:ExactChecked known38 join38_40 known40 0:=ExactChecked.append _ _ _ _ _ _ _ opt38 opt39
def join36_40Opt:ExactChecked known36 join36_40 known40 0:=ExactChecked.append _ _ _ _ _ _ _ join36_38Opt join38_40Opt
def join33_40Opt:ExactChecked known33 join33_40 known40 4:=ExactChecked.append _ _ _ _ _ _ _ join33_36Opt join36_40Opt
def join27_40Opt:ExactChecked known27 join27_40 known40 4:=ExactChecked.append _ _ _ _ _ _ _ join27_33Opt join33_40Opt
def join41_43Opt:ExactChecked known41 join41_43 known43 0:=ExactChecked.append _ _ _ _ _ _ _ opt41 opt42
def join40_43Opt:ExactChecked known40 join40_43 known43 0:=ExactChecked.append _ _ _ _ _ _ _ opt40 join41_43Opt
def join43_45Opt:ExactChecked known43 join43_45 known45 0:=ExactChecked.append _ _ _ _ _ _ _ opt43 opt44
def join45_47Opt:ExactChecked known45 join45_47 known47 0:=ExactChecked.append _ _ _ _ _ _ _ opt45 opt46
def join43_47Opt:ExactChecked known43 join43_47 known47 0:=ExactChecked.append _ _ _ _ _ _ _ join43_45Opt join45_47Opt
def join40_47Opt:ExactChecked known40 join40_47 known47 0:=ExactChecked.append _ _ _ _ _ _ _ join40_43Opt join43_47Opt
def join48_50Opt:ExactChecked known48 join48_50 known50 0:=ExactChecked.append _ _ _ _ _ _ _ opt48 opt49
def join47_50Opt:ExactChecked known47 join47_50 known50 0:=ExactChecked.append _ _ _ _ _ _ _ opt47 join48_50Opt
def join50_52Opt:ExactChecked known50 join50_52 known52 0:=ExactChecked.append _ _ _ _ _ _ _ opt50 opt51
def join52_54Opt:ExactChecked known52 join52_54 known54 0:=ExactChecked.append _ _ _ _ _ _ _ opt52 opt53
def join50_54Opt:ExactChecked known50 join50_54 known54 0:=ExactChecked.append _ _ _ _ _ _ _ join50_52Opt join52_54Opt
def join47_54Opt:ExactChecked known47 join47_54 known54 0:=ExactChecked.append _ _ _ _ _ _ _ join47_50Opt join50_54Opt
def join40_54Opt:ExactChecked known40 join40_54 known54 0:=ExactChecked.append _ _ _ _ _ _ _ join40_47Opt join47_54Opt
def join27_54Opt:ExactChecked known27 join27_54 known54 4:=ExactChecked.append _ _ _ _ _ _ _ join27_40Opt join40_54Opt
def join0_54Opt:ExactChecked known0 join0_54 known54 8:=ExactChecked.append _ _ _ _ _ _ _ join0_27Opt join27_54Opt
def body:Program:=join0_54Opt.out
-- D1 (gate margin): the compiler output is stated once, in FullLogic (`match99`).
theorem literal_verified:ParkAProgramBool.programEq literal (A161Low4FixedFold.checked.out)=true:=by
 unfold A161Low4FixedFold.checked
 exact ECDSAAdd.Entrant.D1Opt.get_of_elim A161Low4Facts.match99 A161Low4Facts.compiled99
theorem literal_eq:literal=A161Low4FixedFold.checked.out:=ParkAProgramBool.programEq_sound _ _ literal_verified
theorem cert:Cert known0 (A161Low4FixedFold.checked.out) body known54 8:=
 Eq.mp (congrArg (fun P:Program=>Cert known0 P body known54 8) literal_eq) join0_54Opt.proof

end ECDSAAdd.Entrant.KnownAMidStaged

end

-- Verified component ReorderedAccMod
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAcc
open Arithmetic Acc
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
structure FitsLen (Z bank : List Wire) (w : Nat) (f : MeasuredSquareFold) : Prop where
  len : f.src.length+f.shift≤w
  shiftLt : f.shift<w
  zpad : w-f.shift-f.src.length≤Z.length
  bankLen : w-f.shift-1≤bank.length

structure Fits (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold) : Prop
    extends FitsLen Z bank w f where
  nd : (cin::(f.src++acc++Z++bank)).Nodup

theorem fits_lengths (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : FitsLen Z bank w f) :
    (tx Z w f).length=(ty acc f).length ∧ (tc bank w f).length+1=(ty acc f).length ∧
      (ty acc f).length=w-f.shift := by
  have sl := hf.shiftLt; have l := hf.len; have z := hf.zpad; have b := hf.bankLen
  simp only [tx,ty,tc,List.length_append,List.length_take,List.length_drop,hacc]
  rw [Nat.min_eq_left z,Nat.min_eq_left b]
  refine ⟨?_,?_,?_⟩
  · generalize f.src.length=k at l ⊢
    generalize f.shift=j at l sl ⊢
    omega
  · generalize f.shift=j at l sl ⊢
    omega
  · trivial

theorem fits_nodup (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hf : Fits acc Z bank cin w f) :
    (cin::(tx Z w f++ty acc f++tc bank w f)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hf.nd q
  have a := (List.take_sublist (w-f.shift-f.src.length) Z).count_le q
  have b := (List.drop_sublist f.shift acc).count_le q
  have c := (List.take_sublist (w-f.shift-1) bank).count_le q
  simp only [tx,ty,tc,List.count_cons,List.count_append] at h a b c ⊢
  omega

theorem op_wires (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) :
    wires (op acc Z bank cin w neg f)=(cin::(tx Z w f++ty acc f++tc bank w f)).toFinset := by
  have L := fits_lengths acc Z bank cin w f hacc hf.toFitsLen
  cases neg
  · simp only [op,Bool.false_eq_true,if_false]
    exact addInPlace_wires _ _ _ _ L.1 L.2.1
  · simp only [op,if_true,subInPlace,wires_append,notRegister_wires,addInPlace_wires _ _ _ _ L.1 L.2.1]
    ext q
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto


def valueMod(V H w sh:Nat)(neg:Bool):Nat:=
 V%2^sh+2^sh*((if neg then V/2^sh+2^(w-sh)-H else H+V/2^sh)%2^(w-sh))

theorem op_mod_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) (base : BasisState)
    (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (neg : Bool) (V : Nat)
    :
    Triple (SquareFrame acc base V) (op acc Z bank cin w neg f)
      (SquareFrame acc base (valueMod V (regValue f.src base) w f.shift neg)) := by
  intro s m hs
  have L := fits_lengths acc Z bank cin w f hacc hf.toFitsLen
  have nd := fits_nodup acc Z bank cin w f hf
  have hnd := List.nodup_iff_count_le_one.mp hf.nd
  have away (q : Wire) (hq : q∈f.src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h := hnd q
    have a := List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b := List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (q : Wire) (hq : q∈f.src++Z++bank ∨ q=cin) : s.basis q=base q := hs.2 q (away q hq)
  let T := regValue f.src base
  let x := tx Z w f
  let y := ty acc f
  let c := tc bank w f
  have xv : regValue x s.basis=T := by
    have zero : regValue (Z.take (w-f.shift-f.src.length)) s.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have hq' := List.mem_of_mem_take hq
      exact (same q (Or.inl (by simp [hq']))).trans (hz q hq')
    have src : regValue f.src s.basis=T :=
      regValue_congr _ _ _ (fun q hq => same q (Or.inl (by simp [hq])))
    simp only [x,tx,regValue_append,zero,src,Nat.mul_zero,Nat.add_zero]
  have cv : regValue c s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have hq' := List.mem_of_mem_take hq
    exact (same q (Or.inl (by simp [hq']))).trans (hb q hq')
  have iv : s.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have accNd : acc.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q
    have h := hnd q
    simp only [List.count_cons,List.count_append] at h
    split at h <;> omega
  have dis := List.disjoint_take_drop accNd (show f.shift≤f.shift by omega)
  have shiftLe : f.shift≤acc.length := by have := hf.len; omega
  have split (t : BasisState) : regValue acc t=regValue (acc.take f.shift) t+2^f.shift*regValue y t := by
    have h := regValue_append (acc.take f.shift) (acc.drop f.shift) t
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left shiftLe] at h
    exact h
  have lowLt : regValue (acc.take f.shift) s.basis<2^f.shift := by
    have h := regValue_lt (acc.take f.shift) s.basis
    rwa [List.length_take,Nat.min_eq_left shiftLe] at h
  have yLt : regValue y s.basis<2^(w-f.shift) := by
    have h := regValue_lt y s.basis; rwa [L.2.2] at h
  have vsplit := split s.basis
  rw [hs.1] at vsplit
  -- the operation's own spec: values of x, y, cin, carry
  have post : (run (op acc Z bank cin w neg f) m s).phase=s.phase ∧
      regValue x (run (op acc Z bank cin w neg f) m s).basis=T ∧
      regValue y (run (op acc Z bank cin w neg f) m s).basis=
        (if neg then (regValue y s.basis+2^y.length-T)%2^y.length
          else (T+regValue y s.basis)%2^y.length) ∧
      (run (op acc Z bank cin w neg f) m s).basis cin=false ∧
      regValue c (run (op acc Z bank cin w neg f) m s).basis=0 := by
    cases neg
    · have h := addInPlace_spec x y c cin nd L.1 L.2.1 T (regValue y s.basis) false s m
        ⟨⟨⟨xv,rfl⟩,iv⟩,cv⟩
      simp only [Holds.holds,Bool.toNat_false,Nat.add_zero] at h
      simp only [op,Bool.false_eq_true,if_false]
      exact ⟨h.1,h.2.1.1.1,h.2.1.1.2,h.2.1.2,h.2.2⟩
    · have h := subInPlace_spec x y c cin nd L.1 L.2.1 T (regValue y s.basis) s m
        ⟨⟨⟨xv,rfl⟩,iv⟩,cv⟩
      simp only [Holds.holds] at h
      simp only [op,if_true]
      exact ⟨h.1,h.2.1.1.1,h.2.1.1.2,h.2.1.2,h.2.2⟩
  let r := run (op acc Z bank cin w neg f) m s
  have frame (q : Wire) (hq : q∉y) : r.basis q=s.basis q := by
    by_cases hx : q∈x
    · exact (regValue_eq_iff x r.basis s.basis).mp (post.2.1.trans xv.symm) q hx
    by_cases hc : q∈c
    · exact ((regValue_zero _ _).mp post.2.2.2.2 q hc).trans ((regValue_zero _ _).mp cv q hc).symm
    by_cases hi' : q=cin
    · subst q; exact post.2.2.2.1.trans iv.symm
    apply run_preserves_outside
    rw [op_wires acc Z bank cin w neg f hacc hf]
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  have lowSame : regValue (acc.take f.shift) r.basis=regValue (acc.take f.shift) s.basis :=
    regValue_congr _ _ _ (fun q hq => frame q (fun hy => List.disjoint_left.mp dis hq hy))
  refine ⟨post.1,?_,?_⟩
  · rw [split r.basis,lowSame,post.2.2.1,L.2.2]
    have vl:regValue (acc.take f.shift) s.basis=V%2^f.shift:=by
      rw [vsplit,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lowLt]
    have vy:regValue y s.basis=V/2^f.shift:=by
      rw [vsplit,Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt lowLt,zero_add]
    simp only [valueMod,T,vl,vy]
    cases neg <;> rfl
  · intro q hq
    have hy : q∉y := fun h => hq (List.mem_of_mem_drop h)
    exact (frame q hy).trans (hs.2 q hq)



end ECDSAAdd.Entrant.ReorderedAcc

end

-- Verified component ReorderedAccPrefix
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAcc
open Arithmetic Acc
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem fits_prefix (acc Z bank : List Wire) (cin : Wire) (w n : Nat)
    (f : MeasuredSquareFold) (hn : n≤w) (hf : Acc.Fits acc Z bank cin w f)
    (hlen : f.src.length+f.shift≤n) (hsh:f.shift<n) : Fits (acc.take n) Z bank cin n f := by
  refine ⟨⟨hlen,hsh,?_,?_⟩,?_⟩
  · have h := hf.zpad
    omega
  · have h := hf.bankLen
    omega
  · apply List.nodup_iff_count_le_one.mpr
    intro q
    have h := List.nodup_iff_count_le_one.mp hf.nd q
    have take := (List.take_sublist n acc).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega

/-- Run a short operation inside a full accumulator frame. The high bits
stay zero; the original frame base may have arbitrary accumulator bits. -/
theorem op_mod_prefix_triple (acc Z bank : List Wire) (cin : Wire) (w n : Nat)
    (f : MeasuredSquareFold) (hacc : acc.length=w) (hn : n≤w)
    (hf : Acc.Fits acc Z bank cin w f) (hlen : f.src.length+f.shift≤n) (hsh:f.shift<n)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) (neg : Bool) (V : Nat) (hV : V<2^n)
    :
    Triple (SquareFrame acc base V) (op (acc.take n) Z bank cin n neg f)
      (SquareFrame acc base (valueMod V (regValue f.src base) n f.shift neg)) := by
  intro s m hs
  have hnd := List.nodup_iff_count_le_one.mp hf.nd
  have away (q : Wire) (hq : q∈f.src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h := hnd q
    have a := List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b := List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (q : Wire) (hq : q∈f.src++Z++bank ∨ q=cin) : s.basis q=base q :=
    hs.2 q (away q hq)
  have source : regValue f.src s.basis=regValue f.src base :=
    regValue_congr _ _ _ (fun q hq => same q (Or.inl (by simp [hq])))
  have pref := regValue_take_drop_of_lt acc n V s.basis (by omega) hs.1 hV
  have len : (acc.take n).length=n := by simp [List.length_take,hacc,Nat.min_eq_left hn]
  have small := op_mod_triple (acc.take n) Z bank cin n f len
    (fits_prefix acc Z bank cin w n f hn hf hlen hsh) s.basis
    (fun q hq => (same q (Or.inl (by simp [hq]))).trans (hz q hq))
    (fun q hq => (same q (Or.inl (by simp [hq]))).trans (hb q hq))
    ((same cin (Or.inr rfl)).trans hi) neg V
    s m ⟨pref.1,fun _ _ => rfl⟩
  have value:valueMod V (regValue f.src s.basis) n f.shift neg=
      valueMod V (regValue f.src base) n f.shift neg:=by rw [source]
  rw [value] at small
  have ndacc : acc.Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have h := hnd q
    simp only [List.count_cons,List.count_append] at h
    split at h <;> omega
  have dis := List.disjoint_take_drop ndacc (show n≤n by omega)
  have high : regValue (acc.drop n)
      (run (op (acc.take n) Z bank cin n neg f) m s).basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) pref.2
    intro q hq
    exact small.2.2 q (fun low => List.disjoint_left.mp dis low hq)
  refine ⟨small.1,?_,?_⟩
  · have split := regValue_append (acc.take n) (acc.drop n)
      (run (op (acc.take n) Z bank cin n neg f) m s).basis
    rw [List.take_append_drop,small.2.1,high,Nat.mul_zero,Nat.add_zero] at split
    exact split
  · intro q hq
    exact (small.2.2 q (fun h => hq (List.mem_of_mem_take h))).trans (hs.2 q hq)












end ECDSAAdd.Entrant.ReorderedAcc

end

-- Verified component ReorderedCPre
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCPre
open Arithmetic
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

theorem sub_value(H:Nat)(hH:H<2^130):
 ReorderedAcc.valueMod (16*H) H 140 6 true=(2^140-48*H)%2^140:=by
 simp only [ReorderedAcc.valueMod,if_true]
 norm_num at hH ⊢
 omega

theorem add_value(H:Nat)(hH:H<2^130):
 ReorderedAcc.valueMod ((2^140-48*H)%2^140) H 140 10 false=976*H:=by
 by_cases hz:H=0
 · subst H
   norm_num [ReorderedAcc.valueMod]
 have ht:2^140-48*H<2^140:=by omega
 rw [Nat.mod_eq_of_lt ht]
 simp only [ReorderedAcc.valueMod,Bool.false_eq_true,if_false]
 norm_num at hH ⊢
 omega

def pre(acc Z bank:List Wire)(cin:Wire)(src:List Wire):Program:=
 Acc.seedOp acc Z 163 (Acc.earlyTerm src false 4)++
 Acc.op (acc.take 140) Z bank cin 140 true (Acc.earlyTerm src true 6)++
 Acc.op (acc.take 140) Z bank cin 140 false (Acc.earlyTerm src false 10)

theorem pre_triple(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=163)(hsrc:src.length≤130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (base:BasisState)(hz:∀q∈Z,base q=false)(hb:∀q∈bank,base q=false)(hi:base cin=false):
 Triple (SquareFrame acc base 0) (pre acc Z bank cin src)
  (SquareFrame acc base (976*regValue src base)):=by
 have tm:=C163NarrowAcc.terms_mem src
 have hf4:=hf _ tm.1
 have hf6:=hf _ tm.2.2.1
 have hf10:=hf _ tm.2.1
 let H:=regValue src base
 have hH:H<2^130:=lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) hsrc)
 have seed:=Acc.seed_triple acc Z bank cin 163 (Acc.earlyTerm src false 4) hacc hf4 base hz
  0 (16*H) (Or.inl (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
 have sub:=ReorderedAcc.op_mod_prefix_triple acc Z bank cin 163 140 (Acc.earlyTerm src true 6)
  hacc (by decide) hf6 (by simp only [Acc.earlyTerm];omega) (by norm_num [Acc.earlyTerm]) base hz hb hi true (16*H)
  (by norm_num at hH ⊢;omega)
 change Triple _ _ (SquareFrame acc base (ReorderedAcc.valueMod (16*H) H 140 6 true)) at sub
 rw [sub_value H hH] at sub
 have add:=ReorderedAcc.op_mod_prefix_triple acc Z bank cin 163 140 (Acc.earlyTerm src false 10)
  hacc (by decide) hf10 (by simp only [Acc.earlyTerm];omega) (by norm_num [Acc.earlyTerm]) base hz hb hi false ((2^140-48*H)%2^140)
  (Nat.mod_lt _ (by positivity))
 change Triple _ _ (SquareFrame acc base (ReorderedAcc.valueMod ((2^140-48*H)%2^140) H 140 10 false)) at add
 rw [add_value H hH] at add
 exact (seed.seq sub).seq add

end ECDSAAdd.Entrant.ReorderedCPre

end

-- Verified component ReorderedCHead
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCHead
open Arithmetic ReorderedCPre
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
def head(acc Z bank:List Wire)(cin:Wire)(src:List Wire):Program:=
 Acc.seedOp acc Z 163 (Acc.earlyTerm src false 4)++
 Acc.op (acc.take 140) Z bank cin 140 true (Acc.earlyTerm src true 6)

theorem head_triple(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=163)(hsrc:src.length≤130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (base:BasisState)(hz:∀q∈Z,base q=false)(hb:∀q∈bank,base q=false)(hi:base cin=false):
 Triple (SquareFrame acc base 0) (head acc Z bank cin src)
  (SquareFrame acc base ((2^140-48*regValue src base)%2^140)):=by
 have tm:=C163NarrowAcc.terms_mem src
 have hf4:=hf _ tm.1
 have hf6:=hf _ tm.2.2.1
 have hf10:=hf _ tm.2.1
 let H:=regValue src base
 have hH:H<2^130:=lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) hsrc)
 have seed:=Acc.seed_triple acc Z bank cin 163 (Acc.earlyTerm src false 4) hacc hf4 base hz
  0 (16*H) (Or.inl (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
 have sub:=ReorderedAcc.op_mod_prefix_triple acc Z bank cin 163 140 (Acc.earlyTerm src true 6)
  hacc (by decide) hf6 (by simp only [Acc.earlyTerm];omega) (by norm_num [Acc.earlyTerm]) base hz hb hi true (16*H)
  (by norm_num at hH ⊢;omega)
 change Triple _ _ (SquareFrame acc base (ReorderedAcc.valueMod (16*H) H 140 6 true)) at sub
 rw [sub_value H hH] at sub
 exact seed.seq sub

end ECDSAAdd.Entrant.ReorderedCHead

end

-- Verified component ReorderedCClear
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCClear
open Arithmetic
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

theorem sub_value(H:Nat)(hH:H<2^130):
 ReorderedAcc.valueMod (976*H) H 140 10 true=(2^140-48*H)%2^140:=by
 simp only [ReorderedAcc.valueMod,if_true]
 norm_num at hH ⊢
 omega

theorem add_value(H:Nat)(hH:H<2^130):
 ReorderedAcc.valueMod ((2^140-48*H)%2^140) H 140 6 false=16*H:=by
 by_cases hz:H=0
 · subst H
   norm_num [ReorderedAcc.valueMod]
 have ht:2^140-48*H<2^140:=by omega
 rw [Nat.mod_eq_of_lt ht]
 simp only [ReorderedAcc.valueMod,Bool.false_eq_true,if_false]
 norm_num at hH ⊢
 omega
































end ECDSAAdd.Entrant.ReorderedCClear

end

-- Verified component ReorderedKnownTail
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedKnownTail
open Arithmetic Arithmetic.KnownOutputAdder MixedLiteralAdderDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

def zero:MappedBit:=⟨none,false⟩
def desired(src:List Wire):List MappedBit:=mappedRead (src.drop 2) false++List.replicate 6 zero
def program(src Z ys carry:List Wire)(cin:Wire):Program:=
 KnownOutputAdder.program (mappedRead (src++Z.take 4) false) ys (desired src) carry cin

theorem arithmeticN(N H:Nat)(hN:0<N)(hH:H<N):
 (H+((1024*N-48*H)%(1024*N))/64)%(16*N)=H/4:=by
 by_cases hz:H=0
 · subst H
   simp
 have ht:1024*N-48*H<1024*N:=by omega
 rw [Nat.mod_eq_of_lt ht]
 have he:H+(1024*N-48*H)/64=16*N+H/4:=by omega
 rw [he]
 have hi:H/4<16*N:=by omega
 simp only [Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_eq_of_lt hi]

theorem arithmetic(n H:Nat)(hH:H<2^n):
 (H+((2^(n+10)-48*H)%2^(n+10))/64)%2^(n+4)=H/4:=by
 have h:=arithmeticN (2^n) H (by positivity) hH
 simpa only [Nat.pow_add,show 2^10=1024 by decide,show 2^4=16 by decide,Nat.mul_comm] using h

theorem desired_length(src:List Wire)(hs:2≤src.length):(desired src).length=src.length+4:=by
 simp only [desired,List.length_append,mappedRead,List.length_map,List.length_drop,List.length_replicate]
 omega

theorem desired_value(src:List Wire)(hs:2≤src.length)(s:BasisState):mappedValue (desired src) s=regValue src s/4:=by
 rw [desired,mappedValue_append,mappedRead_value,CuccaroStreamedSquareWideLayout.regValue_drop_div src 2 hs]
 norm_num [List.replicate_succ,mappedValue,zero,MappedBit.value]

theorem desired_wires(src:List Wire):mappedWires (desired src)=src.drop 2:=by
 simp only [desired,mappedWires,List.flatMap_append]
 rw [show (mappedRead (src.drop 2) false).flatMap (fun b=>b.wire.toList)=src.drop 2 from mappedRead_wires _ _]
 simp [zero,List.flatMap_replicate]

theorem run_eq_add(src Z ys carry:List Wire)(cin:Wire)(hs:2≤src.length)(hzl:4≤Z.length)
 (hy:ys.length=src.length+4)(hc:carry.length+1=ys.length)
 (hn:(cin::((src++Z.take 4)++ys++carry)).Nodup)(s:State)(m:List Bool)
 (hz:∀q∈Z,s.basis q=false)(hcarry:∀q∈carry,s.basis q=false)(hcin:s.basis cin=false)
 (H:Nat)(hH:H<2^src.length)(hsrc:regValue src s.basis=H)
 (hys:regValue ys s.basis=((2^(src.length+10)-48*H)%2^(src.length+10))/64):
 run (program src Z ys carry cin) m s=run (addInPlace (src++Z.take 4) ys carry cin) m s:=by
 have geo:=read_geometry (src++Z.take 4) ys carry cin hn
 have zv:regValue (Z.take 4) s.basis=0:=(regValue_zero _ _).mpr (fun q hq=>hz q (List.mem_of_mem_take hq))
 have sv:mappedValue (mappedRead (src++Z.take 4) false) s.basis=H:=by
  rw [mappedRead_value,regValue_append,hsrc,zv,Nat.mul_zero,Nat.add_zero]
 have hl:(mappedRead (src++Z.take 4) false).length=ys.length:=by simp only [mappedRead,List.length_map,List.length_append,List.length_take,hy,Nat.min_eq_left hzl]
 have hd:(desired src).length=ys.length:=(desired_length src hs).trans hy.symm
 have dv:mappedValue (desired src) s.basis=H/4:=(desired_value src hs s.basis).trans (congrArg (fun x:Nat=>x/4) hsrc)
 have ready:Ready (mappedRead (src++Z.take 4) false) (desired src) ys (s.basis cin) s.basis:=by
  apply ready_of_value _ _ _ _ _ hl hd
  rw [dv,sv,hys,hcin,Bool.toNat_false,Nat.add_zero,hy]
  exact (arithmetic src.length H hH).symm
 have eq:=program_eq_mappedAdd (mappedRead (src++Z.take 4) false) (desired src) ys carry cin geo.1
  (by rw [mappedRead_wires];exact geo.2)
  (by rw [desired_wires];intro q hq;exact geo.2 q (List.mem_append_left _ (List.mem_of_mem_drop hq)))
  hl hd hc s m hcarry ready
 unfold program
 rw [eq,read_add_eq]

theorem counts(src Z ys carry:List Wire)(cin:Wire)(hs:2≤src.length)(hzl:4≤Z.length)
 (hy:ys.length=src.length+4)(hc:carry.length+1=ys.length):
 toffoliCount (program src Z ys carry cin)=0 ∧ measurementCount (program src Z ys carry cin)=ys.length-1:=by
 apply KnownOutputAdder.program_counts
 · simp only [mappedRead,List.length_map,List.length_append,List.length_take,hy,Nat.min_eq_left hzl]
 · exact (desired_length src hs).trans hy.symm
 · exact hc

end ECDSAAdd.Entrant.ReorderedKnownTail

end

-- Verified component ReorderedCarryDual
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCarryDual
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000















end ECDSAAdd.Entrant.ReorderedCarryDual

end

-- Verified component ReorderedGenericCache
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedGenericCache
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop MixedLiteralAdderDevelop
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def cachedAdd (k : Nat) (xs ys cs hs : List Wire) (cin : Wire) : Program :=
 carryPrefix (4+k) xs ys cs cin ++ copyMany ((cs.drop 4).take k) hs ++
 mappedSuffix (4+k) xs ys cs cin

theorem cachedAdd_frame (k : Nat) (xs ys cs hs : List Wire) (cin : Wire)
 (hx : k+6≤xs.length) (hy : k+6≤ys.length) (hc : k+4≤cs.length)
 (nd : hs.Nodup) (fresh : ∀h∈hs,h∉cs)
 (off : ∀h∈hs,h∉wires (mappedAdd (mappedRead xs false) ys cs cin))
 (s : State) (m : List Bool) (zero : ∀h∈hs,s.basis h=false) :
 run (cachedAdd k xs ys cs hs cin) m s =
 scatterState hs (((cs.drop 4).take k).map
   (run (carryPrefix (4+k) xs ys cs cin) [] s).basis)
   (run (mappedAdd (mappedRead xs false) ys cs cin) m s) := by
 have split := mappedAdd_split (4+k) xs ys cs cin (by omega) (by omega) (by omega)
 have op : ∀h∈hs,h∉wires (carryPrefix (4+k) xs ys cs cin) := by
  intro h hh bad
  apply off h hh
  rw [split,wires_append]
  exact Finset.mem_union_left _ bad
 have ot : ∀h∈hs,h∉wires (mappedSuffix (4+k) xs ys cs cin) := by
  intro h hh bad
  apply off h hh
  rw [split,wires_append]
  exact Finset.mem_union_right _ bad
 have ft : ∀h∈hs,h∉(cs.drop 4).take k := by
  intro h hh bad
  exact fresh h hh (List.mem_of_mem_drop (List.mem_of_mem_take bad))
 have eq := insertMany_frame (carryPrefix (4+k) xs ys cs cin)
  (mappedSuffix (4+k) xs ys cs cin) ((cs.drop 4).take k) hs s m nd ft op ot zero
 simpa only [cachedAdd,carryPrefix_measurements,List.take_zero,←split,List.append_assoc] using eq

def consumedAdd (k : Nat) (xs ys cs hs : List Wire) (cin : Wire) : Program :=
 carryPrefix 4 xs ys cs cin ++ moveMany ((cs.drop 4).take k) hs ++
 mappedSuffix (4+k) xs ys cs cin

theorem consumedAdd_frame (k : Nat) (xs ys cs hs : List Wire) (cin : Wire)
 (hx : k+6≤xs.length) (hy : k+6≤ys.length) (hc : k+4≤cs.length)
 (hn : (cin::(xs++ys++cs)).Nodup) (nd : hs.Nodup) (len : hs.length=k)
 (fresh : ∀h∈hs,h∉(cs.drop 4).take k)
 (off : ∀h∈hs,h∉wires (mappedSuffix (4+k) xs ys cs cin))
 (s : State) (m : List Bool)
 (zero : ∀x∈(cs.drop 4).take k,(run (carryPrefix 4 xs ys cs cin) [] s).basis x=false)
 (saved : hs.map (run (carryPrefix 4 xs ys cs cin) [] s).basis =
  ((cs.drop 4).take k).map (run (prefixAfter 4 k xs ys cs cin) []
    (run (carryPrefix 4 xs ys cs cin) [] s)).basis) :
 run (consumedAdd k xs ys cs hs cin) m s =
 scatterState hs (List.replicate hs.length false)
   (run (mappedAdd (mappedRead xs false) ys cs cin) m s) := by
 have layout := layout_after 4 xs ys cs cin (by omega) (by omega) (by omega) hn
 have mv := moveMany_prefix k (xs.drop 4) (ys.drop 4) (cs.drop 4) hs
  (lastCarry 4 cs cin) (run (carryPrefix 4 xs ys cs cin) [] s) []
  (by simp only [List.length_drop];omega) len layout nd fresh zero saved
 have split := mappedAdd_split (4+k) xs ys cs cin (by omega) (by omega) (by omega)
 rw [prefix_compose 4 k xs ys cs cin (by omega) (by omega) (by omega)] at split
 simp only [consumedAdd,split,List.append_assoc,run_append,carryPrefix_measurements,
  (moveMany_counts ((cs.drop 4).take k) hs).2.1,List.take_zero,List.drop_zero]
 rw [mv,run_scatter _ hs _ _ _ off]

theorem cached_context_frame (pre post : Program) (k : Nat) (xs ys cs hs : List Wire) (cin : Wire)
 (hx : k+6≤xs.length) (hy : k+6≤ys.length) (hc : k+4≤cs.length)
 (nd : hs.Nodup) (fresh : ∀h∈hs,h∉cs)
 (off : ∀h∈hs,h∉wires (pre++mappedAdd (mappedRead xs false) ys cs cin++post))
 (s : State) (m : List Bool) (zero : ∀h∈hs,s.basis h=false) :
 run (pre++cachedAdd k xs ys cs hs cin++post) m s =
 scatterState hs (((cs.drop 4).take k).map
   (run (pre++carryPrefix (4+k) xs ys cs cin)
     (m.take (measurementCount (pre++carryPrefix (4+k) xs ys cs cin))) s).basis)
   (run (pre++mappedAdd (mappedRead xs false) ys cs cin++post) m s) := by
 have split := mappedAdd_split (4+k) xs ys cs cin (by omega) (by omega) (by omega)
 have eq : pre++mappedAdd (mappedRead xs false) ys cs cin++post =
   (pre++carryPrefix (4+k) xs ys cs cin)++(mappedSuffix (4+k) xs ys cs cin++post) := by
  rw [split]
  simp only [List.append_assoc]
 have op : ∀h∈hs,h∉wires (pre++carryPrefix (4+k) xs ys cs cin) := by
  intro h hh bad
  apply off h hh
  rw [eq,wires_append]
  exact Finset.mem_union_left _ bad
 have ot : ∀h∈hs,h∉wires (mappedSuffix (4+k) xs ys cs cin++post) := by
  intro h hh bad
  apply off h hh
  rw [eq,wires_append]
  exact Finset.mem_union_right _ bad
 have ft : ∀h∈hs,h∉(cs.drop 4).take k := by
  intro h hh bad
  exact fresh h hh (List.mem_of_mem_drop (List.mem_of_mem_take bad))
 have frame := insertMany_frame (pre++carryPrefix (4+k) xs ys cs cin)
  (mappedSuffix (4+k) xs ys cs cin++post) ((cs.drop 4).take k) hs s m nd ft op ot zero
 simpa only [cachedAdd,eq,List.append_assoc] using frame

theorem count_balance (k : Nat) (xs ys cs hs : List Wire) (cin : Wire)
 (hx : k+6≤xs.length) (hy : k+6≤ys.length) (hc : k+4≤cs.length) :
 toffoliCount (cachedAdd k xs ys cs hs cin) =
   toffoliCount (mappedAdd (mappedRead xs false) ys cs cin) ∧
 measurementCount (cachedAdd k xs ys cs hs cin) =
   measurementCount (mappedAdd (mappedRead xs false) ys cs cin) ∧
 toffoliCount (consumedAdd k xs ys cs hs cin)+k =
   toffoliCount (mappedAdd (mappedRead xs false) ys cs cin) ∧
 measurementCount (consumedAdd k xs ys cs hs cin) =
   measurementCount (mappedAdd (mappedRead xs false) ys cs cin) := by
 have split := mappedAdd_split (4+k) xs ys cs cin (by omega) (by omega) (by omega)
 have tf := carryPrefix_T (4+k) xs ys cs cin (by omega) (by omega) (by omega)
 have t4 := carryPrefix_T 4 xs ys cs cin (by omega) (by omega) (by omega)
 have cp := copyMany_counts ((cs.drop 4).take k) hs
 have mv := moveMany_counts ((cs.drop 4).take k) hs
 simp only [cachedAdd,consumedAdd,split,toffoliCount_append,measurementCount_append,
  tf,t4,cp.1,cp.2,mv.1,mv.2.1,carryPrefix_measurements]
 simp [Nat.add_assoc,Nat.add_comm]





end ECDSAAdd.Entrant.ReorderedGenericCache

end

-- Verified component ReorderedCarryValues
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCarryValues
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000



























































end ECDSAAdd.Entrant.ReorderedCarryValues

end

-- Verified component ReorderedCacheArithmetic
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCacheArithmetic
set_option autoImplicit false

set_option maxHeartbeats 10000000

theorem high_add (M H : Nat) (hM : 0<M) (hH : H<M) :
 (H+((1024*M-48*H)%(1024*M))/1024)%M=976*H/1024 := by
 by_cases hz:H=0
 · subst H
   simp
 have ht:1024*M-48*H<1024*M := by omega
 rw [Nat.mod_eq_of_lt ht]
 have he:H+(1024*M-48*H)/1024=M+976*H/1024 := by omega
 rw [he]
 have hi:976*H/1024<M := by omega
 simp only [Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_eq_of_lt hi]

theorem high_add_low (n j H : Nat) (hj : j≤n) (hH : H<2^n) :
 (H+((2^(n+10)-48*H)%2^(n+10))/1024)%2^j = (976*H/1024)%2^j := by
 have h:=high_add (2^n) H (by positivity) hH
 have hd:2^j∣2^n:=Nat.pow_dvd_pow 2 hj
 have eq:=congrArg (fun x:Nat=>x%2^j) h
 dsimp only at eq
 rw [Nat.mod_mod_of_dvd _ hd] at eq
 simpa only [Nat.pow_add,show 2^10=1024 by decide,Nat.mul_comm] using eq



end ECDSAAdd.Entrant.ReorderedCacheArithmetic

end

-- Verified component ReorderedCacheBits
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCacheBits
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop CuccaroStreamedSquareWideLayout
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def bit (n H C : Nat) : Bool := decide (C%2^n<H%2^n)

theorem bit_value (n H C : Nat) :
 (bit n H C).toNat=if C%2^n<H%2^n then 1 else 0 := by
 unfold bit
 split_ifs with h <;> simp [h]

theorem forward_known (j total : Nat) (xs ys cs : List Wire) (cin : Wire) (s : State)
 (hj : j+1≤total) (hx : total≤xs.length) (hy : total≤ys.length) (hc : total≤cs.length)
 (hn : (cin::(xs++ys++cs)).Nodup) (hz : ∀q∈cs,s.basis q=false) (hi : s.basis cin=false)
 (H Y C : Nat) (source : regValue xs s.basis=H) (target : regValue ys s.basis=Y)
 (hsum : (H+Y)%2^(j+1)=C%2^(j+1)) :
 (run (carryPrefix total xs ys cs cin) [] s).basis (cs.getD j 0)=bit (j+1) H C := by
 rw [prefix_earlier j total xs ys cs cin s hj hx hy hc hn]
 apply bool_nat_injective
 rw [prefix_value_reg j xs ys cs cin s [] (by omega) (by omega) (by omega) hn hz,
  regValue_take_mod xs (j+1) (by omega) s.basis,
  regValue_take_mod ys (j+1) (by omega) s.basis,source,target,hi,Bool.toNat_false,Nat.add_zero]
 have hm : 0<2^(j+1) := by positivity
 rw [←carry_same_mod (2^(j+1)) H Y (H+Y) hm rfl,hsum,
  borrow_value _ _ _ hm (Nat.mod_lt _ hm) (Nat.mod_lt _ hm),bit_value]

theorem inverse_known (j total : Nat) (xs ys cs : List Wire) (cin : Wire) (s : State)
 (hj : j+1≤total) (hx : total≤xs.length) (hy : total≤ys.length) (hc : total≤cs.length)
 (hn : (cin::(xs++ys++cs)).Nodup) (hz : ∀q∈cs,s.basis q=false) (hi : s.basis cin=false)
 (H C : Nat) (source : regValue xs s.basis=H) (target : regValue ys s.basis=C) :
 (run (subPreN total xs ys cs cin) [] s).basis (cs.getD j 0)=bit (j+1) H C := by
 rw [sub_earlier j total xs ys cs cin s hj hx hy hc hn]
 apply bool_nat_injective
 rw [subPre_value j xs ys cs cin (by omega) (by omega) (by omega) hn s hz hi,
  regValue_take_mod xs (j+1) (by omega) s.basis,
  regValue_take_mod ys (j+1) (by omega) s.basis,source,target]
 have hm : 0<2^(j+1) := by positivity
 rw [borrow_value _ _ _ hm (Nat.mod_lt _ hm) (Nat.mod_lt _ hm),bit_value]

def values (n k H C:Nat):List Bool:=(List.range k).map (fun i=>bit (n+i+1) H C)

theorem values_map (n k H C:Nat) (cs:List Wire) (f:Wire→Bool)
 (hc:n+k≤cs.length) (known:∀j,j<k→f (cs.getD (n+j) 0)=bit (n+j+1) H C):
 ((cs.drop n).take k).map f=values n k H C:=by
 apply List.ext_getElem
 · simp only[List.length_map,List.length_take,List.length_drop,values,List.length_range]
   omega
 · intro i _ h2
   have hi:i<k:=by simpa only[values,List.length_map,List.length_range]using h2
   have h:=known i hi
   rw[List.getD_eq_getElem cs 0 (by omega)]at h
   simpa only[List.getElem_map,List.getElem_take,List.getElem_drop,values,List.getElem_range]using h

theorem forward_values (n k H Y C:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hx:n+k≤xs.length) (hy:n+k≤ys.length) (hc:n+k≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false)
 (source:regValue xs s.basis=H) (target:regValue ys s.basis=Y)
 (hsum:∀j,j<k→(H+Y)%2^(n+j+1)=C%2^(n+j+1)):
 ((cs.drop n).take k).map (run (carryPrefix (n+k) xs ys cs cin) [] s).basis=values n k H C:=by
 apply values_map n k H C cs _ hc
 intro j hj
 exact forward_known (n+j) (n+k) xs ys cs cin s (by omega) hx hy hc hn hz hi H Y C source target (hsum j hj)

theorem inverse_values (n k H C:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hx:n+k≤xs.length) (hy:n+k≤ys.length) (hc:n+k≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false)
 (source:regValue xs s.basis=H) (target:regValue ys s.basis=C):
 ((cs.drop n).take k).map (run (subPreN (n+k) xs ys cs cin) [] s).basis=values n k H C:=by
 apply values_map n k H C cs _ hc
 intro j hj
 exact inverse_known (n+j) (n+k) xs ys cs cin s (by omega) hx hy hc hn hz hi H C source target





end ECDSAAdd.Entrant.ReorderedCacheBits

end

-- Verified component ReorderedCTail
section
open ECDSAAdd ECDSAAdd.Entrant
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReorderedCTail
open ReorderedKnownTail
open Arithmetic

def tail (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  program src Z ((acc.take 140).drop 6) (bank.take 133) cin

theorem tail_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length=130)
    (hf : Acc.Fits acc Z bank cin 163 (Acc.earlyTerm src true 6))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base ((2^140-48*regValue src base)%2^140)) (tail acc Z bank cin src)
      (SquareFrame acc base (16*regValue src base)) := by
  let f:=Acc.earlyTerm src true 6
  let H:=regValue src base
  have hH : H<2^130 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have old:=ReorderedAcc.op_mod_prefix_triple acc Z bank cin 163 140 f hacc (by decide) hf
    (by simp only [f,Acc.earlyTerm];omega) (by norm_num [f,Acc.earlyTerm]) base hz hb hi false ((2^140-48*H)%2^140)
    (Nat.mod_lt _ (by positivity))
  change Triple _ _ (SquareFrame acc base (ReorderedAcc.valueMod ((2^140-48*H)%2^140) H 140 6 false)) at old
  rw [ReorderedCClear.add_value H hH] at old
  have fit:=Acc.fits_prefix acc Z bank cin 163 140 f (by decide) hf (by simp [f,Acc.earlyTerm,hsrc])
  have len : (acc.take 140).length=140 := by simp [hacc]
  have rawEq : Acc.op (acc.take 140) Z bank cin 140 false f=
      addInPlace (src++Z.take 4) ((acc.take 140).drop 6) (bank.take 133) cin := by
    simp [Acc.op,Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc]
  intro s m hs
  have away (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h:=List.nodup_iff_count.mp hf.nd q
    have a:=List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b:=List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
      omega
  have same (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : s.basis q=base q := hs.2 q (away q hq)
  have pref:=regValue_take_drop_of_lt acc 140 ((2^140-48*H)%2^140) s.basis (by omega) hs.1 (Nat.mod_lt _ (by positivity))
  have sy : regValue ((acc.take 140).drop 6) s.basis=((2^140-48*H)%2^140)/64 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
    rfl
  have sh : regValue src s.basis=H := regValue_congr src _ base (fun q hq=>same q (Or.inl (by simp [hq])))
  have sz (q : Wire) (hq : q∈Z) : s.basis q=false :=
    (same q (Or.inl (by simp [hq]))).trans (hz q hq)
  have sb (q : Wire) (hq : q∈bank.take 133) : s.basis q=false :=
    (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
  have si : s.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have nd:=Acc.fits_nodup (acc.take 140) Z bank cin 140 f fit
  have nd' : (cin::((src++Z.take 4)++(acc.take 140).drop 6++bank.take 133)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd
  have zl : 4≤Z.length := by
    have h:=fit.zpad
    simpa [f,Acc.earlyTerm,hsrc] using h
  have bl : (bank.take 133).length=133 := by
    have h:=fit.bankLen
    simp only [f,Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have e:=run_eq_add src Z ((acc.take 140).drop 6) (bank.take 133) cin (by omega) zl
    (by simp [len,hsrc]) (by simp [bl,len]) nd' s m sz sb si H (by simpa only [hsrc] using hH) sh (by simpa only [hsrc] using sy)
  change run (tail acc Z bank cin src) m s=_ at e
  rw [e,←rawEq]
  exact old s m hs

end ECDSAAdd.Entrant.ReorderedCTail

end

-- Verified component ReorderedCPlain
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCPlain
open Arithmetic
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def build (acc Z bank:List Wire)(cin:Wire)(src:List Wire):Program:=
 ReorderedCPre.pre acc Z bank cin src++C163Carry.buildPost acc Z bank cin src

def unbuild (acc Z bank:List Wire)(cin:Wire)(src:List Wire):Program:=
 C163Carry.unbuildPre acc Z bank cin src++
 Acc.op (acc.take 140) Z bank cin 140 true (Acc.earlyTerm src false 10)++
 ReorderedCTail.tail acc Z bank cin src++Acc.seedOp acc Z 163 (Acc.earlyTerm src false 4)

theorem build_triple(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (base:BasisState)(hz:∀q∈Z,base q=false)(hb:∀q∈bank,base q=false)(hi:base cin=false):
 Triple (SquareFrame acc base 0) (build acc Z bank cin src)
  (SquareFrame acc base (4294968272*regValue src base)):=by
 let H:=regValue src base
 have hH:H<2^130:=by simpa only [H,hsrc] using regValue_lt src base
 have hf32:=hf _ (C163NarrowAcc.terms_mem src).2.2.2
 have pre:=ReorderedCPre.pre_triple acc Z bank cin src hacc (by omega) hf base hz hb hi
 have top : Triple (SquareFrame acc base (976*H))
     (Acc.op (acc.take 163) Z bank cin 163 false (Acc.earlyTerm src false 32))
     (SquareFrame acc base (4294968272*H)) := by
   have h := Acc.op_prefix_triple acc Z bank cin 163 163 (Acc.earlyTerm src false 32) hacc
     (by norm_num [Acc.earlyTerm]) hf32 (by simp only [Acc.earlyTerm]; omega) base hz hb hi false (976*H)
     (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm] at hH ⊢;dsimp [H] at *;omega)
   have value : Acc.step base false (976*H) (Acc.earlyTerm src false 32)=4294968272*H := by
     norm_num [Acc.step,Acc.earlyTerm]
     dsimp [H]
     omega
   rw [value] at h
   exact h
 exact pre.seq top

theorem unbuild_triple(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (base:BasisState)(hz:∀q∈Z,base q=false)(hb:∀q∈bank,base q=false)(hi:base cin=false):
 Triple (SquareFrame acc base (4294968272*regValue src base)) (unbuild acc Z bank cin src)
  (SquareFrame acc base 0):=by
 let H:=regValue src base
 have hH:H<2^130:=by simpa only [H,hsrc] using regValue_lt src base
 have tm:=C163NarrowAcc.terms_mem src
 have top:=C163Carry.unbuildPre_triple acc Z bank cin src hacc hsrc hf base hz hb hi
 have sub:=ReorderedAcc.op_mod_prefix_triple acc Z bank cin 163 140 (Acc.earlyTerm src false 10)
  hacc (by decide) (hf _ tm.2.1) (by simp only [Acc.earlyTerm];omega) (by norm_num [Acc.earlyTerm]) base hz hb hi true (976*H)
  (by norm_num at hH ⊢;omega)
 change Triple _ _ (SquareFrame acc base (ReorderedAcc.valueMod (976*H) H 140 10 true)) at sub
 rw [ReorderedCClear.sub_value H hH] at sub
 have tail:=ReorderedCTail.tail_triple acc Z bank cin src hacc hsrc (hf _ tm.2.2.1) base hz hb hi
 have seed:=Acc.seed_triple acc Z bank cin 163 (Acc.earlyTerm src false 4) hacc (hf _ tm.1) base hz
  (16*H) 0 (Or.inr (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
 exact ((top.seq sub).seq tail).seq seed



end ECDSAAdd.Entrant.ReorderedCPlain

end

-- Verified component ReorderedCBuild
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCBuild
open Arithmetic InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def build (k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire):Program:=
 ReorderedCHead.head acc Z bank cin src++
 ReorderedGenericCache.cachedAdd k src ((acc.take 140).drop 10) (bank.take 129) hs cin++
 C163Carry.buildPost acc Z bank cin src

theorem plain_split(acc Z bank:List Wire)(cin:Wire)(src:List Wire)(hsrc:src.length=130):
 ReorderedCPlain.build acc Z bank cin src=
 ReorderedCHead.head acc Z bank cin src++
 mappedAdd (mappedRead src false) ((acc.take 140).drop 10) (bank.take 129) cin++
 C163Carry.buildPost acc Z bank cin src:=by
 simp [ReorderedCPlain.build,ReorderedCPre.pre,ReorderedCHead.head,Acc.op,
  Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc,MixedLiteralAdderDevelop.read_add_eq,List.append_assoc]

theorem build_frame (k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0)
 (hk:k≤124)(ndhs:hs.Nodup)(fresh:∀h∈hs,h∉bank)
 (off:∀h∈hs,h∉wires (ReorderedCPlain.build acc Z bank cin src))
 (zero:∀h∈hs,s.basis h=false):
 run (build k acc Z bank cin src hs) m s=
 scatterState hs (ReorderedCacheBits.values 4 k (regValue src s.basis) (976*regValue src s.basis/1024))
  (run (ReorderedCPlain.build acc Z bank cin src) m s):=by
 let H:=regValue src s.basis
 let head:=ReorderedCHead.head acc Z bank cin src
 let t:=run head (m.take (measurementCount head)) s
 have hH:H<2^130:=by simpa only [H,hsrc] using regValue_lt src s.basis
 have hf10:=hf _ (C163NarrowAcc.terms_mem src).2.1
 have preFrame:=ReorderedCHead.head_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s
  (m.take (measurementCount head)) ⟨ha,fun _ _=>rfl⟩
 have away(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):q∉acc:=by
  intro bad
  have h:=List.nodup_iff_count_le_one.mp hf10.nd q
  have a:=List.count_pos_iff.mpr bad
  rcases hq with hq|rfl
  · have b:=List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
    split at h <;> omega
  · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
    omega
 have same(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):t.basis q=s.basis q:=preFrame.2.2 q (away q hq)
 have fit:=ReorderedAcc.fits_prefix acc Z bank cin 163 140 (Acc.earlyTerm src false 10)
  (by decide) hf10 (by simp [Acc.earlyTerm,hsrc]) (by norm_num [Acc.earlyTerm])
 have nd:(cin::(src++(acc.take 140).drop 10++bank.take 129)).Nodup:=by
  simpa [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using
   ReorderedAcc.fits_nodup (acc.take 140) Z bank cin 140 (Acc.earlyTerm src false 10) fit
 have len:(acc.take 140).length=140:=by simp [hacc]
 have bl:(bank.take 129).length=129:=by
  have h:=fit.bankLen
  simp only [Acc.earlyTerm] at h
  simp only [List.length_take]
  omega
 have pref:=regValue_take_drop_of_lt acc 140 ((2^140-48*H)%2^140) t.basis
  (by omega) preFrame.2.1 (Nat.mod_lt _ (by positivity))
 have sy:regValue ((acc.take 140).drop 10) t.basis=((2^140-48*H)%2^140)/1024:=by
  rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
  rfl
 have sh:regValue src t.basis=H:=regValue_congr _ _ _ (fun q hq=>same q (Or.inl (by simp [hq])))
 have sb:∀q∈bank.take 129,t.basis q=false:=by
  intro q hq
  exact (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
 have si:t.basis cin=false:=(same cin (Or.inr rfl)).trans hi
 have vals:=ReorderedCacheBits.forward_values 4 k H (((2^140-48*H)%2^140)/1024) (976*H/1024)
  src ((acc.take 140).drop 10) (bank.take 129) cin t
  (by omega) (by simp only [List.length_drop,len];omega) (by rw [bl];omega)
  nd sb si sh sy (fun j hj=>by
   simpa only [show 130+10=140 by decide] using
    ReorderedCacheArithmetic.high_add_low 130 (4+j+1) H (by omega) hH)
 have frame:=ReorderedGenericCache.cached_context_frame head (C163Carry.buildPost acc Z bank cin src)
  k src ((acc.take 140).drop 10) (bank.take 129) hs cin
  (by omega) (by simp only [List.length_drop,len];omega) (by rw [bl];omega) ndhs
  (fun h hh bad=>fresh h hh (List.mem_of_mem_take bad))
  (by simpa only [head,←plain_split acc Z bank cin src hsrc] using off) s m zero
 have valEq:(((bank.take 129).drop 4).take k).map
  (run (head++carryPrefix (4+k) src ((acc.take 140).drop 10) (bank.take 129) cin)
    (m.take (measurementCount (head++carryPrefix (4+k) src ((acc.take 140).drop 10) (bank.take 129) cin))) s).basis
  =ReorderedCacheBits.values 4 k H (976*H/1024):=by
  simpa only [run_append,measurementCount_append,carryPrefix_measurements,Nat.add_zero,
   List.take_take,Nat.min_self,List.drop_take_self,t] using vals
 rw [valEq] at frame
 simpa only [build,head,←plain_split acc Z bank cin src hsrc,H] using frame

theorem measurement_eq(k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire)
 (hacc:acc.length=163)(hsrc:src.length=130)(hbank:129≤bank.length)(hk:k≤124):
 measurementCount (build k acc Z bank cin src hs)=measurementCount (ReorderedCPlain.build acc Z bank cin src):=by
 have len:(acc.take 140).length=140:=by simp [hacc]
 have bl:(bank.take 129).length=129:=by simp [Nat.min_eq_left hbank]
 have counts:=ReorderedGenericCache.count_balance k src ((acc.take 140).drop 10) (bank.take 129) hs cin
  (by omega) (by simp only [List.length_drop,len];omega) (by rw [bl];omega)
 rw [plain_split acc Z bank cin src hsrc]
 simp only [build,measurementCount_append,counts.2.1]



end ECDSAAdd.Entrant.ReorderedCBuild

end

-- Verified component ReorderedConsumedSub
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedConsumedSub
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def plain (xs ys cs:List Wire)(cin:Wire):Program:=
 notRegister ys++mappedAdd (mappedRead xs false) ys cs cin++notRegister ys
def consumed (k:Nat)(xs ys cs hs:List Wire)(cin:Wire):Program:=
 notRegister ys++ReorderedGenericCache.consumedAdd k xs ys cs hs cin++notRegister ys

theorem frame(k:Nat)(xs ys cs hs:List Wire)(cin:Wire)
 (hx:k+6≤xs.length)(hy:k+6≤ys.length)(hc:k+4≤cs.length)
 (hxy:xs.length=ys.length)(hcs:cs.length+1=ys.length)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=k)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (s:State)(m:List Bool)(hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H C:Nat)(source:regValue xs s.basis=H)(target:regValue ys s.basis=C)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 k H C):
 run (consumed k xs ys cs hs cin) m s=
 scatterState hs (List.replicate hs.length false) (run (plain xs ys cs cin) m s):=by
 let u:=run (notRegister ys) [] s
 let v:=run (carryPrefix 4 xs ys cs cin) [] u
 have notM:measurementCount (notRegister ys)=0:=(notRegister_counts ys).2
 have offNot:∀h∈hs,h∉wires (notRegister ys):=by
  intro h hh bad
  rw [notRegister_wires] at bad
  exact fresh h hh (by simp only [List.mem_cons,List.mem_append];exact Or.inr (Or.inl (Or.inr (List.mem_toFinset.mp bad))))
 have untouched(h:Wire)(hh:h∈hs):v.basis h=s.basis h:=by
  have bankOff:h∉cs.take 4:=by
   intro bad
   exact fresh h hh (by simp only [List.mem_cons,List.mem_append];exact Or.inr (Or.inr (List.mem_of_mem_take bad)))
  exact (carryPrefix_preserves 4 xs ys cs cin hn u [] h bankOff).trans
   (run_preserves_outside (notRegister ys) [] s h (offNot h hh))
 have ndc:cs.Nodup:=(List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
 have dis:=List.disjoint_take_drop ndc (show 4≤4 by omega)
 have cys:∀q∈cs,q∉ys:=by
  intro q hq bad
  exact List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2
   (List.mem_append_right _ bad) hq
 have zero:∀q∈(cs.drop 4).take k,v.basis q=false:=by
  intro q hq
  have hdrop:=List.mem_of_mem_take hq
  have b:=List.mem_of_mem_drop hdrop
  have outside:q∉cs.take 4:=fun bad=>List.disjoint_left.mp dis bad hdrop
  change (run (carryPrefix 4 xs ys cs cin) [] u).basis q=false
  rw [carryPrefix_preserves 4 xs ys cs cin hn u [] q outside]
  change (run (notRegister ys) [] s).basis q=false
  rw [run_preserves_outside (notRegister ys) [] s q (by simpa only [notRegister_wires,List.mem_toFinset] using cys q b)]
  exact hz q b
 have vals:=ReorderedCacheBits.inverse_values 4 k H C xs ys cs cin s (by omega) (by omega) (by omega) hn hz hi source target
 have split:=prefix_compose 4 k xs ys cs cin (by omega) (by omega) (by omega)
 have valsAfter:((cs.drop 4).take k).map (run (prefixAfter 4 k xs ys cs cin) [] v).basis=
  ReorderedCacheBits.values 4 k H C:=by
  simpa only [subPreN,split,run_append,notM,carryPrefix_measurements,List.take_zero,List.drop_zero,u,v,prefixAfter] using vals
 have savedV:hs.map v.basis=((cs.drop 4).take k).map (run (prefixAfter 4 k xs ys cs cin) [] v).basis:=by
  have unchanged:hs.map v.basis=hs.map s.basis:=List.map_congr_left untouched
  exact unchanged.trans (saved.trans valsAfter.symm)
 have splitAdd:=mappedAdd_split (4+k) xs ys cs cin (by omega) (by omega) (by omega)
 have suffixOff:∀h∈hs,h∉wires (mappedSuffix (4+k) xs ys cs cin):=by
  intro h hh bad
  have all: h∉wires (mappedAdd (mappedRead xs false) ys cs cin):=by
   rw [MixedLiteralAdderDevelop.read_add_eq]
   intro hit
   rw [addInPlace_wires xs ys cs cin hxy hcs] at hit
   exact fresh h hh (List.mem_toFinset.mp hit)
  apply all
  rw [splitAdd,wires_append]
  exact Finset.mem_union_right _ bad
 have fr:=ReorderedGenericCache.consumedAdd_frame k xs ys cs hs cin hx hy hc hn nd len
  (fun h hh bad=>fresh h hh (by simp only [List.mem_cons,List.mem_append];exact Or.inr (Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take bad)))))
  suffixOff u (m.take (measurementCount (mappedAdd (mappedRead xs false) ys cs cin))) zero savedV
 have count:=ReorderedGenericCache.count_balance k xs ys cs hs cin hx hy hc
 simp only [consumed,plain,List.append_assoc,run_append,notM,count.2.2.2,List.take_zero,List.drop_zero]
 rw [fr,run_scatter _ hs _ _ _ offNot]

theorem measurement_eq(k:Nat)(xs ys cs hs:List Wire)(cin:Wire)
 (hx:k+6≤xs.length)(hy:k+6≤ys.length)(hc:k+4≤cs.length):
 measurementCount (consumed k xs ys cs hs cin)=measurementCount (plain xs ys cs cin):=by
 have h:=ReorderedGenericCache.count_balance k xs ys cs hs cin hx hy hc
 simp only [consumed,plain,measurementCount_append,h.2.2.2]

theorem replace_middle (before after old new:Program)(hs:List Wire)(values:List Bool)
 (s:State)(m:List Bool)(count:measurementCount new=measurementCount old)
 (off:∀h∈hs,h∉wires after)
 (eq:run new ((m.drop (measurementCount before)).take (measurementCount old))
   (run before (m.take (measurementCount before)) s)=
  scatterState hs values (run old ((m.drop (measurementCount before)).take (measurementCount old))
   (run before (m.take (measurementCount before)) s))):
 run (before++new++after) m s=scatterState hs values (run (before++old++after) m s):=by
 simp only [List.append_assoc,run_append,count]
 rw [eq,run_scatter _ hs _ _ _ off]



end ECDSAAdd.Entrant.ReorderedConsumedSub

end

-- Verified component ReorderedCUnbuild
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCUnbuild
open Arithmetic InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def after(acc Z bank:List Wire)(cin:Wire)(src:List Wire):Program:=
 ReorderedCTail.tail acc Z bank cin src++Acc.seedOp acc Z 163 (Acc.earlyTerm src false 4)
def unbuild(k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire):Program:=
 C163Carry.unbuildPre acc Z bank cin src++
 ReorderedConsumedSub.consumed k src ((acc.take 140).drop 10) (bank.take 129) hs cin++
 after acc Z bank cin src

theorem plain_split(acc Z bank:List Wire)(cin:Wire)(src:List Wire)(hsrc:src.length=130):
 ReorderedCPlain.unbuild acc Z bank cin src=
 C163Carry.unbuildPre acc Z bank cin src++
 ReorderedConsumedSub.plain src ((acc.take 140).drop 10) (bank.take 129) cin++
 after acc Z bank cin src:=by
 simp [ReorderedCPlain.unbuild,ReorderedConsumedSub.plain,after,Acc.op,
  Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc,MixedLiteralAdderDevelop.read_add_eq,subInPlace,List.append_assoc]

theorem unbuild_frame(k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=4294968272*regValue src s.basis)
 (hk:k≤124)(ndhs:hs.Nodup)(lenhs:hs.length=k)
 (fresh:∀h∈hs,h∉cin::(src++acc++Z++bank))
 (off:∀h∈hs,h∉wires (ReorderedCPlain.unbuild acc Z bank cin src))
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 k (regValue src s.basis) (976*regValue src s.basis/1024)):
 run (unbuild k acc Z bank cin src hs) m s=
 scatterState hs (List.replicate hs.length false) (run (ReorderedCPlain.unbuild acc Z bank cin src) m s):=by
 let H:=regValue src s.basis
 let pre:=C163Carry.unbuildPre acc Z bank cin src
 let t:=run pre (m.take (measurementCount pre)) s
 have hH:H<2^130:=by simpa only [H,hsrc] using regValue_lt src s.basis
 have hf10:=hf _ (C163NarrowAcc.terms_mem src).2.1
 have preFrame:=C163Carry.unbuildPre_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s
  (m.take (measurementCount pre)) ⟨ha,fun _ _=>rfl⟩
 have away(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):q∉acc:=by
  intro bad
  have h:=List.nodup_iff_count_le_one.mp hf10.nd q
  have a:=List.count_pos_iff.mpr bad
  rcases hq with hq|rfl
  · have b:=List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
    split at h <;> omega
  · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
    omega
 have same(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):t.basis q=s.basis q:=preFrame.2.2 q (away q hq)
 have fit:=ReorderedAcc.fits_prefix acc Z bank cin 163 140 (Acc.earlyTerm src false 10)
  (by decide) hf10 (by simp [Acc.earlyTerm,hsrc]) (by norm_num [Acc.earlyTerm])
 have nd:(cin::(src++(acc.take 140).drop 10++bank.take 129)).Nodup:=by
  simpa [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using
   ReorderedAcc.fits_nodup (acc.take 140) Z bank cin 140 (Acc.earlyTerm src false 10) fit
 have alen:(acc.take 140).length=140:=by simp [hacc]
 have bl:(bank.take 129).length=129:=by
  have h:=fit.bankLen
  simp only [Acc.earlyTerm] at h
  simp only [List.length_take]
  omega
 have pref:=regValue_take_drop_of_lt acc 140 (976*H) t.basis
  (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
 have sy:regValue ((acc.take 140).drop 10) t.basis=976*H/1024:=by
  rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [alen];decide),pref.1]
  rfl
 have sh:regValue src t.basis=H:=regValue_congr _ _ _ (fun q hq=>same q (Or.inl (by simp [hq])))
 have sb:∀q∈bank.take 129,t.basis q=false:=by
  intro q hq
  exact (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
 have si:t.basis cin=false:=(same cin (Or.inr rfl)).trans hi
 have savedT:hs.map t.basis=ReorderedCacheBits.values 4 k H (976*H/1024):=by
  rw [List.map_congr_left (fun h hh=>preFrame.2.2 h (by
   intro bad
   exact fresh h hh (by simp [bad])))]
  exact saved
 have freshSmall:∀h∈hs,h∉cin::(src++(acc.take 140).drop 10++bank.take 129):=by
  intro h hh bad
  apply fresh h hh
  simp only [List.mem_cons,List.mem_append] at bad ⊢
  rcases bad with a|((a|a)|a)
  · exact Or.inl a
  · exact Or.inr (Or.inl (Or.inl (Or.inl a)))
  · exact Or.inr (Or.inl (Or.inl (Or.inr (List.mem_of_mem_take (List.mem_of_mem_drop a)))))
  · exact Or.inr (Or.inr (List.mem_of_mem_take a))
 have fr:=ReorderedConsumedSub.frame k src ((acc.take 140).drop 10) (bank.take 129) hs cin
  (by omega) (by simp only [List.length_drop,alen];omega) (by rw [bl];omega)
  (by simp [hsrc,alen]) (by simp [bl,alen]) nd ndhs lenhs freshSmall t
  ((m.drop (measurementCount pre)).take (measurementCount
    (ReorderedConsumedSub.plain src ((acc.take 140).drop 10) (bank.take 129) cin)))
  sb si H (976*H/1024) sh sy savedT
 have count:=ReorderedConsumedSub.measurement_eq k src ((acc.take 140).drop 10) (bank.take 129) hs cin
  (by omega) (by simp only [List.length_drop,alen];omega) (by rw [bl];omega)
 have offAfter:∀h∈hs,h∉wires (after acc Z bank cin src):=by
  intro h hh bad
  apply off h hh
  rw [plain_split acc Z bank cin src hsrc,wires_append,wires_append]
  exact Finset.mem_union_right _ bad
 have result:=ReorderedConsumedSub.replace_middle pre (after acc Z bank cin src)
  (ReorderedConsumedSub.plain src ((acc.take 140).drop 10) (bank.take 129) cin)
  (ReorderedConsumedSub.consumed k src ((acc.take 140).drop 10) (bank.take 129) hs cin)
  hs (List.replicate hs.length false) s m count offAfter fr
 simpa only [unbuild,pre,←plain_split acc Z bank cin src hsrc] using result


end ECDSAAdd.Entrant.ReorderedCUnbuild

end

-- Verified component ReorderedCLoop
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCLoop
open Arithmetic InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

theorem loop_eq(k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire)(middle:Program)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0)
 (hk:k≤124)(nd:hs.Nodup)(len:hs.length=k)
 (fresh:∀h∈hs,h∉cin::(src++acc++Z++bank))
 (offF:∀h∈hs,h∉wires (ReorderedCPlain.build acc Z bank cin src))
 (offI:∀h∈hs,h∉wires (ReorderedCPlain.unbuild acc Z bank cin src))
 (offM:∀h∈hs,h∉wires middle)(zero:∀h∈hs,s.basis h=false)
 (good:WReady acc Z bank cin src (regValue src s.basis)
   (middleState (ReorderedCPlain.build acc Z bank cin src) middle s m)):
 run (ReorderedCBuild.build k acc Z bank cin src hs++middle++ReorderedCUnbuild.unbuild k acc Z bank cin src hs) m s=
 run (ReorderedCPlain.build acc Z bank cin src++middle++ReorderedCPlain.unbuild acc Z bank cin src) m s:=by
 let H:=regValue src s.basis
 let vs:=ReorderedCacheBits.values 4 k H (976*H/1024)
 let u:=middleState (ReorderedCPlain.build acc Z bank cin src) middle s m
 let t:=scatterState hs vs u
 have ready:WReady acc Z bank cin src H t:=WReady_scatter acc Z bank cin src H hs vs u fresh good
 have saved:hs.map t.basis=ReorderedCacheBits.values 4 k (regValue src t.basis) (976*regValue src t.basis/1024):=by
  rw [ready.2.1]
  exact scatter_saved_map hs vs u nd (by simp [vs,ReorderedCacheBits.values,len])
 have av:regValue acc t.basis=4294968272*regValue src t.basis:=by
  rw [ready.2.1]
  exact ready.1
 have forward:=ReorderedCBuild.build_frame k acc Z bank cin src hs hacc hsrc hf s
  (m.take (measurementCount (ReorderedCPlain.build acc Z bank cin src))) hz hb hi ha hk nd
  (fun h hh bad=>fresh h hh (by simp [bad])) offF zero
 have inverse:=ReorderedCUnbuild.unbuild_frame k acc Z bank cin src hs hacc hsrc hf t
  (m.drop (measurementCount (ReorderedCPlain.build acc Z bank cin src)+measurementCount middle))
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2 av hk nd len fresh offI saved
 have hb129:129≤bank.length:=by
  have h:=(hf _ (C163NarrowAcc.terms_mem src).2.1).bankLen
  norm_num [Acc.earlyTerm] at h
  omega
 have count:=ReorderedCBuild.measurement_eq k acc Z bank cin src hs hacc hsrc hb129 hk
 exact cached_pair_many_eq (ReorderedCPlain.build acc Z bank cin src) (ReorderedCBuild.build k acc Z bank cin src hs)
  middle (ReorderedCPlain.unbuild acc Z bank cin src) (ReorderedCUnbuild.unbuild k acc Z bank cin src hs)
  hs vs count offF offM offI nd s m zero forward inverse


end ECDSAAdd.Entrant.ReorderedCLoop

end

-- Verified component ReorderedFrameUnique
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedFrameUnique
set_option autoImplicit false


theorem unique(acc:List Wire)(base:BasisState)(V:Nat)(s t:BasisState)
 (hs:SquareFrame acc base V s)(ht:SquareFrame acc base V t):s=t:=by
 funext q
 by_cases hq:q∈acc
 · exact regValue_equal_bits acc s t (hs.1.trans ht.1.symm) q hq
 · exact (hs.2 q hq).trans (ht.2 q hq).symm

theorem program_eq(acc:List Wire)(base:BasisState)(I V:Nat)(p q:Program)
 (hp:Triple (SquareFrame acc base I) p (SquareFrame acc base V))
 (hq:Triple (SquareFrame acc base I) q (SquareFrame acc base V))
 (s:State)(mp mq:List Bool)(h:SquareFrame acc base I s.basis):run p mp s=run q mq s:=by
 have a:=hp s mp h
 have b:=hq s mq h
 apply State.extensionality
 · exact a.1.trans b.1.symm
 · exact unique acc base V _ _ a.2 b.2

theorem c_build_eq(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State)(mp mq:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0):
 run (ReorderedCPlain.build acc Z bank cin src) mp s=run (C163NarrowAcc.build8 acc Z bank cin src) mq s:=by
 exact program_eq acc s.basis 0 (4294968272*regValue src s.basis) _ _
  (ReorderedCPlain.build_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi)
  (C163NarrowAcc.build8_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi)
  s mp mq ⟨ha,fun _ _=>rfl⟩

theorem c_unbuild_eq(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State)(mp mq:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=4294968272*regValue src s.basis):
 run (ReorderedCPlain.unbuild acc Z bank cin src) mp s=run (C163SourceAdd.unbuild acc Z bank cin src) mq s:=by
 exact program_eq acc s.basis (4294968272*regValue src s.basis) 0 _ _
  (ReorderedCPlain.unbuild_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi)
  (C163SourceAdd.unbuild_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi)
  s mp mq ⟨ha,fun _ _=>rfl⟩



end ECDSAAdd.Entrant.ReorderedFrameUnique

end

-- Verified component ReorderedRetape
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedRetape
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def tape(oldCount newCount:Nat)(m:List Bool):List Bool:=List.replicate oldCount false++m.drop newCount
theorem drop_tape(oldCount newCount:Nat)(m:List Bool):
 (tape oldCount newCount m).drop oldCount=m.drop newCount:=by simp [tape]

theorem c_middle_eq(acc Z bank:List Wire)(cin:Wire)(src:List Wire)(middle:Program)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0):
 middleState (ReorderedCPlain.build acc Z bank cin src) middle s m=
 middleState (C163NarrowAcc.build8 acc Z bank cin src) middle s
  (tape (measurementCount (C163NarrowAcc.build8 acc Z bank cin src))
    (measurementCount (ReorderedCPlain.build acc Z bank cin src)) m):=by
 unfold middleState
 rw [drop_tape]
 rw [ReorderedFrameUnique.c_build_eq acc Z bank cin src hacc hsrc hf s _ _ hz hb hi ha]

theorem c_loop_eq(acc Z bank:List Wire)(cin:Wire)(src:List Wire)(middle:Program)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0)
 (good:∀record:List Bool,WReady acc Z bank cin src (regValue src s.basis)
   (middleState (C163NarrowAcc.build8 acc Z bank cin src) middle s record)):
 run (ReorderedCPlain.build acc Z bank cin src++middle++ReorderedCPlain.unbuild acc Z bank cin src) m s=
 run (C163NarrowAcc.build8 acc Z bank cin src++middle++C163SourceAdd.unbuild acc Z bank cin src)
  (tape (measurementCount (C163NarrowAcc.build8 acc Z bank cin src))
    (measurementCount (ReorderedCPlain.build acc Z bank cin src)) m) s:=by
 let record:=tape (measurementCount (C163NarrowAcc.build8 acc Z bank cin src))
    (measurementCount (ReorderedCPlain.build acc Z bank cin src)) m
 let u:=middleState (C163NarrowAcc.build8 acc Z bank cin src) middle s record
 have ready:=good record
 have eq:=c_middle_eq acc Z bank cin src middle hacc hsrc hf s m hz hb hi ha
 simp only [run_three]
 change run (ReorderedCPlain.unbuild acc Z bank cin src) _
   (middleState (ReorderedCPlain.build acc Z bank cin src) middle s m)=
  run (C163SourceAdd.unbuild acc Z bank cin src) _ u
 rw [eq]
 apply ReorderedFrameUnique.c_unbuild_eq acc Z bank cin src hacc hsrc hf u _ _
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2
 rw [ready.2.1]
 exact ready.1


end ECDSAAdd.Entrant.ReorderedRetape

end

-- Verified component ReorderedCFixedDefs
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCFixed
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle
set_option autoImplicit false

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

abbrev p:=C163Low4Middle.p
def hosts:List Wire:=q::r::p::hs
def loop:Program:=ReorderedCBuild.build 99 ga pad bank L.core.cin src hosts++bankChecked.out++
 ReorderedCUnbuild.unbuild 99 ga pad bank L.core.cin src hosts

theorem host_geometry:hosts.Nodup ∧ hosts.length=99 ∧
 (∀h∈hosts,h∉L.core.cin::(src++ga++pad++bank)):=by decide +kernel

end ECDSAAdd.Entrant.ReorderedCFixed

end

-- Verified component ReorderedCFixedSupportList
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCFixed
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle
set_option autoImplicit false

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem off_plain:∀h∈hosts,h∉wires (ReorderedCPlain.build ga pad bank L.core.cin src) ∧
 h∉wires (ReorderedCPlain.unbuild ga pad bank L.core.cin src):=by
 have f6:=ReorderedAcc.fits_prefix ga pad bank L.core.cin 163 140 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have f10:=ReorderedAcc.fits_prefix ga pad bank L.core.cin 163 140 (Acc.earlyTerm src false 10)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.1) (by decide) (by decide)
 have f32:=Acc.fits_prefix ga pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide)
 have w6:=ReorderedAcc.op_wires (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6) (by decide) f6
 have w10(neg:Bool):=ReorderedAcc.op_wires (ga.take 140) pad bank L.core.cin 140 neg (Acc.earlyTerm src false 10) (by decide) f10
 have w32:=Acc.op_wires (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32) (by decide) f32
 have small6:∀h∈hosts,h∉(L.core.cin::(Acc.tx pad 140 (Acc.earlyTerm src true 6)++
  Acc.ty (ga.take 140) (Acc.earlyTerm src true 6)++Acc.tc bank 140 (Acc.earlyTerm src true 6))).toFinset:=by
  simp only [List.mem_toFinset]
  decide +kernel
 have small10:∀h∈hosts,h∉(L.core.cin::(Acc.tx pad 140 (Acc.earlyTerm src false 10)++
  Acc.ty (ga.take 140) (Acc.earlyTerm src false 10)++Acc.tc bank 140 (Acc.earlyTerm src false 10))).toFinset:=by
  simp only [List.mem_toFinset]
  decide +kernel
 have small32:∀h∈hosts,h∉(L.core.cin::(Acc.tx pad 163 (Acc.earlyTerm src false 32)++
  Acc.ty (ga.take 163) (Acc.earlyTerm src false 32)++Acc.tc bank 163 (Acc.earlyTerm src false 32))).toFinset:=by
  simp only [List.mem_toFinset]
  decide +kernel
 have seed:=Acc.seed_support ga pad bank L.core.cin 163 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (C163NarrowAcc.terms_mem src).1)
 have tailSupport:=KnownOutputAdder.program_support (mappedRead (src++pad.take 4) false)
  (ReorderedKnownTail.desired src) ((ga.take 140).drop 6) (bank.take 133) L.core.cin
 rw [mappedRead_wires,ReorderedKnownTail.desired_wires] at tailSupport
 have smallTail:∀h∈hosts,h∉((src++pad.take 4)++src.drop 2++(ga.take 140).drop 6++bank.take 133++[L.core.cin]).toFinset:=by
  simp only [List.mem_toFinset]
  decide +kernel
 intro h hh
 have seedOff:h∉wires (Acc.seedOp ga pad 163 (Acc.earlyTerm src false 4)):=by
  intro bad
  exact host_geometry.2.2 h hh (by simpa only [Acc.earlyTerm,List.mem_toFinset] using seed bad)
 have op6Off:h∉wires (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6)):=by
  rw [w6];exact small6 h hh
 have op10Off(neg:Bool):h∉wires (Acc.op (ga.take 140) pad bank L.core.cin 140 neg (Acc.earlyTerm src false 10)):=by
  rw [w10 neg];exact small10 h hh
 have op32Off:h∉wires (Acc.op (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32)):=by
  rw [w32];exact small32 h hh
 have tailOff:h∉wires (ReorderedCTail.tail ga pad bank L.core.cin src):=by
  exact fun bad=>smallTail h hh (tailSupport bad)
 have oldOff: h∉wires (C163SourceAdd.unbuild ga pad bank L.core.cin src):=
  (off_base h (host_geometry.2.2 h hh)).2
 have preOff:h∉wires (C163Carry.unbuildPre ga pad bank L.core.cin src):=by
  have pieces:=oldOff
  simp only [C163SourceAdd.unbuild,wires_append,Finset.mem_union,not_or] at pieces
  exact pieces.1.1.1
 constructor
 · simpa only [ReorderedCPlain.build,ReorderedCPre.pre,C163Carry.buildPost,wires_append,
    Finset.mem_union,not_or,and_assoc] using And.intro seedOff (And.intro op6Off (And.intro (op10Off false) op32Off))
 · simpa only [ReorderedCPlain.unbuild,wires_append,Finset.mem_union,not_or,and_assoc] using
    And.intro preOff (And.intro (op10Off true) (And.intro tailOff seedOff))


end ECDSAAdd.Entrant.ReorderedCFixed

end

-- Verified component ReorderedBankSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedBankSupport
open C163Low4Middle
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.wires specialChecked bankChecked

theorem subset:wires bankChecked.out⊆wires specialChecked.out:=
 (ZeroSetDevelop.SRewrites.support hs specialChecked.out bankChecked.out bank_cert).1


theorem free:∀h∈hs,h∉wires bankChecked.out:=
 (ZeroSetDevelop.SRewrites.support hs specialChecked.out bankChecked.out bank_cert).2


theorem q_free:C163Low4Middle.q∉wires bankChecked.out:=fun bad=>special_free.1 (subset bad)

theorem r_free:C163Low4Middle.r∉wires bankChecked.out:=fun bad=>special_free.2 (subset bad)

theorem p_free:C163Low4Middle.p∉wires bankChecked.out:=fun bad=>special_p_free (subset bad)

end ECDSAAdd.Entrant.ReorderedBankSupport

end

-- Verified component ReorderedCFixed
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCFixed
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle
set_option autoImplicit false

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires specialChecked bankChecked













theorem off_middle:∀h∈hosts,h∉wires bankChecked.out:=by
 change ∀h∈q::r::C163Low4Middle.p::hs,h∉wires bankChecked.out
 rw [List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons]
 exact ⟨ReorderedBankSupport.q_free,ReorderedBankSupport.r_free,ReorderedBankSupport.p_free,ReorderedBankSupport.free⟩



theorem transport(Q:BasisState→Prop)(s a b:State)(e:a=b)(hb:b.phase=s.phase ∧ Q b.basis):
 a.phase=s.phase ∧ Q a.basis:=e.symm ▸ hb

theorem frame(base:BasisState)(hc:L.PairClean base)(hp:base p=false)(hd:base d=false)
 (O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loop
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have len:=lengths
 have fit:=fits
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue ga s.basis=0:=C163Low4Ghost.ghostAcc_zero L s.basis clean
 have qz:s.basis q=false:=(regValue_zero _ _).mp clean.work q (by decide)
 have rz:s.basis r=false:=(regValue_zero _ _).mp clean.work r (by decide)
 have pz:s.basis p=false:=(hf.2 p (by decide)).trans hp
 have dz:s.basis d=false:=(hf.2 d (by decide)).trans hd
 have zeroU:∀u∈hs,s.basis u=false:=by
  intro u hu
  rcases List.mem_append.mp hu with hu|hu
  · rcases List.mem_append.mp hu with hu|hu
    · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
    · have e:u=d:=by simpa only [List.mem_singleton] using hu
      subst u
      exact dz
  · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_take hu)
 have zero:∀u∈hosts,s.basis u=false:=by
  intro u hu
  simp only [hosts,List.mem_cons] at hu
  rcases hu with rfl|rfl|rfl|hu
  · exact qz
  · exact rz
  · exact pz
  · exact zeroU u hu
 have offHs:∀u∈hs,u∉wires (ReorderedCPlain.build ga pad bank L.core.cin src):=by
  intro u hu
  exact (off_plain u (by simp only [hosts,List.mem_cons];exact Or.inr (Or.inr (Or.inr hu)))).1
 have goodOld:=fun record=>good base hc O hO s record hf
 have goodSpecial:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) specialChecked.out s m):=by
  rw [ReorderedRetape.c_middle_eq ga pad bank L.core.cin src specialChecked.out
   len.1 len.2.2.2 fit s m hz hb clean.cin ha]
  exact goodOld _
 have middleEq:=bank_cert.middle_eq hs specialChecked.out bankChecked.out
  (ReorderedCPlain.build ga pad bank L.core.cin src) s m zeroU offHs
 have goodBank:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) bankChecked.out s m):=by
  rw [middleEq]
  exact goodSpecial
 have cacheEq:=ReorderedCLoop.loop_eq 99 ga pad bank L.core.cin src hosts bankChecked.out
  len.1 len.2.2.2 fit s m hz hb clean.cin ha (by decide) host_geometry.1 host_geometry.2.1
  host_geometry.2.2 (fun u hu=>(off_plain u hu).1) (fun u hu=>(off_plain u hu).2) off_middle zero goodBank
 have middleReplace:=bank_cert.surround_eq hs specialChecked.out bankChecked.out
  (ReorderedCPlain.build ga pad bank L.core.cin src) (ReorderedCPlain.unbuild ga pad bank L.core.cin src)
  s m zeroU offHs
 have plainEq:=ReorderedRetape.c_loop_eq ga pad bank L.core.cin src specialChecked.out
  len.1 len.2.2.2 fit s m hz hb clean.cin ha goodOld
 let record:=ReorderedRetape.tape (measurementCount (C163NarrowAcc.build8 ga pad bank L.core.cin src))
  (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)) m
 have oldFrame:=C163Low4Middle.frame base hc hp hd O hO s record hf
 rw [eq_plain base hc hp hd O hO s record hf] at oldFrame
 have finalEq:run loop m s=run (C163NarrowAcc.build8 ga pad bank L.core.cin src++specialChecked.out++
  C163SourceAdd.unbuild ga pad bank L.core.cin src) record s:=cacheEq.trans (middleReplace.trans plainEq)
 exact transport (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)) s _ _ finalEq oldFrame


end ECDSAAdd.Entrant.ReorderedCFixed

end

-- Verified component ReorderedRecordPadding
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedRecordPadding
set_option autoImplicit false


def program(n:Nat)(wire:Wire):Program:=List.replicate n (.measureX wire [] [])

theorem measure_zero(wire:Wire)(s:State)(record:Bool)(hz:s.basis wire=false):
 measureAndCorrect wire [] [] record s=s:=by
 have update:writeBit s.basis wire false=s.basis:=by
  funext q
  by_cases hq:q=wire
  · subst q
    simp [writeBit,hz]
  · simp [writeBit,Function.update_of_ne hq]
 simp [measureAndCorrect,correct,hz,update]

theorem run_zero(n:Nat)(wire:Wire)(s:State)(m:List Bool)(hz:s.basis wire=false):
 run (program n wire) m s=s:=by
 induction n generalizing m with
 | zero=>rfl
 | succ n ih=>
  simp only [program,List.replicate_succ,run]
  rw [measure_zero wire s (m.headD false) hz]
  exact ih m.tail

theorem counts(n:Nat)(wire:Wire):toffoliCount (program n wire)=0 ∧
 measurementCount (program n wire)=n ∧ Challenge.gateSlots (program n wire)=n:=by
 induction n with
 | zero=>simp [program,toffoliCount,measurementCount,Challenge.gateSlots]
 | succ n ih=>
  simp only [program,List.replicate_succ,toffoliCount,measurementCount,Challenge.gateSlots,
   List.map_cons,List.sum_cons,Challenge.instructionSlots,List.length_nil] at ih ⊢
  omega


end ECDSAAdd.Entrant.ReorderedRecordPadding

end

-- Verified component ReorderedKnownC
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedKnownC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle KnownSparseFold ZeroReadDevelop
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires specialChecked bankChecked

abbrev hosts:=ReorderedCFixed.hosts

theorem guard:∀u∈KnownCMidStaged.known0,u∉hosts ∧ u∉ga ∧ (u∈bank ∨ u=L.core.cin):=by decide +kernel















































def loop:Program:=ReorderedCBuild.build 99 ga pad bank L.core.cin src hosts++KnownCMidStaged.body++
 ReorderedCUnbuild.unbuild 99 ga pad bank L.core.cin src hosts

































def rawBody:Program:=C163Low4Body.bodyProgram L loop



















def body:Program:=rawBody++ReorderedRecordPadding.program 4 L.core.cin















end ECDSAAdd.Entrant.ReorderedKnownC

end

-- Verified component ReorderedPhysical
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedPhysical
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

theorem cached(k:Nat)(xs ys cs hs:List Wire)(cin:Wire)
 (hx:k+6≤xs.length)(hy:k+6≤ys.length)(hc:k+4≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup)(fresh:∀h∈hs,h∉cs):
 GatePhysical (ReorderedGenericCache.cachedAdd k xs ys cs hs cin) ∧
 GatePhysical (ReorderedGenericCache.consumedAdd k xs ys cs hs cin):=by
 have whole:GatePhysical (mappedAdd (mappedRead xs false) ys cs cin):=by
  rw [MixedLiteralAdderDevelop.read_add_eq]
  exact addInPlace_physical xs ys cs cin hn
 have high:=whole
 rw [mappedAdd_split (4+k) xs ys cs cin (by omega) (by omega) (by omega),gatePhysical_append] at high
 have low:=whole
 rw [mappedAdd_split 4 xs ys cs cin (by omega) (by omega) (by omega),gatePhysical_append] at low
 have fr:∀h∈hs,h∉(cs.drop 4).take k:=by
  intro h hh bad
  exact fresh h hh (List.mem_of_mem_drop (List.mem_of_mem_take bad))
 have cp:GatePhysical (copyMany ((cs.drop 4).take k) hs):=
  fun i hi=>valid_to_physical i (copyMany_physical _ _ fr i hi)
 have mv:GatePhysical (moveMany ((cs.drop 4).take k) hs):=
  fun i hi=>valid_to_physical i (moveMany_physical _ _ fr i hi)
 simp only [ReorderedGenericCache.cachedAdd,ReorderedGenericCache.consumedAdd,gatePhysical_append]
 exact ⟨⟨⟨high.1,cp⟩,high.2⟩,⟨⟨low.1,mv⟩,high.2⟩⟩

theorem op(acc Z bank:List Wire)(cin:Wire)(w:Nat)(neg:Bool)(f:MeasuredSquareFold)
 (hf:ReorderedAcc.Fits acc Z bank cin w f):GatePhysical (Acc.op acc Z bank cin w neg f):=by
 have nd:=ReorderedAcc.fits_nodup acc Z bank cin w f hf
 cases neg
 · simpa only [Acc.op,Bool.false_eq_true,if_false] using addInPlace_physical _ _ _ _ nd
 · simpa only [Acc.op,if_true] using subInPlace_physical _ _ _ _ nd

theorem padding(n:Nat)(wire:Wire):GatePhysical (ReorderedRecordPadding.program n wire):=by
 intro i hi
 have eq:i=Instr.measureX wire [] []:=(List.mem_replicate.mp hi).2
 subst i
 simp [RecordedQuantum.PhysicalInstr]



end ECDSAAdd.Entrant.ReorderedPhysical

end

-- Verified component ReorderedCPhysical
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCPhysical
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle
set_option autoImplicit false

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires specialChecked bankChecked
abbrev hosts:=ReorderedCFixed.hosts

end ECDSAAdd.Entrant.ReorderedCPhysical

end

-- Verified component ReorderedCCounts
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCCounts
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle ControlLoan1589BFFold
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
abbrev hosts:=ReorderedCFixed.hosts

theorem cache_counts:
 toffoliCount (ReorderedGenericCache.cachedAdd 99 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=129 ∧
 measurementCount (ReorderedGenericCache.cachedAdd 99 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=129 ∧
 toffoliCount (ReorderedGenericCache.consumedAdd 99 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=30 ∧
 measurementCount (ReorderedGenericCache.consumedAdd 99 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=129:=by
 have old:=addInPlace_counts src ((ga.take 140).drop 10) (bank.take 129) L.core.cin (by decide) (by decide)
 rw [←MixedLiteralAdderDevelop.read_add_eq] at old
 have bal:=ReorderedGenericCache.count_balance 99 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin
  (by decide) (by decide) (by decide)
 change toffoliCount (mappedAdd (mappedRead src false) ((ga.take 140).drop 10) (bank.take 129) L.core.cin)=129 ∧
  measurementCount (mappedAdd (mappedRead src false) ((ga.take 140).drop 10) (bank.take 129) L.core.cin)=129 at old
 omega

theorem pieces:
 toffoliCount (ReorderedCBuild.build 99 ga pad bank L.core.cin src hosts)=392 ∧
 measurementCount (ReorderedCBuild.build 99 ga pad bank L.core.cin src hosts)=392 ∧
 toffoliCount (ReorderedCUnbuild.unbuild 99 ga pad bank L.core.cin src hosts)=137 ∧
 measurementCount (ReorderedCUnbuild.unbuild 99 ga pad bank L.core.cin src hosts)=392:=by
 have f6:=Acc.fits_prefix ga pad bank L.core.cin 163 140 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide)
 have f32:=Acc.fits_prefix ga pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide)
 have seed:=Acc.seed_counts ga pad bank L.core.cin 163 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (C163NarrowAcc.terms_mem src).1).toFitsLen
 have sub:=Acc.op_counts (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6) (by decide) f6.toFitsLen
 have top:=Acc.op_counts (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32) (by decide) f32.toFitsLen
 have preInv:=CodexNarrowTailResource.accSub_counts 108 (ga.take 163) pad bank L.core.cin 163 (Acc.earlyTerm src false 32)
  (by decide) f32.toFitsLen (by decide)
 have tail:=ReorderedKnownTail.counts src pad ((ga.take 140).drop 6) (bank.take 133) L.core.cin
  (by decide) (by decide) (by decide) (by decide)
 have notC:=notRegister_counts ((ga.take 140).drop 10)
 have cache:=cache_counts
 change toffoliCount (ReorderedCTail.tail ga pad bank L.core.cin src)=0 ∧
  measurementCount (ReorderedCTail.tail ga pad bank L.core.cin src)=133 at tail
 change toffoliCount (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6))=133 ∧
  measurementCount (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6))=133 at sub
 change toffoliCount (Acc.op (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32))=130 ∧
  measurementCount (Acc.op (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32))=130 at top
 change toffoliCount (CodexKnownOnesTail.accSub 108 (ga.take 163) pad bank L.core.cin 163 (Acc.earlyTerm src false 32))=107 ∧
  measurementCount (CodexKnownOnesTail.accSub 108 (ga.take 163) pad bank L.core.cin 163 (Acc.earlyTerm src false 32))=130 at preInv
 simp only [ReorderedCBuild.build,ReorderedCHead.head,C163Carry.buildPost,
  ReorderedCUnbuild.unbuild,ReorderedCUnbuild.after,ReorderedConsumedSub.consumed,C163Carry.unbuildPre,
  toffoliCount_append,measurementCount_append]
 omega

theorem body_counts:toffoliCount ReorderedKnownC.body≤2121 ∧ measurementCount ReorderedKnownC.body=2390:=by
 have specialT:=special_cert.toffoli [q,r] middle specialChecked.out
 have specialM:=special_cert.measurements [q,r] middle specialChecked.out
 have bankT:=bank_cert.toffoli hs specialChecked.out bankChecked.out
 have bankM:=bank_cert.measurements hs specialChecked.out bankChecked.out
 have certified:=KnownSparseFold.Cert.counts _ _ _ _ _ KnownCMidStaged.cert
 change toffoliCount KnownCMidStaged.body+8=toffoliCount bankChecked.out ∧
  measurementCount KnownCMidStaged.body=measurementCount bankChecked.out at certified
 have mid:=middle_counts
 have pre:=mixFoldsQ_countsTq L hw false [.inl (negRot L)] (OwnDiagAll12Square.bodyC_static L hw).1
 change toffoliCount (mixFoldsQTq L false [.inl (negRot L)])=766 ∧
  measurementCount (mixFoldsQTq L false [.inl (negRot L)])=767 at pre
 have parts:=pieces
 have padding:=ReorderedRecordPadding.counts 4 L.core.cin
 simp only [ReorderedKnownC.body,ReorderedKnownC.rawBody,C163Low4Body.bodyProgram,
  ReorderedKnownC.loop,ReorderedKnownC.hosts,toffoliCount_append,measurementCount_append]
 simp only [hosts] at parts
 omega



end ECDSAAdd.Entrant.ReorderedCCounts

end

-- Verified component ReorderedCStructural
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCStructural
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout C163Low4Ghost C163Low4Structural
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

theorem build_eq(L:CuccaroStreamedSquareWideLayout)(k:Nat)(Z bank src hs:List Wire)(cin:Wire):
 ReorderedCBuild.build k (ghostAcc L) Z bank cin src hs=
 ReorderedCBuild.build k (C163Fold.acc L) Z bank cin src hs:=by
 simp only [ReorderedCBuild.build,ReorderedCHead.head,C163Carry.buildPost,Acc.seedOp,Acc.op]
 rw [ty L src false 4 (by decide),ty_take L src true 140 6 (by decide),
  ghostAcc_take_drop L 140 10 (by decide),ty_take L src false 163 32 (by decide)]
 rfl

theorem unbuild_eq(L:CuccaroStreamedSquareWideLayout)(k:Nat)(Z bank src hs:List Wire)(cin:Wire):
 ReorderedCUnbuild.unbuild k (ghostAcc L) Z bank cin src hs=
 ReorderedCUnbuild.unbuild k (C163Fold.acc L) Z bank cin src hs:=by
 simp only [ReorderedCUnbuild.unbuild,ReorderedCUnbuild.after,C163Carry.unbuildPre,
  CodexKnownOnesTail.accSub,ReorderedCTail.tail,Acc.seedOp]
 rw [ty_take L src false 163 32 (by decide),ghostAcc_take_drop L 140 10 (by decide),
  ghostAcc_take_drop L 140 6 (by decide),ty L src false 4 (by decide)]
 rfl



end ECDSAAdd.Entrant.ReorderedCStructural

end

-- Verified component ReorderedSupport
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedSupport
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

theorem cached(k:Nat)(xs ys cs hs:List Wire)(cin:Wire)
 (hx:k+6≤xs.length)(hy:k+6≤ys.length)(hc:k+4≤cs.length)
 (hxy:xs.length=ys.length)(hcs:cs.length+1=ys.length):
 wires (ReorderedGenericCache.cachedAdd k xs ys cs hs cin)⊆
  (cin::(xs++ys++cs)).toFinset∪hs.toFinset ∧
 wires (ReorderedGenericCache.consumedAdd k xs ys cs hs cin)⊆
  (cin::(xs++ys++cs)).toFinset∪hs.toFinset:=by
 let S:=(cin::(xs++ys++cs)).toFinset
 have full:wires (mappedAdd (mappedRead xs false) ys cs cin)=S:=by
  rw [MixedLiteralAdderDevelop.read_add_eq,addInPlace_wires xs ys cs cin hxy hcs]
 have split:=mappedAdd_split (4+k) xs ys cs cin (by omega) (by omega) (by omega)
 have split4:=mappedAdd_split 4 xs ys cs cin (by omega) (by omega) (by omega)
 have pre:wires (carryPrefix (4+k) xs ys cs cin)⊆S:=by
  intro q hq
  rw [←full,split,wires_append]
  exact Finset.mem_union_left _ hq
 have post:wires (mappedSuffix (4+k) xs ys cs cin)⊆S:=by
  intro q hq
  rw [←full,split,wires_append]
  exact Finset.mem_union_right _ hq
 have pre4:wires (carryPrefix 4 xs ys cs cin)⊆S:=by
  intro q hq
  rw [←full,split4,wires_append]
  exact Finset.mem_union_left _ hq
 have carries:((cs.drop 4).take k).toFinset⊆S:=by
  intro q hq
  have h:=List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_toFinset.mp hq))
  simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append]
  exact Or.inr (Or.inr h)
 have cp: wires (copyMany ((cs.drop 4).take k) hs)⊆S∪hs.toFinset:=
  (copyMany_support _ _).trans (Finset.union_subset_union carries (Finset.Subset.refl _))
 have mv: wires (moveMany ((cs.drop 4).take k) hs)⊆S∪hs.toFinset:=
  (moveMany_support _ _).trans (Finset.union_subset_union carries (Finset.Subset.refl _))
 have left:S⊆S∪hs.toFinset:=Finset.subset_union_left
 simp only [ReorderedGenericCache.cachedAdd,ReorderedGenericCache.consumedAdd,wires_append]
 exact ⟨Finset.union_subset (Finset.union_subset (pre.trans left) cp) (post.trans left),
  Finset.union_subset (Finset.union_subset (pre4.trans left) mv) (post.trans left)⟩

theorem consumed(k:Nat)(xs ys cs hs:List Wire)(cin:Wire)
 (hx:k+6≤xs.length)(hy:k+6≤ys.length)(hc:k+4≤cs.length)
 (hxy:xs.length=ys.length)(hcs:cs.length+1=ys.length):
 wires (ReorderedConsumedSub.consumed k xs ys cs hs cin)⊆
  (cin::(xs++ys++cs)).toFinset∪hs.toFinset:=by
 have core:=(cached k xs ys cs hs cin hx hy hc hxy hcs).2
 have notSub:wires (notRegister ys)⊆(cin::(xs++ys++cs)).toFinset∪hs.toFinset:=by
  rw [notRegister_wires]
  intro q hq
  apply Finset.mem_union_left
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
  exact Or.inr (Or.inl (Or.inr hq))
 simp only [ReorderedConsumedSub.consumed,wires_append]
 exact Finset.union_subset (Finset.union_subset notSub core) notSub



end ECDSAAdd.Entrant.ReorderedSupport

end

-- Verified component ReorderedCFineList
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCFine
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle OwnDiagAll12Square
set_option autoImplicit false

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires specialChecked bankChecked List.toFinset






































































end ECDSAAdd.Entrant.ReorderedCFine

end

-- Verified component ReorderedSlots
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedSlots
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] Challenge.gateSlots

theorem cache(k:Nat)(xs ys cs hs:List Wire)(cin:Wire)
 (hx:k+6≤xs.length)(hy:k+6≤ys.length)(hc:k+4≤cs.length)(len:hs.length=k):
 Challenge.gateSlots (ReorderedGenericCache.cachedAdd k xs ys cs hs cin)=
  Challenge.gateSlots (mappedAdd (mappedRead xs false) ys cs cin)+k ∧
 Challenge.gateSlots (ReorderedGenericCache.consumedAdd k xs ys cs hs cin)+4*k=
  Challenge.gateSlots (mappedAdd (mappedRead xs false) ys cs cin):=by
 have split:=mappedAdd_split (4+k) xs ys cs cin (by omega) (by omega) (by omega)
 have pn:=carryPrefix_slots (4+k) xs ys cs cin (by omega) (by omega) (by omega)
 have p4:=carryPrefix_slots 4 xs ys cs cin (by omega) (by omega) (by omega)
 have cp:=copyMany_slots ((cs.drop 4).take k) hs
 have mv:=(moveMany_counts ((cs.drop 4).take k) hs).2.2
 have banklen:((cs.drop 4).take k).length=k:=by simp only [List.length_take,List.length_drop];omega
 rw [banklen,len,Nat.min_self] at cp mv
 simp only [ReorderedGenericCache.cachedAdd,ReorderedGenericCache.consumedAdd,split,
  Challenge.gateSlots_append,pn,p4,cp,mv]
 constructor <;> omega


end ECDSAAdd.Entrant.ReorderedSlots

end

-- Verified component ReorderedCSlots
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCSlots
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle OwnDiagAll12Square
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] Challenge.gateSlots
abbrev hosts:=ReorderedCFixed.hosts

theorem pieces:
 Challenge.gateSlots (ReorderedCBuild.build 99 ga pad bank L.core.cin src hosts)≤10000 ∧
 Challenge.gateSlots (ReorderedCUnbuild.unbuild 99 ga pad bank L.core.cin src hosts)≤10000:=by
 have seed:Challenge.gateSlots (Acc.seedOp ga pad 163 (Acc.earlyTerm src false 4))≤200:=by
  rw [Acc.seedOp,Baselines.copyRegister_gateSlots]
  decide +kernel
 have sub:=Acc.op_gateSlots (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6)
 change Challenge.gateSlots (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6))≤1876 at sub
 have top:=Acc.op_gateSlots (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32)
 change Challenge.gateSlots (Acc.op (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32))≤1834 at top
 have old:=Baselines.addInPlace_gateSlots_le src ((ga.take 140).drop 10) (bank.take 129) L.core.cin
 rw [←MixedLiteralAdderDevelop.read_add_eq] at old
 change Challenge.gateSlots (mappedAdd (mappedRead src false) ((ga.take 140).drop 10) (bank.take 129) L.core.cin)≤1560 at old
 have cache:=ReorderedSlots.cache 99 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin
  (by decide) (by decide) (by decide) ReorderedCFixed.host_geometry.2.1
 have cacheBound:Challenge.gateSlots (ReorderedGenericCache.cachedAdd 99 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)≤1919:=by omega
 have consumeBound:Challenge.gateSlots (ReorderedConsumedSub.consumed 99 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)≤2080:=by
  have n:=Baselines.notRegister_gateSlots ((ga.take 140).drop 10)
  change Challenge.gateSlots (notRegister ((ga.take 140).drop 10))=130 at n
  simp only [ReorderedConsumedSub.consumed,Challenge.gateSlots_append]
  omega
 have f32:=Acc.fits_prefix ga pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide)
 have preInv:=CodexNarrowTailResource.accSub_slots 108 (ga.take 163) pad bank L.core.cin 163 (Acc.earlyTerm src false 32)
  (by decide) f32.toFitsLen (by decide)
 have topInv:=Acc.op_gateSlots (ga.take 163) pad bank L.core.cin 163 true (Acc.earlyTerm src false 32)
 change Challenge.gateSlots (Acc.op (ga.take 163) pad bank L.core.cin 163 true (Acc.earlyTerm src false 32))≤1834 at topInv
 have tail:=Win977Develop.known_slots (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
  ((ga.take 140).drop 6) (bank.take 133) L.core.cin
 change Challenge.gateSlots (ReorderedCTail.tail ga pad bank L.core.cin src)≤1876 at tail
 simp only [ReorderedCBuild.build,ReorderedCHead.head,C163Carry.buildPost,
  ReorderedCUnbuild.unbuild,ReorderedCUnbuild.after,C163Carry.unbuildPre,Challenge.gateSlots_append]
 constructor <;> omega

theorem body_slots:Challenge.gateSlots ReorderedKnownC.body≤112000:=by
 have special:=special_cert.slots [q,r] middle specialChecked.out
 have bank:=bank_cert.slots hs specialChecked.out bankChecked.out
 have known:=KRegs.slots_sublist (KnownSparseFold.Cert.sublist _ _ _ _ _ KnownCMidStaged.cert)
 have middle:=middle_slots
 have pre:=measuredFoldQ_gateSlotsTq L hw (negRot L)
 have preBound:Challenge.gateSlots (mixFoldsQTq L false [.inl (negRot L)])≤36000:=by
  rw [prefix_eq L]
  exact pre
 have bounds:=pieces
 have padding:=(ReorderedRecordPadding.counts 4 L.core.cin).2.2
 simp only [hosts] at bounds
 simp only [ReorderedKnownC.body,ReorderedKnownC.rawBody,C163Low4Body.bodyProgram,ReorderedKnownC.loop,
  ReorderedKnownC.hosts,Challenge.gateSlots_append]
 omega


end ECDSAAdd.Entrant.ReorderedCSlots

end

-- Verified component ReorderedCBalance
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedCBalance
open Arithmetic InverseCarryDevelop ThirdSavedCarryDevelop C163Low4Middle
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
abbrev p:=C163Low4Middle.p

theorem old_pieces:
 toffoliCount (C163Carry.buildMany 96 ga pad bank L.core.cin src hs q r p)=393 ∧
 measurementCount (C163Carry.buildMany 96 ga pad bank L.core.cin src hs q r p)=394 ∧
 toffoliCount (C163Carry.unbuildMany 96 ga pad bank L.core.cin src hs q r p)=138 ∧
 measurementCount (C163Carry.unbuildMany 96 ga pad bank L.core.cin src hs q r p)=394:=by
 have len:=lengths
 have fit:=fits
 have b:=C163KnownTail.build8_counts ga pad bank L.core.cin src len.1 (by decide)
  (fun f h=>(fit f h).toFitsLen)
 rw [C163KnownTail.build8_eq] at b
 have u:=C163SourceAdd.unbuild_resources ga pad bank L.core.cin src len.1 len.2.2.2
  (fun f h=>(fit f h).toFitsLen)
 have bc:=C163Carry.buildCached_counts ga pad bank L.core.cin src q len.1 len.2.2.2 (by decide) (by decide)
 have bd:=C163Carry.buildDual_counts ga pad bank L.core.cin src q r len.1 len.2.2.2 (by decide) (by decide)
 have bt:=C163Carry.buildTriple_counts ga pad bank L.core.cin src q r p len.1 len.2.2.2 (by decide) (by decide)
 have bm:=C163Carry.buildMany_counts 96 ga pad bank L.core.cin src hs q r p len.1 len.2.2.2
  (by decide) (by decide) (by decide) (by decide)
 have uc:=C163Carry.unbuildConsumed_counts ga pad bank L.core.cin src q len.1 len.2.2.2 (by decide)
 have ud:=C163Carry.unbuildDual_counts ga pad bank L.core.cin src q r len.1 len.2.2.2 (by decide)
 have ut:=C163Carry.unbuildTriple_counts ga pad bank L.core.cin src q r p len.1 len.2.2.2 (by decide)
 have um:=C163Carry.unbuildMany_counts 96 ga pad bank L.core.cin src hs q r p len.1 len.2.2.2
  (by decide) (by decide) (by decide)
 omega

theorem balance:toffoliCount ReorderedKnownC.body+10=toffoliCount C163Low4Middle.body ∧
 measurementCount ReorderedKnownC.body=measurementCount C163Low4Middle.body:=by
 have old:=old_pieces
 simp only [p] at old
 have new:=ReorderedCCounts.pieces
 have mid:=KnownSparseFold.Cert.counts _ _ _ _ _ KnownCMidStaged.cert
 change toffoliCount KnownCMidStaged.body+8=toffoliCount bankChecked.out ∧
  measurementCount KnownCMidStaged.body=measurementCount bankChecked.out at mid
 have pad:=ReorderedRecordPadding.counts 4 L.core.cin
 simp only [ReorderedCCounts.hosts] at new
 simp only [ReorderedKnownC.body,ReorderedKnownC.rawBody,ReorderedKnownC.loop,ReorderedKnownC.hosts,
  C163Low4Middle.body,C163Low4Body.bodyProgram,C163Low4Middle.loop,toffoliCount_append,measurementCount_append]
 omega


end ECDSAAdd.Entrant.ReorderedCBalance

end

-- Verified component ReorderedAPre
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAPre
open Arithmetic
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

theorem sub_value(H:Nat)(hH:H<2^128):
 ReorderedAcc.valueMod (16*H) H 138 6 true=(2^138-48*H)%2^138:=by
 simp only [ReorderedAcc.valueMod,if_true]
 norm_num at hH ⊢
 omega

theorem add_value(H:Nat)(hH:H<2^128):
 ReorderedAcc.valueMod ((2^138-48*H)%2^138) H 138 10 false=976*H:=by
 by_cases hz:H=0
 · subst H
   norm_num [ReorderedAcc.valueMod]
 have ht:2^138-48*H<2^138:=by omega
 rw [Nat.mod_eq_of_lt ht]
 simp only [ReorderedAcc.valueMod,Bool.false_eq_true,if_false]
 norm_num at hH ⊢
 omega

def pre(acc Z bank:List Wire)(cin:Wire)(src:List Wire):Program:=
 Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)++
 Acc.op (acc.take 138) Z bank cin 138 true (Acc.earlyTerm src true 6)++
 Acc.op (acc.take 138) Z bank cin 138 false (Acc.earlyTerm src false 10)

theorem pre_triple(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=161)(hsrc:src.length≤128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (base:BasisState)(hz:∀q∈Z,base q=false)(hb:∀q∈bank,base q=false)(hi:base cin=false):
 Triple (SquareFrame acc base 0) (pre acc Z bank cin src)
  (SquareFrame acc base (976*regValue src base)):=by
 have tm:=A161NarrowAcc.terms_mem src
 have hf4:=hf _ tm.1
 have hf6:=hf _ tm.2.2.1
 have hf10:=hf _ tm.2.1
 let H:=regValue src base
 have hH:H<2^128:=lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) hsrc)
 have seed:=Acc.seed_triple acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc hf4 base hz
  0 (16*H) (Or.inl (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
 have sub:=ReorderedAcc.op_mod_prefix_triple acc Z bank cin 161 138 (Acc.earlyTerm src true 6)
  hacc (by decide) hf6 (by simp only [Acc.earlyTerm];omega) (by norm_num [Acc.earlyTerm]) base hz hb hi true (16*H)
  (by norm_num at hH ⊢;omega)
 change Triple _ _ (SquareFrame acc base (ReorderedAcc.valueMod (16*H) H 138 6 true)) at sub
 rw [sub_value H hH] at sub
 have add:=ReorderedAcc.op_mod_prefix_triple acc Z bank cin 161 138 (Acc.earlyTerm src false 10)
  hacc (by decide) hf10 (by simp only [Acc.earlyTerm];omega) (by norm_num [Acc.earlyTerm]) base hz hb hi false ((2^138-48*H)%2^138)
  (Nat.mod_lt _ (by positivity))
 change Triple _ _ (SquareFrame acc base (ReorderedAcc.valueMod ((2^138-48*H)%2^138) H 138 10 false)) at add
 rw [add_value H hH] at add
 exact (seed.seq sub).seq add

end ECDSAAdd.Entrant.ReorderedAPre

end

-- Verified component ReorderedAHead
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAHead
open Arithmetic ReorderedAPre
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
def head(acc Z bank:List Wire)(cin:Wire)(src:List Wire):Program:=
 Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)++
 Acc.op (acc.take 138) Z bank cin 138 true (Acc.earlyTerm src true 6)

theorem head_triple(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=161)(hsrc:src.length≤128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (base:BasisState)(hz:∀q∈Z,base q=false)(hb:∀q∈bank,base q=false)(hi:base cin=false):
 Triple (SquareFrame acc base 0) (head acc Z bank cin src)
  (SquareFrame acc base ((2^138-48*regValue src base)%2^138)):=by
 have tm:=A161NarrowAcc.terms_mem src
 have hf4:=hf _ tm.1
 have hf6:=hf _ tm.2.2.1
 have hf10:=hf _ tm.2.1
 let H:=regValue src base
 have hH:H<2^128:=lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) hsrc)
 have seed:=Acc.seed_triple acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc hf4 base hz
  0 (16*H) (Or.inl (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
 have sub:=ReorderedAcc.op_mod_prefix_triple acc Z bank cin 161 138 (Acc.earlyTerm src true 6)
  hacc (by decide) hf6 (by simp only [Acc.earlyTerm];omega) (by norm_num [Acc.earlyTerm]) base hz hb hi true (16*H)
  (by norm_num at hH ⊢;omega)
 change Triple _ _ (SquareFrame acc base (ReorderedAcc.valueMod (16*H) H 138 6 true)) at sub
 rw [sub_value H hH] at sub
 exact seed.seq sub

end ECDSAAdd.Entrant.ReorderedAHead

end

-- Verified component ReorderedAClear
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAClear
open Arithmetic
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

theorem sub_value(H:Nat)(hH:H<2^128):
 ReorderedAcc.valueMod (976*H) H 138 10 true=(2^138-48*H)%2^138:=by
 simp only [ReorderedAcc.valueMod,if_true]
 norm_num at hH ⊢
 omega

theorem add_value(H:Nat)(hH:H<2^128):
 ReorderedAcc.valueMod ((2^138-48*H)%2^138) H 138 6 false=16*H:=by
 by_cases hz:H=0
 · subst H
   norm_num [ReorderedAcc.valueMod]
 have ht:2^138-48*H<2^138:=by omega
 rw [Nat.mod_eq_of_lt ht]
 simp only [ReorderedAcc.valueMod,Bool.false_eq_true,if_false]
 norm_num at hH ⊢
 omega
































end ECDSAAdd.Entrant.ReorderedAClear

end

-- Verified component ReorderedATail
section
open ECDSAAdd ECDSAAdd.Entrant
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReorderedATail
open ReorderedKnownTail
open Arithmetic

def tail (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  program src Z ((acc.take 138).drop 6) (bank.take 131) cin

theorem tail_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : Acc.Fits acc Z bank cin 161 (Acc.earlyTerm src true 6))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base ((2^138-48*regValue src base)%2^138)) (tail acc Z bank cin src)
      (SquareFrame acc base (16*regValue src base)) := by
  let f:=Acc.earlyTerm src true 6
  let H:=regValue src base
  have hH : H<2^128 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have old:=ReorderedAcc.op_mod_prefix_triple acc Z bank cin 161 138 f hacc (by decide) hf
    (by simp only [f,Acc.earlyTerm];omega) (by norm_num [f,Acc.earlyTerm]) base hz hb hi false ((2^138-48*H)%2^138)
    (Nat.mod_lt _ (by positivity))
  change Triple _ _ (SquareFrame acc base (ReorderedAcc.valueMod ((2^138-48*H)%2^138) H 138 6 false)) at old
  rw [ReorderedAClear.add_value H hH] at old
  have fit:=Acc.fits_prefix acc Z bank cin 161 138 f (by decide) hf (by simp [f,Acc.earlyTerm,hsrc])
  have len : (acc.take 138).length=138 := by simp [hacc]
  have rawEq : Acc.op (acc.take 138) Z bank cin 138 false f=
      addInPlace (src++Z.take 4) ((acc.take 138).drop 6) (bank.take 131) cin := by
    simp [Acc.op,Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc]
  intro s m hs
  have away (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h:=List.nodup_iff_count.mp hf.nd q
    have a:=List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b:=List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
      omega
  have same (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : s.basis q=base q := hs.2 q (away q hq)
  have pref:=regValue_take_drop_of_lt acc 138 ((2^138-48*H)%2^138) s.basis (by omega) hs.1 (Nat.mod_lt _ (by positivity))
  have sy : regValue ((acc.take 138).drop 6) s.basis=((2^138-48*H)%2^138)/64 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
    rfl
  have sh : regValue src s.basis=H := regValue_congr src _ base (fun q hq=>same q (Or.inl (by simp [hq])))
  have sz (q : Wire) (hq : q∈Z) : s.basis q=false :=
    (same q (Or.inl (by simp [hq]))).trans (hz q hq)
  have sb (q : Wire) (hq : q∈bank.take 131) : s.basis q=false :=
    (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
  have si : s.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have nd:=Acc.fits_nodup (acc.take 138) Z bank cin 138 f fit
  have nd' : (cin::((src++Z.take 4)++(acc.take 138).drop 6++bank.take 131)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd
  have zl : 4≤Z.length := by
    have h:=fit.zpad
    simpa [f,Acc.earlyTerm,hsrc] using h
  have bl : (bank.take 131).length=131 := by
    have h:=fit.bankLen
    simp only [f,Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have e:=run_eq_add src Z ((acc.take 138).drop 6) (bank.take 131) cin (by omega) zl
    (by simp [len,hsrc]) (by simp [bl,len]) nd' s m sz sb si H (by simpa only [hsrc] using hH) sh (by simpa only [hsrc] using sy)
  change run (tail acc Z bank cin src) m s=_ at e
  rw [e,←rawEq]
  exact old s m hs

end ECDSAAdd.Entrant.ReorderedATail

end

-- Verified component ReorderedAPlain
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAPlain
open Arithmetic
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def build (acc Z bank:List Wire)(cin:Wire)(src:List Wire):Program:=
 ReorderedAPre.pre acc Z bank cin src++A161Carry.buildPost acc Z bank cin src

def unbuild (acc Z bank:List Wire)(cin:Wire)(src:List Wire):Program:=
 A161Carry.unbuildPre acc Z bank cin src++
 Acc.op (acc.take 138) Z bank cin 138 true (Acc.earlyTerm src false 10)++
 ReorderedATail.tail acc Z bank cin src++Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)

theorem build_triple(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=161)(hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (base:BasisState)(hz:∀q∈Z,base q=false)(hb:∀q∈bank,base q=false)(hi:base cin=false):
 Triple (SquareFrame acc base 0) (build acc Z bank cin src)
  (SquareFrame acc base (4294968272*regValue src base)):=by
 let H:=regValue src base
 have hH:H<2^128:=by simpa only [H,hsrc] using regValue_lt src base
 have hf32:=hf _ (A161NarrowAcc.terms_mem src).2.2.2
 have pre:=ReorderedAPre.pre_triple acc Z bank cin src hacc (by omega) hf base hz hb hi
 have top : Triple (SquareFrame acc base (976*H))
     (Acc.op (acc.take 161) Z bank cin 161 false (Acc.earlyTerm src false 32))
     (SquareFrame acc base (4294968272*H)) := by
   have h := Acc.op_prefix_triple acc Z bank cin 161 161 (Acc.earlyTerm src false 32) hacc
     (by norm_num [Acc.earlyTerm]) hf32 (by simp only [Acc.earlyTerm]; omega) base hz hb hi false (976*H)
     (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm] at hH ⊢;dsimp [H] at *;omega)
   have value : Acc.step base false (976*H) (Acc.earlyTerm src false 32)=4294968272*H := by
     norm_num [Acc.step,Acc.earlyTerm]
     dsimp [H]
     omega
   rw [value] at h
   exact h
 exact pre.seq top

theorem unbuild_triple(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=161)(hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (base:BasisState)(hz:∀q∈Z,base q=false)(hb:∀q∈bank,base q=false)(hi:base cin=false):
 Triple (SquareFrame acc base (4294968272*regValue src base)) (unbuild acc Z bank cin src)
  (SquareFrame acc base 0):=by
 let H:=regValue src base
 have hH:H<2^128:=by simpa only [H,hsrc] using regValue_lt src base
 have tm:=A161NarrowAcc.terms_mem src
 have top:=A161Carry.unbuildPre_triple acc Z bank cin src hacc hsrc hf base hz hb hi
 have sub:=ReorderedAcc.op_mod_prefix_triple acc Z bank cin 161 138 (Acc.earlyTerm src false 10)
  hacc (by decide) (hf _ tm.2.1) (by simp only [Acc.earlyTerm];omega) (by norm_num [Acc.earlyTerm]) base hz hb hi true (976*H)
  (by norm_num at hH ⊢;omega)
 change Triple _ _ (SquareFrame acc base (ReorderedAcc.valueMod (976*H) H 138 10 true)) at sub
 rw [ReorderedAClear.sub_value H hH] at sub
 have tail:=ReorderedATail.tail_triple acc Z bank cin src hacc hsrc (hf _ tm.2.2.1) base hz hb hi
 have seed:=Acc.seed_triple acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc (hf _ tm.1) base hz
  (16*H) 0 (Or.inr (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
 exact ((top.seq sub).seq tail).seq seed



end ECDSAAdd.Entrant.ReorderedAPlain

end

-- Verified component ReorderedABuild
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedABuild
open Arithmetic InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def build (k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire):Program:=
 ReorderedAHead.head acc Z bank cin src++
 ReorderedGenericCache.cachedAdd k src ((acc.take 138).drop 10) (bank.take 127) hs cin++
 A161Carry.buildPost acc Z bank cin src

theorem plain_split(acc Z bank:List Wire)(cin:Wire)(src:List Wire)(hsrc:src.length=128):
 ReorderedAPlain.build acc Z bank cin src=
 ReorderedAHead.head acc Z bank cin src++
 mappedAdd (mappedRead src false) ((acc.take 138).drop 10) (bank.take 127) cin++
 A161Carry.buildPost acc Z bank cin src:=by
 simp [ReorderedAPlain.build,ReorderedAPre.pre,ReorderedAHead.head,Acc.op,
  Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc,MixedLiteralAdderDevelop.read_add_eq,List.append_assoc]

theorem build_frame (k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire)
 (hacc:acc.length=161)(hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0)
 (hk:k≤122)(ndhs:hs.Nodup)(fresh:∀h∈hs,h∉bank)
 (off:∀h∈hs,h∉wires (ReorderedAPlain.build acc Z bank cin src))
 (zero:∀h∈hs,s.basis h=false):
 run (build k acc Z bank cin src hs) m s=
 scatterState hs (ReorderedCacheBits.values 4 k (regValue src s.basis) (976*regValue src s.basis/1024))
  (run (ReorderedAPlain.build acc Z bank cin src) m s):=by
 let H:=regValue src s.basis
 let head:=ReorderedAHead.head acc Z bank cin src
 let t:=run head (m.take (measurementCount head)) s
 have hH:H<2^128:=by simpa only [H,hsrc] using regValue_lt src s.basis
 have hf10:=hf _ (A161NarrowAcc.terms_mem src).2.1
 have preFrame:=ReorderedAHead.head_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s
  (m.take (measurementCount head)) ⟨ha,fun _ _=>rfl⟩
 have away(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):q∉acc:=by
  intro bad
  have h:=List.nodup_iff_count_le_one.mp hf10.nd q
  have a:=List.count_pos_iff.mpr bad
  rcases hq with hq|rfl
  · have b:=List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
    split at h <;> omega
  · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
    omega
 have same(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):t.basis q=s.basis q:=preFrame.2.2 q (away q hq)
 have fit:=ReorderedAcc.fits_prefix acc Z bank cin 161 138 (Acc.earlyTerm src false 10)
  (by decide) hf10 (by simp [Acc.earlyTerm,hsrc]) (by norm_num [Acc.earlyTerm])
 have nd:(cin::(src++(acc.take 138).drop 10++bank.take 127)).Nodup:=by
  simpa [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using
   ReorderedAcc.fits_nodup (acc.take 138) Z bank cin 138 (Acc.earlyTerm src false 10) fit
 have len:(acc.take 138).length=138:=by simp [hacc]
 have bl:(bank.take 127).length=127:=by
  have h:=fit.bankLen
  simp only [Acc.earlyTerm] at h
  simp only [List.length_take]
  omega
 have pref:=regValue_take_drop_of_lt acc 138 ((2^138-48*H)%2^138) t.basis
  (by omega) preFrame.2.1 (Nat.mod_lt _ (by positivity))
 have sy:regValue ((acc.take 138).drop 10) t.basis=((2^138-48*H)%2^138)/1024:=by
  rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
  rfl
 have sh:regValue src t.basis=H:=regValue_congr _ _ _ (fun q hq=>same q (Or.inl (by simp [hq])))
 have sb:∀q∈bank.take 127,t.basis q=false:=by
  intro q hq
  exact (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
 have si:t.basis cin=false:=(same cin (Or.inr rfl)).trans hi
 have vals:=ReorderedCacheBits.forward_values 4 k H (((2^138-48*H)%2^138)/1024) (976*H/1024)
  src ((acc.take 138).drop 10) (bank.take 127) cin t
  (by omega) (by simp only [List.length_drop,len];omega) (by rw [bl];omega)
  nd sb si sh sy (fun j hj=>by
   simpa only [show 128+10=138 by decide] using
    ReorderedCacheArithmetic.high_add_low 128 (4+j+1) H (by omega) hH)
 have frame:=ReorderedGenericCache.cached_context_frame head (A161Carry.buildPost acc Z bank cin src)
  k src ((acc.take 138).drop 10) (bank.take 127) hs cin
  (by omega) (by simp only [List.length_drop,len];omega) (by rw [bl];omega) ndhs
  (fun h hh bad=>fresh h hh (List.mem_of_mem_take bad))
  (by simpa only [head,←plain_split acc Z bank cin src hsrc] using off) s m zero
 have valEq:(((bank.take 127).drop 4).take k).map
  (run (head++carryPrefix (4+k) src ((acc.take 138).drop 10) (bank.take 127) cin)
    (m.take (measurementCount (head++carryPrefix (4+k) src ((acc.take 138).drop 10) (bank.take 127) cin))) s).basis
  =ReorderedCacheBits.values 4 k H (976*H/1024):=by
  simpa only [run_append,measurementCount_append,carryPrefix_measurements,Nat.add_zero,
   List.take_take,Nat.min_self,List.drop_take_self,t] using vals
 rw [valEq] at frame
 simpa only [build,head,←plain_split acc Z bank cin src hsrc,H] using frame

theorem measurement_eq(k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire)
 (hacc:acc.length=161)(hsrc:src.length=128)(hbank:127≤bank.length)(hk:k≤122):
 measurementCount (build k acc Z bank cin src hs)=measurementCount (ReorderedAPlain.build acc Z bank cin src):=by
 have len:(acc.take 138).length=138:=by simp [hacc]
 have bl:(bank.take 127).length=127:=by simp [Nat.min_eq_left hbank]
 have counts:=ReorderedGenericCache.count_balance k src ((acc.take 138).drop 10) (bank.take 127) hs cin
  (by omega) (by simp only [List.length_drop,len];omega) (by rw [bl];omega)
 rw [plain_split acc Z bank cin src hsrc]
 simp only [build,measurementCount_append,counts.2.1]



end ECDSAAdd.Entrant.ReorderedABuild

end

-- Verified component ReorderedAUnbuild
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAUnbuild
open Arithmetic InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def after(acc Z bank:List Wire)(cin:Wire)(src:List Wire):Program:=
 ReorderedATail.tail acc Z bank cin src++Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)
def unbuild(k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire):Program:=
 A161Carry.unbuildPre acc Z bank cin src++
 ReorderedConsumedSub.consumed k src ((acc.take 138).drop 10) (bank.take 127) hs cin++
 after acc Z bank cin src

theorem plain_split(acc Z bank:List Wire)(cin:Wire)(src:List Wire)(hsrc:src.length=128):
 ReorderedAPlain.unbuild acc Z bank cin src=
 A161Carry.unbuildPre acc Z bank cin src++
 ReorderedConsumedSub.plain src ((acc.take 138).drop 10) (bank.take 127) cin++
 after acc Z bank cin src:=by
 simp [ReorderedAPlain.unbuild,ReorderedConsumedSub.plain,after,Acc.op,
  Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc,MixedLiteralAdderDevelop.read_add_eq,subInPlace,List.append_assoc]

theorem unbuild_frame(k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire)
 (hacc:acc.length=161)(hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=4294968272*regValue src s.basis)
 (hk:k≤122)(ndhs:hs.Nodup)(lenhs:hs.length=k)
 (fresh:∀h∈hs,h∉cin::(src++acc++Z++bank))
 (off:∀h∈hs,h∉wires (ReorderedAPlain.unbuild acc Z bank cin src))
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 k (regValue src s.basis) (976*regValue src s.basis/1024)):
 run (unbuild k acc Z bank cin src hs) m s=
 scatterState hs (List.replicate hs.length false) (run (ReorderedAPlain.unbuild acc Z bank cin src) m s):=by
 let H:=regValue src s.basis
 let pre:=A161Carry.unbuildPre acc Z bank cin src
 let t:=run pre (m.take (measurementCount pre)) s
 have hH:H<2^128:=by simpa only [H,hsrc] using regValue_lt src s.basis
 have hf10:=hf _ (A161NarrowAcc.terms_mem src).2.1
 have preFrame:=A161Carry.unbuildPre_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s
  (m.take (measurementCount pre)) ⟨ha,fun _ _=>rfl⟩
 have away(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):q∉acc:=by
  intro bad
  have h:=List.nodup_iff_count_le_one.mp hf10.nd q
  have a:=List.count_pos_iff.mpr bad
  rcases hq with hq|rfl
  · have b:=List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
    split at h <;> omega
  · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
    omega
 have same(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):t.basis q=s.basis q:=preFrame.2.2 q (away q hq)
 have fit:=ReorderedAcc.fits_prefix acc Z bank cin 161 138 (Acc.earlyTerm src false 10)
  (by decide) hf10 (by simp [Acc.earlyTerm,hsrc]) (by norm_num [Acc.earlyTerm])
 have nd:(cin::(src++(acc.take 138).drop 10++bank.take 127)).Nodup:=by
  simpa [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using
   ReorderedAcc.fits_nodup (acc.take 138) Z bank cin 138 (Acc.earlyTerm src false 10) fit
 have alen:(acc.take 138).length=138:=by simp [hacc]
 have bl:(bank.take 127).length=127:=by
  have h:=fit.bankLen
  simp only [Acc.earlyTerm] at h
  simp only [List.length_take]
  omega
 have pref:=regValue_take_drop_of_lt acc 138 (976*H) t.basis
  (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
 have sy:regValue ((acc.take 138).drop 10) t.basis=976*H/1024:=by
  rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [alen];decide),pref.1]
  rfl
 have sh:regValue src t.basis=H:=regValue_congr _ _ _ (fun q hq=>same q (Or.inl (by simp [hq])))
 have sb:∀q∈bank.take 127,t.basis q=false:=by
  intro q hq
  exact (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
 have si:t.basis cin=false:=(same cin (Or.inr rfl)).trans hi
 have savedT:hs.map t.basis=ReorderedCacheBits.values 4 k H (976*H/1024):=by
  rw [List.map_congr_left (fun h hh=>preFrame.2.2 h (by
   intro bad
   exact fresh h hh (by simp [bad])))]
  exact saved
 have freshSmall:∀h∈hs,h∉cin::(src++(acc.take 138).drop 10++bank.take 127):=by
  intro h hh bad
  apply fresh h hh
  simp only [List.mem_cons,List.mem_append] at bad ⊢
  rcases bad with a|((a|a)|a)
  · exact Or.inl a
  · exact Or.inr (Or.inl (Or.inl (Or.inl a)))
  · exact Or.inr (Or.inl (Or.inl (Or.inr (List.mem_of_mem_take (List.mem_of_mem_drop a)))))
  · exact Or.inr (Or.inr (List.mem_of_mem_take a))
 have fr:=ReorderedConsumedSub.frame k src ((acc.take 138).drop 10) (bank.take 127) hs cin
  (by omega) (by simp only [List.length_drop,alen];omega) (by rw [bl];omega)
  (by simp [hsrc,alen]) (by simp [bl,alen]) nd ndhs lenhs freshSmall t
  ((m.drop (measurementCount pre)).take (measurementCount
    (ReorderedConsumedSub.plain src ((acc.take 138).drop 10) (bank.take 127) cin)))
  sb si H (976*H/1024) sh sy savedT
 have count:=ReorderedConsumedSub.measurement_eq k src ((acc.take 138).drop 10) (bank.take 127) hs cin
  (by omega) (by simp only [List.length_drop,alen];omega) (by rw [bl];omega)
 have offAfter:∀h∈hs,h∉wires (after acc Z bank cin src):=by
  intro h hh bad
  apply off h hh
  rw [plain_split acc Z bank cin src hsrc,wires_append,wires_append]
  exact Finset.mem_union_right _ bad
 have result:=ReorderedConsumedSub.replace_middle pre (after acc Z bank cin src)
  (ReorderedConsumedSub.plain src ((acc.take 138).drop 10) (bank.take 127) cin)
  (ReorderedConsumedSub.consumed k src ((acc.take 138).drop 10) (bank.take 127) hs cin)
  hs (List.replicate hs.length false) s m count offAfter fr
 simpa only [unbuild,pre,←plain_split acc Z bank cin src hsrc] using result


end ECDSAAdd.Entrant.ReorderedAUnbuild

end

-- Verified component ReorderedALoop
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedALoop
open Arithmetic InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

theorem loop_eq(k:Nat)(acc Z bank:List Wire)(cin:Wire)(src hs:List Wire)(middle:Program)
 (hacc:acc.length=161)(hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0)
 (hk:k≤122)(nd:hs.Nodup)(len:hs.length=k)
 (fresh:∀h∈hs,h∉cin::(src++acc++Z++bank))
 (offF:∀h∈hs,h∉wires (ReorderedAPlain.build acc Z bank cin src))
 (offI:∀h∈hs,h∉wires (ReorderedAPlain.unbuild acc Z bank cin src))
 (offM:∀h∈hs,h∉wires middle)(zero:∀h∈hs,s.basis h=false)
 (good:WReady acc Z bank cin src (regValue src s.basis)
   (middleState (ReorderedAPlain.build acc Z bank cin src) middle s m)):
 run (ReorderedABuild.build k acc Z bank cin src hs++middle++ReorderedAUnbuild.unbuild k acc Z bank cin src hs) m s=
 run (ReorderedAPlain.build acc Z bank cin src++middle++ReorderedAPlain.unbuild acc Z bank cin src) m s:=by
 let H:=regValue src s.basis
 let vs:=ReorderedCacheBits.values 4 k H (976*H/1024)
 let u:=middleState (ReorderedAPlain.build acc Z bank cin src) middle s m
 let t:=scatterState hs vs u
 have ready:WReady acc Z bank cin src H t:=WReady_scatter acc Z bank cin src H hs vs u fresh good
 have saved:hs.map t.basis=ReorderedCacheBits.values 4 k (regValue src t.basis) (976*regValue src t.basis/1024):=by
  rw [ready.2.1]
  exact scatter_saved_map hs vs u nd (by simp [vs,ReorderedCacheBits.values,len])
 have av:regValue acc t.basis=4294968272*regValue src t.basis:=by
  rw [ready.2.1]
  exact ready.1
 have forward:=ReorderedABuild.build_frame k acc Z bank cin src hs hacc hsrc hf s
  (m.take (measurementCount (ReorderedAPlain.build acc Z bank cin src))) hz hb hi ha hk nd
  (fun h hh bad=>fresh h hh (by simp [bad])) offF zero
 have inverse:=ReorderedAUnbuild.unbuild_frame k acc Z bank cin src hs hacc hsrc hf t
  (m.drop (measurementCount (ReorderedAPlain.build acc Z bank cin src)+measurementCount middle))
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2 av hk nd len fresh offI saved
 have hb127:127≤bank.length:=by
  have h:=(hf _ (A161NarrowAcc.terms_mem src).2.1).bankLen
  norm_num [Acc.earlyTerm] at h
  omega
 have count:=ReorderedABuild.measurement_eq k acc Z bank cin src hs hacc hsrc hb127 hk
 exact cached_pair_many_eq (ReorderedAPlain.build acc Z bank cin src) (ReorderedABuild.build k acc Z bank cin src hs)
  middle (ReorderedAPlain.unbuild acc Z bank cin src) (ReorderedAUnbuild.unbuild k acc Z bank cin src hs)
  hs vs count offF offM offI nd s m zero forward inverse


end ECDSAAdd.Entrant.ReorderedALoop

end

-- Verified component ReorderedAFrame
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAFrame
open ReorderedFrameUnique
set_option autoImplicit false

theorem a_build_eq(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=161)(hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State)(mp mq:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0):
 run (ReorderedAPlain.build acc Z bank cin src) mp s=run (A161NarrowAcc.build8 acc Z bank cin src) mq s:=by
 exact program_eq acc s.basis 0 (4294968272*regValue src s.basis) _ _
  (ReorderedAPlain.build_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi)
  (A161NarrowAcc.build8_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi)
  s mp mq ⟨ha,fun _ _=>rfl⟩

theorem a_unbuild_eq(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=161)(hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State)(mp mq:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=4294968272*regValue src s.basis):
 run (ReorderedAPlain.unbuild acc Z bank cin src) mp s=run (A161SourceAdd.unbuild acc Z bank cin src) mq s:=by
 exact program_eq acc s.basis (4294968272*regValue src s.basis) 0 _ _
  (ReorderedAPlain.unbuild_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi)
  (A161SourceAdd.unbuild_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi)
  s mp mq ⟨ha,fun _ _=>rfl⟩



end ECDSAAdd.Entrant.ReorderedAFrame

end

-- Verified component ReorderedARetape
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedARetape
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ReorderedRetape
set_option autoImplicit false

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
theorem a_middle_eq(acc Z bank:List Wire)(cin:Wire)(src:List Wire)(middle:Program)
 (hacc:acc.length=161)(hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0):
 middleState (ReorderedAPlain.build acc Z bank cin src) middle s m=
 middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s
  (tape (measurementCount (A161NarrowAcc.build8 acc Z bank cin src))
    (measurementCount (ReorderedAPlain.build acc Z bank cin src)) m):=by
 unfold middleState
 rw [drop_tape]
 rw [ReorderedAFrame.a_build_eq acc Z bank cin src hacc hsrc hf s _ _ hz hb hi ha]

theorem a_loop_eq(acc Z bank:List Wire)(cin:Wire)(src:List Wire)(middle:Program)
 (hacc:acc.length=161)(hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0)
 (good:∀record:List Bool,WReady acc Z bank cin src (regValue src s.basis)
   (middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s record)):
 run (ReorderedAPlain.build acc Z bank cin src++middle++ReorderedAPlain.unbuild acc Z bank cin src) m s=
 run (A161NarrowAcc.build8 acc Z bank cin src++middle++A161SourceAdd.unbuild acc Z bank cin src)
  (tape (measurementCount (A161NarrowAcc.build8 acc Z bank cin src))
    (measurementCount (ReorderedAPlain.build acc Z bank cin src)) m) s:=by
 let record:=tape (measurementCount (A161NarrowAcc.build8 acc Z bank cin src))
    (measurementCount (ReorderedAPlain.build acc Z bank cin src)) m
 let u:=middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s record
 have ready:=good record
 have eq:=a_middle_eq acc Z bank cin src middle hacc hsrc hf s m hz hb hi ha
 simp only [run_three]
 change run (ReorderedAPlain.unbuild acc Z bank cin src) _
   (middleState (ReorderedAPlain.build acc Z bank cin src) middle s m)=
  run (A161SourceAdd.unbuild acc Z bank cin src) _ u
 rw [eq]
 apply ReorderedAFrame.a_unbuild_eq acc Z bank cin src hacc hsrc hf u _ _
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2
 rw [ready.2.1]
 exact ready.1


end ECDSAAdd.Entrant.ReorderedARetape

end

-- Verified component ReorderedAFixedPrelude
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAFixed
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ManyACarryDevelop A161Low4Ghost
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked
abbrev L:=A161Low4FixedFold.L
abbrev g:=A161Low4FixedFold.g
abbrev d:=A161Low4FixedFold.d
abbrev q:=A161Low4FixedFold.q
abbrev r:=A161Low4FixedFold.r
abbrev p:=A161Low4FixedFold.p
abbrev hs:=A161Low4FixedFold.hs100
abbrev acc:=ghostAcc L
abbrev pad:=FullPadDevelop.pad L
abbrev bank:=accBank L
abbrev src:=hiReg L
abbrev hw:=A161Low4FixedFold.hw
abbrev hn:=A161Low4FixedFold.hn
def hosts:List Wire:=q::r::p::hs
def loop:Program:=ReorderedABuild.build 103 acc pad bank L.core.cin src hosts++A161Low4FixedFold.checked.out++
 ReorderedAUnbuild.unbuild 103 acc pad bank L.core.cin src hosts

theorem host_geometry:hosts.Nodup ∧ hosts.length=103 ∧
 (∀h∈hosts,h∉L.core.cin::(src++acc++pad++bank)):=by decide +kernel

theorem good_old(base:BasisState)(hc:L.PairClean base)(O:Nat)(hO:O<SquareReduction.p)
 (s:State)(m:List Bool)(hf:SquareFrame L.core.out base O s.basis):
 WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (A161NarrowAcc.build8 acc pad bank L.core.cin src) (A161Low4Fold.aMiddle L g) s m):=by
 have fitSmall:=A161Low4GenericFold.smallFit L hw hn
 have fitFull:=A161Low4GenericFold.fullFit L hw hn
 have haLen:acc.length=161:=ghostAcc_length L hw
 have hsrc:=hiReg_length L hw
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hzFull:∀u∈accZ L,s.basis u=false:=by
  intro u hu
  rcases accZ_mem L u hu with hu|hu
  · exact (regValue_zero _ _).mp clean.pad u hu
  · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>hzFull u ((FullPadDevelop.pad_sublist L).subset hu)
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>(regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue acc s.basis=0:=ghostAcc_zero L s.basis clean
 have old:=A161Low4Fold.ghost_middle_good L hw hn g A161Low4FixedFold.ready.1 base hc O hO s m hf
 simp only [A161Fold.wBuild] at old
 rw [←A161Low4Structural.build_eq L] at old
 have eq:=A161Repad.middle_repad acc (accZ L) pad bank L.core.cin src (A161Low4Fold.aMiddle L g)
  haLen hsrc fitFull fitSmall s m hzFull hz hb clean.cin ha
 rw [←eq]
 exact ⟨old.1,old.2.1,(fun u hu=>old.2.2.1 u ((FullPadDevelop.pad_sublist L).subset hu)),old.2.2.2⟩


end ECDSAAdd.Entrant.ReorderedAFixed

end

-- Verified component ReorderedAFixedSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAFixed
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedAFixed
set_option autoImplicit false

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem lengths:acc.length=161 ∧ pad.length=31 ∧ bank.length=160 ∧ src.length=128:=by decide +kernel
theorem fits:∀f∈earlyHTerms src,Acc.Fits acc pad bank L.core.cin 161 f:=
 A161Low4GenericFold.smallFit L hw hn

theorem off_plain:∀h∈hosts,h∉wires (ReorderedAPlain.build acc pad bank L.core.cin src) ∧
 h∉wires (ReorderedAPlain.unbuild acc pad bank L.core.cin src):=by
 have f6:=ReorderedAcc.fits_prefix acc pad bank L.core.cin 161 138 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have f10:=ReorderedAcc.fits_prefix acc pad bank L.core.cin 161 138 (Acc.earlyTerm src false 10)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.1) (by decide) (by decide)
 have f32:=Acc.fits_prefix acc pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide)
 have w6:=ReorderedAcc.op_wires (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6) (by decide) f6
 have w10(neg:Bool):=ReorderedAcc.op_wires (acc.take 138) pad bank L.core.cin 138 neg (Acc.earlyTerm src false 10) (by decide) f10
 have w32:=Acc.op_wires (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32) (by decide) f32
 have small6:∀h∈hosts,h∉(L.core.cin::(Acc.tx pad 138 (Acc.earlyTerm src true 6)++
  Acc.ty (acc.take 138) (Acc.earlyTerm src true 6)++Acc.tc bank 138 (Acc.earlyTerm src true 6))).toFinset:=by
  simp only [List.mem_toFinset]
  decide +kernel
 have small10:∀h∈hosts,h∉(L.core.cin::(Acc.tx pad 138 (Acc.earlyTerm src false 10)++
  Acc.ty (acc.take 138) (Acc.earlyTerm src false 10)++Acc.tc bank 138 (Acc.earlyTerm src false 10))).toFinset:=by
  simp only [List.mem_toFinset]
  decide +kernel
 have small32:∀h∈hosts,h∉(L.core.cin::(Acc.tx pad 161 (Acc.earlyTerm src false 32)++
  Acc.ty (acc.take 161) (Acc.earlyTerm src false 32)++Acc.tc bank 161 (Acc.earlyTerm src false 32))).toFinset:=by
  simp only [List.mem_toFinset]
  decide +kernel
 have seed:=Acc.seed_support acc pad bank L.core.cin 161 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (A161NarrowAcc.terms_mem src).1)
 have tailSupport:=KnownOutputAdder.program_support (mappedRead (src++pad.take 4) false)
  (ReorderedKnownTail.desired src) ((acc.take 138).drop 6) (bank.take 131) L.core.cin
 rw [mappedRead_wires,ReorderedKnownTail.desired_wires] at tailSupport
 have smallTail:∀h∈hosts,h∉((src++pad.take 4)++src.drop 2++(acc.take 138).drop 6++bank.take 131++[L.core.cin]).toFinset:=by
  simp only [List.mem_toFinset]
  decide +kernel
 intro h hh
 have seedOff:h∉wires (Acc.seedOp acc pad 161 (Acc.earlyTerm src false 4)):=by
  intro bad
  exact host_geometry.2.2 h hh (by simpa only [Acc.earlyTerm,List.mem_toFinset] using seed bad)
 have op6Off:h∉wires (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6)):=by
  rw [w6];exact small6 h hh
 have op10Off(neg:Bool):h∉wires (Acc.op (acc.take 138) pad bank L.core.cin 138 neg (Acc.earlyTerm src false 10)):=by
  rw [w10 neg];exact small10 h hh
 have op32Off:h∉wires (Acc.op (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32)):=by
  rw [w32];exact small32 h hh
 have tailOff:h∉wires (ReorderedATail.tail acc pad bank L.core.cin src):=by
  exact fun bad=>smallTail h hh (tailSupport bad)
 have oldOff: h∉wires (A161SourceAdd.unbuild acc pad bank L.core.cin src):=
  (A161Carry.wloop_original_off acc pad bank L.core.cin src h lengths.1 lengths.2.2.2 fits
   (host_geometry.2.2 h hh)).2
 have preOff:h∉wires (A161Carry.unbuildPre acc pad bank L.core.cin src):=by
  have pieces:=oldOff
  simp only [A161SourceAdd.unbuild,wires_append,Finset.mem_union,not_or] at pieces
  exact pieces.1.1.1
 constructor
 · simpa only [ReorderedAPlain.build,ReorderedAPre.pre,A161Carry.buildPost,wires_append,
    Finset.mem_union,not_or,and_assoc] using And.intro seedOff (And.intro op6Off (And.intro (op10Off false) op32Off))
 · simpa only [ReorderedAPlain.unbuild,wires_append,Finset.mem_union,not_or,and_assoc] using
    And.intro preOff (And.intro (op10Off true) (And.intro tailOff seedOff))


end ECDSAAdd.Entrant.ReorderedAFixed

end

-- Verified component ReorderedAPlainFrame
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAFixed
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ManyACarryDevelop A161Low4Ghost
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem transport(Q:BasisState→Prop)(s a b:State)(e:a=b)(hb:b.phase=s.phase ∧ Q b.basis):
 a.phase=s.phase ∧ Q a.basis:=e.symm ▸ hb

theorem plain_frame(base:BasisState)(hc:L.PairClean base)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O)
  (ReorderedAPlain.build acc pad bank L.core.cin src++A161Low4Fold.aMiddle L g++ReorderedAPlain.unbuild acc pad bank L.core.cin src)
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hzFull:∀u∈accZ L,s.basis u=false:=by
  intro u hu
  rcases accZ_mem L u hu with hu|hu
  · exact (regValue_zero _ _).mp clean.pad u hu
  · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>hzFull u ((FullPadDevelop.pad_sublist L).subset hu)
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>(regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue acc s.basis=0:=ghostAcc_zero L s.basis clean
 have ready:=fun record=>good_old base hc O hO s record hf
 have eq:=ReorderedARetape.a_loop_eq acc pad bank L.core.cin src (A161Low4Fold.aMiddle L g)
  lengths.1 lengths.2.2.2 fits s m hz hb clean.cin ha ready
 let record:=ReorderedRetape.tape (measurementCount (A161NarrowAcc.build8 acc pad bank L.core.cin src))
  (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)) m
 have fullfit:=A161Low4GenericFold.fullFit L hw hn
 have oldGood:=A161Low4Fold.ghost_middle_good L hw hn g A161Low4FixedFold.ready.1 base hc O hO s record hf
 simp only [A161Fold.wBuild] at oldGood
 rw [←A161Low4Structural.build_eq L] at oldGood
 have repad:=A161Repad.plain_loop_repad acc (accZ L) pad bank L.core.cin src (A161Low4Fold.aMiddle L g)
  lengths.1 lengths.2.2.2 fullfit fits (FullPadDevelop.pad_sublist L).subset s record hzFull hb clean.cin ha
  (regValue src s.basis) (by simpa only [middleState,run_take] using oldGood)
 have assoc:((A161Fold.wBuild L++A161Low4Fold.aMiddle L g)++A161Fold.wUnbuild L)=
  (A161NarrowAcc.build8 acc (accZ L) bank L.core.cin src++A161Low4Fold.aMiddle L g++A161SourceAdd.unbuild acc (accZ L) bank L.core.cin src):=by
  dsimp only [acc,bank,src]
  rw [A161Low4Structural.build_eq,A161Low4Structural.unbuild_eq]
  all_goals rfl
 have finalEq:=eq.trans (repad.symm.trans (congrArg (fun P:Program=>run P record s) assoc.symm))
 have old:=A161Low4Fold.plain_frame L hw hn g A161Low4FixedFold.ready.1 base hc O hO s record hf
 simp only [A161Low4Fold.wBuild,A161Low4Fold.wUnbuild,A161Low4Fold.cFlipK] at old
 dsimp only at finalEq
 exact transport (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)) s _ _ finalEq old


end ECDSAAdd.Entrant.ReorderedAFixed

end

-- Verified component ReorderedAFixedFrame
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAFixed
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ManyACarryDevelop A161Low4Ghost
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked

theorem off_middle:∀h∈hosts,h∉wires A161Low4FixedFold.checked.out:=by
 have rd:=A161Low4FixedFold.ready
 rcases rd with ⟨hg,hl,hnd,hfresh,hne,fq,fr,fp,rq,pq,pr,fmid⟩
 have sub:=(A161Low4FixedFold.cert100.support hs (A161Low4Fold.aMiddle L g) A161Low4FixedFold.checked.out).1
 have free:=(A161Low4FixedFold.cert100.support hs (A161Low4Fold.aMiddle L g) A161Low4FixedFold.checked.out).2
 have orig(u:Wire)(hu:u∈[q,r,p]):u∉wires (A161Low4Fold.aMiddle L g):=
  A161Low4GenericFold.free_middle L g u (fmid u hu).1 (fmid u hu).2.1
 change ∀h∈q::r::p::hs,h∉wires A161Low4FixedFold.checked.out
 rw [List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons]
 exact ⟨(fun bad=>orig q (by simp) (sub bad)),(fun bad=>orig r (by simp) (sub bad)),
  (fun bad=>orig p (by simp) (sub bad)),free⟩

theorem frame(base:BasisState)(hc:L.PairClean base)(hsum:base q=false)(hV:base r=false)(hP:base p=false)
 (hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loop
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hzFull:∀u∈accZ L,s.basis u=false:=by
  intro u hu
  rcases accZ_mem L u hu with hu|hu
  · exact (regValue_zero _ _).mp clean.pad u hu
  · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>hzFull u ((FullPadDevelop.pad_sublist L).subset hu)
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>(regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue acc s.basis=0:=ghostAcc_zero L s.basis clean
 have qz:s.basis q=false:=(hf.2 q (by decide)).trans hsum
 have rz:s.basis r=false:=(hf.2 r (by decide)).trans hV
 have pz:s.basis p=false:=(hf.2 p (by decide)).trans hP
 have zeroU:∀u∈hs,s.basis u=false:=fun u hu=>
  (hf.2 u (A161Low4FixedFold.hostClean base hc hd u hu).1).trans (A161Low4FixedFold.hostClean base hc hd u hu).2
 have zero:∀u∈hosts,s.basis u=false:=by
  change ∀u∈q::r::p::hs,s.basis u=false
  rw [List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons]
  exact ⟨qz,rz,pz,zeroU⟩
 have offHs:∀u∈hs,u∉wires (ReorderedAPlain.build acc pad bank L.core.cin src):=by
  intro u hu
  exact (off_plain u (by change u∈q::r::p::hs;simp only [List.mem_cons];exact Or.inr (Or.inr (Or.inr hu)))).1
 have goodOriginal:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) (A161Low4Fold.aMiddle L g) s m):=by
  rw [ReorderedARetape.a_middle_eq acc pad bank L.core.cin src (A161Low4Fold.aMiddle L g)
   lengths.1 lengths.2.2.2 fits s m hz hb clean.cin ha]
  exact good_old base hc O hO s _ hf
 have middleEq:=A161Low4FixedFold.cert100.middle_eq hs (A161Low4Fold.aMiddle L g) A161Low4FixedFold.checked.out
  (ReorderedAPlain.build acc pad bank L.core.cin src) s m zeroU offHs
 have good:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out s m):=by
  rw [middleEq]
  exact goodOriginal
 have cached:=ReorderedALoop.loop_eq 103 acc pad bank L.core.cin src hosts A161Low4FixedFold.checked.out
  lengths.1 lengths.2.2.2 fits s m hz hb clean.cin ha (by decide) host_geometry.1 host_geometry.2.1 host_geometry.2.2
  (fun u hu=>(off_plain u hu).1) (fun u hu=>(off_plain u hu).2) off_middle zero good
 have middleReplace:=A161Low4FixedFold.cert100.surround_eq hs (A161Low4Fold.aMiddle L g) A161Low4FixedFold.checked.out
  (ReorderedAPlain.build acc pad bank L.core.cin src) (ReorderedAPlain.unbuild acc pad bank L.core.cin src) s m zeroU offHs
 have eq:run loop m s=run (ReorderedAPlain.build acc pad bank L.core.cin src++A161Low4Fold.aMiddle L g++
  ReorderedAPlain.unbuild acc pad bank L.core.cin src) m s:=cached.trans middleReplace
 exact transport _ s _ _ eq (plain_frame base hc O hO s m hf)



end ECDSAAdd.Entrant.ReorderedAFixed

end

-- Verified component ReorderedKnownA
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedKnownA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedAFixed KnownSparseFold ZeroReadDevelop A161Low4Ghost
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked

abbrev hosts:=ReorderedAFixed.hosts

theorem guard:∀u∈KnownAMidStaged.known0,u∉hosts ∧ u∉acc ∧ (u∈bank ∨ u=L.core.cin):=by decide +kernel

































theorem context_eq(A B N C:Program)(s:State)(m:List Bool)
 (hm:measurementCount N=measurementCount B)
 (he:run N (m.drop (measurementCount A)) (run A m s)=run B (m.drop (measurementCount A)) (run A m s)):
 run (A++N++C) m s=run (A++B++C) m s:=by
 simp only [run_cat,measurementCount_append,hm,he]

def loop:Program:=ReorderedABuild.build 103 acc pad bank L.core.cin src hosts++KnownAMidStaged.body++
 ReorderedAUnbuild.unbuild 103 acc pad bank L.core.cin src hosts





















def fold:Program:=loop

def rawBody:Program:=measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold)
















def body:Program:=rawBody++ReorderedRecordPadding.program 4 L.core.cin















end ECDSAAdd.Entrant.ReorderedKnownA

end

-- Verified component ReorderedAPhysical
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAPhysical
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedAFixed
set_option autoImplicit false

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires A161Low4FixedFold.checked
abbrev hosts:=ReorderedAFixed.hosts

end ECDSAAdd.Entrant.ReorderedAPhysical

end

-- Verified component ReorderedACounts
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedACounts
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedAFixed ControlLoan1589BFFold
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount

abbrev hosts:=ReorderedAFixed.hosts

theorem cache_counts:
 toffoliCount (ReorderedGenericCache.cachedAdd 103 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=127 ∧
 measurementCount (ReorderedGenericCache.cachedAdd 103 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=127 ∧
 toffoliCount (ReorderedGenericCache.consumedAdd 103 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=24 ∧
 measurementCount (ReorderedGenericCache.consumedAdd 103 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=127:=by
 have old:=addInPlace_counts src ((acc.take 138).drop 10) (bank.take 127) L.core.cin (by decide) (by decide)
 rw [←MixedLiteralAdderDevelop.read_add_eq] at old
 have bal:=ReorderedGenericCache.count_balance 103 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin
  (by decide) (by decide) (by decide)
 change toffoliCount (mappedAdd (mappedRead src false) ((acc.take 138).drop 10) (bank.take 127) L.core.cin)=127 ∧
  measurementCount (mappedAdd (mappedRead src false) ((acc.take 138).drop 10) (bank.take 127) L.core.cin)=127 at old
 omega

theorem pieces:
 toffoliCount (ReorderedABuild.build 103 acc pad bank L.core.cin src hosts)=386 ∧
 measurementCount (ReorderedABuild.build 103 acc pad bank L.core.cin src hosts)=386 ∧
 toffoliCount (ReorderedAUnbuild.unbuild 103 acc pad bank L.core.cin src hosts)=129 ∧
 measurementCount (ReorderedAUnbuild.unbuild 103 acc pad bank L.core.cin src hosts)=386:=by
 have f6:=Acc.fits_prefix acc pad bank L.core.cin 161 138 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide)
 have f32:=Acc.fits_prefix acc pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide)
 have seed:=Acc.seed_counts acc pad bank L.core.cin 161 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (A161NarrowAcc.terms_mem src).1).toFitsLen
 have sub:=Acc.op_counts (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6) (by decide) f6.toFitsLen
 have top:=Acc.op_counts (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32) (by decide) f32.toFitsLen
 have preInv:=CodexNarrowTailResource.accSub_counts 106 (acc.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32)
  (by decide) f32.toFitsLen (by decide)
 have tail:=ReorderedKnownTail.counts src pad ((acc.take 138).drop 6) (bank.take 131) L.core.cin
  (by decide) (by decide) (by decide) (by decide)
 have notC:=notRegister_counts ((acc.take 138).drop 10)
 have cache:=cache_counts
 change toffoliCount (ReorderedATail.tail acc pad bank L.core.cin src)=0 ∧
  measurementCount (ReorderedATail.tail acc pad bank L.core.cin src)=131 at tail
 change toffoliCount (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6))=131 ∧
  measurementCount (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6))=131 at sub
 change toffoliCount (Acc.op (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32))=128 ∧
  measurementCount (Acc.op (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32))=128 at top
 change toffoliCount (CodexKnownOnesTail.accSub 106 (acc.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32))=105 ∧
  measurementCount (CodexKnownOnesTail.accSub 106 (acc.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32))=128 at preInv
 simp only [ReorderedABuild.build,ReorderedAHead.head,A161Carry.buildPost,
  ReorderedAUnbuild.unbuild,ReorderedAUnbuild.after,ReorderedConsumedSub.consumed,A161Carry.unbuildPre,
  toffoliCount_append,measurementCount_append]
 omega


end ECDSAAdd.Entrant.ReorderedACounts

end

-- Verified component ReorderedAStructural
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedAStructural
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout A161Low4Ghost A161Low4Structural
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

theorem build_eq(L:CuccaroStreamedSquareWideLayout)(k:Nat)(Z bank src hs:List Wire)(cin:Wire):
 ReorderedABuild.build k (ghostAcc L) Z bank cin src hs=
 ReorderedABuild.build k (A161Fold.accReg L) Z bank cin src hs:=by
 simp only [ReorderedABuild.build,ReorderedAHead.head,A161Carry.buildPost,Acc.seedOp,Acc.op]
 rw [ty L src false 4 (by decide),ty_take L src true 138 6 (by decide),
  ghostAcc_take_drop L 138 10 (by decide),ty_take L src false 161 32 (by decide)]
 rfl

theorem unbuild_eq(L:CuccaroStreamedSquareWideLayout)(k:Nat)(Z bank src hs:List Wire)(cin:Wire):
 ReorderedAUnbuild.unbuild k (ghostAcc L) Z bank cin src hs=
 ReorderedAUnbuild.unbuild k (A161Fold.accReg L) Z bank cin src hs:=by
 simp only [ReorderedAUnbuild.unbuild,ReorderedAUnbuild.after,A161Carry.unbuildPre,
  CodexKnownOnesTail.accSub,ReorderedATail.tail,Acc.seedOp]
 rw [ty_take L src false 161 32 (by decide),ghostAcc_take_drop L 138 10 (by decide),
  ghostAcc_take_drop L 138 6 (by decide),ty L src false 4 (by decide)]
 rfl



end ECDSAAdd.Entrant.ReorderedAStructural

end

-- Verified component ReorderedASlots
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedASlots
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedAFixed OwnDiagAll12Square
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] Challenge.gateSlots
abbrev hosts:=ReorderedAFixed.hosts

theorem pieces:
 Challenge.gateSlots (ReorderedABuild.build 103 acc pad bank L.core.cin src hosts)≤10000 ∧
 Challenge.gateSlots (ReorderedAUnbuild.unbuild 103 acc pad bank L.core.cin src hosts)≤10000:=by
 have seed:Challenge.gateSlots (Acc.seedOp acc pad 161 (Acc.earlyTerm src false 4))≤200:=by
  rw [Acc.seedOp,Baselines.copyRegister_gateSlots]
  decide +kernel
 have sub:=Acc.op_gateSlots (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6)
 change Challenge.gateSlots (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6))≤1848 at sub
 have top:=Acc.op_gateSlots (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32)
 change Challenge.gateSlots (Acc.op (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32))≤1806 at top
 have old:=Baselines.addInPlace_gateSlots_le src ((acc.take 138).drop 10) (bank.take 127) L.core.cin
 rw [←MixedLiteralAdderDevelop.read_add_eq] at old
 change Challenge.gateSlots (mappedAdd (mappedRead src false) ((acc.take 138).drop 10) (bank.take 127) L.core.cin)≤1536 at old
 have cache:=ReorderedSlots.cache 103 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin
  (by decide) (by decide) (by decide) ReorderedAFixed.host_geometry.2.1
 have cacheBound:Challenge.gateSlots (ReorderedGenericCache.cachedAdd 103 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)≤1919:=by omega
 have consumeBound:Challenge.gateSlots (ReorderedConsumedSub.consumed 103 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)≤2080:=by
  have n:=Baselines.notRegister_gateSlots ((acc.take 138).drop 10)
  change Challenge.gateSlots (notRegister ((acc.take 138).drop 10))=128 at n
  simp only [ReorderedConsumedSub.consumed,Challenge.gateSlots_append]
  omega
 have f32:=Acc.fits_prefix acc pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide)
 have preInv:=CodexNarrowTailResource.accSub_slots 106 (acc.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32)
  (by decide) f32.toFitsLen (by decide)
 have topInv:=Acc.op_gateSlots (acc.take 161) pad bank L.core.cin 161 true (Acc.earlyTerm src false 32)
 change Challenge.gateSlots (Acc.op (acc.take 161) pad bank L.core.cin 161 true (Acc.earlyTerm src false 32))≤1806 at topInv
 have tail:=Win977Develop.known_slots (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
  ((acc.take 138).drop 6) (bank.take 131) L.core.cin
 change Challenge.gateSlots (ReorderedATail.tail acc pad bank L.core.cin src)≤1848 at tail
 simp only [ReorderedABuild.build,ReorderedAHead.head,A161Carry.buildPost,
  ReorderedAUnbuild.unbuild,ReorderedAUnbuild.after,A161Carry.unbuildPre,Challenge.gateSlots_append]
 constructor <;> omega

theorem body_slots:Challenge.gateSlots ReorderedKnownA.body≤112000:=by
 have known:Challenge.gateSlots KnownAMidStaged.body≤19000:=by decide +kernel
 have pre1:=measuredFoldQ_gateSlotsTq L hw (negP L)
 have pre2:=measuredFoldQ_gateSlotsTq L hw (rot128F L)
 have bounds:=pieces
 have padding:=(ReorderedRecordPadding.counts 4 L.core.cin).2.2
 simp only [hosts] at bounds
 simp only [ReorderedKnownA.body,ReorderedKnownA.rawBody,ReorderedKnownA.fold,ReorderedKnownA.loop,
  ReorderedKnownA.hosts,Challenge.gateSlots_append]
 omega

end ECDSAAdd.Entrant.ReorderedASlots

end

-- Verified component ReorderedABalance
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ReorderedABalance
open Arithmetic InverseCarryDevelop ThirdSavedCarryDevelop ReorderedAFixed
set_option autoImplicit false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
abbrev p:=ReorderedAFixed.p

theorem old_pieces:
 toffoliCount (A161Carry.buildMany 100 acc pad bank L.core.cin src hs q r p)=387 ∧
 measurementCount (A161Carry.buildMany 100 acc pad bank L.core.cin src hs q r p)=388 ∧
 toffoliCount (A161Carry.unbuildMany 100 acc pad bank L.core.cin src hs q r p)=130 ∧
 measurementCount (A161Carry.unbuildMany 100 acc pad bank L.core.cin src hs q r p)=388:=by
 have len:=lengths
 have fit:=fits
 have b:=A161KnownTail.build8_counts acc pad bank L.core.cin src len.1 (by decide)
  (fun f h=>(fit f h).toFitsLen)
 rw [A161KnownTail.build8_eq] at b
 have u:=A161SourceAdd.unbuild_resources acc pad bank L.core.cin src len.1 len.2.2.2
  (fun f h=>(fit f h).toFitsLen)
 have bc:=A161Carry.buildCached_counts acc pad bank L.core.cin src q len.1 len.2.2.2 (by decide) (by decide)
 have bd:=A161Carry.buildDual_counts acc pad bank L.core.cin src q r len.1 len.2.2.2 (by decide) (by decide)
 have bt:=A161Carry.buildTriple_counts acc pad bank L.core.cin src q r p len.1 len.2.2.2 (by decide) (by decide)
 have bm:=A161Carry.buildMany_counts 100 acc pad bank L.core.cin src hs q r p len.1 len.2.2.2
  (by decide) (by decide) (by decide) (by decide)
 have uc:=A161Carry.unbuildConsumed_counts acc pad bank L.core.cin src q len.1 len.2.2.2 (by decide)
 have ud:=A161Carry.unbuildDual_counts acc pad bank L.core.cin src q r len.1 len.2.2.2 (by decide)
 have ut:=A161Carry.unbuildTriple_counts acc pad bank L.core.cin src q r p len.1 len.2.2.2 (by decide)
 have um:=A161Carry.unbuildMany_counts 100 acc pad bank L.core.cin src hs q r p len.1 len.2.2.2
  (by decide) (by decide) (by decide)
 omega

theorem balance:toffoliCount ReorderedKnownA.body+10=toffoliCount A161Low4FixedFold.body ∧
 measurementCount ReorderedKnownA.body=measurementCount A161Low4FixedFold.body:=by
 have old:=old_pieces
 simp only [p] at old
 have new:=ReorderedACounts.pieces
 have mid:=KnownSparseFold.Cert.counts _ _ _ _ _ KnownAMidStaged.cert
 change toffoliCount KnownAMidStaged.body+8=toffoliCount A161Low4FixedFold.checked.out ∧
  measurementCount KnownAMidStaged.body=measurementCount A161Low4FixedFold.checked.out at mid
 have pad:=ReorderedRecordPadding.counts 4 L.core.cin
 simp only [ReorderedACounts.hosts] at new
 simp only [ReorderedKnownA.body,ReorderedKnownA.rawBody,ReorderedKnownA.loop,ReorderedKnownA.fold,ReorderedKnownA.hosts,
  A161Low4FixedFold.body,A161Low4FixedFold.fold100,A161Low4GenericFold.loop,toffoliCount_append,measurementCount_append]
 simp only [ReorderedAFixed.L,ReorderedAFixed.g] at *
 rw [←A161Low4Structural.buildMany_eq A161Low4FixedFold.L 100,←A161Low4Structural.unbuildMany_eq A161Low4FixedFold.L 100]
 simp only [ReorderedAFixed.L,ReorderedAFixed.acc,ReorderedAFixed.pad,ReorderedAFixed.bank,ReorderedAFixed.src,ReorderedAFixed.hs,ReorderedAFixed.q,ReorderedAFixed.r,ReorderedAFixed.p] at old new ⊢
 simp only [A161Low4FixedFold.q,A161Low4FixedFold.r,A161Low4FixedFold.p] at old
 omega


end ECDSAAdd.Entrant.ReorderedABalance

end

-- Verified component SignExtendThree
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.SignExtendThree
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem constant(r:List Wire)(b:Bool):regValue r (fun _=>b)=b.toNat*(2^r.length-1):=by
 induction r with
 | nil=>simp [regValue]
 | cons a r ih=>
  simp only [regValue,List.foldr_cons,List.length_cons,Nat.pow_succ]
  change (if b then 1 else 0)+2*regValue r (fun _=>b)=_
  rw [ih]
  have p:0<2^r.length:=by positivity
  cases b <;> simp only [Bool.toNat_false,Bool.toNat_true,Bool.false_eq_true,if_false,if_true,Nat.zero_mul,Nat.one_mul] <;> omega

theorem extend_frame(xs ys zs:List Wire)(q:Wire)(base:BasisState)(V:Nat)(b:Bool)
 (nd:(xs++ys++zs).Nodup)(l3:ys.length=3)(off:q∉ys)
 (s:State)(m:List Bool)(hV:V<2^xs.length)
 (frame:SquareFrame (xs++ys++zs) base V s.basis)(bit:s.basis q=b):
 (run (signComplement q ys) m s).phase=s.phase ∧
 SquareFrame (xs++ys++zs) base (V+(if b then 7*2^xs.length else 0))
  (run (signComplement q ys) m s).basis:=by
 have ndx:xs.Nodup:=(List.nodup_append'.mp (List.nodup_append'.mp nd).1).1
 have ndy:ys.Nodup:=(List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1
 have disxy:List.Disjoint xs ys:=(List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.2
 have disyz:List.Disjoint ys zs:=by
  intro u hy hz
  exact List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 (List.mem_append_right _ hy) hz
 have split:regValue (xs++ys++zs) s.basis=regValue xs s.basis+2^xs.length*(regValue ys s.basis+8*regValue zs s.basis):=by
  simp only [regValue_append,List.length_append,Nat.pow_add,l3]
  norm_num
  ring
 have high:regValue ys s.basis+8*regValue zs s.basis=0:=by
  by_contra hn
  have h:1≤regValue ys s.basis+8*regValue zs s.basis:=by omega
  have le:=Nat.mul_le_mul_left (2^xs.length) h
  simp only [Nat.mul_one] at le
  rw [frame.1] at split
  omega
 have hy:∀u∈ys,s.basis u=false:=(regValue_zero _ _).mp (by omega)
 have hz:regValue zs s.basis=0:=by omega
 have low:regValue xs s.basis=V:=by rw [high,Nat.mul_zero,Nat.add_zero,frame.1] at split;exact split.symm
 have out:=narrow_fanout_correct q ys ndy off s m
 rw [out]
 refine ⟨rfl,?_,?_⟩
 · have xeq:regValue xs (fun a=>if a∈ys then s.basis a ^^ s.basis q else s.basis a)=V:=by
    rw [←low]
    apply regValue_congr
    intro u hu
    simp only [if_neg (fun bad=>List.disjoint_left.mp disxy hu bad)]
   have yeq:regValue ys (fun a=>if a∈ys then s.basis a ^^ s.basis q else s.basis a)=b.toNat*7:=by
    have eq:=regValue_congr ys (fun a=>if a∈ys then s.basis a ^^ s.basis q else s.basis a) (fun _=>b)
     (fun a ha=>by simp only [ha,if_true,hy a ha,Bool.false_xor,bit])
    rw [eq,constant,l3]
    norm_num
   have zeq:regValue zs (fun a=>if a∈ys then s.basis a ^^ s.basis q else s.basis a)=0:=by
    rw [←hz]
    apply regValue_congr
    intro u hu
    simp only [if_neg (fun bad=>List.disjoint_left.mp disyz bad hu)]
   simp only [regValue_append,List.length_append,Nat.pow_add,xeq,yeq,zeq,Nat.mul_zero,Nat.add_zero]
   cases b <;> simp <;> omega
 · intro u hu
   have no:u∉ys:=fun h=>hu (List.mem_append_left _ (List.mem_append_right _ h))
   simp only [if_neg no]
   exact frame.2 u hu

end ECDSAAdd.Entrant.SignExtendThree

end

-- Verified component SignAHead
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SignAHead
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed ManyACarryDevelop InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

def value(H:Nat):Nat:=(2^135-48*H)%2^135

theorem sub_value(H:Nat)(hH:H<2^128):
 ReorderedAcc.valueMod (16*H) H 135 6 true=value H:=by
 simp only [ReorderedAcc.valueMod,if_true,value]
 norm_num at hH ⊢
 omega

def small:Program:=Acc.seedOp acc pad 161 (Acc.earlyTerm src false 4)++
 Acc.op (acc.take 135) pad bank L.core.cin 135 true (Acc.earlyTerm src true 6)

def extension:Program:=signComplement (acc.getD 134 0) ((acc.drop 135).take 3)
def head:Program:=small++extension

theorem small_frame(base:BasisState)(hz:∀q∈pad,base q=false)(hb:∀q∈bank,base q=false)(hi:base L.core.cin=false):
 Triple (SquareFrame acc base 0) small (SquareFrame acc base (value (regValue src base))):=by
 let H:=regValue src base
 have hH:H<2^128:=by simpa only [H,lengths.2.2.2] using regValue_lt src base
 have seed:=Acc.seed_triple acc pad bank L.core.cin 161 (Acc.earlyTerm src false 4) lengths.1
  (fits _ (A161NarrowAcc.terms_mem src).1) base hz 0 (16*H) (Or.inl (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
 have sub:=ReorderedAcc.op_mod_prefix_triple acc pad bank L.core.cin 161 135 (Acc.earlyTerm src true 6)
  lengths.1 (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1)
  (by decide) (by decide) base hz hb hi true (16*H) (by norm_num at hH ⊢;omega)
 change Triple _ _ (SquareFrame acc base (ReorderedAcc.valueMod (16*H) H 135 6 true)) at sub
 rw [sub_value H hH] at sub
 exact seed.seq sub

theorem sign(H:Nat)(hH:H<2^128)(s:BasisState)(hv:regValue acc s=value H):
 s (acc.getD 134 0)=decide (H≠0):=by
 apply bool_nat_injective
 rw [regValue_bit acc 134 0 s (by decide),hv]
 by_cases h:H=0
 · subst H
   norm_num [value]
 · have low:2^134≤value H:=by
    have :48*H<2^134:=by norm_num at hH ⊢;omega
    unfold value
    have lt:2^135-48*H<2^135:=by norm_num at hH ⊢;omega
    rw [Nat.mod_eq_of_lt lt]
    norm_num at hH ⊢
    omega
   have high:value H<2^135:=Nat.mod_lt _ (by positivity)
   have d:value H/2^134=1:=Nat.div_eq_of_lt_le (k:=1) (by simpa using low) (by norm_num at high ⊢;omega)
   simp only [d,h,ne_eq,not_false_eq_true,decide_true,Bool.toNat_true]

theorem value_extend(H:Nat)(hH:H<2^128):
 value H+(if decide (H≠0) then 7*2^135 else 0)=(2^138-48*H)%2^138:=by
 by_cases h:H=0
 · subst H
   norm_num [value]
 · simp only [h,ne_eq,not_false_eq_true,decide_true,if_true,value]
   have a:2^135-48*H<2^135:=by norm_num at hH ⊢;omega
   have b:2^138-48*H<2^138:=by norm_num at hH ⊢;omega
   rw [Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b]
   norm_num at hH ⊢
   omega

theorem frame(base:BasisState)(hz:∀q∈pad,base q=false)(hb:∀q∈bank,base q=false)(hi:base L.core.cin=false):
 Triple (SquareFrame acc base 0) head
  (SquareFrame acc base ((2^138-48*regValue src base)%2^138)):=by
 intro s m hin
 let H:=regValue src base
 have hH:H<2^128:=by simpa only [H,lengths.2.2.2] using regValue_lt src base
 have a:=small_frame base hz hb hi s (m.take (measurementCount small)) hin
 have bit:=sign H hH _ a.2.1
 have lists:acc=acc.take 135++(acc.drop 135).take 3++acc.drop 138:=by decide +kernel
 have af:SquareFrame (acc.take 135++(acc.drop 135).take 3++acc.drop 138) base (value H)
  (run small (m.take (measurementCount small)) s).basis:=by rw [←lists];exact a.2
 have f:=SignExtendThree.extend_frame (acc.take 135) ((acc.drop 135).take 3) (acc.drop 138)
  (acc.getD 134 0) base (value H) (decide (H≠0)) (by rw [←lists];decide +kernel) (by decide) (by decide)
  (run small (m.take (measurementCount small)) s) (m.drop (measurementCount small))
  (by change value H<2^135;exact Nat.mod_lt _ (by positivity)) af bit
 have e:value H+(if decide (H≠0) then 7*2^(acc.take 135).length else 0)=
  (2^138-48*H)%2^138:=by change value H+(if decide (H≠0) then 7*2^135 else 0)=_;exact value_extend H hH
 rw [←lists,e] at f
 rw [head,run_append]
 exact ⟨f.1.trans a.1,f.2⟩

end ECDSAAdd.Entrant.SignAHead

end

-- Verified component SignCHead
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SignCHead
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle ManyACarryDevelop InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

def value(H:Nat):Nat:=(2^137-48*H)%2^137

theorem sub_value(H:Nat)(hH:H<2^130):
 ReorderedAcc.valueMod (16*H) H 137 6 true=value H:=by
 simp only [ReorderedAcc.valueMod,if_true,value]
 norm_num at hH ⊢
 omega

def small:Program:=Acc.seedOp ga pad 163 (Acc.earlyTerm src false 4)++
 Acc.op (ga.take 137) pad bank L.core.cin 137 true (Acc.earlyTerm src true 6)

def extension:Program:=signComplement (ga.getD 136 0) ((ga.drop 137).take 3)
def head:Program:=small++extension

theorem small_frame(base:BasisState)(hz:∀q∈pad,base q=false)(hb:∀q∈bank,base q=false)(hi:base L.core.cin=false):
 Triple (SquareFrame ga base 0) small (SquareFrame ga base (value (regValue src base))):=by
 let H:=regValue src base
 have hH:H<2^130:=by simpa only [H,lengths.2.2.2] using regValue_lt src base
 have seed:=Acc.seed_triple ga pad bank L.core.cin 163 (Acc.earlyTerm src false 4) lengths.1
  (fits _ (C163NarrowAcc.terms_mem src).1) base hz 0 (16*H) (Or.inl (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
 have sub:=ReorderedAcc.op_mod_prefix_triple ga pad bank L.core.cin 163 137 (Acc.earlyTerm src true 6)
  lengths.1 (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1)
  (by decide) (by decide) base hz hb hi true (16*H) (by norm_num at hH ⊢;omega)
 change Triple _ _ (SquareFrame ga base (ReorderedAcc.valueMod (16*H) H 137 6 true)) at sub
 rw [sub_value H hH] at sub
 exact seed.seq sub

theorem sign(H:Nat)(hH:H<2^130)(s:BasisState)(hv:regValue ga s=value H):
 s (ga.getD 136 0)=decide (H≠0):=by
 apply bool_nat_injective
 rw [regValue_bit ga 136 0 s (by decide),hv]
 by_cases h:H=0
 · subst H
   norm_num [value]
 · have low:2^136≤value H:=by
    have :48*H<2^136:=by norm_num at hH ⊢;omega
    unfold value
    have lt:2^137-48*H<2^137:=by norm_num at hH ⊢;omega
    rw [Nat.mod_eq_of_lt lt]
    norm_num at hH ⊢
    omega
   have high:value H<2^137:=Nat.mod_lt _ (by positivity)
   have d:value H/2^136=1:=Nat.div_eq_of_lt_le (k:=1) (by simpa using low) (by norm_num at high ⊢;omega)
   simp only [d,h,ne_eq,not_false_eq_true,decide_true,Bool.toNat_true]

theorem value_extend(H:Nat)(hH:H<2^130):
 value H+(if decide (H≠0) then 7*2^137 else 0)=(2^140-48*H)%2^140:=by
 by_cases h:H=0
 · subst H
   norm_num [value]
 · simp only [h,ne_eq,not_false_eq_true,decide_true,if_true,value]
   have a:2^137-48*H<2^137:=by norm_num at hH ⊢;omega
   have b:2^140-48*H<2^140:=by norm_num at hH ⊢;omega
   rw [Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b]
   norm_num at hH ⊢
   omega

theorem frame(base:BasisState)(hz:∀q∈pad,base q=false)(hb:∀q∈bank,base q=false)(hi:base L.core.cin=false):
 Triple (SquareFrame ga base 0) head
  (SquareFrame ga base ((2^140-48*regValue src base)%2^140)):=by
 intro s m hin
 let H:=regValue src base
 have hH:H<2^130:=by simpa only [H,lengths.2.2.2] using regValue_lt src base
 have a:=small_frame base hz hb hi s (m.take (measurementCount small)) hin
 have bit:=sign H hH _ a.2.1
 have lists:ga=ga.take 137++(ga.drop 137).take 3++ga.drop 140:=by decide +kernel
 have af:SquareFrame (ga.take 137++(ga.drop 137).take 3++ga.drop 140) base (value H)
  (run small (m.take (measurementCount small)) s).basis:=by rw [←lists];exact a.2
 have f:=SignExtendThree.extend_frame (ga.take 137) ((ga.drop 137).take 3) (ga.drop 140)
  (ga.getD 136 0) base (value H) (decide (H≠0)) (by rw [←lists];decide +kernel) (by decide) (by decide)
  (run small (m.take (measurementCount small)) s) (m.drop (measurementCount small))
  (by change value H<2^137;exact Nat.mod_lt _ (by positivity)) af bit
 have e:value H+(if decide (H≠0) then 7*2^(ga.take 137).length else 0)=
  (2^140-48*H)%2^140:=by change value H+(if decide (H≠0) then 7*2^137 else 0)=_;exact value_extend H hH
 rw [←lists,e] at f
 rw [head,run_append]
 exact ⟨f.1.trans a.1,f.2⟩

end ECDSAAdd.Entrant.SignCHead

end

-- Verified component SignRetape
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SignRetape
open InverseCarryDevelop ZeroReadDevelop
set_option autoImplicit false

attribute [local irreducible] ECDSAAdd.run

def tape(P Q:Program)(m:List Bool):List Bool:=List.replicate (measurementCount Q) false++m.drop (measurementCount P)

theorem replace(P Q R:Program)(s:State)(m:List Bool)
 (h:∀a b:List Bool,run P a s=run Q b s):
 run (P++R) m s=run (Q++R) (tape P Q m) s:=by
 simp only [run_cat]
 rw [h m (tape P Q m)]
 simp [tape]

end ECDSAAdd.Entrant.SignRetape

end

-- Verified component SignKnownA
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SignKnownA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires


def suffix:Program:=ReorderedGenericCache.cachedAdd 103 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin++
 A161Carry.buildPost acc pad bank L.core.cin src++KnownAMidStaged.body++
 ReorderedAUnbuild.unbuild 103 acc pad bank L.core.cin src hosts

def loop:Program:=SignAHead.head++suffix


































def fold:Program:=loop

def rawBody:Program:=measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold)
















def body:Program:=rawBody++ReorderedRecordPadding.program 7 L.core.cin















end ECDSAAdd.Entrant.SignKnownA

end

-- Verified component SignKnownC
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SignKnownC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires


def suffix:Program:=ReorderedGenericCache.cachedAdd 99 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin++
 C163Carry.buildPost ga pad bank L.core.cin src++KnownCMidStaged.body++
 ReorderedCUnbuild.unbuild 99 ga pad bank L.core.cin src hosts

def loop:Program:=SignCHead.head++suffix










































def rawBody:Program:=C163Low4Body.bodyProgram L loop



















def body:Program:=rawBody++ReorderedRecordPadding.program 7 L.core.cin















end ECDSAAdd.Entrant.SignKnownC

end

-- Verified component SignAHeadResources
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SignAHeadResources
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires

theorem extension_counts:toffoliCount SignAHead.extension=0 ∧ measurementCount SignAHead.extension=0 ∧
 Challenge.gateSlots SignAHead.extension=3:=by decide +kernel

theorem head_counts:toffoliCount SignAHead.head=128 ∧ measurementCount SignAHead.head=128:=by
 have seed:=Acc.seed_counts acc pad bank L.core.cin 161 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (A161NarrowAcc.terms_mem src).1).toFitsLen
 have fit:=Acc.fits_prefix acc pad bank L.core.cin 161 135 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide)
 have sub:=Acc.op_counts (acc.take 135) pad bank L.core.cin 135 true (Acc.earlyTerm src true 6)
  (by decide) fit.toFitsLen
 change toffoliCount (Acc.op (acc.take 135) pad bank L.core.cin 135 true (Acc.earlyTerm src true 6))=128 ∧
  measurementCount (Acc.op (acc.take 135) pad bank L.core.cin 135 true (Acc.earlyTerm src true 6))=128 at sub
 have ext:=extension_counts
 simp only [SignAHead.head,SignAHead.small,toffoliCount_append,measurementCount_append]
 omega

theorem balance:toffoliCount SignAHead.head+3=toffoliCount (ReorderedAHead.head acc pad bank L.core.cin src) ∧
 measurementCount SignAHead.head+3=measurementCount (ReorderedAHead.head acc pad bank L.core.cin src):=by
 have seed:=Acc.seed_counts acc pad bank L.core.cin 161 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (A161NarrowAcc.terms_mem src).1).toFitsLen
 have fit:=Acc.fits_prefix acc pad bank L.core.cin 161 138 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide)
 have sub:=Acc.op_counts (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6)
  (by decide) fit.toFitsLen
 change toffoliCount (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6))=131 ∧
  measurementCount (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6))=131 at sub
 have new:=head_counts
 simp only [ReorderedAHead.head,toffoliCount_append,measurementCount_append]
 omega

theorem physical:GatePhysical SignAHead.head:=by
 have fit:=ReorderedAcc.fits_prefix acc pad bank L.core.cin 161 135 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have sub:=ReorderedPhysical.op (acc.take 135) pad bank L.core.cin 135 true (Acc.earlyTerm src true 6) fit
 have seed:GatePhysical (Acc.seedOp acc pad 161 (Acc.earlyTerm src false 4)):=by
  have nd:=Acc.fits_nodup acc pad bank L.core.cin 161 (Acc.earlyTerm src false 4)
   (fits _ (A161NarrowAcc.terms_mem src).1)
  exact copyRegister_physical none _ _
   ((List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)) (by simp)
 have ext:GatePhysical SignAHead.extension:=by
  intro i hi
  change i∈[.CX (acc.getD 134 0) (acc.getD 135 0),.CX (acc.getD 134 0) (acc.getD 136 0),.CX (acc.getD 134 0) (acc.getD 137 0)] at hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl
  all_goals
   change _ ≠ _
   decide +kernel
 simp only [SignAHead.head,SignAHead.small,gatePhysical_append]
 exact ⟨⟨seed,sub⟩,ext⟩
theorem slots:Challenge.gateSlots SignAHead.head+39=Challenge.gateSlots (ReorderedAHead.head acc pad bank L.core.cin src):=by decide +kernel



end ECDSAAdd.Entrant.SignAHeadResources

end

-- Verified component SignCHeadResources
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SignCHeadResources
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires

theorem extension_counts:toffoliCount SignCHead.extension=0 ∧ measurementCount SignCHead.extension=0 ∧
 Challenge.gateSlots SignCHead.extension=3:=by decide +kernel

theorem head_counts:toffoliCount SignCHead.head=130 ∧ measurementCount SignCHead.head=130:=by
 have seed:=Acc.seed_counts ga pad bank L.core.cin 163 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (C163NarrowAcc.terms_mem src).1).toFitsLen
 have fit:=Acc.fits_prefix ga pad bank L.core.cin 163 137 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide)
 have sub:=Acc.op_counts (ga.take 137) pad bank L.core.cin 137 true (Acc.earlyTerm src true 6)
  (by decide) fit.toFitsLen
 change toffoliCount (Acc.op (ga.take 137) pad bank L.core.cin 137 true (Acc.earlyTerm src true 6))=130 ∧
  measurementCount (Acc.op (ga.take 137) pad bank L.core.cin 137 true (Acc.earlyTerm src true 6))=130 at sub
 have ext:=extension_counts
 simp only [SignCHead.head,SignCHead.small,toffoliCount_append,measurementCount_append]
 omega

theorem balance:toffoliCount SignCHead.head+3=toffoliCount (ReorderedCHead.head ga pad bank L.core.cin src) ∧
 measurementCount SignCHead.head+3=measurementCount (ReorderedCHead.head ga pad bank L.core.cin src):=by
 have seed:=Acc.seed_counts ga pad bank L.core.cin 163 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (C163NarrowAcc.terms_mem src).1).toFitsLen
 have fit:=Acc.fits_prefix ga pad bank L.core.cin 163 140 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide)
 have sub:=Acc.op_counts (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6)
  (by decide) fit.toFitsLen
 change toffoliCount (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6))=133 ∧
  measurementCount (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6))=133 at sub
 have new:=head_counts
 simp only [ReorderedCHead.head,toffoliCount_append,measurementCount_append]
 omega

theorem physical:GatePhysical SignCHead.head:=by
 have fit:=ReorderedAcc.fits_prefix ga pad bank L.core.cin 163 137 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have sub:=ReorderedPhysical.op (ga.take 137) pad bank L.core.cin 137 true (Acc.earlyTerm src true 6) fit
 have seed:GatePhysical (Acc.seedOp ga pad 163 (Acc.earlyTerm src false 4)):=by
  have nd:=Acc.fits_nodup ga pad bank L.core.cin 163 (Acc.earlyTerm src false 4)
   (fits _ (C163NarrowAcc.terms_mem src).1)
  exact copyRegister_physical none _ _
   ((List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)) (by simp)
 have ext:GatePhysical SignCHead.extension:=by
  intro i hi
  change i∈[.CX (ga.getD 136 0) (ga.getD 137 0),.CX (ga.getD 136 0) (ga.getD 138 0),.CX (ga.getD 136 0) (ga.getD 139 0)] at hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl
  all_goals
   change _ ≠ _
   decide +kernel
 simp only [SignCHead.head,SignCHead.small,gatePhysical_append]
 exact ⟨⟨seed,sub⟩,ext⟩
theorem slots:Challenge.gateSlots SignCHead.head+39=Challenge.gateSlots (ReorderedCHead.head ga pad bank L.core.cin src):=by decide +kernel



end ECDSAAdd.Entrant.SignCHeadResources

end

-- Verified component SignAHeadSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SignAHeadSupport
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires List.toFinset

theorem list_subset(A B:List Wire)(h:∀u∈A,u∈B):A.toFinset⊆B.toFinset:=by
 intro u hu
 exact List.mem_toFinset.mpr (h u (List.mem_toFinset.mp hu))

theorem support:wires SignAHead.head⊆wires (ReorderedAHead.head acc pad bank L.core.cin src):=by
 have fs:=ReorderedAcc.fits_prefix acc pad bank L.core.cin 161 135 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have fl:=ReorderedAcc.fits_prefix acc pad bank L.core.cin 161 138 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have ws:=ReorderedAcc.op_wires (acc.take 135) pad bank L.core.cin 135 true (Acc.earlyTerm src true 6) (by decide) fs
 have wl:=ReorderedAcc.op_wires (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6) (by decide) fl
 have sub:wires (Acc.op (acc.take 135) pad bank L.core.cin 135 true (Acc.earlyTerm src true 6))⊆
  wires (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6)):=by
  rw [ws,wl]
  exact list_subset _ _ (by decide +kernel)
 have ext:=signComplement_wires_subset (acc.getD 134 0) ((acc.drop 135).take 3)
 have extSub:wires SignAHead.extension⊆wires (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6)):=by
  rw [wl]
  exact ext.trans (list_subset _ _ (by decide +kernel))
 simp only [SignAHead.head,SignAHead.small,ReorderedAHead.head,wires_append]
 exact Finset.union_subset (Finset.union_subset Finset.subset_union_left (sub.trans Finset.subset_union_right))
  (extSub.trans Finset.subset_union_right)

end ECDSAAdd.Entrant.SignAHeadSupport

end

-- Verified component SignCHeadSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SignCHeadSupport
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires List.toFinset

theorem list_subset(A B:List Wire)(h:∀u∈A,u∈B):A.toFinset⊆B.toFinset:=by
 intro u hu
 exact List.mem_toFinset.mpr (h u (List.mem_toFinset.mp hu))

theorem support:wires SignCHead.head⊆wires (ReorderedCHead.head ga pad bank L.core.cin src):=by
 have fs:=ReorderedAcc.fits_prefix ga pad bank L.core.cin 163 137 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have fl:=ReorderedAcc.fits_prefix ga pad bank L.core.cin 163 140 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have ws:=ReorderedAcc.op_wires (ga.take 137) pad bank L.core.cin 137 true (Acc.earlyTerm src true 6) (by decide) fs
 have wl:=ReorderedAcc.op_wires (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6) (by decide) fl
 have sub:wires (Acc.op (ga.take 137) pad bank L.core.cin 137 true (Acc.earlyTerm src true 6))⊆
  wires (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6)):=by
  rw [ws,wl]
  exact list_subset _ _ (by decide +kernel)
 have ext:=signComplement_wires_subset (ga.getD 136 0) ((ga.drop 137).take 3)
 have extSub:wires SignCHead.extension⊆wires (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6)):=by
  rw [wl]
  exact ext.trans (list_subset _ _ (by decide +kernel))
 simp only [SignCHead.head,SignCHead.small,ReorderedCHead.head,wires_append]
 exact Finset.union_subset (Finset.union_subset Finset.subset_union_left (sub.trans Finset.subset_union_right))
  (extSub.trans Finset.subset_union_right)

end ECDSAAdd.Entrant.SignCHeadSupport

end


-- Verified ghost-cache component
section
namespace ECDSAAdd.Entrant.ControlledBorrowResearch
open ECDSAAdd
def setState (s : State) (q : Wire) (v : Bool) : State := ⟨s.phase,writeBit s.basis q v⟩








theorem run_set_outside (P : Program) (m : List Bool) (s : State) (q : Wire) (v : Bool)
 (hq:q∉wires P) : run P m (setState s q v)=setState (run P m s) q v := by
 have agreement := run_measured_locality P (wires P) (fun _ h=>h) (setState s q v) s m rfl
   (fun w hw=>by
     have ne:w≠q := fun e=>hq (e ▸ hw)
     simp [setState,writeBit,ne])
 apply State.extensionality
 · exact agreement.1
 · funext w
   by_cases he:w=q
   · subst w
     rw [run_preserves_outside P m (setState s q v) q hq]
     simp [setState,writeBit]
   by_cases hw:w∈wires P
   · simpa [setState,writeBit,he] using agreement.2 w hw
   · rw [run_preserves_outside P m (setState s q v) w hw]
     simp [setState,writeBit,he,run_preserves_outside P m s w hw]


theorem run_cat (P Q : Program) (m : List Bool) (s : State) :
 run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
 rw [run_append,run_take]

end ECDSAAdd.Entrant.ControlledBorrowResearch

end


-- Verified ghost-cache component
section
-- The following pull/swap/zero/retired lemmas are retained from FreshSwapDevelop
-- in the adopted d2fd4701 entrant. Only redirect_dirty_run below is new research.
namespace ECDSAAdd.Entrant.RedirectBorrowResearch
open ControlledBorrowResearch










































end ECDSAAdd.Entrant.RedirectBorrowResearch

end


-- Verified ghost-cache component
section
namespace ECDSAAdd.Entrant.ClearCopyBorrow
open ControlledBorrowResearch RedirectBorrowResearch
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local irreducible] ECDSAAdd.run






































def program(q a b:Wire)(P:Program):Program:=
 [.CX b a]++renameProgram (Equiv.swap q a) P++[.CX b a]

theorem counts(q a b:Wire)(P:Program):
 toffoliCount (program q a b P)=toffoliCount P ∧
 measurementCount (program q a b P)=measurementCount P:=by
 have h:=renameProgram_counts (Equiv.swap q a) P
 simp only [program,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,Nat.zero_add,Nat.add_zero,h.1,h.2]
 constructor <;> trivial







end ECDSAAdd.Entrant.ClearCopyBorrow

end


-- Verified ghost-cache component
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ClearXorBorrow
open ControlledBorrowResearch RedirectBorrowResearch
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run

def clearProgram(a b c:Wire):Program:=[.CX b a,.CX c a]






















def program(q a b c:Wire)(P:Program):Program:=
 clearProgram a b c++renameProgram (Equiv.swap q a) P++clearProgram a b c






















theorem counts(q a b c:Wire)(P:Program):
 toffoliCount (program q a b c P)=toffoliCount P ∧
 measurementCount (program q a b c P)=measurementCount P:=by
 have h:=renameProgram_counts (Equiv.swap q a) P
 simp only [program,clearProgram,toffoliCount_append,measurementCount_append,toffoliCount,
  measurementCount,Nat.zero_add,Nat.add_zero,h.1,h.2]
 constructor <;> trivial







end ECDSAAdd.Entrant.ClearXorBorrow

end


-- Verified ghost-cache component
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.RelocateThreeGhosts
open RedirectBorrowResearch
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires




















def first(w:Fin 9→Wire)(P:Program):Program:=ClearCopyBorrow.program (w 0) (w 3) (w 6) P
def second(w:Fin 9→Wire)(P:Program):Program:=ClearCopyBorrow.program (w 1) (w 4) (w 7) (first w P)
def program(w:Fin 9→Wire)(P:Program):Program:=ClearXorBorrow.program (w 2) (w 5) (w 8) (w 6) (second w P)

























theorem counts(w:Fin 9→Wire)(P:Program):
 toffoliCount (program w P)=toffoliCount P ∧ measurementCount (program w P)=measurementCount P:=by
 have c0:=ClearCopyBorrow.counts (w 0) (w 3) (w 6) P
 have c1:=ClearCopyBorrow.counts (w 1) (w 4) (w 7) (first w P)
 have c2:=ClearXorBorrow.counts (w 2) (w 5) (w 8) (w 6) (second w P)
 exact ⟨c2.1.trans (c1.1.trans c0.1),c2.2.trans (c1.2.trans c0.2)⟩























end ECDSAAdd.Entrant.RelocateThreeGhosts

end


-- Verified ghost-cache component
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowWordRecovery
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem word_low(H i:Nat)(hi:i<3):
 (4294968272*H).testBit (i+4)=((5*(H%8))%8).testBit i:=by
 rw [Nat.testBit_add]
 have div:(4294968272*H)/2^4=268435517*H:=by norm_num;omega
 rw [div]
 have low:((268435517*H)%8).testBit i=(268435517*H).testBit i:=by
  simpa [hi] using Nat.testBit_mod_two_pow (268435517*H) 3 i
 have mod:(268435517*H)%8=(5*(H%8))%8:=by norm_num [Nat.mul_mod]
 exact low.symm.trans (congrArg (fun n:Nat=>n.testBit i) mod)

theorem source_low(H i:Nat)(hi:i<3):H.testBit i=(H%8).testBit i:=by
 simpa [hi] using (Nat.testBit_mod_two_pow H 3 i).symm

theorem table(k:Nat)(hk:k<8):
 k.testBit 0=((5*k)%8).testBit 0 ∧ k.testBit 1=((5*k)%8).testBit 1 ∧
 k.testBit 2=(((5*k)%8).testBit 2 ^^ ((5*k)%8).testBit 0):=by
 interval_cases k <;> decide

theorem decode(H:Nat):
 H.testBit 0=(4294968272*H).testBit 4 ∧ H.testBit 1=(4294968272*H).testBit 5 ∧
 H.testBit 2=((4294968272*H).testBit 6 ^^ (4294968272*H).testBit 4):=by
 have t:=table (H%8) (Nat.mod_lt H (by decide))
 constructor
 · rw [show 4=0+4 from rfl,word_low H 0 (by decide),source_low H 0 (by decide)]
   exact t.1
 constructor
 · rw [show 5=1+4 from rfl,word_low H 1 (by decide),source_low H 1 (by decide)]
   exact t.2.1
 · rw [show 6=2+4 from rfl,show 4=0+4 from rfl,word_low H 2 (by decide),word_low H 0 (by decide),source_low H 2 (by decide)]
   exact t.2.2

end ECDSAAdd.Entrant.LowWordRecovery

end


-- Verified ghost-cache component
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowWordRecovery
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

theorem readBit(r:List Wire)(s:BasisState)(i:Nat)(hi:i<r.length):
 s (r.getD i 0)=(regValue r s).testBit i:=by
 apply InverseCarryDevelop.bool_nat_injective
 rw [regValue_bit r i 0 s hi]
 simp only [Nat.testBit_eq_decide_div_mod_eq]
 rcases Nat.mod_two_eq_zero_or_one (regValue r s/2^i) with h|h <;> simp [h]

theorem copies(A S:List Wire)(s:BasisState)(ha:7≤A.length)(hs:3≤S.length)
 (hv:regValue A s=4294968272*regValue S s):
 s (S.getD 0 0)=s (A.getD 4 0) ∧ s (S.getD 1 0)=s (A.getD 5 0) ∧
 s (S.getD 2 0)=(s (A.getD 6 0) ^^ s (A.getD 4 0)):=by
 have d:=decode (regValue S s)
 have a4:s (A.getD 4 0)=(4294968272*regValue S s).testBit 4:=by rw [readBit A s 4 (by omega),hv]
 have a5:s (A.getD 5 0)=(4294968272*regValue S s).testBit 5:=by rw [readBit A s 5 (by omega),hv]
 have a6:s (A.getD 6 0)=(4294968272*regValue S s).testBit 6:=by rw [readBit A s 6 (by omega),hv]
 refine ⟨?_,?_,?_⟩
 · exact (readBit S s 0 (by omega)).trans (d.1.trans a4.symm)
 · exact (readBit S s 1 (by omega)).trans (d.2.1.trans a5.symm)
 · rw [readBit S s 2 (by omega),a6,a4]
   exact d.2.2

theorem zero_low(H i:Nat)(hi:i<4):(4294968272*H).testBit i=false:=by
 have mod:(4294968272*H)%16=0:=by norm_num [Nat.mul_mod]
 have h:=Nat.testBit_mod_two_pow (4294968272*H) 4 i
 simpa [hi,mod] using h.symm

theorem low_register_zero(A:List Wire)(s:BasisState)(H i:Nat)(hi:i<4)(hl:i<A.length)
 (hv:regValue A s=4294968272*H):s (A.getD i 0)=false:=by
 rw [readBit A s i hl,hv]
 exact zero_low H i hi


end ECDSAAdd.Entrant.LowWordRecovery

end


-- Verified ghost-cache component
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.EraseListProof
open ControlledBorrowResearch
set_option autoImplicit false
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

def erase:List Wire→State→State
 | [],s=>s
 | q::qs,s=>setState (erase qs s) q false

theorem basis(xs:List Wire)(s:State)(q:Wire):
 (erase xs s).basis q=if q∈xs then false else s.basis q:=by
 induction xs with
 | nil=>simp [erase]
 | cons a as ih=>
  by_cases h:q=a
  · subst q
    simp [erase,setState,writeBit]
  · simp [erase,setState,writeBit,h,Ne.symm h,ih]

theorem phase(xs:List Wire)(s:State):(erase xs s).phase=s.phase:=by
 induction xs with
 | nil=>rfl
 | cons a as ih=>exact ih

theorem commute(xs:List Wire)(P:Program)(m:List Bool)(s:State)(off:∀q∈xs,q∉wires P):
 run P m (erase xs s)=erase xs (run P m s):=by
 induction xs with
 | nil=>rfl
 | cons a as ih=>
  simp only [erase]
  rw [run_set_outside P m (erase as s) a false (off a (by simp))]
  rw [ih (fun q hq=>off q (by simp [hq]))]












end ECDSAAdd.Entrant.EraseListProof

end


-- Verified ghost-cache component
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SmallWireProof
set_option autoImplicit false
set_option linter.unusedSimpArgs false










end ECDSAAdd.Entrant.SmallWireProof

end


-- Verified ghost-cache component
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.RelocateResources
open Arithmetic RecordedQuantum
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires Challenge.gateSlots

theorem rename_physical(f:Wire→Wire)(inj:Function.Injective f)(P:Program)(hp:GatePhysical P):
 GatePhysical (renameProgram f P):=by
 intro i hi
 obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi
 have h:=hp j hj
 cases j <;>simp_all [renameInstr,PhysicalInstr,ProperGate,inj.eq_iff]

theorem copy_physical(q a b:Wire)(P:Program)(hab:a≠b)(hp:GatePhysical P):
 GatePhysical (ClearCopyBorrow.program q a b P):=by
 have ren:=rename_physical (Equiv.swap q a) (Equiv.swap q a).injective P hp
 simp only [ClearCopyBorrow.program,gatePhysical_append]
 exact ⟨⟨by intro i hi;simp only [List.mem_singleton] at hi;subst i;exact Ne.symm hab,ren⟩,
  by intro i hi;simp only [List.mem_singleton] at hi;subst i;exact Ne.symm hab⟩

theorem xor_physical(q a b c:Wire)(P:Program)(hab:a≠b)(hac:a≠c)(hp:GatePhysical P):
 GatePhysical (ClearXorBorrow.program q a b c P):=by
 have ren:=rename_physical (Equiv.swap q a) (Equiv.swap q a).injective P hp
 have clear:GatePhysical (ClearXorBorrow.clearProgram a b c):=by
  intro i hi
  simp only [ClearXorBorrow.clearProgram,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl
  · exact Ne.symm hab
  · exact Ne.symm hac
 simp only [ClearXorBorrow.program,gatePhysical_append]
 exact ⟨⟨clear,ren⟩,clear⟩

theorem physical(w:Fin 9→Wire)(inj:Function.Injective w)(P:Program)(hp:GatePhysical P):
 GatePhysical (RelocateThreeGhosts.program w P):=by
 have ne(i j:Fin 9)(h:i≠j):w i≠w j:=fun e=>h (inj e)
 exact xor_physical _ _ _ _ _ (ne 5 8 (by decide)) (ne 5 6 (by decide))
  (copy_physical _ _ _ _ (ne 4 7 (by decide))
   (copy_physical _ _ _ _ (ne 3 6 (by decide)) hp))

theorem slots(w:Fin 9→Wire)(P:Program):
 Challenge.gateSlots (RelocateThreeGhosts.program w P)=Challenge.gateSlots P+8:=by
 simp only [RelocateThreeGhosts.program,RelocateThreeGhosts.first,RelocateThreeGhosts.second,
  ClearCopyBorrow.program,ClearXorBorrow.program,ClearXorBorrow.clearProgram,
  Challenge.gateSlots_append,Baselines.rename_gateSlots]
 simp [Challenge.gateSlots,Challenge.instructionSlots]
 omega

theorem swap_support(q a:Wire)(P:Program)(D:Finset Wire)(hp:wires P⊆D)(hq:q∈D)(ha:a∈D):
 wires (renameProgram (Equiv.swap q a) P)⊆D:=by
 rw [renameProgram_support]
 intro u hu
 obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu
 by_cases h:v=q
 · subst v;simpa using ha
 by_cases h':v=a
 · subst v;simpa using hq
 simpa [Equiv.swap_apply_def,h,h'] using hp hv

theorem copy_support(q a b:Wire)(P:Program)(D:Finset Wire)(hp:wires P⊆D)(hq:q∈D)(ha:a∈D)(hb:b∈D):
 wires (ClearCopyBorrow.program q a b P)⊆D:=by
 have ren:=swap_support q a P D hp hq ha
 simp only [ClearCopyBorrow.program,wires_append]
 have pref:wires [.CX b a]⊆D:=by simp [wires,Instr.wires,Finset.insert_subset_iff,Finset.singleton_subset_iff,hb,ha]
 exact Finset.union_subset (Finset.union_subset pref ren) pref

theorem xor_support(q a b c:Wire)(P:Program)(D:Finset Wire)(hp:wires P⊆D)(hq:q∈D)(ha:a∈D)(hb:b∈D)(hc:c∈D):
 wires (ClearXorBorrow.program q a b c P)⊆D:=by
 have ren:=swap_support q a P D hp hq ha
 simp only [ClearXorBorrow.program,wires_append]
 have pref:wires (ClearXorBorrow.clearProgram a b c)⊆D:=by
  simp [ClearXorBorrow.clearProgram,wires,Instr.wires,Finset.insert_subset_iff,Finset.singleton_subset_iff,hb,ha,hc]
 exact Finset.union_subset (Finset.union_subset pref ren) pref

theorem support(w:Fin 9→Wire)(P:Program)(D:Finset Wire)(hp:wires P⊆D)(hw:∀i,w i∈D):
 wires (RelocateThreeGhosts.program w P)⊆D:=
 xor_support _ _ _ _ _ D
  (copy_support _ _ _ _ D (copy_support _ _ _ _ D hp (hw 0) (hw 3) (hw 6)) (hw 1) (hw 4) (hw 7))
  (hw 2) (hw 5) (hw 8) (hw 6)



end ECDSAAdd.Entrant.RelocateResources

end


-- Verified ghost-cache component
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.GhostMiddleSupport
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked C163Low4Middle.specialChecked




































end ECDSAAdd.Entrant.GhostMiddleSupport

end


-- Verified ghost-cache component
section
namespace ECDSAAdd.Entrant.GhostRelocatedKnown
def ports(i:Fin 9):Wire:=([4757,4758,4759,4243,4244,4245,4505,4506,4507]:List Wire).getD i.val 0
 theorem ports_inj:Function.Injective ports:=by decide +kernel

attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
 RelocateThreeGhosts.program RelocateThreeGhosts.first RelocateThreeGhosts.second
 ClearCopyBorrow.program ClearXorBorrow.program
end ECDSAAdd.Entrant.GhostRelocatedKnown

end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.HighBorrowArithmeticResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem borrow_remainder_bound (N H : Nat) (hN : 0<N) (hH : H<16*N) :
 H-976*H/1024-1<N := by omega

theorem borrow_remainder_shape (N H : Nat) (hN : 0<N) (hH : H<16*N) :
 (H+(16*N-1-976*H/1024))%(16*N)=
  if H=0 then 16*N-1 else H-976*H/1024-1 := by
 by_cases hz : H=0
 · subst H
   simp only [Nat.mul_zero,Nat.zero_div,Nat.sub_zero,Nat.zero_add,if_pos rfl]
   exact Nat.mod_eq_of_lt (by omega)
 · rw [if_neg hz]
   have hc : 976*H/1024<H := by omega
   have he : H+(16*N-1-976*H/1024)=16*N+(H-976*H/1024-1) := by omega
   rw [he,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod]
   apply Nat.mod_eq_of_lt
   have hh:=borrow_remainder_bound N H hN hH
   omega

theorem borrow_remainder_high (N H : Nat) (hN : 0<N) (hH : H<16*N) :
 ((H+(16*N-1-976*H/1024))%(16*N))/N=if H=0 then 15 else 0 := by
 rw [borrow_remainder_shape N H hN hH]
 split_ifs with hz
 · apply Nat.div_eq_of_lt_le <;> omega
 · exact Nat.div_eq_of_lt (borrow_remainder_bound N H hN hH)

-- The four high sum bits being equal makes the next carry affine.









end ECDSAAdd.Entrant.HighBorrowArithmeticResearch

end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.UniformHighAdderResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run

def affineMajority (a b cin an bn c : Wire) : Program :=
 [.CX an c,.CX bn c,.CX a c,.CX b c,.CX cin c]































end ECDSAAdd.Entrant.UniformHighAdderResearch

end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.FiniteUniformAdder4Research
open UniformHighAdderResearch MeasuredCodec5
set_option autoImplicit false

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def program : List Wire → List Wire → List Wire → Wire → Program
 | a::an::xs,b::bn::ys,c::cs,cin =>
   affineMajority a b cin an bn c ++ program (an::xs) (bn::ys) cs c ++
    eraseCarry a b cin c ++ [.CX a b,.CX cin b]
 | [a],[b],_,cin => [.CX a b,.CX cin b]
 | _,_,_,_ => []
def fast : Program := program [0,1,2,3] [4,5,6,7] [9,10,11] 8
def original : Program := addInPlace [0,1,2,3] [4,5,6,7] [9,10,11] 8
def uniform (x : Nat) : Bool :=
 let r:=(x%16+x/16%16+x/256%2)%16
 (r==0)||(r==15)

theorem finite : ∀x:Fin 512,uniform x.val=true →
 safe fast x.val=true ∧ safe original x.val=true ∧ bitRun fast x.val=bitRun original x.val := by
 decide +kernel

theorem modeled (x : Nat) (hx : x<512) (hu : uniform x=true) (m : List Bool) (ph : Bool) :
 run fast m ⟨ph,bitsOf x⟩=run original m ⟨ph,bitsOf x⟩ := by
 have f:=finite ⟨x,hx⟩ hu
 rw [run_sim,run_sim,sim_safe fast x f.1 m ph,sim_safe original x f.2.1 m ph,f.2.2]

theorem counts : toffoliCount fast=0 ∧ toffoliCount original=3 ∧
 measurementCount fast=3 ∧ measurementCount original=3 := by decide +kernel



end ECDSAAdd.Entrant.FiniteUniformAdder4Research

namespace ECDSAAdd.Entrant.FiniteUniformAdder4Research
open ECDSAAdd ECDSAAdd.Arithmetic MeasuredCodec5
set_option autoImplicit false

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem pack9_lt : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
 pack10 b0 b1 b2 b3 b4 b5 b6 b7 b8 false<512 := by decide +kernel

theorem local_word12 (s : State) (hc : s.basis 9=false ∧ s.basis 10=false ∧ s.basis 11=false) :
 ∃x,x<512 ∧ ∀q∈Finset.range 12,s.basis q=bitsOf x q := by
 let x:=pack10 (s.basis 0) (s.basis 1) (s.basis 2) (s.basis 3) (s.basis 4)
  (s.basis 5) (s.basis 6) (s.basis 7) (s.basis 8) false
 have hx : x<512:=pack9_lt _ _ _ _ _ _ _ _ _
 refine ⟨x,hx,?_⟩
 intro q hq
 have hq' : q<12:=Finset.mem_range.mp hq
 by_cases lo : q<10
 · change s.basis q=x.testBit q
   rw [show x=pack10 (s.basis 0) (s.basis 1) (s.basis 2) (s.basis 3) (s.basis 4)
    (s.basis 5) (s.basis 6) (s.basis 7) (s.basis 8) false from rfl,pack10_bits _ _ _ _ _ _ _ _ _ _ q lo]
   interval_cases q <;> simp [raw,hc.1]
 · have hi : q=10 ∨ q=11:=by omega
   rcases hi with rfl|rfl
   · rw [hc.2.1];exact (Nat.testBit_eq_false_of_lt (by omega : x<2^10)).symm
   · rw [hc.2.2];exact (Nat.testBit_eq_false_of_lt (by omega : x<2^11)).symm

theorem input_values : ∀x:Fin 512,
 regValue [0,1,2,3] (bitsOf x.val)=x.val%16 ∧
 regValue [4,5,6,7] (bitsOf x.val)=x.val/16%16 ∧
 ((bitsOf x.val) 8).toNat=x.val/256%2 := by decide +kernel

theorem support : wires fast⊆Finset.range 12 ∧ wires original⊆Finset.range 12 := by decide +kernel

theorem run_eq (s : State) (m : List Bool)
 (hc : s.basis 9=false ∧ s.basis 10=false ∧ s.basis 11=false)
 (hu : (regValue [0,1,2,3] s.basis+regValue [4,5,6,7] s.basis+(s.basis 8).toNat)%16=0 ∨
       (regValue [0,1,2,3] s.basis+regValue [4,5,6,7] s.basis+(s.basis 8).toNat)%16=15) :
 run fast m s=run original m s := by
 obtain ⟨x,hx,hb⟩:=local_word12 s hc
 have vx:=input_values ⟨x,hx⟩
 have v0 : regValue [0,1,2,3] s.basis=x%16 :=
 by
  rw [←vx.1]
  exact regValue_congr _ _ _ (fun q hq=>hb q (by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl <;>decide))
 have v1 : regValue [4,5,6,7] s.basis=x/16%16 := by
  rw [←vx.2.1]
  exact regValue_congr _ _ _ (fun q hq=>hb q (by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl <;>decide))
 have v2 : (s.basis 8).toNat=x/256%2 := by rw [hb 8 (by decide)];exact vx.2.2
 have ux : uniform x=true := by
  rw [v0,v1,v2] at hu
  simpa only [uniform,Bool.or_eq_true,beq_iff_eq] using hu
 have eq:=modeled x hx ux m s.phase
 have a:=pool_run_agrees fast (Finset.range 12) support.1 m s ⟨s.phase,bitsOf x⟩ rfl hb
 have b:=pool_run_agrees original (Finset.range 12) support.2 m s ⟨s.phase,bitsOf x⟩ rfl hb
 apply State.extensionality
 · exact a.1.trans ((congrArg State.phase eq).trans b.1.symm)
 · funext q
   by_cases hq:q∈Finset.range 12
   · exact (a.2 q hq).trans ((congrArg (fun t:State=>t.basis q) eq).trans (b.2 q hq).symm)
   · have ea:=run_preserves_outside fast m s q (fun h=>hq (support.1 h))
     have eb:=run_preserves_outside original m s q (fun h=>hq (support.2 h))
     exact ea.trans eb.symm

end ECDSAAdd.Entrant.FiniteUniformAdder4Research

end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.PlacedUniformAdder4Research
open FiniteUniformAdder4Research
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def label (f : Fin 12→Wire) (q : Wire) : Wire := if h:q<12 then f ⟨q,h⟩ else q

theorem label_inj (f : Fin 12→Wire) (hf : Function.Injective f) :
 ∀a∈Finset.range 12,∀b∈Finset.range 12,label f a=label f b → a=b := by
 intro a ha b hb e
 have ha':=Finset.mem_range.mp ha
 have hb':=Finset.mem_range.mp hb
 have he : f ⟨a,ha'⟩=f ⟨b,hb'⟩:=by simpa only [label,dif_pos ha',dif_pos hb'] using e
 exact congrArg Fin.val (hf he)

def fastAt(f:Fin 12→Wire):Program:=renameProgram (label f) fast
def originalAt(f:Fin 12→Wire):Program:=renameProgram (label f) original

theorem originalAt_shape(f:Fin 12→Wire):originalAt f=
 addInPlace [f 0,f 1,f 2,f 3] [f 4,f 5,f 6,f 7] [f 9,f 10,f 11] (f 8):=by rfl

theorem run_eq(f:Fin 12→Wire)(hf:Function.Injective f)(s:State)(m:List Bool)
 (hc:s.basis (f 9)=false ∧ s.basis (f 10)=false ∧ s.basis (f 11)=false)
 (hu:(regValue [f 0,f 1,f 2,f 3] s.basis+
      regValue [f 4,f 5,f 6,f 7] s.basis+(s.basis (f 8)).toNat)%16=0 ∨
     (regValue [f 0,f 1,f 2,f 3] s.basis+
      regValue [f 4,f 5,f 6,f 7] s.basis+(s.basis (f 8)).toNat)%16=15):
 run (fastAt f) m s=run (originalAt f) m s:=by
 let t:State:=⟨s.phase,fun q=>s.basis (label f q)⟩
 have ht:t.basis 9=false ∧ t.basis 10=false ∧ t.basis 11=false:=hc
 have eq:=FiniteUniformAdder4Research.run_eq t m ht hu
 have a:=run_rename_pool (label f) (Finset.range 12) (label_inj f hf) fast support.1 m t s rfl (fun _ _=>rfl)
 have b:=run_rename_pool (label f) (Finset.range 12) (label_inj f hf) original support.2 m t s rfl (fun _ _=>rfl)
 have sa:wires (fastAt f)⊆(Finset.range 12).image (label f):=by
  rw [fastAt,renameProgram_support]
  exact Finset.image_mono (label f) support.1
 have sb:wires (originalAt f)⊆(Finset.range 12).image (label f):=by
  rw [originalAt,renameProgram_support]
  exact Finset.image_mono (label f) support.2
 apply State.extensionality
 · exact a.1.trans ((congrArg State.phase eq).trans b.1.symm)
 · funext q
   by_cases hq:q∈(Finset.range 12).image (label f)
   · obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hq
     exact (a.2 i hi).trans ((congrArg (fun z:State=>z.basis i) eq).trans (b.2 i hi).symm)
   · have ea:=run_preserves_outside (fastAt f) m s q (fun h=>hq (sa h))
     have eb:=run_preserves_outside (originalAt f) m s q (fun h=>hq (sb h))
     exact ea.trans eb.symm

theorem counts(f:Fin 12→Wire):toffoliCount (fastAt f)=0 ∧ toffoliCount (originalAt f)=3 ∧
 measurementCount (fastAt f)=3 ∧ measurementCount (originalAt f)=3:=by
 simpa only [fastAt,originalAt,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using FiniteUniformAdder4Research.counts


end ECDSAAdd.Entrant.PlacedUniformAdder4Research

end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.UniformAdderSpliceResearch
open PlacedUniformAdder4Research
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
abbrev xs(f:Fin 12→Wire):List Wire:=[f 0,f 1,f 2,f 3]
abbrev ys(f:Fin 12→Wire):List Wire:=[f 4,f 5,f 6,f 7]
abbrev cs(f:Fin 12→Wire):List Wire:=[f 9,f 10,f 11]

theorem ports_nd(f:Fin 12→Wire)(hf:Function.Injective f):
 (f 8::(xs f++ys f++cs f)).Nodup:=by
 have nd:([8,0,1,2,3,4,5,6,7,9,10,11]:List (Fin 12)).Nodup:=by decide +kernel
 simpa only [List.map_cons,List.map_nil] using nd.map hf

theorem original_output(f:Fin 12→Wire)(hf:Function.Injective f)(s:State)(m:List Bool)
 (hc:∀q∈cs f,s.basis q=false):
 regValue (ys f) (run (originalAt f) m s).basis=
  (regValue (xs f) s.basis+regValue (ys f) s.basis+(s.basis (f 8)).toNat)%16:=by
 have h:=addInPlace_correct (xs f) (ys f) (cs f) (f 8) (ports_nd f hf) rfl rfl s m hc
 simpa only [originalAt_shape] using h.2.2

theorem replace(f:Fin 12→Wire)(hf:Function.Injective f)(pre post:Program)(s:State)(m:List Bool)
 (hm:measurementCount pre=0)
 (hc:∀q∈cs f,s.basis q=false)
 (fresh:∀q∈cs f,q∉wires pre)
 (away:∀q∈ys f,q∉wires post)
 (hu:regValue (ys f) (run (pre++originalAt f++post) [] s).basis=0 ∨
     regValue (ys f) (run (pre++originalAt f++post) [] s).basis=15):
 run (pre++fastAt f++post) m s=run (pre++originalAt f++post) m s:=by
 let u:=run pre [] s
 have cu:∀q∈cs f,u.basis q=false:=by
  intro q hq
  exact (run_preserves_outside pre [] s q (fresh q hq)).trans (hc q hq)
 have keep:regValue (ys f) (run (originalAt f) [] u).basis=
  regValue (ys f) (run (pre++originalAt f++post) [] s).basis:=by
  simp only [run_append,List.take_nil,List.drop_nil]
  apply regValue_congr
  intro q hq
  exact (run_preserves_outside post [] (run (originalAt f) [] u) q (away q hq)).symm
 have value:=original_output f hf u [] cu
 have ready:(regValue (xs f) u.basis+regValue (ys f) u.basis+(u.basis (f 8)).toNat)%16=0 ∨
  (regValue (xs f) u.basis+regValue (ys f) u.basis+(u.basis (f 8)).toNat)%16=15:=by
  rw [←value,keep]
  exact hu
 have ct:u.basis (f 9)=false ∧ u.basis (f 10)=false ∧ u.basis (f 11)=false:=
  ⟨cu _ (by simp),cu _ (by simp),cu _ (by simp)⟩
 have all:∀r:List Bool,run (fastAt f) r u=run (originalAt f) r u:=
  fun r=>PlacedUniformAdder4Research.run_eq f hf u r ct ready
 exact CodexKnownOnesTail.Helpers.run_mid_congr pre (fastAt f) (originalAt f) post m s hm
  ((PlacedUniformAdder4Research.counts f).2.2.1.trans (PlacedUniformAdder4Research.counts f).2.2.2.symm) all

end ECDSAAdd.Entrant.UniformAdderSpliceResearch

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.HighConsumedInputsResearch
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem inner_frame(k:Nat)(xs ys cs hs:List Wire)(cin:Wire)
 (hx:k+6≤xs.length)(hy:k+6≤ys.length)(hc:k+4≤cs.length)
 (hxy:xs.length=ys.length)(hcs:cs.length+1=ys.length)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=k)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (s:State)(m:List Bool)(hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H C:Nat)(source:regValue xs s.basis=H)(target:regValue ys s.basis=C)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 k H C):
 run (ReorderedGenericCache.consumedAdd k xs ys cs hs cin) m (run (notRegister ys) [] s)=
 scatterState hs (List.replicate hs.length false)
  (run (mappedAdd (mappedRead xs false) ys cs cin) m (run (notRegister ys) [] s)):=by
 let u:=run (notRegister ys) [] s
 let v:=run (carryPrefix 4 xs ys cs cin) [] u
 have notM:measurementCount (notRegister ys)=0:=(notRegister_counts ys).2
 have offNot:∀h∈hs,h∉wires (notRegister ys):=by
  intro h hh bad
  rw [notRegister_wires] at bad
  exact fresh h hh (by simp only [List.mem_cons,List.mem_append];exact Or.inr (Or.inl (Or.inr (List.mem_toFinset.mp bad))))
 have untouched(h:Wire)(hh:h∈hs):v.basis h=s.basis h:=by
  have bankOff:h∉cs.take 4:=by
   intro bad
   exact fresh h hh (by simp only [List.mem_cons,List.mem_append];exact Or.inr (Or.inr (List.mem_of_mem_take bad)))
  exact (carryPrefix_preserves 4 xs ys cs cin hn u [] h bankOff).trans
   (run_preserves_outside (notRegister ys) [] s h (offNot h hh))
 have ndc:cs.Nodup:=(List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
 have dis:=List.disjoint_take_drop ndc (show 4≤4 by omega)
 have cys:∀q∈cs,q∉ys:=by
  intro q hq bad
  exact List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2
   (List.mem_append_right _ bad) hq
 have zero:∀q∈(cs.drop 4).take k,v.basis q=false:=by
  intro q hq
  have hdrop:=List.mem_of_mem_take hq
  have b:=List.mem_of_mem_drop hdrop
  have outside:q∉cs.take 4:=fun bad=>List.disjoint_left.mp dis bad hdrop
  change (run (carryPrefix 4 xs ys cs cin) [] u).basis q=false
  rw [carryPrefix_preserves 4 xs ys cs cin hn u [] q outside]
  change (run (notRegister ys) [] s).basis q=false
  rw [run_preserves_outside (notRegister ys) [] s q (by simpa only [notRegister_wires,List.mem_toFinset] using cys q b)]
  exact hz q b
 have vals:=ReorderedCacheBits.inverse_values 4 k H C xs ys cs cin s (by omega) (by omega) (by omega) hn hz hi source target
 have split:=prefix_compose 4 k xs ys cs cin (by omega) (by omega) (by omega)
 have valsAfter:((cs.drop 4).take k).map (run (prefixAfter 4 k xs ys cs cin) [] v).basis=
  ReorderedCacheBits.values 4 k H C:=by
  simpa only [subPreN,split,run_append,notM,carryPrefix_measurements,List.take_zero,List.drop_zero,u,v,prefixAfter] using vals
 have savedV:hs.map v.basis=((cs.drop 4).take k).map (run (prefixAfter 4 k xs ys cs cin) [] v).basis:=by
  have unchanged:hs.map v.basis=hs.map s.basis:=List.map_congr_left untouched
  exact unchanged.trans (saved.trans valsAfter.symm)
 have splitAdd:=mappedAdd_split (4+k) xs ys cs cin (by omega) (by omega) (by omega)
 have suffixOff:∀h∈hs,h∉wires (mappedSuffix (4+k) xs ys cs cin):=by
  intro h hh bad
  have all: h∉wires (mappedAdd (mappedRead xs false) ys cs cin):=by
   rw [MixedLiteralAdderDevelop.read_add_eq]
   intro hit
   rw [addInPlace_wires xs ys cs cin hxy hcs] at hit
   exact fresh h hh (List.mem_toFinset.mp hit)
  apply all
  rw [splitAdd,wires_append]
  exact Finset.mem_union_right _ bad
 exact ReorderedGenericCache.consumedAdd_frame k xs ys cs hs cin hx hy hc hn nd len
  (fun h hh bad=>fresh h hh (by simp only [List.mem_cons,List.mem_append];exact Or.inr (Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take bad)))))
  suffixOff u m zero savedV

theorem inner_value(k:Nat)(xs ys cs hs:List Wire)(cin:Wire)
 (hx:k+6≤xs.length)(hy:k+6≤ys.length)(hc:k+4≤cs.length)
 (hxy:xs.length=ys.length)(hcs:cs.length+1=ys.length)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=k)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (s:State)(m:List Bool)(hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H C:Nat)(source:regValue xs s.basis=H)(target:regValue ys s.basis=C)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 k H C):
 regValue ys (run (ReorderedGenericCache.consumedAdd k xs ys cs hs cin) m (run (notRegister ys) [] s)).basis=
 (H+(2^ys.length-1-C))%2^ys.length:=by
 let u:=run (notRegister ys) [] s
 have cnt:=List.nodup_iff_count_le_one.mp hn
 have ynd:ys.Nodup:=by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h:=cnt q
  simp only [List.count_cons,List.count_append] at h
  omega
 have away:∀q∈cin::(xs++cs),q∉ys:=by
  intro q hq bad
  have a:=List.count_pos_iff.mpr hq
  have b:=List.count_pos_iff.mpr bad
  have h:=cnt q
  simp only [List.count_cons,List.count_append] at h a
  omega
 have off(q:Wire)(hq:q∈cin::(xs++cs)):q∉wires (notRegister ys):=by
  simpa only [notRegister_wires,List.mem_toFinset] using away q hq
 have zu:∀q∈cs,u.basis q=false:=by
  intro q hq
  exact (run_preserves_outside (notRegister ys) [] s q (off q (by simp [hq]))).trans (hz q hq)
 have iu:u.basis cin=false:=
  (run_preserves_outside (notRegister ys) [] s cin (off cin (by simp))).trans hi
 have xu:regValue xs u.basis=H:=by
  have e:regValue xs u.basis=regValue xs s.basis:=regValue_congr xs _ _
   (fun q hq=>run_preserves_outside (notRegister ys) [] s q (off q (by simp [hq])))
  exact e.trans source
 have yu:regValue ys u.basis=2^ys.length-1-C:=
  (notRegister_spec ys ynd C) s [] target |>.2
 have fr:=inner_frame k xs ys cs hs cin hx hy hc hxy hcs hn nd len fresh s m hz hi H C source target saved
 rw [MixedLiteralAdderDevelop.read_add_eq] at fr
 have out:=addInPlace_correct xs ys cs cin hn hxy hcs u m zu
 have value:regValue ys (run (ReorderedGenericCache.consumedAdd k xs ys cs hs cin) m u).basis=
  regValue ys (run (addInPlace xs ys cs cin) m u).basis:=by
  rw [fr]
  exact regValue_congr ys _ _ (fun q hq=>scatter_outside hs (List.replicate hs.length false) _ q (by
   intro bad
   exact fresh q bad (by simp only [List.mem_cons,List.mem_append];tauto)))
 calc
  _=regValue ys (run (addInPlace xs ys cs cin) m u).basis:=value
  _=(H+(2^ys.length-1-C))%2^ys.length:=by
   rw [out.2.2,xu,yu,iu,Bool.toNat_false,Nat.add_zero]



end ECDSAAdd.Entrant.HighConsumedInputsResearch

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.HighConsumedStreamResearch
theorem untouched(P:Program)(q:Wire)(h:C163Touch.touched P q=false):q∉wires P:=by
 intro bad
 have e:=(C163Touch.touched_spec P q).mpr bad
 rw [h] at e
 contradiction
end ECDSAAdd.Entrant.HighConsumedStreamResearch

namespace ECDSAAdd.Entrant.HighConsumedAResearch
abbrev xs:List Wire:=ReorderedAFixed.src
abbrev ys:List Wire:=(ReorderedAFixed.acc.take 138).drop 10
abbrev cs:List Wire:=ReorderedAFixed.bank.take 127
abbrev hs:List Wire:=(ReorderedAFixed.hosts++[4757,4758,4759])
abbrev cin:Wire:=ReorderedAFixed.L.core.cin
def ports:Fin 12→Wire:=![4367,4368,4369,4370,4635,4636,4637,4638,4496,4497,4498,4499]
def old:Program:=ReorderedGenericCache.consumedAdd 106 xs ys cs hs cin
def pre:Program:=old.take 320
def post:Program:=old.drop 349
def fast:Program:=pre++PlacedUniformAdder4Research.fastAt ports++post

theorem ports_inj:Function.Injective ports:=by decide +kernel

theorem window:(old.drop 320).take 29=PlacedUniformAdder4Research.originalAt ports:=by decide +kernel

theorem shape:old=pre++PlacedUniformAdder4Research.originalAt ports++post:=by
 rw [pre,post,←window,←List.take_add]
 exact (List.take_append_drop 349 old).symm













theorem toffoli:toffoliCount fast+3=toffoliCount old:=by
 have h:=congrArg toffoliCount shape
 have q:=PlacedUniformAdder4Research.counts ports
 simp only [toffoliCount_append] at h
 have g:toffoliCount fast=toffoliCount pre+toffoliCount (PlacedUniformAdder4Research.fastAt ports)+toffoliCount post:=by
  simp only [fast,toffoliCount_append]
 omega

theorem measurements:measurementCount fast=measurementCount old:=by
 have h:=congrArg measurementCount shape
 have q:=PlacedUniformAdder4Research.counts ports
 simp only [measurementCount_append] at h
 have g:measurementCount fast=measurementCount pre+measurementCount (PlacedUniformAdder4Research.fastAt ports)+measurementCount post:=by
  simp only [fast,measurementCount_append]
 omega


end ECDSAAdd.Entrant.HighConsumedAResearch

namespace ECDSAAdd.Entrant.HighConsumedCResearch
abbrev xs:List Wire:=C163Low4Middle.src
abbrev ys:List Wire:=(C163Low4Middle.ga.take 140).drop 10
abbrev cs:List Wire:=C163Low4Middle.bank.take 129
abbrev hs:List Wire:=(ReorderedCFixed.hosts++[4757,4758,4759])
abbrev cin:Wire:=C163Low4Middle.L.core.cin
def ports:Fin 12→Wire:=![4369,4370,4371,4372,4637,4638,4639,4640,4498,4499,4500,4764]
def old:Program:=ReorderedGenericCache.consumedAdd 102 xs ys cs hs cin
def pre:Program:=old.take 348
def post:Program:=old.drop 377
def fast:Program:=pre++PlacedUniformAdder4Research.fastAt ports++post

theorem ports_inj:Function.Injective ports:=by decide +kernel

theorem window:(old.drop 348).take 29=PlacedUniformAdder4Research.originalAt ports:=by decide +kernel

theorem shape:old=pre++PlacedUniformAdder4Research.originalAt ports++post:=by
 rw [pre,post,←window,←List.take_add]
 exact (List.take_append_drop 377 old).symm













theorem toffoli:toffoliCount fast+3=toffoliCount old:=by
 have h:=congrArg toffoliCount shape
 have q:=PlacedUniformAdder4Research.counts ports
 simp only [toffoliCount_append] at h
 have g:toffoliCount fast=toffoliCount pre+toffoliCount (PlacedUniformAdder4Research.fastAt ports)+toffoliCount post:=by
  simp only [fast,toffoliCount_append]
 omega

theorem measurements:measurementCount fast=measurementCount old:=by
 have h:=congrArg measurementCount shape
 have q:=PlacedUniformAdder4Research.counts ports
 simp only [measurementCount_append] at h
 have g:measurementCount fast=measurementCount pre+measurementCount (PlacedUniformAdder4Research.fastAt ports)+measurementCount post:=by
  simp only [fast,measurementCount_append]
 omega


end ECDSAAdd.Entrant.HighConsumedCResearch

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.HighConsumedAResearch
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
































































def sub:Program:=notRegister ys++fast++notRegister ys

theorem sub_measurements:measurementCount sub=measurementCount (ReorderedConsumedSub.consumed 106 xs ys cs hs cin):=by
 simp only [sub,ReorderedConsumedSub.consumed,measurementCount_append,measurements,old]















end ECDSAAdd.Entrant.HighConsumedAResearch

namespace ECDSAAdd.Entrant.HighConsumedCResearch
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
































































def sub:Program:=notRegister ys++fast++notRegister ys

theorem sub_measurements:measurementCount sub=measurementCount (ReorderedConsumedSub.consumed 102 xs ys cs hs cin):=by
 simp only [sub,ReorderedConsumedSub.consumed,measurementCount_append,measurements,old]















end ECDSAAdd.Entrant.HighConsumedCResearch

end

-- Verified relocation of the A cache prefix through physicality.
section

end

-- C foundations retain their original declaration order.
section
-- Verified component RelocatedKnownC
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.GhostRelocatedKnown
open Arithmetic InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked
 ECDSAAdd.toffoliCount ECDSAAdd.measurementCount RelocateThreeGhosts.program RelocateThreeGhosts.first RelocateThreeGhosts.second ClearCopyBorrow.program ClearXorBorrow.program
namespace C



abbrev original:Program:=KnownCMidStaged.body
def program:Program:=RelocateThreeGhosts.program ports original


















































end C
end ECDSAAdd.Entrant.GhostRelocatedKnown

namespace ECDSAAdd.Entrant.GhostRelocatedKnown
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount RelocateThreeGhosts.program
namespace C
theorem counts:toffoliCount program=toffoliCount original ∧ measurementCount program=measurementCount original:=RelocateThreeGhosts.counts ports original






end C
end ECDSAAdd.Entrant.GhostRelocatedKnown

end

-- Verified component Ghost3CacheCSetup
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
def spares:List Wire:=[4757,4758,4759]

def viewPerm:Wire→Wire:=fun q=>Equiv.swap 4757 100000 (Equiv.swap 4758 100001 (Equiv.swap 4759 100002 q))
def viewAcc:List Wire:=ga.map viewPerm
def hosts : List Wire := ReorderedCFixed.hosts++spares

theorem geometry : hosts.Nodup ∧ hosts.length=102 ∧ viewAcc.length=163 ∧
 (∀h∈hosts,h∉L.core.cin::(src++viewAcc++pad++bank)):=by decide +kernel






















end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCState
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run


































































end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCPlainSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires List.toFinset





















































end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCCachedSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires List.toFinset




















































end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCPrograms
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop FourthASavedCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def build:Program:=ReorderedCBuild.build 102 ga pad bank L.core.cin src hosts
def unbuild:Program:=ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src hosts
abbrev middle:Program:=GhostRelocatedKnown.C.program







































































end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCLoop
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked
 ReorderedCPlain.build ReorderedCPlain.unbuild ReorderedCBuild.build ReorderedCUnbuild.unbuild
 RelocateThreeGhosts.program

def loop:Program:=build++middle++unbuild

















































































end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCMiddleFrames
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked

theorem plain_ready(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis L.core.cin=false)(ha:regValue ga s.basis=0):
 WReady ga pad bank L.core.cin src (regValue src s.basis) (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s):=by
 have f:=ReorderedCPlain.build_triple ga pad bank L.core.cin src lengths.1 lengths.2.2.2 fits s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have away:∀q∈src++pad++bank++[L.core.cin],q∉ga:=by decide +kernel
 refine ⟨f.2.1,?_,?_,?_,?_⟩
 · exact regValue_congr _ _ _ (fun q hq=>f.2.2 q (away q (by simp [hq])))
 · intro q hq
   exact (f.2.2 q (away q (by simp [hq]))).trans (hz q hq)
 · intro q hq
   exact (f.2.2 q (away q (by simp [hq]))).trans (hb q hq)
 · exact (f.2.2 _ (away _ (by simp))).trans hi




























end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCFrame
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
 InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires C163Low4Middle.bankChecked C163Low4Middle.specialChecked


























































































end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3KnownC
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3KnownC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

abbrev hosts:=Ghost3CacheC.hosts
abbrev loop:=Ghost3CacheC.loop













def rawBody:Program:=C163Low4Body.bodyProgram L loop



















def body:Program:=rawBody++ReorderedRecordPadding.program 4 L.core.cin














end ECDSAAdd.Entrant.Ghost3KnownC

end

-- Verified component Ghost3SignC
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3SignC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev hosts:=Ghost3CacheC.hosts


def suffix:Program:=ReorderedGenericCache.cachedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin++
 C163Carry.buildPost ga pad bank L.core.cin src++Ghost3CacheC.middle++
 ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src hosts

def loop:Program:=SignCHead.head++suffix










































def rawBody:Program:=C163Low4Body.bodyProgram L loop



















def body:Program:=rawBody++ReorderedRecordPadding.program 7 L.core.cin















end ECDSAAdd.Entrant.Ghost3SignC

end

-- Verified component Ghost3CCounts
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CCounts
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle ControlLoan1589BFFold
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
abbrev hosts:=Ghost3CacheC.hosts

theorem cache_counts:
 toffoliCount (ReorderedGenericCache.cachedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=129 ∧
 measurementCount (ReorderedGenericCache.cachedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=129 ∧
 toffoliCount (ReorderedGenericCache.consumedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=27 ∧
 measurementCount (ReorderedGenericCache.consumedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=129:=by
 have old:=addInPlace_counts src ((ga.take 140).drop 10) (bank.take 129) L.core.cin (by decide) (by decide)
 rw [←MixedLiteralAdderDevelop.read_add_eq] at old
 have bal:=ReorderedGenericCache.count_balance 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin
  (by decide) (by decide) (by decide)
 change toffoliCount (mappedAdd (mappedRead src false) ((ga.take 140).drop 10) (bank.take 129) L.core.cin)=129 ∧
  measurementCount (mappedAdd (mappedRead src false) ((ga.take 140).drop 10) (bank.take 129) L.core.cin)=129 at old
 omega

theorem pieces:
 toffoliCount (ReorderedCBuild.build 102 ga pad bank L.core.cin src hosts)=392 ∧
 measurementCount (ReorderedCBuild.build 102 ga pad bank L.core.cin src hosts)=392 ∧
 toffoliCount (ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src hosts)=134 ∧
 measurementCount (ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src hosts)=392:=by
 have f6:=Acc.fits_prefix ga pad bank L.core.cin 163 140 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide)
 have f32:=Acc.fits_prefix ga pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide)
 have seed:=Acc.seed_counts ga pad bank L.core.cin 163 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (C163NarrowAcc.terms_mem src).1).toFitsLen
 have sub:=Acc.op_counts (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6) (by decide) f6.toFitsLen
 have top:=Acc.op_counts (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32) (by decide) f32.toFitsLen
 have preInv:=CodexNarrowTailResource.accSub_counts 108 (ga.take 163) pad bank L.core.cin 163 (Acc.earlyTerm src false 32)
  (by decide) f32.toFitsLen (by decide)
 have tail:=ReorderedKnownTail.counts src pad ((ga.take 140).drop 6) (bank.take 133) L.core.cin
  (by decide) (by decide) (by decide) (by decide)
 have notC:=notRegister_counts ((ga.take 140).drop 10)
 have cache:=cache_counts
 change toffoliCount (ReorderedCTail.tail ga pad bank L.core.cin src)=0 ∧
  measurementCount (ReorderedCTail.tail ga pad bank L.core.cin src)=133 at tail
 change toffoliCount (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6))=133 ∧
  measurementCount (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6))=133 at sub
 change toffoliCount (Acc.op (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32))=130 ∧
  measurementCount (Acc.op (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32))=130 at top
 change toffoliCount (CodexKnownOnesTail.accSub 108 (ga.take 163) pad bank L.core.cin 163 (Acc.earlyTerm src false 32))=107 ∧
  measurementCount (CodexKnownOnesTail.accSub 108 (ga.take 163) pad bank L.core.cin 163 (Acc.earlyTerm src false 32))=130 at preInv
 simp only [ReorderedCBuild.build,ReorderedCHead.head,C163Carry.buildPost,
  ReorderedCUnbuild.unbuild,ReorderedCUnbuild.after,ReorderedConsumedSub.consumed,C163Carry.unbuildPre,
  toffoliCount_append,measurementCount_append]
 omega


end ECDSAAdd.Entrant.Ghost3CCounts

end

-- Verified component Ghost3CPhysical
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CPhysical
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle
set_option autoImplicit false

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires specialChecked bankChecked
abbrev hosts:=Ghost3CacheC.hosts

theorem body_physical:GatePhysical Ghost3KnownC.body:=by
 have f6:=ReorderedAcc.fits_prefix ga pad bank L.core.cin 163 140 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have subP:=ReorderedPhysical.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6) f6
 have seedP:GatePhysical (Acc.seedOp ga pad 163 (Acc.earlyTerm src false 4)):=by
  have nd:=Acc.fits_nodup ga pad bank L.core.cin 163 (Acc.earlyTerm src false 4)
   (fits _ (C163NarrowAcc.terms_mem src).1)
  exact copyRegister_physical none _ _
   ((List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)) (by simp)
 have topP:=Acc.op_prefix_physical ga pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide) false
 have nd:(L.core.cin::(src++(ga.take 140).drop 10++bank.take 129)).Nodup:=by decide +kernel
 have cacheP:=ReorderedPhysical.cached 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin
  (by decide) (by decide) (by decide) nd (by
   intro h hh bad
   exact (by decide +kernel : ∀h∈hosts,h∉bank) h hh (List.mem_of_mem_take bad))
 have buildP:GatePhysical (ReorderedCBuild.build 102 ga pad bank L.core.cin src hosts):=by
  simp only [ReorderedCBuild.build,ReorderedCHead.head,C163Carry.buildPost,gatePhysical_append]
  exact ⟨⟨⟨seedP,subP⟩,cacheP.1⟩,topP⟩
 have notP:=notRegister_physical ((ga.take 140).drop 10)
 have inverseP:GatePhysical (ReorderedConsumedSub.consumed 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin):=by
  simp only [ReorderedConsumedSub.consumed,gatePhysical_append]
  exact ⟨⟨notP,cacheP.2⟩,notP⟩
 have tailP:GatePhysical (ReorderedCTail.tail ga pad bank L.core.cin src):=by
  apply KnownOutputAdder.program_physical (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
   ((ga.take 140).drop 6) (bank.take 133) L.core.cin
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
 have oldInv:=C163SourceAdd.unbuild_physical ga pad bank L.core.cin src lengths.1 lengths.2.2.2 fits
 simp only [C163SourceAdd.unbuild,gatePhysical_append] at oldInv
 have preInv:GatePhysical (C163Carry.unbuildPre ga pad bank L.core.cin src):=oldInv.1.1.1
 have unbuildP:GatePhysical (ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src hosts):=by
  simp only [ReorderedCUnbuild.unbuild,ReorderedCUnbuild.after,gatePhysical_append]
  exact ⟨⟨preInv,inverseP⟩,⟨tailP,seedP⟩⟩
 have old:=C163Low4Middle.body_physical
 simp only [C163Low4Middle.body,C163Low4Body.bodyProgram,C163Low4Middle.loop,gatePhysical_append] at old
 have midOld:GatePhysical KnownCMidStaged.body:=by
  unfold GatePhysical
  intro i hi
  exact old.2.1.2 i ((KnownSparseFold.Cert.sublist _ _ _ _ _ KnownCMidStaged.cert).subset hi)
 have midP:GatePhysical Ghost3CacheC.middle:=
  RelocateResources.physical GhostRelocatedKnown.ports GhostRelocatedKnown.ports_inj KnownCMidStaged.body midOld
 simp only [Ghost3KnownC.body,Ghost3KnownC.rawBody,C163Low4Body.bodyProgram,Ghost3KnownC.loop,Ghost3CacheC.loop,Ghost3CacheC.build,Ghost3CacheC.unbuild,gatePhysical_append]
 exact ⟨⟨old.1,⟨⟨buildP,midP⟩,unbuildP⟩⟩,ReorderedPhysical.padding 4 L.core.cin⟩



end ECDSAAdd.Entrant.Ghost3CPhysical

end

-- Verified component Ghost3CBalance
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CBalance
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle Challenge
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem counts:toffoliCount Ghost3SignC.body+3=toffoliCount SignKnownC.body ∧
 measurementCount Ghost3SignC.body=measurementCount SignKnownC.body:=by
 have nc:=Ghost3CCounts.cache_counts
 have oc:=ReorderedCCounts.cache_counts
 have np:=Ghost3CCounts.pieces
 have op:=ReorderedCCounts.pieces
 have mid:=GhostRelocatedKnown.C.counts
 change toffoliCount GhostRelocatedKnown.C.program=toffoliCount KnownCMidStaged.body ∧
  measurementCount GhostRelocatedKnown.C.program=measurementCount KnownCMidStaged.body at mid
 simp only [Ghost3CCounts.hosts] at nc np
 simp only [ReorderedCCounts.hosts] at oc op
 simp only [Ghost3SignC.body,Ghost3SignC.rawBody,C163Low4Body.bodyProgram,Ghost3SignC.loop,Ghost3SignC.suffix,Ghost3SignC.hosts,Ghost3CacheC.middle,
  SignKnownC.body,SignKnownC.rawBody,SignKnownC.loop,SignKnownC.suffix,toffoliCount_append,measurementCount_append]
 exact ⟨by omega,by omega⟩

theorem slots:gateSlots Ghost3SignC.body+1=gateSlots SignKnownC.body:=by
 have nc:=ReorderedSlots.cache 102 src ((ga.take 140).drop 10) (bank.take 129) Ghost3CacheC.hosts L.core.cin
  (by decide) (by decide) (by decide) Ghost3CacheC.geometry.2.1
 have oc:=ReorderedSlots.cache 99 src ((ga.take 140).drop 10) (bank.take 129) ReorderedCFixed.hosts L.core.cin
  (by decide) (by decide) (by decide) ReorderedCFixed.host_geometry.2.1
 have mid:=RelocateResources.slots GhostRelocatedKnown.ports KnownCMidStaged.body
 simp only [Ghost3SignC.body,Ghost3SignC.rawBody,C163Low4Body.bodyProgram,Ghost3SignC.loop,Ghost3SignC.suffix,Ghost3SignC.hosts,Ghost3CacheC.middle,
  SignKnownC.body,SignKnownC.rawBody,SignKnownC.loop,SignKnownC.suffix,
  ReorderedCUnbuild.unbuild,ReorderedConsumedSub.consumed,gateSlots_append]
 change gateSlots GhostRelocatedKnown.C.program=gateSlots KnownCMidStaged.body+8 at mid
 omega

end ECDSAAdd.Entrant.Ghost3CBalance

end

-- Verified component SignedBodySupportC
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3BodyResources
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout Challenge
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires Challenge.gateSlots List.toFinset

open ReorderedCFixed C163Low4Middle in
theorem c_support:wires Ghost3SignC.body⊆wires Ghost3KnownC.body:=by
 have loop:wires Ghost3SignC.loop⊆wires Ghost3KnownC.loop:=by
  have eq:Ghost3KnownC.loop=ReorderedCHead.head ga pad bank L.core.cin src++Ghost3SignC.suffix:=by
   simp only [Ghost3KnownC.loop,Ghost3CacheC.loop,Ghost3CacheC.build,Ghost3CacheC.unbuild,ReorderedCBuild.build,Ghost3KnownC.hosts,Ghost3SignC.suffix,Ghost3SignC.hosts,List.append_assoc]
  rw [Ghost3SignC.loop,eq,wires_append,wires_append]
  exact Finset.union_subset_union SignCHeadSupport.support (Finset.Subset.refl _)
 have pad:wires (ReorderedRecordPadding.program 7 L.core.cin)=wires (ReorderedRecordPadding.program 4 L.core.cin):=by
  simp [ReorderedRecordPadding.program,List.replicate_succ,wires,Instr.wires,correctionWires]
 simp only [Ghost3SignC.body,Ghost3SignC.rawBody,C163Low4Body.bodyProgram,Ghost3KnownC.body,Ghost3KnownC.rawBody,wires_append]
 rw [pad]
 repeat' first
  | exact loop
  | exact Finset.Subset.refl _
  | apply Finset.union_subset_union

open ReorderedCFixed C163Low4Middle in
theorem c_physical:GatePhysical Ghost3SignC.body:=by
 have old:=Ghost3CPhysical.body_physical
 have head:=SignCHeadResources.physical
 have pad:=ReorderedPhysical.padding 7 L.core.cin
 simp only [Ghost3SignC.body,Ghost3SignC.rawBody,Ghost3SignC.loop,Ghost3SignC.suffix,Ghost3SignC.hosts,
  Ghost3KnownC.body,Ghost3KnownC.rawBody,C163Low4Body.bodyProgram,Ghost3KnownC.loop,Ghost3CacheC.loop,Ghost3CacheC.build,Ghost3CacheC.unbuild,Ghost3KnownC.hosts,
  ReorderedCBuild.build,gatePhysical_append] at old ⊢
 tauto

end ECDSAAdd.Entrant.Ghost3BodyResources

end

-- Verified component Ghost3CFine
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CFine
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle OwnDiagAll12Square
set_option autoImplicit false

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] RelocateThreeGhosts.program
attribute [local irreducible] ECDSAAdd.wires specialChecked bankChecked List.toFinset
abbrev hosts:=Ghost3CacheC.hosts
def domain:Finset Wire:=(L.core.cin::(src++acc++pad++bank)).toFinset

theorem list_support(A B:List Wire)(h:∀q∈A,q∈B):A.toFinset⊆B.toFinset:=by
 intro q hq
 exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem domain_in:domain⊆C163Middle.ambient.toFinset:=
 list_support (L.core.cin::(src++acc++pad++bank)) C163Middle.ambient (by decide +kernel)

theorem loop_support:wires Ghost3KnownC.loop⊆C163Middle.ambient.toFinset:=by
 have fit:=C163Fold.terms_fits L hw hn
 have len:=C163Fold.lengths L hw
 have seed:=(Acc.seed_support acc pad bank L.core.cin 163 (Acc.earlyTerm src false 4)
  len.1 (fit _ (C163NarrowAcc.terms_mem src).1)).trans domain_in
 have sub:=(Acc.op_prefix_support acc pad bank L.core.cin 163 140 (Acc.earlyTerm src true 6)
  len.1 (by decide) (fit _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide) true).trans domain_in
 have top(neg:Bool):wires (Acc.op (acc.take 163) pad bank L.core.cin 163 neg (Acc.earlyTerm src false 32))⊆C163Middle.ambient.toFinset:=
  (Acc.op_prefix_support acc pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
   len.1 (by decide) (fit _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide) neg).trans domain_in
 have cacheDomain:(L.core.cin::(src++(acc.take 140).drop 10++bank.take 129)).toFinset∪hosts.toFinset⊆
  C163Middle.ambient.toFinset:=Finset.union_subset
   (list_support _ _ (by decide +kernel)) (list_support _ _ (by decide +kernel))
 have cached:=ReorderedSupport.cached 102 src ((acc.take 140).drop 10) (bank.take 129) hosts L.core.cin
  (by decide) (by decide) (by decide) (by decide) (by decide)
 have build:wires (ReorderedCBuild.build 102 acc pad bank L.core.cin src hosts)⊆C163Middle.ambient.toFinset:=by
  simp only [ReorderedCBuild.build,ReorderedCHead.head,C163Carry.buildPost,wires_append]
  exact Finset.union_subset (Finset.union_subset (Finset.union_subset seed sub) (cached.1.trans cacheDomain)) (top false)
 have f32:=Acc.fits_prefix acc pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
  (by decide) (fit _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide)
 have preInv:wires (C163Carry.unbuildPre acc pad bank L.core.cin src)⊆C163Middle.ambient.toFinset:=
  (CodexNarrowTailResource.accSub_support 108 (acc.take 163) pad bank L.core.cin 163
   (Acc.earlyTerm src false 32) (by decide) f32.toFitsLen (by decide)).trans (top true)
 have consumed:=(ReorderedSupport.consumed 102 src ((acc.take 140).drop 10) (bank.take 129) hosts L.core.cin
  (by decide) (by decide) (by decide) (by decide) (by decide)).trans cacheDomain
 have tail:=KnownOutputAdder.program_support (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
  ((acc.take 140).drop 6) (bank.take 133) L.core.cin
 rw [mappedRead_wires,ReorderedKnownTail.desired_wires] at tail
 have tailDomain:((src++pad.take 4)++src.drop 2++(acc.take 140).drop 6++bank.take 133++[L.core.cin]).toFinset⊆
  C163Middle.ambient.toFinset:=list_support _ _ (by decide +kernel)
 have unbuild:wires (ReorderedCUnbuild.unbuild 102 acc pad bank L.core.cin src hosts)⊆C163Middle.ambient.toFinset:=by
  simp only [ReorderedCUnbuild.unbuild,ReorderedCUnbuild.after,wires_append]
  exact Finset.union_subset (Finset.union_subset preInv consumed) (Finset.union_subset (tail.trans tailDomain) seed)
 have midOld:wires KnownCMidStaged.body⊆C163Middle.ambient.toFinset:=
  (Skip4.wires_mono_of_mem _ _ (fun _ hi=>(KnownSparseFold.Cert.sublist _ _ _ _ _ KnownCMidStaged.cert).subset hi)).trans
   (ReorderedBankSupport.subset.trans
    ((special_cert.support [q,r] middle specialChecked.out).1.trans
     (middle_subset.trans C163Middle.middle_support)))
 have mid:wires Ghost3CacheC.middle⊆C163Middle.ambient.toFinset:=
  RelocateResources.support GhostRelocatedKnown.ports KnownCMidStaged.body _ midOld
   (by intro i;apply List.mem_toFinset.mpr;fin_cases i <;>decide +kernel)
 simp only [Ghost3KnownC.loop,Ghost3CacheC.loop,wires_append]
 rw [Ghost3CacheC.build,Ghost3CacheC.unbuild,ReorderedCStructural.build_eq,ReorderedCStructural.unbuild_eq]
 exact Finset.union_subset (Finset.union_subset build mid) unbuild

theorem padding_support:wires (ReorderedRecordPadding.program 4 L.core.cin)⊆C163Middle.ambient.toFinset:=by
 have sub:wires (ReorderedRecordPadding.program 4 L.core.cin)⊆[L.core.cin].toFinset:=by decide +kernel
 exact sub.trans (list_support _ _ (by decide +kernel))

theorem body_fine:wires Ghost3KnownC.body⊆insert d (wires (bodyCKTq L g)):=by
 intro u hu
 simp only [Ghost3KnownC.body,Ghost3KnownC.rawBody,C163Low4Body.bodyProgram,wires_append,Finset.mem_union] at hu
 rcases hu with (hu|hu)|hu
 · apply Finset.mem_insert_of_mem
   simp only [bodyCKTq,wires_append,Finset.mem_union]
   exact Or.inl hu
 · exact C163FineFast.ambient_fine (loop_support hu)
 · exact C163FineFast.ambient_fine (padding_support hu)

theorem body_coarse:wires Ghost3KnownC.body⊆insert d (g::L.wires).toFinset:=
 body_fine.trans (Finset.insert_subset_insert d (bodyCK_supportTq L hw hn g))


end ECDSAAdd.Entrant.Ghost3CFine

end

end


end

-- First original Front segment, current namespace and five original anonymous contexts closed after public old64.
section

-- A foundations relocated from the prior ancestor module.
section
-- Verified component RelocatedKnownA
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.GhostRelocatedKnown
open Arithmetic InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked
 ECDSAAdd.toffoliCount ECDSAAdd.measurementCount RelocateThreeGhosts.program RelocateThreeGhosts.first RelocateThreeGhosts.second ClearCopyBorrow.program ClearXorBorrow.program
namespace A



abbrev original:Program:=KnownAMidStaged.body
def program:Program:=RelocateThreeGhosts.program ports original


















































end A
end ECDSAAdd.Entrant.GhostRelocatedKnown

namespace ECDSAAdd.Entrant.GhostRelocatedKnown
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount RelocateThreeGhosts.program
namespace A
theorem counts:toffoliCount program=toffoliCount original ∧ measurementCount program=measurementCount original:=RelocateThreeGhosts.counts ports original






end A
end ECDSAAdd.Entrant.GhostRelocatedKnown

end

-- Verified component Ghost3CacheASetup
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
def spares:List Wire:=[4757,4758,4759]

def viewPerm:Wire→Wire:=fun q=>Equiv.swap 4757 100000 (Equiv.swap 4758 100001 (Equiv.swap 4759 100002 q))
def viewAcc:List Wire:=acc.map viewPerm
def hosts : List Wire := ReorderedAFixed.hosts++spares

theorem geometry : hosts.Nodup ∧ hosts.length=106 ∧ viewAcc.length=161 ∧
 (∀h∈hosts,h∉L.core.cin::(src++viewAcc++pad++bank)):=by decide +kernel






















end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheAState
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run


































































end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheAPlainSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires List.toFinset

theorem plain_support(A:List Wire)(len:A.length=161)
 (fit:∀f∈earlyHTerms src,Acc.Fits A pad bank L.core.cin 161 f):
 wires (ReorderedAPlain.build A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset ∧
 wires (ReorderedAPlain.unbuild A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset:=by
 have seed:=Acc.seed_support A pad bank L.core.cin 161 (Acc.earlyTerm src false 4) len
  (fit _ (A161NarrowAcc.terms_mem src).1)
 have op6:=Acc.op_prefix_support A pad bank L.core.cin 161 138 (Acc.earlyTerm src true 6)
  len (by decide) (fit _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide) true
 have op10(neg:Bool):wires (Acc.op (A.take 138) pad bank L.core.cin 138 neg (Acc.earlyTerm src false 10))⊆
  (L.core.cin::(src++A++pad++bank)).toFinset:=by
  have ff:=ReorderedAcc.fits_prefix A pad bank L.core.cin 161 138 (Acc.earlyTerm src false 10)
   (by decide) (fit _ (A161NarrowAcc.terms_mem src).2.1) (by decide) (by decide)
  rw [ReorderedAcc.op_wires (A.take 138) pad bank L.core.cin 138 neg (Acc.earlyTerm src false 10) (by simp [len]) ff]
  intro q hq
  have h:=List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,if_true,List.mem_cons,List.mem_append] at h ⊢
  have pa:∀k,q∈pad.take k→q∈pad:=fun _=>List.mem_of_mem_take
  have aa:q∈(A.take 138).drop 10→q∈A:=fun hh=>List.mem_of_mem_take (List.mem_of_mem_drop hh)
  have bb:∀k,q∈bank.take k→q∈bank:=fun _=>List.mem_of_mem_take
  tauto
 have top(neg:Bool):wires (Acc.op (A.take 161) pad bank L.core.cin 161 neg (Acc.earlyTerm src false 32))⊆
  (L.core.cin::(src++A++pad++bank)).toFinset:=
  Acc.op_prefix_support A pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
   len (by decide) (fit _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide) neg
 have f32:=Acc.fits_prefix A pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
  (by decide) (fit _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide)
 have preInv:wires (A161Carry.unbuildPre A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset:=
  (CodexNarrowTailResource.accSub_support 106 (A.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32)
   (by simp [len]) f32.toFitsLen (by decide)).trans (top true)
 have tail:=KnownOutputAdder.program_support (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
  ((A.take 138).drop 6) (bank.take 131) L.core.cin
 rw [mappedRead_wires,ReorderedKnownTail.desired_wires] at tail
 have td:((src++pad.take 4)++src.drop 2++(A.take 138).drop 6++bank.take 131++[L.core.cin]).toFinset⊆
  (L.core.cin::(src++A++pad++bank)).toFinset:=by
  intro q hq
  have h:=List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [List.mem_append,List.mem_singleton] at h
  have pp:q∈pad.take 4→q∈pad:=List.mem_of_mem_take
  have ss:q∈src.drop 2→q∈src:=List.mem_of_mem_drop
  have aa:q∈(A.take 138).drop 6→q∈A:=fun hh=>List.mem_of_mem_take (List.mem_of_mem_drop hh)
  have bb:q∈bank.take 131→q∈bank:=List.mem_of_mem_take
  simp only [List.mem_cons,List.mem_append]
  tauto
 have tailSupport:wires (ReorderedATail.tail A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset:=tail.trans td
 constructor
 · simp only [ReorderedAPlain.build,ReorderedAPre.pre,A161Carry.buildPost,wires_append]
   exact Finset.union_subset (Finset.union_subset (Finset.union_subset seed op6) (op10 false)) (top false)
 · simp only [ReorderedAPlain.unbuild,wires_append]
   exact Finset.union_subset (Finset.union_subset (Finset.union_subset preInv (op10 true)) tailSupport) seed

end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheACachedSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires List.toFinset




















































end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheAPrograms
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop FourthASavedCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def build:Program:=ReorderedABuild.build 106 acc pad bank L.core.cin src hosts
def unbuild:Program:=ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src hosts
abbrev middle:Program:=GhostRelocatedKnown.A.program







































































end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheALoop
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked
 ReorderedAPlain.build ReorderedAPlain.unbuild ReorderedABuild.build ReorderedAUnbuild.unbuild
 RelocateThreeGhosts.program

def loop:Program:=build++middle++unbuild

















































































end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheAMiddleFrames
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked

theorem plain_ready(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis L.core.cin=false)(ha:regValue acc s.basis=0):
 WReady acc pad bank L.core.cin src (regValue src s.basis) (run (ReorderedAPlain.build acc pad bank L.core.cin src) m s):=by
 have f:=ReorderedAPlain.build_triple acc pad bank L.core.cin src lengths.1 lengths.2.2.2 fits s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have away:∀q∈src++pad++bank++[L.core.cin],q∉acc:=by decide +kernel
 refine ⟨f.2.1,?_,?_,?_,?_⟩
 · exact regValue_congr _ _ _ (fun q hq=>f.2.2 q (away q (by simp [hq])))
 · intro q hq
   exact (f.2.2 q (away q (by simp [hq]))).trans (hz q hq)
 · intro q hq
   exact (f.2.2 q (away q (by simp [hq]))).trans (hb q hq)
 · exact (f.2.2 _ (away _ (by simp))).trans hi




























end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheAFrame
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked





































































end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3KnownA
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3KnownA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

abbrev hosts:=Ghost3CacheA.hosts
abbrev loop:=Ghost3CacheA.loop

def fold:Program:=loop

def rawBody:Program:=measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold)
















def body:Program:=rawBody++ReorderedRecordPadding.program 4 L.core.cin














end ECDSAAdd.Entrant.Ghost3KnownA

end

-- Verified component Ghost3SignA
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3SignA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev hosts:=Ghost3CacheA.hosts


def suffix:Program:=ReorderedGenericCache.cachedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin++
 A161Carry.buildPost acc pad bank L.core.cin src++Ghost3CacheA.middle++
 ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src hosts

def loop:Program:=SignAHead.head++suffix


































def fold:Program:=loop

def rawBody:Program:=measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold)
















def body:Program:=rawBody++ReorderedRecordPadding.program 7 L.core.cin















end ECDSAAdd.Entrant.Ghost3SignA

end

-- Verified component Ghost3ACounts
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3ACounts
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedAFixed ControlLoan1589BFFold
set_option autoImplicit false

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount

abbrev hosts:=Ghost3CacheA.hosts

theorem cache_counts:
 toffoliCount (ReorderedGenericCache.cachedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=127 ∧
 measurementCount (ReorderedGenericCache.cachedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=127 ∧
 toffoliCount (ReorderedGenericCache.consumedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=21 ∧
 measurementCount (ReorderedGenericCache.consumedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=127:=by
 have old:=addInPlace_counts src ((acc.take 138).drop 10) (bank.take 127) L.core.cin (by decide) (by decide)
 rw [←MixedLiteralAdderDevelop.read_add_eq] at old
 have bal:=ReorderedGenericCache.count_balance 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin
  (by decide) (by decide) (by decide)
 change toffoliCount (mappedAdd (mappedRead src false) ((acc.take 138).drop 10) (bank.take 127) L.core.cin)=127 ∧
  measurementCount (mappedAdd (mappedRead src false) ((acc.take 138).drop 10) (bank.take 127) L.core.cin)=127 at old
 omega

theorem pieces:
 toffoliCount (ReorderedABuild.build 106 acc pad bank L.core.cin src hosts)=386 ∧
 measurementCount (ReorderedABuild.build 106 acc pad bank L.core.cin src hosts)=386 ∧
 toffoliCount (ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src hosts)=126 ∧
 measurementCount (ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src hosts)=386:=by
 have f6:=Acc.fits_prefix acc pad bank L.core.cin 161 138 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide)
 have f32:=Acc.fits_prefix acc pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide)
 have seed:=Acc.seed_counts acc pad bank L.core.cin 161 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (A161NarrowAcc.terms_mem src).1).toFitsLen
 have sub:=Acc.op_counts (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6) (by decide) f6.toFitsLen
 have top:=Acc.op_counts (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32) (by decide) f32.toFitsLen
 have preInv:=CodexNarrowTailResource.accSub_counts 106 (acc.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32)
  (by decide) f32.toFitsLen (by decide)
 have tail:=ReorderedKnownTail.counts src pad ((acc.take 138).drop 6) (bank.take 131) L.core.cin
  (by decide) (by decide) (by decide) (by decide)
 have notC:=notRegister_counts ((acc.take 138).drop 10)
 have cache:=cache_counts
 change toffoliCount (ReorderedATail.tail acc pad bank L.core.cin src)=0 ∧
  measurementCount (ReorderedATail.tail acc pad bank L.core.cin src)=131 at tail
 change toffoliCount (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6))=131 ∧
  measurementCount (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6))=131 at sub
 change toffoliCount (Acc.op (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32))=128 ∧
  measurementCount (Acc.op (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32))=128 at top
 change toffoliCount (CodexKnownOnesTail.accSub 106 (acc.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32))=105 ∧
  measurementCount (CodexKnownOnesTail.accSub 106 (acc.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32))=128 at preInv
 simp only [ReorderedABuild.build,ReorderedAHead.head,A161Carry.buildPost,
  ReorderedAUnbuild.unbuild,ReorderedAUnbuild.after,ReorderedConsumedSub.consumed,A161Carry.unbuildPre,
  toffoliCount_append,measurementCount_append]
 omega



end ECDSAAdd.Entrant.Ghost3ACounts

end

-- Verified component Ghost3APhysical
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3APhysical
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedAFixed
set_option autoImplicit false

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires A161Low4FixedFold.checked
abbrev hosts:=Ghost3CacheA.hosts

theorem body_physical:GatePhysical Ghost3KnownA.body:=by
 have f6:=ReorderedAcc.fits_prefix acc pad bank L.core.cin 161 138 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have subP:=ReorderedPhysical.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6) f6
 have seedP:GatePhysical (Acc.seedOp acc pad 161 (Acc.earlyTerm src false 4)):=by
  have nd:=Acc.fits_nodup acc pad bank L.core.cin 161 (Acc.earlyTerm src false 4)
   (fits _ (A161NarrowAcc.terms_mem src).1)
  exact copyRegister_physical none _ _
   ((List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)) (by simp)
 have topP:=Acc.op_prefix_physical acc pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide) false
 have nd:(L.core.cin::(src++(acc.take 138).drop 10++bank.take 127)).Nodup:=by decide +kernel
 have cacheP:=ReorderedPhysical.cached 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin
  (by decide) (by decide) (by decide) nd (by
   intro h hh bad
   exact (by decide +kernel : ∀h∈hosts,h∉bank) h hh (List.mem_of_mem_take bad))
 have buildP:GatePhysical (ReorderedABuild.build 106 acc pad bank L.core.cin src hosts):=by
  simp only [ReorderedABuild.build,ReorderedAHead.head,A161Carry.buildPost,gatePhysical_append]
  exact ⟨⟨⟨seedP,subP⟩,cacheP.1⟩,topP⟩
 have notP:=notRegister_physical ((acc.take 138).drop 10)
 have inverseP:GatePhysical (ReorderedConsumedSub.consumed 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin):=by
  simp only [ReorderedConsumedSub.consumed,gatePhysical_append]
  exact ⟨⟨notP,cacheP.2⟩,notP⟩
 have tailP:GatePhysical (ReorderedATail.tail acc pad bank L.core.cin src):=by
  apply KnownOutputAdder.program_physical (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
   ((acc.take 138).drop 6) (bank.take 131) L.core.cin
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
 have oldInv:=(A161KnownTail.build8_physical acc pad bank L.core.cin src lengths.1 (by decide) fits).2
 simp only [A161KnownTail.unbuild8,gatePhysical_append] at oldInv
 have preInv:GatePhysical (A161Carry.unbuildPre acc pad bank L.core.cin src):=oldInv.1.1.1
 have unbuildP:GatePhysical (ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src hosts):=by
  simp only [ReorderedAUnbuild.unbuild,ReorderedAUnbuild.after,gatePhysical_append]
  exact ⟨⟨preInv,inverseP⟩,⟨tailP,seedP⟩⟩
 -- GM: split/join with `gatePhysical_append` only (the `simp … at old` steps cost 25.7 s of kernel time).
 have base:=aBodyTriple_physical L hw g (List.nodup_cons.mpr ⟨A161Low4FixedFold.ready.1,hn⟩)
 have b1:=(gatePhysical_append _ _).mp base
 have b2:=(gatePhysical_append _ _).mp b1.2
 have f1:=(gatePhysical_append _ _).mp A161Low4FixedFold.fold_physical
 have f2:=(gatePhysical_append _ _).mp f1.1
 have midOld:GatePhysical KnownAMidStaged.body:=by
  unfold GatePhysical
  intro i hi
  exact f2.2 i ((KnownSparseFold.Cert.sublist _ _ _ _ _ KnownAMidStaged.cert).subset hi)
 have midP:GatePhysical Ghost3CacheA.middle:=
  RelocateResources.physical GhostRelocatedKnown.ports GhostRelocatedKnown.ports_inj KnownAMidStaged.body midOld
 exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr ⟨b1.1,
  (gatePhysical_append _ _).mpr ⟨b2.1,(gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr ⟨buildP,midP⟩,unbuildP⟩⟩⟩,
  ReorderedPhysical.padding 4 L.core.cin⟩


end ECDSAAdd.Entrant.Ghost3APhysical

end


end


-- Verified relocation of A resources and the high inverse bodies.
-- Verified component Ghost3ABalance
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3ABalance
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed Challenge
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem counts:toffoliCount Ghost3SignA.body+3=toffoliCount SignKnownA.body ∧
 measurementCount Ghost3SignA.body=measurementCount SignKnownA.body:=by
 have nc:=Ghost3ACounts.cache_counts
 have oc:=ReorderedACounts.cache_counts
 have np:=Ghost3ACounts.pieces
 have op:=ReorderedACounts.pieces
 have mid:=GhostRelocatedKnown.A.counts
 change toffoliCount GhostRelocatedKnown.A.program=toffoliCount KnownAMidStaged.body ∧
  measurementCount GhostRelocatedKnown.A.program=measurementCount KnownAMidStaged.body at mid
 simp only [Ghost3ACounts.hosts] at nc np
 simp only [ReorderedACounts.hosts] at oc op
 simp only [Ghost3SignA.body,Ghost3SignA.rawBody,Ghost3SignA.fold,Ghost3SignA.loop,Ghost3SignA.suffix,Ghost3SignA.hosts,Ghost3CacheA.middle,
  SignKnownA.body,SignKnownA.rawBody,SignKnownA.fold,SignKnownA.loop,SignKnownA.suffix,toffoliCount_append,measurementCount_append]
 exact ⟨by omega,by omega⟩

theorem slots:gateSlots Ghost3SignA.body+1=gateSlots SignKnownA.body:=by
 have nc:=ReorderedSlots.cache 106 src ((acc.take 138).drop 10) (bank.take 127) Ghost3CacheA.hosts L.core.cin
  (by decide) (by decide) (by decide) Ghost3CacheA.geometry.2.1
 have oc:=ReorderedSlots.cache 103 src ((acc.take 138).drop 10) (bank.take 127) ReorderedAFixed.hosts L.core.cin
  (by decide) (by decide) (by decide) ReorderedAFixed.host_geometry.2.1
 have mid:=RelocateResources.slots GhostRelocatedKnown.ports KnownAMidStaged.body
 simp only [Ghost3SignA.body,Ghost3SignA.rawBody,Ghost3SignA.fold,Ghost3SignA.loop,Ghost3SignA.suffix,Ghost3SignA.hosts,Ghost3CacheA.middle,
  SignKnownA.body,SignKnownA.rawBody,SignKnownA.fold,SignKnownA.loop,SignKnownA.suffix,
  ReorderedAUnbuild.unbuild,ReorderedConsumedSub.consumed,gateSlots_append]
 change gateSlots GhostRelocatedKnown.A.program=gateSlots KnownAMidStaged.body+8 at mid
 omega

end ECDSAAdd.Entrant.Ghost3ABalance

end

-- Verified component SignedBodySupportA
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3BodyResources
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout Challenge
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires Challenge.gateSlots List.toFinset

open ReorderedAFixed in
theorem a_support:wires Ghost3SignA.body⊆wires Ghost3KnownA.body:=by
 have loop:wires Ghost3SignA.loop⊆wires Ghost3KnownA.loop:=by
  have eq:Ghost3KnownA.loop=ReorderedAHead.head acc pad bank L.core.cin src++Ghost3SignA.suffix:=by
   simp only [Ghost3KnownA.loop,Ghost3CacheA.loop,Ghost3CacheA.build,Ghost3CacheA.unbuild,ReorderedABuild.build,Ghost3KnownA.hosts,Ghost3SignA.suffix,Ghost3SignA.hosts,List.append_assoc]
  rw [Ghost3SignA.loop,eq,wires_append,wires_append]
  exact Finset.union_subset_union SignAHeadSupport.support (Finset.Subset.refl _)
 have pad:wires (ReorderedRecordPadding.program 7 L.core.cin)=wires (ReorderedRecordPadding.program 4 L.core.cin):=by
  simp [ReorderedRecordPadding.program,List.replicate_succ,wires,Instr.wires,correctionWires]
 simp only [Ghost3SignA.body,Ghost3SignA.rawBody,Ghost3SignA.fold,Ghost3KnownA.body,Ghost3KnownA.rawBody,
  Ghost3KnownA.fold,wires_append]
 rw [pad]
 repeat' first
  | exact loop
  | exact Finset.Subset.refl _
  | apply Finset.union_subset_union

open ReorderedAFixed in
theorem a_physical:GatePhysical Ghost3SignA.body:=by
 -- GM: split/join with `gatePhysical_append` only; `simp … at old ⊢` + `tauto` cost 25 s of kernel time.
 have old:=Ghost3APhysical.body_physical
 have head:=SignAHeadResources.physical
 have pad:=ReorderedPhysical.padding 7 L.core.cin
 have k1:=(gatePhysical_append _ _).mp old
 have k2:=(gatePhysical_append _ _).mp k1.1
 have k3:=(gatePhysical_append _ _).mp k2.2
 have k4:=(gatePhysical_append _ _).mp k3.2
 have k5:=(gatePhysical_append _ _).mp k4.1
 have k6:=(gatePhysical_append _ _).mp k5.1
 have k7:=(gatePhysical_append _ _).mp k6.1
 exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr ⟨k2.1,
  (gatePhysical_append _ _).mpr ⟨k3.1,(gatePhysical_append _ _).mpr ⟨head,
   (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr ⟨k7.2,k6.2⟩,k5.2⟩,k4.2⟩⟩⟩⟩,pad⟩

end ECDSAAdd.Entrant.Ghost3BodyResources

end


section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.HighUnbuildAResearch
open ReorderedAFixed InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
attribute [local irreducible] ECDSAAdd.run HighConsumedAResearch.sub

def unbuild(acc:List Wire):Program:=A161Carry.unbuildPre acc pad bank L.core.cin src++
 HighConsumedAResearch.sub++ReorderedAUnbuild.after acc pad bank L.core.cin src























































































end ECDSAAdd.Entrant.HighUnbuildAResearch

namespace ECDSAAdd.Entrant.HighUnbuildCResearch
open C163Low4Middle InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
attribute [local irreducible] ECDSAAdd.run HighConsumedCResearch.sub

def unbuild(acc:List Wire):Program:=C163Carry.unbuildPre acc pad bank L.core.cin src++
 HighConsumedCResearch.sub++ReorderedCUnbuild.after acc pad bank L.core.cin src























































































end ECDSAAdd.Entrant.HighUnbuildCResearch

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.HighCachedLoopAResearch
open ReorderedAFixed InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
attribute [local irreducible] ECDSAAdd.run

















































end ECDSAAdd.Entrant.HighCachedLoopAResearch

namespace ECDSAAdd.Entrant.HighCachedLoopCResearch
open C163Low4Middle InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
attribute [local irreducible] ECDSAAdd.run

















































end ECDSAAdd.Entrant.HighCachedLoopCResearch

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Baselines
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.HighBorrowResourceResearch

theorem quad_support:wires FiniteUniformAdder4Research.fast⊆wires FiniteUniformAdder4Research.original:=by decide +kernel

theorem quad_physical:GatePhysical FiniteUniformAdder4Research.fast:=
 physicalGateCheck_correct _ (by decide +kernel)

theorem quad_slots:Challenge.gateSlots FiniteUniformAdder4Research.fast+3=
 Challenge.gateSlots FiniteUniformAdder4Research.original:=by decide +kernel

theorem placed_support(f:Fin 12→Wire):wires (PlacedUniformAdder4Research.fastAt f)⊆
 wires (PlacedUniformAdder4Research.originalAt f):=by
 simp only [PlacedUniformAdder4Research.fastAt,PlacedUniformAdder4Research.originalAt,renameProgram_support]
 exact Finset.image_mono (PlacedUniformAdder4Research.label f) quad_support

theorem placed_physical(f:Fin 12→Wire)(hf:Function.Injective f):GatePhysical (PlacedUniformAdder4Research.fastAt f):=by
 apply gatePhysical_rename_support _ _ _ quad_physical
 intro a ha b hb eq
 exact PlacedUniformAdder4Research.label_inj f hf a (FiniteUniformAdder4Research.support.1 ha)
  b (FiniteUniformAdder4Research.support.1 hb) eq

theorem placed_slots(f:Fin 12→Wire):Challenge.gateSlots (PlacedUniformAdder4Research.fastAt f)+3=
 Challenge.gateSlots (PlacedUniformAdder4Research.originalAt f):=by
 simpa only [PlacedUniformAdder4Research.fastAt,PlacedUniformAdder4Research.originalAt,rename_gateSlots] using quad_slots
end ECDSAAdd.Entrant.HighBorrowResourceResearch

namespace ECDSAAdd.Entrant.HighConsumedAResearch

theorem support:wires fast⊆wires old:=by
 have q:=HighBorrowResourceResearch.placed_support ports
 have e:=congrArg wires shape
 simp only [wires_append] at e
 rw [fast,wires_append,wires_append,e]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem physical(h:GatePhysical old):GatePhysical fast:=by
 rw [shape] at h
 simp only [gatePhysical_append] at h
 change GatePhysical (pre++PlacedUniformAdder4Research.fastAt ports++post)
 simp only [gatePhysical_append]
 exact ⟨⟨h.1.1,HighBorrowResourceResearch.placed_physical ports ports_inj⟩,h.2⟩

theorem slots:Challenge.gateSlots fast+3=Challenge.gateSlots old:=by
 have h:=congrArg Challenge.gateSlots shape
 have q:=HighBorrowResourceResearch.placed_slots ports
 simp only [Challenge.gateSlots_append] at h
 have g:Challenge.gateSlots fast=Challenge.gateSlots pre+Challenge.gateSlots (PlacedUniformAdder4Research.fastAt ports)+Challenge.gateSlots post:=by
  simp only [fast,Challenge.gateSlots_append]
 omega

theorem sub_support:wires sub⊆wires (ReorderedConsumedSub.consumed 106 xs ys cs hs cin):=by
 have q:wires fast⊆wires (ReorderedGenericCache.consumedAdd 106 xs ys cs hs cin):=by simpa only [old] using support
 simp only [sub,ReorderedConsumedSub.consumed,wires_append]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem sub_physical(h:GatePhysical (ReorderedConsumedSub.consumed 106 xs ys cs hs cin)):GatePhysical sub:=by
 simp only [ReorderedConsumedSub.consumed,gatePhysical_append] at h
 change GatePhysical (notRegister ys++fast++notRegister ys)
 simp only [gatePhysical_append]
 exact ⟨⟨h.1.1,physical h.1.2⟩,h.2⟩

theorem sub_toffoli:toffoliCount sub+3=toffoliCount (ReorderedConsumedSub.consumed 106 xs ys cs hs cin):=by
 have q:=toffoli
 simp only [old] at q
 simp only [sub,ReorderedConsumedSub.consumed,toffoliCount_append]
 omega

theorem sub_slots:Challenge.gateSlots sub+3=Challenge.gateSlots (ReorderedConsumedSub.consumed 106 xs ys cs hs cin):=by
 have q:=slots
 simp only [old] at q
 simp only [sub,ReorderedConsumedSub.consumed,Challenge.gateSlots_append]
 omega
end ECDSAAdd.Entrant.HighConsumedAResearch

namespace ECDSAAdd.Entrant.HighUnbuildAResearch
open ReorderedAFixed

theorem support(acc:List Wire)(targetEq:(acc.take 138).drop 10=HighConsumedAResearch.ys):
 wires (unbuild acc)⊆wires (ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src Ghost3CacheA.hosts):=by
 have q:wires HighConsumedAResearch.sub⊆wires (ReorderedConsumedSub.consumed 106 src ((acc.take 138).drop 10) (bank.take 127) Ghost3CacheA.hosts L.core.cin):=by
  simpa only [targetEq] using HighConsumedAResearch.sub_support
 simp only [unbuild,ReorderedAUnbuild.unbuild,wires_append]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem physical(acc:List Wire)(targetEq:(acc.take 138).drop 10=HighConsumedAResearch.ys)
 (h:GatePhysical (ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src Ghost3CacheA.hosts)):
 GatePhysical (unbuild acc):=by
 simp only [ReorderedAUnbuild.unbuild,gatePhysical_append] at h
 have oldSub:GatePhysical (ReorderedConsumedSub.consumed 106 HighConsumedAResearch.xs HighConsumedAResearch.ys
  HighConsumedAResearch.cs HighConsumedAResearch.hs HighConsumedAResearch.cin):=by
  simpa only [targetEq] using h.1.2
 have newSub:=HighConsumedAResearch.sub_physical oldSub
 simp only [unbuild,gatePhysical_append]
 exact ⟨⟨h.1.1,newSub⟩,h.2⟩

theorem toffoli(acc:List Wire)(targetEq:(acc.take 138).drop 10=HighConsumedAResearch.ys):
 toffoliCount (unbuild acc)+3=toffoliCount (ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src Ghost3CacheA.hosts):=by
 have q:toffoliCount HighConsumedAResearch.sub+3=toffoliCount (ReorderedConsumedSub.consumed 106 src ((acc.take 138).drop 10) (bank.take 127) Ghost3CacheA.hosts L.core.cin):=by
  simpa only [targetEq] using HighConsumedAResearch.sub_toffoli
 simp only [unbuild,ReorderedAUnbuild.unbuild,toffoliCount_append]
 omega

theorem measurements(acc:List Wire)(targetEq:(acc.take 138).drop 10=HighConsumedAResearch.ys):
 measurementCount (unbuild acc)=measurementCount (ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src Ghost3CacheA.hosts):=by
 have q:measurementCount HighConsumedAResearch.sub=measurementCount (ReorderedConsumedSub.consumed 106 src ((acc.take 138).drop 10) (bank.take 127) Ghost3CacheA.hosts L.core.cin):=by
  simpa only [targetEq] using HighConsumedAResearch.sub_measurements
 simp only [unbuild,ReorderedAUnbuild.unbuild,measurementCount_append]
 omega

theorem slots(acc:List Wire)(targetEq:(acc.take 138).drop 10=HighConsumedAResearch.ys):
 Challenge.gateSlots (unbuild acc)+3=Challenge.gateSlots (ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src Ghost3CacheA.hosts):=by
 have q:Challenge.gateSlots HighConsumedAResearch.sub+3=Challenge.gateSlots (ReorderedConsumedSub.consumed 106 src ((acc.take 138).drop 10) (bank.take 127) Ghost3CacheA.hosts L.core.cin):=by
  simpa only [targetEq] using HighConsumedAResearch.sub_slots
 simp only [unbuild,ReorderedAUnbuild.unbuild,Challenge.gateSlots_append]
 omega



end ECDSAAdd.Entrant.HighUnbuildAResearch

namespace ECDSAAdd.Entrant.HighConsumedCResearch

theorem support:wires fast⊆wires old:=by
 have q:=HighBorrowResourceResearch.placed_support ports
 have e:=congrArg wires shape
 simp only [wires_append] at e
 rw [fast,wires_append,wires_append,e]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem physical(h:GatePhysical old):GatePhysical fast:=by
 rw [shape] at h
 simp only [gatePhysical_append] at h
 change GatePhysical (pre++PlacedUniformAdder4Research.fastAt ports++post)
 simp only [gatePhysical_append]
 exact ⟨⟨h.1.1,HighBorrowResourceResearch.placed_physical ports ports_inj⟩,h.2⟩

theorem slots:Challenge.gateSlots fast+3=Challenge.gateSlots old:=by
 have h:=congrArg Challenge.gateSlots shape
 have q:=HighBorrowResourceResearch.placed_slots ports
 simp only [Challenge.gateSlots_append] at h
 have g:Challenge.gateSlots fast=Challenge.gateSlots pre+Challenge.gateSlots (PlacedUniformAdder4Research.fastAt ports)+Challenge.gateSlots post:=by
  simp only [fast,Challenge.gateSlots_append]
 omega

theorem sub_support:wires sub⊆wires (ReorderedConsumedSub.consumed 102 xs ys cs hs cin):=by
 have q:wires fast⊆wires (ReorderedGenericCache.consumedAdd 102 xs ys cs hs cin):=by simpa only [old] using support
 simp only [sub,ReorderedConsumedSub.consumed,wires_append]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem sub_physical(h:GatePhysical (ReorderedConsumedSub.consumed 102 xs ys cs hs cin)):GatePhysical sub:=by
 simp only [ReorderedConsumedSub.consumed,gatePhysical_append] at h
 change GatePhysical (notRegister ys++fast++notRegister ys)
 simp only [gatePhysical_append]
 exact ⟨⟨h.1.1,physical h.1.2⟩,h.2⟩

theorem sub_toffoli:toffoliCount sub+3=toffoliCount (ReorderedConsumedSub.consumed 102 xs ys cs hs cin):=by
 have q:=toffoli
 simp only [old] at q
 simp only [sub,ReorderedConsumedSub.consumed,toffoliCount_append]
 omega

theorem sub_slots:Challenge.gateSlots sub+3=Challenge.gateSlots (ReorderedConsumedSub.consumed 102 xs ys cs hs cin):=by
 have q:=slots
 simp only [old] at q
 simp only [sub,ReorderedConsumedSub.consumed,Challenge.gateSlots_append]
 omega
end ECDSAAdd.Entrant.HighConsumedCResearch

namespace ECDSAAdd.Entrant.HighUnbuildCResearch
open C163Low4Middle

theorem support(acc:List Wire)(targetEq:(acc.take 140).drop 10=HighConsumedCResearch.ys):
 wires (unbuild acc)⊆wires (ReorderedCUnbuild.unbuild 102 acc pad bank L.core.cin src Ghost3CacheC.hosts):=by
 have q:wires HighConsumedCResearch.sub⊆wires (ReorderedConsumedSub.consumed 102 src ((acc.take 140).drop 10) (bank.take 129) Ghost3CacheC.hosts L.core.cin):=by
  simpa only [targetEq] using HighConsumedCResearch.sub_support
 simp only [unbuild,ReorderedCUnbuild.unbuild,wires_append]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem physical(acc:List Wire)(targetEq:(acc.take 140).drop 10=HighConsumedCResearch.ys)
 (h:GatePhysical (ReorderedCUnbuild.unbuild 102 acc pad bank L.core.cin src Ghost3CacheC.hosts)):
 GatePhysical (unbuild acc):=by
 simp only [ReorderedCUnbuild.unbuild,gatePhysical_append] at h
 have oldSub:GatePhysical (ReorderedConsumedSub.consumed 102 HighConsumedCResearch.xs HighConsumedCResearch.ys
  HighConsumedCResearch.cs HighConsumedCResearch.hs HighConsumedCResearch.cin):=by
  simpa only [targetEq] using h.1.2
 have newSub:=HighConsumedCResearch.sub_physical oldSub
 simp only [unbuild,gatePhysical_append]
 exact ⟨⟨h.1.1,newSub⟩,h.2⟩

theorem toffoli(acc:List Wire)(targetEq:(acc.take 140).drop 10=HighConsumedCResearch.ys):
 toffoliCount (unbuild acc)+3=toffoliCount (ReorderedCUnbuild.unbuild 102 acc pad bank L.core.cin src Ghost3CacheC.hosts):=by
 have q:toffoliCount HighConsumedCResearch.sub+3=toffoliCount (ReorderedConsumedSub.consumed 102 src ((acc.take 140).drop 10) (bank.take 129) Ghost3CacheC.hosts L.core.cin):=by
  simpa only [targetEq] using HighConsumedCResearch.sub_toffoli
 simp only [unbuild,ReorderedCUnbuild.unbuild,toffoliCount_append]
 omega

theorem measurements(acc:List Wire)(targetEq:(acc.take 140).drop 10=HighConsumedCResearch.ys):
 measurementCount (unbuild acc)=measurementCount (ReorderedCUnbuild.unbuild 102 acc pad bank L.core.cin src Ghost3CacheC.hosts):=by
 have q:measurementCount HighConsumedCResearch.sub=measurementCount (ReorderedConsumedSub.consumed 102 src ((acc.take 140).drop 10) (bank.take 129) Ghost3CacheC.hosts L.core.cin):=by
  simpa only [targetEq] using HighConsumedCResearch.sub_measurements
 simp only [unbuild,ReorderedCUnbuild.unbuild,measurementCount_append]
 omega

theorem slots(acc:List Wire)(targetEq:(acc.take 140).drop 10=HighConsumedCResearch.ys):
 Challenge.gateSlots (unbuild acc)+3=Challenge.gateSlots (ReorderedCUnbuild.unbuild 102 acc pad bank L.core.cin src Ghost3CacheC.hosts):=by
 have q:Challenge.gateSlots HighConsumedCResearch.sub+3=Challenge.gateSlots (ReorderedConsumedSub.consumed 102 src ((acc.take 140).drop 10) (bank.take 129) Ghost3CacheC.hosts L.core.cin):=by
  simpa only [targetEq] using HighConsumedCResearch.sub_slots
 simp only [unbuild,ReorderedCUnbuild.unbuild,Challenge.gateSlots_append]
 omega



end ECDSAAdd.Entrant.HighUnbuildCResearch

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked
 ReorderedAPlain.build ReorderedAPlain.unbuild ReorderedABuild.build ReorderedAUnbuild.unbuild
 ReorderedCPlain.build ReorderedCPlain.unbuild ReorderedCBuild.build ReorderedCUnbuild.unbuild
 RelocateThreeGhosts.program HighUnbuildAResearch.unbuild HighUnbuildCResearch.unbuild
 HighConsumedAResearch.sub HighConsumedCResearch.sub

namespace ECDSAAdd.Entrant.HighGhostAResearch
open ReorderedAFixed A161Low4Ghost Ghost3CacheA InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold



















































































































































end ECDSAAdd.Entrant.HighGhostAResearch

namespace ECDSAAdd.Entrant.HighGhostCResearch
open ReorderedCFixed C163Low4Middle Ghost3CacheC InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold








































































































































































end ECDSAAdd.Entrant.HighGhostCResearch

end


end
end
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.R2SqEp760
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires
def sqRet (L : CuccaroStreamedSquareWideLayout) : Wire := L.foldPad.getD 239 0
/-- Its body host: extension wire 130 (physically `poolWire 1363`). -/
def sqHost (ext : List Wire) : Wire := ext.getD 130 0
def sqSwap (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) : Equiv.Perm Wire :=
  Equiv.swap (sqRet L) (sqHost ext)
def bodySwap (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (B : Program) : Program :=
  renameProgram (sqSwap L ext) B

end ECDSAAdd.Entrant.R2SqEp760
end
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C163Low4Branch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout R2SqEp760
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
def branch (L:CuccaroStreamedSquareWideLayout) (ext:List Wire) (control:Wire) (bodyProgram:Program):Program:=
 OwnDiagAll12Square.gPrep L++ParkCopyS.withLowK2S L ext control L.core.sum L.core.product
  (bodySwap L ext bodyProgram)++OwnDiagAll12Square.gClear L

end ECDSAAdd.Entrant.C163Low4Branch
end
section



-- Program suffix and public entry share one replay module; original scopes are retained.
section
section
section
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
-- Verified component KnownStage
section

-- Two retained inner-sum witnesses replace outer carry producers32 and33.
-- Exact support, phase, record, T/M/S and physicality proofs checked separately.
section

-- Verified sum-inner carry component AffineProductReplacement
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum
namespace ECDSAAdd.Entrant.AffineProductReplacementResearch
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def parity : List Wire → BasisState → Bool
 | [],_=>false
 | q::qs,s=>s q ^^ parity qs s

def load (xs:List Wire) (t:Wire):Program:=xs.map (fun q=>Instr.CX q t)

theorem parity_write (xs:List Wire) (t:Wire) (s:BasisState) (v:Bool)
 (off:∀q∈xs,q≠t):parity xs (writeBit s t v)=parity xs s:=by
 induction xs with
 | nil=>rfl
 | cons q qs ih=>
  have hq:q≠t:=off q (by simp)
  have hqs:∀a∈qs,a≠t:=fun a ha=>off a (by simp [ha])
  simp only [parity]
  rw [ih hqs]
  simp [writeBit,Function.update,hq]

theorem load_run (xs:List Wire) (t:Wire) (s:State) (m:List Bool)
 (off:∀q∈xs,q≠t):
 run (load xs t) m s=⟨s.phase,writeBit s.basis t (s.basis t ^^ parity xs s.basis)⟩:=by
 induction xs generalizing s with
 | nil=>
  apply State.extensionality
  · rfl
  · funext q;simp [load,run,parity,writeBit]
 | cons q qs ih=>
  have hq:q≠t:=off q (by simp)
  have hqs:∀a∈qs,a≠t:=fun a ha=>off a (by simp [ha])
  simp only [load,List.map_cons,run]
  rw [show run (List.map (fun q=>Instr.CX q t) qs) m _=_ from ih _ hqs]
  rw [parity_write qs t s.basis _ hqs]
  simp [parity,writeBit,Function.update_idem,
   Bool.xor_assoc]

theorem equivalent (xs:List Wire) (a b t:Wire) (s:State) (m n:List Bool)
 (off:∀q∈xs,q≠t) (h:parity xs s.basis=(s.basis a && s.basis b)):
 run (load xs t) m s=run [.CCX a b t] n s:=by
 rw [load_run xs t s m off,h]
 rfl

theorem counts (xs:List Wire) (t:Wire):
 toffoliCount (load xs t)=0 ∧ measurementCount (load xs t)=0:=by
 induction xs with
 | nil=>simp [load,toffoliCount,measurementCount]
 | cons q qs ih=>simpa [load,toffoliCount,measurementCount] using ih

theorem physical (xs:List Wire) (t:Wire) (off:∀q∈xs,q≠t):GatePhysical (load xs t):=by
 intro i hi
 obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hi
 simpa [PhysicalInstr,ProperGate] using off q hq




end ECDSAAdd.Entrant.AffineProductReplacementResearch
end

-- Verified sum-inner carry component SumInnerCarryRelations
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.SumInnerCarryRelations
/-- The retained 33-bit inner split exposes two affine relations in the rebuilt outer sum. -/
theorem invF_bits33 (R : KRegs)(hh : R.h=33)(hs : 1<R.S.length)(ht : 1<R.T.length)
 (v : Nat)(st : BasisState)(inv : R.invF v st) :
 st (R.S.getD 0 0)=(v.testBit 0 ^^ v.testBit 33) ∧
 (st (R.S.getD 1 0) ^^ st (R.T.getD 1 0))=(v.testBit 1 ^^ v.testBit 34) := by
 have k:=InnerLinearCopy.lower_two_identities (v%2^33) (v/2^33)
 have ss:=inv.1;have tt:=inv.2
 change regValue R.S st=v%2^R.h+v/2^R.h at ss
 change regValue R.T st=2*(v%2^R.h)*(v/2^R.h) at tt
 rw [hh]at ss tt
 rw [InnerLinearCopy.register_testBit R.S 0 st (by omega),
  InnerLinearCopy.register_testBit R.S 1 st hs,InnerLinearCopy.register_testBit R.T 1 st ht,ss,tt]
 simpa only [Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow,Nat.reduceLT,
  decide_true,Bool.true_and,Nat.reduceAdd]using k

















end ECDSAAdd.Entrant.SumInnerCarryRelations
end

-- Verified sum-inner carry component SparseAffineCarryAdder
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SparseAffineCarryAdder
open AffineProductReplacementResearch
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def carries : List Wire → List Wire → Bool → BasisState → List Bool
 | a::as,b::bs,c,s =>
   let k:=carryBit (s a) (s b) c
   k::carries as bs k s
 | _,_,_,_=>[]

def witnesses : List (Option (List Wire)) → List Wire
 | []=>[]
 | none::ps=>witnesses ps
 | some qs::ps=>qs++witnesses ps

def Ready : List (Option (List Wire)) → List Bool → BasisState → Prop
 | [],_,_=>True
 | none::ps,_::ks,s=>Ready ps ks s
 | some qs::ps,k::ks,s=>parity qs s=k ∧ Ready ps ks s
 | _::_,[],_=>False

def head (p:Option (List Wire)) (a b cin c:Wire):Program:=
 match p with | none=>majority a b cin c | some qs=>load qs c

def program : List (Option (List Wire)) → List Wire → List Wire → List Wire → Wire → Program
 | p::ps,a::a'::as,b::b'::bs,c::cs,cin=>
   head p a b cin c++program ps (a'::as) (b'::bs) cs c++eraseCarry a b cin c++[.CX a b,.CX cin b]
 | _,xs,ys,cs,cin=>addInPlace xs ys cs cin

theorem carries_congr (xs ys:List Wire)(c:Bool)(s t:BasisState)
 (hx:∀q∈xs,s q=t q)(hy:∀q∈ys,s q=t q):carries xs ys c s=carries xs ys c t:=by
 induction xs generalizing ys c with
 | nil=>rfl
 | cons x xs ih=>
  cases ys with
  | nil=>rfl
  | cons y ys=>
   simp only [carries,hx x (by simp),hy y (by simp)]
   rw [ih ys _ (fun q hq=>hx q (by simp [hq])) (fun q hq=>hy q (by simp [hq]))]

theorem parity_congr (qs:List Wire)(s t:BasisState)(h:∀q∈qs,s q=t q):parity qs s=parity qs t:=by
 induction qs with
 | nil=>rfl
 | cons q qs ih=>
  simp only [parity,h q (by simp)]
  rw [ih (fun a ha=>h a (by simp [ha]))]

theorem ready_congr (ps:List (Option (List Wire)))(ks:List Bool)(s t:BasisState)
 (h:∀q∈witnesses ps,s q=t q)(r:Ready ps ks s):Ready ps ks t:=by
 induction ps generalizing ks with
 | nil=>trivial
 | cons p ps ih=>
  cases ks with
  | nil=>simp [Ready] at r
  | cons k ks=>
   cases p with
   | none=>exact ih ks (fun q hq=>h q hq) r
   | some qs=>
    refine ⟨?_,ih ks (fun q hq=>h q (by simp [witnesses,hq])) r.2⟩
    rw [←parity_congr qs s t (fun q hq=>h q (by simp [witnesses,hq]))]
    exact r.1

theorem head_measurements (p:Option (List Wire))(a b cin c:Wire):measurementCount (head p a b cin c)=0:=by
 cases p with
 | none=>simp [head,majority,measurementCount]
 | some qs=>exact (counts qs c).2

theorem head_run (p:Option (List Wire))(a b cin c:Wire)(s:State)(m:List Bool)
 (nd:[a,b,cin,c].Nodup)(off:∀qs,p=some qs→∀q∈qs,q≠c)
 (h:∀qs,p=some qs→parity qs s.basis=carryBit (s.basis a) (s.basis b) (s.basis cin)):
 run (head p a b cin c) m s=run (majority a b cin c) m s:=by
 cases p with
 | none=>rfl
 | some qs=>
  rw [head,load_run qs c s m (off qs rfl),majority_correct a b cin c nd s m,h qs rfl]

theorem measurement_eq (ps:List (Option (List Wire)))(xs ys cs:List Wire)(cin:Wire):
 measurementCount (program ps xs ys cs cin)=measurementCount (addInPlace xs ys cs cin):=by
 induction ps generalizing xs ys cs cin with
 | nil=>rfl
 | cons p ps ih=>
  cases xs with
  | nil=>rfl
  | cons a xs=>
   cases xs with
   | nil=>rfl
   | cons a' xs=>
    cases ys with
    | nil=>rfl
    | cons b ys=>
     cases ys with
     | nil=>rfl
     | cons b' ys=>
      cases cs with
      | nil=>rfl
      | cons c cs=>
       simp only [program,addInPlace,measurementCount_append,head_measurements,
        KnownSumCarry.majority_mc,ih]

 theorem equivalent (ps:List (Option (List Wire)))(xs ys cs:List Wire)(cin:Wire)
 (nd:(cin::(xs++ys++cs)).Nodup)(hl:xs.length=ys.length)(hc:cs.length+1=ys.length)
 (off:∀q∈witnesses ps,q∉cs)
 (s:State)(m:List Bool)(clean:∀q∈cs,s.basis q=false)
 (ready:Ready ps (carries xs ys (s.basis cin) s.basis) s.basis):
 run (program ps xs ys cs cin) m s=run (addInPlace xs ys cs cin) m s:=by
 induction ps generalizing xs ys cs cin s m with
 | nil=>rfl
 | cons p ps ih=>
  cases xs with
  | nil=>rfl
  | cons a xs=>
   cases xs with
   | nil=>rfl
   | cons a' xs=>
    cases ys with
    | nil=>simp at hl
    | cons b ys=>
     cases ys with
     | nil=>simp at hl
     | cons b' ys=>
      cases cs with
      | nil=>rfl
      | cons c cs=>
       have cnt:=List.nodup_iff_count.mp nd
       have h4:[a,b,cin,c].Nodup:=by
        apply List.nodup_iff_count.mpr
        intro q;have h:=cnt q
        simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
        omega
       have nt:(c::((a'::xs)++(b'::ys)++cs)).Nodup:=by
        apply List.nodup_iff_count.mpr
        intro q;have h:=cnt q
        simp only [List.count_cons,List.count_append] at h ⊢
        omega
       have nexs:∀q∈a'::xs,q≠c:=by
        intro q hq bad
        have h:=cnt c;subst q
        have pos:=List.count_pos_iff.mpr hq
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
        omega
       have neys:∀q∈b'::ys,q≠c:=by
        intro q hq bad
        have h:=cnt c;subst q
        have pos:=List.count_pos_iff.mpr hq
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
        omega
       have necs:∀q∈cs,q≠c:=by
        intro q hq bad
        have h:=cnt c;subst q
        have pos:=List.count_pos_iff.mpr hq
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
        omega
       have sub:∀q∈witnesses ps,q∈witnesses (p::ps):=by
        intro q hq
        cases p with
        | none=>exact hq
        | some qs=>exact List.mem_append_right qs hq
       have woff:∀qs,p=some qs→∀q∈qs,q≠c:=by
        intro qs hp q hq bad
        exact off q (by simp [hp,witnesses,hq]) (by simp [bad])
       let K:=carryBit (s.basis a) (s.basis b) (s.basis cin)
       let u:State:=⟨s.phase,writeBit s.basis c K⟩
       have keep(q:Wire)(hq:q≠c):u.basis q=s.basis q:=by simp [u,writeBit,hq]
       have uc:u.basis c=K:=by simp [u,writeBit]
       have tailReady:Ready ps (carries (a'::xs) (b'::ys) K s.basis) s.basis:=by
        cases p with
        | none=>exact ready
        | some qs=>exact ready.2
       have pre(mm:List Bool):run (head p a b cin c) mm s=u:=by
        rw [head_run p a b cin c s mm h4 woff]
        · rw [majority_correct a b cin c h4 s mm]
          simp [u,K,clean c (by simp)]
        · intro qs hp
          cases p with
          | none=>simp at hp
          | some ws=>
           have eq:ws=qs:=Option.some.inj hp
           subst qs
           exact ready.1
       have old(mm:List Bool):run (majority a b cin c) mm s=u:=by
        rw [majority_correct a b cin c h4 s mm]
        simp [u,K,clean c (by simp)]
       have readyU:Ready ps (carries (a'::xs) (b'::ys) (u.basis c) u.basis) u.basis:=by
        rw [uc,←carries_congr (a'::xs) (b'::ys) K s.basis u.basis
          (fun q hq=>(keep q (nexs q hq)).symm) (fun q hq=>(keep q (neys q hq)).symm)]
        apply ready_congr ps _ s.basis u.basis _ tailReady
        intro q hq
        exact (keep q (fun bad=>off q (sub q hq) (by simp [bad]))).symm
       have cl:∀q∈cs,u.basis q=false:=by
        intro q hq
        rw [keep q (necs q hq)]
        exact clean q (by simp [hq])
       have tail(mm:List Bool):=ih (a'::xs) (b'::ys) cs c nt
        (by simpa using hl) (by simpa using hc)
        (fun q hq hcs=>off q (sub q hq) (by simp [hcs])) u mm cl readyU
       simp only [program,addInPlace,List.append_assoc,run_append,run_take,
        head_measurements,KnownSumCarry.majority_mc,List.take_zero,List.drop_zero,
        measurement_eq]
       rw [pre,old,tail]
       rw [run_take]

def removed : List (Option (List Wire)) → List Wire → List Wire → List Wire → Nat
 | p::ps,_a::a'::as,_b::b'::bs,_c::cs=>(if p.isSome then 1 else 0)+removed ps (a'::as) (b'::bs) cs
 | _,_,_,_=>0

theorem head_toffoli (p:Option (List Wire))(a b cin c:Wire):
 toffoliCount (head p a b cin c)+(if p.isSome then 1 else 0)=1:=by
 cases p with
 | none=>simp [head,majority,toffoliCount]
 | some qs=>simp [head,(counts qs c).1]

theorem toffoli_eq (ps:List (Option (List Wire)))(xs ys cs:List Wire)(cin:Wire):
 toffoliCount (program ps xs ys cs cin)+removed ps xs ys cs=toffoliCount (addInPlace xs ys cs cin):=by
 induction ps generalizing xs ys cs cin with
 | nil=>simp [program,removed]
 | cons p ps ih=>
  cases xs with
  | nil=>simp [program,removed]
  | cons a xs=>
   cases xs with
   | nil=>simp [program,removed]
   | cons a' xs=>
    cases ys with
    | nil=>simp [program,removed]
    | cons b ys=>
     cases ys with
     | nil=>simp [program,removed]
     | cons b' ys=>
      cases cs with
      | nil=>simp [program,removed]
      | cons c cs=>
       have h:=head_toffoli p a b cin c
       have t:=ih (a'::xs) (b'::ys) cs c
       have old:toffoliCount (majority a b cin c)=1:=by simp [majority,toffoliCount]
       simp only [program,removed,addInPlace,toffoliCount_append,old]
       omega




end ECDSAAdd.Entrant.SparseAffineCarryAdder
end

-- Verified sum-inner carry component SparseAffineCarryFacts
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SparseAffineCarryAdder
open Arithmetic.KnownOutputAdder
open AffineProductReplacementResearch
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem next_sum (xs ys:List Wire)(c:Bool)(st:BasisState)(i:Nat)
 (hl:xs.length=ys.length)(hi:i+1<ys.length):
 (sumBits (mappedRead xs false) ys c st).getD (i+1) false=
 sumBit (st (xs.getD (i+1) 0)) (st (ys.getD (i+1) 0)) ((carries xs ys c st).getD i false):=by
 induction i generalizing xs ys c with
 | zero=>
  cases xs with
  | nil=>simp only [List.length_cons,List.length_nil] at hl hi;omega
  | cons x xs=>
   cases ys with
   | nil=>simp at hi
   | cons y ys=>
    cases xs with
    | nil=>simp only [List.length_cons,List.length_nil] at hl hi;omega
    | cons x' xs=>
     cases ys with
     | nil=>simp at hi
     | cons y' ys=>simp [sumBits,mappedRead,MappedBit.value,carries]
 | succ i ih=>
  cases xs with
  | nil=>simp only [List.length_cons,List.length_nil] at hl hi;omega
  | cons x xs=>
   cases ys with
   | nil=>simp at hi
   | cons y ys=>
    simpa [sumBits,mappedRead,MappedBit.value,carries,Nat.add_assoc] using
     ih xs ys (carryBit (st x) (st y) c) (by simpa using hl) (by simp at hi;omega)

theorem carry_from_next_sum (xs ys:List Wire)(c:Bool)(st:BasisState)(i:Nat)
 (hl:xs.length=ys.length)(hi:i+1<ys.length):
 (carries xs ys c st).getD i false=
 ((((regValue xs st+regValue ys st+c.toNat).testBit (i+1)) ^^ st (xs.getD (i+1) 0)) ^^ st (ys.getD (i+1) 0)):=by
 have k:=next_sum xs ys c st i hl hi
 have full:(sumBits (mappedRead xs false) ys c st).getD (i+1) false=
  (regValue xs st+regValue ys st+c.toNat).testBit (i+1):=by
  rw [←MixedLiteralAdderDevelop.boolValue_bit,sumBits_value _ _ _ _ (by simp [mappedRead,hl]),mappedRead_value]
  rw [Nat.testBit_mod_two_pow]
  simp [hi]
 rw [full]at k
 rw [k]
 unfold sumBit
 cases st (xs.getD (i+1) 0) <;> cases st (ys.getD (i+1) 0) <;>
  cases (carries xs ys c st).getD i false <;> rfl
theorem carries_length (xs ys:List Wire)(c:Bool)(st:BasisState)(hl:xs.length=ys.length):
 (carries xs ys c st).length=ys.length:=by
 induction xs generalizing ys c with
 | nil=>have e:ys=[]:=List.eq_nil_of_length_eq_zero hl.symm;subst ys;rfl
 | cons x xs ih=>
  cases ys with
  | nil=>simp at hl
  | cons y ys=>simp [carries,ih ys _ (by simpa using hl)]

theorem ready_of_getD (ps:List (Option (List Wire)))(ks:List Bool)(st:BasisState)
 (hl:ps.length≤ks.length)
 (h:∀i qs,ps.getD i none=some qs→parity qs st=ks.getD i false):Ready ps ks st:=by
 induction ps generalizing ks with
 | nil=>trivial
 | cons p ps ih=>
  cases ks with
  | nil=>simp at hl
  | cons k ks=>
   have t:Ready ps ks st:=ih ks (by simp only [List.length_cons] at hl;omega)
    (fun i qs hi=>by simpa using h (i+1) qs (by simpa using hi))
   cases p with
   | none=>exact t
   | some qs=>exact ⟨by simpa using h 0 qs rfl,t⟩



end ECDSAAdd.Entrant.SparseAffineCarryAdder
end

-- Verified sum-inner carry component SparseAffineCarryResources
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SparseAffineCarryAdder
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem removed_eq_count (ps:List (Option (List Wire)))(xs ys cs:List Wire)
 (hl:xs.length=ys.length)(hc:cs.length+1=ys.length)(hp:ps.length<ys.length):
 removed ps xs ys cs=ps.countP Option.isSome:=by
 induction ps generalizing xs ys cs with
 | nil=>simp [removed]
 | cons p ps ih=>
  cases xs with
  | nil=>simp only [List.length_nil] at hl;omega
  | cons a xs=>
   cases ys with
   | nil=>simp at hl
   | cons b ys=>
    cases xs with
    | nil=>simp only [List.length_cons,List.length_nil] at hl hp;omega
    | cons a' xs=>
     cases ys with
     | nil=>simp only [List.length_cons,List.length_nil] at hl hp;omega
     | cons b' ys=>
      cases cs with
      | nil=>simp only [List.length_cons,List.length_nil] at hc;omega
      | cons c cs=>
       rw [removed,ih (a'::xs) (b'::ys) cs (by simpa using hl) (by simpa using hc)
        (by simp only [List.length_cons] at hp ⊢;omega)]
       simp [List.countP_cons,Nat.add_comm]

 theorem savings (ps:List (Option (List Wire)))(xs ys cs:List Wire)(cin:Wire)
 (hl:xs.length=ys.length)(hc:cs.length+1=ys.length)(hp:ps.length<ys.length):
 toffoliCount (program ps xs ys cs cin)+ps.countP Option.isSome=toffoliCount (addInPlace xs ys cs cin):=by
 rw [←removed_eq_count ps xs ys cs hl hc hp]
 exact toffoli_eq ps xs ys cs cin

end ECDSAAdd.Entrant.SparseAffineCarryAdder
end

-- Verified sum-inner carry component SparseAffineCarryGeometry
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SparseAffineCarryAdder
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem physical (ps:List (Option (List Wire)))(xs ys cs:List Wire)(cin:Wire)
 (off:∀q∈witnesses ps,q∉cs)(old:GatePhysical (addInPlace xs ys cs cin)):
 GatePhysical (program ps xs ys cs cin):=by
 induction ps generalizing xs ys cs cin with
 | nil=>exact old
 | cons p ps ih=>
  cases xs with
  | nil=>exact old
  | cons a xs=>
   cases xs with
   | nil=>exact old
   | cons a' xs=>
    cases ys with
    | nil=>exact old
    | cons b ys=>
     cases ys with
     | nil=>exact old
     | cons b' ys=>
      cases cs with
      | nil=>exact old
      | cons c cs=>
       simp only [addInPlace,gatePhysical_append] at old
       have sub:∀q∈witnesses ps,q∈witnesses (p::ps):=by
        intro q hq
        cases p with
        | none=>exact hq
        | some qs=>exact List.mem_append_right qs hq
       have hp:GatePhysical (head p a b cin c):=by
        cases p with
        | none=>exact old.1.1.1
        | some qs=>
         exact AffineProductReplacementResearch.physical qs c (fun q hq bad=>
          off q (by simp [witnesses,hq]) (by simp [bad]))
       simp only [program,gatePhysical_append]
       exact ⟨⟨⟨hp,ih (a'::xs) (b'::ys) cs c
        (fun q hq hcs=>off q (sub q hq) (by simp [hcs])) old.1.1.2⟩,old.1.2⟩,old.2⟩
theorem load_support (qs:List Wire)(c:Wire):
 wires (AffineProductReplacementResearch.load qs c)⊆insert c qs.toFinset:=by
 induction qs with
 | nil=>simp [AffineProductReplacementResearch.load,wires]
 | cons q qs ih=>
  intro v hv
  simp only [AffineProductReplacementResearch.load,List.map_cons,wires,Instr.wires,
   Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with h|h
  · rcases h with rfl|rfl <;> simp
  · have h:=ih h
    simpa only [Finset.mem_insert,List.mem_toFinset,List.mem_cons] using
     (show v=c ∨ v=q ∨ v∈qs from by
      simp only [Finset.mem_insert,List.mem_toFinset]at h
      tauto)

theorem head_support (p:Option (List Wire))(a b cin c:Wire):
 wires (head p a b cin c)⊆wires (majority a b cin c)∪(p.getD []).toFinset:=by
 cases p with
 | none=>exact Finset.subset_union_left
 | some qs=>
  intro q hq
  have h:=load_support qs c hq
  simp only [Finset.mem_insert,List.mem_toFinset] at h
  rcases h with rfl|h
  · simp [majority,wires,Instr.wires]
  · exact Finset.mem_union_right _ (by simpa using h)

theorem support (ps:List (Option (List Wire)))(xs ys cs:List Wire)(cin:Wire):
 wires (program ps xs ys cs cin)⊆wires (addInPlace xs ys cs cin)∪(witnesses ps).toFinset:=by
 induction ps generalizing xs ys cs cin with
 | nil=>exact Finset.subset_union_left
 | cons p ps ih=>
  cases xs with
  | nil=>exact Finset.subset_union_left
  | cons a xs=>
   cases xs with
   | nil=>exact Finset.subset_union_left
   | cons a' xs=>
    cases ys with
    | nil=>exact Finset.subset_union_left
    | cons b ys=>
     cases ys with
     | nil=>exact Finset.subset_union_left
     | cons b' ys=>
      cases cs with
      | nil=>exact Finset.subset_union_left
      | cons c cs=>
       have hd:=head_support p a b cin c
       have ht:=ih (a'::xs) (b'::ys) cs c
       have we:witnesses (p::ps)=p.getD []++witnesses ps:=by cases p <;> rfl
       intro q hq
       have h1:=@hd q;have h2:=@ht q
       simp only [program,addInPlace,wires_append,Finset.mem_union,we,List.toFinset_append] at hq ⊢
       simp only [Finset.mem_union] at h1 h2
       tauto


end ECDSAAdd.Entrant.SparseAffineCarryAdder
end

-- Verified sum-inner carry component SumInnerSparseCertificate
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SumInnerSparseCertificate
open SparseAffineCarryAdder AffineProductReplacementResearch
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def w32 (xs ys:List Wire)(saved:Wire):List Wire:=
 [saved,ys.getD 0 0,xs.getD 0 0,ys.getD 33 0,xs.getD 33 0]
def w33 (xs ys:List Wire)(saved cross tq:Wire):List Wire:=
 [saved,cross,ys.getD 1 0,xs.getD 1 0,tq,ys.getD 34 0,xs.getD 34 0]
def patches (xs ys:List Wire)(s0 s1 t1 tq:Wire):List (Option (List Wire)):=
 [some [tq]]++List.replicate 31 none++[some (w32 xs ys s0),some (w33 xs ys s1 t1 tq)]

theorem xor_resolve (a b c:Bool)(h:a=(b ^^ c)):c=(a ^^ b):=by
 rw [h]
 cases b <;> cases c <;> rfl

theorem witness32 (xs ys:List Wire)(saved:Wire)(st:BasisState)(A B:Nat)
 (hv:st saved=((A+B).testBit 0 ^^ (A+B).testBit 33))
 (xb:∀i,i<xs.length→st (xs.getD i 0)=B.testBit i)
 (yb:∀i,i<ys.length→st (ys.getD i 0)=A.testBit i)
 (xl:34≤xs.length)(yl:34≤ys.length):
 parity (w32 xs ys saved) st=(((A+B).testBit 33 ^^ B.testBit 33) ^^ A.testBit 33):=by
 simp only [w32,parity,Bool.xor_false]
 rw [hv,yb 0 (by omega),xb 0 (by omega),yb 33 (by omega),xb 33 (by omega),
  (InnerLinearCopy.lower_two_identities A B).1]
 simp [Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

theorem witness33 (xs ys:List Wire)(saved cross tq:Wire)(st:BasisState)(A B:Nat)
 (hv:(st saved ^^ st cross)=((A+B).testBit 1 ^^ (A+B).testBit 34))
 (ht:st tq=(2*A*B).testBit 1)
 (xb:∀i,i<xs.length→st (xs.getD i 0)=B.testBit i)
 (yb:∀i,i<ys.length→st (ys.getD i 0)=A.testBit i)
 (xl:35≤xs.length)(yl:35≤ys.length):
 parity (w33 xs ys saved cross tq) st=(((A+B).testBit 34 ^^ B.testBit 34) ^^ A.testBit 34):=by
 have bit: (A+B).testBit 1=((A.testBit 1 ^^ B.testBit 1) ^^ st tq):=by
  apply xor_resolve _ _ _
  simpa only [ht,Bool.xor_comm] using (InnerLinearCopy.lower_two_identities A B).2.symm
 have top:=xor_resolve _ _ _ hv
 simp only [w33,parity,Bool.xor_false]
 rw [top,bit,yb 1 (by omega),xb 1 (by omega),yb 34 (by omega),xb 34 (by omega)]
 simp [Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
theorem cross_low_carry (A B:Nat):
 (2*A*B).testBit 1=carryBit (B.testBit 0) (A.testBit 0) false:=by
 rw [show 2*A*B=(A*B)*2 by ring]
 simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.reducePow,Nat.mul_div_cancel,
  Nat.div_one,carryBit,Bool.and_false,Bool.xor_false]
 have div : A*B*2/2=A*B := by omega
 rw [div,Nat.mul_mod]
 have ha:A%2=0 ∨ A%2=1:=by omega
 have hb:B%2=0 ∨ B%2=1:=by omega
 rcases ha with ha|ha <;> rcases hb with hb|hb <;> simp [ha,hb]

theorem ready (xs ys:List Wire)(s0 s1 t1 tq:Wire)(st:BasisState)(A B:Nat)
 (hl:xs.length=ys.length)(yl:35≤ys.length)
 (xv:regValue xs st=B)(yv:regValue ys st=A)
 (hs0:st s0=((A+B).testBit 0 ^^ (A+B).testBit 33))
 (hs1:(st s1 ^^ st t1)=((A+B).testBit 1 ^^ (A+B).testBit 34))
 (htq:st tq=(2*A*B).testBit 1):
 Ready (patches xs ys s0 s1 t1 tq) (carries xs ys false st) st:=by
 have xb(i:Nat)(hi:i<xs.length):st (xs.getD i 0)=B.testBit i:=by
  rw [InnerLinearCopy.register_testBit xs i st hi,xv]
 have yb(i:Nat)(hi:i<ys.length):st (ys.getD i 0)=A.testBit i:=by
  rw [InnerLinearCopy.register_testBit ys i st hi,yv]
 apply ready_of_getD
 · simp [patches,carries_length xs ys false st hl];omega
 · intro i qs hi
   have bound:i<34:=by
    by_contra bad
    have outOfRange : (patches xs ys s0 s1 t1 tq).length ≤ i :=by simp [patches];omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none outOfRange,Option.getD_none] at hi
    contradiction
   interval_cases i <;> simp [patches,w32,w33] at hi
   · subst qs
     simp only [parity,Bool.xor_false,carries,List.getD_cons_zero]
     cases xs with
     | nil=>simp at hl;omega
     | cons x xs=>
      cases ys with
      | nil=>simp at yl
      | cons y ys=>
       simpa [carries,htq,←xb 0 (by simp),←yb 0 (by simp)] using cross_low_carry A B
   · subst qs
     rw [carry_from_next_sum xs ys false st 32 hl (by omega),xv,yv,
      Bool.toNat_false,Nat.add_zero,Nat.add_comm B A]
     simp only [Nat.reduceAdd]
     rw [xb 33 (by omega),yb 33 (by omega)]
     simpa only [w32] using witness32 xs ys s0 st A B hs0 xb yb (by omega) (by omega)
   · subst qs
     rw [carry_from_next_sum xs ys false st 33 hl (by omega),xv,yv,
      Bool.toNat_false,Nat.add_zero,Nat.add_comm B A]
     simp only [Nat.reduceAdd]
     rw [xb 34 (by omega),yb 34 (by omega)]
     simpa only [w33] using witness33 xs ys s1 t1 tq st A B hs1 htq xb yb (by omega) (by omega)




















































end ECDSAAdd.Entrant.SumInnerSparseCertificate
end

-- Verified sum-inner carry component SumInnerSparseRebuild
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SumInnerSparseRebuild
open KRegs
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem copy_frame (R:KRegs)(w:R.W)(hn:R.all.Nodup)(s:State)(m:List Bool)
 (hS0:regValue R.S s.basis=0):
 (run R.m3 m s).phase=s.phase ∧
 regValue R.S (run R.m3 m s).basis=regValue R.lo s.basis ∧
 ∀q,q∉R.S→(run R.m3 m s).basis q=s.basis q:=by
 obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩:=R.lens w
 have h4:=w.h4;have hh:=w.hh;have h5:=w.h5;have hSl:=w.S
 have mt {q:Wire}(h:q∈R.S.take R.h):q∈R.S:=List.mem_of_mem_take h
 have md {q:Wire}(h:q∈R.S.drop R.h):q∈R.S:=List.mem_of_mem_drop h
 have ns:R.S.Nodup:=knd hn (fun q=>by simp only [all,List.count_cons,List.count_append];omega)
 obtain ⟨p,f,v⟩:=copyRegister_correct none R.lo (R.S.take R.h) (by omega)
  (knd hn (fun q=>by have c:=R.counts q;simp only [all,List.count_cons,List.count_append];omega))
  (by intro c hc;simp at hc) s m
 have val:regValue (R.S.take R.h) (run R.m3 m s).basis=regValue R.lo s.basis:=by
  change regValue (R.S.take R.h) (run (copyRegister none R.lo (R.S.take R.h)) m s).basis=_
  rw [v,show regValue (R.S.take R.h) s.basis=0 from
   (regValue_zero _ _).mpr (fun q h=>(regValue_zero _ _).mp hS0 q (mt h)),Nat.zero_xor]
  rfl
 have ff:∀q,q∉R.S.take R.h→(run R.m3 m s).basis q=s.basis q:=f
 have high:regValue (R.S.drop R.h) (run R.m3 m s).basis=0:=by
  rw [(kkeep ff (by
   intro q hq hx
   have c1:=List.count_pos_iff.mpr hq;have c2:=List.count_pos_iff.mpr hx
   have c3:=kcnt_split R.S R.h q;have c4:=List.nodup_iff_count_le_one.mp ns q
   omega)),show regValue (R.S.drop R.h) s.basis=0 from
   (regValue_zero _ _).mpr (fun q h=>(regValue_zero _ _).mp hS0 q (md h))]
 have allval:=regValue_append (R.S.take R.h) (R.S.drop R.h) (run R.m3 m s).basis
 rw [List.take_append_drop,val,high,Nat.mul_zero,Nat.add_zero] at allval
 exact ⟨p,allval,fun q h=>ff q (fun x=>h (mt x))⟩
open SparseAffineCarryAdder SumInnerSparseCertificate

def add (R inner:KRegs):Program:=
 SparseAffineCarryAdder.program
  (patches (R.hi++R.zS) R.S (inner.S.getD 0 0) (inner.S.getD 1 0) (inner.T.getD 1 0) R.tq)
  (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin

def rebuild (R inner:KRegs):Program:=R.m3++add R inner
































































end ECDSAAdd.Entrant.SumInnerSparseRebuild
end

-- Verified sum-inner carry component SumInnerSparseSquare
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SumInnerSparseSquare
open KRegs KG SparseAffineCarryAdder SumInnerSparseCertificate
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
abbrev K (L:CuccaroStreamedSquareWideLayout)(ext src dst:List Wire):KG:=
 LowZero18Square.patchKG L (LowZero18LowK.kg L ext src dst)
abbrev inner (L:CuccaroStreamedSquareWideLayout)(ext src dst:List Wire):KRegs:=
 LowZero18LowK.jregsS L ext src dst

def clear (L:CuccaroStreamedSquareWideLayout)(ext src dst:List Wire):Program:=
 let k:=K L ext src dst
 SumInnerSparseRebuild.rebuild k.R (inner L ext src dst)++
  k.R.c8z++k.R.c7t++k.R.c6h++k.Q5c++k.R.scl1591++k.Q2c++k.Q1c

theorem geometry (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)(ext src dst:List Wire)
 (he:300≤ext.length)(hs:src.length=129)
 (hall:(LowZero18LowK.kg L ext src dst).all.Nodup):
 (K L ext src dst).R.h=64 ∧ (K L ext src dst).R.bank.length=129 ∧
 (inner L ext src dst).h=33 ∧ 1 < (inner L ext src dst).S.length ∧ 1 < (inner L ext src dst).T.length ∧
 (∀q∈(inner L ext src dst).S++(inner L ext src dst).T,q∉(K L ext src dst).R.all):=by
 have sizes:=L.measured_bank_widths hw
 have kr:(K L ext src dst).R=LowZero18LowK.oregs L ext src dst:=LowZero18LowK.kg_R L ext src dst
 have x5:(K L ext src dst).X5=(inner L ext src dst).S++(inner L ext src dst).T:=by
  simp only [K,LowZero18Square.patchKG,SquareCarryLoan719.patchKG,LowZero18LowK.kg,hs,
   show ¬(129:Nat)=128 by decide,if_false,LowZero18LowK.kgS,inner]
 refine ⟨?_,?_,rfl,?_,?_,?_⟩
 · rw [kr];rfl
 · rw [kr];simp [LowZero18LowK.oregs,sizes.1,hs]
 · simp only [inner,LowZero18LowK.jregsS,List.length_take,List.length_drop];omega
 · simp only [inner,LowZero18LowK.jregsS,List.length_take,List.length_drop];omega
 · intro q hq bad
   have hX:q∈(K L ext src dst).X:=by
    simp only [KG.X,List.mem_append,x5]
    have h:=List.mem_append.mp hq
    tauto
   exact (K L ext src dst).rX hall q bad hX
































































end ECDSAAdd.Entrant.SumInnerSparseSquare
end

-- Verified sum-inner carry component SumInnerSparsePark
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SumInnerSparsePark
open ParkCopy ParkCopySumDevelop ParkCopyS LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run wires



def pCL (L:CuccaroStreamedSquareWideLayout)(ext src dst:List Wire):Program:=
 SumInnerSparseSquare.clear L ext src dst

def withLowK2S (L:CuccaroStreamedSquareWideLayout)(ext:List Wire)(control:Wire)(src dst:List Wire)(body:Program):Program:=
 ParkCopyS.pA L control src++ParkCopyS.pM L ext src dst++ParkCopyS.pE1 L control src++ParkCopyS.pD ext++ParkCopyS.pMI L ext src++ParkCopyS.pB L ext body++
  ParkCopyS.pC1 L control src dst++ParkCopyS.pMO L ext src++pCL L ext src dst++ParkCopyS.pE L control src






















































































































































































































































































































































































































































































































































































end ECDSAAdd.Entrant.SumInnerSparsePark
end

-- Verified sum-inner carry component SumInnerSparseSupport
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SumInnerSparseSupport
open KRegs KG SparseAffineCarryAdder SumInnerSparseCertificate
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

-- Prepared while native mandatory replay runs. Not checked until that replay ends.





























































end ECDSAAdd.Entrant.SumInnerSparseSupport
end

-- Verified sum-inner carry component SumInnerSparseSwap
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SumInnerSparseSwap
open Arithmetic.CuccaroStreamedSquareWideLayout R2SqEp760
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run wires





























end ECDSAAdd.Entrant.SumInnerSparseSwap
end

-- Verified sum-inner carry component SumInnerSparseCBranch
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SumInnerSparseCBranch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout R2SqEp760
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires















































































































































def branch (L:CuccaroStreamedSquareWideLayout) (ext:List Wire) (control:Wire) (bodyProgram:Program):Program:=
 OwnDiagAll12Square.gPrep L++SumInnerSparsePark.withLowK2S L ext control L.core.sum L.core.product
  (bodySwap L ext bodyProgram)++OwnDiagAll12Square.gClear L




































































































































































end ECDSAAdd.Entrant.SumInnerSparseCBranch
end

-- Verified sum-inner carry component SparseAffineCarrySlots
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SparseAffineCarryAdder
open Challenge AffineProductReplacementResearch
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run wires

theorem load_slots (qs:List Wire)(c:Wire):gateSlots (load qs c)=qs.length:=by
 induction qs with
 | nil=>simp [load,gateSlots]
 | cons q qs ih=>simpa [load,gateSlots,instructionSlots,Nat.add_comm] using congrArg (fun n:Nat=>1+n) ih

theorem head_slots (p:Option (List Wire))(a b cin c:Wire):
 gateSlots (head p a b cin c)+6*(if p.isSome then 1 else 0)=6+(p.getD []).length:=by
 cases p with
 | none=>simp [head,majority,gateSlots,instructionSlots]
 | some qs=>simp [head,load_slots,Nat.add_comm]

theorem slots (ps:List (Option (List Wire)))(xs ys cs:List Wire)(cin:Wire)
 (hl:xs.length=ys.length)(hc:cs.length+1=ys.length)(hp:ps.length<ys.length):
 gateSlots (program ps xs ys cs cin)+6*ps.countP Option.isSome=
 gateSlots (addInPlace xs ys cs cin)+(ps.map (fun p=>(p.getD []).length)).sum:=by
 induction ps generalizing xs ys cs cin with
 | nil=>simp [program]
 | cons p ps ih=>
  cases xs with
  | nil=>simp only [List.length_nil] at hl;omega
  | cons a xs=>
   cases ys with
   | nil=>simp at hl
   | cons b ys=>
    cases xs with
    | nil=>simp only [List.length_cons,List.length_nil] at hl hp;omega
    | cons a' xs=>
     cases ys with
     | nil=>simp only [List.length_cons,List.length_nil] at hl hp;omega
     | cons b' ys=>
      cases cs with
      | nil=>simp only [List.length_cons,List.length_nil] at hc;omega
      | cons c cs=>
       have t:=ih (a'::xs) (b'::ys) cs c (by simpa using hl) (by simpa using hc)
        (by simp only [List.length_cons]at hp ⊢;omega)
       have h:=head_slots p a b cin c
       have old:gateSlots (majority a b cin c)=6:=by simp [majority,gateSlots,instructionSlots]
       simp only [program,addInPlace,gateSlots_append,List.countP_cons,List.map_cons,List.sum_cons,old]
       cases hp:p.isSome <;> simp only [hp,Bool.false_eq_true,if_false,if_true] at h ⊢ <;> omega













end ECDSAAdd.Entrant.SparseAffineCarryAdder
end

-- Verified sum-inner carry component SumInnerSparseSlotLedger
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SumInnerSparseSlotLedger
open Challenge KRegs
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run wires

theorem old_slots (R:KRegs)(w:R.W):gateSlots R.smkT+5=gateSlots R.smk:=by
 obtain ⟨a,a',as,b,b',bs,c,cs,t0,ts,e1,e2,e3,e4,-,-⟩:=R.m4_shape w
 simp only [smkT,smk,m4T,m4,gateSlots_append]
 rw [e3,e1,e2]
 simp only [KnownSumCarry.addFirst,addInPlace,gateSlots_append]
 have cp:gateSlots [.CX R.tq c]=1:=rfl
 have maj:gateSlots (majority a b R.cin c)=6:=rfl
 rw [cp,maj]
 omega

















































end ECDSAAdd.Entrant.SumInnerSparseSlotLedger
end

-- Verified sum-inner carry component SumInnerSparsePhysical
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SumInnerSparsePhysical
open KRegs KG SparseAffineCarryAdder SumInnerSparseCertificate SumInnerSparseSquare
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run wires
























































































end ECDSAAdd.Entrant.SumInnerSparsePhysical
end

-- Verified sum-inner carry component SumInnerSparseExactSupport
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.SumInnerSparseExactSupport
open KRegs SparseAffineCarryAdder SumInnerSparseCertificate
set_option maxHeartbeats 4000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run wires

theorem majority_subset_erase (a b cin c:Wire):wires (majority a b cin c)⊆wires (eraseCarry a b cin c):=by
 intro q hq
 simp only [majority,wires,Instr.wires,eraseCarry,correctionWires,Finset.mem_union,
  Finset.mem_insert,Finset.mem_singleton,or_false] at hq ⊢
 tauto

theorem smk_subset_smkT (R:KRegs)(w:R.W):wires R.smk⊆wires R.smkT:=by
 obtain ⟨a,a',as,b,b',bs,c,cs,t0,ts,e1,e2,e3,e4,-,-⟩:=R.m4_shape w
 simp only [smk,smkT,m4,m4T,wires_append]
 rw [e3,e1,e2]
 simp only [addInPlace,KnownSumCarry.addFirst,wires_append]
 intro q hq
 have h:=@majority_subset_erase a b R.cin c q
 simp only [Finset.mem_union] at hq ⊢
 tauto

def extra (R inner:KRegs):Finset Wire:=
 (witnesses (patches (R.hi++R.zS) R.S (inner.S.getD 0 0) (inner.S.getD 1 0) (inner.T.getD 1 0) R.tq)).toFinset

theorem rebuild_support (R inner:KRegs)(w:R.W):
 wires (SumInnerSparseRebuild.rebuild R inner)⊆wires R.smkT∪extra R inner:=by
 have sparse:=SparseAffineCarryAdder.support
  (patches (R.hi++R.zS) R.S (inner.S.getD 0 0) (inner.S.getD 1 0) (inner.T.getD 1 0) R.tq)
  (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
 have old:=smk_subset_smkT R w
 have pair:wires R.m3∪wires R.m4⊆wires R.smkT:=by
  simpa only [KRegs.smk,wires_append] using old
 intro q hq
 simp only [SumInnerSparseRebuild.rebuild,wires_append] at hq
 rcases Finset.mem_union.mp hq with hm3|hnew
 · exact Finset.mem_union_left _ (pair (Finset.mem_union_left _ hm3))
 · have h:=sparse hnew
   rcases Finset.mem_union.mp h with hbase|hextra
   · exact Finset.mem_union_left _ (pair (Finset.mem_union_right _ hbase))
   · exact Finset.mem_union_right _ hextra



theorem context_support (P Q tail:Program)(extra:Finset Wire)(h:wires P⊆wires Q∪extra):
 wires (P++tail)⊆wires (Q++tail)∪extra:=by
 intro q hq
 have hh:=@h q
 simp only [wires_append,Finset.mem_union]at hq hh ⊢
 tauto

theorem clear_support (L:CuccaroStreamedSquareWideLayout)(ext src dst:List Wire)
 (sp:(LowZero18LowK.kg L ext src dst).Spec):
 wires (SumInnerSparseSquare.clear L ext src dst)⊆
 wires (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst))∪
 extra (SumInnerSparseSquare.K L ext src dst).R (SumInnerSparseSquare.inner L ext src dst):=by
 let k:=SumInnerSparseSquare.K L ext src dst
 let j:=SumInnerSparseSquare.inner L ext src dst
 have h:=rebuild_support k.R j sp.w
 simp only [SumInnerSparseSquare.clear,LowZero18Square.clear,LowZero18KG.clear,List.append_assoc]
 simpa only [List.append_assoc] using context_support (SumInnerSparseRebuild.rebuild k.R j) k.R.smkT
  (k.R.c8z++k.R.c7t++k.R.c6h++k.Q5c++k.R.scl1591++k.Q2c++k.Q1c) (extra k.R j) h


theorem sandwich_support (pre P Q post:Program)(E:Finset Wire)(h:wires P⊆wires Q∪E):
 wires (pre++P++post)⊆wires (pre++Q++post)∪E:=by
 intro q hq
 have hc:=@h q
 simp only [wires_append,Finset.mem_union]at hq hc ⊢
 tauto

abbrev extraL (L:CuccaroStreamedSquareWideLayout)(ext src dst:List Wire):Finset Wire:=
 extra (SumInnerSparseSquare.K L ext src dst).R (SumInnerSparseSquare.inner L ext src dst)

theorem park_support (L:CuccaroStreamedSquareWideLayout)(ext src dst:List Wire)(control:Wire)(body:Program)
 (sp:(LowZero18LowK.kg L ext src dst).Spec):
 wires (SumInnerSparsePark.withLowK2S L ext control src dst body)⊆
 wires (ParkCopyS.withLowK2S L ext control src dst body)∪extraL L ext src dst:=by
 let pre:=ParkCopyS.pA L control src++ParkCopyS.pM L ext src dst++ParkCopyS.pE1 L control src++
  ParkCopyS.pD ext++ParkCopyS.pMI L ext src++ParkCopyS.pB L ext body++ParkCopyS.pC1 L control src dst++ParkCopyS.pMO L ext src
 have h:=sandwich_support pre (SumInnerSparseSquare.clear L ext src dst)
  (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) (ParkCopyS.pE L control src)
  (extraL L ext src dst) (clear_support L ext src dst sp)
 simpa only [SumInnerSparsePark.withLowK2S,ParkCopyS.withLowK2S,SumInnerSparsePark.pCL,ParkCopyS.pCL,
  pre,List.append_assoc] using h

theorem branch_support (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)(ext:List Wire)(control:Wire)
 (hn:(control::L.wires).Nodup)(he:ECDSAAdd.Entrant.ExtOK L control ext)(body:Program):
 wires (SumInnerSparseCBranch.branch L ext control body)⊆
 wires (C163Low4Branch.branch L ext control body)∪extraL L ext L.core.sum L.core.product:=by
 have srcCount(q:Wire):L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q:=by
  have h:=(List.take_sublist 128 (L.core.y.drop 128)).count_le q
  have d:=(List.drop_sublist 128 L.core.y).count_le q
  simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append]at h ⊢
  omega
 have hall:=LowZero18LowK.kg_nodup L control hn ext L.core.sum L.core.product srcCount (fun _=>le_rfl) he.nodup he.away
 have sp:=LowZero18LowK.kg_spec L hw ext L.core.sum L.core.product
  (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
  (by simp [hw.core.product,L.core.sum_length hw.core]) he.len hall
 have cl:=park_support L ext L.core.sum L.core.product control (R2SqEp760.bodySwap L ext body) sp
 have h:=sandwich_support (OwnDiagAll12Square.gPrep L)
  (SumInnerSparsePark.withLowK2S L ext control L.core.sum L.core.product (R2SqEp760.bodySwap L ext body))
  (ParkCopyS.withLowK2S L ext control L.core.sum L.core.product (R2SqEp760.bodySwap L ext body))
  (OwnDiagAll12Square.gClear L) (extraL L ext L.core.sum L.core.product) cl
 simpa only [SumInnerSparseCBranch.branch,C163Low4Branch.branch] using h



def extraProgram (R inner:KRegs):Program:=
 (witnesses (patches (R.hi++R.zS) R.S (inner.S.getD 0 0) (inner.S.getD 1 0) (inner.T.getD 1 0) R.tq)).map Instr.X

theorem x_wires (xs:List Wire):wires (xs.map Instr.X)=xs.toFinset:=by
 induction xs with
 | nil=>simp [wires]
 | cons x xs ih=>simp [wires,Instr.wires,ih]

theorem extraProgram_wires (R inner:KRegs):wires (extraProgram R inner)=extra R inner:=x_wires _

theorem place_support (L:ControlledPointLayout)(P Q E:Program)(h:wires P⊆wires Q∪wires E):
 wires (SquareCarryLoan719BF.place L P)⊆wires (SquareCarryLoan719BF.place L Q)∪wires (SquareCarryLoan719BF.place L E):=by
 simp only [SquareCarryLoan719BF.place,renameProgram_support]
 simpa only [Finset.image_union] using Finset.image_mono (ControlLoan1589Square.swap L) (Finset.image_mono (Prefix1590Square.swap L) (Finset.image_mono (PrefixFrontierSquare1591.swap L) (Finset.image_mono (OwnDiagAll12PlacedQ7.swap L) (Finset.image_mono (OwnDiagAll12PlacedQ6.swap L) (Finset.image_mono (OwnQ5Square.swap L) (Finset.image_mono (OwnQ4Square.swap L) (Finset.image_mono (OwnGuardSquare.swap L) (Finset.image_mono (OwnPlusSquare.swap L) (Finset.image_mono (Square5Placement.blockPerm L 202) (h))))))))))







end ECDSAAdd.Entrant.SumInnerSparseExactSupport
end

-- Verified sum-inner carry component SumInnerSparseExtraFacts
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Baselines
namespace ECDSAAdd.Entrant.SumInnerSparseExtraFacts
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run wires

def program (L:ControlledPointLayout):Program:=
 let K:=L.dialogStreamedSquareWide
 let ext:=OwnDiagAll12Square.kext L
 SquareCarryLoan719BF.place L (SumInnerSparseExactSupport.extraProgram
  (SumInnerSparseSquare.K K ext K.core.sum K.core.product).R
  (SumInnerSparseSquare.inner K ext K.core.sum K.core.product))

def addresses:List Wire:=[5094,5546,5028,4565,5061,4598,5547,5581,5029,4566,5094,5062,4599]
def retired:List Nat:=[1800,766,765,767,770,1285,1286,769,768,718,719,760]

theorem program_eq:program layout=addresses.map Instr.X:=by decide +kernel

theorem program_wires:wires (program layout)=addresses.toFinset:=by
 rw [program_eq]
 exact SumInnerSparseExactSupport.x_wires addresses

theorem pool_eq(i:Nat)(hi:i<5699):layout.core.poolWire i=4115+i:=by
 simp only [PointAddLayout.poolWire,layout]
 rw [List.getD_eq_getElem _ _ (by simp;omega)]
 simp

theorem pool_site(i:Nat)(good:i<515 ∨ (717 ≤ i ∧ i<1029) ∨ (1284 ≤ i ∧ i<1541) ∨ i=1800):
 4115+i∈(OB5Support.sites layout).toFinset:=by
 have bound:i<5699:=by rcases good with h|h|h|h <;> omega
 have mem:=OB5Support.pool_mem layout i good
 rw [pool_eq i bound]at mem
 exact List.mem_toFinset.mpr (OB5Support.pool_in_sites layout _ mem)

theorem within_sites:wires (program layout)⊆(OB5Support.sites layout).toFinset:=by
 rw [program_wires]
 intro q hq
 have h:=List.mem_toFinset.mp hq
 simp only [addresses,List.mem_cons,List.not_mem_nil,or_false]at h
 rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact pool_site 979 (by omega)
 · exact pool_site 1431 (by omega)
 · exact pool_site 913 (by omega)
 · exact pool_site 450 (by omega)
 · exact pool_site 946 (by omega)
 · exact pool_site 483 (by omega)
 · exact pool_site 1432 (by omega)
 · exact pool_site 1466 (by omega)
 · exact pool_site 914 (by omega)
 · exact pool_site 451 (by omega)
 · exact pool_site 979 (by omega)
 · exact pool_site 947 (by omega)
 · exact pool_site 484 (by omega)

theorem retired_map:retired.map layout.core.poolWire=retired.map (fun i=>4115+i):=by
 simp only [retired,List.map_cons,List.map_nil]
 rw [pool_eq 1800 (by decide),pool_eq 766 (by decide),pool_eq 765 (by decide),pool_eq 767 (by decide),pool_eq 770 (by decide),pool_eq 1285 (by decide),pool_eq 1286 (by decide),pool_eq 769 (by decide),pool_eq 768 (by decide),pool_eq 718 (by decide),pool_eq 719 (by decide),pool_eq 760 (by decide)]

theorem disjoint_retired:Disjoint (wires (program layout)) ((retired.map layout.core.poolWire).toFinset):=by
 rw [program_wires,retired_map]
 decide +kernel

theorem free (i:Nat)(hi:i∈retired):layout.core.poolWire i∉wires (program layout):=by
 intro bad
 exact Finset.disjoint_left.mp disjoint_retired bad
  (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hi,rfl⟩))



end ECDSAAdd.Entrant.SumInnerSparseExtraFacts
end

end
end
end
end
end
end
end
