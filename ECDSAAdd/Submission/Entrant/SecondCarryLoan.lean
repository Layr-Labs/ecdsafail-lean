import ECDSAAdd.Submission.Entrant.CarryWindow
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.SecondCarryLoan

def loan (u0 u1 e0 host : Wire) : Program :=
 [.measureX host [] [.Z u1,.Z u0,.CZ u0 e0]]

theorem loan_run (u0 u1 e0 host : Wire) (h0:u0≠host) (h1:u1≠host) (he:e0≠host)
 (s : State) (m : List Bool) (hk:s.basis host=(s.basis u1 ^^ s.basis u0 ^^ (s.basis u0 && s.basis e0))) :
 run (loan u0 u1 e0 host) m s=⟨s.phase,writeBit s.basis host false⟩ := by
 cases m with
 | nil => simp [loan,run,measureAndCorrect,correct]
 | cons bit ms =>
  cases bit <;> cases hu:s.basis u0 <;> cases hv:s.basis u1 <;> cases he0:s.basis e0 <;>
   simp [loan,run,measureAndCorrect,correct,hk,hu,hv,he0,writeBit,Function.update_apply,h0,h1,he]

def restore (u0 u1 e0 host : Wire) : Program :=
 [.CCX u0 e0 host,.CX u0 host,.CX u1 host]

theorem restore_run (u0 u1 e0 host : Wire) (h0:u0≠host) (h1:u1≠host) (_he:e0≠host)
 (s : State) (m : List Bool) : run (restore u0 u1 e0 host) m s=
 ⟨s.phase,writeBit s.basis host (s.basis host ^^ (s.basis u1 ^^ s.basis u0 ^^ (s.basis u0 && s.basis e0)))⟩ := by
 change (⟨s.phase,_⟩:State)=⟨s.phase,_⟩
 apply congrArg (State.mk s.phase)
 funext q
 by_cases hq:q=host
 · subst q
   cases a:s.basis u0 <;> cases b:s.basis u1 <;> cases c:s.basis e0 <;>
    simp [restore,run,writeBit,Function.update_apply,h0,h1,_he,a,b,c]
 · simp [restore,run,writeBit,Function.update_apply,hq]

def prime2 (a b c host : Wire) : Program := [.X b]++majority a b c host++[.X b]

theorem prime2_run (a b c host : Wire) (hab:a≠b) (hac:a≠c) (hah:a≠host)
 (hbc:b≠c) (hbh:b≠host) (hch:c≠host) (s : State) (m : List Bool) :
 run (prime2 a b c host) m s=
 ⟨s.phase,writeBit s.basis host (s.basis host ^^ carryBit (s.basis a) (!s.basis b) (s.basis c))⟩ := by
 change (⟨s.phase,_⟩:State)=⟨s.phase,_⟩
 apply congrArg (State.mk s.phase)
 funext q
 by_cases hq:q=host
 · subst q
   cases aa:s.basis a <;> cases bb:s.basis b <;> cases cc:s.basis c <;>
    simp [prime2,majority,run,writeBit,Function.update_apply,carryBit,hab,hac,hah,hbc,hbh,hch,
      Ne.symm hab,Ne.symm hac,Ne.symm hbc,Ne.symm hbh,Ne.symm hch,aa,bb,cc]
 by_cases hqb:q=b
 · subst q
   simp [prime2,majority,run,writeBit,Function.update_apply,hab,hac,hah,hbc,hbh,hch,
      Ne.symm hab,Ne.symm hac,Ne.symm hbc,Ne.symm hbh,Ne.symm hch]
 by_cases hqc:q=c
 · subst q
   simp [prime2,majority,run,writeBit,Function.update_apply,hab,hac,hah,hbc,hbh,hch,
      Ne.symm hab,Ne.symm hac,Ne.symm hbc,Ne.symm hbh,Ne.symm hch]
 simp [prime2,majority,run,writeBit,Function.update_apply,hq,hqb,hqc]

def clear2 (a b c host : Wire) : Program :=
 [.measureX host [] [.Z a,.CZ a b,.CZ a c,.Z c,.CZ b c]]

theorem clear2_run (a b c host : Wire) (ha:a≠host) (hb:b≠host) (hc:c≠host)
 (s : State) (m : List Bool) (hk:s.basis host=carryBit (s.basis a) (!s.basis b) (s.basis c)) :
 run (clear2 a b c host) m s=⟨s.phase,writeBit s.basis host false⟩ := by
 cases m with
 | nil => simp [clear2,run,measureAndCorrect,correct]
 | cons bit ms =>
  cases bit <;> cases aa:s.basis a <;> cases bb:s.basis b <;> cases cc:s.basis c <;>
   simp [clear2,run,measureAndCorrect,correct,hk,carryBit,aa,bb,cc,writeBit,Function.update_apply,ha,hb,hc]

#print axioms loan_run
#print axioms restore_run
#print axioms prime2_run
#print axioms clear2_run
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SecondCarryLoan
open CarryWindowCache

theorem prepend_zero (pre P : Program) (hp:measurementCount pre=0) (s:State) (m:List Bool) :
 run (pre++P) m s=run P m (run pre [] s) := by
 rw [run_append,hp]
 rfl

theorem append_equal (P Q post : Program) (hm:measurementCount P=measurementCount Q)
 (s:State) (m:List Bool) (he:∀r,run P r s=run Q r s) :
 run (P++post) m s=run (Q++post) m s := by
 rw [run_append,run_append,hm,he]

def cachedMapped2 (cache0 cache1 : Wire) (bits : List MappedBit) (ys cs : List Wire) (cin:Wire) : Program :=
 match bits,ys,cs with
 | b0::b1::b2::bs,y0::y1::y2::ys,k0::k1::ks =>
   [.CX cache0 k0]++cachedMapped cache1 (b1::b2::bs) (y1::y2::ys) (k1::ks) k0++
    mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin
 | _,_,_ => cachedMapped cache0 bits ys cs cin

theorem cachedMapped2_eq (cache0 cache1 : Wire) (b0 b1 b2:MappedBit) (bs:List MappedBit)
 (y0 y1 y2:Wire) (ys:List Wire) (k0 k1:Wire) (ks:List Wire) (cin:Wire)
 (hn:[y1,k0,k1].Nodup) (ha:∀q∈b1.wire,q∉[y1,k0,k1]) (s:State) (m:List Bool)
 (ready:(run [.CX cache0 k0] [] s).basis cache1=
   carryBit (b1.value (run [.CX cache0 k0] [] s).basis)
    ((run [.CX cache0 k0] [] s).basis y1) ((run [.CX cache0 k0] [] s).basis k0)) :
 run (cachedMapped2 cache0 cache1 (b0::b1::b2::bs) (y0::y1::y2::ys) (k0::k1::ks) cin) m s=
 run (cachedMapped cache0 (b0::b1::b2::bs) (y0::y1::y2::ys) (k0::k1::ks) cin) m s := by
 have hl : cachedMapped2 cache0 cache1 (b0::b1::b2::bs) (y0::y1::y2::ys) (k0::k1::ks) cin=
   [.CX cache0 k0]++(cachedMapped cache1 (b1::b2::bs) (y1::y2::ys) (k1::ks) k0++
    (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by
  simp only [cachedMapped2,List.append_assoc]
 have hr : cachedMapped cache0 (b0::b1::b2::bs) (y0::y1::y2::ys) (k0::k1::ks) cin=
   [.CX cache0 k0]++(mappedAdd (b1::b2::bs) (y1::y2::ys) (k1::ks) k0++
    (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by
  simp only [cachedMapped,List.append_assoc]
 rw [hl,hr]
 rw [prepend_zero [.CX cache0 k0] _ (by rfl),prepend_zero [.CX cache0 k0] _ (by rfl)]
 apply append_equal _ _ _ (cachedMapped_counts cache1 b1 b2 bs y1 y2 ys k1 ks k0).2
 intro r
 exact cachedMapped_eq cache1 b1 b2 bs y1 y2 ys k1 ks k0 hn ha _ r ready

def cachedMixed2 (cache0 cache1:Wire) (expected:Bool) (bits:List MappedBit)
 (ys:List Wire) (flags:List Bool) (cs:List Wire) (cin:Wire) : Program :=
 match bits,ys,flags,cs with
 | b0::b1::b2::bs,y0::y1::y2::ys,_::false::false::fs,k0::k1::ks =>
   [.CX cache0 k0]++cachedMixed cache1 expected (b1::b2::bs) (y1::y2::ys) (false::false::fs) (k1::ks) k0++
    mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin
 | _,_,_,_ => cachedMixed cache0 expected bits ys flags cs cin

theorem cachedMixed2_eq (cache0 cache1:Wire) (expected d:Bool) (b0 b1 b2:MappedBit) (bs:List MappedBit)
 (y0 y1 y2:Wire) (ys:List Wire) (fs:List Bool) (k0 k1:Wire) (ks:List Wire) (cin:Wire)
 (hn:[y1,k0,k1].Nodup) (ha:∀q∈b1.wire,q∉[y1,k0,k1]) (s:State) (m:List Bool)
 (ready:(run [.CX cache0 k0] [] s).basis cache1=
   carryBit (b1.value (run [.CX cache0 k0] [] s).basis)
    ((run [.CX cache0 k0] [] s).basis y1) ((run [.CX cache0 k0] [] s).basis k0)) :
 run (cachedMixed2 cache0 cache1 expected (b0::b1::b2::bs) (y0::y1::y2::ys) (d::false::false::fs) (k0::k1::ks) cin) m s=
 run (cachedMixed cache0 expected (b0::b1::b2::bs) (y0::y1::y2::ys) (d::false::false::fs) (k0::k1::ks) cin) m s := by
 have hl : cachedMixed2 cache0 cache1 expected (b0::b1::b2::bs) (y0::y1::y2::ys) (d::false::false::fs) (k0::k1::ks) cin=
   [.CX cache0 k0]++(cachedMixed cache1 expected (b1::b2::bs) (y1::y2::ys) (false::false::fs) (k1::ks) k0++
    (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by
  simp only [cachedMixed2,List.append_assoc]
 have hr : cachedMixed cache0 expected (b0::b1::b2::bs) (y0::y1::y2::ys) (d::false::false::fs) (k0::k1::ks) cin=
   [.CX cache0 k0]++(MixedLiteralAdderDevelop.program expected (b1::b2::bs) (y1::y2::ys) (false::false::fs) (k1::ks) k0++
    (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by
  simp only [cachedMixed,List.append_assoc]
 rw [hl,hr]
 rw [prepend_zero [.CX cache0 k0] _ (by rfl),prepend_zero [.CX cache0 k0] _ (by rfl)]
 apply append_equal _ _ _ (cachedMixed_counts cache1 expected false b1 b2 bs y1 y2 ys fs k1 ks k0).2
 intro r
 exact cachedMixed_eq cache1 expected false b1 b2 bs y1 y2 ys fs k1 ks k0 hn ha _ r ready

theorem cachedMapped2_counts (cache0 cache1:Wire) (b0 b1 b2:MappedBit) (bs:List MappedBit)
 (y0 y1 y2:Wire) (ys:List Wire) (k0 k1:Wire) (ks:List Wire) (cin:Wire) :
 toffoliCount (cachedMapped2 cache0 cache1 (b0::b1::b2::bs) (y0::y1::y2::ys) (k0::k1::ks) cin)+1=
  toffoliCount (cachedMapped cache0 (b0::b1::b2::bs) (y0::y1::y2::ys) (k0::k1::ks) cin) ∧
 measurementCount (cachedMapped2 cache0 cache1 (b0::b1::b2::bs) (y0::y1::y2::ys) (k0::k1::ks) cin)=
  measurementCount (cachedMapped cache0 (b0::b1::b2::bs) (y0::y1::y2::ys) (k0::k1::ks) cin) := by
 have h:=cachedMapped_counts cache1 b1 b2 bs y1 y2 ys k1 ks k0
 simp only [cachedMapped2,cachedMapped,toffoliCount_append,measurementCount_append] at *
 exact ⟨by omega,by omega⟩

theorem cachedMixed2_counts (cache0 cache1:Wire) (expected d:Bool) (b0 b1 b2:MappedBit) (bs:List MappedBit)
 (y0 y1 y2:Wire) (ys:List Wire) (fs:List Bool) (k0 k1:Wire) (ks:List Wire) (cin:Wire) :
 toffoliCount (cachedMixed2 cache0 cache1 expected (b0::b1::b2::bs) (y0::y1::y2::ys) (d::false::false::fs) (k0::k1::ks) cin)+1=
  toffoliCount (cachedMixed cache0 expected (b0::b1::b2::bs) (y0::y1::y2::ys) (d::false::false::fs) (k0::k1::ks) cin) ∧
 measurementCount (cachedMixed2 cache0 cache1 expected (b0::b1::b2::bs) (y0::y1::y2::ys) (d::false::false::fs) (k0::k1::ks) cin)=
  measurementCount (cachedMixed cache0 expected (b0::b1::b2::bs) (y0::y1::y2::ys) (d::false::false::fs) (k0::k1::ks) cin) := by
 have h:=cachedMixed_counts cache1 expected false b1 b2 bs y1 y2 ys fs k1 ks k0
 simp only [cachedMixed2,cachedMixed,toffoliCount_append,measurementCount_append] at *
 exact ⟨by omega,by omega⟩

#print axioms cachedMapped2_eq
#print axioms cachedMixed2_eq
#print axioms cachedMapped2_counts
#print axioms cachedMixed2_counts
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SecondCarryLoan

def carryLow2 (u d : Nat) : Bool :=
 carryBit (u/2%2==1) (d/2%2==1) ((u%2==1)&&(d%2==1))

theorem known_second_loan (v u : Nat) (hv:v/2%2=0) :
 ((v+u)/2%2==1)=((u/2%2==1) ^^ (u%2==1) ^^ ((u%2==1)&&((v+u)%2==1))) := by
 have hu0 : u%2=0 ∨ u%2=1 := by omega
 have hu1 : u/2%2=0 ∨ u/2%2=1 := by omega
 have he0 : (v+u)%2=0 ∨ (v+u)%2=1 := by omega
 have he1 : (v+u)/2%2=0 ∨ (v+u)/2%2=1 := by omega
 rcases hu0 with hu0|hu0 <;> rcases hu1 with hu1|hu1 <;>
  rcases he0 with he0|he0 <;> rcases he1 with he1|he1 <;>
  simp only [hu0,hu1,he0,he1] <;> first | rfl | omega

theorem add_second (u d : Nat) :
 ((u+d)/2%2==1)=((u/2%2==1) ^^ (d/2%2==1) ^^ ((u%2==1)&&(d%2==1))) := by
 have hu0 : u%2=0 ∨ u%2=1 := by omega
 have hu1 : u/2%2=0 ∨ u/2%2=1 := by omega
 have hd0 : d%2=0 ∨ d%2=1 := by omega
 have hd1 : d/2%2=0 ∨ d/2%2=1 := by omega
 have hs : (u+d)/2%2=0 ∨ (u+d)/2%2=1 := by omega
 rcases hu0 with hu0|hu0 <;> rcases hu1 with hu1|hu1 <;>
  rcases hd0 with hd0|hd0 <;> rcases hd1 with hd1|hd1 <;> rcases hs with hs|hs <;>
  simp only [hu0,hu1,hd0,hd1,hs] <;> first | rfl | omega

theorem sub_second_bool (a b c : Bool) :
 carryBit a (!(a ^^ b ^^ c)) c=carryBit a b c := by
 cases a <;> cases b <;> cases c <;> decide

theorem low2_mul (u d k : Nat) (hk:k%4=1) :
 (u+k*d)/2%2=(u+d)/2%2 := by
 have h : (u+k*d)%4=(u+d)%4 := by simp [Nat.add_mod,Nat.mul_mod,hk]
 omega

theorem sub_second (u d k : Nat) (hk:k%4=1) :
 carryBit (u/2%2==1) (!((u+k*d)/2%2==1)) ((u%2==1)&&(d%2==1))=carryLow2 u d := by
 rw [low2_mul u d k hk,add_second]
 exact sub_second_bool _ _ _

#print axioms known_second_loan
#print axioms add_second
#print axioms sub_second
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SecondCarryLoan
open CarryWindowCache

theorem split_three {α : Type} (xs : List α) (h : 3≤xs.length) :
 ∃a b c rest,xs=a::b::c::rest := by
 obtain ⟨a,b,rest,rfl⟩:=split_two xs (by omega)
 obtain ⟨c,rest,rfl⟩:=split_one rest (by simpa using h)
 exact ⟨a,b,c,rest,rfl⟩

theorem second_geometry (a0 a1 a2 b0 b1 b2 k0 k1 cin : Wire) (xs ys ks : List Wire)
 (nd:(cin::(a0::a1::a2::xs)++(b0::b1::b2::ys)++(k0::k1::ks)).Nodup) :
 [b1,k0,k1].Nodup ∧ a1∉[b1,k0,k1] ∧ a1≠k0 ∧ b1≠k0 := by
 have ht : (k0::(a1::a2::xs)++(b1::b2::ys)++(k1::ks)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h:=List.nodup_iff_count_le_one.mp nd q
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega
 have h:=first_geometry a1 a2 xs b1 b2 ys k1 ks k0 ht
 refine ⟨h.1,h.2.1,?_,?_⟩
 · intro he;apply h.2.1;simp [he]
 · intro he;have bad:=List.nodup_cons.mp h.1;exact bad.1 (by simp [he])

theorem prefix_ready (cache0 cache1 a1 b1 k0 : Wire)
 (_ha:a1≠k0) (_hb:b1≠k0) (hc:cache1≠k0) (s:State) (hi:s.basis k0=false)
 (hk:s.basis cache1=carryBit (s.basis a1) (s.basis b1) (s.basis cache0)) :
 (run [.CX cache0 k0] [] s).basis cache1=
 carryBit (s.basis a1) (s.basis b1) ((run [.CX cache0 k0] [] s).basis k0) := by
 simpa [run,writeBit,Function.update_apply,hc,hi] using hk

theorem mapped2_read_eq (cache0 cache1 a0 a1 a2 b0 b1 b2 k0 k1 cin : Wire)
 (xs ys ks : List Wire)
 (nd:(cin::(a0::a1::a2::xs)++(b0::b1::b2::ys)++(k0::k1::ks)).Nodup)
 (away:cache1≠k0) (s:State) (m:List Bool) (hi:s.basis k0=false)
 (hk:s.basis cache1=carryBit (s.basis a1) (s.basis b1) (s.basis cache0)) :
 run (cachedMapped2 cache0 cache1 (mappedRead (a0::a1::a2::xs) false) (b0::b1::b2::ys) (k0::k1::ks) cin) m s=
 run (cachedMapped cache0 (mappedRead (a0::a1::a2::xs) false) (b0::b1::b2::ys) (k0::k1::ks) cin) m s := by
 obtain ⟨hn,ha,hak,hbk⟩:=second_geometry a0 a1 a2 b0 b1 b2 k0 k1 cin xs ys ks nd
 apply cachedMapped2_eq cache0 cache1 ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩
  (mappedRead xs false) b0 b1 b2 ys k0 k1 ks cin hn (by simpa using ha) s m
 have h:=prefix_ready cache0 cache1 a1 b1 k0 hak hbk away s hi hk
 simpa [MappedBit.value,run,writeBit,Function.update_apply,hak,hbk] using h

theorem mixed2_read_eq (cache0 cache1 a0 a1 a2 b0 b1 b2 k0 k1 cin : Wire)
 (expected d:Bool) (xs ys ks:List Wire) (fs:List Bool)
 (nd:(cin::(a0::a1::a2::xs)++(b0::b1::b2::ys)++(k0::k1::ks)).Nodup)
 (away:cache1≠k0) (s:State) (m:List Bool) (hi:s.basis k0=false)
 (hk:s.basis cache1=carryBit (s.basis a1) (s.basis b1) (s.basis cache0)) :
 run (cachedMixed2 cache0 cache1 expected (mappedRead (a0::a1::a2::xs) false) (b0::b1::b2::ys)
  (d::false::false::fs) (k0::k1::ks) cin) m s=
 run (cachedMixed cache0 expected (mappedRead (a0::a1::a2::xs) false) (b0::b1::b2::ys)
  (d::false::false::fs) (k0::k1::ks) cin) m s := by
 obtain ⟨hn,ha,hak,hbk⟩:=second_geometry a0 a1 a2 b0 b1 b2 k0 k1 cin xs ys ks nd
 apply cachedMixed2_eq cache0 cache1 expected d ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩
  (mappedRead xs false) b0 b1 b2 ys fs k0 k1 ks cin hn (by simpa using ha) s m
 have h:=prefix_ready cache0 cache1 a1 b1 k0 hak hbk away s hi hk
 simpa [MappedBit.value,run,writeBit,Function.update_apply,hak,hbk] using h

def cachedSub2 (cache0 cache1:Wire) (expected:Bool) (bits:List MappedBit) (flags:List Bool)
 (ys cs:List Wire) (cin:Wire) : Program :=
 notRegister ys++cachedMixed2 cache0 cache1 expected bits ys flags cs cin++notRegister ys

theorem sub2_read_eq (cache0 cache1 a0 a1 a2 b0 b1 b2 k0 k1 cin : Wire)
 (expected d:Bool) (xs ys ks:List Wire) (fs:List Bool)
 (nd:(cin::(a0::a1::a2::xs)++(b0::b1::b2::ys)++(k0::k1::ks)).Nodup)
 (away:cache1∉b0::b1::b2::ys) (awayk:cache1≠k0) (s:State) (m:List Bool) (hi:s.basis k0=false)
 (hk:s.basis cache1=carryBit (s.basis a1) (!s.basis b1) (s.basis cache0))
 (away0:cache0∉b0::b1::b2::ys) :
 run (cachedSub2 cache0 cache1 expected (mappedRead (a0::a1::a2::xs) false) (d::false::false::fs)
  (b0::b1::b2::ys) (k0::k1::ks) cin) m s=
 run (cachedSub cache0 expected (mappedRead (a0::a1::a2::xs) false) (d::false::false::fs)
  (b0::b1::b2::ys) (k0::k1::ks) cin) m s := by
 have geo:=MixedLiteralAdderDevelop.read_geometry (a0::a1::a2::xs) (b0::b1::b2::ys) (k0::k1::ks) cin nd
 have hnd : (b0::b1::b2::ys).Nodup := (List.nodup_append.mp (List.nodup_cons.mp geo.1).2).1
 have hay : a1∉b0::b1::b2::ys := by
  intro h;exact geo.2 a1 (by simp) (List.mem_cons_of_mem _ (List.mem_append_left _ h))
 have hcy : k0∉b0::b1::b2::ys := by
  intro bad
  have hn:=List.nodup_append.mp (List.nodup_cons.mp geo.1).2
  exact hn.2.2 k0 bad k0 (by simp) rfl
 have h : ∀r,run (cachedMixed2 cache0 cache1 expected (mappedRead (a0::a1::a2::xs) false)
    (b0::b1::b2::ys) (d::false::false::fs) (k0::k1::ks) cin) r
    (run (notRegister (b0::b1::b2::ys)) [] s)=
   run (cachedMixed cache0 expected (mappedRead (a0::a1::a2::xs) false)
    (b0::b1::b2::ys) (d::false::false::fs) (k0::k1::ks) cin) r
    (run (notRegister (b0::b1::b2::ys)) [] s) := by
  intro r
  apply mixed2_read_eq cache0 cache1 a0 a1 a2 b0 b1 b2 k0 k1 cin expected d xs ys ks fs nd awayk _ r
  · rw [notRegister_correct _ hnd];simpa [hcy] using hi
  · rw [notRegister_correct _ hnd];simpa [hay,away,away0] using hk
 have hm:measurementCount (cachedMixed2 cache0 cache1 expected
   (mappedRead (a0::a1::a2::xs) false) (b0::b1::b2::ys) (d::false::false::fs) (k0::k1::ks) cin)=
   measurementCount (cachedMixed cache0 expected (mappedRead (a0::a1::a2::xs) false)
    (b0::b1::b2::ys) (d::false::false::fs) (k0::k1::ks) cin) :=
  (cachedMixed2_counts cache0 cache1 expected d ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩
   (mappedRead xs false) b0 b1 b2 ys fs k0 k1 ks cin).2
 simp only [cachedSub2,cachedSub,List.append_assoc]
 rw [prepend_zero (notRegister _) _ ((notRegister_counts _).2),
  prepend_zero (notRegister _) _ ((notRegister_counts _).2)]
 exact append_equal _ _ _ hm _ m h

#print axioms mapped2_read_eq
#print axioms mixed2_read_eq
#print axioms sub2_read_eq
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SecondCarryLoan
open CarryWindowCache

def bit1 (xs:List Wire) : Wire := (xs.drop 1).headD 0

theorem mapped2_read_general (cache0 cache1:Wire) (x y cs:List Wire) (cin:Wire)
 (nd:(cin::x++y++cs).Nodup) (hx:3≤x.length) (hy:3≤y.length) (hc:2≤cs.length)
 (away:cache1∉cs) (s:State) (m:List Bool) (hi:s.basis (cs.headD 0)=false)
 (hk:s.basis cache1=carryBit (s.basis (bit1 x)) (s.basis (bit1 y)) (s.basis cache0)) :
 run (cachedMapped2 cache0 cache1 (mappedRead x false) y cs cin) m s=
 run (cachedMapped cache0 (mappedRead x false) y cs cin) m s := by
 obtain ⟨a0,a1,a2,xs,rfl⟩:=split_three x hx
 obtain ⟨b0,b1,b2,ys,rfl⟩:=split_three y hy
 obtain ⟨k0,k1,ks,rfl⟩:=split_two cs hc
 apply mapped2_read_eq cache0 cache1 a0 a1 a2 b0 b1 b2 k0 k1 cin xs ys ks nd
  (by intro he;apply away;simp [he]) s m (by simpa using hi)
 simpa [bit1] using hk

theorem sub2_read_general (cache0 cache1:Wire) (expected:Bool) (x y cs:List Wire)
 (flags:List Bool) (cin:Wire) (nd:(cin::x++y++cs).Nodup)
 (hx:3≤x.length) (hy:3≤y.length) (hc:2≤cs.length) (hf:3≤flags.length)
 (hf1:flags.getD 1 false=false) (hf2:flags.getD 2 false=false)
 (away:cache1∉y) (awayk:cache1∉cs) (away0:cache0∉y)
 (s:State) (m:List Bool) (hi:s.basis (cs.headD 0)=false)
 (hk:s.basis cache1=carryBit (s.basis (bit1 x)) (!s.basis (bit1 y)) (s.basis cache0)) :
 run (cachedSub2 cache0 cache1 expected (mappedRead x false) flags y cs cin) m s=
 run (cachedSub cache0 expected (mappedRead x false) flags y cs cin) m s := by
 obtain ⟨a0,a1,a2,xs,rfl⟩:=split_three x hx
 obtain ⟨b0,b1,b2,ys,rfl⟩:=split_three y hy
 obtain ⟨k0,k1,ks,rfl⟩:=split_two cs hc
 obtain ⟨f0,f1,f2,fs,rfl⟩:=split_three flags hf
 have h1:f1=false:=by simpa using hf1
 have h2:f2=false:=by simpa using hf2
 subst f1;subst f2
 apply sub2_read_eq cache0 cache1 a0 a1 a2 b0 b1 b2 k0 k1 cin expected f0 xs ys ks fs
  nd away (by intro he;apply awayk;simp [he]) s m (by simpa using hi) _ away0
 simpa [bit1] using hk

theorem bit1_append (a b:List Wire) (h:2≤a.length) : bit1 (a++b)=bit1 a := by
 obtain ⟨a0,a1,as,rfl⟩:=split_two a h
 simp [bit1]

theorem bit1_take (a:List Wire) (n:Nat) (h:2≤n) : bit1 (a.take n)=bit1 a := by
 cases a with
 | nil => simp [bit1]
 | cons a0 as =>
  cases as with
  | nil => simp [bit1]
  | cons a1 as =>
   obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le h
   subst n
   simp [bit1,Nat.add_comm,List.take_succ_cons]

theorem bit1_parity (r:List Wire) (t:BasisState) (hr:2≤r.length) :
 t (bit1 r)=(regValue r t/2%2==1) := by
 obtain ⟨a,b,rs,rfl⟩:=split_two r hr
 cases ha:t a <;> cases hb:t b <;> simp [bit1,regValue,ha,hb,Nat.add_div,Nat.mul_div_left,Nat.add_mod,Nat.mul_mod]

def sub33CC (cache0 cache1:Wire) (R Z cs U:List Wire) (cin:Wire) : Program :=
 cachedSub2 cache0 cache1 true (mappedRead (U++Z.take 1) false)
  MixedLiteralAdderDevelop.upper33 (R.take 33) (cs.take 32) cin

def sub43CC (cache0 cache1:Wire) (R Z cs U:List Wire) (cin:Wire) : Program :=
 cachedSub2 cache0 cache1 true (mappedRead (U++Z) false)
  MixedLiteralAdderDevelop.mask43 (R.take 43) (cs.take 42) cin

def addCC (cache0 cache1:Wire) (x y cs:List Wire) (cin:Wire) : Program :=
 cachedMapped2 cache0 cache1 (mappedRead x false) y cs cin

theorem sub33CC_eq {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Geo R S Z cs U cin)
 (cache0 cache1:Wire) (h0:cache0∉R) (h1:cache1∉R) (hc:cache1∉cs)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache1=carryBit (s.basis (bit1 U)) (!s.basis (bit1 R)) (s.basis cache0)) :
 run (sub33CC cache0 cache1 R Z cs U cin) m s=run (sub33C cache0 R Z cs U cin) m s := by
 unfold sub33CC sub33C
 apply sub2_read_general cache0 cache1 true (U++Z.take 1) (R.take 33) (cs.take 32)
  MixedLiteralAdderDevelop.upper33 cin (by simpa using g.ndU 1 0 33 32)
  (by simp [g.u,g.z]) (by simp [g.r]) (by simp [g.c]) (by decide) (by decide) (by decide)
  (fun h=>h1 (List.mem_of_mem_take h)) (fun h=>hc (List.mem_of_mem_take h))
  (fun h=>h0 (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply head_mem;simp [g.c]
 · simpa [bit1_append U _ (by rw[g.u];decide),bit1_take R 33 (by decide)] using hk

theorem sub43CC_eq {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Geo R S Z cs U cin)
 (cache0 cache1:Wire) (h0:cache0∉R) (h1:cache1∉R) (hc:cache1∉cs)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache1=carryBit (s.basis (bit1 U)) (!s.basis (bit1 R)) (s.basis cache0)) :
 run (sub43CC cache0 cache1 R Z cs U cin) m s=run (sub43C cache0 R Z cs U cin) m s := by
 unfold sub43CC sub43C
 apply sub2_read_general cache0 cache1 true (U++Z) (R.take 43) (cs.take 42)
  MixedLiteralAdderDevelop.mask43 cin (by simpa using g.ndUZ 0 43 42)
  (by simp [g.u,g.z]) (by simp [g.r]) (by simp [g.c]) (by decide) (by decide) (by decide)
  (fun h=>h1 (List.mem_of_mem_take h)) (fun h=>hc (List.mem_of_mem_take h))
  (fun h=>h0 (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply head_mem;simp [g.c]
 · simpa [bit1_append U _ (by rw[g.u];decide),bit1_take R 43 (by decide)] using hk

theorem addCC_eq {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Geo R S Z cs U cin)
 (cache0 cache1:Wire) (hc:cache1∉cs) (j n i:Nat) (hn:3≤n) (hc2 : 2 ≤ i)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache1=carryBit (s.basis (bit1 U)) (s.basis (bit1 R)) (s.basis cache0)) :
 run (addCC cache0 cache1 (U++Z.take j) (R.take n) (cs.take i) cin) m s=
 run (addC cache0 (U++Z.take j) (R.take n) (cs.take i) cin) m s := by
 apply mapped2_read_general cache0 cache1 (U++Z.take j) (R.take n) (cs.take i) cin
  (by simpa using g.ndU j 0 n i) (by simp [g.u];omega) (by simp [g.r];omega)
  (by simp [g.c];omega) (fun h=>hc (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply head_mem;simp [g.c];omega
 · simpa [bit1_append U _ (by rw[g.u];decide),bit1_take R n (by omega)] using hk

#print axioms mapped2_read_general
#print axioms sub2_read_general
#print axioms bit1_parity
#print axioms sub33CC_eq
#print axioms sub43CC_eq
#print axioms addCC_eq
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SecondCarryLoan
open CarryWindowCache WinArith

theorem ps_second {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache1:Wire) (hR:cache1∉R) (hS:cache1∉S) (t:BasisState)
 (u V D:Nat) (hu:regValue U t=u) (s:State) (h:PS R S t V D s.basis) :
 s.basis (bit1 U)=(u/2%2==1) ∧ s.basis (bit1 R)=(V/2%2==1) ∧ s.basis cache1=t cache1 := by
 have uv:regValue U s.basis=u:=
  (regValue_congr U _ _ (fun q hq=>h.2.2 q (g.UR q hq) (g.US q hq))).trans hu
 refine ⟨?_,?_,h.2.2 cache1 hR hS⟩
 · simpa only [uv] using bit1_parity U s.basis (by rw[g.u];decide)
 · simpa only [h.1] using bit1_parity R s.basis (by rw[g.r];decide)

theorem ps_cs {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 {t:BasisState} (hct:∀q∈cs,t q=false) (V D:Nat) (s:State) (h:PS R S t V D s.basis) :
 ∀q∈cs,s.basis q=false := by
 intro q hq
 have ht:q∈cs.take cs.length:=by simpa using hq
 exact (h.2.2 q (g.csR cs.length q ht) (g.csS cs.length q ht)).trans (hct q hq)

theorem sub33CC_spec {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache:Wire) (hR:cache∉R) (hS:cache∉S) {t:BasisState}
 (cl:Clean Z cs cin t) (u d:Nat) (hu:regValue U t=u) (hu32:u<2^32) (hd:d≤976)
 (hk:t cache=((u%2==1)&&(d%2==1)))
 (cache1:Wire) (h1R:cache1∉R) (h1S:cache1∉S) (h1C:cache1∉cs)
 (hk1:t cache1=carryLow2 u d) :
 Triple (PS R S t (u+d) 0) (sub33CC cache cache1 R Z cs U cin) (PS R S t d 0) := by
 intro s m h
 obtain ⟨bu,br,b1⟩:=ps_second g cache1 h1R h1S t u (u+d) 0 hu s h
 have b0:s.basis cache=t cache:=h.2.2 cache hR hS
 have ready:s.basis cache1=carryBit (s.basis (bit1 U)) (!s.basis (bit1 R)) (s.basis cache) := by
  rw [bu,br,b1,b0,hk,hk1]
  simpa only [Nat.one_mul] using (sub_second u d 1 (by decide)).symm
 rw [sub33CC_eq g cache cache1 hR h1R h1C s m (ps_cs g cl.c _ _ s h) ready]
 exact sub33C_spec g cache hR hS cl u d hu hu32 hd hk s m h

theorem addCC_ps_loose {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache:Wire) (hR:cache∉R) (hS:cache∉S) {t:BasisState}
 (hcin:t cin=false) (u d V D:Nat) (hu:regValue U t=u)
 (hk:t cache=((u%2==1)&&(d%2==1))) (hV:V%2=d%2)
 (j n i:Nat) (hn: 3≤n) (hc: 2 ≤ i)
 (cache1:Wire) (h1R:cache1∉R) (h1S:cache1∉S) (h1C:cache1∉cs)
 (hk1:t cache1=carryLow2 u d) (hV1:V/2%2=d/2%2) (hcs:∀q∈cs,t q=false)
 (s:State) (m:List Bool) (h:PS R S t V D s.basis) :
 run (addCC cache cache1 (U++Z.take j) (R.take n) (cs.take i) cin) m s=
 run (addInPlace (U++Z.take j) (R.take n) (cs.take i) cin) m s := by
 obtain ⟨bu,br,b1⟩:=ps_second g cache1 h1R h1S t u V D hu s h
 have b0:s.basis cache=t cache:=h.2.2 cache hR hS
 have ready:s.basis cache1=carryBit (s.basis (bit1 U)) (s.basis (bit1 R)) (s.basis cache) := by
  rw [bu,br,b1,b0,hk,hk1,hV1]
  rfl
 rw [addCC_eq g cache cache1 h1C j n i hn hc s m (ps_cs g hcs V D s h) ready]
 exact addC_ps_loose g cache hR hS hcin u d V D hu hk hV j n i (by omega) (by omega) s m h

theorem sub43CCK_spec {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin) {t:BasisState}
 (cl:Clean Z cs cin t) (u d:Nat) (hu:regValue U t=u) (hu32:u<2^32) (hd:d≤976)
 (cache:Wire) (hR:cache∉R) (hS:cache∉S) (hZ:cache∉Z)
 (hk:t cache=((u%2==1)&&(d%2==1))) (k:Wire) (hkZ:k∉Z)
 (cache1:Wire) (h1R:cache1∉R) (h1S:cache1∉S) (h1Z:cache1∉Z) (h1C:cache1∉cs)
 (hk1:t cache1=carryLow2 u d) :
 Triple (PS R S (kz t k Z) (u+4294968273*d+2^32*(976*(if t k then 1 else 0))) 0)
  (sub43CC cache cache1 R Z cs U cin) (PS R S (kz t k Z) (4294968273*d) 0) := by
 intro s m h
 obtain ⟨bu,br,b1⟩:=ps_second g cache1 h1R h1S (kz t k Z) u _ 0 ((kz_u g t k).trans hu) s h
 have b0:s.basis cache=t cache:=
  (h.2.2 cache hR hS).trans (kz_out t k Z g.z cache hZ)
 have b11:s.basis cache1=t cache1:=b1.trans (kz_out t k Z g.z cache1 h1Z)
 have hcs:∀q∈cs,kz t k Z q=false:=by
  intro q hq
  have qZ:q∉Z:=fun bad=>g.away cs Z q hq bad (by simp only[List.count_cons,List.count_append,List.count_nil];omega)
  exact (kz_out t k Z g.z q qZ).trans (cl.c q hq)
 have ready:s.basis cache1=carryBit (s.basis (bit1 U)) (!s.basis (bit1 R)) (s.basis cache) := by
  rw [bu,br,b11,b0,hk,hk1]
  have hp:(u+4294968273*d+2^32*(976*(if t k then 1 else 0)))/2%2=(u+4294968273*d)/2%2:=by omega
  rw[hp]
  exact (sub_second u d 4294968273 (by decide)).symm
 rw[sub43CC_eq g cache cache1 hR h1R h1C s m (ps_cs g hcs _ _ s h) ready]
 exact sub43CK_spec g cl u d hu hu32 hd cache hR hS hZ hk k hkZ s m h

#print axioms sub33CC_spec
#print axioms addCC_ps_loose
#print axioms sub43CCK_spec
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.SecondCarryLoan
open CarryWindowCache WinArith
def fwdCC (R S Z cs U : List Wire) (cin k cache cache1 : Wire) : Program :=
  sub33CC cache cache1 R Z cs U cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  (WinArithAux3SmallDevelop.smallF R S cs cin ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (kpat k Z ++ (addCC cache cache1 (U ++ Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin ++ kpat k Z))))))

theorem fwdCC_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (cache : Wire) (hR : cache∉R) (hS : cache∉S) (hZ : cache∉Z)
    (hcache : t cache=((u%2==1) && (d%2==1))) (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (_h35 : u + d < 2^35)
    (cache1 : Wire) (h1R : cache1∉R) (h1S : cache1∉S) (h1Z : cache1∉Z) (h1C : cache1∉cs)
    (hcache1 : t cache1=carryLow2 u d) :
    Triple (PS R S t (u+d) 0) (fwdCC R S Z cs U cin k cache cache1)
      (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) := by
  have s1 := sub33CC_spec g cache hR hS cl u d hu hu32 hd hcache cache1 h1R h1S h1C hcache1
  have s2 := tcopy_in R S 0 t d 0 (by rw [g.r]; omega) g.s (g.ndIn 0) g.SR
  have s3 := WinArithAux3SmallDevelop.smallF_spec g cl d hd
  have s4 := tcopy_out R S 32 t (977*d) d g.rnd (by rw [g.r]; omega) g.s (g.ndOut 32) g.SR
  have s5 := tcopy_in R S 32 t (977*d + 2^32*d) d (by rw [g.r]; omega) g.s (g.ndIn 32) g.SR
  have p1 := kpat_PS g k hkR hkS hkZ t (977*d + 2^32*d) 0
  have cinZ : cin ∉ Z := fun h => g.away [cin] Z cin (by simp) h
    (by simp only [List.count_cons, List.count_append, List.count_nil]; omega)
  have csZ : ∀ q ∈ cs, q ∉ Z := fun q h1 h2 => g.away cs Z q h1 h2
    (by simp only [List.count_cons, List.count_append]; omega)
  have kzc : kz t k Z cin = false := by
    have : cin ∉ zpat Z := fun h => cinZ (zpat_sub Z g.z cin h)
    simp [kz, this, cl.cin]
  have kzs : ∀ q ∈ cs.take 42, kz t k Z q = false := by
    intro q hq
    have hq' := List.mem_of_mem_take hq
    have : q ∉ zpat Z := fun h => csZ q hq' (zpat_sub Z g.z q h)
    simp [kz, this, cl.c q hq']
  have s6old := tstep_add R S (U ++ Z.take 11) (cs.take 42) cin 0 43 (kz t k Z) (977*d + 2^32*d) 0
    (u + 2^32*(976*(if t k then 1 else 0))) g.rnd (by simp [g.r])
    (g.ndU 11 0 43 42) (by simp [g.u, g.z]) (by simp [g.c]) g.SR g.cinR g.cinS (g.csR 42) (g.csS 42) kzc
    kzs (valK g cl u hu k hkZ _ _) (by
      have hv : 977*d + 2^32*d < 2^42 := by omega
      rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt (by omega : 977*d + 2^32*d < 2^43)]
      cases t k <;> simp <;> omega)
  have s6 : Triple (PS R S (kz t k Z) (977*d+2^32*d) 0)
      (addCC cache cache1 (U++Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin)
      (PS R S (kz t k Z) (977*d+2^32*d+2^0*(u+2^32*(976*(if t k then 1 else 0)))) 0) := by
    intro s m hs
    simp only [List.drop_zero]
    rw [addCC_ps_loose g cache hR hS kzc u d (977*d+2^32*d) 0
      ((kz_u g t k).trans hu) ((kz_out t k Z g.z cache hZ).trans hcache)
      (by omega) 11 43 42 (by decide) (by decide)
      cache1 h1R h1S h1C ((kz_out t k Z g.z cache1 h1Z).trans hcache1)
      (by
        have hsum:977*d+2^32*d=4294968273*d:=by norm_num;omega
        rw[hsum]
        simpa only[Nat.zero_add] using low2_mul 0 d 4294968273 (by decide)) (by
        intro q hq
        exact (kz_out t k Z g.z q (csZ q hq)).trans (cl.c q hq)) s m hs]
    exact s6old s m hs
  have p2 := kpat_PS g k hkR hkS hkZ (kz t k Z) (977*d + 2^32*d + 2^0*(u + 2^32*(976*(if t k then 1 else 0)))) 0
  rw [kz_kz t k Z g.z hkZ] at p2
  have a4 : 977*d % 2^32 + 2^32*((((977*d) / 2^32) % 2^10 ^^^ d) + 2^10*(977*d / 2^(32+10))) =
      977*d + 2^32*d := by
    have a : 977*d % 2^32 = 977*d := Nat.mod_eq_of_lt (by omega)
    have b : (977*d / 2^32) % 2^10 = 0 := by rw [Nat.div_eq_of_lt (by omega), Nat.zero_mod]
    have c : 977*d / 2^(32+10) = 0 := Nat.div_eq_of_lt (by norm_num <;> omega)
    rw [a, b, c, Nat.zero_xor]; ring
  have a5 : d ^^^ (((977*d + 2^32*d) / 2^32) % 2^10) = 0 := by
    have a : ((977*d + 2^32*d) / 2^32) % 2^10 = d := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), Nat.zero_add,
        Nat.mod_eq_of_lt (by omega)]
    rw [a, Nat.xor_self]
  have a2 : 0 ^^^ ((d / 2^0) % 2^10) = d := by
    rw [Nat.zero_xor]; norm_num; omega
  unfold fwdCC
  exact seqv s1 (PS_val (by omega)) (seqv s2 (PS_dval a2)
    (seqv s3 (fun _ h => h) (seqv s4 (PS_val a4) (seqv s5 (PS_dval a5)
    (seqv p1 (fun _ h => h) (seqv s6 (fun _ h => h)
    (Triple.conseq (fun s h => h) p2 (PS_val (by cases t k <;> simp <;> omega)))))))))


def invCC (R S Z cs U : List Wire) (cin k cache cache1 : Wire) : Program :=
  kpat k Z ++ (sub43CC cache cache1 R Z cs U cin ++ (kpat k Z ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (WinArithAux3SmallDevelop.smallI R S cs cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  addCC cache cache1 (U ++ Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin))))))

theorem invCC_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (cache : Wire) (hR : cache∉R) (hS : cache∉S) (hZ : cache∉Z)
    (hcache : t cache=((u%2==1) && (d%2==1))) (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (_h35 : u + d < 2^35)
    (cache1 : Wire) (h1R : cache1∉R) (h1S : cache1∉S) (h1Z : cache1∉Z) (h1C : cache1∉cs)
    (hcache1 : t cache1=carryLow2 u d) :
    Triple (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) (invCC R S Z cs U cin k cache cache1)
      (PS R S t (u+d) 0) := by
  have p1 := kpat_PS g k hkR hkS hkZ t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0
  have s1 := sub43CCK_spec g cl u d hu hu32 hd cache hR hS hZ hcache k hkZ cache1 h1R h1S h1Z h1C hcache1
  have p2 := kpat_PS g k hkR hkS hkZ (kz t k Z) (4294968273*d) 0
  rw [kz_kz t k Z g.z hkZ] at p2
  have s2 := tcopy_in R S 32 t (977*d + 2^32*d) 0 (by rw [g.r]; omega) g.s (g.ndIn 32) g.SR
  have s3 := tcopy_out R S 32 t (977*d + 2^32*d) d g.rnd (by rw [g.r]; omega) g.s (g.ndOut 32) g.SR
  have s4 := WinArithAux3SmallDevelop.smallI_spec g cl d hd
  have s5 := tcopy_in R S 0 t d d (by rw [g.r]; omega) g.s (g.ndIn 0) g.SR
  have s6old := tstep_add R S (U ++ Z.take 1) (cs.take 32) cin 0 33 t d 0 u g.rnd (by rw [g.r];omega)
    (g.ndU 1 0 33 32) (by simp [g.u,g.z]) (by simp [g.c]) g.SR g.cinR g.cinS (g.csR 32) (g.csS 32) cl.cin
    (fun q h=>cl.c q (List.mem_of_mem_take h)) (valUZ g cl u hu 1 _ _) (by norm_num at _h35 ⊢; omega)
  have s6 : Triple (PS R S t d 0)
      (addCC cache cache1 (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin)
      (PS R S t (d+2^0*u) 0) := by
    intro s m hs
    simp only [List.drop_zero]
    rw [addCC_ps_loose g cache hR hS cl.cin u d d 0 hu hcache rfl
      1 33 32 (by decide) (by decide) cache1 h1R h1S h1C hcache1 rfl cl.c s m hs]
    exact s6old s m hs
  have a : ((977*d + 2^32*d) / 2^32) % 2^10 = d := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), Nat.zero_add,
      Nat.mod_eq_of_lt (by omega)]
  have a2 : 0 ^^^ (((977*d + 2^32*d) / 2^32) % 2^10) = d := by rw [a, Nat.zero_xor]
  have a3 : (977*d + 2^32*d) % 2^32 + 2^32*((((977*d + 2^32*d) / 2^32) % 2^10 ^^^ d) +
      2^10*((977*d + 2^32*d) / 2^(32+10))) = 977*d := by
    have b : (977*d + 2^32*d) % 2^32 = 977*d := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have c : (977*d + 2^32*d) / 2^(32+10) = 0 := Nat.div_eq_of_lt (by norm_num <;> omega)
    rw [a, b, c, Nat.xor_self]; ring
  have a5 : d ^^^ ((d / 2^0) % 2^10) = 0 := by
    rw [show (d / 2^0) % 2^10 = d by norm_num; omega, Nat.xor_self]
  unfold invCC
  exact seqv p1 (fun _ h => h) (seqv s1 (fun _ h => h) (seqv p2 (PS_val (by ring))
    (seqv s2 (PS_dval a2) (seqv s3 (PS_val a3)
    (seqv s4 (fun _ h => h) (seqv s5 (PS_dval a5)
    (Triple.conseq (fun s h => h) s6 (PS_val (by omega)))))))))

#print axioms fwdCC_spec
#print axioms invCC_spec
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SecondCarryLoan
open CarryWindowCache ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
def wFwdCC (L : CuccaroStreamedSquareWideLayout) (cache cache1 : Wire) : Program :=
 fwdCC (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L) cache cache1
def wInvCC (L : CuccaroStreamedSquareWideLayout) (cache cache1 : Wire) : Program :=
 invCC (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L) cache cache1

set_option maxHeartbeats 1000000 in
theorem wMidCC_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cache : Wire) (cacheE : cache∈eReg L) (cache1 : Wire) (cache1E : cache1∈eReg L)
    (base : BasisState) (hc : L.PairClean base) (O E b1 : Nat) (hb1 : regValue (hiReg L) base = b1)
    (hb1lt : b1 < 2^128) (hO : O < SquareReduction.p)
    (K : Nat) (hK : K ≤ 1) :
    Triple (fun x=> BState L base O E (4294968272*b1) x ∧
      x cache=((b1/2^96%2==1) && ((4294968272*b1/2^128-b1/2^96)%2==1)) ∧
      x cache1=carryLow2 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      (if x (eU L) then 1 else 0)=K) (wFwdCC L cache cache1 ++ (wCoreK L ++ wInvCC L cache cache1))
      (fun x=> BState L base (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 4294968272*2^32*K +
        2^128*((4294968272*b1)%2^128) + (SquareReduction.p-1-O)) % SquareReduction.p) E (4294968272*b1) x ∧
      x cache=((b1/2^96%2==1) && ((4294968272*b1/2^128-b1/2^96)%2==1)) ∧
      x cache1=carryLow2 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      (if x (eU L) then 1 else 0)=K) := by
  intro s m input
  obtain ⟨h,hCache,hCache1,key⟩:=input
  have cr : cache∉mR L := fun hr=>(m_away L hn cache (Or.inl hr)).2 cacheE
  have cS : cache∉mS L := fun hs=>(m_away L hn cache (Or.inr hs)).2 cacheE
  have cZ : cache∉mZ L := by
    intro hz
    have lc:=layoutCount L hn cache
    have ps:=productSplit L cache
    have ec:=eReg_count L cache
    have ce:=List.count_pos_iff.mpr cacheE
    have cz:=List.count_pos_iff.mpr (mZ_pad L cache hz)
    omega
  have co : cache∉L.core.out := (eReg_away L hn cache cacheE).1
  have cr1 : cache1∉mR L := fun hr=>(m_away L hn cache1 (Or.inl hr)).2 cache1E
  have cS1 : cache1∉mS L := fun hs=>(m_away L hn cache1 (Or.inr hs)).2 cache1E
  have cZ1 : cache1∉mZ L := by
    intro hz
    have lc:=layoutCount L hn cache1
    have ps:=productSplit L cache1
    have ec:=eReg_count L cache1
    have ce:=List.count_pos_iff.mpr cache1E
    have cz:=List.count_pos_iff.mpr (mZ_pad L cache1 hz)
    omega
  have cC1 : cache1∉mC L := by
    intro hz
    have lc:=layoutCount L hn cache1
    have ps:=productSplit L cache1
    have ec:=eReg_count L cache1
    have ce:=List.count_pos_iff.mpr cache1E
    have cz:=List.count_pos_iff.mpr (mC_pad L cache1 hz)
    omega
  have co1 : cache1∉L.core.out := (eReg_away L hn cache1 cache1E).1
  obtain ⟨ws1, ws2, ws3⟩ := whi_split b1 hb1lt
  generalize hW : 4294968272*b1 = W at h hCache hCache1 ws1 ws2 ws3 ⊢
  generalize hu : b1/2^96 = u at hCache hCache1 ws1 ws2 ⊢
  generalize hd : W/2^128 - u = d at hCache hCache1 ws2 ⊢
  have hWlt : W < 2^163 := by rw [← hW]; norm_num at hb1lt ⊢; omega
  obtain ⟨hz, hb, hi, padZ, workZ⟩ := zero_regs L hn base hc O E W s.basis h
  have g := mGeo L hw hn
  have hRv := mR_value L hw hn base hc O E W s.basis h
  have Rv : regValue (mR L) s.basis = u + d := by rw [hRv.1, Nat.mod_eq_of_lt (by omega)]; omega
  have Sv : regValue (mS L) s.basis = 0 := (regValue_zero _ _).mpr (fun q hq => padZ q (mS_pad L q hq))
  have P0 : WinArith.PS (mR L) (mS L) s.basis (u+d) 0 s.basis := ⟨Rv, Sv, fun _ _ _ => rfl⟩
  have cl : WinArith.Clean (mZ L) (mC L) L.core.cin s.basis :=
    ⟨hi, fun q hq => padZ q (mZ_pad L q hq), fun q hq => padZ q (mC_pad L q hq)⟩
  have hU : regValue (mU L) s.basis = u := by
    rw [hi96 L hw, regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E W s.basis h q (Or.inl hq)), hb1, hu]
  have hu32 : u < 2^32 := by rw [← hu]; norm_num at hb1lt ⊢; omega
  have eA := eU_away L hw hn
  have heR : eU L ∉ mR L := fun hr => eA.2.1 (mR_work L _ hr)
  have heS : eU L ∉ mS L := fun hs => eA.1 (mS_pad L _ hs)
  have heZ : eU L ∉ mZ L := fun hz => eA.1 (mZ_pad L _ hz)
  have wf := w192_facts L hw hn
  have hkU : s.basis (eU L) = decide (K = 1) := by
    cases e : s.basis (eU L) <;> simp only [e, Bool.false_eq_true, if_false, if_true] at key <;> simp <;> omega
  have T1 : Triple (WinArith.PS (mR L) (mS L) s.basis (u+d) 0) (wFwdCC L cache cache1)
      (WinArith.PS (mR L) (mS L) s.basis (u + 4294968273*d + 2^32*(976*K)) 0) := by
    have := fwdCC_spec g cl u d hU hu32 ws2 cache cr cS cZ hCache (eU L) heR heS heZ (by omega) cache1 cr1 cS1 cZ1 cC1 hCache1
    rw [key] at this; exact this
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hX : (u + 4294968273*d + 4294968272*2^32*K) + 2^128*(W%2^128) < SquareReduction.p := by
    have b := Nat.mod_lt W (show 2^128>0 by positivity)
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at b hu32 ws2 ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hK with hk | hk <;> subst hk <;> omega
  -- frame facts of the start state
  have wnd : L.core.work.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have := lay_pos L hn q; omega
  have keepS (q : Wire) (h1 : q ∉ L.core.out) (h2 : q ∉ eReg L) (h3 : q ∉ accReg L) : s.basis q = base q :=
    h.2.2.2 q h1 h2 h3
  let O' := ((u + 4294968273*d) + 4294968272*2^32*K + 2^128*(W%2^128) + (SquareReduction.p-1-O)) % SquareReduction.p
  let Q2 : BasisState → Prop := fun x => regValue L.core.out x = O' ∧ regValue (mR L) x = u + 4294968273*d + 2^32*(976*K) ∧
    regValue (mS L) x = 0 ∧ ∀ q, q ∉ L.core.out → q ∉ mR L → q ∉ mS L → x q = s.basis q
  have T2 : Triple (WinArith.PS (mR L) (mS L) s.basis (u + 4294968273*d + 2^32*(976*K)) 0) (wCoreK L) Q2 := by
    intro s1 m1 h1
    have keep0 (q : Wire) (a : q ∉ mR L) (b : q ∉ mS L) : s1.basis q = s.basis q := h1.2.2 q a b
    have w0 : s1.basis (w192 L) = false := (keep0 _ wf.2.2.1 wf.2.2.2.1).trans (workZ _ wf.2.1)
    have ek1 : s1.basis (eU L) = decide (K = 1) := (keep0 _ heR heS).trans hkU
    let s1' : State := ⟨s1.phase, writeBit s1.basis (w192 L) (s1.basis (w192 L) ^^ s1.basis (eU L))⟩
    have r1 : ∀ mm, run (kw L) mm s1 = s1' := by intro mm; simp [kw, run, s1']
    have b1' : ∀ q, q ≠ w192 L → s1'.basis q = s1.basis q := by
      intro q hq; simp [s1', writeBit, Function.update_apply, hq]
    have bw : s1'.basis (w192 L) = decide (K = 1) := by simp [s1', writeBit, w0, ek1]
    have keep (q : Wire) (a : q ∉ mR L) (b : q ∉ mS L) (c : q ≠ w192 L) : s1'.basis q = s.basis q :=
      (b1' q c).trans (keep0 q a b)
    have nw_out (q : Wire) (hq : q ∈ L.core.out) : q ≠ w192 L := fun e => wf.2.2.2.2.1 (e ▸ hq)
    have nw_pad (q : Wire) (hq : q ∈ L.foldPad) : q ≠ w192 L := fun e => work_pad L hn _ wf.1 (e ▸ hq)
    have nw_lo (q : Wire) (hq : q ∈ L.core.work.take 128) : q ≠ w192 L := by
      intro e
      have c := List.nodup_iff_count_le_one.mp wnd q
      have sp := congrArg (List.count q) (List.take_append_drop 128 L.core.work)
      have a1 := List.count_pos_iff.mpr hq
      have a2 : 0 < (L.core.work.drop 128).count q := by
        rw [e]; exact List.count_pos_iff.mpr (List.mem_of_mem_drop (w192_tail L hw))
      simp only [List.count_append] at sp; omega
    have nw_R (q : Wire) (hq : q ∈ mR L) : q ≠ w192 L := fun e => wf.2.2.1 (e ▸ hq)
    have outv : regValue L.core.out s1'.basis = O :=
      (regValue_congr _ _ _ (fun q hq => keep q (fun hr => (m_away L hn q (Or.inl hr)).1 hq)
        (fun hs => (m_away L hn q (Or.inr hs)).1 hq) (nw_out q hq))).trans h.1
    have sg (q : Wire) (hq : q ∈ [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
        L.core.modFlag,L.core.sumCarry]) : s1'.basis q = s.basis q :=
      keep q (fun hr => (sing_away L hn q hq).1 (mR_work L q hr)) (fun hs => (sing_away L hn q hq).2.1 (mS_pad L q hs))
        (fun e => (sing_away L hn q hq).1 (e ▸ wf.1))
    have bo (q : Wire) (hq : q = L.core.productHigh ∨ q = L.core.outHigh ∨ q = L.core.workHigh ∨ q = L.core.cin ∨
        q = L.core.modFlag) : s.basis q = base q :=
      bstate_other L hn base O E W s.basis h q (Or.inr (Or.inr (Or.inr (by rcases hq with rfl|rfl|rfl|rfl|rfl <;> simp))))
    have padS (q : Wire) (hq : q ∈ L.foldPad) : s1'.basis q = false := by
      rw [b1' q (nw_pad q hq)]
      by_cases hs : q ∈ mS L
      · exact (regValue_zero _ _).mp h1.2.1 q hs
      · exact (keep0 q (fun hr => work_pad L hn q (mR_work L q hr) hq) hs).trans (padZ q hq)
    have carryZ : ∀q∈(rotWCore L).carry,s1'.basis q=false := by
      intro q hq
      simp only [rotWCore,measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq|rfl|rfl
      · exact padS q hq
      · exact ((sg _ (by simp)).trans (bo _ (Or.inl rfl))).trans hc.productHigh
      · exact ((sg _ (by simp)).trans (bo _ (Or.inr (Or.inr (Or.inl rfl))))).trans hc.workHigh
    have srcv : regValue (rotWCore L).src s1'.basis = (u + 4294968273*d + 4294968272*2^32*K) + 2^128*(W%2^128) := by
      show regValue (rotWork L) s1'.basis = _
      rw [rotWork, regValue_append]
      have l128 : (L.core.work.drop 128).length = 128 := by simp [hw.core.work]
      have hlo : regValue (L.core.work.take 128) s1'.basis = W % 2^128 := by
        rw [regValue_congr _ _ (s.basis) (fun q hq => keep q
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs)) (nw_lo q hq)),
          WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
      have hhi : regValue (L.core.work.drop 128) s1'.basis = u + 4294968273*d + 4294968272*2^32*K := by
        have sp := regValue_append ((L.core.work.drop 128).take 43) ((L.core.work.drop 128).drop 43) s1'.basis
        rw [List.take_append_drop] at sp
        have z : regValue ((L.core.work.drop 128).drop 43) s1'.basis = 2^21 * K := by
          apply tail_value L hw hn s1'.basis K hK bw
          intro q hq hne
          have hq0 := hq
          rw [List.drop_drop] at hq
          have hq' : q ∈ L.core.work.drop (128+43) := hq
          rw [keep q (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq') hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_drop hq') (mS_pad L q hs)) hne]
          apply workZ
          have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
          rw [this] at hq'
          exact List.mem_of_mem_drop hq'
        have rv : regValue ((L.core.work.drop 128).take 43) s1'.basis = u + 4294968273*d + 2^32*(976*K) := by
          show regValue (mR L) s1'.basis = _
          rw [regValue_congr _ _ s1.basis (fun q hq => b1' q (nw_R q hq))]
          exact h1.1
        rw [sp, z, rv]
        have : ((L.core.work.drop 128).take 43).length = 43 := by simp [hw.core.work]
        rw [this]; ring
      rw [hhi, hlo, l128]
    have mk0 : measurementCount (kw L) = 0 := by simp [kw, measurementCount]
    rw [wCoreK, run_append, r1, mk0, List.drop_zero, run_append]
    rw [show wCoreTq L = qprogTq (rotWCore L) SquareReduction.p from rfl]
    have ek := QCore.qprog_correctTq (rotWCore L) 256 SquareReduction.c SquareReduction.p (rotWCore_widths L hw)
      (rotWCore_nodup L hn) (by decide) hp (by norm_num [SquareReduction.c]) _ O hX hO s1'
      (m1.take (measurementCount (qprogTq (rotWCore L) SquareReduction.p))) srcv outv
      (show s1'.basis L.core.outHigh = false from
        (sg L.core.outHigh (by simp)).trans ((bo _ (Or.inr (Or.inl rfl))).trans hc.outHigh))
      (show s1'.basis L.core.modFlag = false from
        (sg L.core.modFlag (by simp)).trans ((bo _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans hc.modFlag)) carryZ
      (show s1'.basis L.core.cin = false from (sg L.core.cin (by simp)).trans hi)
    generalize hr : run (qprogTq (rotWCore L) SquareReduction.p)
      (m1.take (measurementCount (qprogTq (rotWCore L) SquareReduction.p))) s1' = r at ek ⊢
    have rw' : r.basis (w192 L) = decide (K = 1) := (ek.2.2 _ wf.2.2.2.2.1).trans bw
    have re : r.basis (eU L) = decide (K = 1) := by
      rw [ek.2.2 _ eA.2.2, b1' _ (fun e => wf.2.2.2.2.2.1 e.symm), ek1]
    have fin : ∀ mm, run (kw L) mm r = ⟨r.phase, writeBit r.basis (w192 L) false⟩ := by
      intro mm; simp [kw, run, rw', re]
    rw [fin]
    have fb : ∀ q, q ≠ w192 L → (writeBit r.basis (w192 L) false) q = r.basis q := by
      intro q hq; simp [writeBit, Function.update_apply, hq]
    refine ⟨ek.1, ?_, ?_, ?_, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => fb q (nw_out q hq))).trans ek.2.1
    · rw [regValue_congr _ _ r.basis (fun q hq => fb q (nw_R q hq))]
      exact (regValue_congr _ _ _ (fun q hq => (ek.2.2 q (m_away L hn q (Or.inl hq)).1).trans
        (b1' q (nw_R q hq)))).trans h1.1
    · rw [regValue_congr _ _ r.basis (fun q hq => fb q (fun e => wf.2.2.2.1 (e ▸ hq)))]
      exact (regValue_congr _ _ _ (fun q hq => (ek.2.2 q (m_away L hn q (Or.inr hq)).1).trans
        (b1' q (fun e => wf.2.2.2.1 (e ▸ hq))))).trans h1.2.1
    · intro q a b c
      by_cases hq : q = w192 L
      · subst hq; simp [writeBit]; exact workZ _ wf.2.1
      · show writeBit r.basis (w192 L) false q = s.basis q
        rw [fb q hq, ek.2.2 q a, b1' q hq]; exact keep0 q b c
  let Q3 : BasisState → Prop := fun x => regValue L.core.out x = O' ∧ regValue (mR L) x = u + d ∧
    regValue (mS L) x = 0 ∧ ∀ q, q ∉ L.core.out → q ∉ mR L → q ∉ mS L → x q = s.basis q
  have T3 : Triple Q2 (wInvCC L cache cache1) Q3 := by
    intro s2 m2 h2
    have k2 (q : Wire) (a : q ∉ L.core.out) (b : q ∉ mR L) (c : q ∉ mS L) : s2.basis q = s.basis q := h2.2.2.2 q a b c
    have cl2 : WinArith.Clean (mZ L) (mC L) L.core.cin s2.basis := by
      refine ⟨?_, fun q hq => ?_, fun q hq => ?_⟩
      · exact (k2 _ (sing_away L hn _ (by simp)).2.2 (fun hr => (sing_away L hn _ (by simp)).1 (mR_work L _ hr))
          (fun hs => (sing_away L hn _ (by simp)).2.1 (mS_pad L _ hs))).trans hi
      · exact (k2 q (pad_out L hn q (mZ_pad L q hq)) (fun hr => work_pad L hn q (mR_work L q hr) (mZ_pad L q hq))
          (fun hs => g.ZS q hq hs)).trans (padZ q (mZ_pad L q hq))
      · exact (k2 q (pad_out L hn q (mC_pad L q hq)) (fun hr => work_pad L hn q (mR_work L q hr) (mC_pad L q hq))
          (fun hs => (g.csS 42) q (by rwa [List.take_of_length_le (by rw [g.c])]) hs)).trans (padZ q (mC_pad L q hq))
    have hU2 : regValue (mU L) s2.basis = u := by
      rw [regValue_congr (mU L) _ (s.basis) (fun q hq => k2 q
        (fun ho => (other_away L hn q (Or.inl (List.mem_of_mem_drop hq))).1 ho) (g.UR q hq) (g.US q hq)), hU]
    have ke : (if s2.basis (eU L) = true then 1 else 0) = K := by
      rw [k2 _ eA.2.2 heR heS]; exact key
    have P2 : WinArith.PS (mR L) (mS L) s2.basis
        (u + 4294968273*d + 2^32*(976*(if s2.basis (eU L) = true then 1 else 0))) 0 s2.basis :=
      ⟨by rw [ke]; exact h2.2.1, h2.2.2.1, fun _ _ _ => rfl⟩
    have hCache2 : s2.basis cache=((u%2==1) && (d%2==1)) :=
      (k2 cache co cr cS).trans hCache
    have hCache12 : s2.basis cache1=carryLow2 u d :=
      (k2 cache1 co1 cr1 cS1).trans hCache1
    obtain ⟨ph, h3⟩ := invCC_spec g cl2 u d hU2 hu32 ws2 cache cr cS cZ hCache2 (eU L) heR heS heZ (by omega) cache1 cr1 cS1 cZ1 cC1 hCache12 s2 m2 P2
    refine ⟨ph, ?_, h3.1, h3.2.1, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => h3.2.2 q (fun hr => (m_away L hn q (Or.inl hr)).1 hq)
        (fun hs => (m_away L hn q (Or.inr hs)).1 hq))).trans h2.1
    · intro q a b c; exact (h3.2.2 q b c).trans (k2 q a b c)
  obtain ⟨ph, f⟩ := (T1.seq (T2.seq T3)) s m P0
  refine ⟨ph, ⟨f.1, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => f.2.2.2 q (eReg_away L hn q hq).1
      (fun hr => (m_away L hn q (Or.inl hr)).2 hq) (fun hs => (m_away L hn q (Or.inr hs)).2 hq))).trans h.2.1
  · -- the work register is `W` again
    have wv : regValue L.core.work (run (wFwdCC L cache cache1 ++ (wCoreK L ++ wInvCC L cache cache1)) m s).basis = W := by
      rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
      have lo : regValue (L.core.work.take 128) (run (wFwdCC L cache cache1 ++ (wCoreK L ++ wInvCC L cache cache1)) m s).basis = W % 2^128 := by
        rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
          WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
      have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdCC L cache cache1 ++ (wCoreK L ++ wInvCC L cache cache1)) m s).basis = 0 := by
        apply (regValue_zero _ _).mpr
        intro q hq
        rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
        apply workZ
        have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
        rw [this] at hq
        exact List.mem_of_mem_drop hq
      have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdCC L cache cache1 ++ (wCoreK L ++ wInvCC L cache cache1)) m s).basis = u + d :=
        f.2.1
      rw [lo, mr, hi0]
      omega
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) (run (wFwdCC L cache cache1 ++ (wCoreK L ++ wInvCC L cache cache1)) m s).basis
    rw [List.take_append_drop] at sp
    rw [accReg, WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), wv, Nat.mod_eq_of_lt hWlt]
  · intro q h1 h2 h3
    by_cases hr : q ∈ mR L
    · -- bits 163..170 of work are clear again
      have wq : q ∈ L.core.work := mR_work L q hr
      have hd163 : q ∈ L.core.work.drop 163 := by
        have e := L.core.work.take_append_drop 163
        rw [← e] at wq
        rcases List.mem_append.mp wq with a|a
        · exact absurd a h3
        · exact a
      have wv : regValue L.core.work (run (wFwdCC L cache cache1 ++ (wCoreK L ++ wInvCC L cache cache1)) m s).basis = W := by
        rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
        have lo : regValue (L.core.work.take 128) (run (wFwdCC L cache cache1 ++ (wCoreK L ++ wInvCC L cache cache1)) m s).basis = W % 2^128 := by
          rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
            WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
        have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdCC L cache cache1 ++ (wCoreK L ++ wInvCC L cache cache1)) m s).basis = 0 := by
          apply (regValue_zero _ _).mpr
          intro q hq
          rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
          apply workZ
          have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
          rw [this] at hq
          exact List.mem_of_mem_drop hq
        have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdCC L cache cache1 ++ (wCoreK L ++ wInvCC L cache cache1)) m s).basis = u + d :=
          f.2.1
        rw [lo, mr, hi0]
        omega
      have z : regValue (L.core.work.drop 163) (run (wFwdCC L cache cache1 ++ (wCoreK L ++ wInvCC L cache cache1)) m s).basis = 0 := by
        rw [WinArith.drop_div _ _ (by simp [hw.core.work]), wv, Nat.div_eq_of_lt hWlt]
      rw [(regValue_zero _ _).mp z q hd163]
      exact ((regValue_zero _ _).mp hc.work q wq).symm
    by_cases hs : q ∈ mS L
    · rw [(regValue_zero _ _).mp f.2.2.1 q hs]
      exact ((regValue_zero _ _).mp hc.pad q (mS_pad L q hs)).symm
    · exact (f.2.2.2 q h1 hr hs).trans (keepS q h1 h2 h3)



  · exact (f.2.2.2 cache co cr cS).trans hCache
  · exact (f.2.2.2 cache1 co1 cr1 cS1).trans hCache1
  · rw [f.2.2.2 (eU L) eA.2.2 heR heS]
    exact key

#print axioms wMidCC_step
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.SecondCarryLoan
open CarryWindowCache

def prepare (u0 u1 r0 r1 e0 cache host:Wire) : Program :=
 prime u0 r0 cache++(loan u0 u1 e0 host++prime2 u1 r1 cache host)

def finish (u0 u1 r0 r1 e0 cache host:Wire) : Program :=
 clear2 u1 r1 cache host++(clear u0 r0 cache++restore u0 u1 e0 host)

theorem prepare_run (u0 u1 r0 r1 e0 cache host:Wire)
 (nd:[u0,u1,r0,r1,e0,cache,host].Nodup) (s:State) (m:List Bool)
 (hz:s.basis cache=false)
 (hl:s.basis host=(s.basis u1 ^^ s.basis u0 ^^ (s.basis u0&&s.basis e0))) :
 run (prepare u0 u1 r0 r1 e0 cache host) m s=
 ⟨s.phase,writeBit (writeBit s.basis cache (s.basis u0&&!s.basis r0)) host
  (carryBit (s.basis u1) (!s.basis r1) (s.basis u0&&!s.basis r0))⟩ := by
 have geom:=nd
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false] at geom
 have uc:u0≠cache:=by tauto
 have rc:r0≠cache:=by tauto
 have ur:u0≠r0:=by tauto
 let k0:=s.basis u0&&!s.basis r0
 let S1:State:=⟨s.phase,writeBit s.basis cache k0⟩
 let S2:State:=⟨s.phase,writeBit S1.basis host false⟩
 have p:∀r,run (prime u0 r0 cache) r s=S1 := by
  intro r
  rw[prime_run u0 r0 cache ur rc uc s r,hz,Bool.false_xor]
 have l:∀r,run (loan u0 u1 e0 host) r S1=S2 := by
  intro r
  rw[loan_run u0 u1 e0 host (by tauto) (by tauto) (by tauto) S1 r]
  simpa [S1,writeBit,Function.update_apply,uc,show u1≠cache by tauto,
      show e0≠cache by tauto,show host≠cache by tauto] using hl
 have q:∀r,run (prime2 u1 r1 cache host) r S2=
   ⟨s.phase,writeBit S1.basis host (carryBit (s.basis u1) (!s.basis r1) k0)⟩ := by
  intro r
  rw[prime2_run u1 r1 cache host (by tauto) (by tauto) (by tauto)
    (by tauto) (by tauto) (by tauto) S2 r]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw:w=host
  · subst w
    simp [S2,S1,writeBit,Function.update_apply,show u1≠host by tauto,
      show r1≠host by tauto,show cache≠host by tauto,show u1≠cache by tauto,
      show r1≠cache by tauto]
  · simp [S2,writeBit,Function.update_apply,hw]
 rw[prepare,run_append,p,run_append,l,q]

theorem finish_run (u0 u1 r0 r1 e0 cache host:Wire)
 (nd:[u0,u1,r0,r1,e0,cache,host].Nodup) (s:State) (m:List Bool)
 (hk:s.basis cache=(s.basis u0&&!s.basis r0))
 (hk1:s.basis host=carryBit (s.basis u1) (!s.basis r1) (s.basis cache)) :
 run (finish u0 u1 r0 r1 e0 cache host) m s=
 ⟨s.phase,writeBit (writeBit s.basis host
   (s.basis u1 ^^ s.basis u0 ^^ (s.basis u0&&s.basis e0))) cache false⟩ := by
 have geom:=nd
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false] at geom
 let S1:State:=⟨s.phase,writeBit s.basis host false⟩
 let S2:State:=⟨s.phase,writeBit S1.basis cache false⟩
 have p:∀r,run (clear2 u1 r1 cache host) r s=S1 := by
  intro r;rw[clear2_run u1 r1 cache host (by tauto) (by tauto) (by tauto) s r hk1]
 have q:∀r,run (clear u0 r0 cache) r S1=S2 := by
  intro r
  rw[clear_run u0 r0 cache (by tauto) (by tauto) S1 r]
  simpa [S1,writeBit,Function.update_apply,show cache≠host by tauto,
     show u0≠host by tauto,show r0≠host by tauto] using hk
 have z:∀r,run (restore u0 u1 e0 host) r S2=
  ⟨s.phase,writeBit (writeBit s.basis host
   (s.basis u1 ^^ s.basis u0 ^^ (s.basis u0&&s.basis e0))) cache false⟩ := by
  intro r
  rw[restore_run u0 u1 e0 host (by tauto) (by tauto) (by tauto) S2 r]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hh:w=host
  · subst w
    simp [S2,S1,writeBit,Function.update_apply,show u0≠host by tauto,
      show u1≠host by tauto,show e0≠host by tauto,show host≠cache by tauto,
      show u0≠cache by tauto,show u1≠cache by tauto,show e0≠cache by tauto]
  · by_cases hc:w=cache
    · subst w
      simp [S2,S1,writeBit,Function.update_apply,hh]
    · simp [S2,S1,writeBit,Function.update_apply,hh,hc]
 rw[finish,run_append,p,run_append,q,z]

#print axioms prepare_run
#print axioms finish_run
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.SecondCarryLoan
open CarryWindowCache ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

def hostWire (L:CuccaroStreamedSquareWideLayout):Wire:=bit1 (eReg L)

theorem bit1_mem (xs:List Wire) (h:2≤xs.length):bit1 xs∈xs := by
 obtain ⟨a,b,rs,rfl⟩:=split_two xs h
 simp [bit1]

theorem head2_count (xs:List Wire) (h:2≤xs.length) (q:Wire):
 [xs.headD 0,bit1 xs].count q≤xs.count q := by
 obtain ⟨a,b,rs,rfl⟩:=split_two xs h
 simp only[bit1,List.drop_succ_cons,List.drop_zero,List.headD_cons,List.count_cons,List.count_nil]
 omega

theorem geometry7 (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 [(mU L).headD 0,bit1 (mU L),(mR L).headD 0,bit1 (mR L),
   (eReg L).headD 0,cacheWire L,hostWire L].Nodup := by
 have g:=mGeo L hw hn
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have uc:=head2_count (mU L) (by rw[g.u];decide) q
 have rc:=head2_count (mR L) (by rw[g.r];decide) q
 have ec:=head2_count ((eReg L).take 129) (by simp[eReg_length L hw]) q
 have hhead:((eReg L).take 129).headD 0=(eReg L).headD 0:=head_take_pos _ _ (by decide)
 have hbit:bit1 ((eReg L).take 129)=hostWire L:=bit1_take _ _ (by decide)
 rw[hhead,hbit] at ec
 have ed:=congrArg (List.count q) (cache_decomp L hw)
 have ud:(mU L).count q≤(hiReg L).count q:=(List.drop_sublist _ _).count_le q
 have rd:(mR L).count q≤L.core.work.count q:=
  ((List.take_sublist _ _).trans (List.drop_sublist _ _)).count_le q
 have ps:=productSplit L q
 have es:=eReg_count L q
 have lc:=layoutCount L hn q
 simp only[List.count_cons,List.count_append,List.count_nil] at uc rc ec ed ⊢
 omega

theorem host_mem (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):hostWire L∈eReg L :=
 bit1_mem _ (by simp[eReg_length L hw])

theorem host_ne_key (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 hostWire L≠eU L := by
 have shape:=(eShape L hw).1
 have len:(eRlow L).length=128:=by simp[eRlow,hw.core.product]
 have hm:hostWire L∈eRlow L := by
  unfold hostWire
  rw[shape,bit1_append _ _ (by rw[len];decide)]
  exact bit1_mem _ (by rw[len];decide)
 have nd:=eReg_nodup L hn
 rw[shape]at nd
 exact (List.nodup_append.mp nd).2.2 _ hm _ (by simp)

theorem bstate_u (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (base s:BasisState) (O E b1:Nat) (hb1:regValue (hiReg L) base=b1)
 (h:BState L base O E (4294968272*b1) s):regValue (mU L) s=b1/2^96 := by
 rw[hi96 L hw,regValue_congr _ _ _ (fun q hq=>bstate_other L hn base O E _ s h q (Or.inl hq)),hb1]

theorem bstate_heads2 (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (base s:BasisState) (hc:L.PairClean base) (O E b1:Nat) (hb1:regValue (hiReg L) base=b1)
 (hb1lt:b1<2^128) (h:BState L base O E (4294968272*b1) s):
 s (bit1 (mU L))=(b1/2^96/2%2==1) ∧
 s (bit1 (mR L))=((b1/2^96+(4294968272*b1/2^128-b1/2^96))/2%2==1) := by
 have g:=mGeo L hw hn
 obtain ⟨h1,h2,h3⟩:=whi_split b1 hb1lt
 have hr:=mR_value L hw hn base hc O E (4294968272*b1) s h
 have hv:regValue (mR L) s=b1/2^96+(4294968272*b1/2^128-b1/2^96):=by
  rw[hr.1,Nat.mod_eq_of_lt (by omega)]
  omega
 have hu:=bstate_u L hw hn base s O E b1 hb1 h
 constructor
 · rw[bit1_parity (mU L) s (by rw[g.u];decide),hu]
 · rw[bit1_parity (mR L) s (by rw[g.r];decide),hv]

theorem bstate_key (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths)
 (s:BasisState) (E H l K:Nat) (he:regValue (eReg L) s=E)
 (hH:H<2^96) (hl:l<2^32) (hK:K≤1) (hE:E=2^32*H+l+2^128*K):
 (if s (eU L) then 1 else 0)=K := by
 have hv:=eReg_split L hw s
 rw[he,hE]at hv
 have a1:=eLo_lt L hw s
 have a2:=eMid_lt L hw s
 cases e1:s (eU L) <;> cases e2:s (eV L) <;>
  simp only[e1,e2,Bool.false_eq_true,if_false,if_true]at hv ⊢ <;> omega

#print axioms geometry7
#print axioms host_ne_key
#print axioms bstate_heads2
#print axioms bstate_key
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.SecondCarryLoan
open CarryWindowCache ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

def wMidFullCC (L:CuccaroStreamedSquareWideLayout):Program:=
 prepare ((mU L).headD 0) (bit1 (mU L)) ((mR L).headD 0) (bit1 (mR L))
  ((eReg L).headD 0) (cacheWire L) (hostWire L)++
 ((wFwdCC L (cacheWire L) (hostWire L)++(wCoreK L++wInvCC L (cacheWire L) (hostWire L)))++
 finish ((mU L).headD 0) (bit1 (mU L)) ((mR L).headD 0) (bit1 (mR L))
  ((eReg L).headD 0) (cacheWire L) (hostWire L))

theorem wMidFullCC_step (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (base:BasisState) (hc:L.PairClean base) (O E b1:Nat) (hb1:regValue (hiReg L) base=b1)
 (hb1lt:b1<2^128) (hO:O<SquareReduction.p)
 (H l K:Nat) (hH:H<2^96) (hl:l<2^32) (hK:K≤1) (hE:E=2^32*H+l+2^128*K)
 (hLoan:(E/2%2==1)=((b1/2^96/2%2==1) ^^ (b1/2^96%2==1) ^^
   ((b1/2^96%2==1)&&(E%2==1)))) :
 Triple (BState L base O E (4294968272*b1)) (wMidFullCC L)
 (BState L base (((b1/2^96+4294968273*(4294968272*b1/2^128-b1/2^96))+4294968272*2^32*K+
   2^128*((4294968272*b1)%2^128)+(SquareReduction.p-1-O))%SquareReduction.p) E (4294968272*b1)) := by
 intro s m h
 let u0:Wire:=(mU L).headD 0
 let u1:Wire:=bit1 (mU L)
 let r0:Wire:=(mR L).headD 0
 let r1:Wire:=bit1 (mR L)
 let e0:Wire:=(eReg L).headD 0
 let cache:Wire:=cacheWire L
 let host:Wire:=hostWire L
 let u:=b1/2^96
 let d:=4294968272*b1/2^128-u
 let k0:Bool:=(u%2==1)&&(d%2==1)
 let k1:Bool:=carryLow2 u d
 have nd:[u0,u1,r0,r1,e0,cache,host].Nodup:=geometry7 L hw hn
 have geom:=nd
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geom
 have ce:cache∈eReg L:=cache_mem L hw
 have he:host∈eReg L:=host_mem L hw
 have hz:s.basis cache=false:=e_cache_zero L hw s.basis E h.2.1 (by rw[hE];omega)
 have b0:=bstate_heads L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b1s:=bstate_heads2 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have es:s.basis e0=(E%2==1):=by
  dsimp[e0]
  rw[head_parity (eReg L) s.basis (by simp[eReg_length L hw]),h.2.1]
 have hs:s.basis host=(E/2%2==1):=by
  dsimp[host,hostWire]
  rw[bit1_parity (eReg L) s.basis (by simp[eReg_length L hw]),h.2.1]
 have ready:s.basis host=(s.basis u1 ^^ s.basis u0 ^^ (s.basis u0&&s.basis e0)):=by
  rw[hs,b0.1,b1s.1,es]
  exact hLoan
 have carry0:(s.basis u0&&!s.basis r0)=k0:=by
  rw[b0.1,b0.2]
  simpa only[Nat.one_mul] using carry_parity u d 1 (by decide)
 have carry1:carryBit (s.basis u1) (!s.basis r1) k0=k1:=by
  rw[b1s.1,b1s.2]
  simpa only[Nat.one_mul] using sub_second u d 1 (by decide)
 let t:BasisState:=writeBit (writeBit s.basis cache k0) host k1
 let EP:Nat:=regValue (eReg L) t
 have prepared:∀mm,run (prepare u0 u1 r0 r1 e0 cache host) mm s=⟨s.phase,t⟩:=by
  intro mm
  rw[prepare_run u0 u1 r0 r1 e0 cache host nd s mm hz ready,carry0,carry1]
 have hb0:=bstate_write_e L hn cache ce base s.basis O E _ h k0
 have hb2:=bstate_write_e L hn host he base (writeBit s.basis cache k0) O
   (regValue (eReg L) (writeBit s.basis cache k0)) _ hb0 k1
 have inp:BState L base O EP (4294968272*b1) t ∧ t cache=k0 ∧ t host=k1 ∧
   (if t (eU L) then 1 else 0)=K:=by
  refine ⟨hb2,?_,?_,?_⟩
  · simp[t,writeBit,Function.update_apply,show cache≠host by tauto]
  · simp[t,writeBit]
  · have hk:=bstate_key L hw s.basis E H l K h.2.1 hH hl hK hE
    simpa[t,writeBit,Function.update_apply,show eU L≠cache from (cache_ne_k L hw hn).symm,show eU L≠host from (host_ne_key L hw hn).symm] using hk
 let mid:=wFwdCC L cache host++(wCoreK L++wInvCC L cache host)
 let rest:=m.drop (measurementCount (prepare u0 u1 r0 r1 e0 cache host))
 let mmid:=rest.take (measurementCount mid)
 rw[wMidFullCC,run_append,prepared,run_append]
 have hm:=wMidCC_step L hw hn cache ce host he base hc O EP b1 hb1 hb1lt hO K hK
   (⟨s.phase,t⟩:State) mmid inp
 generalize hr:run mid mmid (⟨s.phase,t⟩:State)=r at hm ⊢
 have br0:=bstate_heads L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br1:=bstate_heads2 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have er:∀q∈eReg L,r.basis q=t q:=(regValue_eq_iff _ _ _).mp hm.2.1.2.1
 have rE0:r.basis e0=s.basis e0:=by
  rw[er e0 (head_mem _ (by simp[eReg_length L hw]))]
  simp[t,writeBit,Function.update_apply,show e0≠host by tauto,show e0≠cache by tauto]
 have rU0:r.basis u0=s.basis u0:=br0.1.trans b0.1.symm
 have rU1:r.basis u1=s.basis u1:=br1.1.trans b1s.1.symm
 have rR0:r.basis r0=s.basis r0:=br0.2.trans b0.2.symm
 have rR1:r.basis r1=s.basis r1:=br1.2.trans b1s.2.symm
 have rk:r.basis cache=(r.basis u0&&!r.basis r0):=by
  rw[rU0,rR0,carry0]
  exact hm.2.2.1
 have rk1:r.basis host=carryBit (r.basis u1) (!r.basis r1) (r.basis cache):=by
  rw[rU1,rR1,hm.2.2.1,carry1]
  exact hm.2.2.2.1
 rw[finish_run u0 u1 r0 r1 e0 cache host nd r _ rk rk1]
 have restored:(r.basis u1 ^^ r.basis u0 ^^ (r.basis u0&&r.basis e0))=s.basis host:=by
  rw[rU1,rU0,rE0]
  exact ready.symm
 rw[restored]
 refine ⟨hm.1,?_⟩
 have hf0:=bstate_write_e L hn host he base r.basis _ EP _ hm.2.1 (s.basis host)
 have hf1:=bstate_write_e L hn cache ce base (writeBit r.basis host (s.basis host)) _
   (regValue (eReg L) (writeBit r.basis host (s.basis host))) _ hf0 false
 have ev:regValue (eReg L) (writeBit (writeBit r.basis host (s.basis host)) cache false)=E:=by
  apply Eq.trans _ h.2.1
  apply regValue_congr
  intro q hq
  by_cases qh:q=host
  · subst q
    simp[writeBit,Function.update_apply,show host≠cache by tauto]
  by_cases qc:q=cache
  · subst q
    simp[writeBit,hz]
  · rw[show writeBit (writeBit r.basis host (s.basis host)) cache false q=r.basis q by
       simp[writeBit,Function.update_apply,qh,qc],er q hq]
    simp[t,writeBit,Function.update_apply,qh,qc]
 simpa only[ev] using hf1

#print axioms wMidFullCC_step
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.SecondCarryLoan
open CarryWindowCache ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem add2_patch (cache0 cache1:Wire) (x y cs:List Wire) (cin:Wire)
 (hx:3≤x.length) (hy:3≤y.length) (hc:2≤cs.length):
 Patch cache1 1 (addCC cache0 cache1 x y cs cin) (addC cache0 x y cs cin):=by
 obtain ⟨a0,a1,a2,xs,rfl⟩:=split_three x hx
 obtain ⟨b0,b1,b2,ys,rfl⟩:=split_three y hy
 obtain ⟨k0,k1,ks,rfl⟩:=split_two cs hc
 have p:=add_patch cache1 (a1::a2::xs) (b1::b2::ys) (k1::ks) k0 (by simp) (by simp) (by simp)
 have h:=(Patch.refl cache1 [.CX cache0 k0]).app
  (p.app (Patch.refl cache1 (mappedEraseCarry ⟨some a0,false⟩ b0 cin k0++mappedSum ⟨some a0,false⟩ b0 cin)))
 simpa only[addCC,addC,cachedMapped2,cachedMapped,mappedRead,List.map_cons,
  Nat.zero_add,Nat.add_zero,←MixedLiteralAdderDevelop.read_add_eq,List.append_assoc]using h

theorem sub2_patch (cache0 cache1:Wire) (expected:Bool) (x y cs:List Wire) (flags:List Bool) (cin:Wire)
 (hx:3≤x.length) (hy:3≤y.length) (hc:2≤cs.length) (hf:3≤flags.length)
 (hf1:flags.getD 1 false=false) (hf2:flags.getD 2 false=false):
 Patch cache1 1 (cachedSub2 cache0 cache1 expected (mappedRead x false) flags y cs cin)
  (cachedSub cache0 expected (mappedRead x false) flags y cs cin):=by
 obtain ⟨a0,a1,a2,xs,rfl⟩:=split_three x hx
 obtain ⟨b0,b1,b2,ys,rfl⟩:=split_three y hy
 obtain ⟨k0,k1,ks,rfl⟩:=split_two cs hc
 obtain ⟨f0,f1,f2,fs,rfl⟩:=split_three flags hf
 have h1:f1=false:=by simpa using hf1
 have h2:f2=false:=by simpa using hf2
 subst f1;subst f2
 have inner:=(majority_patch cache1 a1 b1 k0 k1).app (Patch.refl cache1
  (MixedLiteralAdderDevelop.program expected (mappedRead (a2::xs) false) (b2::ys) (false::fs) ks k1++
   mappedEraseCarry ⟨some a1,false⟩ b1 k0 k1++mappedSum ⟨some a1,false⟩ b1 k0))
 have h:=(Patch.refl cache1 [.CX cache0 k0]).app (inner.app (Patch.refl cache1
  (mappedEraseCarry ⟨some a0,false⟩ b0 cin k0++mappedSum ⟨some a0,false⟩ b0 cin)))
 have hh:=(Patch.refl cache1 (notRegister (b0::b1::b2::ys))).app
  (h.app (Patch.refl cache1 (notRegister (b0::b1::b2::ys))))
 simpa only[cachedSub2,cachedSub,cachedMixed2,cachedMixed,MixedLiteralAdderDevelop.program,
  MixedLiteralAdderDevelop.head,mappedRead,List.map_cons,mappedMajority,Bool.false_eq_true,if_false,
  Nat.add_zero,Nat.zero_add,List.append_assoc]using hh

theorem sub33CC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1:Wire):Patch cache1 1 (sub33CC cache0 cache1 R Z cs U cin) (sub33C cache0 R Z cs U cin):=by
 exact sub2_patch cache0 cache1 true (U++Z.take 1) (R.take 33) (cs.take 32)
  MixedLiteralAdderDevelop.upper33 cin (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
  (by decide) (by decide) (by decide)

theorem sub43CC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1:Wire):Patch cache1 1 (sub43CC cache0 cache1 R Z cs U cin) (sub43C cache0 R Z cs U cin):=by
 exact sub2_patch cache0 cache1 true (U++Z) (R.take 43) (cs.take 42)
  MixedLiteralAdderDevelop.mask43 cin (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
  (by decide) (by decide) (by decide)

theorem fwdCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 k:Wire):Patch cache1 2 (fwdCC R S Z cs U cin k cache0 cache1) (fwdCK R S Z cs U cin k cache0):=by
 have a:=add2_patch cache0 cache1 (U++Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
 have kp:=Patch.refl cache1 (WinArith.kpat k Z)
 exact (sub33CC_patch (cin:=cin) g cache0 cache1).app
  ((Patch.refl cache1 (copyRegister none ((R.drop 0).take 10) S)).app
   ((Patch.refl cache1 (WinArithAux3SmallDevelop.smallF R S cs cin)).app
    ((Patch.refl cache1 (copyRegister none S ((R.drop 32).take 10))).app
     ((Patch.refl cache1 (copyRegister none ((R.drop 32).take 10) S)).app (kp.app (a.app kp))))))

theorem invCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 k:Wire):Patch cache1 2 (invCC R S Z cs U cin k cache0 cache1) (invCK R S Z cs U cin k cache0):=by
 have a:=add2_patch cache0 cache1 (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
 have kp:=Patch.refl cache1 (WinArith.kpat k Z)
 exact kp.app ((sub43CC_patch (cin:=cin) g cache0 cache1).app (kp.app
  ((Patch.refl cache1 (copyRegister none ((R.drop 32).take 10) S)).app
   ((Patch.refl cache1 (copyRegister none S ((R.drop 32).take 10))).app
    ((Patch.refl cache1 (WinArithAux3SmallDevelop.smallI R S cs cin)).app
     ((Patch.refl cache1 (copyRegister none ((R.drop 0).take 10) S)).app a))))))

theorem midCC_patch (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 Patch (hostWire L) 4
  (wFwdCC L (cacheWire L) (hostWire L)++(wCoreK L++wInvCC L (cacheWire L) (hostWire L)))
  (wFwdCK L (cacheWire L)++(wCoreK L++wInvCK L (cacheWire L))):=
 (fwdCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).app
  ((Patch.refl _ (wCoreK L)).app
   (invCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)))

theorem midCC_counts (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 toffoliCount (wMidFullCC L)+2=toffoliCount (wMidFullCK L) ∧
 measurementCount (wMidFullCC L)=measurementCount (wMidFullCK L)+2 ∧
 Challenge.gateSlots (wMidFullCC L)=Challenge.gateSlots (wMidFullCK L)+1:=by
 have h:=midCC_patch L hw
 have ht:=h.t;have hm:=h.m;have hs:=h.slots
 simp only[toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]at ht hm hs
 simp only[wMidFullCC,wMidFullCK,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 have prepT (a b c d e f g:Wire):toffoliCount (prepare a b c d e f g)=2:=rfl
 have prepM (a b c d e f g:Wire):measurementCount (prepare a b c d e f g)=1:=rfl
 have prepS (a b c d e f g:Wire):Challenge.gateSlots (prepare a b c d e f g)=15:=rfl
 have finT (a b c d e f g:Wire):toffoliCount (finish a b c d e f g)=1:=rfl
 have finM (a b c d e f g:Wire):measurementCount (finish a b c d e f g)=2:=rfl
 have finS (a b c d e f g:Wire):Challenge.gateSlots (finish a b c d e f g)=12:=rfl
 have pT (a b c:Wire):toffoliCount (prime a b c)=1:=rfl
 have pM (a b c:Wire):measurementCount (prime a b c)=0:=rfl
 have pS (a b c:Wire):Challenge.gateSlots (prime a b c)=3:=rfl
 have cT (a b c:Wire):toffoliCount (clear a b c)=0:=rfl
 have cM (a b c:Wire):measurementCount (clear a b c)=1:=rfl
 have cS (a b c:Wire):Challenge.gateSlots (clear a b c)=3:=rfl
 rw[prepT,prepM,prepS,finT,finM,finS,pT,pM,pS,cT,cM,cS]
 exact ⟨by omega,by omega,by omega⟩

#print axioms midCC_patch
#print axioms midCC_counts
end ECDSAAdd.Entrant.SecondCarryLoan

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.SecondCarryLoan
open CarryWindowCache ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout ECDSAAdd.RecordedQuantum

theorem host_not_mem (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 ¬WinArith.Mem (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (hostWire L):=by
 have ce:=host_mem L hw
 have cp:=List.count_pos_iff.mpr (eReg_product L _ ce)
 have lc:=layoutCount L hn (hostWire L)
 intro hm
 rcases hm with hi|hu|hr|hs|hz|hc
 · have cinPos:0<[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
     L.core.modFlag,L.core.sumCarry].count (hostWire L):=List.count_pos_iff.mpr (by simp[hi])
   omega
 · exact (eReg_away L hn _ ce).2.2 (List.mem_of_mem_drop hu)
 · have :=List.count_pos_iff.mpr (mR_work L _ hr);omega
 · have :=List.count_pos_iff.mpr (mS_pad L _ hs);omega
 · have :=List.count_pos_iff.mpr (mZ_pad L _ hz);omega
 · have :=List.count_pos_iff.mpr (mC_pad L _ hc);omega

theorem ends_physical (u0 u1 r0 r1 e0 cache host:Wire)
 (nd:[u0,u1,r0,r1,e0,cache,host].Nodup):
 GatePhysical (prepare u0 u1 r0 r1 e0 cache host) ∧
 GatePhysical (finish u0 u1 r0 r1 e0 cache host):=by
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at nd
 simp[prepare,finish,loan,restore,prime,prime2,majority,clear,clear2,
  GatePhysical,PhysicalInstr,ProperGate]
 tauto

theorem midCC_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 GatePhysical (wMidFullCC L):=by
 have hp:=CarryWindowCache.mid_physical L hw hn
 simp only[wMidFullCK,gatePhysical_append]at hp
 have ge:=geometry7 L hw hn
 have ne:hostWire L≠cacheWire L:=by
  simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at ge
  tauto
 have af:hostWire L∉wires (wFwdCK L (cacheWire L)):=by
  intro h
  rcases Finset.mem_insert.mp ((fwdK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support h)with he|h
  · exact ne he
  rcases WinArith.tFwdK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact host_not_mem L hw hn hm
  · exact host_ne_key L hw hn he
 have ai:hostWire L∉wires (wInvCK L (cacheWire L)):=by
  intro h
  rcases Finset.mem_insert.mp ((invK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support h)with he|h
  · exact ne he
  rcases WinArith.tInvK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact host_not_mem L hw hn hm
  · exact host_ne_key L hw hn he
 have pf:=(fwdCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).phys af hp.2.1.1
 have pi:=(invCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).phys ai hp.2.1.2.2
 have ends:=ends_physical _ _ _ _ _ _ _ ge
 simp only[wMidFullCC,gatePhysical_append]
 exact ⟨ends.1,⟨pf,hp.2.1.2.1,pi⟩,ends.2⟩

theorem armsCC_oldE (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 wires (wFwdCC L (cacheWire L) (hostWire L))⊆oldE L ∧
 wires (wInvCC L (cacheWire L) (hostWire L))⊆oldE L:=by
 have hE:hostWire L∈oldE L:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inr (Or.inl (host_mem L hw)))))
 have f:=(fwdCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).support
 have i:=(invCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).support
 constructor
 · intro q h;rcases Finset.mem_insert.mp (f h)with he|h
   · exact he ▸ hE
   · exact (cached_arm_oldE L hw).1 h
 · intro q h;rcases Finset.mem_insert.mp (i h)with he|h
   · exact he ▸ hE
   · exact (cached_arm_oldE L hw).2 h

theorem ends_support (u0 u1 r0 r1 e0 cache host:Wire):
 wires (prepare u0 u1 r0 r1 e0 cache host)⊆[u0,u1,r0,r1,e0,cache,host].toFinset ∧
 wires (finish u0 u1 r0 r1 e0 cache host)⊆[u0,u1,r0,r1,e0,cache,host].toFinset:=by
 constructor <;> intro q h <;>
  simp[prepare,finish,prime,loan,prime2,majority,clear2,clear,restore,
   ECDSAAdd.wires,Instr.wires,correctionWires]at h ⊢ <;> tauto

theorem endsCC_oldE (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 wires (prepare ((mU L).headD 0) (bit1 (mU L)) ((mR L).headD 0) (bit1 (mR L))
   ((eReg L).headD 0) (cacheWire L) (hostWire L))⊆oldE L ∧
 wires (finish ((mU L).headD 0) (bit1 (mU L)) ((mR L).headD 0) (bit1 (mR L))
   ((eReg L).headD 0) (cacheWire L) (hostWire L))⊆oldE L:=by
 have lens:=mLens L hw
 have u0:(mU L).headD 0∈hiReg L:=List.mem_of_mem_drop (head_mem (mU L) (by rw[lens.u];decide))
 have u1:bit1 (mU L)∈hiReg L:=List.mem_of_mem_drop (bit1_mem (mU L) (by rw[lens.u];decide))
 have r0:(mR L).headD 0∈L.core.work.drop 128:=List.mem_of_mem_take (head_mem (mR L) (by rw[lens.r];decide))
 have r1:bit1 (mR L)∈L.core.work.drop 128:=List.mem_of_mem_take (bit1_mem (mR L) (by rw[lens.r];decide))
 have e0:(eReg L).headD 0∈eReg L:=head_mem _ (by simp[eReg_length L hw])
 have hu0:=oldE_mem L hw _ (Or.inr (Or.inl u0))
 have hu1:=oldE_mem L hw _ (Or.inr (Or.inl u1))
 have hr0:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inl r0)))
 have hr1:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inl r1)))
 have he0:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inr (Or.inl e0))))
 have hc:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inr (Or.inl (cache_mem L hw)))))
 have hh:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inr (Or.inl (host_mem L hw)))))
 have h:([((mU L).headD 0),bit1 (mU L),((mR L).headD 0),bit1 (mR L),
   ((eReg L).headD 0),cacheWire L,hostWire L].toFinset:Finset Wire)⊆oldE L:=by
  intro q h
  simp only[List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
 have caps:=ends_support ((mU L).headD 0) (bit1 (mU L)) ((mR L).headD 0) (bit1 (mR L))
  ((eReg L).headD 0) (cacheWire L) (hostWire L)
 exact ⟨caps.1.trans h,caps.2.trans h⟩

#print axioms midCC_physical
#print axioms armsCC_oldE
#print axioms endsCC_oldE
end ECDSAAdd.Entrant.SecondCarryLoan
