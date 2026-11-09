import ECDSAAdd.Submission.Entrant.MainPart04Base

-- Ported from promoted submission 52bbcfbf-a358-44fa-b327-8c657e7189cd.
-- Existing ParkCarry7 declarations are retained as a reference implementation.


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop

def loan2 (g v u0 u1 u2 e0 e1 host : Wire) : Program :=
 [.measureX host [] [.Z u2,.CZ v g,.CZ v e0,.CZ v u0,.CZ u1 e1,.Z u1]]

theorem loan2_run (g v u0 u1 u2 e0 e1 host : Wire)
 (hg:g≠host) (hv:v≠host) (h0:u0≠host) (h1:u1≠host) (h2:u2≠host)
 (he0:e0≠host) (he1:e1≠host) (s:State) (m:List Bool)
 (hk:s.basis host=(s.basis u2 ^^ (s.basis v && s.basis g) ^^
   (s.basis v && s.basis e0) ^^ (s.basis v && s.basis u0) ^^
   (s.basis u1 && s.basis e1) ^^ s.basis u1)) :
 run (loan2 g v u0 u1 u2 e0 e1 host) m s=⟨s.phase,writeBit s.basis host false⟩ := by
 cases m with
 | nil => simp [loan2,run,measureAndCorrect,correct]
 | cons bit ms =>
  cases bit <;> cases bg:s.basis g <;> cases bv:s.basis v <;>
   cases b0:s.basis u0 <;> cases b1:s.basis u1 <;> cases b2:s.basis u2 <;>
   cases be0:s.basis e0 <;> cases be1:s.basis e1 <;>
   simp [loan2,run,measureAndCorrect,correct,hk,bg,bv,b0,b1,b2,be0,be1,
    writeBit,Function.update_apply,hg,hv,h0,h1,h2,he0,he1]

def restore2 (g v u0 u1 u2 e0 e1 host : Wire) : Program :=
 [.CX e0 g,.CX u0 g,.CCX v g host,.CX u0 g,.CX e0 g,
  .CCX u1 e1 host,.CX u1 host,.CX u2 host]

theorem restore2_run (g v u0 u1 u2 e0 e1 host : Wire)
 (hg:g≠host) (hv:v≠host) (h0:u0≠host) (h1:u1≠host) (h2:u2≠host)
 (he0:e0≠host) (he1:e1≠host) (hvg:v≠g) (h0g:u0≠g) (he0g:e0≠g)
 (h1g:u1≠g) (h2g:u2≠g) (he1g:e1≠g)
 (s:State) (m:List Bool) :
 run (restore2 g v u0 u1 u2 e0 e1 host) m s=
 ⟨s.phase,writeBit s.basis host (s.basis host ^^
  (s.basis u2 ^^ (s.basis v && s.basis g) ^^ (s.basis v && s.basis e0) ^^
   (s.basis v && s.basis u0) ^^ (s.basis u1 && s.basis e1) ^^ s.basis u1))⟩ := by
 change (⟨s.phase,_⟩:State)=⟨s.phase,_⟩
 apply congrArg (State.mk s.phase)
 funext q
 by_cases hq:q=host
 · subst q
   cases bg:s.basis g <;> cases bv:s.basis v <;>
    cases b0:s.basis u0 <;> cases b1:s.basis u1 <;> cases b2:s.basis u2 <;>
    cases be0:s.basis e0 <;> cases be1:s.basis e1 <;>
    simp [restore2,run,writeBit,Function.update_apply,hg,hv,h0,h1,h2,he0,he1,hvg,h0g,he0g,h1g,h2g,he1g,
     Ne.symm hg,Ne.symm hv,Ne.symm h0,Ne.symm h1,Ne.symm h2,Ne.symm he0,Ne.symm he1,
     bg,bv,b0,b1,b2,be0,be1]
 by_cases hqg:q=g
 · subst q
   cases bg:s.basis g <;> cases b0:s.basis u0 <;> cases be0:s.basis e0 <;>
    simp [restore2,run,writeBit,Function.update_apply,hg,hv,h0,h1,h2,he0,he1,hvg,h0g,he0g,h1g,h2g,he1g,Ne.symm hg,bg,b0,be0]
 · simp [restore2,run,writeBit,Function.update_apply,hq,hqg]

theorem loan2_counts (g v u0 u1 u2 e0 e1 host : Wire) :
 toffoliCount (loan2 g v u0 u1 u2 e0 e1 host)=0 ∧
 measurementCount (loan2 g v u0 u1 u2 e0 e1 host)=1 := by exact ⟨rfl,rfl⟩

theorem restore2_counts (g v u0 u1 u2 e0 e1 host : Wire) :
 toffoliCount (restore2 g v u0 u1 u2 e0 e1 host)=2 ∧
 measurementCount (restore2 g v u0 u1 u2 e0 e1 host)=0 := by exact ⟨rfl,rfl⟩

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop

def digit (x i:Nat) : Bool := x / 2^i % 2 == 1
def lowSum (g:Bool) (m u:Nat) : Nat := (if g then m else 0)^2+u

theorem digit_congr16 (a b:Nat) (h:a%16=b%16) (i:Fin 4) :
 digit a i.val=digit b i.val := by
 fin_cases i <;> simp only [digit] <;> apply congrArg (fun n:Nat=>n==1)
 all_goals norm_num at *; omega

theorem digit_mod16 (a:Nat) (i:Fin 4) : digit (a%16) i.val=digit a i.val :=
 digit_congr16 _ _ (Nat.mod_mod _ _) i

theorem third_fin16 : ∀ (g:Bool) (m u:Fin 16),
 digit (lowSum g m.val u.val) 2=
 (digit u.val 2 ^^ (digit m.val 1 && (g ^^ digit (lowSum g m.val u.val) 0 ^^ digit u.val 0)) ^^
  (digit u.val 1 && digit (lowSum g m.val u.val) 1) ^^ digit u.val 1) := by decide +kernel

theorem fourth_fin16 : ∀ (g:Bool) (m u:Fin 16),
 digit (lowSum g m.val u.val) 3=
 (digit u.val 3 ^^ ((digit (lowSum g m.val u.val) 0 ^^ digit u.val 0) && (digit m.val 1 ^^ digit m.val 2)) ^^
  (digit u.val 2 && digit (lowSum g m.val u.val) 2) ^^ digit u.val 2) := by decide +kernel

theorem lowSum_mod16 (g:Bool) (m u:Nat) :
 lowSum g (m%16) (u%16)%16=lowSum g m u%16 := by
 cases g <;> simp [lowSum,Nat.add_mod,Nat.pow_mod]

theorem third_nat (g:Bool) (m u:Nat) :
 digit (lowSum g m u) 2=
 (digit u 2 ^^ (digit m 1 && (g ^^ digit (lowSum g m u) 0 ^^ digit u 0)) ^^
  (digit u 1 && digit (lowSum g m u) 1) ^^ digit u 1) := by
 have h:=third_fin16 g ⟨m%16,by omega⟩ ⟨u%16,by omega⟩
 have de0:=digit_congr16 _ _ (lowSum_mod16 g m u) ⟨0,by decide⟩
 have de1:=digit_congr16 _ _ (lowSum_mod16 g m u) ⟨1,by decide⟩
 have de2:=digit_congr16 _ _ (lowSum_mod16 g m u) ⟨2,by decide⟩
 have dm1:=digit_mod16 m ⟨1,by decide⟩
 have du0:=digit_mod16 u ⟨0,by decide⟩
 have du1:=digit_mod16 u ⟨1,by decide⟩
 have du2:=digit_mod16 u ⟨2,by decide⟩
 simpa only [de0,de1,de2,dm1,du0,du1,du2] using h

theorem fourth_nat (g:Bool) (m u:Nat) :
 digit (lowSum g m u) 3=
 (digit u 3 ^^ ((digit (lowSum g m u) 0 ^^ digit u 0) && (digit m 1 ^^ digit m 2)) ^^
  (digit u 2 && digit (lowSum g m u) 2) ^^ digit u 2) := by
 have h:=fourth_fin16 g ⟨m%16,by omega⟩ ⟨u%16,by omega⟩
 have de0:=digit_congr16 _ _ (lowSum_mod16 g m u) ⟨0,by decide⟩
 have de2:=digit_congr16 _ _ (lowSum_mod16 g m u) ⟨2,by decide⟩
 have de3:=digit_congr16 _ _ (lowSum_mod16 g m u) ⟨3,by decide⟩
 have dm1:=digit_mod16 m ⟨1,by decide⟩
 have dm2:=digit_mod16 m ⟨2,by decide⟩
 have du0:=digit_mod16 u ⟨0,by decide⟩
 have du2:=digit_mod16 u ⟨2,by decide⟩
 have du3:=digit_mod16 u ⟨3,by decide⟩
 simpa only [de0,de2,de3,dm1,dm2,du0,du2,du3] using h

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan

def cachedMapped3 (cache0 cache1 cache2:Wire) (bits:List MappedBit) (ys cs:List Wire) (cin:Wire) : Program :=
 match bits,ys,cs with
 | b0::b1::b2::b3::bs,y0::y1::y2::y3::ys,k0::k1::k2::ks =>
   [.CX cache0 k0]++cachedMapped2 cache1 cache2 (b1::b2::b3::bs) (y1::y2::y3::ys) (k1::k2::ks) k0++
    mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin
 | _,_,_ => cachedMapped2 cache0 cache1 bits ys cs cin

theorem cachedMapped3_eq (cache0 cache1 cache2:Wire) (b0 b1 b2 b3:MappedBit) (bs:List MappedBit)
 (y0 y1 y2 y3:Wire) (ys:List Wire) (k0 k1 k2:Wire) (ks:List Wire) (cin:Wire)
 (hn:[y2,k1,k2].Nodup) (ha:∀q∈b2.wire,q∉[y2,k1,k2]) (s:State) (m:List Bool)
 (ready:(run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s)).basis cache2=
  carryBit (b2.value (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s)).basis)
   ((run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s)).basis y2)
   ((run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s)).basis k1)) :
 run (cachedMapped3 cache0 cache1 cache2 (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (k0::k1::k2::ks) cin) m s=
 run (cachedMapped2 cache0 cache1 (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (k0::k1::k2::ks) cin) m s := by
 have hl : cachedMapped3 cache0 cache1 cache2 (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (k0::k1::k2::ks) cin=
  [.CX cache0 k0]++(cachedMapped2 cache1 cache2 (b1::b2::b3::bs) (y1::y2::y3::ys) (k1::k2::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only[cachedMapped3,List.append_assoc]
 have hr : cachedMapped2 cache0 cache1 (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (k0::k1::k2::ks) cin=
  [.CX cache0 k0]++(cachedMapped cache1 (b1::b2::b3::bs) (y1::y2::y3::ys) (k1::k2::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only[cachedMapped2,List.append_assoc]
 rw[hl,hr,prepend_zero [.CX cache0 k0] _ (by rfl),prepend_zero [.CX cache0 k0] _ (by rfl)]
 apply append_equal _ _ _ (cachedMapped2_counts cache1 cache2 b1 b2 b3 bs y1 y2 y3 ys k1 k2 ks k0).2
 intro r
 exact cachedMapped2_eq cache1 cache2 b1 b2 b3 bs y1 y2 y3 ys k1 k2 ks k0 hn ha _ r ready

theorem cachedMapped3_counts (cache0 cache1 cache2:Wire) (b0 b1 b2 b3:MappedBit) (bs:List MappedBit)
 (y0 y1 y2 y3:Wire) (ys:List Wire) (k0 k1 k2:Wire) (ks:List Wire) (cin:Wire) :
 toffoliCount (cachedMapped3 cache0 cache1 cache2 (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (k0::k1::k2::ks) cin)+1=
  toffoliCount (cachedMapped2 cache0 cache1 (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (k0::k1::k2::ks) cin) ∧
 measurementCount (cachedMapped3 cache0 cache1 cache2 (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (k0::k1::k2::ks) cin)=
  measurementCount (cachedMapped2 cache0 cache1 (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (k0::k1::k2::ks) cin) := by
 have h:=cachedMapped2_counts cache1 cache2 b1 b2 b3 bs y1 y2 y3 ys k1 k2 ks k0
 simp only[cachedMapped3,cachedMapped2,toffoliCount_append,measurementCount_append]at *
 exact ⟨by omega,by omega⟩

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan

def cachedMixed3 (cache0 cache1 cache2:Wire) (expected:Bool) (bits:List MappedBit)
 (ys:List Wire) (flags:List Bool) (cs:List Wire) (cin:Wire) : Program :=
 match bits,ys,flags,cs with
 | b0::b1::b2::b3::bs,y0::y1::y2::y3::ys,_::false::false::false::fs,k0::k1::k2::ks =>
   [.CX cache0 k0]++cachedMixed2 cache1 cache2 expected (b1::b2::b3::bs) (y1::y2::y3::ys) (false::false::false::fs) (k1::k2::ks) k0++
    mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin
 | _,_,_,_ => cachedMixed2 cache0 cache1 expected bits ys flags cs cin

theorem cachedMixed3_eq (cache0 cache1 cache2:Wire) (expected d:Bool) (b0 b1 b2 b3:MappedBit) (bs:List MappedBit)
 (y0 y1 y2 y3:Wire) (ys:List Wire) (fs:List Bool) (k0 k1 k2:Wire) (ks:List Wire) (cin:Wire)
 (hn:[y2,k1,k2].Nodup) (ha:∀q∈b2.wire,q∉[y2,k1,k2]) (s:State) (m:List Bool)
 (ready:(run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s)).basis cache2=
  carryBit (b2.value (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s)).basis)
   ((run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s)).basis y2)
   ((run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s)).basis k1)) :
 run (cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin) m s=
 run (cachedMixed2 cache0 cache1 expected (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin) m s := by
 have hl : cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin=
  [.CX cache0 k0]++(cachedMixed2 cache1 cache2 expected (b1::b2::b3::bs) (y1::y2::y3::ys) (false::false::false::fs) (k1::k2::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only[cachedMixed3,List.append_assoc]
 have hr : cachedMixed2 cache0 cache1 expected (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin=
  [.CX cache0 k0]++(cachedMixed cache1 expected (b1::b2::b3::bs) (y1::y2::y3::ys) (false::false::false::fs) (k1::k2::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only[cachedMixed2,List.append_assoc]
 rw[hl,hr,prepend_zero [.CX cache0 k0] _ (by rfl),prepend_zero [.CX cache0 k0] _ (by rfl)]
 apply append_equal _ _ _ (cachedMixed2_counts cache1 cache2 expected false b1 b2 b3 bs y1 y2 y3 ys fs k1 k2 ks k0).2
 intro r
 exact cachedMixed2_eq cache1 cache2 expected false b1 b2 b3 bs y1 y2 y3 ys fs k1 k2 ks k0 hn ha _ r ready

theorem cachedMixed3_counts (cache0 cache1 cache2:Wire) (expected d:Bool) (b0 b1 b2 b3:MappedBit) (bs:List MappedBit)
 (y0 y1 y2 y3:Wire) (ys:List Wire) (fs:List Bool) (k0 k1 k2:Wire) (ks:List Wire) (cin:Wire) :
 toffoliCount (cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin)+1=
  toffoliCount (cachedMixed2 cache0 cache1 expected (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin) ∧
 measurementCount (cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin)=
  measurementCount (cachedMixed2 cache0 cache1 expected (b0::b1::b2::b3::bs) (y0::y1::y2::y3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin) := by
 have h:=cachedMixed2_counts cache1 cache2 expected false b1 b2 b3 bs y1 y2 y3 ys fs k1 k2 ks k0
 simp only[cachedMixed3,cachedMixed2,toffoliCount_append,measurementCount_append]at *
 exact ⟨by omega,by omega⟩
end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan

def bit2 (xs:List Wire):Wire := (xs.drop 2).headD 0

theorem split_four {α:Type} (xs:List α) (h:4≤xs.length):
 ∃a b c d rest,xs=a::b::c::d::rest := by
 obtain ⟨a,b,c,rest,rfl⟩:=split_three xs (by omega)
 obtain ⟨d,rest,rfl⟩:=split_one rest (by simpa using h)
 exact ⟨a,b,c,d,rest,rfl⟩

theorem third_geometry (a0 a1 a2 a3 b0 b1 b2 b3 k0 k1 k2 cin:Wire) (xs ys ks:List Wire)
 (nd:(cin::(a0::a1::a2::a3::xs)++(b0::b1::b2::b3::ys)++(k0::k1::k2::ks)).Nodup):
 [a2,b2,k0,k1,k2].Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have h:=List.nodup_iff_count_le_one.mp nd q
 simp only[List.count_cons,List.count_append,List.count_nil]at h ⊢
 omega

theorem mapped3_read_eq (cache0 cache1 cache2 a0 a1 a2 a3 b0 b1 b2 b3 k0 k1 k2 cin:Wire)
 (xs ys ks:List Wire)
 (nd:(cin::(a0::a1::a2::a3::xs)++(b0::b1::b2::b3::ys)++(k0::k1::k2::ks)).Nodup)
 (away1:cache1≠k0) (away20:cache2≠k0) (away21:cache2≠k1)
 (s:State) (m:List Bool) (hi:s.basis k1=false)
 (hk:s.basis cache2=carryBit (s.basis a2) (s.basis b2) (s.basis cache1)):
 run (cachedMapped3 cache0 cache1 cache2 (mappedRead (a0::a1::a2::a3::xs) false)
  (b0::b1::b2::b3::ys) (k0::k1::k2::ks) cin) m s=
 run (cachedMapped2 cache0 cache1 (mappedRead (a0::a1::a2::a3::xs) false)
  (b0::b1::b2::b3::ys) (k0::k1::k2::ks) cin) m s := by
 have hg:=third_geometry a0 a1 a2 a3 b0 b1 b2 b3 k0 k1 k2 cin xs ys ks nd
 have hx : a2≠k0 ∧ a2≠k1 ∧ b2≠k0 ∧ b2≠k1 ∧ k1≠k0 := by
  simp only[List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
   not_false_eq_true,not_or,ne_eq,and_true]at hg
  aesop
 have hn:[b2,k1,k2].Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h:=List.nodup_iff_count_le_one.mp hg q
  simp only[List.count_cons,List.count_nil]at h ⊢
  omega
 have ha:a2∉[b2,k1,k2] := by
  intro bad
  have h:=List.nodup_cons.mp hg
  apply h.1
  simp only[List.mem_cons,List.mem_singleton]at bad ⊢
  tauto
 apply cachedMapped3_eq cache0 cache1 cache2 ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩ ⟨some a3,false⟩
  (mappedRead xs false) b0 b1 b2 b3 ys k0 k1 k2 ks cin hn (by simpa using ha) s m
 simpa [MappedBit.value,run,writeBit,Function.update_apply,away1,away20,away21,
  hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2,hi]using hk

theorem mixed3_read_eq (cache0 cache1 cache2 a0 a1 a2 a3 b0 b1 b2 b3 k0 k1 k2 cin:Wire)
 (expected d:Bool) (xs ys ks:List Wire) (fs:List Bool)
 (nd:(cin::(a0::a1::a2::a3::xs)++(b0::b1::b2::b3::ys)++(k0::k1::k2::ks)).Nodup)
 (away1:cache1≠k0) (away20:cache2≠k0) (away21:cache2≠k1)
 (s:State) (m:List Bool) (hi:s.basis k1=false)
 (hk:s.basis cache2=carryBit (s.basis a2) (s.basis b2) (s.basis cache1)):
 run (cachedMixed3 cache0 cache1 cache2 expected (mappedRead (a0::a1::a2::a3::xs) false)
  (b0::b1::b2::b3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin) m s=
 run (cachedMixed2 cache0 cache1 expected (mappedRead (a0::a1::a2::a3::xs) false)
  (b0::b1::b2::b3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin) m s := by
 have hg:=third_geometry a0 a1 a2 a3 b0 b1 b2 b3 k0 k1 k2 cin xs ys ks nd
 have hx : a2≠k0 ∧ a2≠k1 ∧ b2≠k0 ∧ b2≠k1 ∧ k1≠k0 := by
  simp only[List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
   not_false_eq_true,not_or,ne_eq,and_true]at hg
  aesop
 have hn:[b2,k1,k2].Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h:=List.nodup_iff_count_le_one.mp hg q
  simp only[List.count_cons,List.count_nil]at h ⊢
  omega
 have ha:a2∉[b2,k1,k2] := by
  intro bad
  have h:=List.nodup_cons.mp hg
  apply h.1
  simp only[List.mem_cons,List.mem_singleton]at bad ⊢
  tauto
 apply cachedMixed3_eq cache0 cache1 cache2 expected d ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩ ⟨some a3,false⟩
  (mappedRead xs false) b0 b1 b2 b3 ys fs k0 k1 k2 ks cin hn (by simpa using ha) s m
 simpa [MappedBit.value,run,writeBit,Function.update_apply,away1,away20,away21,
  hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2,hi]using hk

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open SecondCarryLoan

def carryLow3 (u d:Nat):Bool := carryBit (digit u 2) (digit d 2) (carryLow2 u d)

theorem carryLow2_mod16 (u d:Nat):carryLow2 (u%16) (d%16)=carryLow2 u d := by
 have h0:u%16%2=u%2:=by omega
 have h1:u%16/2%2=u/2%2:=by omega
 have h2:d%16%2=d%2:=by omega
 have h3:d%16/2%2=d/2%2:=by omega
 simp only[carryLow2,h0,h1,h2,h3]

theorem sub_third_fin16:∀ (u d:Fin 16),
 carryBit (digit u.val 2) (!(digit (u.val+d.val) 2)) (carryLow2 u.val d.val)=carryLow3 u.val d.val := by decide +kernel

theorem sub_third (u d k:Nat) (hk:k%16=1):
 carryBit (digit u 2) (!(digit (u+k*d) 2)) (carryLow2 u d)=carryLow3 u d := by
 have h:=sub_third_fin16 ⟨u%16,by omega⟩ ⟨d%16,by omega⟩
 have hs:(u%16+d%16)%16=(u+k*d)%16:=by simp[Nat.add_mod,Nat.mul_mod,hk]
 have de:=digit_congr16 _ _ hs ⟨2,by decide⟩
 have du:=digit_mod16 u ⟨2,by decide⟩
 have dd:=digit_mod16 d ⟨2,by decide⟩
 simpa only[carryLow3,carryLow2_mod16,de,du,dd]using h

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan

def cachedSub3 (cache0 cache1 cache2:Wire) (expected:Bool) (bits:List MappedBit) (flags:List Bool)
 (ys cs:List Wire) (cin:Wire):Program :=
 notRegister ys++cachedMixed3 cache0 cache1 cache2 expected bits ys flags cs cin++notRegister ys

theorem sub3_read_eq (cache0 cache1 cache2 a0 a1 a2 a3 b0 b1 b2 b3 k0 k1 k2 cin:Wire)
 (expected d:Bool) (xs ys ks:List Wire) (fs:List Bool)
 (nd:(cin::(a0::a1::a2::a3::xs)++(b0::b1::b2::b3::ys)++(k0::k1::k2::ks)).Nodup)
 (away1:cache1∉b0::b1::b2::b3::ys) (away2:cache2∉b0::b1::b2::b3::ys)
 (awayk1:cache1≠k0) (awayk20:cache2≠k0) (awayk21:cache2≠k1)
 (s:State) (m:List Bool) (hi:s.basis k1=false)
 (hk:s.basis cache2=carryBit (s.basis a2) (!s.basis b2) (s.basis cache1)):
 run (cachedSub3 cache0 cache1 cache2 expected (mappedRead (a0::a1::a2::a3::xs) false)
  (d::false::false::false::fs) (b0::b1::b2::b3::ys) (k0::k1::k2::ks) cin) m s=
 run (cachedSub2 cache0 cache1 expected (mappedRead (a0::a1::a2::a3::xs) false)
  (d::false::false::false::fs) (b0::b1::b2::b3::ys) (k0::k1::k2::ks) cin) m s := by
 have geo:=MixedLiteralAdderDevelop.read_geometry (a0::a1::a2::a3::xs) (b0::b1::b2::b3::ys) (k0::k1::k2::ks) cin nd
 have hnd:(b0::b1::b2::b3::ys).Nodup := (List.nodup_append.mp (List.nodup_cons.mp geo.1).2).1
 have hay:a2∉b0::b1::b2::b3::ys := by
  intro h;exact geo.2 a2 (by simp) (List.mem_cons_of_mem _ (List.mem_append_left _ h))
 have hcy:k1∉b0::b1::b2::b3::ys := by
  intro bad
  have hn:=List.nodup_append.mp (List.nodup_cons.mp geo.1).2
  exact hn.2.2 k1 bad k1 (by simp) rfl
 have h:∀r,run (cachedMixed3 cache0 cache1 cache2 expected (mappedRead (a0::a1::a2::a3::xs) false)
   (b0::b1::b2::b3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin) r
   (run (notRegister (b0::b1::b2::b3::ys)) [] s)=
  run (cachedMixed2 cache0 cache1 expected (mappedRead (a0::a1::a2::a3::xs) false)
   (b0::b1::b2::b3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin) r
   (run (notRegister (b0::b1::b2::b3::ys)) [] s) := by
  intro r
  apply mixed3_read_eq cache0 cache1 cache2 a0 a1 a2 a3 b0 b1 b2 b3 k0 k1 k2 cin
   expected d xs ys ks fs nd awayk1 awayk20 awayk21 _ r
  · rw[notRegister_correct _ hnd];simpa[hcy]using hi
  · rw[notRegister_correct _ hnd];simpa[hay,away1,away2]using hk
 have hm:measurementCount (cachedMixed3 cache0 cache1 cache2 expected
   (mappedRead (a0::a1::a2::a3::xs) false) (b0::b1::b2::b3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin)=
  measurementCount (cachedMixed2 cache0 cache1 expected
   (mappedRead (a0::a1::a2::a3::xs) false) (b0::b1::b2::b3::ys) (d::false::false::false::fs) (k0::k1::k2::ks) cin) :=
  (cachedMixed3_counts cache0 cache1 cache2 expected d ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩ ⟨some a3,false⟩
   (mappedRead xs false) b0 b1 b2 b3 ys fs k0 k1 k2 ks cin).2
 simp only[cachedSub3,cachedSub2,List.append_assoc]
 rw[prepend_zero (notRegister _) _ ((notRegister_counts _).2),prepend_zero (notRegister _) _ ((notRegister_counts _).2)]
 exact append_equal _ _ _ hm _ m h

theorem mapped3_read_general (cache0 cache1 cache2:Wire) (x y cs:List Wire) (cin:Wire)
 (nd:(cin::x++y++cs).Nodup) (hx:4≤x.length) (hy:4≤y.length) (hc:3≤cs.length)
 (away1:cache1∉cs) (away2:cache2∉cs) (s:State) (m:List Bool)
 (hi:s.basis (bit1 cs)=false)
 (hk:s.basis cache2=carryBit (s.basis (bit2 x)) (s.basis (bit2 y)) (s.basis cache1)):
 run (cachedMapped3 cache0 cache1 cache2 (mappedRead x false) y cs cin) m s=
 run (cachedMapped2 cache0 cache1 (mappedRead x false) y cs cin) m s := by
 obtain ⟨a0,a1,a2,a3,xs,rfl⟩:=split_four x hx
 obtain ⟨b0,b1,b2,b3,ys,rfl⟩:=split_four y hy
 obtain ⟨k0,k1,k2,ks,rfl⟩:=split_three cs hc
 apply mapped3_read_eq cache0 cache1 cache2 a0 a1 a2 a3 b0 b1 b2 b3 k0 k1 k2 cin xs ys ks nd
  (by intro he;apply away1;simp[he]) (by intro he;apply away2;simp[he])
  (by intro he;apply away2;simp[he]) s m (by simpa[bit1]using hi)
 simpa[bit2]using hk

theorem sub3_read_general (cache0 cache1 cache2:Wire) (expected:Bool) (x y cs:List Wire)
 (flags:List Bool) (cin:Wire) (nd:(cin::x++y++cs).Nodup)
 (hx:4≤x.length) (hy:4≤y.length) (hc:3≤cs.length) (hf:4≤flags.length)
 (hf1:flags.getD 1 false=false) (hf2:flags.getD 2 false=false) (hf3:flags.getD 3 false=false)
 (away1:cache1∉y) (away2:cache2∉y) (awayk1:cache1∉cs) (awayk2:cache2∉cs)
 (s:State) (m:List Bool) (hi:s.basis (bit1 cs)=false)
 (hk:s.basis cache2=carryBit (s.basis (bit2 x)) (!s.basis (bit2 y)) (s.basis cache1)):
 run (cachedSub3 cache0 cache1 cache2 expected (mappedRead x false) flags y cs cin) m s=
 run (cachedSub2 cache0 cache1 expected (mappedRead x false) flags y cs cin) m s := by
 obtain ⟨a0,a1,a2,a3,xs,rfl⟩:=split_four x hx
 obtain ⟨b0,b1,b2,b3,ys,rfl⟩:=split_four y hy
 obtain ⟨k0,k1,k2,ks,rfl⟩:=split_three cs hc
 obtain ⟨f0,f1,f2,f3,fs,rfl⟩:=split_four flags hf
 have h1:f1=false:=by simpa using hf1
 have h2:f2=false:=by simpa using hf2
 have h3:f3=false:=by simpa using hf3
 subst f1;subst f2;subst f3
 apply sub3_read_eq cache0 cache1 cache2 a0 a1 a2 a3 b0 b1 b2 b3 k0 k1 k2 cin expected f0 xs ys ks fs
  nd away1 away2 (by intro he;apply awayk1;simp[he]) (by intro he;apply awayk2;simp[he])
  (by intro he;apply awayk2;simp[he]) s m (by simpa[bit1]using hi)
 simpa[bit2]using hk

theorem bit2_append (a b:List Wire) (h:3≤a.length):bit2 (a++b)=bit2 a := by
 obtain ⟨a0,a1,a2,as,rfl⟩:=split_three a h
 simp[bit2]

theorem bit2_take (a:List Wire) (n:Nat) (h:3≤n):bit2 (a.take n)=bit2 a := by
 cases a with
 | nil => simp[bit2]
 | cons a0 as =>
  cases as with
  | nil => simp[bit2]
  | cons a1 as =>
   cases as with
   | nil => simp[bit2]
   | cons a2 as =>
    obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le h
    subst n
    simp[bit2,Nat.add_comm,List.take_succ_cons]

theorem bit2_parity (r:List Wire) (t:BasisState) (hr:3≤r.length):
 t (bit2 r)=digit (regValue r t) 2 := by
 obtain ⟨a,b,c,rs,rfl⟩:=split_three r hr
 cases ha:t a <;> cases hb:t b <;> cases hc:t c <;>
  simp[bit2,digit,regValue,ha,hb,hc] <;> omega

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan WinArith

def sub33CCC (cache0 cache1 cache2:Wire) (R Z cs U:List Wire) (cin:Wire):Program :=
 cachedSub3 cache0 cache1 cache2 true (mappedRead (U++Z.take 1) false)
  MixedLiteralAdderDevelop.upper33 (R.take 33) (cs.take 32) cin

def sub43CCC (cache0 cache1 cache2:Wire) (R Z cs U:List Wire) (cin:Wire):Program :=
 cachedSub3 cache0 cache1 cache2 true (mappedRead (U++Z) false)
  MixedLiteralAdderDevelop.mask43 (R.take 43) (cs.take 42) cin

def addCCC (cache0 cache1 cache2:Wire) (x y cs:List Wire) (cin:Wire):Program :=
 cachedMapped3 cache0 cache1 cache2 (mappedRead x false) y cs cin

theorem sub33CCC_eq {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache0 cache1 cache2:Wire) (h1R:cache1∉R) (h1C:cache1∉cs) (h2R:cache2∉R) (h2C:cache2∉cs)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache2=carryBit (s.basis (bit2 U)) (!s.basis (bit2 R)) (s.basis cache1)):
 run (sub33CCC cache0 cache1 cache2 R Z cs U cin) m s=
 run (sub33CC cache0 cache1 R Z cs U cin) m s := by
 unfold sub33CCC sub33CC
 apply sub3_read_general cache0 cache1 cache2 true (U++Z.take 1) (R.take 33) (cs.take 32)
  MixedLiteralAdderDevelop.upper33 cin (by simpa using g.ndU 1 0 33 32)
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c]) (by decide) (by decide) (by decide) (by decide)
  (fun h=>h1R (List.mem_of_mem_take h)) (fun h=>h2R (List.mem_of_mem_take h))
  (fun h=>h1C (List.mem_of_mem_take h)) (fun h=>h2C (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply bit1_mem;simp[g.c]
 · simpa[bit2_append U _ (by rw[g.u];decide),bit2_take R 33 (by decide)]using hk

theorem sub43CCC_eq {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache0 cache1 cache2:Wire) (h1R:cache1∉R) (h1C:cache1∉cs) (h2R:cache2∉R) (h2C:cache2∉cs)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache2=carryBit (s.basis (bit2 U)) (!s.basis (bit2 R)) (s.basis cache1)):
 run (sub43CCC cache0 cache1 cache2 R Z cs U cin) m s=
 run (sub43CC cache0 cache1 R Z cs U cin) m s := by
 unfold sub43CCC sub43CC
 apply sub3_read_general cache0 cache1 cache2 true (U++Z) (R.take 43) (cs.take 42)
  MixedLiteralAdderDevelop.mask43 cin (by simpa using g.ndUZ 0 43 42)
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c]) (by decide) (by decide) (by decide) (by decide)
  (fun h=>h1R (List.mem_of_mem_take h)) (fun h=>h2R (List.mem_of_mem_take h))
  (fun h=>h1C (List.mem_of_mem_take h)) (fun h=>h2C (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply bit1_mem;simp[g.c]
 · simpa[bit2_append U _ (by rw[g.u];decide),bit2_take R 43 (by decide)]using hk

theorem addCCC_eq {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache0 cache1 cache2:Wire) (h1C:cache1∉cs) (h2C:cache2∉cs)
 (j n i:Nat) (hn: 4 ≤ n) (hc: 3 ≤ i)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache2=carryBit (s.basis (bit2 U)) (s.basis (bit2 R)) (s.basis cache1)):
 run (addCCC cache0 cache1 cache2 (U++Z.take j) (R.take n) (cs.take i) cin) m s=
 run (addCC cache0 cache1 (U++Z.take j) (R.take n) (cs.take i) cin) m s := by
 apply mapped3_read_general cache0 cache1 cache2 (U++Z.take j) (R.take n) (cs.take i) cin
  (by simpa using g.ndU j 0 n i) (by simp[g.u];omega) (by simp[g.r];omega)
  (by simp[g.c];omega) (fun h=>h1C (List.mem_of_mem_take h)) (fun h=>h2C (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply bit1_mem;simp[g.c];omega
 · simpa[bit2_append U _ (by rw[g.u];decide),bit2_take R n (by omega)]using hk

theorem ps_third {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache2:Wire) (hR:cache2∉R) (hS:cache2∉S) (t:BasisState)
 (u V D:Nat) (hu:regValue U t=u) (s:State) (h:PS R S t V D s.basis):
 s.basis (bit2 U)=digit u 2 ∧ s.basis (bit2 R)=digit V 2 ∧ s.basis cache2=t cache2 := by
 have uv:regValue U s.basis=u:=
  (regValue_congr U _ _ (fun q hq=>h.2.2 q (g.UR q hq) (g.US q hq))).trans hu
 refine ⟨?_,?_,h.2.2 cache2 hR hS⟩
 · simpa only[uv]using bit2_parity U s.basis (by rw[g.u];decide)
 · simpa only[h.1]using bit2_parity R s.basis (by rw[g.r];decide)

theorem sub33CCC_spec {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache:Wire) (hR:cache∉R) (hS:cache∉S) {t:BasisState}
 (cl:Clean Z cs cin t) (u d:Nat) (hu:regValue U t=u) (hu32:u<2^32) (hd:d≤976)
 (hk:t cache=((u%2==1)&&(d%2==1)))
 (cache1:Wire) (h1R:cache1∉R) (h1S:cache1∉S) (h1C:cache1∉cs) (hk1:t cache1=carryLow2 u d)
 (cache2:Wire) (h2R:cache2∉R) (h2S:cache2∉S) (h2C:cache2∉cs) (hk2:t cache2=carryLow3 u d):
 Triple (PS R S t (u+d) 0) (sub33CCC cache cache1 cache2 R Z cs U cin) (PS R S t d 0) := by
 intro s m h
 obtain ⟨bu,br,b2⟩:=ps_third g cache2 h2R h2S t u (u+d) 0 hu s h
 have b1:s.basis cache1=t cache1:=h.2.2 cache1 h1R h1S
 have ready:s.basis cache2=carryBit (s.basis (bit2 U)) (!s.basis (bit2 R)) (s.basis cache1) := by
  rw[bu,br,b2,b1,hk1,hk2]
  simpa only[Nat.one_mul]using (sub_third u d 1 (by decide)).symm
 rw[sub33CCC_eq g cache cache1 cache2 h1R h1C h2R h2C s m (ps_cs g cl.c _ _ s h) ready]
 exact sub33CC_spec g cache hR hS cl u d hu hu32 hd hk cache1 h1R h1S h1C hk1 s m h

theorem addCCC_ps_loose {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache:Wire) (hR:cache∉R) (hS:cache∉S) {t:BasisState}
 (hcin:t cin=false) (u d V D:Nat) (hu:regValue U t=u)
 (hk:t cache=((u%2==1)&&(d%2==1))) (hV:V%2=d%2)
 (j n i:Nat) (hn: 4 ≤ n) (hc: 3 ≤ i)
 (cache1:Wire) (h1R:cache1∉R) (h1S:cache1∉S) (h1C:cache1∉cs)
 (hk1:t cache1=carryLow2 u d) (hV1:V/2%2=d/2%2) (hcs:∀q∈cs,t q=false)
 (cache2:Wire) (h2R:cache2∉R) (h2S:cache2∉S) (h2C:cache2∉cs)
 (hk2:t cache2=carryLow3 u d) (hV2:digit V 2=digit d 2)
 (s:State) (m:List Bool) (h:PS R S t V D s.basis):
 run (addCCC cache cache1 cache2 (U++Z.take j) (R.take n) (cs.take i) cin) m s=
 run (addInPlace (U++Z.take j) (R.take n) (cs.take i) cin) m s := by
 obtain ⟨bu,br,b2⟩:=ps_third g cache2 h2R h2S t u V D hu s h
 have b1:s.basis cache1=t cache1:=h.2.2 cache1 h1R h1S
 have ready:s.basis cache2=carryBit (s.basis (bit2 U)) (s.basis (bit2 R)) (s.basis cache1) := by
  rw[bu,br,b2,b1,hk1,hk2,hV2]
  rfl
 rw[addCCC_eq g cache cache1 cache2 h1C h2C j n i hn hc s m (ps_cs g hcs V D s h) ready]
 exact addCC_ps_loose g cache hR hS hcin u d V D hu hk hV j n i (by omega) (by omega)
  cache1 h1R h1S h1C hk1 hV1 hcs s m h

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan WinArith

theorem digit_mul_one (d k:Nat) (hk:k%16=1):digit (k*d) 2=digit d 2 := by
 apply digit_congr16 _ _ _ ⟨2,by decide⟩
 simp[Nat.mul_mod,hk]

theorem sub43CCCK_spec {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin) {t:BasisState}
 (cl:Clean Z cs cin t) (u d:Nat) (hu:regValue U t=u) (hu32:u<2^32) (hd:d≤976)
 (cache:Wire) (hR:cache∉R) (hS:cache∉S) (hZ:cache∉Z)
 (hk:t cache=((u%2==1)&&(d%2==1))) (k:Wire) (hkZ:k∉Z)
 (cache1:Wire) (h1R:cache1∉R) (h1S:cache1∉S) (h1Z:cache1∉Z) (h1C:cache1∉cs)
 (hk1:t cache1=carryLow2 u d)
 (cache2:Wire) (h2R:cache2∉R) (h2S:cache2∉S) (h2Z:cache2∉Z) (h2C:cache2∉cs)
 (hk2:t cache2=carryLow3 u d):
 Triple (PS R S (kz t k Z) (u+4294968273*d+2^32*(976*(if t k then 1 else 0))) 0)
  (sub43CCC cache cache1 cache2 R Z cs U cin) (PS R S (kz t k Z) (4294968273*d) 0) := by
 intro s m h
 obtain ⟨bu,br,b2⟩:=ps_third g cache2 h2R h2S (kz t k Z) u _ 0 ((kz_u g t k).trans hu) s h
 have b1:s.basis cache1=t cache1:=
  (h.2.2 cache1 h1R h1S).trans (kz_out t k Z g.z cache1 h1Z)
 have b22:s.basis cache2=t cache2:=b2.trans (kz_out t k Z g.z cache2 h2Z)
 have hcs:∀q∈cs,kz t k Z q=false:=by
  intro q hq
  have qZ:q∉Z:=fun bad=>g.away cs Z q hq bad (by simp only[List.count_cons,List.count_append,List.count_nil];omega)
  exact (kz_out t k Z g.z q qZ).trans (cl.c q hq)
 have ready:s.basis cache2=carryBit (s.basis (bit2 U)) (!s.basis (bit2 R)) (s.basis cache1) := by
  rw[bu,br,b22,b1,hk1,hk2]
  have hp:digit (u+4294968273*d+2^32*(976*(if t k then 1 else 0))) 2=digit (u+4294968273*d) 2:=by
   cases t k <;> norm_num[digit] <;> omega
  rw[hp]
  exact (sub_third u d 4294968273 (by decide)).symm
 rw[sub43CCC_eq g cache cache1 cache2 h1R h1C h2R h2C s m (ps_cs g hcs _ _ s h) ready]
 exact sub43CCK_spec g cl u d hu hu32 hd cache hR hS hZ hk k hkZ cache1 h1R h1S h1Z h1C hk1 s m h

def fwdCCC (R S Z cs U : List Wire) (cin k cache cache1 cache2 : Wire) : Program :=
  sub33CCC cache cache1 cache2 R Z cs U cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  (WinArithAux3SmallDevelop.smallF R S cs cin ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (kpat k Z ++ (addCCC cache cache1 cache2 (U ++ Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin ++ kpat k Z))))))

theorem fwdCCC_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (cache : Wire) (hR : cache∉R) (hS : cache∉S) (hZ : cache∉Z)
    (hcache : t cache=((u%2==1) && (d%2==1))) (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (_h35 : u + d < 2^35)
    (cache1 : Wire) (h1R : cache1∉R) (h1S : cache1∉S) (h1Z : cache1∉Z) (h1C : cache1∉cs)
    (hcache1 : t cache1=carryLow2 u d)
    (cache2:Wire) (h2R:cache2∉R) (h2S:cache2∉S) (h2Z:cache2∉Z) (h2C:cache2∉cs)
    (hcache2:t cache2=carryLow3 u d) :
    Triple (PS R S t (u+d) 0) (fwdCCC R S Z cs U cin k cache cache1 cache2)
      (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) := by
  have s1 := sub33CCC_spec g cache hR hS cl u d hu hu32 hd hcache cache1 h1R h1S h1C hcache1 cache2 h2R h2S h2C hcache2
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
      (addCCC cache cache1 cache2 (U++Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin)
      (PS R S (kz t k Z) (977*d+2^32*d+2^0*(u+2^32*(976*(if t k then 1 else 0)))) 0) := by
    intro s m hs
    simp only [List.drop_zero]
    rw [addCCC_ps_loose g cache hR hS kzc u d (977*d+2^32*d) 0
      ((kz_u g t k).trans hu) ((kz_out t k Z g.z cache hZ).trans hcache)
      (by omega) 11 43 42 (by decide) (by decide)
      cache1 h1R h1S h1C ((kz_out t k Z g.z cache1 h1Z).trans hcache1)
      (by
        have hsum:977*d+2^32*d=4294968273*d:=by norm_num;omega
        rw[hsum]
        simpa only[Nat.zero_add] using low2_mul 0 d 4294968273 (by decide)) (by
        intro q hq
        exact (kz_out t k Z g.z q (csZ q hq)).trans (cl.c q hq))
      cache2 h2R h2S h2C ((kz_out t k Z g.z cache2 h2Z).trans hcache2) (by
        have hsum:977*d+2^32*d=4294968273*d:=by norm_num;omega
        rw[hsum]
        exact digit_mul_one d 4294968273 (by decide)) s m hs]
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
  unfold fwdCCC
  exact seqv s1 (PS_val (by omega)) (seqv s2 (PS_dval a2)
    (seqv s3 (fun _ h => h) (seqv s4 (PS_val a4) (seqv s5 (PS_dval a5)
    (seqv p1 (fun _ h => h) (seqv s6 (fun _ h => h)
    (Triple.conseq (fun s h => h) p2 (PS_val (by cases t k <;> simp <;> omega)))))))))


def invCCC (R S Z cs U : List Wire) (cin k cache cache1 cache2 : Wire) : Program :=
  kpat k Z ++ (sub43CCC cache cache1 cache2 R Z cs U cin ++ (kpat k Z ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (WinArithAux3SmallDevelop.smallI R S cs cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  addCCC cache cache1 cache2 (U ++ Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin))))))

theorem invCCC_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (cache : Wire) (hR : cache∉R) (hS : cache∉S) (hZ : cache∉Z)
    (hcache : t cache=((u%2==1) && (d%2==1))) (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (_h35 : u + d < 2^35)
    (cache1 : Wire) (h1R : cache1∉R) (h1S : cache1∉S) (h1Z : cache1∉Z) (h1C : cache1∉cs)
    (hcache1 : t cache1=carryLow2 u d)
    (cache2:Wire) (h2R:cache2∉R) (h2S:cache2∉S) (h2Z:cache2∉Z) (h2C:cache2∉cs)
    (hcache2:t cache2=carryLow3 u d) :
    Triple (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) (invCCC R S Z cs U cin k cache cache1 cache2)
      (PS R S t (u+d) 0) := by
  have p1 := kpat_PS g k hkR hkS hkZ t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0
  have s1 := sub43CCCK_spec g cl u d hu hu32 hd cache hR hS hZ hcache k hkZ cache1 h1R h1S h1Z h1C hcache1 cache2 h2R h2S h2Z h2C hcache2
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
      (addCCC cache cache1 cache2 (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin)
      (PS R S t (d+2^0*u) 0) := by
    intro s m hs
    simp only [List.drop_zero]
    rw [addCCC_ps_loose g cache hR hS cl.cin u d d 0 hu hcache rfl
      1 33 32 (by decide) (by decide) cache1 h1R h1S h1C hcache1 rfl cl.c cache2 h2R h2S h2C hcache2 rfl s m hs]
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
  unfold invCCC
  exact seqv p1 (fun _ h => h) (seqv s1 (fun _ h => h) (seqv p2 (PS_val (by ring))
    (seqv s2 (PS_dval a2) (seqv s3 (PS_val a3)
    (seqv s4 (fun _ h => h) (seqv s5 (PS_dval a5)
    (Triple.conseq (fun s h => h) s6 (PS_val (by omega)))))))))

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
def wFwdCCC (L:CuccaroStreamedSquareWideLayout) (cache cache1 cache2:Wire):Program :=
 fwdCCC (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L) cache cache1 cache2
def wInvCCC (L:CuccaroStreamedSquareWideLayout) (cache cache1 cache2:Wire):Program :=
 invCCC (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L) cache cache1 cache2
theorem wMidCCC_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cache : Wire) (cacheE : cache∈eReg L) (cache1 : Wire) (cache1E : cache1∈eReg L) (cache2:Wire) (cache2E:cache2∈eReg L)
    (base : BasisState) (hc : L.PairClean base) (O E b1 : Nat) (hb1 : regValue (hiReg L) base = b1)
    (hb1lt : b1 < 2^128) (hO : O < SquareReduction.p)
    (K : Nat) (hK : K ≤ 1) :
    Triple (fun x=> BState L base O E (4294968272*b1) x ∧
      x cache=((b1/2^96%2==1) && ((4294968272*b1/2^128-b1/2^96)%2==1)) ∧
      x cache1=carryLow2 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      x cache2=carryLow3 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      (if x (eU L) then 1 else 0)=K) (wFwdCCC L cache cache1 cache2 ++ (wCoreK L ++ wInvCCC L cache cache1 cache2))
      (fun x=> BState L base (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 4294968272*2^32*K +
        2^128*((4294968272*b1)%2^128) + (SquareReduction.p-1-O)) % SquareReduction.p) E (4294968272*b1) x ∧
      x cache=((b1/2^96%2==1) && ((4294968272*b1/2^128-b1/2^96)%2==1)) ∧
      x cache1=carryLow2 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      x cache2=carryLow3 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      (if x (eU L) then 1 else 0)=K) := by
  intro s m input
  obtain ⟨h,hCache,hCache1,hCache2,key⟩:=input
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
  have cr2 : cache2∉mR L := fun hr=>(m_away L hn cache2 (Or.inl hr)).2 cache2E
  have cS2 : cache2∉mS L := fun hs=>(m_away L hn cache2 (Or.inr hs)).2 cache2E
  have cZ2 : cache2∉mZ L := by
    intro hz
    have lc:=layoutCount L hn cache2
    have ps:=productSplit L cache2
    have ec:=eReg_count L cache2
    have ce:=List.count_pos_iff.mpr cache2E
    have cz:=List.count_pos_iff.mpr (mZ_pad L cache2 hz)
    omega
  have cC2 : cache2∉mC L := by
    intro hz
    have lc:=layoutCount L hn cache2
    have ps:=productSplit L cache2
    have ec:=eReg_count L cache2
    have ce:=List.count_pos_iff.mpr cache2E
    have cz:=List.count_pos_iff.mpr (mC_pad L cache2 hz)
    omega
  have co2 : cache2∉L.core.out := (eReg_away L hn cache2 cache2E).1
  obtain ⟨ws1, ws2, ws3⟩ := whi_split b1 hb1lt
  generalize hW : 4294968272*b1 = W at h hCache hCache1 hCache2 ws1 ws2 ws3 ⊢
  generalize hu : b1/2^96 = u at hCache hCache1 hCache2 ws1 ws2 ⊢
  generalize hd : W/2^128 - u = d at hCache hCache1 hCache2 ws2 ⊢
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
  have T1 : Triple (WinArith.PS (mR L) (mS L) s.basis (u+d) 0) (wFwdCCC L cache cache1 cache2)
      (WinArith.PS (mR L) (mS L) s.basis (u + 4294968273*d + 2^32*(976*K)) 0) := by
    have := fwdCCC_spec g cl u d hU hu32 ws2 cache cr cS cZ hCache (eU L) heR heS heZ (by omega) cache1 cr1 cS1 cZ1 cC1 hCache1 cache2 cr2 cS2 cZ2 cC2 hCache2
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
  have T3 : Triple Q2 (wInvCCC L cache cache1 cache2) Q3 := by
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
    have hCache0at2 : s2.basis cache=((u%2==1) && (d%2==1)) :=
      (k2 cache co cr cS).trans hCache
    have hCache12 : s2.basis cache1=carryLow2 u d :=
      (k2 cache1 co1 cr1 cS1).trans hCache1
    have hCache22 : s2.basis cache2=carryLow3 u d :=
      (k2 cache2 co2 cr2 cS2).trans hCache2
    obtain ⟨ph, h3⟩ := invCCC_spec g cl2 u d hU2 hu32 ws2 cache cr cS cZ hCache0at2 (eU L) heR heS heZ (by omega) cache1 cr1 cS1 cZ1 cC1 hCache12 cache2 cr2 cS2 cZ2 cC2 hCache22 s2 m2 P2
    refine ⟨ph, ?_, h3.1, h3.2.1, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => h3.2.2 q (fun hr => (m_away L hn q (Or.inl hr)).1 hq)
        (fun hs => (m_away L hn q (Or.inr hs)).1 hq))).trans h2.1
    · intro q a b c; exact (h3.2.2 q b c).trans (k2 q a b c)
  obtain ⟨ph, f⟩ := (T1.seq (T2.seq T3)) s m P0
  refine ⟨ph, ⟨f.1, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => f.2.2.2 q (eReg_away L hn q hq).1
      (fun hr => (m_away L hn q (Or.inl hr)).2 hq) (fun hs => (m_away L hn q (Or.inr hs)).2 hq))).trans h.2.1
  · -- the work register is `W` again
    have wv : regValue L.core.work (run (wFwdCCC L cache cache1 cache2 ++ (wCoreK L ++ wInvCCC L cache cache1 cache2)) m s).basis = W := by
      rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
      have lo : regValue (L.core.work.take 128) (run (wFwdCCC L cache cache1 cache2 ++ (wCoreK L ++ wInvCCC L cache cache1 cache2)) m s).basis = W % 2^128 := by
        rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
          WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
      have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdCCC L cache cache1 cache2 ++ (wCoreK L ++ wInvCCC L cache cache1 cache2)) m s).basis = 0 := by
        apply (regValue_zero _ _).mpr
        intro q hq
        rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
        apply workZ
        have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
        rw [this] at hq
        exact List.mem_of_mem_drop hq
      have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdCCC L cache cache1 cache2 ++ (wCoreK L ++ wInvCCC L cache cache1 cache2)) m s).basis = u + d :=
        f.2.1
      rw [lo, mr, hi0]
      omega
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) (run (wFwdCCC L cache cache1 cache2 ++ (wCoreK L ++ wInvCCC L cache cache1 cache2)) m s).basis
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
      have wv : regValue L.core.work (run (wFwdCCC L cache cache1 cache2 ++ (wCoreK L ++ wInvCCC L cache cache1 cache2)) m s).basis = W := by
        rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
        have lo : regValue (L.core.work.take 128) (run (wFwdCCC L cache cache1 cache2 ++ (wCoreK L ++ wInvCCC L cache cache1 cache2)) m s).basis = W % 2^128 := by
          rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
            WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
        have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdCCC L cache cache1 cache2 ++ (wCoreK L ++ wInvCCC L cache cache1 cache2)) m s).basis = 0 := by
          apply (regValue_zero _ _).mpr
          intro q hq
          rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
          apply workZ
          have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
          rw [this] at hq
          exact List.mem_of_mem_drop hq
        have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdCCC L cache cache1 cache2 ++ (wCoreK L ++ wInvCCC L cache cache1 cache2)) m s).basis = u + d :=
          f.2.1
        rw [lo, mr, hi0]
        omega
      have z : regValue (L.core.work.drop 163) (run (wFwdCCC L cache cache1 cache2 ++ (wCoreK L ++ wInvCCC L cache cache1 cache2)) m s).basis = 0 := by
        rw [WinArith.drop_div _ _ (by simp [hw.core.work]), wv, Nat.div_eq_of_lt hWlt]
      rw [(regValue_zero _ _).mp z q hd163]
      exact ((regValue_zero _ _).mp hc.work q wq).symm
    by_cases hs : q ∈ mS L
    · rw [(regValue_zero _ _).mp f.2.2.1 q hs]
      exact ((regValue_zero _ _).mp hc.pad q (mS_pad L q hs)).symm
    · exact (f.2.2.2 q h1 hr hs).trans (keepS q h1 h2 h3)



  · exact (f.2.2.2 cache co cr cS).trans hCache
  · exact (f.2.2.2 cache1 co1 cr1 cS1).trans hCache1
  · exact (f.2.2.2 cache2 co2 cr2 cS2).trans hCache2
  · rw [f.2.2.2 (eU L) eA.2.2 heR heS]
    exact key

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan

def loanValue2 (t:BasisState) (g v u0 u1 u2 e0 e1:Wire):Bool :=
 t u2 ^^ (t v&&t g) ^^ (t v&&t e0) ^^ (t v&&t u0) ^^ (t u1&&t e1) ^^ t u1

def prepare3 (g v u0 u1 u2 r0 r1 r2 e0 cache host1 host2:Wire):Program :=
 loan2 g v u0 u1 u2 e0 host1 host2++
  (SecondCarryLoan.prepare u0 u1 r0 r1 e0 cache host1++prime2 u2 r2 host1 host2)

def finish3 (g v u0 u1 u2 r0 r1 r2 e0 cache host1 host2:Wire):Program :=
 clear2 u2 r2 host1 host2++
  (SecondCarryLoan.finish u0 u1 r0 r1 e0 cache host1++restore2 g v u0 u1 u2 e0 host1 host2)

theorem geometry12_7 (g v u0 u1 u2 r0 r1 r2 e0 cache host1 host2:Wire)
 (nd:[g,v,u0,u1,u2,r0,r1,r2,e0,cache,host1,host2].Nodup):
 [u0,u1,r0,r1,e0,cache,host1].Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have h:=List.nodup_iff_count_le_one.mp nd q
 simp only[List.count_cons,List.count_nil]at h ⊢
 omega

theorem prepare3_run (g v u0 u1 u2 r0 r1 r2 e0 cache host1 host2:Wire)
 (nd:[g,v,u0,u1,u2,r0,r1,r2,e0,cache,host1,host2].Nodup) (s:State) (m:List Bool)
 (hz:s.basis cache=false)
 (hl1:s.basis host1=(s.basis u1 ^^ s.basis u0 ^^ (s.basis u0&&s.basis e0)))
 (hl2:s.basis host2=loanValue2 s.basis g v u0 u1 u2 e0 host1):
 run (prepare3 g v u0 u1 u2 r0 r1 r2 e0 cache host1 host2) m s=
 ⟨s.phase,writeBit (writeBit (writeBit s.basis cache (s.basis u0&&!s.basis r0)) host1
  (carryBit (s.basis u1) (!s.basis r1) (s.basis u0&&!s.basis r0))) host2
  (carryBit (s.basis u2) (!s.basis r2) (carryBit (s.basis u1) (!s.basis r1) (s.basis u0&&!s.basis r0)))⟩ := by
 have geom:=nd
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geom
 have nd7:=geometry12_7 g v u0 u1 u2 r0 r1 r2 e0 cache host1 host2 nd
 let k0:=s.basis u0&&!s.basis r0
 let k1:=carryBit (s.basis u1) (!s.basis r1) k0
 let k2:=carryBit (s.basis u2) (!s.basis r2) k1
 let S0:State:=⟨s.phase,writeBit s.basis host2 false⟩
 let S1:State:=⟨s.phase,writeBit (writeBit S0.basis cache k0) host1 k1⟩
 have p:∀r,run (loan2 g v u0 u1 u2 e0 host1 host2) r s=S0 := by
  intro r
  exact loan2_run g v u0 u1 u2 e0 host1 host2 (by tauto) (by tauto) (by tauto)
   (by tauto) (by tauto) (by tauto) (by tauto) s r hl2
 have q:∀r,run (SecondCarryLoan.prepare u0 u1 r0 r1 e0 cache host1) r S0=S1 := by
  intro r
  rw[SecondCarryLoan.prepare_run u0 u1 r0 r1 e0 cache host1 nd7 S0 r]
  · simp[S1,S0,k0,k1,writeBit,Function.update_apply,show u0≠host2 by tauto,
     show u1≠host2 by tauto,show r0≠host2 by tauto,show r1≠host2 by tauto]
  · simpa[S0,writeBit,Function.update_apply,show cache≠host2 by tauto]using hz
  · simpa[S0,writeBit,Function.update_apply,show host1≠host2 by tauto,
     show u0≠host2 by tauto,show u1≠host2 by tauto,show e0≠host2 by tauto]using hl1
 have z:∀r,run (prime2 u2 r2 host1 host2) r S1=
   ⟨s.phase,writeBit (writeBit (writeBit s.basis cache k0) host1 k1) host2 k2⟩ := by
  intro r
  rw[prime2_run u2 r2 host1 host2 (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) S1 r]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases wh:w=host2
  · subst w
    simp[S1,S0,k2,writeBit,Function.update_apply,
     show u2≠host1 by tauto,show u2≠cache by tauto,show u2≠host2 by tauto,
     show r2≠host1 by tauto,show r2≠cache by tauto,show r2≠host2 by tauto,
     show host2≠host1 by tauto,show host2≠cache by tauto]
  · simp[S1,S0,writeBit,Function.update_apply,wh]
 rw[prepare3,run_append,p,run_append,q,z]

theorem finish3_run (g v u0 u1 u2 r0 r1 r2 e0 cache host1 host2:Wire)
 (nd:[g,v,u0,u1,u2,r0,r1,r2,e0,cache,host1,host2].Nodup) (s:State) (m:List Bool)
 (hk0:s.basis cache=(s.basis u0&&!s.basis r0))
 (hk1:s.basis host1=carryBit (s.basis u1) (!s.basis r1) (s.basis cache))
 (hk2:s.basis host2=carryBit (s.basis u2) (!s.basis r2) (s.basis host1)):
 let t:=writeBit (writeBit (writeBit s.basis host2 false) host1
   (s.basis u1 ^^ s.basis u0 ^^ (s.basis u0&&s.basis e0))) cache false
 run (finish3 g v u0 u1 u2 r0 r1 r2 e0 cache host1 host2) m s=
  ⟨s.phase,writeBit t host2 (loanValue2 t g v u0 u1 u2 e0 host1)⟩ := by
 have geom:=nd
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geom
 have nd7:=geometry12_7 g v u0 u1 u2 r0 r1 r2 e0 cache host1 host2 nd
 let S0:State:=⟨s.phase,writeBit s.basis host2 false⟩
 let t:=writeBit (writeBit S0.basis host1 (s.basis u1 ^^ s.basis u0 ^^ (s.basis u0&&s.basis e0))) cache false
 let S1:State:=⟨s.phase,t⟩
 have p:∀r,run (clear2 u2 r2 host1 host2) r s=S0 := by
  intro r
  exact clear2_run u2 r2 host1 host2 (by tauto) (by tauto) (by tauto) s r hk2
 have q:∀r,run (SecondCarryLoan.finish u0 u1 r0 r1 e0 cache host1) r S0=S1 := by
  intro r
  rw[SecondCarryLoan.finish_run u0 u1 r0 r1 e0 cache host1 nd7 S0 r]
  · simp[S1,t,S0,writeBit,Function.update_apply,show u0≠host2 by tauto,
     show u1≠host2 by tauto,show e0≠host2 by tauto]
  · simpa[S0,writeBit,Function.update_apply,show cache≠host2 by tauto,
     show u0≠host2 by tauto,show r0≠host2 by tauto]using hk0
  · simpa[S0,writeBit,Function.update_apply,show host1≠host2 by tauto,
     show u1≠host2 by tauto,show r1≠host2 by tauto,show cache≠host2 by tauto]using hk1
 have z:∀r,run (restore2 g v u0 u1 u2 e0 host1 host2) r S1=
   ⟨s.phase,writeBit t host2 (loanValue2 t g v u0 u1 u2 e0 host1)⟩ := by
  intro r
  rw[restore2_run g v u0 u1 u2 e0 host1 host2 (by tauto) (by tauto) (by tauto)
   (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto)
   (by tauto) (by tauto) (by tauto) (by tauto) S1 r]
  have hz:S1.basis host2=false:=by
   simp[S1,t,S0,writeBit,Function.update_apply,show host2≠cache by tauto,show host2≠host1 by tauto]
  simp only[hz,Bool.false_xor]
  rfl
 dsimp only
 rw[finish3,run_append,p,run_append,q,z]

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem bit2_mem (xs:List Wire) (h:3≤xs.length):bit2 xs∈xs := by
 obtain ⟨a,b,c,ys,rfl⟩:=split_three xs h
 simp[bit2]

theorem head3_count (xs:List Wire) (h:3≤xs.length) (q:Wire):
 [xs.headD 0,bit1 xs,bit2 xs].count q≤xs.count q := by
 obtain ⟨a,b,c,ys,rfl⟩:=split_three xs h
 simp only[bit1,bit2,List.headD_cons,List.drop_succ_cons,List.drop_zero]
 simp only[List.count_cons,List.count_nil]
 omega

def host2Wire (L:CuccaroStreamedSquareWideLayout):Wire:=bit2 (eReg L)

theorem host2_mem (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):host2Wire L∈eReg L :=
 bit2_mem _ (by simp[eReg_length L hw])

theorem geometry12 (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires):
 [g,bit1 L.core.high,(mU L).headD 0,bit1 (mU L),bit2 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),(eReg L).headD 0,
  cacheWire L,hostWire L,host2Wire L].Nodup := by
 have geo:=mGeo L hw hn
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have uc:=head3_count (mU L) (by rw[geo.u];decide) q
 have rc:=head3_count (mR L) (by rw[geo.r];decide) q
 have ec:=head3_count ((eReg L).take 129) (by simp[eReg_length L hw]) q
 have hhead:((eReg L).take 129).headD 0=(eReg L).headD 0:=head_take_pos _ _ (by decide)
 have hbit:bit1 ((eReg L).take 129)=hostWire L:=bit1_take _ _ (by decide)
 have hbit2:bit2 ((eReg L).take 129)=host2Wire L:=bit2_take _ _ (by decide)
 rw[hhead,hbit,hbit2]at ec
 have ed:=congrArg (List.count q) (cache_decomp L hw)
 have ud:(mU L).count q≤(hiReg L).count q:=(List.drop_sublist _ _).count_le q
 have rd:(mR L).count q≤L.core.work.count q:=
  ((List.take_sublist _ _).trans (List.drop_sublist _ _)).count_le q
 have hy:2≤L.core.high.length:=by simp[CuccaroStreamedSquareLayout.high,hw.core.y]
 have vy:bit1 L.core.high∈L.core.y:=
  List.mem_of_mem_drop (List.mem_of_mem_take (bit1_mem _ hy))
 have vc:([bit1 L.core.high]:List Wire).count q≤L.core.y.count q:=
  (List.singleton_sublist.mpr vy).count_le q
 have ps:=productSplit L q
 have es:=eReg_count L q
 have lc:=List.nodup_iff_count_le_one.mp (List.nodup_cons.mpr ⟨hg,hn⟩) q
 simp only[CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
  List.count_cons,List.count_append,List.count_nil]at lc uc rc ec ed vc ⊢
 omega

theorem bstate_heads3 (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (base s:BasisState) (hc:L.PairClean base) (O E b1:Nat) (hb1:regValue (hiReg L) base=b1)
 (hb1lt:b1<2^128) (h:BState L base O E (4294968272*b1) s):
 s (bit2 (mU L))=digit (b1/2^96) 2 ∧
 s (bit2 (mR L))=digit (b1/2^96+(4294968272*b1/2^128-b1/2^96)) 2 := by
 have g:=mGeo L hw hn
 obtain ⟨h1,h2,h3⟩:=whi_split b1 hb1lt
 have hr:=mR_value L hw hn base hc O E (4294968272*b1) s h
 have hv:regValue (mR L) s=b1/2^96+(4294968272*b1/2^128-b1/2^96):=by
  rw[hr.1,Nat.mod_eq_of_lt (by omega)]
  omega
 have hu:=bstate_u L hw hn base s O E b1 hb1 h
 constructor
 · rw[bit2_parity (mU L) s (by rw[g.u];decide),hu]
 · rw[bit2_parity (mR L) s (by rw[g.r];decide),hv]

theorem source_away (L:CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) (v:Wire)
 (hv:v∈L.core.y):v∉L.core.out ∧ v∉eReg L ∧ v∉accReg L := by
 have vc:=List.count_pos_iff.mpr hv
 have lc:=layoutCount L hn v
 have ec:=eReg_count L v
 have ps:=productSplit L v
 have ws:=workSplit L v
 refine ⟨?_,?_,?_⟩ <;> intro h <;> have hc:=List.count_pos_iff.mpr h <;> omega

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem external_away (L:CuccaroStreamedSquareWideLayout) (q:Wire) (hq:q∉L.wires):
 q∉L.core.out ∧ q∉eReg L ∧ q∉accReg L := by
 have hc:=List.count_eq_zero.mpr hq
 have ec:=eReg_count L q
 have ps:=productSplit L q
 have ws:=workSplit L q
 simp only[CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
  List.count_append]at hc
 refine ⟨?_,?_,?_⟩ <;> intro h <;> have hp:=List.count_pos_iff.mpr h <;> omega

theorem host2_ne_key (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 host2Wire L≠eU L := by
 have shape:=(eShape L hw).1
 have len:(eRlow L).length=128:=by simp[eRlow,hw.core.product]
 have hm:host2Wire L∈eRlow L:=by
  unfold host2Wire
  rw[shape,bit2_append _ _ (by rw[len];decide)]
  exact bit2_mem _ (by rw[len];decide)
 have nd:=eReg_nodup L hn
 rw[shape]at nd
 exact (List.nodup_append.mp nd).2.2 _ hm _ (by simp)

def wMidFullCCC (L:CuccaroStreamedSquareWideLayout) (c:Wire):Program:=
 prepare3 c (bit1 L.core.high) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L)++
 ((wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L)++
   (wCoreK L++wInvCCC L (cacheWire L) (hostWire L) (host2Wire L)))++
  finish3 c (bit1 L.core.high) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L))
   ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) ((eReg L).headD 0)
   (cacheWire L) (hostWire L) (host2Wire L))

theorem wMidFullCCC_step (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (c:Wire) (hcw:c∉L.wires) (base:BasisState) (hc:L.PairClean base) (O E b1:Nat)
 (hb1:regValue (hiReg L) base=b1) (hb1lt:b1<2^128) (hO:O<SquareReduction.p)
 (H l K:Nat) (hH:H<2^96) (hl:l<2^32) (hK:K≤1) (hE:E=2^32*H+l+2^128*K)
 (hLoan:(E/2%2==1)=((b1/2^96/2%2==1) ^^ (b1/2^96%2==1) ^^
   ((b1/2^96%2==1)&&(E%2==1))))
 (hLoan2:digit E 2= (digit (b1/2^96) 2 ^^
   (base (bit1 L.core.high)&&base c) ^^ (base (bit1 L.core.high)&&digit E 0) ^^
   (base (bit1 L.core.high)&&digit (b1/2^96) 0) ^^
   (digit (b1/2^96) 1&&digit E 1) ^^ digit (b1/2^96) 1)):
 Triple (BState L base O E (4294968272*b1)) (wMidFullCCC L c)
 (BState L base (((b1/2^96+4294968273*(4294968272*b1/2^128-b1/2^96))+4294968272*2^32*K+
   2^128*((4294968272*b1)%2^128)+(SquareReduction.p-1-O))%SquareReduction.p) E (4294968272*b1)) := by
 intro s m h
 let u0:Wire:=(mU L).headD 0
 let u1:Wire:=bit1 (mU L)
 let u2:Wire:=bit2 (mU L)
 let r0:Wire:=(mR L).headD 0
 let r1:Wire:=bit1 (mR L)
 let r2:Wire:=bit2 (mR L)
 let e0:Wire:=(eReg L).headD 0
 let v:Wire:=bit1 L.core.high
 let cache:Wire:=cacheWire L
 let host:Wire:=hostWire L
 let host2:Wire:=host2Wire L
 let u:=b1/2^96
 let d:=4294968272*b1/2^128-u
 let k0:Bool:=(u%2==1)&&(d%2==1)
 let k1:Bool:=carryLow2 u d
 let k2:Bool:=carryLow3 u d
 have nd:[c,v,u0,u1,u2,r0,r1,r2,e0,cache,host,host2].Nodup:=geometry12 L hw hn c hcw
 have geom:=nd
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geom
 have ce:cache∈eReg L:=cache_mem L hw
 have he:host∈eReg L:=host_mem L hw
 have he2:host2∈eReg L:=host2_mem L hw
 have ca:=external_away L c hcw
 have vy:v∈L.core.y:=List.mem_of_mem_drop (List.mem_of_mem_take
  (bit1_mem L.core.high (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])))
 have va:=source_away L hn v vy
 have sg:s.basis c=base c:=h.2.2.2 c ca.1 ca.2.1 ca.2.2
 have sv:s.basis v=base v:=h.2.2.2 v va.1 va.2.1 va.2.2
 have hz:s.basis cache=false:=e_cache_zero L hw s.basis E h.2.1 (by rw[hE];omega)
 have b0:=bstate_heads L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b1s:=bstate_heads2 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b2:=bstate_heads3 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have es:s.basis e0=(E%2==1):=by
  dsimp[e0];rw[head_parity (eReg L) s.basis (by simp[eReg_length L hw]),h.2.1]
 have hs:s.basis host=(E/2%2==1):=by
  dsimp[host,hostWire];rw[bit1_parity (eReg L) s.basis (by simp[eReg_length L hw]),h.2.1]
 have hs2:s.basis host2=digit E 2:=by
  dsimp[host2,host2Wire];rw[bit2_parity (eReg L) s.basis (by simp[eReg_length L hw]),h.2.1]
 have ready:s.basis host=(s.basis u1 ^^ s.basis u0 ^^ (s.basis u0&&s.basis e0)):=by
  rw[hs,b0.1,b1s.1,es];exact hLoan
 have ready2:s.basis host2=loanValue2 s.basis c v u0 u1 u2 e0 host:=by
  rw[hs2]
  unfold loanValue2
  rw[b2.1,b0.1,b1s.1,es,hs,sg,sv]
  simpa only[digit,pow_zero,pow_one,Nat.div_one,v]using hLoan2
 have carry0:(s.basis u0&&!s.basis r0)=k0:=by
  rw[b0.1,b0.2];simpa only[Nat.one_mul]using carry_parity u d 1 (by decide)
 have carry1:carryBit (s.basis u1) (!s.basis r1) k0=k1:=by
  rw[b1s.1,b1s.2];simpa only[Nat.one_mul]using sub_second u d 1 (by decide)
 have carry2:carryBit (s.basis u2) (!s.basis r2) k1=k2:=by
  rw[b2.1,b2.2];simpa only[Nat.one_mul]using sub_third u d 1 (by decide)
 let t:BasisState:=writeBit (writeBit (writeBit s.basis cache k0) host k1) host2 k2
 let EP:Nat:=regValue (eReg L) t
 have prepared:∀mm,run (prepare3 c v u0 u1 u2 r0 r1 r2 e0 cache host host2) mm s=⟨s.phase,t⟩:=by
  intro mm
  rw[prepare3_run c v u0 u1 u2 r0 r1 r2 e0 cache host host2 nd s mm hz ready ready2,carry0,carry1,carry2]
 have hb0:=bstate_write_e L hn cache ce base s.basis O E _ h k0
 have hb2:=bstate_write_e L hn host he base (writeBit s.basis cache k0) O
  (regValue (eReg L) (writeBit s.basis cache k0)) _ hb0 k1
 have hb3:=bstate_write_e L hn host2 he2 base (writeBit (writeBit s.basis cache k0) host k1) O
  (regValue (eReg L) (writeBit (writeBit s.basis cache k0) host k1)) _ hb2 k2
 have inp:BState L base O EP (4294968272*b1) t ∧ t cache=k0 ∧ t host=k1 ∧ t host2=k2 ∧
  (if t (eU L) then 1 else 0)=K:=by
  refine ⟨hb3,?_,?_,?_,?_⟩
  · simp[t,writeBit,Function.update_apply,show cache≠host by tauto,show cache≠host2 by tauto]
  · simp[t,writeBit,Function.update_apply,show host≠host2 by tauto]
  · simp[t,writeBit]
  · have hk:=bstate_key L hw s.basis E H l K h.2.1 hH hl hK hE
    simpa[t,writeBit,Function.update_apply,show eU L≠cache from (cache_ne_k L hw hn).symm,
     show eU L≠host from (host_ne_key L hw hn).symm,show eU L≠host2 from (host2_ne_key L hw hn).symm]using hk
 let mid:=wFwdCCC L cache host host2++(wCoreK L++wInvCCC L cache host host2)
 let rest:=m.drop (measurementCount (prepare3 c v u0 u1 u2 r0 r1 r2 e0 cache host host2))
 let mmid:=rest.take (measurementCount mid)
 rw[wMidFullCCC,run_append,prepared,run_append]
 have hm:=wMidCCC_step L hw hn cache ce host he host2 he2 base hc O EP b1 hb1 hb1lt hO K hK
  (⟨s.phase,t⟩:State) mmid inp
 generalize hr:run mid mmid (⟨s.phase,t⟩:State)=r at hm ⊢
 have br0:=bstate_heads L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br1:=bstate_heads2 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br2:=bstate_heads3 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have er:∀q∈eReg L,r.basis q=t q:=(regValue_eq_iff _ _ _).mp hm.2.1.2.1
 have rE0:r.basis e0=s.basis e0:=by
  rw[er e0 (head_mem _ (by simp[eReg_length L hw]))]
  simp[t,writeBit,Function.update_apply,show e0≠host by tauto,show e0≠cache by tauto,show e0≠host2 by tauto]
 have rU0:r.basis u0=s.basis u0:=br0.1.trans b0.1.symm
 have rU1:r.basis u1=s.basis u1:=br1.1.trans b1s.1.symm
 have rU2:r.basis u2=s.basis u2:=br2.1.trans b2.1.symm
 have rR0:r.basis r0=s.basis r0:=br0.2.trans b0.2.symm
 have rR1:r.basis r1=s.basis r1:=br1.2.trans b1s.2.symm
 have rR2:r.basis r2=s.basis r2:=br2.2.trans b2.2.symm
 have rG:r.basis c=s.basis c:=(hm.2.1.2.2.2 c ca.1 ca.2.1 ca.2.2).trans sg.symm
 have rV:r.basis v=s.basis v:=(hm.2.1.2.2.2 v va.1 va.2.1 va.2.2).trans sv.symm
 have rk:r.basis cache=(r.basis u0&&!r.basis r0):=by
  rw[rU0,rR0,carry0];exact hm.2.2.1
 have rk1:r.basis host=carryBit (r.basis u1) (!r.basis r1) (r.basis cache):=by
  rw[rU1,rR1,hm.2.2.1,carry1];exact hm.2.2.2.1
 have rk2:r.basis host2=carryBit (r.basis u2) (!r.basis r2) (r.basis host):=by
  rw[rU2,rR2,hm.2.2.2.1,carry2];exact hm.2.2.2.2.1
 have restored:(r.basis u1 ^^ r.basis u0 ^^ (r.basis u0&&r.basis e0))=s.basis host:=by
  rw[rU1,rU0,rE0];exact ready.symm
 rw[finish3_run c v u0 u1 u2 r0 r1 r2 e0 cache host host2 nd r _ rk rk1 rk2]
 dsimp only
 rw[restored]
 let t0:=writeBit (writeBit (writeBit r.basis host2 false) host (s.basis host)) cache false
 have restored2:loanValue2 t0 c v u0 u1 u2 e0 host=s.basis host2:=by
  dsimp[loanValue2,t0]
  simp only[writeBit,Function.update_apply,
   show c≠cache by tauto,show c≠host by tauto,show c≠host2 by tauto,
   show v≠cache by tauto,show v≠host by tauto,show v≠host2 by tauto,
   show u0≠cache by tauto,show u0≠host by tauto,show u0≠host2 by tauto,
   show u1≠cache by tauto,show u1≠host by tauto,show u1≠host2 by tauto,
   show u2≠cache by tauto,show u2≠host by tauto,show u2≠host2 by tauto,
   show e0≠cache by tauto,show e0≠host by tauto,show e0≠host2 by tauto,
   show host≠cache by tauto,ite_false,ite_true,rG,rV,rU0,rU1,rU2,rE0]
  exact ready2.symm
 refine ⟨hm.1,?_⟩
 have hf0:=bstate_write_e L hn host2 he2 base r.basis _ EP _ hm.2.1 false
 have hf1:=bstate_write_e L hn host he base (writeBit r.basis host2 false) _
  (regValue (eReg L) (writeBit r.basis host2 false)) _ hf0 (s.basis host)
 have hf2:=bstate_write_e L hn cache ce base (writeBit (writeBit r.basis host2 false) host (s.basis host)) _
  (regValue (eReg L) (writeBit (writeBit r.basis host2 false) host (s.basis host))) _ hf1 false
 have hf3:=bstate_write_e L hn host2 he2 base t0 _ (regValue (eReg L) t0) _ hf2 (loanValue2 t0 c v u0 u1 u2 e0 host)
 have ev:regValue (eReg L) (writeBit t0 host2 (loanValue2 t0 c v u0 u1 u2 e0 host))=E:=by
  rw[restored2]
  apply Eq.trans _ h.2.1
  apply regValue_congr
  intro q hq
  by_cases q2:q=host2
  · subst q;simp[writeBit]
  by_cases q1:q=host
  · subst q;simp[t0,writeBit,Function.update_apply,show host≠host2 by tauto,show host≠cache by tauto]
  by_cases qc:q=cache
  · subst q;simp[t0,writeBit,Function.update_apply,show cache≠host2 by tauto,hz]
  · simp only[writeBit,Function.update_apply,q2,q1,qc,ite_false,t0]
    rw[er q hq]
    simp[t,writeBit,Function.update_apply,q2,q1,qc]
 simpa only[ev]using hf3

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop

theorem loan2_from_mod16 (g:Bool) (originalM u E:Nat)
 (hE:E%16=lowSum g originalM u%16):
 digit E 2 = (digit u 2 ^^ (digit originalM 1&&g) ^^
  (digit originalM 1&&digit E 0) ^^ (digit originalM 1&&digit u 0) ^^
  (digit u 1&&digit E 1) ^^ digit u 1) := by
 have h:=third_nat g originalM u
 have h0:=digit_congr16 E (lowSum g originalM u) hE ⟨0,by decide⟩
 have h1:=digit_congr16 E (lowSum g originalM u) hE ⟨1,by decide⟩
 have h2:=digit_congr16 E (lowSum g originalM u) hE ⟨2,by decide⟩
 rw[←h0,←h1,←h2]at h
 simpa only[Bool.and_xor_distrib_left,Bool.xor_assoc]using h

theorem folded_low_mod16 (M u H l K:Nat)
 (hH:H=(M^2%2^128)/2^32) (hl:l=((M^2%2^128)%2^32+u)%2^32):
 (2^32*H+l+2^128*K)%16=(M^2+u)%16 := by
 rw[hl]
 change (4294967296*H+((M^2%340282366920938463463374607431768211456)%4294967296+u)%4294967296+
  340282366920938463463374607431768211456*K)%16=(M^2+u)%16
 omega

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem add3_patch (cache0 cache1 cache2:Wire) (x y cs:List Wire) (cin:Wire)
 (hx:4≤x.length) (hy:4≤y.length) (hc:3≤cs.length):
 Patch cache2 1 (addCCC cache0 cache1 cache2 x y cs cin) (addCC cache0 cache1 x y cs cin):=by
 obtain ⟨a0,a1,a2,a3,xs,rfl⟩:=split_four x hx
 obtain ⟨b0,b1,b2,b3,ys,rfl⟩:=split_four y hy
 obtain ⟨k0,k1,k2,ks,rfl⟩:=split_three cs hc
 have p:=add2_patch cache1 cache2 (a1::a2::a3::xs) (b1::b2::b3::ys) (k1::k2::ks) k0
  (by simp) (by simp) (by simp)
 have h:=(Patch.refl cache2 [.CX cache0 k0]).app
  (p.app (Patch.refl cache2 (mappedEraseCarry ⟨some a0,false⟩ b0 cin k0++mappedSum ⟨some a0,false⟩ b0 cin)))
 simpa only[addCCC,addCC,addC,cachedMapped3,cachedMapped2,cachedMapped,mappedRead,List.map_cons,
  Nat.zero_add,Nat.add_zero,List.append_assoc]using h

theorem sub3_patch (cache0 cache1 cache2:Wire) (expected:Bool) (x y cs:List Wire)
 (flags:List Bool) (cin:Wire) (hx:4≤x.length) (hy:4≤y.length) (hc:3≤cs.length)
 (hf:4≤flags.length) (hf1:flags.getD 1 false=false) (hf2:flags.getD 2 false=false)
 (hf3:flags.getD 3 false=false):
 Patch cache2 1 (cachedSub3 cache0 cache1 cache2 expected (mappedRead x false) flags y cs cin)
  (cachedSub2 cache0 cache1 expected (mappedRead x false) flags y cs cin):=by
 obtain ⟨a0,a1,a2,a3,xs,rfl⟩:=split_four x hx
 obtain ⟨b0,b1,b2,b3,ys,rfl⟩:=split_four y hy
 obtain ⟨k0,k1,k2,ks,rfl⟩:=split_three cs hc
 obtain ⟨f0,f1,f2,f3,fs,rfl⟩:=split_four flags hf
 have h1:f1=false:=by simpa using hf1
 have h2:f2=false:=by simpa using hf2
 have h3:f3=false:=by simpa using hf3
 subst f1;subst f2;subst f3
 have inner:=(majority_patch cache2 a2 b2 k1 k2).app (Patch.refl cache2
  (MixedLiteralAdderDevelop.program expected (mappedRead (a3::xs) false) (b3::ys) (false::fs) ks k2++
   mappedEraseCarry ⟨some a2,false⟩ b2 k1 k2++mappedSum ⟨some a2,false⟩ b2 k1))
 have middle:=(Patch.refl cache2 [.CX cache1 k1]).app (inner.app (Patch.refl cache2
  (mappedEraseCarry ⟨some a1,false⟩ b1 k0 k1++mappedSum ⟨some a1,false⟩ b1 k0)))
 have outer:=(Patch.refl cache2 [.CX cache0 k0]).app (middle.app (Patch.refl cache2
  (mappedEraseCarry ⟨some a0,false⟩ b0 cin k0++mappedSum ⟨some a0,false⟩ b0 cin)))
 have h:=(Patch.refl cache2 (notRegister (b0::b1::b2::b3::ys))).app
  (outer.app (Patch.refl cache2 (notRegister (b0::b1::b2::b3::ys))))
 simpa only[cachedSub3,cachedSub2,cachedMixed3,cachedMixed2,cachedMixed,MixedLiteralAdderDevelop.program,
  MixedLiteralAdderDevelop.head,mappedRead,List.map_cons,mappedMajority,Bool.false_eq_true,if_false,
  Nat.add_zero,Nat.zero_add,List.append_assoc]using h

theorem sub33CCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2:Wire):
 Patch cache2 1 (sub33CCC cache0 cache1 cache2 R Z cs U cin) (sub33CC cache0 cache1 R Z cs U cin):=by
 exact sub3_patch cache0 cache1 cache2 true (U++Z.take 1) (R.take 33) (cs.take 32)
  MixedLiteralAdderDevelop.upper33 cin (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
  (by decide) (by decide) (by decide) (by decide)

theorem sub43CCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2:Wire):
 Patch cache2 1 (sub43CCC cache0 cache1 cache2 R Z cs U cin) (sub43CC cache0 cache1 R Z cs U cin):=by
 exact sub3_patch cache0 cache1 cache2 true (U++Z) (R.take 43) (cs.take 42)
  MixedLiteralAdderDevelop.mask43 cin (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
  (by decide) (by decide) (by decide) (by decide)

theorem fwdCCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2 k:Wire):
 Patch cache2 2 (fwdCCC R S Z cs U cin k cache0 cache1 cache2) (fwdCC R S Z cs U cin k cache0 cache1):=by
 have a:=add3_patch cache0 cache1 cache2 (U++Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
 have kp:=Patch.refl cache2 (WinArith.kpat k Z)
 exact (sub33CCC_patch (cin:=cin) g cache0 cache1 cache2).app
  ((Patch.refl cache2 (copyRegister none ((R.drop 0).take 10) S)).app
   ((Patch.refl cache2 (WinArithAux3SmallDevelop.smallF R S cs cin)).app
    ((Patch.refl cache2 (copyRegister none S ((R.drop 32).take 10))).app
     ((Patch.refl cache2 (copyRegister none ((R.drop 32).take 10) S)).app (kp.app (a.app kp))))))

theorem invCCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2 k:Wire):
 Patch cache2 2 (invCCC R S Z cs U cin k cache0 cache1 cache2) (invCC R S Z cs U cin k cache0 cache1):=by
 have a:=add3_patch cache0 cache1 cache2 (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
 have kp:=Patch.refl cache2 (WinArith.kpat k Z)
 exact kp.app ((sub43CCC_patch (cin:=cin) g cache0 cache1 cache2).app (kp.app
  ((Patch.refl cache2 (copyRegister none ((R.drop 32).take 10) S)).app
   ((Patch.refl cache2 (copyRegister none S ((R.drop 32).take 10))).app
    ((Patch.refl cache2 (WinArithAux3SmallDevelop.smallI R S cs cin)).app
     ((Patch.refl cache2 (copyRegister none ((R.drop 0).take 10) S)).app a))))))

theorem midCCC_patch (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 Patch (host2Wire L) 4
  (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L)++
    (wCoreK L++wInvCCC L (cacheWire L) (hostWire L) (host2Wire L)))
  (wFwdCC L (cacheWire L) (hostWire L)++(wCoreK L++wInvCC L (cacheWire L) (hostWire L))):=
 (fwdCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).app
  ((Patch.refl _ (wCoreK L)).app
   (invCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)))

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem middle_counts (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 toffoliCount (wMidFullCCC L c)+1=toffoliCount (wMidFullCC L) ∧
 measurementCount (wMidFullCCC L c)=measurementCount (wMidFullCC L)+2 ∧
 Challenge.gateSlots (wMidFullCCC L c)=Challenge.gateSlots (wMidFullCC L)+9:=by
 have h:=midCCC_patch L hw
 have ht:=h.t;have hm:=h.m;have hs:=h.slots
 simp only[toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]at ht hm hs
 have prepT (a b c d e f g h i j k l:Wire):toffoliCount (prepare3 a b c d e f g h i j k l)=3:=rfl
 have prepM (a b c d e f g h i j k l:Wire):measurementCount (prepare3 a b c d e f g h i j k l)=2:=rfl
 have prepS (a b c d e f g h i j k l:Wire):Challenge.gateSlots (prepare3 a b c d e f g h i j k l)=30:=by
  simp[prepare3,loan2,SecondCarryLoan.prepare,prime,loan,prime2,majority,Challenge.gateSlots,Challenge.instructionSlots]
 have finT (a b c d e f g h i j k l:Wire):toffoliCount (finish3 a b c d e f g h i j k l)=3:=rfl
 have finM (a b c d e f g h i j k l:Wire):measurementCount (finish3 a b c d e f g h i j k l)=3:=rfl
 have finS (a b c d e f g h i j k l:Wire):Challenge.gateSlots (finish3 a b c d e f g h i j k l)=26:=by
  simp[finish3,SecondCarryLoan.finish,clear2,clear,restore,restore2,Challenge.gateSlots,Challenge.instructionSlots]
 have oldPT (a b c d e f g:Wire):toffoliCount (prepare a b c d e f g)=2:=rfl
 have oldPM (a b c d e f g:Wire):measurementCount (prepare a b c d e f g)=1:=rfl
 have oldPS (a b c d e f g:Wire):Challenge.gateSlots (prepare a b c d e f g)=15:=rfl
 have oldFT (a b c d e f g:Wire):toffoliCount (finish a b c d e f g)=1:=rfl
 have oldFM (a b c d e f g:Wire):measurementCount (finish a b c d e f g)=2:=rfl
 have oldFS (a b c d e f g:Wire):Challenge.gateSlots (finish a b c d e f g)=12:=rfl
 simp only[wMidFullCCC,wMidFullCC,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
  prepT,prepM,prepS,finT,finM,finS,oldPT,oldPM,oldPS,oldFT,oldFM,oldFS]
 exact ⟨by omega,by omega,by omega⟩


end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout ECDSAAdd.RecordedQuantum

theorem host2_not_mem (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 ¬WinArith.Mem (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (host2Wire L):=by
 have ce:=host2_mem L hw
 have cp:=List.count_pos_iff.mpr (eReg_product L _ ce)
 have lc:=layoutCount L hn (host2Wire L)
 intro hm
 rcases hm with hi|hu|hr|hs|hz|hc
 · have cinPos:0<[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
     L.core.modFlag,L.core.sumCarry].count (host2Wire L):=List.count_pos_iff.mpr (by simp[hi])
   omega
 · exact (eReg_away L hn _ ce).2.2 (List.mem_of_mem_drop hu)
 · have :=List.count_pos_iff.mpr (mR_work L _ hr);omega
 · have :=List.count_pos_iff.mpr (mS_pad L _ hs);omega
 · have :=List.count_pos_iff.mpr (mZ_pad L _ hz);omega
 · have :=List.count_pos_iff.mpr (mC_pad L _ hc);omega

theorem ends3_physical (g v u0 u1 u2 r0 r1 r2 e0 cache h1 h2:Wire)
 (nd:[g,v,u0,u1,u2,r0,r1,r2,e0,cache,h1,h2].Nodup):
 GatePhysical (prepare3 g v u0 u1 u2 r0 r1 r2 e0 cache h1 h2) ∧
 GatePhysical (finish3 g v u0 u1 u2 r0 r1 r2 e0 cache h1 h2):=by
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at nd
 simp[prepare3,finish3,loan2,restore2,SecondCarryLoan.prepare,SecondCarryLoan.finish,
  SecondCarryLoan.loan,SecondCarryLoan.restore,prime,prime2,majority,clear,clear2,
  GatePhysical,PhysicalInstr,ProperGate]
 tauto

theorem middle_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (c:Wire) (hc:c∉L.wires):GatePhysical (wMidFullCCC L c):=by
 have hp:=SecondCarryLoan.midCC_physical L hw hn
 simp only[wMidFullCC,gatePhysical_append]at hp
 have geo:=geometry12 L hw hn c hc
 have ne:host2Wire L≠cacheWire L ∧ host2Wire L≠hostWire L:=by
  simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geo
  tauto
 have af:host2Wire L∉wires (wFwdCC L (cacheWire L) (hostWire L)):=by
  intro h
  rcases Finset.mem_insert.mp ((fwdCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).support h)with he|h
  · exact ne.2 he
  rcases Finset.mem_insert.mp ((fwdK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support h)with he|h
  · exact ne.1 he
  rcases WinArith.tFwdK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact host2_not_mem L hw hn hm
  · exact host2_ne_key L hw hn he
 have ai:host2Wire L∉wires (wInvCC L (cacheWire L) (hostWire L)):=by
  intro h
  rcases Finset.mem_insert.mp ((invCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).support h)with he|h
  · exact ne.2 he
  rcases Finset.mem_insert.mp ((invK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support h)with he|h
  · exact ne.1 he
  rcases WinArith.tInvK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact host2_not_mem L hw hn hm
  · exact host2_ne_key L hw hn he
 have pf:=(fwdCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).phys af hp.2.1.1
 have pi:=(invCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).phys ai hp.2.1.2.2
 have ends:=ends3_physical _ _ _ _ _ _ _ _ _ _ _ _ geo
 simp only[wMidFullCCC,gatePhysical_append]
 exact ⟨ends.1,⟨pf,hp.2.1.2.1,pi⟩,ends.2⟩

theorem ends3_support (g v u0 u1 u2 r0 r1 r2 e0 cache h1 h2:Wire):
 wires (prepare3 g v u0 u1 u2 r0 r1 r2 e0 cache h1 h2)⊆[g,v,u0,u1,u2,r0,r1,r2,e0,cache,h1,h2].toFinset ∧
 wires (finish3 g v u0 u1 u2 r0 r1 r2 e0 cache h1 h2)⊆[g,v,u0,u1,u2,r0,r1,r2,e0,cache,h1,h2].toFinset:=by
 constructor <;> intro q h <;>
  simp[prepare3,finish3,loan2,restore2,SecondCarryLoan.prepare,SecondCarryLoan.finish,
   SecondCarryLoan.loan,SecondCarryLoan.restore,prime,prime2,majority,clear,clear2,
   ECDSAAdd.wires,Instr.wires,correctionWires]at h ⊢ <;> tauto

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem armsCCC_oldE (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 wires (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L))⊆oldE L ∧
 wires (wInvCCC L (cacheWire L) (hostWire L) (host2Wire L))⊆oldE L:=by
 have hh:host2Wire L∈oldE L:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inr (Or.inl (host2_mem L hw)))))
 have f:=(fwdCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).support
 have i:=(invCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).support
 constructor
 · intro q h;rcases Finset.mem_insert.mp (f h)with e|h
   · exact e ▸ hh
   · exact (armsCC_oldE L hw).1 h
 · intro q h;rcases Finset.mem_insert.mp (i h)with e|h
   · exact e ▸ hh
   · exact (armsCC_oldE L hw).2 h

theorem ends3_oldE (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g v:Wire):
 wires (prepare3 g v ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L))⊆insert g (insert v (oldE L)) ∧
 wires (finish3 g v ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L))⊆insert g (insert v (oldE L)):=by
 have lens:=mLens L hw
 have uMem (q:Wire) (h:q∈mU L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inl (List.mem_of_mem_drop h)))
 have rMem (q:Wire) (h:q∈mR L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h))))
 have eMem (q:Wire) (h:q∈eReg L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inr (Or.inr (Or.inl h))))
 have hu0:=uMem _ (head_mem _ (by rw[lens.u];decide))
 have hu1:=uMem _ (bit1_mem _ (by rw[lens.u];decide))
 have hu2:=uMem _ (bit2_mem _ (by rw[lens.u];decide))
 have hr0:=rMem _ (head_mem _ (by rw[lens.r];decide))
 have hr1:=rMem _ (bit1_mem _ (by rw[lens.r];decide))
 have hr2:=rMem _ (bit2_mem _ (by rw[lens.r];decide))
 have he0:=eMem _ (head_mem _ (by simp[eReg_length L hw]))
 have hcache:=eMem _ (cache_mem L hw)
 have hh1:=eMem _ (host_mem L hw)
 have hh2:=eMem _ (host2_mem L hw)
 have carrier:([g,v,(mU L).headD 0,bit1 (mU L),bit2 (mU L),
    (mR L).headD 0,bit1 (mR L),bit2 (mR L),(eReg L).headD 0,
    cacheWire L,hostWire L,host2Wire L]:List Wire).toFinset⊆insert g (insert v (oldE L)):=by
  intro q h
  simp only[List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
   simp only[Finset.mem_insert] <;> tauto
 have cap:=ends3_support g v ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L))
   ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) ((eReg L).headD 0)
   (cacheWire L) (hostWire L) (host2Wire L)
 exact ⟨cap.1.trans carrier,cap.2.trans carrier⟩

end ECDSAAdd.Entrant.ThirdCarryLoanDevelop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ParkCarry8Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ParkCarry7Develop

theorem sourceHigh_in_y (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 bit1 L.core.high∈L.core.y:=by
 have h:=bit1_mem L.core.high (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
 exact List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem mid_sumCarry_free (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (c:Wire) (hc:c∉L.wires):L.core.sumCarry∉wires (wMidFullCCC L c):=by
 have oe:=ParkCarry7Develop.oldE_sumCarry_free L hw hn c hc
 have ng:L.core.sumCarry≠c:=by
  intro h;apply hc
  simp[←h,CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
 have nv:L.core.sumCarry≠bit1 L.core.high:=by
  intro h
  apply ParkCarryDevelop.sumCarry_away L hn
  have vy:=sourceHigh_in_y L hw
  rw[←h]at vy
  simp[ParkCarryDevelop.restWires,vy]
 have ends:=ends3_oldE L hw c (bit1 L.core.high)
 have arms:=armsCCC_oldE L hw
 have co:L.core.sumCarry∉wires (wCoreK L):=by
  have off:=(b_wloop_sumCarry_free L hw hn c hc).2.1
  simp only[wires_append,Finset.mem_union,not_or]at off
  exact off.2.1
 have erase {P:Program}(sub:wires P⊆insert c (insert (bit1 L.core.high) (oldE L))):L.core.sumCarry∉wires P:=by
  intro h
  rcases Finset.mem_insert.mp (sub h)with e|h
  · exact ng e
  rcases Finset.mem_insert.mp h with e|h
  · exact nv e
  · exact oe h
 intro h
 simp only[wMidFullCCC,wires_append,Finset.mem_union]at h
 rcases h with h|((h|(h|h))|h)
 · exact erase ends.1 h
 · exact oe (arms.1 h)
 · exact co h
 · exact oe (arms.2 h)
 · exact erase ends.2 h

def fold (L:CuccaroStreamedSquareWideLayout) (c:Wire):Program:=
 eAddLo L++(buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
  (wMidFullCCC L c++(unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
   (ParkCarryDevelop.program (eU L) L.core.sumCarry++eSubK L))))
def rebuild (L:CuccaroStreamedSquareWideLayout):Program:=eAddB L++(restore L++padM L 746)
def body (L:CuccaroStreamedSquareWideLayout)(c:Wire):Program:=
 measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(fold L c++(eFoldTq L c++rebuild L)))

theorem body_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) (hSource:M=if base c then regValue L.core.high base else 0) :
    Triple (SquareFrame L.core.out base O) (body L c) (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let P := M^2
  let b0 := P%2^128
  let b1 := P/2^128
  let W := 4294968272*b1
  let g := base c
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have hb1lt : b1<2^128 := by
    show P/2^128<2^128
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hWlt : W<2^163 := by
    show 4294968272*b1<2^163
    norm_num at hb1lt ⊢
    omega
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
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
  have e0 : regValue (eReg L) base=b0 := eReg_value L hw base P hP hb
  have a0 : regValue (accReg L) base=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (accReg_work L q hq))
  have hb1 : regValue (hiReg L) base=b1 := by
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have conv1 : ∀s,SquareFrame L.core.out base O2 s → BState L base O2 b0 0 s := by
    intro s hs
    refine ⟨hs.1,?_,?_,fun q h1 _ _ => hs.2 q h1⟩
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (eReg_away L hn q hq).1)).trans e0
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (accReg_out L hn q hq))).trans a0


  let u := b1/2^96
  let d := W/2^128 - u
  let H := b0/2^32
  let l' := (b0%2^32 + u)%2^32
  let K := (b0%2^32 + u)/2^32
  let O3 := ((u + 4294968273*d) + 4294968272*2^32*K + 2^128*(W%2^128) + (SquareReduction.p-1-O2)) % SquareReduction.p
  let E1 := (2^32*H + l' + 2^130 - b1) % 2^130
  let O4 := (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
  have hu32 : u < 2^32 := by
    show b1/2^96 < 2^32
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc b1<2^128 := hb1lt
      _ = 2^32*2^96 := by norm_num
  have hH : H < 2^96 := by show b0/2^32 < 2^96; omega
  have hl' : l' < 2^32 := Nat.mod_lt _ (by positivity)
  have hK : K ≤ 1 := by show (b0%2^32 + u)/2^32 ≤ 1; omega
  have hKif : (if l' < u then 1 else 0) = K := by
    show (if (b0%2^32 + u)%2^32 < u then 1 else 0) = (b0%2^32 + u)/2^32
    by_cases hc' : (b0%2^32 + u)%2^32 < u
    · rw [if_pos hc']; omega
    · rw [if_neg hc']; omega
  let kap:Bool:=decide (K=1)
  let baseK:=writeBit base L.core.sumCarry kap
  have kapNat:kap.toNat=K := by
    have kk:K=0 ∨ K=1 := by omega
    rcases kk with kk|kk <;> simp [kap,kk]
  have hcK:L.PairClean baseK := base_clean L hn base hc kap
  have productOff:L.core.sumCarry∉L.core.product := by
    intro h;apply sumCarry_away L hn;simp [restWires,h]
  have highOff:L.core.sumCarry∉hiReg L := by
    intro h;exact productOff (List.mem_of_mem_take (List.mem_of_mem_drop h))
  have hb1K:regValue (hiReg L) baseK=b1 := by
    dsimp only [baseK]
    rw [reg_update_off _ _ _ _ highOff]
    exact hb1
  have cq:c≠L.core.sumCarry := by
    intro h;apply hcw
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
  have gc:baseK c=base c := by simp [baseK,writeBit,cq]
  have resetBase:writeBit baseK L.core.sumCarry false=base := by
    funext q
    by_cases hq:q=L.core.sumCarry
    · subst q;simp [writeBit,Function.update,hsum]
    · simp [baseK,writeBit,Function.update,hq]
  -- Park the completed low-window carry instead of recomputing it.
  have k1 := eAddLo_step L hw hn base hc O2 0 b0 hb0
  rw [hb1] at k1
  have squareBit : (b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw[Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have loanFact : ((2^32*H+l'+2^128*K)/2%2==1)=
      ((b1/2^96/2%2==1) ^^ (b1/2^96%2==1) ^^
        ((b1/2^96%2==1)&&((2^32*H+l'+2^128*K)%2==1))) := by
    have low0:(2^32*H+l'+2^128*K)%2=(b0%2^32+u)%2:=by dsimp[l'];omega
    have low1:(2^32*H+l'+2^128*K)/2%2=(b0%2^32+u)/2%2:=by dsimp[l'];omega
    rw[low0,low1]
    exact known_second_loan (b0%2^32) u squareBit
  let originalM:=regValue L.core.high base
  have source1:base (bit1 L.core.high)=digit originalM 1:=by
    simpa only[digit,pow_one]using bit1_parity L.core.high base
      (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
  have modE:(2^32*H+l'+2^128*K)%16=lowSum (base c) originalM u%16:=by
    rw[lowSum,←hSource]
    exact folded_low_mod16 M u H l' K rfl rfl
  have loanFact2:=loan2_from_mod16 (base c) originalM u (2^32*H+l'+2^128*K) modE
  rw[←source1]at loanFact2
  have wm := wMidFullCCC_step L hw hn c hcw base hc O2 (2^32*H+l'+2^128*K) b1 hb1 hb1lt hO2
    H l' K hH hl' hK rfl loanFact loanFact2
  have wmBase : Triple (BState L base O2 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base))
      (wMidFullCCC L c)
      (BState L base O3 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base)) := by
    simpa only [hb1] using wm
  have off:=b_wloop_sumCarry_free L hw hn c hcw
  have loop:=cached_wloop_bstate_step L hw hn base hc hsum O2 (2^32*H+l'+2^128*K) O3
    (wMidFullCCC L c) wmBase off.1 (mid_sumCarry_free L hw hn c hcw) off.2.2
  have kc:=park_step L hw hn base hsum O3 (2^32*H+l') 0 (by omega) kap
  rw [kapNat] at kc
  have w3 := eSubK_step L hw hn baseK hcK O3 (2^32*H + l') 0 b1 (by omega) hb1K
  have tw : Triple (BState L base O2 b0 0) (fold L c) (BState L baseK O3 E1 0) :=
    by simpa only [fold,List.append_assoc] using k1.seq (loop.seq (kc.seq w3))
  -- eFoldTq
  have f1 := eFlip_step L hw hn baseK c hcw O3 E1 0
  have f2 := eCore_stepTq L hw hn baseK hcK O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn baseK c hcw O4 (flipE g E1) 0
  rw [gc] at f1 f3
  rw [flipE_flipE] at f3
  have tf : Triple (BState L baseK O3 E1 0) (eFoldTq L c) (BState L baseK O4 E1 0) :=
    f1.seq (f2.seq f3)
  -- wRestoreT
  have bk : (E1+b1)%2^130 = 2^32*H + l' := by show ((2^32*H + l' + 2^130 - b1) % 2^130 + b1) % 2^130 = _; omega
  have r2 := eAddB_step L hw hn baseK hcK O4 E1 0 b1 hb1K (by rw [bk]; omega)
  rw [bk] at r2
  have bit32:(b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw [Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have total:l'+2^32*(baseK L.core.sumCarry).toNat=b0%2^32+regValue (hiReg L) baseK/2^96 := by
    have atq:baseK L.core.sumCarry=kap := by simp [baseK,writeBit]
    rw [atq,kapNat,hb1K]
    show ((b0%2^32+u)%2^32)+2^32*((b0%2^32+u)/2^32)=b0%2^32+u
    exact Nat.mod_add_div _ _
  have r3:=restore_step L hw hn baseK hcK O4 0 H l' (b0%2^32) hH hl'
    (Nat.mod_lt _ (by positivity)) bit32 total
  have bb:2^32*H+b0%2^32=b0 := by dsimp [H];omega
  rw [resetBase,bb] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 746
  have tr : Triple (BState L baseK O4 E1 0) (rebuild L) (BState L base O4 b0 0) :=
    r2.seq (r3.seq rp)
  have conv2 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
    intro s hs
    refine ⟨hs.1,fun q hq => ?_⟩
    by_cases he : q∈eReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.1.trans e0.symm) q he
    by_cases ha : q∈accReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.2.1.trans a0.symm) q ha
    exact hs.2.2.2 q hq he ha
  have key : O4 = bO4 (M^2) (base c) O := by
    have hg' : g = false → b1 = 0 ∧ b0 = 0 := by
      intro h0
      have : M = 0 := hg h0
      subst this
      simp [b1, b0, P]
    have e3 : O3 = (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p := by
      simp only [O3, u, d, K, W]
      congr 1; ring
    have e4 : O4 = (4294968272*flipE g ((2^32*(b0/2^32) + (b0%2^32+b1/2^96)%2^32 + 2^130 - b1) % 2^130) +
        (SquareReduction.p-1-((((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p))) % SquareReduction.p := by
      show (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p = _
      rw [e3]
    rw [e4, o4K b0 b1 O2 _ g hb0 hb1lt hO2 hg']
    exact o4_eq b0 b1 O2 g hb0 hb1lt hO2 hg'
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tf.seq tr)) conv2))
  rw [key] at all
  exact all

end ECDSAAdd.Entrant.ParkCarry8Develop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ParkCarry8Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop

def midV (L:CuccaroStreamedSquareWideLayout) (c v:Wire):Program:=
 prepare3 c v ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L)++
 ((wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L)++
   (wCoreK L++wInvCCC L (cacheWire L) (hostWire L) (host2Wire L)))++
  finish3 c v ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L))
   ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) ((eReg L).headD 0)
   (cacheWire L) (hostWire L) (host2Wire L))
def foldV (L:CuccaroStreamedSquareWideLayout)(c v:Wire):Program:=
 eAddLo L++(buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
  (midV L c v++(unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
   (ParkCarryDevelop.program (eU L) L.core.sumCarry++eSubK L))))
def bodyV (L:CuccaroStreamedSquareWideLayout)(c v:Wire):Program:=
 measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(foldV L c v++(eFoldTq L c++rebuild L)))
theorem bodyV_eq (L:CuccaroStreamedSquareWideLayout)(c:Wire):bodyV L c (bit1 L.core.high)=body L c:=rfl

theorem body_counts (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 toffoliCount (body L c)=4764 ∧ measurementCount (body L c)=5924:=by
 have base:=ParkCarry7Develop.body_counts L hw c
 have mid:=middle_counts L hw c
 have p:=padM_counts L 746
 have q:=padM_counts L 748
 simp only[body,fold,rebuild,ParkCarry7Develop.body,ParkCarry7Develop.fold,ParkCarry7Develop.rebuild,
  toffoliCount_append,measurementCount_append]at base ⊢
 exact ⟨by omega,by omega⟩

theorem body_slots (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 Challenge.gateSlots (body L c)=Challenge.gateSlots (ParkCarry7Develop.body L c)+7:=by
 have mid:=(middle_counts L hw c).2.2
 have p:=padM_slots L 746
 have q:=padM_slots L 748
 simp only[body,fold,rebuild,ParkCarry7Develop.body,ParkCarry7Develop.fold,ParkCarry7Develop.rebuild,
  Challenge.gateSlots_append]
 omega

theorem body_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire)
 (hn:(c::L.wires).Nodup):GatePhysical (body L c):=by
 have hp:=ParkCarry7Develop.body_physical L hw c hn
 have nd:=(List.nodup_cons.mp hn).2
 have mid:=middle_physical L hw nd c (List.nodup_cons.mp hn).1
 have pad:=padM_physical L 746
 simp only[ParkCarry7Develop.body,ParkCarry7Develop.fold,ParkCarry7Develop.rebuild,gatePhysical_append]at hp
 simp only[body,fold,rebuild,gatePhysical_append]
 tauto

end ECDSAAdd.Entrant.ParkCarry8Develop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ParkCarry8Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop

theorem midV_counts (L:CuccaroStreamedSquareWideLayout)(c v:Wire):
 toffoliCount (midV L c v)=toffoliCount (wMidFullCCC L c) ∧
 measurementCount (midV L c v)=measurementCount (wMidFullCCC L c) ∧
 Challenge.gateSlots (midV L c v)=Challenge.gateSlots (wMidFullCCC L c):=by
 simp[midV,wMidFullCCC,prepare3,finish3,loan2,restore2,SecondCarryLoan.prepare,SecondCarryLoan.finish,
  SecondCarryLoan.loan,SecondCarryLoan.restore,prime,prime2,majority,clear,clear2,
  toffoliCount,measurementCount,Challenge.gateSlots,Challenge.instructionSlots]

theorem bodyV_counts (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)(c v:Wire):
 toffoliCount (bodyV L c v)=4764 ∧ measurementCount (bodyV L c v)=5924:=by
 have h:=body_counts L hw c
 have m:=midV_counts L c v
 simp only[bodyV,foldV,body,fold,toffoliCount_append,measurementCount_append]at h ⊢
 exact ⟨by omega,by omega⟩
theorem bodyV_slots (L:CuccaroStreamedSquareWideLayout)(c v:Wire):
 Challenge.gateSlots (bodyV L c v)=Challenge.gateSlots (body L c):=by
 have m:=(midV_counts L c v).2.2
 simp only[bodyV,foldV,body,fold,Challenge.gateSlots_append]
 omega

theorem oldE_in_oldBody (L:CuccaroStreamedSquareWideLayout)(c:Wire):oldE L⊆wires (bBody L c):=by
 intro q h
 simp only[oldE,Finset.mem_union]at h
 simp only[bBody,wFold,wRestore,wires_append,Finset.mem_union]
 tauto

theorem control_in_oldBody (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)(c:Wire):c∈wires (bBody L c):=by
 have len:eReg L≠[]:=by have h:=eReg_length L hw;intro e;rw[e]at h;contradiction
 obtain ⟨q,qs,hq⟩:=List.exists_cons_of_ne_nil len
 simp [bBody,eFold,eFlip,flipE,notRegister,maskedConstant,hq,wires_append,ECDSAAdd.wires,Instr.wires]

end ECDSAAdd.Entrant.ParkCarry8Develop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ParkCarry8Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop

theorem bodyV_support_extra (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)(c v:Wire):
 wires (bodyV L c v)⊆insert L.core.sumCarry (insert v (wires (bBody L c))):=by
 have old:=(ParkCarry7Develop.body_le_extra L hw c).1
 have same {P:Program}(hP:wires P⊆wires (ParkCarry7Develop.body L c)):
  wires P⊆insert L.core.sumCarry (insert v (wires (bBody L c))):=by
  intro q h
  rcases Finset.mem_insert.mp (old (hP h))with e|h
  · exact Finset.mem_insert.mpr (Or.inl e)
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
 have oldEmbed {P:Program}(hP:wires P⊆oldE L):
  wires P⊆insert L.core.sumCarry (insert v (wires (bBody L c))):=by
  intro q h;exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (oldE_in_oldBody L c (hP h)))
 have ends:=ends3_oldE L hw c v
 have endEmbed {P:Program}(hP:wires P⊆insert c (insert v (oldE L))):
  wires P⊆insert L.core.sumCarry (insert v (wires (bBody L c))):=by
  intro q h
  rcases Finset.mem_insert.mp (hP h)with e|h
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (e ▸ control_in_oldBody L hw c))
  rcases Finset.mem_insert.mp h with e|h
  · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e))
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (oldE_in_oldBody L c h))
 have mid:wires (midV L c v)⊆insert L.core.sumCarry (insert v (wires (bBody L c))):=by
  intro q h
  simp only[midV,wires_append,Finset.mem_union,or_assoc]at h
  rcases h with h|h|h|h|h
  · exact endEmbed ends.1 h
  · exact oldEmbed (armsCCC_oldE L hw).1 h
  · exact same (P:=wCoreK L) (by intro q h;simp only[ParkCarry7Develop.body,ParkCarry7Develop.fold,
      SecondCarryLoan.wMidFullCC,wires_append,Finset.mem_union];tauto) h
  · exact oldEmbed (armsCCC_oldE L hw).2 h
  · exact endEmbed ends.2 h
 intro q h
 simp only[bodyV,foldV,rebuild,wires_append,Finset.mem_union,or_assoc]at h
 rcases h with h|h|h|h|h|h|h|h|h|h|h|h
 · exact same (P:=measuredFoldQTq L (negP L)) (by intro q h;simp only[ParkCarry7Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=measuredFoldQTq L (rot128F L)) (by intro q h;simp only[ParkCarry7Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eAddLo L) (by intro q h;simp only[ParkCarry7Develop.body,ParkCarry7Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) (by intro q h;simp only[ParkCarry7Develop.body,ParkCarry7Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact mid h
 · exact same (P:=unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) (by intro q h;simp only[ParkCarry7Develop.body,ParkCarry7Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=ParkCarryDevelop.program (eU L) L.core.sumCarry) (by intro q h;simp only[ParkCarry7Develop.body,ParkCarry7Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eSubK L) (by intro q h;simp only[ParkCarry7Develop.body,ParkCarry7Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eFoldTq L c) (by intro q h;simp only[ParkCarry7Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eAddB L) (by intro q h;simp only[ParkCarry7Develop.body,ParkCarry7Develop.rebuild,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=restore L) (by intro q h;simp only[ParkCarry7Develop.body,ParkCarry7Develop.rebuild,wires_append,Finset.mem_union];tauto) h
 · exact oldEmbed (padM_oldE L hw 746) h

end ECDSAAdd.Entrant.ParkCarry8Develop


open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ParkCarry8Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop

theorem bodyV_rel (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)(c v:Wire):
 toffoliCount (bodyV L c v)+1059=toffoliCount (bBody L c) ∧
 measurementCount (bodyV L c v)+4=measurementCount (bBody L c) ∧
 ExtraLeTwo L.core.sumCarry v (bodyV L c v) (bBody L c):=by
 have new:=bodyV_counts L hw c v
 have old:=ParkCarry7Develop.body_rel L hw c
 have bc:=ParkCarry7Develop.body_counts L hw c
 have slots:=bodyV_slots L c v
 have ds:=body_slots L hw c
 have gs:=ParkCarry7Develop.body_slots L hw c
 have ceiling:=(ParkCarryDevelop.body_le_extra L hw c).2
 exact ⟨by omega,by omega,bodyV_support_extra L hw c v,by omega⟩

def hostedBody (L:CuccaroStreamedSquareWideLayout)(rho:Equiv.Perm Wire)(c:Wire):Program:=
 bodyV (hostLayout L rho) c (rho.symm (bit1 L.core.high))

theorem hosted_rel (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)(rho:Equiv.Perm Wire)(c:Wire):
 toffoliCount (hostedBody L rho c)+1059=toffoliCount (bBody L c) ∧
 measurementCount (hostedBody L rho c)+4=measurementCount (bBody L c) ∧
 ExtraLeTwo (rho.symm L.core.sumCarry) (rho.symm (bit1 L.core.high)) (hostedBody L rho c) (bBody L c):=by
 have h:=bodyV_rel (hostLayout L rho) (host_widths L hw rho) c (rho.symm (bit1 L.core.high))
 simpa only[hostedBody,ParkCarryDevelop.oldBody_host,ParkCarryDevelop.hostLayout]using h

theorem hosted_eq (L:CuccaroStreamedSquareWideLayout)(rho:Equiv.Perm Wire)(c:Wire)
 (h:rho L.core.sumCarry=L.core.sumCarry)(hv:rho (bit1 L.core.high)=bit1 L.core.high):
 hostedBody L rho c=body L c:=by
 have iv:rho.symm (bit1 L.core.high)=bit1 L.core.high:=by
  apply rho.injective
  simp only[Equiv.apply_symm_apply]
  exact hv.symm
 rw[hostedBody,ParkCarryDevelop.host_eq L rho h,iv,bodyV_eq]

theorem body_support (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)(hn:L.wires.Nodup)(c:Wire):
 wires (body L c)⊆(c::L.wires).toFinset:=by
 have h:=bodyV_support_extra L hw c (bit1 L.core.high)
 rw[bodyV_eq]at h
 intro q hq
 rcases Finset.mem_insert.mp (h hq)with e|h
 · rw[e];simp[CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
 rcases Finset.mem_insert.mp h with e|h
 · rw[e];have vy:=sourceHigh_in_y L hw
   simp[CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,vy]
 · exact bBody_support L hw hn c h

theorem hosted_slots (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)(rho:Equiv.Perm Wire)(c:Wire):
 Challenge.gateSlots (hostedBody L rho c)=Challenge.gateSlots (body L c):=by
 have v:=bodyV_slots (hostLayout L rho) c (rho.symm (bit1 L.core.high))
 have a:=body_slots (hostLayout L rho) (host_widths L hw rho) c
 have b:=body_slots L hw c
 have old:=ParkCarry7Develop.hosted_slots L hw rho c
 change Challenge.gateSlots (ParkCarry7Develop.body (hostLayout L rho) c)=Challenge.gateSlots (ParkCarry7Develop.body L c)at old
 change Challenge.gateSlots (bodyV (hostLayout L rho) c (rho.symm (bit1 L.core.high)))=Challenge.gateSlots (body L c)
 omega

theorem hosted_counts (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)(rho:Equiv.Perm Wire)(c:Wire):
 toffoliCount (hostedBody L rho c)=4764 ∧ measurementCount (hostedBody L rho c)=5924:=
 bodyV_counts (hostLayout L rho) (host_widths L hw rho) c (rho.symm (bit1 L.core.high))

end ECDSAAdd.Entrant.ParkCarry8Develop
