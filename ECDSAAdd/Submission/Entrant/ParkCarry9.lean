import ECDSAAdd.Submission.Entrant.ParkCarry8

-- Fourth cached carry extending the published 52bbcfbf third-carry package.

section
-- FourthCarryArithmetic
namespace FourthCarryArithmetic
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def digit (x i : Nat) : Bool := x / 2^i % 2 == 1

def lowSum (g : Bool) (m u : Nat) : Nat := (if g then m else 0)^2+u

theorem finite (g : Bool) (m u : Nat) (hm : m<16) (hu : u<16) :
 digit (lowSum g m u) 3 =
 (digit u 3 ^^ ((digit (lowSum g m u) 0 ^^ digit u 0) && (digit m 1 ^^ digit m 2)) ^^
  (digit u 2 && digit (lowSum g m u) 2) ^^ digit u 2) := by
 interval_cases m <;> interval_cases u <;> cases g <;> decide +kernel

theorem digit_mod16 (x i : Nat) (hi : i≤3) : digit (x%16) i=digit x i := by
 unfold digit
 apply congrArg (fun n : Nat => n == 1)
 interval_cases i <;> norm_num <;> omega

theorem lowSum_mod16 (g : Bool) (m u : Nat) :
 lowSum g (m%16) (u%16)%16=lowSum g m u%16 := by
 cases g <;> simp [lowSum,Nat.add_mod,Nat.pow_mod]

theorem identity (g : Bool) (m u : Nat) :
 digit (lowSum g m u) 3 =
 (digit u 3 ^^ ((digit (lowSum g m u) 0 ^^ digit u 0) && (digit m 1 ^^ digit m 2)) ^^
  (digit u 2 && digit (lowSum g m u) 2) ^^ digit u 2) := by
 have f:=finite g (m%16) (u%16) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
 have es (i : Nat) (hi : i≤3) : digit (lowSum g (m%16) (u%16)) i=digit (lowSum g m u) i := by
  rw [←digit_mod16 _ i hi,lowSum_mod16,digit_mod16 _ i hi]
 simpa only [es 0 (by decide),es 2 (by decide),es 3 (by decide),
  digit_mod16 _ 0 (by decide),digit_mod16 _ 1 (by decide),digit_mod16 _ 2 (by decide),
  digit_mod16 _ 3 (by decide)] using f

#print axioms finite
#print axioms identity
end FourthCarryArithmetic

end -- isolated Carry9 component

section
-- FourthCachedMapped
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def cachedMapped4 (cache0 cache1 cache2 cache3 : Wire) (bits : List MappedBit) (ys cs : List Wire) (cin : Wire) : Program :=
 match bits,ys,cs with
 | b0::b1::b2::b3::b4::bs,y0::y1::y2::y3::y4::ys,k0::k1::k2::k3::ks =>
  [.CX cache0 k0]++cachedMapped3 cache1 cache2 cache3 (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (k1::k2::k3::ks) k0++
   mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin
 | _,_,_=>cachedMapped3 cache0 cache1 cache2 bits ys cs cin

theorem cachedMapped4_eq (cache0 cache1 cache2 cache3 : Wire) (b0 b1 b2 b3 b4 : MappedBit) (bs : List MappedBit)
 (y0 y1 y2 y3 y4 : Wire) (ys : List Wire) (k0 k1 k2 k3 : Wire) (ks : List Wire) (cin : Wire)
 (hn : [y3,k2,k3].Nodup) (ha : ∀q∈b3.wire,q∉[y3,k2,k3]) (s : State) (m : List Bool)
 (ready : (run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis cache3=
  carryBit (b3.value (run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis)
   ((run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis y3)
   ((run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis k2)) :
 run (cachedMapped4 cache0 cache1 cache2 cache3 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin) m s=
 run (cachedMapped3 cache0 cache1 cache2 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin) m s := by
 have hl : cachedMapped4 cache0 cache1 cache2 cache3 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin=
  [.CX cache0 k0]++(cachedMapped3 cache1 cache2 cache3 (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (k1::k2::k3::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only [cachedMapped4,List.append_assoc]
 have hr : cachedMapped3 cache0 cache1 cache2 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin=
  [.CX cache0 k0]++(cachedMapped2 cache1 cache2 (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (k1::k2::k3::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only [cachedMapped3,List.append_assoc]
 rw [hl,hr,prepend_zero [.CX cache0 k0] _ (by rfl),prepend_zero [.CX cache0 k0] _ (by rfl)]
 apply append_equal _ _ _ (cachedMapped3_counts cache1 cache2 cache3 b1 b2 b3 b4 bs y1 y2 y3 y4 ys k1 k2 k3 ks k0).2
 intro r
 exact cachedMapped3_eq cache1 cache2 cache3 b1 b2 b3 b4 bs y1 y2 y3 y4 ys k1 k2 k3 ks k0 hn ha _ r ready

theorem cachedMapped4_counts (cache0 cache1 cache2 cache3 : Wire) (b0 b1 b2 b3 b4 : MappedBit) (bs : List MappedBit)
 (y0 y1 y2 y3 y4 : Wire) (ys : List Wire) (k0 k1 k2 k3 : Wire) (ks : List Wire) (cin : Wire) :
 toffoliCount (cachedMapped4 cache0 cache1 cache2 cache3 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin)+1=
  toffoliCount (cachedMapped3 cache0 cache1 cache2 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin) ∧
 measurementCount (cachedMapped4 cache0 cache1 cache2 cache3 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin)=
  measurementCount (cachedMapped3 cache0 cache1 cache2 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin) := by
 have h:=cachedMapped3_counts cache1 cache2 cache3 b1 b2 b3 b4 bs y1 y2 y3 y4 ys k1 k2 k3 ks k0
 simp only [cachedMapped4,cachedMapped3,toffoliCount_append,measurementCount_append] at *
 exact ⟨by omega,by omega⟩
#print axioms cachedMapped4_eq
#print axioms cachedMapped4_counts
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedMixed
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def cachedMixed4 (cache0 cache1 cache2 cache3 : Wire) (expected : Bool) (bits : List MappedBit) (ys : List Wire) (flags : List Bool) (cs : List Wire) (cin : Wire) : Program :=
 match bits,ys,flags,cs with
 | b0::b1::b2::b3::b4::bs,y0::y1::y2::y3::y4::ys,_::false::false::false::false::fs,k0::k1::k2::k3::ks =>
  [.CX cache0 k0]++cachedMixed3 cache1 cache2 cache3 expected (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (false::false::false::false::fs) (k1::k2::k3::ks) k0++
   mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin
 | _,_,_,_=>cachedMixed3 cache0 cache1 cache2 expected bits ys flags cs cin

theorem cachedMixed4_eq (cache0 cache1 cache2 cache3 : Wire) (expected d : Bool) (b0 b1 b2 b3 b4 : MappedBit) (bs : List MappedBit)
 (y0 y1 y2 y3 y4 : Wire) (ys : List Wire) (fs : List Bool) (k0 k1 k2 k3 : Wire) (ks : List Wire) (cin : Wire)
 (hn : [y3,k2,k3].Nodup) (ha : ∀q∈b3.wire,q∉[y3,k2,k3]) (s : State) (m : List Bool)
 (ready : (run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis cache3=
  carryBit (b3.value (run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis)
   ((run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis y3)
   ((run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis k2)) :
 run (cachedMixed4 cache0 cache1 cache2 cache3 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) m s=
 run (cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) m s := by
 have hl : cachedMixed4 cache0 cache1 cache2 cache3 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin=
  [.CX cache0 k0]++(cachedMixed3 cache1 cache2 cache3 expected (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (false::false::false::false::fs) (k1::k2::k3::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only [cachedMixed4,List.append_assoc]
 have hr : cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin=
  [.CX cache0 k0]++(cachedMixed2 cache1 cache2 expected (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (false::false::false::false::fs) (k1::k2::k3::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only [cachedMixed3,List.append_assoc]
 rw [hl,hr,prepend_zero [.CX cache0 k0] _ (by rfl),prepend_zero [.CX cache0 k0] _ (by rfl)]
 apply append_equal _ _ _ (cachedMixed3_counts cache1 cache2 cache3 expected false b1 b2 b3 b4 bs y1 y2 y3 y4 ys fs k1 k2 k3 ks k0).2
 intro r
 exact cachedMixed3_eq cache1 cache2 cache3 expected false b1 b2 b3 b4 bs y1 y2 y3 y4 ys fs k1 k2 k3 ks k0 hn ha _ r ready

theorem cachedMixed4_counts (cache0 cache1 cache2 cache3 : Wire) (expected d : Bool) (b0 b1 b2 b3 b4 : MappedBit) (bs : List MappedBit)
 (y0 y1 y2 y3 y4 : Wire) (ys : List Wire) (fs : List Bool) (k0 k1 k2 k3 : Wire) (ks : List Wire) (cin : Wire) :
 toffoliCount (cachedMixed4 cache0 cache1 cache2 cache3 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin)+1=
  toffoliCount (cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) ∧
 measurementCount (cachedMixed4 cache0 cache1 cache2 cache3 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin)=
  measurementCount (cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) := by
 have h:=cachedMixed3_counts cache1 cache2 cache3 expected false b1 b2 b3 b4 bs y1 y2 y3 y4 ys fs k1 k2 k3 ks k0
 simp only [cachedMixed4,cachedMixed3,toffoliCount_append,measurementCount_append] at *
 exact ⟨by omega,by omega⟩
#print axioms cachedMixed4_eq
#print axioms cachedMixed4_counts
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedRead
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def bit3 (xs : List Wire) : Wire := (xs.drop 3).headD 0

theorem split_five {α : Type} (xs : List α) (h : 5 ≤ xs.length) :
 ∃ a b c d e rest, xs = a::b::c::d::e::rest := by
 obtain ⟨a,b,c,d,rest,rfl⟩ := split_four xs (by omega)
 obtain ⟨e,rest,rfl⟩ := split_one rest (by simpa using h)
 exact ⟨a,b,c,d,e,rest,rfl⟩

theorem fourth_geometry (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin : Wire) (xs ys ks : List Wire)
 (nd : (cin::(a0::a1::a2::a3::a4::xs)++(b0::b1::b2::b3::b4::ys)++(k0::k1::k2::k3::ks)).Nodup) :
 [a3,b3,k0,k1,k2,k3].Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have h := List.nodup_iff_count_le_one.mp nd q
 simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
 omega

theorem mapped4_read_eq (cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin : Wire)
 (xs ys ks : List Wire) 
 (nd : (cin::(a0::a1::a2::a3::a4::xs)++(b0::b1::b2::b3::b4::ys)++(k0::k1::k2::k3::ks)).Nodup)
 (away20 : cache2 ≠ k0) (away21 : cache2 ≠ k1)
 (away30 : cache3 ≠ k0) (away31 : cache3 ≠ k1) (away32 : cache3 ≠ k2)
 (s : State) (m : List Bool) (hi : s.basis k2 = false)
 (hk : s.basis cache3 = carryBit (s.basis a3) (s.basis b3) (s.basis cache2)) :
 run (cachedMapped4 cache0 cache1 cache2 cache3 (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (b0::b1::b2::b3::b4::ys) (k0::k1::k2::k3::ks) cin) m s=
 run (cachedMapped3 cache0 cache1 cache2 (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (b0::b1::b2::b3::b4::ys) (k0::k1::k2::k3::ks) cin) m s := by
 have hg := fourth_geometry a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin xs ys ks nd
 have hn : [b3,k2,k3].Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hg q
  simp only [List.count_cons,List.count_nil] at h ⊢
  omega
 have ha : a3 ∉ [b3,k2,k3] := by
  have h := List.nodup_cons.mp hg
  intro bad
  apply h.1
  simp only [List.mem_cons,List.mem_singleton] at bad ⊢
  tauto
 apply cachedMapped4_eq cache0 cache1 cache2 cache3 ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩ ⟨some a3,false⟩ ⟨some a4,false⟩
  (mappedRead xs false) b0 b1 b2 b3 b4 ys k0 k1 k2 k3 ks cin hn (by simpa using ha) s m
 simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
  not_false_eq_true,not_or,ne_eq,and_true] at hg
 have hax : a3 ≠ k0 ∧ a3 ≠ k1 ∧ a3 ≠ k2 ∧ b3 ≠ k0 ∧ b3 ≠ k1 ∧ b3 ≠ k2 ∧ k2 ≠ k0 ∧ k2 ≠ k1 := by aesop
 rcases hax with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
 simpa [MappedBit.value,run,writeBit,Function.update_apply,away20,away21,away30,away31,away32,
  h0,h1,h2,h3,h4,h5,h6,h7,hi] using hk
#print axioms mapped4_read_eq

theorem mixed4_read_eq (cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin : Wire)
 (expected d : Bool) (xs ys ks : List Wire) (fs : List Bool) 
 (nd : (cin::(a0::a1::a2::a3::a4::xs)++(b0::b1::b2::b3::b4::ys)++(k0::k1::k2::k3::ks)).Nodup)
 (away20 : cache2 ≠ k0) (away21 : cache2 ≠ k1)
 (away30 : cache3 ≠ k0) (away31 : cache3 ≠ k1) (away32 : cache3 ≠ k2)
 (s : State) (m : List Bool) (hi : s.basis k2 = false)
 (hk : s.basis cache3 = carryBit (s.basis a3) (s.basis b3) (s.basis cache2)) :
 run (cachedMixed4 cache0 cache1 cache2 cache3 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (b0::b1::b2::b3::b4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) m s=
 run (cachedMixed3 cache0 cache1 cache2 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (b0::b1::b2::b3::b4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) m s := by
 have hg := fourth_geometry a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin xs ys ks nd
 have hn : [b3,k2,k3].Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hg q
  simp only [List.count_cons,List.count_nil] at h ⊢
  omega
 have ha : a3 ∉ [b3,k2,k3] := by
  have h := List.nodup_cons.mp hg
  intro bad
  apply h.1
  simp only [List.mem_cons,List.mem_singleton] at bad ⊢
  tauto
 apply cachedMixed4_eq cache0 cache1 cache2 cache3 expected d ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩ ⟨some a3,false⟩ ⟨some a4,false⟩
  (mappedRead xs false) b0 b1 b2 b3 b4 ys fs k0 k1 k2 k3 ks cin hn (by simpa using ha) s m
 simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
  not_false_eq_true,not_or,ne_eq,and_true] at hg
 have hax : a3 ≠ k0 ∧ a3 ≠ k1 ∧ a3 ≠ k2 ∧ b3 ≠ k0 ∧ b3 ≠ k1 ∧ b3 ≠ k2 ∧ k2 ≠ k0 ∧ k2 ≠ k1 := by aesop
 rcases hax with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
 simpa [MappedBit.value,run,writeBit,Function.update_apply,away20,away21,away30,away31,away32,
  h0,h1,h2,h3,h4,h5,h6,h7,hi] using hk
#print axioms mixed4_read_eq
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedSub
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def cachedSub4 (cache0 cache1 cache2 cache3 : Wire) (expected : Bool) (bits : List MappedBit) (flags : List Bool)
 (ys cs : List Wire) (cin : Wire) : Program :=
 notRegister ys ++ cachedMixed4 cache0 cache1 cache2 cache3 expected bits ys flags cs cin ++ notRegister ys

theorem sub4_read_eq (cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin : Wire)
 (expected d : Bool) (xs ys ks : List Wire) (fs : List Bool)
 (nd : (cin::(a0::a1::a2::a3::a4::xs)++(b0::b1::b2::b3::b4::ys)++(k0::k1::k2::k3::ks)).Nodup)
 (away2 : cache2 ∉ b0::b1::b2::b3::b4::ys) (away3 : cache3 ∉ b0::b1::b2::b3::b4::ys)
 (away20 : cache2 ≠ k0) (away21 : cache2 ≠ k1)
 (away30 : cache3 ≠ k0) (away31 : cache3 ≠ k1) (away32 : cache3 ≠ k2)
 (s : State) (m : List Bool) (hi : s.basis k2 = false)
 (hk : s.basis cache3 = carryBit (s.basis a3) (!s.basis b3) (s.basis cache2)) :
 run (cachedSub4 cache0 cache1 cache2 cache3 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (d::false::false::false::false::fs) (b0::b1::b2::b3::b4::ys) (k0::k1::k2::k3::ks) cin) m s =
 run (cachedSub3 cache0 cache1 cache2 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (d::false::false::false::false::fs) (b0::b1::b2::b3::b4::ys) (k0::k1::k2::k3::ks) cin) m s := by
 have geo := MixedLiteralAdderDevelop.read_geometry (a0::a1::a2::a3::a4::xs) (b0::b1::b2::b3::b4::ys) (k0::k1::k2::k3::ks) cin nd
 have hnd : (b0::b1::b2::b3::b4::ys).Nodup := (List.nodup_append.mp (List.nodup_cons.mp geo.1).2).1
 have hay : a3 ∉ b0::b1::b2::b3::b4::ys := by
  intro h; exact geo.2 a3 (by simp) (List.mem_cons_of_mem _ (List.mem_append_left _ h))
 have hcy : k2 ∉ b0::b1::b2::b3::b4::ys := by
  intro bad
  have hn := List.nodup_append.mp (List.nodup_cons.mp geo.1).2
  exact hn.2.2 k2 bad k2 (by simp) rfl
 have h : ∀ r, run (cachedMixed4 cache0 cache1 cache2 cache3 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
   (b0::b1::b2::b3::b4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) r
   (run (notRegister (b0::b1::b2::b3::b4::ys)) [] s) =
  run (cachedMixed3 cache0 cache1 cache2 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
   (b0::b1::b2::b3::b4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) r
   (run (notRegister (b0::b1::b2::b3::b4::ys)) [] s) := by
  intro r
  apply mixed4_read_eq cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin
   expected d xs ys ks fs nd away20 away21 away30 away31 away32 _ r
  · rw [notRegister_correct _ hnd]; simpa [hcy] using hi
  · rw [notRegister_correct _ hnd]; simpa [hay,away2,away3] using hk
 have hm := (cachedMixed4_counts cache0 cache1 cache2 cache3 expected d
   ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩ ⟨some a3,false⟩ ⟨some a4,false⟩
   (mappedRead xs false) b0 b1 b2 b3 b4 ys fs k0 k1 k2 k3 ks cin).2
 simp only [cachedSub4,cachedSub3,List.append_assoc]
 rw [prepend_zero (notRegister _) _ ((notRegister_counts _).2),prepend_zero (notRegister _) _ ((notRegister_counts _).2)]
 exact append_equal _ _ _ hm _ m h
#print axioms sub4_read_eq
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedGeneral
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem mapped4_read_general (cache0 cache1 cache2 cache3 : Wire) (x y cs : List Wire) (cin : Wire)
 (nd : (cin::x++y++cs).Nodup) (hx : 5 ≤ x.length) (hy : 5 ≤ y.length) (hc : 4 ≤ cs.length)
 (away2 : cache2 ∉ cs) (away3 : cache3 ∉ cs) (s : State) (m : List Bool)
 (hi : s.basis (bit2 cs) = false)
 (hk : s.basis cache3 = carryBit (s.basis (bit3 x)) (s.basis (bit3 y)) (s.basis cache2)) :
 run (cachedMapped4 cache0 cache1 cache2 cache3 (mappedRead x false) y cs cin) m s =
 run (cachedMapped3 cache0 cache1 cache2 (mappedRead x false) y cs cin) m s := by
 obtain ⟨a0,a1,a2,a3,a4,xs,rfl⟩ := split_five x hx
 obtain ⟨b0,b1,b2,b3,b4,ys,rfl⟩ := split_five y hy
 obtain ⟨k0,k1,k2,k3,ks,rfl⟩ := split_four cs hc
 apply mapped4_read_eq cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin xs ys ks nd
  (by intro he; apply away2; simp [he]) (by intro he; apply away2; simp [he])
  (by intro he; apply away3; simp [he]) (by intro he; apply away3; simp [he])
  (by intro he; apply away3; simp [he]) s m (by simpa [bit2] using hi)
 simpa [bit3] using hk

theorem sub4_read_general (cache0 cache1 cache2 cache3 : Wire) (expected : Bool) (x y cs : List Wire)
 (flags : List Bool) (cin : Wire) (nd : (cin::x++y++cs).Nodup)
 (hx : 5 ≤ x.length) (hy : 5 ≤ y.length) (hc : 4 ≤ cs.length) (hf : 5 ≤ flags.length)
 (hf1 : flags.getD 1 false = false) (hf2 : flags.getD 2 false = false)
 (hf3 : flags.getD 3 false = false) (hf4 : flags.getD 4 false = false)
 (away2 : cache2 ∉ y) (away3 : cache3 ∉ y) (awayk2 : cache2 ∉ cs) (awayk3 : cache3 ∉ cs)
 (s : State) (m : List Bool) (hi : s.basis (bit2 cs) = false)
 (hk : s.basis cache3 = carryBit (s.basis (bit3 x)) (!s.basis (bit3 y)) (s.basis cache2)) :
 run (cachedSub4 cache0 cache1 cache2 cache3 expected (mappedRead x false) flags y cs cin) m s =
 run (cachedSub3 cache0 cache1 cache2 expected (mappedRead x false) flags y cs cin) m s := by
 obtain ⟨a0,a1,a2,a3,a4,xs,rfl⟩ := split_five x hx
 obtain ⟨b0,b1,b2,b3,b4,ys,rfl⟩ := split_five y hy
 obtain ⟨k0,k1,k2,k3,ks,rfl⟩ := split_four cs hc
 obtain ⟨f0,f1,f2,f3,f4,fs,rfl⟩ := split_five flags hf
 have h1 : f1 = false := by simpa using hf1
 have h2 : f2 = false := by simpa using hf2
 have h3 : f3 = false := by simpa using hf3
 have h4 : f4 = false := by simpa using hf4
 subst f1; subst f2; subst f3; subst f4
 apply sub4_read_eq cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin expected f0 xs ys ks fs
  nd away2 away3 (by intro he; apply awayk2; simp [he]) (by intro he; apply awayk2; simp [he])
  (by intro he; apply awayk3; simp [he]) (by intro he; apply awayk3; simp [he])
  (by intro he; apply awayk3; simp [he]) s m (by simpa [bit2] using hi)
 simpa [bit3] using hk

theorem bit3_append (a b : List Wire) (h : 4 ≤ a.length) : bit3 (a++b) = bit3 a := by
 obtain ⟨a0,a1,a2,a3,as,rfl⟩ := split_four a h
 simp [bit3]

theorem bit3_take (a : List Wire) (n : Nat) (h : 4 ≤ n) : bit3 (a.take n) = bit3 a := by
 cases a with
 | nil => simp [bit3]
 | cons a0 as =>
  cases as with
  | nil => simp [bit3]
  | cons a1 as =>
   cases as with
   | nil => simp [bit3]
   | cons a2 as =>
    cases as with
    | nil => simp [bit3]
    | cons a3 as =>
     obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le h
     subst n
     simp [bit3,Nat.add_comm,List.take_succ_cons]

theorem bit3_parity (r : List Wire) (t : BasisState) (hr : 4 ≤ r.length) :
 t (bit3 r) = digit (regValue r t) 3 := by
 obtain ⟨a,b,c,d,rs,rfl⟩ := split_four r hr
 cases ha:t a <;> cases hb:t b <;> cases hc:t c <;> cases hd:t d <;>
  simp [bit3,digit,regValue,ha,hb,hc,hd] <;> omega
#print axioms mapped4_read_general
#print axioms sub4_read_general
#print axioms bit3_parity
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedNarrow
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop WinArith
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def sub33CCCC (cache0 cache1 cache2 cache3:Wire) (R Z cs U:List Wire) (cin:Wire):Program :=
 cachedSub4 cache0 cache1 cache2 cache3 true (mappedRead (U++Z.take 1) false)
  MixedLiteralAdderDevelop.upper33 (R.take 33) (cs.take 32) cin

def sub43CCCC (cache0 cache1 cache2 cache3:Wire) (R Z cs U:List Wire) (cin:Wire):Program :=
 cachedSub4 cache0 cache1 cache2 cache3 true (mappedRead (U++Z) false)
  MixedLiteralAdderDevelop.mask43 (R.take 43) (cs.take 42) cin

def addCCCC (cache0 cache1 cache2 cache3:Wire) (x y cs:List Wire) (cin:Wire):Program :=
 cachedMapped4 cache0 cache1 cache2 cache3 (mappedRead x false) y cs cin

theorem sub33CCCC_eq {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache0 cache1 cache2 cache3:Wire) (h2R:cache2∉R) (h2C:cache2∉cs) (h3R:cache3∉R) (h3C:cache3∉cs)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache3=carryBit (s.basis (bit3 U)) (!s.basis (bit3 R)) (s.basis cache2)):
 run (sub33CCCC cache0 cache1 cache2 cache3 R Z cs U cin) m s=
 run (sub33CCC cache0 cache1 cache2 R Z cs U cin) m s := by
 unfold sub33CCCC sub33CCC
 apply sub4_read_general cache0 cache1 cache2 cache3 true (U++Z.take 1) (R.take 33) (cs.take 32)
  MixedLiteralAdderDevelop.upper33 cin (by simpa using g.ndU 1 0 33 32)
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c]) (by decide) (by decide) (by decide) (by decide) (by decide)
  (fun h=>h2R (List.mem_of_mem_take h)) (fun h=>h3R (List.mem_of_mem_take h))
  (fun h=>h2C (List.mem_of_mem_take h)) (fun h=>h3C (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply bit2_mem;simp[g.c]
 · simpa[bit3_append U _ (by rw[g.u];decide),bit3_take R 33 (by decide)]using hk

theorem sub43CCCC_eq {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache0 cache1 cache2 cache3:Wire) (h2R:cache2∉R) (h2C:cache2∉cs) (h3R:cache3∉R) (h3C:cache3∉cs)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache3=carryBit (s.basis (bit3 U)) (!s.basis (bit3 R)) (s.basis cache2)):
 run (sub43CCCC cache0 cache1 cache2 cache3 R Z cs U cin) m s=
 run (sub43CCC cache0 cache1 cache2 R Z cs U cin) m s := by
 unfold sub43CCCC sub43CCC
 apply sub4_read_general cache0 cache1 cache2 cache3 true (U++Z) (R.take 43) (cs.take 42)
  MixedLiteralAdderDevelop.mask43 cin (by simpa using g.ndUZ 0 43 42)
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c]) (by decide) (by decide) (by decide) (by decide) (by decide)
  (fun h=>h2R (List.mem_of_mem_take h)) (fun h=>h3R (List.mem_of_mem_take h))
  (fun h=>h2C (List.mem_of_mem_take h)) (fun h=>h3C (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply bit2_mem;simp[g.c]
 · simpa[bit3_append U _ (by rw[g.u];decide),bit3_take R 43 (by decide)]using hk

theorem addCCCC_eq {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache0 cache1 cache2 cache3:Wire) (h2C:cache2∉cs) (h3C:cache3∉cs)
 (j n i:Nat) (hn: 5 ≤ n) (hc: 4 ≤ i)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache3=carryBit (s.basis (bit3 U)) (s.basis (bit3 R)) (s.basis cache2)):
 run (addCCCC cache0 cache1 cache2 cache3 (U++Z.take j) (R.take n) (cs.take i) cin) m s=
 run (addCCC cache0 cache1 cache2 (U++Z.take j) (R.take n) (cs.take i) cin) m s := by
 apply mapped4_read_general cache0 cache1 cache2 cache3 (U++Z.take j) (R.take n) (cs.take i) cin
  (by simpa using g.ndU j 0 n i) (by simp[g.u];omega) (by simp[g.r];omega)
  (by simp[g.c];omega) (fun h=>h2C (List.mem_of_mem_take h)) (fun h=>h3C (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply bit2_mem;simp[g.c];omega
 · simpa[bit3_append U _ (by rw[g.u];decide),bit3_take R n (by omega)]using hk

#print axioms sub33CCCC_eq
#print axioms sub43CCCC_eq
#print axioms addCCCC_eq
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryNumbers
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def carryLow4 (u d : Nat) : Bool := carryBit (digit u 3) (digit d 3) (carryLow3 u d)

theorem carryLow3_mod16 (u d : Nat) : carryLow3 (u%16) (d%16) = carryLow3 u d := by
 simp only [carryLow3,carryLow2_mod16,digit_mod16 u ⟨2,by decide⟩,digit_mod16 d ⟨2,by decide⟩]

theorem sub_fourth_fin16 : ∀ (u d : Fin 16),
 carryBit (digit u.val 3) (!(digit (u.val+d.val) 3)) (carryLow3 u.val d.val) = carryLow4 u.val d.val := by decide +kernel

theorem sub_fourth (u d k : Nat) (hk : k%16 = 1) :
 carryBit (digit u 3) (!(digit (u+k*d) 3)) (carryLow3 u d) = carryLow4 u d := by
 have h := sub_fourth_fin16 ⟨u%16,by omega⟩ ⟨d%16,by omega⟩
 have hs : (u%16+d%16)%16 = (u+k*d)%16 := by simp [Nat.add_mod,Nat.mul_mod,hk]
 have de := digit_congr16 _ _ hs ⟨3,by decide⟩
 have du := digit_mod16 u ⟨3,by decide⟩
 have dd := digit_mod16 d ⟨3,by decide⟩
 simpa only [carryLow4,carryLow3_mod16,de,du,dd] using h

theorem digit3_mul_one (d k : Nat) (hk : k%16 = 1) : digit (k*d) 3 = digit d 3 := by
 apply digit_congr16 _ _ _ ⟨3,by decide⟩
 simp [Nat.mul_mod,hk]
#print axioms sub_fourth
#print axioms digit3_mul_one
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedSpecs
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop WinArith
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem ps_fourth {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
 (cache3 : Wire) (hR : cache3 ∉ R) (hS : cache3 ∉ S) (t : BasisState)
 (u V D : Nat) (hu : regValue U t = u) (s : State) (h : PS R S t V D s.basis) :
 s.basis (bit3 U) = digit u 3 ∧ s.basis (bit3 R) = digit V 3 ∧ s.basis cache3 = t cache3 := by
 have uv : regValue U s.basis = u :=
  (regValue_congr U _ _ (fun q hq => h.2.2 q (g.UR q hq) (g.US q hq))).trans hu
 refine ⟨?_,?_,h.2.2 cache3 hR hS⟩
 · simpa only [uv] using bit3_parity U s.basis (by rw [g.u]; decide)
 · simpa only [h.1] using bit3_parity R s.basis (by rw [g.r]; decide)

theorem sub33CCCC_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
 (cache : Wire) (hR : cache ∉ R) (hS : cache ∉ S) {t : BasisState}
 (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
 (hk : t cache = ((u%2==1)&&(d%2==1)))
 (cache1 : Wire) (h1R : cache1 ∉ R) (h1S : cache1 ∉ S) (h1C : cache1 ∉ cs) (hk1 : t cache1 = carryLow2 u d)
 (cache2 : Wire) (h2R : cache2 ∉ R) (h2S : cache2 ∉ S) (h2C : cache2 ∉ cs) (hk2 : t cache2 = carryLow3 u d)
 (cache3 : Wire) (h3R : cache3 ∉ R) (h3S : cache3 ∉ S) (h3C : cache3 ∉ cs) (hk3 : t cache3 = carryLow4 u d) :
 Triple (PS R S t (u+d) 0) (sub33CCCC cache cache1 cache2 cache3 R Z cs U cin) (PS R S t d 0) := by
 intro s m h
 obtain ⟨bu,br,b3⟩ := ps_fourth g cache3 h3R h3S t u (u+d) 0 hu s h
 have b2 : s.basis cache2 = t cache2 := h.2.2 cache2 h2R h2S
 have ready : s.basis cache3 = carryBit (s.basis (bit3 U)) (!s.basis (bit3 R)) (s.basis cache2) := by
  rw [bu,br,b3,b2,hk2,hk3]
  simpa only [Nat.one_mul] using (sub_fourth u d 1 (by decide)).symm
 rw [sub33CCCC_eq g cache cache1 cache2 cache3 h2R h2C h3R h3C s m (ps_cs g cl.c _ _ s h) ready]
 exact sub33CCC_spec g cache hR hS cl u d hu hu32 hd hk cache1 h1R h1S h1C hk1 cache2 h2R h2S h2C hk2 s m h

theorem addCCCC_ps_loose {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
 (cache : Wire) (hR : cache ∉ R) (hS : cache ∉ S) {t : BasisState}
 (hcin : t cin = false) (u d V D : Nat) (hu : regValue U t = u)
 (hk : t cache = ((u%2==1)&&(d%2==1))) (hV : V%2 = d%2)
 (j n i : Nat) (hn : 5 ≤ n) (hc : 4 ≤ i)
 (cache1 : Wire) (h1R : cache1 ∉ R) (h1S : cache1 ∉ S) (h1C : cache1 ∉ cs)
 (hk1 : t cache1 = carryLow2 u d) (hV1 : V/2%2 = d/2%2) (hcs : ∀ q ∈ cs, t q = false)
 (cache2 : Wire) (h2R : cache2 ∉ R) (h2S : cache2 ∉ S) (h2C : cache2 ∉ cs)
 (hk2 : t cache2 = carryLow3 u d) (hV2 : digit V 2 = digit d 2)
 (cache3 : Wire) (h3R : cache3 ∉ R) (h3S : cache3 ∉ S) (h3C : cache3 ∉ cs)
 (hk3 : t cache3 = carryLow4 u d) (hV3 : digit V 3 = digit d 3)
 (s : State) (m : List Bool) (h : PS R S t V D s.basis) :
 run (addCCCC cache cache1 cache2 cache3 (U++Z.take j) (R.take n) (cs.take i) cin) m s =
 run (addInPlace (U++Z.take j) (R.take n) (cs.take i) cin) m s := by
 obtain ⟨bu,br,b3⟩ := ps_fourth g cache3 h3R h3S t u V D hu s h
 have b2 : s.basis cache2 = t cache2 := h.2.2 cache2 h2R h2S
 have ready : s.basis cache3 = carryBit (s.basis (bit3 U)) (s.basis (bit3 R)) (s.basis cache2) := by
  rw [bu,br,b3,b2,hk2,hk3,hV3]
  rfl
 rw [addCCCC_eq g cache cache1 cache2 cache3 h2C h3C j n i hn hc s m (ps_cs g hcs V D s h) ready]
 exact addCCC_ps_loose g cache hR hS hcin u d V D hu hk hV j n i (by omega) (by omega)
  cache1 h1R h1S h1C hk1 hV1 hcs cache2 h2R h2S h2C hk2 hV2 s m h
#print axioms sub33CCCC_spec
#print axioms addCCCC_ps_loose
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedSub43Spec
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop WinArith
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem sub43CCCCK_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
 (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
 (cache : Wire) (hR : cache ∉ R) (hS : cache ∉ S) (hZ : cache ∉ Z)
 (hk : t cache = ((u%2==1)&&(d%2==1))) (k : Wire) (hkZ : k ∉ Z)
 (cache1 : Wire) (h1R : cache1 ∉ R) (h1S : cache1 ∉ S) (h1Z : cache1 ∉ Z) (h1C : cache1 ∉ cs)
 (hk1 : t cache1 = carryLow2 u d)
 (cache2 : Wire) (h2R : cache2 ∉ R) (h2S : cache2 ∉ S) (h2Z : cache2 ∉ Z) (h2C : cache2 ∉ cs)
 (hk2 : t cache2 = carryLow3 u d)
 (cache3 : Wire) (h3R : cache3 ∉ R) (h3S : cache3 ∉ S) (h3Z : cache3 ∉ Z) (h3C : cache3 ∉ cs)
 (hk3 : t cache3 = carryLow4 u d) :
 Triple (PS R S (kz t k Z) (u+4294968273*d+2^32*(976*(if t k then 1 else 0))) 0)
  (sub43CCCC cache cache1 cache2 cache3 R Z cs U cin) (PS R S (kz t k Z) (4294968273*d) 0) := by
 intro s m h
 obtain ⟨bu,br,b3⟩ := ps_fourth g cache3 h3R h3S (kz t k Z) u _ 0 ((kz_u g t k).trans hu) s h
 have b2 : s.basis cache2 = t cache2 :=
  (h.2.2 cache2 h2R h2S).trans (kz_out t k Z g.z cache2 h2Z)
 have b33 : s.basis cache3 = t cache3 := b3.trans (kz_out t k Z g.z cache3 h3Z)
 have hcs : ∀ q ∈ cs, kz t k Z q = false := by
  intro q hq
  have qZ : q ∉ Z := fun bad => g.away cs Z q hq bad (by simp only [List.count_cons,List.count_append,List.count_nil]; omega)
  exact (kz_out t k Z g.z q qZ).trans (cl.c q hq)
 have ready : s.basis cache3 = carryBit (s.basis (bit3 U)) (!s.basis (bit3 R)) (s.basis cache2) := by
  rw [bu,br,b33,b2,hk2,hk3]
  have hp : digit (u+4294968273*d+2^32*(976*(if t k then 1 else 0))) 3 = digit (u+4294968273*d) 3 := by
   cases t k <;> norm_num [digit] <;> omega
  rw [hp]
  exact (sub_fourth u d 4294968273 (by decide)).symm
 rw [sub43CCCC_eq g cache cache1 cache2 cache3 h2R h2C h3R h3C s m (ps_cs g hcs _ _ s h) ready]
 exact sub43CCCK_spec g cl u d hu hu32 hd cache hR hS hZ hk k hkZ
  cache1 h1R h1S h1Z h1C hk1 cache2 h2R h2S h2Z h2C hk2 s m h
#print axioms sub43CCCCK_spec
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryArms
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop WinArith
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
def fwdCCCC (R S Z cs U : List Wire) (cin k cache cache1 cache2 cache3 : Wire) : Program :=
  sub33CCCC cache cache1 cache2 cache3 R Z cs U cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  (WinArithAux3SmallDevelop.smallF R S cs cin ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (kpat k Z ++ (addCCCC cache cache1 cache2 cache3 (U ++ Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin ++ kpat k Z))))))

theorem fwdCCCC_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (cache : Wire) (hR : cache∉R) (hS : cache∉S) (hZ : cache∉Z)
    (hcache : t cache=((u%2==1) && (d%2==1))) (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (_h35 : u + d < 2^35)
    (cache1 : Wire) (h1R : cache1∉R) (h1S : cache1∉S) (h1Z : cache1∉Z) (h1C : cache1∉cs)
    (hcache1 : t cache1=carryLow2 u d)
    (cache2:Wire) (h2R:cache2∉R) (h2S:cache2∉S) (h2Z:cache2∉Z) (h2C:cache2∉cs)
    (hcache2:t cache2=carryLow3 u d)
    (cache3:Wire) (h3R:cache3∉R) (h3S:cache3∉S) (h3Z:cache3∉Z) (h3C:cache3∉cs)
    (hcache3:t cache3=carryLow4 u d) :
    Triple (PS R S t (u+d) 0) (fwdCCCC R S Z cs U cin k cache cache1 cache2 cache3)
      (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) := by
  have s1 := sub33CCCC_spec g cache hR hS cl u d hu hu32 hd hcache cache1 h1R h1S h1C hcache1 cache2 h2R h2S h2C hcache2 cache3 h3R h3S h3C hcache3
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
      (addCCCC cache cache1 cache2 cache3 (U++Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin)
      (PS R S (kz t k Z) (977*d+2^32*d+2^0*(u+2^32*(976*(if t k then 1 else 0)))) 0) := by
    intro s m hs
    simp only [List.drop_zero]
    rw [addCCCC_ps_loose g cache hR hS kzc u d (977*d+2^32*d) 0
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
        exact digit_mul_one d 4294968273 (by decide))
      cache3 h3R h3S h3C ((kz_out t k Z g.z cache3 h3Z).trans hcache3) (by
        have hsum:977*d+2^32*d=4294968273*d:=by norm_num;omega
        rw[hsum]
        exact digit3_mul_one d 4294968273 (by decide)) s m hs]
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
  unfold fwdCCCC
  exact seqv s1 (PS_val (by omega)) (seqv s2 (PS_dval a2)
    (seqv s3 (fun _ h => h) (seqv s4 (PS_val a4) (seqv s5 (PS_dval a5)
    (seqv p1 (fun _ h => h) (seqv s6 (fun _ h => h)
    (Triple.conseq (fun s h => h) p2 (PS_val (by cases t k <;> simp <;> omega)))))))))


def invCCCC (R S Z cs U : List Wire) (cin k cache cache1 cache2 cache3 : Wire) : Program :=
  kpat k Z ++ (sub43CCCC cache cache1 cache2 cache3 R Z cs U cin ++ (kpat k Z ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (WinArithAux3SmallDevelop.smallI R S cs cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  addCCCC cache cache1 cache2 cache3 (U ++ Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin))))))

theorem invCCCC_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (cache : Wire) (hR : cache∉R) (hS : cache∉S) (hZ : cache∉Z)
    (hcache : t cache=((u%2==1) && (d%2==1))) (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (_h35 : u + d < 2^35)
    (cache1 : Wire) (h1R : cache1∉R) (h1S : cache1∉S) (h1Z : cache1∉Z) (h1C : cache1∉cs)
    (hcache1 : t cache1=carryLow2 u d)
    (cache2:Wire) (h2R:cache2∉R) (h2S:cache2∉S) (h2Z:cache2∉Z) (h2C:cache2∉cs)
    (hcache2:t cache2=carryLow3 u d)
    (cache3:Wire) (h3R:cache3∉R) (h3S:cache3∉S) (h3Z:cache3∉Z) (h3C:cache3∉cs)
    (hcache3:t cache3=carryLow4 u d) :
    Triple (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) (invCCCC R S Z cs U cin k cache cache1 cache2 cache3)
      (PS R S t (u+d) 0) := by
  have p1 := kpat_PS g k hkR hkS hkZ t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0
  have s1 := sub43CCCCK_spec g cl u d hu hu32 hd cache hR hS hZ hcache k hkZ cache1 h1R h1S h1Z h1C hcache1 cache2 h2R h2S h2Z h2C hcache2 cache3 h3R h3S h3Z h3C hcache3
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
      (addCCCC cache cache1 cache2 cache3 (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin)
      (PS R S t (d+2^0*u) 0) := by
    intro s m hs
    simp only [List.drop_zero]
    rw [addCCCC_ps_loose g cache hR hS cl.cin u d d 0 hu hcache rfl
      1 33 32 (by decide) (by decide) cache1 h1R h1S h1C hcache1 rfl cl.c cache2 h2R h2S h2C hcache2 rfl cache3 h3R h3S h3C hcache3 rfl s m hs]
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
  unfold invCCCC
  exact seqv p1 (fun _ h => h) (seqv s1 (fun _ h => h) (seqv p2 (PS_val (by ring))
    (seqv s2 (PS_dval a2) (seqv s3 (PS_val a3)
    (seqv s4 (fun _ h => h) (seqv s5 (PS_dval a5)
    (Triple.conseq (fun s h => h) s6 (PS_val (by omega)))))))))

#print axioms fwdCCCC_spec
#print axioms invCCCC_spec
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryMiddle
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
def wFwdCCCC (L:CuccaroStreamedSquareWideLayout) (cache cache1 cache2 cache3:Wire):Program :=
 fwdCCCC (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L) cache cache1 cache2 cache3
def wInvCCCC (L:CuccaroStreamedSquareWideLayout) (cache cache1 cache2 cache3:Wire):Program :=
 invCCCC (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L) cache cache1 cache2 cache3
theorem wMidCCCC_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cache : Wire) (cacheE : cache∈eReg L) (cache1 : Wire) (cache1E : cache1∈eReg L) (cache2:Wire) (cache2E:cache2∈eReg L) (cache3:Wire) (cache3E:cache3∈eReg L)
    (base : BasisState) (hc : L.PairClean base) (O E b1 : Nat) (hb1 : regValue (hiReg L) base = b1)
    (hb1lt : b1 < 2^128) (hO : O < SquareReduction.p)
    (K : Nat) (hK : K ≤ 1) :
    Triple (fun x=> BState L base O E (4294968272*b1) x ∧
      x cache=((b1/2^96%2==1) && ((4294968272*b1/2^128-b1/2^96)%2==1)) ∧
      x cache1=carryLow2 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      x cache2=carryLow3 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      x cache3=carryLow4 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      (if x (eU L) then 1 else 0)=K) (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3))
      (fun x=> BState L base (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 4294968272*2^32*K +
        2^128*((4294968272*b1)%2^128) + (SquareReduction.p-1-O)) % SquareReduction.p) E (4294968272*b1) x ∧
      x cache=((b1/2^96%2==1) && ((4294968272*b1/2^128-b1/2^96)%2==1)) ∧
      x cache1=carryLow2 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      x cache2=carryLow3 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      x cache3=carryLow4 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      (if x (eU L) then 1 else 0)=K) := by
  intro s m input
  obtain ⟨h,hCache,hCache1,hCache2,hCache3,key⟩:=input
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
  have cr3 : cache3∉mR L := fun hr=>(m_away L hn cache3 (Or.inl hr)).2 cache3E
  have cS3 : cache3∉mS L := fun hs=>(m_away L hn cache3 (Or.inr hs)).2 cache3E
  have cZ3 : cache3∉mZ L := by
    intro hz
    have lc:=layoutCount L hn cache3
    have ps:=productSplit L cache3
    have ec:=eReg_count L cache3
    have ce:=List.count_pos_iff.mpr cache3E
    have cz:=List.count_pos_iff.mpr (mZ_pad L cache3 hz)
    omega
  have cC3 : cache3∉mC L := by
    intro hz
    have lc:=layoutCount L hn cache3
    have ps:=productSplit L cache3
    have ec:=eReg_count L cache3
    have ce:=List.count_pos_iff.mpr cache3E
    have cz:=List.count_pos_iff.mpr (mC_pad L cache3 hz)
    omega
  have co3 : cache3∉L.core.out := (eReg_away L hn cache3 cache3E).1
  obtain ⟨ws1, ws2, ws3⟩ := whi_split b1 hb1lt
  generalize hW : 4294968272*b1 = W at h hCache hCache1 hCache2 hCache3 ws1 ws2 ws3 ⊢
  generalize hu : b1/2^96 = u at hCache hCache1 hCache2 hCache3 ws1 ws2 ⊢
  generalize hd : W/2^128 - u = d at hCache hCache1 hCache2 hCache3 ws2 ⊢
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
  have T1 : Triple (WinArith.PS (mR L) (mS L) s.basis (u+d) 0) (wFwdCCCC L cache cache1 cache2 cache3)
      (WinArith.PS (mR L) (mS L) s.basis (u + 4294968273*d + 2^32*(976*K)) 0) := by
    have := fwdCCCC_spec g cl u d hU hu32 ws2 cache cr cS cZ hCache (eU L) heR heS heZ (by omega) cache1 cr1 cS1 cZ1 cC1 hCache1 cache2 cr2 cS2 cZ2 cC2 hCache2 cache3 cr3 cS3 cZ3 cC3 hCache3
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
  have T3 : Triple Q2 (wInvCCCC L cache cache1 cache2 cache3) Q3 := by
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
    have hCache32 : s2.basis cache3=carryLow4 u d :=
      (k2 cache3 co3 cr3 cS3).trans hCache3
    obtain ⟨ph, h3⟩ := invCCCC_spec g cl2 u d hU2 hu32 ws2 cache cr cS cZ hCache0at2 (eU L) heR heS heZ (by omega) cache1 cr1 cS1 cZ1 cC1 hCache12 cache2 cr2 cS2 cZ2 cC2 hCache22 cache3 cr3 cS3 cZ3 cC3 hCache32 s2 m2 P2
    refine ⟨ph, ?_, h3.1, h3.2.1, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => h3.2.2 q (fun hr => (m_away L hn q (Or.inl hr)).1 hq)
        (fun hs => (m_away L hn q (Or.inr hs)).1 hq))).trans h2.1
    · intro q a b c; exact (h3.2.2 q b c).trans (k2 q a b c)
  obtain ⟨ph, f⟩ := (T1.seq (T2.seq T3)) s m P0
  refine ⟨ph, ⟨f.1, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => f.2.2.2 q (eReg_away L hn q hq).1
      (fun hr => (m_away L hn q (Or.inl hr)).2 hq) (fun hs => (m_away L hn q (Or.inr hs)).2 hq))).trans h.2.1
  · -- the work register is `W` again
    have wv : regValue L.core.work (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = W := by
      rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
      have lo : regValue (L.core.work.take 128) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = W % 2^128 := by
        rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
          WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
      have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = 0 := by
        apply (regValue_zero _ _).mpr
        intro q hq
        rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
        apply workZ
        have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
        rw [this] at hq
        exact List.mem_of_mem_drop hq
      have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = u + d :=
        f.2.1
      rw [lo, mr, hi0]
      omega
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis
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
      have wv : regValue L.core.work (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = W := by
        rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
        have lo : regValue (L.core.work.take 128) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = W % 2^128 := by
          rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
            WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
        have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = 0 := by
          apply (regValue_zero _ _).mpr
          intro q hq
          rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
          apply workZ
          have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
          rw [this] at hq
          exact List.mem_of_mem_drop hq
        have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = u + d :=
          f.2.1
        rw [lo, mr, hi0]
        omega
      have z : regValue (L.core.work.drop 163) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = 0 := by
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
  · exact (f.2.2.2 cache3 co3 cr3 cS3).trans hCache3
  · rw [f.2.2.2 (eU L) eA.2.2 heR heS]
    exact key

#print axioms wMidCCCC_step
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryLoanCore
open ECDSAAdd
namespace FourthCarryLoan
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem get_ne (r : List Wire) (hn : r.Nodup) (i j : Nat)
 (hi : i<r.length) (hj : j<r.length) (hij : i≠j) : r.getD i 0≠r.getD j 0 := by
 intro h
 rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] at h
 exact hij ((List.Nodup.getElem_inj_iff hn).mp h)

def loan3 (v1 v2 u0 u2 u3 e0 e2 host : Wire) : Program :=
 [.measureX host [] [.Z u3,.CZ v1 e0,.CZ v2 e0,.CZ v1 u0,.CZ v2 u0,.CZ u2 e2,.Z u2]]
def restore3 (v1 v2 u0 u2 u3 e0 e2 host : Wire) : Program :=
 [.CX u0 e0,.CX v2 v1,.CCX v1 e0 host,.CX v2 v1,.CX u0 e0,
  .CCX u2 e2 host,.CX u2 host,.CX u3 host]

def value (s : BasisState) (v1 v2 u0 u2 u3 e0 e2 : Wire) : Bool :=
 s u3 ^^ ((s e0 ^^ s u0) && (s v1 ^^ s v2)) ^^ (s u2 && s e2) ^^ s u2

theorem loan3_run (v1 v2 u0 u2 u3 e0 e2 host : Wire) (nd : [v1,v2,u0,u2,u3,e0,e2,host].Nodup)
 (s : State) (m : List Bool) (hv : s.basis host=value s.basis v1 v2 u0 u2 u3 e0 e2) :
 run (loan3 v1 v2 u0 u2 u3 e0 e2 host) m s=⟨s.phase,writeBit s.basis host false⟩ := by
 have n01 : v1≠v2 := get_ne _ nd 0 1 (by simp) (by simp) (by decide)
 have n02 : v1≠u0 := get_ne _ nd 0 2 (by simp) (by simp) (by decide)
 have n03 : v1≠u2 := get_ne _ nd 0 3 (by simp) (by simp) (by decide)
 have n04 : v1≠u3 := get_ne _ nd 0 4 (by simp) (by simp) (by decide)
 have n05 : v1≠e0 := get_ne _ nd 0 5 (by simp) (by simp) (by decide)
 have n06 : v1≠e2 := get_ne _ nd 0 6 (by simp) (by simp) (by decide)
 have n07 : v1≠host := get_ne _ nd 0 7 (by simp) (by simp) (by decide)
 have n12 : v2≠u0 := get_ne _ nd 1 2 (by simp) (by simp) (by decide)
 have n13 : v2≠u2 := get_ne _ nd 1 3 (by simp) (by simp) (by decide)
 have n14 : v2≠u3 := get_ne _ nd 1 4 (by simp) (by simp) (by decide)
 have n15 : v2≠e0 := get_ne _ nd 1 5 (by simp) (by simp) (by decide)
 have n16 : v2≠e2 := get_ne _ nd 1 6 (by simp) (by simp) (by decide)
 have n17 : v2≠host := get_ne _ nd 1 7 (by simp) (by simp) (by decide)
 have n23 : u0≠u2 := get_ne _ nd 2 3 (by simp) (by simp) (by decide)
 have n24 : u0≠u3 := get_ne _ nd 2 4 (by simp) (by simp) (by decide)
 have n25 : u0≠e0 := get_ne _ nd 2 5 (by simp) (by simp) (by decide)
 have n26 : u0≠e2 := get_ne _ nd 2 6 (by simp) (by simp) (by decide)
 have n27 : u0≠host := get_ne _ nd 2 7 (by simp) (by simp) (by decide)
 have n34 : u2≠u3 := get_ne _ nd 3 4 (by simp) (by simp) (by decide)
 have n35 : u2≠e0 := get_ne _ nd 3 5 (by simp) (by simp) (by decide)
 have n36 : u2≠e2 := get_ne _ nd 3 6 (by simp) (by simp) (by decide)
 have n37 : u2≠host := get_ne _ nd 3 7 (by simp) (by simp) (by decide)
 have n45 : u3≠e0 := get_ne _ nd 4 5 (by simp) (by simp) (by decide)
 have n46 : u3≠e2 := get_ne _ nd 4 6 (by simp) (by simp) (by decide)
 have n47 : u3≠host := get_ne _ nd 4 7 (by simp) (by simp) (by decide)
 have n56 : e0≠e2 := get_ne _ nd 5 6 (by simp) (by simp) (by decide)
 have n57 : e0≠host := get_ne _ nd 5 7 (by simp) (by simp) (by decide)
 have n67 : e2≠host := get_ne _ nd 6 7 (by simp) (by simp) (by decide)
 cases m with
 | nil => simp [loan3,run,measureAndCorrect,correct]
 | cons bit ms =>
  cases bit <;> cases h1:s.basis v1 <;> cases h2:s.basis v2 <;>
   cases h3:s.basis u0 <;> cases h4:s.basis u2 <;> cases h5:s.basis u3 <;>
   cases h6:s.basis e0 <;> cases h7:s.basis e2 <;>
   simp [loan3,run,measureAndCorrect,correct,hv,value,writeBit,Function.update_apply,
   n01,Ne.symm n01,n02,Ne.symm n02,n03,Ne.symm n03,n04,Ne.symm n04,
   n05,Ne.symm n05,n06,Ne.symm n06,n07,Ne.symm n07,n12,Ne.symm n12,
   n13,Ne.symm n13,n14,Ne.symm n14,n15,Ne.symm n15,n16,Ne.symm n16,
   n17,Ne.symm n17,n23,Ne.symm n23,n24,Ne.symm n24,n25,Ne.symm n25,
   n26,Ne.symm n26,n27,Ne.symm n27,n34,Ne.symm n34,n35,Ne.symm n35,
   n36,Ne.symm n36,n37,Ne.symm n37,n45,Ne.symm n45,n46,Ne.symm n46,
   n47,Ne.symm n47,n56,Ne.symm n56,n57,Ne.symm n57,n67,Ne.symm n67,h1,h2,h3,h4,h5,h6,h7]

theorem restore3_run (v1 v2 u0 u2 u3 e0 e2 host : Wire) (nd : [v1,v2,u0,u2,u3,e0,e2,host].Nodup)
 (s : State) (m : List Bool) :
 run (restore3 v1 v2 u0 u2 u3 e0 e2 host) m s=
 ⟨s.phase,writeBit s.basis host (s.basis host ^^ value s.basis v1 v2 u0 u2 u3 e0 e2)⟩ := by
 have n01 : v1≠v2 := get_ne _ nd 0 1 (by simp) (by simp) (by decide)
 have n02 : v1≠u0 := get_ne _ nd 0 2 (by simp) (by simp) (by decide)
 have n03 : v1≠u2 := get_ne _ nd 0 3 (by simp) (by simp) (by decide)
 have n04 : v1≠u3 := get_ne _ nd 0 4 (by simp) (by simp) (by decide)
 have n05 : v1≠e0 := get_ne _ nd 0 5 (by simp) (by simp) (by decide)
 have n06 : v1≠e2 := get_ne _ nd 0 6 (by simp) (by simp) (by decide)
 have n07 : v1≠host := get_ne _ nd 0 7 (by simp) (by simp) (by decide)
 have n12 : v2≠u0 := get_ne _ nd 1 2 (by simp) (by simp) (by decide)
 have n13 : v2≠u2 := get_ne _ nd 1 3 (by simp) (by simp) (by decide)
 have n14 : v2≠u3 := get_ne _ nd 1 4 (by simp) (by simp) (by decide)
 have n15 : v2≠e0 := get_ne _ nd 1 5 (by simp) (by simp) (by decide)
 have n16 : v2≠e2 := get_ne _ nd 1 6 (by simp) (by simp) (by decide)
 have n17 : v2≠host := get_ne _ nd 1 7 (by simp) (by simp) (by decide)
 have n23 : u0≠u2 := get_ne _ nd 2 3 (by simp) (by simp) (by decide)
 have n24 : u0≠u3 := get_ne _ nd 2 4 (by simp) (by simp) (by decide)
 have n25 : u0≠e0 := get_ne _ nd 2 5 (by simp) (by simp) (by decide)
 have n26 : u0≠e2 := get_ne _ nd 2 6 (by simp) (by simp) (by decide)
 have n27 : u0≠host := get_ne _ nd 2 7 (by simp) (by simp) (by decide)
 have n34 : u2≠u3 := get_ne _ nd 3 4 (by simp) (by simp) (by decide)
 have n35 : u2≠e0 := get_ne _ nd 3 5 (by simp) (by simp) (by decide)
 have n36 : u2≠e2 := get_ne _ nd 3 6 (by simp) (by simp) (by decide)
 have n37 : u2≠host := get_ne _ nd 3 7 (by simp) (by simp) (by decide)
 have n45 : u3≠e0 := get_ne _ nd 4 5 (by simp) (by simp) (by decide)
 have n46 : u3≠e2 := get_ne _ nd 4 6 (by simp) (by simp) (by decide)
 have n47 : u3≠host := get_ne _ nd 4 7 (by simp) (by simp) (by decide)
 have n56 : e0≠e2 := get_ne _ nd 5 6 (by simp) (by simp) (by decide)
 have n57 : e0≠host := get_ne _ nd 5 7 (by simp) (by simp) (by decide)
 have n67 : e2≠host := get_ne _ nd 6 7 (by simp) (by simp) (by decide)
 change (⟨s.phase,_⟩:State)=⟨s.phase,_⟩
 apply congrArg (State.mk s.phase)
 funext q
 by_cases hq:q=host
 · subst q
   cases h1:s.basis v1 <;> cases h2:s.basis v2 <;>
    cases h3:s.basis u0 <;> cases h4:s.basis u2 <;> cases h5:s.basis u3 <;>
    cases h6:s.basis e0 <;> cases h7:s.basis e2 <;>
    simp [restore3,run,value,writeBit,Function.update_apply,
    n01,Ne.symm n01,n02,Ne.symm n02,n03,Ne.symm n03,n04,Ne.symm n04,
   n05,Ne.symm n05,n06,Ne.symm n06,n07,Ne.symm n07,n12,Ne.symm n12,
   n13,Ne.symm n13,n14,Ne.symm n14,n15,Ne.symm n15,n16,Ne.symm n16,
   n17,Ne.symm n17,n23,Ne.symm n23,n24,Ne.symm n24,n25,Ne.symm n25,
   n26,Ne.symm n26,n27,Ne.symm n27,n34,Ne.symm n34,n35,Ne.symm n35,
   n36,Ne.symm n36,n37,Ne.symm n37,n45,Ne.symm n45,n46,Ne.symm n46,
   n47,Ne.symm n47,n56,Ne.symm n56,n57,Ne.symm n57,n67,Ne.symm n67,h1,h2,h3,h4,h5,h6,h7]
 by_cases he:q=e0
 · subst q
   cases h0:s.basis e0 <;> cases hu:s.basis u0 <;>
    simp [restore3,run,value,writeBit,Function.update_apply,n01,Ne.symm n01,n02,Ne.symm n02,n03,Ne.symm n03,n04,Ne.symm n04,
   n05,Ne.symm n05,n06,Ne.symm n06,n07,Ne.symm n07,n12,Ne.symm n12,
   n13,Ne.symm n13,n14,Ne.symm n14,n15,Ne.symm n15,n16,Ne.symm n16,
   n17,Ne.symm n17,n23,Ne.symm n23,n24,Ne.symm n24,n25,Ne.symm n25,
   n26,Ne.symm n26,n27,Ne.symm n27,n34,Ne.symm n34,n35,Ne.symm n35,
   n36,Ne.symm n36,n37,Ne.symm n37,n45,Ne.symm n45,n46,Ne.symm n46,
   n47,Ne.symm n47,n56,Ne.symm n56,n57,Ne.symm n57,n67,Ne.symm n67,h0,hu]
 by_cases hv:q=v1
 · subst q
   cases h1:s.basis v1 <;> cases h2:s.basis v2 <;>
    simp [restore3,run,value,writeBit,Function.update_apply,n01,Ne.symm n01,n02,Ne.symm n02,n03,Ne.symm n03,n04,Ne.symm n04,
   n05,Ne.symm n05,n06,Ne.symm n06,n07,Ne.symm n07,n12,Ne.symm n12,
   n13,Ne.symm n13,n14,Ne.symm n14,n15,Ne.symm n15,n16,Ne.symm n16,
   n17,Ne.symm n17,n23,Ne.symm n23,n24,Ne.symm n24,n25,Ne.symm n25,
   n26,Ne.symm n26,n27,Ne.symm n27,n34,Ne.symm n34,n35,Ne.symm n35,
   n36,Ne.symm n36,n37,Ne.symm n37,n45,Ne.symm n45,n46,Ne.symm n46,
   n47,Ne.symm n47,n56,Ne.symm n56,n57,Ne.symm n57,n67,Ne.symm n67,h1,h2]
 simp [restore3,run,value,writeBit,Function.update_apply,hq,he,hv]

theorem counts (v1 v2 u0 u2 u3 e0 e2 host : Wire) :
 toffoliCount (loan3 v1 v2 u0 u2 u3 e0 e2 host)=0 ∧
 measurementCount (loan3 v1 v2 u0 u2 u3 e0 e2 host)=1 ∧
 Challenge.gateSlots (loan3 v1 v2 u0 u2 u3 e0 e2 host)=8 ∧
 toffoliCount (restore3 v1 v2 u0 u2 u3 e0 e2 host)=2 ∧
 measurementCount (restore3 v1 v2 u0 u2 u3 e0 e2 host)=0 ∧
 Challenge.gateSlots (restore3 v1 v2 u0 u2 u3 e0 e2 host)=8 := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem physical (v1 v2 u0 u2 u3 e0 e2 host : Wire)
 (nd : [v1,v2,u0,u2,u3,e0,e2,host].Nodup) :
 Arithmetic.GatePhysical (loan3 v1 v2 u0 u2 u3 e0 e2 host) ∧
 Arithmetic.GatePhysical (restore3 v1 v2 u0 u2 u3 e0 e2 host) := by
 have n01 : v1≠v2 := get_ne _ nd 0 1 (by simp) (by simp) (by decide)
 have n02 : v1≠u0 := get_ne _ nd 0 2 (by simp) (by simp) (by decide)
 have n03 : v1≠u2 := get_ne _ nd 0 3 (by simp) (by simp) (by decide)
 have n04 : v1≠u3 := get_ne _ nd 0 4 (by simp) (by simp) (by decide)
 have n05 : v1≠e0 := get_ne _ nd 0 5 (by simp) (by simp) (by decide)
 have n06 : v1≠e2 := get_ne _ nd 0 6 (by simp) (by simp) (by decide)
 have n07 : v1≠host := get_ne _ nd 0 7 (by simp) (by simp) (by decide)
 have n12 : v2≠u0 := get_ne _ nd 1 2 (by simp) (by simp) (by decide)
 have n13 : v2≠u2 := get_ne _ nd 1 3 (by simp) (by simp) (by decide)
 have n14 : v2≠u3 := get_ne _ nd 1 4 (by simp) (by simp) (by decide)
 have n15 : v2≠e0 := get_ne _ nd 1 5 (by simp) (by simp) (by decide)
 have n16 : v2≠e2 := get_ne _ nd 1 6 (by simp) (by simp) (by decide)
 have n17 : v2≠host := get_ne _ nd 1 7 (by simp) (by simp) (by decide)
 have n23 : u0≠u2 := get_ne _ nd 2 3 (by simp) (by simp) (by decide)
 have n24 : u0≠u3 := get_ne _ nd 2 4 (by simp) (by simp) (by decide)
 have n25 : u0≠e0 := get_ne _ nd 2 5 (by simp) (by simp) (by decide)
 have n26 : u0≠e2 := get_ne _ nd 2 6 (by simp) (by simp) (by decide)
 have n27 : u0≠host := get_ne _ nd 2 7 (by simp) (by simp) (by decide)
 have n34 : u2≠u3 := get_ne _ nd 3 4 (by simp) (by simp) (by decide)
 have n35 : u2≠e0 := get_ne _ nd 3 5 (by simp) (by simp) (by decide)
 have n36 : u2≠e2 := get_ne _ nd 3 6 (by simp) (by simp) (by decide)
 have n37 : u2≠host := get_ne _ nd 3 7 (by simp) (by simp) (by decide)
 have n45 : u3≠e0 := get_ne _ nd 4 5 (by simp) (by simp) (by decide)
 have n46 : u3≠e2 := get_ne _ nd 4 6 (by simp) (by simp) (by decide)
 have n47 : u3≠host := get_ne _ nd 4 7 (by simp) (by simp) (by decide)
 have n56 : e0≠e2 := get_ne _ nd 5 6 (by simp) (by simp) (by decide)
 have n57 : e0≠host := get_ne _ nd 5 7 (by simp) (by simp) (by decide)
 have n67 : e2≠host := get_ne _ nd 6 7 (by simp) (by simp) (by decide)
 simp [loan3,restore3,Arithmetic.GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,n01,Ne.symm n01,n02,Ne.symm n02,n03,Ne.symm n03,n04,Ne.symm n04,n05,Ne.symm n05,n06,Ne.symm n06,n07,Ne.symm n07,n12,Ne.symm n12,n13,Ne.symm n13,n14,Ne.symm n14,n15,Ne.symm n15,n16,Ne.symm n16,n17,Ne.symm n17,n23,Ne.symm n23,n24,Ne.symm n24,n25,Ne.symm n25,n26,Ne.symm n26,n27,Ne.symm n27,n34,Ne.symm n34,n35,Ne.symm n35,n36,Ne.symm n36,n37,Ne.symm n37,n45,Ne.symm n45,n46,Ne.symm n46,n47,Ne.symm n47,n56,Ne.symm n56,n57,Ne.symm n57,n67,Ne.symm n67]

theorem support (v1 v2 u0 u2 u3 e0 e2 host : Wire) :
 wires (loan3 v1 v2 u0 u2 u3 e0 e2 host)⊆[v1,v2,u0,u2,u3,e0,e2,host].toFinset ∧
 wires (restore3 v1 v2 u0 u2 u3 e0 e2 host)⊆[v1,v2,u0,u2,u3,e0,e2,host].toFinset := by
 constructor <;> intro q h <;>
  simp [loan3,restore3,ECDSAAdd.wires,Instr.wires,correctionWires] at h ⊢ <;> tauto
#print axioms physical
#print axioms support

#print axioms loan3_run
#print axioms restore3_run
#print axioms counts
end FourthCarryLoan

end -- isolated Carry9 component

section
-- FourthCarryEnds
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def prepare4 (g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3 : Wire) : Program :=
 FourthCarryLoan.loan3 v1 v2 u0 u2 u3 e0 host2 host3 ++
 (prepare3 g v1 u0 u1 u2 r0 r1 r2 e0 cache host1 host2 ++ prime2 u3 r3 host2 host3)

def finish4 (g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3 : Wire) : Program :=
 clear2 u3 r3 host2 host3 ++
 (finish3 g v1 u0 u1 u2 r0 r1 r2 e0 cache host1 host2 ++ FourthCarryLoan.restore3 v1 v2 u0 u2 u3 e0 host2 host3)

theorem geometry16_12 (g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3 : Wire)
 (nd : [g,v1,v2,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,host1,host2,host3].Nodup) :
 [g,v1,u0,u1,u2,r0,r1,r2,e0,cache,host1,host2].Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have h := List.nodup_iff_count_le_one.mp nd q
 simp only [List.count_cons,List.count_nil] at h ⊢
 omega

theorem geometry16_8 (g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3 : Wire)
 (nd : [g,v1,v2,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,host1,host2,host3].Nodup) :
 [v1,v2,u0,u2,u3,e0,host2,host3].Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have h := List.nodup_iff_count_le_one.mp nd q
 simp only [List.count_cons,List.count_nil] at h ⊢
 omega

theorem prepare4_run (g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3 : Wire)
 (nd : [g,v1,v2,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,host1,host2,host3].Nodup) (s : State) (m : List Bool)
 (hz : s.basis cache = false)
 (hl1 : s.basis host1 = (s.basis u1 ^^ s.basis u0 ^^ (s.basis u0 && s.basis e0)))
 (hl2 : s.basis host2 = loanValue2 s.basis g v1 u0 u1 u2 e0 host1)
 (hl3 : s.basis host3 = FourthCarryLoan.value s.basis v1 v2 u0 u2 u3 e0 host2) :
 let k0 := s.basis u0 && !s.basis r0
 let k1 := carryBit (s.basis u1) (!s.basis r1) k0
 let k2 := carryBit (s.basis u2) (!s.basis r2) k1
 let k3 := carryBit (s.basis u3) (!s.basis r3) k2
 run (prepare4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3) m s =
 ⟨s.phase,writeBit (writeBit (writeBit (writeBit s.basis cache k0) host1 k1) host2 k2) host3 k3⟩ := by
 have geom := nd
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false] at geom
 have nd12 := geometry16_12 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3 nd
 have nd8 := geometry16_8 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3 nd
 let k0 := s.basis u0 && !s.basis r0
 let k1 := carryBit (s.basis u1) (!s.basis r1) k0
 let k2 := carryBit (s.basis u2) (!s.basis r2) k1
 let k3 := carryBit (s.basis u3) (!s.basis r3) k2
 let S0 : State := ⟨s.phase,writeBit s.basis host3 false⟩
 let S1 : State := ⟨s.phase,writeBit (writeBit (writeBit S0.basis cache k0) host1 k1) host2 k2⟩
 have p : ∀ r, run (FourthCarryLoan.loan3 v1 v2 u0 u2 u3 e0 host2 host3) r s = S0 := by
  intro r
  exact FourthCarryLoan.loan3_run v1 v2 u0 u2 u3 e0 host2 host3 nd8 s r hl3
 have q : ∀ r, run (prepare3 g v1 u0 u1 u2 r0 r1 r2 e0 cache host1 host2) r S0 = S1 := by
  intro r
  rw [prepare3_run g v1 u0 u1 u2 r0 r1 r2 e0 cache host1 host2 nd12 S0 r]
  · simp [S1,S0,k0,k1,k2,writeBit,Function.update_apply,show u0≠host3 by tauto,
     show u1≠host3 by tauto,show u2≠host3 by tauto,show r0≠host3 by tauto,
     show r1≠host3 by tauto,show r2≠host3 by tauto]
  · simpa [S0,writeBit,Function.update_apply,show cache≠host3 by tauto] using hz
  · simpa [S0,writeBit,Function.update_apply,show host1≠host3 by tauto,
     show u0≠host3 by tauto,show u1≠host3 by tauto,show e0≠host3 by tauto] using hl1
  · simpa [S0,loanValue2,writeBit,Function.update_apply,show host2≠host3 by tauto,
     show g≠host3 by tauto,show v1≠host3 by tauto,show u0≠host3 by tauto,
     show u1≠host3 by tauto,show u2≠host3 by tauto,show e0≠host3 by tauto,
     show host1≠host3 by tauto] using hl2
 have z : ∀ r, run (prime2 u3 r3 host2 host3) r S1 =
   ⟨s.phase,writeBit (writeBit (writeBit (writeBit s.basis cache k0) host1 k1) host2 k2) host3 k3⟩ := by
  intro r
  rw [prime2_run u3 r3 host2 host3 (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) S1 r]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases wh : w=host3
  · subst w
    simp [S1,S0,k3,writeBit,Function.update_apply,
     show u3≠cache by tauto,show u3≠host1 by tauto,show u3≠host2 by tauto,show u3≠host3 by tauto,
     show r3≠cache by tauto,show r3≠host1 by tauto,show r3≠host2 by tauto,show r3≠host3 by tauto,
     show host2≠cache by tauto,show host2≠host1 by tauto,show host3≠cache by tauto,
     show host3≠host1 by tauto,show host3≠host2 by tauto]
  · simp [S1,S0,writeBit,Function.update_apply,wh]
 dsimp only
 rw [prepare4,run_append,p,run_append,q,z]

theorem finish4_run (g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3 : Wire)
 (nd : [g,v1,v2,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,host1,host2,host3].Nodup) (s : State) (m : List Bool)
 (hk0 : s.basis cache = (s.basis u0 && !s.basis r0))
 (hk1 : s.basis host1 = carryBit (s.basis u1) (!s.basis r1) (s.basis cache))
 (hk2 : s.basis host2 = carryBit (s.basis u2) (!s.basis r2) (s.basis host1))
 (hk3 : s.basis host3 = carryBit (s.basis u3) (!s.basis r3) (s.basis host2)) :
 let t := writeBit (writeBit (writeBit (writeBit s.basis host3 false) host2 false) host1
  (s.basis u1 ^^ s.basis u0 ^^ (s.basis u0 && s.basis e0))) cache false
 let t3 := writeBit t host2 (loanValue2 t g v1 u0 u1 u2 e0 host1)
 run (finish4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3) m s =
 ⟨s.phase,writeBit t3 host3 (FourthCarryLoan.value t3 v1 v2 u0 u2 u3 e0 host2)⟩ := by
 have geom := nd
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false] at geom
 have nd12 := geometry16_12 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3 nd
 have nd8 := geometry16_8 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host1 host2 host3 nd
 let S0 : State := ⟨s.phase,writeBit s.basis host3 false⟩
 let t := writeBit (writeBit (writeBit S0.basis host2 false) host1
  (s.basis u1 ^^ s.basis u0 ^^ (s.basis u0 && s.basis e0))) cache false
 let t3 := writeBit t host2 (loanValue2 t g v1 u0 u1 u2 e0 host1)
 let S1 : State := ⟨s.phase,t3⟩
 have p : ∀ r, run (clear2 u3 r3 host2 host3) r s = S0 := by
  intro r
  exact clear2_run u3 r3 host2 host3 (by tauto) (by tauto) (by tauto) s r hk3
 have q : ∀ r, run (finish3 g v1 u0 u1 u2 r0 r1 r2 e0 cache host1 host2) r S0 = S1 := by
  intro r
  rw [finish3_run g v1 u0 u1 u2 r0 r1 r2 e0 cache host1 host2 nd12 S0 r]
  · simp [S1,t3,t,S0,writeBit,Function.update_apply,show u0≠host3 by tauto,
     show u1≠host3 by tauto,show e0≠host3 by tauto]
  · simpa [S0,writeBit,Function.update_apply,show cache≠host3 by tauto,
     show u0≠host3 by tauto,show r0≠host3 by tauto] using hk0
  · simpa [S0,writeBit,Function.update_apply,show host1≠host3 by tauto,
     show u1≠host3 by tauto,show r1≠host3 by tauto,show cache≠host3 by tauto] using hk1
  · simpa [S0,writeBit,Function.update_apply,show host2≠host3 by tauto,
     show u2≠host3 by tauto,show r2≠host3 by tauto,show host1≠host3 by tauto] using hk2
 have z : ∀ r, run (FourthCarryLoan.restore3 v1 v2 u0 u2 u3 e0 host2 host3) r S1 =
   ⟨s.phase,writeBit t3 host3 (FourthCarryLoan.value t3 v1 v2 u0 u2 u3 e0 host2)⟩ := by
  intro r
  rw [FourthCarryLoan.restore3_run v1 v2 u0 u2 u3 e0 host2 host3 nd8 S1 r]
  have hz : S1.basis host3 = false := by
   simp [S1,t3,t,S0,writeBit,Function.update_apply,
    show host3≠cache by tauto,show host3≠host1 by tauto,show host3≠host2 by tauto]
  simp only [hz,Bool.false_xor]
  rfl
 dsimp only
 rw [finish4,run_append,p,run_append,q,z]
#print axioms prepare4_run
#print axioms finish4_run
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryGeometry
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem bit3_mem (xs : List Wire) (h : 4 ≤ xs.length) : bit3 xs ∈ xs := by
 obtain ⟨a,b,c,d,ys,rfl⟩ := split_four xs h
 simp [bit3]

theorem head4_count (xs : List Wire) (h : 4 ≤ xs.length) (q : Wire) :
 [xs.headD 0,bit1 xs,bit2 xs,bit3 xs].count q ≤ xs.count q := by
 obtain ⟨a,b,c,d,ys,rfl⟩ := split_four xs h
 simp only [bit1,bit2,bit3,List.headD_cons,List.drop_succ_cons,List.drop_zero]
 simp only [List.count_cons,List.count_nil]
 omega

def host3Wire (L : CuccaroStreamedSquareWideLayout) : Wire := bit3 (eReg L)

theorem host3_mem (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : host3Wire L ∈ eReg L :=
 bit3_mem _ (by simp [eReg_length L hw])

theorem geometry16 (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (g : Wire) (hg : g ∉ L.wires) :
 [g,bit1 L.core.high,bit2 L.core.high,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,
  cacheWire L,hostWire L,host2Wire L,host3Wire L].Nodup := by
 have geo := mGeo L hw hn
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have uc := head4_count (mU L) (by rw [geo.u]; decide) q
 have rc := head4_count (mR L) (by rw [geo.r]; decide) q
 have ec := head4_count ((eReg L).take 129) (by simp [eReg_length L hw]) q
 have hhead : ((eReg L).take 129).headD 0 = (eReg L).headD 0 := head_take_pos _ _ (by decide)
 have hbit : bit1 ((eReg L).take 129) = hostWire L := bit1_take _ _ (by decide)
 have hbit2 : bit2 ((eReg L).take 129) = host2Wire L := bit2_take _ _ (by decide)
 have hbit3 : bit3 ((eReg L).take 129) = host3Wire L := bit3_take _ _ (by decide)
 rw [hhead,hbit,hbit2,hbit3] at ec
 have ed := congrArg (List.count q) (cache_decomp L hw)
 have ud : (mU L).count q ≤ (hiReg L).count q := (List.drop_sublist _ _).count_le q
 have rd : (mR L).count q ≤ L.core.work.count q :=
  ((List.take_sublist _ _).trans (List.drop_sublist _ _)).count_le q
 have hy : 3 ≤ L.core.high.length := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
 have hv := head3_count L.core.high hy q
 have vy : L.core.high.count q ≤ L.core.y.count q := by
  apply List.Sublist.count_le
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)
 have vc : ([bit1 L.core.high,bit2 L.core.high] : List Wire).count q ≤ L.core.y.count q := by
  simp only [List.count_cons,List.count_nil] at hv ⊢
  omega
 have ps := productSplit L q
 have es := eReg_count L q
 have lc := List.nodup_iff_count_le_one.mp (List.nodup_cons.mpr ⟨hg,hn⟩) q
 simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
  List.count_cons,List.count_append,List.count_nil] at lc uc rc ec ed vc ⊢
 omega
#print axioms geometry16
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryBits
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem bstate_heads4 (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (base s:BasisState) (hc:L.PairClean base) (O E b1:Nat) (hb1:regValue (hiReg L) base=b1)
 (hb1lt:b1<2^128) (h:BState L base O E (4294968272*b1) s):
 s (bit3 (mU L))=digit (b1/2^96) 3 ∧
 s (bit3 (mR L))=digit (b1/2^96+(4294968272*b1/2^128-b1/2^96)) 3 := by
 have g:=mGeo L hw hn
 obtain ⟨h1,h2,h3⟩:=whi_split b1 hb1lt
 have hr:=mR_value L hw hn base hc O E (4294968272*b1) s h
 have hv:regValue (mR L) s=b1/2^96+(4294968272*b1/2^128-b1/2^96):=by
  rw[hr.1,Nat.mod_eq_of_lt (by omega)]
  omega
 have hu:=bstate_u L hw hn base s O E b1 hb1 h
 constructor
 · rw[bit3_parity (mU L) s (by rw[g.u];decide),hu]
 · rw[bit3_parity (mR L) s (by rw[g.r];decide),hv]

theorem host3_ne_key (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 host3Wire L≠eU L := by
 have shape:=(eShape L hw).1
 have len:(eRlow L).length=128:=by simp[eRlow,hw.core.product]
 have hm:host3Wire L∈eRlow L:=by
  unfold host3Wire
  rw[shape,bit3_append _ _ (by rw[len];decide)]
  exact bit3_mem _ (by rw[len];decide)
 have nd:=eReg_nodup L hn
 rw[shape]at nd
 exact (List.nodup_append.mp nd).2.2 _ hm _ (by simp)

#print axioms bstate_heads4
#print axioms host3_ne_key
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryEndsResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ECDSAAdd.RecordedQuantum
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem prepare4_counts (g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3 : Wire) :
 toffoliCount (prepare4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3) = 4 ∧
 measurementCount (prepare4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3) = 3 ∧
 Challenge.gateSlots (prepare4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3) = 46 := by
 refine ⟨rfl,rfl,?_⟩
 simp [prepare4,FourthCarryLoan.loan3,prepare3,loan2,SecondCarryLoan.prepare,loan,prime,prime2,majority,
  Challenge.gateSlots,Challenge.instructionSlots]

theorem finish4_counts (g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3 : Wire) :
 toffoliCount (finish4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3) = 5 ∧
 measurementCount (finish4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3) = 4 ∧
 Challenge.gateSlots (finish4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3) = 40 := by
 refine ⟨rfl,rfl,?_⟩
 simp [finish4,FourthCarryLoan.restore3,finish3,restore2,SecondCarryLoan.finish,clear,clear2,restore,
  Challenge.gateSlots,Challenge.instructionSlots]

#print axioms prepare4_counts
#print axioms finish4_counts
theorem ends4_physical (g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3 : Wire)
 (nd : [g,v1,v2,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2,h3].Nodup) :
 GatePhysical (prepare4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3) ∧
 GatePhysical (finish4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3) := by
 have nd12 := geometry16_12 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3 nd
 have nd8 := geometry16_8 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3 nd
 have nd4 : [u3,r3,h2,h3].Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp nd q
  simp only [List.count_cons,List.count_nil] at h ⊢
  omega
 have a := FourthCarryLoan.physical v1 v2 u0 u2 u3 e0 h2 h3 nd8
 have b := ends3_physical g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2 nd12
 have p : GatePhysical (prime2 u3 r3 h2 h3) ∧ GatePhysical (clear2 u3 r3 h2 h3) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false] at nd4
  simp [prime2,majority,clear2,GatePhysical,PhysicalInstr,ProperGate]
  tauto
 simp only [prepare4,finish4,gatePhysical_append]
 exact ⟨⟨a.1,b.1,p.1⟩,p.2,b.2,a.2⟩

theorem ends4_support (g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3 : Wire) :
 wires (prepare4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3) ⊆
 [g,v1,v2,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2,h3].toFinset ∧
 wires (finish4 g v1 v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 h3) ⊆
 [g,v1,v2,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2,h3].toFinset := by
 have a := FourthCarryLoan.support v1 v2 u0 u2 u3 e0 h2 h3
 have b := ends3_support g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2
 have p : wires (prime2 u3 r3 h2 h3) ⊆ [u3,r3,h2,h3].toFinset ∧
   wires (clear2 u3 r3 h2 h3) ⊆ [u3,r3,h2,h3].toFinset := by
  constructor <;> intro q h <;>
   simp [prime2,majority,clear2,ECDSAAdd.wires,Instr.wires,correctionWires] at h ⊢ <;> tauto
 constructor <;> intro q h
 · simp only [prepare4,wires_append,Finset.mem_union] at h
   rcases h with h|h|h
   · have z := a.1 h; simp only [List.mem_toFinset,List.mem_cons,List.mem_singleton] at z ⊢; tauto
   · have z := b.1 h; simp only [List.mem_toFinset,List.mem_cons,List.mem_singleton] at z ⊢; tauto
   · have z := p.1 h; simp only [List.mem_toFinset,List.mem_cons,List.mem_singleton] at z ⊢; tauto
 · simp only [finish4,wires_append,Finset.mem_union] at h
   rcases h with h|h|h
   · have z := p.2 h; simp only [List.mem_toFinset,List.mem_cons,List.mem_singleton] at z ⊢; tauto
   · have z := b.2 h; simp only [List.mem_toFinset,List.mem_cons,List.mem_singleton] at z ⊢; tauto
   · have z := a.2 h; simp only [List.mem_toFinset,List.mem_cons,List.mem_singleton] at z ⊢; tauto
#print axioms prepare4_counts
#print axioms finish4_counts
#print axioms ends4_physical
#print axioms ends4_support
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryPatches
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem add4_patch (cache0 cache1 cache2 cache3 : Wire) (x y cs : List Wire) (cin : Wire)
 (hx : 5 ≤ x.length) (hy : 5 ≤ y.length) (hc : 4 ≤ cs.length) :
 Patch cache3 1 (addCCCC cache0 cache1 cache2 cache3 x y cs cin) (addCCC cache0 cache1 cache2 x y cs cin) := by
 obtain ⟨a0,a1,a2,a3,a4,xs,rfl⟩ := split_five x hx
 obtain ⟨b0,b1,b2,b3,b4,ys,rfl⟩ := split_five y hy
 obtain ⟨k0,k1,k2,k3,ks,rfl⟩ := split_four cs hc
 have p := add3_patch cache1 cache2 cache3 (a1::a2::a3::a4::xs) (b1::b2::b3::b4::ys) (k1::k2::k3::ks) k0
  (by simp) (by simp) (by simp)
 have h := (Patch.refl cache3 [.CX cache0 k0]).app
  (p.app (Patch.refl cache3 (mappedEraseCarry ⟨some a0,false⟩ b0 cin k0 ++ mappedSum ⟨some a0,false⟩ b0 cin)))
 simpa only [addCCCC,addCCC,addCC,cachedMapped4,cachedMapped3,cachedMapped2,mappedRead,List.map_cons,
  Nat.zero_add,Nat.add_zero,List.append_assoc] using h

theorem sub4_patch (cache0 cache1 cache2 cache3 : Wire) (expected : Bool) (x y cs : List Wire)
 (flags : List Bool) (cin : Wire) (hx : 5 ≤ x.length) (hy : 5 ≤ y.length) (hc : 4 ≤ cs.length)
 (hf : 5 ≤ flags.length) (hf1 : flags.getD 1 false = false) (hf2 : flags.getD 2 false = false)
 (hf3 : flags.getD 3 false = false) (hf4 : flags.getD 4 false = false) :
 Patch cache3 1 (cachedSub4 cache0 cache1 cache2 cache3 expected (mappedRead x false) flags y cs cin)
  (cachedSub3 cache0 cache1 cache2 expected (mappedRead x false) flags y cs cin) := by
 obtain ⟨a0,a1,a2,a3,a4,xs,rfl⟩ := split_five x hx
 obtain ⟨b0,b1,b2,b3,b4,ys,rfl⟩ := split_five y hy
 obtain ⟨k0,k1,k2,k3,ks,rfl⟩ := split_four cs hc
 obtain ⟨f0,f1,f2,f3,f4,fs,rfl⟩ := split_five flags hf
 have h1 : f1=false := by simpa using hf1
 have h2 : f2=false := by simpa using hf2
 have h3 : f3=false := by simpa using hf3
 have h4 : f4=false := by simpa using hf4
 subst f1; subst f2; subst f3; subst f4
 have inner := (majority_patch cache3 a3 b3 k2 k3).app (Patch.refl cache3
  (MixedLiteralAdderDevelop.program expected (mappedRead (a4::xs) false) (b4::ys) (false::fs) ks k3 ++
   mappedEraseCarry ⟨some a3,false⟩ b3 k2 k3 ++ mappedSum ⟨some a3,false⟩ b3 k2))
 have third := (Patch.refl cache3 [.CX cache2 k2]).app (inner.app (Patch.refl cache3
  (mappedEraseCarry ⟨some a2,false⟩ b2 k1 k2 ++ mappedSum ⟨some a2,false⟩ b2 k1)))
 have middle := (Patch.refl cache3 [.CX cache1 k1]).app (third.app (Patch.refl cache3
  (mappedEraseCarry ⟨some a1,false⟩ b1 k0 k1 ++ mappedSum ⟨some a1,false⟩ b1 k0)))
 have outer := (Patch.refl cache3 [.CX cache0 k0]).app (middle.app (Patch.refl cache3
  (mappedEraseCarry ⟨some a0,false⟩ b0 cin k0 ++ mappedSum ⟨some a0,false⟩ b0 cin)))
 have h := (Patch.refl cache3 (notRegister (b0::b1::b2::b3::b4::ys))).app
  (outer.app (Patch.refl cache3 (notRegister (b0::b1::b2::b3::b4::ys))))
 simpa only [cachedSub4,cachedSub3,cachedMixed4,cachedMixed3,cachedMixed2,cachedMixed,
  MixedLiteralAdderDevelop.program,MixedLiteralAdderDevelop.head,mappedRead,List.map_cons,mappedMajority,
  Bool.false_eq_true,if_false,Nat.add_zero,Nat.zero_add,List.append_assoc] using h
#print axioms add4_patch
#print axioms sub4_patch
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryArmPatches
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem sub33CCCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2 cache3:Wire):
 Patch cache3 1 (sub33CCCC cache0 cache1 cache2 cache3 R Z cs U cin) (sub33CCC cache0 cache1 cache2 R Z cs U cin):=by
 exact sub4_patch cache0 cache1 cache2 cache3 true (U++Z.take 1) (R.take 33) (cs.take 32)
  MixedLiteralAdderDevelop.upper33 cin (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
  (by decide) (by decide) (by decide) (by decide) (by decide)

theorem sub43CCCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2 cache3:Wire):
 Patch cache3 1 (sub43CCCC cache0 cache1 cache2 cache3 R Z cs U cin) (sub43CCC cache0 cache1 cache2 R Z cs U cin):=by
 exact sub4_patch cache0 cache1 cache2 cache3 true (U++Z) (R.take 43) (cs.take 42)
  MixedLiteralAdderDevelop.mask43 cin (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
  (by decide) (by decide) (by decide) (by decide) (by decide)

theorem fwdCCCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2 cache3 k:Wire):
 Patch cache3 2 (fwdCCCC R S Z cs U cin k cache0 cache1 cache2 cache3) (fwdCCC R S Z cs U cin k cache0 cache1 cache2):=by
 have a:=add4_patch cache0 cache1 cache2 cache3 (U++Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
 have kp:=Patch.refl cache3 (WinArith.kpat k Z)
 exact (sub33CCCC_patch (cin:=cin) g cache0 cache1 cache2 cache3).app
  ((Patch.refl cache3 (copyRegister none ((R.drop 0).take 10) S)).app
   ((Patch.refl cache3 (WinArithAux3SmallDevelop.smallF R S cs cin)).app
    ((Patch.refl cache3 (copyRegister none S ((R.drop 32).take 10))).app
     ((Patch.refl cache3 (copyRegister none ((R.drop 32).take 10) S)).app (kp.app (a.app kp))))))

theorem invCCCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2 cache3 k:Wire):
 Patch cache3 2 (invCCCC R S Z cs U cin k cache0 cache1 cache2 cache3) (invCCC R S Z cs U cin k cache0 cache1 cache2):=by
 have a:=add4_patch cache0 cache1 cache2 cache3 (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
 have kp:=Patch.refl cache3 (WinArith.kpat k Z)
 exact kp.app ((sub43CCCC_patch (cin:=cin) g cache0 cache1 cache2 cache3).app (kp.app
  ((Patch.refl cache3 (copyRegister none ((R.drop 32).take 10) S)).app
   ((Patch.refl cache3 (copyRegister none S ((R.drop 32).take 10))).app
    ((Patch.refl cache3 (WinArithAux3SmallDevelop.smallI R S cs cin)).app
     ((Patch.refl cache3 (copyRegister none ((R.drop 0).take 10) S)).app a))))))

theorem midCCCC_patch (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 Patch (host3Wire L) 4
  (wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) ++
   (wCoreK L ++ wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L)))
  (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L) ++
   (wCoreK L ++ wInvCCC L (cacheWire L) (hostWire L) (host2Wire L))) :=
 (fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) (eU L)).app
  ((Patch.refl _ (wCoreK L)).app
   (invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) (eU L)))
#print axioms fwdCCCC_patch
#print axioms invCCCC_patch
#print axioms midCCCC_patch
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryFull
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def wMidFullCCCC (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
 prepare4 c (bit1 L.core.high) (bit2 L.core.high) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) ++
 ((wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) ++
  (wCoreK L ++ wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L))) ++
 finish4 c (bit1 L.core.high) (bit2 L.core.high) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L))

theorem wMidFullCCCC_step (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (c:Wire) (hcw:c∉L.wires) (base:BasisState) (hc:L.PairClean base) (O E b1:Nat)
 (hb1:regValue (hiReg L) base=b1) (hb1lt:b1<2^128) (hO:O<SquareReduction.p)
 (H l K:Nat) (hH:H<2^96) (hl:l<2^32) (hK:K≤1) (hE:E=2^32*H+l+2^128*K)
 (hLoan:(E/2%2==1)=((b1/2^96/2%2==1) ^^ (b1/2^96%2==1) ^^
   ((b1/2^96%2==1)&&(E%2==1))))
 (hLoan2:digit E 2= (digit (b1/2^96) 2 ^^
   (base (bit1 L.core.high)&&base c) ^^ (base (bit1 L.core.high)&&digit E 0) ^^
   (base (bit1 L.core.high)&&digit (b1/2^96) 0) ^^
   (digit (b1/2^96) 1&&digit E 1) ^^ digit (b1/2^96) 1))
 (hLoan3 : digit E 3 = (digit (b1/2^96) 3 ^^
  ((digit E 0 ^^ digit (b1/2^96) 0) && (base (bit1 L.core.high) ^^ base (bit2 L.core.high))) ^^
  (digit (b1/2^96) 2 && digit E 2) ^^ digit (b1/2^96) 2)) :
 Triple (BState L base O E (4294968272*b1)) (wMidFullCCCC L c)
 (BState L base (((b1/2^96+4294968273*(4294968272*b1/2^128-b1/2^96))+4294968272*2^32*K+
   2^128*((4294968272*b1)%2^128)+(SquareReduction.p-1-O))%SquareReduction.p) E (4294968272*b1)) := by
 intro s m h
 let u0:Wire:=(mU L).headD 0
 let u1:Wire:=bit1 (mU L)
 let u2:Wire:=bit2 (mU L)
 let u3:Wire:=bit3 (mU L)
 let r0:Wire:=(mR L).headD 0
 let r1:Wire:=bit1 (mR L)
 let r2:Wire:=bit2 (mR L)
 let r3:Wire:=bit3 (mR L)
 let e0:Wire:=(eReg L).headD 0
 let v:Wire:=bit1 L.core.high
 let v2:Wire:=bit2 L.core.high
 let cache:Wire:=cacheWire L
 let host:Wire:=hostWire L
 let host2:Wire:=host2Wire L
 let host3:Wire:=host3Wire L
 let u:=b1/2^96
 let d:=4294968272*b1/2^128-u
 let k0:Bool:=(u%2==1)&&(d%2==1)
 let k1:Bool:=carryLow2 u d
 let k2:Bool:=carryLow3 u d
 let k3:Bool:=carryLow4 u d
 have nd:[c,v,v2,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,host,host2,host3].Nodup:=geometry16 L hw hn c hcw
 have geom:=nd
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geom
 have nv2 : v2 ≠ host3 := FourthCarryLoan.get_ne _ nd 2 15 (by simp) (by simp) (by decide)
 have nc : c ≠ host3 := FourthCarryLoan.get_ne _ nd 0 15 (by simp) (by simp) (by decide)
 have nv : v ≠ host3 := FourthCarryLoan.get_ne _ nd 1 15 (by simp) (by simp) (by decide)
 have nu0 : u0 ≠ host3 := FourthCarryLoan.get_ne _ nd 3 15 (by simp) (by simp) (by decide)
 have nu1 : u1 ≠ host3 := FourthCarryLoan.get_ne _ nd 4 15 (by simp) (by simp) (by decide)
 have nu2 : u2 ≠ host3 := FourthCarryLoan.get_ne _ nd 5 15 (by simp) (by simp) (by decide)
 have nu3 : u3 ≠ host3 := FourthCarryLoan.get_ne _ nd 6 15 (by simp) (by simp) (by decide)
 have nr0 : r0 ≠ host3 := FourthCarryLoan.get_ne _ nd 7 15 (by simp) (by simp) (by decide)
 have nr1 : r1 ≠ host3 := FourthCarryLoan.get_ne _ nd 8 15 (by simp) (by simp) (by decide)
 have nr2 : r2 ≠ host3 := FourthCarryLoan.get_ne _ nd 9 15 (by simp) (by simp) (by decide)
 have nr3 : r3 ≠ host3 := FourthCarryLoan.get_ne _ nd 10 15 (by simp) (by simp) (by decide)
 have ne0 : e0 ≠ host3 := FourthCarryLoan.get_ne _ nd 11 15 (by simp) (by simp) (by decide)
 have ncache : cache ≠ host3 := FourthCarryLoan.get_ne _ nd 12 15 (by simp) (by simp) (by decide)
 have nhost : host ≠ host3 := FourthCarryLoan.get_ne _ nd 13 15 (by simp) (by simp) (by decide)
 have nhost2 : host2 ≠ host3 := FourthCarryLoan.get_ne _ nd 14 15 (by simp) (by simp) (by decide)
 have ce:cache∈eReg L:=cache_mem L hw
 have he:host∈eReg L:=host_mem L hw
 have he2:host2∈eReg L:=host2_mem L hw
 have he3:host3∈eReg L:=host3_mem L hw
 have ca:=external_away L c hcw
 have vy:v∈L.core.y:=List.mem_of_mem_drop (List.mem_of_mem_take
  (bit1_mem L.core.high (by simp[CuccaroStreamedSquareLayout.high,hw.core.y,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2])))
 have va:=source_away L hn v vy
 have vy2 : v2 ∈ L.core.y := List.mem_of_mem_drop (List.mem_of_mem_take
  (bit2_mem L.core.high (by simp [CuccaroStreamedSquareLayout.high,hw.core.y])))
 have va2 := source_away L hn v2 vy2
 have sg:s.basis c=base c:=h.2.2.2 c ca.1 ca.2.1 ca.2.2
 have sv:s.basis v=base v:=h.2.2.2 v va.1 va.2.1 va.2.2
 have sv2 : s.basis v2 = base v2 := h.2.2.2 v2 va2.1 va2.2.1 va2.2.2
 have hz:s.basis cache=false:=e_cache_zero L hw s.basis E h.2.1 (by rw[hE];omega)
 have b0:=bstate_heads L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b1s:=bstate_heads2 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b2:=bstate_heads3 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b3:=bstate_heads4 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have es:s.basis e0=(E%2==1):=by
  dsimp[e0,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2];rw[head_parity (eReg L) s.basis (by simp[eReg_length L hw,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2]),h.2.1]
 have hs:s.basis host=(E/2%2==1):=by
  dsimp[host,hostWire,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2];rw[bit1_parity (eReg L) s.basis (by simp[eReg_length L hw,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2]),h.2.1]
 have hs2:s.basis host2=digit E 2:=by
  dsimp[host2,host2Wire,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2];rw[bit2_parity (eReg L) s.basis (by simp[eReg_length L hw,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2]),h.2.1]
 have hs3 : s.basis host3 = digit E 3 := by
  dsimp [host3,host3Wire]; rw [bit3_parity (eReg L) s.basis (by simp [eReg_length L hw]),h.2.1]
 have ready:s.basis host=(s.basis u1 ^^ s.basis u0 ^^ (s.basis u0&&s.basis e0)):=by
  rw[hs,b0.1,b1s.1,es];exact hLoan
 have ready2:s.basis host2=loanValue2 s.basis c v u0 u1 u2 e0 host:=by
  rw[hs2]
  unfold loanValue2
  rw[b2.1,b0.1,b1s.1,es,hs,sg,sv]
  simpa only[digit,pow_zero,pow_one,Nat.div_one,v]using hLoan2
 have ready3 : s.basis host3 = FourthCarryLoan.value s.basis v v2 u0 u2 u3 e0 host2 := by
  rw [hs3]
  unfold FourthCarryLoan.value
  rw [b3.1,b2.1,b0.1,es,hs2,sv,sv2]
  simpa only [digit,pow_zero,Nat.div_one,v,v2] using hLoan3
 have carry0:(s.basis u0&&!s.basis r0)=k0:=by
  rw[b0.1,b0.2];simpa only[Nat.one_mul]using carry_parity u d 1 (by decide)
 have carry1:carryBit (s.basis u1) (!s.basis r1) k0=k1:=by
  rw[b1s.1,b1s.2];simpa only[Nat.one_mul]using sub_second u d 1 (by decide)
 have carry2:carryBit (s.basis u2) (!s.basis r2) k1=k2:=by
  rw[b2.1,b2.2];simpa only[Nat.one_mul]using sub_third u d 1 (by decide)
 have carry3 : carryBit (s.basis u3) (!s.basis r3) k2 = k3 := by
  rw [b3.1,b3.2]; simpa only [Nat.one_mul] using sub_fourth u d 1 (by decide)
 let t:BasisState:=writeBit (writeBit (writeBit (writeBit s.basis cache k0) host k1) host2 k2) host3 k3
 let EP:Nat:=regValue (eReg L) t
 have prepared:∀mm,run (prepare4 c v v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2 host3) mm s=⟨s.phase,t⟩:=by
  intro mm
  rw[prepare4_run c v v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2 host3 nd s mm hz ready ready2 ready3,carry0,carry1,carry2,carry3]
 have hb0:=bstate_write_e L hn cache ce base s.basis O E _ h k0
 have hb2:=bstate_write_e L hn host he base (writeBit s.basis cache k0) O
  (regValue (eReg L) (writeBit s.basis cache k0)) _ hb0 k1
 have hb3:=bstate_write_e L hn host2 he2 base (writeBit (writeBit s.basis cache k0) host k1) O
  (regValue (eReg L) (writeBit (writeBit s.basis cache k0) host k1)) _ hb2 k2
 have hb4 := bstate_write_e L hn host3 he3 base
  (writeBit (writeBit (writeBit s.basis cache k0) host k1) host2 k2) O
  (regValue (eReg L) (writeBit (writeBit (writeBit s.basis cache k0) host k1) host2 k2)) _ hb3 k3
 have inp:BState L base O EP (4294968272*b1) t ∧ t cache=k0 ∧ t host=k1 ∧ t host2=k2 ∧ t host3=k3 ∧
  (if t (eU L) then 1 else 0)=K:=by
  refine ⟨hb4,?_,?_,?_,?_,?_⟩
  · simp[t,writeBit,Function.update_apply,show cache≠host from FourthCarryLoan.get_ne _ nd 12 13 (by simp) (by simp) (by decide),show cache≠host2 from FourthCarryLoan.get_ne _ nd 12 14 (by simp) (by simp) (by decide),nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2]
  · simp[t,writeBit,Function.update_apply,show host≠host2 from FourthCarryLoan.get_ne _ nd 13 14 (by simp) (by simp) (by decide),nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2]
  · simp[t,writeBit,Function.update_apply,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2]
  · simp[t,writeBit,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2]
  · have hk:=bstate_key L hw s.basis E H l K h.2.1 hH hl hK hE
    simpa[t,writeBit,Function.update_apply,show eU L≠cache from (cache_ne_k L hw hn).symm,
     show eU L≠host from (host_ne_key L hw hn).symm,show eU L≠host2 from (host2_ne_key L hw hn).symm,show eU L≠host3 from (host3_ne_key L hw hn).symm]using hk
 let mid:=wFwdCCCC L cache host host2 host3++(wCoreK L++wInvCCCC L cache host host2 host3)
 let rest:=m.drop (measurementCount (prepare4 c v v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2 host3))
 let mmid:=rest.take (measurementCount mid)
 rw[wMidFullCCCC,run_append,prepared,run_append]
 have hm:=wMidCCCC_step L hw hn cache ce host he host2 he2 host3 he3 base hc O EP b1 hb1 hb1lt hO K hK
  (⟨s.phase,t⟩:State) mmid inp
 generalize hr:run mid mmid (⟨s.phase,t⟩:State)=r at hm ⊢
 have br0:=bstate_heads L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br1:=bstate_heads2 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br2:=bstate_heads3 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br3:=bstate_heads4 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have er:∀q∈eReg L,r.basis q=t q:=(regValue_eq_iff _ _ _).mp hm.2.1.2.1
 have rE0:r.basis e0=s.basis e0:=by
  rw[er e0 (head_mem _ (by simp[eReg_length L hw,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2]))]
  simp[t,writeBit,Function.update_apply,show e0≠host from FourthCarryLoan.get_ne _ nd 11 13 (by simp) (by simp) (by decide),show e0≠cache from FourthCarryLoan.get_ne _ nd 11 12 (by simp) (by simp) (by decide),show e0≠host2 from FourthCarryLoan.get_ne _ nd 11 14 (by simp) (by simp) (by decide),nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2]
 have rU0:r.basis u0=s.basis u0:=br0.1.trans b0.1.symm
 have rU1:r.basis u1=s.basis u1:=br1.1.trans b1s.1.symm
 have rU2:r.basis u2=s.basis u2:=br2.1.trans b2.1.symm
 have rR0:r.basis r0=s.basis r0:=br0.2.trans b0.2.symm
 have rR1:r.basis r1=s.basis r1:=br1.2.trans b1s.2.symm
 have rR2:r.basis r2=s.basis r2:=br2.2.trans b2.2.symm
 have rU3 : r.basis u3 = s.basis u3 := br3.1.trans b3.1.symm
 have rR3 : r.basis r3 = s.basis r3 := br3.2.trans b3.2.symm
 have rV2 : r.basis v2 = s.basis v2 := (hm.2.1.2.2.2 v2 va2.1 va2.2.1 va2.2.2).trans sv2.symm
 have rG:r.basis c=s.basis c:=(hm.2.1.2.2.2 c ca.1 ca.2.1 ca.2.2).trans sg.symm
 have rV:r.basis v=s.basis v:=(hm.2.1.2.2.2 v va.1 va.2.1 va.2.2).trans sv.symm
 have rk:r.basis cache=(r.basis u0&&!r.basis r0):=by
  rw[rU0,rR0,carry0];exact hm.2.2.1
 have rk1:r.basis host=carryBit (r.basis u1) (!r.basis r1) (r.basis cache):=by
  rw[rU1,rR1,hm.2.2.1,carry1];exact hm.2.2.2.1
 have rk2:r.basis host2=carryBit (r.basis u2) (!r.basis r2) (r.basis host):=by
  rw[rU2,rR2,hm.2.2.2.1,carry2];exact hm.2.2.2.2.1
 have rk3 : r.basis host3 = carryBit (r.basis u3) (!r.basis r3) (r.basis host2) := by
  rw [rU3,rR3,hm.2.2.2.2.1,carry3]; exact hm.2.2.2.2.2.1
 have restored:(r.basis u1 ^^ r.basis u0 ^^ (r.basis u0&&r.basis e0))=s.basis host:=by
  rw[rU1,rU0,rE0];exact ready.symm
 rw[finish4_run c v v2 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2 host3 nd r _ rk rk1 rk2 rk3]
 dsimp only
 rw[restored]
 let t0:=writeBit (writeBit (writeBit (writeBit r.basis host3 false) host2 false) host (s.basis host)) cache false
 have restored2:loanValue2 t0 c v u0 u1 u2 e0 host=s.basis host2:=by
  dsimp[loanValue2,t0,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2]
  simp only[writeBit,Function.update_apply,
   show c≠cache from FourthCarryLoan.get_ne _ nd 0 12 (by simp) (by simp) (by decide),show c≠host from FourthCarryLoan.get_ne _ nd 0 13 (by simp) (by simp) (by decide),show c≠host2 from FourthCarryLoan.get_ne _ nd 0 14 (by simp) (by simp) (by decide),
   show v≠cache from FourthCarryLoan.get_ne _ nd 1 12 (by simp) (by simp) (by decide),show v≠host from FourthCarryLoan.get_ne _ nd 1 13 (by simp) (by simp) (by decide),show v≠host2 from FourthCarryLoan.get_ne _ nd 1 14 (by simp) (by simp) (by decide),
   show u0≠cache from FourthCarryLoan.get_ne _ nd 3 12 (by simp) (by simp) (by decide),show u0≠host from FourthCarryLoan.get_ne _ nd 3 13 (by simp) (by simp) (by decide),show u0≠host2 from FourthCarryLoan.get_ne _ nd 3 14 (by simp) (by simp) (by decide),
   show u1≠cache from FourthCarryLoan.get_ne _ nd 4 12 (by simp) (by simp) (by decide),show u1≠host from FourthCarryLoan.get_ne _ nd 4 13 (by simp) (by simp) (by decide),show u1≠host2 from FourthCarryLoan.get_ne _ nd 4 14 (by simp) (by simp) (by decide),
   show u2≠cache from FourthCarryLoan.get_ne _ nd 5 12 (by simp) (by simp) (by decide),show u2≠host from FourthCarryLoan.get_ne _ nd 5 13 (by simp) (by simp) (by decide),show u2≠host2 from FourthCarryLoan.get_ne _ nd 5 14 (by simp) (by simp) (by decide),
   show e0≠cache from FourthCarryLoan.get_ne _ nd 11 12 (by simp) (by simp) (by decide),show e0≠host from FourthCarryLoan.get_ne _ nd 11 13 (by simp) (by simp) (by decide),show e0≠host2 from FourthCarryLoan.get_ne _ nd 11 14 (by simp) (by simp) (by decide),
   show host≠cache from FourthCarryLoan.get_ne _ nd 13 12 (by simp) (by simp) (by decide),ite_false,ite_true,rG,rV,rU0,rU1,rU2,rE0,nc,nv,nv2,nu0,nu1,nu2,nu3,nr0,nr1,nr2,nr3,ne0,ncache,nhost,nhost2]
  exact ready2.symm
 let t3 := writeBit t0 host2 (loanValue2 t0 c v u0 u1 u2 e0 host)
 have restored3 : FourthCarryLoan.value t3 v v2 u0 u2 u3 e0 host2 = s.basis host3 := by
  dsimp only [t3]
  rw [restored2]
  dsimp [FourthCarryLoan.value,t0]
  simp only [writeBit,Function.update_apply,
   show v≠cache from FourthCarryLoan.get_ne _ nd 1 12 (by simp) (by simp) (by decide),show v≠host from FourthCarryLoan.get_ne _ nd 1 13 (by simp) (by simp) (by decide),show v≠host2 from FourthCarryLoan.get_ne _ nd 1 14 (by simp) (by simp) (by decide),nv,
   show v2≠cache from FourthCarryLoan.get_ne _ nd 2 12 (by simp) (by simp) (by decide),show v2≠host from FourthCarryLoan.get_ne _ nd 2 13 (by simp) (by simp) (by decide),show v2≠host2 from FourthCarryLoan.get_ne _ nd 2 14 (by simp) (by simp) (by decide),nv2,
   show u0≠cache from FourthCarryLoan.get_ne _ nd 3 12 (by simp) (by simp) (by decide),show u0≠host from FourthCarryLoan.get_ne _ nd 3 13 (by simp) (by simp) (by decide),show u0≠host2 from FourthCarryLoan.get_ne _ nd 3 14 (by simp) (by simp) (by decide),nu0,
   show u2≠cache from FourthCarryLoan.get_ne _ nd 5 12 (by simp) (by simp) (by decide),show u2≠host from FourthCarryLoan.get_ne _ nd 5 13 (by simp) (by simp) (by decide),show u2≠host2 from FourthCarryLoan.get_ne _ nd 5 14 (by simp) (by simp) (by decide),nu2,
   show u3≠cache from FourthCarryLoan.get_ne _ nd 6 12 (by simp) (by simp) (by decide),show u3≠host from FourthCarryLoan.get_ne _ nd 6 13 (by simp) (by simp) (by decide),show u3≠host2 from FourthCarryLoan.get_ne _ nd 6 14 (by simp) (by simp) (by decide),nu3,
   show e0≠cache from FourthCarryLoan.get_ne _ nd 11 12 (by simp) (by simp) (by decide),show e0≠host from FourthCarryLoan.get_ne _ nd 11 13 (by simp) (by simp) (by decide),show e0≠host2 from FourthCarryLoan.get_ne _ nd 11 14 (by simp) (by simp) (by decide),ne0,
   ite_false,ite_true,rV,rV2,rU0,rU2,rU3,rE0]
  exact ready3.symm
 refine ⟨hm.1,?_⟩
 have hf0 := bstate_write_e L hn host3 he3 base r.basis _ EP _ hm.2.1 false
 have hf1 := bstate_write_e L hn host2 he2 base (writeBit r.basis host3 false) _
  (regValue (eReg L) (writeBit r.basis host3 false)) _ hf0 false
 have hf2 := bstate_write_e L hn host he base (writeBit (writeBit r.basis host3 false) host2 false) _
  (regValue (eReg L) (writeBit (writeBit r.basis host3 false) host2 false)) _ hf1 (s.basis host)
 have hf3 := bstate_write_e L hn cache ce base (writeBit (writeBit (writeBit r.basis host3 false) host2 false) host (s.basis host)) _
  (regValue (eReg L) (writeBit (writeBit (writeBit r.basis host3 false) host2 false) host (s.basis host))) _ hf2 false
 have hf4 := bstate_write_e L hn host2 he2 base t0 _ (regValue (eReg L) t0) _ hf3 (loanValue2 t0 c v u0 u1 u2 e0 host)
 have hf5 := bstate_write_e L hn host3 he3 base t3 _ (regValue (eReg L) t3) _ hf4 (FourthCarryLoan.value t3 v v2 u0 u2 u3 e0 host2)
 have ev : regValue (eReg L) (writeBit t3 host3 (FourthCarryLoan.value t3 v v2 u0 u2 u3 e0 host2)) = E := by
  rw [restored3]
  dsimp only [t3]
  rw [restored2]
  apply Eq.trans _ h.2.1
  apply regValue_congr
  intro q hq
  by_cases q3 : q=host3
  · subst q; simp [writeBit]
  by_cases q2 : q=host2
  · subst q; simp [writeBit,Function.update_apply,nhost2]
  by_cases q1 : q=host
  · subst q; simp [t0,writeBit,Function.update_apply,nhost,show host≠host2 from FourthCarryLoan.get_ne _ nd 13 14 (by simp) (by simp) (by decide),show host≠cache from FourthCarryLoan.get_ne _ nd 13 12 (by simp) (by simp) (by decide)]
  by_cases qc : q=cache
  · subst q; simp [t0,writeBit,Function.update_apply,ncache,show cache≠host2 from FourthCarryLoan.get_ne _ nd 12 14 (by simp) (by simp) (by decide),hz]
  · simp only [writeBit,Function.update_apply,q3,q2,q1,qc,ite_false,t0]
    rw [er q hq]
    simp [t,writeBit,Function.update_apply,q3,q2,q1,qc]
 simpa only [ev] using hf5
#print axioms wMidFullCCCC_step
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryModLoan
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

theorem loan3_from_mod16 (g : Bool) (originalM u E : Nat)
 (hE : E%16 = lowSum g originalM u%16) :
 digit E 3 = (digit u 3 ^^ ((digit E 0 ^^ digit u 0) && (digit originalM 1 ^^ digit originalM 2)) ^^
  (digit u 2 && digit E 2) ^^ digit u 2) := by
 have h := FourthCarryArithmetic.identity g originalM u
 change digit (lowSum g originalM u) 3 =
  (digit u 3 ^^ ((digit (lowSum g originalM u) 0 ^^ digit u 0) && (digit originalM 1 ^^ digit originalM 2)) ^^
   (digit u 2 && digit (lowSum g originalM u) 2) ^^ digit u 2) at h
 have h0 := digit_congr16 E (lowSum g originalM u) hE ⟨0,by decide⟩
 have h2 := digit_congr16 E (lowSum g originalM u) hE ⟨2,by decide⟩
 have h3 := digit_congr16 E (lowSum g originalM u) hE ⟨3,by decide⟩
 rw [←h0,←h2,←h3] at h
 exact h
#print axioms loan3_from_mod16
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryOldE
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem armsCCCC_oldE (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 wires (wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L))⊆oldE L ∧
 wires (wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L))⊆oldE L:=by
 have hh:host3Wire L∈oldE L:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inr (Or.inl (host3_mem L hw)))))
 have f:=(fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) (eU L)).support
 have i:=(invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) (eU L)).support
 constructor
 · intro q h;rcases Finset.mem_insert.mp (f h)with e|h
   · exact e ▸ hh
   · exact (armsCCC_oldE L hw).1 h
 · intro q h;rcases Finset.mem_insert.mp (i h)with e|h
   · exact e ▸ hh
   · exact (armsCCC_oldE L hw).2 h

theorem ends4_oldE (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g v v2:Wire):
 wires (prepare4 g v v2 ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L))⊆insert g (insert v (insert v2 (oldE L))) ∧
 wires (finish4 g v v2 ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L))⊆insert g (insert v (insert v2 (oldE L))):=by
 have lens:=mLens L hw
 have uMem (q:Wire) (h:q∈mU L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inl (List.mem_of_mem_drop h)))
 have rMem (q:Wire) (h:q∈mR L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h))))
 have eMem (q:Wire) (h:q∈eReg L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inr (Or.inr (Or.inl h))))
 have hu0:=uMem _ (head_mem _ (by rw[lens.u];decide))
 have hu1:=uMem _ (bit1_mem _ (by rw[lens.u];decide))
 have hu2:=uMem _ (bit2_mem _ (by rw[lens.u];decide))
 have hu3:=uMem _ (bit3_mem _ (by rw[lens.u];decide))
 have hr0:=rMem _ (head_mem _ (by rw[lens.r];decide))
 have hr1:=rMem _ (bit1_mem _ (by rw[lens.r];decide))
 have hr2:=rMem _ (bit2_mem _ (by rw[lens.r];decide))
 have hr3:=rMem _ (bit3_mem _ (by rw[lens.r];decide))
 have he0:=eMem _ (head_mem _ (by simp[eReg_length L hw]))
 have hcache:=eMem _ (cache_mem L hw)
 have hh1:=eMem _ (host_mem L hw)
 have hh2:=eMem _ (host2_mem L hw)
 have hh3:=eMem _ (host3_mem L hw)
 have carrier:([g,v,v2,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
    (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,
    cacheWire L,hostWire L,host2Wire L,host3Wire L]:List Wire).toFinset⊆insert g (insert v (insert v2 (oldE L))):=by
  intro q h
  simp only[List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
   simp only[Finset.mem_insert] <;> tauto
 have cap:=ends4_support g v v2 ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
   ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
   (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L)
 exact ⟨cap.1.trans carrier,cap.2.trans carrier⟩

theorem host3_not_mem (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 ¬WinArith.Mem (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (host3Wire L):=by
 have ce:=host3_mem L hw
 have cp:=List.count_pos_iff.mpr (eReg_product L _ ce)
 have lc:=layoutCount L hn (host3Wire L)
 intro hm
 rcases hm with hi|hu|hr|hs|hz|hc
 · have cinPos:0<[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
     L.core.modFlag,L.core.sumCarry].count (host3Wire L):=List.count_pos_iff.mpr (by simp[hi])
   omega
 · exact (eReg_away L hn _ ce).2.2 (List.mem_of_mem_drop hu)
 · have :=List.count_pos_iff.mpr (mR_work L _ hr);omega
 · have :=List.count_pos_iff.mpr (mS_pad L _ hs);omega
 · have :=List.count_pos_iff.mpr (mZ_pad L _ hz);omega
 · have :=List.count_pos_iff.mpr (mC_pad L _ hc);omega

#print axioms armsCCCC_oldE
#print axioms ends4_oldE
#print axioms host3_not_mem
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryMiddleCounts
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem middle_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (wMidFullCCCC L c)+1 = toffoliCount (wMidFullCCC L c) ∧
 measurementCount (wMidFullCCCC L c) = measurementCount (wMidFullCCC L c)+2 ∧
 Challenge.gateSlots (wMidFullCCCC L c) = Challenge.gateSlots (wMidFullCCC L c)+10 := by
 have h := midCCCC_patch L hw
 have ht := h.t; have hm := h.m; have hs := h.slots
 simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at ht hm hs
 have prepT (a b c d e f g h i j k l m n o p : Wire) : toffoliCount (prepare4 a b c d e f g h i j k l m n o p) = 4 := (prepare4_counts a b c d e f g h i j k l m n o p).1
 have prepM (a b c d e f g h i j k l m n o p : Wire) : measurementCount (prepare4 a b c d e f g h i j k l m n o p) = 3 := (prepare4_counts a b c d e f g h i j k l m n o p).2.1
 have prepS (a b c d e f g h i j k l m n o p : Wire) : Challenge.gateSlots (prepare4 a b c d e f g h i j k l m n o p) = 46 := (prepare4_counts a b c d e f g h i j k l m n o p).2.2
 have finT (a b c d e f g h i j k l m n o p : Wire) : toffoliCount (finish4 a b c d e f g h i j k l m n o p) = 5 := (finish4_counts a b c d e f g h i j k l m n o p).1
 have finM (a b c d e f g h i j k l m n o p : Wire) : measurementCount (finish4 a b c d e f g h i j k l m n o p) = 4 := (finish4_counts a b c d e f g h i j k l m n o p).2.1
 have finS (a b c d e f g h i j k l m n o p : Wire) : Challenge.gateSlots (finish4 a b c d e f g h i j k l m n o p) = 40 := (finish4_counts a b c d e f g h i j k l m n o p).2.2
 have oldPT (a b c d e f g h i j k l : Wire) : toffoliCount (prepare3 a b c d e f g h i j k l) = 3 := rfl
 have oldPM (a b c d e f g h i j k l : Wire) : measurementCount (prepare3 a b c d e f g h i j k l) = 2 := rfl
 have oldPS (a b c d e f g h i j k l : Wire) : Challenge.gateSlots (prepare3 a b c d e f g h i j k l) = 30 := by simp [prepare3,loan2,SecondCarryLoan.prepare,prime,loan,prime2,majority,Challenge.gateSlots,Challenge.instructionSlots]
 have oldFT (a b c d e f g h i j k l : Wire) : toffoliCount (finish3 a b c d e f g h i j k l) = 3 := rfl
 have oldFM (a b c d e f g h i j k l : Wire) : measurementCount (finish3 a b c d e f g h i j k l) = 3 := rfl
 have oldFS (a b c d e f g h i j k l : Wire) : Challenge.gateSlots (finish3 a b c d e f g h i j k l) = 26 := by simp [finish3,SecondCarryLoan.finish,clear2,clear,restore,restore2,Challenge.gateSlots,Challenge.instructionSlots]
 simp only [wMidFullCCCC,wMidFullCCC,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
  prepT,prepM,prepS,finT,finM,finS,oldPT,oldPM,oldPS,oldFT,oldFM,oldFS]
 exact ⟨by omega,by omega,by omega⟩
#print axioms middle_counts
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryPhysical
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem middle_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hc : c ∉ L.wires) : GatePhysical (wMidFullCCCC L c) := by
 have hp := ThirdCarryLoanDevelop.middle_physical L hw hn c hc
 simp only [wMidFullCCC,gatePhysical_append] at hp
 have geo := geometry16 L hw hn c hc
 have nc : host3Wire L ≠ cacheWire L := FourthCarryLoan.get_ne _ geo 15 12 (by simp) (by simp) (by decide)
 have n1 : host3Wire L ≠ hostWire L := FourthCarryLoan.get_ne _ geo 15 13 (by simp) (by simp) (by decide)
 have n2 : host3Wire L ≠ host2Wire L := FourthCarryLoan.get_ne _ geo 15 14 (by simp) (by simp) (by decide)
 have af : host3Wire L ∉ wires (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L)) := by
  intro h
  rcases Finset.mem_insert.mp ((fwdCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).support h) with he|h
  · exact n2 he
  rcases Finset.mem_insert.mp ((fwdCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).support h) with he|h
  · exact n1 he
  rcases Finset.mem_insert.mp ((fwdK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support h) with he|h
  · exact nc he
  rcases WinArith.tFwdK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact host3_not_mem L hw hn hm
  · exact host3_ne_key L hw hn he
 have ai : host3Wire L ∉ wires (wInvCCC L (cacheWire L) (hostWire L) (host2Wire L)) := by
  intro h
  rcases Finset.mem_insert.mp ((invCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).support h) with he|h
  · exact n2 he
  rcases Finset.mem_insert.mp ((invCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).support h) with he|h
  · exact n1 he
  rcases Finset.mem_insert.mp ((invK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support h) with he|h
  · exact nc he
  rcases WinArith.tInvK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact host3_not_mem L hw hn hm
  · exact host3_ne_key L hw hn he
 have pf := (fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) (eU L)).phys af hp.2.1.1
 have pi := (invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) (eU L)).phys ai hp.2.1.2.2
 have ends := ends4_physical _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ geo
 simp only [wMidFullCCCC,gatePhysical_append]
 exact ⟨ends.1,⟨pf,hp.2.1.2.1,pi⟩,ends.2⟩
#print axioms middle_physical
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- ParkCarry9Core
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry9Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ParkCarry7Develop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem mid_sumCarry_free (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hc : c ∉ L.wires) : L.core.sumCarry ∉ wires (wMidFullCCCC L c) := by
 have oe := ParkCarry7Develop.oldE_sumCarry_free L hw hn c hc
 have ng : L.core.sumCarry ≠ c := by
  intro h; apply hc
  simp [←h,CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
 have nv : L.core.sumCarry ≠ bit1 L.core.high := by
  intro h
  apply ParkCarryDevelop.sumCarry_away L hn
  have vy := ParkCarry8Develop.sourceHigh_in_y L hw
  rw [←h] at vy
  simp [ParkCarryDevelop.restWires,vy]
 have nv2 : L.core.sumCarry ≠ bit2 L.core.high := by
  intro h
  apply ParkCarryDevelop.sumCarry_away L hn
  have vy : bit2 L.core.high ∈ L.core.y := List.mem_of_mem_drop (List.mem_of_mem_take
   (bit2_mem _ (by simp [CuccaroStreamedSquareLayout.high,hw.core.y])))
  rw [←h] at vy
  simp [ParkCarryDevelop.restWires,vy]
 have ends := ends4_oldE L hw c (bit1 L.core.high) (bit2 L.core.high)
 have arms := armsCCCC_oldE L hw
 have co : L.core.sumCarry ∉ wires (wCoreK L) := by
  have off := (b_wloop_sumCarry_free L hw hn c hc).2.1
  simp only [wires_append,Finset.mem_union,not_or] at off
  exact off.2.1
 have erase {P : Program} (sub : wires P ⊆ insert c (insert (bit1 L.core.high) (insert (bit2 L.core.high) (oldE L)))) :
   L.core.sumCarry ∉ wires P := by
  intro h
  rcases Finset.mem_insert.mp (sub h) with e|h
  · exact ng e
  rcases Finset.mem_insert.mp h with e|h
  · exact nv e
  rcases Finset.mem_insert.mp h with e|h
  · exact nv2 e
  · exact oe h
 intro h
 simp only [wMidFullCCCC,wires_append,Finset.mem_union] at h
 rcases h with h|((h|(h|h))|h)
 · exact erase ends.1 h
 · exact oe (arms.1 h)
 · exact co h
 · exact oe (arms.2 h)
 · exact erase ends.2 h

def fold (L:CuccaroStreamedSquareWideLayout) (c:Wire):Program:=
 eAddLo L++(buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
  (wMidFullCCCC L c++(unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
   (ParkCarryDevelop.program (eU L) L.core.sumCarry++eSubK L))))
def rebuild (L:CuccaroStreamedSquareWideLayout):Program:=eAddB L++(restore L++padM L 744)
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
  have source2 : base (bit2 L.core.high) = digit originalM 2 := by
    exact bit2_parity L.core.high base (by simp [CuccaroStreamedSquareLayout.high,hw.core.y])
  have loanFact3 := loan3_from_mod16 (base c) originalM u (2^32*H+l'+2^128*K) modE
  rw [←source1,←source2] at loanFact3
  have wm := wMidFullCCCC_step L hw hn c hcw base hc O2 (2^32*H+l'+2^128*K) b1 hb1 hb1lt hO2
    H l' K hH hl' hK rfl loanFact loanFact2 loanFact3
  have wmBase : Triple (BState L base O2 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base))
      (wMidFullCCCC L c)
      (BState L base O3 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base)) := by
    simpa only [hb1] using wm
  have off:=b_wloop_sumCarry_free L hw hn c hcw
  have loop:=cached_wloop_bstate_step L hw hn base hc hsum O2 (2^32*H+l'+2^128*K) O3
    (wMidFullCCCC L c) wmBase off.1 (mid_sumCarry_free L hw hn c hcw) off.2.2
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
  have rp := padM_step L hw hn base hc O4 b0 0 744
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

#print axioms mid_sumCarry_free
#print axioms body_frame
end ECDSAAdd.Entrant.ParkCarry9Develop

end -- isolated Carry9 component

section
-- ParkCarry9Metrics
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry9Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem body_counts (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 toffoliCount (body L c)=4763 ∧ measurementCount (body L c)=5924:=by
 have base:=ParkCarry8Develop.body_counts L hw c
 have mid:=FourthCarryLoanDevelop.middle_counts L hw c
 have p:=padM_counts L 744
 have q:=padM_counts L 746
 simp only[body,fold,rebuild,ParkCarry8Develop.body,ParkCarry8Develop.fold,ParkCarry8Develop.rebuild,
  toffoliCount_append,measurementCount_append]at base ⊢
 exact ⟨by omega,by omega⟩

theorem body_slots (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 Challenge.gateSlots (body L c)=Challenge.gateSlots (ParkCarry8Develop.body L c)+8:=by
 have mid:=(FourthCarryLoanDevelop.middle_counts L hw c).2.2
 have p:=padM_slots L 744
 have q:=padM_slots L 746
 simp only[body,fold,rebuild,ParkCarry8Develop.body,ParkCarry8Develop.fold,ParkCarry8Develop.rebuild,
  Challenge.gateSlots_append]
 omega

theorem body_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire)
 (hn:(c::L.wires).Nodup):GatePhysical (body L c):=by
 have hp:=ParkCarry8Develop.body_physical L hw c hn
 have nd:=(List.nodup_cons.mp hn).2
 have mid:=FourthCarryLoanDevelop.middle_physical L hw nd c (List.nodup_cons.mp hn).1
 have pad:=padM_physical L 744
 simp only[ParkCarry8Develop.body,ParkCarry8Develop.fold,ParkCarry8Develop.rebuild,gatePhysical_append]at hp
 simp only[body,fold,rebuild,gatePhysical_append]
 tauto

#print axioms body_counts
#print axioms body_slots
#print axioms body_physical
end ECDSAAdd.Entrant.ParkCarry9Develop

end -- isolated Carry9 component

section
-- ParkCarry9Hosting
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry9Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def hostedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
 body (hostLayout L rho) c

theorem hosted_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire)
 (h : rho L.core.sumCarry = L.core.sumCarry) : hostedBody L rho c = body L c := by
 rw [hostedBody,ParkCarryDevelop.host_eq L rho h]

theorem hosted_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (rho : Equiv.Perm Wire) (c : Wire) :
 toffoliCount (hostedBody L rho c) = 4763 ∧ measurementCount (hostedBody L rho c) = 5924 :=
 body_counts (hostLayout L rho) (host_widths L hw rho) c

theorem hosted_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (rho : Equiv.Perm Wire) (c : Wire) :
 Challenge.gateSlots (hostedBody L rho c) = Challenge.gateSlots (body L c) := by
 have old := ParkCarry8Develop.hosted_slots L hw rho c
 have v := ParkCarry8Develop.bodyV_slots (hostLayout L rho) c (rho.symm (SecondCarryLoan.bit1 L.core.high))
 change Challenge.gateSlots (ParkCarry8Develop.bodyV (hostLayout L rho) c (rho.symm (SecondCarryLoan.bit1 L.core.high))) =
  Challenge.gateSlots (ParkCarry8Develop.body L c) at old
 have a := body_slots (hostLayout L rho) (host_widths L hw rho) c
 have b := body_slots L hw c
 change Challenge.gateSlots (body (hostLayout L rho) c) = Challenge.gateSlots (body L c)
 omega
#print axioms hosted_eq
#print axioms hosted_counts
#print axioms hosted_slots
end ECDSAAdd.Entrant.ParkCarry9Develop

end -- isolated Carry9 component

section
-- Carry9BodySubset
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Carry9BodySubset
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem old_copy (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 (L.core.product.take 256++L.core.work.take 256).toFinset ⊆ wires (ParkCarry8Develop.body L c) := by
 have pl : (L.core.product.take 256).length=256 := by simp [hw.core.product]
 have wl : (L.core.work.take 256).length=256 := by simp [hw.core.work]
 have nonempty : (L.core.product.take 256).isEmpty=false := by
  rw [List.isEmpty_eq_false_iff]
  intro e
  rw [e] at pl
  contradiction
 have cp : wires (copyRegister none (L.core.product.take 256) (L.core.work.take 256))=
  (L.core.product.take 256++L.core.work.take 256).toFinset := by
  rw [copyRegister_wires none _ _ (pl.trans wl.symm),nonempty]
  rfl
 intro q h
 have used : q∈wires (copyRegister none (L.core.product.take 256) (L.core.work.take 256)) := cp.symm ▸ h
 have foldUsed : q∈wires (measuredFoldQTq L (negP L)) := by
  simp only [measuredFoldQTq,negP,foldDestination,List.drop_zero,pl,wires_append,Finset.mem_union]
  tauto
 simp only [ParkCarry8Develop.body,wires_append,Finset.mem_union]
 tauto

theorem old_prepare (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 [c,bit1 L.core.high,(mU L).headD 0,bit1 (mU L),bit2 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),(eReg L).headD 0,cacheWire L,hostWire L,host2Wire L].toFinset
 ⊆ wires (ParkCarry8Develop.body L c) := by
 have roles (g v u0 u1 u2 r0 r1 r2 e0 cache h1 h2 : Wire) :
  [g,v,u0,u1,u2,r0,r1,r2,e0,cache,h1,h2].toFinset ⊆ wires (prepare3 g v u0 u1 u2 r0 r1 r2 e0 cache h1 h2) := by
  intro q h
  simp [prepare3,loan2,SecondCarryLoan.prepare,SecondCarryLoan.loan,prime,prime2,majority,wires,Instr.wires,correctionWires] at h ⊢
  tauto
 intro q h
 have used := roles c (bit1 L.core.high) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L) h
 have hm : q ∈ wires (wMidFullCCC L c) := by
  rw [wMidFullCCC,wires_append]
  exact Finset.mem_union_left _ used
 have hf : q ∈ wires (ParkCarry8Develop.fold L c) := by
  rw [ParkCarry8Develop.fold,wires_append]
  apply Finset.mem_union_right
  rw [wires_append]
  apply Finset.mem_union_right
  rw [wires_append]
  exact Finset.mem_union_left _ hm
 rw [ParkCarry8Develop.body,wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 exact Finset.mem_union_left _ hf

theorem old_control (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 c∈wires (ParkCarry8Develop.body L c) := by
 have len : eReg L≠[] := by
  have h:=eReg_length L hw
  intro e
  rw [e] at h
  contradiction
 obtain ⟨q,qs,hq⟩:=List.exists_cons_of_ne_nil len
 have hm : (2^129-1)%2=1 := by norm_num
 have used : c∈wires (eFlip L c) := by
  rw [eFlip,hq,List.take_succ_cons,maskedConstant,if_pos hm,wires_append]
  exact Finset.mem_union_left _ (by simp [wires,Instr.wires])
 simp only [ParkCarry8Develop.body,eFoldTq,wires_append,Finset.mem_union]
 tauto

theorem new_roles (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 bit3 (mU L)∈wires (ParkCarry8Develop.body L c) ∧
 bit3 (mR L)∈wires (ParkCarry8Develop.body L c) ∧
 host3Wire L∈wires (ParkCarry8Develop.body L c) := by
 have cp:=old_copy L hw c
 have u : bit3 (mU L)∈L.core.product.take 256 := by
  have hu:=bit3_mem (mU L) (by rw [mU_length L hw];decide)
  change bit3 (mU L)∈(hiReg L).drop 96 at hu
  have hh:=List.mem_of_mem_drop hu
  change bit3 (mU L)∈(L.core.product.take 256).drop 128 at hh
  exact List.mem_of_mem_drop hh
 have r : bit3 (mR L)∈L.core.work.take 256 := by
  have hr:=bit3_mem (mR L) (by rw [(mLens L hw).r];decide)
  exact win_take (l:=L.core.work) (a:=128) (b:=43) (n:=256) (by simpa only [mR] using hr) (by decide)
 have h : host3Wire L∈L.core.product.take 256 := by
  unfold host3Wire eReg
  rw [bit3_append _ _ (by simp [hw.core.product])]
  have mem:=bit3_mem (L.core.product.take 128) (by simp [hw.core.product])
  have eq : (L.core.product.take 256).take 128=L.core.product.take 128 := by simp [List.take_take]
  have mem' : bit3 (L.core.product.take 128)∈(L.core.product.take 256).take 128 := by
   rw [eq]
   exact mem
  exact List.mem_of_mem_take mem'
 exact ⟨cp (by simp [u]),cp (by simp [r]),cp (by simp [h])⟩

#print axioms old_copy
#print axioms old_prepare
#print axioms old_control
#print axioms new_roles
end ECDSAAdd.Entrant.Carry9BodySubset

end -- isolated Carry9 component

section
-- Carry9OldParts
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Carry9OldParts
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem old_mid (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 wires (wMidFullCCC L c) ⊆ wires (ParkCarry8Develop.body L c) := by
 intro q hm
 have hf : q ∈ wires (ParkCarry8Develop.fold L c) := by
  rw [ParkCarry8Develop.fold,wires_append]
  apply Finset.mem_union_right
  rw [wires_append]
  apply Finset.mem_union_right
  rw [wires_append]
  exact Finset.mem_union_left _ hm
 rw [ParkCarry8Develop.body,wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 exact Finset.mem_union_left _ hf

theorem old_fwd (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 wires (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L)) ⊆ wires (ParkCarry8Develop.body L c) := by
 intro q h
 apply old_mid L c
 rw [wMidFullCCC,wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 apply Finset.mem_union_left
 rw [wires_append]
 exact Finset.mem_union_left _ h

theorem old_inv (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 wires (wInvCCC L (cacheWire L) (hostWire L) (host2Wire L)) ⊆ wires (ParkCarry8Develop.body L c) := by
 intro q h
 apply old_mid L c
 rw [wMidFullCCC,wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 apply Finset.mem_union_left
 rw [wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 exact Finset.mem_union_right _ h

theorem old_core (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 wires (wCoreK L) ⊆ wires (ParkCarry8Develop.body L c) := by
 intro q h
 apply old_mid L c
 rw [wMidFullCCC,wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 apply Finset.mem_union_left
 rw [wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 exact Finset.mem_union_left _ h
#print axioms old_mid
#print axioms old_fwd
#print axioms old_inv
#print axioms old_core
end ECDSAAdd.Entrant.Carry9OldParts

end -- isolated Carry9 component

section
-- Carry9BodyRefined
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Carry9BodyRefined
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop Carry9BodySubset
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem body_refined (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 wires (ParkCarry9Develop.body L c)⊆insert (bit2 L.core.high) (wires (ParkCarry8Develop.body L c)) := by
 let v := bit2 L.core.high
 have same {P : Program} (hp : wires P⊆wires (ParkCarry8Develop.body L c)) :
  wires P⊆insert v (wires (ParkCarry8Develop.body L c)) := fun _ h=>Finset.mem_insert_of_mem (hp h)
 have roles:=old_prepare L c
 have extras:=new_roles L hw c
 have carrier : [c,bit1 L.core.high,v,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,cacheWire L,hostWire L,host2Wire L,host3Wire L].toFinset
  ⊆insert v (wires (ParkCarry8Develop.body L c)) := by
  intro q h
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e
  all_goals subst q
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem extras.1
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem extras.2.1
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem extras.2.2
 have ends:=ends4_support c (bit1 L.core.high) v ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L)
 have endEmbed {P : Program} (hp : wires P⊆[c,bit1 L.core.high,v,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,cacheWire L,hostWire L,host2Wire L,host3Wire L].toFinset) :
  wires P⊆insert v (wires (ParkCarry8Develop.body L c)) := hp.trans carrier
 have arms :
  wires (wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L))⊆insert v (wires (ParkCarry8Develop.body L c)) ∧
  wires (wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L))⊆insert v (wires (ParkCarry8Develop.body L c)) := by
  have f:=(fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) (eU L)).support
  have i:=(invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) (eU L)).support
  constructor
  · intro q h
    rcases Finset.mem_insert.mp (f h) with e|h
    · subst q;exact Finset.mem_insert_of_mem extras.2.2
    · exact same (Carry9OldParts.old_fwd L c) h
  · intro q h
    rcases Finset.mem_insert.mp (i h) with e|h
    · subst q;exact Finset.mem_insert_of_mem extras.2.2
    · exact same (Carry9OldParts.old_inv L c) h
 have mid : wires (wMidFullCCCC L c)⊆insert v (wires (ParkCarry8Develop.body L c)) := by
  rw [wMidFullCCCC,wires_append]
  refine Finset.union_subset_iff.mpr ⟨endEmbed ends.1,?_⟩
  rw [wires_append]
  refine Finset.union_subset_iff.mpr ⟨?_,endEmbed ends.2⟩
  rw [wires_append]
  refine Finset.union_subset_iff.mpr ⟨arms.1,?_⟩
  rw [wires_append]
  exact Finset.union_subset_iff.mpr ⟨same (Carry9OldParts.old_core L c),arms.2⟩
 have pad : wires (padM L 744)⊆wires (padM L 746) := by
  have hp : padM L 746=padM L 744++padM L 2 := by
   change List.replicate (744+2) (Instr.measureX (eKw L) [] [])=
    List.replicate 744 (Instr.measureX (eKw L) [] [])++List.replicate 2 (Instr.measureX (eKw L) [] [])
   rw [List.replicate_add]
  rw [hp,wires_append]
  exact Finset.subset_union_left
 intro q h
 simp only [ParkCarry9Develop.body,ParkCarry9Develop.fold,ParkCarry9Develop.rebuild,
  wires_append,Finset.mem_union,or_assoc] at h
 rcases h with h|h|h|h|h|h|h|h|h|h|h|h
 · exact same (P:=measuredFoldQTq L (negP L)) (by intro q h;simp only [ParkCarry8Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=measuredFoldQTq L (rot128F L)) (by intro q h;simp only [ParkCarry8Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eAddLo L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact mid h
 · exact same (P:=unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=ParkCarryDevelop.program (eU L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eSubK L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eFoldTq L c) (by intro q h;simp only [ParkCarry8Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eAddB L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.rebuild,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=ParkCarryDevelop.restore L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.rebuild,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=padM L 746) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.rebuild,wires_append,Finset.mem_union];tauto) (pad h)

#print axioms body_refined
end ECDSAAdd.Entrant.Carry9BodyRefined

end -- isolated Carry9 component
