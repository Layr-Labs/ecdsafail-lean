import ECDSAAdd.Submission.Entrant.MainPart04Base
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CarryWindowCache

theorem cached_prefix (bit : MappedBit) (y cin target cache : Wire)
 (hn : [y,cin,target].Nodup) (ha : ∀q∈bit.wire,q∉[y,cin,target])
 (s : State) (m : List Bool) (rest : Program)
 (hk : s.basis cache=carryBit (bit.value s.basis) (s.basis y) (s.basis cin)) :
 run ([Instr.CX cache target]++rest) m s=
 run (mappedMajority bit y cin target++rest) m s := by
 have h : ∀r,run [Instr.CX cache target] r s=run (mappedMajority bit y cin target) r s := by
  intro r
  rw [mappedMajority_correct bit y cin target hn ha]
  change (⟨s.phase,writeBit s.basis target (s.basis target ^^ s.basis cache)⟩ : State)=_
  rw [hk]
 have hm : measurementCount (mappedMajority bit y cin target)=0 := (mappedBit_counts bit y cin target).2.1
 simp only [run_append,show measurementCount [Instr.CX cache target]=0 from rfl,hm]
 rw [h]

def cachedMapped (cache : Wire) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) : Program :=
 match bits,ys,carry with
 | b::b'::bs,y::y'::ys,c::cs =>
   [Instr.CX cache c]++mappedAdd (b'::bs) (y'::ys) cs c++mappedEraseCarry b y cin c++mappedSum b y cin
 | _,_,_ => mappedAdd bits ys carry cin

theorem cachedMapped_eq (cache : Wire) (b b' : MappedBit) (bits : List MappedBit)
 (y y' : Wire) (ys : List Wire) (c : Wire) (carry : List Wire) (cin : Wire)
 (hn : [y,cin,c].Nodup) (ha : ∀q∈b.wire,q∉[y,cin,c])
 (s : State) (m : List Bool)
 (hk : s.basis cache=carryBit (b.value s.basis) (s.basis y) (s.basis cin)) :
 run (cachedMapped cache (b::b'::bits) (y::y'::ys) (c::carry) cin) m s=
 run (mappedAdd (b::b'::bits) (y::y'::ys) (c::carry) cin) m s := by
 simp only [cachedMapped,mappedAdd, List.append_assoc]
 exact cached_prefix b y cin c cache hn ha s m _ hk

def cachedMixed (cache : Wire) (expected : Bool) (bits : List MappedBit)
 (ys : List Wire) (flags : List Bool) (carry : List Wire) (cin : Wire) : Program :=
 match bits,ys,flags,carry with
 | b::b'::bs,y::y'::ys,_::false::flags,c::cs =>
   [Instr.CX cache c]++MixedLiteralAdderDevelop.program expected (b'::bs) (y'::ys) (false::flags) cs c++
   mappedEraseCarry b y cin c++mappedSum b y cin
 | _,_,_,_ => MixedLiteralAdderDevelop.program expected bits ys flags carry cin

theorem cachedMixed_eq (cache : Wire) (expected d : Bool) (b b' : MappedBit) (bits : List MappedBit)
 (y y' : Wire) (ys : List Wire) (flags : List Bool) (c : Wire) (carry : List Wire) (cin : Wire)
 (hn : [y,cin,c].Nodup) (ha : ∀q∈b.wire,q∉[y,cin,c])
 (s : State) (m : List Bool)
 (hk : s.basis cache=carryBit (b.value s.basis) (s.basis y) (s.basis cin)) :
 run (cachedMixed cache expected (b::b'::bits) (y::y'::ys) (d::false::flags) (c::carry) cin) m s=
 run (MixedLiteralAdderDevelop.program expected (b::b'::bits) (y::y'::ys) (d::false::flags) (c::carry) cin) m s := by
 simp only [cachedMixed,MixedLiteralAdderDevelop.program,MixedLiteralAdderDevelop.head,
   Bool.false_eq_true,if_false,List.append_assoc]
 exact cached_prefix b y cin c cache hn ha s m _ hk

theorem cachedMapped_counts (cache : Wire) (b b' : MappedBit) (bits : List MappedBit)
 (y y' : Wire) (ys : List Wire) (c : Wire) (carry : List Wire) (cin : Wire) :
 toffoliCount (cachedMapped cache (b::b'::bits) (y::y'::ys) (c::carry) cin)+1=
  toffoliCount (mappedAdd (b::b'::bits) (y::y'::ys) (c::carry) cin) ∧
 measurementCount (cachedMapped cache (b::b'::bits) (y::y'::ys) (c::carry) cin)=
  measurementCount (mappedAdd (b::b'::bits) (y::y'::ys) (c::carry) cin) := by
 have ht := (mappedBit_counts b y cin c).1
 have hm := (mappedBit_counts b y cin c).2.1
 simp only [cachedMapped,mappedAdd,toffoliCount_append,measurementCount_append,ht,hm]
 simp only [show toffoliCount [Instr.CX cache c]=0 from rfl,
  show measurementCount [Instr.CX cache c]=0 from rfl]
 constructor
 · omega
 · trivial

def prime (u r cache : Wire) : Program := [.X r,.CCX u r cache,.X r]

theorem prime_run (u r cache : Wire) (hur:u≠r) (hrc:r≠cache) (_huc:u≠cache)
 (s:State) (m:List Bool) : run (prime u r cache) m s=
  ⟨s.phase,writeBit s.basis cache (s.basis cache ^^ (s.basis u && !s.basis r))⟩ := by
 change (⟨s.phase,_⟩ : State)=⟨s.phase,_⟩
 apply congrArg (State.mk s.phase)
 funext q
 by_cases hq:q=cache
 · subst q;simp [prime,run,writeBit,Function.update_apply,hur,hrc,Ne.symm hur,Ne.symm hrc]
 by_cases hqr:q=r
 · subst q;simp [prime,run,writeBit,Function.update_apply,hur,hrc,Ne.symm hur,Ne.symm hrc]
 simp [prime,run,writeBit,Function.update_apply,hq,hqr]

def clear (u r cache : Wire) : Program := [.measureX cache [] [.Z u,.CZ u r]]

theorem clear_run (u r cache : Wire) (huc:u≠cache) (hrc:r≠cache)
 (s:State) (m:List Bool) (hk:s.basis cache=(s.basis u && !s.basis r)) :
 run (clear u r cache) m s=⟨s.phase,writeBit s.basis cache false⟩ := by
 cases m with
 | nil => simp [clear,run,measureAndCorrect,correct]
 | cons bit ms =>
  cases bit <;> cases hu:s.basis u <;> cases hr:s.basis r <;>
   simp [clear,run,measureAndCorrect,correct,hk,hu,hr,writeBit,
    Function.update_apply,huc,hrc]

#print axioms clear_run
#print axioms prime_run
#print axioms cachedMapped_counts
#print axioms cached_prefix
#print axioms cachedMapped_eq
#print axioms cachedMixed_eq

theorem cachedMixed_counts (cache : Wire) (expected d : Bool) (b b' : MappedBit) (bits : List MappedBit)
 (y y' : Wire) (ys : List Wire) (flags : List Bool) (c : Wire) (carry : List Wire) (cin : Wire) :
 toffoliCount (cachedMixed cache expected (b::b'::bits) (y::y'::ys) (d::false::flags) (c::carry) cin)+1=
  toffoliCount (MixedLiteralAdderDevelop.program expected (b::b'::bits) (y::y'::ys) (d::false::flags) (c::carry) cin) ∧
 measurementCount (cachedMixed cache expected (b::b'::bits) (y::y'::ys) (d::false::flags) (c::carry) cin)=
  measurementCount (MixedLiteralAdderDevelop.program expected (b::b'::bits) (y::y'::ys) (d::false::flags) (c::carry) cin) := by
 have ht := (mappedBit_counts b y cin c).1
 have hm := (mappedBit_counts b y cin c).2.1
 simp only [cachedMixed,MixedLiteralAdderDevelop.program,MixedLiteralAdderDevelop.head,
  Bool.false_eq_true,if_false,toffoliCount_append,measurementCount_append,ht,hm]
 simp only [show toffoliCount [Instr.CX cache c]=0 from rfl,
  show measurementCount [Instr.CX cache c]=0 from rfl]
 constructor
 · omega
 · trivial

theorem head_parity (r : List Wire) (t : BasisState) (hr : 0<r.length) :
 t (r.headD 0)=(regValue r t%2==1) := by
 cases r with
 | nil => simp at hr
 | cons q qs => cases h:t q <;> simp [regValue,h,Nat.add_mod,Nat.mul_mod]

theorem carry_parity (u d k : Nat) (hk:k%2=1) :
 ((u%2==1) && !((u+k*d)%2==1))=((u%2==1) && (d%2==1)) := by
 have hu : u%2=0 ∨ u%2=1 := by omega
 have hd : d%2=0 ∨ d%2=1 := by omega
 rcases hu with hu|hu <;> rcases hd with hd|hd <;>
  simp [Nat.add_mod,Nat.mul_mod,hk,hu,hd]

def cachedSub (cache : Wire) (expected : Bool) (bits : List MappedBit) (flags : List Bool)
 (ys carry : List Wire) (cin : Wire) : Program :=
 notRegister ys++cachedMixed cache expected bits ys flags carry cin++notRegister ys

theorem cachedSub_eq (cache : Wire) (expected d : Bool) (b b' : MappedBit) (bits : List MappedBit)
 (y y' : Wire) (ys : List Wire) (flags : List Bool) (c : Wire) (carry : List Wire) (cin : Wire)
 (hn : [y,cin,c].Nodup) (ha : ∀q∈b.wire,q∉[y,cin,c])
 (s : State) (m : List Bool)
 (hk : (run (notRegister (y::y'::ys)) [] s).basis cache=
  carryBit (b.value (run (notRegister (y::y'::ys)) [] s).basis)
   ((run (notRegister (y::y'::ys)) [] s).basis y)
   ((run (notRegister (y::y'::ys)) [] s).basis cin)) :
 run (cachedSub cache expected (b::b'::bits) (d::false::flags) (y::y'::ys) (c::carry) cin) m s=
 run (MixedLiteralAdderDevelop.mixedSub expected (b::b'::bits) (d::false::flags) (y::y'::ys) (c::carry) cin) m s := by
 have hm := (cachedMixed_counts cache expected d b b' bits y y' ys flags c carry cin).2
 simp only [cachedSub,MixedLiteralAdderDevelop.mixedSub,List.append_assoc,run_append,
   (notRegister_counts (y::y'::ys)).2,Nat.zero_add,List.take_zero,List.drop_zero]
 rw [hm]
 rw [cachedMixed_eq cache expected d b b' bits y y' ys flags c carry cin hn ha _ _ hk]

#print axioms cachedMixed_counts
#print axioms head_parity
#print axioms carry_parity
#print axioms cachedSub_eq


theorem cachedSub_read_eq (cache : Wire) (expected d : Bool) (a a' : Wire) (xs : List Wire)
 (y y' : Wire) (ys : List Wire) (flags : List Bool) (c : Wire) (carry : List Wire) (cin : Wire)
 (hn : [y,cin,c].Nodup) (ha : a∉[y,cin,c]) (hnd : (y::y'::ys).Nodup)
 (hay : a∉y::y'::ys) (hiy : cin∉y::y'::ys) (hky : cache∉y::y'::ys)
 (s : State) (m : List Bool) (hi : s.basis cin=false)
 (hk : s.basis cache=(s.basis a && !s.basis y)) :
 run (cachedSub cache expected (mappedRead (a::a'::xs) false) (d::false::flags) (y::y'::ys) (c::carry) cin) m s=
 run (MixedLiteralAdderDevelop.mixedSub expected (mappedRead (a::a'::xs) false) (d::false::flags) (y::y'::ys) (c::carry) cin) m s := by
 have hap : ∀q∈(⟨some a,false⟩ : MappedBit).wire,q∉[y,cin,c] := by simpa using ha
 apply cachedSub_eq cache expected d ⟨some a,false⟩ ⟨some a',false⟩ (mappedRead xs false)
   y y' ys flags c carry cin hn hap s m
 have hay' : a≠y ∧ a≠y' ∧ a∉ys := by simpa using hay
 rw [notRegister_correct (y::y'::ys) hnd]
 simpa [MappedBit.value,hay,hiy,hky,hi,carryBit,hay'.1,hay'.2.1,hay'.2.2] using hk

theorem cachedAdd_read_eq (cache a a' : Wire) (xs : List Wire)
 (y y' : Wire) (ys : List Wire) (c : Wire) (carry : List Wire) (cin : Wire)
 (hn : [y,cin,c].Nodup) (ha : a∉[y,cin,c]) (s : State) (m : List Bool)
 (hk : s.basis cache=carryBit (s.basis a) (s.basis y) (s.basis cin)) :
 run (cachedMapped cache (mappedRead (a::a'::xs) false) (y::y'::ys) (c::carry) cin) m s=
 run (addInPlace (a::a'::xs) (y::y'::ys) (c::carry) cin) m s := by
 rw [←MixedLiteralAdderDevelop.read_add_eq]
 apply cachedMapped_eq cache ⟨some a,false⟩ ⟨some a',false⟩ (mappedRead xs false)
   y y' ys c carry cin hn (by simpa using ha) s m
 simpa [MappedBit.value] using hk

theorem cachedSub_counts (cache : Wire) (expected d : Bool) (b b' : MappedBit) (bits : List MappedBit)
 (y y' : Wire) (ys : List Wire) (flags : List Bool) (c : Wire) (carry : List Wire) (cin : Wire) :
 toffoliCount (cachedSub cache expected (b::b'::bits) (d::false::flags) (y::y'::ys) (c::carry) cin)+1=
  toffoliCount (MixedLiteralAdderDevelop.mixedSub expected (b::b'::bits) (d::false::flags) (y::y'::ys) (c::carry) cin) ∧
 measurementCount (cachedSub cache expected (b::b'::bits) (d::false::flags) (y::y'::ys) (c::carry) cin)=
  measurementCount (MixedLiteralAdderDevelop.mixedSub expected (b::b'::bits) (d::false::flags) (y::y'::ys) (c::carry) cin) := by
 have h := cachedMixed_counts cache expected d b b' bits y y' ys flags c carry cin
 simpa only [cachedSub,MixedLiteralAdderDevelop.mixedSub,toffoliCount_append,measurementCount_append,
  (notRegister_counts (y::y'::ys)).1,(notRegister_counts (y::y'::ys)).2,Nat.zero_add,Nat.add_zero] using h

#print axioms cachedSub_read_eq
#print axioms cachedAdd_read_eq
#print axioms cachedSub_counts


theorem split_two {α : Type} (xs : List α) (h : 2≤xs.length) :
 ∃ a b rest,xs=a::b::rest := by
 cases xs with
 | nil => simp at h
 | cons a xs =>
  cases xs with
  | nil => simp at h
  | cons b rest => exact ⟨a,b,rest,rfl⟩

theorem split_one {α : Type} (xs : List α) (h : 1≤xs.length) :
 ∃ a rest,xs=a::rest := by
 cases xs with
 | nil => simp at h
 | cons a rest => exact ⟨a,rest,rfl⟩

theorem first_geometry (a a' : Wire) (xs : List Wire) (y y' : Wire) (ys : List Wire)
 (c : Wire) (cs : List Wire) (cin : Wire)
 (nd : (cin::(a::a'::xs)++(y::y'::ys)++(c::cs)).Nodup) :
 [y,cin,c].Nodup ∧ a∉[y,cin,c] ∧ (y::y'::ys).Nodup ∧
 a∉y::y'::ys ∧ cin∉y::y'::ys := by
 have geo:=MixedLiteralAdderDevelop.read_geometry (a::a'::xs) (y::y'::ys) (c::cs) cin nd
 have away:=geo.2 a (by simp)
 refine ⟨?_,?_,?_,?_,?_⟩
 · apply List.nodup_iff_count_le_one.mpr
   intro q
   have h:=List.nodup_iff_count_le_one.mp geo.1 q
   simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
   omega
 · intro bad
   apply away
   simp only [List.mem_cons,List.not_mem_nil,or_false] at bad
   rcases bad with rfl|rfl|rfl <;> simp
 · exact (List.nodup_append.mp (List.nodup_cons.mp geo.1).2).1
 · intro bad
   exact away (List.mem_cons_of_mem _ (List.mem_append_left _ bad))
 · intro bad
   exact (List.nodup_cons.mp geo.1).1 (List.mem_append_left _ bad)

theorem cachedSub_read_general (cache : Wire) (expected : Bool) (x y cs : List Wire)
 (flags : List Bool) (cin : Wire) (nd : (cin::x++y++cs).Nodup)
 (hx : 2≤x.length) (hy : 2≤y.length) (hc : 1≤cs.length) (hf : 2≤flags.length)
 (hf1 : flags.getD 1 false=false) (away : cache∉y)
 (s : State) (m : List Bool) (hi : s.basis cin=false)
 (hk : s.basis cache=(s.basis (x.headD 0) && !s.basis (y.headD 0))) :
 run (cachedSub cache expected (mappedRead x false) flags y cs cin) m s=
 run (MixedLiteralAdderDevelop.mixedSub expected (mappedRead x false) flags y cs cin) m s := by
 obtain ⟨a,a',xs,rfl⟩:=split_two x hx
 obtain ⟨b,b',ys,rfl⟩:=split_two y hy
 obtain ⟨c,cs,rfl⟩:=split_one cs hc
 obtain ⟨f,f',fs,rfl⟩:=split_two flags hf
 have ff : f'=false := by simpa using hf1
 subst f'
 obtain ⟨hn,ha,hnd,hay,hiy⟩:=first_geometry a a' xs b b' ys c cs cin nd
 apply cachedSub_read_eq cache expected f a a' xs b b' ys fs c cs cin hn ha hnd hay hiy away s m hi
 simpa only [List.headD_cons] using hk

theorem cachedAdd_read_general (cache : Wire) (x y cs : List Wire) (cin : Wire)
 (nd : (cin::x++y++cs).Nodup) (hx : 2≤x.length) (hy : 2≤y.length) (hc : 1≤cs.length)
 (s : State) (m : List Bool)
 (hk : s.basis cache=carryBit (s.basis (x.headD 0)) (s.basis (y.headD 0)) (s.basis cin)) :
 run (cachedMapped cache (mappedRead x false) y cs cin) m s=run (addInPlace x y cs cin) m s := by
 obtain ⟨a,a',xs,rfl⟩:=split_two x hx
 obtain ⟨b,b',ys,rfl⟩:=split_two y hy
 obtain ⟨c,cs,rfl⟩:=split_one cs hc
 obtain ⟨hn,ha,_,_,_⟩:=first_geometry a a' xs b b' ys c cs cin nd
 apply cachedAdd_read_eq cache a a' xs b b' ys c cs cin hn ha s m
 simpa only [List.headD_cons] using hk

#print axioms cachedSub_read_general
#print axioms cachedAdd_read_general


theorem head_append_of_pos (a b : List Wire) (h : 0<a.length) :
 (a++b).headD 0=a.headD 0 := by
 cases a with
 | nil => simp at h
 | cons a xs => rfl

theorem head_take_pos (a : List Wire) (n : Nat) (h : 0<n) :
 (a.take n).headD 0=a.headD 0 := by
 cases a with
 | nil => simp
 | cons a xs => cases n <;> simp_all

def sub33C (cache : Wire) (R Z cs U : List Wire) (cin : Wire) : Program :=
 cachedSub cache true (mappedRead (U++Z.take 1) false) MixedLiteralAdderDevelop.upper33 (R.take 33) (cs.take 32) cin

def sub43C (cache : Wire) (R Z cs U : List Wire) (cin : Wire) : Program :=
 cachedSub cache true (mappedRead (U++Z) false) MixedLiteralAdderDevelop.mask43 (R.take 43) (cs.take 42) cin

theorem sub33C_eq {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Geo R S Z cs U cin)
 (cache : Wire) (away : cache∉R) (s : State) (m : List Bool) (hi : s.basis cin=false)
 (hk : s.basis cache=(s.basis (U.headD 0) && !s.basis (R.headD 0))) :
 run (sub33C cache R Z cs U cin) m s=run (KnownWindowSubDevelop.sub33 R Z cs U cin) m s := by
 unfold sub33C KnownWindowSubDevelop.sub33
 simp only [List.drop_zero]
 apply cachedSub_read_general cache true (U++Z.take 1) (R.take 33) (cs.take 32)
   MixedLiteralAdderDevelop.upper33 cin (by simpa using g.ndU 1 0 33 32)
   (by simp [g.u,g.z]) (by simp [g.r]) (by simp [g.c]) (by decide) (by decide)
   (fun h=>away (List.mem_of_mem_take h)) s m hi
 simpa only [head_append_of_pos U _ (by rw [g.u];decide),head_take_pos R 33 (by decide)] using hk

theorem sub43C_eq {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Geo R S Z cs U cin)
 (cache : Wire) (away : cache∉R) (s : State) (m : List Bool) (hi : s.basis cin=false)
 (hk : s.basis cache=(s.basis (U.headD 0) && !s.basis (R.headD 0))) :
 run (sub43C cache R Z cs U cin) m s=run (KnownWindowSubDevelop.sub43 R Z cs U cin) m s := by
 unfold sub43C KnownWindowSubDevelop.sub43
 simp only [List.drop_zero]
 apply cachedSub_read_general cache true (U++Z) (R.take 43) (cs.take 42)
   MixedLiteralAdderDevelop.mask43 cin (by simpa using g.ndUZ 0 43 42)
   (by simp [g.u,g.z]) (by simp [g.r]) (by simp [g.c]) (by decide) (by decide)
   (fun h=>away (List.mem_of_mem_take h)) s m hi
 simpa only [head_append_of_pos U _ (by rw [g.u];decide),head_take_pos R 43 (by decide)] using hk

def addC (cache : Wire) (x y cs : List Wire) (cin : Wire) : Program :=
 cachedMapped cache (mappedRead x false) y cs cin

theorem addC_eq {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Geo R S Z cs U cin)
 (cache : Wire) (j n i : Nat) (hn : 2 ≤ n) (hc : 1 ≤ i)
 (s : State) (m : List Bool) (hi : s.basis cin=false)
 (hk : s.basis cache=(s.basis (U.headD 0) && s.basis (R.headD 0))) :
 run (addC cache (U++Z.take j) (R.take n) (cs.take i) cin) m s=
 run (addInPlace (U++Z.take j) (R.take n) (cs.take i) cin) m s := by
 apply cachedAdd_read_general cache (U++Z.take j) (R.take n) (cs.take i) cin
   (by simpa using g.ndU j 0 n i) (by simp [g.u];omega) (by simp [g.r];omega) (by simp [g.c];omega) s m
 rw [head_append_of_pos U _ (by rw [g.u];decide),head_take_pos R n (by omega),hi]
 simpa [carryBit] using hk

#print axioms sub33C_eq
#print axioms sub43C_eq
#print axioms addC_eq


theorem ps_heads {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Geo R S Z cs U cin)
 (cache : Wire) (hR : cache∉R) (hS : cache∉S) (t : BasisState)
 (u d V D : Nat) (hu : regValue U t=u)
 (hk : t cache=((u%2==1) && (d%2==1))) (s : State) (h : WinArith.PS R S t V D s.basis) :
 s.basis (U.headD 0)=(u%2==1) ∧ s.basis (R.headD 0)=(V%2==1) ∧
 s.basis cache=((u%2==1) && (d%2==1)) := by
 have uv : regValue U s.basis=u :=
  (regValue_congr U _ _ (fun q hq=>h.2.2 q (g.UR q hq) (g.US q hq))).trans hu
 refine ⟨?_,?_,(h.2.2 cache hR hS).trans hk⟩
 · simpa only [uv] using head_parity U s.basis (by rw [g.u];decide)
 · simpa only [h.1] using head_parity R s.basis (by rw [g.r];decide)

theorem sub33C_spec {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Geo R S Z cs U cin)
 (cache : Wire) (hR : cache∉R) (hS : cache∉S) {t : BasisState}
 (cl : WinArith.Clean Z cs cin t) (u d : Nat) (hu : regValue U t=u)
 (hu32 : u<2^32) (hd : d≤976) (hk : t cache=((u%2==1) && (d%2==1))) :
 Triple (WinArith.PS R S t (u+d) 0) (sub33C cache R Z cs U cin) (WinArith.PS R S t d 0) := by
 intro s m h
 obtain ⟨bu,br,bc⟩:=ps_heads g cache hR hS t u d (u+d) 0 hu hk s h
 have hi : s.basis cin=false := (h.2.2 cin g.cinR g.cinS).trans cl.cin
 have eq : s.basis cache=(s.basis (U.headD 0) && !s.basis (R.headD 0)) := by
  rw [bu,br,bc]
  symm
  simpa only [Nat.one_mul] using carry_parity u d 1 (by decide)
 rw [sub33C_eq g cache hR s m hi eq]
 exact KnownWindowSubDevelop.sub33_spec g cl u d hu hu32 hd s m h

theorem sub43C_spec {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Geo R S Z cs U cin)
 (cache : Wire) (hR : cache∉R) (hS : cache∉S) {t : BasisState}
 (cl : WinArith.Clean Z cs cin t) (u d : Nat) (hu : regValue U t=u)
 (hu32 : u<2^32) (hd : d≤976) (hk : t cache=((u%2==1) && (d%2==1))) :
 Triple (WinArith.PS R S t (u+4294968273*d) 0) (sub43C cache R Z cs U cin)
  (WinArith.PS R S t (4294968273*d) 0) := by
 intro s m h
 obtain ⟨bu,br,bc⟩:=ps_heads g cache hR hS t u d (u+4294968273*d) 0 hu hk s h
 have hi : s.basis cin=false := (h.2.2 cin g.cinR g.cinS).trans cl.cin
 have eq : s.basis cache=(s.basis (U.headD 0) && !s.basis (R.headD 0)) := by
  rw [bu,br,bc]
  exact (carry_parity u d 4294968273 (by decide)).symm
 rw [sub43C_eq g cache hR s m hi eq]
 exact KnownWindowSubDevelop.sub43_spec g cl u d hu hu32 hd s m h

theorem addC_ps_eq {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Geo R S Z cs U cin)
 (cache : Wire) (hR : cache∉R) (hS : cache∉S) {t : BasisState}
 (cl : WinArith.Clean Z cs cin t) (u d V D : Nat) (hu : regValue U t=u)
 (hk : t cache=((u%2==1) && (d%2==1))) (hV : V%2=d%2)
 (j n i : Nat) (hn : 2 ≤ n) (hc : 1 ≤ i) (s : State) (m : List Bool)
 (h : WinArith.PS R S t V D s.basis) :
 run (addC cache (U++Z.take j) (R.take n) (cs.take i) cin) m s=
 run (addInPlace (U++Z.take j) (R.take n) (cs.take i) cin) m s := by
 obtain ⟨bu,br,bc⟩:=ps_heads g cache hR hS t u d V D hu hk s h
 have hi : s.basis cin=false := (h.2.2 cin g.cinR g.cinS).trans cl.cin
 apply addC_eq g cache j n i hn hc s m hi
 rw [bu,br,bc,hV]

#print axioms sub33C_spec
#print axioms sub43C_spec
#print axioms addC_ps_eq

theorem head_mem (xs : List Wire) (h : 0<xs.length) : xs.headD 0∈xs := by
 cases xs with
 | nil => simp at h
 | cons a rest => simp
end ECDSAAdd.Entrant.CarryWindowCache

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.CarryWindowCache
open WinArith
theorem addC_ps_loose {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Geo R S Z cs U cin)
 (cache : Wire) (hR : cache∉R) (hS : cache∉S) {t : BasisState}
 (hcin : t cin=false) (u d V D : Nat) (hu : regValue U t=u)
 (hk : t cache=((u%2==1) && (d%2==1))) (hV : V%2=d%2)
 (j n i : Nat) (hn : 2 ≤ n) (hc : 1 ≤ i) (s : State) (m : List Bool)
 (h : WinArith.PS R S t V D s.basis) :
 run (addC cache (U++Z.take j) (R.take n) (cs.take i) cin) m s=
 run (addInPlace (U++Z.take j) (R.take n) (cs.take i) cin) m s := by
 obtain ⟨bu,br,bc⟩:=ps_heads g cache hR hS t u d V D hu hk s h
 have hi : s.basis cin=false := (h.2.2 cin g.cinR g.cinS).trans hcin
 apply addC_eq g cache j n i hn hc s m hi
 rw [bu,br,bc,hV]


theorem kz_out (t : BasisState) (k : Wire) (Z : List Wire) (hz : Z.length=11)
 (q : Wire) (hq : q ∉ Z) : kz t k Z q=t q := by
 have hzq : q ∉ zpat Z := fun h => hq (zpat_sub Z hz q h)
 simp [kz,hzq]

theorem kz_u {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
 (t : BasisState) (k : Wire) : regValue U (kz t k Z)=regValue U t := by
 apply regValue_congr
 intro q hq
 apply kz_out t k Z g.z
 exact fun hZ => g.away U Z q hq hZ (by simp only [List.count_cons,List.count_append];omega)
def fwdCK (R S Z cs U : List Wire) (cin k cache : Wire) : Program :=
  sub33C cache R Z cs U cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  (WinArithAux3SmallDevelop.smallF R S cs cin ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (kpat k Z ++ (addC cache (U ++ Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin ++ kpat k Z))))))

theorem sub43CK_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (cache : Wire) (hR : cache∉R) (hS : cache∉S) (hZ : cache∉Z)
    (hcache : t cache=((u%2==1) && (d%2==1))) (k : Wire) (hkZ : k ∉ Z) :
    Triple (PS R S (kz t k Z) (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0)
      (sub43C cache R Z cs U cin) (PS R S (kz t k Z) (4294968273*d) 0) := by
  intro s m hs
  obtain ⟨bu,br,bc⟩:=ps_heads g cache hR hS (kz t k Z) u d _ 0
    ((kz_u g t k).trans hu) ((kz_out t k Z g.z cache hZ).trans hcache) s hs
  have cinZ : cin ∉ Z := fun h => g.away [cin] Z cin (by simp) h
    (by simp only [List.count_cons,List.count_append,List.count_nil];omega)
  have ci : s.basis cin=false := (hs.2.2 cin g.cinR g.cinS).trans
    ((kz_out t k Z g.z cin cinZ).trans cl.cin)
  have eq : s.basis cache=(s.basis (U.headD 0) && !s.basis (R.headD 0)) := by
    rw [bu,br,bc]
    have hp : (u+4294968273*d+2^32*(976*(if t k then 1 else 0)))%2=(u+4294968273*d)%2 := by omega
    rw [hp]
    exact (carry_parity u d 4294968273 (by decide)).symm
  rw [sub43C_eq g cache hR s m ci eq]
  exact sub43K_spec g cl u d hu hu32 hd k hkZ s m hs
def invCK (R S Z cs U : List Wire) (cin k cache : Wire) : Program :=
  kpat k Z ++ (sub43C cache R Z cs U cin ++ (kpat k Z ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (WinArithAux3SmallDevelop.smallI R S cs cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  addC cache (U ++ Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin))))))

#print axioms sub43CK_spec
end ECDSAAdd.Entrant.CarryWindowCache

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CarryWindowCache
open ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

def wFwdCK (L : CuccaroStreamedSquareWideLayout) (cache : Wire) : Program :=
 fwdCK (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L) cache
def wInvCK (L : CuccaroStreamedSquareWideLayout) (cache : Wire) : Program :=
 invCK (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L) cache

end ECDSAAdd.Entrant.CarryWindowCache

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CarryWindowCache
open ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
def cacheWire (L : CuccaroStreamedSquareWideLayout) : Wire := (eReg L).drop 129 |>.headD 0

theorem cache_decomp (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 eReg L=(eReg L).take 129++cacheWire L::(eReg L).drop 130 := by
 have hl : 0<((eReg L).drop 129).length := by simp [eReg_length L hw]
 have h : (eReg L).drop 129=cacheWire L::((eReg L).drop 129).tail := by
  generalize he:(eReg L).drop 129=xs at hl ⊢
  have hc : cacheWire L=xs.headD 0 := by rw [cacheWire,he]
  cases xs with
  | nil => simp at hl
  | cons a rest => simp [hc]
 rw [show (eReg L).drop 130=((eReg L).drop 129).tail by simp [List.tail_drop]]
 rw [←h,List.take_append_drop]

theorem cache_mem (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : cacheWire L∈eReg L := by
 rw [cache_decomp L hw]
 simp

theorem write_value (pre post : List Wire) (q : Wire) (hn : (pre++q::post).Nodup)
 (s : BasisState) (v : Bool) :
 regValue (pre++q::post) (writeBit s q v)+2^pre.length*(s q).toNat=
 regValue (pre++q::post) s+2^pre.length*v.toNat := by
 have hpre : q∉pre := by
  intro h
  exact (List.nodup_append.mp hn).2.2 q h q (by simp) rfl
 have hpost : q∉post := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
 have p : regValue pre (writeBit s q v)=regValue pre s :=
  regValue_congr _ _ _ (fun r hr=>by simp [writeBit,Function.update_apply,show r≠q from fun e=>hpre (e ▸ hr)])
 have t : regValue post (writeBit s q v)=regValue post s :=
  regValue_congr _ _ _ (fun r hr=>by simp [writeBit,Function.update_apply,show r≠q from fun e=>hpost (e ▸ hr)])
 have hhead (b : BasisState) : regValue (q::post) b=(b q).toNat+2*regValue post b := by
  cases h : b q <;> simp [regValue,h,Bool.toNat]
 rw [regValue_append,regValue_append,p,hhead,hhead,t]
 simp only [writeBit,Function.update_self]
 ring

theorem e_write_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : BasisState) (v : Bool) :
 regValue (eReg L) (writeBit s (cacheWire L) v)+2^129*(s (cacheWire L)).toNat=
 regValue (eReg L) s+2^129*v.toNat := by
 have h := write_value ((eReg L).take 129) ((eReg L).drop 130) (cacheWire L)
  (by rw [←cache_decomp L hw];exact eReg_nodup L hn) s v
 simpa only [←cache_decomp L hw,List.length_take,eReg_length L hw,show min 129 130=129 from rfl] using h

theorem e_cache_zero (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (s : BasisState) (E : Nat) (he : regValue (eReg L) s=E) (hE : E<2^129) :
 s (cacheWire L)=false := by
 have h : regValue (eReg L) s=regValue ((eReg L).take 129) s+
  2^129*regValue (cacheWire L::(eReg L).drop 130) s := by
  conv_lhs => rw [cache_decomp L hw]
  rw [regValue_append]
  simp only [List.length_take,eReg_length L hw,show min 129 130=129 from rfl]
 have zero : regValue (cacheWire L::(eReg L).drop 130) s=0 := by omega
 exact (regValue_zero _ _).mp zero _ (by simp)

theorem bstate_write_e (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
 (cache : Wire) (hm : cache∈eReg L) (base s : BasisState) (O E A : Nat)
 (h : BState L base O E A s) (v : Bool) :
 BState L base O (regValue (eReg L) (writeBit s cache v)) A (writeBit s cache v) := by
 have a:=eReg_away L hn cache hm
 refine ⟨?_,rfl,?_,?_⟩
 · exact (regValue_congr _ _ _ (fun q hq=>by simp [writeBit,Function.update_apply,
     show q≠cache from fun e=>a.1 (e ▸ hq)])).trans h.1
 · exact (regValue_congr _ _ _ (fun q hq=>by simp [writeBit,Function.update_apply,
     show q≠cache from fun e=>a.2.1 (e ▸ hq)])).trans h.2.2.1
 · intro q h1 h2 h3
   have ne : q≠cache := fun e=>h2 (e.symm ▸ hm)
   simpa only [writeBit,Function.update_of_ne ne] using h.2.2.2 q h1 h2 h3

#print axioms e_write_value
#print axioms e_cache_zero
#print axioms bstate_write_e


theorem bstate_heads (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (base s : BasisState) (hc : L.PairClean base) (O E b1 : Nat) (hb1 : regValue (hiReg L) base=b1)
 (hb1lt : b1<2^128) (h : BState L base O E (4294968272*b1) s) :
 s ((mU L).headD 0)=(b1/2^96%2==1) ∧
 s ((mR L).headD 0)=((b1/2^96+(4294968272*b1/2^128-b1/2^96))%2==1) := by
 have g:=mGeo L hw hn
 obtain ⟨h1,h2,h3⟩:=whi_split b1 hb1lt
 have hr := mR_value L hw hn base hc O E (4294968272*b1) s h
 have hv : regValue (mR L) s=b1/2^96+(4294968272*b1/2^128-b1/2^96) := by
  rw [hr.1,Nat.mod_eq_of_lt (by omega)]
  omega
 have hu : regValue (mU L) s=b1/2^96 := by
  rw [hi96 L hw,regValue_congr _ _ _ (fun q hq=>bstate_other L hn base O E _ s h q (Or.inl hq)),hb1]
 constructor
 · rw [head_parity (mU L) s (by rw [g.u];decide),hu]
 · rw [head_parity (mR L) s (by rw [g.r];decide),hv]

theorem cache_geometry (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 (mU L).headD 0≠(mR L).headD 0 ∧
 (mU L).headD 0≠cacheWire L ∧ (mR L).headD 0≠cacheWire L := by
 have g:=mGeo L hw hn
 have u : (mU L).headD 0∈mU L:=head_mem _ (by rw [g.u];decide)
 have r : (mR L).headD 0∈mR L:=head_mem _ (by rw [g.r];decide)
 have c:=cache_mem L hw
 refine ⟨fun e=>g.UR _ u (e.symm ▸ r),?_,?_⟩
 · intro e
   exact (eReg_away L hn (cacheWire L) c).2.2 (e ▸ List.mem_of_mem_drop u)
 · intro e
   exact (m_away L hn (cacheWire L) (Or.inl (e ▸ r))).2 c

def wMidFullCK (L : CuccaroStreamedSquareWideLayout) : Program :=
 prime ((mU L).headD 0) ((mR L).headD 0) (cacheWire L) ++
 ((wFwdCK L (cacheWire L)++(wCoreK L++wInvCK L (cacheWire L))) ++
 clear ((mU L).headD 0) ((mR L).headD 0) (cacheWire L))

#print axioms bstate_heads
#print axioms cache_geometry
end ECDSAAdd.Entrant.CarryWindowCache

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CarryWindowCache
open ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end ECDSAAdd.Entrant.CarryWindowCache

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.CarryWindowCache
open ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
open ECDSAAdd.RecordedQuantum
structure Patch (cache : Wire) (n : Nat) (p q : Program) : Prop where
 t : toffoliCount p+n=toffoliCount q
 m : measurementCount p=measurementCount q
 slots : Challenge.gateSlots p+5*n=Challenge.gateSlots q
 support : wires p⊆insert cache (wires q)
 phys : cache∉wires q→GatePhysical q→GatePhysical p

namespace Patch
 theorem refl (cache : Wire) (p : Program) : Patch cache 0 p p :=
 ⟨by omega,rfl,by omega,fun _ h=>Finset.mem_insert_of_mem h,fun _ h=>h⟩
 theorem app {cache : Wire} {n k : Nat} {p q a b : Program}
 (h : Patch cache n p q) (g : Patch cache k a b) : Patch cache (n+k) (p++a) (q++b) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [toffoliCount_append];have :=h.t;have :=g.t;omega
  · simp only [measurementCount_append];rw [h.m,g.m]
  · simp only [Challenge.gateSlots_append];have :=h.slots;have :=g.slots;omega
  · intro x hx
    rw [wires_append,Finset.mem_union] at hx
    rw [wires_append,Finset.mem_insert,Finset.mem_union]
    rcases hx with hx|hx
    · have :=h.support hx;simp only [Finset.mem_insert] at this;tauto
    · have :=g.support hx;simp only [Finset.mem_insert] at this;tauto
  · intro away hp
    rw [gatePhysical_append] at hp ⊢
    have a : cache∉wires q:=fun hm=>away (by rw [wires_append];exact Finset.mem_union_left _ hm)
    have b : cache∉wires b:=fun hm=>away (by rw [wires_append];exact Finset.mem_union_right _ hm)
    exact ⟨h.phys a hp.1,g.phys b hp.2⟩
end Patch

theorem majority_patch (cache a y cin c : Wire) : Patch cache 1 [.CX cache c] (majority a y cin c) := by
 refine ⟨by simp [toffoliCount,majority],by simp [measurementCount,majority],?_,?_,?_⟩
 · simp [Challenge.gateSlots,Challenge.instructionSlots,majority]
 · intro q hq
   simp only [ECDSAAdd.wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    or_false] at hq ⊢
   simp only [majority,ECDSAAdd.wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    or_false]
   tauto
 · intro away _
   have hc : cache≠c := by
    intro e;apply away;simp [e,majority,ECDSAAdd.wires,Instr.wires]
   simp [GatePhysical,PhysicalInstr,ProperGate,hc]

theorem add_patch (cache : Wire) (x y cs : List Wire) (cin : Wire)
 (hx : 2≤x.length) (hy : 2≤y.length) (hc : 1≤cs.length) :
 Patch cache 1 (addC cache x y cs cin) (addInPlace x y cs cin) := by
 obtain ⟨a,a',xs,rfl⟩:=split_two x hx
 obtain ⟨b,b',ys,rfl⟩:=split_two y hy
 obtain ⟨c,cs,rfl⟩:=split_one cs hc
 have h:= (majority_patch cache a b cin c).app (Patch.refl cache
  (mappedAdd (mappedRead (a'::xs) false) (b'::ys) cs c++mappedEraseCarry ⟨some a,false⟩ b cin c++mappedSum ⟨some a,false⟩ b cin))
 simpa only [addC,cachedMapped,mappedRead,List.map_cons,mappedAdd,mappedMajority,
  Bool.false_eq_true,if_false,Nat.add_zero,←MixedLiteralAdderDevelop.read_add_eq,List.append_assoc] using h

theorem sub_patch (cache : Wire) (expected : Bool) (x y cs : List Wire) (flags : List Bool) (cin : Wire)
 (hx : 2≤x.length) (hy : 2≤y.length) (hc : 1≤cs.length) (hf : 2≤flags.length)
 (hf1 : flags.getD 1 false=false) :
 Patch cache 1 (cachedSub cache expected (mappedRead x false) flags y cs cin)
 (MixedLiteralAdderDevelop.mixedSub expected (mappedRead x false) flags y cs cin) := by
 obtain ⟨a,a',xs,rfl⟩:=split_two x hx
 obtain ⟨b,b',ys,rfl⟩:=split_two y hy
 obtain ⟨c,cs,rfl⟩:=split_one cs hc
 obtain ⟨f,f',fs,rfl⟩:=split_two flags hf
 have ff : f'=false:=by simpa using hf1
 subst f'
 have h:= (majority_patch cache a b cin c).app (Patch.refl cache
  (MixedLiteralAdderDevelop.program expected (mappedRead (a'::xs) false) (b'::ys) (false::fs) cs c++
   mappedEraseCarry ⟨some a,false⟩ b cin c++mappedSum ⟨some a,false⟩ b cin))
 have h2:=(Patch.refl cache (notRegister (b::b'::ys))).app (h.app (Patch.refl cache (notRegister (b::b'::ys))))
 simpa only [cachedSub,cachedMixed,MixedLiteralAdderDevelop.mixedSub,MixedLiteralAdderDevelop.program,
  MixedLiteralAdderDevelop.head,mappedRead,List.map_cons,mappedMajority,Bool.false_eq_true,if_false,
  Nat.add_zero,Nat.zero_add,List.append_assoc] using h2

#print axioms majority_patch
#print axioms add_patch
#print axioms sub_patch


theorem sub33_patch {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Lens R S Z cs U)
 (cache : Wire) : Patch cache 1 (sub33C cache R Z cs U cin) (KnownWindowSubDevelop.sub33 R Z cs U cin) := by
 simpa only [sub33C,KnownWindowSubDevelop.sub33,List.drop_zero] using
  sub_patch cache true (U++Z.take 1) (R.take 33) (cs.take 32) MixedLiteralAdderDevelop.upper33 cin
   (by simp [g.u,g.z]) (by simp [g.r]) (by simp [g.c]) (by decide) (by decide)

theorem sub43_patch {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Lens R S Z cs U)
 (cache : Wire) : Patch cache 1 (sub43C cache R Z cs U cin) (KnownWindowSubDevelop.sub43 R Z cs U cin) := by
 simpa only [sub43C,KnownWindowSubDevelop.sub43,List.drop_zero] using
  sub_patch cache true (U++Z) (R.take 43) (cs.take 42) MixedLiteralAdderDevelop.mask43 cin
   (by simp [g.u,g.z]) (by simp [g.r]) (by simp [g.c]) (by decide) (by decide)


theorem fwdK_patch {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Lens R S Z cs U)
 (cache k : Wire) : Patch cache 2 (fwdCK R S Z cs U cin k cache) (WinArith.tFwdK R S Z cs U cin k) := by
 have a:=add_patch cache (U++Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin
  (by simp [g.u,g.z]) (by simp [g.r]) (by simp [g.c])
 have kp:=Patch.refl cache (WinArith.kpat k Z)
 exact (sub33_patch (cin:=cin) g cache).app ((Patch.refl cache (copyRegister none ((R.drop 0).take 10) S)).app
  ((Patch.refl cache (WinArithAux3SmallDevelop.smallF R S cs cin)).app
   ((Patch.refl cache (copyRegister none S ((R.drop 32).take 10))).app
    ((Patch.refl cache (copyRegister none ((R.drop 32).take 10) S)).app (kp.app (a.app kp))))))

theorem invK_patch {R S Z cs U : List Wire} {cin : Wire} (g : WinArith.Lens R S Z cs U)
 (cache k : Wire) : Patch cache 2 (invCK R S Z cs U cin k cache) (WinArith.tInvK R S Z cs U cin k) := by
 have a:=add_patch cache (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin
  (by simp [g.u,g.z]) (by simp [g.r]) (by simp [g.c])
 have kp:=Patch.refl cache (WinArith.kpat k Z)
 exact kp.app ((sub43_patch (cin:=cin) g cache).app (kp.app ((Patch.refl cache (copyRegister none ((R.drop 32).take 10) S)).app
  ((Patch.refl cache (copyRegister none S ((R.drop 32).take 10))).app
   ((Patch.refl cache (WinArithAux3SmallDevelop.smallI R S cs cin)).app
    ((Patch.refl cache (copyRegister none ((R.drop 0).take 10) S)).app a))))))
theorem mid_patch (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 Patch (cacheWire L) 4 (wFwdCK L (cacheWire L)++(wCoreK L++wInvCK L (cacheWire L)))
 (wFwdK L++(wCoreK L++wInvK L)) :=
 (fwdK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).app
 ((Patch.refl _ (wCoreK L)).app (invK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)))

theorem mid_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 toffoliCount (wMidFullCK L)+3=toffoliCount (wFwdK L++(wCoreK L++wInvK L)) ∧
 measurementCount (wMidFullCK L)=measurementCount (wFwdK L++(wCoreK L++wInvK L))+1 ∧
 Challenge.gateSlots (wMidFullCK L)+14=Challenge.gateSlots (wFwdK L++(wCoreK L++wInvK L)) := by
 have h:=mid_patch L hw
 have ht:=h.t;have hm:=h.m;have hs:=h.slots
 simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at ht hm hs
 simp only [wMidFullCK,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 have pt : toffoliCount (prime ((mU L).headD 0) ((mR L).headD 0) (cacheWire L))=1:=rfl
 have pm : measurementCount (prime ((mU L).headD 0) ((mR L).headD 0) (cacheWire L))=0:=rfl
 have ps : Challenge.gateSlots (prime ((mU L).headD 0) ((mR L).headD 0) (cacheWire L))=3:=rfl
 have ct : toffoliCount (clear ((mU L).headD 0) ((mR L).headD 0) (cacheWire L))=0:=rfl
 have cm : measurementCount (clear ((mU L).headD 0) ((mR L).headD 0) (cacheWire L))=1:=rfl
 have cs : Challenge.gateSlots (clear ((mU L).headD 0) ((mR L).headD 0) (cacheWire L))=3:=rfl
 rw [pt,pm,ps,ct,cm,cs]
 exact ⟨by omega,by omega,by omega⟩

theorem cache_not_mem (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 ¬WinArith.Mem (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (cacheWire L) := by
 have ce:=cache_mem L hw
 have cp:=List.count_pos_iff.mpr (eReg_product L _ ce)
 have lc:=layoutCount L hn (cacheWire L)
 intro hm
 rcases hm with hi|hu|hr|hs|hz|hc
 · have cinPos : 0<[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
    L.core.modFlag,L.core.sumCarry].count (cacheWire L):=List.count_pos_iff.mpr (by simp [hi])
   omega
 · exact (eReg_away L hn _ ce).2.2 (List.mem_of_mem_drop hu)
 · have :=List.count_pos_iff.mpr (mR_work L _ hr);omega
 · have :=List.count_pos_iff.mpr (mS_pad L _ hs);omega
 · have :=List.count_pos_iff.mpr (mZ_pad L _ hz);omega
 · have :=List.count_pos_iff.mpr (mC_pad L _ hc);omega


theorem cache_ne_k (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 cacheWire L ≠ eU L := by
 have shape := (eShape L hw).1
 have cv : cacheWire L=eV L := by
  simp [cacheWire,shape,eRlow,hw.core.product,List.drop_append]
 rw [cv]
 have nd:=eReg_nodup L hn
 rw [shape] at nd
 have nd2 := (List.nodup_append.mp nd).2.1
 have ne : eU L≠eV L := by simpa using (List.nodup_cons.mp nd2).1
 exact ne.symm

theorem mid_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 GatePhysical (wMidFullCK L) := by
 have a:=cache_not_mem L hw hn
 have ck:=cache_ne_k L hw hn
 have af : cacheWire L∉ECDSAAdd.wires (wFwdK L):=by
  intro h
  rcases WinArith.tFwdK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact a hm
  · exact ck he
 have ai : cacheWire L∉ECDSAAdd.wires (wInvK L):=by
  intro h
  rcases WinArith.tInvK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact a hm
  · exact ck he
 have g:=mGeo L hw hn
 have heZ : eU L∉mZ L:=fun hz=>(eU_away L hw hn).1 (mZ_pad L _ hz)
 have cg:=cache_geometry L hw hn
 have p : GatePhysical (prime ((mU L).headD 0) ((mR L).headD 0) (cacheWire L)):=by
  simp [prime,GatePhysical,PhysicalInstr,ProperGate]
  simpa only [List.headD_eq_head?_getD] using And.intro cg.2.1 cg.2.2
 have c : GatePhysical (clear ((mU L).headD 0) ((mR L).headD 0) (cacheWire L)):=by
  simp [clear,GatePhysical,PhysicalInstr]
 have pf:=(fwdK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).phys af (WinArith.tFwdK_physical g (eU L) heZ)
 have pi:=(invK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).phys ai (WinArith.tInvK_physical g (eU L) heZ)
 have pc : GatePhysical (wCoreK L):= by
  simp only [wCoreK,gatePhysical_append]
  exact ⟨kw_physical L hw hn,QCore.qprog_physicalTq (rotWCore L) SquareReduction.p (rotWCore_nodup L hn),kw_physical L hw hn⟩
 simp only [wMidFullCK,gatePhysical_append]
 exact ⟨p,⟨pf,pc,pi⟩,c⟩
theorem cached_arm_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 ECDSAAdd.wires (wFwdCK L (cacheWire L))⊆oldE L ∧
 ECDSAAdd.wires (wInvCK L (cacheWire L))⊆oldE L := by
 have ce : cacheWire L∈oldE L:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inr (Or.inl (cache_mem L hw)))))
 have f:=(fwdK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support
 have i:=(invK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support
 constructor
 · intro q h;rcases Finset.mem_insert.mp (f h) with e|h
   · exact e ▸ ce
   · exact wFwdK_oldE L hw h
 · intro q h;rcases Finset.mem_insert.mp (i h) with e|h
   · exact e ▸ ce
   · exact wInvK_oldE L hw h

theorem cache_ends_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 ECDSAAdd.wires (prime ((mU L).headD 0) ((mR L).headD 0) (cacheWire L))⊆oldE L ∧
 ECDSAAdd.wires (clear ((mU L).headD 0) ((mR L).headD 0) (cacheWire L))⊆oldE L := by
 have lens:=mLens L hw
 have hu : (mU L).headD 0∈hiReg L:=List.mem_of_mem_drop (head_mem (mU L) (by rw [lens.u];decide))
 have hr : (mR L).headD 0∈L.core.work.drop 128:=List.mem_of_mem_take (head_mem (mR L) (by rw [lens.r];decide))
 have u:=oldE_mem L hw _ (Or.inr (Or.inl hu))
 have r:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inl hr)))
 have c:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inr (Or.inl (cache_mem L hw)))))
 simp only [List.headD_eq_head?_getD] at u r
 constructor <;> intro q h
 · simp [prime,ECDSAAdd.wires,Instr.wires] at h
   rcases h with h|h|h <;> subst q <;> assumption
 · simp [clear,ECDSAAdd.wires,Instr.wires,correctionWires] at h
   rcases h with h|h|h <;> subst q <;> assumption


#print axioms mid_physical
end ECDSAAdd.Entrant.CarryWindowCache

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.CarryWindowCache
open ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
end ECDSAAdd.Entrant.CarryWindowCache
