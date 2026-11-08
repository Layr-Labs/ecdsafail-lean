import ECDSAAdd.Submission.Entrant.NarrowWindow
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

theorem fwdCK_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (cache : Wire) (hR : cache∉R) (hS : cache∉S) (hZ : cache∉Z)
    (hcache : t cache=((u%2==1) && (d%2==1))) (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (_h35 : u + d < 2^35) :
    Triple (PS R S t (u+d) 0) (fwdCK R S Z cs U cin k cache)
      (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) := by
  have s1 := sub33C_spec g cache hR hS cl u d hu hu32 hd hcache
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
      (addC cache (U++Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin)
      (PS R S (kz t k Z) (977*d+2^32*d+2^0*(u+2^32*(976*(if t k then 1 else 0)))) 0) := by
    intro s m hs
    simp only [List.drop_zero]
    rw [addC_ps_loose g cache hR hS kzc u d (977*d+2^32*d) 0
      ((kz_u g t k).trans hu) ((kz_out t k Z g.z cache hZ).trans hcache)
      (by omega) 11 43 42 (by decide) (by decide) s m hs]
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
  unfold fwdCK
  exact seqv s1 (PS_val (by omega)) (seqv s2 (PS_dval a2)
    (seqv s3 (fun _ h => h) (seqv s4 (PS_val a4) (seqv s5 (PS_dval a5)
    (seqv p1 (fun _ h => h) (seqv s6 (fun _ h => h)
    (Triple.conseq (fun s h => h) p2 (PS_val (by cases t k <;> simp <;> omega)))))))))


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

theorem invCK_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (cache : Wire) (hR : cache∉R) (hS : cache∉S) (hZ : cache∉Z)
    (hcache : t cache=((u%2==1) && (d%2==1))) (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (_h35 : u + d < 2^35) :
    Triple (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) (invCK R S Z cs U cin k cache)
      (PS R S t (u+d) 0) := by
  have p1 := kpat_PS g k hkR hkS hkZ t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0
  have s1 := sub43CK_spec g cl u d hu hu32 hd cache hR hS hZ hcache k hkZ
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
      (addC cache (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin)
      (PS R S t (d+2^0*u) 0) := by
    intro s m hs
    simp only [List.drop_zero]
    rw [addC_ps_loose g cache hR hS cl.cin u d d 0 hu hcache rfl
      1 33 32 (by decide) (by decide) s m hs]
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
  unfold invCK
  exact seqv p1 (fun _ h => h) (seqv s1 (fun _ h => h) (seqv p2 (PS_val (by ring))
    (seqv s2 (PS_dval a2) (seqv s3 (PS_val a3)
    (seqv s4 (fun _ h => h) (seqv s5 (PS_dval a5)
    (Triple.conseq (fun s h => h) s6 (PS_val (by omega)))))))))


#print axioms fwdCK_spec
#print axioms sub43CK_spec
#print axioms invCK_spec
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

set_option maxHeartbeats 1000000 in
theorem wMidCK_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cache : Wire) (cacheE : cache∈eReg L)
    (base : BasisState) (hc : L.PairClean base) (O E b1 : Nat) (hb1 : regValue (hiReg L) base = b1)
    (hb1lt : b1 < 2^128) (hO : O < SquareReduction.p)
    (H l K : Nat) (hH : H < 2^96) (hl : l < 2^32) (hK : K ≤ 1) (hE : E % 2^129 = 2^32*H + l + 2^128*K) :
    Triple (fun x=> BState L base O E (4294968272*b1) x ∧
      x cache=((b1/2^96%2==1) && ((4294968272*b1/2^128-b1/2^96)%2==1))) (wFwdCK L cache ++ (wCoreK L ++ wInvCK L cache))
      (fun x=> BState L base (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 4294968272*2^32*K +
        2^128*((4294968272*b1)%2^128) + (SquareReduction.p-1-O)) % SquareReduction.p) E (4294968272*b1) x ∧
      x cache=((b1/2^96%2==1) && ((4294968272*b1/2^128-b1/2^96)%2==1))) := by
  intro s m input
  obtain ⟨h,hCache⟩:=input
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
  obtain ⟨ws1, ws2, ws3⟩ := whi_split b1 hb1lt
  generalize hW : 4294968272*b1 = W at h hCache ws1 ws2 ws3 ⊢
  generalize hu : b1/2^96 = u at hCache ws1 ws2 ⊢
  generalize hd : W/2^128 - u = d at hCache ws2 ⊢
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
  have key : (if s.basis (eU L) = true then 1 else 0) = K := by
    have hv := eReg_split L hw s.basis
    rw [h.2.1] at hv
    have a1 := eLo_lt L hw s.basis
    have a2 := eMid_lt L hw s.basis
    cases e1 : s.basis (eU L) <;> cases e2 : s.basis (eV L) <;>
      simp only [e1, e2, Bool.false_eq_true, if_false, if_true] at hv ⊢ <;> omega
  have hkU : s.basis (eU L) = decide (K = 1) := by
    cases e : s.basis (eU L) <;> simp only [e, Bool.false_eq_true, if_false, if_true] at key <;> simp <;> omega
  have T1 : Triple (WinArith.PS (mR L) (mS L) s.basis (u+d) 0) (wFwdCK L cache)
      (WinArith.PS (mR L) (mS L) s.basis (u + 4294968273*d + 2^32*(976*K)) 0) := by
    have := fwdCK_spec g cl u d hU hu32 ws2 cache cr cS cZ hCache (eU L) heR heS heZ (by omega)
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
  have T3 : Triple Q2 (wInvCK L cache) Q3 := by
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
    obtain ⟨ph, h3⟩ := invCK_spec g cl2 u d hU2 hu32 ws2 cache cr cS cZ hCache2 (eU L) heR heS heZ (by omega) s2 m2 P2
    refine ⟨ph, ?_, h3.1, h3.2.1, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => h3.2.2 q (fun hr => (m_away L hn q (Or.inl hr)).1 hq)
        (fun hs => (m_away L hn q (Or.inr hs)).1 hq))).trans h2.1
    · intro q a b c; exact (h3.2.2 q b c).trans (k2 q a b c)
  obtain ⟨ph, f⟩ := (T1.seq (T2.seq T3)) s m P0
  refine ⟨ph, ⟨f.1, ?_, ?_, ?_⟩, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => f.2.2.2 q (eReg_away L hn q hq).1
      (fun hr => (m_away L hn q (Or.inl hr)).2 hq) (fun hs => (m_away L hn q (Or.inr hs)).2 hq))).trans h.2.1
  · -- the work register is `W` again
    have wv : regValue L.core.work (run (wFwdCK L cache ++ (wCoreK L ++ wInvCK L cache)) m s).basis = W := by
      rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
      have lo : regValue (L.core.work.take 128) (run (wFwdCK L cache ++ (wCoreK L ++ wInvCK L cache)) m s).basis = W % 2^128 := by
        rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
          WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
      have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdCK L cache ++ (wCoreK L ++ wInvCK L cache)) m s).basis = 0 := by
        apply (regValue_zero _ _).mpr
        intro q hq
        rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
        apply workZ
        have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
        rw [this] at hq
        exact List.mem_of_mem_drop hq
      have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdCK L cache ++ (wCoreK L ++ wInvCK L cache)) m s).basis = u + d :=
        f.2.1
      rw [lo, mr, hi0]
      omega
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) (run (wFwdCK L cache ++ (wCoreK L ++ wInvCK L cache)) m s).basis
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
      have wv : regValue L.core.work (run (wFwdCK L cache ++ (wCoreK L ++ wInvCK L cache)) m s).basis = W := by
        rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
        have lo : regValue (L.core.work.take 128) (run (wFwdCK L cache ++ (wCoreK L ++ wInvCK L cache)) m s).basis = W % 2^128 := by
          rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
            WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
        have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdCK L cache ++ (wCoreK L ++ wInvCK L cache)) m s).basis = 0 := by
          apply (regValue_zero _ _).mpr
          intro q hq
          rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
          apply workZ
          have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
          rw [this] at hq
          exact List.mem_of_mem_drop hq
        have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdCK L cache ++ (wCoreK L ++ wInvCK L cache)) m s).basis = u + d :=
          f.2.1
        rw [lo, mr, hi0]
        omega
      have z : regValue (L.core.work.drop 163) (run (wFwdCK L cache ++ (wCoreK L ++ wInvCK L cache)) m s).basis = 0 := by
        rw [WinArith.drop_div _ _ (by simp [hw.core.work]), wv, Nat.div_eq_of_lt hWlt]
      rw [(regValue_zero _ _).mp z q hd163]
      exact ((regValue_zero _ _).mp hc.work q wq).symm
    by_cases hs : q ∈ mS L
    · rw [(regValue_zero _ _).mp f.2.2.1 q hs]
      exact ((regValue_zero _ _).mp hc.pad q (mS_pad L q hs)).symm
    · exact (f.2.2.2 q h1 hr hs).trans (keepS q h1 h2 h3)



  · exact (f.2.2.2 cache co cr cS).trans hCache

#print axioms wMidCK_step
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

theorem wMidFullCK_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (base : BasisState) (hc : L.PairClean base) (O E b1 : Nat) (hb1 : regValue (hiReg L) base=b1)
 (hb1lt : b1<2^128) (hO : O<SquareReduction.p)
 (H l K : Nat) (hH : H<2^96) (hl : l<2^32) (hK : K≤1)
 (hE : E=2^32*H+l+2^128*K) :
 Triple (BState L base O E (4294968272*b1)) (wMidFullCK L)
 (BState L base (((b1/2^96+4294968273*(4294968272*b1/2^128-b1/2^96))+4294968272*2^32*K+
    2^128*((4294968272*b1)%2^128)+(SquareReduction.p-1-O))%SquareReduction.p) E (4294968272*b1)) := by
 let k : Bool := (b1/2^96%2==1) && ((4294968272*b1/2^128-b1/2^96)%2==1)
 let E' : Nat:=E+2^129*k.toNat
 let O' := (((b1/2^96+4294968273*(4294968272*b1/2^128-b1/2^96))+4294968272*2^32*K+
    2^128*((4294968272*b1)%2^128)+(SquareReduction.p-1-O))%SquareReduction.p)
 have cg:=cache_geometry L hw hn
 have ce:=cache_mem L hw
 have heads (s : BasisState) (O0 E0 : Nat) (h : BState L base O0 E0 (4294968272*b1) s) :
   (s ((mU L).headD 0) && !(s ((mR L).headD 0)))=k := by
  obtain ⟨hu,hr⟩:=bstate_heads L hw hn base s hc O0 E0 b1 hb1 hb1lt h
  rw [hu,hr]
  simpa only [Nat.one_mul] using carry_parity (b1/2^96) (4294968272*b1/2^128-b1/2^96) 1 (by decide)
 have T1 : Triple (BState L base O E (4294968272*b1))
   (prime ((mU L).headD 0) ((mR L).headD 0) (cacheWire L))
   (fun s=>BState L base O E' (4294968272*b1) s ∧ s (cacheWire L)=k) := by
  intro s m h
  have hz:=e_cache_zero L hw s.basis E h.2.1 (by rw [hE];omega)
  have hk:=heads s.basis O E h
  rw [prime_run _ _ _ cg.1 cg.2.2 cg.2.1]
  rw [hz,Bool.false_xor,hk]
  refine ⟨rfl,?_,?_⟩
  · have he:=e_write_value L hw hn s.basis k
    rw [hz,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,h.2.1] at he
    simpa only [he] using bstate_write_e L hn _ ce base s.basis O E _ h k
  · simp [writeBit]
 have T2 := wMidCK_step L hw hn (cacheWire L) ce base hc O E' b1 hb1 hb1lt hO H l K hH hl hK (by dsimp [E'];cases k <;> simp [Bool.toNat] <;> omega)
 have T3 : Triple (fun s=>BState L base O' E' (4294968272*b1) s ∧ s (cacheWire L)=k)
   (clear ((mU L).headD 0) ((mR L).headD 0) (cacheWire L))
   (BState L base O' E (4294968272*b1)) := by
  intro s m h
  have hk:=heads s.basis O' E' h.1
  rw [clear_run _ _ _ cg.2.1 cg.2.2 s m (h.2.trans hk.symm)]
  refine ⟨rfl,?_⟩
  have he:=e_write_value L hw hn s.basis false
  rw [h.2,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,h.1.2.1] at he
  have hv : regValue (eReg L) (writeBit s.basis (cacheWire L) false)=E:= by dsimp [E'] at he;omega
  simpa only [hv] using bstate_write_e L hn _ ce base s.basis O' E' _ h.1 false
 exact Triple.seq T1 (Triple.seq T2 T3)

#print axioms bstate_heads
#print axioms cache_geometry
#print axioms wMidFullCK_step


#print axioms wMidFullCK_step
end ECDSAAdd.Entrant.CarryWindowCache

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CarryWindowCache
open ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
def wFoldCK (L : CuccaroStreamedSquareWideLayout) : Program :=
  eAddLo L++(wBuild L++(wMidFullCK L++(wUnbuildKnown L++(kapClr L++eSubK L))))

/-- The restore: `+b1`, then the low-window `-u`.
No rebuild of `W`; 733 no-op measurements keep the measurement count of the B body. -/
def wRestoreCK (L : CuccaroStreamedSquareWideLayout) : Program :=
  eAddB L++(eSubLo L++padM L 720)

def bBodyCK (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(wFoldCK L++(eFoldTq L c++wRestoreCK L)))


theorem bBodyCK_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (bBodyCK L c) (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
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
  -- wFoldCK
  have k1 := eAddLo_step L hw hn base hc O2 0 b0 hb0
  rw [hb1] at k1
  have w1 := wBuild_step L hw hn base hc O2 (2^32*H + l' + 2^128*K)
  rw [hb1] at w1
  have wm := wMidFullCK_step L hw hn base hc O2 (2^32*H + l' + 2^128*K) b1 hb1 hb1lt hO2 H l' K hH hl' hK rfl
  have w5 := wUnbuildKnown_step L hw hn base hc O3 (2^32*H + l' + 2^128*K)
  rw [hb1] at w5
  have kc := kapClr_step L hw hn base hc O3 0 H l' hH hl'
  rw [hb1] at kc
  change Triple (BState L base O3 (2^32*H + l' + 2^128*(if l' < u then 1 else 0)) 0) (kapClr L)
    (BState L base O3 (2^32*H + l') 0) at kc
  rw [hKif] at kc
  have w3 := eSubK_step L hw hn base hc O3 (2^32*H + l') 0 b1 (by omega) hb1
  have tw : Triple (BState L base O2 b0 0) (wFoldCK L) (BState L base O3 E1 0) :=
    k1.seq (w1.seq (wm.seq (w5.seq (kc.seq w3))))
  -- eFoldTq
  have f1 := eFlip_step L hw hn base c hcw O3 E1 0
  have f2 := eCore_stepTq L hw hn base hc O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn base c hcw O4 (flipE g E1) 0
  rw [flipE_flipE] at f3
  have tf : Triple (BState L base O3 E1 0) (eFoldTq L c) (BState L base O4 E1 0) :=
    f1.seq (f2.seq f3)
  -- wRestoreCK
  have bk : (E1+b1)%2^130 = 2^32*H + l' := by show ((2^32*H + l' + 2^130 - b1) % 2^130 + b1) % 2^130 = _; omega
  have r2 := eAddB_step L hw hn base hc O4 E1 0 b1 hb1 (by rw [bk]; omega)
  rw [bk] at r2
  have r3 := eSubLo_step L hw hn base hc O4 0 H l' hH hl'
  rw [hb1] at r3
  have bb : 2^32*H + (l' + 2^32 - u) % 2^32 = b0 := by
    show 2^32*(b0/2^32) + ((b0%2^32 + u)%2^32 + 2^32 - u) % 2^32 = b0; omega
  rw [bb] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 720
  have tr : Triple (BState L base O4 E1 0) (wRestoreCK L) (BState L base O4 b0 0) :=
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


#print axioms bBodyCK_frame
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

theorem bBodyCK_delta (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (bBodyCK L c)+3=toffoliCount (bBodyN L c) ∧
 measurementCount (bBodyCK L c)=measurementCount (bBodyN L c) ∧
 Challenge.gateSlots (bBodyCK L c)+15=Challenge.gateSlots (bBodyN L c) := by
 have h:=mid_counts L hw
 have pt:=padM_counts L 720;have po:=padM_counts L 721
 have ps:=padM_slots L 720;have os:=padM_slots L 721
 simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at h
 simp only [bBodyCK,bBodyN,wFoldCK,wFoldN,wRestoreCK,wRestoreN,
  toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

theorem bBodyCK_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (bBodyCK L c)=4801 ∧ measurementCount (bBodyCK L c)=5924 := by
 have h:=bBodyCK_delta L hw c
 have old:=bBodyN_counts L hw c
 exact ⟨by omega,by omega⟩

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


#print axioms bBodyCK_counts
#print axioms mid_physical
end ECDSAAdd.Entrant.CarryWindowCache

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.CarryWindowCache
open ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
theorem bBodyCK_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (hn : (c::L.wires).Nodup) : GatePhysical (bBodyCK L c) := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw := (List.nodup_cons.mp hn).1
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have p1 := measuredFoldQ_physicalTq L hw nd (negP L) sP
  have p2 := measuredFoldQ_physicalTq L hw nd (rot128F L) sR
  have wb := CodexNarrowTail.build8_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    (acc_lengths L hw).1 (by rw [hiReg_length L hw]) (wTerms_fits L hw nd)
  rw [CodexNarrowTail.build8_eq] at wb
  have wc := QCore.qprog_physicalTq (rotWCore L) SquareReduction.p (rotWCore_nodup L nd)
  have hct : c∉(eReg L).take 129 := fun hm => hcw (by
    have := eReg_product L c (List.mem_of_mem_take hm)
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this])
  have fl : GatePhysical (eFlip L c) := maskedConstant_physical c ((eReg L).take 129) (2^129-1) hct
  have st := eItem_static L hw
  have ac := Q4.accFoldQ4KTq_physical L hw nd (eItem L) st.1 st.2.1 st.2.2.1 st.2.2.2
  have g := mGeo L hw nd
  have heZ : eU L ∉ mZ L := fun hz => (eU_away L hw nd).1 (mZ_pad L _ hz)
  simp only [bBodyCK,wFoldCK,eFoldTq,wRestoreCK,gatePhysical_append]
  exact ⟨p1,p2,⟨eAddLo_physical L hw nd,wb.1,mid_physical L hw nd,wUnbuildKnown_physical L hw nd,
    kapClr_physical L hw nd,eSubK_physical L hw nd⟩,⟨fl,ac,fl⟩,
    ⟨eAddB_physical L hw nd,eSubLo_physical L hw nd,padM_physical L 720⟩⟩

theorem bBodyCK_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    QRel.Le (bBodyCK L c) (bBody L c) := by
  refine ⟨?_, ?_⟩
  · have hs : wires (wFoldCK L++(eFoldTq L c++wRestoreCK L)) ⊆
        wires (wFold L++(eFold L c++wRestore L)) := by
      have wc := (QRel.qprog_le (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)).1
      have ef := (QRel.eFold_le L hw c).1
      have sk := eSubK_wires L hw
      have ab := eAddB_wires L hw
      have ml {A B : Program} {q : Wire} (h : q ∈ wires A) : q ∈ wires (A ++ B) := by
        rw [wires_append]; exact Finset.mem_union_left _ h
      have mr {A B : Program} {q : Wire} (h : q ∈ wires B) : q ∈ wires (A ++ B) := by
        rw [wires_append]; exact Finset.mem_union_right _ h
      have hOE {q : Wire} (h : q ∈ oldE L) : q ∈ wires (wFold L ++ (eFold L c ++ wRestore L)) := by
        rcases Finset.mem_union.mp h with h|h
        · exact ml (mr (mr (ml h)))
        · exact ml (mr (mr (mr (ml h))))
      intro q hq
      simp only [wFoldCK,wMidFullCK,wCoreK,wRestoreCK,wires_append,Finset.mem_union] at hq
      rcases hq with (h|h|(h|((h|(h|h|h)|h)|h))|h|h|h)|h|h|h|h
      · exact hOE (eAddLo_oldE L hw h)
      · exact ml (ml h)
      · exact hOE ((cache_ends_oldE L hw).1 h)
      · exact hOE ((cached_arm_oldE L hw).1 h)
      · exact hOE (kw_oldE L hw h)
      · exact ml (mr (ml (wc h)))
      · exact hOE (kw_oldE L hw h)
      · exact hOE ((cached_arm_oldE L hw).2 h)
      · exact hOE ((cache_ends_oldE L hw).2 h)
      · exact ml (mr (mr (mr (mr (wUnbuildKnown_wires L hw h)))))
      · exact hOE (kapClr_oldE L hw h)
      · exact ml (mr (mr (ml (sk h))))
      · exact mr (ml (ef h))
      · exact mr (mr (mr (mr (ml (ab h)))))
      · exact hOE (eSubLo_oldE L hw h)
      · exact hOE (padM_oldE L hw 720 h)
    simpa only [bBodyCK,bBody,wires_append] using
      Finset.union_subset_union (QRel.measuredFoldQ_le L hw (negP L)).1
        (Finset.union_subset_union (QRel.measuredFoldQ_le L hw (rot128F L)).1 hs)
  · have h := (bBodyCK_delta L hw c).2.2
    have old := (bBodyN_le L hw c).2
    omega

theorem bBodyCK_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (c : Wire) :
 ECDSAAdd.wires (bBodyCK L c)⊆(c::L.wires).toFinset := (bBodyCK_le L hw c).1.trans (bBody_support L hw hn c)
theorem bBodyCK_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (bBodyCK L c)+1022=toffoliCount (bBody L c) ∧
 measurementCount (bBodyCK L c)+4=measurementCount (bBody L c) ∧ QRel.Le (bBodyCK L c) (bBody L c) := by
 have a:=bBodyCK_counts L hw c
 have b:=bBody_counts L hw c
 exact ⟨by omega,by omega,bBodyCK_le L hw c⟩
#print axioms bBodyCK_physical
#print axioms bBodyCK_le
#print axioms bBodyCK_rel
end ECDSAAdd.Entrant.CarryWindowCache
