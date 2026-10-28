import ECDSAAdd.Arithmetic.NativeFirstDirectWordProof
import ECDSAAdd.Arithmetic.NativeFirstDirectLayout

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run mappedAdd hAdd kAdd kTail lowCopy rotateRight forward

private theorem block_one (w : Nat → Wire) (a : Nat) :
    wireBlock w a 1=[w a] := by simp [wireBlock,List.range']

private theorem cons_value (h : Wire) (r : List Wire) (s : BasisState) :
    regValue (h::r) s=(s h).toNat+2*regValue r s := by
  cases hb : s h <;> simp [regValue,hb]

private theorem write_value (r : List Wire) (s : BasisState) (q : Wire) (v : Bool)
    (ha : q∉r) : regValue r (writeBit s q v)=regValue r s := by
  apply regValue_congr
  intro j hj
  simp [writeBit,show j≠q from fun e => ha (e ▸ hj)]

private theorem contained (w : Nat → Wire) (a n b m : Nat)
    (lo : b≤a) (hi : a+n≤b+m) : ∀q∈wireBlock w a n,q∈wireBlock w b m := by
  intro q hq
  obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨i,by
    simp only [List.mem_range'_1] at hi' ⊢
    omega,rfl⟩

/-- A257 and Ext258 are preserved even though the physical A view is wider. -/
def mutable (w : Nat → Wire) : List Wire :=
  wireBlock w 0 257++wireBlock w 770 258++[w 1028]

private def Stable (w : Nat → Wire) (s t : State) : Prop :=
  t.phase=s.phase ∧ ∀q,q∉mutable w → t.basis q=s.basis q

private theorem stable_trans (w : Nat → Wire) (s t u : State)
    (a : Stable w s t) (b : Stable w t u) : Stable w s u :=
  ⟨b.1.trans a.1,fun q hq => (b.2 q hq).trans (a.2 q hq)⟩

private theorem stable_target (w : Nat → Wire) (s t : State) (r : List Wire)
    (hp : t.phase=s.phase) (hf : ∀q,q∉r → t.basis q=s.basis q)
    (hr : ∀q∈r,q∈mutable w) : Stable w s t :=
  ⟨hp,fun q hq => hf q (fun h => hq (hr q h))⟩

private theorem stable_write (w : Nat → Wire) (s : State) (q : Wire) (v : Bool)
    (hq : q∈mutable w) : Stable w s ⟨s.phase,writeBit s.basis q v⟩ := by
  refine ⟨rfl,?_⟩
  intro j hj
  simp [writeBit,show j≠q from fun e => hj (e ▸ hq)]

private theorem outside_index (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i < 1798) (ha : 257 ≤ i) (hb : i < 770 ∨ 1028 ≤ i)
    (hs : i ≠ 1028) : w i∉mutable w := by
  simp only [mutable,List.mem_append,List.mem_singleton,not_or]
  exact ⟨⟨block_not_mem w hn i 0 257 hi (by omega) (by omega),
    block_not_mem w hn i 770 258 hi (by omega) hb⟩,
    index_ne w hn i 1028 hi (by omega) hs⟩

private theorem bank_clean (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s t : State) (a n : Nat) (ha : 1540≤a) (hb : a+n≤1797)
    (hc : regValue (wireBlock w 1540 257) s.basis=0) (fr : Stable w s t) :
    ∀q∈wireBlock w a n,t.basis q=false := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  rw [fr.2 _ (outside_index w hn i (by omega) (by omega) (by omega) (by omega))]
  exact (regValue_zero _ _).mp hc _ (List.mem_map.mpr
    ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)

private theorem keep_value (r target : List Wire) (s t : BasisState)
    (hf : ∀q,q∉target → t q=s q) (sep : List.Disjoint r target) :
    regValue r t=regValue r s :=
  regValue_congr r t s (fun q hq => hf q (List.disjoint_left.mp sep hq))

private theorem clear_value (h : Wire) (r : List Wire) (s : BasisState)
    (ha : h∉r) (X : Nat) (hv : regValue (h::r) s=X) :
    regValue (h::r) (writeBit s h false)=2*(X/2) := by
  rw [cons_value,show (writeBit s h false) h=false by simp [writeBit],
    Bool.toNat_false,write_value r s h false ha]
  rw [cons_value] at hv
  cases hb : s h <;> simp only [hb,Bool.toNat_false,Bool.toNat_true] at hv <;> omega

/-- Copy prepares the complete H word from a canonical x, with full frame. -/
theorem lowCopy_prepares (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<2^256) (s : State) (m : List Bool)
    (ha : regValue (wireBlock w 1 256) s.basis=0)
    (hb : regValue (wireBlock w 770 258) s.basis=x) :
    (run (lowCopy w) m s).phase=s.phase ∧
    (∀q,q∉wireBlock w 1 255 → (run (lowCopy w) m s).basis q=s.basis q) ∧
    regValue (wireBlock w 1 256) (run (lowCopy w) m s).basis=x/2 := by
  have raw := copyRegister_correct none (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length]) (copy_inputs_nd w hn) (by simp) s m
  have c : (run (lowCopy w) m s).phase=s.phase ∧
      (∀q,q∉wireBlock w 1 255 → (run (lowCopy w) m s).basis q=s.basis q) ∧
      regValue (wireBlock w 1 255) (run (lowCopy w) m s).basis=
        regValue (wireBlock w 1 255) s.basis ^^^ regValue (wireBlock w 771 255) s.basis := by
    simpa only [lowCopy,copyValue] using raw
  generalize hz : run (lowCopy w) m s=z at c ⊢
  have clean := (regValue_zero _ _).mp ha
  have dst : regValue (wireBlock w 1 255) s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact clean q (block_subset w 1 255 256 (by omega) q hq)
  have splitB := wireBlock_append w 770 256 2
  have val := hb
  rw [←splitB,regValue_append,wireBlock_length] at val
  have bound := regValue_lt (wireBlock w 770 256) s.basis
  rw [wireBlock_length] at bound
  have low : regValue (wireBlock w 770 256) s.basis=x := by omega
  have splitLow : w 770::wireBlock w 771 255=wireBlock w 770 256 := by
    simpa [block_one] using wireBlock_append w 770 1 255
  have bits : (if s.basis (w 770) then 1 else 0)+
      2*regValue (wireBlock w 771 255) s.basis=x := by
    rw [←splitLow] at low
    exact low
  have src : regValue (wireBlock w 771 255) s.basis=x/2 := by
    cases e : s.basis (w 770) <;> simp [e] at bits <;> omega
  have guard : s.basis (w 256)=false := clean _ (List.mem_map.mpr
    ⟨256,by simp [List.mem_range'_1],rfl⟩)
  have guardOut : z.basis (w 256)=false :=
    (c.2.1 _ (block_not_mem w hn 256 1 255 (by omega) (by omega) (by omega))).trans guard
  refine ⟨c.1,c.2.1,?_⟩
  have splitH := wireBlock_append w 1 255 1
  rw [←splitH,regValue_append]
  have value : regValue (wireBlock w 1 255) z.basis=x/2 := by
    simpa only [dst,src,Nat.zero_xor] using c.2.2
  have high : regValue (wireBlock w 256 1) z.basis=0 := by
    simp only [block_one,regValue,List.foldr_cons,List.foldr_nil,guardOut,
      Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero]
  rw [value,high,Nat.mul_zero,Nat.add_zero]
/-- Complete emitted forward state on the original canonical seed domain.
The Nat expressions are the physical word encodings of the direct first tick. -/
theorem forward_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s : State) (m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis) :
    let e := s.basis (w 770)
    let z := run (forward w) m s
    z.phase=s.phase ∧
    regValue (wireBlock w 0 258) z.basis=
      2*(x/2+(if e then hConstant else 0))+(!e).toNat ∧
    regValue (wireBlock w 770 258) z.basis=
      (x/2+kConstant false e)%2^258 ∧
    z.basis (w 0)=!e ∧ z.basis (w 1028)=e ∧
    (∀q,q∉mutable w → z.basis q=s.basis q) := by
  let e := s.basis (w 770)
  generalize ha : run [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)] m s=a
  generalize hb : run (lowCopy w) m a=b
  generalize hcr : run (hAdd w false) m b=c
  generalize hd : run [.CX (w 1028) (w 770)] (m.drop 252) c=d
  generalize ht : run (rotateRight (wireBlock w 770 258)) (m.drop 252) d=t
  generalize hu : run (kAdd w false) (m.drop 252) t=u
  have full : run (forward w) m s=u := by
    simp only [forward,List.append_assoc]
    rw [run_append,run_take,
      show measurementCount [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]=0 from rfl,
      List.drop_zero,ha]
    rw [run_append,run_take,(lowCopy_counts w).2,List.drop_zero,hb]
    rw [run_append,run_take,(hAdd_counts w false).2,hcr]
    rw [run_append,run_take,
      show measurementCount [.CX (w 1028) (w 770)]=0 from rfl,List.drop_zero,hd]
    rw [run_append,run_take,(rotate_counts (wireBlock w 770 258)).2.1,List.drop_zero,ht,hu]
  have cleanA := (regValue_zero _ _).mp hin.a
  have mem0 : w 0∈wireBlock w 0 258 := List.mem_map.mpr
    ⟨0,by simp [List.mem_range'_1],rfl⟩
  have fr := front_spec w s m (index_ne w hn 0 1028 (by omega) (by omega) (by omega))
    (cleanA _ mem0) hin.one
  rw [ha] at fr
  have ah : regValue (wireBlock w 1 256) a.basis=0 := by
    rw [fr,write_value _ _ (w 0) _ (block_not_mem w hn 0 1 256 (by omega) (by omega) (by omega)),
      write_value _ _ (w 1028) _ (block_not_mem w hn 1028 1 256 (by omega) (by omega) (by omega))]
    exact (regValue_zero _ _).mpr (fun q hq => cleanA q (contained w 1 256 0 258 (by omega) (by omega) q hq))
  have ab : regValue (wireBlock w 770 258) a.basis=x := by
    rw [fr,write_value _ _ (w 0) _ (block_not_mem w hn 0 770 258 (by omega) (by omega) (by omega)),
      write_value _ _ (w 1028) _ (block_not_mem w hn 1028 770 258 (by omega) (by omega) (by omega))]
    exact hin.b
  have ag : a.basis (w 0)=!e := by rw [fr]; simp [e,writeBit]
  have ase : a.basis (w 1028)=e := by
    rw [fr]; simp [e,writeBit,index_ne w hn 1028 0 (by omega) (by omega) (by omega)]
  have ae : a.basis (w 770)=e := by
    rw [fr]; simp [e,writeBit,index_ne w hn 770 0 (by omega) (by omega) (by omega),
      index_ne w hn 770 1028 (by omega) (by omega) (by omega)]
  have fa : Stable w s a := by
    rw [fr]
    apply stable_trans w s ⟨s.phase,writeBit s.basis (w 1028) e⟩
    · exact stable_write w s _ _ (by simp [mutable])
    · exact stable_write w _ _ _ (by
        simp only [mutable,List.mem_append,List.mem_singleton]
        exact Or.inl (Or.inl (List.mem_map.mpr ⟨0,by simp [List.mem_range'_1],rfl⟩)))
  have xb : x<2^256 := lt_trans hx (by norm_num [p])
  have cp := lowCopy_prepares w hn x xb a m ah ab
  rw [hb] at cp
  have fb : Stable w s b := stable_trans w s a b fa (stable_target w a b _
    cp.1 cp.2.1 (fun q hq => by
      simp only [mutable,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (contained w 1 255 0 257 (by omega) (by omega) q hq))))
  have bs : b.basis (w 1028)=e := (cp.2.1 _ (block_not_mem w hn 1028 1 255 (by omega) (by omega) (by omega))).trans ase
  have bg : b.basis (w 0)=!e := (cp.2.1 _ (block_not_mem w hn 0 1 255 (by omega) (by omega) (by omega))).trans ag
  have be : b.basis (w 770)=e := (cp.2.1 _ (block_not_mem w hn 770 1 255 (by omega) (by omega) (by omega))).trans ae
  have bb : regValue (wireBlock w 770 258) b.basis=x :=
    (keep_value _ _ _ _ cp.2.1 (block_disjoint w hn 770 258 1 255 (by omega) (by omega) (by omega))).trans ab
  have fit : regValue (wireBlock w 1 256) b.basis+(if b.basis (w 1028) then hConstant else 0)<2^256 := by
    rw [cp.2.2,bs]
    have pp : p<2^256 := by norm_num [p]
    have hh : 2*hConstant=p+1 := by norm_num [hConstant,p]
    cases he : e <;> simp [he] <;> omega
  have hc := hAdd_word w b m (h_inputs_nd w hn) (h_sources_fresh w hn false)
    (bank_clean w hn s b 1540 252 (by omega) (by omega) hin.carry fb)
    ((fb.2 _ (outside_index w hn 1797 (by omega) (by omega) (by omega) (by omega))).trans hin.cin)
    (List.disjoint_left.mp (block_disjoint w hn 1 3 4 253 (by omega) (by omega) (by omega))) fit
  rw [hcr] at hc
  have fc : Stable w s c := stable_trans w s b c fb (stable_target w b c _
    hc.1 hc.2.1 (fun q hq => by
      simp only [mutable,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (contained w 4 253 0 257 (by omega) (by omega) q hq))))
  have ch : regValue (wireBlock w 1 256) c.basis=x/2+(if e then hConstant else 0) := by rw [hc.2.2,cp.2.2,bs]
  have cs : c.basis (w 1028)=e := (hc.2.1 _ (block_not_mem w hn 1028 4 253 (by omega) (by omega) (by omega))).trans bs
  have cg : c.basis (w 0)=!e := (hc.2.1 _ (block_not_mem w hn 0 4 253 (by omega) (by omega) (by omega))).trans bg
  have ce : c.basis (w 770)=e := (hc.2.1 _ (block_not_mem w hn 770 4 253 (by omega) (by omega) (by omega))).trans be
  have cb : regValue (wireBlock w 770 258) c.basis=x :=
    (keep_value _ _ _ _ hc.2.1 (block_disjoint w hn 770 258 4 253 (by omega) (by omega) (by omega))).trans bb
  have cl := clear_spec w c (m.drop 252) (ce.trans cs.symm)
  rw [hd] at cl
  have fd : Stable w s d := stable_trans w s c d fc (by
    rw [cl]
    exact stable_write w c _ _ (by
      simp only [mutable,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inr (List.mem_map.mpr ⟨770,by simp [List.mem_range'_1],rfl⟩))))
  have headB : w 770::wireBlock w 771 257=wireBlock w 770 258 := by
    simpa [block_one] using wireBlock_append w 770 1 257
  have awayB : w 770∉wireBlock w 771 257 := block_not_mem w hn 770 771 257 (by omega) (by omega) (by omega)
  have db : regValue (wireBlock w 770 258) d.basis=2*(x/2) := by
    rw [cl,←headB]
    exact clear_value _ _ _ awayB x (by rw [headB]; exact cb)
  have rr := rotateRight_spec (wireBlock w 770 258) (block_nodup w hn 770 258 (by omega))
    (2*(x/2)) (by omega) d (m.drop 252) db
  have rf := rotate_frame (wireBlock w 770 258) d (m.drop 252)
  rw [ht] at rr rf
  have ft : Stable w s t := stable_trans w s d t fd (stable_target w d t _ rf.1 rf.2.1 (by
    intro q hq; simp [mutable,hq]))
  have tb : regValue (wireBlock w 770 258) t.basis=x/2 := by simpa using rr.2
  have ts : t.basis (w 1028)=e := by
    rw [rf.2.1 _ (block_not_mem w hn 1028 770 258 (by omega) (by omega) (by omega)),cl]
    simpa [writeBit,index_ne w hn 1028 770 (by omega) (by omega) (by omega)] using cs
  have tg : t.basis (w 0)=!e := by
    rw [rf.2.1 _ (block_not_mem w hn 0 770 258 (by omega) (by omega) (by omega)),cl]
    simpa [writeBit,index_ne w hn 0 770 (by omega) (by omega) (by omega)] using cg
  have kh := kAdd_word w t (m.drop 252) (k_inputs_nd w hn) (k_sources_fresh w hn false)
    (bank_clean w hn s t 1540 256 (by omega) (by omega) hin.carry ft)
  rw [hu] at kh
  have fu : Stable w s u := stable_trans w s t u ft (stable_target w t u _ kh.1 kh.2.1 (by
    intro q hq; simp [mutable,hq]))
  have uh : regValue (wireBlock w 1 256) u.basis=x/2+(if e then hConstant else 0) := by
    rw [keep_value _ _ _ _ kh.2.1 (block_disjoint w hn 1 256 770 258 (by omega) (by omega) (by omega)),
      keep_value _ _ _ _ rf.2.1 (block_disjoint w hn 1 256 770 258 (by omega) (by omega) (by omega)),cl,
      write_value _ _ (w 770) _ (block_not_mem w hn 770 1 256 (by omega) (by omega) (by omega))]
    exact ch
  have ug : u.basis (w 0)=!e := (kh.2.1 _ (block_not_mem w hn 0 770 258 (by omega) (by omega) (by omega))).trans tg
  have us : u.basis (w 1028)=e := (kh.2.1 _ (block_not_mem w hn 1028 770 258 (by omega) (by omega) (by omega))).trans ts
  have guard : u.basis (w 257)=false := (fu.2 _ (outside_index w hn 257 (by omega) (by omega) (by omega) (by omega))).trans
    (cleanA _ (List.mem_map.mpr ⟨257,by simp [List.mem_range'_1],rfl⟩))
  have ua : regValue (wireBlock w 0 258) u.basis=2*(x/2+(if e then hConstant else 0))+(!e).toNat := by
    rw [←wireBlock_append w 0 257 1,regValue_append,block_one]
    have headA : w 0::wireBlock w 1 256=wireBlock w 0 257 := by
      simpa [block_one] using wireBlock_append w 0 1 256
    rw [←headA,cons_value,ug,uh]
    simp [regValue,guard,wireBlock_length,Nat.add_comm]
  rw [full]
  exact ⟨fu.1,ua,by simpa [tb,ts] using kh.2.2,ug,us,fu.2⟩

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.lowCopy_prepares
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.forward_spec
