import ECDSAAdd.Submission.Entrant.FrontierEntry1591Forward

/-! The new history decoder precedes each unchanged reverse integer tick.
The final parity restore must complete before this program starts. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.NewStackOB5
open Arithmetic MappedCompressed Secp256k1 OB5

def unpackFirst (w : Nat → Wire) (i : Nat) : Program :=
  if i=5 then ParityCodec5New.decodeAtFirst (History5.historyMap w 0)
  else NewHistory5.decodeBefore w i

def regularReverse (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => regularReverse w (i+1) n ++
      (NewHistory5.decodeBefore w i ++ W.ReverseCarry.compactReceiverTick w i)

def reverse (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => reverse (i+1) n ++ renameProgram (sig i)
      (unpackFirst base i ++ W.ReverseCarry.compactReceiverTick base i)

def stackReverse510 : Program :=
  renameProgram (sig 510) (NewHistory5.decodeBefore base 510 ++ tick510R) ++ reverse 1 509

def stackReverseT : Program := renameProgram (sig 511) tickR ++ stackReverse510

attribute [local irreducible] run wires measurementCount regularForward regularReverse reverse
  stackForwardT stackReverseT stackReverse510
  W.repairedTick W.compactSkywalkTick W.ReverseCarry.compactReceiverTick
  ParityCodec5New.encodeAt ParityCodec5New.decodeAt ParityCodec5New.encodeAtFirst ParityCodec5New.decodeAtFirst

theorem regularReverse_snoc (w : Nat → Wire) (i n : Nat) :
    regularReverse w i (n+1)=
      (NewHistory5.decodeBefore w (i+n) ++ W.ReverseCarry.compactReceiverTick w (i+n)) ++
        regularReverse w i n := by
  induction n generalizing i with
  | zero => simp [regularReverse]
  | succ n ih =>
    rw [regularReverse,ih (i+1),regularReverse]
    rw [show i+1+n=i+(n+1) by omega]
    simp only [List.append_assoc]

theorem reverse_snoc (i n : Nat) : reverse i (n+1)=
    renameProgram (sig (i+n))
      (unpackFirst base (i+n) ++ W.ReverseCarry.compactReceiverTick base (i+n)) ++
        reverse i n := by
  induction n generalizing i with
  | zero => simp [reverse]
  | succ n ih =>
    rw [reverse,ih (i+1),reverse]
    rw [show i+1+n=i+(n+1) by omega]
    simp only [List.append_assoc]

theorem unpack511 : unpackFirst base 511=[] := by decide +kernel

theorem reverse_split511 : reverse 1 511=
    renameProgram (sig 511) (W.ReverseCarry.compactReceiverTick base 511) ++ reverse 1 510 := by
  rw [reverse_snoc 1 510,show 1+510=511 by rfl,unpack511,List.nil_append]

theorem reverse_split510 : reverse 1 510=
    renameProgram (sig 510)
      (NewHistory5.decodeBefore base 510 ++ W.ReverseCarry.compactReceiverTick base 510) ++
        reverse 1 509 := by
  have packet : unpackFirst base 510=NewHistory5.decodeBefore base 510 := by
    unfold unpackFirst
    exact if_neg (by decide)
  exact (reverse_snoc 1 509).trans (congrArg
    (fun P : Program => renameProgram (sig 510)
      (P ++ W.ReverseCarry.compactReceiverTick base 510) ++ reverse 1 509) packet)

theorem decodeBefore_support_eq (w : Nat → Wire) (i : Nat) :
    wires (NewHistory5.decodeBefore w i)=wires (History5.decodeBefore w i) := by
  unfold NewHistory5.decodeBefore History5.decodeBefore
  split <;> simp only [NewHistory5.decode_support_eq]

theorem regularReverse_support_eq (w : Nat → Wire) (i n : Nat) :
    wires (regularReverse w i n)=wires (Stack5.reverse5 w i n) := by
  induction n generalizing i with
  | zero => simp only [regularReverse,Stack5.reverse5]
  | succ n ih =>
    simp only [regularReverse,Stack5.reverse5,wires_append,ih,decodeBefore_support_eq,
      Finset.union_assoc]

theorem regularReverse_pool (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hi : i+n  ≤  512) :
    wires (regularReverse w i n)⊆(skywalkPoolWires w).toFinset := by
  rw [regularReverse_support_eq]
  exact (Stack5.support w hn i n hi).2.trans (History5.integerSites5_pool w)

theorem untick_pool (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i<512) :
    wires (NewHistory5.decodeBefore w i ++ W.ReverseCarry.compactReceiverTick w i)⊆
      (skywalkPoolWires w).toFinset := by
  have a := regularReverse_pool w hn i 1 (by omega)
  simpa only [regularReverse,wires_append,wires,Finset.empty_union] using a

theorem oneStep_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32  ≤  2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512)
    (t : State) (ht : Stage w x p i t.basis) (mE mD : List Bool) :
    run (NewHistory5.decodeBefore w i ++ W.ReverseCarry.compactReceiverTick w i) mD
      (run (W.repairedTick w i ++ NewHistory5.packAfter w i) mE t)=t := by
  rw [step_eq w hn x p i hp0 hx0 hpo hp hgap hx hc hi t mE [] ht]
  obtain ⟨raw,hraw,hbits⟩ := ht
  have dis := prefix_disjoint_layout w hn i i (Nat.le_refl i) hi
  have read : ∀q∈(W.compactSkywalkTickLayout w i).wires,t.basis q=raw.basis q := by
    intro q hq
    rw [hbits]
    exact run_preserves_outside _ _ _ q
      (fun he => Finset.disjoint_left.mp dis he (List.mem_toFinset.mpr hq))
  have loc := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hgap hx hc hi raw hraw
  have hh : t.basis (W.compactSkywalkTickLayout w i).history=false := by
    rw [read _ (by simp [SkywalkIntegerLayout.wires])]
    exact loc.2.2.2.2.1
  have clean : regValue (W.compactSkywalkTickLayout w i).carry t.basis=0 := by
    rw [regValue_congr _ t.basis raw.basis (by
      intro q hq
      exact read q (by simp only [SkywalkIntegerLayout.wires,List.mem_append,List.mem_cons]; tauto))]
    exact loc.2.2.2.2.2
  have rt := W.ReverseCarry.compactReceiverTick_roundtrip w i hi hn t []
    (mD.drop (measurementCount (NewHistory5.decodeBefore w i))) hh clean
  have dp : run (NewHistory5.decodeBefore w i)
      (mD.take (measurementCount (NewHistory5.decodeBefore w i)))
      (run (NewHistory5.packAfter w i) [] (run (W.compactSkywalkTick w i) [] t))=
        run (W.compactSkywalkTick w i) [] t := by
    cases due : History5.packDue i
    · simp only [NewHistory5.packAfter,NewHistory5.decodeBefore,due,Bool.false_eq_true,if_false,run]
    · have hd := History5.packDue_true i due
      have legal := tick_pack_legal w hn x p i hp0 hx0 hpo hp hgap hx hc hi t [] ⟨raw,hraw,hbits⟩ due
      simpa only [NewHistory5.packAfter,NewHistory5.decodeBefore,due,if_true,NewHistory5.encode,NewHistory5.decode]
        using ParityCodec5New.roundtripAt (History5.historyMap w (i-5))
          (History5.historyMap_injective w hn (i-5) (by omega)) _ [] _ legal
  rw [run_append,run_append]
  simp only [List.take_nil,List.drop_nil]
  rw [dp]
  exact rt

theorem regularReverse_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : History5.HistoryAbove w) (x p : Nat)
    (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hgap : p+2^32  ≤  2^256) (hx : x<p) (hc : x.Coprime p) (n : Nat) :
    ∀i,i+n  ≤  512 → ∀(s : State)(mE mD : List Bool), Stage w x p i s.basis →
      run (regularReverse w i n) mD (run (regularForward w i n) mE s)=s := by
  induction n with
  | zero => intro i hi s mE mD hs; simp only [regularForward,regularReverse,run]
  | succ n ih =>
    intro i hi s mE mD hs
    have next := (step_spec w hn hlo x p i hp0 hx0 hpo hp hgap hx hc (by omega) s
      (mE.take (measurementCount (W.repairedTick w i ++ NewHistory5.packAfter w i))) hs).2
    rw [regularReverse,run_append]
    conv in (run (regularForward w i (n+1)) mE s) => rw [regularForward,run_append]
    rw [ih (i+1) (by omega) _ _ _ next]
    exact oneStep_roundtrip w hn x p i hp0 hx0 hpo hp hgap hx hc (by omega) s hs _ _

theorem unpack_measurements (w : Nat → Wire) (i : Nat) :
    measurementCount (unpackFirst w i)=measurementCount (NewHistory5.decodeBefore w i) := by
  by_cases hi : i=5
  · subst i
    have due : History5.packDue 5=true := by decide
    simp only [unpackFirst,if_pos rfl,NewHistory5.decodeBefore,due,if_true,
      Nat.sub_self,NewHistory5.decode]
    exact (ParityCodec5New.first_countsAt _).2.2.2.trans (ParityCodec5New.countsAt _).2.2.2.symm
  · simp only [unpackFirst,if_neg hi]

theorem reverse_measurements (i n : Nat) :
    measurementCount (reverse i n)=measurementCount (regularReverse base i n) := by
  induction n generalizing i with
  | zero => simp only [reverse,regularReverse]
  | succ n ih =>
    simp only [reverse,regularReverse,measurementCount_append,
      (renameProgram_counts _ _).2,ih,unpack_measurements]

theorem unpack_support_eq (w : Nat → Wire) (i : Nat) :
    wires (unpackFirst w i)=wires (FirstNonzeroCodec.unpack9first w i) := by
  by_cases hi : i=5
  · subst i
    simp only [unpackFirst,FirstNonzeroCodec.unpack9first,if_true,
      ParityCodec5New.decodeAtFirst,FirstNonzeroCodec.decodeAtFirst,renameProgram_support]
    have h : wires ParityCodec5New.decodeFirst=wires FirstNonzeroCodec.decodeFirst := by decide +kernel
    exact congrArg (Finset.image (ParityCodec5New.label (History5.historyMap w 0))) h
  · simp only [unpackFirst,FirstNonzeroCodec.unpack9first,if_neg hi,StackOB5.unpack11_eq,
      decodeBefore_support_eq]

theorem reverse_support_eq (i n : Nat) :
    wires (reverse i n)=wires (StackOB5.reverse i n) := by
  induction n generalizing i with
  | zero => simp only [reverse,StackOB5.reverse]
  | succ n ih =>
    simp only [reverse,StackOB5.reverse,wires_append,renameProgram_support,ih,unpack_support_eq]

theorem reverse_pool (i n : Nat) (h1 : 1  ≤  i) (hi : i+n  ≤  512) :
    wires (reverse i n)⊆(skywalkPoolWires base).toFinset := by
  rw [reverse_support_eq]
  intro q hq
  have good := (StackOB5.support_gen i n h1 hi).2 q hq
  obtain ⟨j,rfl,hj⟩ := (StackOB5Base.integerSites_mem q).mp good
  exact List.mem_toFinset.mpr (StackOB5Base.base_pool j (by omega))

theorem first_stage_old (w : Nat → Wire) (x p : Nat) (s : State)
    (hs : Stage w x p 5 s.basis) : W.CompressedCompactStage5 w x p 5 s.basis := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  refine ⟨raw,hraw,?_⟩
  have eNew : NewHistory5.encodePrefix w 5=[] := by
    simp [NewHistory5.encodePrefix,NewHistory5.packAfter,History5.packDue]
  have eOld : History5.encodePrefix w 5=[] := by
    simp [History5.encodePrefix,History5.packAfter,History5.packDue]
  simpa only [eNew,eOld] using hbits

theorem first_decode_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32  ≤  2^256) (hx : x<p) (hc : x.Coprime p)
    (t u : State) (mE mD : List Bool) (hs : Stage w x p 5 t.basis)
    (hb : ∀q∈skywalkPoolWires w,u.basis q=
      (run (W.repairedTick w 5 ++ NewHistory5.packAfter w 5) mE t).basis q) :
    run (ParityCodec5New.decodeAtFirst (History5.historyMap w 0)) mD u=
      run (ParityCodec5New.decodeAt (History5.historyMap w 0)) mD u := by
  have old := first_stage_old w x p t hs
  have hr := FirstNonzeroCodec.w_first_tick_stage w hn x p hp0 hx0 hpo hp hgap hx hc t
    (mE.take (measurementCount (W.repairedTick w 5))) old
  generalize hraw : run (W.repairedTick w 5)
    (mE.take (measurementCount (W.repairedTick w 5))) t=raw at hr
  have legal := FirstNonzeroCodec.w_stage_first_legal w hn x p 6 hp0 hpo
    (by decide) (by decide) raw.basis hr
  have nz := FirstNonzeroCodec.w_first_nonzero w hn x p 6 hp0 hpo hx
    (by decide) (by decide) raw.basis hr
  have nz' : raw.basis (History5.historyMap w 0 0)=true ∨
      raw.basis (History5.historyMap w 0 1)=true := by
    simpa [History5.historyMap,History5.historyId,Bool.or_eq_true] using nz
  have due : History5.packDue 5=true := by decide
  apply ParityCodec5New.decodeAt_eq_on_pool _
    (History5.historyMap_injective w hn 0 (by decide)) raw u
    (mE.drop (measurementCount (W.repairedTick w 5))) mD legal nz'
  intro q hq
  have same := hb q (List.mem_toFinset.mp (FirstNonzeroCodec.first_ports_pool w hq))
  simpa only [run_append,NewHistory5.packAfter,due,if_true,Nat.sub_self,
    NewHistory5.encode,hraw] using same

theorem reverse_step_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32  ≤  2^256) (hx : x<p) (hc : x.Coprime p)
    (t u : State) (mE mD : List Bool) (hs : Stage w x p i t.basis)
    (hb : ∀q∈skywalkPoolWires w,u.basis q=
      (run (W.repairedTick w i ++ NewHistory5.packAfter w i) mE t).basis q) :
    run (unpackFirst w i ++ W.ReverseCarry.compactReceiverTick w i) mD u=
      run (NewHistory5.decodeBefore w i ++ W.ReverseCarry.compactReceiverTick w i) mD u := by
  by_cases hi : i=5
  · subst i
    have due : History5.packDue 5=true := by decide
    have he := first_decode_eq w hn x p hp0 hx0 hpo hp hgap hx hc t u mE
      (mD.take (measurementCount (NewHistory5.decodeBefore w 5))) hs hb
    rw [run_append,run_append,unpack_measurements]
    simpa only [unpackFirst,if_pos rfl,NewHistory5.decodeBefore,due,if_true,
      Nat.sub_self,NewHistory5.decode] using congrArg
        (run (W.ReverseCarry.compactReceiverTick w 5)
          (mD.drop (measurementCount (NewHistory5.decodeBefore w 5)))) he
  · simp only [unpackFirst,if_neg hi]

theorem reverse_gen (x : Nat) (hx0 : 0<x) (hx : x<p) (n : Nat) :
    ∀i,1  ≤  i → i+n  ≤  512 → ∀(t : State)(mE : List Bool)(v : State)(mD : List Bool),
    Stage base x p i t.basis →
    (∀q∈skywalkPoolWires base,v.basis q=(run (regularForward base i n) mE t).basis q) →
    run (reverse i n) mD (pullState (sig (i+n-1)) v)=
      pullState (sig (i-1)) (run (regularReverse base i n) mD v) ∧
    ∀q∈skywalkPoolWires base,(run (regularReverse base i n) mD v).basis q=t.basis q := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  induction n with
  | zero =>
    intro i _ _ t mE v mD _ hv
    refine ⟨?_,?_⟩
    · simp only [reverse,regularReverse,run,Nat.add_zero]
    · intro q hq
      simpa only [regularReverse,regularForward,run] using hv q hq
  | succ n ih =>
    intro i h1 hb t mE v mD ht hv
    have hi : i  ≤  511 := by omega
    have e1 : reverse i (n+1)=reverse (i+1) n ++ renameProgram (sig i)
        (unpackFirst base i ++ W.ReverseCarry.compactReceiverTick base i) := by rw [reverse]
    have e2 : regularReverse base i (n+1)=regularReverse base (i+1) n ++
        (NewHistory5.decodeBefore base i ++ W.ReverseCarry.compactReceiverTick base i) := by
      rw [regularReverse]
    have e3 : regularForward base i (n+1)=
        (W.repairedTick base i ++ NewHistory5.packAfter base i) ++ regularForward base (i+1) n := by
      rw [regularForward]
    rw [e3,run_append] at hv
    have ht' := (step_spec base base_pool_nodup StackOB5.historyAbove x p i hp0 hx0 hpo hp hgap hx cop
      (by omega) t (mE.take (measurementCount (W.repairedTick base i ++ NewHistory5.packAfter base i))) ht).2
    have cnt := reverse_measurements (i+1) n
    obtain ⟨r1,r2⟩ := ih (i+1) (by omega) (by omega) _ _ v
      (mD.take (measurementCount (regularReverse base (i+1) n))) ht' hv
    rw [show i+1-1=i by omega,show i+1+n-1=i+(n+1)-1 by omega] at r1
    have rt := oneStep_roundtrip base base_pool_nodup x p i hp0 hx0 hpo hp hgap hx cop
      (by omega) t ht
      (mE.take (measurementCount (W.repairedTick base i ++ NewHistory5.packAfter base i)))
      (mD.drop (measurementCount (regularReverse base (i+1) n)))
    have agree := StackOB5Base.pool_agree _ (untick_pool base base_pool_nodup i (by omega))
      (mD.drop (measurementCount (regularReverse base (i+1) n))) _ _ r2
    rw [rt] at agree
    have z := stage_zero x i (by omega) t.basis ht
    have hz1 : (run (NewHistory5.decodeBefore base i ++ W.ReverseCarry.compactReceiverTick base i)
        (mD.drop (measurementCount (regularReverse base (i+1) n)))
        (run (regularReverse base (i+1) n)
          (mD.take (measurementCount (regularReverse base (i+1) n))) v)).basis (base (1028+i))=false :=
      (agree _ (StackOB5Base.base_pool (1028+i) (by omega))).trans z.1
    have hz2 : 257  ≤  i → (run (NewHistory5.decodeBefore base i ++ W.ReverseCarry.compactReceiverTick base i)
        (mD.drop (measurementCount (regularReverse base (i+1) n)))
        (run (regularReverse base (i+1) n)
          (mD.take (measurementCount (regularReverse base (i+1) n))) v)).basis (base (2053-i))=false :=
      fun big => (agree _ (StackOB5Base.base_pool (2053-i) (by omega))).trans (z.2 big)
    have decoder := reverse_step_eq base base_pool_nodup x p i hp0 hx0 hpo hp hgap hx cop t
      (run (regularReverse base (i+1) n) (mD.take (measurementCount (regularReverse base (i+1) n))) v)
      (mE.take (measurementCount (W.repairedTick base i ++ NewHistory5.packAfter base i)))
      (mD.drop (measurementCount (regularReverse base (i+1) n))) ht r2
    rw [e1,e2,run_append,run_append,cnt,r1,OB5.run_rename i hi,decoder,
      ←pull_step i hi _ hz1 hz2]
    exact ⟨rfl,agree⟩

theorem reverse_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE : List Bool)
    (hs : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis)
    (v : State) (hv : ∀q∈skywalkPoolWires base,
      v.basis q=(run (regularForward base 1 511) mE s).basis q) (mD : List Bool) :
    run (reverse 1 511) mD (pullState (sig 511) v)=run (regularReverse base 1 511) mD v := by
  have h := (reverse_gen x hx0 hx 511 1 (by omega) (by omega) s mE v mD
    (stage_one base x p s hs) hv).1
  have e : ∀u : State,pullState (sig (1-1)) u=u := by
    intro u
    apply State.extensionality
    · rfl
    · funext q
      show u.basis (sig 0 q)=u.basis q
      rw [sig_zero]
  rw [e,show 1+511-1=511 by rfl] at h
  exact h

theorem stage510_bits_new (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State)
    (hs : Stage base x p 510 s.basis) :
    ∃G S : Bool,∃u∈[0,1],∀q∈sites510,s.basis q=pre510 G S u q := by
  obtain ⟨t,ht,read⟩ := old_stage_local base base_pool_nodup x p 510 (by decide) s hs
  obtain ⟨G,S,u,hu,bits⟩ := ECDSAAdd.Entrant.stage510_bits x hx0 hx t ht
  refine ⟨G,S,u,hu,?_⟩
  intro q hq
  exact (read q (W.compactSkywalkTick_support base 510 (by decide) base_pool_nodup
    (sites510_tick q hq))).trans (bits q hq)

theorem block510_eq_new (x : Nat) (hx0 : 0<x) (hx : x<p) (t : State)
    (ht : Stage base x p 510 t.basis) (mE mD : List Bool) :
    run (NewHistory5.decodeBefore base 510 ++ tick510R) mD
        (run (W.repairedTick base 510 ++ NewHistory5.packAfter base 510) mE t)=
      run (NewHistory5.decodeBefore base 510 ++ W.ReverseCarry.compactReceiverTick base 510) mD
        (run (W.repairedTick base 510 ++ NewHistory5.packAfter base 510) mE t) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  obtain ⟨G,S,u,hu,bits⟩ := stage510_bits_new x hx0 hx t ht
  have due : History5.packDue 510=true := by decide
  have rep : W.repairedTick base 510=W.compactSkywalkTick base 510 := by
    rw [tick510ExF_explicit,tick510ExF_compact]
  set k := measurementCount (W.repairedTick base 510) with hk
  set d := measurementCount (NewHistory5.decodeBefore base 510) with hd
  set a := run (W.repairedTick base 510) (mE.take k) t with ha
  have legal := tick_pack_legal base base_pool_nodup x p 510 hp0 hx0 hpo hp hgap hx cop
    (by omega) t (mE.take k) ht due
  rw [←rep] at legal
  have dp : run (NewHistory5.decodeBefore base 510) (mD.take d)
      (run (NewHistory5.packAfter base 510) (mE.drop k) a)=a := by
    simpa only [NewHistory5.packAfter,NewHistory5.decodeBefore,due,if_true,NewHistory5.encode,
      NewHistory5.decode] using ParityCodec5New.roundtripAt (History5.historyMap base (510-5))
        (History5.historyMap_injective base base_pool_nodup (510-5) (by omega)) a
        (mE.drop k) (mD.take d) legal
  have abits : ∀q∈sites510,a.basis q=(run tick510ExF [] ⟨false,pre510 G S u⟩).basis q := by
    intro q hq
    rw [ha,tick510ExF_explicit,
      site_run tick510ExF sites510 (le_of_eq tick510ExF_wires) t ⟨false,pre510 G S u⟩ bits
        (mE.take k) q hq]
    exact congrFun (run_basis_records tick510ExF _ _ (mE.take k) [] rfl) q
  rw [run_append (W.repairedTick base 510),run_append (NewHistory5.decodeBefore base 510) tick510R,
    run_append (NewHistory5.decodeBefore base 510),←hk,←hd,←ha,dp,tick510ExR_explicit]
  symm
  exact forced_eqN tick510ExR tick510R sites510 _ 2 recs2 take2_mem tick510ExR_wires tick510R_wires
    (le_of_eq tick510_counts.2.2.2.2.2.1) (le_of_eq tick510_counts.2.2.2.2.2.2.2)
    (fun c hc => conc510R G S u hu c hc) a abits (mD.drop d)

theorem stackReverse510_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (u : State) (hu : ∀q∈skywalkPoolWires base,
      u.basis q=(run (regularForward base 1 510) mE s1).basis q) (mD : List Bool) :
    run stackReverse510 mD (pullState (sig 510) u)=
      run (reverse 1 510) mD (pullState (sig 510) u) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  have stage : Stage base x p 510
      (run (regularForward base 1 509)
        (mE.take (measurementCount (regularForward base 1 509))) s1).basis :=
    ((regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 509
      hp0 hx0 hpo hp hgap hx cop (by omega)) s1 _ (stage_one base x p s1 first)).2
  have fwd : run (regularForward base 1 510) mE s1=
      run (W.repairedTick base 510 ++ NewHistory5.packAfter base 510)
        (mE.drop (measurementCount (regularForward base 1 509)))
        (run (regularForward base 1 509)
          (mE.take (measurementCount (regularForward base 1 509))) s1) := by
    rw [regularForward_snoc base 1 509,show (1:Nat)+509=510 by rfl,run_append]
  rw [fwd] at hu
  generalize run (regularForward base 1 509)
    (mE.take (measurementCount (regularForward base 1 509))) s1=a at stage hu
  have c := tick510_counts
  rw [←tick510ExR_explicit] at c
  have mc : measurementCount (NewHistory5.decodeBefore base 510 ++ tick510R)=
      measurementCount (NewHistory5.decodeBefore base 510 ++ W.ReverseCarry.compactReceiverTick base 510) := by
    rw [measurementCount_append,measurementCount_append,c.2.2.2.2.2.1,c.2.2.2.2.2.2.2]
  have rn := (renameProgram_counts (sig 510) (NewHistory5.decodeBefore base 510 ++ tick510R)).2
  have ro := (renameProgram_counts (sig 510)
    (NewHistory5.decodeBefore base 510 ++ W.ReverseCarry.compactReceiverTick base 510)).2
  have pool : ∀q∈sites510,q∈(skywalkPoolWires base).toFinset :=
    fun q hq => List.mem_toFinset.mpr (sites510_pool q hq)
  have hB : wires (NewHistory5.decodeBefore base 510 ++ tick510R)⊆(skywalkPoolWires base).toFinset := by
    have dec := (History5.pack_support5 base 510 (by omega)).2.trans (History5.integerSites5_pool base)
    rw [←decodeBefore_support_eq] at dec
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,fun q hq => pool q (List.mem_toFinset.mp (tick510R_wires hq))⟩
  have inner (r : List Bool) :
      run (NewHistory5.decodeBefore base 510 ++ tick510R) r u=
        run (NewHistory5.decodeBefore base 510 ++ W.ReverseCarry.compactReceiverTick base 510) r u :=
    Stack5.local_replace _ _ _ hB (untick_pool base base_pool_nodup 510 (by omega)) u _ r r
      (fun q hq => hu q (List.mem_toFinset.mp hq)) (block510_eq_new x hx0 hx a stage _ r)
  rw [stackReverse510,reverse_split510,run_append,run_append,rn,ro,mc,
    OB5.run_rename 510 (by omega),OB5.run_rename 510 (by omega),inner]

theorem regular_pack511 : NewHistory5.packAfter base 511=[] := by decide +kernel

theorem stackReverseT_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (t5 : State) (agree : ∀q∈skywalkPoolWires base,
      t5.basis q=(run (regularForward base 1 511) mE s1).basis q) (mD : List Bool) :
    run stackReverseT mD (pullState (sig 511) t5)=
      run (reverse 1 511) (false::mD) (pullState (sig 511) t5) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  have aStage : Stage base x p 511
      (run (regularForward base 1 510)
        (mE.take (measurementCount (regularForward base 1 510))) s1).basis :=
    ((regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 510
      hp0 hx0 hpo hp hgap hx cop (by omega)) s1 _ (stage_one base x p s1 first)).2
  have whole : run (regularForward base 1 510)
      (mE.take (measurementCount (regularForward base 1 510))) s1=
        run (regularForward base 1 510) mE s1 := run_take _ mE s1
  have last : run (regularForward base 1 511) mE s1=
      run (W.repairedTick base 511) (mE.drop (measurementCount (regularForward base 1 510)))
        (run (regularForward base 1 510)
          (mE.take (measurementCount (regularForward base 1 510))) s1) := by
    rw [regularForward_snoc base 1 510,show (1:Nat)+510=511 by rfl,regular_pack511,List.append_nil,run_append]
  rw [last] at agree
  generalize run (regularForward base 1 510)
    (mE.take (measurementCount (regularForward base 1 510))) s1=a at aStage whole agree
  obtain ⟨G,bits⟩ := stage511_bits x hx0 hx a aStage
  rw [repaired511_forced G a bits] at agree
  have post : ∀q∈tickSites,t5.basis q=postBits G q := by
    intro q hq
    rw [agree q (tickSites_pool q hq)]
    exact tickF_post G a bits q hq
  have uAgree : ∀q∈skywalkPoolWires base,(run tickR [] t5).basis q=a.basis q := by
    intro q hq
    by_cases ht : q∈tickSites
    · rw [site_run tickR tickSites tickR_wires t5 ⟨false,postBits G⟩ post [] q ht,tickR_pre G q ht]
      exact (bits q ht).symm
    · have hr : q∉wires tickR := fun h => ht (List.mem_toFinset.mp (tickR_wires h))
      have hf : q∉wires tickF := fun h => ht (List.mem_toFinset.mp (tickF_wires h))
      rw [run_preserves_outside tickR [] t5 q hr,agree q hq,run_preserves_outside tickF [] a q hf]
  have z := stage_zero x 511 (by omega) a.basis aStage
  have move : pullState (sig 511) (run tickR [] t5)=pullState (sig 510) (run tickR [] t5) :=
    (OB5.pull_step 511 (by omega) _
      ((uAgree _ (StackOB5Base.base_pool _ (by omega))).trans z.1)
      (fun big => (uAgree _ (StackOB5Base.base_pool _ (by omega))).trans (z.2 big))).symm
  have cn : measurementCount (renameProgram (sig 511) tickR)=0 :=
    (renameProgram_counts (sig 511) tickR).2.trans tickR_counts.2
  have co : measurementCount (renameProgram (sig 511) (W.ReverseCarry.compactReceiverTick base 511))=1 := by
    rw [(renameProgram_counts (sig 511) (W.ReverseCarry.compactReceiverTick base 511)).2,
      receiver511_explicit]
    exact tickExR_counts.2
  rw [stackReverseT,reverse_split511,run_append,run_append,cn,co]
  simp only [List.take_zero,List.drop_zero,List.take_succ_cons,List.drop_succ_cons]
  rw [OB5.run_rename 511 (by omega),OB5.run_rename 511 (by omega),
    receiver511_forced G t5 post,tickR_run,move]
  exact stackReverse510_run x hx0 hx s1 mE first _
    (fun q hq => (uAgree q hq).trans (congrArg (fun st : State => st.basis q) whole)) mD

theorem stackReverseT_support_eq : wires stackReverseT=wires ECDSAAdd.Entrant.stackReverseT := by
  simp only [stackReverseT,ECDSAAdd.Entrant.stackReverseT,stackReverse510,
    ECDSAAdd.Entrant.stackReverse510,wires_append,renameProgram_support,reverse_support_eq,
    decodeBefore_support_eq]

theorem stackReverseT_subset : wires stackReverseT⊆wires (StackOB5.reverse 1 511) := by
  rw [stackReverseT_support_eq]
  exact ECDSAAdd.Entrant.stackReverseT_subset

theorem stackReverseT_pool : wires stackReverseT⊆(skywalkPoolWires base).toFinset := by
  have h := reverse_pool 1 511 (by omega) (by omega)
  rw [reverse_support_eq] at h
  exact stackReverseT_subset.trans h

theorem stackReverseT_outside (s : State) (m : List Bool) (q : Wire)
    (hq : q∉skywalkPoolWires base) : (run stackReverseT m s).basis q=s.basis q :=
  run_preserves_outside stackReverseT m s q
    (fun used => hq (List.mem_toFinset.mp (stackReverseT_pool used)))

theorem decodeBefore_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i<512) : GatePhysical (NewHistory5.decodeBefore w i) := by
  cases due : History5.packDue i
  · simp [NewHistory5.decodeBefore,due,GatePhysical]
  · have hd := History5.packDue_true i due
    simp only [NewHistory5.decodeBefore,due,if_true,NewHistory5.decode]
    exact (ParityCodec5New.physicalAt _ (History5.historyMap_injective w hn (i-5) (by omega))).2

theorem unpackFirst_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i<512) : GatePhysical (unpackFirst w i) := by
  by_cases h5 : i=5
  · simp only [unpackFirst,if_pos h5]
    exact (ParityCodec5New.first_mapped_physical _ (History5.historyMap_injective w hn 0 (by decide))).2
  · simp only [unpackFirst,if_neg h5]
    exact decodeBefore_physical w hn i hi

theorem reverse_physical (i n : Nat) (hi : i+n ≤ 512) : GatePhysical (reverse i n) := by
  induction n generalizing i with
  | zero => simp [reverse,GatePhysical]
  | succ n ih =>
    rw [reverse,gatePhysical_append]
    exact ⟨ih (i+1) (by omega),gatePhysical_rename _ (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr ⟨unpackFirst_physical base base_pool_nodup i (by omega),
        W.ReverseCarry.compactReceiverTick_physical base i (by omega) base_pool_nodup⟩)⟩

theorem stackReverseT_physical : GatePhysical stackReverseT := by
  have tr : GatePhysical tickR := by
    simp [tickR,base,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  have dk := decodeBefore_physical base base_pool_nodup 510 (by omega)
  have blk := gatePhysical_rename _ (sig_injective 510 (by omega)) _
    ((gatePhysical_append _ _).mpr ⟨dk,tick510_physical.2⟩)
  rw [stackReverseT,stackReverse510]
  exact (gatePhysical_append _ _).mpr ⟨gatePhysical_rename _ (sig_injective 511 (by omega)) _ tr,
    (gatePhysical_append _ _).mpr ⟨blk,reverse_physical 1 509 (by omega)⟩⟩

/-- Independent forward and inverse record lists restore the complete State. -/
theorem stack_roundtrip
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis) :
    run stackReverseT mD (run stackForwardT mE s1)=s1 := by
  have fwd : run stackForwardT mE s1=
      pullState (sig 511) (run (regularForward base 1 511) mE s1) :=
    (stackForwardT_run hn hlo x hx0 hx s1 mE first).trans (forward_run x hx0 hx s1 mE first)
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32 ≤ 2^256 := by norm_num [p]
  exact (congrArg (run stackReverseT mD) fwd).trans
    ((stackReverseT_run x hx0 hx s1 mE first
      (run (regularForward base 1 511) mE s1) (fun _ _ => rfl) mD).trans
      ((reverse_run x hx0 hx s1 mE first
        (run (regularForward base 1 511) mE s1) (fun _ _ => rfl) (false::mD)).trans
        (regularReverse_roundtrip base base_pool_nodup hlo x p hp0 hx0 hpo hp hgap hx cop
          511 1 (by omega) s1 mE (false::mD) (stage_one base x p s1 first))))

end ECDSAAdd.Entrant.NewStackOB5
