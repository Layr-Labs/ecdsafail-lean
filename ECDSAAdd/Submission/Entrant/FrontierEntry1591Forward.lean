import ECDSAAdd.Submission.Entrant.NewEncodedFrame
import ECDSAAdd.Submission.Entrant.ParityCodec5New
import ECDSAAdd.Math.SkywalkTerminalLastControls

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.NewHistory5
open Arithmetic

 theorem pack_support_eq (w : Nat → Wire) (i : Nat) :
    wires (packAfter w i)=wires (History5.packAfter w i) := by
  unfold packAfter History5.packAfter
  split <;> simp only [encode_support_eq]

 theorem prefix_support_eq (w : Nat → Wire) (i : Nat) :
    wires (encodePrefix w i)=wires (History5.encodePrefix w i) := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [encodePrefix,History5.encodePrefix,wires_append,ih,pack_support_eq]

 theorem prefix_next_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (hb : n<512) (due : History5.packDue n=true) :
    Disjoint (wires (encodePrefix w n)) (wires (encode w (n-5))) := by
  rw [prefix_support_eq,encode_support_eq]
  exact History5.prefix_next_disjoint w hn n hb due

 theorem prefix_next_legal (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (hb : n<512) (due : History5.packDue n=true) (s : State) (m : List Bool)
    (legal : MeasuredCodec5.legalAt (History5.historyMap w (n-5)) s.basis) :
    MeasuredCodec5.legalAt (History5.historyMap w (n-5)) (run (encodePrefix w n) m s).basis := by
  have dis := prefix_next_disjoint w hn n hb due
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  have same (q : Fin 10) : (run (encodePrefix w n) m s).basis (History5.historyMap w (n-5) q)=
      s.basis (History5.historyMap w (n-5) q) :=
    run_preserves_outside _ _ _ _ (fun used => Finset.disjoint_left.mp dis used
      (ParityCodec5New.site_mem _ q))
  intro i
  rw [same,same]
  exact (MeasuredCodec5.legalAt_iff _ _).mp legal i

 theorem encodePrefix_zero_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (hb : n        ≤        512) (s : State) : (run (encodePrefix w n) [] s).phase=s.phase := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [encodePrefix,run_append]
    simp only [List.take_nil,List.drop_nil]
    cases due : History5.packDue n
    · simp only [packAfter,due,Bool.false_eq_true,if_false,run]
      exact ih (by omega)
    · have hd := History5.packDue_true n due
      simp only [packAfter,due,if_true,encode]
      exact (ParityCodec5New.encodeAt_zero_phase _
        (History5.historyMap_injective w hn (n-5) (by omega)) _).trans (ih (by omega))

theorem encodePrefix_index (w : Nat → Wire) (n : Nat) : encodePrefix w (5*n+1)=allEncode w n := by
  induction n with
  | zero => simp [encodePrefix,packAfter,History5.packDue,allEncode]
  | succ n ih =>
    have index : 5*(n+1)+1=5*n+1+1+1+1+1+1 := by omega
    rw [index,encodePrefix,encodePrefix,encodePrefix,encodePrefix,encodePrefix,ih]
    have d1 : History5.packDue (5*n+1)=false := by simp [History5.packDue,Nat.add_mod]
    have d2 : History5.packDue (5*n+1+1)=false := by simp [History5.packDue,Nat.add_mod]
    have d3 : History5.packDue (5*n+1+1+1)=false := by simp [History5.packDue,Nat.add_mod]
    have d4 : History5.packDue (5*n+1+1+1+1)=false := by simp [History5.packDue,Nat.add_mod]
    have d5 : History5.packDue (5*n+1+1+1+1+1)=true := by simp [History5.packDue,Nat.add_mod]
    simp only [packAfter,d1,d2,d3,d4,d5,Bool.false_eq_true,if_false,if_true,List.append_nil]
    rw [show 5*n+1+1+1+1+1-5=5*n by omega]
    rfl

 theorem encodePrefix_512 (w : Nat → Wire) : encodePrefix w 512=allEncode w 102 := by
  rw [show (512:Nat)=511+1 from rfl,encodePrefix]
  rw [show (511:Nat)=5*102+1 from rfl,encodePrefix_index]
  have h : History5.packDue 511=false := by decide
  simp only [packAfter,h,Bool.false_eq_true,if_false,List.append_nil]

end ECDSAAdd.Entrant.NewHistory5

namespace ECDSAAdd.Entrant.NewStackOB5
open Arithmetic MappedCompressed Secp256k1 OB5

abbrev Stage := NewHistory5.CompressedCompactStage5

def packFirst (w : Nat → Wire) (i : Nat) : Program :=
  if i=5 then ParityCodec5New.encodeAtFirst (History5.historyMap w 0)
  else NewHistory5.packAfter w i

def regularForward (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => (W.repairedTick w i++NewHistory5.packAfter w i)++regularForward w (i+1) n

def compactForward (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => (W.compactSkywalkTick w i++NewHistory5.packAfter w i)++compactForward w (i+1) n

def forward (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (sig i) (W.repairedTick base i++packFirst base i)++forward (i+1) n

 theorem prefix_disjoint_layout (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n i : Nat) (hni : n        ≤        i) (hi : i<512) :
    Disjoint (wires (NewHistory5.encodePrefix w n)) (W.compactSkywalkTickLayout w i).wires.toFinset := by
  rw [NewHistory5.prefix_support_eq]
  exact Stack5.prefix_disjoint_layout w hn n i hni hi

 theorem prefix_disjoint_tick (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n i : Nat) (hni : n        ≤        i) (hi : i<512) :
    Disjoint (wires (NewHistory5.encodePrefix w n)) (wires (W.compactSkywalkTick w i)) :=
  Finset.disjoint_left.mpr (fun _ he ht => Finset.disjoint_left.mp
    (prefix_disjoint_layout w hn n i hni hi) he (W.compactSkywalkTick_support w i hi hn ht))

 theorem old_stage_local (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hi : i<512) (s : State) (hs : Stage w x p i s.basis) :
    ∃t : State, W.CompressedCompactStage5 w x p i t.basis ∧
      ∀q∈(W.compactSkywalkTickLayout w i).wires.toFinset,s.basis q=t.basis q := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  refine ⟨run (History5.encodePrefix w i) [] raw,⟨raw,hraw,rfl⟩,?_⟩
  intro q hq
  rw [hbits]
  have dn := prefix_disjoint_layout w hn i i (le_refl _) hi
  have oldDis := Stack5.prefix_disjoint_layout w hn i i (le_refl _) hi
  exact (run_preserves_outside _ _ _ q (fun h=>Finset.disjoint_left.mp dn h hq)).trans
    (run_preserves_outside _ _ _ q (fun h=>Finset.disjoint_left.mp oldDis h hq)).symm

 theorem repaired_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512)
    (s : State) (m n : List Bool) (hs : Stage w x p i s.basis) :
    run (W.repairedTick w i) m s=run (W.compactSkywalkTick w i) n s := by
  obtain ⟨t,ht,read⟩ := old_stage_local w hn x p i hi s hs
  exact Stack5.local_replace _ _ _ (W.repairedTick_support w i hi hn)
    (W.compactSkywalkTick_support w i hi hn) s t m n read
    (Stack5.repaired_eq5 w hn x p i hp0 hx0 hpo hp hgap hx hc hi t m n ht)

 theorem stage_one (w : Nat → Wire) (x p : Nat) (s : State)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    Stage w x p 1 s.basis := by
  refine ⟨s,hs,?_⟩
  simp [NewHistory5.encodePrefix,NewHistory5.packAfter,History5.packDue,run]

theorem compact_step_spec (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (_hlo : History5.HistoryAbove w)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (hq : p+2^32         ≤         2^256) (hx : x < p) (hc : x.Coprime p) (hi : i < 512) :
    Triple (Stage w x p i)
      (W.compactSkywalkTick w i++NewHistory5.packAfter w i) (Stage w x p (i+1)) := by
  intro s m hs
  obtain ⟨raw,hraw,hbits⟩ := hs
  let tick := W.compactSkywalkTick w i
  let mt := m.take (measurementCount tick)
  let me := m.drop (measurementCount tick)
  let actual := run tick mt s
  let next := run tick [] raw
  have step := W.compactSkywalkStageStep w hn x p i hp0 hx0 hpo hp hq hx hc hi
  have hnxt := step raw [] hraw
  have hmt := step raw mt hraw
  have hd := prefix_disjoint_tick w hn i i (Nat.le_refl i) hi
  have read : ∀q∈wires tick,s.basis q=raw.basis q := by
    intro q hq
    rw [hbits]
    exact run_preserves_outside _ _ _ q (fun he => Finset.disjoint_left.mp hd he hq)
  have localStep := run_local_increment tick s raw mt read
  have phase : actual.phase=s.phase := by
    have hh := localStep.1
    rw [hmt.1] at hh
    have neutral : (actual.phase ^^ s.phase)=false := by
      simpa only [Bool.xor_self] using hh
    cases ha : actual.phase <;> cases hb : s.phase <;> simp_all
  have commute := run_disjoint_commute (NewHistory5.encodePrefix w i) tick hd [] [] raw
  have same := run_basis_records tick s (run (NewHistory5.encodePrefix w i) [] raw) mt [] hbits
  have bits : actual.basis=(run (NewHistory5.encodePrefix w i) [] next).basis :=
    same.trans (congrArg State.basis commute.symm)
  have packPhase : (run (NewHistory5.packAfter w i) me actual).phase=actual.phase := by
    cases due : History5.packDue i
    · simp only [NewHistory5.packAfter,due,Bool.false_eq_true,if_false,run]
    · have hd := History5.packDue_true i due
      have nextLegal := W.stage_group_legal w hn x p (i+1) (i-5) hp0 hpo (by omega) (by omega) next.basis hnxt.2
      have encLegal := NewHistory5.prefix_next_legal w hn i hi due next [] nextLegal
      have actualLegal : MeasuredCodec5.legalAt (History5.historyMap w (i-5)) actual.basis := by
        rw [bits]
        exact encLegal
      simpa only [NewHistory5.packAfter,due,if_true,NewHistory5.encode] using
        ParityCodec5New.encodeAt_phase _ (History5.historyMap_injective w hn (i-5) (by omega)) actual me actualLegal
  have packBits := run_basis_records (NewHistory5.packAfter w i) actual
    (run (NewHistory5.encodePrefix w i) [] next) me [] bits
  have nextBits : (run (NewHistory5.packAfter w i) me actual).basis=
      (run (NewHistory5.encodePrefix w (i+1)) [] next).basis := by
    rw [NewHistory5.encodePrefix,run_append]
    simp only [List.take_nil,List.drop_nil]
    exact packBits
  rw [run_append]
  exact ⟨packPhase.trans phase,⟨next,hnxt.2,nextBits⟩⟩

 theorem tick_pack_legal (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512)
    (s : State) (m : List Bool) (hs : Stage w x p i s.basis) (due : History5.packDue i=true) :
    MeasuredCodec5.legalAt (History5.historyMap w (i-5)) (run (W.compactSkywalkTick w i) m s).basis := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  let next := run (W.compactSkywalkTick w i) [] raw
  have ns := W.compactSkywalkStageStep w hn x p i hp0 hx0 hpo hp hgap hx hc hi raw [] hraw
  have dis := prefix_disjoint_tick w hn i i (le_refl _) hi
  have commute := run_disjoint_commute (NewHistory5.encodePrefix w i) (W.compactSkywalkTick w i) dis [] [] raw
  have same := run_basis_records (W.compactSkywalkTick w i) s (run (NewHistory5.encodePrefix w i) [] raw) m [] hbits
  have bits : (run (W.compactSkywalkTick w i) m s).basis=(run (NewHistory5.encodePrefix w i) [] next).basis :=
    same.trans (congrArg State.basis commute.symm)
  have hd := History5.packDue_true i due
  have legal := W.stage_group_legal w hn x p (i+1) (i-5) hp0 hpo (by omega) (by omega) next.basis ns.2
  rw [bits]
  exact NewHistory5.prefix_next_legal w hn i hi due next [] legal

 theorem step_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512)
    (s : State) (m n : List Bool) (hs : Stage w x p i s.basis) :
    run (W.repairedTick w i++NewHistory5.packAfter w i) m s=
      run (W.compactSkywalkTick w i++NewHistory5.packAfter w i) n s := by
  rw [run_append,run_append]
  rw [repaired_eq w hn x p i hp0 hx0 hpo hp hgap hx hc hi s
    (m.take (measurementCount (W.repairedTick w i)))
    (n.take (measurementCount (W.compactSkywalkTick w i))) hs]
  cases due : History5.packDue i
  · simp only [NewHistory5.packAfter,due,Bool.false_eq_true,if_false,run]
  · have hd := History5.packDue_true i due
    have legal := tick_pack_legal w hn x p i hp0 hx0 hpo hp hgap hx hc hi s
      (n.take (measurementCount (W.compactSkywalkTick w i))) hs due
    simp only [NewHistory5.packAfter,due,if_true,NewHistory5.encode]
    exact ParityCodec5New.encodeAt_independent _ (History5.historyMap_injective w hn (i-5) (by omega)) _
      (m.drop (measurementCount (W.repairedTick w i)))
      (n.drop (measurementCount (W.compactSkywalkTick w i))) legal

 theorem step_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (hlo : History5.HistoryAbove w)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512) :
    Triple (Stage w x p i) (W.repairedTick w i++NewHistory5.packAfter w i) (Stage w x p (i+1)) := by
  intro s m hs
  rw [step_eq w hn x p i hp0 hx0 hpo hp hgap hx hc hi s m [] hs]
  exact compact_step_spec w hn hlo x p i hp0 hx0 hpo hp hgap hx hc hi s [] hs

 theorem regularForward_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (hlo : History5.HistoryAbove w)
    (x p i n : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p) (hi : i+n        ≤        512) :
    Triple (Stage w x p i) (regularForward w i n) (Stage w x p (i+n)) := by
  induction n generalizing i with
  | zero =>
    rw [regularForward,Nat.add_zero]
    intro s m hs
    exact ⟨rfl,hs⟩
  | succ n ih =>
    have first := step_spec w hn hlo x p i hp0 hx0 hpo hp hgap hx hc (by omega)
    have rest := ih (i+1) (by omega)
    have idx : i+(n+1)=(i+1)+n := by omega
    rw [regularForward,idx]
    exact first.seq rest

 theorem prefix_keep (i : Nat) (hi : i        ≤        512) (raw : State) (l : Nat) (hl : 1027+i        ≤        l) :
    (run (NewHistory5.encodePrefix base i) [] raw).basis (base l)=raw.basis (base l) := by
  apply run_preserves_outside
  intro hm
  rw [NewHistory5.prefix_support_eq] at hm
  obtain ⟨j,hj,hr⟩ := StackOB5Base.encodePrefix_mem i hi _ hm
  have := base_injective hj
  omega

theorem stage_zero (x i : Nat) (hi : i < 512) (b : BasisState)
    (h : Stage base x p i b) :
    b (base (1028+i)) = false ∧ (257         ≤         i → b (base (2053-i)) = false) := by
  obtain ⟨raw, hraw, rfl⟩ := h
  have virt : ∀ l, 1028         ≤         l → W.compactSkywalkStageVirtual base i raw.basis (base l) =
      raw.basis (base l) := by
    intro l hl
    have ex := W.compactSkywalkStage_expanded base i (by omega)
    apply W.compactSkywalkStage_virtual_outside
    · intro hm
      have hm' : base l ∈ (W.compactSkywalkSignPoolA base i).expanded :=
        List.mem_append_right _ hm
      rw [ex.1] at hm'
      obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
      have := base_injective he
      simp only [List.mem_range'_1] at hj
      omega
    · intro hm
      have hm' : base l ∈ (W.compactSkywalkSignPoolB base i).expanded :=
        List.mem_append_right _ hm
      rw [ex.2] at hm'
      obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
      have := base_injective he
      simp only [List.mem_range'_1] at hj
      omega
  have stage := hraw.1
  have fut := (stage.2.2.2.2.1 i (Nat.le_refl i) hi).2
  have carry := (regValue_zero _ _).mp stage.2.2.2.2.2.1
  constructor
  · rw [prefix_keep i (by omega) raw (1028+i) (by omega), ← virt (1028+i) (by omega)]
    exact fut
  · intro big
    rw [prefix_keep i (by omega) raw (2053-i) (by omega), ← virt (2053-i) (by omega)]
    apply carry
    exact List.mem_map.mpr ⟨2053-i, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩


 theorem forward_step_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p)
    (s : State) (m : List Bool) (hs : Stage w x p i s.basis) :
    run (W.repairedTick w i++packFirst w i) m s=
      run (W.repairedTick w i++NewHistory5.packAfter w i) m s := by
  by_cases hi:i=5
  · subst i
    have rawStage : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 5 s.basis := by
      obtain ⟨raw,hr,hbits⟩ := hs
      have empty : NewHistory5.encodePrefix w 5=[] := by
        simp [NewHistory5.encodePrefix,NewHistory5.packAfter,History5.packDue]
      have bits : s.basis=raw.basis := by simpa only [empty,run] using hbits
      rw [bits]
      exact hr
    let mt := m.take (measurementCount (W.repairedTick w 5))
    have eq := repaired_eq w hn x p 5 hp0 hx0 hpo hp hgap hx hc (by decide) s mt mt hs
    have next := W.compactSkywalkStageStep w hn x p 5 hp0 hx0 hpo hp hgap hx hc (by decide) s mt rawStage
    have actual : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 6
        (run (W.repairedTick w 5) mt s).basis := by rw [eq]; exact next.2
    have legal := W.stage_group_legal w hn x p 6 0 hp0 hpo (by omega) (by omega)
      (run (W.repairedTick w 5) mt s).basis actual
    have nz := FirstNonzeroCodec.w_first_nonzero w hn x p 6 hp0 hpo hx (by decide) (by decide)
      (run (W.repairedTick w 5) mt s).basis actual
    have nz' : (run (W.repairedTick w 5) mt s).basis (History5.historyMap w 0 0)=true ∨
        (run (W.repairedTick w 5) mt s).basis (History5.historyMap w 0 1)=true := by
      simpa [History5.historyMap,History5.historyId,Bool.or_eq_true] using nz
    simp only [packFirst,if_pos rfl,NewHistory5.packAfter,show History5.packDue 5=true from rfl,
      if_true,Nat.sub_self,NewHistory5.encode,run_append]
    exact ParityCodec5New.encodeAt_eq _ (History5.historyMap_injective w hn 0 (by decide)) _ _ legal nz'
  · rw [packFirst,if_neg hi]

 theorem packFirst_records (w : Nat → Wire) (i : Nat) :
    measurementCount (packFirst w i)=measurementCount (NewHistory5.packAfter w i) := by
  by_cases hi:i=5
  · subst i
    simp only [packFirst,if_pos rfl,NewHistory5.packAfter,show History5.packDue 5=true from rfl,
      if_true,Nat.sub_self,NewHistory5.encode]
    exact (ParityCodec5New.first_countsAt _).2.2.1.trans (ParityCodec5New.countsAt _).2.1.symm
  · rw [packFirst,if_neg hi]

 theorem forward_gen (x : Nat) (hx0 : 0<x) (hx : x<p) (n : Nat) :
    ∀i,1        ≤        i → i+n        ≤        512 → ∀(t : State)(m : List Bool), Stage base x p i t.basis →
      run (forward i n) m (pullState (sig (i-1)) t)=
        pullState (sig (i+n-1)) (run (regularForward base i n) m t) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32        ≤        2^256 := by norm_num [p]
  induction n with
  | zero => intro i _ _ t m _; simp only [forward,regularForward,run,Nat.add_zero]
  | succ n ih =>
    intro i h1 hb t m ht
    have hi : i        ≤        511 := by omega
    have z := stage_zero x i (by omega) t.basis ht
    rw [pull_step i hi t z.1 z.2]
    have cnt := (renameProgram_counts (sig i) (W.repairedTick base i++packFirst base i)).2
    have records : measurementCount (W.repairedTick base i++packFirst base i)=
        measurementCount (W.repairedTick base i++NewHistory5.packAfter base i) := by
      rw [measurementCount_append,measurementCount_append,packFirst_records]
    rw [forward,regularForward,run_append,run_append,cnt,records,OB5.run_rename i hi,
      forward_step_eq base base_pool_nodup x p i hp0 hx0 hpo hp hgap hx cop _ _ ht]
    have ht' := (step_spec base base_pool_nodup StackOB5.historyAbove x p i hp0 hx0 hpo hp hgap hx
      cop (by omega) t (m.take (measurementCount (W.repairedTick base i++NewHistory5.packAfter base i))) ht).2
    have rest := ih (i+1) (by omega) (by omega) _
      (m.drop (measurementCount (W.repairedTick base i++NewHistory5.packAfter base i))) ht'
    rw [show i+1-1=i by omega,show i+1+n-1=i+(n+1)-1 by omega] at rest
    exact rest

 theorem forward_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (forward 1 511) m s=pullState (sig 511) (run (regularForward base 1 511) m s) := by
  have h := forward_gen x hx0 hx 511 1 (le_refl _) (by omega) s m (stage_one base x p s hs)
  have e : pullState (sig (1-1)) s=s := by
    apply State.extensionality
    · rfl
    · funext q
      show s.basis (sig 0 q)=s.basis q
      rw [sig_zero]
  rw [e,show 1+511-1=511 from rfl] at h
  exact h


 theorem regularForward_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (hlo : History5.HistoryAbove w)
    (x p : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p)
    (n : Nat) : ∀i,i+n        ≤        512 → ∀(s : State)(m k : List Bool), Stage w x p i s.basis →
      run (regularForward w i n) m s=run (compactForward w i n) k s := by
  induction n with
  | zero => intro i hi s m k hs; rfl
  | succ n ih =>
    intro i hi s m k hs
    have e := step_eq w hn x p i hp0 hx0 hpo hp hgap hx hc (by omega) s
      (m.take (measurementCount (W.repairedTick w i++NewHistory5.packAfter w i)))
      (k.take (measurementCount (W.compactSkywalkTick w i++NewHistory5.packAfter w i))) hs
    have next := (compact_step_spec w hn hlo x p i hp0 hx0 hpo hp hgap hx hc (by omega)
      s (k.take (measurementCount (W.compactSkywalkTick w i++NewHistory5.packAfter w i))) hs).2
    rw [regularForward,compactForward]
    conv_lhs => rw [run_append]
    conv_rhs => rw [run_append]
    rw [e]
    exact ih (i+1) (by omega) _ _ _ next

 theorem compactForward_normalize (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hi : i+n        ≤        512) (s : State) :
    run (compactForward w i n) [] (run (NewHistory5.encodePrefix w i) [] s)=
      run (NewHistory5.encodePrefix w (i+n)) [] (run (W.compactSkywalkForward w i n) [] s) := by
  induction n generalizing i s with
  | zero => simp only [compactForward,W.compactSkywalkForward,Nat.add_zero,run]
  | succ n ih =>
    have dis := prefix_disjoint_tick w hn i i (le_refl _) (by omega)
    have commute := run_disjoint_commute (NewHistory5.encodePrefix w i) (W.compactSkywalkTick w i) dis [] [] s
    have join (t : State) : run (NewHistory5.packAfter w i) [] (run (NewHistory5.encodePrefix w i) [] t)=
        run (NewHistory5.encodePrefix w (i+1)) [] t := by
      rw [NewHistory5.encodePrefix,run_append]
      simp only [List.take_nil,List.drop_nil]
    rw [compactForward,W.compactSkywalkForward]
    simp only [run_append,List.take_nil,List.drop_nil]
    rw [←commute,join,ih (i+1) (by omega)]
    rw [show i+(n+1)=(i+1)+n by omega]

 theorem regularForward_first_normalize (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : History5.HistoryAbove w) (x p : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1)
    (hp : p<2^256) (hgap : p+2^32        ≤        2^256) (hx : x<p) (hc : x.Coprime p)
    (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (regularForward w 1 511) m s=
      run (NewHistory5.allEncode w 102) [] (run (W.compactSkywalkForward w 1 511) [] s) := by
  have h := compactForward_normalize w hn 1 511 (by omega) s
  have empty : NewHistory5.encodePrefix w 1=[] := by
    simp [NewHistory5.encodePrefix,NewHistory5.packAfter,History5.packDue]
  rw [empty,show (1:Nat)+511=512 from rfl,NewHistory5.encodePrefix_512] at h
  simp only [run] at h
  rw [regularForward_eq w hn hlo x p hp0 hx0 hpo hp hgap hx hc 511 1 (by omega)
    s m [] (stage_one w x p s hs)]
  exact h

 theorem regularForward_snoc (w : Nat → Wire) (i n : Nat) :
    regularForward w i (n+1)=regularForward w i n++
      (W.repairedTick w (i+n)++NewHistory5.packAfter w (i+n)) := by
  induction n generalizing i with
  | zero => simp [regularForward]
  | succ n ih =>
    rw [regularForward,ih (i+1),regularForward]
    rw [show i+1+n=i+(n+1) by omega]
    simp only [List.append_assoc]

 theorem forward_snoc (i n : Nat) : forward i (n+1)=forward i n++
    renameProgram (sig (i+n)) (W.repairedTick base (i+n)++packFirst base (i+n)) := by
  induction n generalizing i with
  | zero => simp [forward]
  | succ n ih =>
    rw [forward,ih (i+1),forward]
    rw [show i+1+n=i+(n+1) by omega]
    simp only [List.append_assoc]

 theorem stage511_bits (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State)
    (hs : Stage base x p 511 s.basis) :
    ∃G : Bool, ∀q∈tickSites,s.basis q=preBits G q := by
  obtain ⟨t,ht,read⟩ := old_stage_local base base_pool_nodup x p 511 (by omega) s hs
  obtain ⟨G,bits⟩ := stage511_bits5 x hx0 hx t ht
  refine ⟨G,?_⟩
  intro q hq
  have mem : q∈(W.compactSkywalkTickLayout base 511).wires.toFinset := by
    apply W.compactSkywalkTick_support base 511 (by omega) base_pool_nodup
    have same : W.compactSkywalkTick base 511=Arithmetic.compactSkywalkTick base 511 := by decide +kernel
    rw [same]
    exact tickSites_tick q hq
  exact (read q mem).trans (bits q hq)

 theorem tick509_forced_forward (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State)
    (hs : Stage base x p 509 s.basis) (m : List Bool) :
    run tick509F m s=run (W.repairedTick base 509) m s := by
  obtain ⟨t,ht,read⟩ := old_stage_local base base_pool_nodup x p 509 (by omega) s hs
  have hp : wires tick509F⊆(W.compactSkywalkTickLayout base 509).wires.toFinset := by
    apply Finset.Subset.trans _ (W.repairedTick_support base 509 (by omega) base_pool_nodup)
    rw [tick509ExF_explicit]
    exact tick509F_sub
  exact Stack5.local_replace _ _ _ hp (W.repairedTick_support base 509 (by omega) base_pool_nodup)
    s t m m read (ECDSAAdd.Entrant.tick509_forced_forward x hx0 hx t ht m)

 theorem tick510_forced_forward (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State)
    (hs : Stage base x p 510 s.basis) (m : List Bool) :
    run tick510F m s=run (W.repairedTick base 510) m s := by
  obtain ⟨t,ht,read⟩ := old_stage_local base base_pool_nodup x p 510 (by omega) s hs
  have hp : wires tick510F⊆(W.compactSkywalkTickLayout base 510).wires.toFinset := by
    apply Finset.Subset.trans _ (W.repairedTick_support base 510 (by omega) base_pool_nodup)
    rw [tick510ExF_explicit]
    exact tick510F_sub
  exact Stack5.local_replace _ _ _ hp (W.repairedTick_support base 510 (by omega) base_pool_nodup)
    s t m m read (ECDSAAdd.Entrant.tick510_forced_forward x hx0 hx t ht m)


 theorem packFirst_support_eq (w : Nat → Wire) (i : Nat) :
    wires (packFirst w i)=wires (FirstNonzeroCodec.pack8first w i) := by
  by_cases hi:i=5
  · subst i
    have old : wires FirstNonzeroCodec.encodeFirst=Finset.range 10 := by decide +kernel
    simp only [packFirst,FirstNonzeroCodec.pack8first,if_pos rfl,
      if_true,ParityCodec5New.encodeAtFirst,FirstNonzeroCodec.encodeAtFirst,renameProgram_support,
      ParityCodec5New.first_support_exact.1,old]
  · simp only [packFirst,FirstNonzeroCodec.pack8first,if_neg hi,StackOB5.pack9_eq]
    exact NewHistory5.pack_support_eq w i

 theorem packFirst_metrics (w : Nat → Wire) (i : Nat) :
    toffoliCount (packFirst w i)=toffoliCount (FirstNonzeroCodec.pack8first w i) ∧
    measurementCount (packFirst w i)=measurementCount (FirstNonzeroCodec.pack8first w i) ∧
    Challenge.gateSlots (packFirst w i)=Challenge.gateSlots (FirstNonzeroCodec.pack8first w i)+
      2*(if History5.packDue i then 1 else 0) := by
  by_cases hi:i=5
  · subst i
    have a := ParityCodec5New.first_countsAt (History5.historyMap w 0)
    have b := renameProgram_counts (MeasuredCodec5.label (History5.historyMap w 0)) FirstNonzeroCodec.encodeFirst
    have c := ParityCodec5New.first_slotsAt (History5.historyMap w 0)
    have d := Baselines.rename_gateSlots (MeasuredCodec5.label (History5.historyMap w 0)) FirstNonzeroCodec.encodeFirst
    simp only [packFirst,FirstNonzeroCodec.pack8first,if_pos rfl,show History5.packDue 5=true from rfl,
      if_true,Nat.mul_one,FirstNonzeroCodec.encodeAtFirst]
    rw [b.1,b.2,FirstNonzeroCodec.counts.1,FirstNonzeroCodec.counts.2.2.1,d,FirstNonzeroCodec.restricted_slots.1]
    exact ⟨a.1,a.2.2.1,by rw [c.1]⟩
  · simp only [packFirst,FirstNonzeroCodec.pack8first,if_neg hi,StackOB5.pack9_eq]
    cases due : History5.packDue i
    · simp only [NewHistory5.packAfter,History5.packAfter,due,Bool.false_eq_true,if_false,
        toffoliCount,measurementCount,Challenge.gateSlots,if_false,Nat.mul_zero,Nat.add_zero]
      exact ⟨True.intro,True.intro,True.intro⟩
    · simp only [NewHistory5.packAfter,History5.packAfter,due,if_true,NewHistory5.encode,History5.encode,Nat.mul_one]
      have a := ParityCodec5New.countsAt (History5.historyMap w (i-5))
      have b := MeasuredCodec5.countsAt (History5.historyMap w (i-5))
      have c := ParityCodec5New.slotsAt (History5.historyMap w (i-5))
      have d := MeasuredCodec5.slotsAt (History5.historyMap w (i-5))
      exact ⟨a.1.trans b.1.symm,a.2.1.trans b.2.1.symm,by rw [c.1,d.1]⟩

 theorem counts_gen (i n : Nat) :
    toffoliCount (forward i n)=toffoliCount (StackOB5.forward i n) ∧
    measurementCount (forward i n)=measurementCount (StackOB5.forward i n) ∧
    Challenge.gateSlots (forward i n)=Challenge.gateSlots (StackOB5.forward i n)+2*History5.packCount i n := by
  induction n generalizing i with
  | zero => simp [forward,StackOB5.forward,History5.packCount,toffoliCount,measurementCount,Challenge.gateSlots]
  | succ n ih =>
    have r := ih (i+1)
    have p := packFirst_metrics base i
    have f := renameProgram_counts (sig i) (W.repairedTick base i++packFirst base i)
    have g := renameProgram_counts (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    have fs := Baselines.rename_gateSlots (sig i) (W.repairedTick base i++packFirst base i)
    have gs := Baselines.rename_gateSlots (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    rw [forward,StackOB5.forward]
    simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,History5.packCount] at f g fs gs ⊢
    omega

 theorem forward_regular_records (i n : Nat) :
    measurementCount (forward i n)=measurementCount (regularForward base i n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [forward,regularForward,measurementCount_append,measurementCount_append,
      (renameProgram_counts _ _).2,measurementCount_append,measurementCount_append,packFirst_records,ih]

 theorem forward_support_eq (i n : Nat) : wires (forward i n)=wires (StackOB5.forward i n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [forward,StackOB5.forward,wires_append,renameProgram_support,packFirst_support_eq,ih]

 theorem forward_physical_gen (i n : Nat) (hb : i+n       ≤       512) : GatePhysical (forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,GatePhysical]
  | succ n ih =>
    have tick := W.repairedTick_physical base i (by omega) base_pool_nodup
    have pack : GatePhysical (packFirst base i) := by
      by_cases hi:i=5
      · subst i
        simpa only [packFirst,if_pos rfl] using
          (ParityCodec5New.first_mapped_physical _ (History5.historyMap_injective base base_pool_nodup 0 (by omega))).1
      · simp only [packFirst,if_neg hi,NewHistory5.packAfter]
        split
        · have hd := History5.packDue_true i ‹History5.packDue i=true›
          exact (ParityCodec5New.physicalAt _ (History5.historyMap_injective base base_pool_nodup (i-5) (by omega))).1
        · simp [GatePhysical]
    rw [forward,gatePhysical_append]
    exact ⟨gatePhysical_rename _ (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr ⟨tick,pack⟩),ih (i+1) (by omega)⟩


 theorem packAfter_metrics (w : Nat → Wire) (i : Nat) :
    toffoliCount (NewHistory5.packAfter w i)=toffoliCount (History5.packAfter w i) ∧
    measurementCount (NewHistory5.packAfter w i)=measurementCount (History5.packAfter w i) ∧
    Challenge.gateSlots (NewHistory5.packAfter w i)=Challenge.gateSlots (History5.packAfter w i)+
      2*(if History5.packDue i then 1 else 0) := by
  cases due : History5.packDue i
  · simp [NewHistory5.packAfter,History5.packAfter,due,toffoliCount,measurementCount,Challenge.gateSlots]
  · simp only [NewHistory5.packAfter,History5.packAfter,due,if_true,NewHistory5.encode,History5.encode,Nat.mul_one]
    have a := ParityCodec5New.countsAt (History5.historyMap w (i-5))
    have b := MeasuredCodec5.countsAt (History5.historyMap w (i-5))
    have c := ParityCodec5New.slotsAt (History5.historyMap w (i-5))
    have d := MeasuredCodec5.slotsAt (History5.historyMap w (i-5))
    exact ⟨a.1.trans b.1.symm,a.2.1.trans b.2.1.symm,by rw [c.1,d.1]⟩

 def stackForward509 : Program :=
  forward 1 508++renameProgram (sig 509) (tick509F++NewHistory5.packAfter base 509)
 def stackForward510 : Program :=
  stackForward509++renameProgram (sig 510) (tick510F++NewHistory5.packAfter base 510)
 def stackForwardT : Program := stackForward510++renameProgram (sig 511) tickF

 theorem stackForward_split509 : forward 1 509=forward 1 508++
    renameProgram (sig 509) (W.repairedTick base 509++NewHistory5.packAfter base 509) := by
  rw [forward_snoc 1 508,show (1:Nat)+508=509 from rfl]
  simp only [packFirst,show ¬(509:Nat)=5 by decide,if_false]

 theorem stackForward_split510 : forward 1 510=forward 1 509++
    renameProgram (sig 510) (W.repairedTick base 510++NewHistory5.packAfter base 510) := by
  rw [forward_snoc 1 509,show (1:Nat)+509=510 from rfl]
  simp only [packFirst,show ¬(510:Nat)=5 by decide,if_false]

 theorem pack511 : packFirst base 511=[] := by decide +kernel

 theorem stackForward_splitT : forward 1 511=forward 1 510++
    renameProgram (sig 511) (W.repairedTick base 511) := by
  rw [forward_snoc 1 510,show (1:Nat)+510=511 from rfl,pack511,List.append_nil]

 theorem stackForward509_counts :
    toffoliCount stackForward509=toffoliCount ECDSAAdd.Entrant.stackForward509 ∧
    measurementCount stackForward509=measurementCount ECDSAAdd.Entrant.stackForward509 ∧
    Challenge.gateSlots stackForward509=Challenge.gateSlots ECDSAAdd.Entrant.stackForward509+202 := by
  have f := counts_gen 1 508
  have p := packAfter_metrics base 509
  have pc : History5.packCount 1 508=101 := by decide +kernel
  have due : History5.packDue 509=false := by decide
  rw [pc] at f
  simp only [due,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at p
  simp only [stackForward509,ECDSAAdd.Entrant.stackForward509,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

 theorem stackForward510_counts :
    toffoliCount stackForward510=toffoliCount ECDSAAdd.Entrant.stackForward510 ∧
    measurementCount stackForward510=measurementCount ECDSAAdd.Entrant.stackForward510 ∧
    Challenge.gateSlots stackForward510=Challenge.gateSlots ECDSAAdd.Entrant.stackForward510+204 := by
  have f := stackForward509_counts
  have p := packAfter_metrics base 510
  have due : History5.packDue 510=true := by decide
  simp only [due,if_true,Nat.mul_one] at p
  simp only [stackForward510,ECDSAAdd.Entrant.stackForward510,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

 theorem stackForwardT_counts :
    toffoliCount stackForwardT=toffoliCount ECDSAAdd.Entrant.stackForwardT ∧
    measurementCount stackForwardT=measurementCount ECDSAAdd.Entrant.stackForwardT ∧
    Challenge.gateSlots stackForwardT=Challenge.gateSlots ECDSAAdd.Entrant.stackForwardT+204 := by
  have f := stackForward510_counts
  simp only [stackForwardT,ECDSAAdd.Entrant.stackForwardT,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append]
  omega

 theorem stackForward509_records : measurementCount stackForward509=measurementCount (forward 1 509) :=
  stackForward509_counts.2.1.trans (ECDSAAdd.Entrant.stackForward509_metrics.2.1.trans (counts_gen 1 509).2.1.symm)

 theorem stackForward510_records : measurementCount stackForward510=measurementCount (forward 1 510) :=
  stackForward510_counts.2.1.trans (ECDSAAdd.Entrant.stackForward510_metrics.2.1.trans (counts_gen 1 510).2.1.symm)


theorem stackForward509_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run stackForward509 m s = run (forward 1 509) m s := by
  let k := measurementCount (regularForward base 1 508)
  let a := run (regularForward base 1 508) (m.take k) s
  have cnt := forward_regular_records 1 508
  have e0 : pullState (OB5.sig (1-1)) s = s := by
    apply State.extensionality
    · rfl
    · funext q; show s.basis (OB5.sig 0 q)=s.basis q; rw [OB5.sig_zero]
  have pref := forward_gen x hx0 hx 508 1 (by omega) (by omega) s (m.take k) (stage_one base x p s first)
  rw [e0, show 1+508-1=508 by rfl] at pref
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32     ≤     2^256 := by norm_num [p]
  have stage := ((regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 508
    hp0 hx0 hpo hp hpGap hx cop (by omega)) s (m.take k) (stage_one base x p s first)).2
  change Stage base x p 509 a.basis at stage
  have z := stage_zero x 509 (by omega) a.basis stage
  have move := OB5.pull_step 509 (by omega) a z.1 z.2
  change pullState (OB5.sig 508) a = pullState (OB5.sig 509) a at move
  change run (forward 1 508) (m.take k) s = pullState (OB5.sig 508) a at pref
  have c := tick509_counts
  rw [←tick509ExF_explicit] at c
  have mc : measurementCount tick509F = measurementCount (W.repairedTick base 509) :=
    c.2.2.2.trans c.2.1.symm
  rw [stackForward509,stackForward_split509,run_append,run_append,cnt]
  change run (renameProgram (OB5.sig 509) (tick509F ++ NewHistory5.packAfter base 509)) (m.drop k)
      (run (forward 1 508) (m.take k) s) =
    run (renameProgram (OB5.sig 509) (W.repairedTick base 509 ++ NewHistory5.packAfter base 509)) (m.drop k)
      (run (forward 1 508) (m.take k) s)
  rw [pref,move,OB5.run_rename 509 (by omega),OB5.run_rename 509 (by omega),
    run_append,run_append,mc,tick509_forced_forward x hx0 hx a stage]


theorem stackForward510_run (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run stackForward510 m s = run (forward 1 510) m s := by
  let k := measurementCount (regularForward base 1 509)
  let a := run (regularForward base 1 509) (m.take k) s
  have cnt := forward_regular_records 1 509
  have e0 : pullState (OB5.sig (1-1)) s = s := by
    apply State.extensionality
    · rfl
    · funext q; show s.basis (OB5.sig 0 q)=s.basis q; rw [OB5.sig_zero]
  have pref := forward_gen x hx0 hx 509 1 (by omega) (by omega) s (m.take k) (stage_one base x p s first)
  rw [e0, show 1+509-1=509 by rfl] at pref
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32     ≤     2^256 := by norm_num [p]
  have stage := ((regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 509
    hp0 hx0 hpo hp hpGap hx cop (by omega)) s (m.take k) (stage_one base x p s first)).2
  change Stage base x p 510 a.basis at stage
  have z := stage_zero x 510 (by omega) a.basis stage
  have move := OB5.pull_step 510 (by omega) a z.1 z.2
  change pullState (OB5.sig 509) a = pullState (OB5.sig 510) a at move
  change run (forward 1 509) (m.take k) s = pullState (OB5.sig 509) a at pref
  have c := tick510_counts
  rw [←tick510ExF_explicit] at c
  have mc : measurementCount tick510F = measurementCount (W.repairedTick base 510) :=
    c.2.2.2.1.trans c.2.1.symm
  rw [stackForward510,stackForward_split510,run_append,run_append,stackForward509_records,cnt,
    stackForward509_run x hx0 hx s _ first]
  change run (renameProgram (OB5.sig 510) (tick510F ++ NewHistory5.packAfter base 510)) (m.drop k)
      (run (forward 1 509) (m.take k) s) =
    run (renameProgram (OB5.sig 510) (W.repairedTick base 510 ++ NewHistory5.packAfter base 510)) (m.drop k)
      (run (forward 1 509) (m.take k) s)
  rw [pref,move,OB5.run_rename 510 (by omega),OB5.run_rename 510 (by omega),
    run_append,run_append,mc,tick510_forced_forward x hx0 hx a stage]


theorem stackForwardT_run (_hn : (skywalkSharedWires base).Nodup) (_hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run stackForwardT m s = run (forward 1 511) m s := by
  let k := measurementCount (regularForward base 1 510)
  let a := run (regularForward base 1 510) (m.take k) s
  have cnt := forward_regular_records 1 510
  have e0 : pullState (OB5.sig (1-1)) s = s := by
    apply State.extensionality
    · rfl
    · funext q; show s.basis (OB5.sig 0 q)=s.basis q; rw [OB5.sig_zero]
  have pref := forward_gen x hx0 hx 510 1 (by omega) (by omega) s (m.take k) (stage_one base x p s first)
  rw [e0, show 1+510-1=510 by rfl] at pref
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32     ≤     2^256 := by norm_num [p]
  have stage := ((regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 510
    hp0 hx0 hpo hp hpGap hx cop (by omega)) s (m.take k) (stage_one base x p s first)).2
  change Stage base x p 511 a.basis at stage
  have z := stage_zero x 511 (by omega) a.basis stage
  have move := OB5.pull_step 511 (by omega) a z.1 z.2
  change pullState (OB5.sig 510) a = pullState (OB5.sig 511) a at move
  obtain ⟨G,bits⟩ := stage511_bits x hx0 hx a stage
  change ∀q∈tickSites,a.basis q=preBits G q at bits
  change run (forward 1 510) (m.take k) s = pullState (OB5.sig 510) a at pref
  rw [stackForwardT,stackForward_splitT,run_append,run_append,stackForward510_records,cnt,
    stackForward510_run x hx0 hx s _ first]
  change run (renameProgram (OB5.sig 511) tickF) (m.drop k) (run (forward 1 510) (m.take k) s) =
    run (renameProgram (OB5.sig 511) (W.repairedTick base 511)) (m.drop k)
      (run (forward 1 510) (m.take k) s)
  rw [pref,move,OB5.run_rename 511 (by omega),OB5.run_rename 511 (by omega),
    repaired511_forced G a bits,tickF_run]



 theorem stackForward509_support_eq : wires stackForward509=wires ECDSAAdd.Entrant.stackForward509 := by
  simp only [stackForward509,ECDSAAdd.Entrant.stackForward509,wires_append,renameProgram_support,
    forward_support_eq,NewHistory5.pack_support_eq]

 theorem stackForward510_support_eq : wires stackForward510=wires ECDSAAdd.Entrant.stackForward510 := by
  simp only [stackForward510,ECDSAAdd.Entrant.stackForward510,wires_append,renameProgram_support,
    stackForward509_support_eq,NewHistory5.pack_support_eq]

 theorem stackForwardT_support_eq : wires stackForwardT=wires ECDSAAdd.Entrant.stackForwardT := by
  simp only [stackForwardT,ECDSAAdd.Entrant.stackForwardT,wires_append,stackForward510_support_eq]

 theorem stackForwardT_subset : wires stackForwardT⊆wires (StackOB5.forward 1 511) := by
  rw [stackForwardT_support_eq]
  exact ECDSAAdd.Entrant.stackForwardT_subset

 theorem stackForwardT_support : wires stackForwardT⊆StackOB5.integerSites :=
  stackForwardT_subset.trans StackOB5.forward_support

 theorem stackForwardT_physical : GatePhysical stackForwardT := by
  have tf : GatePhysical tickF := by simp [tickF,base,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  have pk : GatePhysical (NewHistory5.packAfter base 510) := by
    simp only [NewHistory5.packAfter,show History5.packDue 510=true from rfl,if_true,NewHistory5.encode]
    exact (ParityCodec5New.physicalAt _ (History5.historyMap_injective base base_pool_nodup (510-5) (by omega))).1
  have pk9 : GatePhysical (NewHistory5.packAfter base 509) := by
    simp [NewHistory5.packAfter,History5.packDue,GatePhysical]
  have blk := gatePhysical_rename _ (OB5.sig_injective 510 (by omega)) _
    ((gatePhysical_append tick510F (NewHistory5.packAfter base 510)).mpr ⟨tick510_physical.1,pk⟩)
  have blk9 := gatePhysical_rename _ (OB5.sig_injective 509 (by omega)) _
    ((gatePhysical_append tick509F (NewHistory5.packAfter base 509)).mpr ⟨tick509_physical,pk9⟩)
  exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr
    ⟨(gatePhysical_append _ _).mpr ⟨forward_physical_gen 1 508 (by omega),blk9⟩,blk⟩,
    gatePhysical_rename _ (OB5.sig_injective 511 (by omega)) _ tf⟩

 theorem rawForward_old_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x prime : Nat) (hp0 : 0<prime) (hx0 : 0<x) (hpo : prime%2=1) (hp : prime<2^256)
    (hgap : prime+2^32     ≤     2^256) (hx : x<prime) (hc : x.Coprime prime)
    (s : State) (m n : List Bool)
    (hs : Arithmetic.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (prime:Int)) 1 s.basis) :
    run (W.compactSkywalkForward w 1 511) m s=run (Arithmetic.compactSkywalkForward w 1 511) n s := by
  have fw := W.compactSkywalkForward_spec w hn x prime 1 511 hp0 hx0 hpo hp hgap hx hc (by omega) s m
    ((W.compactSkywalkStage_one w _ s.basis).mpr hs)
  have fo := Arithmetic.compactSkywalkForward_spec w hn x prime 1 511 hp0 hx0 hpo hp hx hc (by omega) s n hs
  have tw := (Arithmetic.compactSkywalkStage_terminal w hn x prime hp0 hx0 hpo hp hx hc _
    ((W.compactSkywalkStage_eq w _ 512 W.narrowSkywalkRouteWidth_endpoints.2.2.1 _).mp fw.2)).2
  have oldTerminal :=  (Arithmetic.compactSkywalkStage_terminal w hn x prime hp0 hx0 hpo hp hx hc _ fo.2).2
  apply State.extensionality
  · exact fw.1.trans fo.1.symm
  · funext q
    by_cases hq:q∈skywalkPoolWires w
    · exact skywalkIntegerStage_agrees w _ 512 (by omega) _ _ tw oldTerminal q hq
    · rw [W.compactSkywalkForward_frame w hn 1 511 (by omega) s m q hq,
        Arithmetic.compactSkywalkForward_frame w hn 1 511 (by omega) s n q hq]


attribute [local irreducible] run wires NewHistory5.allEncode literalSkywalkSeed
  Arithmetic.compactSkywalkForward W.compactSkywalkForward NativeFirstDirect.forward
  NativeFirstDirect.reference skywalkArithmeticClear regularForward stackForwardT forward compactForward

 theorem stackForwardT_boundary (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run stackForwardT m s=pullState (sig 511) (run (NewHistory5.allEncode base 102) []
      (run (W.compactSkywalkForward base 1 511) [] s)) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32   ≤   2^256 := by norm_num [p]
  exact (stackForwardT_run hn hlo x hx0 hx s m hs).trans ((forward_run x hx0 hx s m hs).trans
    (congrArg (pullState (sig 511))
      (regularForward_first_normalize base base_pool_nodup hlo x p hp0 hx0 hpo hp hgap hx cop s m hs)))

open DirectSkywalk CompressedFieldSupport NativeFirstDirect OffsetBorrowedCanonical History5

 theorem encoder_clear_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    Disjoint (wires (NewHistory5.allEncode w 102)) (wires (skywalkArithmeticClear w)) := by
  rw [NewHistory5.allEncode_support_eq]
  exact Kernel5.encoder_clear_disjoint w hn

theorem preparation_facts (hn : (skywalkSharedWires base).Nodup)
    (hlo : HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (s1 s2 s3 : State)
    (hs1 : run (NativeFirstDirect.forward base) m1 s=s1)
    (hs2 : run (regularForward base 1 511) m2 s1=s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2=s3)
    (first : CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis) :
    ∃origin:State,PreparationFacts x Y s origin ∧ History5.RawLegal base 102 origin.basis ∧
      origin.phase=s3.phase ∧ s3=run (NewHistory5.allEncode base 102) [] origin ∧
      NewHistory5.EncodedCanonicalFrame5 origin.basis Y 0 s3 := by
  have hp0 : 0 < p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p < 2^256 := by norm_num [p]
  have cop := arith_coprime x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have ready := caller_ready base hn x Y.val s.basis hin
  let oldSeed := run (literalSkywalkSeed (literalSkywalkPoolSeed base) p) [] s
  have seedEq : run (literalSkywalkSeed (literalSkywalkPoolSeed base) p) [] s=oldSeed := rfl
  have reference := forward_reference_eq base pool x hx s m1 [] ready.1 ready.2
  have referenceEq : run (NativeFirstDirect.reference base) [] s=
      run (compactSkywalkTick base 0) [] oldSeed := by
    rw [NativeFirstDirect.reference,run_append]
    simp only [List.take_nil,List.drop_nil]
    rfl
  have firstEq : s1=run (compactSkywalkTick base 0) [] oldSeed :=
    hs1.symm.trans (reference.trans referenceEq)
  let rawFinal := run (compactSkywalkForward base 0 512) [] oldSeed
  have rawJoin : rawFinal=run (compactSkywalkForward base 1 511) [] s1 := by
    dsimp only [rawFinal]
    rw [compactSkywalkForward,run_append]
    simp only [List.take_nil,List.drop_nil]
    rw [←firstEq]
  have rawStep := compactSkywalkForward_spec base pool x p 1 511 hp0 hx0 hpo hp hx cop
    (by omega) s1 [] first
  have s2Encoded : s2=run (NewHistory5.allEncode base 102) [] rawFinal := by
    rw [←hs2,regularForward_first_normalize base pool hlo x p hp0 hx0 hpo hp (by norm_num [p]) hx cop
      s1 m2 ((W.compactSkywalkStage_one base _ s1.basis).mpr first),
      rawForward_old_eq base pool x p hp0 hx0 hpo hp (by norm_num [p]) hx cop s1 [] [] first,←rawJoin]
  let origin := run (skywalkArithmeticClear base) m3 rawFinal
  have facts := rawPreparation_facts hn ho x Y hx0 hx s [] [] m3 hin oldSeed rawFinal origin seedEq rfl rfl
  have encoded : s3=run (NewHistory5.allEncode base 102) [] origin := by
    rw [←hs3,s2Encoded]
    exact (run_disjoint_commute _ _ (encoder_clear_disjoint base pool) [] m3 rawFinal).symm
  have phase : origin.phase=s3.phase := by
    rw [encoded]
    exact (NewHistory5.allEncode_zero_phase base pool 102 (by decide) origin).symm
  have legalBefore : History5.RawLegal base 102 rawFinal.basis := by
    rw [rawJoin]
    exact rawLegal_of_compactStage base pool x p 512 102 hp0 hpo (by omega) (by omega)
      _ rawStep.2
  have legal := Kernel5.clear_raw_legal5 base pool rawFinal origin m3 rfl legalBefore
  refine ⟨origin,facts,legal,phase,encoded,origin,phase,?_,encoded⟩
  exact ⟨facts.targetValue,by simpa only [ZMod.val_zero] using facts.sourceZero,fun _ _ _ => rfl⟩



attribute [local irreducible] NewHistory5.encodePrefix OB5.sig

 theorem final_prefix_keep (raw : State) (l : Nat) (hl : l=1026 ∨ 1539   ≤   l) :
    (run (NewHistory5.encodePrefix base 512) [] raw).basis (base l)=raw.basis (base l) := by
  apply run_preserves_outside
  intro hm
  rw [NewHistory5.prefix_support_eq] at hm
  obtain ⟨j,hj,hr⟩ := StackOB5Base.encodePrefix_mem 512 (by omega) _ hm
  have := base_injective hj
  omega

 theorem terminal_host_bits (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State)
    (hs : Stage base x p 512 s.basis) :
    s.basis (base 1026)=false ∧ s.basis (base 1541)=false ∧ s.basis (base 1539)=false := by
  obtain ⟨raw,stage,eq⟩ := hs
  have fields := (W.compactSkywalkStage_fields_iff base _ 512 (by omega) base_pool_nodup raw.basis).mp stage
  have mem : base 1026∈(W.compactSkywalkSignPoolB base 512).released := by decide +kernel
  have clean1026 := stage.2.2 _ mem
  have carry : regValue (wireBlock base 1540 257) raw.basis=0 := fields.2.2.2.2.2.1
  have clean1541 : raw.basis (base 1541)=false := (regValue_zero _ _).mp carry _ (by decide +kernel)
  have bit := (fields.2.2.2.1 511 (by omega)).2
  rw [SkywalkTrace.code511 x hx0 hx] at bit
  exact ⟨((congrFun eq (base 1026)).trans (final_prefix_keep raw 1026 (Or.inl rfl))).trans clean1026,
    ((congrFun eq (base 1541)).trans (final_prefix_keep raw 1541 (Or.inr (by omega)))).trans clean1541,
    ((congrFun eq (base 1539)).trans (final_prefix_keep raw 1539 (Or.inr (by omega)))).trans bit⟩

 theorem forward_host_bits (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    (run stackForwardT m s).basis (base 1026)=false ∧
    (run stackForwardT m s).basis (base 1541)=false ∧
    (run stackForwardT m s).basis (base 1542)=false := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  obtain ⟨t,ht⟩ : ∃t : State,run (regularForward base 1 511) m s=t := ⟨_,rfl⟩
  have stage : Stage base x p 512 t.basis := by
    have raw := (regularForward_spec base base_pool_nodup StackOB5.historyAbove x p 1 511 hp0 hx0 hpo hp hgap hx cop
      (by omega) s m (stage_one base x p s hs)).2
    rw [ht] at raw
    exact raw
  have bits := terminal_host_bits x hx0 hx t stage
  have eq : run stackForwardT m s=pullState (sig 511) t := by
    rw [←ht]
    exact (stackForwardT_run hn StackOB5.historyAbove x hx0 hx s m hs).trans (forward_run x hx0 hx s m hs)
  have fixed0 : sig 511 (base 1026)=base 1026 := by decide +kernel
  have fixed1 : sig 511 (base 1541)=base 1541 := by decide +kernel
  have fixed2 : sig 511 (base 1542)=base 1539 := by decide +kernel
  rw [eq]
  change t.basis (sig 511 (base 1026))=false ∧ t.basis (sig 511 (base 1541))=false ∧
    t.basis (sig 511 (base 1542))=false
  rw [fixed0,fixed1,fixed2]
  exact bits


 theorem forward_clear_zero (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m2 m3 : List Bool)
    (hs : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    let out := run (skywalkArithmeticClear base) m3 (run stackForwardT m2 s)
    out.basis (base 1026)=false ∧ out.basis (base 1541)=false ∧ out.basis (base 1542)=false := by
  have bits := forward_host_bits hn x hx0 hx s m2 hs
  have keep (l : Nat) (hl : l=1026 ∨ l=1541 ∨ l=1542) :
      (run (skywalkArithmeticClear base) m3 (run stackForwardT m2 s)).basis (base l)=
        (run stackForwardT m2 s).basis (base l) := by
    apply run_preserves_outside
    intro hm
    rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at hm
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h|h|h
    all_goals have := base_injective h; omega
  dsimp only
  rw [keep 1026 (by simp),keep 1541 (by simp),keep 1542 (by simp)]
  exact bits


end ECDSAAdd.Entrant.NewStackOB5
