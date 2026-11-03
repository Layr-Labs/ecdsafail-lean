import ECDSAAdd.Submission.Entrant.ExitMerge
import ECDSAAdd.Submission.Entrant.E1WholeKAdd52Draft
import ECDSAAdd.Submission.Entrant.E1ActualMF52Draft
import ECDSAAdd.Submission.Entrant.E1ResourceBridge52Draft

/-! SOURCE-ONLY actual ordinary/exit endpoints. Old39 ancestors are unchanged.
Only the selected kAdd sites use the checked52 whole program and real ordinary MF bridge.
Proofs have not been elaborated in this new module; no reflected/global certificate claim. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1AffineEndpoints52Research
open Arithmetic NativeFirstDirect RecordedQuantum Challenge
open E1WholeKAdd52Research

attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

namespace Forward
open E1Merge

private def pre (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  comparePart w g k++(parGates w g k++rotateRight (kR w))++prodPart w g++loadK w g k

private def post (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  loadK w g k++[.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]

/-- The only runtime substitution is old39 flagKAdd → checked whole flagKAdd52. -/
def merged (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  pre w g k++flagKAdd52 w++post w g k

private theorem base_split (w : Nat → Wire) (g : Wire) (k : Nat) :
    E1Merge.merged w g k=pre w g k++KAddCallerBridgeResearch.flagKAdd w++post w g k := by
  simp only [E1Merge.merged,pre,post,List.append_assoc]

section Semantics
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

private theorem merged_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let f := decide (2^256-1-(if G then 2^256-p+k else 0)<X)
    let dx := (X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    Triple (MF w b0 0 X 0 false false false false) (merged w g k)
      (MF w b0 (2*H+(!par).toNat) K 0 par false false false) := by
  intro G f dx par K H
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX G
  change decide (X%2=1)=E1Merge.x0 k G f par at a1
  change (X/2+tk k G f par)%2^258=K at a2
  change H=dx/2+(if par then hConstant else 0) at a3
  change f=decide (H<thr k G par) at a4
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hpar : (decide (X%2=1) ^^ (G && decide (k%2=1)) ^^ f)=par := by
    have e : decide (X%2=1)=E1Merge.x0 k G f par := a1
    rw [e]; unfold E1Merge.x0 E1Merge.ksel0
    generalize (G && decide (k%2=1))=a
    cases par <;> cases a <;> cases f <;> rfl
  have hfg : f=true → G=true := by
    intro hf; cases hG : G
    · have : f=false := by
        simp only [f,hG,Bool.false_eq_true,if_false,decide_eq_false_iff_not]; rw [p_val] at hX; omega
      rw [this] at hf; exact absurd hf (by simp)
    · rfl
  have fC : decide (2^256-1-(if b0 g then cmpC+k else 0)<X)=f := by simp [f,G,cmpC]
  have s1 := stepCompareMF w g hn b0 k X (by unfold cmpC; rw [p_val] at hk ⊢; omega) (by rw [p_val] at hX; omega)
    hc hcin (g_out w hn g hg 0 256 (by omega)) (g_ne w hn g hg 514 (by omega)) gm
  rw [fC] at s1
  have s2 := stepPar w g hn b0 k X f hg
  rw [show (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f)=par from hpar] at s2
  have s3 := stepRot w hn b0 X par f false false
  have s4a := stepCCX w hn b0 0 (X/2) 0 par f false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s4a
  have s4b := stepCCX w hn b0 0 (X/2) 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s4b
  have s5 := stepLoadK w g hn b0 k 0 (X/2) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkv_eq k G f par hfg] at s5
  have kWord : (tk k G f par+X/2)%2^258=K := by rw [Nat.add_comm]; exact a2
  have s6 := ActualMF52Research.stepKAddFlag52 w hn b0 (tk k G f par) (X/2) 0 par f (G && par) (f && par) hac h1797
    dx (Nat.mod_lt _ (by rw [p_val]; norm_num)) rfl (by exact kWord)
  rw [kWord] at s6
  have s7 := stepLoadK w g hn b0 k (tk k G f par) K 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkv_eq k G f par hfg,Nat.xor_self] at s7
  have s8 := stepMeasFp w hn b0 0 K 0 par f (G && par)
  have s9 := stepCopy w hn b0 K 0 par f (G && par) false
  have s10 := stepHAddT w hn b0 (K%2^257) K 0 par f (G && par) false (Nat.mod_lt _ (by positivity)) hac h1797
  rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]] at s10
  have s11 := stepW0 w hn b0 H K 0 par f (G && par) false
  have s12 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K 0 hk par f (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltv_eq] at s12
  have hHlt : 2*H+(!par).toNat<2^257 := by
    have dxl : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
    rw [a3]; rw [p_val] at dxl
    cases par <;>
      simp only [hC_val,Bool.not_true,Bool.not_false,Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,if_true,if_false] <;>
      omega
  have s13 := stepErase w hn b0 (2*H+(!par).toNat) K (thr k G par) par f (G && par) false hac h1797 hHlt
    (by rw [show (2*H+(!par).toNat)/2=H by cases par <;> simp; omega]; exact a4)
  have s14 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K (thr k G par) hk par false (G && par) false hg
  rw [show b0 g=G from rfl,ltv_eq,Nat.xor_self] at s14
  have s15 := stepMeasGp w g hn b0 (2*H+(!par).toNat) K 0 par false false gm (g_ne w hn g hg 721 (by omega))
  have t := s1.seq (s2.seq (s3.seq (s4a.seq (s4b.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq (s13.seq (s14.seq s15))))))))))))))
  unfold merged pre post prodPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

theorem merged_eq_forward (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (t u : State) (m m' : List Bool)
    (tk0 : regValue (kR w) t.basis=X) (th0 : regValue (hR w) t.basis=0) (tt0 : regValue (tR w) t.basis=0)
    (t1028 : t.basis (w 1028)=false) (t514 : t.basis (w 514)=false) (t515 : t.basis (w 721)=false)
    (t516 : t.basis (w 722)=false)
    (hc : ∀ i, 258 ≤ i → i < 512 → t.basis (w i) = false) (hcin : t.basis (w 513)=false)
    (hac : ∀q∈aC w,t.basis q=false) (h1797 : t.basis (w 1797)=false)
    (hu : u.phase=t.phase) (hu2 : ∀q,q∉kR w → u.basis q=t.basis q)
    (hu3 : regValue (kR w) u.basis=(X+(if t.basis g then k else 0))%p) :
    run (merged w g k) m t=run (NativeFirstDirect.forward w) m' u := by
  have mf0 : MF w t.basis 0 X 0 false false false false t.basis :=
    ⟨th0,tk0,tt0,t1028,t514,t515,t516,fun _ _ => rfl⟩
  have tri := merged_triple w g hn hg k hk t.basis X hX hc hcin hac h1797 t m mf0
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX (t.basis g)
  generalize hG : t.basis g=G at tri a1 a2 a3 a4 a5 hu3
  generalize hdx : (X+(if G then k else 0))%p=dx at tri a1 a2 a3 a4 a5 hu3
  generalize hpar : decide (dx%2=1)=par at tri a1 a2 a3 a4 a5
  generalize hK : (dx/2+kConstant false par)%2^258=K at tri a1 a2 a3 a4 a5
  generalize hH : (K%2^257+delta par)%2^257=H at tri a1 a2 a3 a4 a5
  obtain ⟨lp,l1,l2,l3,l4,l5,l6,l7,l8⟩ := tri
  have dxlt : dx<p := by rw [←hdx]; exact Nat.mod_lt _ (by rw [p_val]; norm_num)
  have kh : ∀q∈hR w,q∉kR w := kR_hR w hn
  have kt : ∀q∈tR w,q∉kR w := kR_tR w hn
  have hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 dx u.basis := by
    constructor
    · change regValue (wireBlock w 0 258) u.basis=0
      rw [show wireBlock w 0 258=hR w from rfl,regValue_congr _ _ t.basis (fun q hq => hu2 q (kh q hq)),th0]
    · change regValue (wireBlock w 770 258) u.basis=dx
      exact hu3
    · change regValue (wireBlock w 1540 257) u.basis=0
      apply (regValue_zero _ _).mpr
      intro q hq
      rw [hu2 q (fun h' => List.disjoint_left.mp (blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)) h' hq)]
      exact hac q hq
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
    · change u.basis (w 1028)=false
      rw [hu2 _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact t1028
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec w hn dx dxlt u m' hin
  have e770 : u.basis (w 770)=par := by
    have sp := kR_split w hn u.basis
    rw [hu3] at sp
    rw [←hpar]
    cases hb : u.basis (w 770) <;> simp [hb] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  rw [hK] at zk
  have hv : 2*(dx/2+(if par then hConstant else 0))+(!par).toNat=2*H+(!par).toNat := by rw [a3]
  rw [hv] at zh
  apply State.extensionality
  · rw [lp,zp,hu]
  · funext q
    by_cases qh : q∈hR w
    · exact (regValue_eq_iff (hR w) _ _).mp (l1.trans zh.symm) q qh
    by_cases qk : q∈kR w
    · exact (regValue_eq_iff (kR w) _ _).mp (l2.trans zk.symm) q qk
    by_cases q1 : q=w 1028
    · rw [q1,l4,z1028]
    have nmut : q∉NativeFirstDirect.mutable w := by
      simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
      exact ⟨⟨fun h' => qh (blk_sub w 0 257 0 258 (by omega) (by omega) q h'),qk⟩,q1⟩
    rw [zrest q nmut,hu2 q qk]
    by_cases qt : q∈tR w
    · rw [(regValue_zero _ _).mp l3 q qt,(regValue_zero _ _).mp tt0 q qt]
    by_cases q4 : q=w 514
    · rw [q4,l5,t514]
    by_cases q5 : q=w 721
    · rw [q5,l6,t515]
    by_cases q6 : q=w 722
    · rw [q6,l7,t516]
    apply l8
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,qk⟩,qt⟩,q1,q4,q5,q6⟩

end Semantics

theorem merged_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (merged w g k)⊆(mSites w g).toFinset := by
  have B := blk_mSites w g
  have I := in_mSites w g
  have G := g_mSites w g
  have mskH (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have mskS (v : Nat) : wires (maskedConstant g (srcR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset g (srcR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 0 256 (by omega) q hq))
  have notS : wires (notRegister (srcR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]; exact lsub w g _ (B 0 256 (by omega))
  have cmp : wires (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (srcR w) (xR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,xR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 0 256 (by omega) q hq
    · exact B 770 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mSites w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mskS _,notS⟩,cmp⟩,notS⟩,mskS _⟩
  have cx (a b : Nat) (ha : a < 515 ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have hP : wires (parGates w g k)⊆(mSites w g).toFinset := by
    unfold parGates
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hR' : wires (rotateRight (kR w))⊆(mSites w g).toFinset := by
    rw [(rotate_wires (kR w)).1]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub w g _ (B 770 258 (by omega))
  have hPr : wires (prodPart w g)⊆(mSites w g).toFinset := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub <;> intro q hq <;>
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hL : wires (loadK w g k)⊆(mSites w g).toFinset := by
    simp only [loadK,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub w g _ (B 0 258 (by omega)))
  have hKOld : wires (kAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hK : wires (E1WholeKAdd52Research.flagKAdd52 w)⊆(mSites w g).toFinset := by
    apply (E1ResourceBridge52Research.flag_support52 w).trans
    simp only [Finset.union_subset_iff]
    constructor
    · simpa only [←kAdd_literal] using hKOld
    · intro q hq
      have eq : q=w 1028 := Finset.mem_singleton.mp hq
      rw [eq]
      exact List.mem_toFinset.mpr (I 1028 (by omega))
  have hM1 : wires [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hM2 : wires [.measureX (w 721) [] [.CZ g (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl
    · exact I _ (by omega)
    · exact G
    · exact I _ (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mSites w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hH : wires (hAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · rw [dBits_wire w q hq]; exact I 1028 (by omega)
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mSites w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hT : wires (loadT w g k)⊆(mSites w g).toFinset := by
    simp only [loadT,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have hE : wires (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hHT : wires (hAddT w)⊆(mSites w g).toFinset := (hAddT_wires w).trans hH
  simp only [merged,pre,post,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨hC,⟨hP,hR'⟩⟩,hPr⟩,hL⟩,hK⟩,⟨⟨⟨⟨⟨⟨⟨⟨hL,hM1⟩,hCp⟩,hHT⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩⟩

theorem merged_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (merged w g k)=1023 ∧ measurementCount (merged w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (srcR w)
  have c1' := compareLt_counts none (srcR w) (xR w) (cR w) (w 513) (w 514)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,xR,wireBlock_length])
  have r1 := rotate_counts (kR w)
  have k1 := mappedAdd_counts (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length])
  have h1 := mappedAdd_counts (dBits w) (hpR w) (hC2 w) (w 1797)
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length])
  have e1 := eraseLtChain_counts (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length])
  have cp1 := copyRegister_counts none (wireBlock w 770 257) (hpR w) (by simp [hpR,wireBlock_length])
  have pg : toffoliCount (parGates w g k)=0 ∧ measurementCount (parGates w g k)=0 := by
    unfold parGates; split_ifs <;> simp [toffoliCount,measurementCount]
  have lx : (xR w).length=256 := by simp [xR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  rw [lx] at c1'
  rw [lk] at k1
  have kOld : toffoliCount (KAddCallerBridgeResearch.literalKAdd w)=257 ∧
      measurementCount (KAddCallerBridgeResearch.literalKAdd w)=257 := k1
  have kDelta := E1WholeKAdd52Research.flag_counts52 w
  have kNew : toffoliCount (E1WholeKAdd52Research.flagKAdd52 w)=255 ∧
      measurementCount (E1WholeKAdd52Research.flagKAdd52 w)=257 := by omega
  rw [lh] at h1
  rw [lt] at e1
  have hT := hAddT_counts w
  rw [hAddM,h1.1,h1.2] at hT
  have hT' : toffoliCount (hAddT w)=255 ∧ measurementCount (hAddT w)=256 := by omega
  simp only [merged,pre,post,comparePart,prodPart,loadK,kNew.1,kNew.2,hT'.1,hT'.2,loadT,toffoliCount_append,
    measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,n1.1,n1.2,c1'.1,c1'.2.1,
    r1.1,r1.2.1,h1.1,h1.2,e1.1,e1.2,cp1.1,cp1.2,pg.1,pg.2]
  simp [toffoliCount,measurementCount]

section Phys
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_physical (k : Nat) : GatePhysical (merged w g k) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j := w_ne w hn i j hi hj h
  have gn (i : Nat) (hi : i<1798) : g≠w i := g_ne w hn g hg i hi
  have cxp (a b : Wire) (h : a≠b) : GatePhysical [.CX a b] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h]
  have ccxp (a b c : Wire) (h1 : a≠c) (h2 : b≠c) : GatePhysical [.CCX a b c] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h1,h2]
  have mp (c : Wire) (c' : Wire) : GatePhysical [.measureX c [] [.CZ c' c]] ∧
      GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by
    simp [GatePhysical,PhysicalInstr]
  have gS : g∉srcR w := g_out w hn g hg 0 256 (by omega)
  have gH : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have cmpP : GatePhysical (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
      have l1 : (srcR w++xR w).Nodup := List.nodup_append'.mpr ⟨src_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
      have l2 : (srcR w++xR w++cR w).Nodup := by
        apply List.nodup_append'.mpr
        refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
        apply List.disjoint_left.mpr
        intro q hq hc'
        rcases List.mem_append.mp hq with h1|h1
        · exact List.disjoint_left.mp a2 h1 hc'
        · exact List.disjoint_left.mp a3 h1 hc'
      simp only [List.cons_append,List.append_assoc] at l2 ⊢
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,by simpa [List.append_assoc] using l2⟩⟩
      · simp only [List.mem_cons,List.mem_append,not_or]
        exact ⟨ne 514 513 (by omega) (by omega) (by omega),nb w hn 514 0 256 (by omega) (by omega) (by omega),
          nb w hn 514 770 256 (by omega) (by omega) (by omega),nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 513 0 256 (by omega) (by omega) (by omega),nb w hn 513 770 256 (by omega) (by omega) (by omega),
          nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
    · simp
  have kPOld : GatePhysical (kAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      refine ⟨?_,?_,?_⟩
      · intro e; exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq')
      · exact fun h' => hR_kR w hn _ h' hq'
      · exact fun h' => List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq' h'
  have kP : GatePhysical (E1WholeKAdd52Research.flagKAdd52 w) :=
    E1ResourceBridge52Research.flag_gatePhysical_pool52 w hn (by simpa only [←kAdd_literal] using kPOld)
  have hP : GatePhysical (hAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      have : q∈mappedWires (dBits w) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [dBits_wire w q this,List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne 1028 1797 (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
        nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have eP : GatePhysical (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)) := by
    apply eraseLtChain_physical
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    rw [List.cons_append,List.cons_append]
    refine List.nodup_cons.mpr ⟨?_,l2⟩
    simp only [List.mem_append,not_or]
    exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cpP : GatePhysical (copyRegister none (wireBlock w 770 257) (hpR w)) :=
    copyRegister_physical none _ _ (List.nodup_append'.mpr ⟨blk_nd w hn 770 257 (by omega),
      blk_nd w hn 1 257 (by omega),blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩) (by simp)
  have parP : GatePhysical (parGates w g k) := by
    unfold parGates
    split_ifs <;> simp only [gatePhysical_append] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first
        | exact cxp _ _ (ne _ _ (by omega) (by omega) (by omega))
        | exact cxp _ _ (gn _ (by omega))
        | simp [GatePhysical]
  have rotP := (rotate_physical (kR w) (kR_nd w hn)).1
  have prodP : GatePhysical (prodPart w g) := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,gatePhysical_append]
    exact ⟨ccxp _ _ _ (gn _ (by omega)) (ne _ _ (by omega) (by omega) (by omega)),
      ccxp _ _ _ (ne _ _ (by omega) (by omega) (by omega)) (ne _ _ (by omega) (by omega) (by omega))⟩
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h1286 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h1287 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t1286 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  have lkP : GatePhysical (loadK w g k) := by
    simp only [loadK,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨xorConstant_physical _ _,maskedConstant_physical _ _ _ gH⟩,maskedConstant_physical _ _ _ h514⟩,
      maskedConstant_physical _ _ _ h1028⟩,maskedConstant_physical _ _ _ h1286⟩,maskedConstant_physical _ _ _ h1287⟩
  have ltP : GatePhysical (loadT w g k) := by
    simp only [loadT,gatePhysical_append]
    exact ⟨maskedConstant_physical _ _ _ gT,maskedConstant_physical _ _ _ t1286⟩
  have w0P : GatePhysical [.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,ne 1028 0 (by omega) (by omega) (by omega)]
  have cP : GatePhysical (comparePart w g k) := by
    simp only [comparePart,gatePhysical_append]
    exact ⟨⟨⟨⟨maskedConstant_physical _ _ _ gS,notRegister_physical _⟩,cmpP⟩,notRegister_physical _⟩,
      maskedConstant_physical _ _ _ gS⟩
  have m1 : GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have m2 : GatePhysical [.measureX (w 721) [] [.CZ g (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have hPT : GatePhysical (hAddT w) := hAddT_physical w hP
  simp only [merged,pre,post,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨cP,⟨parP,rotP⟩⟩,prodP⟩,lkP⟩,kP⟩,⟨⟨⟨⟨⟨⟨⟨⟨lkP,m1⟩,cpP⟩,hPT⟩,w0P⟩,ltP⟩,eP⟩,ltP⟩,m2⟩⟩

end Phys

theorem merged_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (merged w g k)≤25000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (srcR w) (xR w) (cR w) (w 513) (w 514)
  have r1 := (Baselines.rotate_gateSlots_le (kR w)).1
  have k1 := Baselines.mappedAdd_gateSlots_le (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
  have h1 := Baselines.mappedAdd_gateSlots_le (dBits w) (hpR w) (hC2 w) (w 1797)
  have e1 := Baselines.eraseLt_gateSlots_le (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
  have pg : Challenge.gateSlots (parGates w g k)≤6 := by
    unfold parGates; split_ifs <;> simp [Challenge.gateSlots,Challenge.instructionSlots]
  have pr : Challenge.gateSlots (prodPart w g)=2 := by simp [prodPart,Challenge.gateSlots,Challenge.instructionSlots]
  have w0 : Challenge.gateSlots [.CX (w 1028) (w 0),.X (w 0)]=2 := by simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q1 : Challenge.gateSlots [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q2 : Challenge.gateSlots [.measureX (w 721) [] [.CZ g (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have lK : Challenge.gateSlots (loadK w g k)≤6*258 := by
    simp only [loadK,Challenge.gateSlots_append]
    have := x1 (hR w) (c1 k); have := m1 g (hR w) (cg k); have := m1 (w 514) (hR w) (cf k)
    have := m1 (w 1028) (hR w) (cp k); have := m1 (w 721) (hR w) (cgp k); have := m1 (w 722) (hR w) (cfp k)
    simp only [hR,wireBlock_length] at *
    omega
  have lT : Challenge.gateSlots (loadT w g k)≤2*256 := by
    simp only [loadT,Challenge.gateSlots_append]
    have := m1 g (tR w) (thrA k); have := m1 (w 721) (tR w) (thrB k)
    simp only [tR,wireBlock_length] at *
    omega
  have cP : Challenge.gateSlots (comparePart w g k)≤4*256+12*256+4 := by
    simp only [comparePart,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
    have := m1 g (srcR w) (cmpC+k)
    simp only [srcR,xR,wireBlock_length] at *
    omega
  have cp : Challenge.gateSlots (copyRegister none (wireBlock w 770 257) (hpR w))=257 := by
    simp [hpR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hp8 w).length=256 := by simp [hp8,wireBlock_length]
  have lhR : (hR w).length=258 := by simp [hR,wireBlock_length]
  rw [lk] at r1
  rw [mappedRead_length,lhR] at k1
  have kOld : Challenge.gateSlots (KAddCallerBridgeResearch.literalKAdd w)≤17*258 := k1
  have kNew : Challenge.gateSlots (E1WholeKAdd52Research.flagKAdd52 w)+2≤17*258 := by
    rw [(E1WholeKAdd52Research.flag_counts52 w).2.2]
    exact kOld
  rw [dBits_length] at h1
  rw [lh] at e1
  have hS := hAddT_slots w
  rw [hAddM] at hS
  simp only [merged,pre,post,Challenge.gateSlots_append,pr,w0,q1,q2,cp]
  omega

end Forward

namespace Exit
open E1Merge ExitMerge

private def addPre (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  FastConst.maskedNot g (kR w)++loadKX w g k

private def addPost (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  loadKX w g k++[.measureX (w 722) [] [.CZ (w 514) (w 1028)],
    .measureX (w 721) [] [.CZ g (w 1028)]]

/-- Both original product erasers are retained in addPost, in their old order. -/
private def addPart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  addPre w g k++zeroKAdd52 w++addPost w g k

private def pre (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  fPart w g k++eraseH w++addPre w g k

private def post (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  addPost w g k++rotateLeft (kR w)++parBack w g k++eraseF w g k

def program (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  fPart w g k++eraseH w++addPart w g k++rotateLeft (kR w)++parBack w g k++eraseF w g k

private theorem base_split (w : Nat → Wire) (g : Wire) (k : Nat) :
    ExitMerge.program w g k=pre w g k++KAddCallerBridgeResearch.zeroKAdd w++post w g k := by
  simp only [ExitMerge.program,ExitMerge.addPart,pre,post,addPre,addPost,List.append_assoc]

private theorem new_split (w : Nat → Wire) (g : Wire) (k : Nat) :
    program w g k=pre w g k++zeroKAdd52 w++post w g k := by
  simp only [program,addPart,pre,post,addPre,addPost,List.append_assoc]

section Semantics
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

private theorem program_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let Y := if G then (k+p-X)%p else X
    Triple (MF w b0 (2*H+(!par).toNat) K 0 par false false false) (program w g k)
      (MF w b0 0 Y 0 false false false false) := by
  intro G par H K Y
  obtain ⟨a1,a2,a3,a5,a6,a7,a8⟩ := archX k X hk hX G
  let f := G && decide (k<X)
  change H<2^256 at a1
  change (dInv par+H)%2^257=K%2^257 at a2
  change f=(decide (H<thrX k G par) ^^ G) at a3
  change ((if G then 2^258-1-K else K)+tkX k G f par)%2^258=Y/2 at a5
  change Y<p at a6
  change decide (Y%2=1)=(par ^^ (G && decide (k%2=1)) ^^ f) at a7
  change f=decide ((if G then k else 2^256-1)<Y) at a8
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hfg : f=true → G=true := by
    intro hf; simp only [f,Bool.and_eq_true] at hf; exact hf.1
  have hKlt : K<2^258 := Nat.mod_lt _ (by positivity)
  have hpb : (!par).toNat<2 := Bool.toNat_lt _
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  -- threshold compare
  have s1 := stepCCX w hn b0 (2*H+(!par).toNat) K 0 par false false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s1
  have s2 := stepLoadTX w g hn b0 k (2*H+(!par).toNat) K 0 hk par false (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltvX_eq] at s2
  have s3 := stepCmpH w hn b0 H (!par).toNat K (thrX k G par) par (G && par) false a1 hpb hac h1797
  have s4 := stepFlagCX w hn b0 (2*H+(!par).toNat) K (thrX k G par) par (decide (H<thrX k G par))
    (G && par) false g G (g_ne w hn g hg 514 (by omega)) (fun s h => h.2.2.2.2.2.2.2 g gm)
  rw [←a3] at s4
  have s5 := stepLoadTX w g hn b0 k (2*H+(!par).toNat) K (thrX k G par) hk par f (G && par) false hg
  rw [show b0 g=G from rfl,ltvX_eq,Nat.xor_self] at s5
  have s6 := stepCCX w hn b0 (2*H+(!par).toNat) K 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s6
  -- erase the tick word
  have s7 := stepW0Back w hn b0 H K 0 par f (G && par) (f && par)
  have s8 := stepKnownH w hn b0 H K 0 par f (G && par) (f && par) (by omega) a2 hac h1797
  have s9 := stepCopyBack w hn b0 K 0 par f (G && par) (f && par)
  -- one mapped addition to `y/2`
  have s10 := stepNegK w g hn b0 0 K 0 par f (G && par) (f && par) hKlt hg
  have s11 := stepLoadKX w g hn b0 k 0 (if G then 2^258-1-K else K) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkvX_eq k G f par hfg] at s11
  have kWord : (tkX k G f par+(if G then 2^258-1-K else K))%2^258=Y/2 := by
    rw [Nat.add_comm]; exact a5
  have s12 := ActualMF52Research.stepKAddZero52 w hn b0 (tkX k G f par) (if G then 2^258-1-K else K) 0 par f (G && par) (f && par)
    hac h1797 Y a6 kWord
  rw [kWord] at s12
  have s13 := stepLoadKX w g hn b0 k (tkX k G f par) (Y/2) 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkvX_eq k G f par hfg,Nat.xor_self] at s13
  have s14 := stepMeasFp w hn b0 0 (Y/2) 0 par f (G && par)
  have s15 := stepMeasGp w g hn b0 0 (Y/2) 0 par f false gm (g_ne w hn g hg 721 (by omega))
  -- rotate and parity
  have s16 := stepRotL w hn b0 0 (Y/2) 0 par f false false (by rw [p_val] at a6; omega)
  have s17 := stepParBack w g hn b0 k (Y/2) par f hg
  rw [show b0 g=G from rfl,←a7,show 2*(Y/2)+(decide (Y%2=1)).toNat=Y by
    rcases Nat.mod_two_eq_zero_or_one Y with hy|hy <;> simp [hy] <;> omega] at s17
  -- erase the flag
  have s18 := stepMaskT w hn b0 0 Y 0 false f false false g G gT (fun s h => h.2.2.2.2.2.2.2 g gm)
    (2^256-1-k) (by omega)
  have s19 := stepNotT w hn b0 0 Y (0^^^(if G then 2^256-1-k else 0)) false f false false
  have hT (G' : Bool) : 2^256-1-(0^^^(if G' then 2^256-1-k else 0))=(if G' then k else 2^256-1) := by
    rw [p_val] at hk; cases G' <;> simp; omega
  rw [hT G] at s19
  have s20 := stepEraseF w hn b0 0 Y (if G then k else 2^256-1) false f false false hac h1797
    (by rw [p_val] at a6; omega) a8
  have s21 := stepNotT w hn b0 0 Y (if G then k else 2^256-1) false false false false
  have s22 := stepMaskT w hn b0 0 Y (2^256-1-(if G then k else 2^256-1)) false false false false g G gT
    (fun s h => h.2.2.2.2.2.2.2 g gm) (2^256-1-k) (by omega)
  have hT2 (G' : Bool) : (2^256-1-(if G' then k else 2^256-1))^^^(if G' then 2^256-1-k else 0)=0 := by
    cases G' <;> simp [Nat.xor_self]
  rw [hT2 G] at s22
  have t := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq
    (s12.seq (s13.seq (s14.seq (s15.seq (s16.seq (s17.seq (s18.seq (s19.seq (s20.seq (s21.seq
    s22))))))))))))))))))))
  unfold program fPart eraseH addPart addPre addPost eraseF
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

theorem program_run (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (initial field : State) (mF m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 X initial.basis)
    (ht : regValue (tR w) initial.basis=0) (h514 : initial.basis (w 514)=false)
    (h721 : initial.basis (w 721)=false) (h722 : initial.basis (w 722)=false)
    (hphase : field.phase=(run (NativeFirstDirect.forward w) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires w,
      field.basis q=(run (NativeFirstDirect.forward w) mF initial).basis q) :
    (run (program w g k) m field).phase=initial.phase ∧
    regValue (kR w) (run (program w g k) m field).basis=(if field.basis g then (k+p-X)%p else X) ∧
    (∀q∈skywalkPoolWires w,q∉kR w → (run (program w g k) m field).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires w → (run (program w g k) m field).basis q=field.basis q) := by
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec w hn X hX initial mF hin
  have e770 : initial.basis (w 770)=decide (X%2=1) := by
    have sp := kR_split w hn initial.basis
    have hb : regValue (kR w) initial.basis=X := hin.b
    rw [hb] at sp
    cases h : initial.basis (w 770) <;> simp [h] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  have inPool (a n : Nat) (ha : a+n≤1798) : ∀q∈wireBlock w a n,q∈skywalkPoolWires w :=
    blk_sub w a n 0 1798 (by omega) ha
  have wPool (i : Nat) (hi : i<1798) : w i∈skywalkPoolWires w :=
    List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  have keepI (i : Nat) (hi : i < 1798) (h1 : 257 ≤ i) (h2 : i < 770 ∨ 1028 < i) :
      field.basis (w i)=initial.basis (w i) := by
    rw [hpool _ (wPool i hi)]
    apply zrest
    simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
    exact ⟨⟨nb w hn i 0 257 hi (by omega) (by omega),nb w hn i 770 258 hi (by omega) (by omega)⟩,
      w_ne w hn i 1028 hi (by omega) (by omega)⟩
  have hR0 : regValue (hR w) field.basis=
      2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat := by
    rw [regValue_congr (hR w) field.basis _ (fun q hq => hpool q (inPool 0 258 (by omega) q hq))]
    exact zh
  have kR0 : regValue (kR w) field.basis=(X/2+kConstant false (decide (X%2=1)))%2^258 := by
    rw [regValue_congr (kR w) field.basis _ (fun q hq => hpool q (inPool 770 258 (by omega) q hq))]
    exact zk
  have tR0 : regValue (tR w) field.basis=0 := by
    rw [regValue_congr (tR w) field.basis initial.basis (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact keepI i (by omega) (by omega) (by omega))]
    exact ht
  have f1028 : field.basis (w 1028)=decide (X%2=1) := (hpool _ (wPool 1028 (by omega))).trans z1028
  have f514 : field.basis (w 514)=false := (keepI 514 (by omega) (by omega) (by omega)).trans h514
  have f721 : field.basis (w 721)=false := (keepI 721 (by omega) (by omega) (by omega)).trans h721
  have f722 : field.basis (w 722)=false := (keepI 722 (by omega) (by omega) (by omega)).trans h722
  have hac : ∀q∈aC w,field.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [keepI i (by omega) (by omega) (by omega)]
    exact (regValue_zero _ _).mp hin.carry _ hq
  have h1797 : field.basis (w 1797)=false := (keepI 1797 (by omega) (by omega) (by omega)).trans hin.cin
  have mf0 : MF w field.basis (2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat)
      ((X/2+kConstant false (decide (X%2=1)))%2^258) 0 (decide (X%2=1)) false false false field.basis :=
    ⟨hR0,kR0,tR0,f1028,f514,f721,f722,fun _ _ => rfl⟩
  obtain ⟨tp,o1,o2,o3,o4,o5,o6,o7,o8⟩ := program_triple w g hn hg k hk field.basis X hX hac h1797 field m mf0
  have outMut (q : Wire) (hq : q∉skywalkPoolWires w) : q∉mutL w := fun h => hq (mutL_pool w q h)
  refine ⟨tp.trans (hphase.trans zp),o2,?_,fun q hq => o8 q (outMut q hq)⟩
  intro q hq hk'
  by_cases qh : q∈hR w
  · rw [(regValue_zero _ _).mp o1 q qh]
    exact ((regValue_zero _ _).mp hin.a q qh).symm
  by_cases qt : q∈tR w
  · rw [(regValue_zero _ _).mp o3 q qt]
    exact ((regValue_zero _ _).mp ht q qt).symm
  by_cases q1 : q=w 1028
  · rw [q1,o4]; exact hin.one.symm
  by_cases q2 : q=w 514
  · rw [q2,o5]; exact h514.symm
  by_cases q3 : q=w 721
  · rw [q3,o6]; exact h721.symm
  by_cases q4 : q=w 722
  · rw [q4,o7]; exact h722.symm
  have nm : q∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,hk'⟩,qt⟩,q1,q2,q3,q4⟩
  rw [o8 q nm,hpool q hq]
  apply zrest
  simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
  exact ⟨⟨fun h' => qh (blk_sub w 0 257 0 258 (by omega) (by omega) q h'),hk'⟩,q1⟩

end Semantics

theorem program_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (program w g k)⊆(mSites w g).toFinset := by
  have B := blk_mSites w g
  have I := in_mSites w g
  have G := g_mSites w g
  have mskH (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have notT : wires (notRegister (tR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]; exact lsub w g _ (B 1029 256 (by omega))
  have cx (a b : Nat) (ha : a < 515 ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have ccx1 : wires [.CCX g (w 1028) (w 721)]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl|rfl
    · exact G
    · exact I _ (by omega)
    · exact I _ (by omega)
  have ccx2 : wires [.CCX (w 514) (w 1028) (w 722)]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hT : wires (loadTX w g k)⊆(mSites w g).toFinset := by
    simp only [loadTX,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have cmp : wires (compareLt none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514) (by simp [hp8,tR,wireBlock_length])
      (by simp [hC2,tR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 1797 (by omega)
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
  have hF : wires (fPart w g k)⊆(mSites w g).toFinset := by
    simp only [fPart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨ccx1,hT⟩,cmp⟩,cxg 514 (by omega)⟩,hT⟩,ccx2⟩
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mSites w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hKn : wires (knownH w)⊆(mSites w g).toFinset := by
    apply (KnownOutputAdder.program_support _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with (((hq|hq)|hq)|hq)|rfl
    · rw [dBitsX_wire w q hq]; exact I 1028 (by omega)
    · rw [desiredX,mappedRead_wires] at hq; exact B 770 257 (by omega) q hq
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mSites w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hE : wires (eraseH w)⊆(mSites w g).toFinset := by
    simp only [eraseH,wires_append,Finset.union_subset_iff]
    exact ⟨⟨hW,hKn⟩,hCp⟩
  have hNeg : wires (FastConst.maskedNot g (kR w))⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset g (kR w) _).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 770 258 (by omega) q hq))
  have hL : wires (loadKX w g k)⊆(mSites w g).toFinset := by
    simp only [loadKX,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub w g _ (B 0 258 (by omega)))
  have hKOld : wires (kAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hK : wires (E1WholeKAdd52Research.zeroKAdd52 w)⊆(mSites w g).toFinset := by
    apply (E1ResourceBridge52Research.zero_support52 w).trans
    simpa only [←kAdd_literal] using hKOld
  have hM : wires ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],.measureX (w 721) [] [.CZ g (w 1028)]] : Program)⊆
      (mSites w g).toFinset := by
    rw [show ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],.measureX (w 721) [] [.CZ g (w 1028)]] : Program)=
      [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++[.measureX (w 721) [] [.CZ g (w 1028)]] from rfl,
      wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub <;> intro q hq <;>
      simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
        Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hA : wires (addPart w g k)⊆(mSites w g).toFinset := by
    simp only [addPart,addPre,addPost,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨hNeg,hL⟩,hK⟩,⟨hL,hM⟩⟩
  have hRot : wires (rotateLeft (kR w))⊆(mSites w g).toFinset := by
    rw [(rotate_wires (kR w)).2]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub w g _ (B 770 258 (by omega))
  have hP : wires (parBack w g k)⊆(mSites w g).toFinset := by
    unfold parBack
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hEr : wires (eraseLtChain (tR w) (xR w) (hC3 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1029 256 (by omega) q hq
    · exact B 770 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hEF : wires (eraseF w g k)⊆(mSites w g).toFinset := by
    simp only [eraseF,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mskT g G _,notT⟩,hEr⟩,notT⟩,mskT g G _⟩
  simp only [program,addPre,addPost,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨hF,hE⟩,hA⟩,hRot⟩,hP⟩,hEF⟩

theorem program_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (program w g k)=767 ∧ measurementCount (program w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (tR w)
  have c1' := compareLt_counts none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC2,tR,wireBlock_length])
  have r1 := rotate_counts (kR w)
  have k1 := mappedAdd_counts (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length])
  have kh := KnownOutputAdder.program_counts (dBitsX w) (desiredX w) (hpR w) (hC2 w) (w 1797)
    (by rw [dBitsX_length]; simp [hpR,wireBlock_length]) (by rw [desiredX_length]; simp [hpR,wireBlock_length])
    (by simp [hC2,hpR,wireBlock_length])
  have e1 := eraseLtChain_counts (tR w) (xR w) (hC3 w) (w 1797) (w 514)
    (by simp [xR,tR,wireBlock_length]) (by simp [hC3,xR,wireBlock_length])
  have cp1 := copyRegister_counts none (wireBlock w 770 257) (hpR w) (by simp [hpR,wireBlock_length])
  have pb : toffoliCount (parBack w g k)=0 ∧ measurementCount (parBack w g k)=0 := by
    unfold parBack; split_ifs <;> simp [toffoliCount,measurementCount]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lx : (xR w).length=256 := by simp [xR,wireBlock_length]
  rw [lt] at c1'
  rw [lk] at k1
  have kOld : toffoliCount (KAddCallerBridgeResearch.literalKAdd w)=257 ∧
      measurementCount (KAddCallerBridgeResearch.literalKAdd w)=257 := k1
  have kDelta := E1WholeKAdd52Research.zero_counts52 w
  have kNew : toffoliCount (E1WholeKAdd52Research.zeroKAdd52 w)=254 ∧
      measurementCount (E1WholeKAdd52Research.zeroKAdd52 w)=257 := by omega
  rw [lh] at kh
  rw [lx] at e1
  simp only [program,addPre,addPost,fPart,eraseH,addPart,eraseF,loadTX,loadKX,knownH,kNew.1,kNew.2,FastConst.maskedNot,
    toffoliCount_append,measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,
    n1.1,n1.2,c1'.1,c1'.2.1,r1.2.2.1,r1.2.2.2,kh.1,kh.2,e1.1,e1.2,cp1.1,cp1.2,pb.1,pb.2]
  simp [toffoliCount,measurementCount]

section Phys
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem program_physical (k : Nat) : GatePhysical (program w g k) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j := w_ne w hn i j hi hj h
  have gn (i : Nat) (hi : i<1798) : g≠w i := g_ne w hn g hg i hi
  have cxp (a b : Wire) (h : a≠b) : GatePhysical [.CX a b] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h]
  have ccxp (a b c : Wire) (h1 : a≠c) (h2 : b≠c) : GatePhysical [.CCX a b c] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h1,h2]
  have gH : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have gK : g∉kR w := g_out w hn g hg 770 258 (by omega)
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have cmpP : GatePhysical (compareLt none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 1 256 1540 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 1029 256 1540 256 (by omega) (by omega) (by omega)
      have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
      have l2 : (hp8 w++tR w++hC2 w).Nodup := by
        apply List.nodup_append'.mpr
        refine ⟨l1,blk_nd w hn 1540 256 (by omega),?_⟩
        apply List.disjoint_left.mpr
        intro q hq hc'
        rcases List.mem_append.mp hq with h1|h1
        · exact List.disjoint_left.mp a2 h1 hc'
        · exact List.disjoint_left.mp a3 h1 hc'
      simp only [List.cons_append,List.append_assoc] at l2 ⊢
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,by simpa [List.append_assoc] using l2⟩⟩
      · simp only [List.mem_cons,List.mem_append,not_or]
        exact ⟨ne 514 1797 (by omega) (by omega) (by omega),nb w hn 514 1 256 (by omega) (by omega) (by omega),
          nb w hn 514 1029 256 (by omega) (by omega) (by omega),nb w hn 514 1540 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega),
          nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · simp
  have khP : GatePhysical (knownH w) := by
    unfold knownH
    apply KnownOutputAdder.program_physical
    · rw [dBitsX_length]; simp [hpR,wireBlock_length]
    · rw [desiredX_length]; simp [hpR,wireBlock_length]
    · simp [hC2,hpR,wireBlock_length]
    · rw [List.cons_append]
      have d := blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      have : q∈mappedWires (dBitsX w) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [dBitsX_wire w q this,List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne 1028 1797 (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
        nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [desiredX,mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq'
      simp only [List.mem_range'_1] at hi
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne i 1797 (by omega) (by omega) (by omega),nb w hn i 1 257 (by omega) (by omega) (by omega),
        nb w hn i 1540 256 (by omega) (by omega) (by omega)⟩
  have kPOld : GatePhysical (kAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      refine ⟨?_,?_,?_⟩
      · intro e; exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq')
      · exact fun h' => hR_kR w hn _ h' hq'
      · exact fun h' => List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq' h'
  have kP : GatePhysical (E1WholeKAdd52Research.zeroKAdd52 w) :=
    E1ResourceBridge52Research.zero_gatePhysical_pool52 w hn (by simpa only [←kAdd_literal] using kPOld)
  have eP : GatePhysical (eraseLtChain (tR w) (xR w) (hC3 w) (w 1797) (w 514)) := by
    apply eraseLtChain_physical
    have a1 := blk_dis w hn 1029 256 770 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 770 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (tR w++xR w).Nodup := List.nodup_append'.mpr ⟨tR_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
    have l2 : (tR w++xR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    rw [List.cons_append,List.cons_append]
    refine List.nodup_cons.mpr ⟨?_,l2⟩
    simp only [List.mem_append,not_or]
    exact ⟨⟨nb w hn 1797 1029 256 (by omega) (by omega) (by omega),nb w hn 1797 770 256 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cpP : GatePhysical (copyRegister none (wireBlock w 770 257) (hpR w)) :=
    copyRegister_physical none _ _ (List.nodup_append'.mpr ⟨blk_nd w hn 770 257 (by omega),
      blk_nd w hn 1 257 (by omega),blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩) (by simp)
  have parP : GatePhysical (parBack w g k) := by
    unfold parBack
    split_ifs <;> simp only [gatePhysical_append] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first
        | exact cxp _ _ (ne _ _ (by omega) (by omega) (by omega))
        | exact cxp _ _ (gn _ (by omega))
        | simp [GatePhysical]
  have rotP := (rotate_physical (kR w) (kR_nd w hn)).2
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h721 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h722 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t721 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  have lkP : GatePhysical (loadKX w g k) := by
    simp only [loadKX,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨xorConstant_physical _ _,maskedConstant_physical _ _ _ gH⟩,maskedConstant_physical _ _ _ h514⟩,
      maskedConstant_physical _ _ _ h1028⟩,maskedConstant_physical _ _ _ h721⟩,maskedConstant_physical _ _ _ h722⟩
  have ltP : GatePhysical (loadTX w g k) := by
    simp only [loadTX,gatePhysical_append]
    exact ⟨maskedConstant_physical _ _ _ gT,maskedConstant_physical _ _ _ t721⟩
  have w0P : GatePhysical [.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,ne 1028 0 (by omega) (by omega) (by omega)]
  have mP : GatePhysical ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],.measureX (w 721) [] [.CZ g (w 1028)]] :
      Program) := by
    simp [GatePhysical,PhysicalInstr]
  have fP : GatePhysical (fPart w g k) := by
    simp only [fPart,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨ccxp _ _ _ (gn _ (by omega)) (ne _ _ (by omega) (by omega) (by omega)),ltP⟩,cmpP⟩,
      cxp _ _ (gn _ (by omega))⟩,ltP⟩,
      ccxp _ _ _ (ne _ _ (by omega) (by omega) (by omega)) (ne _ _ (by omega) (by omega) (by omega))⟩
  have eHP : GatePhysical (eraseH w) := by
    simp only [eraseH,gatePhysical_append]
    exact ⟨⟨w0P,khP⟩,cpP⟩
  have negP : GatePhysical (FastConst.maskedNot g (kR w)) :=
    maskedConstant_physical _ _ _ gK
  have aP : GatePhysical (addPart w g k) := by
    simp only [addPart,addPre,addPost,gatePhysical_append]
    exact ⟨⟨⟨negP,lkP⟩,kP⟩,⟨lkP,mP⟩⟩
  have eFP : GatePhysical (eraseF w g k) := by
    simp only [eraseF,gatePhysical_append]
    exact ⟨⟨⟨⟨maskedConstant_physical _ _ _ gT,notRegister_physical _⟩,eP⟩,notRegister_physical _⟩,
      maskedConstant_physical _ _ _ gT⟩
  simp only [program,addPre,addPost,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨fP,eHP⟩,aP⟩,rotP⟩,parP⟩,eFP⟩

end Phys

theorem program_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (program w g k)≤22000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514)
  have r1 := (Baselines.rotate_gateSlots_le (kR w)).2
  have k1 := Baselines.mappedAdd_gateSlots_le (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
  have h1 := Baselines.knownAdder_gateSlots_le (dBitsX w) (desiredX w) (hpR w) (hC2 w) (w 1797)
  have e1 := Baselines.eraseLt_gateSlots_le (tR w) (xR w) (hC3 w) (w 1797) (w 514)
  have pb : Challenge.gateSlots (parBack w g k)≤6 := by
    unfold parBack; split_ifs <;> simp [Challenge.gateSlots,Challenge.instructionSlots]
  have g1 : Challenge.gateSlots [.CCX g (w 1028) (w 721)]=1 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have g2 : Challenge.gateSlots [.CCX (w 514) (w 1028) (w 722)]=1 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have g3 : Challenge.gateSlots [.CX g (w 514)]=1 := by simp [Challenge.gateSlots,Challenge.instructionSlots]
  have w0 : Challenge.gateSlots [.CX (w 1028) (w 0),.X (w 0)]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q1 : Challenge.gateSlots ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],
      .measureX (w 721) [] [.CZ g (w 1028)]] : Program)=4 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have lK : Challenge.gateSlots (loadKX w g k)≤6*258 := by
    simp only [loadKX,Challenge.gateSlots_append]
    have := x1 (hR w) (c1X k); have := m1 g (hR w) (cgX k); have := m1 (w 514) (hR w) (cfX k)
    have := m1 (w 1028) (hR w) (cpX k); have := m1 (w 721) (hR w) (cgpX k); have := m1 (w 722) (hR w) (cfpX k)
    simp only [hR,wireBlock_length] at *
    omega
  have lT : Challenge.gateSlots (loadTX w g k)≤2*256 := by
    simp only [loadTX,Challenge.gateSlots_append]
    have := m1 g (tR w) (thrXA k); have := m1 (w 721) (tR w) (thrXB k)
    simp only [tR,wireBlock_length] at *
    omega
  have nT : Challenge.gateSlots (notRegister (tR w))=256 := by
    simp [Baselines.notRegister_gateSlots,tR,wireBlock_length]
  have mT : Challenge.gateSlots (maskedConstant g (tR w) (2^256-1-k))≤256 := by
    have := m1 g (tR w) (2^256-1-k); simpa [tR,wireBlock_length] using this
  have mK : Challenge.gateSlots (FastConst.maskedNot g (kR w))≤258 := by
    have bound := m1 g (kR w) (2^(kR w).length-1)
    change Challenge.gateSlots (FastConst.maskedNot g (kR w))≤(kR w).length at bound
    exact bound.trans (by simp only [kR,wireBlock_length]; exact Nat.le_refl _)
  have cp : Challenge.gateSlots (copyRegister none (wireBlock w 770 257) (hpR w))=257 := by
    simp [hpR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lp : (hp8 w).length=256 := by simp [hp8,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  have lhR : (hR w).length=258 := by simp [hR,wireBlock_length]
  rw [lk] at r1
  rw [mappedRead_length,lhR] at k1
  have kOld : Challenge.gateSlots (KAddCallerBridgeResearch.literalKAdd w)≤17*258 := k1
  have kNew : Challenge.gateSlots (E1WholeKAdd52Research.zeroKAdd52 w)+12≤17*258 := by
    rw [(E1WholeKAdd52Research.zero_counts52 w).2.2]
    exact kOld
  rw [dBitsX_length] at h1
  rw [lt] at e1
  rw [lp,lt] at c1'
  simp only [program,addPre,addPost,fPart,eraseH,addPart,eraseF,knownH,Challenge.gateSlots_append,g1,g2,g3,w0,q1,cp,nT]
  omega

end Exit
end ECDSAAdd.Entrant.E1AffineEndpoints52Research
