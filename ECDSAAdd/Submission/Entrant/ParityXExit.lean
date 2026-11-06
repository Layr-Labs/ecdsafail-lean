import ECDSAAdd.Submission.Entrant.ParityEven
import ECDSAAdd.Submission.Entrant.MainPart07
namespace ECDSAAdd.Entrant.ParityXExit
open Arithmetic Challenge RecordedQuantum NativeFirstDirect MappedCompressed E1Merge ExitMerge ParityCarry ParityConvert ParityEven
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires GatePhysical toffoliCount measurementCount gateSlots
  ExitMerge.fPart ExitMerge.eraseH ExitMerge.addPart ExitMerge.parBack ExitMerge.eraseF
  FastConst.maskedNot ExitMerge.loadKX Verifier.Leaf4.zero4KAdd rotateLeft

def eraseLayout (w:Nat→Wire) : MeasuredCanonicalModLayout where
  src:=tR w
  out:=xR w
  carry:=hC2 w
  high:=w 721
  cin:=w 1797
  flag:=w 514

theorem eraseLayout_widths (w:Nat→Wire) : (eraseLayout w).Widths 256 := by
  constructor <;> simp [eraseLayout,tR,xR,hC2,wireBlock]

theorem eraseLayout_nodup : (base 2400::(eraseLayout base).wires).Nodup := by
  have numeric:(2400::((List.range' 1029 256)++(List.range' 770 256)++(List.range' 1540 256)++[721,1797,514])).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    simp only [List.count_cons,List.count_append,List.count_nil,List.count_range_1',beq_iff_eq]
    split_ifs <;> omega
  simpa only [eraseLayout,MeasuredCanonicalModLayout.wires,tR,xR,hC2,wireBlock,
    List.map_cons,List.map_nil,List.map_append] using numeric.map base_injective

theorem eraseF_eq (w:Nat→Wire) (g:Wire) (k:Nat) :
    eraseF w g k=erasePrefixOld g (eraseLayout w).src (eraseLayout w).out
      ((eraseLayout w).carry.take 255) (eraseLayout w).cin (eraseLayout w).flag (2^256-1-k) := by
  simp only [eraseF,erasePrefixOld,loadNot,unloadNot,eraseLayout,hC2,hC3,wireBlock,
    ←List.map_take,List.take_range'_of_length_ge (by decide : 256 ≥ 255),List.append_assoc]

def eraseOdd (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  erasePrefixNew g (eraseLayout w).src (eraseLayout w).out ((eraseLayout w).carry.take 255)
    (eraseLayout w).cin (eraseLayout w).flag (2^256-1-k)

theorem eraseOdd_eq (k:Nat) (hk:k<2^256) (he:k%2=1) (s:State) (m:List Bool)
    (ht:regValue (tR base) s.basis=0) (hc:s.basis (base 1797)=false) :
    run (eraseOdd base (base 2400) k) m s=run (eraseF base (base 2400) k) m s := by
  have even:(2^256-1-k)%2=0:=by omega
  rw [eraseF_eq]
  exact erase_layout_eq (eraseLayout base) (base 2400) (eraseLayout_widths base)
    eraseLayout_nodup (2^256-1-k) even s m ht hc

theorem eraseOdd_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (eraseOdd w g k)+1=toffoliCount (eraseF w g k) ∧
    measurementCount (eraseOdd w g k)=measurementCount (eraseF w g k) ∧
    gateSlots (eraseOdd w g k)+8=gateSlots (eraseF w g k) := by
  rw [eraseF_eq]
  exact erase_layout_counts (eraseLayout w) g (eraseLayout_widths w) (2^256-1-k)

def programOdd (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  ExitMerge.fPart w g k++ExitMerge.eraseH w++ExitMerge.addPart w g k++
    rotateLeft (kR w)++ExitMerge.parBack w g k++eraseOdd w g k

theorem programOdd_triple (k : Nat) (hk : k<p) (he:k%2=1) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hac : ∀q∈aC base,b0 q=false) (h1797 : b0 (base 1797)=false) :
    let G := b0 (base 2400)
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let Y := if G then (k+p-X)%p else X
    Triple (MF base b0 (2*H+(!par).toNat) K 0 par false false false) (programOdd base (base 2400) k)
      (MF base b0 0 Y 0 false false false false) := by
  intro G par H K Y
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  obtain ⟨a1,a2,a3,a5,a6,a7,a8⟩ := archX k X hk hX G
  let f := G && decide (k<X)
  change H<2^256 at a1
  change (dInv par+H)%2^257=K%2^257 at a2
  change f=(decide (H<thrX k G par) ^^ G) at a3
  change ((if G then 2^258-1-K else K)+tkX k G f par)%2^258=Y/2 at a5
  change Y<p at a6
  change decide (Y%2=1)=(par ^^ (G && decide (k%2=1)) ^^ f) at a7
  change f=decide ((if G then k else 2^256-1)<Y) at a8
  have gm := g_mut base (base 2400) hn hg
  have hp' := p_val
  have hfg : f=true → G=true := by
    intro hf; simp only [f,Bool.and_eq_true] at hf; exact hf.1
  have hKlt : K<2^258 := Nat.mod_lt _ (by norm_num)
  have hpb : (!par).toNat<2 := Bool.toNat_lt _
  have gT : (base 2400)∉tR base := g_out base hn (base 2400) hg 1029 256 (by omega)
  -- threshold compare
  have s1 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par false false false (base 2400) (base 1028) 721 (by omega) G par
    (g_ne base hn (base 2400) hg 721 (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s1
  have s2 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K 0 hk par false (G && par) false hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,ltvX_eq] at s2
  have s3 := stepCmpH base hn b0 H (!par).toNat K (thrX k G par) par (G && par) false a1 hpb hac h1797
  have s4 := stepFlagCX base hn b0 (2*H+(!par).toNat) K (thrX k G par) par (decide (H<thrX k G par))
    (G && par) false (base 2400) G (g_ne base hn (base 2400) hg 514 (by omega)) (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm)
  rw [←a3] at s4
  have s5 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K (thrX k G par) hk par f (G && par) false hg
  rw [show b0 (base 2400)=G from rfl,ltvX_eq,Nat.xor_self] at s5
  have s6 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par f (G && par) false (base 514) (base 1028) 722 (by omega) f par
    (w_ne base hn _ _ (by omega) (by omega) (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s6
  -- erase the tick word
  have s7 := stepW0Back base hn b0 H K 0 par f (G && par) (f && par)
  have s8 := stepKnownH base hn b0 H K 0 par f (G && par) (f && par) (by omega) a2 hac h1797
  have s9 := stepCopyBack base hn b0 K 0 par f (G && par) (f && par)
  -- one mapped addition to `y/2`
  have s10 := stepNegK base (base 2400) hn b0 0 K 0 par f (G && par) (f && par) hKlt hg
  have s11 := stepLoadKX base (base 2400) hn b0 k 0 (if G then 2^258-1-K else K) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg] at s11
  have kWord : (tkX k G f par+(if G then 2^258-1-K else K))%2^258=Y/2 := by
    rw [Nat.add_comm]; exact a5
  have s12 := stepKAddZero4 base hn b0 (tkX k G f par) (if G then 2^258-1-K else K) 0 par f (G && par) (f && par)
    hac h1797 Y a6 kWord
  rw [kWord] at s12
  have s13 := stepLoadKX base (base 2400) hn b0 k (tkX k G f par) (Y/2) 0 par f (G && par) (f && par) hg
  rw [show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg,Nat.xor_self] at s13
  have s14 := stepMeasFp base hn b0 0 (Y/2) 0 par f (G && par)
  have s15 := stepMeasGp base (base 2400) hn b0 0 (Y/2) 0 par f false gm (g_ne base hn (base 2400) hg 721 (by omega))
  -- rotate and parity
  have s16 := stepRotL base hn b0 0 (Y/2) 0 par f false false (by rw [p_val] at a6; omega)
  have s17 := stepParBack base (base 2400) hn b0 k (Y/2) par f hg
  rw [show b0 (base 2400)=G from rfl,←a7,show 2*(Y/2)+(decide (Y%2=1)).toNat=Y by
    rcases Nat.mod_two_eq_zero_or_one Y with hy|hy <;> simp [hy] <;> omega] at s17
  -- erase the flag
  have s18 := stepMaskT base hn b0 0 Y 0 false f false false (base 2400) G gT (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm)
    (2^256-1-k) (by omega)
  have s19 := stepNotT base hn b0 0 Y (0^^^(if G then 2^256-1-k else 0)) false f false false
  have hT (G' : Bool) : 2^256-1-(0^^^(if G' then 2^256-1-k else 0))=(if G' then k else 2^256-1) := by
    rw [p_val] at hk
    cases G'
    · simp
    · simp only [if_true, Nat.zero_xor]
      omega
  rw [hT G] at s19
  have s20 := stepEraseF base hn b0 0 Y (if G then k else 2^256-1) false f false false hac h1797
    (by rw [p_val] at a6; omega) a8
  have s21 := stepNotT base hn b0 0 Y (if G then k else 2^256-1) false false false false
  have s22 := stepMaskT base hn b0 0 Y (2^256-1-(if G then k else 2^256-1)) false false false false (base 2400) G gT
    (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm) (2^256-1-k) (by omega)
  have hT2 (G' : Bool) : (2^256-1-(if G' then k else 2^256-1))^^^(if G' then 2^256-1-k else 0)=0 := by
    cases G' <;> simp [Nat.xor_self]
  rw [hT2 G] at s22
  have oldErase:=s18.seq (s19.seq (s20.seq (s21.seq s22)))
  have ncin:base 1797∉E1Merge.mutL base:=by decide +kernel
  have erase : Triple (MF base b0 0 Y 0 false f false false) (eraseOdd base (base 2400) k)
      (MF base b0 0 Y 0 false false false false) := by
    intro s m hs
    rw [eraseOdd_eq k (by rw [p_val] at hk;omega) he s m hs.2.2.1
      ((hs.2.2.2.2.2.2.2 _ ncin).trans h1797)]
    simpa only [ExitMerge.eraseF,List.append_assoc] using oldErase s m hs
  have t:=s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq
    (s12.seq (s13.seq (s14.seq (s15.seq (s16.seq (s17.seq erase))))))))))))))))
  unfold programOdd ExitMerge.fPart ExitMerge.eraseH ExitMerge.addPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

theorem MF_unique (w:Nat→Wire) (b:BasisState) (H X T:Nat) (par f gp fp:Bool)
    (s t:BasisState) (hs:MF w b H X T par f gp fp s) (ht:MF w b H X T par f gp fp t) : s=t := by
  have hH:∀q∈hR w,s q=t q:=(regValue_eq_iff _ _ _).mp (hs.1.trans ht.1.symm)
  have hX:∀q∈kR w,s q=t q:=(regValue_eq_iff _ _ _).mp (hs.2.1.trans ht.2.1.symm)
  have hT:∀q∈tR w,s q=t q:=(regValue_eq_iff _ _ _).mp (hs.2.2.1.trans ht.2.2.1.symm)
  funext q
  by_cases A:q∈hR w
  · exact hH q A
  by_cases B:q∈kR w
  · exact hX q B
  by_cases C:q∈tR w
  · exact hT q C
  by_cases D:q=w 1028
  · subst q;exact hs.2.2.2.1.trans ht.2.2.2.1.symm
  by_cases E:q=w 514
  · subst q;exact hs.2.2.2.2.1.trans ht.2.2.2.2.1.symm
  by_cases F:q=w 721
  · subst q;exact hs.2.2.2.2.2.1.trans ht.2.2.2.2.2.1.symm
  by_cases G:q=w 722
  · subst q;exact hs.2.2.2.2.2.2.1.trans ht.2.2.2.2.2.2.1.symm
  have off:q∉mutL w:=by simp [mutL,A,B,C,D,E,F,G]
  exact (hs.2.2.2.2.2.2.2 q off).trans (ht.2.2.2.2.2.2.2 q off).symm

section Keep
variable (w:Nat→Wire) (g:Wire) (hn:(skywalkPoolWires w).Nodup)
include hn
theorem stepParBackKeep (b0 : BasisState) (k V : Nat) (par f gp : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 0 (2*V) 0 par f gp false) (parBack w g k)
      (MF w b0 0 (2*V+(par ^^ (b0 g && decide (k%2=1)) ^^ f).toNat) 0 false f gp false) := by
  have gm := g_mut w g hn hg
  have g1028 : g≠w 1028 := g_ne w hn g hg 1028 (by omega)
  have g770 : g≠w 770 := g_ne w hn g hg 770 (by omega)
  have e1 : w 770≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e2 : w 514≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e3 : w 1028≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e4 : w 514≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have gv (H X T : Nat) (par f gp fp : Bool) : ∀s : BasisState,MF w b0 H X T par f gp fp s → s g=b0 g :=
    fun s h => h.2.2.2.2.2.2.2 g gm
  have lb (b par' : Bool) : ∀s : BasisState,MF w b0 0 (2*V+b.toNat) 0 par' f gp false s → s (w 770)=b := by
    intro s h; have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; cases b <;> simp
  apply Triple.conseq (fun s h => by rw [show 2*V=2*V+(false).toNat by simp] at h; exact h) ?_ (fun s h => h)
  by_cases hk : k%2=1
  · rw [parBack,if_pos hk,if_pos hk]
    have t := (stepLowCX w hn b0 0 V 0 false par f gp false (w 1028) par e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f gp false g (b0 g) g770 (gv _ _ _ _ _ _ _)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f gp false (w 514) f e4 (fun s h => h.2.2.2.2.1)).seq
      ((stepParCX w hn b0 0 _ 0 par f gp false (w 770) _ e1 (lb _ par)).seq
      ((stepParCX w hn b0 0 _ 0 _ f gp false g (b0 g) g1028 (gv _ _ _ _ _ _ _)).seq
      (stepParCX w hn b0 0 _ 0 _ f gp false (w 514) f e2 (fun s h => h.2.2.2.2.1))))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    have e : (((par ^^ (((false ^^ par) ^^ b0 g) ^^ f)) ^^ b0 g) ^^ f)=false := by
      cases par <;> cases b0 g <;> cases f <;> rfl
    rw [e] at h
    have e' : (((false ^^ par) ^^ b0 g) ^^ f)=(par ^^ (b0 g && decide (k%2=1)) ^^ f) := by
      simp [hk]
    rw [e'] at h
    exact h
  · rw [parBack,if_neg hk,if_neg hk]
    try simp only [List.nil_append,List.append_nil]
    have t := (stepLowCX w hn b0 0 V 0 false par f gp false (w 1028) par e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f gp false (w 514) f e4 (fun s h => h.2.2.2.2.1)).seq
      ((stepParCX w hn b0 0 _ 0 par f gp false (w 770) _ e1 (lb _ par)).seq
      (stepParCX w hn b0 0 _ 0 _ f gp false (w 514) f e2 (fun s h => h.2.2.2.2.1))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    have e : ((par ^^ ((false ^^ par) ^^ f)) ^^ f)=false := by
      cases par <;> cases f <;> rfl
    rw [e] at h
    have e' : ((false ^^ par) ^^ f)=(par ^^ (b0 g && decide (k%2=1)) ^^ f) := by
      simp [hk]
    rw [e'] at h
    exact h


theorem MF_put_alpha (b:BasisState) (H X T:Nat) (par f gp fp v:Bool) (s:State)
    (hs:MF w b H X T par f gp fp s.basis) :
    MF w b H X T par f v fp (put s (w 721) v).basis := by
  have h:=stepBit w hn b H X T par f gp fp s (put s (w 721) v) 721 (by omega) hs
    (fun q hq=>by simp [put,writeBit,hq])
  simpa [put,writeBit] using h

theorem stepRetainGp (b:BasisState) (H X T:Nat) (par f:Bool) (hg:g∉skywalkPoolWires w) :
    Triple (MF w b H X T par f (b g && par) false)
      [.CX (w 514) (w 721),.measureX (w 722) [] []]
      (MF w b H X T par f ((b g && par) ^^ f) false) := by
  intro s m hs
  have gm:=g_mut w g hn hg
  have known:s.basis (w 721)=(s.basis g && s.basis (w 1028)):=by
    rw [hs.2.2.2.2.2.1,hs.2.2.2.1,hs.2.2.2.2.2.2.2 g gm]
  have eq:=retain_product g (w 1028) (w 514) (w 721) (w 722)
    (g_ne w hn g hg 721 (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) s m m hs.2.2.2.2.2.2.1 known
  rw [eq]
  have old:=stepMeasGp w g hn b H X T par f false gm (g_ne w hn g hg 721 (by omega)) s m hs
  have frame:=MF_put_alpha w hn b H X T par f false false ((b g && par) ^^ f) _ old.2
  rw [hs.2.2.2.2.2.2.2 g gm,hs.2.2.2.1,hs.2.2.2.2.1]
  exact ⟨old.1,frame⟩

end Keep

theorem eraseF_step (k Y:Nat) (hk:k<p) (a6:Y<p) (b0:BasisState) (f:Bool)
    (hac:∀q∈aC base,b0 q=false) (h1797:b0 (base 1797)=false)
    (a8:f=decide ((if b0 (base 2400) then k else 2^256-1)<Y)) :
    Triple (MF base b0 0 Y 0 false f false false) (eraseF base (base 2400) k)
      (MF base b0 0 Y 0 false false false false) := by
  let G:=b0 (base 2400)
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  have gm:=g_mut base (base 2400) hn hg
  have gT:=g_out base hn (base 2400) hg 1029 256 (by omega)
  have s18 := stepMaskT base hn b0 0 Y 0 false f false false (base 2400) G gT (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm)
    (2^256-1-k) (by omega)
  have s19 := stepNotT base hn b0 0 Y (0^^^(if G then 2^256-1-k else 0)) false f false false
  have hT (G' : Bool) : 2^256-1-(0^^^(if G' then 2^256-1-k else 0))=(if G' then k else 2^256-1) := by
    rw [p_val] at hk
    cases G'
    · simp
    · simp only [if_true, Nat.zero_xor]
      omega
  rw [hT G] at s19
  have s20 := stepEraseF base hn b0 0 Y (if G then k else 2^256-1) false f false false hac h1797
    (by rw [p_val] at a6; omega) a8
  have s21 := stepNotT base hn b0 0 Y (if G then k else 2^256-1) false false false false
  have s22 := stepMaskT base hn b0 0 Y (2^256-1-(if G then k else 2^256-1)) false false false false (base 2400) G gT
    (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm) (2^256-1-k) (by omega)
  have hT2 (G' : Bool) : (2^256-1-(if G' then k else 2^256-1))^^^(if G' then 2^256-1-k else 0)=0 := by
    cases G' <;> simp [Nat.xor_self]
  rw [hT2 G] at s22

  simpa only [eraseF,List.append_assoc] using s18.seq (s19.seq (s20.seq (s21.seq s22)))

def eraseEven (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  erasePrefixMoved g (w 721) (eraseLayout w).src (eraseLayout w).out ((eraseLayout w).carry.take 255)
    (eraseLayout w).cin (eraseLayout w).flag (2^256-1-k)

theorem eraseEven_step (k Y:Nat) (hk:k<p) (he:k%2=0) (hY:Y<p) (b:BasisState) (f:Bool)
    (hac:∀q∈aC base,b q=false) (h1797:b (base 1797)=false)
    (hf:f=decide ((if b (base 2400) then k else 2^256-1)<Y)) :
    Triple (MF base b 0 Y 0 false f (b (base 2400) && decide (Y%2=1)) false)
      (eraseEven base (base 2400) k) (MF base b 0 Y 0 false false false false) := by
  intro s m hs
  let z:=put s (base 721) false
  have hz:MF base b 0 Y 0 false f false false z.basis:=
    MF_put_alpha base base_pool_nodup b 0 Y 0 false f _ false false s hs
  have old:=eraseF_step k Y hk hY b f hac h1797 hf z m hz
  have pc:(2^256-1-k)%2=1:=by rw [p_val] at hk;omega
  have outcin:base 1797∉mutL base:=by decide +kernel
  have outcarry:∀q∈hC2 base,q∉mutL base:=by
    intro q hq
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb base base_pool_nodup i 0 258 (by omega) (by omega) (by omega),
      nb base base_pool_nodup i 770 258 (by omega) (by omega) (by omega)⟩,
      nb base base_pool_nodup i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩
    all_goals exact w_ne base base_pool_nodup _ _ (by omega) (by omega) (by omega)
  have carry:∀q∈(eraseLayout base).carry,z.basis q=false:=by
    intro q hq
    exact (hz.2.2.2.2.2.2.2 q (outcarry q hq)).trans
      (hac q (blk_sub base 1540 256 1540 257 (by omega) (by omega) q hq))
  have ci:z.basis (base 1797)=false:=(hz.2.2.2.2.2.2.2 _ outcin).trans h1797
  have e:=eraseMoved_layout_eq (eraseLayout base) (base 2400) (eraseLayout_widths base)
    eraseLayout_nodup (2^256-1-k) pc z m hz.2.2.1 ci hz.2.2.2.2.2.1 carry
  have prod:(z.basis (base 2400) && z.basis (EntryFuse.lowBit (eraseLayout base)))=
      (b (base 2400) && decide (Y%2=1)):=by
    have lb:EntryFuse.lowBit (eraseLayout base)=base 770:=by rfl
    rw [lb,low_bit base base_pool_nodup b 0 Y 0 false f false false z.basis hz,
      hz.2.2.2.2.2.2.2 _ (g_mut base (base 2400) base_pool_nodup E1QubitPlacement.g2400)]
  have restore:put z (base 721) (b (base 2400) && decide (Y%2=1))=s:=by
    apply State.extensionality
    · rfl
    funext q
    by_cases h:q=base 721
    · subst q;simp [z,put,writeBit,hs.2.2.2.2.2.1]
    · simp [z,put,writeBit,h]
  rw [prod,←eraseF_eq] at e
  change run (eraseEven base (base 2400) k) m
    (put z (base 721) (b (base 2400) && decide (Y%2=1)))=run (eraseF base (base 2400) k) m z at e
  rw [restore] at e
  rw [e]
  exact old

def addPartKeep (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  FastConst.maskedNot g (kR w)++loadKX w g k++Verifier.Leaf4.zero4KAdd w++loadKX w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  [.CX (w 514) (w 721),.measureX (w 722) [] []]

def programEven (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  ExitMerge.fPart w g k++ExitMerge.eraseH w++addPartKeep w g k++
    rotateLeft (kR w)++ExitMerge.parBack w g k++eraseEven w g k

theorem programEven_triple (k : Nat) (hk : k<p) (he:k%2=0) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hac : ∀q∈aC base,b0 q=false) (h1797 : b0 (base 1797)=false) :
    let G := b0 (base 2400)
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let Y := if G then (k+p-X)%p else X
    Triple (MF base b0 (2*H+(!par).toNat) K 0 par false false false) (programEven base (base 2400) k)
      (MF base b0 0 Y 0 false false false false) := by
  intro G par H K Y
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  obtain ⟨a1,a2,a3,a5,a6,a7,a8⟩ := archX k X hk hX G
  let f := G && decide (k<X)
  change H<2^256 at a1
  change (dInv par+H)%2^257=K%2^257 at a2
  change f=(decide (H<thrX k G par) ^^ G) at a3
  change ((if G then 2^258-1-K else K)+tkX k G f par)%2^258=Y/2 at a5
  change Y<p at a6
  change decide (Y%2=1)=(par ^^ (G && decide (k%2=1)) ^^ f) at a7
  change f=decide ((if G then k else 2^256-1)<Y) at a8
  have gm := g_mut base (base 2400) hn hg
  have hp' := p_val
  have hfg : f=true → G=true := by
    intro hf; simp only [f,Bool.and_eq_true] at hf; exact hf.1
  have hKlt : K<2^258 := Nat.mod_lt _ (by norm_num)
  have hpb : (!par).toNat<2 := Bool.toNat_lt _
  have gT : (base 2400)∉tR base := g_out base hn (base 2400) hg 1029 256 (by omega)
  -- threshold compare
  have s1 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par false false false (base 2400) (base 1028) 721 (by omega) G par
    (g_ne base hn (base 2400) hg 721 (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s1
  have s2 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K 0 hk par false (G && par) false hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,ltvX_eq] at s2
  have s3 := stepCmpH base hn b0 H (!par).toNat K (thrX k G par) par (G && par) false a1 hpb hac h1797
  have s4 := stepFlagCX base hn b0 (2*H+(!par).toNat) K (thrX k G par) par (decide (H<thrX k G par))
    (G && par) false (base 2400) G (g_ne base hn (base 2400) hg 514 (by omega)) (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm)
  rw [←a3] at s4
  have s5 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K (thrX k G par) hk par f (G && par) false hg
  rw [show b0 (base 2400)=G from rfl,ltvX_eq,Nat.xor_self] at s5
  have s6 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par f (G && par) false (base 514) (base 1028) 722 (by omega) f par
    (w_ne base hn _ _ (by omega) (by omega) (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s6
  -- erase the tick word
  have s7 := stepW0Back base hn b0 H K 0 par f (G && par) (f && par)
  have s8 := stepKnownH base hn b0 H K 0 par f (G && par) (f && par) (by omega) a2 hac h1797
  have s9 := stepCopyBack base hn b0 K 0 par f (G && par) (f && par)
  -- one mapped addition to `y/2`
  have s10 := stepNegK base (base 2400) hn b0 0 K 0 par f (G && par) (f && par) hKlt hg
  have s11 := stepLoadKX base (base 2400) hn b0 k 0 (if G then 2^258-1-K else K) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg] at s11
  have kWord : (tkX k G f par+(if G then 2^258-1-K else K))%2^258=Y/2 := by
    rw [Nat.add_comm]; exact a5
  have s12 := stepKAddZero4 base hn b0 (tkX k G f par) (if G then 2^258-1-K else K) 0 par f (G && par) (f && par)
    hac h1797 Y a6 kWord
  rw [kWord] at s12
  have s13 := stepLoadKX base (base 2400) hn b0 k (tkX k G f par) (Y/2) 0 par f (G && par) (f && par) hg
  rw [show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg,Nat.xor_self] at s13
  have s14 := stepMeasFp base hn b0 0 (Y/2) 0 par f (G && par)
  have s15 := stepRetainGp base (base 2400) hn b0 0 (Y/2) 0 par f hg
  -- rotate and parity
  have s16 := stepRotL base hn b0 0 (Y/2) 0 par f ((G && par) ^^ f) false (by rw [p_val] at a6; omega)
  have s17 := stepParBackKeep base (base 2400) hn b0 k (Y/2) par f ((G && par) ^^ f) hg
  rw [show b0 (base 2400)=G from rfl,←a7,show 2*(Y/2)+(decide (Y%2=1)).toNat=Y by
    rcases Nat.mod_two_eq_zero_or_one Y with hy|hy <;> simp [hy] <;> omega] at s17
  have aprod:((G && par) ^^ f)=(G && decide (Y%2=1)):=by
    rw [a7]
    simp only [he,show ¬(0:Nat)=1 by decide,decide_false,Bool.and_false,Bool.xor_false]
    cases hG:G <;> cases hp:par <;> cases hf:f <;> simp [hG,hp,hf] at hfg ⊢
  have erase:=eraseEven_step k Y hk he a6 b0 f hac h1797 a8
  change Triple (MF base b0 0 Y 0 false f (G && decide (Y%2=1)) false) _ _ at erase
  rw [←aprod] at erase
  have t:=s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq
    (s12.seq (s13.seq (s14.seq (s15.seq (s16.seq (s17.seq erase))))))))))))))))
  unfold programEven ExitMerge.fPart ExitMerge.eraseH addPartKeep
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

theorem eraseEven_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (eraseEven w g k)+1=toffoliCount (eraseF w g k) ∧
    measurementCount (eraseEven w g k)=measurementCount (eraseF w g k) ∧
    gateSlots (eraseEven w g k)+6=gateSlots (eraseF w g k) := by
  rw [eraseF_eq]
  exact eraseMoved_layout_counts (eraseLayout w) g (w 721) (eraseLayout_widths w) (2^256-1-k)

theorem addPartKeep_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (addPartKeep w g k)=toffoliCount (addPart w g k) ∧
    measurementCount (addPartKeep w g k)=measurementCount (addPart w g k) ∧
    gateSlots (addPartKeep w g k)=gateSlots (addPart w g k) := by
  simp only [addPartKeep,addPart,toffoliCount_append,measurementCount_append,gateSlots_append]
  simp [toffoliCount,measurementCount,gateSlots,instructionSlots]

theorem programOdd_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (programOdd w g k)+1=toffoliCount (ExitMerge.program w g k) ∧
    measurementCount (programOdd w g k)=measurementCount (ExitMerge.program w g k) ∧
    gateSlots (programOdd w g k)+8=gateSlots (ExitMerge.program w g k) := by
  have h:=eraseOdd_counts w g k
  simp only [programOdd,ExitMerge.program,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem programEven_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (programEven w g k)+1=toffoliCount (ExitMerge.program w g k) ∧
    measurementCount (programEven w g k)=measurementCount (ExitMerge.program w g k) ∧
    gateSlots (programEven w g k)+6=gateSlots (ExitMerge.program w g k) := by
  have h:=eraseEven_counts w g k
  have a:=addPartKeep_counts w g k
  simp only [programEven,ExitMerge.program,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

def programAll (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  if k%2=1 then programOdd w g k else programEven w g k

theorem programAll_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (programAll w g k)+1=toffoliCount (ExitMerge.program w g k) ∧
    measurementCount (programAll w g k)=measurementCount (ExitMerge.program w g k) ∧
    gateSlots (programAll w g k)≤gateSlots (ExitMerge.program w g k) := by
  unfold programAll
  split_ifs
  · have h:=programOdd_counts w g k;omega
  · have h:=programEven_counts w g k;omega

theorem programAll_triple (k:Nat) (hk:k<p) (b:BasisState) (X:Nat) (hX:X<p)
    (hac:∀q∈aC base,b q=false) (hc:b (base 1797)=false) :
    let G:=b (base 2400)
    let par:=decide (X%2=1)
    let H:=X/2+(if par then hConstant else 0)
    let K:=(X/2+kConstant false par)%2^258
    let Y:=if G then (k+p-X)%p else X
    Triple (MF base b (2*H+(!par).toNat) K 0 par false false false)
      (programAll base (base 2400) k) (MF base b 0 Y 0 false false false false) := by
  unfold programAll
  split_ifs with he
  · exact programOdd_triple k hk he b X hX hac hc
  · exact programEven_triple k hk (by omega) b X hX hac hc

theorem programAll_run (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (initial field : State) (mF m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed base) 0 X initial.basis)
    (ht : regValue (tR base) initial.basis=0) (h514 : initial.basis (base 514)=false)
    (h721 : initial.basis (base 721)=false) (h722 : initial.basis (base 722)=false)
    (hphase : field.phase=(run (NativeFirstDirect.forward base) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires base,
      field.basis q=(run (NativeFirstDirect.forward base) mF initial).basis q) :
    (run (programAll base (base 2400) k) m field).phase=initial.phase ∧
    regValue (kR base) (run (programAll base (base 2400) k) m field).basis=(if field.basis (base 2400) then (k+p-X)%p else X) ∧
    (∀q∈skywalkPoolWires base,q∉kR base → (run (programAll base (base 2400) k) m field).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires base → (run (programAll base (base 2400) k) m field).basis q=field.basis q) := by
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec base hn X hX initial mF hin
  have e770 : initial.basis (base 770)=decide (X%2=1) := by
    have sp := kR_split base hn initial.basis
    have hb : regValue (kR base) initial.basis=X := hin.b
    rw [hb] at sp
    cases h : initial.basis (base 770) <;> simp [h] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  have inPool (a n : Nat) (ha : a+n≤1798) : ∀q∈wireBlock base a n,q∈skywalkPoolWires base :=
    blk_sub base a n 0 1798 (by omega) ha
  have wPool (i : Nat) (hi : i<1798) : base i∈skywalkPoolWires base :=
    List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  have keepI (i : Nat) (hi : i < 1798) (h1 : 257 ≤ i) (h2 : i < 770 ∨ 1028 < i) :
      field.basis (base i)=initial.basis (base i) := by
    rw [hpool _ (wPool i hi)]
    apply zrest
    simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
    exact ⟨⟨nb base hn i 0 257 hi (by omega) (by omega),nb base hn i 770 258 hi (by omega) (by omega)⟩,
      w_ne base hn i 1028 hi (by omega) (by omega)⟩
  have hR0 : regValue (hR base) field.basis=
      2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat := by
    rw [regValue_congr (hR base) field.basis _ (fun q hq => hpool q (inPool 0 258 (by omega) q hq))]
    exact zh
  have kR0 : regValue (kR base) field.basis=(X/2+kConstant false (decide (X%2=1)))%2^258 := by
    rw [regValue_congr (kR base) field.basis _ (fun q hq => hpool q (inPool 770 258 (by omega) q hq))]
    exact zk
  have tR0 : regValue (tR base) field.basis=0 := by
    rw [regValue_congr (tR base) field.basis initial.basis (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact keepI i (by omega) (by omega) (by omega))]
    exact ht
  have f1028 : field.basis (base 1028)=decide (X%2=1) := (hpool _ (wPool 1028 (by omega))).trans z1028
  have f514 : field.basis (base 514)=false := (keepI 514 (by omega) (by omega) (by omega)).trans h514
  have f721 : field.basis (base 721)=false := (keepI 721 (by omega) (by omega) (by omega)).trans h721
  have f722 : field.basis (base 722)=false := (keepI 722 (by omega) (by omega) (by omega)).trans h722
  have hac : ∀q∈aC base,field.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [keepI i (by omega) (by omega) (by omega)]
    exact (regValue_zero _ _).mp hin.carry _ hq
  have h1797 : field.basis (base 1797)=false := (keepI 1797 (by omega) (by omega) (by omega)).trans hin.cin
  have mf0 : MF base field.basis (2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat)
      ((X/2+kConstant false (decide (X%2=1)))%2^258) 0 (decide (X%2=1)) false false false field.basis :=
    ⟨hR0,kR0,tR0,f1028,f514,f721,f722,fun _ _ => rfl⟩
  obtain ⟨tp,o1,o2,o3,o4,o5,o6,o7,o8⟩ := programAll_triple k hk field.basis X hX hac h1797 field m mf0
  have outMut (q : Wire) (hq : q∉skywalkPoolWires base) : q∉mutL base := fun h => hq (mutL_pool base q h)
  refine ⟨tp.trans (hphase.trans zp),o2,?_,fun q hq => o8 q (outMut q hq)⟩
  intro q hq hk'
  by_cases qh : q∈hR base
  · rw [(regValue_zero _ _).mp o1 q qh]
    exact ((regValue_zero _ _).mp hin.a q qh).symm
  by_cases qt : q∈tR base
  · rw [(regValue_zero _ _).mp o3 q qt]
    exact ((regValue_zero _ _).mp ht q qt).symm
  by_cases q1 : q=base 1028
  · rw [q1,o4]; exact hin.one.symm
  by_cases q2 : q=base 514
  · rw [q2,o5]; exact h514.symm
  by_cases q3 : q=base 721
  · rw [q3,o6]; exact h721.symm
  by_cases q4 : q=base 722
  · rw [q4,o7]; exact h722.symm
  have nm : q∉mutL base := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,hk'⟩,qt⟩,q1,q2,q3,q4⟩
  rw [o8 q nm,hpool q hq]
  apply zrest
  simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
  exact ⟨⟨fun h' => qh (blk_sub base 0 257 0 258 (by omega) (by omega) q h'),hk'⟩,q1⟩

theorem eraseOdd_wires (w:Nat→Wire) (g:Wire) (k:Nat) :
    wires (eraseOdd w g k)⊆wires (eraseF w g k) := by
  rw [eraseF_eq]
  exact erase_layout_wires (eraseLayout w) g (eraseLayout_widths w) (2^256-1-k)

theorem eraseEven_wires (w:Nat→Wire) (g:Wire) (k:Nat) :
    wires (eraseEven w g k)⊆wires (eraseF w g k)∪{w 721} := by
  rw [eraseF_eq]
  exact eraseMoved_layout_wires (eraseLayout w) g (eraseLayout_widths w) (2^256-1-k)

theorem addPartKeep_wires (w:Nat→Wire) (g:Wire) (k:Nat) :
    wires (addPartKeep w g k)⊆wires (addPart w g k) := by
  let P:=FastConst.maskedNot g (kR w)++loadKX w g k++Verifier.Leaf4.zero4KAdd w++loadKX w g k
  let A:Program:=[.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
    [.CX (w 514) (w 721),.measureX (w 722) [] []]
  let B:Program:=[.measureX (w 722) [] [.CZ (w 514) (w 1028)],
    .measureX (w 721) [] [.CZ g (w 1028)]]
  have tail:wires A⊆wires B:=by
    intro a H
    simp [A,B,wires,Instr.wires,correctionWires] at H ⊢
    tauto
  have whole:wires (P++A)⊆wires (P++B):=by
    rw [show wires (P++A)=wires P∪wires A from wires_append P A,
      show wires (P++B)=wires P∪wires B from wires_append P B]
    exact Finset.union_subset_union (Finset.Subset.refl _) tail
  simpa only [P,A,B,addPartKeep,addPart,List.append_assoc] using whole

theorem programAll_wires (w:Nat→Wire) (g:Wire) (k:Nat) :
    wires (programAll w g k)⊆wires (ExitMerge.program w g k) := by
  have odd:=eraseOdd_wires w g k
  have even:=eraseEven_wires w g k
  have add:=addPartKeep_wires w g k
  have alpha:w 721∈wires (addPart w g k):=by
    simp only [addPart,wires_append,Finset.mem_union]
    right
    simp [wires,Instr.wires,correctionWires]
  unfold programAll
  split_ifs
  · simp only [programOdd,ExitMerge.program,wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _) odd
  · simp only [programEven,ExitMerge.program,wires_append]
    intro q h
    have C:=add (a:=q)
    have E:=even (a:=q)
    simp only [Finset.mem_union,Finset.mem_singleton] at h C E ⊢
    by_cases e:q=w 721
    · subst q;tauto
    · tauto

theorem eraseOdd_physical (k:Nat) (h:GatePhysical (eraseF base (base 2400) k)) :
    GatePhysical (eraseOdd base (base 2400) k) := by
  rw [eraseF_eq] at h
  exact erase_layout_physical (eraseLayout base) (base 2400) (eraseLayout_widths base) (2^256-1-k) h

theorem eraseEven_physical (k:Nat) (h:GatePhysical (eraseF base (base 2400) k)) :
    GatePhysical (eraseEven base (base 2400) k) := by
  rw [eraseF_eq] at h
  exact eraseMoved_layout_physical (eraseLayout base) (base 2400) (eraseLayout_widths base)
    eraseLayout_nodup (2^256-1-k) h

theorem addPartKeep_physical (k:Nat) (old:GatePhysical (addPart base (base 2400) k)) :
    GatePhysical (addPartKeep base (base 2400) k) := by
  have tail:GatePhysical ([Instr.measureX (base 722) [] [Correction.CZ (base 514) (base 1028)]]++
      [Instr.CX (base 514) (base 721),Instr.measureX (base 722) [] []]):=by
    simp [GatePhysical,PhysicalInstr,ProperGate,base]
  simp only [addPart,gatePhysical_append] at old
  simp only [addPartKeep,gatePhysical_append] at tail ⊢
  tauto

theorem programAll_physical (k:Nat) : GatePhysical (programAll base (base 2400) k) := by
  have old:=ExitMerge.program_physical base (base 2400) base_pool_nodup E1QubitPlacement.g2400 k
  simp only [ExitMerge.program,gatePhysical_append] at old
  have erase:GatePhysical (eraseF base (base 2400) k):=old.2
  have add:GatePhysical (addPart base (base 2400) k):=old.1.1.1.2
  have oddP:=eraseOdd_physical k erase
  have evenP:=eraseEven_physical k erase
  have addP:=addPartKeep_physical k add
  unfold programAll
  split_ifs
  · simp only [programOdd,gatePhysical_append]
    tauto
  · simp only [programEven,gatePhysical_append]
    tauto

end ECDSAAdd.Entrant.ParityXExit
