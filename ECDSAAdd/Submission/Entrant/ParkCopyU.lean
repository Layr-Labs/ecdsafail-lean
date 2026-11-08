import ECDSAAdd.Submission.Entrant.MainPart04

/-! Ten-host parking for the 128-bit A leaf: the nine ParkCopy ext hosts plus product[256] (eU),
which the dual-carry A body never touches and which is zero at the start of the A branch. -/



set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem eU_mem_product (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) : eU L∈L.core.product :=
  eReg_product L _ (eK_mem L hw).2.1

theorem eU_off_aux (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (q : Wire) (hq:q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,L.core.workHigh,
      L.core.cin,L.core.normFlag,L.core.modFlag]) : eU L≠q := by
  intro eq
  have off:=(L.pairAuxAway hn q hq).1
  exact off (eq ▸ eU_mem_product L hw)


theorem eU_fresh_domain (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    eU L∉L.core.cin::(hiReg L++accReg L++accZ L++accBank L) := by
  have off:=eU_off_aux L hw hn
  intro h
  simp only [List.mem_cons,List.mem_append] at h
  rcases h with h|(((h|h)|h)|h)
  · exact off _ (by simp) h
  · exact (eReg_away L hn _ (eK_mem L hw).2.1).2.2 h
  · exact off _ (by simp [accReg_work L _ h]) rfl
  · rcases accZ_mem L _ h with h|h
    · exact off _ (by simp [h]) rfl
    · exact off _ (by simp [List.mem_of_mem_drop h]) rfl
  · exact off _ (by simp [List.mem_of_mem_take h]) rfl


theorem eU_ne_sumCarry (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    eU L≠L.core.sumCarry := by
  intro eq
  apply ParkCarryDevelop.sumCarry_away L hn
  have h:=eU_mem_product L hw
  simp [ParkCarryDevelop.restWires,←eq,h]


theorem eU_off_acore (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    eU L∉wires (qprogTq L.measuredCore SquareReduction.p) := by
  intro h
  have old:=(QRel.qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)).1 h
  have hh:=List.mem_toFinset.mp (QCore.qprog_support L.measuredCore SquareReduction.p old)
  simp only [measuredCore,MeasuredCanonicalModLayout.wires,foldCarry,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hh
  have flat : eU L∈L.core.work ∨ eU L∈L.core.out ∨ eU L∈L.foldPad ∨
      eU L=L.core.productHigh ∨ eU L=L.core.workHigh ∨ eU L=L.core.outHigh ∨ eU L=L.core.cin ∨ eU L=L.core.modFlag := by
    simpa only [or_assoc] using hh
  have off:=eU_off_aux L hw hn
  rcases flat with h|h|h|h|h|h|h|h
  · exact off _ (by simp [h]) rfl
  · exact (eReg_away L hn _ (eK_mem L hw).2.1).1 h
  · exact off _ (by simp [h]) rfl
  · exact off _ (by simp) h
  · exact off _ (by simp) h
  · exact off _ (by simp) h
  · exact off _ (by simp) h
  · exact off _ (by simp) h


theorem eU_off_amiddle (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) : eU L∉wires (aMiddle L g) := by
  have ne:eU L≠g := by
    intro e
    apply hg
    have h:=eU_mem_product L hw
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,←e,h]
  have away:eU L∉accReg L := (eReg_away L hn _ (eK_mem L hw).2.1).2.1
  have masks:eU L∉wires (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK) := by
    intro h
    have mem:=maskedConstant_wires_subset g (accReg L) OwnDiagAll12Square.cFlipK h
    simp only [List.mem_toFinset,List.mem_cons] at mem
    exact mem.elim ne away
  simp only [aMiddle,wires_append,Finset.mem_union,not_or]
  exact ⟨masks,eU_off_acore L hw hn,masks⟩


theorem eU_off_cached_build_unbuild (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    eU L∉wires (buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) ∧
    eU L∉wires (unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) := by
  have lens:=acc_lengths L hw
  have fresh:=eU_fresh_domain L hw hn
  have off:=wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (eU L)
    lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) fresh
  have b:=buildCached_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
    lens.1 (hiReg_length L hw) (by omega) (by omega)
  have u:=unbuildConsumed_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
    lens.1 (hiReg_length L hw) (by omega)
  constructor
  · intro h
    exact (Finset.mem_insert.mp (b h)).elim (eU_ne_sumCarry L hw hn) off.1
  · intro h
    exact (Finset.mem_insert.mp (u h)).elim (eU_ne_sumCarry L hw hn) off.2



theorem eU_not_low (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    eU L∉L.core.product.take 256 := by
  have prodND:L.core.product.Nodup := by
    apply List.nodup_iff_count_le_one.mpr;intro q
    have h:=lay_pos L hn q
    omega
  have plen:L.core.product.length=258 := hw.core.product
  have nd:(L.core.product.take 256++L.core.product.drop 256).Nodup := by
    rw [List.take_append_drop]; exact prodND
  have dis:=List.disjoint_of_nodup_append nd
  have memd:eU L∈L.core.product.drop 256 := by
    have ne:(L.core.product.drop 256)≠[] := by
      intro h; have := congrArg List.length h; simp [plen] at this
    simp only [eU]
    cases hx:L.core.product.drop 256 with
    | nil => exact absurd hx ne
    | cons a t => simp
  intro h
  exact dis h memd

theorem eU_off_fold (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (f : MeasuredSquareFold) (hs:∀q∈f.src,q∈L.core.product.take 256) : eU L∉wires (measuredFoldQTq L f) := by
  have cp:=copyRegister_wires_subset none f.src (L.foldDestination f)
  have offc:eU L∉wires (copyRegister none f.src (L.foldDestination f)) := by
    intro h
    have m:=List.mem_toFinset.mp (cp h)
    simp only [Option.toList_none,List.nil_append,List.mem_append] at m
    rcases m with m|m
    · exact eU_not_low L hw hn (hs _ m)
    · have w:eU L∈L.core.work := List.mem_of_mem_drop (List.mem_of_mem_take m)
      exact eU_off_aux L hw hn _ (by simp [w]) rfl
  simp only [measuredFoldQTq,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨offc,eU_off_acore L hw hn⟩,offc⟩

theorem eU_off_aBodyDual (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (c : Wire) (hc:c∉L.wires) : eU L∉wires (aBodyDual L c) := by
  have lens:=acc_lengths L hw
  have cu:=eU_off_cached_build_unbuild L hw hn
  have b:=buildDual_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)
    lens.1 (hiReg_length L hw) (by omega) (by omega)
  have u:=unbuildDual_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)
    lens.1 (hiReg_length L hw) (by omega)
  have ne:eU L≠eV L := fun e=>eV_ne_eU L hw hn e.symm
  have ob:eU L∉wires (buildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)) :=
    fun h=>(Finset.mem_insert.mp (b h)).elim ne cu.1
  have ou:eU L∉wires (unbuildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)) :=
    fun h=>(Finset.mem_insert.mp (u h)).elim ne cu.2
  have neg:eU L∉wires (measuredFoldQTq L (negP L)) :=
    eU_off_fold L hw hn _ (fun q hq=>by simpa [negP] using hq)
  have rot:eU L∉wires (measuredFoldQTq L (rot128F L)) := by
    apply eU_off_fold L hw hn
    intro q hq
    simp only [rot128F,rotated128,List.mem_append] at hq
    rcases hq with hq|hq
    · have e:(L.core.product.take 256).drop 128=(L.core.product.drop 128).take 128 := by
        simp [List.drop_take]
      rw [← e] at hq
      exact List.mem_of_mem_drop hq
    · exact (List.take_subset_take_left _ (by omega)) hq
  simp only [aBodyDual,aFoldDual,wires_append,Finset.mem_union,not_or]
  exact ⟨neg,rot,⟨ob,eU_off_amiddle L hw hn c hc⟩,ou⟩

end ECDSAAdd.Entrant.InverseCarryDevelop

namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem eU_mem_wires (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) : eU L∈L.wires := by
  have h:=eU_mem_product L hw
  simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]

theorem fold_fixes_eU (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (hn:L.wires.Nodup) (ext : List Wire) (hlen:300≤ext.length)
    (away:∀q∈ext,q∉L.wires) :
    SquareCarryLoan719.foldPerm L ext (eU L)=eU L := by
  have ht:SquareCarryLoan719.target L∈L.foldPad := by
    apply List.mem_of_mem_drop
    exact DiagSq.getD_in (LowZero18LowK.ktmp L) 67 (by rw [LowZero18LowK.ktmp_length L hw];omega)
  have hn1:eU L≠SquareCarryLoan719.target L := eU_off_aux L hw hn _ (List.mem_append_left _ (List.mem_append_left _ ht))
  have hn2:eU L≠ext.getD 0 0 := by
    intro h
    exact away (ext.getD 0 0) (DiagSq.getD_in ext 0 (by omega)) (h ▸ eU_mem_wires L hw)
  rw [SquareCarryLoan719.foldPerm_eq L hw]
  exact Equiv.swap_apply_of_ne_of_ne hn1 hn2

/-- `product[256]` is untouched by the fold-renamed dual-carry A body. -/
theorem eU_off_hostedADual (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (hn:L.wires.Nodup) (ext : List Wire) (hlen:300≤ext.length) (away:∀q∈ext,q∉L.wires)
    (c : Wire) (hc:c∉L.wires) :
    eU L∉wires (renameProgram (LowZero18Square.foldPerm L ext)
      (hostedADual L (LowZero18Square.foldPerm L ext) c)) := by
  rw [hostedADual_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away),renameProgram_support]
  intro h
  obtain ⟨a,ha,eq⟩:=Finset.mem_image.mp h
  have fx:=fold_fixes_eU L hw hn ext hlen away
  have : a=eU L := (LowZero18Square.foldPerm L ext).injective (eq.trans fx.symm)
  exact eU_off_aBodyDual L hw hn c hc (this ▸ ha)

end ECDSAAdd.Entrant.InverseCarryDevelop

namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem eU_mem_parkCarry7 (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
    ControlLoan1589BFFold.eU L∈wires (ParkCarry7Develop.body L c) := by
  simp only [ParkCarry7Develop.body,ParkCarry7Develop.fold,wires_append,Finset.mem_union]
  right; right; left; right; right; right; right; left
  simp [ParkCarryDevelop.program, wires]
  left; simp [Instr.wires]

end ECDSAAdd.Entrant.InverseCarryDevelop


/-! Part B: the parked 128-bit leaf and its correctness (appended after part A). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

/-! 118-bit versions of i34-9's inner linear cached copy lemmas (the copy is used on the
first 118 bank bits when the A leaf parks ten bits). Same proofs with the length 119 replaced by 118. -/

theorem conditions_after_prefix118 (c cache x y z : Wire)(src dst : List Wire)
 (ls : src.length=118)(ld : dst.length=118)(nd : (c::(src++dst)).Nodup)
 (xn : x∉dst)(yn : y∉dst)(zn : z∉dst)(s : State)(m : List Bool)
 (bank0 : ∀q∈dst,s.basis q=false)
 (cached : s.basis cache=(s.basis c && s.basis ((src.take 96).headD 0)))
 (hx : s.basis x=((s.basis c && s.basis (src.getD 64 0)) ^^
  (s.basis c && s.basis (src.getD 96 0))))
 (hyz : (s.basis y ^^ s.basis z)=((s.basis c && s.basis (src.getD 65 0)) ^^
  (s.basis c && s.basis (src.getD 97 0)))) :
 let u:=run (copyPrefix c cache src dst) m s
 ((u.basis x ^^ u.basis (dst.getD 64 0))=(u.basis c && u.basis (src.getD 96 0))) ∧
 (((u.basis y ^^ u.basis z) ^^ u.basis (dst.getD 65 0))=
  (u.basis c && u.basis (src.getD 97 0))) := by
 have lens : (src.take 96).length=(dst.take 96).length := by simp [ls,ld]
 have nd0 : (src++dst).Nodup := (List.nodup_cons.mp nd).2
 have ndp : (src.take 96++dst.take 96).Nodup :=
  nd0.sublist (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _))
 have cn : c∉dst := fun h=>(List.nodup_cons.mp nd).1 (List.mem_append_right _ h)
 have sn (q : Wire)(hq : q∈src) : q∉dst :=
  fun hd=>List.disjoint_left.mp (List.nodup_append'.mp nd0).2.2 hq hd
 have getTake (r : List Wire)(hr : r.length=118)(i : Nat)(hi : i<96) :
  (r.take 96).getD i 0=r.getD i 0 := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_take,hr];omega),
   List.getD_eq_getElem _ _ (by omega)]
  simp
 let v:=run (copyRegister (some c) (src.take 96) (dst.take 96)) m s
 have eq : run (copyPrefix c cache src dst) m s=v :=
  CachedSquareCopy.run_eq c cache (src.take 96) (dst.take 96) s m cached
 have raw:=copyRegister_correct (some c) (src.take 96) (dst.take 96) lens ndp
  (by
    intro q h
    have qc : c=q := by simpa using h
    rw [←qc]
    exact fun hd=>cn (List.mem_of_mem_take hd)) s m
 have frame (q : Wire)(hn : q∉dst) : v.basis q=s.basis q :=
  raw.2.1 q (fun hd=>hn (List.mem_of_mem_take hd))
 have bit (i : Nat)(hi : i<96) : v.basis (dst.getD i 0)=
  (s.basis c && s.basis (src.getD i 0)) := by
  have h:=copyRegister_bit c (src.take 96) (dst.take 96) lens ndp
   (fun hd=>cn (List.mem_of_mem_take hd)) s m i (by simp only [List.length_take,ld];omega)
  rw [getTake dst ld i hi,getTake src ls i hi,
   bank0 (dst.getD i 0) (DiagSq.getD_in dst i (by omega))]at h
  simpa only [Bool.false_xor]using h
 have c96 : src.getD 96 0∉dst := sn _ (DiagSq.getD_in src 96 (by omega))
 have c97 : src.getD 97 0∉dst := sn _ (DiagSq.getD_in src 97 (by omega))
 have cancel (a b : Bool) : ((a^^b)^^a)=b := by cases a <;> cases b <;> rfl
 dsimp only
 rw [eq]
 constructor
 · rw [frame x xn,bit 64 (by omega),frame c cn,frame (src.getD 96 0) c96,hx]
   exact cancel _ _
 · rw [frame y yn,frame z zn,bit 65 (by omega),frame c cn,frame (src.getD 97 0) c97,hyz]
   exact cancel _ _

theorem copy_correct118 (c cache x y z : Wire)(src dst : List Wire)
 (ls : src.length=118)(ld : dst.length=118)(nd : (c::(src++dst)).Nodup)
 (xn : x∉dst)(yn : y∉dst)(zn : z∉dst)(s : State)(m : List Bool)
 (bank0 : ∀q∈dst,s.basis q=false)
 (cached : s.basis cache=(s.basis c && s.basis ((src.take 96).headD 0)))
 (hx : s.basis x=((s.basis c && s.basis (src.getD 64 0)) ^^
  (s.basis c && s.basis (src.getD 96 0))))
 (hyz : (s.basis y ^^ s.basis z)=((s.basis c && s.basis (src.getD 65 0)) ^^
  (s.basis c && s.basis (src.getD 97 0)))) :
 run (copy c cache x y z src dst) m s=run (CachedSquareCopy.copy c cache src dst) m s := by
 have nd0 : (src++dst).Nodup := (List.nodup_cons.mp nd).2
 have dn : dst.Nodup := (List.nodup_append'.mp nd0).2.1
 have dm (i : Nat)(hi : i<118) : dst.getD i 0∈dst := DiagSq.getD_in dst i (by omega)
 have dd (i j : Nat)(hi : i<118)(hj : j<118)(ne : i≠j) : dst.getD i 0≠dst.getD j 0 := by
  intro e
  rw [List.getD_eq_getElem dst 0 (n:=i) (by omega),List.getD_eq_getElem dst 0 (n:=j) (by omega)]at e
  exact ne ((List.Nodup.getElem_inj_iff dn).mp e)
 have cn : c∉dst := fun h=>(List.nodup_cons.mp nd).1 (List.mem_append_right _ h)
 have sn : src.getD 97 0∉dst := fun h=>List.disjoint_left.mp
  (List.nodup_append'.mp nd0).2.2 (DiagSq.getD_in src 97 (by omega)) h
 have neq (q : Wire)(hn : q∉dst)(i : Nat)(hi : i<118) : q≠dst.getD i 0 := by
  intro e;apply hn;rw [e];exact dm i hi
 have cond:=conditions_after_prefix118 c cache x y z src dst ls ld nd xn yn zn s m bank0 cached hx hyz
 exact copy_run_eq c cache x y z src dst (by omega) (by omega) s m
  (dd 64 96 (by omega) (by omega) (by omega)) (neq c cn 96 (by omega))
  (neq _ sn 96 (by omega)) (neq y yn 96 (by omega)) (neq z zn 96 (by omega))
  (dd 65 96 (by omega) (by omega) (by omega)) (neq z zn 97 (by omega))
  (dd 65 97 (by omega) (by omega) (by omega)) cond.1 cond.2

theorem copy_counts118 (c cache x y z : Wire)(src dst : List Wire)(ls : src.length=118)(ld : dst.length=118) :
 toffoliCount (copy c cache x y z src dst)+2=toffoliCount (CachedSquareCopy.copy c cache src dst) ∧
 measurementCount (copy c cache x y z src dst)=measurementCount (CachedSquareCopy.copy c cache src dst) := by
 have lp : (src.take 96).length=(dst.take 96).length := by simp [ls,ld]
 have lt : (src.drop 98).length=(dst.drop 98).length := by simp [ls,ld]
 have cp:=copyRegister_counts (some c) (src.take 96) (dst.take 96) lp
 have ct:=copyRegister_counts (some c) (src.drop 98) (dst.drop 98) lt
 have co:=copyRegister_counts (some c) src dst (by omega)
 have pc : toffoliCount (copyPrefix c cache src dst)+1=96 := by
  have h:=CachedSquareCopy.counts_nonempty c cache (src.take 96) (dst.take 96)
   (by simp [ls]) (by simp [ld])
  have e : toffoliCount (copyRegister (some c) (src.take 96) (dst.take 96))=96 := by simpa [ls,ld]using cp.1
  exact h.trans e
 have oc : toffoliCount (CachedSquareCopy.copy c cache src dst)+1=118 := by
  have h:=CachedSquareCopy.counts_nonempty c cache src dst (by omega) (by omega)
  have e : toffoliCount (copyRegister (some c) src dst)=118 := by simpa [ls]using co.1
  exact h.trans e
 have tc : toffoliCount (copyRegister (some c) (src.drop 98) (dst.drop 98))=20 := by simpa [ls,ld]using ct.1
 have mp:=prefix_measurements c cache src dst (by omega)
 have mo : measurementCount (CachedSquareCopy.copy c cache src dst)=0 := by
  rw [CachedSquareCopy.measurements];exact co.2
 constructor
 · simp only [copy,toffoliCount_append]
   have zm : toffoliCount (middle x y z (dst.getD 64 0) (dst.getD 65 0) (dst.getD 96 0) (dst.getD 97 0))=0 := rfl
   rw [zm]
   omega
 · simp only [copy,measurementCount_append]
   have zm : measurementCount (middle x y z (dst.getD 64 0) (dst.getD 65 0) (dst.getD 96 0) (dst.getD 97 0))=0 := rfl
   rw [mp,zm,ct.2,mo]

theorem copy_slots118 (c cache x y z : Wire)(src dst : List Wire)(ls : src.length=118)(ld : dst.length=118) :
 Challenge.gateSlots (copy c cache x y z src dst)=Challenge.gateSlots (CachedSquareCopy.copy c cache src dst)+3 := by
 have zm : Challenge.gateSlots (middle x y z (dst.getD 64 0) (dst.getD 65 0) (dst.getD 96 0) (dst.getD 97 0))=5 := rfl
 simp only [copy,Challenge.gateSlots_append,copyPrefix,cached_slots_eq,
  Baselines.copyRegister_gateSlots,zm,List.length_take,List.length_drop,ls,ld]
 rfl

theorem copy_wires118 (c cache x y z : Wire)(src dst : List Wire)(ls : src.length=118)(ld : dst.length=118) :
 wires (copy c cache x y z src dst)⊆wires (CachedSquareCopy.copy c cache src dst)∪{x,y,z} := by
 have lens:src.length=dst.length:=by omega
 have pref : wires (copyPrefix c cache src dst)⊆wires (CachedSquareCopy.copy c cache src dst) := by
  intro q h
  rw [cached_take_split c cache src dst 96 lens (by omega) (by omega),wires_append]
  exact Finset.mem_union_left _ h
 have tail : wires (copyRegister (some c) (src.drop 98) (dst.drop 98))⊆wires (CachedSquareCopy.copy c cache src dst) := by
  intro q h
  rw [cached_take_split c cache src dst 98 lens (by omega) (by omega),wires_append]
  exact Finset.mem_union_right _ h
 have bank (i : Nat)(hi : i<118) : dst.getD i 0∈wires (CachedSquareCopy.copy c cache src dst) :=
  dst_mem_cached c cache src dst lens _ (DiagSq.getD_in dst i (by omega))
 have b64:=bank 64 (by omega);have b65:=bank 65 (by omega)
 have b96:=bank 96 (by omega);have b97:=bank 97 (by omega)
 intro q h
 simp only [copy,wires_append,Finset.mem_union]at h
 rcases h with (h|h)|h
 · exact Finset.mem_union_left _ (pref h)
 · simp only [middle,wires,Instr.wires,Finset.union_empty,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton]at h
   aesop
 · exact Finset.mem_union_left _ (tail h)

theorem copy_physical118 (c cache x y z : Wire)(src dst : List Wire)
 (ls : src.length=118)(ld : dst.length=118)(dn : dst.Nodup)
 (xn : x∉dst)(yn : y∉dst)(zn : z∉dst)
 (old : GatePhysical (CachedSquareCopy.copy c cache src dst)) :
 GatePhysical (copy c cache x y z src dst) := by
 have lens:src.length=dst.length:=by omega
 have pref : GatePhysical (copyPrefix c cache src dst) := by
  rw [cached_take_split c cache src dst 96 lens (by omega) (by omega),gatePhysical_append]at old
  exact old.1
 have tail : GatePhysical (copyRegister (some c) (src.drop 98) (dst.drop 98)) := by
  rw [cached_take_split c cache src dst 98 lens (by omega) (by omega),gatePhysical_append]at old
  exact old.2
 have dd (i j : Nat)(hi : i<118)(hj : j<118)(ne : i≠j) : dst.getD i 0≠dst.getD j 0 := by
  intro e
  rw [List.getD_eq_getElem dst 0 (n:=i) (by omega),List.getD_eq_getElem dst 0 (n:=j) (by omega)]at e
  exact ne ((List.Nodup.getElem_inj_iff dn).mp e)
 have neq (q : Wire)(hn : q∉dst)(i : Nat)(hi : i<118) : q≠dst.getD i 0 := by
  intro e;apply hn;rw [e];exact DiagSq.getD_in dst i (by omega)
 have mid : GatePhysical (middle x y z (dst.getD 64 0) (dst.getD 65 0) (dst.getD 96 0) (dst.getD 97 0)) := by
  have a:=neq x xn 96 (by omega)
  have b:=dd 64 96 (by omega) (by omega) (by omega)
  have d:=neq y yn 97 (by omega)
  have e:=neq z zn 97 (by omega)
  have f:=dd 65 97 (by omega) (by omega) (by omega)
  simp [middle,GatePhysical,RecordedQuantum.PhysicalInstr,ECDSAAdd.ProperGate]
  exact ⟨a,b,d,e,f⟩
 simpa only [copy,gatePhysical_append] using And.intro (And.intro pref mid) tail

end ECDSAAdd.Entrant.InnerLinearCopy

namespace ECDSAAdd.Entrant.ParkCopyU
open ParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

def hostsU (ext : List Wire) (g : Wire) : List Wire := hosts ext++[g]

theorem hostsU_length (ext : List Wire) (g : Wire) : (hostsU ext g).length=10 := rfl

section Pieces
variable (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire)
  (body : Program) (g : Wire)

def pA : Program := copyRegister (some control) src (L.inputBank.take src.length)
def pM : Program := LowZero18Square.make L (LowZero18LowK.kg L ext src dst)
def pE1 : Program := eraseMask control (src.take 118) ((L.inputBank.take src.length).take 118)
def pD : Program := dummies (hostsU ext g)
def pMI : Program := move ((L.inputBank.take src.length).drop 118) (hostsU ext g)
def pB : Program := renameProgram (LowZero18Square.foldPerm L ext) body
def pC1 : Program := InnerLinearCopy.copy control (LowZero18Square.cacheWire L dst) (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 118) ((L.inputBank.take src.length).take 118)
def pMO : Program := move (hostsU ext g) ((L.inputBank.take src.length).drop 118)
def pCL : Program := LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)
def pE : Program := eraseMask control src (L.inputBank.take src.length)

/-- The 128-bit leaf with its last ten bank bits parked on nine `ext` wires and product[256]. -/
def withLowK2PU : Program :=
  pA L control src++pM L ext src dst++pE1 L control src++pD ext g++pMI L ext src g++pB L ext body++
    pC1 L ext control src dst++pMO L ext src g++pCL L ext src dst++pE L control src

end Pieces

private theorem xor_false_eq {a b : Bool} (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

end ECDSAAdd.Entrant.ParkCopyU


namespace ECDSAAdd.Entrant.ParkCopyU
open ParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

open LowZero18Square in
theorem withLowK2PU_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (h128' : src.length=128)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (g : Wire) (hgE : g∉ext) (hgB : g∉L.inputBank.take src.length) (hgD : g∉dst) (hgS : g∉src)
    (hgC : g≠control) (hgO : g∉L.core.out) (hgK : g∉LowZero18LowK.ktmp L) (hgW : g∉ECDSAAdd.wires body)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (hg0 : s.basis g=false) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (withLowK2PU L ext control src dst body g) records s).phase=s.phase ∧
    regValue L.core.out (run (withLowK2PU L ext control src dst body g) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (withLowK2PU L ext control src dst body g) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈LowZero18LowK.ktmp L,q∉L.core.out := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈LowZero18LowK.ktmp L,q∉dst := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈LowZero18LowK.ktmp L,q∉src := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈LowZero18LowK.ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈LowZero18LowK.ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉LowZero18LowK.ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉LowZero18LowK.ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlD : control∉dst := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlE : control∉ext := fun h => hdx control h (by simp)
  have ctlO : control∉L.core.out := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have srcB : ∀q∈src,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcD : ∀q∈src,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcOut : ∀q∈src,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bOut : ∀q∈(L.inputBank.take src.length),q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have dOut : ∀q∈dst,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padOut : ∀q∈L.leafPad,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carOut : ∀q∈L.leafCarry,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinOut : L.core.cin∉L.core.out := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padD : ∀q∈L.leafPad,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carD : ∀q∈L.leafCarry,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinD : L.core.cin∉dst := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padE : ∀q∈L.leafPad,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carE : ∀q∈L.leafCarry,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinE : L.core.cin∉ext := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  -- generic "not a leaf scratch wire" from being outside ext and LowZero18LowK.ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉LowZero18LowK.ktmp L) :
      q∉(LowZero18LowK.oregs L ext src dst).dst ∧ q∉(LowZero18LowK.oregs L ext src dst).T ∧ q∉(LowZero18LowK.kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  have cacheFix : earlyPerm L (dst.headD 0)=dst.headD 0 := by
    have mem : dst.headD 0∈dst := by
      rcases dst with _|⟨d,ds⟩
      · have hz : src.length=0 := by simpa using hlen.symm
        omega
      · exact List.mem_cons_self
    have targetM : target L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 67 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 67 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    have hostM : earlyHost L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 1 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 1 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    change (SquareCarryLoan719.earlyPerm L) (dst.headD 0)=dst.headD 0
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (fun e => tmpD _ targetM (by simpa only [e] using mem))
      (fun e => tmpD _ hostM (by simpa only [e] using mem))
  let P := if s.basis control then regValue src s.basis else 0
  -- parking data
  have Blen : (L.inputBank.take src.length).length=128 := by rw [inputLen,h128']
  have hHc : ∀h∈hostsU ext g,h∈hosts ext ∨ h=g := fun h hh =>
    (List.mem_append.mp hh).imp id List.mem_singleton.mp
  have hHx : ∀h∈hostsU ext g,h∈ext ∨ h=g := fun h hh => (hHc h hh).imp (hosts_sub ext he h) id
  have hHnd : (hostsU ext g).Nodup := List.nodup_append.mpr ⟨hosts_nodup ext hx he,List.nodup_singleton g,
    fun a ha b hb e => hgE (by rw [List.mem_singleton.mp hb] at e; exact e ▸ hosts_sub ext he a ha)⟩
  have hHT : ∀h∈hostsU ext g,h≠ext.getD 129 0 → h∉(LowZero18LowK.oregs L ext src dst).T := fun h hh e =>
    (hHc h hh).elim (fun hh' => host_not_oT L ext src dst hx he h128' h hh' e)
      (fun e' => by subst e'; exact fun ht => hgE (xT _ ht))
  have hHX : ∀h∈hostsU ext g,h≠ext.getD 197 0 → h≠ext.getD 297 0 → h≠ext.getD 132 0 → h≠ext.getD 232 0 → h∉(LowZero18LowK.kg L ext src dst).X := fun h hh e1 e2 e3 e4 =>
    (hHc h hh).elim (fun hh' => host_not_X L ext src dst hx he h128' tmpE h hh' e1 e2 e3 e4)
      (fun e' => by subst e'; exact fun ht => (xX _ ht).elim hgE hgK)
  have hH0 : ∀h∈hostsU ext g,h≠ext.getD 0 0 := fun h hh =>
    (hHc h hh).elim (fun hh' => host_ne_zero ext hx he h hh')
      (fun e' => by subst e'; exact fun e => hgE (e ▸ DiagSq.getD_in ext 0 (by omega)))
  have hHB : ∀h∈hostsU ext g,h∉(L.inputBank.take src.length) := fun h hh =>
    (hHx h hh).elim (extB h) (fun e' => e' ▸ hgB)
  have hHD : ∀h∈hostsU ext g,h∉dst := fun h hh => (hHx h hh).elim (extD h) (fun e' => e' ▸ hgD)
  have hHo : ∀h∈hostsU ext g,h∉L.core.out := fun h hh => (hHx h hh).elim (extOut h) (fun e' => e' ▸ hgO)
  have hHs : ∀q∈src,q∉hostsU ext g := fun q hq hh =>
    (hHx q hh).elim (fun h => extSrc q h hq) (fun e' => hgS (e' ▸ hq))
  have ctlH : control∉hostsU ext g := fun h => (hHx _ h).elim ctlE (fun e' => hgC e'.symm)
  have hH0g : ∀h∈hostsU ext g,s.basis h=false := fun h hh => (hHx h hh).elim (ext0 h) (fun e' => e' ▸ hg0)
  have bNd : (L.inputBank.take src.length).Nodup := (List.nodup_append.mp ndCopy).2.1
  have b15 : ∀q∈(L.inputBank.take src.length).take 118,q∉(L.inputBank.take src.length).drop 118 := by
    intro q h1 h5
    have nd : ((L.inputBank.take src.length).take 118++(L.inputBank.take src.length).drop 118).Nodup := by
      rw [List.take_append_drop]; exact bNd
    exact (List.nodup_append.mp nd).2.2 q h1 q h5 rfl
  have b51 : ∀q∈(L.inputBank.take src.length).drop 118,q∉(L.inputBank.take src.length).take 118 :=
    fun q h5 h1 => b15 q h1 h5
  have ndMI : ((L.inputBank.take src.length).drop 118++hostsU ext g).Nodup :=
    List.nodup_append.mpr ⟨bNd.sublist (List.drop_sublist _ _),hHnd,
      fun a ha b hb e => hHB b hb (e ▸ List.mem_of_mem_drop ha)⟩
  have ndMO : (hostsU ext g++(L.inputBank.take src.length).drop 118).Nodup :=
    (List.perm_append_comm.nodup_iff).mp ndMI
  have lenMI : ((L.inputBank.take src.length).drop 118).length=(hostsU ext g).length := by
    rw [List.length_drop,Blen,hostsU_length]
  obtain ⟨a9,r10,e10⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext g++pMI L ext src g++pB L ext body++pC1 L ext control src dst++pMO L ext src g++pCL L ext src dst) (pE L control src) records s
  obtain ⟨a8,r9,e9⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext g++pMI L ext src g++pB L ext body++pC1 L ext control src dst++pMO L ext src g) (pCL L ext src dst) a9 s
  obtain ⟨a7,r8,e8⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext g++pMI L ext src g++pB L ext body++pC1 L ext control src dst) (pMO L ext src g) a8 s
  obtain ⟨a6,r7,e7⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext g++pMI L ext src g++pB L ext body) (pC1 L ext control src dst) a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext g++pMI L ext src g) (pB L ext body) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext g) (pMI L ext src g) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src) (pD ext g) a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (pA L control src++pM L ext src dst) (pE1 L control src) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (pA L control src) (pM L ext src dst) a2 s
  rw [show withLowK2PU L ext control src dst body g=pA L control src++pM L ext src dst++pE1 L control src++pD ext g++
    pMI L ext src g++pB L ext body++pC1 L ext control src dst++pMO L ext src g++pCL L ext src dst++pE L control src from rfl,
    e10,e9,e8,e7,e6,e5,e4,e3,e2]
  simp only [pA,pM,pE1,pD,pMI,pB,pC1,pMO,pCL,pE]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have mkEq := make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  simp only [←mkEq] at mk
  have i1 := mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at i1
  rw [hKR] at mk
  generalize run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(LowZero18LowK.oregs L ext src dst).dst → q∉(LowZero18LowK.oregs L ext src dst).T → q∉(LowZero18LowK.kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈LowZero18LowK.ktmp L
    · by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · have hI : q∈((LowZero18LowK.ktmp L).drop 66).take 33 := (LowZero18LowK.kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- hosts stay zero through the copy and the producer
  -- ext[129] is the top bit of the outer T = 2*lo*hi < 2^129
  have tTop : u1.basis (ext.getD 129 0)=false := by
    have tv := mk.2.2.2.1
    have lo_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).lo u0.basis
    have hi_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).hi u0.basis
    have lol : (LowZero18LowK.oregs L ext src dst).lo.length=64 := by
      simp [LowZero18LowK.oregs,KRegs.lo,sizes.1,h128']
    have hil : (LowZero18LowK.oregs L ext src dst).hi.length=64 := by
      simp [LowZero18LowK.oregs,KRegs.hi,sizes.1,h128']
    rw [lol] at lo_lt
    rw [hil] at hi_lt
    have prod : 2*regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis*
        regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis<2^129 := by
      have := Nat.mul_lt_mul'' lo_lt hi_lt
      have e : (2:Nat)^129=2*(2^64*2^64) := by norm_num
      rw [e,Nat.mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left this (by norm_num)
    rw [← tv] at prod
    apply park_top_bits_zero _ _ 129 prod
    have tl : (LowZero18LowK.oregs L ext src dst).T=ext.take 130 := by
      simp [LowZero18LowK.oregs,h128',List.take_take]
    rw [tl,List.getD_eq_getElem _ _ (by omega)]
    have : ext[129]'(by omega)=((ext.take 130).drop 129)[0]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _
  have tInner:=ParkCopyMoreDevelop.inner_top_hosts_zero L hw ext src dst he h128' u0.basis u1.basis
    mk.2.2.2.2.1 mk.2.2.2.2.2.1
  have bInner:=ParkCopyBottomDevelop.inner_bottom_hosts_zero L ext src dst he h128' u0.basis u1.basis
    mk.2.2.2.2.1 mk.2.2.2.2.2.1
  have hU1 : ∀h∈hostsU ext g,u1.basis h=false := by
    intro h hh
    by_cases e : h=ext.getD 129 0
    · rw [e]; exact tTop
    by_cases e1:h=ext.getD 197 0
    · rw[e1];exact tInner.1
    by_cases e2:h=ext.getD 297 0
    · rw[e2];exact tInner.2
    by_cases e3:h=ext.getD 132 0
    · rw[e3];exact bInner.1
    by_cases e4:h=ext.getD 232 0
    · rw[e4];exact bInner.2
    exact (u1s h (hHD h hh) (hHT h hh e) (hHX h hh e1 e2 e3 e4)).trans
      ((u0s h (hHB h hh)).trans (hH0g h hh))
  have srcw1 : ∀q∈src,u1.basis q=s.basis q := fun q hq =>
    (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq))
  have mask1 : regValue ((L.inputBank.take src.length).take 118) u1.basis=
      if u1.basis control then regValue (src.take 118) u1.basis else 0 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ 118 (by rw [inputLen]; omega) u1.basis,bank1,
      CuccaroStreamedSquareWideLayout.regValue_take_mod src 118 (by omega) u1.basis,ctl1,src1]
    simp only [P]
    split_ifs <;> simp
  -- erase only the first 123 bank bits
  have ndMask1 : (control::(src.take 118++(L.inputBank.take src.length).take 118)).Nodup :=
    ndMask.sublist (List.Sublist.cons₂ _ (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _)))
  obtain ⟨ep1,ef1,ev1⟩ := eraseMask_correct control (src.take 118) ((L.inputBank.take src.length).take 118)
    (by simp only [List.length_take,inputLen]) ndMask1 u1 r3 mask1
  generalize run (eraseMask control (src.take 118) ((L.inputBank.take src.length).take 118)) r3 u1=u2a at ep1 ef1 ev1 ⊢
  -- record-preserving dummies on the (zero) hosts
  have hU2a : ∀h∈hostsU ext g,u2a.basis h=false := fun h hh =>
    (ef1 h (fun hb => hHB h hh (List.mem_of_mem_take hb))).trans (hU1 h hh)
  rw [dummies_run (hostsU ext g) u2a r4 hU2a]
  -- park the last five bank bits on the hosts
  obtain ⟨mp1,mf1,mv1,mz1⟩ := move_correct ((L.inputBank.take src.length).drop 118) (hostsU ext g) lenMI ndMI u2a r5
    ((regValue_zero _ _).mpr hU2a)
  generalize run (move ((L.inputBank.take src.length).drop 118) (hostsU ext g)) r5 u2a=u2 at mp1 mf1 mv1 mz1 ⊢
  have x5 : regValue (hostsU ext g) u2.basis=regValue ((L.inputBank.take src.length).drop 118) u1.basis := by
    rw [mv1]; exact regValue_congr _ _ _ (fun q hq => ef1 q (b51 q hq))
  have u2B : ∀q∈(L.inputBank.take src.length),u2.basis q=false := by
    intro q hq
    have hsplit : q∈(L.inputBank.take src.length).take 118 ∨ q∈(L.inputBank.take src.length).drop 118 := by
      rw [←List.mem_append,List.take_append_drop]; exact hq
    rcases hsplit with h1|h5
    · rw [mf1 q (b15 q h1) (fun hh => hHB q hh hq)]; exact (regValue_zero _ _).mp ev1 q h1
    · exact (regValue_zero _ _).mp mz1 q h5
  have u2s : ∀q,q∉dst → q∉ext → q≠g → u2.basis q=s.basis q := by
    intro q hq hx' hg'
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact (u2B q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [mf1 q (fun h => hb (List.mem_of_mem_drop h)) (fun h => (hHx q h).elim hx' hg'),
        ef1 q (fun h => hb (List.mem_of_mem_take h))]
      exact (u1z q hq hx').trans (u0s q hb)
  have u2ext : ∀q∈ext,q∉hostsU ext g → u2.basis q=u1.basis q := fun q h hH =>
    (mf1 q (fun h5 => extB q h (List.mem_of_mem_drop h5)) hH).trans (ef1 q (fun h1 => extB q h (List.mem_of_mem_take h1)))
  have u2u1 : ∀q,q∉(L.inputBank.take src.length) → q∉hostsU ext g → u2.basis q=u1.basis q := fun q hb hH =>
    (mf1 q (fun h => hb (List.mem_of_mem_drop h)) hH).trans (ef1 q (fun h => hb (List.mem_of_mem_take h)))
  -- body
  let u2' : State := ⟨u2.phase,fun q => if q∈ext ∨ q=g then s.basis q else u2.basis q⟩
  have dst2' : regValue dst u2'.basis=P^2 := by
    rw [←dst1]
    apply regValue_congr
    intro q hq
    have hx : ¬(q∈ext ∨ q=g) := fun h => h.elim (fun h => extD q h hq) (fun e => hgD (e ▸ hq))
    simp only [u2',if_neg hx]
    exact u2u1 q (fun h => bD q h hq) (fun h => hHD q h hq)
  have cb := callback u2' r6 dst2' (by
    intro q hq
    by_cases hx : q∈ext ∨ q=g
    · simp only [u2',if_pos hx]
    · simp only [u2',if_neg hx]; exact u2s q hq (fun h => hx (Or.inl h)) (fun e => hx (Or.inr e)))
  have loc := run_local_increment body u2 u2' r6 (by
    intro q hq
    have hx : ¬(q∈ext ∨ q=g) := fun h => h.elim (fun h => hbody q h hq) (fun e => hgW (e ▸ hq))
    simp only [u2',if_neg hx])
  generalize hv' : run body r6 u2'=v' at cb loc
  generalize hv : run body r6 u2=v at loc
  have vIn : ∀q,q∈ext ∨ q=g → v.basis q=u2.basis q := by
    intro q hq; rw [←hv]
    exact run_preserves_outside body r6 u2 q (hq.elim (hbody q) (fun e => e ▸ hgW))
  have vOut : ∀q,¬(q∈ext ∨ q=g) → v.basis q=v'.basis q := by
    intro q hq
    by_cases hb : q∈ECDSAAdd.wires body
    · exact loc.2 q hb
    · rw [←hv,←hv',run_preserves_outside body r6 u2 q hb,run_preserves_outside body r6 u2' q hb]
      simp only [u2',if_neg hq]
  have vPhase : v.phase=u2.phase := by
    apply xor_false_eq
    rw [loc.1,cb.1]
    cases u2'.phase <;> rfl
  have vFrame : ∀q,q∉L.core.out → v.basis q=u2.basis q := by
    intro q hq
    by_cases hx : q∈ext ∨ q=g
    · exact vIn q hx
    · rw [vOut q hx,cb.2.2 q hq]; simp only [u2',if_neg hx]
  have vVal : regValue L.core.out v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => vOut q (fun h => h.elim (fun h => extOut q h hq) (fun e => hgO (e ▸ hq))))).trans cb.2.1
  have targetTmp : target L∈LowZero18LowK.ktmp L := by
    apply DiagSq.getD_in
    rw [LowZero18LowK.ktmp_length L hw]
    omega
  have targetIn : u2.basis (target L)=false :=
    (u2s _ (tmpD _ targetTmp) (tmpE _ targetTmp) (fun e => hgK (e ▸ targetTmp))).trans (tmp0 _ targetTmp)
  have targetOut : (run body r6 u2).basis (target L)=false := by
    rw [hv]
    exact (vFrame _ (tmpOut _ targetTmp)).trans targetIn
  have extMember : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by omega)
  have hostIn : u2.basis (ext.getD 0 0)=false :=
    (u2ext _ extMember (fun hm => hH0 _ hm rfl)).trans
      (cross_host_zero L ext src dst h128 he u1.basis _ _ mk.2.2.2.1)
  have foldEq := fold_run_eq L hw ext body u2 r6 targetIn targetOut hostIn (hbody _ extMember)
  rw [hv] at foldEq
  rw [foldEq]
  -- second copy
  have vDst : regValue dst v.basis=P^2 := by
    calc
      regValue dst v.basis = regValue dst u2.basis :=
        regValue_congr _ _ _ (fun q hq => vFrame q (dOut q hq))
      _ = regValue dst u1.basis :=
        regValue_congr _ _ _ (fun q hq => u2u1 q (fun hb => bD q hb hq) (fun h => hHD q h hq))
      _ = P^2 := dst1
  have vControl : v.basis control=s.basis control :=
    (vFrame _ ctlO).trans (u2s _ ctlD ctlE (fun e => hgC e.symm))
  have vSource : regValue src v.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq =>
      (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq) (fun e => hgS (e ▸ hq))))
  have cached : v.basis (dst.headD 0)=(v.basis control && v.basis (src.headD 0)) :=
    CachedSquareCopy.square_head src dst control v (by omega) (by omega)
      (by simpa only [P,vControl,vSource] using vDst)
  rw [cacheWire,cacheFix]
  have readFree (i : Nat)(hi : i=198 ∨ i=199 ∨ i=233) : ext.getD i 0∉hostsU ext g := by
    intro hh
    rcases List.mem_append.mp hh with hh|hh
    · simp only [hosts,List.mem_map]at hh
      obtain ⟨j,hj,e⟩:=hh
      have jlt:= (idx_free j hj).2.2.2.2.2
      rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)]at e
      have eq:=(List.Nodup.getElem_inj_iff hx).mp e
      have ni : i∉hostIdx := by rcases hi with rfl|rfl|rfl <;> decide
      exact ni (eq ▸ hj)
    · exact hgE ((List.mem_singleton.mp hh) ▸ DiagSq.getD_in ext i (by omega))
  have readFrame (i : Nat)(hi : i=198 ∨ i=199 ∨ i=233) : v.basis (ext.getD i 0)=u1.basis (ext.getD i 0) := by
    have mem:=DiagSq.getD_in ext i (by omega)
    exact (vIn _ (Or.inl mem)).trans (u2ext _ mem (readFree i hi))
  have made:=InnerLinearCopy.masked_upper_relations L hw ext src dst he h128' control
    s.basis u0.basis u1.basis bank0 mk.2.2.2.2.2.1
  have takeGet (i : Nat)(hi : i<118) : (src.take 118).getD i 0=src.getD i 0 := by
    rw [List.getD_eq_getElem _ _ (by simp [h128'];omega),List.getD_eq_getElem _ _ (by omega)]
    simp
  have sourceBit (i : Nat)(hi : i<118) : v.basis ((src.take 118).getD i 0)=s.basis (src.getD i 0) := by
    rw [takeGet i hi,InnerLinearCopy.register_testBit src i v.basis (by omega),vSource,
      ←InnerLinearCopy.register_testBit src i s.basis (by omega)]
  have away (i : Nat)(hi : i<300) : ext.getD i 0∉(L.inputBank.take src.length).take 118 :=
    fun hb=>extB _ (DiagSq.getD_in ext i (by omega)) (List.mem_of_mem_take hb)
  have bankClean : ∀q∈(L.inputBank.take src.length).take 118,v.basis q=false := by
    intro q hq
    have qb:=List.mem_of_mem_take hq
    exact (vFrame q (bOut q qb)).trans (u2B q qb)
  have headEq : ((src.take 118).take 96).headD 0=src.headD 0 := by cases src <;> rfl
  have hcache : v.basis (dst.headD 0)=(v.basis control && v.basis (((src.take 118).take 96).headD 0)) := by
    simpa only [headEq]using cached
  have hxlin : v.basis (ext.getD 198 0)=
    ((v.basis control && v.basis ((src.take 118).getD 64 0)) ^^
     (v.basis control && v.basis ((src.take 118).getD 96 0))) := by
    rw [readFrame 198 (by omega),vControl,sourceBit 64 (by omega),sourceBit 96 (by omega)]
    exact made.1
  have hyzlin : (v.basis (ext.getD 199 0) ^^ v.basis (ext.getD 233 0))=
    ((v.basis control && v.basis ((src.take 118).getD 65 0)) ^^
     (v.basis control && v.basis ((src.take 118).getD 97 0))) := by
    rw [readFrame 199 (by omega),readFrame 233 (by omega),vControl,
      sourceBit 65 (by omega),sourceBit 97 (by omega)]
    exact made.2
  have linearEq:=InnerLinearCopy.copy_correct118 control (dst.headD 0) (ext.getD 198 0)
    (ext.getD 199 0) (ext.getD 233 0) (src.take 118) ((L.inputBank.take src.length).take 118)
    (by simp [h128']) (by simp [Blen]) ndMask1 (away 198 (by omega)) (away 199 (by omega))
    (away 233 (by omega)) v r7 bankClean hcache hxlin hyzlin
  rw [linearEq,CachedSquareCopy.run_eq control (dst.headD 0) (src.take 118) ((L.inputBank.take src.length).take 118) v r7
    (by rw [headD_take src 118 (by omega)]; exact cached)]
  have inputLen1 : (src.take 118).length=((L.inputBank.take src.length).take 118).length := by
    simp only [List.length_take,inputLen]
  have ndCopy1 : (src.take 118++(L.inputBank.take src.length).take 118).Nodup :=
    ndCopy.sublist (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _))
  have hcB1 : ∀c∈some control,c∉(L.inputBank.take src.length).take 118 := fun c hc' h =>
    hcB c hc' (List.mem_of_mem_take h)
  obtain ⟨cp2,cf2,cv2⟩ := copyRegister_correct (some control) (src.take 118) ((L.inputBank.take src.length).take 118)
    inputLen1 ndCopy1 hcB1 v r7
  generalize run (copyRegister (some control) (src.take 118) ((L.inputBank.take src.length).take 118)) r7 v=w0' at cp2 cf2 cv2 ⊢
  have vB : ∀q∈(L.inputBank.take src.length),v.basis q=s.basis q := fun q hq =>
    (vFrame q (bOut q hq)).trans (u2s q (bD q hq) (fun h => extB q h hq) (fun e => hgB (e ▸ hq)))
  have vSrc : ∀q∈src,v.basis q=s.basis q := fun q hq =>
    (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq) (fun e => hgS (e ▸ hq)))
  have w0'B5 : regValue ((L.inputBank.take src.length).drop 118) w0'.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (cf2 q (b51 q hq)).trans ((vB q (List.mem_of_mem_drop hq)).trans
      ((regValue_zero _ _).mp banks.1 q (List.mem_of_mem_drop hq))))
  -- unpark: hosts back into the bank, hosts cleared
  obtain ⟨mp2,mf2,mv2,mz2⟩ := move_correct (hostsU ext g) ((L.inputBank.take src.length).drop 118) lenMI.symm ndMO w0' r8 w0'B5
  generalize run (move (hostsU ext g) ((L.inputBank.take src.length).drop 118)) r8 w0'=w0 at mp2 mf2 mv2 mz2 ⊢
  have cf2n : ∀q,q∉(L.inputBank.take src.length) → q∉hostsU ext g → w0.basis q=v.basis q := fun q hb hH =>
    (mf2 q hH (fun h => hb (List.mem_of_mem_drop h))).trans (cf2 q (fun h => hb (List.mem_of_mem_take h)))
  have w0B5 : regValue ((L.inputBank.take src.length).drop 118) w0.basis=
      regValue ((L.inputBank.take src.length).drop 118) u1.basis := by
    rw [mv2,←x5]
    apply regValue_congr; intro q hq
    rw [cf2 q (fun h => hHB q hq (List.mem_of_mem_take h)),vIn q (hHx q hq)]
  have vCtl1 : v.basis control=u1.basis control := (vFrame _ ctlO).trans ((u2s _ ctlD ctlE (fun e => hgC e.symm)).trans ctl1.symm)
  have w0B1 : regValue ((L.inputBank.take src.length).take 118) w0.basis=
      regValue ((L.inputBank.take src.length).take 118) u1.basis := by
    have v0 : regValue ((L.inputBank.take src.length).take 118) v.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (vB q (List.mem_of_mem_take hq)).trans
        ((regValue_zero _ _).mp banks.1 q (List.mem_of_mem_take hq)))
    have vs1 : regValue (src.take 118) v.basis=regValue (src.take 118) u1.basis :=
      regValue_congr _ _ _ (fun q hq => (vSrc q (List.mem_of_mem_take hq)).trans (srcw1 q (List.mem_of_mem_take hq)).symm)
    rw [show regValue ((L.inputBank.take src.length).take 118) w0.basis=
        regValue ((L.inputBank.take src.length).take 118) w0'.basis from
      regValue_congr _ _ _ (fun q hq => mf2 q (fun h => hHB q h (List.mem_of_mem_take hq)) (b15 q hq)),
      cv2,mask1,v0,Nat.zero_xor]
    change (if v.basis control then regValue (src.take 118) v.basis else 0)=_
    rw [vCtl1,vs1]
  have wB : ∀q∈(L.inputBank.take src.length),w0.basis q=u1.basis q := by
    intro q hq
    have hsplit : q∈(L.inputBank.take src.length).take 118 ∨ q∈(L.inputBank.take src.length).drop 118 := by
      rw [←List.mem_append,List.take_append_drop]; exact hq
    rcases hsplit with h1|h5
    · exact (regValue_eq_iff _ _ _).mp w0B1 q h1
    · exact (regValue_eq_iff _ _ _).mp w0B5 q h5
  have bankW : regValue (L.inputBank.take src.length) w0.basis=P := (regValue_congr _ _ _ wB).trans bank1
  have w0u1 : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → w0.basis q=u1.basis q := by
    intro q hb ho
    by_cases hH : q∈hostsU ext g
    · rw [(regValue_zero _ _).mp mz2 q hH,hU1 q hH]
    · rw [cf2n q hb hH,vFrame q ho]
      by_cases hx' : q∈ext
      · exact u2ext q hx' hH
      · exact u2u1 q hb hH
  have w0s : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → q∉dst → q∉ext → w0.basis q=s.basis q :=
    fun q hb ho hD hE => (w0u1 q hb ho).trans ((u1z q hD hE).trans (u0s q hb))
  have bankLoHi : regValue (LowZero18LowK.oregs L ext src dst).lo w0.basis=regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis ∧
      regValue (LowZero18LowK.oregs L ext src dst).hi w0.basis=regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈LowZero18LowK.ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(LowZero18LowK.kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(LowZero18LowK.kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(LowZero18LowK.kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(LowZero18LowK.kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := LowZero18KG.clear_correct (LowZero18LowK.kg L ext src dst) sp hall w0 r9
    (by
      rw [hKR,show regValue (LowZero18LowK.oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (LowZero18LowK.oregs L ext src dst).dst w0.basis=regValue (LowZero18LowK.oregs L ext src dst).dst u1.basis from
          regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => bD q h hq) (fun h => dOut q hq h))]
      exact dst1)
    (by
      rw [hKR,←mk.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (tmpB q (xS q hq)) (tmpOut q (xS q hq))))
    (by
      rw [hKR,bankLoHi.1,bankLoHi.2,←mk.2.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => extB q (xT q hq) h)
        (fun h => extOut q (xT q hq) h)))
    (by rw [hKR]; exact I1w) (by rw [hKR]; exact I2w) (by rw [hKR]; exact I5w)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (xz q hq)))
    (by rw [hKR]; exact (regValue_congr _ _ _ (fun q hq => w0s q (padB q hq) (padOut q hq) (padD q hq) (padE q hq))).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (List.mem_of_mem_take hq)))
    (by rw [hKR]; exact (w0s _ cinB cinOut cinD cinE).trans hc.cin)
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have clEq := clear_run_eq_of_boundaries L hw (LowZero18LowK.kg L ext src dst) w0 r9
    (LowZero18SquareSupport.target_clearPrefix_free
      L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he) free.2
    (by
      have inv := I1w
      rw [LowZero18LowK.kg_I1] at inv
      exact (regValue_zero _ _).mp inv.1 _
        (SquareCarryLoan719Support.target_mem_inner L hw ext src dst))
    ((regValue_zero _ _).mp cl.2.2.2.2.1 _ (by
      have member := LowZero18SquareSupport.target_mem_X1 L hw ext src dst
      simp only [KG.X,List.mem_append]
      exact Or.inl (Or.inl member)))
    ((regValue_zero _ _).mp cl.2.2.1 _
      (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128))
  simp only [←clEq] at cl
  rw [hKR] at cl
  generalize run (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) r9 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉LowZero18LowK.ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
    let o := nK q hD hE hT; cl.2.2.2.2.2 q o.1 o.2.1 o.2.2
  have w1B : regValue (L.inputBank.take src.length) w1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => w1s q (bD q hq) (fun h => extB q h hq) (fun h => tmpB q h hq))).trans bankW
  have w1src : regValue src w1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (w1s q (srcD q hq) (fun h => extSrc q h hq) (fun h => tmpSrc q h hq)).trans
      ((cf2n q (srcB q hq) (hHs q hq)).trans (vSrc q hq)))
  have w1ctl : w1.basis control=s.basis control :=
    (w1s _ ctlD ctlE ctlT).trans ((cf2n _ ctlB ctlH).trans ((vFrame _ ctlO).trans (u2s _ ctlD ctlE (fun e => hgC e.symm))))
  obtain ⟨ep2,ef2,ev2⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask w1 r10 (by
    rw [w1B,w1ctl,w1src])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r10 w1=w2 at ep2 ef2 ev2 ⊢
  refine ⟨ep2.trans (cl.1.trans (mp2.trans (cp2.trans (vPhase.trans (mp1.trans (ep1.trans (mk.1.trans cp1))))))),?_,?_⟩
  · rw [←vVal]
    apply regValue_congr
    intro q hq
    have o := nK q (fun h => dOut q h hq) (fun h => extOut q h hq) (fun h => tmpOut q h hq)
    rw [ef2 q (fun h => bOut q h hq),cl.2.2.2.2.2 q o.1 o.2.1 o.2.2,cf2n q (fun h => bOut q h hq) (fun h => hHo q h hq)]
  · intro q hq
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev2 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [ef2 q hb]
      by_cases hD : q∈(LowZero18LowK.oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q hD).trans ((regValue_zero _ _).mp hzero q hD).symm
      by_cases hT : q∈(LowZero18LowK.oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q hT).trans (ext0 q (xT q hT)).symm
      by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q hX]
        rcases xX q hX with e|e
        · exact (ext0 q e).symm
        · exact (tmp0 q e).symm
      rw [cl.2.2.2.2.2 q hD hT hX]
      by_cases hH : q∈hostsU ext g
      · rw [(regValue_zero _ _).mp mz2 q hH]; exact (hH0g q hH).symm
      rw [cf2n q hb hH,vFrame q hq]
      by_cases hx : q∈ext
      · rw [u2ext q hx hH,u1s q hD hT hX,u0s q hb]
      · exact u2s q hD hx (fun e => hH (e ▸ List.mem_append_right _ (List.mem_singleton_self _)))

end ECDSAAdd.Entrant.ParkCopyU
