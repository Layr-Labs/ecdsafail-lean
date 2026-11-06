import ECDSAAdd.Submission.Entrant.ParityEven
import ECDSAAdd.Submission.Entrant.MainPart07
namespace ECDSAAdd.Entrant.ParityXEntry
open Arithmetic Challenge RecordedQuantum NativeFirstDirect MappedCompressed
  E1Merge ParityCarry ParityConvert ParityEven EntryFuseArithmetic E1WholeKAdd52Research
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires GatePhysical toffoliCount measurementCount gateSlots
  E1Merge.comparePart E1Merge.parGates E1Merge.prodPart E1Merge.loadK E1Merge.loadT E1Merge.hAddT flagKAdd52

def postX (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  loadK w g k++[.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]

def tailX (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  (parGates w g k++rotateRight (kR w))++prodPart w g++loadK w g k++flagKAdd52 w++postX w g k

theorem merged_split (w:Nat→Wire) (g:Wire) (k:Nat) :
    E1AffineEndpoints52Research.Forward.merged w g k=comparePart w g k++tailX w g k := by
  unfold E1AffineEndpoints52Research.Forward.merged
  change ((comparePart w g k++(parGates w g k++rotateRight (kR w)))++prodPart w g++loadK w g k)++
    flagKAdd52 w++postX w g k=comparePart w g k++tailX w g k
  simp only [tailX,List.append_assoc]

def compareLayout (w:Nat→Wire) : MeasuredCanonicalModLayout where
  src:=srcR w
  out:=xR w
  carry:=cR w
  high:=w 721
  cin:=w 513
  flag:=w 514

theorem compareLayout_widths (w:Nat→Wire) : (compareLayout w).Widths 256 := by
  constructor <;> simp [compareLayout,srcR,xR,cR,wireBlock]

theorem compareLayout_nodup : (base 2400::(compareLayout base).wires).Nodup := by
  have numeric:(2400::((List.range' 0 256)++(List.range' 770 256)++(List.range' 256 256)++[721,513,514])).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    simp only [List.count_cons,List.count_append,List.count_nil,List.count_range_1',beq_iff_eq]
    split_ifs <;> omega
  simpa only [compareLayout,MeasuredCanonicalModLayout.wires,srcR,xR,cR,wireBlock,
    List.map_cons,List.map_nil,List.map_append] using numeric.map base_injective

theorem comparePart_eq (w:Nat→Wire) (g:Wire) (k:Nat) :
    comparePart w g k=comparePrefixOld g (compareLayout w).src (compareLayout w).out
      (compareLayout w).carry (compareLayout w).cin (compareLayout w).flag (complement+k) := by
  have hc:E1Merge.cmpC=complement:=by norm_num [E1Merge.cmpC,ECDSAAdd.p,complement]
  simp only [comparePart,comparePrefixOld,loadNot,unloadNot,compareLayout,hc,List.append_assoc]

def compareOdd (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  comparePrefixNew g (compareLayout w).src (compareLayout w).out (compareLayout w).carry
    (compareLayout w).cin (compareLayout w).flag (complement+k)

def mergedOdd (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  if k%2=1 then compareOdd w g k++tailX w g k else E1AffineEndpoints52Research.Forward.merged w g k

theorem mergedOdd_eq (k:Nat) (s:State) (m:List Bool)
    (hs:regValue (srcR base) s.basis=0) (hc:s.basis (base 513)=false) :
    run (mergedOdd base (base 2400) k) m s=
      run (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) m s := by
  unfold mergedOdd
  split_ifs with he
  · have even:(complement+k)%2=0:=by norm_num [complement,Nat.add_mod,he]
    rw [merged_split,comparePart_eq]
    exact prefix_eq _ _ _ s m
      (ParityConvert.compare_layout_counts (compareLayout base) (base 2400) (compareLayout_widths base) (complement+k)).2.1
      (compare_layout_eq (compareLayout base) (base 2400) (compareLayout_widths base)
        compareLayout_nodup (complement+k) even s m hs hc)
  · rfl

theorem mergedOdd_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (mergedOdd w g k)+oddSavings k=toffoliCount (E1AffineEndpoints52Research.Forward.merged w g k) ∧
    measurementCount (mergedOdd w g k)=measurementCount (E1AffineEndpoints52Research.Forward.merged w g k) ∧
    gateSlots (mergedOdd w g k)≤gateSlots (E1AffineEndpoints52Research.Forward.merged w g k) := by
  by_cases he:k%2=1
  · have delta:=ParityConvert.compare_layout_counts (compareLayout w) g (compareLayout_widths w) (complement+k)
    simp only [mergedOdd,oddSavings,he,if_true]
    rw [merged_split,comparePart_eq]
    simp only [compareOdd,toffoliCount_append,measurementCount_append,gateSlots_append]
    omega
  · simp [mergedOdd,oddSavings,he]


theorem mergedOdd_wires (w:Nat→Wire) (g:Wire) (k:Nat) :
    wires (mergedOdd w g k)⊆wires (E1AffineEndpoints52Research.Forward.merged w g k) := by
  unfold mergedOdd
  split_ifs
  · rw [merged_split,comparePart_eq]
    simp only [compareOdd,wires_append]
    exact Finset.union_subset_union
      (ParityConvert.compare_layout_wires (compareLayout w) g (compareLayout_widths w) (complement+k))
      (Finset.Subset.refl _)
  · exact Finset.Subset.refl _

theorem mergedOdd_physical (k:Nat)
    (old:GatePhysical (E1AffineEndpoints52Research.Forward.merged base (base 2400) k)) :
    GatePhysical (mergedOdd base (base 2400) k) := by
  unfold mergedOdd
  split_ifs
  · rw [merged_split,comparePart_eq] at old
    simp only [gatePhysical_append] at old ⊢
    exact ⟨ParityConvert.compare_layout_physical (compareLayout base) (base 2400)
      (compareLayout_widths base) (complement+k) old.1,old.2⟩
  · exact old

def parStage (k:Nat) : Program := parGates base (base 2400) k++rotateRight (kR base)

theorem rotate_outside (i:Nat) (hi : i < 770 ∨ 1028 ≤ i) : base i∉wires (rotateRight (kR base)) := by
  rw [(rotate_wires (kR base)).1]
  simp only [kR,wireBlock,List.length_map,List.length_range',show ¬(258:Nat)<2 by decide,
    if_false,List.mem_toFinset,List.mem_map]
  intro H
  obtain ⟨j,hj,e⟩:=H
  have E:=base_injective e
  simp only [List.mem_range'_1] at hj
  omega

theorem parStage_alpha_free (k:Nat) : base 721∉wires (parStage k) := by
  have R:=rotate_outside 721 (Or.inl (by decide))
  simp only [parStage,wires_append,Finset.mem_union,not_or]
  constructor
  · unfold parGates
    split_ifs <;> simp [wires_append,wires,Instr.wires,base]
  · exact R

theorem parStage_values (k:Nat) (he:k%2=0) (s:State) (m:List Bool)
    (hp:s.basis (base 1028)=false) :
    let t:=run (parStage k) m s
    t.basis (base 2400)=s.basis (base 2400) ∧ t.basis (base 514)=s.basis (base 514) ∧
    t.basis (base 1028)=(s.basis (base 770) ^^ s.basis (base 514)) := by
  have ne:¬k%2=1:=by omega
  let u:=run (parGates base (base 2400) k) m s
  have ug:u.basis (base 2400)=s.basis (base 2400):=by
    simp [u,parGates,ne,run,writeBit,Function.update,base]
  have uf:u.basis (base 514)=s.basis (base 514):=by
    simp [u,parGates,ne,run,writeBit,Function.update,base]
  have up:u.basis (base 1028)=(s.basis (base 770) ^^ s.basis (base 514)):=by
    have hp':s.basis 1044=false:=hp
    simp [u,parGates,ne,run,writeBit,Function.update,base,hp']
  dsimp only
  simp only [parStage,run_append,run_take]
  have z:measurementCount (parGates base (base 2400) k)=0:=by
    simp [parGates,ne,measurementCount_append,measurementCount]
  rw [z,List.drop_zero]
  exact ⟨(run_preserves_outside _ m u _ (rotate_outside 2400 (Or.inr (by decide)))).trans ug,
    (run_preserves_outside _ m u _ (rotate_outside 514 (Or.inl (by decide)))).trans uf,
    (run_preserves_outside _ m u _ (rotate_outside 1028 (Or.inr (by decide)))).trans up⟩

def evenTail (k:Nat) : Program :=
  parStage k++[.CX (base 514) (base 721),.CCX (base 514) (base 1028) (base 722)]++
    loadK base (base 2400) k++flagKAdd52 base++postX base (base 2400) k

theorem evenTail_eq (k:Nat) (he:k%2=0) (s:State) (m:List Bool)
    (ha:s.basis (base 721)=false) (hp:s.basis (base 1028)=false)
    (wrap:s.basis (base 514)=true→s.basis (base 2400)=true) :
    run (evenTail k) m (put s (base 721) (s.basis (base 2400) && s.basis (base 770)))=
      run (tailX base (base 2400) k) m s := by
  let S:=parStage k
  let A:=s.basis (base 2400) && s.basis (base 770)
  have vals:=parStage_values k he s m hp
  have product:((run S m s).basis (base 2400) && (run S m s).basis (base 1028))=
      (A ^^ (run S m s).basis (base 514)):=by
    rw [vals.1,vals.2.1,vals.2.2]
    dsimp only [A]
    cases hg:s.basis (base 2400) <;> cases hx:s.basis (base 770) <;>
      cases hf:s.basis (base 514) <;> simp_all
  have ac:(run S m s).basis (base 721)=false:=
    (run_preserves_outside S m s _ (parStage_alpha_free k)).trans ha
  have e:run (S++[.CX (base 514) (base 721)]) m (put s (base 721) A)=
      run (S++[.CCX (base 2400) (base 1028) (base 721)]) m s:=by
    simp only [run_append,run_take]
    rw [run_put S m s (base 721) A (parStage_alpha_free k)]
    exact cached_flag_eq (base 2400) (base 1028) (base 514) (base 721) (by decide) (run S m s) _ A ac product
  have E:=append_eq_states _ _
    ([Instr.CCX (base 514) (base 1028) (base 722)]++loadK base (base 2400) k++flagKAdd52 base++postX base (base 2400) k)
    (put s (base 721) A) s m (by simp [measurementCount_append,measurementCount]) e
  simpa only [evenTail,tailX,prodPart,parStage,S,A,List.append_assoc,List.cons_append,List.nil_append] using E

def mergedEven (k:Nat) : Program :=
  [.CCX (base 2400) (base 770) (base 721)]++
    comparePrefixCached (base 2400) (base 721) (srcR base) (xR base) (cR base)
      (base 513) (base 514) (complement+k)++evenTail k

theorem mergedEven_eq (k X:Nat) (hk:k<ECDSAAdd.p) (hX:X<ECDSAAdd.p)
    (s:State) (m:List Bool) (he:k%2=0) (hx:regValue (xR base) s.basis=X)
    (hs:regValue (srcR base) s.basis=0) (hf:s.basis (base 514)=false)
    (ha:s.basis (base 721)=false) (hp:s.basis (base 1028)=false) (hc:s.basis (base 513)=false)
    (hcarry:∀q∈cR base,s.basis q=false) :
    run (mergedEven k) m s=run (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) m s := by
  let K:=compareLayout base
  let g:=base 2400
  let c:=complement
  let P:=[Instr.CCX g (base 770) (base 721)]++
    comparePrefixCached g (base 721) (srcR base) (xR base) (cR base) (base 513) (base 514) (c+k)
  let O:=comparePrefixOld g K.src K.out K.carry K.cin K.flag (c+k)
  let n:=measurementCount O
  let t:=run O (m.take n) s
  have hw:=compareLayout_widths base
  have hn:=compareLayout_nodup
  have lb:EntryFuse.lowBit K=base 770:=rfl
  have count:measurementCount P=measurementCount O:=(cached_layout_counts K g hw (c+k)).2.1
  have odd:(c+k)%2=1:=by
    have C:c%2=1:=by norm_num [c,complement]
    omega
  have cachedRun:run P (m.take n) s=put t (base 721) (s.basis g && s.basis (base 770)):=by
    simpa only [K,compareLayout,lb] using cachedPrefix_after_compute K g hw hn (c+k) odd s (m.take n) hs hc ha
  have primeBound:X<prime:=by rw [EntryFuse.prime_eq_secp];exact hX
  have kBound:k<prime:=by rw [EntryFuse.prime_eq_secp];exact hk
  have pc:prime+c=2^256:=by norm_num [prime,c,modulus,complement]
  have initial:FastConst.Frame K s.basis 0 X false s.basis:=⟨hs,hx,hf,by intro q hq;rfl⟩
  have pre:=EntryFuse.comparePrefix_correct hn 256 hw s.basis hcarry hc c prime k X pc kBound primeBound
    s (m.take n) initial
  have oe:O=EntryFuse.comparePrefix K g c k:=by
    simp only [O,comparePrefixOld,loadNot,unloadNot,EntryFuse.comparePrefix,List.append_assoc]
  rw [←oe] at pre
  change t.phase=s.phase ∧ FastConst.Frame K s.basis 0 X
    (if s.basis g then decide (prime≤X+k) else false) t.basis at pre
  have tg:t.basis g=s.basis g:=pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have ta:t.basis (base 721)=false:=(pre.2.2.2.2 K.high
    (FastConst.fixed_not_mutable hn K.high (by simp [K]))).trans ha
  have po:base 1028∉FastConst.mutable K:=by decide +kernel
  have tp:t.basis (base 1028)=false:=(pre.2.2.2.2 _ po).trans hp
  have tv:t.basis (base 770)=s.basis (base 770):=
    (regValue_eq_iff K.out t.basis s.basis).mp (pre.2.2.1.trans hx.symm) _ (by decide +kernel)
  have wrap:t.basis (base 514)=true→t.basis g=true:=by
    intro F
    change t.basis K.flag=true at F
    rw [tg]
    have f:=pre.2.2.2.1
    cases G:s.basis g <;> simp_all
  rw [←tg,←tv] at cachedRun
  rw [merged_split,comparePart_eq]
  change run (P++evenTail k) m s=run (O++tailX base g k) m s
  simp only [run_append,count]
  change run (evenTail k) (m.drop n) (run P (m.take n) s)=run (tailX base g k) (m.drop n) t
  rw [cachedRun]
  exact evenTail_eq k he t (m.drop n) ta tp wrap

theorem evenTail_counts (k:Nat) :
    toffoliCount (evenTail k)+1=toffoliCount (tailX base (base 2400) k) ∧
    measurementCount (evenTail k)=measurementCount (tailX base (base 2400) k) ∧
    gateSlots (evenTail k)=gateSlots (tailX base (base 2400) k) := by
  simp only [evenTail,tailX,parStage,prodPart,toffoliCount_append,measurementCount_append,gateSlots_append]
  simp only [toffoliCount,measurementCount,gateSlots,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,instructionSlots]
  constructor
  · omega
  · exact ⟨trivial,trivial⟩

theorem mergedEven_counts (k:Nat) :
    toffoliCount (mergedEven k)+1=toffoliCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) ∧
    measurementCount (mergedEven k)=measurementCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) ∧
    gateSlots (mergedEven k)+3=gateSlots (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) := by
  let K:=compareLayout base
  let P:=[Instr.CCX (base 2400) (base 770) (base 721)]++
    comparePrefixCached (base 2400) (base 721) (srcR base) (xR base) (cR base)
      (base 513) (base 514) (complement+k)
  have C:toffoliCount P=toffoliCount (comparePrefixOld (base 2400) K.src K.out K.carry K.cin K.flag (complement+k)) ∧
      measurementCount P=measurementCount (comparePrefixOld (base 2400) K.src K.out K.carry K.cin K.flag (complement+k)) ∧
      gateSlots P+3=gateSlots (comparePrefixOld (base 2400) K.src K.out K.carry K.cin K.flag (complement+k)):=
    cached_layout_counts K (base 2400) (compareLayout_widths base) (complement+k)
  have B:=evenTail_counts k
  have E:mergedEven k=P++evenTail k:=rfl
  rw [E,merged_split,comparePart_eq]
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append]
  dsimp only [K] at C ⊢
  omega

theorem evenTail_wires (k:Nat) : wires (evenTail k)⊆wires (tailX base (base 2400) k) := by
  have flags:wires [.CX (base 514) (base 721),.CCX (base 514) (base 1028) (base 722)]⊆
      wires (prodPart base (base 2400)):=by
    simp [prodPart,wires,Instr.wires]
    intro q H
    simp only [Finset.mem_insert,Finset.mem_singleton] at H ⊢
    tauto
  simp only [evenTail,tailX,parStage,wires_append]
  intro q H
  have F:=flags (a:=q)
  simp only [Finset.mem_union] at H F ⊢
  tauto

theorem tail_control_wires (k:Nat) : ({base 2400,base 770,base 721}:Finset Wire)⊆
    wires (tailX base (base 2400) k) := by
  simp only [tailX,parGates,prodPart,wires_append]
  intro q H
  simp only [Finset.mem_insert,Finset.mem_singleton] at H
  simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.notMem_empty,or_false]
  tauto

theorem mergedEven_wires (k:Nat) : wires (mergedEven k)⊆
    wires (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) := by
  let K:=compareLayout base
  have C:wires (comparePrefixCached (base 2400) (base 721) (srcR base) (xR base) (cR base)
      (base 513) (base 514) (complement+k))⊆
      wires (comparePrefixOld (base 2400) K.src K.out K.carry K.cin K.flag (complement+k))∪{base 721}:=
    compareCached_layout_wires K (base 2400) (compareLayout_widths base) (complement+k)
  have B:=evenTail_wires k
  have E:=tail_control_wires k
  have pre:wires [.CCX (base 2400) (base 770) (base 721)]⊆wires (tailX base (base 2400) k):=by
    simpa only [wires,Instr.wires,Finset.union_empty] using E
  rw [merged_split,comparePart_eq]
  simp only [mergedEven,wires_append]
  intro q H
  have c:=C (a:=q)
  have b:=B (a:=q)
  have e:=pre (a:=q)
  have a:q=base 721→q∈wires (tailX base (base 2400) k):=by intro e;apply E;simp [e]
  simp only [Finset.mem_union,Finset.mem_singleton] at H c b e ⊢
  tauto

theorem evenTail_physical (k:Nat) (old:GatePhysical (tailX base (base 2400) k)) :
    GatePhysical (evenTail k) := by
  have flags:GatePhysical [.CX (base 514) (base 721),.CCX (base 514) (base 1028) (base 722)]:=by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,base]
  simp only [tailX,gatePhysical_append] at old
  simp only [evenTail,parStage,gatePhysical_append]
  exact ⟨⟨⟨⟨old.1.1.1.1,flags⟩,old.1.1.2⟩,old.1.2⟩,old.2⟩

theorem mergedEven_physical (k:Nat)
    (old:GatePhysical (E1AffineEndpoints52Research.Forward.merged base (base 2400) k)) :
    GatePhysical (mergedEven k) := by
  rw [merged_split,comparePart_eq] at old
  simp only [gatePhysical_append] at old
  have pre:GatePhysical [.CCX (base 2400) (base 770) (base 721)]:=by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,base]
  simp only [mergedEven,gatePhysical_append]
  exact ⟨⟨pre,compareCached_layout_physical (compareLayout base) (base 2400) (compareLayout_widths base)
    compareLayout_nodup (complement+k) old.1⟩,evenTail_physical k old.2⟩

def mergedAll (k:Nat) : Program :=
  if k%2=1 then mergedOdd base (base 2400) k else mergedEven k

theorem mergedAll_eq (k X:Nat) (hk:k<ECDSAAdd.p) (hX:X<ECDSAAdd.p)
    (s:State) (m:List Bool) (hx:regValue (xR base) s.basis=X)
    (hs:regValue (srcR base) s.basis=0) (hf:s.basis (base 514)=false)
    (ha:s.basis (base 721)=false) (hp:s.basis (base 1028)=false) (hc:s.basis (base 513)=false)
    (hcarry:∀q∈cR base,s.basis q=false) :
    run (mergedAll k) m s=run (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) m s := by
  unfold mergedAll
  split_ifs with he
  · exact mergedOdd_eq k s m hs hc
  · exact mergedEven_eq k X hk hX s m (by omega) hx hs hf ha hp hc hcarry

theorem mergedAll_counts (k:Nat) :
    toffoliCount (mergedAll k)+1=toffoliCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) ∧
    measurementCount (mergedAll k)=measurementCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) ∧
    gateSlots (mergedAll k)≤gateSlots (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) := by
  unfold mergedAll
  split_ifs with he
  · have H:=mergedOdd_counts base (base 2400) k
    simpa only [oddSavings,he,if_true] using H
  · have H:=mergedEven_counts k
    exact ⟨H.1,H.2.1,by omega⟩

theorem mergedAll_wires (k:Nat) : wires (mergedAll k)⊆
    wires (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) := by
  unfold mergedAll
  split_ifs
  · exact mergedOdd_wires base (base 2400) k
  · exact mergedEven_wires k

theorem mergedAll_physical (k:Nat) : GatePhysical (mergedAll k) := by
  have old:=E1AffineEndpoints52Research.Forward.merged_physical base (base 2400)
    base_pool_nodup E1QubitPlacement.g2400 k
  unfold mergedAll
  split_ifs
  · exact mergedOdd_physical k old
  · exact mergedEven_physical k old

theorem rename_run_equal (f:Wire→Wire) (S:Finset Wire)
    (inj:∀a∈S,∀b∈S,f a=f b→a=b) (P Q:Program) (hP:wires P⊆S) (hQ:wires Q⊆S)
    (s:State) (m:List Bool) (eq:run P m (pullState f s)=run Q m (pullState f s)) :
    run (renameProgram f P) m s=run (renameProgram f Q) m s := by
  have A:=run_rename_pool f S inj P hP m (pullState f s) s (by rfl) (by intro q hq;rfl)
  have B:=run_rename_pool f S inj Q hQ m (pullState f s) s (by rfl) (by intro q hq;rfl)
  rw [eq] at A
  apply State.extensionality
  · exact A.1.trans B.1.symm
  funext q
  by_cases im:q∈S.image f
  · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp im
    exact (A.2 a ha).trans (B.2 a ha).symm
  · rw [run_rename_pool_outside f S P hP m s q im,run_rename_pool_outside f S Q hQ m s q im]

def entryXAll (L:ControlledPointLayout) (k:Fp) : Program :=
  renameProgram (E1QubitPlacement.pmapR L) (mergedAll k.val)

theorem entryXAll_eq (L:ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (X k:Fp) (s:State) (m:List Bool) (hx:regValue L.point.x s.basis=X.val)
    (hc:regValue L.dialogPool s.basis=0) :
    run (entryXAll L k) m s=run (E1QubitPlacement.entryM L k) m s := by
  have inj:=E1QubitPlacement.pmap_inj L hw hn
  have pool:=E1QubitPlacement.pmap_pool L hw hn
  have hzero:=(regValue_zero _ _).mp hc
  let F:=E1QubitPlacement.pmapR L
  let t:=pullState F s
  have clean (q:Wire) (hq:q∈E1QubitPlacement.S) (notx:q∉wireBlock base 770 256) (notg:q≠base 2400) :
      t.basis q=false:=hzero _ (pool q hq notx notg)
  have inS (i:Nat) (hi : i < 515 ∨ i = 721 ∨ i = 1028) : base i∈E1QubitPlacement.S:=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i (by omega))
  have notx (i:Nat) (hi : i < 770 ∨ 1026 ≤ i) : base i∉wireBlock base 770 256:=by
    intro H
    obtain ⟨j,hj,e⟩:=List.mem_map.mp H
    have E:=base_injective e
    simp only [List.mem_range'_1] at hj
    omega
  have cl (i:Nat) (hi : i < 515 ∨ i = 721 ∨ i = 1028) : t.basis (base i)=false:=
    clean _ (inS i hi) (notx i (by omega)) (fun E=>by have e:=base_injective E;omega)
  have src:regValue (srcR base) t.basis=0:=by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (Or.inl (by omega))
  have carry:∀q∈cR base,t.basis q=false:=by
    intro q hq
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (Or.inl (by omega))
  have xval:regValue (xR base) t.basis=X.val:=by
    change regValue (wireBlock base 770 256) (fun q=>s.basis (F q))=X.val
    rw [E1QubitPlacement.regValue_pull,E1QubitPlacement.pmap_x L hw hn,hx]
  have old:=E1QubitPlacement.merged_S k.val
  have new:=(mergedAll_wires k.val).trans old
  unfold entryXAll E1QubitPlacement.entryM
  apply rename_run_equal F E1QubitPlacement.S inj _ _ new old s m
  exact mergedAll_eq k.val X.val k.isLt X.isLt t m xval src (cl 514 (by omega))
    (cl 721 (by simp)) (cl 1028 (by simp)) (cl 513 (by omega)) carry

theorem entryXAll_counts (L:ControlledPointLayout) (k:Fp) :
    toffoliCount (entryXAll L k)+1=toffoliCount (E1QubitPlacement.entryM L k) ∧
    measurementCount (entryXAll L k)=measurementCount (E1QubitPlacement.entryM L k) ∧
    gateSlots (entryXAll L k)≤gateSlots (E1QubitPlacement.entryM L k) := by
  simpa only [entryXAll,E1QubitPlacement.entryM,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,Baselines.rename_gateSlots] using mergedAll_counts k.val

theorem entryXAll_wires (L:ControlledPointLayout) (k:Fp) :
    wires (entryXAll L k)⊆wires (E1QubitPlacement.entryM L k) := by
  simp only [entryXAll,E1QubitPlacement.entryM,renameProgram_support]
  exact Finset.image_subset_image (mergedAll_wires k.val)

theorem entryXAll_physical (L:ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (k:Fp) :
    GatePhysical (entryXAll L k) := by
  have support:=(mergedAll_wires k.val).trans (E1QubitPlacement.merged_S k.val)
  exact gatePhysical_rename_support (E1QubitPlacement.pmapR L) (mergedAll k.val)
    (fun a ha b hb e=>E1QubitPlacement.pmap_inj L hw hn a (support ha) b (support hb) e)
    (mergedAll_physical k.val)

end ECDSAAdd.Entrant.ParityXEntry
