import ECDSAAdd.Submission.Entrant.ControlLoanCore
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.OwnFirstYMarker
open ControlMarkerDevelop
theorem eraseGeneral_run (b g x c : Wire) (hxb:x≠b) (hcb:c≠b) (hcx:c≠x)
 (bs : List ZeroBit) (hnd:(c::bs.flatMap ZeroBit.wires).Nodup)
 (hdis:∀q∈bs,q.input∉[b,x] ∧ q.work∉[b,x])
 (hoff:∀q∈bs,q.input≠c ∧ q.work≠c)
 (s : State) (m : List Bool)
 (hs:s.basis b=(s.basis g ^^ ((!s.basis c && bs.all (fun q=>!s.basis q.input)) && !s.basis x)))
 (hz:∀q∈bs,s.basis q.work=false) :
 run (eraseControl b g x c bs) m s=⟨s.phase,writeBit s.basis b false⟩ := by
 let t:State:=⟨s.phase,writeBit (writeBit s.basis b (s.basis b ^^ s.basis g)) c (!s.basis c)⟩
 have ib (q : ZeroBit) (hq:q∈bs) : q.input≠b ∧ q.work≠b := by
  have h:=hdis q hq
  constructor
  · intro he;exact h.1 (by simp [he])
  · intro he;exact h.2 (by simp [he])
 have hh:run [.CX g b,.X c] m s=t := by simp [run,t,writeBit,Function.update_apply,hcb]
 have hall:bs.all (fun q=>!t.basis q.input)=bs.all (fun q=>!s.basis q.input) := by
  simp only [t]
  rw [all_write _ _ c (!s.basis c) (fun q hq=>(hoff q hq).1),all_write _ _ b _ (fun q hq=>(ib q hq).1)]
 have ht: t.basis b=(t.basis c && bs.all (fun q=>!t.basis q.input) && !t.basis x) := by
  rw [hall]
  simp only [t,writeBit,Function.update_apply,if_pos rfl,Ne.symm hcb,hxb,Ne.symm hcx,if_false,Bool.true_and]
  rw [hs]
  cases h:s.basis c <;> cases s.basis g <;> simp [h]
 have htz:∀q∈bs,t.basis q.work=false := by
  intro q hq
  simp [t,writeBit,Function.update_apply,(hoff q hq).2,(ib q hq).2,hz q hq]
 have he:=erase_run b x c hxb bs (by simp [hcb,hcx]) hnd hdis t m ht htz
 unfold eraseControl
 rw [run_append,run_take,run_append,run_take]
 simp only [show measurementCount [.CX g b,.X c]=0 from rfl,List.drop_zero]
 rw [hh,he]
 simp only [run]
 apply congrArg (State.mk s.phase)
 funext w
 by_cases hb:w=b
 · subst w;simp [t,writeBit,Function.update_apply,Ne.symm hcb,hcb]
 by_cases hcc:w=c
 · subst w;simp [t,writeBit,Function.update_apply,hcb]
 simp [t,writeBit,Function.update_apply,hb,hcc]

theorem loadGeneral_run (b g x c : Wire) (hxb:x≠b) (hcb:c≠b) (hcx:c≠x)
 (hgb:g≠b) (hgc:g≠c)
 (bs : List ZeroBit) (hnd:(c::bs.flatMap ZeroBit.wires).Nodup)
 (hdis:∀q∈bs,q.input∉[b,x] ∧ q.work∉[b,x])
 (hoff:∀q∈bs,q.input≠c ∧ q.work≠c)
 (s : State) (m : List Bool)
 (hz:∀q∈bs,s.basis q.work=false) :
 run (loadControl b g x c bs) m s=
  ⟨s.phase,writeBit s.basis b ((s.basis b ^^ ((!s.basis c && bs.all (fun q=>!s.basis q.input)) && !s.basis x)) ^^ s.basis g)⟩ := by
 let t:State:=⟨s.phase,writeBit s.basis c (!s.basis c)⟩
 have hh:run [.X c] m s=t := by simp [run,t]
 have hall:bs.all (fun q=>!t.basis q.input)=bs.all (fun q=>!s.basis q.input) := by
  exact all_write bs s.basis c (!s.basis c) (fun q hq=>(hoff q hq).1)
 have htz:∀q∈bs,t.basis q.work=false := by
  intro q hq
  simp [t,writeBit,Function.update_apply,(hoff q hq).2,hz q hq]
 have hl:=load_run b x c hxb bs (by simp [hcb,hcx]) hnd hdis t m htz
 rw [hall] at hl
 unfold loadControl
 rw [run_append,run_take,run_append,run_take]
 simp only [show measurementCount [.X c]=0 from rfl,List.drop_zero]
 rw [hh,hl]
 simp only [run]
 apply congrArg (State.mk s.phase)
 funext w
 by_cases hb:w=b
 · subst w;simp [t,writeBit,Function.update_apply,Ne.symm hcb,hcb,hgb,hgc,Ne.symm hcx]
 by_cases hcc:w=c
 · subst w;simp [t,writeBit,Function.update_apply,hcb]
 simp [t,writeBit,Function.update_apply,hb,hcc]

#print axioms eraseGeneral_run
#print axioms loadGeneral_run
end ECDSAAdd.Entrant.OwnFirstYMarker

namespace ECDSAAdd.Entrant.OwnFirstYQ
open Secp256k1 Baselines ControlledPointLayout ControlPointEncodingDevelop ControlMarkerDevelop
attribute [local irreducible] ECDSAAdd.wires run layout

def markerHead : Wire := layout.point.y.headD 0
def markerTail : List ZeroBit := markerBits.drop 1
def eraseB : Program := eraseControl layout.control layout.genericSelect markerMSB markerHead markerTail
def loadB : Program := loadControl layout.control layout.genericSelect markerMSB markerHead markerTail

theorem marker_decomp : markerBits=⟨markerHead,w 0⟩::markerTail := by
 unfold markerTail markerBits markerHead markerWork
 unfold ControlledPointLayout.point Baselines.layout
 rfl

theorem head_nd : (markerHead::markerTail.flatMap ZeroBit.wires).Nodup := by
 have h:=marker_nd
 rw [marker_decomp] at h
 change (layout.point.finite::markerHead::w 0::markerTail.flatMap ZeroBit.wires).Nodup at h
 exact List.Nodup.sublist (List.Sublist.cons₂ _ (List.Sublist.cons _ (List.Sublist.refl _)))
   (List.nodup_cons.mp h).2

theorem tail_disjoint : ∀q∈markerTail,q.input∉[layout.control,markerMSB] ∧ q.work∉[layout.control,markerMSB] := by
 intro q hq
 exact marker_disjoint q (List.mem_of_mem_drop hq)

theorem tail_off : ∀q∈markerTail,q.input≠markerHead ∧ q.work≠markerHead := by
 intro q hq
 have absent:markerHead∉markerTail.flatMap ZeroBit.wires:=(List.nodup_cons.mp head_nd).1
 constructor
 · intro he
   exact absent (List.mem_flatMap.mpr ⟨q,hq,by simp [ZeroBit.wires,he]⟩)
 · intro he
   exact absent (List.mem_flatMap.mpr ⟨q,hq,by simp [ZeroBit.wires,he]⟩)

theorem tail_length : markerTail.length=255 := by
 simp only [markerTail,List.length_drop,marker_length]

theorem head_flags : markerHead≠layout.control ∧ markerHead≠markerMSB ∧ markerHead≠layout.genericSelect := by
 decide +kernel

theorem head_predicate (s:State) (X Y:Nat)
 (hx:regValue layout.point.x s.basis=X) (hy:regValue layout.point.y s.basis=Y) :
 ((!s.basis markerHead && markerTail.all (fun q=>!s.basis q.input)) && !s.basis markerMSB)=
 ControlSentinelDevelop.marker X Y := by
 have h:=marker_predicate s X Y hx hy
 rw [marker_decomp,List.all_cons] at h
 exact h

theorem eraseB_run (s:State) (m:List Bool) (X Y:Nat)
 (hx:regValue layout.point.x s.basis=X) (hy:regValue layout.point.y s.basis=Y)
 (hf:s.basis layout.point.finite=false)
 (hz:∀q∈markerBits,s.basis q.work=false)
 (hb:s.basis layout.control=ControlSentinelDevelop.recover (s.basis layout.genericSelect) X Y) :
 run eraseB m s=⟨s.phase,writeBit s.basis layout.control false⟩ := by
 apply OwnFirstYMarker.eraseGeneral_run _ _ _ _ (by decide +kernel) head_flags.1 head_flags.2.1
   markerTail head_nd tail_disjoint tail_off s m
 · rw [head_predicate s X Y hx hy]
   exact hb
 · intro q hq
   exact hz q (List.mem_of_mem_drop hq)

theorem loadB_run (s:State) (m:List Bool) (X Y:Nat)
 (hx:regValue layout.point.x s.basis=X) (hy:regValue layout.point.y s.basis=Y)
 (hf:s.basis layout.point.finite=false)
 (hz:∀q∈markerBits,s.basis q.work=false) (hb:s.basis layout.control=false) :
 run loadB m s=⟨s.phase,writeBit s.basis layout.control
   (ControlSentinelDevelop.recover (s.basis layout.genericSelect) X Y)⟩ := by
 have h:=OwnFirstYMarker.loadGeneral_run layout.control layout.genericSelect markerMSB markerHead
   (by decide +kernel) head_flags.1 head_flags.2.1 (by decide +kernel) (Ne.symm head_flags.2.2)
   markerTail head_nd tail_disjoint tail_off s m (fun q hq=>hz q (List.mem_of_mem_drop hq))
 change run loadB m s=_ at h
 rw [hb,head_predicate s X Y hx hy] at h
 simpa only [Bool.false_xor,ControlSentinelDevelop.recover,Bool.xor_comm] using h

theorem marker_counts : toffoliCount eraseB=255 ∧ measurementCount eraseB=256 ∧
 toffoliCount loadB=256 ∧ measurementCount loadB=255 := by
 simpa only [eraseB,loadB,tail_length] using control_counts
   layout.control layout.genericSelect markerMSB markerHead markerTail

theorem work_sublist (bs:List ZeroBit) : List.Sublist (bs.map ZeroBit.work) (bs.flatMap ZeroBit.wires) := by
 induction bs with
 | nil=>exact List.Sublist.refl _
 | cons b bs ih=>
   exact List.Sublist.cons _ (List.Sublist.cons₂ _ ih)

theorem marker_physical : GatePhysical eraseB ∧ GatePhysical loadB := by
 have hn:(markerHead::markerTail.map ZeroBit.work).Nodup:=
   List.Nodup.sublist (List.Sublist.cons₂ _ (work_sublist markerTail)) head_nd
 have hiw:∀q∈markerTail,q.input≠q.work := by
   intro q hq
   have h:=(List.nodup_flatMap.mp (List.nodup_cons.mp head_nd).2).1 q hq
   simpa [ZeroBit.wires] using h
 have hd:∀q∈markerHead::markerTail.map ZeroBit.work,q≠layout.control ∧ q≠markerMSB := by
   intro q hq
   rcases List.mem_cons.mp hq with eq | hm
   · subst q
     exact ⟨head_flags.1,head_flags.2.1⟩
   · obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hm
     simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or] using (tail_disjoint b hb).2
 exact ⟨eraseControl_physical _ _ _ _ (by decide +kernel) _ hn hiw,
   loadControl_physical _ _ _ _ (by decide +kernel) (by decide +kernel) _ hn hiw hd⟩

#print axioms eraseB_run
#print axioms loadB_run
#print axioms marker_physical
end ECDSAAdd.Entrant.OwnFirstYQ

namespace ECDSAAdd.Entrant.OwnFirstYSupport
open ControlMarkerDevelop
attribute [local irreducible] ECDSAAdd.wires

theorem chainA (c a t:Wire) : wires (chainAnd c a t)={c,a,t} := by
 ext q
 simp [chainAnd,wires,Instr.wires]
 tauto

theorem chainE (c a t:Wire) : wires (chainErase c a t)={c,a,t} := by
 ext q
 simp [chainErase,wires,Instr.wires,correctionWires]
 tauto

theorem zero_ports (T:Wire→Program) (b x:Wire)
 (hT:∀c,wires (T c)={b,x,c}) (c:Wire) (bs:List ZeroBit) :
 wires (zeroWith T c bs)={b,x,c} ∪ (bs.flatMap ZeroBit.wires).toFinset := by
 induction bs generalizing c with
 | nil=>simp [zeroWith,hT]
 | cons z bs ih=>
   simp only [zeroWith,wires_append,ih,chainA,chainE,List.flatMap_cons,List.toFinset_append]
   ext q
   simp [ZeroBit.wires]
   aesop

theorem erase_ports (b g x c:Wire) (bs:List ZeroBit) :
 wires (eraseControl b g x c bs)={b,g,x,c} ∪ (bs.flatMap ZeroBit.wires).toFinset := by
 have ht:∀w,wires (eraseTail b x w)={b,x,w} := by
   intro w
   ext q
   simp [eraseTail,wires,Instr.wires,correctionWires]
   tauto
 rw [eraseControl,wires_append,wires_append,zero_ports _ b x ht]
 ext q
 simp [wires,Instr.wires]
 tauto

theorem load_ports (b g x c:Wire) (bs:List ZeroBit) :
 wires (loadControl b g x c bs)={b,g,x,c} ∪ (bs.flatMap ZeroBit.wires).toFinset := by
 have ht:∀w,wires (loadTail b x w)={b,x,w} := by
   intro w
   ext q
   simp [loadTail,wires,Instr.wires]
   tauto
 rw [loadControl,wires_append,wires_append,zero_ports _ b x ht]
 ext q
 simp [wires,Instr.wires]
 tauto
end ECDSAAdd.Entrant.OwnFirstYSupport

namespace ECDSAAdd.Entrant.OwnFirstYQ
open Baselines ControlledPointLayout ControlPointEncodingDevelop ControlMarkerDevelop OwnFirstYSupport
attribute [local irreducible] ECDSAAdd.wires

theorem marker_slots : Challenge.gateSlots eraseB=1791 ∧ Challenge.gateSlots loadB=1791 := by
 simpa only [eraseB,loadB,tail_length] using control_slots
   layout.control layout.genericSelect markerMSB markerHead markerTail

theorem erase_subset : wires eraseB⊆wires ControlPointEncodingDevelop.eraseB := by
 rw [eraseB,ControlPointEncodingDevelop.eraseB,erase_ports,erase_ports,marker_decomp]
 intro q hq
 simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,
   List.flatMap_cons,ZeroBit.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
 tauto

theorem load_subset : wires loadB⊆wires ControlPointEncodingDevelop.loadB := by
 rw [loadB,ControlPointEncodingDevelop.loadB,load_ports,load_ports,marker_decomp]
 intro q hq
 simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,
   List.flatMap_cons,ZeroBit.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
 tauto

#print axioms erase_subset
#print axioms load_subset
end ECDSAAdd.Entrant.OwnFirstYQ

namespace ECDSAAdd.Entrant.OwnFirstYQ
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel
 ControlPointEncodingDevelop LinearCornerHeadDevelop LinearCornerPlacedDevelop
attribute [local irreducible] layout wires run

def classify (C : Point) : Program := renameProgram (pin (firstPorts (triOf C).role1)) linearClass
 def undo (C : Point) : Program := renameProgram (pin (firstPorts (triOf C).role1)) linearUndo
 def tagClassify : Program := renameProgram (pin tagPorts) linearTag
 def tagClear : Program := renameProgram (pin tagPorts) linearClear
 def firstFragment (C : Point) : Program := ControlPointEncodingDevelop.normalize C++classify C++(ControlPointEncodingDevelop.normalize C).reverse
 def undoFragment (C : Point) : Program := ControlPointEncodingDevelop.normalize C++undo C++(ControlPointEncodingDevelop.normalize C).reverse
 def tagClassFragment : Program := copyTag++tagClassify++copyTag.reverse
 def tagClearFragment : Program := copyTag++tagClear++copyTag.reverse
 def legal (s : State) : Prop := s.basis layout.genericSelect=true→s.basis layout.control=true

 theorem x_mem (i : Nat) (hi:i<256) : layout.point.x.getD i 0∈layout.point.x := by
 have hl:layout.point.x.length=256:=layout_widths.inputX
 rw [List.getD_eq_getElem _ _ (by omega)]
 exact List.getElem_mem _
 theorem normalize_free_wire {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (q : Wire)
 (hxy:q∉layout.point.x++layout.point.y) (hw:∀i:Fin 9,q≠w i.val) : q∉wires (ControlPointEncodingDevelop.normalize (.some hc)) := by
 have hp:=Tri.pivots (triOf_valid hc)
 have hx(i : Nat)(hi:i<256):q≠layout.point.x.getD i 0:=by
  intro he
  exact hxy (he ▸ List.mem_append_left _ (x_mem i hi))
 have hy:q≠yLow layout:=by intro he;exact hxy (he ▸ List.mem_append_right _ (yLow_mem layout layout_widths))
 simp only [ControlPointEncodingDevelop.normalize,wires_append,Finset.mem_union,not_or]
 exact ⟨⟨copyBit_free _ _ _ _ (hx _ hp.1) (hw ⟨6,by decide⟩),
  copyBit_free _ _ _ _ (hx _ hp.2.1) (hw ⟨7,by decide⟩)⟩,
  copyBit_free _ _ _ _ hy (hw ⟨8,by decide⟩)⟩
 theorem copyTag_free_wire (q : Wire) (hxy:q∉layout.point.x++layout.point.y)
 (hw:∀i:Fin 9,q≠w i.val) : q∉wires copyTag := by
 have hx(i : Nat)(hi:i<256):q≠layout.point.x.getD i 0:=by
  intro he
  exact hxy (he ▸ List.mem_append_left _ (x_mem i hi))
 simp only [copyTag,wires_append,Finset.mem_union,not_or]
 exact ⟨copyBit_free _ _ _ _ (hx 0 (by decide)) (hw ⟨6,by decide⟩),
  copyBit_free _ _ _ _ (hx 1 (by decide)) (hw ⟨7,by decide⟩)⟩
 theorem legal_run (P : Program) (hc:layout.control∉wires P) (hg:layout.genericSelect∉wires P)
 (s : State) (m : List Bool) (hs:legal s) : legal (run P m s) := by
 intro h
 rw [run_preserves_outside P m s _ hg] at h
 exact (run_preserves_outside P m s _ hc).trans (hs h)
 theorem norm_legal {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (s : State) (m : List Bool) (hs:legal s) :
 legal (run (ControlPointEncodingDevelop.normalize (.some hc)) m s) :=
 legal_run _ (normalize_free_wire hc _ control_off_xy (fun i=>(work_off_control i).symm))
  (normalize_free_wire hc _ generic_off_xy (fun i=>(work_off_generic i).symm)) s m hs
 theorem tag_legal (s : State) (m : List Bool) (hs:legal s) : legal (run copyTag m s) :=
 legal_run _ (copyTag_free_wire _ control_off_xy (fun i=>(work_off_control i).symm))
  (copyTag_free_wire _ generic_off_xy (fun i=>(work_off_generic i).symm)) s m hs

 theorem collar_equal (A P' P B : Program) (s : State) (m : List Bool)
 (hm:measurementCount P'=measurementCount P)
 (he:∀r,run P' r (run A (m.take (measurementCount A)) s)=run P r (run A (m.take (measurementCount A)) s)) :
 run (A++P'++B) m s=run (A++P++B) m s := by
 simp only [List.append_assoc,run_append,hm]
 rw [he]

 theorem firstFragment_equal {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (s : State) (m : List Bool) (hs:legal s) :
 run (firstFragment (.some hc)) m s=run (ControlPointEncodingDevelop.firstFragment (.some hc)) m s := by
 unfold firstFragment ControlPointEncodingDevelop.firstFragment
 apply collar_equal _ _ _ _ s m (by rfl)
 intro r
 apply mapped_class_equal _ (ports_inj _ (first_nd _) (by simp [firstPorts]))
 have h:=norm_legal hc s (m.take (measurementCount (ControlPointEncodingDevelop.normalize (.some hc)))) hs
 simpa only [pin,firstPorts,List.getD_cons_zero,List.getD_cons_succ] using h
 theorem undoFragment_equal {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (s : State) (m : List Bool) (hs:legal s) :
 run (undoFragment (.some hc)) m s=run (ControlPointEncodingDevelop.undoFragment (.some hc)) m s := by
 unfold undoFragment ControlPointEncodingDevelop.undoFragment
 apply collar_equal _ _ _ _ s m (by rfl)
 intro r
 apply mapped_undo_equal _ (ports_inj _ (first_nd _) (by simp [firstPorts]))
 have h:=norm_legal hc s (m.take (measurementCount (ControlPointEncodingDevelop.normalize (.some hc)))) hs
 simpa only [pin,firstPorts,List.getD_cons_zero,List.getD_cons_succ] using h
 theorem tagClassFragment_equal (s : State) (m : List Bool) (hs:legal s) :
 run tagClassFragment m s=run ControlPointEncodingDevelop.tagClassFragment m s := by
 unfold tagClassFragment ControlPointEncodingDevelop.tagClassFragment
 apply collar_equal _ _ _ _ s m (by rfl)
 intro r
 apply mapped_tag_equal _ (ports_inj _ tag_nd (by simp [tagPorts]))
 have h:=tag_legal s (m.take (measurementCount copyTag)) hs
 simpa only [pin,tagPorts,List.getD_cons_zero,List.getD_cons_succ] using h
 theorem tagClearFragment_equal (s : State) (m : List Bool) (hs:legal s) :
 run tagClearFragment m s=run ControlPointEncodingDevelop.tagClearFragment m s := by
 unfold tagClearFragment ControlPointEncodingDevelop.tagClearFragment
 apply collar_equal _ _ _ _ s m (by rfl)
 intro r
 apply mapped_clear_equal _ (ports_inj _ tag_nd (by simp [tagPorts]))
 have h:=tag_legal s (m.take (measurementCount copyTag)) hs
 simpa only [pin,tagPorts,List.getD_cons_zero,List.getD_cons_succ] using h

#print axioms firstFragment_equal
#print axioms tagClearFragment_equal
end ECDSAAdd.Entrant.OwnFirstYQ

namespace ECDSAAdd.Entrant.OwnFirstYQ
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel
 ControlPointEncodingDevelop LinearCornerHeadDevelop LinearCornerPlacedDevelop
attribute [local irreducible] layout wires run

 theorem append_legal (P Q : Program)
 (hp:∀s m,legal s→legal (run P m s)) (hq:∀s m,legal s→legal (run Q m s)) :
 ∀s m,legal s→legal (run (P++Q) m s) := by
 intro s m hs
 rw [run_append]
 exact hq _ _ (hp _ _ hs)

 theorem mapped_legal (f : Wire→Wire) (hf:∀a<11,∀b<11,f a=f b→a=b)
 (hf0:f 0=layout.control) (hf1:f 1=layout.genericSelect) (P : Program) (hp:wires P⊆Finset.range 11)
 (hi:∀s m,(run P m s).basis 0=s.basis 0 ∧ (run P m s).basis 1=s.basis 1) :
 ∀s m,legal s→legal (run (renameProgram f P) m s) := by
 intro s m hs
 have hr:=run_rename_pool f (Finset.range 11)
  (fun a ha b hb=>hf a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb)) P hp m (pullState f s) s rfl (fun _ _=>rfl)
 have hi:=hi (pullState f s) m
 have h0:(run (renameProgram f P) m s).basis (f 0)=s.basis (f 0):=(hr.2 0 (by decide)).trans hi.1
 have h1:(run (renameProgram f P) m s).basis (f 1)=s.basis (f 1):=(hr.2 1 (by decide)).trans hi.2
 rw [hf0] at h0
 rw [hf1] at h1
 intro h
 rw [h1] at h
 exact h0.trans (hs h)

 theorem old_first_legal {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
 ∀s m,legal s→legal (run (ControlPointEncodingDevelop.firstFragment (.some hc)) m s) := by
 have ha:=norm_legal hc
 have hr:∀s m,legal s→legal (run (ControlPointEncodingDevelop.normalize (.some hc)).reverse m s):=by
  apply legal_run
  · simpa only [wires_reverse] using normalize_free_wire hc _ control_off_xy (fun i=>(work_off_control i).symm)
  · simpa only [wires_reverse] using normalize_free_wire hc _ generic_off_xy (fun i=>(work_off_generic i).symm)
 have hm:=mapped_legal (pin (firstPorts (triOf (.some hc)).role1)) (ports_inj _ (first_nd _) (by simp [firstPorts]))
  rfl rfl OneHotCornersDevelop.classify OneHotCornersDevelop.programs_support.1 classify_inputs
 exact append_legal _ _ (append_legal _ _ ha hm) hr

 theorem old_tag_legal : ∀s m,legal s→legal (run ControlPointEncodingDevelop.tagClassFragment m s) := by
 have ha:=tag_legal
 have hr:∀s m,legal s→legal (run copyTag.reverse m s):=by
  apply legal_run
  · simpa only [wires_reverse] using copyTag_free_wire _ control_off_xy (fun i=>(work_off_control i).symm)
  · simpa only [wires_reverse] using copyTag_free_wire _ generic_off_xy (fun i=>(work_off_generic i).symm)
 have hm:=mapped_legal (pin tagPorts) (ports_inj _ tag_nd (by simp [tagPorts]))
  rfl rfl OneHotCornersDevelop.tagClassify OneHotCornersDevelop.programs_support.2.2.1 tag_inputs
 exact append_legal _ _ (append_legal _ _ ha hm) hr

 theorem masked_free (flag : Fin 9) (x y tag : Nat) (q : Wire)
 (hxy:q∉layout.point.x++layout.point.y) (hw:q≠w flag.val) : q∉wires (maskXY (w flag.val) x y tag) := by
 simp only [maskXY,wires_append,Finset.mem_union,not_or]
 constructor
 · intro h
   have hm:=List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
   rcases List.mem_cons.mp hm with h|h
   · exact hw h
   · exact hxy (List.mem_append_left _ h)
 · intro h
   have hm:=List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
   rcases List.mem_cons.mp hm with h|h
   · exact hw h
   · exact hxy (List.mem_append_right _ h)
 theorem masks_free (C : Point) (q : Wire)
 (hxy:q∉layout.point.x++layout.point.y) (hw:∀i:Fin 9,q≠w i.val) : q∉wires (masks C) := by
 simp only [masks,wires_append,Finset.mem_union,not_or]
 exact ⟨⟨⟨masked_free ⟨0,by decide⟩ _ _ _ q hxy (hw ⟨0,by decide⟩),
  masked_free ⟨1,by decide⟩ _ _ _ q hxy (hw ⟨1,by decide⟩)⟩,
  masked_free ⟨2,by decide⟩ _ _ _ q hxy (hw ⟨2,by decide⟩)⟩,
  masked_free ⟨3,by decide⟩ _ _ _ q hxy (hw ⟨3,by decide⟩)⟩
 theorem masks_legal (C : Point) : ∀s m,legal s→legal (run (masks C) m s) :=
 legal_run _ (masks_free C _ control_off_xy (fun i=>(work_off_control i).symm))
  (masks_free C _ generic_off_xy (fun i=>(work_off_generic i).symm))

#print axioms old_first_legal
#print axioms masks_legal
end ECDSAAdd.Entrant.OwnFirstYQ


-- Linearized exceptional-control classifiers.
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnFirstYQ
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel ControlPointEncodingDevelop
attribute [local irreducible] layout wires run

def encode (C : Point) : Program := firstFragment C++masks C++tagClearFragment
 def decode (C : Point) : Program := tagClassFragment++masks C++undoFragment C
 theorem first_M (C : Point) : measurementCount (firstFragment C)=0 := by
 simp only [firstFragment,classify,measurementCount_append,measurementCount_reverse,(normalize_counts C).2,(renameProgram_counts _ _).2]
 rfl
 theorem undo_M (C : Point) : measurementCount (undoFragment C)=0 := by
 simp only [undoFragment,undo,measurementCount_append,measurementCount_reverse,(normalize_counts C).2,(renameProgram_counts _ _).2]
 rfl
 theorem tag_M : measurementCount tagClassFragment=2 := by
 simp only [tagClassFragment,tagClassify,measurementCount_append,measurementCount_reverse,copyTag_counts.2,(renameProgram_counts _ _).2]
 rfl
 theorem clear_M : measurementCount tagClearFragment=2 := by
 simp only [tagClearFragment,tagClear,measurementCount_append,measurementCount_reverse,copyTag_counts.2,(renameProgram_counts _ _).2]
 rfl
 theorem old_first_M (C : Point) : measurementCount (ControlPointEncodingDevelop.firstFragment C)=0 := by
 simp only [ControlPointEncodingDevelop.firstFragment,ControlPointEncodingDevelop.classify,measurementCount_append,measurementCount_reverse,(normalize_counts C).2,(renameProgram_counts _ _).2]
 rfl
 theorem old_tag_M : measurementCount ControlPointEncodingDevelop.tagClassFragment=2 := by
 simp only [ControlPointEncodingDevelop.tagClassFragment,ControlPointEncodingDevelop.tagClassify,measurementCount_append,measurementCount_reverse,copyTag_counts.2,(renameProgram_counts _ _).2]
 rfl

 theorem encode_run (C : Point) (s : State) (m : List Bool) :
 run (encode C) m s=run tagClearFragment m (run (masks C) m (run (firstFragment C) m s)) := by
 unfold encode
 rw [List.append_assoc,run_append,run_take,run_append,run_take]
 simp only [first_M,(masks_counts C).2,List.drop_zero]
 theorem old_encode_run (C : Point) (s : State) (m : List Bool) :
 run (ControlPointEncodingDevelop.encode C) m s=run ControlPointEncodingDevelop.tagClearFragment m
  (run (masks C) m (run (ControlPointEncodingDevelop.firstFragment C) m s)) := by
 rw [encode_split,List.append_assoc,run_append,run_take,run_append,run_take]
 simp only [old_first_M,(masks_counts C).2,List.drop_zero]
 theorem decode_run (C : Point) (s : State) (m : List Bool) :
 run (decode C) m s=run (undoFragment C) (m.drop 2) (run (masks C) (m.drop 2) (run tagClassFragment m s)) := by
 unfold decode
 rw [List.append_assoc,run_append,run_take,run_append,run_take]
 simp only [tag_M,(masks_counts C).2,List.drop_zero]
 theorem old_decode_run (C : Point) (s : State) (m : List Bool) :
 run (ControlPointEncodingDevelop.decode C) m s=run (ControlPointEncodingDevelop.undoFragment C) (m.drop 2)
  (run (masks C) (m.drop 2) (run ControlPointEncodingDevelop.tagClassFragment m s)) := by
 rw [decode_split,List.append_assoc,run_append,run_take,run_append,run_take]
 simp only [old_tag_M,(masks_counts C).2,List.drop_zero]

 theorem encode_equal {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (s : State) (m : List Bool) (hs:legal s) :
 run (encode (.some hc)) m s=run (ControlPointEncodingDevelop.encode (.some hc)) m s := by
 have h1:=firstFragment_equal hc s m hs
 have h2:=masks_legal (.some hc) _ m (old_first_legal hc s m hs)
 rw [encode_run,old_encode_run,h1]
 exact tagClearFragment_equal _ m h2
 theorem decode_equal {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (s : State) (m : List Bool) (hs:legal s) :
 run (decode (.some hc)) m s=run (ControlPointEncodingDevelop.decode (.some hc)) m s := by
 have h1:=tagClassFragment_equal s m hs
 have h2:=masks_legal (.some hc) _ (m.drop 2) (old_tag_legal s m hs)
 rw [decode_run,old_decode_run,h1]
 exact undoFragment_equal hc _ (m.drop 2) h2

#print axioms encode_equal
#print axioms decode_equal
end ECDSAAdd.Entrant.OwnFirstYQ

namespace ECDSAAdd.Entrant.OwnFirstYQ
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel ControlPointEncodingDevelop LinearCornerHeadDevelop
attribute [local irreducible] layout wires run

 theorem counts (C : Point) : toffoliCount (encode C)=6 ∧ measurementCount (encode C)=2 ∧
 toffoliCount (decode C)=6 ∧ measurementCount (decode C)=2 := by
 have h:=linear_counts
 simp only [encode,decode,firstFragment,undoFragment,tagClassFragment,tagClearFragment,classify,undo,tagClassify,tagClear,
  toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
  (normalize_counts C).1,(normalize_counts C).2,copyTag_counts.1,copyTag_counts.2,(masks_counts C).1,(masks_counts C).2,
  (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
 omega

 theorem encoding_slots (C : Point) : gateSlots (encode C)≤2110 ∧ gateSlots (decode C)≤2110 := by
 have hn:=ControlPointEncodingDevelop.normalize_slots C
 have ht:=copyTag_slots
 have hm:=masks_slots C
 have hp:gateSlots linearClass=11 ∧ gateSlots linearUndo=11 ∧ gateSlots linearTag=17 ∧ gateSlots linearClear=17:=by decide +kernel
 simp only [encode,decode,firstFragment,undoFragment,tagClassFragment,tagClearFragment,classify,undo,tagClassify,tagClear,
  gateSlots_append,slots_reverse,rename_gateSlots]
 omega

 theorem placed_subset (f : Wire→Wire) (P Q : Program) (h:wires P⊆wires Q) :
 wires (renameProgram f P)⊆wires (renameProgram f Q) := by
 rw [renameProgram_support,renameProgram_support]
 exact Finset.image_subset_image h
 theorem fragment_support (C : Point) :
 wires (firstFragment C)⊆wires (ControlPointEncodingDevelop.firstFragment C) ∧
 wires (undoFragment C)⊆wires (ControlPointEncodingDevelop.undoFragment C) ∧
 wires tagClassFragment⊆wires ControlPointEncodingDevelop.tagClassFragment ∧
 wires tagClearFragment⊆wires ControlPointEncodingDevelop.tagClearFragment := by
 have hc:=placed_subset (pin (firstPorts (triOf C).role1)) _ _ linear_support.1
 have hu:=placed_subset (pin (firstPorts (triOf C).role1)) _ _ linear_support.2.1
 have ht:=placed_subset (pin tagPorts) _ _ linear_support.2.2.1
 have he:=placed_subset (pin tagPorts) _ _ linear_support.2.2.2
 simp only [firstFragment,undoFragment,tagClassFragment,tagClearFragment,
  ControlPointEncodingDevelop.firstFragment,ControlPointEncodingDevelop.undoFragment,
  ControlPointEncodingDevelop.tagClassFragment,ControlPointEncodingDevelop.tagClearFragment,wires_append]
 exact ⟨Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) hc) (Finset.Subset.refl _),
  Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) hu) (Finset.Subset.refl _),
  Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) ht) (Finset.Subset.refl _),
  Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) he) (Finset.Subset.refl _)⟩
 theorem encoding_support (C : Point) : wires (encode C)⊆wires (ControlPointEncodingDevelop.encode C) ∧
 wires (decode C)⊆wires (ControlPointEncodingDevelop.decode C) := by
 have h:=fragment_support C
 rw [ControlPointEncodingDevelop.encode_split,ControlPointEncodingDevelop.decode_split]
 simp only [encode,decode,wires_append]
 exact ⟨Finset.union_subset_union (Finset.union_subset_union h.1 (Finset.Subset.refl _)) h.2.2.2,
  Finset.union_subset_union (Finset.union_subset_union h.2.2.1 (Finset.Subset.refl _)) h.2.1⟩

 theorem physical (C : Point) : GatePhysical (encode C) ∧ GatePhysical (decode C) := by
 have hn:=ControlPointEncodingDevelop.normalize_physical C
 have hnr:=physical_reverse _ hn
 have ht:=copyTag_physical
 have htr:=physical_reverse _ ht
 have hm:=masks_physical C
 have hc:=placed_physical _ (first_nd (triOf C).role1) (by simp [firstPorts]) _ linear_physical.1
  (linear_support.1.trans OneHotCornersDevelop.programs_support.1)
 have hu:=placed_physical _ (first_nd (triOf C).role1) (by simp [firstPorts]) _ linear_physical.2.1
  (linear_support.2.1.trans OneHotCornersDevelop.programs_support.2.1)
 have htc:=placed_physical _ tag_nd (by simp [tagPorts]) _ linear_physical.2.2.1
  (linear_support.2.2.1.trans OneHotCornersDevelop.programs_support.2.2.1)
 have hte:=placed_physical _ tag_nd (by simp [tagPorts]) _ linear_physical.2.2.2
  (linear_support.2.2.2.trans OneHotCornersDevelop.programs_support.2.2.2)
 simp only [encode,decode,firstFragment,undoFragment,tagClassFragment,tagClearFragment,classify,undo,tagClassify,tagClear,gatePhysical_append]
 tauto

 theorem encode_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
 (b g : Bool) (R : Point) (s : State) (m : List Bool) (hgb:g=true→b=true)
 (hR:(b && !g)=true→ControlSentinelDevelop.corner (.some hc) R)
 (hX:regValue layout.point.x s.basis=ControlSentinelDevelop.ordinaryX R) (hY:regValue layout.point.y s.basis=pointY R)
 (hb:s.basis layout.control=b) (hg:s.basis layout.genericSelect=g) (hz:∀i:Fin 9,s.basis (w i.val)=false) :
 let t:=run (encode (.some hc)) m s
 XYResult s t (formatX (.some hc) b g R) (formatY (.some hc) b g R) ∧ (∀i:Fin 9,t.basis (w i.val)=false) := by
 have hs:legal s:=by intro h;rw [hg] at h;rw [hb];exact hgb h
 dsimp only
 rw [encode_equal hc s m hs]
 exact ControlPointEncodingDevelop.encode_spec hc b g R s m hR hX hY hb hg hz
 theorem decode_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
 (b g : Bool) (R : Point) (s : State) (m : List Bool) (hgb:g=true→b=true)
 (hR:(b && !g)=true→ControlSentinelDevelop.corner (.some hc) R)
 (hX:regValue layout.point.x s.basis=formatX (.some hc) b g R) (hY:regValue layout.point.y s.basis=formatY (.some hc) b g R)
 (hb:s.basis layout.control=b) (hg:s.basis layout.genericSelect=g) (hz:∀i:Fin 9,s.basis (w i.val)=false) :
 let t:=run (decode (.some hc)) m s
 XYResult s t (ControlSentinelDevelop.ordinaryX R) (pointY R) ∧ (∀i:Fin 9,t.basis (w i.val)=false) := by
 have hs:legal s:=by intro h;rw [hg] at h;rw [hb];exact hgb h
 dsimp only
 rw [decode_equal hc s m hs]
 exact ControlPointEncodingDevelop.decode_spec hc b g R s m hR hX hY hb hg hz

#print axioms counts
#print axioms encoding_support
#print axioms physical
#print axioms encode_spec
end ECDSAAdd.Entrant.OwnFirstYQ


-- Linearized exceptional-control classifiers.
set_option autoImplicit false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnFirstYQ
open ControlPointEncodingDevelop
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel FlagTop FlagExit FlagTop2 ParityEven ControlGenericPointDevelop
attribute [local irreducible] layout run
noncomputable section
open Classical

structure MiddleResult (s t : State) (X Y : Nat) (pk : Bool) : Prop where
 phase:t.phase=s.phase
 x:regValue layout.point.x t.basis=X
 y:regValue layout.point.y t.basis=Y
 parked:t.basis (FlagEntry.pkW layout)=pk
 rest:∀q,q∉layout.point.x++layout.point.y→q≠FlagEntry.pkW layout→t.basis q=s.basis q

theorem middleResult_unique {s t u : State} {X Y : Nat} {pk : Bool}
 (h:MiddleResult s t X Y pk) (k:MiddleResult s u X Y pk) : t=u := by
 apply State.extensionality _ _ (h.phase.trans k.phase.symm)
 funext q
 by_cases hp:q=FlagEntry.pkW layout
 · subst q;exact h.parked.trans k.parked.symm
 by_cases hx:q∈layout.point.x
 · exact (regValue_eq_iff _ _ _).mp (h.x.trans k.x.symm) q hx
 by_cases hy:q∈layout.point.y
 · exact (regValue_eq_iff _ _ _).mp (h.y.trans k.y.symm) q hy
 have hq:q∉layout.point.x++layout.point.y:=by simp [hx,hy]
 exact (h.rest q hq hp).trans (k.rest q hq hp).symm

 def middle (C : Point) (cx cy : Fp) : Program :=
 encode C ++ eraseB ++ borrowGeneric cx cy ++ loadB ++ decode C

theorem middle_sequence {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
 (s : State) (me ma mg ml md : List Bool)
 (hx : regValue layout.point.x s.basis = ControlSentinelDevelop.ordinaryX R)
 (hy : regValue layout.point.y s.basis = pointY R)
 (hb:s.basis layout.control=b)
 (hf : s.basis layout.point.finite = false)
 (hg : s.basis layout.genericSelect = dialogOrdinary b R (.some hc))
 (he : s.basis layout.core.equalNegY = false) (hd : s.basis layout.doubleSelect = false)
 (hz : ∀q∈layout.dialogPool,q≠FlagEntry.pkW layout→s.basis q=false)
 (hpk:s.basis (FlagEntry.pkW layout)=(dialogOrdinary b R (.some hc) && decide ((triOf (.some hc)).A < ControlSentinelDevelop.ordinaryX R))) :
 let C:Point:=.some hc
 let G:=dialogOrdinary b R C
 let O:=if G then R+C else R
 let a:=run (encode C) me s
 let u:=put a layout.control false
 let t:=run (borrowGeneric cx cy) mg u
 let v:=put t layout.control b
 let z:=run (decode C) md v
 run eraseB ma a=u ∧ run loadB ml t=v ∧
 MiddleResult s z (ControlSentinelDevelop.ordinaryX O) (pointY O) (vB hc b R) := by
 let C:Point:=.some hc
 let G:=dialogOrdinary b R C
 let O:=if G then R+C else R
 have hG:G=ControlSentinelDevelop.generic C b R:=ControlSentinelDevelop.generic_agrees C R b (WeierstrassCurve.Affine.Point.some_ne_zero hc)
 have hcorner:(b && !G)=true→ControlSentinelDevelop.corner C R:=by
  rw [hG]
  cases b <;> by_cases hr:ControlSentinelDevelop.corner C R <;> simp [ControlSentinelDevelop.generic,hr]
 have hgb:G=true→b=true:=by
  rw [hG]
  cases b <;> simp [ControlSentinelDevelop.generic]
 let a:=run (encode C) me s
 have hp:=encode_spec hc b G R s me hgb hcorner hx hy hb hg
  (fun i=>hz _ (work_pool i) (work_off_pk i))
 have ha:XYResult s a (formatX C b G R) (formatY C b G R):=hp.1
 have apool:∀q∈layout.dialogPool,q≠FlagEntry.pkW layout→a.basis q=false:=by
  intro q hq hpq
  exact (ha.rest q (pool_off_xy q hq)).trans (hz q hq hpq)
 have af:a.basis layout.point.finite=false:=(ha.rest _ finite_off_xy).trans hf
 have ag:a.basis layout.genericSelect=G:=(ha.rest _ generic_off_xy).trans hg
 have ab:a.basis layout.control=b:=(ha.rest _ control_off_xy).trans hb
 have ae:a.basis layout.core.equalNegY=false:=(ha.rest _ eneg_off_xy).trans he
 have ad:a.basis layout.doubleSelect=false:=(ha.rest _ double_off_xy).trans hd
 have apk:a.basis (FlagEntry.pkW layout)=(G && decide ((triOf C).A < ControlSentinelDevelop.ordinaryX R)):=
  (ha.rest _ (pool_off_xy _ (FlagEntry.pk_pool layout layout_widths))).trans hpk
 let u:=put a layout.control false
 have erase:run eraseB ma a=u:=by
  apply eraseB_run a ma (formatX C b G R) (formatY C b G R) ha.x ha.y af
   (fun q hq=>apool _ (marker_work_pool q hq) (marker_work_off_pk q hq))
  rw [ag,format_recover C b G R hgb]
  exact ab
 have ux:regValue layout.point.x u.basis=formatX C b G R:=
  (put_reg _ _ _ _ (by decide +kernel)).trans ha.x
 have uy:regValue layout.point.y u.basis=formatY C b G R:=
  (put_reg _ _ _ _ (by decide +kernel)).trans ha.y
 have uf:u.basis layout.point.finite=false:=(put_away a _ _ false finite_off_control).trans af
 have ug:u.basis layout.genericSelect=G:=(put_away a _ _ false generic_off_control).trans ag
 have ue:u.basis layout.core.equalNegY=false:=(put_away a _ _ false eneg_off_control).trans ae
 have ud:u.basis layout.doubleSelect=false:=(put_away a _ _ false double_off_control).trans ad
 have ub:u.basis layout.control=false:=put_at _ _ _
 have upool:∀q∈layout.dialogPool,q≠FlagEntry.pkW layout→u.basis q=false:=by
  intro q hq hpq
  exact (put_away a _ _ false (pool_off_control q hq)).trans (apool q hq hpq)
 have upk:u.basis (FlagEntry.pkW layout)=(G && decide ((triOf C).A < ControlSentinelDevelop.ordinaryX R)):=
  (put_away a _ _ false pk_off_control).trans apk
 have gt:=generic_format_run hc b R u mg ux uy uf ug ue ud upool upk
 have gd:(run (genericBlock cx cy) mg u).basis layout.doubleSelect=false:=
  (gt.2.2.2.2 _ double_off_xy double_off_pk).trans ud
 have eqg:=borrowGeneric_run cx cy u mg ub ud gd
 let t:=run (borrowGeneric cx cy) mg u
 have ht:t.phase=u.phase ∧ regValue layout.point.x t.basis=formatX C b G O ∧
  regValue layout.point.y t.basis=formatY C b G O ∧ t.basis (FlagEntry.pkW layout)=vB hc b R ∧
  ∀q,q∉layout.point.x++layout.point.y→q≠FlagEntry.pkW layout→t.basis q=u.basis q:=by
  dsimp only [t]
  rw [eqg]
  exact gt
 have tf:t.basis layout.point.finite=false:=(ht.2.2.2.2 _ finite_off_xy finite_off_pk).trans uf
 have tg:t.basis layout.genericSelect=G:=(ht.2.2.2.2 _ generic_off_xy generic_off_pk).trans ug
 have tb':t.basis layout.control=false:=by
  change (run (borrowGeneric cx cy) mg u).basis layout.control=false
  rw [eqg]
  exact (run_preserves_outside _ _ _ _ (generic_control_free cx cy)).trans ub
 have tpool:∀q∈layout.dialogPool,q≠FlagEntry.pkW layout→t.basis q=false:=by
  intro q hq hpq
  exact (ht.2.2.2.2 q (pool_off_xy q hq) hpq).trans (upool q hq hpq)
 let v:=put t layout.control b
 have load:run loadB ml t=v:=by
  have h:=loadB_run t ml (formatX C b G O) (formatY C b G O) ht.2.1 ht.2.2.1 tf
   (fun q hq=>tpool _ (marker_work_pool q hq) (marker_work_off_pk q hq)) tb'
  rw [tg,format_recover C b G O hgb] at h
  exact h
 have vx:regValue layout.point.x v.basis=formatX C b G O:=
  (put_reg _ _ _ _ (by decide +kernel)).trans ht.2.1
 have vy:regValue layout.point.y v.basis=formatY C b G O:=
  (put_reg _ _ _ _ (by decide +kernel)).trans ht.2.2.1
 have vg:v.basis layout.genericSelect=G:=(put_away t _ _ b generic_off_control).trans tg
 have vb:v.basis layout.control=b:=put_at _ _ _
 have vz:∀i:Fin 9,v.basis (w i.val)=false:=by
  intro i
  exact (put_away t _ _ b (work_off_control i)).trans (tpool _ (work_pool i) (work_off_pk i))
 have houtcorner:(b && !G)=true→ControlSentinelDevelop.corner C O:=by
  intro h
  have hh:∀b g:Bool,(b && !g)=true→g=false:=by decide
  have hg0:G=false:=hh b G h
  simpa only [O,hg0,Bool.false_eq_true,if_false] using hcorner h
 have hout:=decode_spec hc b G O v md hgb houtcorner vx vy vb vg vz
 let z:=run (decode C) md v
 have hzout:XYResult v z (ControlSentinelDevelop.ordinaryX O) (pointY O):=hout.1
 refine ⟨erase,load,?_,?_,?_,?_,?_⟩
 · exact hzout.phase.trans (ht.1.trans ha.phase)
 · exact hzout.x
 · exact hzout.y
 · exact (hzout.rest _ (pool_off_xy _ (FlagEntry.pk_pool layout layout_widths))).trans
    ((put_away t _ _ b pk_off_control).trans ht.2.2.2.1)
 · intro q hq hpq
   rw [hzout.rest q hq]
   by_cases hqb:q=layout.control
   · subst q;exact vb.trans hb.symm
   · exact (put_away t _ _ b hqb).trans ((ht.2.2.2.2 q hq hpq).trans
      ((put_away a _ _ false hqb).trans (ha.rest q hq)))

#print axioms middle_sequence
end
end ECDSAAdd.Entrant.OwnFirstYQ

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnFirstYQ
open ControlPointEncodingDevelop
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel FlagTop FlagExit FlagTop2 ParityEven ControlGenericPointDevelop
attribute [local irreducible] layout run
open Classical in
theorem middle_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
 (s : State) (m : List Bool)
 (hx : regValue layout.point.x s.basis = ControlSentinelDevelop.ordinaryX R)
 (hy : regValue layout.point.y s.basis = pointY R)
 (hb:s.basis layout.control=b)
 (hf : s.basis layout.point.finite = false)
 (hg : s.basis layout.genericSelect = dialogOrdinary b R (.some hc))
 (he : s.basis layout.core.equalNegY = false) (hd : s.basis layout.doubleSelect = false)
 (hz : ∀q∈layout.dialogPool,q≠FlagEntry.pkW layout→s.basis q=false)
 (hpk:s.basis (FlagEntry.pkW layout)=(dialogOrdinary b R (.some hc) && decide ((triOf (.some hc)).A < ControlSentinelDevelop.ordinaryX R))) :
 let O:=if dialogOrdinary b R (.some hc) then R+.some hc else R
 MiddleResult s (run (middle (.some hc) cx cy) m s) (ControlSentinelDevelop.ordinaryX O) (pointY O) (vB hc b R) := by
 let C:Point:=.some hc
 let d1:=m.drop (measurementCount (encode C))
 let d2:=d1.drop (measurementCount eraseB)
 let d3:=d2.drop (measurementCount (borrowGeneric cx cy))
 let d4:=d3.drop (measurementCount loadB)
 let me:=m.take (measurementCount (encode C))
 let ma:=d1.take (measurementCount eraseB)
 let mg:=d2.take (measurementCount (borrowGeneric cx cy))
 let ml:=d3.take (measurementCount loadB)
 have h:=middle_sequence hc b R s me ma mg ml d4 hx hy hb hf hg he hd hz hpk
 dsimp only at h
 obtain ⟨her,hload,hout⟩:=h
 unfold middle
 simp only [List.append_assoc]
 rw [run_append,run_append,run_append,run_append]
 rw [her,hload]
 exact hout

open Classical in
theorem middle_eq_generic {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
 (s : State) (m n : List Bool)
 (hx : regValue layout.point.x s.basis = ControlSentinelDevelop.ordinaryX R)
 (hy : regValue layout.point.y s.basis = pointY R)
 (hb:s.basis layout.control=b)
 (hf : s.basis layout.point.finite = false)
 (hg : s.basis layout.genericSelect = dialogOrdinary b R (.some hc))
 (he : s.basis layout.core.equalNegY = false) (hd : s.basis layout.doubleSelect = false)
 (hz : ∀q∈layout.dialogPool,q≠FlagEntry.pkW layout→s.basis q=false)
 (hpk:s.basis (FlagEntry.pkW layout)=(dialogOrdinary b R (.some hc) && decide ((triOf (.some hc)).A < ControlSentinelDevelop.ordinaryX R))) :
 run (middle (.some hc) cx cy) m s=run (genericBlock cx cy) n s := by
 have hm:=middle_run hc b R s m hx hy hb hf hg he hd hz hpk
 have hg:=generic_parked_run hc b R s n (by simpa only [codeX_ordinary] using hx) hy hf hg he hd hz
  (by simpa only [codeX_ordinary] using hpk)
 apply middleResult_unique hm
 exact ⟨hg.1,by simpa only [codeX_ordinary] using hg.2.1,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2⟩

#print axioms middle_run
#print axioms middle_eq_generic
end ECDSAAdd.Entrant.OwnFirstYQ

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnFirstYQ
open ControlPointEncodingDevelop
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel
attribute [local irreducible] layout run

theorem middle_metrics (C : Point) (cx cy : Fp) :
 toffoliCount (middle C cx cy)=toffoliCount (genericBlock cx cy)+523 ∧
 measurementCount (middle C cx cy)=measurementCount (genericBlock cx cy)+515 ∧
 gateSlots (middle C cx cy)≤gateSlots (genericBlock cx cy)+7816 := by
 have h:=counts C
 have hm:=marker_counts
 have hs:=marker_slots
 have he:=encoding_slots C
 simp only [middle,borrowGeneric,toffoliCount_append,measurementCount_append,gateSlots_append,
  (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
 omega
 theorem middle_physical (C : Point) (cx cy : Fp) : GatePhysical (middle C cx cy) := by
 have he:=physical C
 have hm:=marker_physical
 have hg:=borrowGeneric_physical cx cy
 simp only [middle,gatePhysical_append]
 tauto

#print axioms middle_metrics
#print axioms middle_physical
end ECDSAAdd.Entrant.OwnFirstYQ

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnFirstYQ
open ControlPointEncodingDevelop
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel FlagTop FlagExit FlagTop2 FlagEntry ParityEven ControlGenericPointDevelop ControlTapeDevelop
attribute [local irreducible] layout run
noncomputable section
open Classical

def finiteBorrow (C : Point) (cx cy : Fp) : Program :=
 stageNew layout C (pkW layout) ++ middle C cx cy ++ borrowOut C
 def wrapperBorrow (C : Point) (cx cy : Fp) : Program :=
 renameProgram (Wrapper5.U layout) (finiteBorrow C cx cy)

theorem finiteBorrow_correct {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
 (s : State) (m : List Bool) (hs:PointDialogBoundary layout R b (fun _=>false) s.basis) :
 (run (finiteBorrow (.some hc) cx cy) m s).phase=s.phase ∧
 PointDialogBoundary layout (if b then R+.some hc else R) b (fun _=>false)
  (run (finiteBorrow (.some hc) cx cy) m s).basis := by
 let C:Point:=.some hc
 let P:=stageNew layout C (pkW layout)
 let ds:=m.take (measurementCount P)
 let d1:=m.drop (measurementCount P)
 let dm:=d1.take (measurementCount (middle C cx cy))
 let dout:=d1.drop (measurementCount (middle C cx cy))
 let s1:=run P ds s
 let q:=run (genericBlock cx cy) [] s1
 have hv:=stage_values hc b R s ds hs
 have eqmid:=middle_eq_generic hc b R s1 dm [] hv.x hv.y hv.control hv.finite hv.generic hv.eneg hv.double hv.clean hv.parked
 let oldTape:=pfx (measurementCount P) ds++(pfx (measurementCount (genericBlock cx cy)) []++dout)
 have hold:run (finiteN layout C cx cy) oldTape s=run (OutFlag.outNew layout C) dout q:=by
  simpa only [finiteN,genericBlock,List.append_assoc] using
   run_three_tapes P (genericBlock cx cy) (OutFlag.outNew layout C) ds [] dout s
 have ho:=finite_run_N hc b R s oldTape hs
 rw [hold] at ho
 have hq:=generic_parked_run hc b R s1 [] (by simpa only [codeX_ordinary] using hv.x) hv.y hv.finite hv.generic hv.eneg hv.double hv.clean
  (by simpa only [codeX_ordinary] using hv.parked)
 have qD:q.basis layout.doubleSelect=false:=(hq.2.2.2.2 _ double_off_xy double_off_pk).trans hv.double
 have qp:q.basis (layout.core.poolWire 511)=false:=by
  have hm:layout.core.poolWire 511∈layout.dialogPool:=Square5Placement.pool_member layout layout_widths 511 (by decide)
  have hn:layout.core.poolWire 511≠pkW layout:=by decide +kernel
  exact (hq.2.2.2.2 _ (pool_off_xy _ hm) hn).trans (hv.clean _ hm hn)
 have hD:(run (OutFlag.outNew layout C) dout q).basis layout.doubleSelect=false:=ho.2.flags _ (by simp [flags_list])
 have hout:=borrowOut_run hc q dout qD qp hD
 unfold finiteBorrow
 rw [List.append_assoc,run_append,run_append]
 change (run (borrowOut C) dout (run (middle C cx cy) dm s1)).phase=s.phase ∧ _
 rw [eqmid,hout]
 exact ho

theorem wrapperBorrow_correct {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
 Triple (PointDialogBoundary layout R b (fun _=>false)) (wrapperBorrow (.some hc) cx cy)
  (PointDialogBoundary layout (if b then R+.some hc else R) b (fun _=>false)) := by
 intro s m hs
 have h:=finiteBorrow_correct hc b R s m hs
 unfold wrapperBorrow
 rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
  (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
 exact h

#print axioms finiteBorrow_correct
#print axioms wrapperBorrow_correct
end
end ECDSAAdd.Entrant.OwnFirstYQ


-- Linearized exceptional-control classifiers.
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnFirstYQ
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel ControlPointEncodingDevelop
attribute [local irreducible] layout wires run

theorem middle_subset (C : Point) (cx cy : Fp) : wires (middle C cx cy)⊆wires (ControlPointEncodingDevelop.middle C cx cy) := by
 have h:=encoding_support C
 simp only [middle,ControlPointEncodingDevelop.middle,wires_append]
 exact Finset.union_subset_union
  (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union h.1 erase_subset) (Finset.Subset.refl _)) load_subset) h.2
 theorem finite_subset (C : Point) (cx cy : Fp) : wires (finiteBorrow C cx cy)⊆wires (ControlPointEncodingDevelop.finiteBorrow C cx cy) := by
 simp only [finiteBorrow,ControlPointEncodingDevelop.finiteBorrow,wires_append]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) (middle_subset C cx cy)) (Finset.Subset.refl _)
 theorem wrapper_subset (C : Point) (cx cy : Fp) : wires (wrapperBorrow C cx cy)⊆wires (ControlPointEncodingDevelop.wrapperBorrow C cx cy) := by
 simp only [wrapperBorrow,ControlPointEncodingDevelop.wrapperBorrow,renameProgram_support]
 exact Finset.image_subset_image (finite_subset C cx cy)
 theorem wrapperBorrow_qubits {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : qubits (wrapperBorrow (.some hc) cx cy)≤1586 :=
 (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl _) (wrapper_subset (.some hc) cx cy))).trans (ControlPointEncodingDevelop.wrapperBorrow_qubits hc)

#print axioms wrapperBorrow_qubits
end ECDSAAdd.Entrant.OwnFirstYQ

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnFirstYQ
open ControlPointEncodingDevelop
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel FlagTop FlagExit FlagTop2 FlagEntry ParityEven
attribute [local irreducible] layout wires run

theorem support_used_borrow {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
 wires (wrapperBorrow (.some hc) cx cy)⊆layout.dialogUsedWires.toFinset := by
 exact (wrapper_subset (.some hc) cx cy).trans (ControlPointEncodingDevelop.support_used_borrow hc)

open Classical in
theorem full_spec_borrow {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
 {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperBorrow (.some hc) cx cy
 {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
 intro s m hs
 have hz:regValue layout.work s.basis=0:=hs.2
 have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
  (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
 have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
  refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
  exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
 have a:=wrapperBorrow_correct hc b R s m hi
 have old:=InputSentinel530.wrapper530_spec hc b R s m hi
 rw [MeasuredDH.boundary_unique layout _ _ (support_used_borrow hc) (InputSentinel530.support_used530 hc)
  s m _ b a.2 old.2 (a.1.trans old.1.symm)]
 exact InputSentinel530.full_spec530 hc b R s m hs

theorem wrapperBorrow_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GatePhysical (wrapperBorrow (.some hc) cx cy) := by
 unfold wrapperBorrow
 apply gatePhysical_rename _ (Wrapper5.U layout).injective
 simp only [finiteBorrow,gatePhysical_append]
 exact ⟨⟨FlagTop.stageNew_physical hc,middle_physical (.some hc) cx cy⟩,borrowOut_physical hc⟩

theorem wrapperBorrow_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
 toffoliCount (wrapperBorrow (.some hc) cx cy)=toffoliCount (wrapperN layout (.some hc) cx cy)+523 ∧
 measurementCount (wrapperBorrow (.some hc) cx cy)=measurementCount (wrapperN layout (.some hc) cx cy)+515 ∧
 gateSlots (wrapperBorrow (.some hc) cx cy)≤gateSlots (wrapperN layout (.some hc) cx cy)+7816 := by
 have h:=middle_metrics (.some hc) cx cy
 simp only [genericBlock,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots] at h
 simp only [wrapperBorrow,finiteBorrow,wrapperN,finiteN,borrowOut,toffoliCount_append,measurementCount_append,gateSlots_append,
  (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
 omega

def programQ (C : Point) : Program :=
 match C with
 | .zero=>[]
 | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperBorrow C cx cy
 def entryQ : Challenge.Entry :=fun C=>normalizeProgram (programQ C)
 def boundsQ : Challenge.Bounds :=⟨2148202,1498902,1586,50264772⟩

theorem program_correct_Q (C : Point) (b : Bool) (R : Point) :
 Triple (encodes b R) (programQ C) (encodes b (if b then R+C else R)) := by
 cases C with
 | zero=>
  intro s m hs
  simpa only [programQ,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self] using And.intro (Eq.refl s.phase) hs
 | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec_borrow hc b R) (support_used_borrow hc)
 theorem program_toffoli_Q (C : Point) : toffoliCount (programQ C)≤2148202 := by
 cases C with
 | zero=>simp [programQ,toffoliCount]
 | @some cx cy hc=>
  have h:=program_toffoli_B (.some hc)
  have d:=(wrapperBorrow_metrics hc).1
  change toffoliCount (wrapperN layout (.some hc) cx cy)≤2147679 at h
  change toffoliCount (wrapperBorrow (.some hc) cx cy)≤2148202
  omega
 theorem program_measurements_Q (C : Point) : measurementCount (programQ C)≤1498902 := by
 cases C with
 | zero=>simp [programQ,measurementCount]
 | @some cx cy hc=>
  have h:=program_measurements_B (.some hc)
  have d:=(wrapperBorrow_metrics hc).2.1
  change measurementCount (wrapperN layout (.some hc) cx cy)≤1498385 at h
  change measurementCount (wrapperBorrow (.some hc) cx cy)≤1498902
  omega
 theorem program_qubits_Q (C : Point) : qubits (programQ C)≤1586 := by
 cases C with
 | zero=>change qubits []≤1586;rw [qubits_empty];decide
 | @some cx cy hc=>exact wrapperBorrow_qubits hc
 theorem program_physical_Q (C : Point) : GatePhysical (programQ C) := by
 cases C with
 | zero=>simp [programQ,GatePhysical]
 | @some cx cy hc=>exact wrapperBorrow_physical hc
 theorem program_slots_Q (C : Point) : gateSlots (programQ C)≤50264772 := by
 cases C with
 | zero=>simp [programQ,gateSlots]
 | @some cx cy hc=>
  have h:=program_slots_B (.some hc)
  have d:=(wrapperBorrow_metrics hc).2.2
  change gateSlots (wrapperN layout (.some hc) cx cy)≤50256956 at h
  change gateSlots (wrapperBorrow (.some hc) cx cy)≤50264772
  omega
 theorem certificateQ : Challenge.Certificate entryQ boundsQ where
 correct C b R:=(normalize_triple _ _ _).mpr (program_correct_Q C b R)
 physical C:=Baselines.normalize_physical _ (by simpa only [GatePhysical] using program_physical_Q C)
 toffoli_le C:=(normalize_toffoli _).trans (program_toffoli_Q C)
 measurements_le C:=by
  change measurementCount (normalizeProgram (programQ C))≤1498902
  rw [normalize_measurements];exact program_measurements_Q C
 qubits_le C:=by
  change qubits (normalizeProgram (programQ C))≤1586
  rw [normalize_qubits];exact program_qubits_Q C
 gateSlots_le C:=by
  change gateSlots (normalizeProgram (programQ C))≤50264772
  rw [Baselines.normalize_slots];exact program_slots_Q C

#print axioms certificateQ
end ECDSAAdd.Entrant.OwnFirstYQ


namespace ECDSAAdd.Entrant
noncomputable def program := OwnFirstYQ.programQ
noncomputable def entry := OwnFirstYQ.entryQ
def bounds := OwnFirstYQ.boundsQ
theorem certificate : Challenge.Certificate entry bounds := OwnFirstYQ.certificateQ
end ECDSAAdd.Entrant
