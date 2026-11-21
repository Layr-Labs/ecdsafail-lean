import ECDSAAdd.Submission.Entrant.Window
import ECDSAAdd.Submission.Entrant.ShadowGates
import ECDSAAdd.Submission.Entrant.ShadowParts
import ECDSAAdd.Submission.Entrant.ShadowRoute
import ECDSAAdd.Submission.Entrant.ShadowRouteCover
import ECDSAAdd.Submission.Entrant.ShadowLeaveFacts
import ECDSAAdd.Submission.Entrant.ShadowPortalFacts
import ECDSAAdd.Submission.Entrant.ShadowEntryFacts
import ECDSAAdd.Submission.Entrant.ShadowEnterJ
import ECDSAAdd.Submission.Entrant.ShadowGeometry
import ECDSAAdd.Submission.Entrant.ShadowBox2
import ECDSAAdd.Submission.Entrant.ShadowLeave
import ECDSAAdd.Submission.Entrant.ShadowLeaveMove
import ECDSAAdd.Submission.Entrant.ShadowPortal90
import ECDSAAdd.Submission.Entrant.ShadowExit390

namespace ECDSAAdd.Entrant.StairPacket.ArchiveJ7
open Arithmetic Partial

theorem head_port_eq (j : Fin 23) (i : Fin 16) :
    ArchiveJ.codePorts j ⟨i.val, by omega⟩ = ArchiveJ7.codePorts j ⟨i.val, by omega⟩ := by
  have hi : i.val < (cellsRestoreP (start j + 15)).length := by
    have h : (cellsRestoreP (start j + 15)).length = 16 := by simp [cellsRestoreP]
    rw [h]
    exact i.isLt
  simp only [ArchiveJ.codePorts, ArchiveJ7.codePorts, ArchiveJ.code_split, ArchiveJ7.code_split, List.append_assoc]
  rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]

theorem kept_stock (j : Fin 23) (d : Bool) (row : Nat) (s : State)
    (h : Kept (ArchiveJ7.codePorts j) d row s) : Kept (ArchiveJ.codePorts j) d row s := by
  intro i
  rw [head_port_eq j i]
  exact h i

end ECDSAAdd.Entrant.StairPacket.ArchiveJ7
/-! build-chain: Shadow7 renders of the stock window families ArchiveJ, NativeJ, LeaveJ.ArchiveCut, LeaveJ.AssembleCut, LeaveJ.CertifiedCut, LeaveJ.BodyCut, NativeFirstJ, StockWindowW (helpers/build-chain/shadow/render7.py). -/

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw ArchivePortAction
namespace ArchiveJ7
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-- Source and loader blocks: the archive of block `i` is read from block `i`'s first ten ticks and loaded inside
block `i+1` (`next`). -/
def next (i : Fin 23) (hi : i.val≤20) : Fin 23 := ⟨i.val+1,by omega⟩
theorem chronological_all : ∀ i : Fin 23, i.val≤20 → ∀k:Fin 20, rawPorts i ⟨k,by omega⟩=nativeRawPort i k := by
  decide +kernel
theorem observed (i : Fin 23) (hi : i.val≤20) (before now:State)
    (kept:∀q:Fin 20,now.basis (rawPorts i ⟨q,by omega⟩)=before.basis (rawPorts i ⟨q,by omega⟩))
    (far u c:Bool) (tags:now.basis (rawPorts i 20)=far ∧ now.basis (rawPorts i 21)=u ∧ now.basis (rawPorts i 22)=c) :
    let cells:=readCells (Shadow7.shape i) 0 15 (mappedBasis i before.basis)
    ∀k:Fin 157,k.val<23 → now.basis (rawPorts i k)=rawBit (read (cells.drop 5)) far u c k := by
  dsimp only
  intro k bound
  by_cases young:k.val<20
  · let col:Fin 20:=⟨k,young⟩
    refine (kept col).trans ?_
    rw [chronological_all i hi col]
    exact (Shadow7.native_raw_read i before k young).trans (by simp [rawBit,young])
  · have eq:k=20 ∨ k=21 ∨ k=22:=by omega
    rcases eq with rfl|rfl|rfl
    · exact tags.1
    · exact tags.2.1
    · exact tags.2.2
end ArchiveJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Generic native pack of block `j` (par-c2): the stock pack at tick `s-10` (`s = start j`) in the `OB5.sig s`
frame, then the window archive of block `j-1` (`Shadow7.archiveLoadP (prev j)`). dadon's `NativePack{s}` is
`NativeJ` at `j = (s-75)/15`. Valid for `2 ≤ j` (the pack is due: `s-10 ≥ 95`, `s-10 ≡ 0 mod 5`). -/

def prev (j : Fin 23) : Fin 23 := ⟨j.val-1,by omega⟩
def program (j : Fin 23) (d:Bool) := renameProgram (OB5.sig (start j)) (Rolling1588.packAtTick d (start j-10))
def reverse (j : Fin 23) (d:Bool) := renameProgram (OB5.sig (start j)) (Rolling1588.unpackAtTick d (start j-10))
def support (j : Fin 23) :=
  (List.range' (start j-15) 5).flatMap fun v=>[OB5.sig (start j) (base v),OB5.sig (start j) (base (1028+v))]
def history (j : Fin 23) (q:Fin 10) := OB5.sig (start j) (History5.historyMap base (start j-15) q)

theorem due (j : Fin 23) (h : 1≤j.val) : ¬start j-10=5 ∧ History5.packDue (start j-10)=true ∧
    start j-10-5=start j-15 := by
  have hj:=j.isLt
  simp only [History5.packDue,start,decide_eq_true_eq]
  omega

theorem equals (j : Fin 23) (h : 1≤j.val) (d:Bool) :
    program j d=Rolling1588.codeEncodeAt d (history j) ∧ reverse j d=Rolling1588.codeDecodeAt d (history j) := by
  obtain ⟨n5,dueP,sub⟩:=due j h
  have lab : ∀ q∈Finset.range 10, (OB5.sig (start j) ∘ MeasuredCodec5.label (History5.historyMap base (start j-15))) q=
      MeasuredCodec5.label (history j) q := by
    intro q hq
    have lt:=Finset.mem_range.mp hq
    simp only [Function.comp,MeasuredCodec5.label,history,dif_pos lt]
  constructor
  · unfold program Rolling1588.packAtTick Rolling1588.codeEncodeAt
    rw [if_neg n5,if_pos dueP,sub,renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    rw [(Rolling1588.code_support d).1] at hq
    exact lab q hq
  · unfold reverse Rolling1588.unpackAtTick Rolling1588.codeDecodeAt
    rw [if_neg n5,if_pos dueP,sub,renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    rw [(Rolling1588.code_support d).2] at hq
    exact lab q hq

theorem history_mem (j : Fin 23) (q:Fin 10) : history j q∈support j := by
  have hq:=q.isLt
  simp only [history,support,History5.historyMap,History5.historyId,List.mem_flatMap,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  refine ⟨start j-15+q.val/2,⟨by omega,by omega⟩,?_⟩
  split
  · exact Or.inl rfl
  · right; congr 2; omega

theorem histInj (j : Fin 23) : Function.Injective (history j) := by
  intro a b eq
  have inv:=OB5.sig_invol (start j) (by have:=j.isLt;simp only [start];omega)
  have e:=congrArg (OB5.sig (start j)) eq
  simp only [history,inv,History5.historyMap,History5.historyId,base] at e
  have ha:=a.isLt; have hb:=b.isLt
  apply Fin.ext
  split at e <;> split at e <;> simp only [Wire] at * <;> omega

theorem codes (j : Fin 23) (h : 1≤j.val) (d:Bool) :
    wires (program j d)⊆(support j).toFinset ∧ wires (reverse j d)⊆(support j).toFinset := by
  rw [(equals j h d).1,(equals j h d).2,Rolling1588.codeEncodeAt,Rolling1588.codeDecodeAt,
    renameProgram_support,renameProgram_support,(Rolling1588.code_support d).1,(Rolling1588.code_support d).2]
  have img : Finset.image (MeasuredCodec5.label (history j)) (Finset.range 10)⊆(support j).toFinset := by
    intro q hq
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hq
    have lt:=Finset.mem_range.mp hw
    simp only [MeasuredCodec5.label,dif_pos lt,List.mem_toFinset]
    exact history_mem j ⟨w,lt⟩
  exact ⟨img,img⟩

theorem watchFree_all : ∀ j : Fin 23, (Shadow7.watch j).all (fun q=>decide (q∉support j)) := by decide +kernel
theorem disjoint (j : Fin 23) : ∀q∈support j,q∉Shadow7.watch j :=
  fun q hs hw=>(of_decide_eq_true (List.all_eq_true.mp (watchFree_all j) q hw)) hs

theorem retains (j : Fin 23) (h : 1≤j.val) (d back:Bool) (s:State) (m:List Bool) :
    ∀q∈Shadow7.watch j,(run (if back then reverse j d else program j d) m s).basis q=s.basis q:=by
  intro q hq
  apply run_preserves_outside
  intro used
  have seen:q∈(support j).toFinset:=by
    cases back
    · exact (codes j h d).1 used
    · exact (codes j h d).2 used
  exact disjoint j _ (List.mem_toFinset.mp seen) hq

theorem source_law (j : Fin 23) (h : 1≤j.val) (d:Bool) (s:State) (m:List Bool)
    (ok:MeasuredCodec5.legalAt (history j) s.basis) :
    (run (program j d) m s).phase=s.phase ∧ ∀t,run (reverse j d) t (run (program j d) m s)=s:=by
  rw [(equals j h d).1,(equals j h d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d (history j) (histInj j) s m ok).1,
    fun t=>Rolling1588.codeRoundtripAt d (history j) (histInj j) s m t ok⟩

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Generic first-form native pack (par-c2): the window's first block `j` (`s = start j`) packs the five
pre-window letters at tick `s` (group `s-5`) in the `OB5.sig s` frame; no archive. dadon's `NativePack225`
(first block of 225..270) is `NativeFirstJ7 10`. -/

def program (j : Fin 23) (d:Bool) := renameProgram (OB5.sig (start j)) (Rolling1588.packAtTick d (start j))
def reverse (j : Fin 23) (d:Bool) := renameProgram (OB5.sig (start j)) (Rolling1588.unpackAtTick d (start j))
def support (j : Fin 23) :=
  (List.range' (start j-5) 5).flatMap fun v=>[OB5.sig (start j) (base v),OB5.sig (start j) (base (1028+v))]
def history (j : Fin 23) (q:Fin 10) := OB5.sig (start j) (History5.historyMap base (start j-5) q)

theorem due (j : Fin 23) (h : 1≤j.val) : ¬start j=5 ∧ History5.packDue (start j)=true := by
  have hj:=j.isLt
  simp only [History5.packDue,start,decide_eq_true_eq]
  omega

theorem equals (j : Fin 23) (h : 1≤j.val) (d:Bool) :
    program j d=Rolling1588.codeEncodeAt d (history j) ∧ reverse j d=Rolling1588.codeDecodeAt d (history j) := by
  obtain ⟨n5,dueP⟩:=due j h
  have lab : ∀ q∈Finset.range 10, (OB5.sig (start j) ∘ MeasuredCodec5.label (History5.historyMap base (start j-5))) q=
      MeasuredCodec5.label (history j) q := by
    intro q hq
    have lt:=Finset.mem_range.mp hq
    simp only [Function.comp,MeasuredCodec5.label,history,dif_pos lt]
  constructor
  · unfold program Rolling1588.packAtTick Rolling1588.codeEncodeAt
    rw [if_neg n5,if_pos dueP,renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    rw [(Rolling1588.code_support d).1] at hq
    exact lab q hq
  · unfold reverse Rolling1588.unpackAtTick Rolling1588.codeDecodeAt
    rw [if_neg n5,if_pos dueP,renameProgram_comp]
    apply renameProgram_congr_support
    intro q hq
    rw [(Rolling1588.code_support d).2] at hq
    exact lab q hq

theorem history_mem (j : Fin 23) (q:Fin 10) : history j q∈support j := by
  have hq:=q.isLt
  simp only [history,support,History5.historyMap,History5.historyId,List.mem_flatMap,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  refine ⟨start j-5+q.val/2,⟨by omega,by omega⟩,?_⟩
  split
  · exact Or.inl rfl
  · right; congr 2; omega

theorem histInj (j : Fin 23) : Function.Injective (history j) := by
  intro a b eq
  have inv:=OB5.sig_invol (start j) (by have:=j.isLt;simp only [start];omega)
  have e:=congrArg (OB5.sig (start j)) eq
  simp only [history,inv,History5.historyMap,History5.historyId,base] at e
  have ha:=a.isLt; have hb:=b.isLt
  apply Fin.ext
  split at e <;> split at e <;> simp only [Wire] at * <;> omega

theorem codes (j : Fin 23) (h : 1≤j.val) (d:Bool) :
    wires (program j d)⊆(support j).toFinset ∧ wires (reverse j d)⊆(support j).toFinset := by
  rw [(equals j h d).1,(equals j h d).2,Rolling1588.codeEncodeAt,Rolling1588.codeDecodeAt,
    renameProgram_support,renameProgram_support,(Rolling1588.code_support d).1,(Rolling1588.code_support d).2]
  have img : Finset.image (MeasuredCodec5.label (history j)) (Finset.range 10)⊆(support j).toFinset := by
    intro q hq
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hq
    have lt:=Finset.mem_range.mp hw
    simp only [MeasuredCodec5.label,dif_pos lt,List.mem_toFinset]
    exact history_mem j ⟨w,lt⟩
  exact ⟨img,img⟩

theorem watchFree_all : ∀ j : Fin 23, (Shadow7.watch j).all (fun q=>decide (q∉support j)) := by decide +kernel
theorem disjoint (j : Fin 23) : ∀q∈support j,q∉Shadow7.watch j :=
  fun q hs hw=>(of_decide_eq_true (List.all_eq_true.mp (watchFree_all j) q hw)) hs

theorem retains (j : Fin 23) (h : 1≤j.val) (d back:Bool) (s:State) (m:List Bool) :
    ∀q∈Shadow7.watch j,(run (if back then reverse j d else program j d) m s).basis q=s.basis q:=by
  intro q hq
  apply run_preserves_outside
  intro used
  have seen:q∈(support j).toFinset:=by
    cases back
    · exact (codes j h d).1 used
    · exact (codes j h d).2 used
  exact disjoint j _ (List.mem_toFinset.mp seen) hq

theorem source_law (j : Fin 23) (h : 1≤j.val) (d:Bool) (s:State) (m:List Bool)
    (ok:MeasuredCodec5.legalAt (history j) s.basis) :
    (run (program j d) m s).phase=s.phase ∧ ∀t,run (reverse j d) t (run (program j d) m s)=s:=by
  rw [(equals j h d).1,(equals j h d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d (history j) (histInj j) s m ok).1,
    fun t=>Rolling1588.codeRoundtripAt d (history j) (histInj j) s m t ok⟩

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket CodecBitSliceVerify ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace ArchiveJ7
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
theorem scratch_code (i : Fin 23) (k : Fin 157) (h : 23≤k.val) : rawPorts i k=codePorts i ⟨k.val-7,by omega⟩ := by
  have a:=raw_scratch i (k:=k.val-23) (by omega)
  have b:=code_scratch i (k:=k.val-23) (by omega)
  rw [show 23+(k.val-23)=k.val by omega] at a
  rw [show 16+(k.val-23)=k.val-7 by omega] at b
  exact a.trans b.symm
theorem pastFree_all : ∀ i : Fin 23,
    (if hi : i.val≤20 then (Shadow7.watch (next i hi)).all (fun q=>decide (q∉rawHead i)) else true)=true := by
  decide +kernel
theorem past_only (i : Fin 23) (hi : i.val≤20) : ∀k:Fin 23, rawPorts i ⟨k,by omega⟩∉Shadow7.watch (next i hi) := by
  intro k hw
  have all:=pastFree_all i
  rw [dif_pos hi] at all
  have off:=of_decide_eq_true (List.all_eq_true.mp all _ hw)
  apply off
  have e:rawPorts i ⟨k,by omega⟩=(rawHead i).getD k 0:=by
    rw [rawPorts,raw_split,List.getD_append _ _ _ _ (by simp [rawHead,cellsLoadP])]
  rw [e,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp [rawHead,cellsLoadP]),Option.getD_some]
  exact List.getElem_mem _
/-- `ArchiveBoundary{t}.retain_watch`, generic: the load keeps every watched wire of the loader block, given that the
watched scratch wires are clean before the load (dadon: carry wires; late blocks: also future history ports). -/
theorem retain_watch (i : Fin 23) (hi : i.val≤20) (d:Bool) (row:Nat) (s t:State)
    (clean:∀k:Fin 157,23≤k.val → rawPorts i k∈Shadow7.watch (next i hi) → s.basis (rawPorts i k)=false)
    (frame:Frame (codePorts i) (code d) row t)
    (outside:∀q,(∀k,rawPorts i k≠q) → t.basis q=s.basis q) :
    ∀q∈Shadow7.watch (next i hi),t.basis q=s.basis q := by
  intro q h
  by_cases mem:∃k,rawPorts i k=q
  · obtain ⟨k,rfl⟩:=mem
    have hk:23≤ k.val:=by
      by_contra! bad
      exact past_only i hi ⟨k,bad⟩ h
    rw [clean k hk h,scratch_code i k hk,frame,archive_blank _ _ (by dsimp;omega),Nat.zero_testBit]
  · exact outside _ (fun k eq=>mem ⟨k,eq⟩)
end ArchiveJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run Shadow7.unrouted Shadow7.onRails
namespace NativeJ7
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-- Block `j`'s administrative piece: the pack, then the window archive of block `j-1`. -/
def withArchive (j : Fin 23) (d:Bool) := program j d++Shadow7.archiveLoadP (prev j) d
def fromArchive (j : Fin 23) (d:Bool) := Shadow7.archiveRestoreP (prev j) d++reverse j d
theorem next_prev (j : Fin 23) (h3 : 1≤j.val) (h19 : j.val≤21) : ArchiveJ7.next (prev j) (by simp only [prev]; omega)=j := by
  apply Fin.ext; simp only [ArchiveJ7.next,prev]; omega

theorem admin (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State)
    (active:Shadow7.onRails j 1 z s.basis) (ok:MeasuredCodec5.legalAt (history j) s.basis)
    (row:Nat) (limit:row<63145)
    (raw:Frame (ArchiveJ7.rawPorts (prev j)) ArchivePortAction.raw row (run (program j d) m s))
    (clean:∀k:Fin 157,23≤k.val → ArchiveJ7.rawPorts (prev j) k∈Shadow7.watch j →
      (run (program j d) m s).basis (ArchiveJ7.rawPorts (prev j) k)=false) :
    let out:=run (withArchive j d) m s
    Shadow7.AdminResult j (fromArchive j d) s out ∧ Frame (ArchiveJ7.codePorts (prev j)) (code d) row out := by
  have hp:(prev j).val≤20:=by simp only [prev]; omega
  have nx:=next_prev j (by omega) h19
  let p:=run (program j d) m s
  let tape:=m.drop (measurementCount (program j d))
  let a:=run (Shadow7.archiveLoadP (prev j) d) tape p
  have old:=source_law j h2 d s m ok
  have stay:=retains j h2 d false s m
  have now:=Shadow7.watch_congr j s p stay z active
  have arr:=ArchiveJ7.load_run (prev j) hp d row limit p tape raw
  have untouched:=ArchiveJ7.retain_watch (prev j) hp d row p a (by rw [nx]; exact clean) arr.2.1 arr.2.2
  rw [nx] at untouched
  dsimp only [withArchive,fromArchive]
  simp only [run_append,run_take]
  refine ⟨⟨arr.1.trans old.1,fun q h=>(untouched _ h).trans (stay _ h),?_⟩,arr.2.1⟩
  intro n
  rw [run_append,run_take]
  change run (reverse j d) _ (run (Shadow7.archiveRestoreP (prev j) d) _ a)=s
  rw [ArchiveJ7.roundtrip (prev j) hp d row limit p tape _ raw]
  exact old.2 _
end NativeJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
attribute [local irreducible] run Shadow7.unrouted Shadow7.onRails
namespace NativeJ7
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
def window (j : Fin 23) (d:Bool) := Shadow7.body j (withArchive j d)
def unwind (j : Fin 23) (d:Bool) := Shadow7.unbody j (fromArchive j d)
theorem window_run (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (start0:Shadow7.onRails j 0 z s.basis)
    (legal:MeasuredCodec5.legalAt (history j) (run (Shadow7.routed j 0 1) m s).basis)
    (row:Nat) (limit:row<63145) (frame:Frame (ArchiveJ7.rawPorts (prev j)) ArchivePortAction.raw row
      (run (program j d) (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m s)))
    (clean:∀k:Fin 157,23≤k.val → ArchiveJ7.rawPorts (prev j) k∈Shadow7.watch j →
      (run (program j d) (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m s)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false) :
    let out:=run (window j d) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unwind j d) n out=s := by
  apply Shadow7.body_run _ _ _ _ _ z odd start0
  exact (admin j h2 h19 d _ _ (SkywalkTrace.next z) (Shadow7.route_frame j 0 1 (by decide) z odd s m start0).2 legal row limit frame clean).1
end NativeJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed IntegerPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
theorem admin (j : Fin 23) (h : 1≤j.val) (d:Bool) (s:State) (m:List Bool) (ok:MeasuredCodec5.legalAt (history j) s.basis) :
    Shadow7.AdminResult j (reverse j d) s (run (program j d) m s) :=
  ⟨(source_law j h d s m ok).1,retains j h d false s m,(source_law j h d s m ok).2⟩
def window (j : Fin 23) (d:Bool) := Shadow7.body j (program j d)
def unwind (j : Fin 23) (d:Bool) := Shadow7.unbody j (reverse j d)
theorem window_run (j : Fin 23) (h : 1≤j.val) (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (start0:Shadow7.onRails j 0 z s.basis)
    (legal:MeasuredCodec5.legalAt (history j) (run (Shadow7.routed j 0 1) m s).basis) :
    let out:=run (window j d) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unwind j d) n out=s := by
  apply Shadow7.body_run _ _ _ _ _ z odd start0
  exact admin j h d _ _ legal
end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace SkywalkRails Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
namespace NativeJ7
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-! The head of block `j`'s window (`2 ≤ j ≤ 19`): enter, the Shadow7.routed first tick, the pack, then the archive
of block `j-1` read from `j-1`'s records. The archive scratch must be clean after the pack (`scratch`); for
`j ≤ 13` this follows from the rails (`scratch_rails`), later blocks need D2's invariant. -/

theorem rawHead_mem (i : Fin 23) (k : Fin 157) (hk : k.val<23) : ArchiveJ7.rawPorts i k∈ArchiveJ7.rawHead i := by
  have e:ArchiveJ7.rawPorts i k=(ArchiveJ7.rawHead i).getD k 0:=by
    rw [ArchiveJ7.rawPorts,ArchiveJ7.raw_split,List.getD_append _ _ _ _ (by simp [ArchiveJ7.rawHead,Partial.cellsLoadP]; omega)]
  rw [e,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp [ArchiveJ7.rawHead,Partial.cellsLoadP]; omega),
    Option.getD_some]
  exact List.getElem_mem _

theorem forwardTargets : ∀ g∈EnterProof.forward, CodecBitSliceVerify.target g≠8 ∧
    CodecBitSliceVerify.target g<EnterProof.width := by decide +kernel
/-- The enter writes only its ports, never its gate wire `s+15` (a control). -/
theorem enterTargets (j : Fin 23) : ∀g∈Shadow7.enterP j,
    CodecBitSliceVerify.target g≠EnterJ7.gate j ∧ CodecBitSliceVerify.target g∈EnterJ7.ports j := by
  intro g hg
  rw [EnterJ7.emitted j,renameProgram,List.mem_map] at hg
  obtain ⟨g0,h0,rfl⟩:=hg
  have t:CodecBitSliceVerify.target (renameInstr (EnterJ7.map j) g0)=EnterJ7.map j (CodecBitSliceVerify.target g0):=by
    cases g0 <;> rfl
  obtain ⟨n8,lt⟩:=forwardTargets g0 h0
  rw [t]
  refine ⟨fun e=>n8 ?_,?_⟩
  · have same:=EnterJ7.inc j ⟨_,lt⟩ ⟨8,by decide⟩ (e.trans (rfl : EnterJ7.gate j=EnterJ7.map j 8))
    exact congrArg Fin.val same
  · rw [EnterJ7.map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [EnterJ7.ports_length]; exact lt),
      Option.getD_some]
    exact List.getElem_mem _
theorem enter_readonly (j : Fin 23) {q : Wire} (h : q∉EnterJ7.ports j ∨ q=EnterJ7.gate j) :
    ∀g∈Shadow7.enterP j,CodecBitSliceVerify.target g≠q := by
  intro g hg eq
  obtain ⟨ng,mp⟩:=enterTargets j g hg
  rcases h with h|h
  · exact h (eq ▸ mp)
  · exact ng (eq.trans h)

/-- Interval form of `Shadow7.firstUnchanged`: the window wire is the previous-tick wire or off tick 0's ports. -/
def FirstFree (j : Fin 23) (r : Wire) : Prop :=
  r=start j+15 ∨ ¬(r=start j+1044 ∨ (start j+16≤r ∧ r≤start j+Shadow7.sbP (start j)+35) ∨ (786≤r ∧ r≤Shadow7.sbP (start j)+804) ∨
    (1556≤r ∧ r≤Shadow7.sbP (start j)+1573))
instance (j : Fin 23) (r : Wire) : Decidable (FirstFree j r) := by unfold FirstFree; infer_instance
theorem firstFree (j : Fin 23) {q : Wire} (h : FirstFree j (windowNet j q)) : Shadow7.firstUnchanged j q := by
  unfold Shadow7.firstUnchanged
  by_cases hp:(windowNet j q:Nat)=start j+15
  · left
    rw [hp]
    show start j+15=start j+0+16-1
    omega
  · right
    intro mem
    rcases h with h|h
    · exact hp h
    · apply h
      simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
        SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at mem
      simp only [Shadow7.sbP,Wire] at *
      omega

theorem heads_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 →
    (∀r:Fin 5,history j ⟨2*r.val,by omega⟩=windowNet (prev j) (IntegerPacket.ports (Shadow7.shape (prev j)) r).a0 ∧
      history j ⟨2*r.val+1,by omega⟩=windowNet (prev j) (IntegerPacket.ports (Shadow7.shape (prev j)) r).history) ∧
    (∀i:Fin 10,FirstFree j (windowNet j (history j i)) ∧ history j i∉EnterJ7.ports j) ∧
    (∀q∈ArchiveJ7.rawHead (prev j),FirstFree j (windowNet j q) ∧ (q∉EnterJ7.ports j ∨ q=EnterJ7.gate j) ∧ q∉support j) := by
  decide +kernel

theorem legal_prefix (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (s t:State)
    (legal:StairArchiveRaw.legal (readCells (Shadow7.shape (prev j)) 0 15 (mappedBasis (prev j) s.basis)))
    (kept:∀i,t.basis (history j i)=s.basis (history j i)) : MeasuredCodec5.legalAt (history j) t.basis := by
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  intro i
  rw [kept,kept,((heads_all j h2 h19).1 i).1,((heads_all j h2 h19).1 i).2]
  have good:=legal _ (member_cell (Shadow7.shape (prev j)) 15 0 i (mappedBasis (prev j) s.basis) (by have h:=i.isLt;omega))
  apply not_both
  simpa only [Nat.zero_add,cell,mappedBasis] using good
theorem prefix_kept (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (s:State) (e t:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z (run (Shadow7.enterP j) e s).basis) :
    let now:=run (Shadow7.routed j 0 1) t (run (Shadow7.enterP j) e s)
    ∀i,now.basis (history j i)=s.basis (history j i) := by
  dsimp only
  intro i
  obtain ⟨f,no⟩:=(heads_all j h2 h19).2.1 i
  exact (Shadow7.first_preserves j _ odd _ t active _ (firstFree j f)).trans (run_preserves_outside _ _ _ _ (EnterJ7.notWire j no))
theorem bank_kept (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (s:State) (e t p:List Bool)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z (run (Shadow7.enterP j) e s).basis) :
    let now:=run (program j d) p (run (Shadow7.routed j 0 1) t (run (Shadow7.enterP j) e s))
    ∀i:Fin 23,now.basis (ArchiveJ7.rawPorts (prev j) ⟨i,by omega⟩)=s.basis (ArchiveJ7.rawPorts (prev j) ⟨i,by omega⟩) := by
  dsimp only
  intro i
  obtain ⟨f,no,sup⟩:=(heads_all j h2 h19).2.2 _ (rawHead_mem (prev j) ⟨i,by omega⟩ i.isLt)
  exact (run_preserves_outside _ _ _ _ (fun h=>sup (List.mem_toFinset.mp ((codes j h2 d).1 h)))).trans
    ((Shadow7.first_preserves j _ odd _ t active _ (firstFree j f)).trans (preserve_readonly _ _ (enter_readonly j no) s e))

theorem matching (j : Fin 23) (before:State) (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past g sign cross before) :
    let cells:=Shadow7.physicalCells (prev j) before
    let f:=decide (Shadow.far (Shadow7.sbP (start (prev j))) 15 past)
    let u:=f && afterFlags (decide (past.v<past.u)) (cells.take 5)
    ∃row<63145,∀q<23,(rawCol q).testBit row=rawBit (read (cells.drop 5)) f u (f && cross) q :=
  interrupted_row_shadow7 (Shadow7.sbP (start (prev j))) past small odd g sign cross _ (prior.records.trans (true_records_shadow7 _ _ small odd _ _).symm)

theorem frame_for (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (before out:State)
    (scratch:∀k:Fin 157,23≤k.val → out.basis (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past g sign cross before)
    (bk:∀i:Fin 23,out.basis (ArchiveJ7.rawPorts (prev j) ⟨i,by omega⟩)=before.basis (ArchiveJ7.rawPorts (prev j) ⟨i,by omega⟩)) :
    ∃row<63145,ArchivePortAction.Frame (ArchiveJ7.rawPorts (prev j)) raw row out := by
  have hp:(prev j).val≤20:=by simp only [prev]; omega
  let cells:=Shadow7.physicalCells (prev j) before
  let f:=decide (Shadow.far (Shadow7.sbP (start (prev j))) 15 past)
  let u:=f && afterFlags (decide (past.v<past.u)) (cells.take 5)
  let c:=f && cross
  let data:=rawBit (read (cells.drop 5)) f u c
  have tags:out.basis (ArchiveJ7.rawPorts (prev j) 20)=f ∧ out.basis (ArchiveJ7.rawPorts (prev j) 21)=u ∧
      out.basis (ArchiveJ7.rawPorts (prev j) 22)=c:=
    ⟨(bk 20).trans prior.far,(bk 21).trans prior.suffix,(bk 22).trans prior.crossed⟩
  have record:∀i:Fin 157,i.val<23 → out.basis (ArchiveJ7.rawPorts (prev j) i)=data i:=
    ArchiveJ7.observed (prev j) hp before out (fun q=>bk ⟨q,Nat.lt_trans q.isLt (by decide : 20<23)⟩) f u c tags
  obtain ⟨row,lim,matchRow⟩:=matching j before past g sign cross odd small prior
  exact ⟨row,lim,starting_frame (ArchiveJ7.rawPorts (prev j)) out row data matchRow record scratch⟩

theorem completed_head (j : Fin 23) (h2 : 1≤j.val) (d:Bool) (src:State) (first pack:List Bool)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z src.basis) :
    Shadow7.onRails j 1 (SkywalkTrace.next z) (run (program j d) pack (run (Shadow7.routed j 0 1) first src)).basis :=
  Shadow7.ready_after_head j (program j d) src first pack z odd active (fun t=>retains j h2 d false t pack)

theorem head_legal (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (before:State) (et first:List Bool)
    (nowZ:SkywalkRails.State) (parity:(nowZ.a+nowZ.b)%2=1)
    (ready:Shadow7.onRails j 0 nowZ (run (Shadow7.enterP j) et before).basis)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past g sign cross before) :
    MeasuredCodec5.legalAt (history j) (run (Shadow7.routed j 0 1) first (run (Shadow7.enterP j) et before)).basis := by
  apply legal_prefix j h2 h19 before _ _ (prefix_kept j h2 h19 before et first nowZ parity ready)
  change StairArchiveRaw.legal (Shadow7.physicalCells (prev j) before)
  rw [Shadow7.physicalCells_eq, prior.records]
  exact legal_signed 15 past g sign (by omega) odd

theorem admits (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (before:State) (et first pack:List Bool)
    (nowZ:SkywalkRails.State) (parity:(nowZ.a+nowZ.b)%2=1)
    (ready:Shadow7.onRails j 0 nowZ (run (Shadow7.enterP j) et before).basis)
    (scratch:∀k:Fin 157,23≤k.val →
      (run (program j d) pack (run (Shadow7.routed j 0 1) first (run (Shadow7.enterP j) et before))).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past g sign cross before) :
    let src:=run (Shadow7.routed j 0 1) first (run (Shadow7.enterP j) et before)
    let out:=run (program j d) pack src
    MeasuredCodec5.legalAt (history j) src.basis ∧ ∃row<63145,ArchivePortAction.Frame (ArchiveJ7.rawPorts (prev j)) raw row out := by
  dsimp only
  refine ⟨head_legal j h2 h19 before et first nowZ parity ready past g sign cross odd prior,?_⟩
  exact frame_for j h2 h19 before _ scratch past g sign cross odd small prior (bank_kept j h2 h19 d before et first pack nowZ parity ready)
end NativeJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run Shadow7.onRails Shadow7.unrouted
namespace NativeJ7
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-- Block `j`'s window up to its leave: enter, then the window body with the pack and the archive. -/
def nextWindow (j : Fin 23) (d:Bool) := Shadow7.enterP j++window j d
def nextUnwind (j : Fin 23) (d:Bool) := unwind j d++Shadow7.enterInvP j

theorem backward_sub : wires EnterProof.backward ⊆ Finset.range 23 := by decide +kernel
theorem enterInvCover (j : Fin 23) : wires (Shadow7.enterInvP j) ⊆ (EnterJ7.ports j).toFinset := by
  rw [EnterJ7.emittedInv j,renameProgram_support]
  intro q hq
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hq
  have lt:w<(EnterJ7.ports j).length:=Finset.mem_range.mp (backward_sub hw)
  rw [List.mem_toFinset,EnterJ7.map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem lt,Option.getD_some]
  exact List.getElem_mem lt

theorem next_window (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    let out:=run (nextWindow j d) m s
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] (encode G S T.u T.v)) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      ∀t,run (nextUnwind j d) t out=s := by
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m small cut input hist
  obtain ⟨legal,row,limit,frame⟩:=admits j h2 h19 d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity ready.2.1
    scratch past pg ps cross po pm prior
  have all:=window_run j h2 h19 d pre tape Z parity ready.2.1 legal row limit frame
    (fun k hk _=>scratch k hk)
  dsimp only [nextWindow,nextUnwind]
  simp only [run_append,run_take]
  refine ⟨all.1.trans ready.1,all.2.1,all.2.2.1.trans (true_records_shadow7 (Shadow7.sbP (start j)) z small odd G S),?_⟩
  intro n
  rw [all.2.2.2 n]
  have free:∀q∈EnterJ7.pending j,q∉wires (Shadow7.enterInvP j):=by
    intro q hq used
    have r:=EnterJ7.portsRegion j (List.mem_toFinset.mp (enterInvCover j used))
    have f:=EnterJ7.frame j
    simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false] at hq
    simp only [Wire] at *
    omega
  apply unmask (Shadow7.enterP j) (Shadow7.enterInvP j) (EnterJ7.pending j) (EnterJ7.avoid_enter j) free
  exact EnterProof.return_packed_shadow7 (EnterJ7.layout j) (EnterJ7.map j) _ _ (EnterJ7.inc j) (fun _=>rfl) rfl (EnterJ7.emitted j)
    (EnterJ7.emittedInv j) raw _ z G S small cut input _ _
end NativeJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run Shadow7.onRails Shadow7.unrouted
namespace NativeFirstJ7
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-! First-form head (par-c2): the first block's five pre-window letters are legal from the stock stage, and its
window runs from the portal's cut (dadon's `NativePack225.original_legal/history_from_stock`). -/
theorem original_legal (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21) (d:Bool) (seed p:Nat) (hp0:0<p) (odd:p%2=1)
    (raw:State) (stage:Rolling1588.Integer.Stage base d seed p (start j) raw.basis) :
    MeasuredCodec5.legalAt (History5.historyMap base (start j-5)) raw.basis := by
  have hj:=j.isLt
  obtain ⟨pre,original,packed⟩:=stage
  rw [packed]
  apply Rolling1588.Integer.prefix_next_legal base d base_pool_nodup (start j) (by simp only [start]; omega)
    (by simp only [History5.packDue,start,decide_eq_true_eq]; omega)
  exact W.stage_group_legal base base_pool_nodup seed p (start j) (start j-5) hp0 odd (by simp only [start]; omega)
    (by simp only [start]; omega) _ original
theorem headF_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 → ∀i:Fin 10,
    NativeJ7.FirstFree j (windowNet j (history j i)) ∧ (history j i∉EnterJ7.ports j ∨ history j i=EnterJ7.gate j) ∧
    history j i≠EnterJ7.flagN j ∧ history j i≠EnterJ7.flagF j ∧ history j i≠EnterJ7.flagU j ∧
    history j i∉RailPair.sites (EnterJ7.upperPairs j) ∧ EnterJ7.pull j (history j i)=History5.historyMap base (start j-5) i := by
  decide +kernel
theorem history_from_stock (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤20) (raw cut t:State) {neg far long:Bool}
    (frame:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) cut)
    (m n:List Bool) (head:t=run (Shadow7.enterP j) m cut)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (ready:Shadow7.onRails j 0 z t.basis) :
    ∀i,(run (Shadow7.routed j 0 1) n t).basis (history j i)=raw.basis (History5.historyMap base (start j-5) i) := by
  intro i
  obtain ⟨f,no,hn,hf,hu,hh,coord⟩:=headF_all j h1 (by omega) i
  rw [Shadow7.first_preserves j z odd _ _ ready _ (NativeJ7.firstFree j f),head,preserve_readonly _ _ (NativeJ7.enter_readonly j no)]
  exact (frame.unchanged _ hn hf hu hh).trans (congrArg raw.basis coord)

/-- The first block's enter and window (dadon's `NativePack225.firstWindow` without the portal). -/
def enteredWindow (j : Fin 23) (d:Bool) := Shadow7.enterP j++window j d
def enteredUnwind (j : Fin 23) (d:Bool) := unwind j d++Shadow7.enterInvP j
theorem entered_window (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤20) (d:Bool) (raw v:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) v)
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (legal0:MeasuredCodec5.legalAt (History5.historyMap base (start j-5)) raw.basis) :
    let out:=run (enteredWindow j d) m v
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    out.phase=v.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] (encode G S T.u T.v)) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      ∀t,run (enteredUnwind j d) t out=v := by
  let pre:=run (Shadow7.enterP j) m v
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_from_cut_at j raw v z G S m small cut input hist
  have legal:=legal_congr (history_from_stock j h1 (by omega) raw v pre cut m tape rfl _ parity ready.2) legal0
  have all:=window_run j h1 d pre tape Z parity ready.2 legal
  dsimp only [enteredWindow,enteredUnwind]
  simp only [run_append,run_take]
  refine ⟨all.1.trans ready.1,all.2.1,all.2.2.1.trans (true_records_shadow7 (Shadow7.sbP (start j)) z small odd G S),?_⟩
  intro n
  rw [all.2.2.2 n]
  exact EnterProof.return_packed_shadow7 (EnterJ7.layout j) (EnterJ7.map j) _ _ (EnterJ7.inc j) (fun _=>rfl) rfl (EnterJ7.emitted j)
    (EnterJ7.emittedInv j) raw _ z G S small cut input _ _
end NativeFirstJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic ArchivePortAction StairArchiveIntegerHook
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
namespace ArchiveJ7
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-- The wires of a swap list are its pairs' ends. -/
theorem moves_wires (ps : List (Wire×Wire)) : ∀q∈wires (moves ps), ∃p∈ps, q=p.1 ∨ q=p.2 := by
  induction ps with
  | nil => intro q h; simp [moves,wires] at h
  | cons p ps ih =>
    intro q h
    obtain ⟨a,b⟩:=p
    simp only [moves,List.flatMap_cons,wires_append,Finset.mem_union] at h
    rcases h with h|h
    · refine ⟨(a,b),List.mem_cons_self,?_⟩
      simp [swapBits,wires,Instr.wires] at h ⊢
      tauto
    · obtain ⟨p',hp',e⟩:=ih q (by simpa [moves] using h)
      exact ⟨p',List.mem_cons_of_mem _ hp',e⟩
theorem load_cover (i : Fin 23) (hi : i.val≤20) (d:Bool) : wires (Shadow7.archiveLoadP i d) ⊆ (rawPortsList i).toFinset := by
  rw [load_program,wires_append,Finset.union_subset_iff]
  constructor
  · rw [placed,renameProgram_support]
    intro q member
    obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp member
    have bound:=Finset.mem_range.mp (sub (op true d) used)
    have small:w<155:=by cases d <;> exact bound
    rw [load_map i ⟨w,small⟩,List.mem_toFinset,rawPorts,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [rawLength]; omega),Option.getD_some]
    exact List.getElem_mem _
  · intro q hq
    obtain ⟨p,hp,e⟩:=moves_wires _ q hq
    obtain ⟨h1,h2,-⟩:=(heads_all i hi).2.2.2.2.2.1 p hp
    rw [List.mem_toFinset,raw_split]
    rcases e with rfl|rfl
    · exact List.mem_append_left _ h1
    · exact List.mem_append_left _ h2
end ArchiveJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction CodecBitSliceVerify EnterProof PortalValues SkywalkRails Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! NativeJ, part 3 (Tail10d9): what block `j`'s window keeps (`2 ≤ j ≤ 19`). -/

theorem codesOld_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 →
    (∀i:Fin 16,oldRange (start j+1) (windowNet j (ArchiveJ7.codePorts (prev j) ⟨i.val,by omega⟩))) ∧
    (∀k:Fin 3,ArchiveJ7.codePorts (prev j) ⟨154+k.val,by omega⟩=Shadow7.sbP (start j)+1580+k.val ∧
      ¬Shadow7.MayTouch j (windowNet j (Shadow7.sbP (start j)+1580+k.val))) := by
  decide +kernel
theorem encoded_outside (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) :
    ∀i:Fin 16,ArchiveJ7.codePorts (prev j) ⟨i.val,by omega⟩∉Shadow7.spanSites j 1 14 :=
  fun i=>Shadow7.old_clear (by decide) ((codesOld_all j h2 h19).1 i)
theorem window_keeps (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (s:State) (m:List Bool) (row:Nat)
    (hold:Frame (ArchiveJ7.codePorts (prev j)) (code d) row
      (run (withArchive j d) (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m s))) :
    Kept (ArchiveJ7.codePorts (prev j)) d row (run (window j d) m s) :=
  Shadow7.body_keeps j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row s m (encoded_outside j h2 h19) hold

/-- The enter flags and the saved high word, kept through the window. -/
def protectedSites (j : Fin 23) : List Wire := [EnterJ7.flagN j,EnterJ7.flagF j,EnterJ7.flagU j]++EnterJ7.saved j
theorem admin_cover (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) :
    wires (withArchive j d)⊆(support j++ArchiveJ7.rawPortsList (prev j)).toFinset := by
  rw [withArchive,wires_append,List.toFinset_append]
  exact Finset.union_subset_union (codes j h2 d).1 (ArchiveJ7.load_cover (prev j) (by simp only [prev]; omega) d)
/-- The protected sites are the flag block `e0..e0+5` and the parked B-side word. -/
theorem protected_band (j : Fin 23) : ∀q∈protectedSites j,
    (Shadow7.sbP (start j)+1574≤q ∧ q≤Shadow7.sbP (start j)+1579) ∨ (Shadow7.sbP (start j)+805≤q ∧ q+3<Shadow7.sbP (start j)+805+Shadow7.wpP (start j)) := by
  intro q hq
  rw [protectedSites,List.mem_append] at hq
  rcases hq with hq|hq
  · simp only [EnterJ7.flagN,EnterJ7.flagF,EnterJ7.flagU,List.mem_cons,List.not_mem_nil,or_false] at hq
    simp only [Wire] at *; omega
  · rw [EnterJ7.saved,List.mem_append] at hq
    rcases hq with hq|hq
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      simp only [Wire] at *; omega
    · simp only [EnterJ7.upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp] at hq
      obtain ⟨i,hi,rfl⟩:=hq
      simp only [Wire] at *; omega
theorem free_native (j : Fin 23) : ∀q∈protectedSites j,¬Shadow7.MayTouch j (windowNet j q) := by
  intro q hq
  have b:=protected_band j q hq
  have f:=EnterJ7.frame j
  have fix:windowNet j q=q:=by
    simp only [windowNet,net,OB5.sig]
    split <;> simp only [Wire] at * <;> omega
  rw [fix]
  unfold Shadow7.MayTouch
  simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *
  simp only [Wire] at *
  omega
theorem adminBand_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 → ∀q∈ArchiveJ7.rawHead (prev j)++support j,
    q<Shadow7.sbP (start j)+805 ∨ (Shadow7.sbP (start j)+802+Shadow7.wpP (start j)≤q ∧ q<Shadow7.sbP (start j)+1574) ∨ Shadow7.sbP (start j)+1579<q := by
  decide +kernel
theorem free_admin (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) :
    ∀q∈protectedSites j,q∉(support j++ArchiveJ7.rawPortsList (prev j)) := by
  intro q hq hm
  have b:=protected_band j q hq
  have f:=EnterJ7.frame j
  have tick:start (prev j)+15=start j:=by simp only [prev,start]; omega
  rw [ArchiveJ7.raw_split,List.mem_append,List.mem_append] at hm
  rcases hm with hm|hm|hm
  · have:=adminBand_all j h2 h19 q (List.mem_append_right _ hm); simp only [Wire] at *; omega
  · have:=adminBand_all j h2 h19 q (List.mem_append_left _ hm); simp only [Wire] at *; omega
  · obtain ⟨k,hk,eq⟩:=List.mem_map.mp hm
    apply ArchiveJ7.band_off (start (prev j)+15) (ArchiveJ.tick_lt (prev j)) (List.mem_range.mp hk) _ eq
    rw [tick]
    unfold ArchiveJ7.Band
    rcases b with b|b
    · right; right; right; right; refine ⟨q-(Shadow7.sbP (start j)+1574),?_,?_⟩ <;> simp only [Shadow7.e0P,Wire] at * <;> omega
    · left
      have top : start j<369 ∨ Shadow7.wpP (start j)+Shadow7.sbP (start j)+start j≤497 := by
        by_cases h : start j<369
        · exact Or.inl h
        · right
          have r : railP (start j)=513-start j := by unfold railP; rw [if_neg (by omega),if_neg (by omega)]
          have wdef : Shadow7.wpP (start j)=railP (start j)-Shadow7.sbP (start j)-16 := rfl
          omega
      simp only [Wire] at *; omega
theorem keeps_stored (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (s:State) (m:List Bool) (q:Wire)
    (hq:q∈protectedSites j) : (run (Shadow7.body j (withArchive j d)) m s).basis q=s.basis q :=
  Shadow7.body_cover j (withArchive j d) (protectedSites j) (support j++ArchiveJ7.rawPortsList (prev j))
    (free_native j) (free_admin j h2 h19) (admin_cover j h2 h19 d) s m q hq
theorem source_tags (j : Fin 23) (s:BasisState) (z:SkywalkNat.State) (G S:Bool)
    (hit:∀q∈wires EnterProof.forward,s (EnterJ7.map j q)=(shadowRow (Shadow7.sbP (start j)) 15 z G S).testBit q) :
    s (EnterJ7.flagN j)=false ∧ s (EnterJ7.flagF j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      s (EnterJ7.flagU j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u) :=
  (actual_tags (EnterJ7.ports j) s (Shadow7.sbP (start j)) 15 z G S hit).2
theorem relay (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (s:State) (m:List Bool) (h:Nat) (x y:Bool)
    (high:regValue (EnterJ7.saved j) s.basis=h) (hn:s.basis (EnterJ7.flagN j)=false) (hf:s.basis (EnterJ7.flagF j)=x)
    (hu:s.basis (EnterJ7.flagU j)=y) :
    let out:=run (Shadow7.body j (withArchive j d)) m s
    regValue (EnterJ7.saved j) out.basis=h ∧ out.basis (EnterJ7.flagN j)=false ∧ out.basis (EnterJ7.flagF j)=x ∧
      out.basis (EnterJ7.flagU j)=y :=
  keep_values (EnterJ7.flagN j) (EnterJ7.flagF j) (EnterJ7.flagU j) (EnterJ7.saved j) s (run (Shadow7.body j (withArchive j d)) m s)
    h x y (keeps_stored j h2 h19 d s m) high hn hf hu
theorem saved_at_leave (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (raw cut:State) (z:SkywalkNat.State)
    (G S:Bool) (head ticks:List Bool) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (packed:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (negative S z.u) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u)) (pullState (EnterJ7.pull j) raw) cut)
    (input:SkywalkIntegerInput (EnterJ7.lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let out:=run (Shadow7.body j (withArchive j d)) ticks (run (Shadow7.enterP j) head cut)
    regValue (EnterJ7.saved j) out.basis=(if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) ∧
      out.basis (EnterJ7.flagN j)=false ∧ out.basis (EnterJ7.flagF j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      out.basis (EnterJ7.flagU j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u) := by
  let pre:=run (Shadow7.enterP j) head cut
  have high:=EnterJ7.high_from_cut j raw cut z G S head small packed input
  have body0:=EnterJ7.from_full j raw cut z G S head small packed input
  have tags:=source_tags j pre.basis z G S body0.2.1
  exact relay j h2 h19 d pre ticks (if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) _ _
    high tags.1 tags.2.1 tags.2.2
theorem protected_bound (j : Fin 23) : ∀q∈protectedSites j,q<Shadow7.sbP (start j)+1580 := by
  have f:=EnterJ7.frame j
  intro q hq
  have:=protected_band j q hq
  simp only [Wire] at *; omega
theorem protected_pending (j : Fin 23) : ∀q∈protectedSites j,q∉EnterJ7.pending j := by
  intro q hq hp
  have b:=protected_bound j q hq
  simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false] at hp
  simp only [Wire] at *
  omega
theorem saved_with_pending (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (raw cut:State)
    (z:SkywalkNat.State) (G S:Bool) (head ticks:List Bool) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (packed:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (negative S z.u) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u)) (pullState (EnterJ7.pull j) raw)
      (eraseSites (EnterJ7.pending j) cut))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let out:=run (Shadow7.body j (withArchive j d)) ticks (run (Shadow7.enterP j) head cut)
    regValue (EnterJ7.saved j) out.basis=(if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) ∧
      out.basis (EnterJ7.flagN j)=false ∧ out.basis (EnterJ7.flagF j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      out.basis (EnterJ7.flagU j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u) := by
  have observed:=saved_at_leave j h2 h19 d raw (eraseSites (EnterJ7.pending j) cut) z G S head ticks small packed input
  have eq:=masked_body (Shadow7.enterP j) (Shadow7.body j (withArchive j d)) (protectedSites j) (EnterJ7.pending j) cut head ticks
    (EnterJ7.avoid_enter j) (protected_pending j) (fun s=>keeps_stored j h2 h19 d s ticks)
  exact keep_values (EnterJ7.flagN j) (EnterJ7.flagF j) (EnterJ7.flagU j) (EnterJ7.saved j) _ _ _ _ _ eq
    observed.1 observed.2.1 observed.2.2.1 observed.2.2.2

theorem popped (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (src:State) (m:List Bool) (row:Nat)
    (frame:Frame (ArchiveJ7.codePorts (prev j)) (code d) row
      (run (withArchive j d) (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m src))) :
    ∀k:Fin 3,(run (Shadow7.body j (withArchive j d)) m src).basis (Shadow7.sbP (start j)+1580+k.val)=false := by
  intro k
  have phys:=(codesOld_all j h2 h19).2 k
  exact Shadow7.after_encoded j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row src m frame ⟨154+k.val,by omega⟩
    (by dsimp;omega) _ phys.1 phys.2
theorem archive_result (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (row:Nat) (lim:row<63145) (s:State)
    (m:List Bool) (raw0:Frame (ArchiveJ7.rawPorts (prev j)) ArchivePortAction.raw row (run (program j d) m s)) :
    Frame (ArchiveJ7.codePorts (prev j)) (code d) row (run (withArchive j d) m s) :=
  from_append (prop:=Frame (ArchiveJ7.codePorts (prev j)) (code d) row)
    (ArchiveJ7.load_run (prev j) (by simp only [prev]; omega) d row lim _ (m.drop (measurementCount (program j d))) raw0).2.1
theorem receipt (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (s:State) (m:List Bool) (row:Nat)
    (lim:row<63145)
    (raw0:Frame (ArchiveJ7.rawPorts (prev j)) ArchivePortAction.raw row
      (run (program j d) (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m s))) :
    Kept (ArchiveJ7.codePorts (prev j)) d row (run (Shadow7.body j (withArchive j d)) m s) ∧
      ∀k:Fin 3,(run (Shadow7.body j (withArchive j d)) m s).basis (Shadow7.sbP (start j)+1580+k.val)=false := by
  have frame:=archive_result j h2 h19 d row lim _ _ raw0
  exact ⟨Shadow7.body_keeps j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row s m (encoded_outside j h2 h19) frame,
    popped j h2 h19 d s m row frame⟩

/-- Hypotheses of block `j`'s window head, as `next_window` takes them. -/
theorem real_receipt (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    let out:=run (nextWindow j d) m s
    ∃row<63145, RowTruth past pg ps row ∧ Kept (ArchiveJ7.codePorts (prev j)) d row out ∧
      ∀k:Fin 3,out.basis (Shadow7.sbP (start j)+1580+k.val)=false := by
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m small cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j h2 h19 d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity ready.2.1
    scratch past pg ps cross po pm prior
  have matchRow:=row_truth (prev j) (ArchiveJ7.rawPorts (prev j)) (ArchiveJ7.chronological_all (prev j) (by simp only [prev]; omega))
    row past pg ps s _ prior.records
    (bank_kept j h2 h19 d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity ready.2.1) frame
  have final:=receipt j h2 h19 d pre tape row limit frame
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨row,limit,matchRow,final⟩

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run measurementCount Shadow7.onRails

/-- dadon's `NativePack{s}.fourHoles`: the four B-side history cells the archive of block `prev j` (at tick
`start j`) frees, i.e. the first four wires of `ArchiveJ7.codeTail (prev j)`. -/
def fourHoles (j : Fin 23) : List Wire := ((ArchiveJ7.codeTail (prev j)).take 4)

theorem fourHoles_eq (j : Fin 23) (h1 : 1 ≤ j.val) : fourHoles j =
    [OB5.sig (start j) (start j+1036), OB5.sig (start j) (start j+1038), OB5.sig (start j) (start j+1041),
      OB5.sig (start j) (start j+1043)] := by
  have e : start (prev j) + 15 = start j := by simp only [prev, start]; omega
  simp only [fourHoles, ArchiveJ7.codeTail, e, List.take_succ_cons, List.take_zero]

/-- dadon's `blank_slots`: every hole is a code port at index ≥ 16 (where the archive code is blank). -/
theorem blank_slots (j : Fin 23) : ∀ q ∈ fourHoles j, ∃ i : Fin 157, 16 ≤ i.val ∧ ArchiveJ7.codePorts (prev j) i = q := by
  have hl : (cellsRestoreP (start (prev j)+15) ++ ArchiveJ7.scratch (prev j)).length = 150 := by
    simp [cellsRestoreP, ArchiveJ7.scratch]
  have key : ∀ c, (hc : c < 4) → ArchiveJ7.codePorts (prev j) ⟨150+c, by omega⟩ = (ArchiveJ7.codeTail (prev j)).getD c 0 := by
    intro c hc
    show (ArchiveJ7.codePortsList (prev j)).getD (150+c) 0 = _
    rw [ArchiveJ7.code_split, List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, show 150+c-150 = c by omega]
  intro q hq
  simp only [fourHoles, ArchiveJ7.codeTail, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl
  · exact ⟨⟨150, by omega⟩, Nat.le_of_lt_succ (by show 16 < 150+1; omega), (key 0 (by omega)).trans rfl⟩
  · exact ⟨⟨151, by omega⟩, Nat.le_of_lt_succ (by show 16 < 151+1; omega), (key 1 (by omega)).trans rfl⟩
  · exact ⟨⟨152, by omega⟩, Nat.le_of_lt_succ (by show 16 < 152+1; omega), (key 2 (by omega)).trans rfl⟩
  · exact ⟨⟨153, by omega⟩, Nat.le_of_lt_succ (by show 16 < 153+1; omega), (key 3 (by omega)).trans rfl⟩

/-- The holes are outside every wire the Shadow7.routed ticks of block `j` may touch. -/
theorem holes_free (j : Fin 23) (h1 : 1 ≤ j.val) (h19 : j.val ≤ 21) : ∀ q ∈ fourHoles j, ¬Shadow7.MayTouch j (windowNet j q) := by
  intro q hq
  have closed : ∀ i : Fin 23, 1 ≤ i.val → i.val ≤ 21 →
      (fourHoles i).all (fun w => decide (¬Shadow7.MayTouch i (windowNet i w))) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (closed j h1 h19) q hq)

/-- dadon's `NativePack{s}.cleared_holes`, generic: after block `j`'s window head, the four freed history cells of the
previous block's archive are zero. -/
theorem cleared_holes (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    ∀q∈fourHoles j,(run (nextWindow j d) m s).basis q=false := by
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m small cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j h2 (by omega) d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity
    ready.2.1 scratch past pg ps cross po pm prior
  have final:=archive_result j h2 (by omega) d row limit _ _ frame
  intro q hq
  obtain ⟨i,hi,slot⟩:=blank_slots j q hq
  rw [nextWindow,run_append,run_take]
  exact Shadow7.after_encoded j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row pre tape final i hi q slot
    (holes_free j h2 h19 q hq)

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! The leave of block `j` writes only inside par-c1's box (dadon's `NativePack{s}.writes/exterior`, which
decided 37 leave parts per block); generic from `Shadow7.leaveOps_box`. -/
theorem front_target (g : GateMirror.Gate) : CodecBitSliceVerify.target (GateMirror.front g)∈g.wires := by
  cases g <;> simp [GateMirror.front,GateMirror.erase,GateMirror.Gate.wires,CodecBitSliceVerify.target]
theorem back_target (g : GateMirror.Gate) : CodecBitSliceVerify.target (GateMirror.back g)∈g.wires := by
  cases g <;> simp [GateMirror.back,GateMirror.erase,GateMirror.Gate.wires,CodecBitSliceVerify.target]
theorem exterior (j : Fin 23) (h2 : 1≤j.val) (h20 : j.val≤21) (s:State) (m:List Bool) (q:Wire)
    (ext:¬leaveBox (start j) q) : (run (Shadow7.leaveP j) m s).basis q=s.basis q := by
  apply preserve_readonly
  intro i hi eq
  obtain ⟨g,hg,rfl⟩:=List.mem_map.mp hi
  exact ext (eq ▸ Shadow7.leaveOps_box j (by omega) (by omega) g hg _ (front_target g))
theorem exteriorInv (j : Fin 23) (h2 : 1≤j.val) (h20 : j.val≤21) (s:State) (m:List Bool) (q:Wire)
    (ext:¬leaveBox (start j) q) : (run (Shadow7.leaveInvP j) m s).basis q=s.basis q := by
  apply preserve_readonly
  intro i hi eq
  obtain ⟨g,hg,rfl⟩:=List.mem_map.mp (List.mem_reverse.mp hi)
  exact ext (eq ▸ Shadow7.leaveOps_box j (by omega) (by omega) g hg _ (back_target g))

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! `NativePack{s}.tailTemps/tail_clean`, generic: after the window head, the wires above the anchored block
(`e0+9 ..`) are clean. From `s ≥ 270` the wires `2055-s..1812` hold the block's own history cells (windowNet
mirror), so the tail stops below them (dadon's 255: `1712..1799`). Late blocks' archive scratch reaches into the
tail; those wires are clean as unused code ports (`Shadow7.after_encoded`). -/
def tailTemps (j : Fin 23) : List Wire :=
  List.range' (Shadow7.e0P (start j)+9) (min 1813 (2055-start j)-(Shadow7.e0P (start j)+9))
theorem tail_mem (j : Fin 23) {q : Wire} (h : q∈tailTemps j) :
    Shadow7.e0P (start j)+9≤q ∧ q≤1812 ∧ q+start j≤2054 := by
  simp only [tailTemps,List.mem_range'_1] at h; simp only [Wire] at *; omega
theorem tail_geometry (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21) {q : Wire} (hq : q∈tailTemps j) :
    windowNet j q=q ∧ EnterJ7.pull j q=q ∧ ¬Shadow7.MayTouch j q ∧ q∉EnterJ7.ports j ∧ q∉EnterJ7.pending j ∧
    q≠EnterJ7.flagN j ∧ q≠EnterJ7.flagF j ∧ q≠EnterJ7.flagU j ∧ q∉RailPair.sites (EnterJ7.upperPairs j) := by
  have t:=tail_mem j hq
  have f:=EnterJ7.frame j
  simp only [Shadow7.e0P] at t
  refine ⟨?_,?_,?_,fun m=>?_,fun m=>?_,?_,?_,?_,fun m=>?_⟩
  · rw [windowNet,net]
    exact Shadow7.sig_tail j h21 q (by have:=t.1; simp only [Shadow7.e0P,Wire] at *; omega) t.2.2 (start j+14) (le_refl _)
  · rw [EnterJ7.pull]
    exact Shadow7.sig_tail j h21 q (by have:=t.1; simp only [Shadow7.e0P,Wire] at *; omega) t.2.2 (start j-1)
      (by have:=EnterJ7.frame j; simp only [Wire] at *; omega)
  · unfold Shadow7.MayTouch; simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *; simp only [Wire] at *; omega
  · have:=EnterJ7.portsRegion j m; simp only [Wire] at *; omega
  · simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false] at m; simp only [Wire] at *; omega
  · simp only [EnterJ7.flagN,Wire]; omega
  · simp only [EnterJ7.flagF,Wire]; omega
  · simp only [EnterJ7.flagU,Wire]; omega
  · have:=EnterJ7.upperSites j m; simp only [Wire] at *; omega
theorem tailHead_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 → ∀q∈ArchiveJ7.rawHead (prev j)++support j,
    q<Shadow7.sbP (start j)+1583 ∨ 2055≤q+start j := by
  decide +kernel
theorem tail_clean (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21) (d:Bool) (x p:Nat) (raw s:State)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (row:Nat) (frame:Frame (ArchiveJ7.codePorts (prev j)) (code d) row
      (run (withArchive j d) (b.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) b (run (Shadow7.enterP j) a s)))) :
    ∀q∈tailTemps j,(run (Shadow7.body j (withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false := by
  intro q hq
  obtain ⟨wn,same,touch,port,pend,hn,hf,hu,hi⟩:=tail_geometry j h1 h21 hq
  have t:=tail_mem j hq
  by_cases sc:q∈ArchiveJ7.scratch (prev j)
  · obtain ⟨k,hk,eq⟩:=List.mem_map.mp sc
    have hk':=List.mem_range.mp hk
    have code0:ArchiveJ7.codePorts (prev j) ⟨16+k,by omega⟩=q:=(ArchiveJ7.code_scratch (prev j) hk').trans eq
    exact Shadow7.after_encoded j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row (run (Shadow7.enterP j) a s) b frame
      ⟨16+k,by omega⟩ (by dsimp only; omega) q code0 (by rw [wn]; exact touch)
  · have notAdmin:q∉support j++ArchiveJ7.rawPortsList (prev j):=by
      rw [ArchiveJ7.raw_split,List.mem_append,List.mem_append]
      rintro (h|h|h)
      · have:=tailHead_all j h1 h21 q (List.mem_append_right _ h); simp only [Shadow7.e0P,Wire] at *; omega
      · have:=tailHead_all j h1 h21 q (List.mem_append_left _ h); simp only [Shadow7.e0P,Wire] at *; omega
      · exact sc h
    have stay:=Shadow7.ext_head (Shadow7.enterP j) j (withArchive j d) (support j++ArchiveJ7.rawPortsList (prev j)) s a b q
      (by rw [wn]; exact touch) (EnterJ7.notWire j port) notAdmin (admin_cover j h1 h21 d)
    have read:=cut.unchanged q hn hf hu hi
    have canon:s.basis q=raw.basis q:=by simpa only [pullState,same,eraseSites,if_neg pend] using read
    have zero:raw.basis q=false:=WideReference.domain_carry (by simp only [start]; omega) domain q
      (by simp only [Shadow7.e0P,Wire] at *; omega) t.2.1
    exact stay.trans (canon.trans zero)

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! `NativePack{s}.upperA/upper_clear`, generic: the A rail above the block's own ticks (`s+h+50 .. top`,
`top = min (s+30+R(s+14)) 529`, par-a's exact span top) is clean after the window head: the parked bank's A side is zeroed by the cut, the
wires above the bank (`s+R+16 ..`) are free in the stock domain. -/
theorem upperFree_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 → ∀k:Fin 20,
    start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val≤min (start j+30+railP (start j+14)) 529 →
    start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val∈(W.compactSkywalkSignPoolA base (start j)).released ∨
      (start j+274≤start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val ∧ start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val<786) := by
  decide +kernel
theorem upperHead_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 → ∀q∈ArchiveJ7.rawHead (prev j)++support j,
    q<start j+Shadow7.sbP (start j)+50 ∨ 1043<q := by
  decide +kernel

theorem upper_clear (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21) (d:Bool) (raw s:State) (x p:Nat)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (q:Nat) (low:start j+Shadow7.sbP (start j)+50≤q) (high:q≤min (start j+30+railP (start j+14)) 529) :
    (run (Shadow7.body j (withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false := by
  have f:=EnterJ7.frame j
  have wn:windowNet j q=q:=by
    rw [windowNet,net]
    exact WideReference.sig_rail j q (le_trans high (min_le_right _ _)) (start j+14) (le_refl _)
  have same:EnterJ7.pull j q=q:=by
    rw [EnterJ7.pull]
    exact WideReference.sig_rail j q (le_trans high (min_le_right _ _)) (start j-1)
      (by have:=EnterJ7.frame j; simp only [Wire] at *; omega)
  have touch:¬Shadow7.MayTouch j (windowNet j q):=by
    rw [wn]; unfold Shadow7.MayTouch; simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *; simp only [Wire] at *; omega
  have port:q∉EnterJ7.ports j:=fun m=>by have:=EnterJ7.portsRegion j m; simp only [Wire] at *; omega
  have pend:q∉EnterJ7.pending j:=by
    simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false,Wire]; omega
  have notAdmin:q∉support j++ArchiveJ7.rawPortsList (prev j):=by
    rw [ArchiveJ7.raw_split,List.mem_append,List.mem_append]
    rintro (h|h|h)
    · have:=upperHead_all j h1 h21 q (List.mem_append_right _ h); simp only [Wire] at *; omega
    · have:=upperHead_all j h1 h21 q (List.mem_append_left _ h); simp only [Wire] at *; omega
    · obtain ⟨k,hk,eq⟩:=List.mem_map.mp h
      have tl:=ArchiveJ.tick_lt (prev j)
      rcases Shadow7.scratchS_cases _ k tl (List.mem_range.mp hk) with ⟨-,b1,-⟩|⟨-,b1,-⟩ <;>
        simp only [Wire] at * <;> omega
  have normal:=Shadow7.ext_head (Shadow7.enterP j) j (withArchive j d) (support j++ArchiveJ7.rawPortsList (prev j)) s a b q
    touch (EnterJ7.notWire j port) notAdmin (admin_cover j h1 h21 d)
  apply normal.trans
  have clean:(eraseSites (EnterJ7.pending j) s).basis q=false:=by
    by_cases inPair:q∈(EnterJ7.upperPairs j).map Prod.fst
    · obtain ⟨pair,hp,rfl⟩:=List.mem_map.mp inPair
      exact (cut.upper _ hp).1
    · have notHi:q∉RailPair.sites (EnterJ7.upperPairs j):=by
        intro m
        rcases EnterJ7.upperSites j m with ⟨u1,u2⟩|⟨u1,u2⟩
        · apply inPair
          simp only [Wire] at u1 u2
          simp only [EnterJ7.upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp]
          exact ⟨q-(start j+Shadow7.sbP (start j)+35),by omega,by omega⟩
        · simp only [Wire] at *; omega
      have above:start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)≤q:=by
        by_contra lo
        simp only [Nat.not_le] at lo
        apply inPair
        simp only [EnterJ7.upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp]
        exact ⟨q-(start j+Shadow7.sbP (start j)+35),by omega,by omega⟩
      have rl:start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)=start j+railP (start j)+16 ∧
          (257≤railP (start j) ∨ start j+railP (start j)=513) ∧ railP (start j+14)≤railP (start j):=by
        have:=j.isLt; simp only [Shadow7.wpP,railP,Shadow7.sbP,start]; split_ifs <;> omega
      have k0:q-(start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j))<20:=by omega
      have free:=upperFree_all j h1 h21 ⟨_,k0⟩ (by simp only; omega)
      simp only [show start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+(q-(start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)))=q by omega] at free
      have hn:q≠EnterJ7.flagN j:=by simp only [EnterJ7.flagN,Wire]; omega
      have hf:q≠EnterJ7.flagF j:=by simp only [EnterJ7.flagF,Wire]; omega
      have hu:q≠EnterJ7.flagU j:=by simp only [EnterJ7.flagU,Wire]; omega
      have src:=WideReference.incoming_free_A (start j) x p (by simp only [start]; omega) raw domain q
        (by omega) (by omega) free
      exact (cut.unchanged q hn hf hu notHi).trans (by simpa only [pullState,same] using src)
  simpa [eraseSites,pend] using clean

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction CodecBitSliceVerify EnterProof PortalValues SkywalkRails Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! First-form window head (par-c2): what the first block's window keeps (pack only, no archive). -/
theorem adminBand_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 → ∀q∈support j,
    q<Shadow7.sbP (start j)+805 ∨ (Shadow7.sbP (start j)+802+Shadow7.wpP (start j)≤q ∧ q<Shadow7.sbP (start j)+1574) ∨ Shadow7.sbP (start j)+1579<q := by
  decide +kernel
theorem free_admin (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) : ∀q∈NativeJ7.protectedSites j,q∉support j := by
  intro q hq hm
  have b:=NativeJ7.protected_band j q hq
  have f:=EnterJ7.frame j
  have:=adminBand_all j h2 h19 q hm; simp only [Wire] at *; omega
theorem keeps_stored (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (s:State) (m:List Bool) (q:Wire)
    (hq:q∈NativeJ7.protectedSites j) : (run (Shadow7.body j (program j d)) m s).basis q=s.basis q :=
  Shadow7.body_cover j (program j d) (NativeJ7.protectedSites j) (support j)
    (NativeJ7.free_native j) (free_admin j h2 h19) (codes j h2 d).1 s m q hq
theorem source_tags (j : Fin 23) (s:BasisState) (z:SkywalkNat.State) (G S:Bool)
    (hit:∀q∈wires EnterProof.forward,s (EnterJ7.map j q)=(shadowRow (Shadow7.sbP (start j)) 15 z G S).testBit q) :
    s (EnterJ7.flagN j)=false ∧ s (EnterJ7.flagF j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      s (EnterJ7.flagU j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u) :=
  (actual_tags (EnterJ7.ports j) s (Shadow7.sbP (start j)) 15 z G S hit).2
theorem relay (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (s:State) (m:List Bool) (h:Nat) (x y:Bool)
    (high:regValue (EnterJ7.saved j) s.basis=h) (hn:s.basis (EnterJ7.flagN j)=false) (hf:s.basis (EnterJ7.flagF j)=x)
    (hu:s.basis (EnterJ7.flagU j)=y) :
    let out:=run (Shadow7.body j (program j d)) m s
    regValue (EnterJ7.saved j) out.basis=h ∧ out.basis (EnterJ7.flagN j)=false ∧ out.basis (EnterJ7.flagF j)=x ∧
      out.basis (EnterJ7.flagU j)=y :=
  keep_values (EnterJ7.flagN j) (EnterJ7.flagF j) (EnterJ7.flagU j) (EnterJ7.saved j) s (run (Shadow7.body j (program j d)) m s)
    h x y (keeps_stored j h2 h19 d s m) high hn hf hu
theorem saved_at_leave (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤21) (d:Bool) (raw cut:State) (z:SkywalkNat.State)
    (G S:Bool) (head ticks:List Bool) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (packed:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (negative S z.u) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u)) (pullState (EnterJ7.pull j) raw) cut)
    (input:SkywalkIntegerInput (EnterJ7.lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let out:=run (Shadow7.body j (program j d)) ticks (run (Shadow7.enterP j) head cut)
    regValue (EnterJ7.saved j) out.basis=(if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) ∧
      out.basis (EnterJ7.flagN j)=false ∧ out.basis (EnterJ7.flagF j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z) ∧
      out.basis (EnterJ7.flagU j)=decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u) := by
  let pre:=run (Shadow7.enterP j) head cut
  have high:=EnterJ7.high_from_cut j raw cut z G S head small packed input
  have body0:=EnterJ7.from_full j raw cut z G S head small packed input
  have tags:=source_tags j pre.basis z G S body0.2.1
  exact relay j h2 h19 d pre ticks (if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0) _ _
    high tags.1 tags.2.1 tags.2.2

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! First-form tail and upper rail (par-c2): as `NativeJ7.tail_clean/upper_clear` without archive and pending
(the first block's `e0+6..8` are spare, so its tail starts at `e0+6`, dadon's 225: `1724..1812`). -/
def tailTempsF (j : Fin 23) : List Wire :=
  List.range' (Shadow7.e0P (start j)+6) (min 1813 (2055-start j)-(Shadow7.e0P (start j)+6))
theorem tailF_mem (j : Fin 23) {q : Wire} (h : q∈tailTempsF j) :
    Shadow7.e0P (start j)+6≤q ∧ q≤1812 ∧ q+start j≤2054 := by
  simp only [tailTempsF,List.mem_range'_1] at h; simp only [Wire] at *; omega
theorem tailF_geometry (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21) {q : Wire} (hq : q∈tailTempsF j) :
    windowNet j q=q ∧ EnterJ7.pull j q=q ∧ ¬Shadow7.MayTouch j q ∧ q∉EnterJ7.ports j ∧
    q≠EnterJ7.flagN j ∧ q≠EnterJ7.flagF j ∧ q≠EnterJ7.flagU j ∧ q∉RailPair.sites (EnterJ7.upperPairs j) := by
  have t:=tailF_mem j hq
  have f:=EnterJ7.frame j
  simp only [Shadow7.e0P] at t
  refine ⟨?_,?_,?_,fun m=>?_,?_,?_,?_,fun m=>?_⟩
  · rw [windowNet,net]
    exact Shadow7.sig_tail j h21 q (by have:=t.1; simp only [Shadow7.e0P,Wire] at *; omega) t.2.2 (start j+14) (le_refl _)
  · rw [EnterJ7.pull]
    exact Shadow7.sig_tail j h21 q (by have:=t.1; simp only [Shadow7.e0P,Wire] at *; omega) t.2.2 (start j-1)
      (by have:=EnterJ7.frame j; simp only [Wire] at *; omega)
  · unfold Shadow7.MayTouch; simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *; simp only [Wire] at *; omega
  · have:=EnterJ7.portsRegion j m; simp only [Wire] at *; omega
  · simp only [EnterJ7.flagN,Wire]; omega
  · simp only [EnterJ7.flagF,Wire]; omega
  · simp only [EnterJ7.flagU,Wire]; omega
  · have:=EnterJ7.upperSites j m; simp only [Wire] at *; omega
theorem tailFHead_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 → ∀q∈support j,
    q<Shadow7.sbP (start j)+1580 ∨ 2055≤q+start j := by
  decide +kernel
theorem tailF_clean (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21) (d:Bool) (x p:Nat) (raw v:State)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) v) :
    ∀q∈tailTempsF j,(run (Shadow7.body j (program j d)) b (run (Shadow7.enterP j) a v)).basis q=false := by
  intro q hq
  obtain ⟨wn,same,touch,port,hn,hf,hu,hi⟩:=tailF_geometry j h1 h21 hq
  have t:=tailF_mem j hq
  have notAdmin:q∉support j:=by
    intro h; have:=tailFHead_all j h1 h21 q h; simp only [Shadow7.e0P,Wire] at *; omega
  have stay:=Shadow7.ext_head (Shadow7.enterP j) j (program j d) (support j) v a b q
    (by rw [wn]; exact touch) (EnterJ7.notWire j port) notAdmin (codes j h1 d).1
  have read:=cut.unchanged q hn hf hu hi
  have canon:v.basis q=raw.basis q:=by simpa only [pullState,same] using read
  have zero:raw.basis q=false:=WideReference.domain_carry (by simp only [start]; omega) domain q
    (by simp only [Shadow7.e0P,Wire] at *; omega) t.2.1
  exact stay.trans (canon.trans zero)
theorem upperFreeF_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 → ∀k:Fin 20,
    start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val≤min (start j+30+railP (start j+14)) 529 →
    start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val∈(W.compactSkywalkSignPoolA base (start j)).released ∨
      (start j+274≤start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val ∧ start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+k.val<786) := by
  decide +kernel
theorem upperFHead_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 → ∀q∈support j,
    q<start j+Shadow7.sbP (start j)+50 ∨ 1043<q := by
  decide +kernel

theorem upperF_clear (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21) (d:Bool) (raw s:State) (x p:Nat)
    (domain:WideReference.Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) s)
    (q:Nat) (low:start j+Shadow7.sbP (start j)+50≤q) (high:q≤min (start j+30+railP (start j+14)) 529) :
    (run (Shadow7.body j (program j d)) b (run (Shadow7.enterP j) a s)).basis q=false := by
  have f:=EnterJ7.frame j
  have wn:windowNet j q=q:=by
    rw [windowNet,net]
    exact WideReference.sig_rail j q (le_trans high (min_le_right _ _)) (start j+14) (le_refl _)
  have same:EnterJ7.pull j q=q:=by
    rw [EnterJ7.pull]
    exact WideReference.sig_rail j q (le_trans high (min_le_right _ _)) (start j-1)
      (by have:=EnterJ7.frame j; simp only [Wire] at *; omega)
  have touch:¬Shadow7.MayTouch j (windowNet j q):=by
    rw [wn]; unfold Shadow7.MayTouch; simp only [Shadow7.shape,Shadow7.smallBits,Shadow7.sbP] at *; simp only [Wire] at *; omega
  have port:q∉EnterJ7.ports j:=fun m=>by have:=EnterJ7.portsRegion j m; simp only [Wire] at *; omega
  have notAdmin:q∉support j:=by
    intro h; have:=upperFHead_all j h1 h21 q h; simp only [Wire] at *; omega
  have normal:=Shadow7.ext_head (Shadow7.enterP j) j (program j d) (support j) s a b q
    touch (EnterJ7.notWire j port) notAdmin (codes j h1 d).1
  apply normal.trans
  have clean:s.basis q=false:=by
    by_cases inPair:q∈(EnterJ7.upperPairs j).map Prod.fst
    · obtain ⟨pair,hp,rfl⟩:=List.mem_map.mp inPair
      exact (cut.upper _ hp).1
    · have notHi:q∉RailPair.sites (EnterJ7.upperPairs j):=by
        intro m
        rcases EnterJ7.upperSites j m with ⟨u1,u2⟩|⟨u1,u2⟩
        · apply inPair
          simp only [Wire] at u1 u2
          simp only [EnterJ7.upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp]
          exact ⟨q-(start j+Shadow7.sbP (start j)+35),by omega,by omega⟩
        · simp only [Wire] at *; omega
      have above:start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)≤q:=by
        by_contra lo
        simp only [Nat.not_le] at lo
        apply inPair
        simp only [EnterJ7.upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp]
        exact ⟨q-(start j+Shadow7.sbP (start j)+35),by omega,by omega⟩
      have rl:start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)=start j+railP (start j)+16 ∧
          (257≤railP (start j) ∨ start j+railP (start j)=513) ∧ railP (start j+14)≤railP (start j):=by
        have:=j.isLt; simp only [Shadow7.wpP,railP,Shadow7.sbP,start]; split_ifs <;> omega
      have k0:q-(start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j))<20:=by omega
      have free:=upperFreeF_all j h1 h21 ⟨_,k0⟩ (by simp only; omega)
      simp only [show start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)+(q-(start j+Shadow7.sbP (start j)+32+Shadow7.wpP (start j)))=q by omega] at free
      have hn:q≠EnterJ7.flagN j:=by simp only [EnterJ7.flagN,Wire]; omega
      have hf:q≠EnterJ7.flagF j:=by simp only [EnterJ7.flagF,Wire]; omega
      have hu:q≠EnterJ7.flagU j:=by simp only [EnterJ7.flagU,Wire]; omega
      have src:=WideReference.incoming_free_A (start j) x p (by simp only [start]; omega) raw domain q
        (by omega) (by omega) free
      exact (cut.unchanged q hn hf hu notHi).trans (by simpa only [pullState,same] using src)
  exact clean

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! `NativePack{s}.agree_origin` for an interior block, on wires `OB5.sig (s+14)` does not move.
    The band `[1301,1044+s+14]` is excluded by `still`: `sig` is not the identity there.
    Comparison is `box_origin_j`; the unmoved frame is `sig_fixed`. -/
/-! The first block of the window (`WideReference.firstBlock`) keeps only the last five stock ticks in
    `oldSites`, so the `rawHead`/`support` wires of the ten ticks before those are in neither `Box` nor `sites`.
    Every other block has the full 15. -/
theorem admin_outside (j : Fin 23) (h2 : 2≤j.val) (h21 : j.val≤21) (hne : start j≠WideReference.firstBlock)
    (q : Wire) (hq : q∈ArchiveJ7.rawHead (prev j)++support j) :
    WideReference.Box (start j) q ∨ q∈WideReference.sites (start j) := by
  have f:=EnterJ7.frame j
  have tick:start (prev j)+15=start j:=by simp only [prev,start]; omega
  have s10:(10:Nat)≤(start j:Nat):=by have h:=f.1; simp only [start] at h; omega
  have s15:(15:Nat)≤(start j:Nat):=by have h:=f.1; simp only [start] at h; omega
  have inSites (r:Nat) (hr1:start j-15≤r) (hr2:r<start j) :
      base r∈WideReference.sites (start j) ∧
      OB5.sig (start j) (base (1028+r))∈WideReference.sites (start j) ∧
      OB5.sig (start j) (base r)=base r ∧
      OB5.sig (start j) (base (1028+r))=OB5.sig (start j+14) (base (1028+r)) := by
    have hr:r≤390:=by have:=f; simp only [Wire] at *; omega
    have idA:OB5.sig (start j+14) (base r)=base r:=by
      rw [show base r=r+16 by simp [base]]
      exact WideReference.sig_fixed (by simp only [Wire] at *; omega) (by simp only [Wire] at *; omega)
    have idAs:OB5.sig (start j) (base r)=base r:=by
      rw [show base r=r+16 by simp [base]]
      exact WideReference.sig_fixed (by simp only [Wire] at *; omega) (by simp only [Wire] at *; omega)
    have eqB:OB5.sig (start j) (base (1028+r))=OB5.sig (start j+14) (base (1028+r)):=by
      rw [OB5.sig_base (start j) (1028+r) (by have:=f; simp only [start]; omega),
        OB5.sig_base (start j+14) (1028+r) (by have:=f; simp only [start]; omega)]
      have:=f; simp only [base, Wire] at *; split_ifs <;> omega
    refine ⟨?_,?_,idAs,eqB⟩
    · rw [← idA]; unfold WideReference.sites
      refine List.mem_map.mpr ⟨base r,?_,rfl⟩
      unfold WideReference.oldSites
      rw [WideReference.oldStart_interior hne, WideReference.oldCount_interior hne]
      simp only [List.mem_flatMap, List.mem_cons]
      exact ⟨r, List.mem_range'.mpr ⟨r-(start j-15), by omega, by omega⟩, Or.inl rfl⟩
    · unfold WideReference.sites
      refine List.mem_map.mpr ⟨base (1028+r),?_,eqB.symm⟩
      unfold WideReference.oldSites
      rw [WideReference.oldStart_interior hne, WideReference.oldCount_interior hne]
      simp only [List.mem_flatMap, List.mem_cons]
      exact ⟨r, List.mem_range'.mpr ⟨r-(start j-15), by omega, by omega⟩, Or.inr (Or.inl rfl)⟩
  have flagBox (n:Nat) (hn:n=6 ∨ n=7 ∨ n=8) : WideReference.Box (start j) (Shadow7.e0P (start j)+n) := by
    unfold WideReference.Box
    right; right; left
    have:=f; simp only [Shadow7.e0P, Wire] at *; rcases hn with rfl|rfl|rfl <;> omega
  simp only [List.mem_append, ArchiveJ7.rawHead, support, cellsLoadP, tick] at hq
  rcases hq with hq|hq
  · simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with ⟨k,hk,hq⟩|hq
    · rcases hq with rfl|rfl
      · right
        have cell:=inSites (start j-10+k) (by omega) (by omega)
        have addr:base (start j-10+k)=start j+6+k:=by
          simp only [base, Wire]; omega
        rw [← addr]; exact cell.1
      · right
        have cell:=inSites (start j-10+k) (by omega) (by omega)
        have addr:base (1028+(start j-10+k))=start j+1034+k:=by
          simp only [base, Wire]; omega
        rw [← addr]; exact cell.2.1
    · left
      rcases hq with rfl|rfl|rfl
      · exact flagBox 6 (Or.inl rfl)
      · exact flagBox 7 (Or.inr (Or.inl rfl))
      · exact flagBox 8 (Or.inr (Or.inr rfl))
  · simp only [List.mem_flatMap, List.mem_range', List.mem_cons, List.not_mem_nil, or_false] at hq
    obtain ⟨v,hv,hq⟩:=hq
    obtain ⟨i,hi,hsum⟩:=hv
    have hv1:start j-15≤v:=by simp only [start,Wire] at *; omega
    have hv2:v<start j-10:=by simp only [start,Wire] at *; omega
    right
    rcases hq with rfl|rfl
    · have cell:=inSites v hv1 (by omega)
      rw [cell.2.2.1]; exact cell.1
    · exact (inSites v hv1 (by omega)).2.1
theorem agree_origin (j : Fin 23) (h2 : 2≤j.val) (h21 : j.val≤21) (hne : start j≠WideReference.firstBlock) (d : Bool)
    (raw s : State) (m t : List Bool) (neg far long : Bool)
    (packed : PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j)
      (EnterJ7.flagF j) (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw)
      (eraseSites (EnterJ7.pending j) s))
    (q : Wire) (ext : ¬WideReference.Box (start j) q)
    (still : ¬(1301≤(q:Nat) ∧ (q:Nat)≤1044+(start j+14)))
    (mirror : ¬(2069≤(q:Nat)+(start j+14) ∧ (q:Nat)≤1812))
    (nh : ¬(369≤start j ∧ 1302≤(q:Nat)+start j ∧ (q:Nat)≤933)) :
    let history := run (Shadow7.body j (withArchive j d)) t (run (Shadow7.enterP j) m s)
    history.basis q = (WideReference.origin (start j) raw history).basis q := by
  intro history
  have f := EnterJ7.frame j
  have hw := WideReference.route_width (start j+14) (by have := f; omega)
  have h0 := WideReference.route_width (start j) (by have := f; omega)
  have wdef : Shadow7.wpP (start j) = railP (start j) - Shadow7.sbP (start j) - 16 := rfl
  have rdef : railP (start j) = W.narrowSkywalkRouteWidth (start j) := by
    rw [WideReference.route_eq (start j) (by have := f; omega)]; rfl
  have wn : windowNet j q = q := by
    rw [windowNet, net]; exact WideReference.sig_fixed still mirror
  have pullId : OB5.sig (start j-1) q = q := by
    refine WideReference.sig_fixed ?_ ?_
    · intro h; apply still; simp only [Wire] at *; omega
    · intro h; apply mirror; simp only [Wire] at *; omega
  have notMay : ¬Shadow7.MayTouch j q := by
    intro mt
    apply ext
    unfold Shadow7.MayTouch at mt
    have mid : (Shadow7.shape j).mid = Shadow7.sbP (start j)+17 := rfl
    rw [mid] at mt
    unfold WideReference.Box
    simp only [Wire] at *
    omega
  have free : ¬Shadow7.MayTouch j (windowNet j q) := by rwa [wn]
  have port : q∉EnterJ7.ports j := by
    intro mem
    apply ext
    have r := EnterJ7.portsRegion j mem
    unfold WideReference.Box
    simp only [Wire] at *
    omega
  apply WideReference.box_origin_j j ext raw history
  intro notSite
  have notAdmin : q∉support j++ArchiveJ7.rawPortsList (prev j) := by
    intro mem
    rw [ArchiveJ7.raw_split, List.mem_append, List.mem_append] at mem
    rcases mem with mem|mem|mem
    · rcases admin_outside j h2 h21 hne q (List.mem_append_right _ mem) with b|b
      · exact ext b
      · exact notSite b
    · rcases admin_outside j h2 h21 hne q (List.mem_append_left _ mem) with b|b
      · exact ext b
      · exact notSite b
    · obtain ⟨k,hk,eq⟩ := List.mem_map.mp mem
      have hk' := List.mem_range.mp hk
      have tick : start (prev j)+15 = start j := by simp only [prev, start]; omega
      have qeq : (q:Nat) = Shadow7.scratchS (start j) k := by simpa only [tick, Wire] using eq.symm
      have still' : ¬(1301 ≤ Shadow7.scratchS (start j) k ∧ Shadow7.scratchS (start j) k ≤ 1044+(start j+14)) := by
        rw [← qeq]; exact still
      have mirror' : ¬(2069 ≤ Shadow7.scratchS (start j) k+(start j+14) ∧ Shadow7.scratchS (start j) k ≤ 1812) := by
        rw [← qeq]; exact mirror
      rcases Shadow7.scratchS_cases (start j) k (by simp only [start]; omega) hk' with ⟨eqs,lo,hi⟩|⟨lo,hi⟩
      · apply ext
        unfold WideReference.Box
        rw [qeq]
        omega
      · exact nh ⟨lo, by rw [qeq]; omega⟩
  have stay := Shadow7.ext_head (Shadow7.enterP j) j (withArchive j d)
      (support j++ArchiveJ7.rawPortsList (prev j)) s m t q free (EnterJ7.notWire j port) notAdmin
      (admin_cover j (by omega) h21 d)
  have hn : q≠EnterJ7.flagN j := by
    intro eq; apply ext; rw [eq]; unfold WideReference.Box EnterJ7.flagN
    simp only [Wire] at *; omega
  have hf : q≠EnterJ7.flagF j := by
    intro eq; apply ext; rw [eq]; unfold WideReference.Box EnterJ7.flagF
    simp only [Wire] at *; omega
  have hu : q≠EnterJ7.flagU j := by
    intro eq; apply ext; rw [eq]; unfold WideReference.Box EnterJ7.flagU
    simp only [Wire] at *; omega
  have hi : q∉RailPair.sites (EnterJ7.upperPairs j) := by
    intro m; apply ext
    have u := EnterJ7.upperSites j m
    unfold WideReference.Box
    simp only [Wire] at *
    omega
  have pend : q∉EnterJ7.pending j := by
    intro mem; apply ext
    simp only [EnterJ7.pending, List.mem_cons, List.not_mem_nil, or_false] at mem
    unfold WideReference.Box
    simp only [Wire] at *
    rcases mem with rfl|rfl|rfl <;> omega
  have old := packed.unchanged q hn hf hu hi
  have same : history.basis q = (pullState (OB5.sig (start j-1)) raw).basis q := by
    rw [stay]
    simpa only [eraseSites, if_neg pend, EnterJ7.pull, pullId] using old
  exact same

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run measurementCount Shadow7.onRails

/-- The entry's saved high word is the leave's bank `ys` (dadon's literal lists agree per block). -/
theorem saved_ys (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) : EnterJ7.saved j = LeaveJ7.ys j := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have r := Shadow7.rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have wp3 : 3 ≤ Shadow7.wpP (start j) := by omega
  have hr : List.range (Shadow7.wpP (start j)) = List.range 3 ++ (List.range (Shadow7.wpP (start j) - 3)).map (3 + ·) := by
    rw [← List.range_add]; congr 1; omega
  rw [LeaveJ7.ys, hr, List.map_append, List.map_map]
  simp only [EnterJ7.saved, EnterJ7.upperPairs, List.map_map]
  congr 1
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append,
      Shadow7.bankW, if_pos (show (0:Nat) < 3 by omega), if_pos (show (1:Nat) < 3 by omega), if_pos (show (2:Nat) < 3 by omega)]
    rw [ee]; simp only [List.cons.injEq, and_true]; omega
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp, Shadow7.bankW]
    rw [if_neg (by omega), if_pos (by omega)]
    (try unfold Wire at *); omega

/-- dadon's `NativePack{s}.admitted`, generic: block `j`'s window head delivers the leave's `Admission.Inputs`. -/
theorem admitted (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤20) (d:Bool) (x p:Nat) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (numbers:LeaveJ7.Admission.Numeric j z)
    (domain:WideReference.Domain (start j) x p raw)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    LeaveJ7.Admission.Inputs j (run (nextWindow j d) m s) z G S := by
  obtain ⟨w1, w2⟩ := start_win j h2 (by omega)
  have r := Shadow7.rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  have saved:=saved_with_pending j h2 (by omega) d raw s z G S m tape numbers.farSmall cut input
  have all:=next_window j h2 (by omega) d raw s m z G S numbers.odd numbers.farSmall cut input hist scratch past pg ps cross
    po pm prior
  obtain ⟨_,_,_,_,tags⟩:=real_receipt j h2 (by omega) d raw s m z G S numbers.odd numbers.farSmall cut input hist scratch
    past pg ps cross po pm prior
  -- the archive frame, for the overflow spares (dadon's 255 `extra_clean`)
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z numbers.farSmall numbers.odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m numbers.farSmall cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j h2 (by omega) d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity
    ready.2.1 scratch past pg ps cross po pm prior
  have final:=archive_result j h2 (by omega) d row limit _ _ frame
  have tail:=tail_clean j h2 (by omega) d x p raw s domain m tape _ _ _ cut row final
  have runEq : run (nextWindow j d) m s = run (Shadow7.body j (withArchive j d)) tape pre := by
    simp only [nextWindow, window, run_append, run_take, pre, tape]
  apply LeaveJ7.Admission.assemble j h2 (by omega) _ z G S numbers all.2.1 all.2.2.1
  · rw [runEq, ←saved_ys j h2 (by omega)]
    refine ⟨saved.1, ?_, ?_, ?_⟩
    · have e : Shadow7.e0P (start j) + 5 = EnterJ7.flagN j := by simp only [EnterJ7.flagN, Shadow7.e0P]; omega
      rw [e]; exact saved.2.1
    · have e : Shadow7.e0P (start j) + 3 = EnterJ7.flagF j := by simp only [EnterJ7.flagF, Shadow7.e0P]; omega
      rw [e]; exact saved.2.2.1
    · have e : Shadow7.e0P (start j) + 4 = EnterJ7.flagU j := by simp only [EnterJ7.flagU, Shadow7.e0P]; omega
      rw [e]; exact saved.2.2.2
  · intro q hq
    rw [LeaveJ7.Admission.mem_spare] at hq
    rcases hq with rfl | rfl | ⟨lo, hi⟩
    · have t := tags ⟨0, by omega⟩
      have e : Shadow7.e0P (start j) + 6 = Shadow7.sbP (start j)+1580+0 := by simp only [Shadow7.e0P]; omega
      rw [e]; exact t
    · have t := tags ⟨1, by omega⟩
      have e : Shadow7.e0P (start j) + 7 = Shadow7.sbP (start j)+1580+1 := by simp only [Shadow7.e0P]; omega
      rw [e]; exact t
    · rw [runEq]
      apply tail q
      simp only [tailTemps, List.mem_range'_1]
      (try unfold Wire at *); omega

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step Shadow7.onRails measurementCount

/-- dadon's `NativePack{s}.from_domain_matched`, generic (interior blocks `j ≥ 2`): from the stock-reference domain
at `start j`, the window head admits the leave, keeps the phase, keeps the previous archive at a row matching the
previous block's trace, and unwinds. `scratch` (the archive codec scratch is clean) is par-d2's `scratch_raw_clean`. -/
theorem from_domain_matched (j : Fin 23) (h2 : 2≤j.val) (h19 : j.val≤20) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (m:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (pg ps cross:Bool)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) (unsigned (start (prev j)) x p) pg ps cross s) :
    let out:=run (nextWindow j d) m s
    LeaveJ7.Admission.Inputs j out (unsigned (start j) x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,RowTruth (unsigned (start (prev j)) x p) pg ps row ∧ Kept (ArchiveJ7.codePorts (prev j)) d row out) ∧
    ∀n,run (nextUnwind j d) n out=s:=by
  let z:=unsigned (start j) x p
  let past:=unsigned (start (prev j)) x p
  have nums:=LeaveJ7.Admission.actualNumbers j (by omega) (by omega) x p good
  have old:=LeaveJ7.Admission.actualNumbers (prev j) (by simp only [prev]; omega) (by simp only [prev]; omega) x p good
  have hist:=pulled_history j rfl domain
  have a:=next_window j (by omega) (by omega) d raw s m z G S nums.odd nums.farSmall cut input hist scratch past pg ps cross
    old.odd old.farSmall prior
  obtain ⟨row,limit,truth,code,_⟩:=real_receipt j (by omega) (by omega) d raw s m z G S nums.odd nums.farSmall cut input hist
    scratch past pg ps cross old.odd old.farSmall prior
  exact ⟨admitted j (by omega) (by omega) d x p raw s m z G S nums domain cut input hist scratch past pg ps cross old.odd old.farSmall
    prior,a.1,⟨row,limit,truth,code⟩,a.2.2.2⟩

/-- dadon's `NativePack{s}.from_domain`: `from_domain_matched` without the row's trace. -/
theorem from_domain (j : Fin 23) (h2 : 2≤j.val) (h19 : j.val≤20) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (m:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (pg ps cross:Bool)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) (unsigned (start (prev j)) x p) pg ps cross s) :
    let out:=run (nextWindow j d) m s
    LeaveJ7.Admission.Inputs j out (unsigned (start j) x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,Kept (ArchiveJ7.codePorts (prev j)) d row out) ∧ ∀n,run (nextUnwind j d) n out=s:=by
  obtain ⟨i,ph,⟨row,limit,_,code⟩,un⟩:=from_domain_matched j h2 (by omega) d x p good raw s m domain G S cut input scratch pg ps
    cross prior
  exact ⟨i,ph,⟨row,limit,code⟩,un⟩

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2 (job D2): the archive scratch of block `j-1` is clean after block `j`'s head (enter, Shadow7.routed first tick,
pack), for every loader `2 ≤ j ≤ 19`. Each scratch wire `Shadow7.scratchW (start j) kk` is either
- below the live anchored block `e0..e0+9`: a carry wire of block `j`'s tick 1, clean on the rails; or
- above it (`e0+10 .. 1699`, only for loaders from 285 on: the old anchored blocks of blocks 270..j-1): a carry
  wire of the stock tick `start j`. The hand-off cut keeps it at its stock value (`PackedCut.frame`, it is no flag,
  pending flag or rail-pair site), `SkywalkIntegerInput` says that value is zero, and neither the enter, the first
  tick nor the pack touch it.
So no chain invariant is needed: the cut of `At{s}` already carries it. All geometry is `omega` over `j`. -/

theorem prev_tick (j : Fin 23) (h1 : 1≤j.val) : start (prev j)+15=start j := by
  simp only [prev,start]; (try simp only [Wire] at *); omega

/-- Archive scratch port `kk` of the archive loaded in block `j` (`Shadow7.scratchS`: the raw port `Shadow7.scratchW` while it
is a carry wire of the stock tick `start j`, a released B-rail wire beyond; equal to `Shadow7.scratchW` up to 360). -/
def scratchPort (j : Fin 23) (kk : Nat) : Wire := Shadow7.scratchS (start j) kk

theorem scratch_port (j : Fin 23) (h1 : 1≤j.val) (k : Fin 157) (hk : 23≤k.val) :
    ArchiveJ7.rawPorts (prev j) k=scratchPort j (k.val-23) := by
  have a:=ArchiveJ7.raw_scratch (prev j) (k:=k.val-23) (by omega)
  rw [show 23+(k.val-23)=k.val by omega,prev_tick j h1] at a
  rw [ArchiveJ7.rawPorts,a,scratchPort]

/-- Scratch wires below the live block are carry wires of block `j`'s tick 1. -/
theorem lower_carry (j : Fin 23) {kk : Nat} (h : 1556+kk<Shadow7.e0P (start j)) :
    1556+kk∈(IntegerPacket.ports (Shadow7.shape j) 1).carry.map (windowNet j) := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at h
  apply List.mem_map.mpr
  refine ⟨1556+kk,?_,?_⟩
  · simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,List.mem_range'_1]; (try simp only [Wire] at *); omega
  · simp only [windowNet,net,OB5.sig_nat,OB5.sigNat,start]
    split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | rfl | omega

/-- The stock route width stays at least 145 through tick 368. -/
theorem route_width (t : Nat) (ht : t≤368) : 145≤W.narrowSkywalkRouteWidth t := by
  unfold W.narrowSkywalkRouteWidth
  simp only [Nat.min_def]
  split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | rfl | omega

theorem upper_support (j : Fin 23) (h19 : j.val≤19) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (hi : w≤1699) :
    w∉support j := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo
  intro mem
  simp only [support,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at mem
  obtain ⟨v,⟨v1,v2⟩,e⟩:=mem
  simp only [OB5.sig_nat,OB5.sigNat,base,start] at e v1 v2
  rcases e with e|e <;> split_ifs at e with hc <;> (try rcases hc with hc|hc) <;> omega

theorem upper_first (j : Fin 23) (h19 : j.val≤19) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (hi : w≤1699) :
    Shadow7.firstUnchanged j w := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo
  have key:OB5.sigNat (start j+14) w=w ∨ (OB5.sigNat (start j+14) w+w=3113 ∧ 1414≤OB5.sigNat (start j+14) w) := by
    unfold OB5.sigNat
    simp only [start]
    split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | (left; rfl) | omega
  unfold Shadow7.firstUnchanged
  dsimp only
  right
  show OB5.sigNat (start j+14) w∉(IntegerPacket.ports (Shadow7.shape j) 0).wires
  generalize OB5.sigNat (start j+14) w=r at key ⊢
  intro mem
  simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at mem
  try simp only [Wire] at *
  omega

theorem upper_enter (j : Fin 23) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) : w∉EnterJ7.ports j := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo
  intro mem
  simp only [EnterJ7.ports,List.mem_cons,List.not_mem_nil,or_false,Shadow7.sbP,start] at mem
  try simp only [Wire] at *
  omega

theorem upper_cut (j : Fin 23) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) :
    w≠EnterJ7.flagN j ∧ w≠EnterJ7.flagF j ∧ w≠EnterJ7.flagU j ∧ w∉EnterJ7.pending j ∧
      w∉RailPair.sites (EnterJ7.lowerPairs j) ∧ w∉RailPair.sites (EnterJ7.upperPairs j) := by
  have hj:=j.isLt
  have wb:Shadow7.wpP (start j)≤258:=by
    simp only [Shadow7.wpP,railP]; split <;> (try split) <;> omega
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo
  simp only [start] at wb
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp only [EnterJ7.flagN,Shadow7.sbP,start]; (try simp only [Wire] at *); omega
  · simp only [EnterJ7.flagF,Shadow7.sbP,start]; (try simp only [Wire] at *); omega
  · simp only [EnterJ7.flagU,Shadow7.sbP,start]; (try simp only [Wire] at *); omega
  · intro mem
    simp only [EnterJ7.pending,Shadow7.sbP,start,List.mem_cons,List.not_mem_nil,or_false] at mem
    try simp only [Wire] at *
    omega
  · intro mem
    simp only [RailPair.sites,EnterJ7.lowerPairs,Shadow7.sbP,start,List.flatMap_cons,List.flatMap_nil,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.append_nil] at mem
    try simp only [Wire] at *
    omega
  · intro mem
    simp only [RailPair.sites,EnterJ7.upperPairs,List.mem_flatMap,List.mem_map,List.mem_range,List.mem_cons,
      List.not_mem_nil,or_false] at mem
    obtain ⟨_,⟨i,hi,rfl⟩,e⟩:=mem
    simp only [Shadow7.sbP,start] at e hi
    try simp only [Wire] at *
    omega

theorem upper_pull (j : Fin 23) (h19 : j.val≤19) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (hi : w≤1699) :
    EnterJ7.pull j w=w := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo
  show @Eq Nat (OB5.sigNat (start j-1) w) w
  simp only [OB5.sigNat,start]
  split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | rfl | omega

theorem upper_carry (j : Fin 23) (h19 : j.val≤19) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (hi : w≤1699) :
    w∈(EnterJ7.lay j).carry := by
  have hj:=j.isLt
  have rw':=route_width (start j) (by simp only [start]; omega)
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo
  simp only [start] at rw'
  simp only [EnterJ7.lay,W.compactSkywalkTickLayout,W.compactSkywalkTickPreWidth,wireBlock,List.mem_map,
    List.mem_range'_1,start]
  have h16:16≤w:=by omega
  refine ⟨w-16,⟨?_,?_⟩,?_⟩
  · omega
  · omega
  · show w-16+16=w
    omega

/-- **D2's invariant.** After block `j`'s head every scratch port of the archive of block `j-1` is clean, for every
loader `2 ≤ j ≤ 19`; the statement is `next_window`'s `scratch` hypothesis. Inputs: the hand-off cut and the stock
input at tick `start j` (`At{s}`), and the rails after the enter. -/
theorem scratch_clean (j : Fin 23) (h2 : 2≤j.val) (h19 : j.val≤19) (d:Bool) (raw s:State) (m:List Bool)
    (neg far long G:Bool) (A B:Int) (Z:SkywalkRails.State) (parity:(Z.a+Z.b)%2=1)
    (active:Shadow7.onRails j 0 Z (run (Shadow7.enterP j) m s).basis)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) A B G raw.basis) :
    ∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false := by
  intro k hk
  dsimp only
  have hj:=j.isLt
  rw [scratch_port j (by omega) k hk,scratchPort,Shadow7.scratchS_window _ _ (by simp only [start]; omega) (by omega)]
  by_cases low:1556+(k.val-23)<Shadow7.e0P (start j)
  · have on:=completed_head j (by omega) d (run (Shadow7.enterP j) m s) (m.drop (measurementCount (Shadow7.enterP j)))
      ((m.drop (measurementCount (Shadow7.enterP j))).drop (measurementCount (Shadow7.routed j 0 1))) Z parity active
    rw [Shadow7.scratchW_low _ _ low]
    obtain ⟨c,hc,eq⟩:=List.mem_map.mp (lower_carry j low)
    rw [←eq]
    exact (regValue_zero _ _).mp on.2.2.2.1 _ hc
  · have hw:Shadow7.scratchW (start j) (k.val-23)=1566+(k.val-23):=if_neg low
    have lo:Shadow7.e0P (start j)+10≤1566+(k.val-23):=by omega
    have hi:1566+(k.val-23)≤1699:=by omega
    rw [hw]
    obtain ⟨nN,nF,nU,nP,nLo,nHi⟩:=upper_cut j lo
    rw [run_preserves_outside _ _ _ _ (fun used=>upper_support j h19 lo hi (List.mem_toFinset.mp ((codes j (by omega) d).1 used))),
      Shadow7.first_preserves j Z parity _ _ active _ (upper_first j h19 lo hi),
      run_preserves_outside _ _ _ _ (EnterJ7.notWire j (upper_enter j lo))]
    have f:=cut.frame _ nN nF nU nLo nHi
    simp only [eraseSites,nP,↓reduceIte,pullState,upper_pull j h19 lo hi] at f
    rw [f]
    exact (regValue_zero _ _).mp input.2.2.2.2.2 _ (upper_carry j h19 lo hi)

/-- `ArchiveJ7.retain_watch`'s `clean` and `load_record`'s `blank` follow (restrict to the watched ports). -/
theorem watch_clean (j : Fin 23) (h2 : 2≤j.val) (h19 : j.val≤19) (d:Bool) (raw s:State) (m:List Bool)
    (neg far long G:Bool) (A B:Int) (Z:SkywalkRails.State) (parity:(Z.a+Z.b)%2=1)
    (active:Shadow7.onRails j 0 Z (run (Shadow7.enterP j) m s).basis)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) A B G raw.basis) :
    ∀k:Fin 157,23≤k.val → ArchiveJ7.rawPorts (prev j) k∈Shadow7.watch j →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false :=
  fun k hk _=>scratch_clean j h2 h19 d raw s m neg far long G A B Z parity active cut input k hk

/-- `next_window` without its `scratch` hypothesis: D2's invariant discharges it for every loader `2 ≤ j ≤ 19`. -/
theorem next_window_clean (j : Fin 23) (h2 : 2≤j.val) (h19 : j.val≤19) (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    let out:=run (nextWindow j d) m s
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] (encode G S T.u T.v)) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      ∀t,run (nextUnwind j d) t out=s := by
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m small cut input hist
  exact next_window j (by omega) (by omega) d raw s m z G S odd small cut input hist
    (scratch_clean j h2 h19 d raw s m _ _ _ G _ _ Z parity ready.2.1 cut input) past pg ps cross po pm prior
#print axioms next_window_clean

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2: D2's invariant for the 90..390 target, loaders `2 ≤ j ≤ 21`, for `Shadow7.scratchS` (window390: the
ports beyond the stock carry are re-hosted on released B-rail wires). With `w := Shadow7.scratchW t kk`, `t = start j`:
- `w` below `e0`: a tick-1 carry wire (as in `scratch_clean`).
- `w ≥ e0+10` and `w+t < 2068`: the port is `w`. The cut keeps it at its stock value, and the stock state has
  the whole 257-wire carry `1556..1812` clean (`WideReference.full_carry` from `Domain`).
- `w+t ≥ 2068` (only `t = 375, 390`): the port is the host `w-766 ∈ [1302-t, 933]`, a released wire of the stock
  B rail. The cut keeps it at its stock value, clean by `WideReference.released_clear`.
Enter, first tick and pack never touch these ports. -/

/-- Unwrapped upper ports (`w+t < 2069`) for `j ≤ 21`: untouched by the pack and the first tick. -/
theorem mid_support (j : Fin 23) (h21 : j.val≤21) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (nw : w+start j<2069) :
    w∉support j := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo nw
  intro mem
  simp only [support,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at mem
  obtain ⟨v,⟨v1,v2⟩,e⟩:=mem
  simp only [OB5.sig_nat,OB5.sigNat,base,start] at e v1 v2
  rcases e with e|e <;> split_ifs at e with hc <;> (try rcases hc with hc|hc) <;> omega

theorem mid_first (j : Fin 23) (h21 : j.val≤21) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (nw : w+start j<2069) :
    Shadow7.firstUnchanged j w := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo nw
  have key:OB5.sigNat (start j+14) w=w ∨ (OB5.sigNat (start j+14) w+w=3113 ∧ 1044+start j+1≤OB5.sigNat (start j+14) w) := by
    unfold OB5.sigNat
    simp only [start]
    split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | (left; rfl) | omega
  unfold Shadow7.firstUnchanged
  dsimp only
  right
  show OB5.sigNat (start j+14) w∉(IntegerPacket.ports (Shadow7.shape j) 0).wires
  generalize OB5.sigNat (start j+14) w=r at key ⊢
  intro mem
  simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at mem
  omega

theorem mid_pull (j : Fin 23) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (nw : w+start j<2069) :
    EnterJ7.pull j w=w := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo nw
  show @Eq Nat (OB5.sigNat (start j-1) w) w
  simp only [OB5.sigNat,start]
  split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | rfl | omega

/-- Wrapped ports `q = 3113-w` (`w+t ≥ 2069`, `w ≤ 1699`), for `j ≤ 21`. -/
theorem wrap_geometry (j : Fin 23) (h21 : j.val≤21) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (hi : w≤1699)
    (wr : 2069≤w+start j) :
    let q:=3113-w
    q∉support j ∧ Shadow7.firstUnchanged j q ∧ q∉EnterJ7.ports j ∧ q≠EnterJ7.flagN j ∧ q≠EnterJ7.flagF j ∧
      q≠EnterJ7.flagU j ∧ q∉EnterJ7.pending j ∧ q∉RailPair.sites (EnterJ7.lowerPairs j) ∧
      q∉RailPair.sites (EnterJ7.upperPairs j) := by
  have hj:=j.isLt
  have wb:Shadow7.wpP (start j)≤258:=by
    simp only [Shadow7.wpP,railP]; split <;> (try split) <;> omega
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo wr
  simp only [start] at wb
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro mem
    simp only [support,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at mem
    obtain ⟨v,⟨v1,v2⟩,e⟩:=mem
    simp only [OB5.sig_nat,OB5.sigNat,base,start] at e v1 v2
    rcases e with e|e <;> split_ifs at e with hc <;> (try rcases hc with hc|hc) <;> omega
  · unfold Shadow7.firstUnchanged
    dsimp only
    right
    show OB5.sigNat (start j+14) (3113-w)∉(IntegerPacket.ports (Shadow7.shape j) 0).wires
    have key:OB5.sigNat (start j+14) (3113-w)=w:=by
      unfold OB5.sigNat; simp only [start]
      split_ifs with hc <;> (try rcases hc with hc|hc) <;> omega
    rw [key]
    intro mem
    simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
      SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at mem
    omega
  · intro mem
    simp only [EnterJ7.ports,List.mem_cons,List.not_mem_nil,or_false,Shadow7.sbP,start] at mem
    omega
  · simp only [EnterJ7.flagN,Shadow7.sbP,start]; omega
  · simp only [EnterJ7.flagF,Shadow7.sbP,start]; omega
  · simp only [EnterJ7.flagU,Shadow7.sbP,start]; omega
  · intro mem
    simp only [EnterJ7.pending,Shadow7.sbP,start,List.mem_cons,List.not_mem_nil,or_false] at mem
    omega
  · intro mem
    simp only [RailPair.sites,EnterJ7.lowerPairs,Shadow7.sbP,start,List.flatMap_cons,List.flatMap_nil,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.append_nil] at mem
    omega
  · intro mem
    simp only [RailPair.sites,EnterJ7.upperPairs,List.mem_flatMap,List.mem_map,List.mem_range,List.mem_cons,
      List.not_mem_nil,or_false] at mem
    obtain ⟨_,⟨i,hi',rfl⟩,e⟩:=mem
    simp only [Shadow7.sbP,start] at e hi'
    omega

/-- window390: a scratch host `q ∈ [1302-t, 933]` (`t = start j`; loaders at 375 and 390) is a released B-rail wire
above the three park slots: no head piece touches it and it is no flag, pending flag or rail-pair site. -/
theorem host_geometry (j : Fin 23) (h21 : j.val≤21) {q : Nat} (lo : 1302≤q+start j) (hi : q≤933) :
    q∉support j ∧ Shadow7.firstUnchanged j q ∧ q∉EnterJ7.ports j ∧ q≠EnterJ7.flagN j ∧ q≠EnterJ7.flagF j ∧
      q≠EnterJ7.flagU j ∧ q∉EnterJ7.pending j ∧ q∉RailPair.sites (EnterJ7.lowerPairs j) ∧
      q∉RailPair.sites (EnterJ7.upperPairs j) := by
  have hj:=j.isLt
  have wb:Shadow7.wpP (start j)≤258:=by
    simp only [Shadow7.wpP,railP]; split <;> (try split) <;> omega
  have f:=EnterJ7.frame j
  have top:Shadow7.wpP (start j)+Shadow7.sbP (start j)+start j≤497:=by
    have r:railP (start j)=513-start j:=by unfold railP; rw [if_neg (by omega),if_neg (by omega)]
    have wdef:Shadow7.wpP (start j)=railP (start j)-Shadow7.sbP (start j)-16:=rfl
    omega
  simp only [Shadow7.sbP,start] at top
  simp only [start] at lo
  simp only [start] at wb
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro mem
    simp only [support,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at mem
    obtain ⟨v,⟨v1,v2⟩,e⟩:=mem
    simp only [OB5.sig_nat,OB5.sigNat,base,start] at e v1 v2
    rcases e with e|e <;> split_ifs at e with hc <;> (try rcases hc with hc|hc) <;> omega
  · unfold Shadow7.firstUnchanged
    dsimp only
    right
    show OB5.sigNat (start j+14) q∉(IntegerPacket.ports (Shadow7.shape j) 0).wires
    have key:OB5.sigNat (start j+14) q=q:=by
      unfold OB5.sigNat; simp only [start]
      split_ifs with hc <;> (try rcases hc with hc|hc) <;> omega
    rw [key]
    intro mem
    simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
      SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at mem
    omega
  · intro mem
    simp only [EnterJ7.ports,List.mem_cons,List.not_mem_nil,or_false,Shadow7.sbP,start] at mem
    omega
  · simp only [EnterJ7.flagN,Shadow7.sbP,start]; omega
  · simp only [EnterJ7.flagF,Shadow7.sbP,start]; omega
  · simp only [EnterJ7.flagU,Shadow7.sbP,start]; omega
  · intro mem
    simp only [EnterJ7.pending,Shadow7.sbP,start,List.mem_cons,List.not_mem_nil,or_false] at mem
    omega
  · intro mem
    simp only [RailPair.sites,EnterJ7.lowerPairs,Shadow7.sbP,start,List.flatMap_cons,List.flatMap_nil,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.append_nil] at mem
    omega
  · intro mem
    simp only [RailPair.sites,EnterJ7.upperPairs,List.mem_flatMap,List.mem_map,List.mem_range,List.mem_cons,
      List.not_mem_nil,or_false] at mem
    obtain ⟨_,⟨i,hi',rfl⟩,e⟩:=mem
    simp only [Shadow7.sbP,start] at e hi'
    omega

/-- window390: the placement before the block does not move a host. -/
theorem host_pull (j : Fin 23) {q : Nat} (hi : q≤933) : EnterJ7.pull j q=q := by
  have hj:=j.isLt
  show @Eq Nat (OB5.sigNat (start j-1) q) q
  simp only [OB5.sigNat,start]
  split_ifs with hc <;> (try rcases hc with hc|hc) <;> first | rfl | omega

/-- In the stock frame the wrapped port reads the carry top (`w`) or the history cell of tick `t`. -/
theorem wrap_pull (j : Fin 23) (h21 : j.val≤21) {w : Nat} (lo : Shadow7.e0P (start j)+10≤w) (hi : w≤1699)
    (wr : 2069≤w+start j) :
    (EnterJ7.pull j (3113-w)=w) ∨ (EnterJ7.pull j (3113-w)=base (1028+start j) ∧ w+start j=2069) := by
  have hj:=j.isLt
  simp only [Shadow7.e0P,Shadow7.sbP,start] at lo wr
  show (@Eq Nat (OB5.sigNat (start j-1) (3113-w)) w) ∨
    (@Eq Nat (OB5.sigNat (start j-1) (3113-w)) (1028+start j+16) ∧ w+start j=2069)
  simp only [OB5.sigNat,start]
  split_ifs with hc <;> (try rcases hc with hc|hc) <;> omega

/-- **D2's invariant, 90..390 form.** After block `j`'s head every wrapped archive scratch port is clean, for every
loader `2 ≤ j ≤ 21`. Inputs: `At{s}`'s domain and cut, the bounds, and the rails after the enter. -/
theorem scratch_wire_clean (j : Fin 23) (h2 : 2≤j.val) (h21 : j.val≤21) (d:Bool) (raw s:State) (m:List Bool)
    (x p:Nat) (good:WideReference.Bounds x p) (domain:WideReference.Domain (start j) x p raw)
    (neg far long:Bool) (Z:SkywalkRails.State) (parity:(Z.a+Z.b)%2=1)
    (active:Shadow7.onRails j 0 Z (run (Shadow7.enterP j) m s).basis)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s)) :
    ∀kk<134,
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (scratchPort j kk)=false := by
  intro kk hk
  dsimp only
  have hj:=j.isLt
  have carryTop (r:Nat) (r1:1556≤r) (r2:r≤1812):raw.basis r=false:=by
    have h:=WideReference.full_carry (start j) 0 x p (by simp only [start]; omega) good raw domain [] r r1 r2
    simpa only [WideReference.span,run] using h
  -- the head keeps a port that no head piece touches, and the cut keeps it at its stock value
  have viaCut (q:Wire) (ns:q∉support j) (nf:Shadow7.firstUnchanged j q) (ne:q∉EnterJ7.ports j) (nN:q≠EnterJ7.flagN j)
      (nF:q≠EnterJ7.flagF j) (nU:q≠EnterJ7.flagU j) (nP:q∉EnterJ7.pending j)
      (nLo:q∉RailPair.sites (EnterJ7.lowerPairs j)) (nHi:q∉RailPair.sites (EnterJ7.upperPairs j))
      (clean:raw.basis (EnterJ7.pull j q)=false) :
      (run (program j d) ((m.drop (measurementCount (Shadow7.enterP j))).drop (measurementCount (Shadow7.routed j 0 1)))
        (run (Shadow7.routed j 0 1) (m.drop (measurementCount (Shadow7.enterP j))) (run (Shadow7.enterP j) m s))).basis q=false:=by
    rw [run_preserves_outside _ _ _ _ (fun used=>ns (List.mem_toFinset.mp ((codes j (by omega) d).1 used))),
      Shadow7.first_preserves j Z parity _ _ active _ nf,
      run_preserves_outside _ _ _ _ (EnterJ7.notWire j ne)]
    have f:=cut.frame _ nN nF nU nLo nHi
    simp only [eraseSites,nP,↓reduceIte,pullState] at f
    rw [f]
    exact clean
  by_cases low:1556+kk<Shadow7.e0P (start j)
  · have on:=completed_head j (by omega) d (run (Shadow7.enterP j) m s) (m.drop (measurementCount (Shadow7.enterP j)))
      ((m.drop (measurementCount (Shadow7.enterP j))).drop (measurementCount (Shadow7.routed j 0 1))) Z parity active
    have idp:scratchPort j kk=1556+kk:=by
      show Shadow7.scratchS (start j) kk=1556+kk
      have e0:=Shadow7.scratchW_low (start j) kk low
      rw [Shadow7.scratchS_eq (start j) kk (by simp only [start]; omega)
        (by rw [e0]; simp only [Shadow7.e0P,Shadow7.sbP,start] at low ⊢; omega),e0]
    rw [idp]
    obtain ⟨c,hc,eq⟩:=List.mem_map.mp (lower_carry j low)
    rw [←eq]
    exact (regValue_zero _ _).mp on.2.2.2.1 _ hc
  · have hw:Shadow7.scratchW (start j) kk=1566+kk:=if_neg low
    have lo:Shadow7.e0P (start j)+10≤1566+kk:=by omega
    have hi:1566+kk≤1699:=by omega
    by_cases nw:1566+kk+start j<2068
    · have idp:scratchPort j kk=1566+kk:=by
        show Shadow7.scratchS (start j) kk=1566+kk
        rw [Shadow7.scratchS_eq (start j) kk (by simp only [start]; omega) (by rw [hw]; exact nw),hw]
      rw [idp]
      obtain ⟨nN,nF,nU,nP,nLo,nHi⟩:=upper_cut j lo
      apply viaCut _ (mid_support j h21 lo (by omega)) (mid_first j h21 lo (by omega)) (upper_enter j lo) nN nF nU nP nLo nHi
      rw [mid_pull j lo (by omega)]
      exact carryTop _ (by omega) (by omega)
    · have wr:2068≤1566+kk+start j:=by omega
      have tj:375≤start j ∧ start j≤390:=by simp only [start] at wr ⊢; omega
      have idp:scratchPort j kk=800+kk:=by
        show Shadow7.scratchS (start j) kk=800+kk
        rw [Shadow7.scratchS_high (start j) kk (by omega) hk (by rw [hw]; exact wr),hw]
        omega
      rw [idp]
      have q1:1302≤800+kk+start j:=by omega
      have q2:800+kk≤933:=by omega
      obtain ⟨ns,nf,ne,nN,nF,nU,nP,nLo,nHi⟩:=host_geometry j h21 q1 q2
      apply viaCut _ ns nf ne nN nF nU nP nLo nHi
      rw [host_pull j q2]
      exact WideReference.released_clear (i:=start j) (by omega) (by omega) domain (800+kk) (by omega) (by omega)

/-- The same in `ArchiveJ7.rawPorts` form (`next_window`'s `scratch` hypothesis), for every loader `2 ≤ j ≤ 21`. -/
theorem scratch_raw_clean (j : Fin 23) (h2 : 2≤j.val) (h21 : j.val≤21) (d:Bool) (raw s:State) (m:List Bool)
    (x p:Nat) (good:WideReference.Bounds x p) (domain:WideReference.Domain (start j) x p raw)
    (neg far long:Bool) (Z:SkywalkRails.State) (parity:(Z.a+Z.b)%2=1)
    (active:Shadow7.onRails j 0 Z (run (Shadow7.enterP j) m s).basis)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s)) :
    ∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false := by
  intro k hk
  dsimp only
  rw [scratch_port j (by omega) k hk]
  exact scratch_wire_clean j h2 h21 d raw s m x p good domain neg far long Z parity active cut (k.val-23) (by omega)

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}ArchiveCut.result`: the archive facts of the next pack, after the leave. -/
theorem result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (g sg : Bool) (h : Admission.Inputs j s z g sg) :
    PastFacts j (ArchiveJ7.rawPorts j) (Shadow7.sbP (start j)) z g sg
      (HighBankSum.cross (TrueMiddle.d j z)) (run (Shadow7.leaveP j) m s) := by
  let u := Admission.flags z g sg
  let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v)
  have par := RecordedParity.result j h0 (by omega) s z g sg ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z =
      LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j h0 (by omega) s z g sg ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have all := ActualHistory.result j h0 (by omega) s m z u.1 u.2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero ⟨h.nextFarSmall, h.endSmall⟩ h.bound h.far h.side g sg h.record
  exact ⟨all.1, all.2.1, all.2.2.1, all.2.2.2⟩

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.ArchiveCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.AssembleCut
open Arithmetic WideReference RailPair Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

/-- The route widths are `railP` on the window. -/
theorem route_rail (k : Nat) (hk : k ≤ 510) : W.narrowSkywalkRouteWidth k = railP k := by
  rw [WideReference.route_eq k hk]; rfl

/-- par-c1's leave box lies inside the wide reference box. -/
theorem box_of_box2 (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (q : Wire)
    (h : Shadow7.leaveBox2 (start j) q) : WideReference.Box (start j) q := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have r14 := Partial.rail14 (start j)
  unfold Shadow7.leaveBox2 at h
  unfold WideReference.Box
  rw [route_rail (start j) (by omega), route_rail (start j+14) (by omega)]
  simp only [Wire] at *
  omega

/-- dadon's `Leave{s}AssembleCut.result`, generic. The frame is split on the wide box: inside it the leftovers
(`left`), the carry scratch (`zs`/`clear` against the origin's clean carry, `carry`) and the next rails
(`low`/`high`); outside it the stock exterior (`ext`) and the older moved history (`mirror`, empty while
`start j ≤ 257`). -/
theorem result (j k : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (hk0 : 1 ≤ k.val) (hk1 : k.val ≤ 21)
    (hs:start k=start j+15) (s o : State) (neg far long : Bool)
    (phase : s.phase=o.phase) (sign : s.basis (EnterJ7.flagN k)=neg) (mode : s.basis (EnterJ7.flagF k)=far)
    (side : s.basis (EnterJ7.flagU k)=long)
    (low : ∀i:Fin (Shadow7.sbP (start k)+19), s.basis (start k+16+i.val)=o.basis (start k+16+i.val) ∧
      s.basis (786+i.val)=o.basis (786+i.val))
    (high : ∀i:Fin (Shadow7.wpP (start k)-3), s.basis (start k+Shadow7.sbP (start k)+35+i.val)=false ∧
      s.basis (Shadow7.sbP (start k)+805+i.val)=(if o.basis (EnterJ7.gate k) then o.basis (Shadow7.sbP (start k)+805+i.val)
        else o.basis (start k+Shadow7.sbP (start k)+35+i.val)))
    (ext : ∀q:Wire,¬WideReference.Box (start j) q → ¬leftovers j q → ¬(2070≤(q:Nat)+start j ∧ (q:Nat)≤1812) →
      s.basis q=o.basis q)
    (mirror : ∀q:Nat,2070≤q+start j → q≤1812 → s.basis q=o.basis q)
    (left : ∀q,leftovers j q → s.basis q=o.basis q)
    (zs : List Wire) (clear : ∀q∈zs,s.basis q=false)
    (zcover : ∀q:Nat,1556≤q → q≤1812 → WideReference.Box (start j) q → ¬leftovers j q → q∉EnterJ7.pending k →
      q≠EnterJ7.flagN k → q≠EnterJ7.flagF k → q≠EnterJ7.flagU k → q∈zs)
    (rails : ∀q:Nat,WideReference.Box (start j) q → ¬leftovers j q → q<1556 →
      (start k+16≤q ∧ q<start k+Shadow7.sbP (start k)+32+Shadow7.wpP (start k)) ∨ (786≤q ∧ q<Shadow7.sbP (start k)+802+Shadow7.wpP (start k)))
    (carry : ∀q:Nat,1556≤q → q+start j≤2054 → q≤1812 → o.basis q=false) :
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k) neg far long o (eraseSites (EnterJ7.pending k) s) := by
  have f:=EnterJ7.frame k
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  have rj := Shadow7.rail_win w1 w2
  have away (q:Wire) (small:q<1556) : (eraseSites (EnterJ7.pending k) s).basis q=s.basis q := by
    have no:q∉EnterJ7.pending k:=by
      simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false]; simp only [Wire] at *; omega
    simp [eraseSites,no]
  have flagOff (q:Wire) (h:q=Shadow7.sbP (start k)+1579 ∨ q=Shadow7.sbP (start k)+1577 ∨ q=Shadow7.sbP (start k)+1578) :
      (eraseSites (EnterJ7.pending k) s).basis q=s.basis q := by
    have no:q∉EnterJ7.pending k:=by
      simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false]; simp only [Wire] at *; omega
    simp [eraseSites,no]
  refine ⟨phase,?_,?_,?_,?_,?_,?_⟩
  · show (eraseSites (EnterJ7.pending k) s).basis (Shadow7.sbP (start k) + 1579) = neg
    rw [flagOff _ (Or.inl rfl)]; exact sign
  · show (eraseSites (EnterJ7.pending k) s).basis (Shadow7.sbP (start k) + 1577) = far
    rw [flagOff _ (Or.inr (Or.inl rfl))]; exact mode
  · show (eraseSites (EnterJ7.pending k) s).basis (Shadow7.sbP (start k) + 1578) = long
    rw [flagOff _ (Or.inr (Or.inr rfl))]; exact side
  · intro pair mem
    simp only [EnterJ7.lowerPairs,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl <;> dsimp only <;>
    · rw [away _ (by simp only [Wire] at *; omega),away _ (by simp only [Wire] at *; omega)]
      first
      | exact (show _ from by have l:=low ⟨Shadow7.sbP (start k)+16,by omega⟩; simp only at l
                              rw [show start k+16+(Shadow7.sbP (start k)+16)=start k+Shadow7.sbP (start k)+32 by omega,
                                show 786+(Shadow7.sbP (start k)+16)=Shadow7.sbP (start k)+802 by omega] at l; exact l)
      | exact (show _ from by have l:=low ⟨Shadow7.sbP (start k)+17,by omega⟩; simp only at l
                              rw [show start k+16+(Shadow7.sbP (start k)+17)=start k+Shadow7.sbP (start k)+33 by omega,
                                show 786+(Shadow7.sbP (start k)+17)=Shadow7.sbP (start k)+803 by omega] at l; exact l)
      | exact (show _ from by have l:=low ⟨Shadow7.sbP (start k)+18,by omega⟩; simp only at l
                              rw [show start k+16+(Shadow7.sbP (start k)+18)=start k+Shadow7.sbP (start k)+34 by omega,
                                show 786+(Shadow7.sbP (start k)+18)=Shadow7.sbP (start k)+804 by omega] at l; exact l)
  · intro pair mem
    simp only [EnterJ7.upperPairs,List.mem_map,List.mem_range] at mem
    obtain ⟨i,hi,rfl⟩:=mem
    dsimp only
    rw [away _ (by simp only [Wire] at *; omega),away _ (by simp only [Wire] at *; omega)]
    exact high ⟨i,hi⟩
  · intro q notN notF notU notLo notHi
    by_cases pend:q∈EnterJ7.pending k
    · have r:1556≤(q:Nat) ∧ (q:Nat)+start j≤2054 ∧ (q:Nat)≤1812:=by
        simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false] at pend
        rw [hs] at pend
        simp only [Wire] at *; omega
      simp [eraseSites,pend,carry q r.1 r.2.1 r.2.2]
    simp only [eraseSites,if_neg pend]
    by_cases lf:leftovers j q
    · exact left q lf
    have lf' := lf
    unfold leftovers ReleasedOrigin.releasedSite at lf'
    simp only [not_or, not_and] at lf'
    by_cases inBox:WideReference.Box (start j) q
    · have inBox' := inBox
      unfold WideReference.Box at inBox'
      rw [route_rail (start j) (by omega), route_rail (start j+14) (by omega)] at inBox'
      have r14 := Partial.rail14 (start j)
      by_cases hc:1556≤(q:Nat)
      · have top:(q:Nat)+start j≤2054 ∧ (q:Nat)≤1812:=by
          simp only [Wire] at *
          rcases inBox' with h|h|h|h <;> omega
        rw [carry q hc top.1 top.2]
        exact clear q (zcover q hc top.2 inBox lf pend notN notF notU)
      · rcases rails q inBox lf (by simp only [Wire] at *; omega) with ⟨a1,a2⟩|⟨b1,b2⟩
        · by_cases lo:(q:Nat)<start k+Shadow7.sbP (start k)+35
          · have l:=(low ⟨q-(start k+16),by simp only [Wire] at *; omega⟩).1; simp only at l
            rw [show start k+16+(q-(start k+16))=(q:Nat) by simp only [Wire] at *; omega] at l; exact l
          · exfalso; apply notHi
            simp only [RailPair.sites,EnterJ7.upperPairs,List.mem_flatMap,List.mem_map,List.mem_range]
            exact ⟨_,⟨q-(start k+Shadow7.sbP (start k)+35),by simp only [Wire] at *; omega,rfl⟩,
              by simp only [List.mem_cons]; left; simp only [Wire] at *; omega⟩
        · by_cases lo:(q:Nat)<Shadow7.sbP (start k)+805
          · have l:=(low ⟨q-786,by simp only [Wire] at *; omega⟩).2; simp only at l
            rw [show 786+(q-786)=(q:Nat) by simp only [Wire] at *; omega] at l; exact l
          · exfalso; apply notHi
            simp only [RailPair.sites,EnterJ7.upperPairs,List.mem_flatMap,List.mem_map,List.mem_range]
            exact ⟨_,⟨q-(Shadow7.sbP (start k)+805),by simp only [Wire] at *; omega,rfl⟩,
              by simp only [List.mem_cons,List.mem_singleton]; right; simp only [Wire] at *; omega⟩
    · by_cases mi:2070≤(q:Nat)+start j ∧ (q:Nat)≤1812
      · exact mirror q mi.1 mi.2
      · exact ext q inBox lf mi

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.AssembleCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl
private theorem both (P Q:Prop) [Decidable P] [Decidable Q] : (decide P && decide Q)=decide (P ∧ Q) := by
  by_cases a:P <;> by_cases b:Q <;> simp [a,b]

/-- The rail of a window block narrows by at most one wire per tick, never widens, and when it narrows over the
block it narrows at the block's last tick. -/
theorem rail_step (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) :
    railP (start j+14) ≤ railP (start j+15) + 1 ∧ railP (start j+14) ≤ railP (start j) ∧
    railP (start j+15) ≤ railP (start j) ∧ start j + 30 + railP (start j+15) ≤ 529 ∧
    (railP (start j+15) < railP (start j) → railP (start j+14) = railP (start j+15) + 1 ∧
      start j + 31 + railP (start j+15) ≤ 529) := by
  have e : start j = 75 + 15 * j.val := rfl
  rw [e]
  unfold railP; refine ⟨?_,?_,?_,?_,?_⟩ <;> (try intro) <;> split_ifs at * <;> omega

/-- dadon's `Leave{s}CertifiedCut.result`, generic: the leave's output is the packed cut of the next block `k`
(`start k = start j + 15`). The window side comes in as `ext` (the stock exterior of the wide box), `mirror`
(the older moved history), `upper` (the A rail above the join, dadon's `upper`), `band` (the sig band
`[1301, s+1058]`, empty before 243) and `quiet` (the raw sites). -/
theorem result (j k : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 20) (hk0 : 1 ≤ k.val) (hk1 : k.val ≤ 21)
    (hs : start k = start j + 15)
    (x p : Nat) (good : Bounds x p) (raw s : State) (m : List Bool) (g0 s0 : Bool)
    (h : Admission.Inputs j s (unsigned (start j) x p) g0 s0)
    (dom : Domain (start j) x p raw)
    (input : InputAt (start j) (encode g0 s0 (unsigned (start j) x p).u (unsigned (start j) x p).v) raw)
    (phase : s.phase = (origin (start j) raw s).phase)
    (ext : ∀ q:Wire, ¬WideReference.Box (start j) q → ¬AssembleCut.leftovers j q →
      ¬(2070≤(q:Nat)+start j ∧ (q:Nat)≤1812) → s.basis q = (origin (start j) raw s).basis q)
    (mirror : ∀ q:Nat, 2070≤q+start j → q≤1812 → s.basis q = (origin (start j) raw s).basis q)
    (upper : ∀ q:Nat, Shadow7.a0P (start j)+18 ≤ q → q ≤ min (start j+30+railP (start j+14)) 529 → s.basis q = false)
    (band : ∀ q:Nat, 1301 ≤ q → q ≤ 1058+start j → s.basis q = false)
    (hosts : ∀ q:Nat, 369 ≤ start j → 1302 ≤ q+start j → q ≤ 933 → s.basis q = false)
    (quiet : ∀ q ∈ CoreCheckpoint.rawSites j, s.basis q = false) :
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k) (PortalValues.negative (Admission.flags (unsigned (start j) x p) g0 s0).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k)) ≤ (unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) (endRaw (start j) raw s)) (eraseSites (EnterJ7.pending k) (run (Shadow7.leaveP j) m s)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  obtain ⟨st1, st2, st3, st4, st5⟩ := rail_step j h0 (by omega)
  have r14 := Partial.rail14 (start j)
  let z := unsigned (start j) x p
  let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have endpointState : SkywalkNat.step^[15] z = unsigned (start k) x p := by
    show SkywalkNat.step^[15] (SkywalkNat.step^[start j] (SkywalkNat.init x p)) =
      SkywalkNat.step^[start k] (SkywalkNat.init x p)
    rw [hs, Nat.add_comm, Function.iterate_add_apply]
  have par := RecordedParity.result j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start j)) z =
      LeaveSelector.farMode (s.basis (Shadow7.e0P (start j) + 3)) (s.basis (Shadow7.e0P (start j) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := RecordedEvents.result j h0 (by omega) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have bits := EndWords.result j h0 (by omega) s m z
    (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.bound xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
    ev.1 h.far h.side
  have whole := Whole.result j h0 (by omega) s m z
    (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.bound xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
    ev.1 h.far h.side
  have carried := StockWindowTicket.stepInput_gen_shadow7 (start j) (Shadow7.sbP (start j)) x p (by omega) (by omega) good raw s
    g0 s0 dom input h.farSmall
  have nextInput : SkywalkIntegerInput (WideWords.L j)
      (SkywalkRails.encode (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 (SkywalkNat.step^[15] z).u
        (SkywalkNat.step^[15] z).v).a
      (SkywalkRails.encode (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 (SkywalkNat.step^[15] z).u
        (SkywalkNat.step^[15] z).v).b (Admission.flags z g0 s0).1 (endRaw (start j) raw s).basis := by
    have c2 := carried.2
    unfold InputAt StockWindowTicket.signedAt at c2
    rw [flagEq] at c2
    have eA : SkywalkNat.step^[15] z = unsigned (start j+15) x p := hs ▸ endpointState
    rw [eA]
    exact c2
  have highZero : ∀ q : Nat, Shadow7.a0P (start j) + 18 ≤ q → q ≤ (start j) + 30 + railP ((start j) + 15) → s.basis q = false :=
    fun q lo hi => upper q lo (Nat.le_min.mpr ⟨by omega, by omega⟩)
  have rails := BoundaryRails.result j h0 (by omega) s m z
    (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.bound xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
    ev.1 h.far h.side highZero (endRaw (start j) raw s) nextInput
  have eo : pullState (OB5.sig (start j + 14)) (endRaw (start j) raw s) = origin (start j) raw s :=
    endpoint (start j) (by omega) raw s
  simp only [eo] at rails
  have kept := PreservedRecords.result j h0 (by omega) s m bits.2.2.2.1
  have clear := BoundaryClean.result j h0 (by omega) s m z
    (Admission.flags z g0 s0).1 (Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩ h.ready h.fresh h.scratch h.temp h.odd h.room
    h.clean h.padding h.bank h.zero par mode ev.2 ⟨h.nextFarSmall, h.endSmall⟩ h.bound xs (SkywalkTrace.trace_length _ _)
    (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd) (LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd)
    ev.1 h.far h.side quiet (terminal_fit j h0 (by omega) x p good)
  have pre : ∀ q : Wire, (railP ((start j) + 15) < railP (start j) ∧ q = (start j) + 31 + railP ((start j) + 15)) ∨
      (1301 ≤ q ∧ q ≤ 1058 + (start j)) ∨ (369 ≤ start j ∧ 1302 ≤ q + start j ∧ q ≤ 933) → s.basis q = false := by
    intro q hq
    rcases hq with ⟨sh, rfl⟩ | ⟨lo, hi⟩ | ⟨t369, lo, hi⟩
    · have st := st5 sh
      exact upper _ (by omega) (Nat.le_min.mpr ⟨by omega, by omega⟩)
    · exact band q lo hi
    · exact hosts q t369 lo hi
  have rel := ReleasedActual.agree j h0 (by omega) x p good raw s dom m pre clear
  have left := FrameHistory.result j h0 (by omega) x p good raw s m g0 s0 dom input h.record kept rel
  have pk : pullState (EnterJ7.pull k) (endRaw (start j) raw s) = origin (start j) raw s := by
    simp only [EnterJ7.pull]
    rw [hs, show start j + 15 - 1 = start j + 14 by omega]
    exact eo
  rw [pk]
  refine AssembleCut.result j k h0 (by omega) hk0 (by omega) hs (run (Shadow7.leaveP j) m s) (origin (start j) raw s) _ _ _
    (whole.1.trans phase) ?_ ?_ ?_ ?_ ?_ ?_ ?_ left (BoundaryClean.zeros j) clear ?_ ?_ ?_
  · -- sign
    have e : EnterJ7.flagN k = Shadow7.e0P (start j + 15) + 5 := by
      show Shadow7.sbP (start k) + 1579 = 1574 + Shadow7.sbP (start j + 15) + 5; rw [hs]; omega
    rw [e, ← endpointState]; exact bits.2.2.1
  · -- mode
    have e : EnterJ7.flagF k = Shadow7.e0P (start j + 15) + 3 := by
      show Shadow7.sbP (start k) + 1577 = 1574 + Shadow7.sbP (start j + 15) + 3; rw [hs]; omega
    rw [e, ← endpointState, hs]; exact bits.1
  · -- orientation
    have e : EnterJ7.flagU k = Shadow7.e0P (start j + 15) + 4 := by
      show Shadow7.sbP (start k) + 1578 = 1574 + Shadow7.sbP (start j + 15) + 4; rw [hs]; omega
    rw [e, ← endpointState, hs]; exact bits.2.1.trans (both _ _)
  · -- low rails
    intro i
    have hi := i.isLt
    have e1 : start k + 16 + i.val = start j + 31 + i.val := by omega
    have esb : Shadow7.sbP (start k) = Shadow7.sbP (start j + 15) := by rw [hs]
    rw [e1]
    exact rails.1 ⟨i.val, by unfold Shadow7.lowsP; omega⟩
  · -- high rails
    intro i
    have hi := i.isLt
    have esb : Shadow7.sbP (start k) = Shadow7.sbP (start j + 15) := by rw [hs]
    have ewp : Shadow7.wpP (start k) = Shadow7.wpP (start j + 15) := by rw [hs]
    have r := rails.2 ⟨i.val, by unfold Shadow7.lowsP; omega⟩
    have e1 : start k + Shadow7.sbP (start k) + 35 + i.val = Shadow7.a0P (start j) + Shadow7.lowsP (start j) + i.val := by
      unfold Shadow7.a0P Shadow7.lowsP; omega
    have e2 : Shadow7.sbP (start k) + 805 + i.val = Shadow7.b0P (start j) + Shadow7.lowsP (start j) + i.val := by
      unfold Shadow7.b0P Shadow7.lowsP; omega
    have e3 : EnterJ7.gate k = start j + 30 := by simp only [EnterJ7.gate]; rw [hs]
    rw [e1, e2, e3]
    exact r
  · -- exterior
    intro q nb nl nm
    rw [leave_keeps j h0 (by omega) q (fun hb => nb (AssembleCut.box_of_box2 j h0 (by omega) q hb)) m s]
    exact ext q nb nl nm
  · -- the older moved history
    intro q lo hi
    rw [leave_keeps j h0 (by omega) q (by unfold Shadow7.leaveBox2; omega) m s]
    exact mirror q lo hi
  · -- zcover
    intro q lo hi inBox lf pend nN nF nU
    unfold WideReference.Box at inBox
    rw [AssembleCut.route_rail (start j) (by omega), AssembleCut.route_rail (start j+14) (by omega)] at inBox
    unfold AssembleCut.leftovers ReleasedOrigin.releasedSite at lf
    simp only [EnterJ7.pending, EnterJ7.flagN, EnterJ7.flagF, EnterJ7.flagU, List.mem_cons, List.not_mem_nil,
      or_false] at pend nN nF nU
    rw [hs] at pend nN nF nU
    simp only [BoundaryClean.zeros, List.mem_append, List.mem_range'_1]
    simp only [Wire] at *
    omega
  · -- rails
    intro q inBox lf lo
    unfold WideReference.Box at inBox
    rw [AssembleCut.route_rail (start j) (by omega), AssembleCut.route_rail (start j+14) (by omega)] at inBox
    unfold AssembleCut.leftovers ReleasedOrigin.releasedSite at lf
    rw [hs]
    unfold Shadow7.wpP
    simp only [Wire] at *
    omega
  · -- carry
    intro q lo hs' hi
    exact carry_origin (i := start j) (upper := min 1812 (2054 - start j)) (by omega) (by omega) good raw s dom
      (fun q' l u => sig_carry j h0 (by omega) q' l (by omega)) q lo (by omega)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.CertifiedCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}BodyCut.result`, generic for the interior blocks up to 255 (the older moved history is
empty there). `band` is the sig band `[1301, s+1058]` before the leave (empty before 243). -/
theorem result (j k : Fin 23) (hk : k.val=j.val+1) (h2 : 2≤j.val) (h12 : j.val≤12)
    (hne : start j≠WideReference.firstBlock) (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (a b m:List Bool)
    (neg far long g0 s0:Bool) (domain:Domain (start j) x p raw)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:InputAt (start j) (encode g0 s0 (unsigned (start j) x p).u (unsigned (start j) x p).v) raw)
    (h:Admission.Inputs j (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s))
      (unsigned (start j) x p) g0 s0)
    (phase:(run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).phase=s.phase)
    (popped:(run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis (Shadow7.e0P (start j)+8)=false)
    (tail:∀q∈NativeJ7.tailTemps j,(run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false)
    (band:∀q:Nat,1301≤q → q≤1058+start j →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false) :
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k) (PortalValues.negative (Admission.flags (unsigned (start j) x p) g0 s0).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k)) ≤ (unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k)
        (endRaw (start j) raw (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s))))
      (eraseSites (EnterJ7.pending k)
        (run (Shadow7.leaveP j) m (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)))) := by
  obtain ⟨w1, w2⟩ := start_win j (by omega) (by omega)
  have hs : start k = start j + 15 := by simp only [StairPacket.start]; omega
  have top : start j ≤ 255 := by simp only [StairPacket.start]; omega
  have ag : ∀ q : Wire, ¬WideReference.Box (start j) q → ¬AssembleCut.leftovers j q →
      ¬(2070≤(q:Nat)+start j ∧ (q:Nat)≤1812) →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q =
        (origin (start j) raw (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s))).basis q := by
    intro q nb nl nm
    unfold AssembleCut.leftovers ReleasedOrigin.releasedSite at nl
    simp only [not_or, not_and] at nl
    exact NativeJ7.agree_origin j h2 (by omega) hne d raw s a b neg far long cut q nb
      (by simp only [Wire] at *; omega) (by simp only [Wire] at *; omega) (by simp only [Wire] at *; omega)
  have up : ∀ q:Nat, Shadow7.a0P (start j)+18 ≤ q → q ≤ min (start j+30+railP (start j+14)) 529 →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q = false :=
    fun q lo hi => NativeJ7.upper_clear j (by omega) (by omega) d raw s x p domain a b neg far long cut q
      (by unfold Shadow7.a0P at lo; omega) hi
  generalize hv : run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s) = v at h phase popped tail band ag up ⊢
  have quiet : ∀ q ∈ CoreCheckpoint.rawSites j, v.basis q = false := by
    intro q hq
    simp only [CoreCheckpoint.rawSites, List.mem_append, List.mem_range'_1] at hq
    rcases hq with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact native_carryJ j (by omega) (by omega) _ v h.ready q (by simp only [Wire] at *; omega)
        (by simp only [Wire] at *; omega)
    · by_cases e8 : (q:Nat) = Shadow7.e0P (start j) + 8
      · have e8' : q = Shadow7.e0P (start j) + 8 := e8
        rw [e8']; exact popped
      · exact tail q (by simp only [NativeJ7.tailTemps, List.mem_range'_1]; simp only [Wire] at *; omega)
  have ph : v.phase = (origin (start j) raw v).phase :=
    phase.trans (cut.phase.trans (origin_phase (start j) x p (by omega) good raw v domain).symm)
  exact CertifiedCut.result j k (by omega) (by omega) (by omega) (by omega) hs x p good raw v m g0 s0 h domain input ph ag
    (fun q lo hi => absurd hi (by omega)) up band (fun q t369 _ _ => absurd t369 (by omega)) quiet

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.BodyCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `NativePack{s}.stock_endpoint`, generic (interior blocks `2 ≤ j ≤ 12`, next block `k = j+1`): the
leave's output is the next block's packed cut, and the next pack's archive facts hold. -/
theorem stock_endpoint (j k : Fin 23) (hk : k.val=j.val+1) (h2 : 2≤j.val) (h12 : j.val≤12)
    (hne : start j≠WideReference.firstBlock) (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State)
    (m n:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (pg ps cross:Bool)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) (unsigned (start (prev j)) x p) pg ps cross s)
    (band : ∀q:Nat,1301≤q → q≤1058+start j → (run (nextWindow j d) m s).basis q=false) :
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k)
      (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start j) x p) G S).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) (endRaw (start j) raw (run (nextWindow j d) m s)))
      (eraseSites (EnterJ7.pending k) (run (Shadow7.leaveP j) n (run (nextWindow j d) m s))) ∧
    PastFacts j (ArchiveJ7.rawPorts j) (Shadow7.sbP (start j)) (unsigned (start j) x p) G S
      (HighBankSum.cross (LeaveJ7.TrueMiddle.d j (unsigned (start j) x p)))
      (run (Shadow7.leaveP j) n (run (nextWindow j d) m s)) := by
  obtain ⟨w1, w2⟩ := start_win j (by omega) (by omega)
  have numbers:=LeaveJ7.Admission.actualNumbers j (by omega) (by omega) x p good
  have old:=LeaveJ7.Admission.actualNumbers (prev j) (by simp only [prev]; omega) (by simp only [prev]; omega) x p good
  have hist:=pulled_history j rfl domain
  have native:=from_domain j h2 (by omega) d x p good raw s m domain G S cut input scratch pg ps cross prior
  obtain ⟨_,_,_,_,tags⟩:=real_receipt j (by omega) (by omega) d raw s m (unsigned (start j) x p) G S numbers.odd
    numbers.farSmall cut input hist scratch (unsigned (start (prev j)) x p) pg ps cross old.odd old.farSmall prior
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) (unsigned (start j) x p) numbers.farSmall numbers.odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s (unsigned (start j) x p) G S m numbers.farSmall cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j (by omega) (by omega) d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity
    ready.2.1 scratch (unsigned (start (prev j)) x p) pg ps cross old.odd old.farSmall prior
  have final:=archive_result j (by omega) (by omega) d row limit _ _ frame
  have tail:=tail_clean j (by omega) (by omega) d x p raw s domain m tape _ _ _ cut row final
  have runEq : run (nextWindow j d) m s = run (Shadow7.body j (withArchive j d)) tape pre := by
    simp only [nextWindow, window, run_append, run_take, pre, tape]
  have gg (g s:Bool) (u v:Int) : (encode g s u v).g=g:=by cases g <;> rfl
  have orig:InputAt (start j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v) raw:=by
    unfold InputAt;rw [gg];exact input
  have h := native.1
  have ph := native.2.1
  refine ⟨?_, LeaveJ7.ArchiveCut.result j (by omega) (by omega) (run (nextWindow j d) m s) n (unsigned (start j) x p) G S h⟩
  have bit : (run (nextWindow j d) m s).basis (Shadow7.e0P (start j)+8) = false := by
    have t2 := tags ⟨2, by omega⟩
    have e : Shadow7.e0P (start j) + 8 = Shadow7.sbP (start j)+1580+(⟨2, by omega⟩:Fin 3).val := by simp only [Shadow7.e0P]; omega
    rw [e]; exact t2
  rw [runEq] at h ph band bit ⊢
  exact LeaveJ7.BodyCut.result j k hk h2 h12 hne d x p good raw s m tape n _ _ _ G S domain cut orig h ph bit tail band

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-- dadon's `At240`/`At255` for any block `k` (the saved keys are `window_strong`'s `Key`). -/
structure AtJ (k : Fin 23) (d:Bool) (x p:Nat) (raw s:State) (g sg pg ps:Bool) : Prop where
  domain : Domain (start k) x p raw
  input : InputAt (start k) (signedAt (start k) x p g sg) raw
  cut : PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k) (flagNeg (start k) x p sg)
      (decide (farAt (Shadow7.sbP (start k)) (start k) x p))
      (decide (farAt (Shadow7.sbP (start k)) (start k) x p ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) raw) (eraseSites (EnterJ7.pending k) s)
  facts : PastFacts (NativeJ7.prev k) (ArchiveJ7.rawPorts (NativeJ7.prev k)) (Shadow7.sbP (start (NativeJ7.prev k)))
      (unsigned (start (NativeJ7.prev k)) x p) pg ps
      (HighBankSum.cross (LeaveJ7.TrueMiddle.d (NativeJ7.prev k) (unsigned (start (NativeJ7.prev k)) x p))) s
  pastCanonical : signedAt (start (NativeJ7.prev k)) x p pg ps=WideReference.canonical (start (NativeJ7.prev k)) x p

/-- The hand-off at tick `t` (a block start). -/
def ReadyW (d:Bool) (x p:Nat) (t:Nat) (s:State) : Prop :=
  ∃ k : Fin 23, start k=t ∧ ∃ raw g sg pg ps, AtJ k d x p raw s g sg pg ps

/-- Block `i`'s saved archive key (dadon's `Saved (start i) x p (codePorts) d`). -/
def KeyW (d:Bool) (x p:Nat) (i:Fin 23) (s:State) : Prop :=
  ∃row<63145, Chronology (start i) x p row ∧ Kept (ArchiveJ7.codePorts i) d row s

/-- The window's precondition: the stock walk at tick 120 (dadon's `Before` at 225). -/
def BeforeW (d:Bool) (x p:Nat) (s:State) := ∃raw:State,
  Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis ∧ s=pullState (OB5.sig (start WindowParams.first-1)) raw

/-- par-c2's archive-scratch hypothesis of `NativeJ7.from_domain(_matched)`. -/
def ScratchAt (j : Fin 23) (d:Bool) (m:List Bool) (s:State) : Prop :=
  ∀k:Fin 157,23≤k.val →
    let pre:=run (Shadow7.enterP j) m s
    let tape:=m.drop (measurementCount (Shadow7.enterP j))
    (run (NativeJ7.program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1)))
      (run (Shadow7.routed j 0 1) tape pre)).basis
      (ArchiveJ7.rawPorts (NativeJ7.prev j) k)=false

-- ===== Leaves (statements fixed here; each becomes a theorem) =====

/-- L2: the archive scratch of block `j` is clean after its pack (par-d2's ScratchWrap). -/
abbrev ScratchSpec : Prop :=
  ∀ (j : Fin 23), 2≤j.val → j.val≤20 → ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool)
    (m:List Bool), AtJ j d x p raw s g sg pg ps → ScratchAt j d m s

/-- L3: the (move) leave undoes (GlueB's `Admission.Inputs.roundtrip`, on the window's move leave). -/
abbrev RoundtripSpec : Prop :=
  ∀ (j : Fin 23), 1≤j.val → j.val≤20 → ∀ (v:State) (z:SkywalkNat.State) (G S:Bool),
    LeaveJ7.Admission.Inputs j v z G S → ∀ m n:List Bool, run (Shadow7.leaveMoveInvP j) n (run (Shadow7.leaveMoveP j) m v)=v

/-- The block after the window's first block. -/
def firstNext : Fin 23 := ⟨WindowParams.first.val+1,by decide⟩

/-- L9: the first block's endpoint at `start WindowParams.first` (dadon's `NativePack225.stock_endpoint`, first form). -/
abbrev FirstSpec : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m n:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis),
    ∃g s:Bool,
      InputAt (start WindowParams.first) (encode g s (unsigned (start WindowParams.first) x p).u (unsigned (start WindowParams.first) x p).v) raw ∧
      LeaveJ7.Admission.Inputs WindowParams.first
        (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))
        (unsigned (start WindowParams.first) x p) g s ∧
      PackedCut (EnterJ7.lowerPairs firstNext) (EnterJ7.upperPairs firstNext) (EnterJ7.gate firstNext)
        (EnterJ7.flagN firstNext) (EnterJ7.flagF firstNext) (EnterJ7.flagU firstNext)
        (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start WindowParams.first) x p) g s).2 (unsigned (start WindowParams.first+15) x p).u)
        (decide (Shadow.far (Shadow7.sbP (start WindowParams.first+15)) 15 (unsigned (start WindowParams.first+15) x p)))
        (decide (Shadow.far (Shadow7.sbP (start WindowParams.first+15)) 15 (unsigned (start WindowParams.first+15) x p) ∧ 2^(Shadow7.sbP (start WindowParams.first+15))≤(unsigned (start WindowParams.first+15) x p).u))
        (pullState (EnterJ7.pull firstNext)
          (endRaw (start WindowParams.first) raw (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))))
        (eraseSites (EnterJ7.pending firstNext) (run (Shadow7.leaveP WindowParams.first) n
          (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)))) ∧
      PastFacts WindowParams.first (ArchiveJ7.rawPorts WindowParams.first) (Shadow7.sbP (start WindowParams.first)) (unsigned (start WindowParams.first) x p) g s
        (HighBankSum.cross (LeaveJ7.TrueMiddle.d WindowParams.first (unsigned (start WindowParams.first) x p)))
        (run (Shadow7.leaveP WindowParams.first) n
          (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)))

/-- L10: the first window (portal 120, enter, pack) keeps the phase and undoes (dadon's `NativePack225.first_window`). -/
abbrev FirstBackSpec : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis),
    (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)).phase=raw.phase ∧
    ∀k, run (NativeFirstJ7.enteredUnwind WindowParams.first d ++ Shadow7.portalInvP (start WindowParams.first)) k
      (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))=
      pullState (OB5.sig (start WindowParams.first-1)) raw

-- ===== Program bridges =====

theorem prev_of (i k : Fin 23) (hk : k.val=i.val+1) : NativeJ7.prev k=i := Fin.ext (by simp only [NativeJ7.prev]; omega)

theorem start_succ (i k : Fin 23) (hk : k.val=i.val+1) : start k=start i+15 := by simp only [StairPacket.start]; omega

theorem next_eq (d:Bool) (i k : Fin 23) (hk : k.val=i.val+1) :
    (nextF Shadow7.params d i k).flatten=NativeJ7.nextWindow k d++Shadow7.leaveMoveP k := by
  have e:=prev_of i k hk
  subst e
  simp only [nextF,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeJ7.nextWindow,NativeJ7.window,Shadow7.body,NativeJ7.withArchive,NativeJ7.program,List.append_assoc]

theorem nextR_eq (d:Bool) (i k : Fin 23) (hk : k.val=i.val+1) :
    (nextR Shadow7.params d i k).flatten=Shadow7.leaveMoveInvP k++NativeJ7.nextUnwind k d := by
  have e:=prev_of i k hk
  subst e
  simp only [nextR,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeJ7.nextUnwind,NativeJ7.unwind,Shadow7.unbody,NativeJ7.fromArchive,NativeJ7.reverse,List.append_assoc]

theorem first_eq (d:Bool) :
    (Shadow7.params.portal (start WindowParams.first) :: firstF Shadow7.params d WindowParams.first).flatten=
      (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d)++Shadow7.leaveMoveP WindowParams.first := by
  simp only [firstF,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeFirstJ7.enteredWindow,NativeFirstJ7.window,Shadow7.body,NativeFirstJ7.program,List.append_assoc]

theorem firstR_eq (d:Bool) :
    (firstR Shadow7.params d WindowParams.first++[Shadow7.params.portalInv (start WindowParams.first)]).flatten=
      Shadow7.leaveMoveInvP WindowParams.first++(NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) := by
  simp only [firstR,Shadow7.params,ofParts,List.cons_append,List.nil_append,List.flatten_cons,List.flatten_nil,
    List.append_nil,NativeFirstJ7.enteredUnwind,NativeFirstJ7.unwind,Shadow7.unbody,NativeFirstJ7.reverse,List.append_assoc]


/-- The move leave runs like the reference leave after block `k`'s head, from any hand-off state. -/
theorem sameAt (L2 : ScratchSpec) (k : Fin 23) (h2 : 2≤k.val) (h19 : k.val≤20) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (g sg pg ps:Bool) (m:List Bool) (pre:AtJ k d x p raw s g sg pg ps) (n:List Bool) :
    run (Shadow7.leaveMoveP k) n (run (NativeJ7.nextWindow k d) m s)=run (Shadow7.leaveP k) n (run (NativeJ7.nextWindow k d) m s) := by
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=L2 k h2 (by omega) d x p good raw s g sg pg ps m pre
  have native:=NativeJ7.from_domain_matched k h2 (by omega) d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  exact LeaveJ7.Admission.Inputs.sameMove (by omega) (by omega) native.1 n

/-- The same for the first block. -/
theorem firstSame (L1 : FirstSpec) (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m n:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis) :
    run (Shadow7.leaveMoveP WindowParams.first) n
      (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))=
    run (Shadow7.leaveP WindowParams.first) n
      (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)) := by
  obtain ⟨g,sg,input,hin,cut,facts⟩:=L1 d x p good raw m n stage
  exact LeaveJ7.Admission.Inputs.sameMove (by decide) (by decide) hin n

-- ===== The three step forms =====

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

/-- `OB5.sig i` fixes the wires below the moved band. -/
theorem fix_low (i q : Nat) (h : q < 1301) (h2 : q + i < 2069) : OB5.sig i q = q :=
  WideReference.sig_fixed (by intro h'; simp only [Wire] at *; omega) (by intro h'; simp only [Wire] at *; omega)

/-- The saved key cells of block `i` are its archive's first 16 code ports. -/
theorem bank_cells (i : Fin 23) (q : Wire) (h : q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i)) :
    q ∈ cellsRestoreP (start i + 15) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
  have hl : (cellsRestoreP (start i + 15)).length = 16 := by simp [cellsRestoreP]
  have hj : j.val < (cellsRestoreP (start i + 15)).length := by rw [hl]; exact j.isLt
  simp only [ArchiveJ7.codePorts, ArchiveJ7.code_split, List.append_assoc]
  rw [List.getD_append _ _ _ _ hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem _

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

/-- The sig band `[1301, s+1058]` is clean after block `j`'s head: empty before 243; at 255 the wires
`1301..1313`, which the head never touches and which hold future history (clean) in the stock reference
(dadon's `Leave255ReleasedActual.mirror`). -/
theorem band_clean (j : Fin 23) (h2 : 2 ≤ j.val) (h12 : j.val ≤ 12) (d:Bool) (x p:Nat) (raw s:State) (m:List Bool)
    (domain:Domain (start j) x p raw) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s)) :
    ∀ q:Nat, 1301 ≤ q → q ≤ 1058 + start j → (run (nextWindow j d) m s).basis q = false := by
  intro q lo hi
  by_cases e12 : j.val = 12
  · have hj : j = ⟨12, by decide⟩ := Fin.ext e12
    subst hj
    have mem : q ∈ List.range' 1301 13 := List.mem_range'_1.mpr ⟨lo, by simp only [StairPacket.start] at hi; omega⟩
    have marks : ∀ q ∈ List.range' 1301 13, ¬Shadow7.MayTouch ⟨12,by decide⟩ (windowNet ⟨12,by decide⟩ q) ∧
        q ∉ support ⟨12,by decide⟩ ++ ArchiveJ7.rawPortsList (prev ⟨12,by decide⟩) ∧ q ∉ EnterJ7.ports ⟨12,by decide⟩ ∧
        q ∉ EnterJ7.pending ⟨12,by decide⟩ ∧ EnterJ7.pull ⟨12,by decide⟩ q = q ∧ q ≠ EnterJ7.flagN ⟨12,by decide⟩ ∧
        q ≠ EnterJ7.flagF ⟨12,by decide⟩ ∧ q ≠ EnterJ7.flagU ⟨12,by decide⟩ ∧
        q ∉ RailPair.sites (EnterJ7.lowerPairs ⟨12,by decide⟩) ∧ q ∉ RailPair.sites (EnterJ7.upperPairs ⟨12,by decide⟩) := by
      (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    obtain ⟨off, adminOff, enterOff, pendOff, pullId, hn, hf, hu, nlo, nhi⟩ := marks q mem
    have split : run (nextWindow ⟨12,by decide⟩ d) m s = run (Shadow7.body ⟨12,by decide⟩ (withArchive ⟨12,by decide⟩ d))
        (m.drop (measurementCount (Shadow7.enterP ⟨12,by decide⟩))) (run (Shadow7.enterP ⟨12,by decide⟩) m s) := by
      simp only [nextWindow, window, run_append, run_take]
    rw [split]
    have normal := Shadow7.ext_head (Shadow7.enterP _) _ (withArchive _ d) _ s m
      (m.drop (measurementCount (Shadow7.enterP ⟨12,by decide⟩))) q off (EnterJ7.notWire _ enterOff)
      adminOff (admin_cover _ (by decide) (by decide) d)
    rw [normal]
    have fr := cut.frame q hn hf hu nlo nhi
    have e1 : (eraseSites (EnterJ7.pending ⟨12,by decide⟩) s).basis q = s.basis q := by
      show (if q ∈ EnterJ7.pending ⟨12,by decide⟩ then false else s.basis q) = s.basis q
      rw [if_neg pendOff]
    rw [← e1, fr]
    show raw.basis (EnterJ7.pull ⟨12,by decide⟩ q) = false
    rw [pullId]
    have qid : q = MappedCompressed.base (1028 + (q - 1044)) := by
      show q = 1028 + (q - 1044) + 16; omega
    have hq : q ≤ 1313 := by simp only [StairPacket.start] at hi; omega
    rw [qid]
    exact WideReference.future_history (by simp only [StairPacket.start]; omega) (by omega) domain
  · exfalso
    simp only [StairPacket.start] at hi; omega

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem scratch : ScratchSpec := by
  intro j h2 h19 d x p good raw s g sg pg ps m pre
  have numbers := LeaveJ7.Admission.actualNumbers j (by omega) (by omega) x p good
  have hist := WideReference.pulled_history j rfl pre.domain
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)
  let Z:=encode g sg T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) (unsigned (start j) x p) numbers.farSmall numbers.odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum g sg _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s (unsigned (start j) x p) g sg m numbers.farSmall pre.cut
    (readInput (start j) x p raw g sg pre.input) hist
  exact NativeJ7.scratch_raw_clean j h2 (by omega) d raw s m x p good pre.domain _ _ _ Z parity ready.2.1 pre.cut

theorem roundtrip : RoundtripSpec := by
  intro j h2 h19 v z G S h m n
  exact LeaveJ7.Admission.Inputs.roundtripMove (by omega) (by omega) h m n

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

abbrev j1 : Fin 23 := ⟨1, by decide⟩

theorem start1 : start j1 = 90 := rfl

/-- `OB5.sig i` fixes the wires below the moved band. -/
theorem fix_low (i q : Nat) (h : q < 1301) (h2 : q + i < 2069) : OB5.sig i q = q :=
  WideReference.sig_fixed (by intro h'; simp only [Wire] at *; omega) (by intro h'; simp only [Wire] at *; omega)

/-- The first block's admin (its pack at 90) touches only its five ticks' cells. -/
theorem admin_cover1 (d:Bool) : wires (program j1 d) ⊆ (support j1).toFinset := by
  intro q hq
  rw [program, renameProgram_support] at hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨r, r1, r2, e | e⟩ := (WindowCovered.pack_cells d 90 (by decide) (by decide)).1 w hw <;>
    subst e <;> simp only [support, List.mem_toFinset, List.mem_flatMap, List.mem_range'_1, List.mem_cons,
      List.not_mem_nil, or_false, start1]
  · exact ⟨r, ⟨by omega, by omega⟩, Or.inl rfl⟩
  · exact ⟨r, ⟨by omega, by omega⟩, Or.inr rfl⟩

theorem support_sites : ∀ q ∈ support j1, q ∈ WideReference.sites 90 := by decide

/-- `NativeJ7.agree_origin` for the first block (first form: no archive, the pack at 90 itself). -/
theorem agree_origin1 (d:Bool) (raw s:State) (m t:List Bool) (neg far long:Bool)
    (packed:PackedCut (EnterJ7.lowerPairs j1) (EnterJ7.upperPairs j1) (EnterJ7.gate j1) (EnterJ7.flagN j1)
      (EnterJ7.flagF j1) (EnterJ7.flagU j1) neg far long (pullState (EnterJ7.pull j1) raw) s)
    (q:Wire) (ext:¬WideReference.Box 90 q) :
    (run (Shadow7.body j1 (program j1 d)) t (run (Shadow7.enterP j1) m s)).basis q =
      (WideReference.origin 90 raw (run (Shadow7.body j1 (program j1 d)) t (run (Shadow7.enterP j1) m s))).basis q := by
  have w104 : W.narrowSkywalkRouteWidth (90+14) = 258 :=
    (LeaveJ7.AssembleCut.route_rail (90+14) (by omega)).trans (by decide)
  have w90 : W.narrowSkywalkRouteWidth 90 = 258 := (LeaveJ7.AssembleCut.route_rail 90 (by omega)).trans (by decide)
  unfold WideReference.Box at ext
  rw [w104, w90] at ext
  have wn : windowNet j1 q = q := by
    show OB5.sig 104 q = q
    exact WideReference.sig_fixed (by intro h'; simp only [Wire] at *; omega) (by intro h'; simp only [Wire] at *; omega)
  have pullId : OB5.sig 89 q = q := by
    exact WideReference.sig_fixed (by intro h'; simp only [Wire] at *; omega) (by intro h'; simp only [Wire] at *; omega)
  have notMay : ¬Shadow7.MayTouch j1 q := by
    intro mt
    apply ext
    unfold Shadow7.MayTouch at mt
    have mid : (Shadow7.shape j1).mid = Shadow7.sbP (start j1)+17 := rfl
    rw [mid, start1] at mt
    have sb : Shadow7.sbP 90 = 204 := by decide
    rw [sb] at mt
    simp only [Wire] at *
    omega
  have free : ¬Shadow7.MayTouch j1 (windowNet j1 q) := by rwa [wn]
  have port : q∉EnterJ7.ports j1 := by
    intro mem
    apply ext
    have r := EnterJ7.portsRegion j1 mem
    rw [start1] at r
    have sb : Shadow7.sbP 90 = 204 := by decide
    rw [sb] at r
    simp only [Wire] at *
    omega
  have origin_eq : WideReference.origin 90 raw = WideReference.origin (StairPacket.start j1) raw := rfl
  rw [origin_eq]
  have ext' : ¬WideReference.Box (StairPacket.start j1) q := by
    unfold WideReference.Box; rw [start1, w104, w90]; exact ext
  apply WideReference.box_origin_j j1 ext' raw _
  intro notSite
  have notAdmin : q∉support j1 := fun mem => notSite (support_sites q mem)
  have stay := Shadow7.ext_head (Shadow7.enterP j1) j1 (program j1 d) (support j1) s m t q free (EnterJ7.notWire j1 port)
    notAdmin (admin_cover1 d)
  have sb : Shadow7.sbP 90 = 204 := by decide
  have hn : q≠EnterJ7.flagN j1 := by
    intro eq; apply ext; rw [eq]; unfold EnterJ7.flagN; rw [start1, sb]
    simp only [Wire] at *; omega
  have hf : q≠EnterJ7.flagF j1 := by
    intro eq; apply ext; rw [eq]; unfold EnterJ7.flagF; rw [start1, sb]
    simp only [Wire] at *; omega
  have hu : q≠EnterJ7.flagU j1 := by
    intro eq; apply ext; rw [eq]; unfold EnterJ7.flagU; rw [start1, sb]
    simp only [Wire] at *; omega
  have hi : q∉RailPair.sites (EnterJ7.upperPairs j1) := by
    intro mm; apply ext
    have u := EnterJ7.upperSites j1 mm
    rw [start1, sb] at u
    have wp : Shadow7.wpP 90 = 38 := by decide
    rw [wp] at u
    simp only [Wire] at *
    omega
  have old := packed.unchanged q hn hf hu hi
  rw [stay]
  simpa only [EnterJ7.pull, pullId] using old

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl

/-- Everything the first block at 90 (block 1) gives, from the stock stage at 90. -/
theorem first_core (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) :
    ∃ G S:Bool,
      InputAt 90 (encode G S (unsigned 90 x p).u (unsigned 90 x p).v) raw ∧
      PackedCut (EnterJ7.lowerPairs j1) (EnterJ7.upperPairs j1) (EnterJ7.gate j1) (EnterJ7.flagN j1) (EnterJ7.flagF j1)
        (EnterJ7.flagU j1) (PortalValues.negative S (unsigned 90 x p).u)
        (decide (Shadow.far (Shadow7.sbP (start j1)) 15 (unsigned 90 x p)))
        (decide (Shadow.far (Shadow7.sbP (start j1)) 15 (unsigned 90 x p) ∧ 2^(Shadow7.sbP (start j1))≤(unsigned 90 x p).u))
        (pullState (EnterJ7.pull j1) raw) (run (Shadow7.portalP 90) m (pullState (OB5.sig 89) raw)) ∧
      (∀ q ∈ Portal90Flag7.activeScratch, (pullState (OB5.sig 89) raw).basis q = false) := by
  have small : Shadow7.SmallIfFar 204 15 (unsigned 90 x p) :=
    (Shadow7.Envelope.inputs x p 90 (lt_trans good.small good.cap) good.cap (by decide)).1
  obtain ⟨G,S,input⟩ := PortalValues.real_input d x p 90 good.positive good.nonzero good.odd good.cap good.gap
    good.small good.coprime (by decide) raw stage
  have pcut := Portal90Flag7.physical_frame_for d x p good.positive good.nonzero good.odd good.cap good.gap good.small
    good.coprime raw m stage G S input
  have same : Shadow.far 204 15 (unsigned 90 x p) = (3*2^220≤(unsigned 90 x p).u+(unsigned 90 x p).v) := by
    apply propext; unfold Shadow.far Shadow.high Shadow.limb; exact Nat.le_div_iff_mul_le (by positivity)
  have lo : Portal90Flag7.loPairs = EnterJ7.lowerPairs j1 := by decide
  have hi : Portal90Flag7.hiPairs = EnterJ7.upperPairs j1 := by decide
  have sb : Shadow7.sbP (start j1) = 204 := by decide
  refine ⟨G, S, ?_, ?_, Portal90Flag7.clean_for raw _ G S input⟩
  · unfold InputAt; rw [flagEq]; exact input
  · rw [sb, ← lo, ← hi]
    simpa only [same] using pcut

/-- L9: the first block's endpoint at 90. -/
theorem first : StockWindowW7.FirstSpec := by
  intro d x p good raw m n stage
  obtain ⟨G, S, input, cut0, clean⟩ := first_core d x p good raw m stage
  let origin := pullState (OB5.sig 89) raw
  let cut := run (Shadow7.portalP 90) m origin
  let n0 := m.drop (measurementCount (Shadow7.portalP 90))
  let tape := n0.drop (measurementCount (Shadow7.enterP j1))
  have dom := initial 90 x p (by decide) d raw stage
  have numbers := LeaveJ7.Admission.actualNumbers j1 (by decide) (by decide) x p good
  have hist := WideReference.pulled_history j1 rfl dom
  have legal0 := original_legal j1 (by decide) (by decide) d x p good.positive good.odd raw stage
  have inputL : SkywalkIntegerInput (EnterJ7.lay j1) (encode G S (unsigned 90 x p).u (unsigned 90 x p).v).a
      (encode G S (unsigned 90 x p).u (unsigned 90 x p).v).b G raw.basis := by
    have i2 := input; unfold InputAt at i2; rw [flagEq] at i2; exact i2
  have win := entered_window j1 (by decide) (by decide) d raw cut n0 (unsigned 90 x p) G S numbers.odd numbers.farSmall
    cut0 inputL hist legal0
  have values := saved_at_leave j1 (by decide) (by decide) d raw cut (unsigned 90 x p) G S n0 tape numbers.farSmall cut0
    inputL
  have tail := tailF_clean j1 (by decide) (by decide) d x p raw cut dom n0 tape _ _ _ cut0
  have vEq : run (Shadow7.portalP 90 ++ enteredWindow j1 d) m origin = run (Shadow7.body j1 (program j1 d)) tape (run (Shadow7.enterP j1) n0 cut) := by
    simp only [enteredWindow, window, run_append, run_take, cut, n0, tape, origin]
  have vEq' : run (Shadow7.portalP 90 ++ enteredWindow j1 d) m origin = run (enteredWindow j1 d) n0 cut := by
    simp only [run_append, run_take, cut, n0, origin]
  have hin : LeaveJ7.Admission.Inputs j1 (run (Shadow7.portalP 90 ++ enteredWindow j1 d) m origin) (unsigned 90 x p) G S := by
    apply LeaveJ7.Admission.assemble j1 (by decide) (by decide) _ (unsigned 90 x p) G S numbers
    · rw [vEq']; exact win.2.1
    · rw [vEq']; exact win.2.2.1
    · rw [vEq, ← NativeJ7.saved_ys j1 (by decide) (by decide)]
      refine ⟨values.1, ?_, ?_, ?_⟩
      · have e : Shadow7.e0P (start j1) + 5 = EnterJ7.flagN j1 := by simp only [EnterJ7.flagN, Shadow7.e0P]; omega
        rw [e]; exact values.2.1
      · have e : Shadow7.e0P (start j1) + 3 = EnterJ7.flagF j1 := by simp only [EnterJ7.flagF, Shadow7.e0P]; omega
        rw [e]; exact values.2.2.1
      · have e : Shadow7.e0P (start j1) + 4 = EnterJ7.flagU j1 := by simp only [EnterJ7.flagU, Shadow7.e0P]; omega
        rw [e]; exact values.2.2.2
    · intro q hq
      rw [vEq]
      apply tail q
      have ew : Shadow7.e0P (start j1) = 1778 := by decide
      have ewp : Shadow7.wpP (start j1) = 38 := by decide
      have s3 : start j1 = 90 := rfl
      have hl : ∀ r : Nat, r ∈ LeaveJ7.Admission.spare j1 → r ∈ tailTempsF j1 := by
        intro r hr
        rw [LeaveJ7.Admission.mem_spare] at hr
        rcases hr with rfl | rfl | ⟨lo, hi⟩ <;> simp only [tailTempsF, List.mem_range'_1] <;>
          simp only [Wire] at * <;> omega
      exact hl q hq
  -- the next block's cut
  have ph : (run (Shadow7.portalP 90 ++ enteredWindow j1 d) m origin).phase =
      (WideReference.origin 90 raw (run (Shadow7.portalP 90 ++ enteredWindow j1 d) m origin)).phase := by
    rw [vEq', win.1, origin_phase 90 x p (by decide) good raw _ dom]
    exact cut0.phase
  have ext : ∀ q:Wire, ¬WideReference.Box (start j1) q → ¬LeaveJ7.AssembleCut.leftovers j1 q →
      ¬(2070≤(q:Nat)+start j1 ∧ (q:Nat)≤1812) → (run (Shadow7.portalP 90 ++ enteredWindow j1 d) m origin).basis q =
        (WideReference.origin (start j1) raw (run (Shadow7.portalP 90 ++ enteredWindow j1 d) m origin)).basis q := by
    intro q nb _ _
    rw [vEq]
    exact agree_origin1 d raw cut n0 tape _ _ _ cut0 q nb
  have upper : ∀ q:Nat, Shadow7.a0P (start j1)+18 ≤ q → q ≤ min (start j1+30+railP (start j1+14)) 529 →
      (run (Shadow7.portalP 90 ++ enteredWindow j1 d) m origin).basis q = false := by
    intro q lo hi
    rw [vEq]
    exact upperF_clear j1 (by decide) (by decide) d raw cut x p dom n0 tape _ _ _ cut0 q (by unfold Shadow7.a0P at lo; omega) hi
  have quiet : ∀ q ∈ LeaveJ7.CoreCheckpoint.rawSites j1, (run (Shadow7.portalP 90 ++ enteredWindow j1 d) m origin).basis q = false := by
    intro q hq
    simp only [LeaveJ7.CoreCheckpoint.rawSites, List.mem_append, List.mem_range'_1] at hq
    rcases hq with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact LeaveJ7.native_carryJ j1 (by decide) (by decide) _ _ hin.ready q (by simp only [Wire] at *; omega)
        (by simp only [Wire] at *; omega)
    · rw [vEq]
      exact tail q (by simp only [tailTempsF, List.mem_range'_1]; simp only [Wire] at *; omega)
  have cutK := LeaveJ7.CertifiedCut.result j1 ⟨2, by decide⟩ (by decide) (by decide) (by decide) (by decide) rfl x p good raw
    (run (Shadow7.portalP 90 ++ enteredWindow j1 d) m origin) n G S hin dom input ph ext
    (fun q lo hi => absurd hi (by simp only [start1] at lo; omega)) upper
    (fun q lo hi => absurd hi (by simp only [start1]; omega))
    (fun q t369 _ _ => absurd t369 (by have e1 := start1; omega)) quiet
  refine ⟨G, S, input, hin, cutK, ?_⟩
  exact LeaveJ7.ArchiveCut.result j1 (by decide) (by decide) _ n (unsigned 90 x p) G S hin

/-- L10: the first window keeps the phase and undoes. -/
theorem firstBack : StockWindowW7.FirstBackSpec := by
  intro d x p good raw m stage
  have hf : WindowParams.first = j1 := rfl
  rw [hf]
  simp only [start1]
  obtain ⟨G, S, input, cut0, clean⟩ := first_core d x p good raw m stage
  let origin := pullState (OB5.sig 89) raw
  let cut := run (Shadow7.portalP 90) m origin
  let n0 := m.drop (measurementCount (Shadow7.portalP 90))
  have dom := initial 90 x p (by decide) d raw stage
  have numbers := LeaveJ7.Admission.actualNumbers j1 (by decide) (by decide) x p good
  have hist := WideReference.pulled_history j1 rfl dom
  have legal0 := original_legal j1 (by decide) (by decide) d x p good.positive good.odd raw stage
  have inputL : SkywalkIntegerInput (EnterJ7.lay j1) (encode G S (unsigned 90 x p).u (unsigned 90 x p).v).a
      (encode G S (unsigned 90 x p).u (unsigned 90 x p).v).b G raw.basis := by
    have i2 := input; unfold InputAt at i2; rw [flagEq] at i2; exact i2
  have win := entered_window j1 (by decide) (by decide) d raw cut n0 (unsigned 90 x p) G S numbers.odd numbers.farSmall
    cut0 inputL hist legal0
  have vEq' : run (Shadow7.portalP 90 ++ enteredWindow j1 d) m origin = run (enteredWindow j1 d) n0 cut := by
    simp only [run_append, run_take, cut, n0, origin]
  refine ⟨?_, ?_⟩
  · rw [vEq', win.1]; exact cut0.phase
  · intro k
    rw [vEq', run_append, win.2.2.2]
    exact Portal90Flag7.portal_return origin m _ clean

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

abbrev EndpointUpTo (J : Nat) : Prop :=
  ∀ (j k : Fin 23), k.val=j.val+1 → WindowParams.first.val+1≤j.val → j.val≤J → ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State)
    (m n:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:ScratchAt j d m s) (pg ps cross:Bool)
    (prior:PastFacts (NativeJ7.prev j) (ArchiveJ7.rawPorts (NativeJ7.prev j)) (Shadow7.sbP (start (NativeJ7.prev j)))
      (unsigned (start (NativeJ7.prev j)) x p) pg ps cross s),
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k)
      (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start j) x p) G S).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) (endRaw (start j) raw (run (NativeJ7.nextWindow j d) m s)))
      (eraseSites (EnterJ7.pending k) (run (Shadow7.leaveP j) n (run (NativeJ7.nextWindow j d) m s))) ∧
    PastFacts j (ArchiveJ7.rawPorts j) (Shadow7.sbP (start j)) (unsigned (start j) x p) G S
      (HighBankSum.cross (LeaveJ7.TrueMiddle.d j (unsigned (start j) x p)))
      (run (Shadow7.leaveP j) n (run (NativeJ7.nextWindow j d) m s))

abbrev KeepLeaveUpTo (J : Nat) : Prop :=
  ∀ (k : Fin 23), 2≤k.val → k.val≤J → ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts (NativeJ7.prev k)),
    ∀ (v:State) (n:List Bool), (run (Shadow7.leaveMoveP k) n v).basis q=v.basis q

abbrev KeepOlderUpTo (J : Nat) : Prop :=
  ∀ (i k i' : Fin 23), k.val=i.val+1 → 1≤ i'.val → i'.val+2≤k.val → k.val≤J → ∀ (d:Bool),
    ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i'), ∀ (s:State) (m:List Bool),
    (run (nextF Shadow7.params d i k).flatten m s).basis q=s.basis q

/-- The leaves of a window whose last block is `J`. -/
structure LeavesUpTo (J : Nat) : Prop where
  endpoint : EndpointUpTo J
  scratch : ScratchSpec
  roundtrip : RoundtripSpec
  keepLeave : KeepLeaveUpTo J
  keepOlder : KeepOlderUpTo J
  first : FirstSpec
  firstBack : FirstBackSpec

/-- The last block's frame at the exit (dadon's `Final.last`, exit ports `ports`). -/
def LastAt (ports : Ports) (J : Fin 23) (d:Bool) (x p:Nat) (s:State) : Prop :=
  ∃row<63145,Chronology (start J) x p row ∧ Frame ports (code d) row s

/-- The exit of a window whose last block is `J`: its step (from the hand-off at `start J+15` to the last frame) and
the keys it keeps. -/
structure ExitLeaves (J : Fin 23) (ports : Ports) : Prop where
  step : ∀ (d:Bool) (x:Nat), Bounds x p → Checked (exitF Shadow7.params d (start J+15)).flatten
    (exitR Shadow7.params d (start J+15)).flatten (ReadyW d x p (start J+15)) (LastAt ports J d x p)
  keep : ∀ (i : Fin 23), WindowParams.first.val ≤ i.val → i.val < J.val → ∀ (d:Bool), ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i),
    ∀ (s:State) (m:List Bool), (run (exitF Shadow7.params d (start J+15)).flatten m s).basis q=s.basis q

theorem interiorG (J : Nat) (hJ : J ≤ 20) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) (i k : Fin 23) (hk : k.val=i.val+1)
    (h4 : WindowParams.first.val+1≤k.val) (h12 : k.val≤J) :
    Checked (nextF Shadow7.params d i k).flatten (nextR Shadow7.params d i k).flatten
      (ReadyW d x p (start k)) (ReadyW d x p (start k+15)) := by
  rw [next_eq d i k hk,nextR_eq d i k hk]
  apply pair (F:=NativeJ7.nextWindow k d) (F':=Shadow7.leaveMoveP k) (R:=NativeJ7.nextUnwind k d) (R':=Shadow7.leaveMoveInvP k)
  intro s m h
  obtain ⟨k1',e0,raw,g,sg,pg,ps,pre⟩:=h
  have same0:k1'=k:=Fin.ext (by have := e0; simp only [StairPacket.start] at this; omega)
  rw [same0] at pre
  let k0:=k
  let v:=run (NativeJ7.nextWindow k0 d) m s
  let n:=m.drop (measurementCount (NativeJ7.nextWindow k0 d))
  let out:=run (Shadow7.leaveP k0) n v
  let raw':=endRaw (start k0) raw v
  let k1:Fin 23:=⟨k0.val+1,by omega⟩
  have p1:NativeJ7.prev k1=k0:=prev_of k0 k1 rfl
  have s1:start k1=start k0+15:=start_succ k0 k1 rfl
  let flags:=LeaveJ7.Admission.flags (unsigned (start k0) x p) g sg
  have hf1 : 1 ≤ WindowParams.first.val := by decide
  have h2 : 2≤k0.val := by omega
  have h19 : k0.val≤20 := by omega
  have curr:=readInput (start k0) x p raw g sg pre.input
  have scr:=L.scratch k0 h2 h19 d x p good raw s g sg pg ps m pre
  have native:=NativeJ7.from_domain_matched k0 h2 h19 d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  obtain ⟨cut,facts⟩:=L.endpoint k0 k1 rfl h4 h12 d x p good raw s m n pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  have hin:=native.1
  have carried:=stepInput_gen_shadow7 (start k0) (Shadow7.sbP (start k0)) x p (by simp only [StairPacket.start]; omega)
    (by simp only [StairPacket.start]; omega) good raw v g sg pre.domain pre.input hin.farSmall
  have lastPhase:out.phase=raw'.phase:=cutPhase cut
  have prevPhase:s.phase=raw.phase:=cutPhase pre.cut
  have ph:=lastPhase.trans ((endRaw_phase (start k0) x p (by simp only [StairPacket.start]; omega) good raw v
    pre.domain).trans prevPhase.symm)
  have canon:=unique_input pre.input (fixed_input _ _ _ (by simp only [StairPacket.start]; omega) good raw pre.domain)
  have same:run (Shadow7.leaveMoveP k0) n v=run (Shadow7.leaveP k0) n v:=LeaveJ7.Admission.Inputs.sameMove (by omega) (by omega) hin n
  show (run (Shadow7.leaveMoveP k0) n v).phase=s.phase ∧ ReadyW d x p (start k+15) (run (Shadow7.leaveMoveP k0) n v) ∧
    (∀t,run (Shadow7.leaveMoveInvP k0) t (run (Shadow7.leaveMoveP k0) n v)=v) ∧ (∀t,run (NativeJ7.nextUnwind k d) t v=s)
  rw [same]
  refine ⟨ph,⟨k1,s1,raw',flags.1,flags.2,g,sg,?_⟩,fun t=>by rw [← same]; exact L.roundtrip k0 (by omega) h19 v _ g sg hin n t,
    native.2.2.2⟩
  refine ⟨?_,?_,cut,?_,?_⟩
  · rw [s1]; exact carried.1
  · rw [s1]; exact carried.2
  · rw [p1]; exact facts
  · rw [p1]; exact canon

theorem firstStepG (J : Nat) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) :
    Checked (Shadow7.params.portal (start WindowParams.first) :: firstF Shadow7.params d WindowParams.first).flatten
      (firstR Shadow7.params d WindowParams.first++[Shadow7.params.portalInv (start WindowParams.first)]).flatten
      (BeforeW d x p) (ReadyW d x p (start WindowParams.first+15)) := by
  rw [first_eq d,firstR_eq d]
  apply pair (F:=Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d) (F':=Shadow7.leaveMoveP WindowParams.first)
    (R:=NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) (R':=Shadow7.leaveMoveInvP WindowParams.first)
  intro s m h
  obtain ⟨raw,stage,rfl⟩:=h
  let v:=run (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)
  let n:=m.drop (measurementCount (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d))
  let out:=run (Shadow7.leaveP WindowParams.first) n v
  let raw':=endRaw (start WindowParams.first) raw v
  obtain ⟨g,sg,input,hin,cut,facts⟩:=L.first d x p good raw m n stage
  let flags:=LeaveJ7.Admission.flags (unsigned (start WindowParams.first) x p) g sg
  have dom:=initial (start WindowParams.first) x p (by decide) d raw stage
  have carried:=stepInput_gen_shadow7 (start WindowParams.first) (Shadow7.sbP (start WindowParams.first)) x p (by decide) (by decide) good raw v g sg dom input hin.farSmall
  have base:out.phase=raw'.phase:=cutPhase cut
  have ph:=base.trans (endRaw_phase (start WindowParams.first) x p (by decide) good raw v dom)
  have back:=L.firstBack d x p good raw m stage
  have same:run (Shadow7.leaveMoveP WindowParams.first) n v=run (Shadow7.leaveP WindowParams.first) n v:=
    LeaveJ7.Admission.Inputs.sameMove (by decide) (by decide) hin n
  show (run (Shadow7.leaveMoveP WindowParams.first) n v).phase=(pullState (OB5.sig (start WindowParams.first-1)) raw).phase ∧
    ReadyW d x p (start WindowParams.first+15) (run (Shadow7.leaveMoveP WindowParams.first) n v) ∧
    (∀t,run (Shadow7.leaveMoveInvP WindowParams.first) t (run (Shadow7.leaveMoveP WindowParams.first) n v)=v) ∧
    (∀t,run (NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) t v=pullState (OB5.sig (start WindowParams.first-1)) raw)
  rw [same]
  exact ⟨ph,⟨firstNext,rfl,raw',flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts,
    unique_input input (fixed_input (start WindowParams.first) x p (by decide) good raw dom)⟩,
    fun t=>by rw [← same]; exact L.roundtrip WindowParams.first (by decide) (by decide) v _ g sg hin n t,back.2⟩

theorem receiptG (J : Nat) (hJ : J ≤ 20) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) (i k : Fin 23) (hk : k.val=i.val+1)
    (h2 : 2≤k.val) (h12 : k.val≤J) :
    ∀ s m, ReadyW d x p (start k) s → KeyW d x p i (run (nextF Shadow7.params d i k).flatten m s) := by
  intro s m h
  obtain ⟨k1',e0,raw,g,sg,pg,ps,pre⟩:=h
  have same0:k1'=k:=Fin.ext (by have := e0; simp only [StairPacket.start] at this; omega)
  rw [same0] at pre
  have pk:=prev_of i k hk
  rw [next_eq d i k hk,←pk]
  simp only [run_append,run_take]
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=L.scratch k h2 (by omega) d x p good raw s g sg pg ps m pre
  have native:=NativeJ7.from_domain_matched k h2 (by omega) d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  obtain ⟨row,bound,truth,kept⟩:=native.2.2.1
  have chr:Chronology (start (NativeJ7.prev k)) x p row:=by unfold Chronology;rw [←pre.pastCanonical];exact truth
  exact ⟨row,bound,chr,ArchiveWindowPreserve.keep kept (fun q hq=>L.keepLeave k h2 h12 q hq _ _)⟩

theorem keepG (J : Nat) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (i k : Fin 23) (hk : k.val=i.val+1) (h12 : k.val≤J) :
    ∀ s m, ReadyW d x p (start k) s → ∀ i' : Fin 23, WindowParams.first.val ≤ i'.val → i'.val< i.val → KeyW d x p i' s →
      KeyW d x p i' (run (nextF Shadow7.params d i k).flatten m s) := by
  intro s m _ i' h1 h2 key
  have hf1 : 1 ≤ WindowParams.first.val := by decide
  obtain ⟨r,lim,chr,kept⟩:=key
  exact ⟨r,lim,chr,ArchiveWindowPreserve.keep kept (fun q hq=>L.keepOlder i k i' hk (by omega) (by omega) h12 d q hq s m)⟩

/-- The window's stock chain, generic in its last block `J` and its interior list `rest`. -/
theorem checkedG (J : Fin 23) (h4 : WindowParams.first.val+1 ≤ J.val) (hJ : J.val ≤ 20) (ports : Ports) (rest : List (Fin 23))
    (consec : Consec WindowParams.first rest) (mem : ∀ k ∈ rest, WindowParams.first.val+1 ≤ k.val ∧ k.val ≤ J.val)
    (exitT : exitTick WindowParams.first rest = start J+15)
    (L : LeavesUpTo J.val) (X : ExitLeaves J ports) (d:Bool) (x:Nat) (good:Bounds x p) :
    Checked (forwardW Shadow7.params d WindowParams.first rest)
      (reverseW Shadow7.params d WindowParams.first rest)
      (BeforeW d x p) (FinalW WindowParams.first J ports d x p) := by
  have hf1 : 1 ≤ WindowParams.first.val := by decide
  have bl:blockOf (exitTick WindowParams.first rest)=J.val+1:=by rw [exitT]; exact blockOf_next J
  have h:=window_strong Shadow7.params d (ReadyW d x p) (KeyW d x p) (BeforeW d x p) (LastAt ports J d x p)
    WindowParams.first rest consec (firstStepG J.val L d x p good)
    (fun i k hm hk=>interiorG J.val (by omega) L d x p good i k hk (mem k hm).1 (mem k hm).2)
    (fun i k hm hk=>receiptG J.val (by omega) L d x p good i k hk (by have := mem k hm; omega) (by have := mem k hm; omega))
    (fun i k hm hk s m r i' h1 h2=>keepG J.val L d x p i k hk (by have := mem k hm; omega) s m r i' (by omega) h2)
    (by rw [exitT]; exact X.step d x good)
    (by
      intro s m _ i h1 h2 key
      rw [bl] at h2
      revert key
      rw [exitT]
      intro key
      obtain ⟨r,lim,chr,kept⟩:=key
      exact ⟨r,lim,chr,ArchiveWindowPreserve.keep kept (fun q hq=>X.keep i (by omega) (by omega) d q hq s m)⟩)
  refine checked_mono h ?_
  intro s ⟨last,saved⟩
  refine ⟨?_, last⟩
  intro k h1 h2
  obtain ⟨r, lim, chr, kept⟩ := saved k h1 (by rw [bl]; omega)
  exact ⟨r, lim, chr, ArchiveJ7.kept_stock k d r s kept⟩

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

theorem sig_moved (i q : Nat) (h : (1301 ≤ q ∧ q ≤ 1044+i) ∨ (2069 ≤ q+i ∧ q ≤ 1812)) :
    OB5.sig i q = 3113 - q := by
  rw [OB5.sig_nat]; unfold OB5.sigNat; rw [if_pos h]

theorem sig_kept (i q : Nat) (h1 : ¬(1301 ≤ q ∧ q ≤ 1044+i)) (h2 : ¬(2069 ≤ q+i ∧ q ≤ 1812)) :
    OB5.sig i q = q := by
  rw [OB5.sig_nat]; unfold OB5.sigNat; rw [if_neg (by omega)]

/-- The admin of block `j` (its pack and the previous block's archive load) never writes the band `[1301, 1058+s]`
nor the older moved history `[2070-s, 1812]`, for `start j ≤ 345` (no scratch is moved before tick 370). -/
theorem admin_away (j : Fin 23) (h2 : 2≤j.val) (h18 : j.val≤20) (q : Wire)
    (hq : (1301 ≤ (q:Nat) ∧ (q:Nat) ≤ 1058+start j) ∨ (2070 ≤ (q:Nat)+start j ∧ (q:Nat) ≤ 1812 ∧
      ¬(2070 ≤ (q:Nat)+start j ∧ (q:Nat)+start j ≤ 2084))) :
    q ∉ support j ++ ArchiveJ7.rawPortsList (prev j) := by
  have hs : 105 ≤ start j ∧ start j ≤ 375 := by simp only [StairPacket.start]; omega
  have tick : start (prev j)+15 = start j := by simp only [prev, StairPacket.start]; omega
  intro mem
  rw [List.mem_append, ArchiveJ7.raw_split, List.mem_append] at mem
  rcases mem with mem | mem | mem
  · simp only [support, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false] at mem
    obtain ⟨v, ⟨v1, v2⟩, e | e⟩ := mem
    · rw [sig_kept _ _ (by simp only [MappedCompressed.base]; omega) (by simp only [MappedCompressed.base]; omega)] at e
      simp only [MappedCompressed.base, Wire] at *; omega
    · by_cases mv : 1301 ≤ 1044 + v
      · rw [sig_moved _ _ (Or.inl ⟨by simp only [MappedCompressed.base]; omega, by simp only [MappedCompressed.base]; omega⟩)] at e
        simp only [MappedCompressed.base, Wire] at *; omega
      · rw [sig_kept _ _ (by simp only [MappedCompressed.base]; omega) (by simp only [MappedCompressed.base]; omega)] at e
        simp only [MappedCompressed.base, Wire] at *; omega
  · simp only [ArchiveJ7.rawHead, cellsLoadP, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false, tick] at mem
    rcases mem with ⟨k, hk, e | e⟩ | e
    · simp only [Wire] at *; omega
    · by_cases mv : 1301 ≤ start j + 1034 + k
      · rw [sig_moved _ _ (Or.inl ⟨mv, by omega⟩)] at e
        simp only [Wire] at *; omega
      · rw [sig_kept _ _ (by omega) (by omega)] at e
        simp only [Wire] at *; omega
    · have eb : Shadow7.e0P (start j) = 1574 + Shadow7.sbP (start j) := rfl
      have sbb := Shadow7.rail_win (show 90 ≤ start j by omega) (show start j ≤ 390 by omega)
      simp only [Wire] at *; omega
  · obtain ⟨k, hk, e⟩ := List.mem_map.mp mem
    have hk' := List.mem_range.mp hk
    rw [tick] at e
    have qv : (q:Nat) = Shadow7.scratchS (start j) k := e.symm
    rcases Shadow7.scratchS_cases (start j) k (by omega) hk' with ⟨eqs, lo, hi⟩ | ⟨lo, hi⟩
    · simp only [Wire] at *; omega
    · simp only [Wire] at *; omega

/-- The older moved history of block `j ≤ 18` agrees with the origin after the head (the block's own fold is a
site of the origin; the older folds are untouched and pulled from the stock state). -/
theorem mirror_origin (j : Fin 23) (h2 : 2≤j.val) (h18 : j.val≤20) (hne : start j≠WideReference.firstBlock) (d : Bool)
    (raw s : State) (m t : List Bool) (neg far long : Bool)
    (packed : PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j)
      (EnterJ7.flagF j) (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw)
      (eraseSites (EnterJ7.pending j) s))
    (q : Wire) (lo : 2070 ≤ (q:Nat)+start j) (hi : (q:Nat) ≤ 1812) :
    let history := run (Shadow7.body j (withArchive j d)) t (run (Shadow7.enterP j) m s)
    history.basis q = (WideReference.origin (start j) raw history).basis q := by
  intro history
  have hs : 105 ≤ start j ∧ start j ≤ 375 := by simp only [StairPacket.start]; omega
  have sb := Shadow7.rail_win (show 90 ≤ start j by omega) (show start j ≤ 390 by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := sb
  have w14 : W.narrowSkywalkRouteWidth (start j+14) = railP (start j+14) :=
    LeaveJ7.AssembleCut.route_rail (start j+14) (by omega)
  have w0 : W.narrowSkywalkRouteWidth (start j) = railP (start j) := LeaveJ7.AssembleCut.route_rail (start j) (by omega)
  have rr : railP (start j+14) ≤ 258 := by unfold railP; split_ifs <;> omega
  have ext : ¬WideReference.Box (start j) q := by
    unfold WideReference.Box; rw [w14, w0]; simp only [Wire] at *; omega
  have wn : windowNet j q = 3113 - q := by
    show OB5.sig (start j+14) q = _
    exact sig_moved _ _ (Or.inr ⟨by simp only [Wire] at *; omega, hi⟩)
  have free : ¬Shadow7.MayTouch j (windowNet j q) := by
    rw [wn]
    unfold Shadow7.MayTouch
    have mid : (Shadow7.shape j).mid = Shadow7.sbP (start j)+17 := rfl
    rw [mid]
    simp only [Wire] at *
    omega
  have port : q∉EnterJ7.ports j := by
    intro mem
    have r := EnterJ7.portsRegion j mem
    simp only [Wire] at *
    omega
  apply WideReference.box_origin_j j ext raw history
  intro notSite
  have notAdmin : q∉support j++ArchiveJ7.rawPortsList (prev j) := by
    intro mem
    rw [List.mem_append] at mem
    have tick : start (prev j)+15 = start j := by simp only [prev, StairPacket.start]; omega
    rcases mem with mem | mem
    · rcases admin_outside j h2 (by omega) hne q (List.mem_append_right _ mem) with b|b
      · exact ext b
      · exact notSite b
    · rw [ArchiveJ7.raw_split, List.mem_append] at mem
      rcases mem with mem|mem
      · rcases admin_outside j h2 (by omega) hne q (List.mem_append_left _ mem) with b|b
        · exact ext b
        · exact notSite b
      · obtain ⟨k,hk,eq⟩ := List.mem_map.mp mem
        have hk' := List.mem_range.mp hk
        rw [tick] at eq
        have qv : (q:Nat) = Shadow7.scratchS (start j) k := eq.symm
        rcases Shadow7.scratchS_cases (start j) k (by omega) hk' with ⟨eqs,lo',hi'⟩|⟨lo',hi'⟩
        · simp only [Wire] at *; omega
        · simp only [Wire] at *; omega
  have stay := Shadow7.ext_head (Shadow7.enterP j) j (withArchive j d)
      (support j++ArchiveJ7.rawPortsList (prev j)) s m t q free (EnterJ7.notWire j port) notAdmin
      (admin_cover j (by omega) (by omega) d)
  have hn : q≠EnterJ7.flagN j := by intro eq; rw [eq] at lo hi; unfold EnterJ7.flagN at lo hi; simp only [Wire] at *; omega
  have hf : q≠EnterJ7.flagF j := by intro eq; rw [eq] at lo hi; unfold EnterJ7.flagF at lo hi; simp only [Wire] at *; omega
  have hu : q≠EnterJ7.flagU j := by intro eq; rw [eq] at lo hi; unfold EnterJ7.flagU at lo hi; simp only [Wire] at *; omega
  have hi' : q∉RailPair.sites (EnterJ7.upperPairs j) := by
    intro mm
    have u := EnterJ7.upperSites j mm
    simp only [Wire] at *
    omega
  have pend : q∉EnterJ7.pending j := by
    intro mem
    simp only [EnterJ7.pending, List.mem_cons, List.not_mem_nil, or_false] at mem
    simp only [Wire] at *
    rcases mem with rfl|rfl|rfl <;> omega
  have old := packed.unchanged q hn hf hu hi'
  rw [stay]
  simpa only [eraseSites, if_neg pend, EnterJ7.pull] using old


/-- The sig band `[1301, 1058+s]` is clean after the head of block `j ≤ 18`: the head never writes it; below
`1044+s` it holds the stock carry top (moved by the pull), above it the block's own future history. -/
theorem band_clean_gen (j : Fin 23) (h2 : 2 ≤ j.val) (h18 : j.val ≤ 20) (d:Bool) (x p:Nat) (good : Bounds x p)
    (raw s:State) (m:List Bool)
    (domain:Domain (start j) x p raw) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s)) :
    ∀ q:Nat, 1301 ≤ q → q ≤ 1058 + start j → (run (nextWindow j d) m s).basis q = false := by
  intro q lo hi
  have hs : 105 ≤ start j ∧ start j ≤ 375 := by simp only [StairPacket.start]; omega
  have sb := Shadow7.rail_win (show 90 ≤ start j by omega) (show start j ≤ 390 by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := sb
  have split : run (nextWindow j d) m s = run (Shadow7.body j (withArchive j d))
      (m.drop (measurementCount (Shadow7.enterP j))) (run (Shadow7.enterP j) m s) := by
    simp only [nextWindow, window, run_append, run_take]
  rw [split]
  have wn : windowNet j q = 3113 - q := by
    show OB5.sig (start j+14) q = _
    exact sig_moved _ _ (Or.inl ⟨lo, by omega⟩)
  have free : ¬Shadow7.MayTouch j (windowNet j q) := by
    rw [wn]
    unfold Shadow7.MayTouch
    have mid : (Shadow7.shape j).mid = Shadow7.sbP (start j)+17 := rfl
    rw [mid]
    simp only [Wire] at *
    omega
  have port : q∉EnterJ7.ports j := by
    intro mem
    have r := EnterJ7.portsRegion j mem
    simp only [Wire] at *
    omega
  have notAdmin := admin_away j h2 h18 q (Or.inl ⟨lo, hi⟩)
  rw [Shadow7.ext_head (Shadow7.enterP j) j (withArchive j d) _ s m _ q free (EnterJ7.notWire j port) notAdmin
      (admin_cover j (by omega) (by omega) d)]
  have hn : q≠EnterJ7.flagN j := by unfold EnterJ7.flagN; simp only [Wire] at *; omega
  have hf : q≠EnterJ7.flagF j := by unfold EnterJ7.flagF; simp only [Wire] at *; omega
  have hu : q≠EnterJ7.flagU j := by unfold EnterJ7.flagU; simp only [Wire] at *; omega
  have hi' : q∉RailPair.sites (EnterJ7.upperPairs j) := by
    intro mm
    have u := EnterJ7.upperSites j mm
    simp only [Wire] at *
    omega
  have pend : q∉EnterJ7.pending j := by
    intro mem
    simp only [EnterJ7.pending, List.mem_cons, List.not_mem_nil, or_false] at mem
    simp only [Wire] at *
    rcases mem with rfl|rfl|rfl <;> omega
  have old := cut.unchanged q hn hf hu hi'
  have e1 : s.basis q = (eraseSites (EnterJ7.pending j) s).basis q := by
    show s.basis q = (if q ∈ EnterJ7.pending j then false else s.basis q)
    rw [if_neg pend]
  rw [e1, old]
  show raw.basis (OB5.sig (start j - 1) q) = false
  by_cases mv : q ≤ 1043 + start j
  · rw [sig_moved _ _ (Or.inl ⟨lo, by omega⟩)]
    have c := WideReference.full_carry (start j) 0 x p (by omega) good raw domain [] (3113 - q) (by omega) (by omega)
    simp only [WideReference.span] at c
    have rn : run [] [] raw = raw := by unfold run; rfl
    rw [rn] at c
    exact c
  · rw [sig_kept _ _ (by omega) (by omega)]
    have qid : q = MappedCompressed.base (1028 + (q - 1044)) := by
      show q = 1028 + (q - 1044) + 16; omega
    rw [qid]
    exact WideReference.future_history (show start j ≤ q - 1044 by omega) (by omega) domain

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}BodyCut.result`, generic for the interior blocks up to 255 (the older moved history is
empty there). `band` is the sig band `[1301, s+1058]` before the leave (empty before 243). -/
theorem resultG (j k : Fin 23) (hk : k.val=j.val+1) (h2 : 2≤j.val) (h12 : j.val≤20)
    (hne : start j≠WideReference.firstBlock) (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (a b m:List Bool)
    (neg far long g0 s0:Bool) (domain:Domain (start j) x p raw)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:InputAt (start j) (encode g0 s0 (unsigned (start j) x p).u (unsigned (start j) x p).v) raw)
    (h:Admission.Inputs j (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s))
      (unsigned (start j) x p) g0 s0)
    (phase:(run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).phase=s.phase)
    (popped:(run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis (Shadow7.e0P (start j)+8)=false)
    (tail:∀q∈NativeJ7.tailTemps j,(run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false)
    (band:∀q:Nat,1301≤q → q≤1058+start j →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false)
    (hosts:∀q:Nat,369≤start j → 1302≤q+start j → q≤933 →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q=false) :
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k) (PortalValues.negative (Admission.flags (unsigned (start j) x p) g0 s0).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k)) ≤ (unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k)
        (endRaw (start j) raw (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s))))
      (eraseSites (EnterJ7.pending k)
        (run (Shadow7.leaveP j) m (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)))) := by
  obtain ⟨w1, w2⟩ := start_win j (by omega) (by omega)
  have hs : start k = start j + 15 := by simp only [StairPacket.start]; omega
  have top : start j ≤ 375 := by simp only [StairPacket.start]; omega
  have ag : ∀ q : Wire, ¬WideReference.Box (start j) q → ¬AssembleCut.leftovers j q →
      ¬(2070≤(q:Nat)+start j ∧ (q:Nat)≤1812) →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q =
        (origin (start j) raw (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s))).basis q := by
    intro q nb nl nm
    unfold AssembleCut.leftovers ReleasedOrigin.releasedSite at nl
    simp only [not_or, not_and] at nl
    exact NativeJ7.agree_origin j h2 (by omega) hne d raw s a b neg far long cut q nb
      (by simp only [Wire] at *; omega) (by simp only [Wire] at *; omega) (by simp only [Wire] at *; omega)
  have up : ∀ q:Nat, Shadow7.a0P (start j)+18 ≤ q → q ≤ min (start j+30+railP (start j+14)) 529 →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q = false :=
    fun q lo hi => NativeJ7.upper_clear j (by omega) (by omega) d raw s x p domain a b neg far long cut q
      (by unfold Shadow7.a0P at lo; omega) hi
  have mir : ∀ q:Nat, 2070≤q+start j → q≤1812 →
      (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)).basis q =
        (origin (start j) raw (run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s))).basis q :=
    fun q lo hi => NativeJ7.mirror_origin j h2 (by omega) hne d raw s a b neg far long cut q lo hi
  generalize hv : run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s) = v at h phase popped tail band hosts ag up mir ⊢
  have quiet : ∀ q ∈ CoreCheckpoint.rawSites j, v.basis q = false := by
    intro q hq
    simp only [CoreCheckpoint.rawSites, List.mem_append, List.mem_range'_1] at hq
    rcases hq with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact native_carryJ j (by omega) (by omega) _ v h.ready q (by simp only [Wire] at *; omega)
        (by simp only [Wire] at *; omega)
    · by_cases e8 : (q:Nat) = Shadow7.e0P (start j) + 8
      · have e8' : q = Shadow7.e0P (start j) + 8 := e8
        rw [e8']; exact popped
      · exact tail q (by simp only [NativeJ7.tailTemps, List.mem_range'_1]; simp only [Wire] at *; omega)
  have ph : v.phase = (origin (start j) raw v).phase :=
    phase.trans (cut.phase.trans (origin_phase (start j) x p (by omega) good raw v domain).symm)
  exact CertifiedCut.result j k (by omega) (by omega) (by omega) (by omega) hs x p good raw v m g0 s0 h domain input ph ag
    mir up band hosts quiet

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.BodyCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `NativePack{s}.stock_endpoint`, generic (interior blocks `2 ≤ j ≤ 12`, next block `k = j+1`): the
leave's output is the next block's packed cut, and the next pack's archive facts hold. -/
theorem stock_endpointG (j k : Fin 23) (hk : k.val=j.val+1) (h2 : 2≤j.val) (h12 : j.val≤20)
    (hne : start j≠WideReference.firstBlock) (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State)
    (m n:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (pg ps cross:Bool)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) (unsigned (start (prev j)) x p) pg ps cross s)
    (band : ∀q:Nat,1301≤q → q≤1058+start j → (run (nextWindow j d) m s).basis q=false) :
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k)
      (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start j) x p) G S).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) (endRaw (start j) raw (run (nextWindow j d) m s)))
      (eraseSites (EnterJ7.pending k) (run (Shadow7.leaveP j) n (run (nextWindow j d) m s))) ∧
    PastFacts j (ArchiveJ7.rawPorts j) (Shadow7.sbP (start j)) (unsigned (start j) x p) G S
      (HighBankSum.cross (LeaveJ7.TrueMiddle.d j (unsigned (start j) x p)))
      (run (Shadow7.leaveP j) n (run (nextWindow j d) m s)) := by
  obtain ⟨w1, w2⟩ := start_win j (by omega) (by omega)
  have numbers:=LeaveJ7.Admission.actualNumbers j (by omega) (by omega) x p good
  have old:=LeaveJ7.Admission.actualNumbers (prev j) (by simp only [prev]; omega) (by simp only [prev]; omega) x p good
  have hist:=pulled_history j rfl domain
  have native:=from_domain j h2 (by omega) d x p good raw s m domain G S cut input scratch pg ps cross prior
  obtain ⟨_,_,_,_,tags⟩:=real_receipt j (by omega) (by omega) d raw s m (unsigned (start j) x p) G S numbers.odd
    numbers.farSmall cut input hist scratch (unsigned (start (prev j)) x p) pg ps cross old.odd old.farSmall prior
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) (unsigned (start j) x p) numbers.farSmall numbers.odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s (unsigned (start j) x p) G S m numbers.farSmall cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j (by omega) (by omega) d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity
    ready.2.1 scratch (unsigned (start (prev j)) x p) pg ps cross old.odd old.farSmall prior
  have final:=archive_result j (by omega) (by omega) d row limit _ _ frame
  have tail:=tail_clean j (by omega) (by omega) d x p raw s domain m tape _ _ _ cut row final
  have runEq : run (nextWindow j d) m s = run (Shadow7.body j (withArchive j d)) tape pre := by
    simp only [nextWindow, window, run_append, run_take, pre, tape]
  have gg (g s:Bool) (u v:Int) : (encode g s u v).g=g:=by cases g <;> rfl
  have orig:InputAt (start j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v) raw:=by
    unfold InputAt;rw [gg];exact input
  have h := native.1
  have ph := native.2.1
  refine ⟨?_, LeaveJ7.ArchiveCut.result j (by omega) (by omega) (run (nextWindow j d) m s) n (unsigned (start j) x p) G S h⟩
  have bit : (run (nextWindow j d) m s).basis (Shadow7.e0P (start j)+8) = false := by
    have t2 := tags ⟨2, by omega⟩
    have e : Shadow7.e0P (start j) + 8 = Shadow7.sbP (start j)+1580+(⟨2, by omega⟩:Fin 3).val := by simp only [Shadow7.e0P]; omega
    rw [e]; exact t2
  have hosts : ∀ q:Nat, 369≤start j → 1302≤q+start j → q≤933 →
      (run (Shadow7.body j (withArchive j d)) tape pre).basis q=false := by
    intro q t369 lo hi
    have tj : start j≤390 := by simp only [start]; omega
    have hk' : q-800<134 := by omega
    have tk : start (prev j)+15=start j := by simp only [prev,start]; omega
    have low : ¬(1556+(q-800)<Shadow7.e0P (start j)) := by simp only [Shadow7.e0P,Shadow7.sbP]; omega
    have hw : Shadow7.scratchW (start j) (q-800)=1566+(q-800) := if_neg low
    have far : 2068≤Shadow7.scratchW (start j) (q-800)+start j := by rw [hw]; omega
    have sv : Shadow7.scratchS (start j) (q-800)=q := by
      rw [Shadow7.scratchS_high (start j) (q-800) (by omega) hk' far,hw]; omega
    have port : ArchiveJ7.codePorts (prev j) ⟨16+(q-800),by omega⟩=q := by
      show (ArchiveJ7.codePortsList (prev j)).getD (16+(q-800)) 0=q
      rw [ArchiveJ7.code_scratch (prev j) hk',tk]; exact sv
    have wn : windowNet j q=q := by
      show OB5.sig (start j+14) q=q
      exact sig_kept _ _ (by omega) (by omega)
    have free : ¬Shadow7.MayTouch j (windowNet j q) := by
      rw [wn]
      unfold Shadow7.MayTouch
      have mid : (Shadow7.shape j).mid=Shadow7.sbP (start j)+17 := rfl
      rw [mid]
      simp only [Shadow7.sbP,Wire] at *
      omega
    exact Shadow7.after_encoded j (withArchive j d) (ArchiveJ7.codePorts (prev j)) d row pre tape final
      ⟨16+(q-800),by omega⟩ (by show 16≤16+(q-800); omega) q port free
  rw [runEq] at h ph band bit ⊢
  exact LeaveJ7.BodyCut.resultG j k hk h2 (by omega) hne d x p good raw s m tape n _ _ _ G S domain cut orig h ph bit tail band
    hosts

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

/-- One B-side code cell `OB5.sig t (t+1034+c)`, `c ≤ 8`: unmoved below 1301, else in the fold. -/
theorem bcell (t c : Nat) (ht : t ≤ 390) (hc : c ≤ 8) :
    (OB5.sig t (t+1034+c) = t+1034+c ∧ t+1034+c ≤ 1300) ∨
    (OB5.sig t (t+1034+c) = 3113-(t+1034+c) ∧ 1301 ≤ t+1034+c) := by
  by_cases h : 1301 ≤ t+1034+c
  · exact Or.inr ⟨NativeJ7.sig_moved _ _ (Or.inl ⟨h, by omega⟩), h⟩
  · exact Or.inl ⟨NativeJ7.sig_kept _ _ (by omega) (by omega), by omega⟩

/-- The 16 restore cells of tick `t ≤ 390`, sig-aware. -/
theorem cells_rangeG (t : Nat) (ht : t ≤ 390) (q : Nat) (h : q ∈ cellsRestoreP t) :
    (t+6 ≤ q ∧ q ≤ t+15) ∨ (t+1034 ≤ q ∧ q ≤ t+1042 ∧ q ≤ 1300) ∨ (2071 ≤ q+t ∧ q+t ≤ 2079 ∧ q ≤ 1812) := by
  have b0 := bcell t 0 ht (by omega)
  have b1 := bcell t 1 ht (by omega)
  have b3 := bcell t 3 ht (by omega)
  have b5 := bcell t 5 ht (by omega)
  have b6 := bcell t 6 ht (by omega)
  have b8 := bcell t 8 ht (by omega)
  simp only [Nat.add_zero] at b0
  simp only [cellsRestoreP, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  first
  | omega
  | (rcases b0 with ⟨e, l⟩ | ⟨e, l⟩ <;> rw [e] <;> omega)
  | (rcases b1 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1035 = t+1034+1 by omega]; rw [e]) <;> omega)
  | (rcases b3 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1037 = t+1034+3 by omega]; rw [e]) <;> omega)
  | (rcases b5 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1039 = t+1034+5 by omega]; rw [e]) <;> omega)
  | (rcases b6 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1040 = t+1034+6 by omega]; rw [e]) <;> omega)
  | (rcases b8 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1042 = t+1034+8 by omega]; rw [e]) <;> omega)

theorem key_rangeG (i : Fin 23) (hi : i.val ≤ 20) (q : Nat)
    (h : q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i)) :
    (start i+21 ≤ q ∧ q ≤ start i+30) ∨ (start i+1049 ≤ q ∧ q ≤ start i+1057 ∧ q ≤ 1300) ∨
    (2056 ≤ q+start i ∧ q+start i ≤ 2064 ∧ q ≤ 1812) := by
  have c := cells_rangeG (start i + 15) (by simp only [StairPacket.start]; omega) q (bank_cells i q h)
  omega

theorem keepLeaveG : KeepLeaveUpTo 20 := by
  intro k h2 h18 q hq v n
  have c := key_rangeG (NativeJ7.prev k) (by simp only [NativeJ7.prev]; omega) q hq
  have pk : start (NativeJ7.prev k) + 15 = start k := by simp only [NativeJ7.prev, StairPacket.start]; omega
  obtain ⟨w1, w2⟩ := start_win k (by omega) (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  exact LeaveJ7.leaveMove_keeps k (by omega) (by omega) q (by unfold Shadow7.leaveBox2; simp only [Wire] at *; omega) n v

theorem keepOlderG : KeepOlderUpTo 20 := by
  intro i k i' hk h2 hik h18 d q hq s m
  have hs : start i' + 30 ≤ start k := by simp only [StairPacket.start]; omega
  have c := key_rangeG i' (by omega) q hq
  obtain ⟨w1, w2⟩ := start_win k (by omega) (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have sk : start k ≤ 375 := by simp only [StairPacket.start]; omega
  have pk : NativeJ7.prev k = i := Fin.ext (by simp only [NativeJ7.prev]; omega)
  rw [next_eq d i k hk]
  simp only [run_append, run_take]
  rw [LeaveJ7.leaveMove_keeps k (by omega) (by omega) q (by unfold Shadow7.leaveBox2; simp only [Wire] at *; omega)]
  simp only [NativeJ7.nextWindow, NativeJ7.window, run_append, run_take]
  have native : ¬Shadow7.MayTouch k (windowNet k q) := by
    have mid : (Shadow7.shape k).mid = Shadow7.sbP (start k)+17 := rfl
    rcases c with c | c | c
    · have fixed : windowNet k q = q := by
        show OB5.sig (start k + 14) q = q
        exact NativeJ7.sig_kept _ _ (by omega) (by omega)
      rw [fixed]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
    · have fixed : windowNet k q = q := by
        show OB5.sig (start k + 14) q = q
        exact NativeJ7.sig_kept _ _ (by omega) (by omega)
      rw [fixed]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
    · have moved : windowNet k q = 3113 - q := by
        show OB5.sig (start k + 14) q = _
        exact NativeJ7.sig_moved _ _ (Or.inr ⟨by omega, by omega⟩)
      rw [moved]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
  have port : q ∉ EnterJ7.ports k := by
    simp only [EnterJ7.ports, List.mem_cons, List.not_mem_nil, or_false]
    simp only [Wire] at *
    omega
  have admin : q ∉ NativeJ7.support k ++ ArchiveJ7.rawPortsList (NativeJ7.prev k) := by
    rw [List.mem_append, ArchiveJ7.raw_split]
    intro mem
    rcases mem with mem | mem
    · simp only [NativeJ7.support, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      obtain ⟨v, ⟨v1, v2⟩, e | e⟩ := mem
      · rw [NativeJ7.sig_kept _ _ (by simp only [MappedCompressed.base, Wire] at *; omega)
          (by simp only [MappedCompressed.base, Wire] at *; omega)] at e
        simp only [MappedCompressed.base, Wire] at *; omega
      · by_cases mv : 1301 ≤ 1044 + v
        · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨by simp only [MappedCompressed.base]; omega,
            by simp only [MappedCompressed.base]; omega⟩)] at e
          simp only [MappedCompressed.base, Wire] at *; omega
        · rw [NativeJ7.sig_kept _ _ (by simp only [MappedCompressed.base]; omega)
            (by simp only [MappedCompressed.base]; omega)] at e
          simp only [MappedCompressed.base, Wire] at *; omega
    · rw [List.mem_append] at mem
      have tk : start (NativeJ7.prev k) + 15 = start k := by simp only [NativeJ7.prev, StairPacket.start]; omega
      rcases mem with mem | mem
      · simp only [ArchiveJ7.rawHead, cellsLoadP, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false, tk] at mem
        rcases mem with ⟨c', hc, e | e⟩ | e
        · simp only [Wire] at *; omega
        · by_cases mv : 1301 ≤ start k + 1034 + c'
          · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨mv, by omega⟩)] at e
            simp only [Wire] at *; omega
          · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)] at e
            simp only [Wire] at *; omega
        · simp only [Shadow7.e0P, Wire] at *; omega
      · obtain ⟨kk, hkk, e⟩ := List.mem_map.mp mem
        have hk' := List.mem_range.mp hkk
        rw [tk] at e
        have qv : (q:Nat) = Shadow7.scratchS (start k) kk := e.symm
        rcases Shadow7.scratchS_cases (start k) kk (by omega) hk' with ⟨-, lo, hi⟩ | ⟨-, lo, hi⟩ <;>
          (simp only [Wire] at *; omega)
  exact Shadow7.ext_head (Shadow7.enterP k) k (NativeJ7.withArchive k d) _ s m _ q native (EnterJ7.notWire k port) admin
    (NativeJ7.admin_cover k (by omega) (by omega) d)

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- `EndpointSpec` for every interior block up to `J = 20` (`start j ≤ 375`). -/
theorem endpoint20 : EndpointUpTo 20 := by
  intro j k hk h4 h18 d x p good raw s m n domain G S cut input scratch pg ps cross prior
  have hf1 : 1 ≤ WindowParams.first.val := by decide
  have hne : start j ≠ WideReference.firstBlock := by
    simp only [WideReference.firstBlock, StairPacket.start]; omega
  exact NativeJ7.stock_endpointG j k hk (by omega) h18 hne d x p good raw s m n domain G S cut input scratch pg ps cross
    prior (NativeJ7.band_clean_gen j (by omega) h18 d x p good raw s m domain _ _ _ cut)


/-- Every interior leaf of the window up to block 20 (start 375). -/
theorem leaves20 : LeavesUpTo 20 :=
  ⟨endpoint20, scratch, roundtrip, keepLeaveG, keepOlderG, NativeFirstJ7.first, NativeFirstJ7.firstBack⟩

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run

/-- The generic hand-off at block 21 is the exit-390 hand-off (pairs, flags, pending, raw ports of block 20). -/
theorem exitBridge390 :
    EnterJ7.lowerPairs ⟨21,by decide⟩=Portal390Flag7.loPairs ∧ EnterJ7.upperPairs ⟨21,by decide⟩=Portal390Flag7.hiPairs ∧
    EnterJ7.gate ⟨21,by decide⟩=405 ∧ EnterJ7.flagN ⟨21,by decide⟩=1633 ∧ EnterJ7.flagF ⟨21,by decide⟩=1631 ∧
    EnterJ7.flagU ⟨21,by decide⟩=1632 ∧ EnterJ7.pending ⟨21,by decide⟩=ParkEndpoint3907.src ∧
    ArchiveJ7.rawPorts ⟨20,by decide⟩ 20=1634 ∧ ArchiveJ7.rawPorts ⟨20,by decide⟩ 21=1635 ∧
    ArchiveJ7.rawPorts ⟨20,by decide⟩ 22=1636 := by
  refine ⟨?_,?_,rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩ <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem exitProg390 (d:Bool) : (exitF Shadow7.params d 390).flatten=NativePack3907.lastWindow d ∧
    (exitR Shadow7.params d 390).flatten=NativePack3907.lastUnwind d := by
  constructor
  · simp only [exitF,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
      NativePack3907.lastWindow,NativePack3907.endSlice,EndTick3907.physP,EndTick3907.P,NativePack3907.program,List.append_assoc]
  · simp only [exitR,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
      NativePack3907.lastUnwind,NativePack3907.endUndo,EndTick3907.physQ,EndTick3907.Q,NativePack3907.reverse,List.append_assoc]

/-- The exit at 390 (dadon's `step270` rendered at 390). -/
theorem exitStep390 (d:Bool) (x:Nat) (good:Bounds x p) :
    Checked (exitF Shadow7.params d (start ⟨20,by decide⟩+15)).flatten
      (exitR Shadow7.params d (start ⟨20,by decide⟩+15)).flatten
      (ReadyW d x p (start ⟨20,by decide⟩+15)) (LastAt ArchiveBoundary3907.codePorts ⟨20,by decide⟩ d x p) := by
  have e390 : start ⟨20,by decide⟩+15=390 := rfl
  rw [e390]
  obtain ⟨ef,er⟩:=exitProg390 d
  rw [ef,er]
  intro s m h
  obtain ⟨k,ek,raw,g,sg,pg,ps,pre⟩:=h
  have k20:k=⟨21,by decide⟩:=Fin.ext (by have := ek; simp only [StairPacket.start] at this; show k.val=21; omega)
  subst k20
  obtain ⟨bl,bu,bg,bn,bf,bu',bp,r20,r21,r22⟩:=exitBridge390
  let z:=unsigned 390 x p
  have short:Shadow7.SmallIfFar 54 15 z:=(Shadow7.Envelope.inputs x p 390 (lt_trans good.small good.cap) good.cap (by decide)).1
  have old:=LeaveJ7.Admission.actualNumbers ⟨20,by decide⟩ (by decide) (by decide) x p good
  have eq:farAt 54 390 x p=(3*2^70≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have cut:=pre.cut
  have e20:start (⟨21,by decide⟩:Fin 23)=390:=rfl
  have sb:Shadow7.sbP 390=54:=by decide
  rw [bl,bu,bg,bn,bf,bu',bp] at cut
  simp only [e20,sb] at cut
  have facts:=pre.facts
  have mode:s.basis 1634=decide (Shadow.far 62 15 (unsigned 375 x p)):=by rw [←r20]; exact facts.far
  have side:s.basis 1635=(decide (Shadow.far 62 15 (unsigned 375 x p)) &&
      StairArchiveTrace.afterFlags (decide ((unsigned 375 x p).v<(unsigned 375 x p).u))
        ((Shadow7.physicalCells ArchiveBoundary3907.sourceIdx s).take 5)):=by rw [←r21]; simpa only [Shadow7.physicalCells_eq] using facts.suffix
  have cross:s.basis 1636=(decide (Shadow.far 62 15 (unsigned 375 x p)) &&
      HighBankSum.cross (LeaveJ7.TrueMiddle.d ⟨20,by decide⟩ (unsigned 375 x p))):=by rw [←r22]; exact facts.crossed
  have last:=NativePack3907.matched_from_domain d x good.nonzero good.small raw s m pre.domain z short g sg
    (readInput 390 x p raw g sg pre.input) (by simpa only [eq] using cut) (unsigned 375 x p) pg ps _
    old.odd old.farSmall (by simpa only [Shadow7.physicalCells_eq] using facts.records) mode side cross
  obtain ⟨r,lim,truth,frame⟩:=last.2.1
  have pc:signedAt 375 x p pg ps=WideReference.canonical 375 x p:=pre.pastCanonical
  have chr:Chronology 375 x p r:=by unfold Chronology;rw [←pc];exact truth
  exact ⟨last.1,⟨r,lim,chr,frame⟩,last.2.2⟩


/-- A wire bound for a whole program from a per-instruction check. -/
theorem wires_bound390 (P : Program) (b : Nat) (h : P.all (fun i => decide (∀ q ∈ i.wires, q < b)) = true) :
    ∀ q ∈ wires P, q < b := by
  induction P with
  | nil => intro q hq; simp [wires] at hq
  | cons i p ih =>
    intro q hq
    simp only [wires, Finset.mem_union] at hq
    simp only [List.all_cons, Bool.and_eq_true] at h
    rcases hq with hq | hq
    · exact of_decide_eq_true h.1 q hq
    · exact ih h.2 q hq

theorem portalInv_low390 : ∀ q ∈ wires (Shadow7.portalInvP 390), q < 1690 :=
  wires_bound390 _ _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem park_low390 : ∀ q ∈ wires (Shadow7.parkP 390), q < 1690 :=
  wires_bound390 _ _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem raw390_ranges : ∀ w ∈ ArchiveBoundary3907.rawPortsList,
    (396 ≤ w ∧ w ≤ 405) ∨ (1680 ≤ w ∧ w ≤ 1689) ∨ (909 ≤ w ∧ w ≤ 911) ∨ (1556 ≤ w ∧ w ≤ 1677) ∨
    (912 ≤ w ∧ w ≤ 923) := by
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

/-- The exit pieces at 390 never touch the window's key cells (blocks first..19; first = block 1, tick 90). -/
theorem keepExit390 : ∀ (i : Fin 23), WindowParams.first.val ≤ i.val → i.val < 20 → ∀ (d:Bool),
    ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i), ∀ (s:State) (m:List Bool),
    (run (exitF Shadow7.params d (start ⟨20,by decide⟩+15)).flatten m s).basis q=s.basis q := by
  intro i h3 h17 d q hq s m
  have hf1 : 1 ≤ WindowParams.first.val := by decide
  have c := key_rangeG i (by omega) q hq
  have si : 90 ≤ start i ∧ start i ≤ 360 := by simp only [StairPacket.start]; omega
  have e390 : start ⟨20,by decide⟩+15=390 := rfl
  rw [e390]
  simp only [exitF, Shadow7.params, ofParts, List.flatten_cons, List.flatten_nil, List.append_nil, run_append, run_take]
  -- exit archive load
  rw [run_preserves_outside (Shadow7.exitLoadP 390 d) _ _ q (fun hit => by
    have r := raw390_ranges q (List.mem_toFinset.mp (ArchiveBoundary3907.load_cover d hit))
    simp only [Wire] at *; omega)]
  -- stock pack at 380
  rw [run_preserves_outside _ _ _ q (fun hit => by
    rw [renameProgram_support] at hit
    obtain ⟨w, hw, e⟩ := Finset.mem_image.mp hit
    have pc := (WindowCovered.pack_cells d 380 (by decide) (by decide)).1 w hw
    obtain ⟨r, r1, r2, er | er⟩ := pc <;> rw [er, OB5.sig_nat] at e <;> unfold OB5.sigNat at e <;>
      rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩ <;> split_ifs at e <;>
      simp only [MappedCompressed.base, Wire] at * <;> omega)]
  -- the stock tick at 390
  have nt : q ∉ wires (renameProgram (OB5.sig 390) (TickRanges.tick base 390)) :=
    EndTick3907.physical_free EndTick3907.P EndTick3907.supports.1 q (by
      apply WideReference.away (by decide)
      rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
      · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)]
        have hn : ∀ n : Nat, 16 ≤ n → n = n - 16 + 16 := fun n h => by omega
        exact ⟨q - 16, by omega, Or.inl (hn q (by omega))⟩
      · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)]
        have hn : ∀ n : Nat, 1044 ≤ n → n = 1028 + (n - 1044) + 16 := fun n h => by omega
        exact ⟨q - 1044, by omega, Or.inr (hn q (by omega))⟩
      · rw [NativeJ7.sig_moved _ _ (Or.inr ⟨by omega, hh⟩)]
        have hn : ∀ n : Nat, n ≤ 1812 → 1301 ≤ 3113 - n → 3113 - n = 1028 + (2069 - n) + 16 := fun n h h' => by omega
        exact ⟨2069 - q, by omega, Or.inr (hn q hh (by omega))⟩)
  rw [run_preserves_outside _ _ _ q nt]
  -- exit portal (inverse) and park
  rw [run_preserves_outside (Shadow7.portalInvP 390) _ _ q (fun hit => by
    have f := portalInv_low390 q hit
    rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
    all_goals
      have f2 := (Shadow7.portal_wires 390 (by decide) (by decide)).2 q hit
      have hr : railP 390 = 123 := by decide
      unfold footP at f2; rw [hr] at f2; simp only [Wire] at *; omega)]
  rw [run_preserves_outside (Shadow7.parkP 390) _ _ q (fun hit => by
    have f := park_low390 q hit
    rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
    all_goals
      have f2 := (Shadow7.park_wires 390 (by decide) (by decide)).1 q hit
      have hr : railP 390 = 123 := by decide
      unfold parkFootP at f2; rw [hr] at f2; simp only [Wire] at *; omega)]

/-- The exit of the window whose last block is 20 (start 375): the exit at 390. -/
theorem exitLeaves390 : ExitLeaves ⟨20,by decide⟩ ArchiveBoundary3907.codePorts :=
  ⟨exitStep390, keepExit390⟩

end ECDSAAdd.Entrant.StairPacket.StockWindowW7

end


section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
/-- The shadow window program unfolds into the fold over the seven-bit pieces (t1hh's ShadowGeometry defines it). -/
theorem assembly (d:Bool) : Shadow7.forward45plus1 d =
    WindowFold.forwardW Shadow7.params d WindowParams.first WindowParams.rest := rfl
theorem unwind_assembly (d:Bool) : Shadow7.reverse45plus1 d =
    WindowFold.reverseW Shadow7.params d WindowParams.first WindowParams.rest := rfl
end ECDSAAdd.Entrant.StairPacket.Shadow7
end
