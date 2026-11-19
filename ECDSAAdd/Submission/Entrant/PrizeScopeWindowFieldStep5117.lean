import ECDSAAdd.Submission.Entrant.PrizeScopeWindowFieldRelation99df
import ECDSAAdd.Submission.Entrant.PrizeScopeWindowFieldRestore6ae6
import ECDSAAdd.Submission.Entrant.PrizeScopeWindowFieldTen933e

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
open Arithmetic MappedCompressed ArchiveFieldScratch StairArchiveInactive StairArchiveNativeCut StairArchiveRelease
def slots (j : Nat) := (List.range 16).map (fieldPort j)
def banks := [46,49,52]
def allowed (j k : Nat) := k=j || k=j+1 || (slots j).all (fun q => !(cover k).contains (preimage k q))
def apart (j h : Nat) := j=h || (slots h).all (fun q => !(StairArchiveRelease.fieldSites j).contains q)
def part (h offset count : Nat) := (List.range' offset count).all (allowed h)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck


end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h46_1 : part 46 1 7 = true := by decide +kernel
theorem h46_8 : part 46 8 7 = true := by decide +kernel
theorem h46_15 : part 46 15 7 = true := by decide +kernel
theorem h46_22 : part 46 22 7 = true := by decide +kernel
theorem h46_29 : part 46 29 7 = true := by decide +kernel
theorem h46_36 : part 46 36 7 = true := by decide +kernel
theorem h46_43 : part 46 43 7 = true := by decide +kernel
theorem h46_50 : part 46 50 7 = true := by decide +kernel
theorem h46_57 : part 46 57 7 = true := by decide +kernel
theorem h46_64 : part 46 64 7 = true := by decide +kernel
theorem h46_71 : part 46 71 7 = true := by decide +kernel
theorem h46_78 : part 46 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck


end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h49_1 : part 49 1 7 = true := by decide +kernel
theorem h49_8 : part 49 8 7 = true := by decide +kernel
theorem h49_15 : part 49 15 7 = true := by decide +kernel
theorem h49_22 : part 49 22 7 = true := by decide +kernel
theorem h49_29 : part 49 29 7 = true := by decide +kernel
theorem h49_36 : part 49 36 7 = true := by decide +kernel
theorem h49_43 : part 49 43 7 = true := by decide +kernel
theorem h49_50 : part 49 50 7 = true := by decide +kernel
theorem h49_57 : part 49 57 7 = true := by decide +kernel
theorem h49_64 : part 49 64 7 = true := by decide +kernel
theorem h49_71 : part 49 71 7 = true := by decide +kernel
theorem h49_78 : part 49 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck


end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h52_1 : part 52 1 7 = true := by decide +kernel
theorem h52_8 : part 52 8 7 = true := by decide +kernel
theorem h52_15 : part 52 15 7 = true := by decide +kernel
theorem h52_22 : part 52 22 7 = true := by decide +kernel
theorem h52_29 : part 52 29 7 = true := by decide +kernel
theorem h52_36 : part 52 36 7 = true := by decide +kernel
theorem h52_43 : part 52 43 7 = true := by decide +kernel
theorem h52_50 : part 52 50 7 = true := by decide +kernel
theorem h52_57 : part 52 57 7 = true := by decide +kernel
theorem h52_64 : part 52 64 7 = true := by decide +kernel
theorem h52_71 : part 52 71 7 = true := by decide +kernel
theorem h52_78 : part 52 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck


end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
open Arithmetic MappedCompressed ArchiveFieldScratch StairArchiveInactive StairArchiveNativeCut StairArchiveRelease WindowFieldMask
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 100000
private theorem splitRange : List.range' 1 84 = List.range' 1 7 ++ List.range' 8 7 ++ List.range' 15 7 ++ List.range' 22 7 ++ List.range' 29 7 ++ List.range' 36 7 ++ List.range' 43 7 ++ List.range' 50 7 ++ List.range' 57 7 ++ List.range' 64 7 ++ List.range' 71 7 ++ List.range' 78 7 := by decide +kernel
attribute [local irreducible] allowed fieldPort packet cover preimage
private theorem pass46 : (List.range' 1 84).all (allowed 46)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h46_1,h46_8⟩,h46_15⟩,h46_22⟩,h46_29⟩,h46_36⟩,h46_43⟩,h46_50⟩,h46_57⟩,h46_64⟩,h46_71⟩,h46_78⟩
private theorem pass49 : (List.range' 1 84).all (allowed 49)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h49_1,h49_8⟩,h49_15⟩,h49_22⟩,h49_29⟩,h49_36⟩,h49_43⟩,h49_50⟩,h49_57⟩,h49_64⟩,h49_71⟩,h49_78⟩
private theorem pass52 : (List.range' 1 84).all (allowed 52)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h52_1,h52_8⟩,h52_15⟩,h52_22⟩,h52_29⟩,h52_36⟩,h52_43⟩,h52_50⟩,h52_57⟩,h52_64⟩,h52_71⟩,h52_78⟩
private theorem pass (h : Nat) (hm : h ∈ banks) : (List.range' 1 84).all (allowed h) = true := by
  simp only [banks,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl
  · exact pass46
  · exact pass49
  · exact pass52

theorem packet_free (h k : Nat) (hm : h∈banks) (km : k∈List.range' 1 84)
    (not0 : k≠h) (not1 : k≠h+1) (d : Bool) : avoids (packet d k) (bank h) := by
  have once := List.all_eq_true.mp (pass h hm) k km
  simp only [allowed, decide_eq_false not0, decide_eq_false not1, Bool.false_or] at once
  intro q member used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp member
  have qmem : fieldPort h i ∈ slots h := List.mem_map.mpr ⟨i,List.mem_range.mpr (Finset.mem_range.mp hi),rfl⟩
  have outside := List.all_eq_true.mp once _ qmem
  have limit := (List.mem_range'_1.mp km).2
  have inside := original d k (by omega) used
  simp [inside] at outside

private def distinct (j h : Nat) := j=h || (slots h).all (fun q =>
  !((List.range 121).map (fieldPort j)).contains q)
private theorem distinct_ok : banks.all (fun j=>banks.all (distinct j))=true := by decide +kernel

theorem separate (j h : Nat) (jm : j∈banks) (hm : h∈banks) (ne : j≠h) :
    ∀ q∈inside j, q∉bank h := by
  have ok := List.all_eq_true.mp (List.all_eq_true.mp distinct_ok j jm) h hm
  simp only [distinct, decide_eq_false ne, Bool.false_or] at ok
  intro q own other
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp other
  have qmem : fieldPort h i ∈ slots h := List.mem_map.mpr ⟨i,List.mem_range.mpr (Finset.mem_range.mp hi),rfl⟩
  have outside := List.all_eq_true.mp ok _ qmem
  have inside' : fieldPort h i ∈ (List.range 121).map (fieldPort j) := by
    obtain ⟨t,ht,eq⟩ := Finset.mem_image.mp own
    exact List.mem_map.mpr ⟨t,List.mem_range.mpr (Finset.mem_range.mp ht),eq⟩
  simp [inside'] at outside
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck


end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify
set_option maxRecDepth 1600
set_option maxHeartbeats 400000
attribute [local irreducible] run packet fieldPort StairArchiveNativeCut.canonical inputCols outputCols CodecBitSliceVerify.get

private theorem memberList {j : Nat} (h : j∈bankIds) : j∈WindowBankCheck.banks := by
  simpa [bankIds,WindowBankCheck.banks] using h
private theorem geometry {j : Nat} (h : j∈bankIds) : j∈starts ∧ j∈List.range' 1 83 := by
  simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl|rfl|rfl <;> decide
private theorem apart {j : Nat} (hj : j∈bankIds) : ∀ q∈inside j, q∉others j := by
  intro q hi ho
  obtain ⟨k,hk,mem⟩ := Finset.mem_biUnion.mp ho
  obtain ⟨ne,kid⟩ := Finset.mem_erase.mp hk
  exact WindowBankCheck.separate j k (memberList hj) (memberList kid) ne.symm q hi mem
private theorem native_safe (j k : Nat) (hj : j∈bankIds) (which : k=j ∨ k=j+1) (d : Bool) :
    avoids (packet d k) (others j) := by
  intro q ho used
  obtain ⟨h,hm,mem⟩ := Finset.mem_biUnion.mp ho
  obtain ⟨ne,hid⟩ := Finset.mem_erase.mp hm
  apply WindowBankCheck.packet_free h k (memberList hid) _ _ _ d q mem used
  all_goals simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at hj hid
  · apply List.mem_range'_1.mpr; omega
  all_goals omega
private theorem hook_safe (j : Nat) (hj : j∈bankIds) (s : Stage) :
    avoids (fieldHook j s) (others j) := by
  intro q ho used
  rw [fieldHook,renameProgram_support] at used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp used
  exact apart hj _ (Finset.mem_image.mpr ⟨i,sub s hi,rfl⟩) ho
private theorem append_safe {P Q : Program} {W : Finset Wire} (p : avoids P W) (q : avoids Q W) :
    avoids (P++Q) W := by
  intro i hi used
  rw [wires_append, Finset.mem_union] at used
  exact used.elim (p i hi) (q i hi)

def update (code : Nat→Cols) (j : Nat) (out : Cols) := fun k => if k=j then out else code k
attribute [local irreducible] inside StairArchiveRelease.fieldHook
  StairArchiveTen.first StairArchiveTen.second StairArchiveTen.ten

theorem stepTen (j : Nat) (hj : j∈bankIds) (rows : Nat→Nat) (code : Nat→Cols) (rev : Bool)
    (bound : rows j < 63145) (m : List Bool) (a r : State) (h : Fits rows code a r)
    (active : code j=inputCols (enter rev))
    (before_ : frame j (rows j) (StairArchiveNativeCut.canonical (!rev) (!rev)) r)
    (middle_ : frame j (rows j) middle (refMiddle j rev m r))
    (after_ : frame j (rows j) (StairArchiveNativeCut.canonical rev rev) (refExit j rev m r)) :
    Fits rows (update code j (outputCols (leave rev))) (run (ten j rev) m a) (refExit j rev m r) := by
  have ⟨hs,hr⟩ := geometry hj
  have fa : avoids (first j rev) (others j) := by
    rw [first]; apply native_safe _ _ hj; cases rev <;> simp
  have sa : avoids (second j rev) (others j) := by
    rw [second]; apply native_safe _ _ hj; cases rev <;> simp
  have ea : avoids (ten j rev) (others j) := by
    rw [ten]; exact append_safe (hook_safe j hj _)
      (append_safe fa (append_safe (hook_safe j hj _) (append_safe sa (hook_safe j hj _))))
  have same : offBanks (bank j) (others j) a r := by
    intro q a0 a1; apply h.outside; rw [decompose j hj,Finset.mem_union]; exact fun hit => hit.elim a0 a1
  have result := ten_masked j hs hr rev (rows j) bound m a r (others j) (apart hj) fa sa
    (beforeFrame j hj rows code rev a r h active (apart hj) before_ (field_inj j hr)) same h.phase before_ middle_ after_
  refine ⟨result.1,?_,?_⟩
  · intro q off
    rw [decompose j hj,Finset.mem_union] at off
    exact result.2.1 q (fun a=>off (Or.inl a)) (fun b=>off (Or.inr b))
  · intro k hk i hi
    by_cases eq : k=j
    · subst k
      simpa only [update,if_pos rfl] using result.2.2 i (Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega))
    · have ho : fieldPort k i∈others j := Finset.mem_biUnion.mpr
        ⟨k,Finset.mem_erase.mpr ⟨eq,hk⟩,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
      rw [run_preserves_outside _ m a _ (ea _ ho)]
      simpa only [update,if_neg eq] using h.bytes k hk i hi
end ECDSAAdd.Entrant.StairPacket.WindowFieldMask


end
