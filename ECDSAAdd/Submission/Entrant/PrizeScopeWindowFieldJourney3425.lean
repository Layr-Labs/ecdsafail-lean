import ECDSAAdd.Submission.Entrant.PrizeScopeWindowFieldRelation99df
import ECDSAAdd.Submission.Entrant.PrizeScopeWindowFieldStep5117

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveInactive WindowFieldCosts
attribute [local irreducible] packet run allBanks
def nativeRanges (j n : Nat) := (j=1 ∧ n=45) ∨ (j=48 ∧ n=1) ∨ (j=51 ∧ n=1) ∨ (j=54 ∧ n=31)
private theorem disjointRange {j n k h : Nat} (valid : nativeRanges j n) (hk : j≤k ∧ k<j+n)
    (isBank : h∈bankIds) : k∈List.range' 1 84 ∧ k≠h ∧ k≠h+1 := by
  simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at isBank
  unfold nativeRanges at valid
  rw [List.mem_range'_1]; omega
private theorem seqSafe (d : Bool) (j n : Nat)
    (h : ∀ k, j≤k → k<j+n → avoids (packet d k) allBanks) :
    avoids (PacketSequence.program d (packet d) j n) allBanks := by
  induction n generalizing j with
  | zero =>
    intro q _ used; simp [PacketSequence.program,wires] at used
  | succ n ih =>
    have head := h j (by omega) (by omega)
    have tail := ih (j+1) (fun k l u=>h k (by omega) (by omega))
    intro q inbank used
    cases d <;> simp only [PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union] at used
    · exact used.elim (tail q inbank) (head q inbank)
    · exact used.elim (head q inbank) (tail q inbank)
theorem groupSafe (d : Bool) (j n : Nat) (valid : nativeRanges j n) : avoids (group d j n) allBanks := by
  rw [group,distribute]
  apply seqSafe
  intro k lower upper q mem used
  rw [allBanks] at mem
  obtain ⟨h,hm,hq⟩ := Finset.mem_biUnion.mp mem
  have triple := disjointRange valid ⟨lower,upper⟩ hm
  have hlist : h∈WindowBankCheck.banks := by simpa [bankIds,WindowBankCheck.banks] using hm
  exact WindowBankCheck.packet_free h k hlist triple.1 triple.2.1 triple.2.2 d q hq used
end ECDSAAdd.Entrant.StairPacket.WindowFieldMask


end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveTen
open CodecBitSliceVerify WindowFieldMask WindowFieldCosts ArchiveFieldScratch
attribute [local irreducible] run measurementCount WindowFieldCosts.group StairArchiveTen.ten refExit
  inputCols outputCols StairArchiveNativeCut.canonical enter leave
inductive Leg where
  | native (j n : Nat)
  | paired (j : Nat)
def emitted (d : Bool) : Leg → Program
  | .native j n => group d j n
  | .paired j => ten j (!d)
def stock (d : Bool) (m : List Bool) (r : State) : Leg → State
  | .native j n => run (group d j n) m r
  | .paired j => refExit j (!d) m r
def codes (d : Bool) (c : Nat→Cols) : Leg → Nat→Cols
  | .native _ _ => c
  | .paired j => update c j (outputCols (leave (!d)))
def nextTape (d : Bool) (l : Leg) (m : List Bool) := m.drop (measurementCount (emitted d l))
def concatenate (d : Bool) : List Leg → Program
  | [] => []
  | l::ls => emitted d l ++ concatenate d ls
def destination (d : Bool) : List Leg → List Bool → State → State
  | [],_,r => r
  | l::ls,m,r => destination d ls (nextTape d l m) (stock d m r l)
def finalCode (d : Bool) : List Leg → (Nat→Cols) → Nat→Cols
  | [],c => c
  | l::ls,c => finalCode d ls (codes d c l)
def validLeg (d : Bool) (c : Nat→Cols) : Leg → Prop
  | .native j n => nativeRanges j n
  | .paired j => j∈bankIds ∧ c j=inputCols (enter (!d))
def valid (d : Bool) : List Leg → (Nat→Cols) → Prop
  | [],_ => True
  | l::ls,c => validLeg d c l ∧ valid d ls (codes d c l)
def Cuts (d : Bool) (row : Nat→Nat) (m : List Bool) (r : State) : Leg → Prop
  | .native _ _ => True
  | .paired j => frame j (row j) (StairArchiveNativeCut.canonical d d) r ∧
      frame j (row j) middle (refMiddle j (!d) m r) ∧ frame j (row j) (StairArchiveNativeCut.canonical (!d) (!d)) (refExit j (!d) m r)
def NativeTrail (d : Bool) (row : Nat→Nat) : List Leg → List Bool → State → Prop
  | [],_,_ => True
  | l::ls,m,r => Cuts d row m r l ∧ NativeTrail d row ls (nextTape d l m) (stock d m r l)

theorem travel (d : Bool) (row : Nat→Nat) (bounded : ∀j∈bankIds,row j<63145)
    (ls : List Leg) (m : List Bool) (a r : State) (c : Nat→Cols)
    (shape : valid d ls c) (cuts : NativeTrail d row ls m r) (initial : Fits row c a r) :
    Fits row (finalCode d ls c) (run (concatenate d ls) m a) (destination d ls m r) := by
  induction ls generalizing c m a r with
  | nil =>
    simpa only [concatenate,run,finalCode,destination] using initial
  | cons l ls ih =>
    obtain ⟨loc,tail⟩ := shape
    obtain ⟨here,rest⟩ := cuts
    have one : Fits row (codes d c l) (run (emitted d l) m a) (stock d m r l) := by
      cases l with
      | native j n => exact plain _ _ _ _ _ _ initial (groupSafe d j n loc)
      | paired j =>
        exact stepTen j loc.1 row c (!d) (bounded j loc.1) m a r initial loc.2
          (by simpa only [Bool.not_not] using here.1) here.2.1 here.2.2
    rw [concatenate,run_append,run_take]
    exact ih _ _ _ _ tail rest one

def plan : Bool→List Leg
  | true => [.native 1 45,.paired 46,.native 48 1,.paired 49,.native 51 1,.paired 52,.native 54 31]
  | false => [.native 54 31,.paired 52,.native 51 1,.paired 49,.native 48 1,.paired 46,.native 1 45]
def initialCode (d : Bool) : Nat→Cols := fun _=>inputCols (enter (!d))
private theorem emits (d : Bool) : group84 d=concatenate d (plan d) := by
  cases d <;> simp only [group84,ordered,concatenate,emitted,plan,if_true,if_false,Bool.false_eq_true,
    List.append_assoc,List.append_nil]
private theorem valid_plan (d : Bool) : valid d (plan d) (initialCode d) := by
  cases d <;> simp [valid,plan,validLeg,nativeRanges,bankIds,codes,update,initialCode]
theorem group_run (d : Bool) (row : Nat→Nat) (bounded : ∀j∈bankIds,row j<63145)
    (m : List Bool) (a r : State) (initial : Fits row (initialCode d) a r)
    (native : NativeTrail d row (plan d) m r) :
    Fits row (finalCode d (plan d) (initialCode d)) (run (group84 d) m a) (destination d (plan d) m r) := by
  rw [emits]
  exact travel d row bounded _ m a r _ (valid_plan d) native initial
end ECDSAAdd.Entrant.StairPacket.WindowFieldJourney


end
