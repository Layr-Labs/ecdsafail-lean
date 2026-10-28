import ECDSAAdd.Arithmetic.Paper935.FusedRepackAllocation

namespace ECDSAAdd.Arithmetic.Paper935

/-- Source circuit.py, HMR935, pin64b5a13; logical allocation excludes free home slots.
This snapshot is not asserted to equal compileAuthorWalk output. -/
def s2SourceLive : Finset Wire :=
  arenaWires.filter (fun q =>
    (4 ≤ q ∧ q < 512) ∨
    (768 ≤ q ∧ q < 779) ∨
    (780 ≤ q ∧ q < 784) ∨
    (786 ≤ q ∧ q < 790) ∨
    (791 ≤ q ∧ q < 793) ∨
    (794 ≤ q ∧ q < 801) ∨
    (802 ≤ q ∧ q < 806) ∨
    (807 ≤ q ∧ q < 808) ∨
    (809 ≤ q ∧ q < 811) ∨
    (812 ≤ q ∧ q < 815) ∨
    (816 ≤ q ∧ q < 821) ∨
    (822 ≤ q ∧ q < 829) ∨
    (832 ≤ q ∧ q < 842) ∨
    (843 ≤ q ∧ q < 877) ∨
    (878 ≤ q ∧ q < 879) ∨
    (880 ≤ q ∧ q < 882) ∨
    (883 ≤ q ∧ q < 885) ∨
    (886 ≤ q ∧ q < 894) ∨
    (895 ≤ q ∧ q < 901) ∨
    (902 ≤ q ∧ q < 913) ∨
    (914 ≤ q ∧ q < 915) ∨
    (918 ≤ q ∧ q < 919) ∨
    (920 ≤ q ∧ q < 921) ∨
    (925 ≤ q ∧ q < 927) ∨
    (929 ≤ q ∧ q < 930))

theorem s2SourceLive_bounded : s2SourceLive⊆arenaWires :=
  Finset.filter_subset _ _

def s2SourceArena : Arena := ⟨s2SourceLive,s2SourceLive_bounded⟩

def s2SourceRepack : List (Wire × Wire) := [(787, 0), (817, 1), (788, 2), (804, 3)]

theorem s2SourceRepack_checked :
    (s2SourceArena.checkRepack s2SourceRepack).isSome = true := by
  simp [Arena.checkRepack, s2SourceRepack, s2SourceArena,
    Arena.reserve, Arena.retireSet, s2SourceLive, arenaWires,
    Finset.disjoint_singleton_right]

/-- Source circuit.py, HMR935, pin64b5a13; logical allocation excludes free home slots.
This snapshot is not asserted to equal compileAuthorWalk output. -/
def s6SourceLive : Finset Wire :=
  arenaWires.filter (fun q =>
    (4 ≤ q ∧ q < 256) ∨
    (512 ≤ q ∧ q < 778) ∨
    (779 ≤ q ∧ q < 782) ∨
    (783 ≤ q ∧ q < 786) ∨
    (787 ≤ q ∧ q < 789) ∨
    (792 ≤ q ∧ q < 798) ∨
    (799 ≤ q ∧ q < 800) ∨
    (801 ≤ q ∧ q < 810) ∨
    (811 ≤ q ∧ q < 816) ∨
    (818 ≤ q ∧ q < 820) ∨
    (821 ≤ q ∧ q < 825) ∨
    (826 ≤ q ∧ q < 828) ∨
    (829 ≤ q ∧ q < 830) ∨
    (831 ≤ q ∧ q < 832) ∨
    (833 ≤ q ∧ q < 842) ∨
    (843 ≤ q ∧ q < 854) ∨
    (855 ≤ q ∧ q < 857) ∨
    (858 ≤ q ∧ q < 859) ∨
    (861 ≤ q ∧ q < 865) ∨
    (866 ≤ q ∧ q < 873) ∨
    (874 ≤ q ∧ q < 875) ∨
    (877 ≤ q ∧ q < 882) ∨
    (883 ≤ q ∧ q < 898) ∨
    (899 ≤ q ∧ q < 903) ∨
    (904 ≤ q ∧ q < 914) ∨
    (917 ≤ q ∧ q < 920) ∨
    (921 ≤ q ∧ q < 928) ∨
    (930 ≤ q ∧ q < 931) ∨
    (932 ≤ q ∧ q < 933))

theorem s6SourceLive_bounded : s6SourceLive⊆arenaWires :=
  Finset.filter_subset _ _

def s6SourceArena : Arena := ⟨s6SourceLive,s6SourceLive_bounded⟩

def s6SourceRepack : List (Wire × Wire) := [(793, 0), (833, 1), (927, 2), (856, 3)]

theorem s6SourceRepack_checked :
    (s6SourceArena.checkRepack s6SourceRepack).isSome = true := by
  simp [Arena.checkRepack, s6SourceRepack, s6SourceArena,
    Arena.reserve, Arena.retireSet, s6SourceLive, arenaWires,
    Finset.disjoint_singleton_right]

def s2SourceAfter : Arena :=
  (s2SourceArena.checkRepack s2SourceRepack).get s2SourceRepack_checked

theorem s2SourceRepack_eq :
    s2SourceArena.checkRepack s2SourceRepack = some s2SourceAfter :=
  Option.eq_some_of_isSome s2SourceRepack_checked

theorem s2SourceRepack_valid :
    ∀ p∈s2SourceRepack, p.1≠p.2 ∧ p.1∈arenaWires ∧ p.2∈arenaWires :=
  Arena.checkRepack_valid _ _ _ s2SourceRepack_eq

/-- Conditional on physical readiness of the source snapshot, all tape
executions preserve readiness. No compiled-walk correspondence is assumed. -/
theorem s2SourceRepack_ready (s : State) (m : List Bool)
    (ready : s2SourceArena.Ready s.basis) :
    s2SourceAfter.Ready (run (repack s2SourceRepack) m s).basis :=
  Arena.checkRepack_ready _ _ _ s2SourceRepack_eq s m ready

theorem s2SourceRepack_live :
    s2SourceAfter.live = s2SourceLive.image (repackEquiv s2SourceRepack) :=
  Arena.checkRepack_live _ _ _ s2SourceRepack_eq

def s6SourceAfter : Arena :=
  (s6SourceArena.checkRepack s6SourceRepack).get s6SourceRepack_checked

theorem s6SourceRepack_eq :
    s6SourceArena.checkRepack s6SourceRepack = some s6SourceAfter :=
  Option.eq_some_of_isSome s6SourceRepack_checked

theorem s6SourceRepack_valid :
    ∀ p∈s6SourceRepack, p.1≠p.2 ∧ p.1∈arenaWires ∧ p.2∈arenaWires :=
  Arena.checkRepack_valid _ _ _ s6SourceRepack_eq

/-- Conditional on physical readiness of the source snapshot, all tape
executions preserve readiness. No compiled-walk correspondence is assumed. -/
theorem s6SourceRepack_ready (s : State) (m : List Bool)
    (ready : s6SourceArena.Ready s.basis) :
    s6SourceAfter.Ready (run (repack s6SourceRepack) m s).basis :=
  Arena.checkRepack_ready _ _ _ s6SourceRepack_eq s m ready

theorem s6SourceRepack_live :
    s6SourceAfter.live = s6SourceLive.image (repackEquiv s6SourceRepack) :=
  Arena.checkRepack_live _ _ _ s6SourceRepack_eq

end ECDSAAdd.Arithmetic.Paper935
