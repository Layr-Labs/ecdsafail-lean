import ECDSAAdd.Arithmetic.Paper935.BranchInverse
import ECDSAAdd.Arithmetic.Paper935.RowStage

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

theorem shiftLeft_proper (c : Wire) (r : List Wire) (hn : (c::r).Nodup) :
    ProperProgram (shiftLeft c r) := by
  induction r with
  | nil => simp [shiftLeft,ProperProgram]
  | cons a r ih =>
    cases r with
    | nil => simp [shiftLeft,ProperProgram]
    | cons b bs =>
      have ht : (c::b::bs).Nodup := List.nodup_cons.mpr
        ⟨fun h => (List.nodup_cons.mp hn).1 (List.mem_cons_of_mem _ h),
          (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2⟩
      have nd := hn
      simp only [List.nodup_cons,List.mem_cons,not_or] at nd
      rw [shiftLeft,properProgram_append]
      exact ⟨ih ht,by simp [cswap,ProperProgram,ProperGate,nd.1.2.1,nd.2.1.1,Ne.symm]⟩

theorem finishRows_proper (active glow gsign vlow vsign : Wire) (vmid : List Wire)
    (hn : (active::vlow::(vmid++[vsign])).Nodup) (hg : gsign≠glow) :
    ProperProgram (finishRows active glow gsign vlow vsign vmid) := by
  have ha : active≠vlow := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hs : vsign≠vlow := by
    intro h
    exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [←h])
  simp only [finishRows,doubleSigned,properProgram_append]
  exact ⟨⟨shiftLeft_proper _ _ hn,by simp [ProperProgram,ProperGate,ha,hs]⟩,
    by simpa [skywalkSignedHalf,ProperProgram,ProperGate] using hg⟩

def rowStageInverse (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire) : Program :=
  (finishRows active glow gsign vlow vsign vmid).reverse ++
    branchPairInverse q parity u k f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv

theorem rowStage_roundtrip (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire)
    (hn1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).Nodup)
    (hn2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).Nodup)
    (hgn : (glow::(gmid++[gsign])).Nodup)
    (hvn : (active::vlow::(vmid++[vsign])).Nodup)
    (hl1 : f.length=gmid.length+2) (hl2 : gv.length=vmid.length+2)
    (s : State) (m n : List Bool) (hu : s.basis u=false) (hk : s.basis k=false) :
    run (rowStageInverse q parity u k active glow gsign vlow vsign f gmid vmid gv) n
      (run (rowStage q parity u k active glow gsign vlow vsign f gmid vmid gv) m s)=s := by
  have hgs : gsign≠glow := by
    intro h
    exact (List.nodup_cons.mp hgn).1 (by simp [←h])
  have proper := finishRows_proper active glow gsign vlow vsign vmid hvn hgs
  rw [rowStage,rowStageInverse,run_append,run_take,run_append,run_take]
  rw [run_reverse_proper _ proper]
  exact branchPair_roundtrip q parity u k f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv hn1 hn2 (by simpa using hl1)
    (by simpa using hl2.symm) s m _ hu hk

end ECDSAAdd.Arithmetic.Paper935
