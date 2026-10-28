import ECDSAAdd.Arithmetic.Paper935.DepthCompilerTotal
import ECDSAAdd.Arithmetic.Paper935.BorrowGeometry

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileDepthList_separated (one frozen output : Wire) (z f v work : List Wire)
    (depths : List Nat) (hz : z.length=7) (hf : 7≤f.length) (hv : 13≤v.length)
    (hw : work.length=11) (hd : ∀ d∈depths,2≤d ∧ d≤6)
    (hn : ([one,frozen,output]++z++f++v++work).Nodup) :
    ∃ layouts,compileDepthList one frozen output z f v work depths=some layouts := by
  induction depths with
  | nil => exact ⟨[],rfl⟩
  | cons d ds ih =>
    obtain ⟨L,hL⟩ := compileDepth_separated one frozen output z f v work d hz hf hv hw
      (hd d (by simp)) hn
    obtain ⟨ls,hls⟩ := ih (fun e he => hd e (List.mem_cons_of_mem _ he))
    exact ⟨L::ls,by simp [compileDepthList,hL,hls]⟩

theorem compileBorrowedDepths_exists (A : Arena) (one frozen output : Wire) (z f v : List Wire)
    (hz : z.length=7) (hf : 7≤f.length) (hv : 13≤v.length)
    (hn : ([one,frozen,output]++z++f++v).Nodup)
    (owned : ([one,frozen,output]++z++f++v).toFinset⊆A.live)
    (budget : A.live.card+11≤935) :
    ∃ D work layouts,compileBorrowedDepths A one frozen output z f v=some (D,work,layouts) := by
  obtain ⟨D,work,borrow⟩ := (A.borrowMany_capacity 11).mpr budget
  have geom := A.borrowMany_append D 11 work _ borrow hn owned
  have len := (A.borrowMany_contract D 11 work borrow).1
  obtain ⟨ls,hls⟩ := compileDepthList_separated one frozen output z f v work [2,3,4,5,6]
    hz hf hv len (by intro d hd; simp only [List.mem_cons,List.not_mem_nil,or_false] at hd; omega)
    (by simpa only [List.append_assoc] using geom.1)
  exact ⟨D,work,ls,by simp [compileBorrowedDepths,borrow,hls]⟩

end ECDSAAdd.Arithmetic.Paper935
