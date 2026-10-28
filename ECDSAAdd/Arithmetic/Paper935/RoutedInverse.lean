import ECDSAAdd.Arithmetic.Paper935.RowStageInverse
import ECDSAAdd.Arithmetic.Paper935.RoutedStage

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

theorem copyRegister_proper (ctrl : Option Wire) (a b : List Wire)
    (hn : (a++b).Nodup) (hc : ∀ c,ctrl=some c → c∉b) :
    ProperProgram (copyRegister ctrl a b) := by
  induction a generalizing b with
  | nil => simp [copyRegister,ProperProgram]
  | cons x xs ih =>
    cases b with
    | nil => simp [copyRegister,ProperProgram]
    | cons y ys =>
      have hxy : x≠y := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
      have ht : (xs++ys).Nodup := by
        apply List.nodup_iff_count.mpr
        intro w
        have h := List.nodup_iff_count.mp hn w
        simp only [List.count_cons,List.count_append] at h ⊢
        omega
      rw [copyRegister,properProgram_append]
      refine ⟨?_,ih ys ht (fun c he hw => hc c he (by simp [hw]))⟩
      cases ctrl with
      | none => simpa [ProperProgram,ProperGate,copyGate] using hxy
      | some c =>
        have hcy : c≠y := fun h => hc c rfl (by simp [h])
        simpa [ProperProgram,ProperGate,copyGate] using And.intro hcy hxy

theorem routeRows_proper (c : Wire) (f g fv gv : List Wire)
    (hn : (c::((f++fv)++(g++gv))).Nodup) :
    ProperProgram (routeRows c f g fv gv) := by
  have hnd := (List.nodup_cons.mp hn).2
  have hrev : ((g++gv)++(f++fv)).Nodup := by rwa [List.nodup_append_comm]
  have hnone := copyRegister_proper none (g++gv) (f++fv) hrev (by simp)
  have hsome := copyRegister_proper (some c) (f++fv) (g++gv) hnd (by
    intro d he
    cases he
    exact fun hw => (List.nodup_cons.mp hn).1 (List.mem_append_right _ hw))
  simp only [routeRows,swapRegisters,properProgram_append]
  exact ⟨⟨hnone,hsome⟩,hnone⟩

def routedStageInverse (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire) : Program :=
  rowStageInverse q parity u k active glow gsign vlow vsign f gmid vmid gv ++
    (routeRows q f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv).reverse

theorem routedStage_roundtrip (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire)
    (hn1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).Nodup)
    (hn2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).Nodup)
    (hgn : (glow::(gmid++[gsign])).Nodup)
    (hvn : (active::vlow::(vmid++[vsign])).Nodup)
    (hl1 : f.length=gmid.length+2) (hl2 : gv.length=vmid.length+2)
    (hr : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup)
    (s : State) (m n : List Bool) (hu : s.basis u=false) (hk : s.basis k=false) :
    run (routedStageInverse q parity u k active glow gsign vlow vsign f gmid vmid gv) n
      (run (routedStage q parity u k active glow gsign vlow vsign f gmid vmid gv) m s)=s := by
  have nd1 := hn1
  have nd2 := hn2
  simp only [List.nodup_cons,List.mem_cons,not_or] at nd1 nd2
  have outside (w : Wire) (h1 : w∉f++(glow::(gmid++[gsign])))
      (h2 : w∉(vlow::(vmid++[vsign]))++gv) :
      w∉f++(vlow::(vmid++[vsign])) ∧ w∉(glow::(gmid++[gsign]))++gv := by
    simp only [List.mem_append,not_or] at h1 h2 ⊢
    exact ⟨⟨h1.1,h2.1⟩,h1.2,h2.2⟩
  have ou := outside u nd1.2.2.1.2 nd2.2.2.1.2
  have ok := outside k nd1.2.2.2.1 nd2.2.2.2.1
  have frame := (routeRows_correct q f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv (by simpa using hl1) (by simpa using hl2.symm) hr s m).2.1
  rw [routedStage,routedStageInverse,run_append,run_take,run_append,run_take]
  rw [rowStage_roundtrip q parity u k active glow gsign vlow vsign f gmid vmid gv
    hn1 hn2 hgn hvn hl1 hl2 _ _ n ((frame u ou.1 ou.2).trans hu) ((frame k ok.1 ok.2).trans hk)]
  exact run_reverse_proper _ (routeRows_proper _ _ _ _ _ hr) s m _

end ECDSAAdd.Arithmetic.Paper935
