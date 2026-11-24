import ECDSAAdd.Framework.Syntax
import ECDSAAdd.Submission.Entrant.Stair44Stock
import ECDSAAdd.Submission.Entrant.TickCut
import ECDSAAdd.Framework.Semantics
import ECDSAAdd.Framework.WireRenamePool

-- ==== begin FlagLeave + DeadScan (credited to spariev 65b176b3) ====
section
namespace ECDSAAdd.Entrant.StairPacket.FlagLeave
open Arithmetic GateMirror Partial
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def hit (f u l : Wire) (g : Gate) : Bool :=
  decide (g = .make f u l ∨ g = .pop f u l)

def cut (f u l : Wire) : Nat → List Gate → List Gate
  | 0, gs => gs
  | _+1, [] => []
  | n+1, g::gs => if hit f u l g then .cx u l :: cut f u l n gs
      else g :: cut f u l (n+1) gs

/-- Track the temporary far-flag XOR between its matching adjust gates. -/
def check (f u c l : Wire) : Nat → Bool → List Gate → Bool
  | 0, _, _ => true
  | _+1, _, [] => true
  | n+1, shifted, g::gs =>
    if hit f u l g then !shifted && check f u c l n shifted gs
    else if target g = f then
      if g = .cx c f then check f u c l (n+1) (!shifted) gs else false
    else if target g = u ∨ (shifted = true ∧ target g = c) then false
    else check f u c l (n+1) shifted gs

def Rel (f u c : Wire) (shifted : Bool) (s : State) : Prop :=
  ((s.basis f ^^ (shifted && s.basis c)) && s.basis u) = s.basis u

private theorem transition_frame (g : Gate) (s : State) (q : Wire) (hq : q ≠ target g) :
    (transition g s).basis q = s.basis q := by
  cases g <;> simp_all [transition,front,erase,run,measureAndCorrect,writeBit,target]

private theorem transition_cut (f u l : Wire) (g : Gate) (s : State)
    (hf : f ≠ l) (hu : u ≠ l) (hg : hit f u l g = true)
    (rel : (s.basis f && s.basis u) = s.basis u)
    (ok : ValueOK s g) :
    transition (.cx u l) s = transition g s := by
  have h := of_decide_eq_true hg
  rcases h with rfl | rfl
  · simp only [transition,front,run,rel]
  · change s.basis l = (s.basis f && s.basis u) at ok
    rw [rel] at ok
    simp [transition,front,erase,run,measureAndCorrect,ECDSAAdd.correct,writeBit,ok]

private theorem rel_step (f u c : Wire) (g : Gate) (s : State) (shifted : Bool)
    (distinct : f ≠ u ∧ c ≠ f ∧ c ≠ u)
    (hrel : Rel f u c shifted s)
    (notf : target g ≠ f) (notu : target g ≠ u)
    (notc : shifted = true → target g ≠ c) :
    Rel f u c shifted (transition g s) := by
  unfold Rel at *
  rw [transition_frame _ _ _ (Ne.symm notf),transition_frame _ _ _ (Ne.symm notu)]
  cases shifted with
  | false => simpa using hrel
  | true => rw [transition_frame _ _ _ (Ne.symm (notc rfl))]; exact hrel

private theorem rel_toggle (f u c : Wire) (s : State) (shifted : Bool)
    (distinct : f ≠ u ∧ c ≠ f ∧ c ≠ u)
    (hrel : Rel f u c shifted s) : Rel f u c (!shifted) (transition (.cx c f) s) := by
  unfold Rel at *
  simp only [transition,front,run,writeBit,Function.update_self,
    Function.update_of_ne (Ne.symm distinct.1),Function.update_of_ne distinct.2.1]
  cases shifted <;> cases hF : s.basis f <;> cases hC : s.basis c <;> cases hU : s.basis u <;> simp_all

/-- Each replacement has the reference default transition and preserves freshness/erasures. -/
theorem cut_valid (f u c l : Wire) (n : Nat) (shifted : Bool) (gs : List Gate) (s : State)
    (distinct : f ≠ u ∧ c ≠ f ∧ c ≠ u) (fl : f ≠ l) (ul : u ≠ l)
    (checked : check f u c l n shifted gs = true)
    (related : Rel f u c shifted s)
    (phys : ∀ g ∈ gs, proper g = true) (prepared : Prepared s gs) (ready : Ready s gs) :
    (∀ g ∈ cut f u l n gs, proper g = true) ∧ Prepared s (cut f u l n gs) ∧ Ready s (cut f u l n gs) ∧
    run (GateMirror.forward (cut f u l n gs)) [] s = run (GateMirror.forward gs) [] s := by
  induction gs generalizing n shifted s with
  | nil => cases n <;> simp_all [cut,check,Prepared,Ready,forward]
  | cons g gs ih =>
    cases n with
    | zero => exact ⟨phys,prepared,ready,rfl⟩
    | succ n =>
      have pg := phys g List.mem_cons_self
      have tailphys : ∀ x ∈ gs, proper x = true := fun x hx => phys x (List.mem_cons_of_mem _ hx)
      by_cases hitg : hit f u l g = true
      · have checks := checked
        rw [check,if_pos hitg] at checks
        simp only [Bool.and_eq_true,Bool.not_eq_true'] at checks
        have sm : shifted = false := checks.1
        subst shifted
        have eq := transition_cut f u l g s fl ul hitg (by simpa [Rel] using related) prepared.1
        have newrel : Rel f u c false (transition g s) := by
          unfold Rel at *
          simp only [Bool.false_and,Bool.xor_false] at *
          have hg := of_decide_eq_true hitg
          rcases hg with rfl | rfl
          all_goals rw [transition_frame _ _ _ fl,transition_frame _ _ _ ul]; exact related
        obtain ⟨p,h,r,e⟩ := ih n false (transition g s) checks.2 newrel tailphys prepared.2 ready.2
        refine ⟨?_,?_,?_,?_⟩
        · intro x hx
          simp only [cut,hitg,↓reduceIte,List.mem_cons] at hx
          rcases hx with rfl | hx
          · simpa [proper] using ul
          · exact p x hx
        · simpa only [cut,hitg,↓reduceIte,Prepared,eq] using (show True ∧ Prepared (transition g s) (cut f u l n gs) from ⟨trivial,h⟩)
        · simpa only [cut,hitg,↓reduceIte,Ready,eq] using (show True ∧ Ready (transition g s) (cut f u l n gs) from ⟨trivial,r⟩)
        · change run (GateMirror.forward (cut f u l (n+1) (g::gs))) [] s = _
          simp only [cut,hitg,↓reduceIte,GateMirror.forward,List.map_cons]
          change run ([front (.cx u l)] ++ GateMirror.forward (cut f u l n gs)) [] s = run ([front g] ++ GateMirror.forward gs) [] s
          rw [run_append,run_take,List.drop_nil,run_append,run_take,List.drop_nil]
          rw [show run [front (.cx u l)] [] s = transition g s from eq,e]
          rfl
      · have miss : hit f u l g = false := Bool.eq_false_iff.mpr hitg
        have checks := checked
        rw [check,if_neg hitg] at checks
        obtain ⟨shifted',hc,hr⟩ : ∃ shifted', check f u c l (n+1) shifted' gs = true ∧ Rel f u c shifted' (transition g s) := by
          by_cases gf : target g = f
          · rw [if_pos gf] at checks
            by_cases hg : g = .cx c f
            · rw [if_pos hg] at checks
              subst g
              exact ⟨!shifted,checks,rel_toggle f u c s shifted distinct related⟩
            · rw [if_neg hg] at checks
              contradiction
          · rw [if_neg gf] at checks
            by_cases bad : target g = u ∨ (shifted = true ∧ target g = c)
            · rw [if_pos bad] at checks
              contradiction
            · rw [if_neg bad] at checks
              have hu : target g ≠ u := fun h => bad (Or.inl h)
              have hc : shifted = true → target g ≠ c := fun hs h => bad (Or.inr ⟨hs,h⟩)
              exact ⟨shifted,checks,rel_step f u c g s shifted distinct related gf hu hc⟩
        obtain ⟨p,h,r,e⟩ := ih (n+1) shifted' (transition g s) hc hr tailphys prepared.2 ready.2
        refine ⟨?_,?_,?_,?_⟩
        · intro x hx
          rw [cut,if_neg hitg] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact pg
          · exact p x hx
        · simpa only [cut,miss,↓reduceIte,Prepared] using (show ValueOK s g ∧ Prepared (transition g s) (cut f u l (n+1) gs) from ⟨prepared.1,h⟩)
        · simpa only [cut,miss,↓reduceIte,Ready] using (show Fresh s g ∧ Ready (transition g s) (cut f u l (n+1) gs) from ⟨ready.1,r⟩)
        · simp only [cut,miss,↓reduceIte,GateMirror.forward,List.map_cons]
          change run ([front g] ++ GateMirror.forward (cut f u l (n+1) gs)) [] s = run ([front g] ++ GateMirror.forward gs) [] s
          simp only [run_append,run_take,List.drop_nil]
          exact e


theorem cut_proper (f u l : Wire) (n : Nat) (gs : List Gate)
    (phys : ∀ g ∈ gs, proper g = true) : ∀ g ∈ cut f u l n gs, proper g = true := by
  induction gs generalizing n with
  | nil => cases n <;> simp [cut]
  | cons g gs ih =>
    cases n with
    | zero => exact phys
    | succ n =>
      have pg := phys g List.mem_cons_self
      have pt : ∀ x ∈ gs, proper x = true := fun x hx => phys x (List.mem_cons_of_mem _ hx)
      by_cases hh : hit f u l g = true
      · rw [cut,if_pos hh]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · have h := of_decide_eq_true hh
          rcases h with rfl | rfl <;> simp_all [proper]
        · exact ih n pt x hx
      · rw [cut,if_neg hh]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact pg
        · exact ih (n+1) pt x hx

theorem cut_allW {P : Wire → Prop} (f u l : Wire) (n : Nat) (gs : List Gate)
    (box : AllW P gs) : AllW P (cut f u l n gs) := by
  induction gs generalizing n with
  | nil => cases n <;> simpa [cut] using box
  | cons g gs ih =>
    cases n with
    | zero => exact box
    | succ n =>
      have bg := box g List.mem_cons_self
      have bt : AllW P gs := fun x hx => box x (List.mem_cons_of_mem _ hx)
      by_cases hh : hit f u l g = true
      · rw [cut,if_pos hh]
        apply allW_cons
        · intro q hq
          have h := of_decide_eq_true hh
          rcases h with rfl | rfl
          all_goals apply bg q; simp only [Gate.wires,List.mem_cons,List.mem_singleton] at *; tauto
        · exact ih n bt
      · rw [cut,if_neg hh]
        exact allW_cons bg (ih (n+1) bt)

end ECDSAAdd.Entrant.StairPacket.FlagLeave

namespace ECDSAAdd.Entrant.StairPacket.FlagLeave
open GateMirror Partial Challenge
set_option linter.unusedSimpArgs false

def removed (f u l : Wire) : Nat → List Gate → List Gate
  | 0, _ => []
  | _+1, [] => []
  | n+1, g::gs => if hit f u l g then g :: removed f u l n gs else removed f u l (n+1) gs

theorem cut_length (f u l : Wire) (n : Nat) (gs : List Gate) : (cut f u l n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => cases n <;> rfl
  | cons g gs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      by_cases h : hit f u l g = true
      · rw [cut,if_pos h]; simp only [List.length_cons,ih]
      · rw [cut,if_neg h]; simp only [List.length_cons,ih]

theorem cut_count (p : Gate → Bool) (f u l : Wire) (n : Nat) (gs : List Gate)
    (zero : p (.cx u l) = false) :
    (cut f u l n gs).countP p + (removed f u l n gs).countP p = gs.countP p := by
  induction gs generalizing n with
  | nil => cases n <;> rfl
  | cons g gs ih =>
    cases n with
    | zero => simp [cut,removed]
    | succ n =>
      by_cases h : hit f u l g = true
      · rw [cut,if_pos h,removed,if_pos h]
        simp only [List.countP_cons,zero,Bool.false_eq_true,if_false]
        have e := ih n
        split <;> omega
      · rw [cut,if_neg h,removed,if_neg h]
        simp only [List.countP_cons]
        have e := ih (n+1)
        split <;> omega

theorem cut_append (f u l : Wire) (n : Nat) (as bs : List Gate) :
    cut f u l n (as++bs) = cut f u l n as ++ cut f u l (n-(removed f u l n as).length) bs := by
  induction as generalizing n with
  | nil => cases n <;> simp [cut,removed]
  | cons g gs ih =>
    cases n with
    | zero => simp [cut,removed]
    | succ n =>
      by_cases h : hit f u l g = true
      · simp only [List.cons_append]
        rw [cut,if_pos h,cut,if_pos h,removed,if_pos h]
        simp only [List.length_cons,Nat.add_sub_add_right,List.cons_append]
        rw [ih]
      · simp only [List.cons_append]
        rw [cut,if_neg h,cut,if_neg h,removed,if_neg h]
        simp only [List.cons_append]
        rw [ih]

theorem cut_of_removed_nil (f u l : Wire) (n : Nat) (gs : List Gate)
    (empty : removed f u l n gs = []) : cut f u l n gs = gs := by
  induction gs generalizing n with
  | nil => cases n <;> rfl
  | cons g gs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      by_cases h : hit f u l g = true
      · rw [removed,if_pos h] at empty
        contradiction
      · rw [removed,if_neg h] at empty
        rw [cut,if_neg h,ih (n+1) empty]


theorem pair_savings (f u l : Wire) (a b : List Gate)
    (ha : removed f u l 2 a = [.make f u l]) (hb : removed f u l 1 b = [.pop f u l]) :
    toffoliCount (GateMirror.forward (cut f u l 2 a)) + toffoliCount (GateMirror.forward (cut f u l 1 b)) + 1 =
      toffoliCount (GateMirror.forward a) + toffoliCount (GateMirror.forward b) ∧
    toffoliCount (inverse (cut f u l 1 b)) + toffoliCount (inverse (cut f u l 2 a)) + 1 =
      toffoliCount (inverse b) + toffoliCount (inverse a) ∧
    measurementCount (GateMirror.forward (cut f u l 2 a)) + measurementCount (GateMirror.forward (cut f u l 1 b)) + 1 =
      measurementCount (GateMirror.forward a) + measurementCount (GateMirror.forward b) ∧
    measurementCount (inverse (cut f u l 1 b)) + measurementCount (inverse (cut f u l 2 a)) + 1 =
      measurementCount (inverse b) + measurementCount (inverse a) ∧
    gateSlots (GateMirror.forward (cut f u l 2 a)) + gateSlots (GateMirror.forward (cut f u l 1 b)) + 1 =
      gateSlots (GateMirror.forward a) + gateSlots (GateMirror.forward b) ∧
    gateSlots (inverse (cut f u l 1 b)) + gateSlots (inverse (cut f u l 2 a)) + 1 =
      gateSlots (inverse b) + gateSlots (inverse a) := by
  have ac := cut_count isCCX f u l 2 a rfl
  have am := cut_count isMake f u l 2 a rfl
  have ap := cut_count isPop f u l 2 a rfl
  have bc := cut_count isCCX f u l 1 b rfl
  have bm := cut_count isMake f u l 1 b rfl
  have bp := cut_count isPop f u l 1 b rfl
  simp only [ha,hb,List.countP_cons,List.countP_nil,isCCX,isMake,isPop,Bool.true_eq_false,if_false,if_true,
    Bool.false_eq_true,Nat.add_zero,Nat.zero_add] at ac am ap bc bm bp
  simp only [toffoli_forward,toffoli_inverse,meas_forward,meas_inverse,slots_forward,slots_inverse,cut_length]
  omega

end ECDSAAdd.Entrant.StairPacket.FlagLeave

namespace ECDSAAdd.Entrant.StairPacket.FlagLeave
open GateMirror
set_option linter.unusedSimpArgs false

theorem check_prefix (f u c l : Wire) (n : Nat) (shifted : Bool) (a b : List Gate)
    (ok : check f u c l n shifted (a++b) = true) : check f u c l n shifted a = true := by
  induction a generalizing n shifted with
  | nil => cases n <;> rfl
  | cons g gs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.cons_append] at ok
      by_cases hh : hit f u l g = true
      · rw [check,if_pos hh] at ok ⊢
        obtain ⟨hs,ht⟩ := Bool.and_eq_true_iff.mp ok
        exact Bool.and_eq_true_iff.mpr ⟨hs,ih n shifted ht⟩
      · rw [check,if_neg hh] at ok ⊢
        by_cases gf : target g = f
        · rw [if_pos gf] at ok ⊢
          by_cases hg : g = .cx c f
          · rw [if_pos hg] at ok ⊢
            exact ih (n+1) (!shifted) ok
          · rw [if_neg hg] at ok
            contradiction
        · rw [if_neg gf] at ok ⊢
          by_cases bad : target g = u ∨ (shifted = true ∧ target g = c)
          · rw [if_pos bad] at ok
            contradiction
          · rw [if_neg bad] at ok ⊢
            exact ih (n+1) shifted ok
end ECDSAAdd.Entrant.StairPacket.FlagLeave

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
namespace ECDSAAdd.Entrant.StairPacket.DeadScan
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- Measured replacement for the last exchange in the leave scan. -/
def topM (g a b : Wire) : Program :=
  [.CX a b, .measureX a [] [.CZ g b], .CX a b]

theorem eraseProduct (g b a : Wire) (ga : g ≠ a) (ba : b ≠ a)
    (s : State) (m : List Bool) (known : s.basis a = (s.basis g && s.basis b)) :
    run [.measureX a [] [.CZ g b]] m s = run [.CCX g b a] [] s := by
  cases m with
  | nil => simp [run,measureAndCorrect,correct,known,writeBit]
  | cons c m =>
    cases c <;> cases hg : s.basis g <;> cases hb : s.basis b <;>
      simp [run,measureAndCorrect,correct,known,hg,hb,writeBit,ga,ba]

/-- The sum rail is positive and lies opposite the oriented signed rail. -/
theorem topM_eq (g a b : Wire) (ga : g ≠ a) (gb : g ≠ b) (ab : a ≠ b)
    (s : State) (m : List Bool)
    (known : s.basis a = (s.basis g && (s.basis a ^^ s.basis b))) :
    run (topM g a b) m s = run (cswap g b a) [] s := by
  let t : State := ⟨s.phase, writeBit s.basis b (s.basis b ^^ s.basis a)⟩
  have kt : t.basis a = (t.basis g && t.basis b) := by
    simp only [t, writeBit, Function.update_of_ne ab, Function.update_of_ne gb,
      Function.update_self]
    rw [Bool.xor_comm]
    exact known
  have same := eraseProduct g b a ga ab.symm t m kt
  simp only [run] at same
  simp only [topM,cswap,run]
  change (let z := measureAndCorrect a [] [.CZ g b] (m.headD false) t
    State.mk z.phase (writeBit z.basis b (z.basis b ^^ z.basis a))) = _
  rw [same]

theorem noTape (p : Program) (h : measurementCount p = 0) (m : List Bool) (s : State) :
    run p m s = run p [] s := by
  rw [←run_take p m s,h]
  rfl

theorem exchange_mc (g : Wire) (ps : List (Wire×Wire)) : measurementCount (RailPair.exchange g ps) = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [RailPair.exchange,List.flatMap_cons,measurementCount_append] at *
    simp only [cswap] at ih
    simp [cswap,measurementCount,ih]

def scanM (a b g n : Wire) (ps : List (Wire×Wire)) : Program :=
  [.CX a n,.CX b n] ++ RailPair.exchange g ps ++ topM g a b ++
    signComplement n ((ps++[(a,b)]).map Prod.snd)

theorem scanM_eq (a b g n : Wire) (ps : List (Wire×Wire))
    (ga : g ≠ a) (gb : g ≠ b) (ab : a ≠ b)
    (an : a ≠ n) (bn : b ≠ n) (gn : g ≠ n)
    (ap : a ∉ RailPair.sites ps) (bp : b ∉ RailPair.sites ps) (gp : g ∉ RailPair.sites ps)
    (nd : (g::RailPair.sites ps).Nodup) (s : State) (m : List Bool)
    (known : s.basis a = (s.basis g && (s.basis a ^^ s.basis b))) :
    run (scanM a b g n ps) m s = run (RailPair.scan a b g n (ps++[(a,b)])) [] s := by
  let P : Program := [.CX a n,.CX b n] ++ RailPair.exchange g ps
  let S : Program := signComplement n ((ps++[(a,b)]).map Prod.snd)
  let u := run ([.CX a n,.CX b n] : Program) [] s
  let v := run P [] s
  have Pu (q : Wire) (h : q ≠ n) : u.basis q = s.basis q := by
    simp [u,run,writeBit,h]
  have er := RailPair.exchange_run g ps nd u []
  have vp : v = run (RailPair.exchange g ps) [] u := by
    simp [v,P,u,run_append,run_take]
  have Va : v.basis a = s.basis a := by rw [vp]; exact (er.2.1 a ap).trans (Pu a an)
  have Vb : v.basis b = s.basis b := by rw [vp]; exact (er.2.1 b bp).trans (Pu b bn)
  have Vg : v.basis g = s.basis g := by rw [vp]; exact (er.2.1 g gp).trans (Pu g gn)
  have vm : run (topM g a b) m v = run (cswap g b a) [] v :=
    topM_eq g a b ga gb ab v m (by rw [Va,Vb,Vg]; exact known)
  have p0 : measurementCount P = 0 := by simp [P,measurementCount_append,measurementCount,exchange_mc]
  have s0 : measurementCount S = 0 := (signComplement_counts _ _).2
  have old : RailPair.scan a b g n (ps++[(a,b)]) = P ++ cswap g b a ++ S := by
    simp [RailPair.scan,RailPair.exchange,List.flatMap_append,P,S,List.append_assoc]
  rw [old]
  change run (P ++ topM g a b ++ S) m s = _
  simp only [run_append,run_take]
  rw [p0,List.drop_zero,noTape P p0 m s,noTape P p0 [] s]
  change run S _ (run (topM g a b) m v) = run S _ (run (cswap g b a) [] v)
  rw [vm,noTape S s0,noTape S s0]
  simp only [List.drop_nil]

/-- The sign-side condition needed by topM follows solely from signed packet input. -/
theorem sign_relation (L : SkywalkIntegerLayout) (G sg : Bool) (u v : Nat) (s : BasisState)
    (ha : signedRegValue L.a s = (SkywalkRails.encode G sg u v).a)
    (hb : signedRegValue L.b s = (SkywalkRails.encode G sg u v).b)
    (hg : s L.previous = G) :
    s L.aSign = (s L.previous && (s L.aSign ^^ s L.bSign)) := by
  have sign (lo : List Wire) (q : Wire)
      (h : signedRegValue (lo ++ [q]) s = SkywalkRails.signed sg u) :
      s q = PortalValues.negative sg u := by
    have z := (PortalValues.full lo q s _ h).1
    cases sg <;> simpa [SkywalkRails.neg,SkywalkRails.signed,PortalValues.negative] using z
  cases G with
  | false =>
    simp only [hg,Bool.false_and]
    exact (PortalValues.positive (L.a0::L.aMid) L.aSign s (u+v)
      (by simpa only [SkywalkIntegerLayout.a,SkywalkRails.encode,Bool.false_eq_true,ite_false,Nat.cast_add] using ha)).1
  | true =>
    have az : s L.aSign = PortalValues.negative sg u := sign (L.a0::L.aMid) L.aSign ha
    have bz : s L.bSign = false := (PortalValues.positive (L.b0::L.bMid) L.bSign s (u+v)
      (by simpa only [SkywalkIntegerLayout.b,SkywalkRails.encode,ite_true,Nat.cast_add] using hb)).1
    simp [hg,bz]
end ECDSAAdd.Entrant.StairPacket.DeadScan

namespace ECDSAAdd.Entrant.StairPacket.DeadScan
open GateMirror LeaveJ7
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def fix0M (s h : Nat) : List Gate :=
  (Shadow7.fix0P s h).take 51 ++ [.pop (s+30) (h+802) (s+h+47)] ++ (Shadow7.fix0P s h).drop 52

theorem fix0M_inverse (s h : Nat) : GateMirror.inverse (fix0M s h) =
    GateMirror.inverse (Shadow7.fix0P s h) := rfl

def lowerPairs (j : Fin 26) : List (Wire×Wire) :=
  (List.range 16).map (fun i => (Shadow7.a0P (start j) - 1 + i, Shadow7.b0P (start j) - 1 + i))

theorem fix0M_emitted : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    GateMirror.forward (fix0M (start j) (Shadow7.sbP (start j))) =
    scanM (Shadow7.a0P (start j)+15) (Shadow7.b0P (start j)+15) (start j+30)
      (Shadow7.e0P (start j)+5) (lowerPairs j) := by decide +kernel

theorem scanPairs_split (j : Fin 26) : scanPairs j = lowerPairs j ++
    [(Shadow7.a0P (start j)+15,Shadow7.b0P (start j)+15)] := by
  revert j
  decide +kernel

theorem physical_geometry : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    let a := Shadow7.a0P (start j)+15
    let b := Shadow7.b0P (start j)+15
    let g := start j+30
    let n := Shadow7.e0P (start j)+5
    g ≠ a ∧ g ≠ b ∧ a ≠ b ∧ a ≠ n ∧ b ≠ n ∧ g ≠ n ∧
      a ∉ RailPair.sites (lowerPairs j) ∧ b ∉ RailPair.sites (lowerPairs j) ∧
      g ∉ RailPair.sites (lowerPairs j) ∧ (g::RailPair.sites (lowerPairs j)).Nodup := by
  decide +kernel

theorem fix0M_run (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24)
    (s : State) (m : List Bool) (u v : Nat) (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) s.basis) :
    run (GateMirror.forward (fix0M (start j) (Shadow7.sbP (start j)))) m s =
      run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s := by
  rw [fix0M_emitted j lo hi,scan_emitted j lo hi,scanPairs_split]
  obtain ⟨ga,gb,ab,an,bn,gn,ap,bp,gp,nd⟩ := physical_geometry j lo hi
  apply scanM_eq _ _ _ _ _ ga gb ab an bn gn ap bp gp nd
  obtain ⟨pl,pr,pa,pb,pg,la,lb⟩ := scan_ports j lo hi
  rw [pa,pb,pg]
  let L := IntegerPacket.ports (Shadow7.shape j) 15
  have hg : mappedBasis j s.basis L.previous = G := by
    have eq := ready.2.2.1
    cases G <;> exact eq
  exact sign_relation L G sg u v (mappedBasis j s.basis) ready.1 ready.2.1 hg

theorem fix0M_counts (s h : Nat) :
    toffoliCount (GateMirror.forward (fix0M s h)) = 16 ∧
    measurementCount (GateMirror.forward (fix0M s h)) = 1 ∧
    Challenge.gateSlots (GateMirror.forward (fix0M s h)) = 71 := by
  simp [fix0M,Shadow7.fix0P,GateMirror.forward,GateMirror.front,GateMirror.erase,toffoliCount,measurementCount,Challenge.gateSlots,Challenge.instructionSlots]

end ECDSAAdd.Entrant.StairPacket.DeadScan

end
-- ==== end FlagLeave + DeadScan ====

-- ==== CRT: merged by merge4.py from CRTBarrelData, CRTBarrel, CRTBitCount, CRTDomain, CRTResources, CRTBarrelMetrics, CRTLinear, CRTMeasurement, CRTPlacement, CRTShapeData, CRTPhysical, CRTBarrelChecks, CRTField, CRTFieldCases, CRTFieldRows, CRTMatrix, CRTFieldRun, CRTTriangle, CRTComponents, CRTCoordinates, CRTWindowRun, CRTBarrelRun, CRTPackedData, CRTPivots, CRTPacked, CRTBasisReceipt, CRTFastField, CRTPackedActions, CRTPrototype, CRTPrototypeReceipt, CRTPackedRun, CRTSlice, CRTTemplateAction, CRTBarrelCorrect ====

-- ==== begin CRTBarrelData ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

/-- Irreducible polynomial and multiplicity for each primary component. -/
def schedule : Nat → List (Nat × Nat)
  | 31 => [(257,1), (21,1), (11,2), (13,1), (31,1), (73,1)]
  | 39 => [(257,1), (21,1), (11,2), (13,1), (19,1), (25,1), (31,1), (73,1)]
  | 46 => [(257,2), (21,1), (11,1), (13,1), (19,1), (31,1), (67,1), (73,1)]
  | 54 => [(257,1), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (87,1), (91,1)]
  | 61 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1)]
  | 69 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1), (313,1)]
  | 76 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (87,1), (91,1), (97,1), (313,1)]
  | 84 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (87,1), (91,1), (97,1), (313,1), (471,1)]
  | 91 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1)]
  | 99 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (313,1)]
  | 106 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,2), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (313,1), (471,1)]
  | 113 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1), (313,1), (471,1)]
  | 120 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (41,1), (47,1), (55,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1), (313,1)]
  | 128 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (41,1), (47,1), (55,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1), (313,1), (471,1)]
  | _ => []

/-- Pivot donor and row-target mask for each binary elimination column. -/
def pivots : Nat → List (Nat × Nat)
  | 31 => [
      (31,35918080), (31,107819777), (31,179590401), (31,535351047),
      (31,601388033), (31,1740549139), (31,957374741), (31,1223136127),
      (31,1261188097), (31,129722370), (31,1200111877), (31,519156234),
      (31,1995982101), (14,154984255), (31,1733602155), (31,1206785943),
      (17,1507244217), (31,1704060645), (31,559481857), (20,1614220291),
      (31,321130500), (22,400110605), (31,741500954), (24,1331553337),
      (31,583639144), (26,83192987), (27,166385974), (28,332771948),
      (29,665543896), (30,1331087792), (31,558861221)]
  | 39 => [
      (39,9162723584), (39,27488236289), (39,45813617921), (39,137437433607),
      (39,153819313153), (39,445114133523), (39,244935844117), (39,313191273343),
      (39,323171922945), (39,33002579970), (39,307138937093), (39,132704743946),
      (39,510957995285), (14,39357046591), (39,443565779819), (39,309056116631),
      (17,385726462137), (39,436095543013), (39,142868022273), (20,412970585091),
      (39,82286219268), (39,102447526925), (39,190701529114), (39,381403058228),
      (39,224461362277), (39,547035290823), (28,69531608393), (39,340231484188),
      (39,485014174463), (30,464940250767), (31,319995145502), (32,30104934972),
      (39,51619935352), (34,231636032805), (35,463272065610), (39,83918230523),
      (37,425745629337), (39,390219838783), (39,3580570581)]
  | 46 => [
      (46,1117841850368), (46,3353525551105), (46,5589209251841), (46,16767507169287),
      (46,18998979985409), (46,56965689245715), (46,31173583634453), (46,40587249254527),
      (46,40915229278209), (46,42181727289603), (46,39475535413509), (46,48528424175375),
      (46,67485271392529), (46,16087578252083), (46,20816508294485), (46,59615316246527),
      (18,21203428573185), (19,42406822543362), (46,5700254171140), (46,11381382316040),
      (22,3111364395029), (46,7082239524927), (46,14163304644734), (46,25266388140183),
      (46,63791416541625), (46,67109693555570), (46,41682161829491), (29,42010729056917),
      (29,35744384619353), (46,49372809208001), (46,69263555915173), (46,12129909323503),
      (46,24259818647006), (46,48519637294012), (46,63396788025091), (46,3254931478789),
      (46,67409597039881), (46,56753868507666), (46,40710542960949), (46,3355760349802),
      (42,13331996154309), (43,26663992308618), (44,53327984617236), (44,22680587317497),
      (46,41651601592587), (46,27359468136323)]
  | 54 => [
      (54,285942888042752), (54,857828664128257), (54,1429714440213761), (54,4289143320170247),
      (54,4861028853314561), (54,14583084516879379), (54,3951394086871317), (54,5095474532225919),
      (54,15246186454823937), (54,15569319629121538), (54,996425707897093), (54,1773496631439882),
      (54,16523164908471573), (52,6065240697200447), (54,4775386916498283), (54,7324172083282883),
      (53,16751616026639226), (54,1736278935201509), (52,4640750221977836), (54,4935240241906186),
      (54,915208713617194), (54,1830417330765396), (52,7284948628100410), (53,15900494212403015),
      (54,16404744525473142), (52,8315971812622680), (53,14855177065919457), (54,11281867355084874),
      (54,17047410463991026), (53,10591459681989041), (54,2014937368319019), (54,4029874736638038),
      (52,5415955734484108), (54,12694829068427907), (54,518215948049170), (54,833640720250404),
      (52,8393596253497743), (54,10889928385643120), (53,9835165330140729), (54,11948540805592747),
      (53,10543098507560425), (53,10174765160718603), (54,10841081368553679), (54,16615332641341057),
      (52,6521971216994853), (54,3882638591185148), (53,15127371437168559), (53,10221135042639406),
      (54,3631440712908923), (52,4632624451368763), (53,16806474671037358), (54,5416957039703412),
      (53,10302840710015229), (54,4371370747318727)]
  | 61 => [
      (61,36600836273537024), (61,109802508820611073), (61,183004181367685121), (61,549012543982469127),
      (61,622214154336600065), (61,1866633968526032915), (61,88022369366507541), (61,236950379853709439),
      (61,381234937232424961), (61,1102463894659465475), (61,1245190803987628293), (61,1790255261776873231),
      (61,178671229595615505), (61,440584049940173619), (61,731232588413605205), (61,2192256054710992895),
      (59,695408723984908289), (60,1390807827208470530), (61,975691170323628036), (61,2249685330690375693),
      (61,1286973423767978015), (61,1211713822260199456), (61,1424824253238280289), (61,1580100120507252963),
      (59,1032486471891878275), (60,1808879421117694780), (61,1300276199448577543), (57,273713890856340117),
      (61,1643036438565493176), (61,2176603826264684867), (60,1559764365287710281), (61,497234154589962886),
      (61,1652755276980351249), (60,2193578671138334737), (61,1102530216054938129), (60,2208174865320522095),
      (57,175912824331836836), (61,2273210136906257966), (59,775819858925853877), (61,652591411373234865),
      (58,305906964783989639), (58,458228676743118246), (60,1989275317532856995), (61,1131072155640466539),
      (61,300031352224007718), (60,1253197378997272821), (61,683014482292295543), (61,1563444814438108740),
      (61,1363168153908436193), (61,1041607516398678743), (61,1673358352873925233), (57,240357096634085266),
      (61,695314217902319062), (57,203845363139293044), (59,1098556976563432022), (59,1083557157119377945),
      (60,1788268045198739678), (61,354064315340131850), (61,702372751206116985), (61,256292258210509484),
      (61,188716590027930101)]
  | 69 => [
      (69,2342443845487230976), (69,7027331536461692929), (69,11712219227436154881), (69,35136657682187878407),
      (69,39821545310969397249), (69,119464627438424424467), (69,196084678152530493461), (69,588226917729345667199),
      (69,129508443453199286273), (69,167123160558045430019), (69,499307280794145521925), (69,188563539008086083343),
      (69,560498522468523245841), (69,101897676455342707507), (69,268209021657202103637), (69,361903765492047249407),
      (68,362712761170534858753), (62,8308336854849552386), (68,352173023686229164039), (64,35189324039907835914),
      (68,308122759987743227921), (69,139198502828753027112), (68,573997948496662429767), (69,149856700273566089367),
      (69,36193431834575700275), (69,129201140468856652684), (68,458587706219397383264), (69,400398227673199742221),
      (68,360568676940286008916), (68,502291503321775155033), (67,165051247327524054070), (69,105346147320403824803),
      (69,320739471627732928897), (69,507330491328191671617), (69,209806243836096804239), (68,299681662373771198240),
      (69,183276335124762500859), (66,144096955804694909496), (69,75263165358266174097), (68,439782788681007529630),
      (69,353405203609374162453), (68,379656316940085848111), (68,300090784581067185255), (69,243068497200475939897),
      (67,175377714172514945383), (69,27365732446840198369), (66,139349716330600749146), (68,588026280081700180516),
      (67,179929008888367430520), (68,379215570626249958141), (69,44081335213266931559), (69,278669430806938377486),
      (69,321962520306449053969), (69,316139687256055518947), (69,244749212523770761135), (68,572958013471338260963),
      (69,312651476870604206529), (68,538828463051621471847), (68,570763402664796123700), (69,318216364540086630816),
      (66,130220997194545625640), (69,517995492848635959487), (69,471912659779401024038), (68,500623710495742823284),
      (69,340330075922605668160), (68,377532022333503341068), (69,309764464280182246051), (69,140448834922817414696),
      (69,274581540090760837147)]
  | 76 => [
      (76,299832792577119158272), (76,899498377731357474817), (76,1499163962885595791361), (76,4497491888656666787847),
      (76,5097157473748712161281), (76,15291472420723112017939), (76,25328391170089453420565), (76,75545333109339291058303),
      (76,16707429782476433981441), (76,21301484228610772369667), (76,63885941498255826485509), (76,24087252307759943386895),
      (76,71758920894001096753425), (76,13098427039636993020723), (76,34425322229894577722709), (76,46159442672595354222591),
      (75,46537842379996030828545), (69,1141723982642049187842), (75,44952822405344252329991), (71,4616460621858064171018),
      (75,39361145631656806252561), (76,17741759071122249744424), (75,73351383233942436380743), (76,19087551535850756440215),
      (76,4663833839794650284339), (76,16576635646233298076556), (75,58453327861032270431328), (76,51251802873949982625037),
      (75,46112779687773678607956), (75,64100117866956019279705), (74,21248529207529498371126), (76,13409751553049809359011),
      (76,41216878835050169256321), (76,65216375409649878445377), (76,26825167967013674022287), (75,38319937843737790365472),
      (76,23604733547822579359483), (73,18484465654472034521656), (76,9608638065286776408721), (76,56247417541315705077406),
      (75,45188561301287002963477), (76,38867099553562218916004), (76,38386603900573216906343), (76,34505367862573165082770),
      (75,55263094148191354542417), (74,27673056683008584174391), (76,13188401841816185515721), (76,48055369416021967119280),
      (76,29656401949671988125230), (75,63360954320802578496380), (73,12565011893921333615230), (76,13823015755073359603796),
      (75,46692008862231305514174), (75,40989098819017212155452), (75,53777135941157025696748), (74,37594104189151905574529),
      (76,63737708415608801154675), (76,12336916070618658869374), (68,367328751246387814497), (71,3520404209372265435178),
      (76,13351249293191189565946), (76,26582424358687506892916), (75,69425060621020763775480), (73,13653718278686349541213),
      (75,71839381873660882672150), (76,12565358408349725046847), (76,70409083315736037509943), (76,73812505623469773246941),
      (72,5436526508728386072404), (75,52502015699409126918688), (76,54461614401564105911301), (76,1401173451447264398748),
      (76,21979240795559854638395), (75,43245086387284550290356), (75,39387672410137059214575), (76,25569021199906157419616)]
  | 84 => [
      (84,75857696518491442577408), (84,227573089555474327732225), (84,379288482592457212887041), (84,1137865447777371518074887),
      (84,1289580840814292210286593), (84,3868742522442353606393875), (84,6447746807872806944047125), (84,19342800583217491762937983),
      (84,16186090267128141645676545), (84,13092811908811788723880195), (84,2481737580727514175897861), (84,7277642169995534991623951),
      (84,12161017117040292843815185), (84,4168780931964924781073203), (84,6759075193836269362025813), (84,17802257418262461357719551),
      (83,17727077954243947710906369), (77,227815315160385019445250), (83,17877569866774211602743301), (79,1137984416510572915458058),
      (83,19232176710598630090276889), (84,4551213582625981654892584), (84,9970387076668610095022159), (83,13957007036021808896671952),
      (84,1779777755625639111360973), (84,18327150423962200395678655), (84,14000230750907602722751814), (84,11686388413087048234568358),
      (84,8209378554722136061189953), (83,13415768079135383896800437), (84,8057717055553937755226746), (84,6074014244417930489682762),
      (82,6596974034430680277738573), (83,12082688705923685390860867), (82,5804700931801749606377302), (84,15373410994435341249312642),
      (84,9854656641285600238916807), (82,5147908303047164500512749), (83,11335942217012246702736523), (82,7780479612168047978909084),
      (84,10102968037518731917423034), (84,18395827168191470788803368), (81,3910625766203720113470253), (84,3336000606891152652027616),
      (84,5127186493701937862423455), (83,15527652975106816170951861), (84,298499228020677483415838), (84,159410205676662044313649),
      (83,14575908044545276339757538), (84,14818378669341360343819614), (81,3154434258745728350747648), (83,11998858884191820341355994),
      (82,7944683803920224218432418), (83,9931009712368106662434875), (84,17852477535276267979901406), (83,11342966143217174139233123),
      (83,16101948632252096607124091), (83,11011593954660883185941875), (81,3383829310613734023048198), (84,4358270428405867892292179),
      (81,4452975701865833840873221), (83,16337354337908672657410844), (84,14444053845891700251443228), (84,11682564243373262762492432),
      (80,1538238632655913179282939), (84,10029302540538009769786261), (84,12297534938305342668124811), (84,18635686838981436387673450),
      (84,5766196113480299980826194), (84,5735684714834388154777161), (83,13364601366798170743445037), (83,12846008551552103450226460),
      (80,2100852271410553330830512), (82,8862507840437004999544682), (84,2347554762553578521189044), (84,18149789633313132378885832),
      (84,6542254523790668738604073), (83,17676544293565426351833585), (84,1420027552347446111512372), (84,17332227268190220416419690),
      (84,10262027990239246158079195), (84,16256005778072050677292294), (83,14244027743955415777172709), (84,4315470880829962440581504)]
  | 91 => [
      (91,39299683786837622632022016), (91,117899051360512867896066049), (91,196498418934188113160110081), (91,589495256802564339359744007),
      (91,668094624376239522430844929), (91,2004283873128710072808767507), (91,1504383662464244819387547669), (91,989977619023127720689336447),
      (91,1665187712430518659148218369), (91,545784410612961766241403139), (91,702786867788005532946923781), (91,2107399590616063438998996751),
      (91,1607069753143306047885213969), (91,316383246301112109543658291), (91,946424932852200981935756629), (91,1571201165804364063242682367),
      (88,428561146200964549060067329), (89,856163799579849529056821250), (91,1712313455618599066435321860), (89,1042313211642656302523940879),
      (86,111933124719445733345132565), (91,255363281967373793217151039), (90,1843929018162833280627441745), (91,1982189359579011504676274420),
      (90,2436321541955315929630900704), (91,1532577158785420754006704674), (90,2026531420901968404437075209), (90,1407822075121058359000960100),
      (91,1732114476770425439628497963), (89,818387245746808002346692575), (90,2066791718571335017720600530), (90,1784320522886396178249861312),
      (91,1020695107714250351664034508), (91,665186106009301481238177212), (91,541658298666636780755815894), (91,1950160183071552610040179366),
      (88,465278468881595141111962459), (89,650579833265599255579564931), (91,2173137605799331980158748309), (91,674305258079225966904979268),
      (89,1068307217185406770165067040), (90,1454882151818279094465687076), (91,652365654410789638982935263), (90,2110232860025691171827822320),
      (91,1738094821311640006054629926), (90,2422099295188997697936686046), (91,1615907517418293684877531237), (91,816337977837367247202918135),
      (90,1964179294928775739402512022), (91,1157653209893764216774323104), (91,731547533381873613991168371), (91,2471491946068423777969199206),
      (87,189996525284894627835210711), (91,1101356684251240521398234855), (91,1398845493638672179362238044), (89,1209600511325297844236567334),
      (91,941916326943876262164904102), (91,1010252570423548376043296410), (91,698499308357752514357902454), (91,1999536018608282828033003201),
      (88,369213960803152584833575364), (89,656782202177388051375302681), (91,1432051404563710755672861398), (90,1499681967849078119504309902),
      (91,2355038538360862932141386380), (90,1578477589492646438477545412), (89,698095998260770894431015585), (88,322131007797309659206484202),
      (91,835445864035008189612560755), (90,1347094383251920115894235168), (90,1458980783067908468107204595), (91,1685417328905245830667325537),
      (91,1504503047370786620067075447), (91,2225711350131108240586758274), (91,1723059602371399392234916660), (91,685092615184417018492810091),
      (91,1946129787660665388246773118), (91,2060735057117136170178138334), (91,372493444159573267903076921), (91,1878717751250420897274864728),
      (90,1289912699237634484538227734), (91,1495618630500636040527288316), (91,1345924328217409047621953242), (91,1360399674982396242276823077),
      (90,1673985774233326578005383773), (91,786863359811386383582133601), (91,513936523666429355366640502), (91,463952729887574242590434152),
      (91,1352637978518259897740817616), (90,1540468247710846467741826672), (91,997383726892145313469287930)]
  | 99 => [
      (99,2515179762357598172430270464), (99,7545539287072794517290811393), (99,12575898811787990862151352321), (99,37727696435363972586333470727),
      (99,42758055960079168869001068545), (99,128274167880237498112519438355), (99,211954190340978891552238665749), (99,632339397654567067919242690687),
      (99,140314472112393109447850131457), (99,178809150067707721351715291395), (99,535492883839072284289368588549), (99,202653685954847667972657121039),
      (99,603245928845838119648859586833), (99,109255106703414576300666590003), (99,288148514047060424758532576597), (99,387808493422843009831769440255),
      (98,389141733481810370867385073665), (92,8283804035292131178451566594), (98,378246484374951438540033687559), (94,39522454513643987297908162570),
      (98,331096913992640798676918272017), (99,149263191356576048194767028264), (98,615894026181964282370260926535), (99,159340981725236948567380656279),
      (99,37347759040560651828613808435), (99,139018083880103369736589149068), (98,491774174464984603558892536928), (99,430497102107912375960337190157),
      (98,386354116389699232464414973524), (98,537784844041512040798898169689), (97,176137856769515132889601565750), (99,113376354229598240555535667363),
      (99,346402370931209077953077987713), (99,545930763605311255984746933569), (99,225181001182910386974929581455), (98,319971684150590170545947262752),
      (99,195747200088317538548545396475), (96,155435716460883001244452426296), (99,81529575285722188246645000849), (98,471610656804093166773445230238),
      (99,381076681709643605892063034901), (98,406114367050865747303594944559), (98,323502278582224874866316123239), (99,260167611631313780189891535929),
      (97,188689193664090407797279050087), (99,29614366851491679315505616097), (96,149167361358285352920540534874), (98,631370030548146163474576724516),
      (97,194925132065629551618883992440), (98,407054296639538257273505653501), (99,49430381019190957906318167911), (99,297489091349746649803825863950),
      (99,345331716741305683617327020305), (99,341086558399885127004170131171), (99,262953086101355586192495693743), (98,615767365578792196556319091171),
      (99,336160644624930641579366887873), (98,578147216244929228237715215975), (98,613689195407158892568376930868), (99,342229081776693892387735517600),
      (96,139235148828484920186673560104), (98,558375979725041377877287196863), (96,118617585886044389286135945881), (99,536059019574181671741094300532),
      (99,203295538854793016011078104422), (96,114728366494429925510545439774), (99,495889844981416943075350103003), (98,451871543268385211173131587906),
      (98,357893966218611100817843167751), (98,444620741966311064191820270854), (98,437607245430654867772854767873), (99,45628072527503834677768057171),
      (96,140540585098405626201989591562), (98,389435886709120617526558013650), (97,239796332735394511035774189634), (99,170119526166310540021506070624),
      (98,468086576951621191496920919343), (98,571521932448844024144188624534), (99,442594494113589656636440912266), (99,487685837261005335325047243153),
      (99,391315044650676166734367314057), (99,336542217646090406935780015804), (99,436243054053627077303885429803), (98,525487665110342234432738131712),
      (98,529465723210328870438805724795), (99,491885321899477724354109219873), (96,141793406886735682747808469780), (99,560319195583539868831194872819),
      (97,194520755579847131419937432667), (95,77370363044297663338791637525), (99,424284439558484678597095653736), (99,610619336555707383513141480569),
      (99,119018491140987559804696838477), (99,179014356632874704735550774579), (98,367689088717383276413793297506), (97,271255556128292154974300170295),
      (97,226215208270368168834279927242), (98,400993572129202162619155973650), (99,4962903621849852664394817173)]
  | 106 => [
      (106,318170239938236149332117094400), (106,954510719814708448546107097089), (106,1590851199691180746660585472001), (106,4772553599073542242730414899207),
      (106,5408894078950014538583677075457), (106,16226682236850043616052640481299), (106,27043552350020364223391140478997), (106,81128895463376907883011118399615),
      (106,67889464348266469533233790124033), (106,54915293034904775476271986442499), (106,10408951243745371350786197684485), (106,30524941248454929470003636602639),
      (106,51007646973552095117238819946769), (106,17484823306489861557278155674419), (106,28349300112101634393572558312789), (106,74668377010119898842993812013055),
      (105,74352130980092325169444922064897), (99,954879852188818116079550726146), (105,74984026597943704995953508417541), (101,4773450978112682245288652570634),
      (105,80665510608625562710854337101849), (106,19089390599101729045073197793320), (106,41818155899084810738704139092047), (105,58540455911958776903630182154448),
      (106,7465009800366136598102841033165), (106,76868819431714557921467559773119), (106,58721368914560744800369007527238), (106,49017047200681407501502360455846),
      (106,34432176821888940148492528066369), (105,56270244018325853708709434571957), (106,33795815347233386911098581172858), (106,25476469693645008759703378516810),
      (104,27669808011179177830640958334029), (105,50677875653022744100817070047811), (104,24346814337288827986536723130198), (106,64481208573546065722480502929282),
      (106,41333084623201471904176963343559), (104,21592064009378143825814965063661), (106,47545849597954080539255561012363), (105,76374342062152774524309298530583),
      (105,42374930605825331795520288223674), (106,37635052011422465272972307696274), (106,66094684256104033334268825880331), (105,53906703065049916645219822437733),
      (104,24091058004250820939499086268764), (106,49181056437642070428332024463419), (105,52673499770866841582479296280248), (105,64675646139251826359870235803323),
      (106,39095818252726487132087536179591), (106,18278892099095055234595658552280), (105,62077306635089997114184558881966), (105,52374443288822786978501846549134),
      (106,59923970135987650302992035755417), (104,26156281629542748765812136990666), (105,45755550362496378920113087538305), (106,58074173756756689721771676575195),
      (105,63464647817358506998952701395912), (106,40936917464716253115580512954227), (106,6839778114958564049803459026851), (106,72223347935051548857640455180684),
      (106,24343189197251399544109967788636), (105,63198953705806889201539524210517), (106,62893319776283560066374959450986), (105,58249157057644992536143205927113),
      (103,17760591967921313477261724745020), (105,62572909881491642543205059485982), (105,51468356948513096253944781488122), (106,71218007972886675739504645182013),
      (106,7670789867334537560142702039475), (105,63980488612373923576853452961151), (106,33000137745765636612809876664572), (106,33891409652425286813888371267710),
      (104,24597241999654721995458566798938), (106,41583071082784104315919305849520), (106,54949915799046589715211774093214), (106,28119345611524042532496946529028),
      (104,39929931610602640062040057069133), (103,11641069340313407194244800709525), (106,75421438896397168800676376887939), (106,65269317897395073252462348909158),
      (104,34203111585108998650962309805830), (104,36478584115708006235890865128493), (105,44347810250600779651978895969855), (105,62363187985393378158327084393725),
      (106,75875048342125172924052577446723), (102,8844804125102786771753685230559), (105,79196451483437275206688386134921), (106,17134776057244626859963233935838),
      (106,31170784720135621541512094608080), (103,15360939505061331416054120671303), (105,52236377753339281780678997633428), (106,63575963980425987896993590672874),
      (103,13628590249275017478299465839315), (106,58576099797044190047125388815915), (106,65172695546414817789913353180388), (106,38299546500589786589459712983135),
      (105,69127516647609918593033943928233), (104,37828075149663194092509375863886), (105,45894297187548778521795502339417), (106,21615554872322120194608885620759),
      (106,44069770176049638523223269706303), (103,10693998986412414929230381322471), (105,42662685025107723999116316348313), (105,67867807454143437244456654746776),
      (106,10635484771546507128637796000769), (106,12081644718244539061407032838157)]
  | 113 => [
      (113,40725790712094227121254020743168), (113,122177372136282681363762062229505), (113,203628953560471135606270103715841), (113,610886860681413406818810190561287),
      (113,692338442105601861061256039104513), (113,2077015326316805583175273633546259), (113,3461559152794385638044348121677845), (113,10384488244203895737485072023093375),
      (113,8689902510197174935693196910723073), (113,7029251869814028323809575024132355), (113,1332402994709958290161109743960325), (113,3907094375949122150799162541344527),
      (113,6528922133061634420729527025074449), (113,2238171148610428130524228158165811), (113,3628767155941932339731135378822485), (113,9557463175142215659990656252608511),
      (18,9517075476660549810502833041309697), (19,122230103882680886671968986202114), (113,244460207751218232243946294083588), (113,488732982727224314703617344929800),
      (22,9918628246455605699513596049162261), (113,8264591944595780654543438063009855), (113,2647015870211575007095970772942974), (113,2241259139341856276091097323077783),
      (113,3640850779512909145676021061190073), (113,7249879747561018529806210166817650), (113,5356307548273937910489983680185971), (29,3696007733634465227723068694399637),
      (29,2036029888654425148123960252633945), (113,9103200660987270460403778360254657), (113,1650137846371812851282456992902565), (113,3260951268294909636417340098403146),
      (113,8763318988214209151796839930527867), (113,1292692491278626163773887817168409), (36,2851536226820468089474417063156445), (37,5702946123664961343635281352439226),
      (113,8400344163803378710610515379579764), (113,7806951316199669641102345845434177), (39,9034289472995764456135806452596523), (113,7378302430490741588275383792533885),
      (42,328988535805716351944091899298695), (42,4682957116242731538469268216576735), (113,5422232187044544088414286457112687), (44,2091926872917304342409201790445287),
      (45,4141894503215738419842173667560910), (46,8283785861099075673367085295967132), (47,3221746181475675679323048990422840), (48,6443488080662201027623121749175920),
      (113,5843947025045237473660615505138682), (113,3433023515257215523561255391728361), (113,10256990403036282257738269104813883), (113,4996576025963934443783895788584095),
      (53,6610971381792241566938420928637911), (54,5995225092997590943432075646719918), (113,323105979474238493074400670864994), (58,8368139428169979415353049556729825),
      (59,3065934280560885779698109919559618), (113,803683827646728222200449755824039), (113,7168313073984528468283141648384202), (113,7436961664918655613153982950867348),
      (113,7038981887956484511857258636000721), (64,7408485222321921021998073763379703), (65,7605464624511780965211173497172974), (66,6570620995584670985492356389857244),
      (113,6076781691266185901189089882132408), (113,10288742229083602414218597725085552), (113,570575954853111708946280109459631), (72,2568182290343638764316008591517457),
      (72,5136336843088549924097363079319074), (72,10223203695122053243849364410440772), (72,1908284991109437186328578682206344), (72,3816285190978129899596046328033552),
      (113,7632570381068454900412599355892256), (74,1793623446813586168987798064906609), (113,3587244997087013885663121147790050), (78,6365495360801601565282067679528117),
      (113,7443920430229071284200279231564680), (113,9140571543343462946130443555935730), (113,8485557297336893939467617806413235), (80,10227264883959167924835016557343799),
      (113,8564429768549450760316746669644889), (113,6587255177964262130429898922321131), (113,5994537356235832930782470889392598), (113,5066830057096837717270142208778025),
      (113,10097056703112085310572067112500818), (86,3341521807041620013358795247373939), (113,6682774362124695456507799935229158), (113,8319996387053510512094294030677951),
      (113,1483229349990776358464221327754279), (113,1368632446080497301291928167473943), (113,2687984975077122184600671997838894), (113,9619291507976171189453034232997637),
      (113,538201361385502248026702780288522), (96,10046533325796655436613531031599889), (96,8612351596417136381887676516602151), (96,5952361882315274343321525932901707),
      (113,1232686886677312595946158608379283), (113,2278674583251824906112788644702881), (113,4557349166503649812225577289405762), (113,9114698333007299624451154578811524),
      (113,8428457028143194626431241633584429), (113,5888666280570904824190988699970175), (113,9951915696813159310226724784198910), (113,2501523953693185396706707964996092),
      (113,4302201119182310843634631910764255), (107,7961869932174538057413820726321305), (113,3754294102158073860459290681033010), (113,1412678911003886205931100684805071),
      (109,2027161085198337256915589578384739), (110,4054322170396674513831179156769478), (111,8108644340793349027662358313538956), (113,6626013345967924459400292217428677),
      (113,1598014099830051871289074217381501)]
  | 120 => [
      (120,5274714268987761405134610975752192), (120,15824142806963284215403832927256577), (120,26373571344938807025673054878760961), (120,79120714034816421077019164515696647),
      (120,89670142572791943887288324274257921), (120,269010427718375831231824286576279571), (120,443990677048579390440996350657101845), (120,1325771860919707935588252559974006911),
      (120,295934356169031491367846985501835265), (120,378081999275634102318832673617805571), (120,1124885465538605318991629652683129093), (120,421780915748910838554823501457131279),
      (120,1263241130577097033781415240970338577), (120,232852429496135971377408405208765235), (120,606150541047726219957006194873537877), (120,810374313604892614217659253423833087),
      (119,816178205542581931090758636066308097), (113,17552056672939675739621690627850242), (119,792212465241197833202824760049467399), (115,79017265390696286996680249500106762),
      (119,693717550213455293559092516348821521), (120,315779830659145088177302504525529128), (119,1289292549169622927302622599457472583), (120,334039709783573445366110457874022551),
      (120,81217634845043279599325685119910195), (120,292159912752363914050969857283589004), (119,1031046232715598203556990800640345184), (120,903206236427546697435573990372216077),
      (119,814302008860586286381140574194638420), (119,1129990606072224479334290822239168345), (118,373126688031962526520333926950921270), (120,236476048986902044895197453466439843),
      (120,722938971425189064361746001316301185), (120,1143725051541315761180639894654037313), (120,469330892179532053105096948701590927), (119,669906533180169647440964004480925472),
      (120,415307621862111664808145411279331067), (117,322147944481273126372965614222348856), (120,170204264449125342563096862076750481), (119,990469732468899625644386789986827934),
      (120,798065409474898100741430436160863765), (119,854540776300579451483291603371517999), (119,678459706093624548330141524236409959), (118,545603378602631123099364566994658361),
      (118,397065565379559906502082931745245543), (120,61493113830286264166472136421709025), (120,586164661152830203557558078343090493), (119,960311937131736597059619774517776290),
      (120,1313777525619091031571799687441162299), (120,149657008346579182516087443775794527), (116,155340300253623808492995035106149341), (118,559049559652052987305106055373673065),
      (120,740512093617232204038008791923254533), (118,646878064699850999959156482288876267), (120,637253354025229505155008440457991371), (120,1051062482753023634782142103723881885),
      (120,1195574132425041440902109994403291665), (120,1236037581949292809152046034196950303), (120,872832668828722597486976422070986378), (120,514642013381791473606825434251994079),
      (120,1310022641592327279556174495540315056), (118,631080731275449996988636673465125123), (119,1165844560386360339547270669426465483), (120,671287198980503363465556415895728797),
      (120,707903069588482179064535841274173107), (120,1052782288288969514197141593953390431), (119,1288713704429970877376768345572430749), (120,1166952442368753748947614156969134797),
      (118,628654336494641146063951722797596940), (120,858533732631297250920832067423763090), (120,1104300362176115479356407331268599197), (119,1179626259095067754486666024870335295),
      (120,159305445598240189986715790091889159), (118,648560697364633296683169483553036835), (117,248834913477110891381628763019658604), (120,605103671359893946618310403063806472),
      (118,449913098202068505080043902922100248), (115,81886930714239573239215727878241611), (120,275286720730626054456922557243198776), (120,832525397712149864886698912403945314),
      (120,1292208718071755801765186263591897473), (120,1238927322212567693722025944340893660), (118,530967398394538093822374080873232464), (120,555629770378292765760292529461370210),
      (118,565496770080681104491458327701275064), (120,263179589394212196123210339420606871), (118,638834407248478006847404542365414681), (119,1124926021293251929727488012469458451),
      (120,804760499613397699858913579403658738), (120,714510497522911185026718958506163282), (117,331892381107938366752087146642588600), (119,932858567348495583535060233536180822),
      (117,169018588051591110778344936686652889), (120,395967211585266464453600097175159700), (119,1109406018712643064412482894579112918), (120,1006439787088164816983932489817882461),
      (120,1080758853432013004970800289194501527), (114,32308297768437950355936575119672331), (120,725798083060471657123343730932646705), (118,556540940385361782246023794412113038),
      (120,436047706261166064948785189530535458), (120,745389478489709543030262826029023291), (118,562394104607017933520945286333992669), (115,78759454364466680337152581796999138),
      (120,642998675583972536725820037787794512), (120,1011049796570622900904116268596924602), (120,97082425968902403235285369818755643), (116,131822928099617974928818108758638774),
      (120,292749060400202225157956937681254285), (119,1324133606590532060987869609118233935), (120,195826992284805105546471390055632840), (118,592308811774856884296745575836066836),
      (120,197673932915831872092311199839502218), (120,44651192797539382436994429837442211), (119,1043400850486921637303095166569680965), (117,280521955267714117941059733049643623),
      (120,1204681927300324378441091173165078837), (120,141270023420173201238325401909262547), (120,934208558461878912007223287014145561), (120,659390781460394243749750814590213141)]
  | 128 => [
      (128,1334502710053903634308941671256096768), (128,4003508130161710902926825013768290305), (128,6672513550269518171544708356280483841), (128,20017540650808554514634125068720865287),
      (128,22686546070916361783252008349040115713), (128,68059638212749085349325984360873852947), (128,113428370318766428587264596474486390805), (128,340278910786073255526059052931461873791),
      (128,284750725454141028292782557885495574529), (128,230334525270066080114677454102117417219), (128,43660181330655913251913455581654155525), (128,128027668511100834637320301288370210575),
      (128,213939720456163636698390544885825470737), (128,73340392197666508981086796720627716915), (128,118907442165905238908395834559824205141), (128,313178953323060122746612318419304808447),
      (127,311855529219212896190581610741666938881), (121,4005236044027687294451042871468883970), (127,314507530635329618022248237317030477829), (123,20017437202164434380553786153705275402),
      (127,338339399745059746935155110210227994649), (128,80069459577754097462405726121346203688), (128,175396310138493973380780332330832035919), (127,245533869601521626177138500090639417552),
      (128,31313702831160872378198603764601782733), (128,322411628131359649234284466773111538623), (128,246293660052604407743721109606870943046), (128,205591156656602784885837860184053385894),
      (128,144420255923029845737135754771121119041), (127,236012993165205135053117725886163270837), (128,141754818831098439314010113639527891578), (128,106854851159487598966156183116572187466),
      (126,116055906612072208214941957629514900557), (127,212559998415840909298482181996219056707), (126,102117324190705019025714820339391801174), (128,270453235720438228587954020386549168002),
      (128,173365323957544945036633158662120035527), (126,90562332437848793048189187368231505901), (128,199423403759753355761175478756382885003), (128,320337513582126056445816865397108164887),
      (128,155896644847967050888797896260334434477), (128,4702911422052806253308990229203202623), (128,277217123628180288707076727524589750027), (124,37794173697599817040308930097778118642),
      (128,165223522860560121434174508312613929038), (128,273863056302333269335402083973757908618), (128,89898407753608716910621876296455604414), (126,96669093951855194026303544552456321132),
      (127,278134463670462905818008720949101766595), (126,115170000136721732537473580343144698085), (127,325448653010568433964357219301282452287), (128,152628186806373374709280976311215631964),
      (126,90423849392111824304001113363290789391), (128,302904194361975429046396770583475992196), (127,335810110318151701781066007630088616933), (128,137223955881794859829840312358791417431),
      (126,165284825688633695680103300825706018095), (127,193096384327768957257894480286037260751), (128,237360201392231934183668619688179950521), (127,183373352775943286997511384730197420041),
      (128,38962973544379669594967805204806162710), (127,170252877757084156064098926604665113121), (127,339614460489391896341823646059382250598), (124,24704341081945161306736960875104502570),
      (128,42021205127013854641975664436438689540), (124,32227555554641340245735373158744344625), (125,61380644248748737290688881108036856558), (128,127575434758883296420964592067736562486),
      (128,329330554110896452000938956194591169643), (127,202836961711343274557953493585164658712), (128,114363559349230693552638026766816177540), (128,37015630493700166309355445367402048952),
      (125,70705821854316378082885695831734796501), (127,200363820514776957147953791005285714202), (125,62569459096689448835901315885116518088), (124,33714782776890459034557705217655185669),
      (128,185131189092221477857999636379460216459), (128,144258644835684662578640461063480909353), (128,180981771000059138705597413487304192712), (127,174101361411992534000380782754661120567),
      (128,142102564997613661914050817268562872282), (126,117740674940567541422972060023815580268), (126,119163904488898649111328436237728750713), (128,204876414682732341508497981486607654172),
      (128,227268831579717944965670267415415468301), (128,198319467410931655141022363612510937009), (128,292858829764925775082833101551523489181), (128,101713369905218191949494103701070939075),
      (128,58218239830538848546802984681123077106), (127,298710890018115091030929744178297007750), (127,182906807909838798810342010841566422565), (128,269743244008946709948490895161577074198),
      (128,35324944312273426377046748576849508198), (127,337896464029056301638631666002104464488), (128,239975993160284077979594856837980275239), (128,173731763015782360769355315388830804139),
      (128,222000451519509461128724098531532724310), (126,168804793612770265557463176341067893479), (128,97184295740700665247385953347497886488), (126,113229769249511560508975130441821620193),
      (128,88448614769640380426337724164381806684), (128,91674277785905280881845291645632298625), (127,215831168454319587594996671847674493272), (124,32483809274746159363375037370195154519),
      (127,226766153262461748709507145477103293626), (125,78307165062490833847283946908243842700), (128,156086304462652754683730974274770981002), (127,310440445424890368197950633811612979637),
      (128,252966929552301725603434749710635816825), (128,61568199987340609016085854524312729717), (126,99113165322930705135166041272562902986), (128,69568680178919174286392007593142419592),
      (127,259668918319820531897269954450052588050), (127,292872644559407730991787388117205045378), (123,17990319710564827599222977017429936411), (125,64970169535335440048922288908146286819),
      (126,109568086253313363777736031280482113277), (126,122631979062446221822794000566425631095), (127,269273930882999033425307440273103765976), (125,52132322616471802078205780769228776166),
      (128,21909074216695534048246852453417467777), (127,265849878235076560867741856175017718048), (126,85455803519456511305621453542683428225), (126,153082321934498790881396044062408397063),
      (128,311272303955906299611725626572328787573), (127,182104348596914960059645982288499633600), (128,14498770037995152247865646402039211766), (128,55388010969361681701335552187667450206)]
  | _ => []

/-- Input, flag and output masks of each rank-one product. -/
def products : Nat → Bool → List (Nat × Nat × Nat)
  | 7, false => [(1,9362,3), (2,28086,1), (3,18724,2)]
  | 7, true => [(1,18724,3), (2,28086,1), (3,9362,2)]
  | 11, false => [(1,35606,7), (2,40250,5), (4,14964,1), (3,5676,2), (5,45410,4), (6,42830,3)]
  | 11, true => [(1,13416,7), (2,11868,5), (4,38702,1), (3,6708,2), (5,41798,4), (6,47474,3)]
  | 13, false => [(1,41798,7), (2,47474,3), (4,11868,6), (3,6708,2), (5,36122,4), (6,38702,5)]
  | 13, true => [(1,45410,7), (2,42830,3), (4,40250,6), (3,5676,2), (5,11352,4), (6,14964,5)]
  | 19, false => [(11,28180,5), (3,10680,1), (5,14090,10), (4,5340,8), (7,19906,9), (9,21360,6), (1,31432,2), (14,28838,15), (8,2670,4)]
  | 19, true => [(11,10358,5), (3,7572,1), (5,20716,10), (4,15144,8), (7,17330,9), (9,3786,6), (1,4958,2), (14,25870,15), (8,30288,4)]
  | 25, false => [(14,17330,9), (12,7572,8), (2,15144,1), (9,3786,6), (8,4958,4), (13,10358,10), (10,20716,5), (7,25870,15), (1,30288,2)]
  | 25, true => [(14,19906,9), (12,10680,8), (2,5340,1), (9,21360,6), (8,31432,4), (13,28180,10), (10,14090,5), (7,28838,15), (1,2670,2)]
  | 31, false => [(11,2114,3), (1,4228,14), (15,12684,9), (14,10570,4), (2,23254,1), (7,21140,2), (13,16912,12), (4,27482,8), (8,8456,7)]
  | 31, true => [(11,16912,3), (1,8456,14), (15,12684,9), (14,21140,4), (2,27482,1), (7,10570,2), (13,2114,12), (4,23254,8), (8,4228,7)]
  | 37, false => [(8,5592,4), (13,14386,24), (5,13022,9), (27,48452,13), (16,60540,2), (3,39490,19), (20,59024,10), (4,54350,8), (31,17632,29), (24,62280,6), (22,34166,21), (1,25574,1), (2,43164,18)]
  | 37, true => [(8,19262,4), (13,35574,24), (5,7306,9), (27,42510,13), (16,20630,2), (3,61882,19), (20,50922,10), (4,55904,8), (31,48550,29), (24,36308,6), (22,11512,21), (1,59922,1), (2,60720,18)]
  | 41, false => [(2,38524,8), (31,50922,25), (20,63128,7), (24,14160,14), (16,55904,21), (8,60720,26), (13,35574,17), (12,49608,19), (9,42510,16), (3,56642,31), (22,24804,1), (18,19484,3), (5,26566,4)]
  | 41, true => [(2,2796,8), (31,59024,25), (20,20792,7), (24,31954,14), (16,54350,21), (8,43164,26), (13,14386,17), (12,11754,19), (9,48452,16), (3,7988,31), (22,23508,1), (18,56994,3), (5,37038,4)]
  | 47, false => [(9,48344,2), (13,58036,27), (5,2282,3), (24,59998,17), (6,42470,6), (30,39684,1), (23,10204,8), (26,50536,26), (12,46130,9), (8,54460,31), (16,16098,14), (25,26724,22), (10,4564,5)]
  | 47, true => [(9,11144,2), (13,31896,27), (5,27892,3), (24,4204,17), (6,28934,6), (30,59740,1), (23,49876,8), (26,48716,26), (12,18300,9), (8,34870,31), (16,39002,14), (25,41918,22), (10,13946,5)]
  | 55, false => [(16,63088,17), (20,28884,25), (24,9788,21), (3,64312,18), (27,7766,7), (2,13602,1), (8,3400,4), (5,38330,27), (10,23456,5), (17,56580,2), (13,39154,31), (14,34468,13), (4,14442,8)]
  | 55, true => [(16,41558,17), (20,28578,25), (24,5994,21), (3,17580,18), (27,51246,7), (2,14782,1), (8,59130,4), (5,58144,27), (10,40498,5), (17,21446,2), (13,1498,31), (14,52724,13), (4,57156,8)]
  | 59, false => [(5,61840,4), (24,16758,16), (22,41558,19), (18,32018,8), (17,35160,10), (8,28578,15), (14,11022,25), (20,52724,30), (9,51246,26), (10,40498,2), (2,39912,13), (15,62538,6), (1,55966,31)]
  | 59, true => [(5,11124,4), (24,25546,16), (22,63088,19), (18,52762,8), (17,32156,10), (8,28884,15), (14,35820,25), (20,34468,30), (9,7766,26), (10,23456,2), (2,50002,13), (15,45958,6), (1,41112,31)]
  | 61, false => [(1,3486,2), (16,63792,16), (3,59740,18), (24,31896,30), (31,44576,5), (2,58562,11), (8,34216,17), (5,13946,25), (20,49876,15), (13,46034,24), (22,9750,13), (4,15332,22), (27,38340,21)]
  | 61, true => [(1,18258,2), (16,29018,16), (3,39684,18), (24,58036,30), (31,12086,5), (2,56406,11), (8,37870,17), (5,4564,25), (20,10204,15), (13,33338,24), (22,64394,13), (4,22150,22), (27,31152,21)]
  | 67, false => [(25,678,42), (56,26936,9), (33,27550,35), (23,55528,13), (32,35872,14), (55,21704,3), (29,21282,34), (30,40030,16), (3,53116,50), (19,35180,62), (6,31046,22), (21,61482,40), (28,46236,23), (48,51760,18), (44,32428,5)]
  | 67, true => [(25,55876,42), (56,35450,9), (33,20542,35), (23,62380,13), (32,13694,14), (55,50898,3), (29,29108,34), (30,17172,16), (3,12960,50), (19,22620,62), (6,64528,22), (21,42060,40), (28,5364,23), (48,24450,18), (44,19318,5)]
  | 73, false => [(1,32190,8), (8,36936,9), (9,60918,1), (7,28728,55), (56,61944,14), (63,33216,57), (53,5386,21), (30,48478,58), (43,43092,47), (51,6284,35), (46,56558,60), (29,50274,31), (4,2308,16), (32,16672,18), (36,18468,2)]
  | 73, true => [(1,60918,8), (8,36936,9), (9,32190,1), (7,57456,55), (56,64638,14), (63,7182,57), (53,34114,21), (30,54762,58), (43,20648,47), (51,35012,35), (46,47580,60), (29,12568,31), (4,1154,16), (32,9234,18), (36,8336,2)]
  | 87, false => [(41,44950,11), (32,25760,9), (9,52022,2), (7,5048,63), (24,53208,14), (31,56416,49), (37,11482,43), (38,16806,23), (3,28028,60), (11,37108,48), (30,60126,17), (21,31274,33), (52,10292,22), (16,12880,18), (36,6756,4)]
  | 87, true => [(41,32108,11), (32,18838,9), (9,13562,2), (7,29190,63), (24,64738,14), (31,36580,49), (37,52542,43), (38,24740,23), (3,44442,60), (11,49748,48), (30,54736,17), (21,6020,33), (52,1318,22), (16,37676,18), (36,38410,4)]
  | 91, false => [(1,49342,44), (24,30616,9), (25,46886,37), (55,53896,1), (8,14408,14), (63,60096,15), (61,43778,59), (30,46558,46), (35,7900,21), (11,47412,25), (14,64014,40), (5,17210,49), (44,9324,3), (32,40864,18), (12,48076,17)]
  | 91, true => [(1,15224,44), (24,48938,9), (25,33874,37), (55,54732,1), (8,44342,14), (63,30970,15), (61,56894,59), (30,51852,46), (35,5298,21), (11,12426,25), (14,55440,40), (5,59418,49), (44,63322,3), (32,35086,18), (12,32340,17)]
  | 97, false => [(25,53798,20), (8,32264,9), (17,44078,29), (55,6984,24), (56,54776,14), (15,52912,22), (45,50898,56), (62,13694,57), (19,62380,1), (3,4028,13), (14,40590,63), (13,37170,50), (4,48900,40), (40,10728,18), (44,38636,58)]
  | 97, true => [(25,57428,20), (8,62092,9), (17,4824,29), (55,5426,24), (56,41736,14), (15,46650,22), (45,21704,56), (62,35872,57), (19,55528,1), (3,41390,13), (14,56740,63), (13,31754,50), (4,58648,40), (40,55886,18), (44,16214,58)]
  | 103, false => [(17,33070,23), (24,7064,9), (9,39606,30), (15,54704,26), (8,63112,14), (7,9016,20), (37,56986,1), (62,7550,44), (27,50148,45), (59,35332,33), (46,61550,42), (21,31338,11), (36,45732,46), (40,49000,18), (12,3532,60)]
  | 103, true => [(17,22110,23), (24,57262,9), (9,35312,30), (15,12606,26), (8,38196,14), (7,41994,20), (37,61658,1), (62,41238,44), (27,20940,45), (59,38842,33), (46,60300,42), (21,31798,11), (36,60446,46), (40,21314,18), (12,48988,60)]
  | 109, false => [(41,8854,24), (56,9272,9), (17,1710,17), (15,22320,16), (24,46296,14), (23,58344,30), (21,41066,39), (22,15830,19), (3,40380,52), (51,54732,56), (54,44342,21), (5,30970,45), (28,4636,48), (40,64680,18), (52,61108,34)]
  | 109, true => [(41,63204,24), (56,42984,9), (17,20748,17), (15,13474,16), (24,3602,14), (23,15024,30), (21,4302,39), (22,37298,19), (3,33148,52), (51,53896,56), (54,14408,21), (5,60096,45), (28,20432,48), (40,24038,18), (52,4662,34)]
  | 115, false => [(57,20358,55), (8,19720,9), (49,654,62), (7,50424,11), (16,21712,14), (23,36904,5), (37,61658,26), (22,41238,41), (51,20940,51), (27,31652,63), (14,47310,47), (21,50026,16), (4,42628,29), (56,32440,18), (60,55356,15)]
  | 115, true => [(57,54102,55), (8,45018,9), (49,31884,62), (7,13676,11), (16,64930,14), (23,51406,5), (37,56986,26), (22,7550,41), (51,50148,51), (27,14496,63), (14,20230,47), (21,30630,16), (4,24500,29), (56,1766,18), (60,22866,15)]
  | 117, false => [(25,60262,13), (48,19632,9), (41,42966,4), (39,51224,37), (8,62344,14), (47,15248,43), (45,24082,42), (46,63150,59), (3,43196,17), (19,32108,29), (22,18838,61), (5,13562,32), (12,2636,26), (24,9816,18), (20,11284,8)]
  | 117, true => [(25,46578,13), (48,19604,9), (41,63846,4), (39,1262,37), (8,29686,14), (47,30488,43), (45,7818,42), (46,23490,59), (3,17736,17), (19,44950,29), (22,25760,61), (5,52022,32), (12,37914,26), (24,39208,18), (20,3378,8)]
  | 283, false => [(86,4694,136), (76,30540,36), (26,25882,172), (50,3634,240), (196,53956,56), (246,56566,200), (128,22656,71), (205,24882,205), (77,14770,138), (66,65346,229), (200,35272,119), (138,30346,146), (166,48038,72), (141,19826,67), (43,63188,11), (16,19216,43), (217,35878,34), (201,50998,9), (233,20758,30), (163,21340,7), (74,586,25), (249,6662,50), (122,57210,60), (131,50556,14)]
  | 283, true => [(86,25242,136), (76,43296,36), (26,52154,172), (50,48364,240), (196,12736,56), (246,36140,200), (128,51598,71), (205,64406,205), (77,12824,138), (66,17848,229), (200,3068,119), (138,20036,146), (166,21056,72), (141,26762,67), (43,15050,11), (16,19568,43), (217,56500,34), (201,37060,9), (233,46844,30), (163,41514,7), (74,5334,25), (249,64140,50), (122,32414,60), (131,33810,14)]
  | 313, false => [(155,57956,171), (242,1266,128), (105,59030,43), (81,942,37), (216,2264,23), (137,2934,50), (174,54446,84), (154,25754,254), (52,45108,170), (169,17494,45), (201,38198,33), (96,53600,12), (205,28978,57), (121,64902,86), (180,36020,111), (167,58200,228), (168,49832,97), (15,8688,133), (179,7244,200), (158,32926,148), (45,40146,92), (20,65300,184), (54,16950,169), (34,48418,17)]
  | 313, true => [(155,39196,171), (242,15488,128), (105,42396,43), (81,55040,37), (216,27714,23), (137,47938,50), (174,54446,84), (154,25754,254), (52,45108,170), (169,43146,45), (201,45734,33), (96,6700,12), (205,12856,57), (121,34558,86), (180,46278,111), (167,27422,228), (168,21772,97), (15,15890,133), (179,51426,200), (158,58372,148), (45,11494,92), (20,41980,184), (54,45320,169), (34,4852,17)]
  | _, _ => []

/-- Per erased input coordinate, bits k*d+j select CZ(tag[k], output[j]). -/
def eraseMasks : Nat → Bool → List Nat
  | 7, false => [954437176, 477218588]
  | 7, true => [749914924, 886263092]
  | 11, false => [73366397898640, 215273929855728, 179310540924904]
  | 11, true => [177498600732904, 249809912568632, 214364201661552]
  | 13, false => [108837207532824, 248392170031736, 177289623630760]
  | 13, true => [177870652452328, 109518228609432, 73546383957712]
  | 19, false => [672036325805778464, 856976472988007008, 493195967688046016, 910094624233094032]
  | 19, true => [175355288354305424, 478250024237092528, 889245052255243616, 702410165007424192]
  | 25, false => [711540861358474544, 265375212226485088, 458393767547316176, 317490383610301072]
  | 25, true => [240986334144953744, 482254078858816048, 969010726820169056, 696962713456178752]
  | 31, false => [709071326929344288, 822030861247146096, 1015228432634484432, 354535663464672144]
  | 31, true => [179458060983631248, 542314836382942896, 964299005465813472, 702069630206328384]
  | 37, false => [229654388483330148765792, 497088824562340280901856, 1067955561146355649008000, 963545632539502301226752, 719307955772544808307232]
  | 37, true => [565500812776888266303008, 1129784140478963243108448, 801746075996135820375744, 433562712194768571525504, 906083758922943343710976]
  | 41, false => [1133310547111984692991072, 1018736904082354618248384, 827330539471111762008480, 877764723448325557528320, 547784254931537445407264]
  | 41, true => [963445082342737122600480, 719146089613032727857248, 267182184961441316607168, 855367864524630465088384, 462851539998361662591744]
  | 47, false => [862901738216168414944320, 1036708298593445185560800, 45670403294089704496544, 820187776336349368788736, 431450887140624122465824]
  | 47, true => [601862031892299275478560, 611972083399728695306848, 549549617155897735542464, 754643069971889811278720, 300322273954683835192064]
  | 55, false => [382641142887663162235968, 1147740111716028843205856, 903469636326166533199232, 599192855708120785529632, 814673505611918413090336]
  | 55, true => [848808367790259198420512, 1003614872869445734443616, 126061163767984225269440, 250903726661361089964416, 1029456813034458419507456]
  | 59, false => [1054266541558843791874112, 459291171018383807753408, 918619235489697409063328, 427097643568305035160352, 508243805428468291456544]
  | 59, true => [804576838107914881656352, 1165876299966255492442720, 1122827933274536394773696, 574525985835192844733312, 383398953668386399416576]
  | 61, false => [1075743220590989945409632, 981520181078689477960928, 550092950020380898188704, 52925607832739044110112, 1161224562476915162270240]
  | 61, true => [1008777490981172863755808, 809808564982982325913696, 619412963217301440329408, 1036726338877050978208640, 504407173656762459582720]
  | 67, false => [30588138722095498866395209856, 50598683261311998531331465600, 21949856472897642872947426048, 43899410640553691736579671552, 8570654043323645973219843072, 15903367973556921048003131456]
  | 67, true => [14036009072113560608353622080, 35879636729802525448719771840, 70521031188847034041713709440, 61794557049180989316974027520, 43123011472178205974199879168, 7017855781512567711329324032]
  | 73, false => [11862924987758325478818074816, 22487910010000513985322987904, 44956477208039838330453582656, 1473121591660438710238217728, 2965581347837190515028728832, 5931464854494948422159837248]
  | 73, true => [10282260121001544265194870848, 20545177356255204070335848640, 39852410024645802697222541696, 11338521953728951718424980224, 22677346065125553722392004096, 45374030220980725719474801664]
  | 87, false => [44935951233686786423710052480, 56740250123907747741588296128, 79110572872051152081838232320, 77755043264339567056821073472, 31964647763182292342447873024, 62691355487061194409550428224]
  | 87, true => [49877622455325042542811355200, 70400697843045829366508103872, 30907261399504656261484599680, 61814527595144757219149914880, 13092987041931238433794575872, 24948331554800147409505651712]
  | 91, false => [42402342567445255730505736320, 49216497905751769954740384128, 19223873878916147192667398976, 75873837541575310771131954752, 30717111244224379611656297472, 61434222561064799615034734656]
  | 91, true => [53649797846058870105262331968, 75512182672977972666766665920, 71776553063621765913164009856, 30487046610624155089459587840, 32300707611155401295536999936, 65820012522287620898765704192]
  | 97, false => [49927146720614050743789572288, 21883409057014509696964927872, 43786463084811062297100632832, 9583010647311636695918482944, 17947428864587172018426297408, 65196473521930891065646262336]
  | 97, true => [15393457047483466653354104896, 30786616587031715428833042624, 61554192666209486673655386496, 42661630315502207977082102528, 7333340461249038246342116864, 8315696219103679574455714816]
  | 103, false => [8099922055691331079981002880, 14357407765349195961917804992, 20702016577428309551082717952, 41404033082204831389475051008, 3579903649010141002395364416, 4059781151485849068266731584]
  | 103, true => [25597078949574757091356645440, 76694224831344504075008420032, 58563823173377439987496212864, 39137726029443568542736098048, 78294790149616473814336095744, 53021919344438007665293100032]
  | 109, false => [53621776331561638011601436864, 28015385425339252581520937408, 7535484651784808429007233856, 48880257572770282585226909184, 19789942510130601760797834304, 66424818270283040662157142080]
  | 109, true => [43427125757969561386463205440, 7645427092422422249538724032, 58543889237187695102527756672, 74923093059987441648325208832, 70637068982351999305272477184, 21094743938176056470392636416]
  | 115, false => [26834581042408648535654817920, 79169367711168578526976450944, 77872632869940646563156677376, 76497760412521140331249837632, 58492549679172879283951578176, 13417290557521208760791349312]
  | 115, true => [60080956371739617137961408576, 20563939783696836756136077504, 41128177076499831620409381248, 3047232221529444568057291520, 64857309044291228525985943040, 30040478222763298914877801472]
  | 117, false => [13091269810468810109328572608, 24944901813107147930395509184, 44410461015687059586814923520, 8354819404037429478188299840, 9808594046001501128317811776, 6555306311791460627063908416]
  | 117, true => [24239050578996921495418509376, 47259801442045629073451524288, 39375752564435489934139414912, 78751807285385985726110671616, 56550816372953132408026844672, 12110007322967615326479680512]
  | 283, false => [52602031676736367413248923353460638208, 140520928625548622646129741769523004928, 279717821552479145071727388243233475840, 173202911542228966511521203012145715456, 45243663614461213149818532418250878976, 90482134852836942605930295344976912384, 182293477418739717164085855681907900416, 25639008129955050143764290933702754560]
  | 283, true => [139338618423628186030465377414525583616, 246519482326293722472084283805483041536, 154080633351347199993357873600902006272, 190116420365351022976903518774522186752, 157999202970778498586636918336980817920, 315993213723617144554008037498370404352, 290374852733693555112596878613617336320, 240472510561205854021778985680287875072]
  | 313, false => [86574122467770779953795156791093691136, 173143032276735773904205677580161582592, 7332905266369540116364833554452385024, 98576252841582957615955734761837369600, 282391538300275961424438932662373200128, 309402851572592339845408056026813456384, 277188915931602765545428251307468242944, 212761024367214013275351473852128592128]
  | 313, true => [6688046472168239524582798916092788992, 14710533598308215609658750488274928384, 30755507692442527242189973503655347712, 57564502058839421396534495972898278400, 109765642462373350960089968752675035136, 212848517588809139383989592701083889664, 86743896332003592331333701489212284928, 173487813025955640041948416362711924736]
  | 255, false => [0, 40567295238506862995294117691520, 81453979008339169098698881778048, 162910433896766132330018776318848, 325820887288650920938687531403136, 651641774728426792701240566517632, 1303283549458043400395235399131008]
  | 255, true => [0, 40567295238506862995294117691520, 122016322486670443828750973944064, 284597464331759956520175052816896, 610079155743771996400618005660672, 1260725606574925904972664625301504, 2562332945007212208710945928908800]
  | 257, false => [0, 1329248278504009256834117639467958528, 2663709136277370641153569795824747264, 5327438554964349656344047508057622272, 10654877189467560484959875181515706112, 21309754379244610702107578301418184448, 42619508758490435052401254101656354560, 85239017516980874827168991072957923072]
  | 257, true => [0, 1329248278504009256834117639467958528, 3992916849962163149913871602476450304, 9315061696018727182624952928012731392, 19964564046318671231789345126251497472, 41258376370831861988224979953584181248, 83851173034307174677054636532792565760, 169031574064399265227085137719903404032]
  | 21, false => [12984042326850909232, 7525579197569984624, 7332108020503111104, 15749302140901972624]
  | 21, true => [13083014871924389264, 7651748164377537072, 7052854040635728352, 15186308173458494144]
  | 471, true => [9367455389391041106394642083152494848, 12072990206188763508193833572811047680, 28117657431239025963930976349034219008, 57569735155121502609875207111970524160, 108425950549963797921285720607598876672, 215522673183681536419572931442049036288, 88088844312693359604556431086171774976, 174827507303748157749887098463088295936]
  | 471, false => [257048253033682677601934886936900993536, 88574477695036615835485239415962928896, 91904071195901608150842409912829807616, 183813314326713291046184091686338763008, 283057442741692334309474518517414965248, 224498098349029708062005899248762249472, 192282211806401519189661953759841009920, 298000695939803426885384380317186621696]
  | _, _ => []

/-- Exact T, M, forward slots and inverse slots for the physical barrel. -/
def measuredCosts : Nat → Nat × Nat × Nat × Nat
  | 31 => (60,9,1952,1948)
  | 39 => (78,17,3160,3156)
  | 46 => (95,16,4025,3947)
  | 54 => (114,32,6373,6323)
  | 61 => (132,31,7201,7137)
  | 69 => (152,31,8314,8250)
  | 76 => (169,38,10229,10225)
  | 84 => (189,38,11561,11557)
  | 91 => (207,61,15093,15099)
  | 99 => (227,61,16628,16634)
  | 106 => (245,56,17932,17913)
  | 113 => (262,67,20331,20344)
  | 120 => (281,82,23652,23654)
  | 128 => (301,82,25620,25622)
  | _ => (0,0,0,0)

def measuredField : Nat → Nat × Nat × Nat × Nat
  | 3 => (0,0,0,0)
  | 7 => (3,0,35,35)
  | 11 => (6,3,210,210)
  | 13 => (6,3,214,210)
  | 19 => (9,4,331,331)
  | 25 => (9,4,331,331)
  | 31 => (7,0,81,81)
  | 37 => (13,5,509,534)
  | 41 => (13,5,534,521)
  | 47 => (13,5,540,529)
  | 55 => (13,5,519,532)
  | 59 => (13,5,532,533)
  | 61 => (13,5,525,542)
  | 67 => (15,6,707,633)
  | 73 => (13,0,129,129)
  | 87 => (15,6,692,681)
  | 91 => (15,6,663,702)
  | 97 => (15,6,661,707)
  | 103 => (15,6,678,736)
  | 109 => (15,6,698,631)
  | 115 => (15,6,720,714)
  | 117 => (15,6,689,696)
  | 283 => (24,8,1123,1154)
  | 313 => (20,0,153,153)
  | 471 => (20,0,166,166)
  | 255 => (11,0,85,85)
  | 257 => (12,0,92,92)
  | 21 => (7,0,99,99)
  | _ => (0,0,0,0)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrelData ====

-- ==== begin CRTBarrel ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Arithmetic.MappedCompressed

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

def fieldDegree (p : Nat) : Nat := Nat.log2 p

def mulX (p d a : Nat) : Nat :=
  let b := 2 * a
  if b.testBit d then b ^^^ p else b

def powers (p d n : Nat) : Array Nat := Id.run do
  let mut a := 1
  let mut out := #[]
  for _ in [:n] do
    out := out.push a
    a := mulX p d a
  return out

def residues (n : Nat) : Array Nat := Id.run do
  let mut rows := #[]
  for (p, m) in schedule n do
    let d := fieldDegree p
    let cols := powers p d n
    for j in [:m] do
      for k in [:d] do
        let mut row := 0
        for i in [:n] do
          if (i &&& j) == j && cols[i]!.testBit k then
            row := row ||| (1 <<< i)
        rows := rows.push row
  return rows

def selected (n mask : Nat) : List Nat := (List.range n).filter (fun i => mask.testBit i)

def elimStep (n i : Nat) (row : Nat × Nat) : List (Nat × Nat) :=
  (if row.1 < n then [(row.1,i)] else []) ++ (selected n row.2).map (fun j => (i,j))

def basisNetwork (n : Nat) : List (Nat × Nat) :=
  ((pivots n).zipIdx.flatMap (fun (row,i) => elimStep n i row)).reverse

def revCore7 : Program := [
  .CX 20 16, .CX 23 16, .CX 26 16, .CX 29 16, .CX 32 16, .CX 1 0,
  .CCX 16 0 1, .CX 1 0, .CX 19 16, .CX 20 16, .CX 22 16, .CX 23 16,
  .CX 25 16, .CX 26 16, .CX 28 16, .CX 29 16, .CX 31 16, .CX 32 16,
  .CCX 16 0 1, .CX 20 16, .CX 23 16, .CX 26 16, .CX 29 16, .CX 32 16,
  .CCX 16 1 0, .CX 19 16, .CX 20 16, .CX 22 16, .CX 23 16, .CX 25 16,
  .CX 26 16, .CX 28 16, .CX 29 16, .CX 31 16, .CX 32 16
]

def revCore21 : Program := [
  .CX 20 16, .CX 21 16, .CX 23 16, .CX 26 16, .CX 27 16, .CX 29 16,
  .CX 32 16, .CX 33 16, .CX 2 1, .CX 2 0, .CX 2 3, .CCX 16 1 2,
  .CX 2 3, .CX 2 0, .CX 2 1, .CX 19 16, .CX 20 16, .CX 25 16,
  .CX 26 16, .CX 31 16, .CX 32 16, .CX 1 0, .CX 2 0, .CX 3 0,
  .CCX 16 0 3, .CX 3 0, .CX 2 0, .CX 1 0, .CX 20 16, .CX 21 16,
  .CX 23 16, .CX 26 16, .CX 27 16, .CX 29 16, .CX 32 16, .CX 33 16,
  .CX 3 2, .CX 3 1, .CCX 16 2 3, .CX 3 1, .CX 3 2, .CX 19 16,
  .CX 20 16, .CX 22 16, .CX 23 16, .CX 25 16, .CX 26 16, .CX 28 16,
  .CX 29 16, .CX 31 16, .CX 32 16, .CX 0 1, .CX 0 2, .CCX 16 3 0,
  .CX 0 2, .CX 0 1, .CX 20 16, .CX 21 16, .CX 23 16, .CX 26 16,
  .CX 27 16, .CX 29 16, .CX 32 16, .CX 33 16, .CX 0 3, .CCX 16 1 0,
  .CX 0 3, .CX 19 16, .CX 21 16, .CX 23 16, .CX 25 16, .CX 27 16,
  .CX 29 16, .CX 31 16, .CX 33 16, .CX 2 0, .CX 3 0, .CCX 16 0 2,
  .CX 3 0, .CX 2 0, .CX 20 16, .CX 21 16, .CX 23 16, .CX 26 16,
  .CX 27 16, .CX 29 16, .CX 32 16, .CX 33 16, .CX 2 1, .CCX 16 1 0,
  .CX 2 1, .CX 19 16, .CX 21 16, .CX 22 16, .CX 25 16, .CX 27 16,
  .CX 28 16, .CX 31 16, .CX 33 16
]

def revCore31 : Program := [
  .CX 21 16, .CX 26 16, .CX 31 16, .CX 0 1, .CX 0 2, .CCX 16 3 0,
  .CX 0 2, .CX 0 1, .CX 19 16, .CX 20 16, .CX 21 16, .CX 24 16,
  .CX 25 16, .CX 26 16, .CX 29 16, .CX 30 16, .CX 31 16, .CX 3 1,
  .CCX 16 1 3, .CX 3 1, .CX 19 16, .CX 22 16, .CX 24 16, .CX 27 16,
  .CX 29 16, .CX 32 16, .CX 2 1, .CCX 16 1 2, .CX 2 1, .CX 19 16,
  .CX 20 16, .CX 24 16, .CX 25 16, .CX 29 16, .CX 30 16, .CX 1 2,
  .CX 1 3, .CCX 16 0 1, .CX 1 3, .CX 1 2, .CX 19 16, .CX 20 16,
  .CX 21 16, .CX 24 16, .CX 25 16, .CX 26 16, .CX 29 16, .CX 30 16,
  .CX 31 16, .CX 2 0, .CCX 16 0 2, .CX 2 0, .CX 19 16, .CX 22 16,
  .CX 24 16, .CX 27 16, .CX 29 16, .CX 32 16, .CX 0 2, .CX 0 3,
  .CCX 16 1 0, .CX 0 3, .CX 0 2, .CX 20 16, .CX 22 16, .CX 25 16,
  .CX 27 16, .CX 30 16, .CX 32 16, .CX 3 2, .CCX 16 2 3, .CX 3 2,
  .CX 19 16, .CX 21 16, .CX 22 16, .CX 24 16, .CX 26 16, .CX 27 16,
  .CX 29 16, .CX 31 16, .CX 32 16
]

def revCore73 : Program := [
  .CX 24 16, .CX 25 16, .CX 26 16, .CX 33 16, .CCX 16 3 0, .CX 21 16,
  .CX 22 16, .CX 23 16, .CX 30 16, .CX 31 16, .CX 32 16, .CCX 16 0 3,
  .CX 24 16, .CX 25 16, .CX 26 16, .CX 33 16, .CCX 16 3 0, .CX 21 16,
  .CX 22 16, .CX 24 16, .CX 25 16, .CX 30 16, .CX 31 16, .CX 33 16,
  .CCX 16 4 1, .CX 20 16, .CX 21 16, .CX 22 16, .CX 29 16, .CX 30 16,
  .CX 31 16, .CCX 16 1 4, .CX 23 16, .CX 24 16, .CX 25 16, .CX 32 16,
  .CX 33 16, .CCX 16 4 1, .CX 20 16, .CX 21 16, .CX 23 16, .CX 24 16,
  .CX 29 16, .CX 30 16, .CX 32 16, .CX 33 16, .CCX 16 5 2, .CX 19 16,
  .CX 20 16, .CX 21 16, .CX 28 16, .CX 29 16, .CX 30 16, .CCX 16 2 5,
  .CX 22 16, .CX 23 16, .CX 24 16, .CX 31 16, .CX 32 16, .CX 33 16,
  .CCX 16 5 2, .CX 21 16, .CX 22 16, .CX 23 16, .CX 25 16, .CX 26 16,
  .CX 30 16, .CX 31 16, .CX 32 16, .CX 1 0, .CCX 16 0 1, .CX 1 0,
  .CX 20 16, .CX 23 16, .CX 26 16, .CX 29 16, .CX 32 16, .CX 2 0,
  .CCX 16 0 2, .CX 2 0, .CX 19 16, .CX 20 16, .CX 22 16, .CX 23 16,
  .CX 25 16, .CX 26 16, .CX 28 16, .CX 29 16, .CX 31 16, .CX 32 16,
  .CX 2 1, .CCX 16 1 2, .CX 2 1, .CX 19 16, .CX 22 16, .CX 25 16,
  .CX 28 16, .CX 31 16, .CX 4 3, .CCX 16 3 4, .CX 4 3, .CX 20 16,
  .CX 23 16, .CX 26 16, .CX 29 16, .CX 32 16, .CX 5 3, .CCX 16 3 5,
  .CX 5 3, .CX 19 16, .CX 20 16, .CX 22 16, .CX 23 16, .CX 25 16,
  .CX 26 16, .CX 28 16, .CX 29 16, .CX 31 16, .CX 32 16, .CX 5 4,
  .CCX 16 4 5, .CX 5 4, .CX 20 16, .CX 23 16, .CX 26 16, .CX 29 16,
  .CX 32 16
]

def primaryShift8 : Program := [
  .CX 19 16, .CX 21 16, .CX 23 16, .CX 25 16, .CX 27 16, .CX 29 16,
  .CX 31 16, .CX 33 16, .CCX 16 0 1, .CCX 16 2 3, .CCX 16 4 5, .CCX 16 6 7,
  .CX 20 16, .CX 21 16, .CX 24 16, .CX 25 16, .CX 28 16, .CX 29 16,
  .CX 32 16, .CX 33 16, .CX 1 0, .CCX 16 0 2, .CX 1 0, .CX 5 4,
  .CCX 16 4 6, .CX 5 4, .CX 19 16, .CX 21 16, .CX 23 16, .CX 25 16,
  .CX 27 16, .CX 29 16, .CX 31 16, .CX 33 16, .CX 2 3, .CCX 16 1 2,
  .CX 2 3, .CX 6 7, .CCX 16 5 6, .CX 6 7, .CX 19 16, .CX 22 16,
  .CX 24 16, .CX 25 16, .CX 27 16, .CX 30 16, .CX 32 16, .CX 33 16,
  .CX 1 0, .CX 2 0, .CX 3 0, .CCX 16 0 4, .CX 3 0, .CX 2 0,
  .CX 1 0, .CX 19 16, .CX 23 16, .CX 27 16, .CX 31 16, .CX 3 1,
  .CX 4 5, .CCX 16 1 4, .CX 4 5, .CX 3 1, .CX 20 16, .CX 24 16,
  .CX 28 16, .CX 32 16, .CX 3 2, .CX 4 6, .CCX 16 2 4, .CX 4 6,
  .CX 3 2, .CX 21 16, .CX 25 16, .CX 29 16, .CX 33 16, .CX 4 5,
  .CX 4 6, .CX 4 7, .CCX 16 3 4, .CX 4 7, .CX 4 6, .CX 4 5,
  .CX 22 16, .CX 23 16, .CX 24 16, .CX 25 16, .CX 30 16, .CX 31 16,
  .CX 32 16, .CX 33 16
]

def orderNineSix : Program := [
  .CX 0 1,
  .CX 0 2,
  .CX 5 2,
  .CX 20 16,
  .CX 21 16,
  .CX 24 16,
  .CX 25 16,
  .CX 29 16,
  .CX 30 16,
  .CX 33 16,
  .CCX 16 2 0,
  .CX 5 2,
  .CX 0 2,
  .CX 0 1,
  .CX 5 2,
  .CX 5 3,
  .CCX 16 3 5,
  .CX 5 3,
  .CX 4 2,
  .CX 0 2,
  .CX 21 16,
  .CX 26 16,
  .CX 30 16,
  .CCX 16 2 1,
  .CX 0 2,
  .CX 4 2,
  .CX 3 2,
  .CX 1 2,
  .CX 20 16,
  .CX 21 16,
  .CX 22 16,
  .CX 23 16,
  .CX 29 16,
  .CX 30 16,
  .CX 31 16,
  .CX 32 16,
  .CCX 16 2 4,
  .CX 1 2,
  .CX 3 2,
  .CX 5 2,
  .CX 3 4,
  .CX 3 5,
  .CX 5 0,
  .CX 21 16,
  .CX 26 16,
  .CX 30 16,
  .CCX 16 0 3,
  .CX 5 0,
  .CX 3 5,
  .CX 3 4,
  .CX 2 4,
  .CX 2 3,
  .CX 2 0,
  .CX 21 16,
  .CX 26 16,
  .CX 30 16,
  .CCX 16 0 2,
  .CX 2 0,
  .CX 22 16,
  .CX 23 16,
  .CX 24 16,
  .CX 25 16,
  .CX 31 16,
  .CX 32 16,
  .CX 33 16,
  .CCX 16 4 2,
  .CX 2 3,
  .CX 2 4,
  .CX 0 1,
  .CX 0 2,
  .CX 0 3,
  .CX 19 16,
  .CX 22 16,
  .CX 25 16,
  .CX 28 16,
  .CX 31 16,
  .CCX 16 3 0,
  .CX 0 3,
  .CX 0 2,
  .CX 0 1,
  .CX 4 1,
  .CX 4 5,
  .CCX 16 5 4,
  .CX 4 5,
  .CX 4 1,
  .CX 1 2,
  .CX 2 0,
  .CX 3 0,
  .CX 4 0,
  .CX 21 16,
  .CX 26 16,
  .CX 30 16,
  .CCX 16 0 1,
  .CX 4 0,
  .CX 3 0,
  .CX 2 0,
  .CX 1 3,
  .CX 20 16,
  .CX 22 16,
  .CX 23 16,
  .CX 26 16,
  .CX 29 16,
  .CX 31 16,
  .CX 32 16,
  .CCX 16 3 1,
  .CX 1 3,
  .CX 1 2,
  .CX 0 4,
  .CX 21 16,
  .CX 26 16,
  .CX 30 16,
  .CCX 16 4 0,
  .CX 0 4,
  .CX 3 1,
  .CX 5 1,
  .CX 21 16,
  .CX 26 16,
  .CX 30 16,
  .CCX 16 1 2,
  .CX 5 1,
  .CX 3 1,
  .CX 19 16,
  .CX 20 16,
  .CX 23 16,
  .CX 25 16,
  .CX 26 16,
  .CX 28 16,
  .CX 29 16,
  .CX 32 16
]

def orderSeventeen313 : Program := [
  .CX 4 7,
  .CX 4 6,
  .CX 4 5,
  .CX 4 3,
  .CX 4 0,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 2 6,
  .CX 2 5,
  .CX 2 3,
  .CX 3 2,
  .CX 1 4,
  .CX 4 1,
  .CX 0 3,
  .CX 0 1,
  .CX 19 16,
  .CX 21 16,
  .CX 23 16,
  .CX 25 16,
  .CX 27 16,
  .CX 29 16,
  .CX 31 16,
  .CX 33 16,
  .CCX 16 4 0,
  .CCX 16 5 1,
  .CCX 16 6 2,
  .CCX 16 7 3,
  .CX 3 5,
  .CX 3 4,
  .CX 2 7,
  .CX 2 6,
  .CX 2 3,
  .CX 3 2,
  .CX 1 6,
  .CX 1 5,
  .CX 1 2,
  .CX 2 1,
  .CX 0 6,
  .CX 0 3,
  .CX 0 1,
  .CX 1 0,
  .CX 20 16,
  .CX 21 16,
  .CX 24 16,
  .CX 25 16,
  .CX 28 16,
  .CX 29 16,
  .CX 32 16,
  .CX 33 16,
  .CCX 16 4 0,
  .CCX 16 5 1,
  .CCX 16 6 2,
  .CCX 16 7 3,
  .CX 4 6,
  .CX 4 5,
  .CX 4 3,
  .CX 4 0,
  .CX 3 4,
  .CX 2 6,
  .CX 2 4,
  .CX 2 1,
  .CX 2 0,
  .CX 1 7,
  .CX 1 5,
  .CX 1 3,
  .CX 3 1,
  .CX 0 7,
  .CX 0 3,
  .CX 19 16,
  .CX 21 16,
  .CX 22 16,
  .CX 24 16,
  .CX 27 16,
  .CX 29 16,
  .CX 30 16,
  .CX 32 16,
  .CCX 16 4 0,
  .CCX 16 5 1,
  .CCX 16 6 2,
  .CCX 16 7 3,
  .CX 3 7,
  .CX 3 6,
  .CX 3 5,
  .CX 3 1,
  .CX 2 7,
  .CX 2 3,
  .CX 1 7,
  .CX 1 5,
  .CX 1 2,
  .CX 1 0,
  .CX 2 1,
  .CX 0 7,
  .CX 0 5,
  .CX 0 4,
  .CX 0 1,
  .CX 20 16,
  .CX 21 16,
  .CX 24 16,
  .CX 25 16,
  .CX 26 16,
  .CX 27 16,
  .CX 30 16,
  .CX 31 16,
  .CCX 16 4 0,
  .CCX 16 5 1,
  .CCX 16 6 2,
  .CCX 16 7 3,
  .CX 3 5,
  .CX 3 0,
  .CX 2 6,
  .CX 2 5,
  .CX 2 4,
  .CX 1 7,
  .CX 1 6,
  .CX 1 5,
  .CX 0 6,
  .CX 0 3,
  .CX 22 16,
  .CX 23 16,
  .CX 24 16,
  .CX 25 16,
  .CX 30 16,
  .CX 31 16,
  .CX 32 16,
  .CX 33 16,
  .CCX 16 4 0,
  .CCX 16 5 1,
  .CCX 16 6 2,
  .CCX 16 7 3,
  .CX 3 6,
  .CX 3 4,
  .CX 3 0,
  .CX 2 7,
  .CX 2 6,
  .CX 2 5,
  .CX 2 4,
  .CX 2 1,
  .CX 1 7,
  .CX 1 6,
  .CX 1 2,
  .CX 2 1,
  .CX 0 7,
  .CX 0 6,
  .CX 0 5,
  .CX 26 16,
  .CX 27 16,
  .CX 28 16,
  .CX 29 16,
  .CX 30 16,
  .CX 31 16,
  .CX 32 16,
  .CX 33 16
]

def orderSeventeen471 : Program := [
  .CX 3 7,
  .CX 3 4,
  .CX 3 1,
  .CX 3 0,
  .CX 2 5,
  .CX 2 4,
  .CX 2 3,
  .CX 3 2,
  .CX 1 6,
  .CX 1 5,
  .CX 1 4,
  .CX 1 3,
  .CX 3 1,
  .CX 0 3,
  .CX 0 2,
  .CX 2 0,
  .CX 19 16,
  .CX 21 16,
  .CX 23 16,
  .CX 25 16,
  .CX 27 16,
  .CX 29 16,
  .CX 31 16,
  .CX 33 16,
  .CCX 16 4 0,
  .CCX 16 5 1,
  .CCX 16 6 2,
  .CCX 16 7 3,
  .CX 4 7,
  .CX 4 3,
  .CX 4 1,
  .CX 4 0,
  .CX 3 4,
  .CX 3 2,
  .CX 4 3,
  .CX 2 7,
  .CX 2 6,
  .CX 2 3,
  .CX 3 2,
  .CX 1 6,
  .CX 1 5,
  .CX 1 2,
  .CX 2 1,
  .CX 0 7,
  .CX 0 3,
  .CX 0 1,
  .CX 20 16,
  .CX 21 16,
  .CX 24 16,
  .CX 25 16,
  .CX 28 16,
  .CX 29 16,
  .CX 32 16,
  .CX 33 16,
  .CCX 16 4 0,
  .CCX 16 5 1,
  .CCX 16 6 2,
  .CCX 16 7 3,
  .CX 3 6,
  .CX 3 4,
  .CX 2 5,
  .CX 1 7,
  .CX 1 5,
  .CX 1 3,
  .CX 3 1,
  .CX 0 6,
  .CX 0 3,
  .CX 0 2,
  .CX 2 0,
  .CX 19 16,
  .CX 21 16,
  .CX 22 16,
  .CX 24 16,
  .CX 27 16,
  .CX 29 16,
  .CX 30 16,
  .CX 32 16,
  .CCX 16 4 0,
  .CCX 16 5 1,
  .CCX 16 6 2,
  .CCX 16 7 3,
  .CX 4 0,
  .CX 3 5,
  .CX 3 1,
  .CX 3 0,
  .CX 2 5,
  .CX 2 4,
  .CX 2 3,
  .CX 2 1,
  .CX 3 2,
  .CX 1 6,
  .CX 1 4,
  .CX 1 3,
  .CX 1 2,
  .CX 1 0,
  .CX 0 7,
  .CX 0 4,
  .CX 0 3,
  .CX 3 0,
  .CX 20 16,
  .CX 21 16,
  .CX 24 16,
  .CX 25 16,
  .CX 26 16,
  .CX 27 16,
  .CX 30 16,
  .CX 31 16,
  .CCX 16 4 0,
  .CCX 16 5 1,
  .CCX 16 6 2,
  .CCX 16 7 3,
  .CX 4 0,
  .CX 3 7,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 3 1,
  .CX 2 4,
  .CX 2 3,
  .CX 2 1,
  .CX 2 0,
  .CX 1 7,
  .CX 1 3,
  .CX 1 2,
  .CX 1 0,
  .CX 0 7,
  .CX 0 6,
  .CX 0 4,
  .CX 0 2,
  .CX 0 1,
  .CX 22 16,
  .CX 23 16,
  .CX 24 16,
  .CX 25 16,
  .CX 30 16,
  .CX 31 16,
  .CX 32 16,
  .CX 33 16,
  .CCX 16 4 0,
  .CCX 16 5 1,
  .CCX 16 6 2,
  .CCX 16 7 3,
  .CX 3 7,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 3 1,
  .CX 2 7,
  .CX 2 6,
  .CX 2 3,
  .CX 2 1,
  .CX 2 0,
  .CX 3 2,
  .CX 1 7,
  .CX 1 6,
  .CX 1 4,
  .CX 0 5,
  .CX 0 1,
  .CX 26 16,
  .CX 27 16,
  .CX 28 16,
  .CX 29 16,
  .CX 30 16,
  .CX 31 16,
  .CX 32 16,
  .CX 33 16
]

def fieldCore (p : Nat) (mirror : Bool) : Program := Id.run do
  if p == 7 then return if mirror then revCore7.reverse else revCore7
  if p == 21 then return if mirror then revCore21.reverse else revCore21
  if p == 31 then return if mirror then revCore31.reverse else revCore31
  if p == 73 then return if mirror then orderNineSix.reverse else orderNineSix
  if p == 471 then return if mirror then orderSeventeen471.reverse else orderSeventeen471
  if p == 313 then return if mirror then orderSeventeen313.reverse else orderSeventeen313
  if p == 257 then return if mirror then primaryShift8.reverse else primaryShift8
  let d := fieldDegree p
  if d == 1 then return []
  let xs := List.range d
  let ys := (List.range d).map (8 + ·)
  let (a,b) := (16,17)
  let tags := (List.range 16).map (18 + ·)
  let copy := (xs.zip ys).map (fun (x,y) => Instr.CX x y)
  let ops := (products p mirror).flatMap fun (xm,tm,om) => Id.run do
    let left := (selected d xm).map (fun i => Instr.CX (xs[i]!) a)
    let right := (selected 16 tm).map (fun k => Instr.CX (tags[k]!) b)
    let out := selected d om
    let compute := match out with
      | [] => []
      | j0 :: rest =>
        let fan := rest.map (fun j => Instr.CX (ys[j0]!) (ys[j]!))
        fan ++ [Instr.CCX a b (ys[j0]!)] ++ fan.reverse
    return left ++ right ++ compute ++ right.reverse ++ left.reverse
  let erase := (List.range d).map fun i =>
    let mask := (eraseMasks p mirror)[i]!
    let pairs := (List.range 16).flatMap fun k => (List.range d).filterMap fun j =>
      if mask.testBit (k*d+j) then some (Correction.CZ (tags[k]!) (ys[j]!))
      else none
    Instr.measureX (xs[i]!) [] (.Z (ys[i]!) :: pairs)
  let move := (xs.zip ys).flatMap (fun (x,y) => [Instr.CX y x, Instr.CX x y])
  return copy ++ ops ++ erase ++ move

def fieldPlace (n offset q : Nat) : Wire :=
  if q < 8 then offset + q else if q < 18 then n + 16 + (q-8) else n + (q-18)

def stage (n offset d m h : Nat) : Program :=
  let inc := 2^h
  if m ≤ inc then [] else
  let toggle := ((List.range 16).filter fun k => k.testBit h).map
    (fun k => Instr.CX (n+k) (n+24))
  let mix := (List.range (m-inc)).reverse.flatMap fun j =>
    (List.range d).map (fun i => Instr.CCX (n+24) (offset+d*j+i) (offset+d*(j+inc)+i))
  toggle ++ mix ++ toggle.reverse

def triangular (n offset d m : Nat) : Program :=
  (List.range 4).flatMap (stage n offset d m)

structure R8Step where
  tags : List Nat
  pre : List (Nat × Nat)
  src : Nat
  dst : Nat

def pascalR8Steps (mir : Bool) : List R8Step :=
  if mir then [
    ⟨[8, 9, 10, 11, 12, 13, 14, 15], [(1,0), (2,0), (3,0), (4,0), (5,0), (6,0), (7,0)], 0, 8⟩,
    ⟨[7, 8, 9, 10, 11, 12, 13, 14], [(3,1), (5,1), (7,1), (8,9)], 1, 8⟩,
    ⟨[6, 7, 8, 9, 10, 11, 12, 13], [(3,2), (6,2), (7,2), (8,10)], 2, 8⟩,
    ⟨[5, 6, 7, 8, 9, 10, 11, 12], [(7,3), (8,9), (8,10), (8,11)], 3, 8⟩,
    ⟨[4, 5, 6, 7, 8, 9, 10, 11], [(5,4), (6,4), (7,4), (8,12)], 4, 8⟩,
    ⟨[3, 4, 5, 6, 7, 8, 9, 10], [(7,5), (8,9), (8,12), (8,13)], 5, 8⟩,
    ⟨[2, 3, 4, 5, 6, 7, 8, 9], [(7,6), (8,10), (8,12), (8,14)], 6, 8⟩,
    ⟨[1, 2, 3, 4, 5, 6, 7, 8], [(8,9), (8,10), (8,11), (8,12), (8,13), (8,14), (8,15)], 7, 8⟩
  ]
  else [
    ⟨[1, 2, 3, 4, 5, 6, 7, 8], [(1,0), (2,0), (3,0), (4,0), (5,0), (6,0), (7,0)], 0, 8⟩,
    ⟨[2, 3, 4, 5, 6, 7, 8, 9], [(3,1), (5,1), (7,1), (8,9)], 1, 8⟩,
    ⟨[3, 4, 5, 6, 7, 8, 9, 10], [(3,2), (6,2), (7,2), (8,10)], 2, 8⟩,
    ⟨[4, 5, 6, 7, 8, 9, 10, 11], [(7,3), (8,9), (8,10), (8,11)], 3, 8⟩,
    ⟨[5, 6, 7, 8, 9, 10, 11, 12], [(5,4), (6,4), (7,4), (8,12)], 4, 8⟩,
    ⟨[6, 7, 8, 9, 10, 11, 12, 13], [(7,5), (8,9), (8,12), (8,13)], 5, 8⟩,
    ⟨[7, 8, 9, 10, 11, 12, 13, 14], [(7,6), (8,10), (8,12), (8,14)], 6, 8⟩,
    ⟨[8, 9, 10, 11, 12, 13, 14, 15], [(8,9), (8,10), (8,11), (8,12), (8,13), (8,14), (8,15)], 7, 8⟩
  ]

def r8Step (n off : Nat) (st : R8Step) : Program :=
  let toggle := st.tags.map (fun k => Instr.CX (n+k) (n+24))
  let pre := st.pre.map (fun p => Instr.CX (off+p.1) (off+p.2))
  toggle ++ pre ++ [Instr.CCX (n+24) (off+st.src) (off+st.dst)] ++ pre.reverse ++ toggle.reverse

def pascalR8 (n off : Nat) (mir : Bool) : Program :=
  (pascalR8Steps mir).flatMap (r8Step n off)

def primary (n offset p m : Nat) (mirror : Bool) : Program :=
  let d := fieldDegree p
  let scalar := (List.range m).flatMap fun j =>
    renameProgram (fieldPlace n (offset+d*j)) (fieldCore p mirror)
  let shift := if d == 8 && m == 2 then pascalR8 n offset mirror
    else let t := triangular n offset d m; if mirror then t.reverse else t
  scalar ++ shift

def components (n : Nat) (mirror : Bool) : Nat → List (Nat × Nat) → Program
  | _, [] => []
  | offset, (p,m) :: tail => primary n offset p m mirror ++
      components n mirror (offset + fieldDegree p * m) tail

def logical (n : Nat) (mirror : Bool) : Program :=
  let basis := (basisNetwork n).map (fun (i,j) => Instr.CX i j)
  basis ++ components n mirror 0 (schedule n) ++ basis.reverse

def barrelWidth (s : Nat) : Nat :=
  (if 224 ≤ s+15 ∧ s+15 ≤ 286 then min 256 (511-(s+15)) else if 257 ≤ s+15 then 512-(s+15) else min 257 (Partial.railP (s+15))) - Shadow7.sbP s

def place (s q : Nat) : Wire :=
  let n := barrelWidth s
  if q < n then Shadow7.bankW s q else if q < n+16 then Partial.tagsP.getD (q-n) 1560
  else Shadow7.poolW s (17 + (q-n-16)%10)

def barrel (s : Nat) (mirror : Bool) : Program :=
  renameProgram (place s) (logical (barrelWidth s) mirror)

def barrelT (s : Nat) (_mirror : Bool) : Nat := (measuredCosts (barrelWidth s)).1
def barrelM (s : Nat) (_mirror : Bool) : Nat := (measuredCosts (barrelWidth s)).2.1
def barrelSlots (s : Nat) (mirror : Bool) : Nat :=
  let v := (measuredCosts (barrelWidth s)).2.2
  if mirror then v.2 else v.1

def beforeReference (s : Nat) : List GateMirror.Gate :=
  let b := Shadow7.sbP s
  Shadow7.fix0P s b ++ Partial.leaveFix1 s b ++ Shadow7.fix2P s b ++ Partial.leaveFix3 s b ++
    Partial.leaveFix4 s b ++ Shadow7.leaveFix5Move s b ++ Shadow7.leaveAdjust s

def afterReference (s : Nat) : List GateMirror.Gate :=
  let b := Shadow7.sbP s
  Shadow7.fix8P s b ++ Shadow7.glueG3 s ++ Shadow7.leaveJoinMove s ++ Shadow7.fix10P s b ++
    Partial.leaveFix11 s b ++ Partial.leaveFix12 s b ++ Shadow7.leaveLowStore s ++
    Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

-- ==== begin DeadJoin (credited to spariev 65b176b3) ====
end ECDSAAdd.Entrant.StairPacket.CRTBarrel

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
def wordOpen (a : Wire) : List HighBankJoin.Column → List Gate
  | [] => []
  | r::rs => toggleG a r.hot ++ pairGM r.low a r.shadow r.tube ++ wordOpen a rs

def wordClose (a : Wire) : List HighBankJoin.Column → List Gate
  | [] => []
  | r::rs => wordClose a rs ++ toggleG a r.hot

theorem word_split (a : Wire) (rs tail : List HighBankJoin.Column) :
    wordGM a (rs++tail) = wordOpen a rs ++ (wordGM a tail ++ wordClose a rs) := by
  induction rs with
  | nil => simp [wordGM,wordOpen,wordClose]
  | cons r rs ih => simp only [List.cons_append,wordGM,wordOpen,wordClose,ih,List.append_assoc]

def cols16 (s : Nat) : List HighBankJoin.Column :=
  (List.range 16).map fun i => ⟨decide (i < Shadow7.lowsP s),
    if i < 16 then some (tagsP.getD i 0) else none, Shadow7.a0P s - 1 + i, Shadow7.bankW s i⟩

def lastCol (s : Nat) : HighBankJoin.Column :=
  ⟨false,none,Shadow7.a0P s - 1 + 16,Shadow7.bankW s 16⟩

theorem cols_split : ∀ j : Fin 26, j.val≤24 →
    Shadow7.columnsP (start j) = cols16 (start j) ++ [lastCol (start j)] := by
  intro j hi
  have high : ¬16 < Shadow7.lowsP (start j) := by revert j; decide +kernel
  simp only [Shadow7.columnsP,cols16,List.range_succ,List.map_append,List.map_cons,List.map_nil,
    decide_eq_false high,show ¬16<16 by decide,if_false,lastCol]

def postEntry (s : Nat) : List Gate :=
  leaveFix3 s (Shadow7.sbP s) ++ leaveFix4 s (Shadow7.sbP s) ++
  Shadow7.leaveFix5Move s (Shadow7.sbP s) ++ Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++
  Shadow7.fix8P s (Shadow7.sbP s) ++ Shadow7.glueG3 s ++ keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++ wordOpen 1614 (cols16 s)

def pair16 (s : Nat) : List Gate :=
  [.cx (Shadow7.a0P s - 1 + 16) (Shadow7.bankW s 16),.cx (Shadow7.bankW s 16) (Shadow7.a0P s - 1 + 16),
   .pop 1614 (Shadow7.bankW s 16) (Shadow7.a0P s - 1 + 16)]

def afterWord (s : Nat) : List Gate :=
  wordClose 1614 (cols16 s) ++ Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++
  leaveFix12 s (Shadow7.sbP s) ++ Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++
  Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

theorem post_keeps_checked : ∀ j : Fin 26, j.val≤24 →
    (postEntry (start j)).all (fun g => decide (target g ≠ Shadow7.a0P (start j) - 1 + 16)) = true := by
  decide +kernel


theorem pair_layout_checked : ∀ j : Fin 26, j.val≤24 →
  [1614,Shadow7.a0P (start j) - 1 + 16,Shadow7.bankW (start j) 16].Nodup := by decide +kernel

def shortenedOps (s : Nat) : List Gate :=
  LeaveJ7.entryOps s ++ postEntry s ++ afterWord s



-- Explicit 3d shape; cached 83c has a different kept width.

def referenceOps (s : Nat) : List Gate :=
  Shadow7.fix0P s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s) ++
  leaveFix3 s (Shadow7.sbP s) ++ leaveFix4 s (Shadow7.sbP s) ++ Shadow7.leaveFix5Move s (Shadow7.sbP s) ++
  Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++ Shadow7.fix8P s (Shadow7.sbP s) ++
  Shadow7.glueG3 s ++ (keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++ wordGM 1614 (Shadow7.columnsP s)) ++
  Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++ leaveFix12 s (Shadow7.sbP s) ++
  Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

theorem reference_shape (j : Fin 26) (hi : j.val≤24) :
    referenceOps (start j) = LeaveJ7.entryOps (start j) ++
      (postEntry (start j) ++ (pair16 (start j) ++ afterWord (start j))) := by
  simp only [referenceOps,LeaveJ7.entryOps,postEntry,afterWord,cols_split j hi,word_split,
    wordGM,toggleG,pairGM,lastCol,pair16,Bool.false_eq_true,if_false,
    List.append_nil,List.nil_append,List.append_assoc]

theorem wordOpenClose (a : Wire) (rs : List HighBankJoin.Column) :
    wordGM a rs = wordOpen a rs ++ wordClose a rs := by
  simpa only [List.append_nil,wordGM,List.nil_append] using word_split a rs []

def afterShort (s : Nat) : List Gate :=
  Shadow7.fix8P s (Shadow7.sbP s) ++
  Shadow7.glueG3 s ++ (keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++ wordGM 1614 (cols16 s)) ++
  Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++ leaveFix12 s (Shadow7.sbP s) ++
  Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

theorem shortened_shape (s : Nat) : shortenedOps s = CRTBarrel.beforeReference s ++
    (Shadow7.leaveBarrel s ++ afterShort s) := by
  simp only [shortenedOps,postEntry,afterWord,afterShort,LeaveJ7.entryOps,
    CRTBarrel.beforeReference,wordOpenClose,List.append_assoc]

def scanTail (s : Nat) : List Gate :=
  leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s) ++ postEntry s ++ afterWord s

def scanShortenedOps (s : Nat) : List Gate := DeadScan.fix0M s (Shadow7.sbP s) ++ scanTail s

theorem shortened_scan_shape (s : Nat) : shortenedOps s =
    Shadow7.fix0P s (Shadow7.sbP s) ++ scanTail s := by
  simp only [shortenedOps,LeaveJ7.entryOps,scanTail,List.append_assoc]

theorem scan_physical : ∀ j : Fin 26, j.val≤24 →
    (DeadScan.fix0M (start j) (Shadow7.sbP (start j))).all proper=true := by decide +kernel

def beforeScanTail (s : Nat) : List Gate :=
  leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s) ++
  leaveFix3 s (Shadow7.sbP s) ++ leaveFix4 s (Shadow7.sbP s) ++
  Shadow7.leaveFix5Move s (Shadow7.sbP s) ++ Shadow7.leaveAdjust s

def beforeScan (s : Nat) : List Gate :=
  DeadScan.fix0M s (Shadow7.sbP s) ++ beforeScanTail s

def beforeAll (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s+3) (Shadow7.e0P s+4) 1559 2 (beforeScan s)

def afterAll (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s+3) (Shadow7.e0P s+4) 1559 1 (afterShort s)

def allOps (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s+3) (Shadow7.e0P s+4) 1559 2 (scanShortenedOps s)

theorem scan_shortened_shape (s : Nat) : scanShortenedOps s = beforeScan s ++
    (Shadow7.leaveBarrel s ++ afterShort s) := by
  simp only [scanShortenedOps,scanTail,postEntry,afterWord,beforeScan,beforeScanTail,afterShort,
    wordOpenClose,List.append_assoc]

theorem all_checked : ∀ j : Fin 26, j.val≤24 →
    FlagLeave.check (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) (Shadow7.e0P (start j)+6) 1559
      2 false (scanShortenedOps (start j)) = true := by decide +kernel

theorem before_all_checked : ∀ j : Fin 26, j.val≤24 →
    FlagLeave.check (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) (Shadow7.e0P (start j)+6) 1559
      2 false (beforeScan (start j)) = true := by
  intro j hi
  exact FlagLeave.check_prefix _ _ _ _ 2 false (beforeScan (start j))
    (Shadow7.leaveBarrel (start j) ++ afterShort (start j))
    (by rw [←scan_shortened_shape]; exact all_checked j hi)

theorem removed_before : ∀ j : Fin 26, j.val≤24 →
    FlagLeave.removed (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 2 (beforeScan (start j)) =
      [.make (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559] := by decide +kernel

theorem removed_barrel : ∀ j : Fin 26, j.val≤24 →
    FlagLeave.removed (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 1
      (Shadow7.leaveBarrel (start j)) = [] := by decide +kernel

theorem all_split (j : Fin 26) (hi : j.val≤24) : allOps (start j) =
    beforeAll (start j) ++ (Shadow7.leaveBarrel (start j) ++ afterAll (start j)) := by
  rw [allOps,scan_shortened_shape,FlagLeave.cut_append,removed_before j hi]
  simp only [List.length_singleton,show 2-1=1 by decide]
  rw [FlagLeave.cut_append,removed_barrel j hi]
  simp only [List.length_nil,Nat.sub_zero]
  rw [FlagLeave.cut_of_removed_nil _ _ _ _ _ (removed_barrel j hi)]
  rfl

def afterReference (s : Nat) : List Gate :=
  Shadow7.fix8P s (Shadow7.sbP s) ++
  Shadow7.glueG3 s ++ (keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++ wordGM 1614 (Shadow7.columnsP s)) ++
  Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++ leaveFix12 s (Shadow7.sbP s) ++
  Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

def afterOpen (s : Nat) : List Gate :=
  Shadow7.fix8P s (Shadow7.sbP s) ++ Shadow7.glueG3 s ++ keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++
    wordOpen 1614 (cols16 s)
theorem inverse_append (a b : List Gate) : inverse (a ++ b) = inverse b ++ inverse a := by
  simp only [inverse,List.map_append,List.reverse_append]

theorem cut_metrics (a c : List Gate) (active sh tu : Wire) :
    let old := a ++ ([Gate.cx sh tu,Gate.cx tu sh,Gate.pop active tu sh] ++ c)
    let new := a ++ c
    toffoliCount (GateMirror.forward old) = toffoliCount (GateMirror.forward new) ∧
    toffoliCount (GateMirror.inverse old) = toffoliCount (GateMirror.inverse new)+1 ∧
    measurementCount (GateMirror.forward old) = measurementCount (GateMirror.forward new)+1 ∧
    measurementCount (GateMirror.inverse old) = measurementCount (GateMirror.inverse new) ∧
    gateSlots (GateMirror.forward old) = gateSlots (GateMirror.forward new)+4 ∧
    gateSlots (GateMirror.inverse old) = gateSlots (GateMirror.inverse new)+3 := by
  dsimp only
  simp only [toffoli_forward,toffoli_inverse,meas_forward,meas_inverse,slots_forward,slots_inverse,
    List.countP_append,List.length_append,List.countP_cons,List.countP_nil,List.length_cons,
    List.length_nil,isCCX,isMake,isPop,if_false,if_true,Bool.false_eq_true]
  omega


set_option linter.constructorNameAsVariable false

theorem after_short_metrics (j : Fin 26) (hi : j.val≤24) :
    toffoliCount (GateMirror.forward (afterReference (start j))) =
      toffoliCount (GateMirror.forward (afterShort (start j))) ∧
    toffoliCount (GateMirror.inverse (afterReference (start j))) =
      toffoliCount (GateMirror.inverse (afterShort (start j)))+1 ∧
    measurementCount (GateMirror.forward (afterReference (start j))) =
      measurementCount (GateMirror.forward (afterShort (start j)))+1 ∧
    measurementCount (GateMirror.inverse (afterReference (start j))) =
      measurementCount (GateMirror.inverse (afterShort (start j))) ∧
    gateSlots (GateMirror.forward (afterReference (start j))) =
      gateSlots (GateMirror.forward (afterShort (start j)))+4 ∧
    gateSlots (GateMirror.inverse (afterReference (start j))) =
      gateSlots (GateMirror.inverse (afterShort (start j)))+3 := by
  have oldshape : afterReference (start j) = afterOpen (start j) ++
      (pair16 (start j) ++ afterWord (start j)) := by
    simp only [afterReference,afterOpen,afterWord,cols_split j hi,word_split,wordGM,toggleG,
      pairGM,lastCol,pair16,Bool.false_eq_true,if_false,List.append_nil,List.nil_append,List.append_assoc]
  have newshape : afterShort (start j) = afterOpen (start j) ++ afterWord (start j) := by
    simp only [afterShort,afterOpen,afterWord,wordOpenClose,List.append_assoc]
  rw [oldshape,newshape]
  exact cut_metrics _ _ _ _ _

theorem before_scan_metrics (s : Nat) :
    toffoliCount (GateMirror.forward (beforeScan s))+1 = toffoliCount (GateMirror.forward (CRTBarrel.beforeReference s)) ∧
    toffoliCount (GateMirror.inverse (beforeScan s)) = toffoliCount (GateMirror.inverse (CRTBarrel.beforeReference s)) ∧
    measurementCount (GateMirror.forward (beforeScan s)) = measurementCount (GateMirror.forward (CRTBarrel.beforeReference s))+1 ∧
    measurementCount (GateMirror.inverse (beforeScan s)) = measurementCount (GateMirror.inverse (CRTBarrel.beforeReference s)) ∧
    gateSlots (GateMirror.forward (beforeScan s)) = gateSlots (GateMirror.forward (CRTBarrel.beforeReference s))+1 ∧
    gateSlots (GateMirror.inverse (beforeScan s)) = gateSlots (GateMirror.inverse (CRTBarrel.beforeReference s)) := by
  have oldshape : CRTBarrel.beforeReference s = Shadow7.fix0P s (Shadow7.sbP s) ++ beforeScanTail s := by
    simp only [CRTBarrel.beforeReference,beforeScanTail,List.append_assoc]
  obtain ⟨nt,nm,ns⟩ := DeadScan.fix0M_counts s (Shadow7.sbP s)
  obtain ⟨ot,_it,om,_im,os,_is⟩ := (Shadow7.counts_fix0P s (Shadow7.sbP s)).programs
  simp only [Nat.add_zero] at ot os
  simp only [beforeScan,oldshape,forward_app,inverse_append,DeadScan.fix0M_inverse,
    toffoliCount_append,measurementCount_append,gateSlots_append,nt,nm,ns,ot,om,os]
  refine ⟨?_,trivial,?_,trivial,?_,trivial⟩ <;> omega

end ECDSAAdd.Entrant.StairPacket.DeadJoin

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem removed_after : ∀ j : Fin 26, j.val≤24 →
    FlagLeave.removed (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 1 (afterShort (start j)) =
      [.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559] := by decide +kernel

theorem all_local_deltas (j : Fin 26) (hi : j.val≤24) :
    toffoliCount (GateMirror.forward (beforeAll (start j))) +
      toffoliCount (GateMirror.forward (afterAll (start j))) + 2 =
      toffoliCount (GateMirror.forward (CRTBarrel.beforeReference (start j))) +
      toffoliCount (GateMirror.forward (afterReference (start j))) ∧
    toffoliCount (inverse (afterAll (start j))) + toffoliCount (inverse (beforeAll (start j))) + 2 =
      toffoliCount (inverse (afterReference (start j))) + toffoliCount (inverse (CRTBarrel.beforeReference (start j))) ∧
    measurementCount (GateMirror.forward (beforeAll (start j))) +
      measurementCount (GateMirror.forward (afterAll (start j))) + 1 =
      measurementCount (GateMirror.forward (CRTBarrel.beforeReference (start j))) +
      measurementCount (GateMirror.forward (afterReference (start j))) ∧
    measurementCount (inverse (afterAll (start j))) + measurementCount (inverse (beforeAll (start j))) + 1 =
      measurementCount (inverse (afterReference (start j))) + measurementCount (inverse (CRTBarrel.beforeReference (start j))) ∧
    gateSlots (GateMirror.forward (beforeAll (start j))) + gateSlots (GateMirror.forward (afterAll (start j))) + 4 =
      gateSlots (GateMirror.forward (CRTBarrel.beforeReference (start j))) + gateSlots (GateMirror.forward (afterReference (start j))) ∧
    gateSlots (inverse (afterAll (start j))) + gateSlots (inverse (beforeAll (start j))) + 4 =
      gateSlots (inverse (afterReference (start j))) + gateSlots (inverse (CRTBarrel.beforeReference (start j))) := by
  have flag := FlagLeave.pair_savings (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559
    (beforeScan (start j)) (afterShort (start j)) (removed_before j hi) (removed_after j hi)
  have scan := before_scan_metrics (start j)
  have join := after_short_metrics j hi
  dsimp only [beforeAll,afterAll]
  omega
end ECDSAAdd.Entrant.StairPacket.DeadJoin

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem scan_replacement_member (s h : Nat) (g : Gate) (hg : g ∈ DeadScan.fix0M s h) :
    ∃ old ∈ Shadow7.fix0P s h, g.wires=old.wires ∧ proper g=proper old := by
  have shape : Shadow7.fix0P s h = (Shadow7.fix0P s h).take 51 ++
      [.ccx (s+30) (h+802) (s+h+47)] ++ (Shadow7.fix0P s h).drop 52 := rfl
  rcases List.mem_append.mp hg with pre | tail
  · rcases List.mem_append.mp pre with head | cell
    · exact ⟨g,List.mem_of_mem_take head,rfl,rfl⟩
    · have eg : g = .pop (s+30) (h+802) (s+h+47) := List.mem_singleton.mp cell
      subst g
      refine ⟨.ccx (s+30) (h+802) (s+h+47),?_,rfl,rfl⟩
      rw [shape]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
  · exact ⟨g,List.mem_of_mem_drop tail,rfl,rfl⟩

theorem before_scan_member (s : Nat) (g : Gate) (hg : g∈beforeScan s) :
    ∃ old∈CRTBarrel.beforeReference s,g.wires=old.wires ∧ proper g=proper old := by
  have shape : CRTBarrel.beforeReference s = Shadow7.fix0P s (Shadow7.sbP s) ++ beforeScanTail s := by
    simp only [CRTBarrel.beforeReference,beforeScanTail,List.append_assoc]
  rw [beforeScan,List.mem_append] at hg
  rcases hg with head | tail
  · obtain ⟨old,ho,hw,hp⟩ := scan_replacement_member s (Shadow7.sbP s) g head
    exact ⟨old,by rw [shape]; exact List.mem_append_left _ ho,hw,hp⟩
  · exact ⟨g,by rw [shape]; exact List.mem_append_right _ tail,rfl,rfl⟩

theorem before_scan_allW {P : Wire → Prop} (s : Nat)
    (h : AllW P (CRTBarrel.beforeReference s)) : AllW P (beforeScan s) := by
  intro g hg q hq
  obtain ⟨old,ho,hw,hp⟩ := before_scan_member s g hg
  exact h old ho q (hw ▸ hq)

theorem before_scan_proper (s : Nat) (h : Proper (CRTBarrel.beforeReference s)) : Proper (beforeScan s) := by
  intro g hg
  obtain ⟨old,ho,hw,hp⟩ := before_scan_member s g hg
  exact hp.trans (h old ho)

theorem after_short_member (j : Fin 26) (hi : j.val≤24) (g : Gate) (hg : g∈afterShort (start j)) :
    g∈afterReference (start j) := by
  have oldshape : afterReference (start j) = afterOpen (start j) ++
      (pair16 (start j) ++ afterWord (start j)) := by
    simp only [afterReference,afterOpen,afterWord,cols_split j hi,word_split,wordGM,toggleG,
      pairGM,lastCol,pair16,Bool.false_eq_true,if_false,List.append_nil,List.nil_append,List.append_assoc]
  have newshape : afterShort (start j) = afterOpen (start j) ++ afterWord (start j) := by
    simp only [afterShort,afterOpen,afterWord,wordOpenClose,List.append_assoc]
  rw [oldshape]
  rw [newshape,List.mem_append] at hg
  rcases hg with head | tail
  · exact List.mem_append_left _ head
  · exact List.mem_append_right _ (List.mem_append_right _ tail)

theorem after_short_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val≤24)
    (h : AllW P (afterReference (start j))) : AllW P (afterShort (start j)) :=
  fun g hg q hq => h g (after_short_member j hi g hg) q hq

theorem after_short_proper (j : Fin 26) (hi : j.val≤24)
    (h : Proper (afterReference (start j))) : Proper (afterShort (start j)) :=
  fun g hg => h g (after_short_member j hi g hg)
end ECDSAAdd.Entrant.StairPacket.DeadJoin


-- ==== begin FlagCut57 (credited to ercumentyildirim ae9d602d) ====
namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-- Prefix of `beforeScan` before Fix5Move's row-0 swap. -/
def beforePre5 (s : Nat) : List Gate :=
  let b := Shadow7.sbP s
  DeadScan.fix0M s b ++ leaveFix1 s b ++ Shadow7.fix2P s b ++ leaveFix3 s b ++
    leaveFix4 s b ++ (Shadow7.fix5P s b).take 27

/-- Stock Fix5Move row-0 controlled swap. -/
def row0Old (s : Nat) : List Gate :=
  [.cx (Shadow7.a0P s - 1 + 0) (Shadow7.e0P s + 6),
   .ccx (tagsP.getD 0 0) (Shadow7.e0P s + 6) (Shadow7.a0P s - 1 + 0),
   .cx (Shadow7.a0P s - 1 + 0) (Shadow7.e0P s + 6)]

/-- Row-0 swap specialized for `e0+6 = 0`: fresh Toffoli copy plus CNOT. -/
def row0New (s : Nat) : List Gate :=
  [.make (tagsP.getD 0 0) (Shadow7.a0P s - 1 + 0) (Shadow7.e0P s + 6),
   .cx (Shadow7.e0P s + 6) (Shadow7.a0P s - 1 + 0)]

/-- Suffix of `beforeScan` after Fix5Move's row-0 swap. -/
def beforePost5 (s : Nat) : List Gate :=
  let b := Shadow7.sbP s
  rowGates (Shadow7.e0P s + 6) ((Shadow7.moveRows s).drop 1) ++ (Shadow7.fix5P s b).drop 43 ++
    Shadow7.leaveAdjust s

theorem moveRows_cut5 (s : Nat) :
    Shadow7.moveRows s = (tagsP.getD 0 0, Shadow7.a0P s - 1 + 0) :: (Shadow7.moveRows s).drop 1 := rfl

theorem beforeScan_split5 (s : Nat) :
    beforeScan s = beforePre5 s ++ (row0Old s ++ beforePost5 s) := by
  have e := moveRows_cut5 s
  simp only [beforeScan, beforeScanTail, beforePre5, row0Old, beforePost5, Shadow7.leaveFix5Move]
  conv_lhs => rw [e]
  simp only [rowGates, List.append_assoc, List.cons_append, List.nil_append]

def beforePre5Cut (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 2 (beforePre5 s)

def before5 (s : Nat) : List Gate :=
  beforePre5Cut s ++ (row0New s ++ beforePost5 s)

theorem removed_pre5 : ∀ j : Fin 26, j.val ≤ 24 →
    FlagLeave.removed (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559 2 (beforePre5 (start j)) =
      [.make (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] := by decide +kernel

theorem removed_post5 : ∀ j : Fin 26, j.val ≤ 24 →
    FlagLeave.removed (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559 1
      (row0Old (start j) ++ beforePost5 (start j)) = [] := by decide +kernel

theorem beforeAll_split5 (j : Fin 26) (hi : j.val ≤ 24) :
    beforeAll (start j) = beforePre5Cut (start j) ++ (row0Old (start j) ++ beforePost5 (start j)) := by
  rw [beforeAll, beforeScan_split5, FlagLeave.cut_append, removed_pre5 j hi]
  simp only [List.length_singleton, show 2 - 1 = 1 by decide]
  rw [FlagLeave.cut_of_removed_nil _ _ _ _ _ (removed_post5 j hi)]
  rfl

/-- `leaveLowStore` after its leading 3 flag gates. -/
def lowRest7 (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s - 1; let bs := (List.range L).map (Shadow7.b0P s + ·)
  [.cx (Shadow7.a0P s - 1) 1557, .x 1557, .make (Shadow7.b0P s - 1) 1557 1558] ++
  (List.range L).map (fun i => .make 1556 (Shadow7.a0P s + i) (Shadow7.b0P s + i)) ++ xsG bs ++
    addG bs ((List.range (L-1)).map (1559 + ·)) 1558 ++ xsG bs ++
    [.pop (Shadow7.b0P s - 1) 1557 1558, .cx (Shadow7.a0P s - 1) 1557, .x 1557]

/-- `leaveStoreMapped` up to its carry chain. -/
def storeHead7 (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s; let top := Shadow7.a0P s + L - 2; let H := Shadow7.liveW s - L
  [.x 1558, .x top] ++ xsG ((List.range H).map (fun i => Shadow7.bankW s (L+i)))

def topW7 (s : Nat) : Wire := Shadow7.a0P s + Shadow7.lowsP s - 2

/-- Prefix of `afterShort` up through the flag erasure at the start of `leaveLowStore`. -/
def afterPre7Head (s : Nat) : List Gate :=
  let b := Shadow7.sbP s
  Shadow7.fix8P s b ++ Shadow7.glueG3 s ++ (keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++ wordGM 1614 (cols16 s)) ++
  Shadow7.fix10P s b ++ leaveFix11 s b ++ leaveFix12 s b ++
  [.cx (Shadow7.e0P s + 3) 1560, .cx 1559 1560, .pop (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559]

def afterPre7Tail (s : Nat) : List Gate := lowRest7 s ++ storeHead7 s

/-- The store chain below level 0. -/
def chainMid7 (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s; let top := Shadow7.a0P s + L - 2; let H := Shadow7.liveW s - L
  chainG (Shadow7.storeW s) (fun i => if i = 0 then top else Shadow7.bankW s (L+i-1))
    [.cx (Shadow7.storeW s (H+1)) 1557, .x 1557] 1 H

/-- Suffix of `afterShort` after the store chain's level-0 pop. -/
def afterPost7 (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s; let top := Shadow7.a0P s + L - 2; let H := Shadow7.liveW s - L
  let hi := (List.range H).map (fun i => Shadow7.bankW s (L+i))
  let seq2 := (List.range L).map (Shadow7.b0P s - 1 + ·)
  xsG hi.reverse ++ [.x top, .x 1558, .make 1556 1557 1558, .x 1558] ++ xsG seq2 ++
    chainG (1558 + ·) (Shadow7.b0P s - 1 + ·) [.cx (1558+L) 1556, .x 1556] 0 L ++
    xsG seq2.reverse ++ [.x 1558] ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

theorem store0_7 (s : Nat) : Shadow7.storeW s 0 = 1558 := by
  simp only [Shadow7.storeW, Partial.storeW]
  split_ifs <;> ((try unfold Shadow7.e0P at *); (try unfold Wire at *); omega)

theorem store1_7 (s : Nat) : Shadow7.storeW s 1 = 1559 := by
  simp only [Shadow7.storeW, Partial.storeW]
  split_ifs <;> ((try unfold Shadow7.e0P at *); (try unfold Wire at *); omega)

theorem afterShort_split7 (s : Nat) :
    afterShort s = afterPre7Head s ++ (afterPre7Tail s ++
      ([.make 1558 (topW7 s) 1559] ++ (chainMid7 s ++ ([.pop 1558 (topW7 s) 1559] ++ afterPost7 s)))) := by
  simp only [afterShort, afterPre7Head, afterPre7Tail, lowRest7, storeHead7, topW7, chainMid7, afterPost7,
    Shadow7.leaveLowStore, Shadow7.leaveStoreMapped, Partial.chainG, Nat.zero_add, store0_7, store1_7,
    if_pos rfl, ite_true, if_true, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]

def afterPre7HeadCut (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 1 (afterPre7Head s)

def after7 (s : Nat) : List Gate :=
  afterPre7HeadCut s ++ (afterPre7Tail s ++
    ([.cx (topW7 s) 1559] ++ (chainMid7 s ++ ([.cx (topW7 s) 1559] ++ afterPost7 s))))

theorem removed_afterPre7Head : ∀ j : Fin 26, j.val ≤ 24 →
    FlagLeave.removed (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559 1 (afterPre7Head (start j)) =
      [.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] := by decide +kernel

theorem afterAll_split7 (j : Fin 26) (hi : j.val ≤ 24) :
    afterAll (start j) = afterPre7HeadCut (start j) ++ (afterPre7Tail (start j) ++
      ([.make 1558 (topW7 (start j)) 1559] ++ (chainMid7 (start j) ++ ([.pop 1558 (topW7 (start j)) 1559] ++ afterPost7 (start j))))) := by
  rw [afterAll, afterShort_split7, FlagLeave.cut_append, removed_afterPre7Head j hi]
  simp only [List.length_singleton, Nat.sub_self, FlagLeave.cut]
  rfl

theorem before5_deltas (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (before5 (start j))) = toffoliCount (GateMirror.forward (beforeAll (start j))) ∧
    toffoliCount (inverse (before5 (start j))) + 1 = toffoliCount (inverse (beforeAll (start j))) ∧
    measurementCount (GateMirror.forward (before5 (start j))) = measurementCount (GateMirror.forward (beforeAll (start j))) ∧
    measurementCount (inverse (before5 (start j))) = measurementCount (inverse (beforeAll (start j))) + 1 ∧
    gateSlots (GateMirror.forward (before5 (start j))) + 1 = gateSlots (GateMirror.forward (beforeAll (start j))) ∧
    gateSlots (inverse (before5 (start j))) = gateSlots (inverse (beforeAll (start j))) := by
  rw [beforeAll_split5 j hi, before5]
  simp only [row0Old, row0New, toffoli_forward, toffoli_inverse, meas_forward, meas_inverse, slots_forward, slots_inverse,
    List.countP_append, List.length_append, List.countP_cons, List.countP_nil, List.length_cons,
    List.length_nil, isCCX, isMake, isPop, if_false, if_true, Bool.false_eq_true]
  refine ⟨?_, ?_, trivial, ?_, ?_, ?_⟩ <;> omega

theorem after7_deltas (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (after7 (start j))) + 1 = toffoliCount (GateMirror.forward (afterAll (start j))) ∧
    toffoliCount (inverse (after7 (start j))) + 1 = toffoliCount (inverse (afterAll (start j))) ∧
    measurementCount (GateMirror.forward (after7 (start j))) + 1 = measurementCount (GateMirror.forward (afterAll (start j))) ∧
    measurementCount (inverse (after7 (start j))) + 1 = measurementCount (inverse (afterAll (start j))) ∧
    gateSlots (GateMirror.forward (after7 (start j))) + 1 = gateSlots (GateMirror.forward (afterAll (start j))) ∧
    gateSlots (inverse (after7 (start j))) + 1 = gateSlots (inverse (afterAll (start j))) := by
  rw [afterAll_split7 j hi, after7]
  have c1 : ∀ a b t : Wire, toffoliCount (GateMirror.forward [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have c2 : ∀ a b t : Wire, toffoliCount (inverse [Gate.make a b t]) = 0 := fun _ _ _ => rfl
  have c3 : ∀ a b t : Wire, toffoliCount (GateMirror.forward [Gate.pop a b t]) = 0 := fun _ _ _ => rfl
  have c4 : ∀ a b t : Wire, toffoliCount (inverse [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have c5 : ∀ b t : Wire, toffoliCount (GateMirror.forward [Gate.cx b t]) = 0 := fun _ _ => rfl
  have c6 : ∀ b t : Wire, toffoliCount (inverse [Gate.cx b t]) = 0 := fun _ _ => rfl
  have d1 : ∀ a b t : Wire, measurementCount (GateMirror.forward [Gate.make a b t]) = 0 := fun _ _ _ => rfl
  have d2 : ∀ a b t : Wire, measurementCount (inverse [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have d3 : ∀ a b t : Wire, measurementCount (GateMirror.forward [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have d4 : ∀ a b t : Wire, measurementCount (inverse [Gate.pop a b t]) = 0 := fun _ _ _ => rfl
  have d5 : ∀ b t : Wire, measurementCount (GateMirror.forward [Gate.cx b t]) = 0 := fun _ _ => rfl
  have d6 : ∀ b t : Wire, measurementCount (inverse [Gate.cx b t]) = 0 := fun _ _ => rfl
  have e1 : ∀ a b t : Wire, gateSlots (GateMirror.forward [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have e2 : ∀ a b t : Wire, gateSlots (inverse [Gate.make a b t]) = 2 := fun _ _ _ => rfl
  have e3 : ∀ a b t : Wire, gateSlots (GateMirror.forward [Gate.pop a b t]) = 2 := fun _ _ _ => rfl
  have e4 : ∀ a b t : Wire, gateSlots (inverse [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have e5 : ∀ b t : Wire, gateSlots (GateMirror.forward [Gate.cx b t]) = 1 := fun _ _ => rfl
  have e6 : ∀ b t : Wire, gateSlots (inverse [Gate.cx b t]) = 1 := fun _ _ => rfl
  simp only [forward_app, inverse_append, toffoliCount_append, measurementCount_append, gateSlots_append,
    c1, c2, c3, c4, c5, c6, d1, d2, d3, d4, d5, d6, e1, e2, e3, e4, e5, e6]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem all_local_deltas57 (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (before5 (start j))) +
      toffoliCount (GateMirror.forward (after7 (start j))) + 3 =
      toffoliCount (GateMirror.forward (CRTBarrel.beforeReference (start j))) +
      toffoliCount (GateMirror.forward (afterReference (start j))) ∧
    toffoliCount (inverse (after7 (start j))) + toffoliCount (inverse (before5 (start j))) + 4 =
      toffoliCount (inverse (afterReference (start j))) + toffoliCount (inverse (CRTBarrel.beforeReference (start j))) ∧
    measurementCount (GateMirror.forward (before5 (start j))) +
      measurementCount (GateMirror.forward (after7 (start j))) + 2 =
      measurementCount (GateMirror.forward (CRTBarrel.beforeReference (start j))) +
      measurementCount (GateMirror.forward (afterReference (start j))) ∧
    measurementCount (inverse (after7 (start j))) + measurementCount (inverse (before5 (start j))) + 1 =
      measurementCount (inverse (afterReference (start j))) + measurementCount (inverse (CRTBarrel.beforeReference (start j))) ∧
    gateSlots (GateMirror.forward (before5 (start j))) + gateSlots (GateMirror.forward (after7 (start j))) + 6 =
      gateSlots (GateMirror.forward (CRTBarrel.beforeReference (start j))) + gateSlots (GateMirror.forward (afterReference (start j))) ∧
    gateSlots (inverse (after7 (start j))) + gateSlots (inverse (before5 (start j))) + 5 =
      gateSlots (inverse (afterReference (start j))) + gateSlots (inverse (CRTBarrel.beforeReference (start j))) := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := all_local_deltas j hi
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := before5_deltas j hi
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := after7_deltas j hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem row0New_proper : ∀ j : Fin 26, j.val ≤ 24 →
    (row0New (start j)).all proper = true := by decide +kernel

theorem top_cx_proper : ∀ j : Fin 26, j.val ≤ 24 →
    proper (.cx (topW7 (start j)) 1559) = true := by decide +kernel

theorem before5_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val ≤ 24)
    (h : AllW P (beforeAll (start j))) : AllW P (before5 (start j)) := by
  rw [beforeAll_split5 j hi] at h
  intro x hx q hq
  rw [before5] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ hx) q hq
  · rcases List.mem_append.mp hx with hx | hx
    · refine h (.ccx (tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) - 1 + 0))
        (List.mem_append_right _ (List.mem_append_left _ (by simp [row0Old]))) q ?_
      simp only [row0New, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;>
        simp only [GateMirror.Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢ <;> tauto
    · exact h x (List.mem_append_right _ (List.mem_append_right _ hx)) q hq

theorem before5_proper (j : Fin 26) (hi : j.val ≤ 24)
    (h : Proper (beforeAll (start j))) : Proper (before5 (start j)) := by
  rw [beforeAll_split5 j hi] at h
  intro x hx
  rw [before5] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ hx)
  · rcases List.mem_append.mp hx with hx | hx
    · exact List.all_eq_true.mp (row0New_proper j hi) x hx
    · exact h x (List.mem_append_right _ (List.mem_append_right _ hx))

theorem after7_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val ≤ 24)
    (h : AllW P (afterAll (start j))) : AllW P (after7 (start j)) := by
  rw [afterAll_split7 j hi] at h
  intro x hx q hq
  rw [after7] at hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx | rfl | hx | rfl | hx
  · exact h x (by simp [hx]) q hq
  · exact h x (by simp [hx]) q hq
  · refine h (.make 1558 (topW7 (start j)) 1559) (by simp) q ?_
    simp only [GateMirror.Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto
  · exact h x (by simp [hx]) q hq
  · refine h (.pop 1558 (topW7 (start j)) 1559) (by simp) q ?_
    simp only [GateMirror.Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto
  · exact h x (by simp [hx]) q hq

theorem after7_proper (j : Fin 26) (hi : j.val ≤ 24)
    (h : Proper (afterAll (start j))) : Proper (after7 (start j)) := by
  rw [afterAll_split7 j hi] at h
  intro x hx
  rw [after7] at hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx | rfl | hx | rfl | hx
  · exact h x (by simp [hx])
  · exact h x (by simp [hx])
  · exact top_cx_proper j hi
  · exact h x (by simp [hx])
  · exact top_cx_proper j hi
  · exact h x (by simp [hx])

end ECDSAAdd.Entrant.StairPacket.DeadJoin
-- ==== end FlagCut57 ====

-- ==== begin KeptParity (credited to GordoAR a2ce2c3a; margin-16 port: bank rows a0P-1+i) ====
namespace ECDSAAdd.Entrant.StairPacket.KeptParity
open Arithmetic Partial GateMirror Challenge
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000

/-- The 8-row kept pass on local wires: 0 = the digit `1613`, 1..8 = tags 0..7, 9..16 = the cells of rows 0..7. -/
def old : List Gate := [.ccx 1 0 9, .ccx 2 0 10, .ccx 3 0 11, .ccx 4 0 12, .ccx 5 0 13, .ccx 6 0 14, .ccx 7 0 15, .ccx 8 0 16]

/-- Row 0 by parity: the tags are one-hot, so `tag0 & d = d ^ (tag1 & d) ^ .. ^ (tag7 & d)` whenever the digit can be set
only with a hot tag below 8 (`relation`). Row 0's Toffoli becomes one CX; the parity is carried on cell 0. -/
def replacement : List Gate := [.cx 0 9,
  .cx 10 9, .ccx 2 0 10, .cx 10 9,
  .cx 11 9, .ccx 3 0 11, .cx 11 9,
  .cx 12 9, .ccx 4 0 12, .cx 12 9,
  .cx 13 9, .ccx 5 0 13, .cx 13 9,
  .cx 14 9, .ccx 6 0 14, .cx 14 9,
  .cx 15 9, .ccx 7 0 15, .cx 15 9,
  .cx 16 9, .ccx 8 0 16, .cx 16 9]

def port (s : Nat) : Wire → Wire
  | 0 => 1613
  | i+1 => if i < 8 then tagsP.getD i 0 else Shadow7.a0P s - 1 + (i-7)

def placed (s : Nat) : List Gate := [.cx (port s 0) (port s 9),
  .cx (port s 10) (port s 9), .ccx (port s 2) (port s 0) (port s 10), .cx (port s 10) (port s 9),
  .cx (port s 11) (port s 9), .ccx (port s 3) (port s 0) (port s 11), .cx (port s 11) (port s 9),
  .cx (port s 12) (port s 9), .ccx (port s 4) (port s 0) (port s 12), .cx (port s 12) (port s 9),
  .cx (port s 13) (port s 9), .ccx (port s 5) (port s 0) (port s 13), .cx (port s 13) (port s 9),
  .cx (port s 14) (port s 9), .ccx (port s 6) (port s 0) (port s 14), .cx (port s 14) (port s 9),
  .cx (port s 15) (port s 9), .ccx (port s 7) (port s 0) (port s 15), .cx (port s 15) (port s 9),
  .cx (port s 16) (port s 9), .ccx (port s 8) (port s 0) (port s 16), .cx (port s 16) (port s 9)]

theorem physical : ∀ j : Fin 26, j.val ≤ 24 → (placed (start j)).all proper = true := by decide +kernel

theorem wiresCovered : ∀ j : Fin 26, j.val ≤ 24 → (placed (start j)).all (fun g =>
    g.wires.all (fun q => ((Shadow7.moveKept (start j)).flatMap Gate.wires).contains q)) = true := by decide +kernel

theorem counts : toffoliCount (GateMirror.forward replacement) + 1 = toffoliCount (GateMirror.forward old) ∧
    toffoliCount (inverse replacement) + 1 = toffoliCount (inverse old) ∧
    measurementCount (GateMirror.forward replacement) = measurementCount (GateMirror.forward old) ∧
    measurementCount (inverse replacement) = measurementCount (inverse old) ∧
    gateSlots (GateMirror.forward replacement) = gateSlots (GateMirror.forward old) + 14 ∧
    gateSlots (inverse replacement) = gateSlots (inverse old) + 14 := by decide

/-- The placed pass has one Toffoli fewer each way, no measurement, and 14 more slots each way: both passes are the
local passes renamed by `port s` (GordoAR's proof). -/
theorem cellCounts (s : Nat) :
    toffoliCount (GateMirror.forward (placed s)) + 1 = toffoliCount (GateMirror.forward (Shadow7.moveKept s)) ∧
    toffoliCount (inverse (placed s)) + 1 = toffoliCount (inverse (Shadow7.moveKept s)) ∧
    measurementCount (GateMirror.forward (placed s)) = measurementCount (GateMirror.forward (Shadow7.moveKept s)) ∧
    measurementCount (inverse (placed s)) = measurementCount (inverse (Shadow7.moveKept s)) ∧
    gateSlots (GateMirror.forward (placed s)) = gateSlots (GateMirror.forward (Shadow7.moveKept s)) + 14 ∧
    gateSlots (inverse (placed s)) = gateSlots (inverse (Shadow7.moveKept s)) + 14 := by
  have nf : GateMirror.forward (placed s) = renameProgram (port s) (GateMirror.forward replacement) := rfl
  have nr : inverse (placed s) = renameProgram (port s) (inverse replacement) := rfl
  have ofw : GateMirror.forward (Shadow7.moveKept s) = renameProgram (port s) (GateMirror.forward old) := rfl
  have obw : inverse (Shadow7.moveKept s) = renameProgram (port s) (inverse old) := rfl
  rw [nf, nr, ofw, obw]
  simp only [renameProgram_counts, Baselines.rename_gateSlots]
  exact counts

end ECDSAAdd.Entrant.StairPacket.KeptParity

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

/-- `afterPre7Head` after its kept pass. -/
def afterPre7Rest (s : Nat) : List Gate :=
  let b := Shadow7.sbP s
  wordGM 1614 (cols16 s) ++ Shadow7.fix10P s b ++ leaveFix11 s b ++ leaveFix12 s b ++
  [.cx (Shadow7.e0P s + 3) 1560, .cx 1559 1560, .pop (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559]

/-- `afterPre7Head` in front of its kept pass. -/
def keptHead (s : Nat) : List Gate := Shadow7.fix8P s (Shadow7.sbP s) ++ Shadow7.glueG3 s

theorem afterPre7Head_kept (s : Nat) :
    afterPre7Head s = (keptHead s ++ Shadow7.moveKept s) ++ afterPre7Rest s := by
  simp only [afterPre7Head, keptHead, afterPre7Rest, Shadow7.moveKept, List.append_assoc]

theorem removed_keptHead : ∀ j : Fin 26, j.val ≤ 24 →
    FlagLeave.removed (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559 1
      (keptHead (start j) ++ Shadow7.moveKept (start j)) = [] := by decide +kernel

/-- `after7` behind its kept pass. -/
def afterRest7 (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 1 (afterPre7Rest s) ++ (afterPre7Tail s ++
    ([.cx (topW7 s) 1559] ++ (chainMid7 s ++ ([.cx (topW7 s) 1559] ++ afterPost7 s))))

/-- KeptParity: `after7` with the kept pass replaced by the parity pass. -/
def after7K (s : Nat) : List Gate := keptHead s ++ (KeptParity.placed s ++ afterRest7 s)

theorem after7_kept (j : Fin 26) (hi : j.val ≤ 24) :
    after7 (start j) = keptHead (start j) ++ (Shadow7.moveKept (start j) ++ afterRest7 (start j)) := by
  rw [after7, afterPre7HeadCut, afterPre7Head_kept, FlagLeave.cut_append, removed_keptHead j hi,
    FlagLeave.cut_of_removed_nil _ _ _ _ _ (removed_keptHead j hi)]
  simp only [List.length_nil, Nat.sub_zero, afterRest7, List.append_assoc]

theorem after7K_counts (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (after7K (start j))) + 1 = toffoliCount (GateMirror.forward (after7 (start j))) ∧
    toffoliCount (inverse (after7K (start j))) + 1 = toffoliCount (inverse (after7 (start j))) ∧
    measurementCount (GateMirror.forward (after7K (start j))) = measurementCount (GateMirror.forward (after7 (start j))) ∧
    measurementCount (inverse (after7K (start j))) = measurementCount (inverse (after7 (start j))) ∧
    gateSlots (GateMirror.forward (after7K (start j))) = gateSlots (GateMirror.forward (after7 (start j))) + 14 ∧
    gateSlots (inverse (after7K (start j))) = gateSlots (inverse (after7 (start j))) + 14 := by
  obtain ⟨a, b, c, d, e, f⟩ := KeptParity.cellCounts (start j)
  rw [after7_kept j hi, after7K]
  simp only [forward_app, inverse_append, toffoliCount_append, measurementCount_append, gateSlots_append]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem after7K_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val ≤ 24)
    (h : AllW P (afterAll (start j))) : AllW P (after7K (start j)) := by
  have old := after7_allW j hi h
  rw [after7_kept j hi, allW_append_iff, allW_append_iff] at old
  rw [after7K, allW_append_iff, allW_append_iff]
  refine ⟨old.1, ?_, old.2.2⟩
  intro g hg q hq
  have inc := List.all_eq_true.mp (List.all_eq_true.mp (KeptParity.wiresCovered j hi) g hg) q hq
  obtain ⟨k, hk, hw⟩ := List.mem_flatMap.mp (List.contains_iff_mem.mp inc)
  exact old.2.1 k hk q hw

theorem after7K_proper (j : Fin 26) (hi : j.val ≤ 24)
    (h : Proper (afterAll (start j))) : Proper (after7K (start j)) := by
  have keep : (after7 (start j)).all proper = true := List.all_eq_true.mpr (after7_proper j hi h)
  rw [after7_kept j hi] at keep
  simp only [List.all_append, Bool.and_eq_true] at keep
  have all : (after7K (start j)).all proper = true := by
    rw [after7K]
    simp only [List.all_append, Bool.and_eq_true]
    exact ⟨keep.1, KeptParity.physical j hi, keep.2.2⟩
  intro g hg
  exact List.all_eq_true.mp all g hg

end ECDSAAdd.Entrant.StairPacket.DeadJoin
-- ==== end KeptParity defs ====

-- ==== begin ScanRowGordo defs (margin 16, credited to GordoAR e2530dcd) ====
section
namespace ECDSAAdd.Entrant.StairPacket.ScanRowGordo
open Arithmetic GateMirror Partial Challenge MeasuredCodec5
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def firstRows (s h : Nat) : List Gate := (Shadow7.fix0P s h).take 47

def cell (s h : Nat) : List Gate :=
  [.cx (s+h+46) (h+801), .ccx (s+30) (h+801) (s+h+46), .cx (s+h+46) (h+801)]

def shortCell (s h : Nat) : List Gate :=
  let a := s+h+46
  let b := h+801
  let z := h+1579
  [.cx a b, .cx b a, .cx z a, .pop (s+30) b a, .cx z a, .cx b a, .cx a b]

def suffix (s h : Nat) : List Gate := ((Shadow7.fix0P s h).drop 50).take 18

def lastTwo (h : Nat) : List Gate := [.cx (h+1579) (h+801), .cx (h+1579) (h+802)]

def port (s h : Nat) : Wire → Wire
  | 0 => s+30
  | 1 => s+h+46
  | 2 => h+801
  | _ => h+1579

def before5Tail (s : Nat) : List Gate :=
  let h := Shadow7.sbP s
  let preTail := (DeadScan.fix0M s h).drop 50 ++ leaveFix1 s h ++ Shadow7.fix2P s h ++
    leaveFix3 s h ++ leaveFix4 s h ++ (Shadow7.fix5P s h).take 27
  FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 2 preTail ++
    (DeadJoin.row0New s ++ DeadJoin.beforePost5 s)

def before5Row (s : Nat) : List Gate :=
  let h := Shadow7.sbP s
  firstRows s h ++ (shortCell s h ++ before5Tail s)

end ECDSAAdd.Entrant.StairPacket.ScanRowGordo
end
-- ==== end ScanRowGordo defs ====

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

def before (s : Nat) : List GateMirror.Gate := ScanRowGordo.before5Row s
def afterPart (s : Nat) : List GateMirror.Gate := DeadJoin.after7K s
-- ==== end DeadJoin ====

def leave (j : Fin 26) : Program :=
  let s := start j
  if j.val ≤ 24 then
    GateMirror.forward (before s) ++ barrel s false ++ GateMirror.forward (afterPart s)
  else Shadow7.leaveMoveP j

def unleave (j : Fin 26) : Program :=
  let s := start j
  if j.val ≤ 24 then
    GateMirror.inverse (afterPart s) ++ barrel s true ++ GateMirror.inverse (before s)
  else Shadow7.leaveMoveInvP j

def params : WindowFold.Pieces Program := { Shadow7.params with leave := leave, leaveInv := unleave, unrouted := TickCut.Tail.selected }

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrel ====

-- ==== begin CRTBitCount ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

/-- Count eight set bits with three additions on independent groups of bits. -/
def byteCount (n : Nat) : Nat :=
  let pairs := (n &&& 85) + ((n >>> 1) &&& 85)
  let fours := (pairs &&& 51) + ((pairs >>> 2) &&& 51)
  (fours &&& 15) + (fours >>> 4)

private theorem byte_checked : ∀ i : Fin 256, (selected 8 i.val).length = byteCount i.val := by decide +kernel

private theorem byte_count (m : Nat) : (selected 8 m).length = byteCount (m%256) := by
  have h : selected 8 m = selected 8 (m % 2^8) := by
    apply List.filter_congr
    intro i hi
    have sm := List.mem_range.mp hi
    simpa only [sm,decide_true,Bool.true_and] using (Nat.testBit_mod_two_pow m 8 i).symm
  rw [h]
  exact byte_checked ⟨_,Nat.mod_lt _ (by decide)⟩

private theorem select_split (a b m : Nat) : (selected (a+b) m).length =
    (selected a m).length + (selected b (m >>> a)).length := by
  simp only [selected,List.range_add,List.filter_append,List.length_append,List.filter_map,
    List.length_map,Function.comp_def,Nat.testBit_shiftRight]

def chunkCount (remainder : Nat) : Nat → Nat → Nat
  | 0, m => (selected remainder m).length
  | c+1, m => byteCount (m%256) + chunkCount remainder c (m >>> 8)

private theorem chunks_length (r c m : Nat) : (selected (8*c+r) m).length = chunkCount r c m := by
  induction c generalizing m with
  | zero => simp [chunkCount]
  | succ c ih =>
    rw [show 8*(c+1)+r = 8+(8*c+r) by omega,select_split,byte_count,ih]
    rfl

def fastCount (n m : Nat) := chunkCount (n%8) (n/8) m

theorem selected_length (n m : Nat) : (selected n m).length = fastCount n m := by
  have e := chunks_length (n%8) (n/8) m
  simpa only [Nat.div_add_mod] using e

def basisSize (n : Nat) : Nat :=
  ((pivots n).map (fun (donor,mask) => (if donor<n then 1 else 0) + fastCount n mask)).sum

theorem basis_size (n : Nat) : (basisNetwork n).length = basisSize n := by
  unfold basisNetwork basisSize
  rw [List.length_reverse, List.length_flatMap]
  have each (row : Nat × Nat) (i : Nat) : (elimStep n i row).length =
      (if row.1 < n then 1 else 0) + fastCount n row.2 := by
    simp only [elimStep,List.length_append,List.length_map,selected_length]
    split <;> rfl
  simp only [each]
  have eq (xs : List (Nat × Nat)) (i : Nat) :
      (xs.zipIdx i).map (fun (row,_) => (if row.1<n then 1 else 0) + fastCount n row.2) =
      xs.map (fun row => (if row.1<n then 1 else 0) + fastCount n row.2) := by
    induction xs generalizing i with
    | nil => rfl
    | cons x xs ih => simp only [List.zipIdx_cons,List.map_cons]; rw [ih]
  exact congrArg List.sum (eq _ 0)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBitCount ====

-- ==== begin CRTDomain ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

def UsedField (p : Nat) : Prop :=
  p = 11 ∨ p = 13 ∨ p = 19 ∨ p = 21 ∨ p = 25 ∨ p = 31 ∨ p = 37 ∨ p = 41 ∨ p = 47 ∨ p = 55 ∨ p = 59 ∨ p = 61 ∨ p = 67 ∨ p = 73 ∨ p = 87 ∨ p = 91 ∨ p = 97 ∨ p = 103 ∨ p = 109 ∨ p = 115 ∨ p = 117 ∨ p = 257 ∨ p = 313 ∨ p = 471

instance (p : Nat) : Decidable (UsedField p) := by
  unfold UsedField
  infer_instance

def UsedWidth (n : Nat) : Prop :=
  n = 31 ∨ n = 39 ∨ n = 46 ∨ n = 54 ∨ n = 61 ∨ n = 69 ∨ n = 76 ∨ n = 84 ∨ n = 91 ∨ n = 99 ∨ n = 106 ∨ n = 113 ∨ n = 120 ∨ n = 128

instance (n : Nat) : Decidable (UsedWidth n) := by
  unfold UsedWidth
  infer_instance

theorem usedWidth : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 → UsedWidth (barrelWidth (start j)) := by
  decide +kernel

theorem schedule_fields (n : Nat) (hn : UsedWidth n) :
    ∀ pair ∈ schedule n, UsedField pair.1 := by
  have h : (schedule n).all (fun x => decide (UsedField x.1)) = true := by
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  intro pair hp
  exact of_decide_eq_true (List.all_eq_true.mp h pair hp)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTDomain ====

-- ==== begin CRTResources ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Challenge ECDSAAdd.Baselines

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Resources

structure Count where
  t : Nat
  m : Nat
  slots : Nat
  deriving DecidableEq

def count (p : Program) : Count := ⟨toffoliCount p, measurementCount p, gateSlots p⟩
def zero : Count := ⟨0,0,0⟩
def add (a b : Count) : Count := ⟨a.t+b.t,a.m+b.m,a.slots+b.slots⟩
def scale (k : Nat) (a : Count) : Count := ⟨k*a.t,k*a.m,k*a.slots⟩

theorem append (p q : Program) : count (p++q) = add (count p) (count q) := by
  simp [count, add]

theorem reverse (p : Program) : count p.reverse = count p := by
  simp [count, toffoliCount_reverse, measurementCount_reverse]

theorem renamed (f : Wire → Wire) (p : Program) : count (renameProgram f p) = count p := by
  simp only [count, (renameProgram_counts f p).1, (renameProgram_counts f p).2, rename_gateSlots]

theorem flatConstant {α} (xs : List α) (f : α → Program) (r : Count)
    (h : ∀ x ∈ xs, count (f x) = r) : count (xs.flatMap f) = scale xs.length r := by
  induction xs with
  | nil => cases r; simp [count, scale, toffoliCount, measurementCount]
  | cons x xs ih =>
    rw [List.flatMap_cons, append, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    cases r
    simp [scale, add, Nat.succ_mul, Nat.add_comm]

theorem cxMap {α} (xs : List α) (a b : α → Wire) :
    count (xs.map (fun x => Instr.CX (a x) (b x))) = ⟨0,0,xs.length⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change count ([_] ++ _) = _
    rw [append, ih]
    simp [count, add, toffoliCount, measurementCount, gateSlots, instructionSlots, Nat.add_comm]

theorem ccxMap {α} (xs : List α) (a b c : α → Wire) :
    count (xs.map (fun x => Instr.CCX (a x) (b x) (c x))) = ⟨xs.length,0,xs.length⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change count ([_] ++ _) = _
    rw [append, ih]
    simp [count, add, toffoliCount, measurementCount, gateSlots, instructionSlots, Nat.add_comm]

def stagePrice (d m h : Nat) : Count :=
  let inc := 2^h
  let edits := (m-inc)*d
  let tags := ((List.range 16).filter fun k => k.testBit h).length
  if m ≤ inc then zero else ⟨edits,0,tags+edits+tags⟩

theorem stage_count (n off d m h : Nat) :
    count (stage n off d m h) = stagePrice d m h := by
  unfold stage stagePrice
  dsimp only
  by_cases short : m ≤ 2^h
  · simp only [if_pos short]; rfl
  · simp only [if_neg short]
    rw [append, append, reverse]
    rw [cxMap]
    rw [flatConstant _ _ ⟨d,0,d⟩]
    · simp [add, scale]
    · intro j _
      simpa only [List.length_range] using
        (ccxMap (List.range d) (fun _ => n+24) (fun i => off+d*j+i)
          (fun i => off+d*(j+2^h)+i))

def sumBy {α} (f : α → Count) (xs : List α) : Count :=
  xs.foldr (fun x r => add (f x) r) zero

theorem flatSum {α} (xs : List α) (f : α → Program) (g : α → Count)
    (h : ∀ x ∈ xs, count (f x) = g x) : count (xs.flatMap f) = sumBy g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, append, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rfl

def r8StepPrice (st : R8Step) : Count :=
  ⟨1, 0, st.tags.length + st.pre.length + 1 + st.pre.length + st.tags.length⟩

theorem r8Step_count (n off : Nat) (st : R8Step) : count (r8Step n off st) = r8StepPrice st := by
  unfold r8Step r8StepPrice
  dsimp only
  rw [append, append, append, append, reverse, reverse, cxMap, cxMap]
  have h1 : count [Instr.CCX (n+24) (off+st.src) (off+st.dst)] = ⟨1, 0, 1⟩ := by
    simp [count, toffoliCount, measurementCount, gateSlots, instructionSlots]
  rw [h1]
  simp [add]

def r8Price (mir : Bool) : Count := sumBy r8StepPrice (pascalR8Steps mir)

private theorem r8Price_eq : ∀ mir : Bool, r8Price mir = ⟨8, 0, 212⟩ := by decide +kernel

theorem pascalR8_count (n off : Nat) (mir : Bool) : count (pascalR8 n off mir) = r8Price mir :=
  flatSum _ _ _ (fun st _ => r8Step_count n off st)

def stdTriPrice (d m : Nat) := sumBy (stagePrice d m) (List.range 4)

def triPrice (d m : Nat) := if d == 8 && m == 2 then ⟨8, 0, 212⟩ else stdTriPrice d m

theorem triangular_count (n off d m : Nat) : count (triangular n off d m) = stdTriPrice d m :=
  flatSum _ _ _ (fun i _ => stage_count n off d m i)

theorem primary_count (n off p m : Nat) (mir : Bool) : count (primary n off p m mir) =
    add (scale m (count (fieldCore p mir))) (triPrice (fieldDegree p) m) := by
  unfold primary triPrice; dsimp only
  rw [append, flatConstant _ _ (count (fieldCore p mir)) (fun _ _ => renamed _ _), List.length_range]
  by_cases h82 : (fieldDegree p == 8 && m == 2) = true
  · rw [if_pos h82, if_pos h82, pascalR8_count, r8Price_eq]
  · rw [if_neg h82, if_neg h82]; cases mir <;> simp [reverse, triangular_count]

def fieldPrice (p : Nat) (mir : Bool) : Count :=
  let x := measuredField p
  ⟨x.1, x.2.1, if mir then x.2.2.2 else x.2.2.1⟩

def partsPrice (mir : Bool) (parts : List (Nat × Nat)) : Count :=
  sumBy (fun (p,m) => add (scale m (fieldPrice p mir)) (triPrice (fieldDegree p) m)) parts

theorem components_count (n : Nat) (mir : Bool) (off : Nat) (parts : List (Nat × Nat))
    (h : ∀ pair ∈ parts, count (fieldCore pair.1 mir) = fieldPrice pair.1 mir) :
    count (components n mir off parts) = partsPrice mir parts := by
  induction parts generalizing off with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨p,m⟩ := pair
    rw [components, append, primary_count, h (p,m) (by simp),
      ih _ (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    rfl

def windowPrice (n : Nat) (mir : Bool) : Count :=
  let basis : Count := ⟨0,0,(basisNetwork n).length⟩
  add (add basis (partsPrice mir (schedule n))) basis

theorem logical_count (n : Nat) (mir : Bool)
    (h : ∀ pair ∈ schedule n, count (fieldCore pair.1 mir) = fieldPrice pair.1 mir) :
    count (logical n mir) = windowPrice n mir := by
  unfold logical windowPrice
  rw [append, append, reverse, components_count _ _ _ _ h]
  have b := cxMap (basisNetwork n) Prod.fst Prod.snd
  exact congrArg (fun v => add (add v (partsPrice mir (schedule n))) v) b

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Resources

end
-- ==== end CRTResources ====

-- ==== begin CRTBarrelMetrics ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Resources
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem field_count (p : Nat) (hp : UsedField p) (mir : Bool) :
    count (fieldCore p mir) = fieldPrice p mir := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases mir <;> decide +kernel

def listedPrice (n : Nat) (mir : Bool) : Count :=
  let z := measuredCosts n
  ⟨z.1, z.2.1, if mir then z.2.2.2 else z.2.2.1⟩

private theorem window_price (n : Nat) (hn : UsedWidth n) (mir : Bool) :
    windowPrice n mir = listedPrice n mir := by
  unfold windowPrice
  rw [basis_size]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases mir <;> decide +kernel

theorem barrel_metrics (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool) :
    toffoliCount (barrel (start j) mir) = barrelT (start j) mir ∧
    measurementCount (barrel (start j) mir) = barrelM (start j) mir ∧
    Challenge.gateSlots (barrel (start j) mir) = barrelSlots (start j) mir := by
  have hn := usedWidth j lo hi
  have h : count (barrel (start j) mir) = listedPrice (barrelWidth (start j)) mir := by
    unfold barrel
    rw [renamed, logical_count _ _ (fun pair hm => field_count _ (schedule_fields _ hn pair hm) _),
        window_price _ hn]
  exact ⟨congrArg Count.t h, congrArg Count.m h, congrArg Count.slots h⟩

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrelMetrics ====

-- ==== begin CRTLinear ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

/-- Evaluate a binary matrix row against the indicated number of input bits. -/
def rowValue (x : Nat → Bool) (row : Nat) : Nat → Bool
  | 0 => false
  | n+1 => rowValue x row n ^^ (row.testBit n && x n)

theorem rowValue_xor (x : Nat → Bool) (a b n : Nat) :
    rowValue x (a ^^^ b) n = (rowValue x a n ^^ rowValue x b n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rowValue, ih, Nat.testBit_xor]
    cases rowValue x a n <;> cases rowValue x b n <;> cases a.testBit n <;>
      cases b.testBit n <;> cases x n <;> rfl

def cnotProgram (ops : List (Wire × Wire)) : Program :=
  ops.map fun (a,b) => .CX a b

theorem inverse_cnot (a b : Wire) (hab : a ≠ b) (s : State) (m n : List Bool) :
    run [.CX a b] n (run [.CX a b] m s) = s := by
  cases s with
  | mk ph bits =>
    change State.mk ph _ = State.mk ph bits
    congr 1
    funext q
    by_cases e : q = b
    · subst q; simp [run, writeBit, Function.update_of_ne hab]
    · simp [run, writeBit, Function.update_of_ne e]

theorem reverse_cnots (ops : List (Wire × Wire)) (apart : ∀ p ∈ ops, p.1 ≠ p.2)
    (s : State) (m n : List Bool) :
    run (cnotProgram ops.reverse) n (run (cnotProgram ops) m s) = s := by
  induction ops generalizing s m n with
  | nil => rfl
  | cons p tail ih =>
    obtain ⟨a,b⟩ := p
    have sep := apart (a,b) (by simp)
    have rest : ∀ p ∈ tail, p.1 ≠ p.2 := fun p hp => apart p (List.mem_cons_of_mem _ hp)
    change run (cnotProgram (((a,b) :: tail).reverse)) n
      (run (cnotProgram tail) m (run [.CX a b] m s)) = s
    rw [List.reverse_cons, cnotProgram, List.map_append]
    rw [run_append, run_take]
    change run [.CX a b] _ (run (cnotProgram tail.reverse) n
      (run (cnotProgram tail) m (run [.CX a b] m s))) = s
    rw [ih rest]
    exact inverse_cnot a b sep s m _

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTLinear ====

-- ==== begin CRTMeasurement ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTMeasurement ====

-- ==== begin CRTPlacement ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.RecordedQuantum

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Placement

/-- A proper gate whose targets, controls and both correction lists stay in S. -/
def Fits (S : Wire → Prop) (P : Program) : Prop :=
  ∀ i ∈ P, PhysicalInstr (.gate i) ∧ ∀ q ∈ i.wires, S q

theorem fits_append {S : Wire → Prop} {p q : Program} (hp : Fits S p) (hq : Fits S q) :
    Fits S (p++q) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hp i hi
  · exact hq i hi

theorem fits_reverse {S : Wire → Prop} {p : Program} (hp : Fits S p) : Fits S p.reverse :=
  fun i hi => hp i (List.mem_reverse.mp hi)

theorem fits_flatMap {α} {S : Wire → Prop} (xs : List α) (f : α → Program)
    (h : ∀ x ∈ xs, Fits S (f x)) : Fits S (xs.flatMap f) := by
  intro i hi
  obtain ⟨x,hx,hit⟩ := List.mem_flatMap.mp hi
  exact h x hx i hit

theorem fits_map {α} {S : Wire → Prop} (xs : List α) (f : α → Instr)
    (h : ∀ x ∈ xs, PhysicalInstr (.gate (f x)) ∧ ∀ q ∈ (f x).wires, S q) : Fits S (xs.map f) := by
  intro i hi
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hi
  exact h x hx

theorem support {S : Wire → Prop} {p : Program} (h : Fits S p) : ∀ q ∈ wires p, S q := by
  induction p with
  | nil => simp [wires]
  | cons i p ih =>
    intro q hq
    rcases Finset.mem_union.mp hq with a | a
    · exact (h i (by simp)).2 q a
    · exact ih (fun j hj => h j (List.mem_cons_of_mem i hj)) q a

theorem fits_rename {S T : Wire → Prop} (f : Wire → Wire) (p : Program) (hp : Fits S p)
    (bound : ∀ q, S q → T (f q)) (inj : ∀ a, S a → ∀ b, S b → f a = f b → a = b) :
    Fits T (renameProgram f p) := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  obtain ⟨phy, sub⟩ := hp i hi
  constructor
  · cases i with
    | X t => trivial
    | measureX t c0 c1 => trivial
    | CX a b =>
      intro e
      exact phy (inj a (sub a (by simp [Instr.wires])) b (sub b (by simp [Instr.wires])) e)
    | CCX a b c =>
      have sa := sub a (by simp [Instr.wires])
      have sb := sub b (by simp [Instr.wires])
      have sc := sub c (by simp [Instr.wires])
      exact ⟨fun e => phy.1 (inj a sa c sc e), fun e => phy.2 (inj b sb c sc e)⟩
  · intro q hq
    rw [renameInstr_support, Finset.mem_image] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    exact bound a (sub a ha)

def fieldScope (d q : Nat) : Prop := q < d ∨ 8 ≤ q ∧ q < 34

instance (d q : Nat) : Decidable (fieldScope d q) := by unfold fieldScope; infer_instance

def physicalBit : Instr → Bool
  | .CX a b => decide (a ≠ b)
  | .CCX a b c => decide (a ≠ c ∧ b ≠ c)
  | _ => true

def coreTest (p : Nat) (mir : Bool) : Bool :=
  (fieldCore p mir).all fun i => physicalBit i && decide (∀ q ∈ i.wires, fieldScope (fieldDegree p) q)

theorem fits_core_of_test (p : Nat) (mir : Bool) (h : coreTest p mir = true) :
    Fits (fieldScope (fieldDegree p)) (fieldCore p mir) := by
  intro i hi
  have ok := List.all_eq_true.mp h i hi
  simp only [Bool.and_eq_true] at ok
  obtain ⟨hi, bound⟩ := ok
  refine ⟨?_, of_decide_eq_true bound⟩
  cases i <;> simp_all [physicalBit, PhysicalInstr, ProperGate]

theorem field_place_maps {n off d : Nat} (small : d ≤ 8) (endp : off+d ≤ n) :
    (∀ q, fieldScope d q → fieldPlace n off q < n+26) ∧
    (∀ a, fieldScope d a → ∀ b, fieldScope d b → fieldPlace n off a = fieldPlace n off b → a = b) := by
  constructor
  · intro q hq
    unfold fieldScope at hq
    simp only [fieldPlace]
    split <;> (try split) <;> (try unfold Wire at *) <;> omega
  · intro a ha b hb he
    unfold fieldScope at ha hb
    simp only [fieldPlace] at he
    split at he <;> (try split at he) <;> (try split at he) <;> (try split at he) <;>
      (try unfold Wire at *) <;> omega

theorem stage_fits (n off d m h : Nat) (hd : 0 < d) (endp : off+d*m ≤ n) :
    Fits (· < n+26) (stage n off d m h) := by
  unfold stage
  dsimp only
  split
  · simp [Fits]
  · rename_i wide
    have toggle : Fits (· < n+26) (((List.range 16).filter (fun k => k.testBit h)).map
        (fun k => Instr.CX (n+k) (n+24))) := by
      apply fits_map
      intro k hk
      have sk := List.mem_range.mp (List.mem_filter.mp hk).1
      simp [PhysicalInstr, ProperGate, Instr.wires]
      unfold Wire at *
      omega
    apply fits_append (fits_append toggle ?_) (fits_reverse toggle)
    apply fits_flatMap
    intro j hj
    have sj := List.mem_range.mp (List.mem_reverse.mp hj)
    apply fits_map
    intro i hi
    have si := List.mem_range.mp hi
    have hp := Nat.two_pow_pos h
    have step : d*j < d*(j+2^h) := Nat.mul_lt_mul_of_pos_left (by omega) hd
    have bound : d*(j+2^h)+i < d*m := calc
      _ < d*(j+2^h)+d := Nat.add_lt_add_left si _
      _ = d*(j+2^h+1) := (Nat.mul_succ _ _).symm
      _ ≤ d*m := Nat.mul_le_mul_left _ (by omega)
    simp [PhysicalInstr, ProperGate, Instr.wires]
    unfold Wire at *
    omega

def r8StepGood (st : R8Step) : Bool :=
  (st.tags.all (fun k => decide (k < 16))) &&
  (st.pre.all (fun p => decide (p.1 < 16 ∧ p.2 < 16 ∧ p.1 ≠ p.2))) &&
  decide (st.src < 16 ∧ st.dst < 16 ∧ st.src ≠ st.dst)

theorem pascalR8Steps_good : ∀ mir : Bool, (pascalR8Steps mir).all r8StepGood = true := by decide +kernel

theorem r8Step_fits (n off : Nat) (st : R8Step) (hg : r8StepGood st = true) (endp : off + 16 ≤ n) :
    Fits (· < n + 26) (r8Step n off st) := by
  unfold r8StepGood at hg
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨htags, hpre⟩, hsrc, hdst, hne⟩ := hg
  unfold r8Step
  dsimp only
  have ht : Fits (· < n + 26) (st.tags.map (fun k => Instr.CX (n + k) (n + 24))) := by
    apply fits_map
    intro k hk
    have sk := htags k hk
    simp [PhysicalInstr, ProperGate, Instr.wires]
    unfold Wire at *; omega
  have hp : Fits (· < n + 26) (st.pre.map (fun p => Instr.CX (off + p.1) (off + p.2))) := by
    apply fits_map
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hpre p hp
    simp [PhysicalInstr, ProperGate, Instr.wires]
    unfold Wire at *; omega
  have hc : Fits (· < n + 26) [Instr.CCX (n + 24) (off + st.src) (off + st.dst)] := by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    simp [PhysicalInstr, ProperGate, Instr.wires]
    unfold Wire at *; omega
  exact fits_append (fits_append (fits_append (fits_append ht hp) hc) (fits_reverse hp)) (fits_reverse ht)

theorem pascalR8_fits (n off : Nat) (mir : Bool) (endp : off + 16 ≤ n) :
    Fits (· < n + 26) (pascalR8 n off mir) :=
  fits_flatMap _ _ (fun st hst => r8Step_fits n off st (List.all_eq_true.mp (pascalR8Steps_good mir) st hst) endp)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Placement

end
-- ==== end CRTPlacement ====

-- ==== begin CRTShapeData ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.RecordedQuantum

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Placement
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem fits_core (p : Nat) (hp : UsedField p) (mir : Bool) :
    Fits (fieldScope (fieldDegree p)) (fieldCore p mir) := by
  apply fits_core_of_test
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases mir <;> decide +kernel

theorem used_degree (p : Nat) (hp : UsedField p) : 0 < fieldDegree p ∧ fieldDegree p ≤ 8 := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def pivotTest (n : Nat) : Bool :=
  (pivots n).zipIdx.all fun ((donor,mask),i) => decide (i < n ∧ (donor < n → donor ≠ i) ∧ mask.testBit i = false)

theorem good_pivots (n : Nat) (hn : UsedWidth n) : pivotTest n = true := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def extent (parts : List (Nat × Nat)) : Nat :=
  parts.foldr (fun (p,m) r => fieldDegree p * m + r) 0

theorem schedule_extent (n : Nat) (hn : UsedWidth n) : extent (schedule n) = n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- replay memory (build-chain s5-mem2): one decide per block, each its own kernel check (the single Fin 26 decide
peaked at about +3 to +4.5 GB; per block <= +0.2 GB). -/
private theorem place_nodup_0 : ((List.range (barrelWidth (start ⟨0, by decide⟩)+26)).map (place (start ⟨0, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_1 : ((List.range (barrelWidth (start ⟨1, by decide⟩)+26)).map (place (start ⟨1, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_2 : ((List.range (barrelWidth (start ⟨2, by decide⟩)+26)).map (place (start ⟨2, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_3 : ((List.range (barrelWidth (start ⟨3, by decide⟩)+26)).map (place (start ⟨3, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_4 : ((List.range (barrelWidth (start ⟨4, by decide⟩)+26)).map (place (start ⟨4, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_5 : ((List.range (barrelWidth (start ⟨5, by decide⟩)+26)).map (place (start ⟨5, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_6 : ((List.range (barrelWidth (start ⟨6, by decide⟩)+26)).map (place (start ⟨6, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_7 : ((List.range (barrelWidth (start ⟨7, by decide⟩)+26)).map (place (start ⟨7, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_8 : ((List.range (barrelWidth (start ⟨8, by decide⟩)+26)).map (place (start ⟨8, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_9 : ((List.range (barrelWidth (start ⟨9, by decide⟩)+26)).map (place (start ⟨9, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_10 : ((List.range (barrelWidth (start ⟨10, by decide⟩)+26)).map (place (start ⟨10, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_11 : ((List.range (barrelWidth (start ⟨11, by decide⟩)+26)).map (place (start ⟨11, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_12 : ((List.range (barrelWidth (start ⟨12, by decide⟩)+26)).map (place (start ⟨12, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_13 : ((List.range (barrelWidth (start ⟨13, by decide⟩)+26)).map (place (start ⟨13, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_14 : ((List.range (barrelWidth (start ⟨14, by decide⟩)+26)).map (place (start ⟨14, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_15 : ((List.range (barrelWidth (start ⟨15, by decide⟩)+26)).map (place (start ⟨15, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_16 : ((List.range (barrelWidth (start ⟨16, by decide⟩)+26)).map (place (start ⟨16, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_17 : ((List.range (barrelWidth (start ⟨17, by decide⟩)+26)).map (place (start ⟨17, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_18 : ((List.range (barrelWidth (start ⟨18, by decide⟩)+26)).map (place (start ⟨18, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_19 : ((List.range (barrelWidth (start ⟨19, by decide⟩)+26)).map (place (start ⟨19, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_20 : ((List.range (barrelWidth (start ⟨20, by decide⟩)+26)).map (place (start ⟨20, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_21 : ((List.range (barrelWidth (start ⟨21, by decide⟩)+26)).map (place (start ⟨21, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_22 : ((List.range (barrelWidth (start ⟨22, by decide⟩)+26)).map (place (start ⟨22, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_23 : ((List.range (barrelWidth (start ⟨23, by decide⟩)+26)).map (place (start ⟨23, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_24 : ((List.range (barrelWidth (start ⟨24, by decide⟩)+26)).map (place (start ⟨24, by decide⟩))).Nodup := by
  decide +kernel

private theorem place_nodup : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    ((List.range (barrelWidth (start j)+26)).map (place (start j))).Nodup := by
  intro j lo hi
  rcases j with ⟨k, hk⟩
  change k ≤ 24 at hi
  interval_cases k
  exacts [place_nodup_0, place_nodup_1, place_nodup_2, place_nodup_3, place_nodup_4, place_nodup_5, place_nodup_6, place_nodup_7, place_nodup_8, place_nodup_9, place_nodup_10, place_nodup_11, place_nodup_12, place_nodup_13, place_nodup_14, place_nodup_15, place_nodup_16, place_nodup_17, place_nodup_18, place_nodup_19, place_nodup_20, place_nodup_21, place_nodup_22, place_nodup_23, place_nodup_24]

theorem place_inj (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) : ∀ a, a < barrelWidth (start j)+26 →
    ∀ b, b < barrelWidth (start j)+26 → place (start j) a = place (start j) b → a = b := by
  intro a ha b hb
  exact List.inj_on_of_nodup_map (place_nodup j lo hi) (List.mem_range.mpr ha) (List.mem_range.mpr hb)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Placement

end
-- ==== end CRTShapeData ====

-- ==== begin CRTPhysical ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.RecordedQuantum

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Placement

theorem basis_pairs (n : Nat) (hn : UsedWidth n) :
    ∀ pair ∈ basisNetwork n, pair.1 < n ∧ pair.2 < n ∧ pair.1 ≠ pair.2 := by
  intro pair hp
  obtain ⟨⟨⟨donor,mask⟩,i⟩,hit,hlist⟩ := List.mem_flatMap.mp (List.mem_reverse.mp hp)
  have h := of_decide_eq_true (List.all_eq_true.mp (good_pivots n hn) _ hit)
  change i < n ∧ (donor < n → donor ≠ i) ∧ mask.testBit i = false at h
  change pair ∈ (if donor < n then [(donor,i)] else []) ++ (selected n mask).map (fun j => (i,j)) at hlist
  rcases List.mem_append.mp hlist with hd | ht
  · split at hd
    · rename_i within
      simp only [List.mem_singleton] at hd
      subst pair
      exact ⟨within,h.1,h.2.1 within⟩
    · simp at hd
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    obtain ⟨bound,bit⟩ := List.mem_filter.mp hj
    refine ⟨h.1,List.mem_range.mp bound,?_⟩
    change i ≠ j
    rintro rfl
    simp [h.2.2] at bit

theorem basis_fits (n : Nat) (hn : UsedWidth n) :
    Fits (· < n+26) ((basisNetwork n).map fun (i,j) => Instr.CX i j) := by
  apply fits_map
  intro pair hp
  obtain ⟨a,b⟩ := pair
  obtain ⟨ha,hb,apart⟩ := basis_pairs n hn (a,b) hp
  change a < n at ha
  change b < n at hb
  refine ⟨apart,?_⟩
  intro q hq
  simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with eq | eq
  · subst q; exact Nat.lt_of_lt_of_le ha (Nat.le_add_right _ _)
  · subst q; exact Nat.lt_of_lt_of_le hb (Nat.le_add_right _ _)

theorem primary_fits (n off p m : Nat) (hp : UsedField p) (endp : off+fieldDegree p*m ≤ n) (mir : Bool) :
    Fits (· < n+26) (primary n off p m mir) := by
  obtain ⟨pos,small⟩ := used_degree p hp
  unfold primary
  apply fits_append
  · apply fits_flatMap
    intro j hj
    have next := Nat.mul_le_mul_left (fieldDegree p) (List.mem_range.mp hj : j+1 ≤ m)
    rw [Nat.mul_succ] at next
    have bounds := field_place_maps (n := n) (off := off+fieldDegree p*j) small (by omega)
    exact fits_rename _ _ (fits_core p hp mir) bounds.1 bounds.2
  · by_cases h82 : (fieldDegree p == 8 && m == 2) = true
    · rw [if_pos h82]
      simp only [Bool.and_eq_true, beq_iff_eq] at h82
      have h16 : fieldDegree p * m = 16 := by rw [h82.1, h82.2]
      exact pascalR8_fits n off mir (by omega)
    · rw [if_neg h82]
      have tri := fits_flatMap (List.range 4) (stage n off (fieldDegree p) m)
                    (fun h _ => stage_fits n off (fieldDegree p) m h pos endp)
      cases mir
      · exact tri
      · exact fits_reverse tri

theorem components_fits (n : Nat) (mir : Bool) (off : Nat) (parts : List (Nat × Nat))
    (endp : off+extent parts ≤ n) (fields : ∀ pair ∈ parts, UsedField pair.1) :
    Fits (· < n+26) (components n mir off parts) := by
  induction parts generalizing off with
  | nil => simp [components,Fits]
  | cons pair tail ih =>
    obtain ⟨p,m⟩ := pair
    change off+(fieldDegree p*m + extent tail) ≤ n at endp
    exact fits_append (primary_fits n off p m (fields (p,m) (by simp)) (by omega) mir)
      (ih _ (by omega) (fun x hx => fields x (List.mem_cons_of_mem _ hx)))

theorem logical_fits (n : Nat) (hn : UsedWidth n) (mir : Bool) : Fits (· < n+26) (logical n mir) := by
  have basis := basis_fits n hn
  exact fits_append (fits_append basis (components_fits n mir 0 (schedule n)
    (by rw [schedule_extent n hn]; omega) (schedule_fields n hn))) (fits_reverse basis)

theorem barrel_phys (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool) :
    GatePhysical (barrel (start j) mir) := by
  have logicalOK := logical_fits _ (usedWidth j lo hi) mir
  have physicalOK := fits_rename (T := fun _ => True) (place (start j)) _ logicalOK
    (fun _ _ => trivial) (place_inj j lo hi)
  exact fun i hit => (physicalOK i hit).1

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTPhysical ====

-- ==== begin CRTBarrelChecks ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

private theorem tag_mem : ∀ i : Fin 16, Partial.tagsP.getD i.val 1560 ∈ Partial.tagsP := by
  decide +kernel

theorem barrelWidth_le : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    barrelWidth (start j) ≤ Shadow7.wpP (start j) + 15 := by decide +kernel

theorem place_mem (s x : Nat) :
    (∃ i, i < barrelWidth s ∧ place s x = Shadow7.bankW s i) ∨
    (∃ k, k < 10 ∧ place s x = Shadow7.poolW s (17+k)) ∨ place s x ∈ Partial.tagsP := by
  by_cases h : x < barrelWidth s
  · exact Or.inl ⟨x, h, by simp [place, h]⟩
  by_cases t : x < barrelWidth s + 16
  · apply Or.inr (Or.inr ?_)
    have k : x - barrelWidth s < 16 := by omega
    simpa only [place, if_neg h, if_pos t] using tag_mem ⟨_, k⟩
  · right; left
    exact ⟨(x - barrelWidth s - 16) % 10, Nat.mod_lt _ (by decide), by simp [place, h, t]⟩

theorem barrel_wires (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool) :
    ∀ q ∈ wires (barrel (start j) mir),
      (∃ i, i < Shadow7.wpP (start j)+15 ∧ q = Shadow7.bankW (start j) i) ∨
      (∃ k, k < 10 ∧ q = Shadow7.poolW (start j) (17+k)) ∨ q ∈ Partial.tagsP := by
  intro q h
  rw [barrel, renameProgram_support, Finset.mem_image] at h
  obtain ⟨x, _, rfl⟩ := h
  rcases place_mem (start j) x with ⟨i, hiw, eq⟩ | rest
  · exact Or.inl ⟨i, Nat.lt_of_lt_of_le hiw (barrelWidth_le j lo hi), eq⟩
  · exact Or.inr rest

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrelChecks ====

-- ==== begin CRTField ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field
open CodecBitSliceVerify

/-- A column packs the value of one wire for each possible input row. -/
def rowWord (cols : Cols) (row : Nat) : Nat := packBits (cols.map (·.testBit row))

theorem run_columns (P : Program) (input output : Cols) (mask row : Nat)
    (hm : mask.testBit row = true) (hb : ∀ i ∈ P, target i < input.length)
    (checked : eval mask P input = (true, output)) (phase : Bool) (tape : List Bool) :
    run P tape ⟨phase, MeasuredCodec5.bitsOf (rowWord input row)⟩ =
      ⟨phase, MeasuredCodec5.bitsOf (rowWord output row)⟩ := by
  have initial : Rel input (rowWord input row) row := fun q => pack_rows input row q
  have proof := eval_sound mask row hm P input _ hb initial (congrArg Prod.fst checked)
  rw [MeasuredCodec5.run_sim, MeasuredCodec5.sim_safe P _ proof.1]
  apply congrArg (State.mk phase)
  funext q
  change (MeasuredCodec5.bitRun P _).testBit q = (rowWord output row).testBit q
  rw [proof.2 q, checked]
  exact (pack_rows output row q).symm

/-- Slot zero means no tag. Slot k+1 selects k; each slot contains all 2^d input words. -/
def tagColumn (d k : Nat) : Nat := CertificateBits.mask d <<< ((k+1)*2^d)

def inputColumn (d q : Nat) : Nat :=
  if q < d then CertificateBits.input (d+5) q else if 18 ≤ q ∧ q < 34 then tagColumn d (q-18) else 0

def inputCols (d : Nat) : Cols := (List.range 34).map (inputColumn d)

/-- The opposite direction's erasure masks give the rows of this scalar minus identity. -/
def rowMask (p : Nat) (mir : Bool) (i : Nat) := (eraseMasks p (!mir)).getD i 0

def outputColumn (p : Nat) (mir : Bool) (q : Nat) : Nat :=
  let d := fieldDegree p
  if q < d then
    let extra := (List.range 16).flatMap fun k => (selected d ((rowMask p mir q) >>> (k*d))).map
      fun j => tagColumn d k &&& inputColumn d j
    extra.foldl Nat.xor (inputColumn d q)
  else inputColumn d q

def outputCols (p : Nat) (mir : Bool) : Cols := (List.range 34).map (outputColumn p mir)

def fieldTest (p : Nat) (mir : Bool) : Bool :=
  let P := fieldCore p mir
  let d := fieldDegree p
  (P.all (fun i => decide (target i < 34))) &&
    (eval (CertificateBits.mask (d+5)) P (inputCols d) == (true, outputCols p mir))

theorem run_field_of_test (p : Nat) (mir : Bool) (tested : fieldTest p mir = true)
    (row : Nat) (small : row < 2^(fieldDegree p+5)) (phase : Bool) (m : List Bool) :
    run (fieldCore p mir) m ⟨phase, MeasuredCodec5.bitsOf (rowWord (inputCols (fieldDegree p)) row)⟩ =
      ⟨phase, MeasuredCodec5.bitsOf (rowWord (outputCols p mir) row)⟩ := by
  simp only [fieldTest, Bool.and_eq_true] at tested
  obtain ⟨bound, check⟩ := tested
  apply run_columns _ _ _ (CertificateBits.mask (fieldDegree p+5)) row
  · exact CertificateBits.mask_bit _ _ small
  · intro i hi
    simpa [inputCols] using (of_decide_eq_true (List.all_eq_true.mp bound i hi))
  · exact beq_iff_eq.mp check

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field

end
-- ==== end CRTField ====

-- ==== begin CRTFieldCases ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

private theorem field_tested_257 : ∀ mir : Bool, fieldTest 257 mir = true := by decide +kernel

private theorem field_tested_313 : ∀ mir : Bool, fieldTest 313 mir = true := by decide +kernel

private theorem field_tested_471 : ∀ mir : Bool, fieldTest 471 mir = true := by decide +kernel

theorem field_tested (p : Nat) (hp : UsedField p) (mir : Bool) : fieldTest p mir = true := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · exact field_tested_257 mir
  · exact field_tested_313 mir
  · exact field_tested_471 mir

theorem run_field (p : Nat) (hp : UsedField p) (mir : Bool) (row : Nat) (small : row < 2^(fieldDegree p+5))
    (phase : Bool) (m : List Bool) :
    run (fieldCore p mir) m ⟨phase, MeasuredCodec5.bitsOf (rowWord (inputCols (fieldDegree p)) row)⟩ =
      ⟨phase, MeasuredCodec5.bitsOf (rowWord (outputCols p mir) row)⟩ :=
  run_field_of_test p mir (field_tested p hp mir) row small phase m

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field

end
-- ==== end CRTFieldCases ====

-- ==== begin CRTFieldRows ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field

/-- Apply a scalar matrix to one row, allowing the row entries to be Boolean values or linear forms. -/
def accumulate {α : Type} (p : Nat) (mir : Bool) (q : Nat) (combine : α → α → α)
    (source : Nat → α) (term : Nat → Nat → α) : α :=
  let d := fieldDegree p
  ((List.range 16).flatMap fun k => (selected d (rowMask p mir q >>> (k*d))).map (term k)).foldl combine (source q)

private theorem map_fold {α β} (f : α → β) (op : α → α → α) (op' : β → β → β)
    (pres : ∀ a b, f (op a b) = op' (f a) (f b)) (xs : List α) (a : α) :
    f (xs.foldl op a) = (xs.map f).foldl op' (f a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons]; rw [ih,pres]

theorem map_accumulate {α β} (p : Nat) (mir : Bool) (q : Nat) (f : α → β)
    (op : α → α → α) (op' : β → β → β) (pres : ∀ a b, f (op a b) = op' (f a) (f b))
    (src : Nat → α) (term : Nat → Nat → α) :
    f (accumulate p mir q op src term) =
      accumulate p mir q op' (fun j => f (src j)) (fun k j => f (term k j)) := by
  unfold accumulate
  rw [map_fold _ _ _ pres]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

/-- Linear forms for the output coefficient bits under a fixed selector. -/
def scalarRow (p : Nat) (mir : Bool) (hot : Nat → Bool) (data : Nat → Nat) (q : Nat) : Nat :=
  accumulate p mir q Nat.xor data (fun k j => if hot k then data j else 0)

theorem rowValue_zero (x : Nat → Bool) (n : Nat) : rowValue x 0 n = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rowValue,ih]

theorem accumulate_congr {α} (p : Nat) (mir : Bool) (q : Nat) (op : α → α → α)
    (src src' : Nat → α) (a b : Nat → Nat → α) (hs : src q = src' q)
    (ht : ∀ k, ∀ j < fieldDegree p, a k j = b k j) :
    accumulate p mir q op src a = accumulate p mir q op src' b := by
  have same k : (selected (fieldDegree p) (rowMask p mir q >>> (k*fieldDegree p))).map (a k) =
      (selected (fieldDegree p) (rowMask p mir q >>> (k*fieldDegree p))).map (b k) := by
    apply List.map_congr_left
    intro j hj
    exact ht k j (List.mem_range.mp (List.mem_filter.mp hj).1)
  unfold accumulate
  simp only [same,hs]

theorem output_bit (p : Nat) (mir : Bool) (q : Nat) (hq : q < fieldDegree p) (row dim : Nat)
    (x : Nat → Bool) (hot : Nat → Bool) (data : Nat → Nat)
    (ht : ∀ k, (tagColumn (fieldDegree p) k).testBit row = hot k)
    (hd : ∀ j < fieldDegree p, (inputColumn (fieldDegree p) j).testBit row = rowValue x (data j) dim) :
    (outputColumn p mir q).testBit row = rowValue x (scalarRow p mir hot data q) dim := by
  simp only [outputColumn, if_pos hq]
  change ((accumulate p mir q Nat.xor (inputColumn (fieldDegree p))
    (fun k j => tagColumn (fieldDegree p) k &&& inputColumn (fieldDegree p) j))).testBit row = _
  rw [map_accumulate p mir q (fun a : Nat => a.testBit row) Nat.xor Bool.xor (fun _ _ => Nat.testBit_xor ..)]
  unfold scalarRow
  rw [map_accumulate p mir q (fun a => rowValue x a dim) Nat.xor Bool.xor (fun a b => rowValue_xor x a b dim)]
  apply accumulate_congr
  · exact hd q hq
  · intro k j hj
    rw [Nat.testBit_and,ht,hd j hj]
    cases hot k <;> simp [rowValue_zero]

def packedRow (d slot v : Nat) : Nat := v+slot*2^d

theorem packedRow_lt {d slot v : Nat} (sv : v < 2^d) (ss : slot < 32) : packedRow d slot v < 2^(d+5) := by
  have h := Nat.mul_le_mul_right (2^d) (show slot+1 ≤ 32 by omega)
  simp only [Nat.succ_mul] at h
  unfold packedRow
  rw [Nat.pow_add, show 2^5 = 32 by decide]
  omega

theorem data_bit {d q slot v : Nat} (sq : q < d) (sv : v < 2^d) (ss : slot < 32) :
    (inputColumn d q).testBit (packedRow d slot v) = v.testBit q := by
  rw [inputColumn,if_pos sq,CertificateBits.input_bit _ _ _ (packedRow_lt sv ss)]
  have low : packedRow d slot v % 2^d = v := by simp [packedRow, Nat.mod_eq_of_lt sv]
  have bit := congrArg (fun a : Nat => a.testBit q) low
  simpa only [Nat.testBit_mod_two_pow,sq,decide_true,Bool.true_and] using bit

theorem tag_bit {d slot v : Nat} (sv : v < 2^d) (k : Nat) :
    (tagColumn d k).testBit (packedRow d slot v) = decide (slot = k+1) := by
  let b := 2^d
  change ((2^b-1) <<< ((k+1)*b)).testBit (v+slot*b) = _
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  change v < b at sv
  rcases lt_trichotomy slot (k+1) with low | eq | high
  · have h := Nat.mul_le_mul_right b (show slot+1 ≤ k+1 by omega)
    rw [Nat.succ_mul] at h
    simp [show ¬v+slot*b ≥ (k+1)*b by omega,show slot ≠ k+1 by omega]
  · subst slot
    simp [sv]
  · have h := Nat.mul_le_mul_right b (show k+1+1 ≤ slot by omega)
    rw [Nat.succ_mul] at h
    simp [show ¬v+slot*b-(k+1)*b < b by omega,show slot ≠ k+1 by omega]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field

end
-- ==== end CRTFieldRows ====

-- ==== begin CRTMatrix ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Matrix

abbrev Rows := Array Nat

def read (rows : Rows) (q : Nat) := (rows[q]?).getD 0

def basis (rows : Rows) (word : Nat → Bool) (dim : Nat) (outside : BasisState) (q : Wire) : Bool :=
  if q < rows.size then rowValue word (read rows q) dim else outside q

def applyPair (rows : Rows) (op : Wire × Wire) : Rows :=
  rows.setIfInBounds op.2 (read rows op.2 ^^^ read rows op.1)

def applyOps (ops : List (Wire × Wire)) (rows : Rows) : Rows := ops.foldl applyPair rows

@[simp] theorem applyPair_size (rows : Rows) (op : Wire × Wire) : (applyPair rows op).size = rows.size := by
  simp [applyPair]

@[simp] theorem applyOps_size (ops : List (Wire × Wire)) (rows : Rows) : (applyOps ops rows).size = rows.size := by
  induction ops generalizing rows with
  | nil => rfl
  | cons op tail ih => exact (ih (applyPair rows op)).trans (applyPair_size rows op)

theorem run_ops (ops : List (Wire × Wire)) (rows : Rows) (x : Nat → Bool) (dim : Nat)
    (outside : BasisState) (ph : Bool) (m : List Bool)
    (within : ∀ op ∈ ops, op.1 < rows.size ∧ op.2 < rows.size) :
    run (cnotProgram ops) m ⟨ph,basis rows x dim outside⟩ =
      ⟨ph,basis (applyOps ops rows) x dim outside⟩ := by
  induction ops generalizing rows with
  | nil => rfl
  | cons op tail ih =>
    obtain ⟨a,b⟩ := op
    obtain ⟨ha,hb⟩ := within (a,b) (by simp)
    change a < rows.size at ha
    change b < rows.size at hb
    have step : writeBit (basis rows x dim outside) b
        (basis rows x dim outside b ^^ basis rows x dim outside a) =
        basis (applyPair rows (a,b)) x dim outside := by
      funext q
      by_cases e : q = b
      · subst q
        simp [basis,read,applyPair,writeBit,ha,hb,rowValue_xor]
      · simp [basis,read,applyPair,writeBit,Function.update_of_ne e,Ne.symm e]
    change run (cnotProgram tail) m ⟨ph,_⟩ = _
    rw [step]
    apply ih
    intro op ho
    simpa only [applyPair_size] using within op (List.mem_cons_of_mem _ ho)

theorem apply_map (ops : List (Wire × Wire)) (f : Nat → Nat) (zero : f 0 = 0)
    (linear : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (rows : Rows) :
    applyOps ops (rows.map f) = (applyOps ops rows).map f := by
  have mapRead (r : Rows) (i : Nat) : read (r.map f) i = f (read r i) := by
    unfold read
    rw [Array.getElem?_map]
    cases r[i]? <;> simp [zero]
  have step (r : Rows) (p : Wire × Wire) : applyPair (r.map f) p = (applyPair r p).map f := by
    unfold applyPair
    rw [mapRead,mapRead,←linear]
    apply Array.ext_getElem?; intro i
    simp only [Array.getElem?_map, Array.getElem?_setIfInBounds, Array.size_map]
    split <;> (try split) <;> rfl
  induction ops generalizing rows with
  | nil => rfl
  | cons op tail ih =>
    change applyOps tail (applyPair (rows.map f) op) = (applyOps tail (applyPair rows op)).map f
    rw [step,ih]

def units (n : Nat) : Rows := Array.ofFn (fun i : Fin n => 2^i.val)

theorem value_unit (x : Nat → Bool) (i dim : Nat) :
    rowValue x (2^i) dim = if i < dim then x i else false := by
  induction dim with
  | zero => simp [rowValue]
  | succ n ih =>
    simp only [rowValue,ih,Nat.testBit_two_pow]
    by_cases e : i = n
    · subst i; simp
    · by_cases h : i<n
      · simp [e,h,show i < n+1 by omega]
      · simp [e,h,show ¬i < n+1 by omega]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Matrix

end
-- ==== end CRTMatrix ====

-- ==== begin CRTFieldRun ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Field Placement Matrix CodecBitSliceVerify

def flags (n slot q : Nat) : Bool := decide (n ≤ q ∧ q < n+16 ∧ slot = q-n+1)

def frame (rows : Rows) (x : Nat → Bool) (dim slot : Nat) (ph : Bool) : State :=
  ⟨ph, Matrix.basis rows x dim (flags rows.size slot)⟩

def scalarRows (rows : Rows) (p : Nat) (mir : Bool) (slot off : Nat) : Rows :=
  Array.ofFn fun q : Fin rows.size =>
    if off ≤ q.val ∧ q.val < off + fieldDegree p then
      scalarRow p mir (fun k => decide (slot = k+1)) (fun j => read rows (off+j)) (q.val-off)
    else read rows q.val

@[simp] theorem scalarRows_size (r : Rows) (p : Nat) (mir : Bool) (s o : Nat) :
    (scalarRows r p mir s o).size = r.size := by simp [scalarRows]

theorem scalar_read {r : Rows} {q : Nat} (hq : q < r.size) (p : Nat) (mir : Bool) (slot off : Nat) :
    read (scalarRows r p mir slot off) q =
      if off ≤ q ∧ q < off+fieldDegree p then
        scalarRow p mir (fun k => decide (slot = k+1)) (fun j => read r (off+j)) (q-off)
      else read r q := by
  simp [scalarRows,Matrix.read,hq]

def fieldPool (d : Nat) := (Finset.range 34).filter (fieldScope d)

theorem fieldPool_iff {d q : Nat} (sd : d ≤ 8) : q ∈ fieldPool d ↔ fieldScope d q := by
  simp only [fieldPool,Finset.mem_filter,Finset.mem_range]
  unfold fieldScope
  omega

private theorem pack_lt (bs : List Bool) : packBits bs < 2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp [packBits, Nat.bit, Nat.pow_succ] <;> omega

def fieldWord (d : Nat) (getBit : Nat → Bool) : Nat := packBits ((List.range d).map getBit)

theorem fieldWord_small (d : Nat) (v : Nat → Bool) : fieldWord d v < 2^d := by
  simpa [fieldWord] using pack_lt ((List.range d).map v)

theorem fieldWord_bit (d : Nat) (v : Nat → Bool) (q : Nat) (hq : q < d) :
    (fieldWord d v).testBit q = v q := by
  simp [fieldWord,pack_testBit,List.getElem?_map,List.getElem?_range hq]

private theorem column_bit (f : Nat → Nat) (row q : Nat) (hq : q < 34) :
    (rowWord ((List.range 34).map f) row).testBit q = (f q).testBit row := by
  rw [rowWord,pack_rows,List.getElem?_map,List.getElem?_range hq]
  rfl

theorem frame_field (r : Rows) (p : Nat) (hp : UsedField p) (mir : Bool) (off slot dim : Nat)
    (small : slot < 32) (endp : off+fieldDegree p ≤ r.size) (x : Nat → Bool) (ph : Bool) (m : List Bool) :
    run (renameProgram (fieldPlace r.size off) (fieldCore p mir)) m (frame r x dim slot ph) =
      frame (scalarRows r p mir slot off) x dim slot ph := by
  let d := fieldDegree p
  let f := fieldPlace r.size off
  let data := fun j => read r (off+j)
  let v := fieldWord d (fun j => rowValue x (data j) dim)
  let row := packedRow d slot v
  have sd := (used_degree p hp).2
  have sv : v < 2^d := fieldWord_small _ _
  have val (j : Nat) (hj : j < d) : (inputColumn d j).testBit row = rowValue x (data j) dim :=
    (data_bit hj sv small).trans (fieldWord_bit _ _ _ hj)
  have tags (k : Nat) : (tagColumn d k).testBit row = decide (slot=k+1) := tag_bit sv k
  have live := Placement.support (fits_core p hp mir)
  have sub : wires (fieldCore p mir) ⊆ fieldPool d := fun _ h => (fieldPool_iff sd).mpr (live _ h)
  have maps := field_place_maps sd endp
  have inj : ∀ a ∈ fieldPool d, ∀ b ∈ fieldPool d, f a = f b → a = b :=
    fun a ha b hb => maps.2 a ((fieldPool_iff sd).mp ha) b ((fieldPool_iff sd).mp hb)
  have point (q : Nat) (hq : fieldScope d q) :
      (inputColumn d q).testBit row = (frame r x dim slot ph).basis (f q) := by
    by_cases left : q < d
    · have lt : q < 8 := by omega
      have inside : off+q < r.size := by omega
      simpa [frame,Matrix.basis,f,fieldPlace,lt,inside,data] using val q left
    · obtain hq := hq.resolve_left left
      by_cases mid : q < 18
      · simp [frame,Matrix.basis,f,fieldPlace,inputColumn,left,flags,show ¬q<8 by omega,mid,
          show ¬18≤q by omega,show ¬r.size+16+(q-8)<r.size by omega,
          show ¬r.size+16+(q-8)<r.size+16 by omega]
      · have inside : r.size+(q-18) < r.size+16 := by omega
        simp [frame,Matrix.basis,f,fieldPlace,inputColumn,left,flags,show ¬q<8 by omega,mid,
          show 18≤q by omega,hq.2,inside,tags]
  have rel := run_rename_pool f (fieldPool d) inj (fieldCore p mir) sub m
    ⟨ph,MeasuredCodec5.bitsOf (rowWord (inputCols d) row)⟩ (frame r x dim slot ph) rfl (by
      intro q hq
      have bound := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
      exact (column_bit (inputColumn d) row q bound).trans (point q ((fieldPool_iff sd).mp hq)))
  rw [run_field p hp mir row (packedRow_lt sv small)] at rel
  refine State.extensionality _ _ ?_ ?_
  · exact rel.1
  funext q
  by_cases inPool : q ∈ (fieldPool d).image f
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp inPool
    rw [rel.2 a ha]
    have shape := (fieldPool_iff sd).mp ha
    have sa := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    change (rowWord (outputCols p mir) row).testBit a = _
    rw [show (rowWord (outputCols p mir) row).testBit a = (outputColumn p mir a).testBit row from
      column_bit _ _ _ sa]
    by_cases left : a < d
    · have a8 : a < 8 := by omega
      have inside : off+a < r.size := by omega
      have inSlice : off ≤ off+a ∧ off+a < off+fieldDegree p := ⟨by omega, Nat.add_lt_add_left left _⟩
      rw [output_bit p mir a left row dim x _ data tags val]
      simp [frame,Matrix.basis,f,fieldPlace,a8,inside,scalar_read inside,inSlice,data]
    · rw [outputColumn,if_neg left]
      rw [point a shape]
      have edge : r.size ≤ f a := by
        obtain ⟨a8,_⟩ := shape.resolve_left left
        unfold f fieldPlace
        simp only [show ¬a<8 by omega,if_false]
        split <;> (try unfold Wire at *) <;> omega
      simp only [frame,Matrix.basis,scalarRows_size,if_neg (Nat.not_lt_of_ge edge)]
  · rw [run_rename_pool_outside f (fieldPool d) (fieldCore p mir) sub m _ q inPool]
    by_cases inside : q < r.size
    · have outsideSlice : ¬(off ≤ q ∧ q < off+fieldDegree p) := by
        rintro ⟨lower,upper⟩
        apply inPool
        have sq : q-off < d := (Nat.sub_lt_iff_lt_add lower).mpr (Nat.add_comm off d ▸ upper)
        refine Finset.mem_image.mpr ⟨q-off,(fieldPool_iff sd).mpr (Or.inl sq),?_⟩
        simpa only [f,fieldPlace,if_pos (Nat.lt_of_lt_of_le sq sd)] using Nat.add_sub_of_le lower
      simp [frame,Matrix.basis,inside,scalar_read inside,outsideSlice]
    · simp [frame,Matrix.basis,inside]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTFieldRun ====

-- ==== begin CRTTriangle ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix

def controlled (c : Wire) (pairs : List (Wire × Wire)) : Program :=
  pairs.map (fun (a,b) => Instr.CCX c a b)

theorem run_controlled (c : Wire) (pairs : List (Wire × Wire)) (m : List Bool) (s : State)
    (apart : ∀ p ∈ pairs, p.2 ≠ c) :
    run (controlled c pairs) m s = if s.basis c then run (cnotProgram pairs) m s else s := by
  induction pairs generalizing s with
  | nil => simp [controlled,cnotProgram,run]
  | cons p tail ih =>
    obtain ⟨a,b⟩ := p
    have ne : b ≠ c := apart (a,b) (by simp)
    have rest : ∀ p ∈ tail, p.2 ≠ c := fun p hp => apart p (List.mem_cons_of_mem _ hp)
    cases s with
    | mk ph bits =>
      cases bit : bits c <;>
        simp only [controlled,cnotProgram,List.map_cons,run,bit,Bool.false_and,Bool.xor_false,
          Bool.true_and,Bool.false_eq_true,if_false,if_true]
      · simpa [writeBit,Function.update_eq_self,controlled,cnotProgram,bit] using ih ⟨ph,bits⟩ rest
      · have unchanged : writeBit bits b (bits b ^^ bits a) c = true := by
          simp [writeBit,Function.update_of_ne ne.symm,bit]
        simpa [controlled,cnotProgram,unchanged] using ih ⟨ph,writeBit bits b (bits b ^^ bits a)⟩ rest

def xorAt (bits : BasisState) : List Wire → Bool
  | [] => false
  | w::ws => bits w ^^ xorAt bits ws

private theorem xorAt_congr (xs : List Wire) (u v : BasisState) (h : ∀ q ∈ xs, u q = v q) :
    xorAt u xs = xorAt v xs := by
  induction xs with
  | nil => rfl
  | cons q xs ih => rw [xorAt,xorAt,h q (by simp),ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

def toggles (xs : List Wire) (t : Wire) : Program := xs.map (fun q => Instr.CX q t)

theorem run_toggles (xs : List Wire) (t : Wire) (sep : t ∉ xs) (m : List Bool) (ph : Bool) (bits : BasisState) :
    run (toggles xs t) m ⟨ph,bits⟩ = ⟨ph,writeBit bits t (bits t ^^ xorAt bits xs)⟩ := by
  induction xs generalizing bits with
  | nil => simp [toggles,xorAt,run,writeBit,Function.update_eq_self]
  | cons q xs ih =>
    have hn : t ∉ xs := fun h => sep (List.mem_cons_of_mem _ h)
    change run (toggles xs t) m ⟨ph,writeBit bits t (bits t ^^ bits q)⟩ = _
    rw [ih hn]
    have same : xorAt (writeBit bits t (bits t ^^ bits q)) xs = xorAt bits xs := by
      apply xorAt_congr
      intro j hj
      have ne : j ≠ t := fun eq => hn (eq ▸ hj)
      simp [writeBit,Function.update_of_ne ne]
    rw [same]
    simp [xorAt,writeBit,Function.update_idem]

def tagSources (n h : Nat) : List Wire :=
  ((List.range 16).filter (fun k => k.testBit h)).map (n+·)

def enabled (n slot h : Nat) := xorAt (flags n slot) (tagSources n h)

def editPairs (off d m h : Nat) : List (Wire × Wire) :=
  (List.range (m-2^h)).reverse.flatMap fun j => (List.range d).map
    (fun i => (off+d*j+i, off+d*(j+2^h)+i))

def oriented {α : Type} (mir : Bool) (xs : List α) := if mir then xs.reverse else xs

def stageRows (rows : Rows) (slot off d m h : Nat) (mir : Bool) : Rows :=
  if m ≤ 2^h then rows else if enabled rows.size slot h then
    applyOps (oriented mir (editPairs off d m h)) rows else rows

@[simp] theorem stageRows_size (rows : Rows) (s o d m h : Nat) (mir : Bool) :
    (stageRows rows s o d m h mir).size = rows.size := by
  unfold stageRows
  split <;> (try split) <;> simp

theorem tagSource_bounds {n h q : Nat} (hit : q ∈ tagSources n h) : n ≤ q ∧ q < n+16 := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hit
  have sk := List.mem_range.mp (List.mem_filter.mp hk).1
  omega

theorem edit_bounds (rows : Rows) (off d m h : Nat) (mir : Bool) (endp : off+d*m ≤ rows.size) :
    ∀ p ∈ oriented mir (editPairs off d m h), p.1 < rows.size ∧ p.2 < rows.size := by
  intro p hp
  have mem : p ∈ editPairs off d m h := by cases mir <;> simpa [oriented] using hp
  obtain ⟨j,hj,atj⟩ := List.mem_flatMap.mp mem
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp atj
  have ji := List.mem_range.mp (List.mem_reverse.mp hj)
  have si := List.mem_range.mp hi
  unfold Wire at *
  have maxj := Nat.mul_le_mul_left d (show j+2^h+1 ≤ m by omega)
  rw [Nat.mul_succ] at maxj
  have ord := Nat.mul_le_mul_left d (Nat.le_add_right j (2^h))
  dsimp only
  omega


def withTag (r : Rows) (x : Nat → Bool) (dim slot h : Nat) (ph : Bool) : State :=
  ⟨ph, Matrix.basis r x dim (writeBit (flags r.size slot) (r.size+24) (enabled r.size slot h))⟩

private theorem toggle_frame (r : Rows) (x : Nat → Bool) (dim slot h : Nat) (ph : Bool) (tape : List Bool) :
    run (toggles (tagSources r.size h) (r.size+24)) tape (frame r x dim slot ph) =
      withTag r x dim slot h ph := by
  have external (q : Wire) (hq : r.size ≤ q) : (frame r x dim slot ph).basis q = flags r.size slot q := by
    simp only [frame,Matrix.basis,if_neg (Nat.not_lt_of_ge hq)]
  have parity := xorAt_congr (tagSources r.size h) (frame r x dim slot ph).basis (flags r.size slot)
    (fun q hq => external q (tagSource_bounds hq).1)
  have sep : r.size+24 ∉ tagSources r.size h := fun hq => by have := (tagSource_bounds hq).2; omega
  change run _ _ ⟨ph,(frame r x dim slot ph).basis⟩ = _
  rw [run_toggles _ _ sep,parity,external _ (by omega)]
  apply congrArg (State.mk ph)
  funext q
  by_cases eq : q = r.size+24
  · subst q; simp [Matrix.basis,flags,writeBit,enabled]
  · by_cases inside : q < r.size <;> simp [frame,Matrix.basis,inside,writeBit,Function.update_of_ne eq]

private theorem tag_restore (r : Rows) (x : Nat → Bool) (dim slot h : Nat) (ph : Bool) (tape : List Bool) :
    run (toggles (tagSources r.size h) (r.size+24)).reverse tape (withTag r x dim slot h ph) =
      frame r x dim slot ph := by
  let ops := (tagSources r.size h).map (fun a => (a,r.size+24))
  have same : cnotProgram ops = toggles (tagSources r.size h) (r.size+24) := by
    simp [cnotProgram,ops,toggles,List.map_map,Function.comp_def]
  have inv := reverse_cnots ops (by
    intro pair hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have b := (tagSource_bounds hq).2
    change q ≠ r.size+24
    exact Nat.ne_of_lt (lt_trans b (by omega : r.size+16 < r.size+24))) (frame r x dim slot ph) [] tape
  have rev : cnotProgram ops.reverse = (cnotProgram ops).reverse := List.map_reverse
  rw [rev,same,toggle_frame] at inv
  exact inv

private theorem stage_shape (n off d m h : Nat) (wide : ¬m≤2^h) (mir : Bool) :
    oriented mir (stage n off d m h) =
    toggles (tagSources n h) (n+24) ++ controlled (n+24) (oriented mir (editPairs off d m h)) ++
      (toggles (tagSources n h) (n+24)).reverse := by
  cases mir <;> simp [oriented,stage,wide,toggles,tagSources,controlled,editPairs,List.map_flatMap,
    List.map_map,Function.comp_def,List.reverse_append,List.append_assoc]

theorem frame_stage (r : Rows) (off d m h : Nat) (mir : Bool) (endp : off+d*m ≤ r.size)
    (x : Nat → Bool) (dim slot : Nat) (ph : Bool) (tape : List Bool) :
    run (oriented mir (stage r.size off d m h)) tape (frame r x dim slot ph) =
      frame (stageRows r slot off d m h mir) x dim slot ph := by
  by_cases short : m ≤ 2^h
  · cases mir <;> simp [stage,stageRows,short,oriented,run]
  rw [stage_shape _ _ _ _ _ short, run_append,run_take,run_append,run_take,toggle_frame]
  let ops := oriented mir (editPairs off d m h)
  have within := edit_bounds r off d m h mir endp
  have sep : ∀ p ∈ ops, p.2 ≠ r.size+24 := fun p hp => by
    have := (within p hp).2; unfold Wire at *; omega
  have bit : (withTag r x dim slot h ph).basis (r.size+24) = enabled r.size slot h := by
    simp [withTag,Matrix.basis,writeBit]
  rw [run_controlled _ _ _ _ sep,bit]
  cases yes : enabled r.size slot h with
  | false => simpa [stageRows,short,yes] using tag_restore r x dim slot h ph _
  | true =>
    simp only [if_true]
    rw [show run (cnotProgram ops) _ (withTag r x dim slot h ph) = withTag (applyOps ops r) x dim slot h ph by
      simpa only [withTag,applyOps_size] using run_ops ops r x dim _ ph _ within]
    simpa only [stageRows,if_neg short,yes,if_true,applyOps_size] using
      tag_restore (applyOps ops r) x dim slot h ph _

def r8Enabled (n slot : Nat) (tags : List Nat) : Bool :=
  xorAt (flags n slot) (tags.map (n + ·))

def r8Ops (off : Nat) (st : R8Step) : List (Wire × Wire) :=
  let pre := st.pre.map (fun p => (off + p.1, off + p.2))
  pre ++ [(off + st.src, off + st.dst)] ++ pre.reverse

def r8StepRows (rows : Rows) (slot off : Nat) (st : R8Step) : Rows :=
  if r8Enabled rows.size slot st.tags then applyOps (r8Ops off st) rows else rows

@[simp] theorem r8StepRows_size (rows : Rows) (s o : Nat) (st : R8Step) :
    (r8StepRows rows s o st).size = rows.size := by
  unfold r8StepRows; split <;> simp

theorem r8Ops_bounds (rows : Rows) (off : Nat) (st : R8Step)
    (hg : Placement.r8StepGood st = true) (endp : off + 16 ≤ rows.size) :
    ∀ p ∈ r8Ops off st, p.1 < rows.size ∧ p.2 < rows.size ∧ p.1 ≠ p.2 := by
  unfold Placement.r8StepGood at hg
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨_, hpre⟩, hsrc, hdst, hne⟩ := hg
  intro p hp
  unfold r8Ops at hp
  rcases List.mem_append.mp hp with hp1 | hp2
  · rcases List.mem_append.mp hp1 with hpA | hpB
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpA
      obtain ⟨h1, h2, h3⟩ := hpre q hq
      unfold Wire at *; dsimp only; omega
    · simp only [List.mem_singleton] at hpB; subst hpB
      unfold Wire at *; dsimp only; omega
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hp2)
    obtain ⟨h1, h2, h3⟩ := hpre q hq
    unfold Wire at *; dsimp only; omega

def withR8Tag (r : Rows) (x : Nat → Bool) (dim slot : Nat) (tags : List Nat) (ph : Bool) : State :=
  ⟨ph, Matrix.basis r x dim (writeBit (flags r.size slot) (r.size+24) (r8Enabled r.size slot tags))⟩

private theorem toggle_r8_frame (r : Rows) (x : Nat → Bool) (dim slot : Nat) (tags : List Nat)
    (htags : ∀ k ∈ tags, k < 16) (ph : Bool) (tape : List Bool) :
    run (toggles (tags.map (r.size + ·)) (r.size+24)) tape (frame r x dim slot ph) =
      withR8Tag r x dim slot tags ph := by
  have external (q : Wire) (hq : r.size ≤ q) : (frame r x dim slot ph).basis q = flags r.size slot q := by
    simp only [frame, Matrix.basis, if_neg (Nat.not_lt_of_ge hq)]
  have parity := xorAt_congr (tags.map (r.size + ·)) (frame r x dim slot ph).basis (flags r.size slot)
    (fun q hq => by obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq; exact external _ (by omega))
  have sep : r.size+24 ∉ tags.map (r.size + ·) := by
    intro hq; obtain ⟨k, hk, he⟩ := List.mem_map.mp hq; have := htags k hk; unfold Wire at *; omega
  change run _ _ ⟨ph, (frame r x dim slot ph).basis⟩ = _
  rw [run_toggles _ _ sep, parity, external _ (by omega)]
  apply congrArg (State.mk ph)
  funext q
  by_cases eq : q = r.size+24
  · subst q; simp [Matrix.basis, flags, writeBit, r8Enabled]
  · by_cases inside : q < r.size <;> simp [frame, Matrix.basis, inside, writeBit, Function.update_of_ne eq]

private theorem tag_r8_restore (r : Rows) (x : Nat → Bool) (dim slot : Nat) (tags : List Nat)
    (htags : ∀ k ∈ tags, k < 16) (ph : Bool) (tape : List Bool) :
    run (toggles (tags.map (r.size + ·)) (r.size+24)).reverse tape (withR8Tag r x dim slot tags ph) =
      frame r x dim slot ph := by
  let ops := (tags.map (r.size + ·)).map (fun a => (a, r.size+24))
  have same : cnotProgram ops = toggles (tags.map (r.size + ·)) (r.size+24) := by
    simp [cnotProgram, ops, toggles, List.map_map, Function.comp_def]
  have inv := reverse_cnots ops (by
    intro pair hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    have := htags k hk; change r.size + k ≠ r.size + 24; unfold Wire at *; omega) (frame r x dim slot ph) [] tape
  have rev : cnotProgram ops.reverse = (cnotProgram ops).reverse := List.map_reverse
  rw [rev, same, toggle_r8_frame r x dim slot tags htags] at inv
  exact inv

theorem frame_r8Step (r : Rows) (off : Nat) (st : R8Step)
    (hg : Placement.r8StepGood st = true) (endp : off + 16 ≤ r.size)
    (x : Nat → Bool) (dim slot : Nat) (ph : Bool) (tape : List Bool) :
    run (r8Step r.size off st) tape (frame r x dim slot ph) =
      frame (r8StepRows r slot off st) x dim slot ph := by
  have hg' := hg
  unfold Placement.r8StepGood at hg'
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hg'
  obtain ⟨⟨htags, hpre⟩, hsrc, hdst, hne⟩ := hg'
  let prePairs : List (Wire × Wire) := st.pre.map (fun p => (off + p.1, off + p.2))
  have hpreB : ∀ p ∈ prePairs, p.1 < r.size ∧ p.2 < r.size := by
    intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, _⟩ := hpre q hq; unfold Wire at *; dsimp only; omega
  have hpreA : ∀ p ∈ prePairs, p.1 ≠ p.2 := by
    intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨_, _, h3⟩ := hpre q hq; unfold Wire at *; dsimp only; omega
  have hpreRevB : ∀ p ∈ prePairs.reverse, p.1 < r.size ∧ p.2 < r.size :=
    fun p hp => hpreB p (List.mem_reverse.mp hp)
  have shape : r8Step r.size off st =
      toggles (st.tags.map (r.size + ·)) (r.size+24) ++ cnotProgram prePairs ++
      controlled (r.size+24) [(off+st.src, off+st.dst)] ++ cnotProgram prePairs.reverse ++
      (toggles (st.tags.map (r.size + ·)) (r.size+24)).reverse := by
    simp [r8Step, toggles, cnotProgram, controlled, prePairs, List.map_reverse, List.map_map, Function.comp_def]
  rw [shape, run_append, run_take, run_append, run_take, run_append, run_take, run_append, run_take]
  rw [toggle_r8_frame r x dim slot st.tags htags]
  have sepC : ∀ p ∈ ([(off+st.src, off+st.dst)] : List (Wire × Wire)), p.2 ≠ r.size+24 := by
    intro p hp; simp only [List.mem_singleton] at hp; subst hp; unfold Wire at *; dsimp only; omega
  have hpreRun : ∀ t, run (cnotProgram prePairs) t (withR8Tag r x dim slot st.tags ph) =
      withR8Tag (applyOps prePairs r) x dim slot st.tags ph := fun t => by
    simpa only [withR8Tag, applyOps_size] using run_ops prePairs r x dim _ ph t hpreB
  cases yes : r8Enabled r.size slot st.tags with
  | false =>
    rw [run_controlled _ _ _ _ sepC]
    have bit : ∀ t, (run (cnotProgram prePairs) t (withR8Tag r x dim slot st.tags ph)).basis (r.size+24) = false := fun t => by
      rw [hpreRun]; simp [withR8Tag, Matrix.basis, writeBit, yes]
    rw [bit]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [reverse_cnots prePairs hpreA]
    simpa [r8StepRows, yes] using tag_r8_restore r x dim slot st.tags htags ph _
  | true =>
    rw [hpreRun, run_controlled _ _ _ _ sepC]
    have bit : (withR8Tag (applyOps prePairs r) x dim slot st.tags ph).basis (r.size+24) = true := by
      simp [withR8Tag, Matrix.basis, writeBit, yes]
    rw [bit]; simp only [↓reduceIte]
    have hmidB : ∀ p ∈ ([(off+st.src, off+st.dst)] : List (Wire × Wire)),
        p.1 < (applyOps prePairs r).size ∧ p.2 < (applyOps prePairs r).size := by
      intro p hp; simp only [List.mem_singleton] at hp; subst hp; rw [applyOps_size]; unfold Wire at *; dsimp only; omega
    have h2 : ∀ t, run (cnotProgram [(off+st.src, off+st.dst)]) t (withR8Tag (applyOps prePairs r) x dim slot st.tags ph) =
        withR8Tag (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)) x dim slot st.tags ph := fun t => by
      simpa only [withR8Tag, applyOps_size] using run_ops [(off+st.src, off+st.dst)] (applyOps prePairs r) x dim _ ph t hmidB
    rw [h2]
    have hrevB : ∀ p ∈ prePairs.reverse,
        p.1 < (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)).size ∧
        p.2 < (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)).size := by
      intro p hp; rw [applyOps_size, applyOps_size]; exact hpreRevB p hp
    have h3 : ∀ t, run (cnotProgram prePairs.reverse) t (withR8Tag (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)) x dim slot st.tags ph) =
        withR8Tag (applyOps prePairs.reverse (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r))) x dim slot st.tags ph := fun t => by
      simpa only [withR8Tag, applyOps_size] using
        run_ops prePairs.reverse (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)) x dim _ ph t hrevB
    rw [h3]
    have hcomb : applyOps prePairs.reverse (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)) = applyOps (r8Ops off st) r := by
      simp [r8Ops, applyOps, prePairs, List.foldl_append]
    rw [hcomb]
    simpa only [r8StepRows, yes, if_true, applyOps_size] using
      tag_r8_restore (applyOps (r8Ops off st) r) x dim slot st.tags htags ph _

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTTriangle ====

-- ==== begin CRTComponents ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix Placement

private theorem run_parts {α} (xs : List α) (g : α → Program) (next : Rows → α → Rows)
    (n : Nat) (x : Nat → Bool) (dim slot : Nat) (ph : Bool) (m : List Bool) (r : Rows) (size : r.size = n)
    (keep : ∀ r a, (next r a).size = r.size)
    (step : ∀ a ∈ xs, ∀ r : Rows, r.size = n → ∀ m,
      run (g a) m (frame r x dim slot ph) = frame (next r a) x dim slot ph) :
    run (xs.flatMap g) m (frame r x dim slot ph) = frame (xs.foldl next r) x dim slot ph := by
  induction xs generalizing r m with
  | nil => rfl
  | cons a xs ih =>
    rw [List.flatMap_cons,run_append,run_take,step a (by simp) r size]
    exact ih _ _ ((keep r a).trans size) (fun y hy => step y (List.mem_cons_of_mem _ hy))

private theorem fold_size {α} (xs : List α) (f : Rows → α → Rows) (r : Rows)
    (h : ∀ r a, (f r a).size = r.size) : (xs.foldl f r).size = r.size := by
  induction xs generalizing r with
  | nil => rfl
  | cons a xs ih => exact (ih (f r a)).trans (h r a)

def scalars (r : Rows) (p m off slot : Nat) (mir : Bool) : Rows :=
  (List.range m).foldl (fun a j => scalarRows a p mir slot (off+fieldDegree p*j)) r

def triRows (r : Rows) (off d m slot : Nat) (mir : Bool) : Rows :=
  (oriented mir (List.range 4)).foldl (fun a h => stageRows a slot off d m h mir) r

@[simp] theorem scalars_size (r : Rows) (p m off slot : Nat) (mir : Bool) :
    (scalars r p m off slot mir).size = r.size := fold_size _ _ _ (fun _ _ => scalarRows_size ..)

@[simp] theorem triRows_size (r : Rows) (off d m slot : Nat) (mir : Bool) :
    (triRows r off d m slot mir).size = r.size := fold_size _ _ _ (fun _ _ => stageRows_size ..)

def r8Rows (r : Rows) (off slot : Nat) (mir : Bool) : Rows :=
  (pascalR8Steps mir).foldl (fun a st => r8StepRows a slot off st) r

@[simp] theorem r8Rows_size (r : Rows) (off slot : Nat) (mir : Bool) :
    (r8Rows r off slot mir).size = r.size := fold_size _ _ _ (fun _ _ => r8StepRows_size ..)

def primaryRows (r : Rows) (off p m slot : Nat) (mir : Bool) : Rows :=
  let d := fieldDegree p
  if d == 8 && m == 2 then r8Rows (scalars r p m off slot mir) off slot mir
  else triRows (scalars r p m off slot mir) off d m slot mir

@[simp] theorem primaryRows_size (r : Rows) (off p m slot : Nat) (mir : Bool) :
    (primaryRows r off p m slot mir).size = r.size := by unfold primaryRows; dsimp only; split <;> simp

theorem frame_primary (r : Rows) (p : Nat) (hp : UsedField p) (mir : Bool) (off m slot dim : Nat)
    (small : slot < 32) (endp : off+fieldDegree p*m ≤ r.size) (x : Nat → Bool) (ph : Bool) (tape : List Bool) :
    run (primary r.size off p m mir) tape (frame r x dim slot ph) = frame (primaryRows r off p m slot mir) x dim slot ph := by
  let d := fieldDegree p
  change off+d*m ≤ r.size at endp
  have scalar := run_parts (List.range m) (fun j => renameProgram (fieldPlace r.size (off+d*j)) (fieldCore p mir))
    (fun a j => scalarRows a p mir slot (off+d*j)) r.size x dim slot ph tape r rfl
    (fun _ _ => scalarRows_size ..) (by
      intro j hj a size tape
      have limit := Nat.mul_le_mul_left d (show j+1 ≤ m from List.mem_range.mp hj)
      rw [Nat.mul_succ] at limit
      rw [←size]
      exact frame_field a p hp mir _ _ _ small (by change off+d*j+d ≤ a.size; rw [size]; omega) x ph tape)
  unfold primary primaryRows; dsimp only
  rw [run_append,run_take,scalar]
  by_cases h82 : (fieldDegree p == 8 && m == 2) = true
  · have h82' := h82; simp only [Bool.and_eq_true, beq_iff_eq] at h82'
    have h16 : d * m = 16 := by change fieldDegree p * m = 16; rw [h82'.1, h82'.2]
    rw [if_pos h82, if_pos h82]
    unfold pascalR8 r8Rows
    apply run_parts (pascalR8Steps mir) (r8Step r.size off) (fun a st => r8StepRows a slot off st) r.size _ _ _ _ _ _
      (scalars_size ..) (fun _ _ => r8StepRows_size ..)
    intro st hst a size tape
    rw [←size]
    exact frame_r8Step a off st (List.all_eq_true.mp (Placement.pascalR8Steps_good mir) st hst)
      (by rw [size]; omega) x dim slot ph tape
  · rw [if_neg h82, if_neg h82]
    have shape : oriented mir (triangular r.size off d m) =
        (oriented mir (List.range 4)).flatMap (fun h => oriented mir (stage r.size off d m h)) := by
      cases mir <;> simp [oriented,triangular,List.reverse_flatMap,Function.comp_def]
    change run (oriented mir (triangular r.size off d m)) _ (frame (scalars r p m off slot mir) _ _ _ _) = _
    rw [shape]
    apply run_parts _ _ (fun a h => stageRows a slot off d m h mir) r.size _ _ _ _ _ _
      (scalars_size ..) (fun _ _ => stageRows_size ..)
    intro h _ a size tape
    rw [←size]
    exact frame_stage a off d m h mir (by rw [size]; exact endp) x dim slot ph tape

def componentRows (mir : Bool) (slot : Nat) : Nat → List (Nat × Nat) → Rows → Rows
  | _, [], r => r
  | off, (p,m)::ps, r => componentRows mir slot (off+fieldDegree p*m) ps (primaryRows r off p m slot mir)

@[simp] theorem componentRows_size (mir : Bool) (slot off : Nat) (parts : List (Nat × Nat)) (r : Rows) :
    (componentRows mir slot off parts r).size = r.size := by
  induction parts generalizing off r with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨p,m⟩ := pair
    exact (ih _ _).trans (primaryRows_size ..)

theorem frame_components (r : Rows) (mir : Bool) (off slot dim : Nat) (parts : List (Nat × Nat))
    (small : slot < 32) (endp : off+extent parts ≤ r.size) (fields : ∀ pair ∈ parts, UsedField pair.1)
    (x : Nat → Bool) (ph : Bool) (tape : List Bool) :
    run (components r.size mir off parts) tape (frame r x dim slot ph) =
      frame (componentRows mir slot off parts r) x dim slot ph := by
  induction parts generalizing off r tape with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨p,m⟩ := pair
    change off+(fieldDegree p*m+extent tail) ≤ r.size at endp
    rw [components,run_append,run_take,frame_primary r p (fields (p,m) (by simp)) mir off m slot dim small (by omega)]
    let new := primaryRows r off p m slot mir
    have eq : new.size = r.size := primaryRows_size ..
    rw [←eq]
    exact ih new _ (by omega) (fun a ha => fields a (List.mem_cons_of_mem _ ha)) _

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTComponents ====

-- ==== begin CRTCoordinates ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix

/-- Binary coefficient rows of the primary-component coordinates at every supported width. -/
def encoded : Nat → Rows
  | 31 => #[
      2147483647, 715827882, 1288490188, 143165576,
      1894838512, 547397792, 1086374080, 8421504,
      1363481681, 579479714, 340870420, 681740840,
      490370281, 659463482, 1318926964, 136978600,
      571115562, 176695840, 388914361, 777828722,
      1268199004, 1662567985, 623462994, 692736660,
      831283992, 151290433, 302580866, 605161732,
      1092653128, 37822608, 75645216]
  | 39 => #[
      549755813887, 183251937962, 329853488332, 36650387592,
      485078659312, 140133834912, 278111764672, 2155905152,
      87262827601, 174525655202, 296693613844, 43631413800,
      337645303017, 359289232698, 168822651508, 45234135208,
      11308533802, 146205583904, 324658945209, 99562076530,
      437207379548, 431556720017, 191383543474, 382767086948,
      215778360008, 258997787377, 517995574754, 486235335620,
      404376800632, 53202175537, 88670292562, 159606526612,
      301478994712, 77460701761, 154921403522, 309842807044,
      9682587720, 19365175440, 38730350880]
  | 46 => #[
      70368744177663, 46912496118442, 14073748835532, 9382499223688,
      53811392606448, 35874261737632, 827867578560, 551911719040,
      69273510805248, 46182340536832, 13197562137600, 8798374758400,
      52780584726528, 35187056484352, 3221274624, 2147516416,
      5584820966481, 11169641932962, 18988391286036, 37976782572072,
      43218598786281, 45989021785402, 21609299393140, 41556344986809,
      12743945795954, 55962544582236, 67501766014353, 8437720751794,
      16875441503588, 33750883007176, 54479027750449, 20429635406418,
      22699594896020, 27239513875224, 65188038776897, 15231265745090,
      30462531490180, 60925062980360, 51481381783056, 32594019388448,
      39659879301697, 8951014425730, 17902028851460, 4957484912712,
      9914969825424, 19829939650848]
  | 54 => #[
      18014398509481983, 12009599006321322, 3602879701896396, 2401919801264264,
      13775716507250928, 9183811004833952, 211934100111552, 141289400074368,
      4861028169225297, 9722056338450594, 5718856669676820, 11437713339353640,
      5531980644644073, 14893794043272506, 11773189577063028, 14326411413052601,
      10638424316623218, 16170404961267292, 14141250601547153, 6271255952563890,
      12542511905127780, 7070625300773576, 8486839496776433, 16973678993552866,
      15932959477623748, 13250619003129208, 1743328888014385, 2905548146690642,
      5229986664043156, 9878863698748184, 7242799944898625, 12048286520125634,
      6082174530769284, 12164349061538568, 6314299613595152, 12628599227190304,
      2291459692986945, 4582919385973890, 9165838771947780, 2538232275308616,
      5076464550617232, 10152929101234464, 10421829012605249, 13242154992098242,
      16626608015048388, 15238817520614792, 2605457253151312, 5210914506302624,
      9963426261843777, 10606933195047362, 3199467880612740, 15162689070839880,
      2490856565460944, 4981713130921888]
  | 61 => #[
      2305843009213693951, 768614336404564650, 922337203685477580, 614891469123651720,
      1220740416642543856, 45212608023797920, 54255129628557504, 36170086419038336,
      2234065794919104256, 720762860208171520, 864915432249805824, 576610288166537216,
      1153185391424106496, 175924544839680, 211109453807616, 140739635871744,
      1464027307437266001, 622211605660838050, 366006826859316500, 732013653718633000,
      708093522514441449, 1906405637538880826, 1506968265864067700, 1833780660870732985,
      1361718312527772018, 2069811835042213468, 2211897868758349201, 276487233594793650,
      552974467189587300, 1105948934379174600, 1395595524726889201, 485348040240084450,
      970696080480168900, 697797762363444600, 1785168781326730801, 669438292997524050,
      743820325552804500, 892584390663365400, 1685444194648706337, 1065045380083718722,
      787141276634511780, 1574282553269023560, 842722097324353168, 2114927425554290753,
      570494640314067138, 1140989280628134276, 2281978561256268552, 2258114113298843152,
      2210385217383992352, 1173227362809315905, 40611716404937858, 81223432809875716,
      1299574924958011464, 293306840702328976, 586613681404657952, 1379516115733236033,
      1544466028298066882, 1872109654491692740, 1438376299769691528, 1497800533540155984,
      689758057866618016]
  | 69 => #[
      590295810358705651711, 196765270119568550570, 236118324143482260684, 157412216095654840456,
      312509546660491227376, 11574427654092267680, 13889313184910721216, 9259542123273814144,
      18374966859414961920, 12249977906276641280, 14699973487531969536, 9799982325021313024,
      17294086455919964160, 11529390970613309440, 13835269164735971328, 9223512776490647552,
      93697747675985024081, 187395495351970048162, 318572342098349081876, 46848873837992512040,
      385783876061201331433, 539167826784329571642, 488039843209953491572, 529871829770806647993,
      469447849182907644274, 264935914885403323996, 463380499711497139601, 205496515053613555378,
      410993030107227110756, 231690249855748569800, 278096756630370163441, 556193513260740326882,
      522091216162775002052, 434196283494537907576, 57125401002455385649, 95209001670758976082,
      171376203007366156948, 323710605680580518680, 153871082802752507169, 307742165605505014338,
      166807837940020476324, 333615675880040952648, 76935541401376253584, 18255828490050148417,
      19017238714023618754, 38034477428047237508, 76068954856094475016, 152137909712188950032,
      304275819424377900064, 10396599399664091713, 20793198799328183426, 41586397598656366852,
      75086551219796217928, 150173102439592435856, 300346204879184871712, 15214574171015399745,
      26908739129648700354, 41071440811124489924, 82142881622248979848, 151377596132430262864,
      302755192264860525728, 364902440192748714241, 139509070026791776770, 279018140053583553540,
      249627424652000342280, 163175666630426434320, 45612805024093589280, 91225610048187178560,
      182451220096374357120]
  | 76 => #[
      75557863725914323419135, 50371909150609548946090, 60446290980731458735308, 40297527320487639156872,
      4444580219171430789360, 2963053479447620526240, 3555664175337144631488, 2370442783558096420992,
      70853872209904093167360, 47235914806602728778240, 56683097767923274533888, 37788731845282183022592,
      17294086455919964160, 11529390970613309440, 13835269164735971328, 9223512776490647552,
      5996655851263041541201, 11993311702526083082402, 20388629894294341240084, 40777259788588682480168,
      49380336135833770423529, 69013481828394185170234, 62469099930874046921332, 67823594210663250943161,
      60089324695412178467186, 33911797105331625471580, 72479469363473586648465, 9059933670434198331058,
      18119867340868396662116, 36239734681736793324232, 45730874154250705345265, 15903884582587087271394,
      31807769165174174542788, 22865437077125352672632, 58496410626514314905137, 21936153984942868089426,
      24373504427714297877140, 29248205313257157452568, 57276949433284498364481, 20679370601268721428674,
      41358741202537442857348, 7159618679160562295560, 14319237358321124591120, 28638474716642249182240,
      5323058892628014957121, 10646117785256029914242, 21292235570512059828484, 38444314224535663579208,
      1330764723157003739280, 2661529446314007478560, 21856159557443124513089, 65549743688945976040386,
      72647456114931919650500, 69737048503949515881864, 43242971752317942837840, 10928079778721562256544,
      73803199216923002093377, 4153068053707681120706, 8306136107415362241412, 57340313992731472443464,
      37340265735709331378128, 74680531471418662756256, 37198303566742610685889, 74396607133485221371778,
      73235350541056119324420, 70912837356197915229704, 66267810986481507040272, 56378083646328467052512,
      364902440192748714241, 729804880385497428482, 1459609760770994856964, 2610810666086822949128,
      4885542149500071648016, 9490345770763384016672, 18980691541526768033344, 37961383083053536066688]
  | 84 => #[
      19342813113834066795298815, 12895208742556044530199210, 15474250491067253436239052, 10316166994044835624159368,
      1137812536107886282076400, 758541690738590854717600, 910250028886309025661120, 606833352590872683774080,
      1204221828098618944454400, 802814552065745962969600, 963377462478895155563520, 642251641652596770375680,
      1133385249975170771251200, 755590166650113847500800, 906708199980136617000960, 604472133320091078000640,
      5219489252939351357461585, 10438978505878702714923170, 6140575591693354538190100, 12281151183386709076380200,
      15992089582303756011861225, 8833725674034455701790010, 17667451348068911403580020, 8681420058964896120724665,
      17362840117929792241449330, 14012116586399481458011740, 15184052214546338270475665, 6733709805276808982634162,
      13467419610553617965268324, 7592026107273169135237832, 9112674521263969515641585, 18225349042527939031283170,
      17107884971221811267267524, 14227743817549018155470200, 1871885140048458076964401, 3119808566747430128274002,
      5615655420145374230893204, 10607349126941262436131608, 3079591498469857435129921, 9163180881436901855144130,
      18326361762873803710288260, 17309910411913540625277704, 15277007709993014455256592, 11211202306151962115214368,
      2725406153025543658046017, 5450812306051087316092034, 10901624612102174632184068, 340675769128192957255752,
      681351538256385914511504, 1362703076512771829023008, 12564461538059220812089665, 17746089855552897656118210,
      8761801784595079112851140, 17523603569190158225702280, 7976818662973321901847120, 15953637325946643803694240,
      12843082168896443659927361, 18893618999532288535904706, 18444424885230510276510596, 4968601456177162494687304,
      3210770542224110914981840, 6421541084448221829963680, 4041765081040201751900097, 8083530162080403503800194,
      16167060324160807007600388, 12991307534487547219901960, 6639801955141027644505104, 11692289097437134273599456,
      9142866413275825882429697, 18285732826551651764859394, 17228652539269236734419972, 13376352690152922068136200,
      2044947862749186803964688, 5978561580117994934128416, 11957123160235989868256832, 4571433206637912941214848,
      5667325739565347537898241, 16699153157617791093038338, 18210764686674579750973700, 17078716259515092706648584,
      10809579349834194632085264, 2276345585834322468871712, 9010491567862964472084288, 12505069426699707166598528]
  | 91 => #[
      2475880078570760549798248447, 825293359523586849932749482, 1485528047142456329878949068, 165058671904717369986549896,
      291280009243618888211558640, 194186672829079258807705760, 233024007394895110569246912, 155349338263263407046164608,
      2167599290577514100017921792, 619772834194755883412531712, 1238903416747859170054687744, 642251641652596770375680,
      1133385249975170771251200, 755590166650113847500800, 906708199980136617000960, 604472133320091078000640,
      1571987351473498761776665681, 668094624376236973755082914, 392996837868374690444166420, 785993675736749380888332840,
      2046987466534880769518236905, 1130716886276410329829121338, 2261433772552820659658242676, 1111221767547506703452757177,
      2222443535095013406905514354, 1793550923059133626625502812, 2375007252102302487296931217, 296875906512787810912116402,
      593751813025575621824232804, 1187503626051151243648465608, 1498509284286487112753650417, 521138490002213675709052386,
      1042276980004427351418104772, 749254642143243556376825208, 1916810383409621070811547185, 718803893778607901554330194,
      798670993087342112838144660, 958405191704810535405773592, 1143583769053865414048075041, 2287167538107730828096150082,
      1690373020238458520379914660, 904865961906156490961580872, 1809731923812312981923161744, 912191807848670996814174273,
      2194901062744686449723910338, 1913922046918612349649572228, 1351964015266464149500896008, 228047951962167749203543568,
      456095903924335498407087136, 1395407950349078352919560769, 314935822127396156040873090, 629871644254792312081746180,
      174425993793634794114945096, 348851987587269588229890192, 697703975174539176459780384, 1269847313937273562506512705,
      1294371755368601306145840066, 1324073093525311621193170628, 172266108479862692588092808, 1555401867769698665525752400,
      634923656968636781253256352, 477070596900914046747098945, 811948956666729027143156162, 1623897913333458054286312324,
      1223565827627723370598512712, 1976177708153298924035461072, 1476475337735837298272673696, 1145267738797250142674530241,
      2290535477594500285349060482, 2105190876618240020899872516, 1734501674665719492001496584, 993123270760678434204744720,
      1810573908684005346236389344, 431935398335134046939157441, 1141047139831027236792677442, 1928225505167509614648228676,
      1380570931764258679498208904, 285261784957756809198169360, 215967699167567023469578720, 1499752182941225352806080961,
      523624287311690155813913474, 2392253503171269575723820740, 1137854872178904964607405128, 2275709744357809929214810256,
      749876091470612676403040480, 2278104436250938967487729345, 585921148211486517113738050, 1171842296422973034227476100,
      2343684592845946068454952200, 146480287052871629278434512, 2376992257410849758642988896]
  | 99 => #[
      633825300114114700748351602687, 211275100038038233582783867562, 380295180068468820449010961612, 42255020007607646716556773512,
      74567682366366435382159012080, 49711788244244290254772674720, 59654145893093148305727209664, 39769430595395432203818139776,
      78919881726271091143763623680, 52613254484180727429175749120, 63135905381016872915010898944, 42090603587344581943340599296,
      74277535742372791664718704640, 49518357161581861109812469760, 59422028593898233331774963712, 39614685729265488887849975808,
      100607190494303920753706603601, 201214380988607841507413207202, 342064447680633330562602452244, 50303595247151960376853301800,
      578927045773522088872510125289, 144731761443380522218127531322, 289463522886761044436255062644, 459149036303138208416128720057,
      284472772492161716083905837426, 229574518151569104208064360028, 497551022966254412446946620817, 220650202899310476742956228274,
      441300405798620953485912456548, 248775511483127206223473310408, 298604118712777753088543464177, 597208237425555506177086928354,
      560591174736996311605822254020, 466214709413446226918447533432, 61337932269107874265969509937, 102229887115179790443282516562,
      184013796807323622797908529812, 347581616191611287507160556312, 330435634218965018537215118625, 27045968323815336326078634562,
      358217104334427977691327691172, 82608908554741254634303779656, 165217817109482509268607559312, 387149484064887316765340932161,
      408239233948349416616636655810, 182653167782584132484921708932, 365306335565168264969843417864, 96787371016221829191335233040,
      193574742032443658382670466080, 80623570464613415946463511105, 161247140929226831892927022210, 322494281858453663785854044420,
      89306108822341014586851889224, 178612217644682029173703778448, 357224435289364058347407556896, 362748338785268313833050786113,
      454380426133817781919225306050, 627721732971927730720150027972, 621618165829740760691948453256, 249143409724845753645350597200,
      498286819449691507290701194400, 592212409375312685448528478017, 122130072806633995967257330114, 244260145613267991934514660228,
      105210529127599666462124947528, 464965752400885521736307920848, 296106204687656342724264239008, 186836273631604291377543163841,
      373672547263208582755086327682, 113519794412302464761821052676, 227039588824604929523642105352, 454079177649209859047284210704,
      93418136815802145688771581920, 168791780741146851433220051905, 506220583168266179395635360834, 546621842790734830570262887236,
      459418385467354960392174171784, 285011470820595220035996740880, 401308540427630776090785827296, 531338088997083983009631248833,
      428850877880053265270910894978, 349015464503077746547478603460, 513645031136326338772844833864, 393464762158537976797338065040,
      582581694555599341878991425760, 455364158814700119580567195329, 535376018119495765273535402818, 436926736124876829798719202948,
      240028172135638958849086803208, 292300329558402616505471751376, 227682079407350059790283597664, 564548486406774349313473673473,
      495271672699433997878595744258, 356718045284753295008839885828, 485614699575494399818044911880, 268035406266261412769259658000,
      149796723315111131257728159520, 299593446630222262515456319040, 599186893260444525030912638080]
  | 106 => #[
      81129638414606681695789005144063, 54086425609737787797192670096042, 16225927682921336339157801028812, 10817285121947557559438534019208,
      19089326685789807457832707092720, 12726217790526538305221804728480, 15271461348631845966266165674176, 10180974232421230644177443782784,
      60926148692681282362985517481728, 40617432461787521575323678321152, 63135905381016872915010898944, 42090603587344581943340599296,
      74277535742372791664718704640, 49518357161581861109812469760, 59422028593898233331774963712, 39614685729265488887849975808,
      6438860191635450928237222630481, 12877720383270901856474445260962, 21892124651560533156006556943636, 43784249303121066312013113887272,
      74102661859010827375681296037097, 18525665464752706843920324009274, 37051330929505413687840648018548, 58771076646801690677264476167353,
      36412514878996699658739947190642, 29385538323400845338632238083676, 77824237636888247903745842148753, 9728029704611030987968230268594,
      19456059409222061975936460537188, 38912118818444123951872921074376, 49103152227499609710711616871153, 17076666040392537725634228598242,
      34153332080785075451268457196484, 24551576113749804855355808435576, 62810042643566463248352778176049, 23553765991337423718132291816018,
      26170851101486026353480324240020, 31405021321783231624176389088024, 41238916887190102132756874560032, 3172224375937700164058221120002,
      793056093984425041014555280000, 10785562878188180557797951808008, 33346065089998851755679624271937, 59353992144561016586213335705794,
      37578345874515351476637666267524, 75156691749030702953275332535048, 69183745083454724210761659926032, 57237851752302766725734314708000,
      41279268077882068964589317685825, 1428897741157456233389630227586, 2857795482314912466779260455172, 45724727717038599468468167282760,
      10319817019470517241147329421456, 20639634038941034482294658842912, 66914404850767311892409969068353, 37216247832752470425323618261954,
      18374830136167139351673994903236, 36749660272334278703347989806472, 16728601212691827973102492267088, 33457202425383655946204984534176,
      57636489419645635752800172719937, 70476738385473365779034285228482, 59823838356340049862279565312900, 64755391140767299142793988421704,
      14409122354911408938200043179984, 28818244709822817876400086359968, 9060390475229210101854465601473, 18120780950458420203708931202946,
      36241561900916840407417862405892, 72483123801833680814835724811784, 63836609189060679933882444479504, 45095014444917945898821735372768,
      78129303694777255043480467182529, 8745949484651757289124206195778, 61393850653745746102412016745284, 41658062892884810509035028346504,
      2186487371162939322281051548944, 79629471054691968369634736163296, 39194681395958080728659079012801, 78389362791916161457318158025602,
      47252087672947565601925497202372, 25866657035700914368706908941384, 51733314071401828737413817882768, 19597340697979040364329539506400,
      5525966559727617725567380016833, 16381008520972363283982325470018, 32762017041944726567964650940036, 65524034083889453135929301880072,
      44660071337546431668890083939536, 2762983279863808862783690008416, 6268976187433806656048638097665, 12537952374867613312097276195330,
      25075904749735226624194552390660, 44853385707563523452202657100040, 2803336606722720215762666068752, 783622023429225832006079762208,
      1567244046858451664012159524416, 3134488093716903328024319048832, 8348731320705685641467617561345, 14865297404957573129113753214210,
      22669330952663480941066876154116, 45338661905326961882133752308232, 1416833184541467558816679759632, 2833666369082935117633359519264,
      3716324351239393282278438303552, 4174365660352842820733808780672]
  | 113 => #[
      10384593717069655257060992658440191, 3461531239023218419020330886146730, 4153837486827862102824397063376076, 2769224991218574735216264708917384,
      4886867631562190709205173015736560, 3257911754374793806136782010491040, 3909494105249752567364138412589248, 2606329403499835044909425608392832,
      5172093368812902229197692841557760, 3448062245875268152798461894371840, 4137674695050321783358154273246208, 2758449796700214522238769515497472,
      4867852582412143274539005027348480, 3245235054941428849692670018232320, 3894282065929714619631204021878784, 2596188043953143079754136014585856,
      5604383910799496487937678577570897, 824174104529337718814364496701602, 6593392836234701750514915973612820, 2802191955399748243968839288785448,
      9485140717953385904087205892748521, 2371285179488346476021801473187130, 4742570358976692952043602946374260, 7522697810790616406689852949421241,
      4660801904511577556318713240402290, 3761348905395308203344926474710620, 5919158203488569330000554212521361, 7230265848604605701913189688090290,
      4075937980139556146765386717740388, 8151875960279112293530773435480776, 9784659761980301413205392234158833, 9184725806890947569349791809877474,
      7984857896712239881638590961314756, 4892329880990150706602696117079416, 2009921364594126823947288901633585, 3349868940990211373245481502722642,
      6029764093782380471841866704900756, 1004960682297063411973644450816792, 5063326932945767194596369817390369, 10126653865891534389192739634780738,
      5825212725153048527855042556393892, 1265831733236441798649092454347592, 2531663466472883597298184908695184, 4495476177893366345024074907195457,
      7279891811044555687511434793527490, 4175189905019456117961876928614788, 8350379810038912235923753857229576, 6316165903008169214786515056018960,
      2247738088946683172512037453597728, 365797821736308795747745338262081, 731595643472617591495490676524162, 1463191286945235182990981353048324,
      2641873156984452413733716331892808, 5283746313968904827467432663785616, 182898910868154397873872669131040, 2663062834118181126157658133678401,
      7906791174049600594916857117236162, 7969079394767621945538996499021508, 5553565072465588634017000339602824, 3261914137796959095804662698029648,
      6523828275593918191609325396059296, 8819637438197167258898012728278849, 4370347574359627495655851557863874, 8740695148719254991311703115727748,
      4851404057602561519194345291921480, 2204909359549291814724503182069712, 4409818719098583629449006364139424, 4957968333766236793544983779389377,
      9915936667532473587089967558778754, 9447279617995291917118942459117316, 8509965518920928577176892259794440, 6635337320772201897292791861148688,
      2478984166883118396772491889694688, 8759000614057692196492904017597377, 4876524254361052659036464514839618, 1602856980531272698322403114482500,
      3205713961062545396644806228965000, 6411427922125090793289612457930000, 9571797165563673726776948338018784, 5718269370418425799433889439097281,
      1051945023767196341806786219754370, 7754567737060582326701880985888452, 9842552905203109399559176531373128, 9300512093336563542057360404306064,
      2859134685209212899716944719548640, 2114896565339501341816081513762497, 3748344375592879721290276562096962, 7496688751185759442580553124193924,
      4608783785301863628100113589947656, 8725531381700461373118313634354384, 6249745141204578299438537086101344, 7840670289142395006646133914677953,
      5296746861215134756231275170915714, 7968420810352684602377159744289220, 5552247903635713947693326830138248, 8476570679983287273562782079833552,
      3920335144571197503323066957338976, 1304343190821140713788672720402689, 2608686381642281427577345440805378, 5217372763284562855154690881610756,
      1342927600341270430584826739405064, 3978155618922450123309423918127888, 9249562401288590939151952666185504, 8114531085507526621242912673930816,
      5844468453945397985424832689421440, 3902571375221826407039339864476417, 6505236370573492108792234164739330, 1320743545586370388073690958459140,
      2641487091172740776147381916918280, 9169065974035096499182974261038864, 7953538231000537741304955863637536, 9414754380445614469993803035014976,
      7143582546145740832050166261458304]
  | 120 => #[
      1329227995784915872903807060280344575, 886151997189943915269204706853563050, 1063382396627932698323045648224275660, 708921597751955132215363765482850440,
      1251038113679920821556524292028559600, 834025409119947214371016194685706400, 1000830490943936657245219433622847680, 667220327295957771496812955748565120,
      5172093368812902229197692841557760, 3448062245875268152798461894371840, 4137674695050321783358154273246208, 2758449796700214522238769515497472,
      4867852582412143274539005027348480, 3245235054941428849692670018232320, 3894282065929714619631204021878784, 2596188043953143079754136014585856,
      358680570291167775228011428964537425, 717361140582335550456022857929074850, 421977141519020912032954622311220500, 843954283038041824065909244622441000,
      1214098011898033395723162354271810793, 303524502974508348930790588567952698, 607049005949016697861581177135905396, 962905319781198900056301177525918905,
      596582643777481927208795294771493234, 481452659890599450028150588762959452, 1220916623100638234406136695250023825, 318768077360694263413742969441296050,
      637536154721388526827485938882592100, 1275072309442777053654971877765184200, 279784096405791338096791201353603825, 559568192811582676193582402707207650,
      1119136385623165352387164805414415300, 804506046095353605500299130816974200, 728931481559469994818216774992447025, 771809804004144700395758938227296850,
      857566448893494111550843264696996500, 1029079738672192933861011917636395800, 1126599448376468534957183576928931105, 923970900968021197010560093577517634,
      971592428412630987434527359791331748, 613956861040346101965247659302318920, 1227913722080692203930495318604637840, 1077682077484572405753526399780286113,
      826136159184228938603245739280227650, 323044322583542004302684418280110724, 934034517263601037890285130085243816, 538841038742286202876763199890143056,
      326520506495135608519623010384549281, 348692360470212382498957038271938274, 958892478914940851698766760405985380, 413937125570012870355857517666223464,
      827874251140025740711715035332446928, 755430721726354043237432115916958945, 932152003508933833822027986723681570, 1279593496750418118018584676085761700,
      1229958997715920363133362291891178824, 377715360863177021618716057958479472, 897570535845883718452269443533051969, 1274200325293542497048952539123230914,
      1219172654802169121194098017966117252, 1109117313819422369484388975651889928, 889006631853928866064970891023435280, 448785267922941859226134721766525984,
      187288484728990103422845613190185537, 374576969457980206845691226380371074, 749153938915960413691382452760742148, 23411060591123762927855701648773192,
      46822121182247525855711403297546384, 93644242364495051711422806595092768, 760738404180203014891610122199812417, 952904819427388228987467189035293634,
      1316427887745544184335224071462485700, 1303627779706172495766641082644626824, 522491599991279721948854295620039248, 1044983199982559443897708591240078496,
      756510385067212345767289484135972673, 928599188393558945374084198159040962, 527970381002202017844361336037737348, 472158121325737048086939014921730120,
      189127596266803086441822371033993168, 378255192533606172883644742067986336, 108803905504462789364154910363791297, 217607811008925578728309820727582594,
      435215622017851157456619641455165188, 870431244035702314913239282910330376, 411634492286488756922671505540316176, 719015950644689331133980985322067936,
      517604092750470799792481544281166785, 856413209054072783738037862506935362, 219679325038994033096603248941726532, 439358650077988066193206497883453064,
      878717300155976132386412995766906128, 258802046375235399896240772140583392, 774178204433572914821947346163671489, 219128413082229956740087632046998402,
      1004675564575747487004557176196146884, 124073083792969317227230095774215240, 248146167585938634454460191548430480, 1051703100109244393862877203222008032,
      220191364623802261740096927341006529, 657977748550981160916132814043829058, 1315955497101962321832265628087658116, 1302682998419008770760724195894971656,
      1161415433976432194906888498721215696, 774709680204359067321951993810675552, 527070356142625157859695766836687553, 1054140712285250315719391533673375106,
      1264504260575780970706757271415552452, 1199780525366646068509707482550760328, 891167036630903984123747158047249872, 263535178071312578929847883418343776,
      821687246839323906021607092737177857, 314146497893731939139407125194011138, 628292995787463878278814250388022276, 562110988322102654311878430295175432,
      367438935716360384120444166963534608, 102710905854915488252700886592147232, 205421811709830976505401773184294464, 410843623419661953010803546368588928]
  | 128 => #[
      340282366920938463463374607431768211455, 226854911280625642308916404954512140970, 272225893536750770770699685945414569164, 181483929024500513847133123963609712776,
      320265757102059730318470218759311257840, 213510504734706486878980145839540838560, 256212605681647784254776175007449006272, 170808403787765189503184116671632670848,
      338958311018522360492699998064329424640, 225972207345681573661799998709552949760, 271166648814817888394159998451463539712, 180777765876545258929439998967642359808,
      319019586840962221640188233472310046720, 212679724560641481093458822314873364480, 255215669472769777312150586777848037376, 170143779648513184874767057851898691584,
      108026148228869353480436383311672448081, 216052296457738706960872766623344896162, 27006537057217338370109095827918112020, 54013074114434676740218191655836224040,
      155404545522948274652564781346791781609, 208992319841206300394828499052582051130, 77702272761474137326282390673395890804, 123251880931993459207206550723317619897,
      246503761863986918414413101446635239794, 61625940465996729603603275361658809948, 193958976011913439805458160435899987345, 236921351327075719640291399699342630578,
      133560335733212975817208191966917049700, 267120671466425951634416383933834099400, 320623731080570516707914292728916646641, 300965095240202569952453978026065081826,
      261647823559466676441533348620361952196, 160311865540285258353957146364458323320, 65861103275020347767104762728729331249, 109768505458367246278507937881215552082,
      197583309825061043301314288186187993748, 32930551637510173883552381364364665624, 29040387359859701865937131842816167201, 58080774719719403731874263685632334402,
      88700640150217078599085793338294073764, 177401280300434157198171586676588147528, 14520193679929850932968565921408083600, 25003786001613058118022053484826488481,
      50007572003226116236044106969652976962, 100015144006452232472088213939305953924, 176392129960872496261192817087090727848, 12501893000806529059011026742413244240,
      33557220401118032431114799517393163681, 57505496179221594917362660630326755042, 105967904145923294811099524522553206884, 178530488560748739839466003595232396648,
      16778610200559016215557399758696581840, 35315358612134166738736415683205917921, 63405867805399979860300959819899876642, 92996325205909613348381271835429537444,
      185992650411819226696762543670859074888, 17657679306067083369368207841602958960, 168380298004745283704331959038856468545, 175403067773117521847447677435848370370,
      10523768625296580231520747439928529284, 21047537250593160463041494879857058568, 42095074501186320926082989759714117136, 84190149002372641852165979519428234272,
      95891704181242932952496953953374995009, 191783408362485865904993907906749990018, 43284449804033268346613208381731768580, 11986463022655366619062119244171874376,
      23972926045310733238124238488343748752, 47945852090621466476248476976687497504, 140329677961596369669791351451635992897, 248189312035421740589095580401179384770,
      38534811769723188625641821759312133828, 77069623539446377251283643518624267656, 35082419490399092417447837862908998224, 70164838980798184834895675725817996448,
      149630045912977790110993680235534565185, 193666658577206360516426107938809004482, 47050950233474257569477608445849797508, 72250469893711194184892520270060337224,
      37407511478244447527748420058883641296, 74815022956488895055496840117767282592, 89167079623093826273919227949146877889, 178334159246187652547838455898293755778,
      16385951571436841632302304364819300100, 32771903142873683264604608729638600200, 65543806285747366529209217459277200400, 44583539811546913136959613974573438944,
      146732683629091216819211258175119070145, 237458996458769098160615694592408269890, 14841187278673068635038480912025516868, 29682374557346137270076961824051033736,
      59364749114692274540153923648102067472, 73366341814545608409605629087559535072, 127050837804000580840683618072796406209, 254101675608001161681367236145592812418,
      44869199425477971292830190165447517892, 37342456965770613758533827783623863368, 74684913931541227517067655567247726736, 63525418902000290420341809036398203104,
      161056778854598622883100751221262700225, 185420669162654287494545314193011725122, 30558971404370111525716020954255238788, 61117942808740223051432041908510477576,
      46355167290663571873636328548252931280, 80528389427299311441550375610631350112, 109523766010505726735971874709824942785, 219047532021011453471943749419649885570,
      37153660146768509539109547898984856004, 74307320293537019078219095797969712008, 81974074779510772231255977835148269008, 54761883005252863367985937354912471392,
      170962870707308555637708910808621283585, 1643374493678647812043214185474355714, 3286748987357295624086428370948711428, 176020206431930997877614410387300659464,
      181142446362464919099038204365090396944, 191511542298882801186400917566961766176, 42740717676827138909427227702155320896, 85481435353654277818854455404310641792,
      171235468372136767360085747284884802305, 172089607721931830756866501577177160962, 173112498007096739505594821307156459780, 5942629093255015547815035182544708104,
      180960714585912777950786980047581384464, 21639062250887092438199352663394557472, 213163585390952189420903929110178395968, 255758917646537615411730177358326506880]
  | _ => #[]

def clipShift (dim k a : Nat) : Nat := (a >>> k) &&& (2^dim-1)

theorem clip_zero (dim k : Nat) : clipShift dim k 0 = 0 := by simp [clipShift]

theorem clip_xor (dim k a b : Nat) : clipShift dim k (a ^^^ b) = clipShift dim k a ^^^ clipShift dim k b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [clipShift,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_xor]
  cases (2^dim-1).testBit i <;> simp

def plain (n dim k : Nat) : Rows := (units n).map (clipShift dim k)
def coded (n dim k : Nat) : Rows := (encoded n).map (clipShift dim k)

@[simp] theorem plain_size (n dim k : Nat) : (plain n dim k).size = n := by simp [plain,units]

theorem encode_of_receipt (n dim k : Nat) (h : applyOps (basisNetwork n) (units n) = encoded n) :
    applyOps (basisNetwork n) (plain n dim k) = coded n dim k := by
  rw [plain,apply_map _ _ (clip_zero dim k) (clip_xor dim k),h,coded]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTCoordinates ====

-- ==== begin CRTWindowRun ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix Field

def entryShift (mir : Bool) (slot : Nat) := if mir then slot-1 else 0
def exitShift (mir : Bool) (slot : Nat) := if mir then 0 else slot-1

def CoordinatesOK (n : Nat) : Prop := applyOps (basisNetwork n) (units n) = encoded n

def ActionOK (n slot : Nat) (mir : Bool) : Prop :=
  componentRows mir slot 0 (schedule n) (coded n (n-(slot-1)) (entryShift mir slot)) =
    coded n (n-(slot-1)) (exitShift mir slot)

theorem logical_action (n : Nat) (hn : UsedWidth n) (mir : Bool) (slot : Nat) (small : slot < 32)
    (basisOK : CoordinatesOK n) (action : ActionOK n slot mir)
    (x : Nat → Bool) (ph : Bool) (tape : List Bool) :
    run (logical n mir) tape (frame (plain n (n-(slot-1)) (entryShift mir slot)) x (n-(slot-1)) slot ph) =
      frame (plain n (n-(slot-1)) (exitShift mir slot)) x (n-(slot-1)) slot ph := by
  let dim := n - (slot - 1)
  let ops := basisNetwork n
  have bounds : ∀ o ∈ ops, o.1 < n ∧ o.2 < n := fun o ho => ⟨(basis_pairs n hn o ho).1,(basis_pairs n hn o ho).2.1⟩
  have apart : ∀ o ∈ ops, o.1 ≠ o.2 := fun o ho => (basis_pairs n hn o ho).2.2
  have size (k : Nat) : (coded n dim k).size = n := by rw [←encode_of_receipt n dim k basisOK,applyOps_size,plain_size]
  have fwd (k : Nat) (m : List Bool) : run (cnotProgram ops) m (frame (plain n dim k) x dim slot ph) =
      frame (coded n dim k) x dim slot ph := by
    have step := run_ops ops (plain n dim k) x dim (flags n slot) ph m (by simpa only [plain_size] using bounds)
    rw [show applyOps ops (plain n dim k) = coded n dim k from encode_of_receipt n dim k basisOK] at step
    simpa only [frame,plain_size,size] using step
  have inv (k : Nat) (m : List Bool) : run (cnotProgram ops).reverse m (frame (coded n dim k) x dim slot ph) =
      frame (plain n dim k) x dim slot ph := by
    have hr := reverse_cnots ops apart (frame (plain n dim k) x dim slot ph) [] m
    have rev : cnotProgram ops.reverse = (cnotProgram ops).reverse := List.map_reverse
    rw [rev,fwd] at hr
    exact hr
  have c := frame_components (coded n dim (entryShift mir slot)) mir 0 slot dim (schedule n) small
    (by rw [Placement.schedule_extent n hn,size]; omega) (schedule_fields n hn) x ph
  change run (cnotProgram ops ++ components n mir 0 (schedule n) ++ (cnotProgram ops).reverse) _ _ = _
  rw [run_append,run_take,run_append,run_take,fwd]
  simp only [size] at c
  rw [c,show componentRows mir slot 0 (schedule n) (coded n dim (entryShift mir slot)) = _ from action,inv]

theorem rowValue_congr (x : Nat → Bool) (d a b : Nat) (eq : ∀ i < d, a.testBit i = b.testBit i) :
    rowValue x a d = rowValue x b d := by
  induction d with
  | zero => rfl
  | succ w ih => rw [rowValue,rowValue,eq w (by omega),ih (fun i hi => eq i (by omega))]

theorem plain_bits (n dim k v q : Nat) (small : v < 2^dim) (hq : q < n) :
    rowValue v.testBit (Matrix.read (plain n dim k) q) dim = (v <<< k).testBit q := by
  have rd : Matrix.read (plain n dim k) q = clipShift dim k (2^q) := by
    simp [Matrix.read,plain,units,hq]
  rw [rd]
  by_cases fits : k ≤ q
  · have equal := rowValue_congr v.testBit dim (clipShift dim k (2^q)) (2^(q-k)) (by
      intro i hi
      simp only [clipShift,Nat.testBit_and,Nat.testBit_two_pow_sub_one,Nat.testBit_shiftRight,
        Nat.testBit_two_pow,hi,decide_true,Bool.and_true]
      exact decide_eq_decide.mpr (by omega))
    rw [equal,value_unit,Nat.testBit_shiftLeft]
    by_cases bound : q-k < dim
    · simp [fits,bound]
    · have high := Nat.testBit_lt_two_pow (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : dim ≤ q-k)))
      simp [fits,bound,high]
  · have equal := rowValue_congr v.testBit dim (clipShift dim k (2^q)) 0 (by
      intro i _
      simp [clipShift,Nat.testBit_shiftRight,show q ≠ k+i by omega])
    rw [equal,rowValue_zero,Nat.testBit_shiftLeft]
    simp [fits]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTWindowRun ====

-- ==== begin CRTBarrelRun ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Placement Matrix Partial

/-- Slot zero has no tag; slot k+1 selects k. The mirror enters on the forward image. -/
theorem barrel_result_of_matrix (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool)
    (slot : Fin 17) (v : Nat) (s : State) (tape : List Bool)
    (basisOK : CoordinatesOK (barrelWidth (start j)))
    (action : ActionOK (barrelWidth (start j)) slot.val mir)
    (small : v < 2^(barrelWidth (start j) - (slot.val - 1)))
    (input : HighBankBarrel.holds (Shadow7.bankW (start j)) (barrelWidth (start j))
      (v <<< entryShift mir slot.val) s)
    (tag : ∀ k : Fin 16, s.basis (tagsP.getD k.val 1560) = decide (slot.val = k.val+1))
    (scratch : ∀ k < 10, s.basis (Shadow7.poolW (start j) (17+k)) = false) :
    HighBankBarrel.Result (Shadow7.bankW (start j)) (barrelWidth (start j))
      (v <<< exitShift mir slot.val) s (run (barrel (start j) mir) tape s) := by
  let n := barrelWidth (start j)
  let dim := n - (slot.val - 1)
  let P := logical n mir
  let f := place (start j)
  let S := Finset.range (n+26)
  let before := entryShift mir slot.val
  let after := exitShift mir slot.val
  have sv : v < 2^dim := small
  have scope : wires P ⊆ S := fun _ hw => Finset.mem_range.mpr (support (logical_fits _ (usedWidth j lo hi) _) _ hw)
  have inj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b :=
    fun a ha b hb => place_inj j lo hi a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb)
  have bank (k i : Nat) (ik : i < n) :
      (frame (plain n dim k) v.testBit dim slot.val s.phase).basis i = (v <<< k).testBit i := by
    simpa only [frame,Matrix.basis,plain_size,if_pos ik] using plain_bits n dim k v i sv ik
  have placed (q : Nat) (hq : q < n) : f q = Shadow7.bankW (start j) q := by simp [f,place,n] at hq ⊢; simp [hq]
  have other (k q : Nat) (qn : n ≤ q) (high : q < n+26) :
      (frame (plain n dim k) v.testBit dim slot.val s.phase).basis q = s.basis (f q) := by
    have outside : ¬q<n := Nat.not_lt.mpr qn
    simp only [frame,Matrix.basis,plain_size,if_neg outside]
    change flags n slot.val q = s.basis (if q<n then Shadow7.bankW (start j) q else if q<n+16 then
      tagsP.getD (q-n) 1560 else Shadow7.poolW (start j) (17+(q-n-16)%10))
    rw [if_neg outside]
    by_cases mid : q < n+16
    · have k16 : q-n < 16 := by omega
      simpa [flags,qn,mid] using (tag ⟨q-n,k16⟩).symm
    · have pos : q-n-16 < 10 := by omega
      have val := scratch (q-n-16) pos
      simpa [flags,mid,Nat.mod_eq_of_lt pos] using val.symm
  have result := run_rename_pool f S inj P scope tape
    (frame (plain n dim before) v.testBit dim slot.val s.phase) s rfl (by
       intro q hq
       by_cases low : q<n
       · rw [bank before q low,placed q low]; exact (input q low).symm
       · exact other before q (Nat.le_of_not_lt low) (Finset.mem_range.mp hq))
  have shift := logical_action n (usedWidth j lo hi) mir slot.val
    (by have := slot.isLt; omega) basisOK action v.testBit s.phase tape
  change run P tape (frame (plain n dim before) _ _ _ _) = frame (plain n dim after) _ _ _ _ at shift
  rw [shift] at result
  change HighBankBarrel.Result (Shadow7.bankW (start j)) n (v <<< after) s (run (renameProgram f P) tape s)
  refine ⟨?_,result.1,?_⟩
  · intro i bound
    have hi : i ∈ S := Finset.mem_range.mpr (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))
    have bit := (result.2 i hi).trans (bank after i bound)
    rwa [placed i bound] at bit
  · intro q free
    by_cases hit : q ∈ S.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hit
      have above : n ≤ a := by
        by_contra! low
        exact free a low (placed a low)
      change (run (renameProgram f P) tape s).basis (f a) = s.basis (f a)
      exact Eq.trans (result.2 a ha) (other after a above (Finset.mem_range.mp ha))
    · exact run_rename_pool_outside f S P scope tape s q hit

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrelRun ====

-- ==== begin CRTPackedData ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

def width : Nat := 144

def basisWord : Nat → Nat
  | 31 => 2129917273750201232991211575846355010352118899165478610449818878348517044510003826965075644763265078148572651909240140854801888604854550992569324044045825750565988086242202115456114212965290991073208958104977242667547986434596779022612250648266567767430958948155645128552884511382990138546233188059544412823976300561786153659888213157868845088933840722810352373002937654852545956256042778481602228885971275736835716679977321183366054218054075987450923364894472751615259908089865414997210598078504154204801934428862256403026396313434970980482927202470123006122760682390694216098144745740493369391235123684225365225448045412984041273698149595121222811691500111803769188439975587172239898061084373774735080749968618857936300035536088972417070439354738935243194020912349428494117265626324195100384763007167029410603810198725060069085571460962684043620387279253939299264194634433021664154120576781132584241145339756801771581400711239757557533386928421708627512017816950701806602176616003958287329743713461094981632420276286936764228047007221862182419216806323590730687288906971560242786840932837545546070729178950842873180770909751164050464319897292740882558547978332047679856915209044103965642496296463113214705210536078189119465721198541588167669317935987551919679137250386797009721706134861870368323980903841791
  | 39 => 66709502961343665485124629215248935765392639528500155646844127244492998350538572766046356857449067304872836238252796773138780444129786071689512818182131730933027768326575717269188621301515539964451105564613762196265727761116008466388638844610652912095229049894816787100453988072199025224635190920271817965253908266454425956623213699094116827454881383524482795434215401303370001923461081188238067165977429579838980049692184386216070054445924665411315282288931951119430226325609872634361487983629896776944966596226052857852297149947607638252656048616905674150432145009784855058024737558049313927680837779943272135680842902899272895311965364061287496389444622402285254002395268421458080915869182622387087835953513079581440750422765493227420598711222435061402935139260829378505752913205148107613297985075314810529899357475985827791215947090739791133167575878440801961682506197352627700737088808540162643009176304564533907131704220356718303705246923406308633642034531531966395780966950028480965489876741436269149118039485975410301162025405067219542573063806828999741914559122128844968705984084575829060474439974672896389825889487664478457602967102661653289979711831184612033143767560713417822643184935694167742147036357069083785865218780521493865983748253843904250226257710581090901366250025921421982518278778973807901083252753825208320083307899792763600360739561486929782498720295138623687607108683610254709761259573715035541188014669388924044729055493382947979803101499677801807763045685207155091819040359435503312626768628445242073992308326690524739867761285658189025004005173224200865734725415787227338361235149174061223242862806317638852034208991488652607487
  | 46 => 93690012113614487890973665271124803094152512159343956468145805255301843217088296363236080849607179202015855510667425640815968134238431526755186496319278357438323298143540511297334619926815228708877753019588638911180484530442919982305311430131947699386242105724242264846204687441410483293714739462418107669408466366758139134679978940001968607274829844413771692804524091555381550763172139912741939194263243073043117943135815964455085132502575837692715921238483505433446588253683695295649745647462228774089801383830627162260784635979607049792492227207011544070258473988202236795557158478092596690685851872346563066827611322260593539082770017001216870632424189379382673085282702900143637460802440979428444394366132498321436446362168748422463148503721476206230108664177884594800064259735285574288858734156755641038651499136003466303027308946998354803725113007959575977117673841849738436111262050413243339140134062357135636877390235932660529437850480505776053916802716337377154833375679695053006161662770730711001918949552072424077868723498461224850611790862994700871200630649718676188688934647486112359281416540914222169406860318189174178991638631509938726270763919381371304493797864675457325303824278385532040293462341603886217429908515777575835114805133641348074053308230998172550565760640129955018824063565062519486416935116731065832357088482819661409008662911585131312895432061136843393177999473603866313089106815797840019083587911996833781663587078946705040260863792594036440901232168598414369063041066407571410730112031037016141375208006791782916660265366821418348800037536762826387165625579973270406215336621814921511832773418276222341078529412690618696123667856599915660502599319247377744929230705575393208384607856702855934743197261188861169461172870033916313347691889220410526565834044400669355121800934707039005364081678814833881599501759748818505432977037237002535605998894791571059305748560699217320840583614398214833955500202101242291848263595548536209407
  | 54 => 1439811449633274883576906798024467749714960417833179733186740618820265586969961656209551385585225736013313942150884172677230125510697893180921115004491831143284340702366842195126776557610952303006711385552622268625839036237708618475163232454679003941495296568576333853285973351437968865895201574652621363677683679169567924751770213735401476549803251633333241894669726026226964685957418181435783168982322141123739684979296982776847523632595214785641908087389667356488060773156193978032778869730075554113283720407499115581427563281035672407076610464745041545958223026186917500290910994129348192181379751087944190902550999321501470279673634928492847709011864215937253156620070143047613789836413224452535883126272586576099082518547919747201181994012003755097000614357665760989909533919311510918163369281178382352181137347512555588857149218947408757176526489517891221821995367489553279689261884482021072919968903156908789095136932427796273706808734477474409708182218100711206955603380018314903309282254847083838696570893859785181800498907178274094864408548321197794238188474794185232832158929341566374275773890103636545516374722766552774527487815685802971827253904628648814748184861990349408741669152400336165283316335250764076073324322843022747303376276127409786701187068430485940786128741569775745560517725419795001473526392056966356563271249129784627387080730473134255599829134741347442986065755417115865684449328451439994680360150219710964841164438192125395688110010882575130517423730770919962059743229848305030095937499680842076679766052214824329398298999556797284832359657945032000718399360276843752701831437160128476722872611523595446640647067704866218446726253907164306247173450102520681695048218938836596855974634885258361275192321709852407783507420096626389083928898672410835175279853002027974268304853042897921839556067229900371096665688202922261763506177406407697604775988861527077252681106424417392504334590845785056912490092405414025194918068387975230641622322505600640615916269895465509271008716535361836314609324943353061411686139617845434453911253323908789858500526730530530390332289781625997752769339815154029110970871936914760015593782807816944101323955848194738358125833989966750009229672306159300664248763054325587448137544260399731482833743163283869872721536567647185245497030775143381067846647807
  | 61 => 546838797325335328045805158765788408137190016162507361318177820988396684046238406363685657897914110718108984401475857279293565993769173040304098824471781437075028471133579826423228807599786468300750669241719116550500102229329491308436059765763533275234694902289244191701592172620254674943146698246465388831236486049017791971898362035599681008598944335738510219674421149670967261868463986041477591967013285535223796699701977533286644059801487082290336286915143725925466895857101651010722651015904395873851363757404354023075767447512712134943668877606284345944088343334534782440611429189199886799740893099841922621734843941613669148018550042084669337991442974993720001315213568929688326422712244671061098631172709860363922658331277297753272931568652147236914963301554485881203581015437148344674474829116168753343663359731467692466212764512214855162643826729200286666628690358885075056327947599552156758086112566612726319018906764334250469941219540008068734595186687594093500122266966962238896579467339104405373521488990352659010916190407930608476521554490351134227270623461481760563141539689601334307552951072066725969556332153606855155244416306149168325245671535296882080933893991547700751480694138638039738031833772142300233424538850339735019148916568669131830808823323921355866012852127443943547213165889997356451834341917841261277547668895651719966753069114804616564060143040677840573281410354444138389489761082312042149334511072321324424178285203517073996602645665751169373684758271162730591793097208601443598221014879113249017708291067821356722928582858289466884053413132829285635563574575083048596037216936647546190637896482922756962475962853949409511475223146767279652284732635735451611356128195534290304391104749452002569192784436785365615068133099081018817746257905659092071216436111515616298020625052978951812767060561565976182729389910572449067280637232757448780633003478220312603421616627812323211412505278042746282960369172015944427567448073835283838159941006590436844238958564072742740821381432408320067438713882239191068239834035012379587583538271651880593262154094134565370469723915900222802181254108089312252351164842292508532493198406779538036536863658936560265179356314356306479454033997779697207237078785884446083818506058071224800734965677251280529282305919298499121794729219188178089046919585289519191544817114372134875612819225269167785599194676187499110977615428988715335027670948996693120769400746179906269303295136971464401543365482632174675257772255075250535326489235209950453987717246432112353206942789189286629598995540524733099837398944509562390443808772179094909727526834872694266369409023
  | 69 => 8848391169131620204405939388837973970583440024875011152974524085441397307398682856454392937161303078993583333222968076965814952914414139088311257570573162481354531660480377077765449994085283599440398732115929759687590586719264699117096631866617000996153858941923685275893229042432755986357534233128866310810800790260450635623645406924822419312349111557371407689742453278088358984185020376261057702483063915086271195723098705398701457270700769111923929877411163593447266752908421233885056713741124996883161643032785986471101551525987162256649763393158159215670836031863124425924948450243872122364355083625922521126922232363023640928055990003253049912282438452717763093598942207302895535395143233655346780255106111120947443457455513298566346289960820741586667649592818218850835759052995516198306686793424430361586067105820273748188555384988120458456991453699074160789917504970325860957273010750290913655256654960457643283084045459474921456815448654962321230816966540736367790253303359666819257337635760381949530659865659434822784757651279919632514718972370336527076248426109099272293768539312749326095588464608221712067293619905055043516002537828857779340809271469019641126567209521095840671499051114044349787132411631237372377026700787421135636135106009857875938106481790848286501085096659562624241559823691742001751604185500034543978985444405126725306152251052819827567360403575572039984895922978166028013160169185199041048639115364989586053453146453057633143964213059691737415110495624383407207304450213144280961279826040711791956351778811364775396044362698614081418843938745694888295917713809575971653146801576507120971446550161925987860424242596223768195534974712882890900432003079473318646602062251093412323110736269744922347045541473419022493523870039574818787446476817239338568727294676608605513963715070357808801359501492105753066420912424756025516502545449773323159057324276538682281937271758466240505048743792471929428044793649813702008282208607309638004769923575887066263380857405676727505365576758745271210252039530328843305826589398608140847163081346490126640282424383386985453453429374967367955137710778867379030779351868851667304199655577423632782628985314452634981644568695652171574021469400581326370884714912106930404919207548500887090347981788507920817602845623141992857200966842013035310443445015172694497503362248938550406515500033654305075867635343722949336959190417424684039667840674377655627420470261487276805914623331375002770668009505756927461247280873612893293898293776722643543464708741629521670497203348387434670869426372277648880957322689375567438760510609427303659364804694855574752984678534523556019176646293826050788653149639469100280124915239383080936876561342704517360788988480941011614472476794490588122985210474609476574677630878267175703346582077954627895532642226413391527832520626687281143472527933450063837454505023570187778377338231399334968435579813028895975539224821426636419675149941154421685825909856998696453772153802719231
  | 76 => 5050044419181646941459256090969568430259939035708066976629947913142425547601954457418422953442284062776647104966207622100074856559117997195270960227998121932472602739216181687678450498350781535828309207708493365726507328898204999227619926989931233960895404445102597946113245279934570503330821109724345336256396002270337347329238496551682466438377539667804720102059295128830723669054352402446341538018984634328209767471034340538718557531293453669375669230095030237098602482726959798367564937786891784627970313404058779334331924689119746321586613973629746528920324417754071030357200687676582157414845886638357954800237673989978038523850161582182111403398577409195662315553328939234957319231333022535760772020390993630047166835745398424828370754817993361539045508581774068033241303762780323717673031296531722214638690120156078220371920480506189649536674570525306270735711705798831219016267652675860147120719614862278159081908879846006217600256321207518737865164214919913714255781713776770986963489907299990859431889108662659809933499262581239997636427397929339790186531319556501422683703454377734540846229301242017630194193366838836136150218824864401541588694885950607875323959919879809267598312350570480524878350538422960276206488560067243893377370334037562898174278444028607514329631527301333074007740007131899055349213520234748545013501997134924809383016292739392604591160200441912036698568614084835336825389864067156955037342374208045038333980727275080258883161147709800696869206192348180990114266120977291201322719623041876855452374135698023071980973937197055754376251885534370831800569650581039284358606871276667920539252302876965727054761731067125153493111564827365105565028519782446125602568638430088834148745313197708571330869399814346874015116227203566332112043534469806725554708918156487483451325187218005062144995034725883674489135892173289802656618447673386620863838736701035126488364386227956890920619780444966257919964564805178561289947662419090726909649366850310409477095478175013469864728391964413721789826958835360530749745824941720070386702160331093151653312248072790588917847236473393674976748521404124934283845885709514250460947132583698729350740196097368142137105420155481462316414411855824854261589570779851506347055666086584759135698823922720723268929642204570774989491513597290676124057967664553747849238416781356807074913753894477410767940923183361191955342257153654979802121705461418091197663183513294006733798678105507562917383878779661113726151014297846745715861052827131737746785547124114527924791517094771274756978019819782932346709683803284864174342914890525313158161666699983553466200957228320981859486092153676489583227814672530136041661610411183139075413901326522206848414004879669874435062658365143165648795248914411083395905813313834778931012724080654631068885033417925486706917167956869150468674562935030115783771668822584743165839043834341733013576974632768679087328668566841840818549632282288855893222301743714634214138778698710725590081402947498823259058935279658982032536536518096268983165889722314857717759912770379610116392850593832531423889691877175844696929980849230848161981456244226378750672376245767042664732058325300609656307074914942176245419466500265682255107130548142362974792945087552166368200264783847602415985364259831807
  | 84 => 101764026674182420810251851531051373403586804776149299327606614641127309283692528142959864171793153286714647278509066203243766883354707827546598431448243039750589536859322171276632106244948377719387705927410622874736599246561287827105178493162671266582475168601266085873917152203837018723061095951305939835755311806829211093967026608789534096166428334616226226526208851448532097481763106119297662233673232388656612991909118784607649738044005250908751281780721601163542879610294318219596751695260298422410359971947163004716372430690230555786334339109458557601191319078686757738255282212283630719650563328760034263003856465407194633819169054043119098706324965529591731941058299282749085516537980365439960472518048765756483421338574538902014271182034801086604119502148739215398452170570492401974950424847007211924205443478949700136808330288028885342604959791087347085925673100331449835541516047510831708505431203892868814667391075824685268676853457529727269634734167081925111842658796065392710242436285228007133628391712257176316492252630677322915228824895514117167009665516058980971349713226367444235797937448474226751056142144055719674895297028050893366296765760516197231127920519796532334615921460390742363212337407182743669097481784596210950054485357308543526815315446392728196811231968920492937874004380195831818569296095675478701253230686692697049013684640904395087273996373825475829263443023572512533085418073138825049482371941271235049472235965963259986648143193524575648933900997162864834717203710910766383569338893651002787606755527521152141720615603276300372915740479798457300737089247538764936226230260696571988221245447516143556651280047428998904090108726588587401787561424384989691004938717717371969285552373256007625941189661001894607730365386786726925620908477670594257476378618392040998828491067934569082689487098302163767333414638634075865015824822759111269573222350448924678277931510935893779861193052372801603265366214813716015564097952833768881743605471847438628715608704942872527240173449572013934010810645341119746901884435253624653710804912429880897992011922693846666675022477747607125129218882523960167079787922962837624095381170273331497552127012165668253822691067263447309059805044120387636456479391968730218226130702456860333712526707671388995477839562484767949223931892774507576729719212574671052374852264464986854705508805422612302998844962664253916808280331383483661454827799145711196962294198450981445662609409732204261444885123869882369602792079627965669614966543339958505169024284608506406612017519754116515588112382504174286866239715626846127459368195107452622005954544602090945787790222998825904913883960994876124159640662201629089077157105765927249226507931811109286745464687756809230285956501134343459395160564152191112052144634492001037460025243995573537142161655557966229015638672662958155867323512423336672983166946658675993610656686226445640963259385441277115012672360569408681516260927303742280286740822861707822588079316760037499216155772982672432320268835446003459561596805988402314406640831512245657604827867089526920008522920593798204062715926315310103343491645654399114304445087964288125918002040993792932549686550997378593528449016660043878976574394921775756453977038554025214102133637358865227581187008382144438409133863408740485162849416582327299352943123614939729312347051491086464280976413741720065399774560189628360694740230830584364572513073593668804880102256230604915875582255501327264445321345190847053305186545380961084457556220038711161851761076524599868236128114505317809942411526064571606334421636601665146483870499245796888721919702779855657804919974053163999166463
  | 91 => 53060528611909413626649761866837969386725618113273076244206505401715498127988930734509632895085362157581925771611935161872853270062452100922534430704016063601022877078439325584193791206358412801028047931944138205029553343739128489146662107664105523631424275140370257387650327770869858842470966650369330492430340440912938490558219926739957654963581922092087478742523188089297794987750742230499970446641515255645018010945644857580771497314329892719081918848952718585648369556202162442831807544452615930566835297483405561518456862792576682938709128886687426561280131256738398302941362394611977963015045839684866135360276900047219573045855840771214625325750775622943758381658773124479343603417008450483963218649678701864677203969105263885135233789634020893518107779025401352764024211231803689249322515109675573648762199885142684961105951490365098104326406479792032213221459844247779943309517127323972001180749636584598300626847517602539491907194256032868181217677331310473346841051386804015786173993521626387578125328826850622164403597827150108118155859886498578918100880954242386151234953421291467819621865591718400227681737323711954878479338157842236267828891061166557781327575043000901532604586570557627713249962111671297928199809141875253378494147612212560351031701114624365004311409916838400822241218372541336727864789796770561326436731808671556992522919899937491515909037468307147357681369342809388286860439513878756193639902109343474736196891736781019477973581953571061250560723583202402498446217598436281491701635475946343120352421381185449141520592268833776189082843192787878783702887152272208038791926084016802221102673858449692054213472358060891418835841704997432529704270500030554854118952862760758006708138679626200073989449226358931013509858294223401282228631654101113202524493738779417245277916571579347446812227770948107045118262280476593391997665835878242965610271996540756151075265049920934234476219418515249295836083343324213770790159373006976469994995473320917888936437149832227189740484203490156639718417846841413752532174502642449664958127354645341031905323659708482684366508567867592552592020834370439055778064959427137034332201962514713059398224890167028895154436054593655092623754727236772077664503858186524722432973938957745459714302033240187829957953918966907423748085106129644361220695396254981822135572920558788781969130198720524067889207291239169685402366834230927081704846194199358999424926648852199275809360034901922709284951067364187328926738727433526943024817867892791806935412610966613762745648441196333620427106495149825769854446023620477372734282993950247684335086216985723894150981672646349183206726409981520858293275585448124834853467902114536895092153631503837746477168825958014688620267346028969588182241058888973156847124502554445064613261228208529402979387974288239920426832973715923787404071114056011770947924489030218246011818966989151703916056529386525219628902382189560934562578624123940155500682188097494717263147885996620623049508801205794295494621232560196297713217347480332201110468351167847825320532712159085770941174467765255018611313877034302990857510043780016145656239478844995092875235452024569925877321943765261629515519027780652975488884704987701812607681201340959378796889780854906687298950799161856302673208357852329689467168424211311245622658065568003211144027874565425929417091103843078357470947109675398853193599471409724309027422539778528773284279075914835615423540814772126949955196522559564753895109595058089080507092418114164256454842113540428221449588845156309670856235362857317332204690128587366712090279186878162867838803910018702083369095114144377030877853585672531131312596712062594199591943743017397125782668412577593830340917099235118316361711148083688492511438810547495806281516848520183825188593605860892772778017069790604349783331453543207813794724260011485608755486151596218246480101199373691493009741761334932602075862093263776280201627448991552374833151
  | 99 => 818203089512438603350395492396624435939154983975108294243602695286442689641797914234385818803240165489439229244042765183057789199212886254858904729643078063657146522118409894496882729938789279733684194278305033824310938179716511004219956069387185850038057562978168728285705281337259292878846800142012437748063798670209182548625454598588481985358645522303966649024715633330420593417515155384297841772299929397765640297344235028777102165962365038753041382155547954858365950945021351558490831648075901167144531691239472904098354027575842706616751820450963644645663005509881078976000040569004490260951466042337827347438667017236024728547506659158105591631202248244406421385106583792594217396054793553787395322421556020286360222150733677061770668675527261915531850178917790077424684703520434672905939605882887940778156686776959700711939706132234221583594977312442324902481149830350534751179135675437056433282995624864850736828119633140685990561622238668442303308546778564608574324372162133845097163293956202922311278971750788868489370126163629604874626895548432534646268716584110985843495794191890918804078442161164292639366257754389685242881885747759061921506195628704253165325377559394745135613624544170115994072756090347396955131186993949623875170267140077161163661464269436337841399600150266889962851574365847298386960885396658759546966352185958913847423459827291303128244341803350497420357532577783865205123600920857433183545979549629600811104626665134358837642538430044111457238857471428000649470372377545028553644537091895111179168832711288349391522964133776877570397170520746859611769336590532798781649706030998857250359514860618780810849586488124935791619967122528239173063617844254117191285888488261025672326032282309688112231697453211551235711079273241866453542361376946398035670711228429715893643780013213657566851146526694457779293975660027960764418923960924895542327110426983795860385353819206303945964595581115911771113312229080105901025826057904717786947784797832626657523197282215056889013748196296478768615750457406055446439897819675474812517438651115836458373286951109748763083266487952342627715007837779248090947600463077678689385856575704191890321691062176758871834734196440520712619799103616391443056910343333247278616596574751464173409799766271566282351135059387914839714123764765014416725703697296552042940383726909821351760958064500973167960717095517822853697990438545097989593476589497025221461427642652592440200974229162706602353019546858762017586156209797730469097878097547901539231013083964939081217306918749041550971667140807705864665814231168704771559808506673217618339783527995525522049579329148860502868392448598113283891812612036770566646547678379812637694626282746850283790996523089817484883842443035191485210529534534726130899118573676085772086035664355591556805889448396102925032987268153870708670392950292301228934480827202528663494312628496366207993663371662534980384667936016751856428415294287159265030312684817835722967783000012145494826278670077271011567117590011273586493797058728475549991667466392966189755976406872725008341680873822538957739232458942790197709637303228188183403454143185826796756643087335401233871150954349155292864270293257751072983447908519833695104117638703137206379385829356887462103510332859827742466489016284013421435159139389896492690599670940486385856642676417342888451938656440646043364060686918229279254665039892623711161591973324463531389467033699998898258026966071629025308161227449267274368712809753596161817832828394888535828698278131352418759182339966158162166190278608322661457324312450651381137300856023772118475582090582130651373221970927886029898962155442130044672514419188551744310321026475622297548061169490208018631767569688568720726299337894815744717791190550265194757115403765345915340678113691719934408178032588280336960680897067212267412416472071226659507213048494599639440259586085737477710306934979545157665174404804972981052027170091212750959122593131941762423092003533494806801871967835319905870360272146117591102912495217781744788388466845354620202771606100021190152931712133215161682858686688417495185013101348037090373353271355187691233452682398480208215369131563225524307357384356773330387937559157305824535979640956345849214522463591677594141661915772362187984222738307468690970596343807
  | 106 => 15635973601131019539254056843232844379179360928026942741984507642763329803674137534523829606009728935719788735547752364786786627325331321293796897855872889726998864607206002517852302519120930019243943685212545267953065138981075828147555619623642661313218749908399003285819010740283554074139458788454004495620042697469804468829000675429802674853623926360913675333895521503478910205974448914256745152612283066472218956268609985420067260593426111658987443331059142301062744051479162805008460441149503943222126858122616869690766070260524107369316841477801706783526958288855741388237336097241558913640536683298172067506258457393210952983102443051827416673036837327693520804431655459985707205724860259987588446489376268550101050605550719054907537502271115242508589950601075485103969571611490966238371236597772017348501693066794749609954975924094373489541101104087058840153260531835308801740148556989959128056097571619890269688783657224302250398885422615697407830637489603995478536798198188738729621247187262884146946021443051660902554940217215018409023384529690973580412820896527277907500151237372032860156259793195366642535905240393217061149680727508138106268435935027390985558495263917687361489967638304865125548886583633316319346738883665691538571073087289420949258961382736722411016082046783731135923091980518961988834206029736553220199575473388553813442176478161495601967514796964236716270315454610686473162363772230172615146972773422895039331012214827643532948986139857548698870441823897002202055676007173895628947619261803585869647167824429385052968977868875372045997988708049882167964614235997071642639657676895891982728222470974421170045134494404181286288980088094531188342862745161243456246938530024466048524764824333749106605168269607625090002370651955518187540155156622658604751229623419784704179360313045565848075923905370715570725522724144815413070599804689046859337768028223979424722644325948584305577153699536729448399234989360013878159205081899096084771051655576954045653880093093741046083556077227873563924570209125867222218036273944950169568922772553131822835774187574671147025048218967612131175787611183998233554979427164876419057910521915819895536248240940128826389170447057608859567998154323282773318112995345909610868309351199512687536755410718166425072286580064250116475809698696778219969201617279856462991236110349520801355107352634191431634115072044833585679257040454774247673938513403324245749037035854281328014445612779430726992631222911251537041521935478371337960426361097484308036314754431321815062155335127005173572700907222623168532180444603101853038943686317314904760629528105007741231398109269811112400889338559885736758583117977099875080328748936272522698492847626684139363317440710356658943232287174846984948612284351014329283763674043912916260635761662305755848656508870382211895269337099008807377532317349303792792640147941077351513561400024368096970539167277235497751434011821593135247399409842025122881961465314243381704341431114879865810927471189167015011699882744642392648180953500778648640826403059457671514740014718626924339859317640690065020482331591399727230801637096344988321901183830322354225196851288783872052479302193900594862259775555247465617713927795693546477097318871302898394245921511561763622378084122640394483984661550476038837567670688798183171660826494242654690299849919174107419249853642841184473303142563068041655079398991849849088607434631509586879650303850504034449429797530719706535124875167494491011567203148654455544046309373180872117125136616569562926691595867108713839997250277658112939338111250301106158043984595900285856446007339286822701960853757857938541830412889199532182157086963506610951875583547187993001426040188142796545969149370834761629861774884732043741341413420088091929050695206267027517184314647049411190571326199244400556203535733732892594111694206915971935860791775769704471490076907372204166761731114378902496742293003567492214451841187646828389618752799349272173706601356376075383721817766506019850308070759560944611715669413058779098115112637449450145738704565799673639631546516050561744676375419411082036371286246615626358231163692042824338600576492329206486130994275195629504553511563587392999453887238296581947377145866847155072600915616563886594576884928896913653660848375845961590522821821687887290680329332152851617351185367291132251002417770942264173278008665955924489647268582593979316805422110661486557093149964704436455850967705831727150483001171584505454177631037036676481247999370309331208187871502159063743913151133169165892464706399822693619642331913471401436286132881224715561863217151
  | 113 => 73398322811286206348237732865044628791079367690760189477417897210260317003632393716708307799866765210284790907658237296597469289298860675989253954853916984458991215013962878128759455766170463420077598120083703324857263930879430578900004487640172009113841539241045424571435404496480998341316779343901442175534379923476514993615851214160331534894206607003608056397552440067715281064690774677438559838193406072207797549520163808851398528459891544255333722704827435222211986874148624553208861143670750685040856266413903608715956365458324888126269160270193163949443404385270383849763940354247684539426783339533270785781369002683120610668957373081213620215718269720300776346461793359155303704749203348316111754544892556395226048382714484171055203777946851849422514657463941315399839007283696376821634085895524539608290825298643899668201616692459808576158500393370929928716029909642060042908173168004162111441056071643871887465134521848907393904904046663919049664852432711917271638731958141916500947116215041500873472956881383024908282257321499306587389992909921260266395307452466135728224081471297258585432748039984020470635397404300416025384937380207689225524049799526405472898995170199775609293183045820258781355341339724059562391796289130516091717080479109301730990078104026123025435805255188458084308014654203268224104057141892727855352986699788714658663570101991309845456453060843014598687931572207041688057122879231923571577855352069009180530598810662282966083326008469496471260333927055764158971155850236353158790947319434131643375520814355527528539372429271345467153758447327571502368339053487234142817361708161515555360707749887329039391495192976770947901869209485067036711855016861064643257715792701974856523765210279104724895214053081296601598585051227860031642821051350783417524504938571740161221653098002169906482341521548445905796242164689946384675199757291190019361934308841107028583429107330504388166905072320717905638627429658791425262517370850437497611364728043119439137628723406153351650746587909092600918124367033921435137171554712513163828674139300971271075977811292526322337065734213063234477612011871962028457995496516368326230343557574145740179646214213635742864892968071684061830308346233848201105090373222832930414162745674925077596526976147458373551733283917388163973028422940944036649669694533161309263643417714069424477403227586048887471222027955122240075774380350516447391930663010055856102495601215593344342260964045160631426725144941238709269495743873511036973651847321904675168063771935693502586159771191554538356547439376954192276963100281919231760658518568771726556785814661216761556574204572000710931915183124407429521173242000657498979645295795020861724018186625552302429065187676640845805000958964508718228615672702950303150619895776788615007446771499272765646080893265743173725241879159623359718587463737926763427664624382708195882904610609397520067062027205523562008952977739768339033756812483572201259333572829009615107695518944734307829155140248149881307777169548936469074332055458634542115265129506536581080650693472993295635036048699514729630682039878677520774757518671865352512072306034736037510413632769518521106808399564251820899629102351147481085195302741588719777570914853308480091594439154423882185731635307697491923355684047049649547969183703306028720632412033629984277127711411562315828298913679780347322772392446485320905535616170191511093850835226683227142846419008394071013125467383739035978025504972175077265123790782063291111581820847291245576999471938871049372826903276215544063904199221932323281053135102975166635782164880931351062784379490617612575661021806964118191771444159549279166952306447072194432818409812815235908448149616016936910128005665737594632845096578246419577064137334240005658233352574075175205770907930952601869251492049918415369992636007194148821087777142157783532522733959201933481296506562243535290709529985479934631308007262893681183847605821279941048556237942125173004133718613235859860773540158266305496624753456579272906029428628133181400881751055940065780019947903826600176952699069794882623630549094037463126440308164572241158406026376297791428223287234298745382621256952702901661670970281999873281594792423147889837782290943180965950359594678551522732132357957102008131881477272029022395753843850544103882513077613143062501060840738861555231749218145020273941104630363418546158419347915953394253880674934131410615761713730138770804313697053783836526245042589004364451867941089680848333821722820272975883072444126993314338749390194521704471695009419932038767805699200030386014321691101976424745566124707908399137778439432477856911880162706962068297713059558761369395803902345948105633348655745926526205532065476332156255737499850871883045191109804339288496481112146825007915336825554148485501539164041320305491491624412688363657093703431126633241032761455779005249382680073751325022359941114465956441431736319
  | 120 => 11579298477064972064307649454014780651733875316039349613137861219316248765393873090689477851894942243989661294545725110014557521231401322155055413094059382869709654697159092515153600470265030391327323210080151448085453672957383870172791339005349941566245360450513319763693474945093282489476946500117517303707844923007862266621493408878848664940311657546306645923259580276376133595298518102624304836098220192343668856749398948450947483312013297780938857838451983143308903349005754238991545544588747569292322873720169856316239683584876021261003936278543315513053292956197751771710651898417869070152488552554220749634282678556316155632119030216782145197572240452321620520359121630147812401192411318268592020432818112499179678438017336358912638221434347996892866036286578197713378847342383285350651503196027257288270670698962765554601261001112351568330015401236082869542184380367384701176252883109595456664514506051309746492398977815964122248168995647045917655812192085641324159915220380214378930723666918768307876059423815142067540595142519702719920951257855350372847722209892790225648937216469083757028390800060334873299884839111565829796173764430696677640154583038160528636600129576336151966348004550763686191293646205627381405360070755472108974799316355620858102697733826910469914331969485390341391856472756983797464619711796839439139770391911978202154556649382156176501684329259855374634652698035640557866841366417771012636717579666759010557499056260188002475940274783008745571761563199019363450817416190378045985724481802473215579003777507373568070071820060864835820103123487756215879758864621880803001590080461775018842304164920128258309185430750570703023751221730541497319084045717636161260994663147600501103097708737445975163746211454956143425506475061055500047518521680792838654679809608332225387518656226611245872298012169920223329128814817898082408785750442636258489277011687777039461371281804158016119069322205464686421920453091209066909665178208349694360245770336898835769779778827741230046025755977953204471927564745203401919305340736744087675798750650676193308193307286303498290641581743440216838068705878423892260035837069441594334281099837601335140999787366988080699939691958230369366720432292390114055771113339020026830925901358164928537474611426736941368436616019303964036411704079668731379027753354863929846149940965272508700916147501659000409936638244638552944501356941046276535444323948358890176779685256740159108853490524196868609450008801524026407378062186060438230468789186318813124099431701065414998912778987025430327364865632586854629185087466098589193142339905347398166590136055110718576751963601255477618544906187214451847800067971577240725782319109032223953760765826394567929049752920251462304186378646495505178491492919010374027903751277784908530622644595206611234132787208741926015027282341397763355957156225498473393485477193158313678957144565539153082750673487675255782395722515642949035758308622625845291260490564977085110327100439075551492812203606842939438166595609621319067228981709306945561657922244854600844635021101795516426119901567161005037733972656898916637949689729736734383068900432788340489659043182860765129724170932222016285350723821426087500486714992392314836820995163608920066055597838427730016722014134082723777287160689418442068814570036834217459268603277450461521589455048539310602779095367209841739604057854240823316680491110804706126587234331585580685784674245618397444417759184184096507042216609937662529567638487787514360346807486516060917368070821605592241228824027244974325039896445731185652856188858033215911807733189849187756433594577004749009422495317070988285632975276724454570838576834876661891605736571393867647539205325385156112258753128564632235624994832099381126015769828070297982352756024512058771396753630695880829530377862505048367350566136506504900812054893506122268593145510645593702516815965744006484233879018226814157584878547183260323828356727068681274784226350911465983741349393215878365366376292430609131476644128329530236559030049300873598098571309144703439635349724053824321016766948841218746356846230957053165492683956762008703431359920778186191077894018243638673061859762657587513609500641390852854277554534958619276792087143787584734629419398974016108062206627033795620105240482523730941327451716675510451409848542124608836954473750483358100102691432564139844036900935111021452450991977103895140147208745843171075324743915045585518716141197153033091203821877678506013789843985199975561147122912963632377606049989217232024626357125638164752352938808164369747569650312859976194455213844719213715269439159927290814394557845870772337732074951633821850349889225731113750335058961724433738346326258351814611727094229764763456300187293467835008134147996068466788984142214071416086950567176920502323728756589494451588490045644820037465182655880614938039827745427364072499968930349058113456895016195573452502913532582162200705785541992761402911261532686604277138648282431271576857004859291623318158904651655125230492212008767797360302845047848296914565876912101459083466850478335716757241895036558067452374574221277163630247237964860306643276608093684178342605203545575981291546697042159725618458964395514119842857201172479
  | 128 => 440952174134090260709731794930631735754255928361397472139455685101653436050745686255277545642937803994732082302893780067579098381322339593701697164714013836091493085924042524016805858828865262257124336519290145504540874114519824617971168871510125447578925760082072224857312928231305355868923819574556829658379418876102758700824537735037627717071573118205605568578084670989591228901397843624949854855411139832209477130927740507441029212882283778641801138755109219039321101184268135238443427554335418299033829017077880624864276966582017652537854596191899719651335319518123150303456931650752798529382123423122842205239094261430926177968723712574461538294708521151210601645227134589768776688870708504020434559165063188932269784203212718957594642106345908475317978926828982217220538662488658417844805152955031535100139253880510638211162963370261569929226137877805883960334954649152274870152905540394786033646551557144991357337720216810115448788117188368929893213518612499215507956184485202406304742052883353094059870773106803404526091573263405895844169196573701697282020693589373436559442769306387055314222304158267396711278527339471892522192643930818219829382654297211264221603968172304980783751721744964431723906853206550930605861601912673583981580759319559662508801815831358003447967577283937260419780983078360427945614568521844223180247376119446174523573685017568081002106330465290148315585522849060906876645857529817988239617860514935138141648244412546628607995707384719815290273648135502103169514951887334945847089315249170386625523420549684876147846829985340690241994672459480918849720311499816935694506791643152191382588085879957490858717320121572869062528260136245380711034980685282046568302750561719180871882738696733436533993220528035743918914018330987215554535850115358628030403794205098640642822356991170245113806283509880712293125234494334060953062863479948153352381012783392682262249900525694453199528585577653780328721480993757620522466120422384376148186912136963185015904898997666796405374287998683957659452649413574540969162845358324270878066798946271914462495327435301408877149017841948275078853786989864628839303528027367900138886213226469320361734044084742300095040775657819533739489242827659895710110160912212759901235475124011249470373738506508894680897543865875886457901870525266831704551124255612855200451833589617836463727090195708035904480233747193234499017921327397860637107504538546572817523821339531479819602723634863988129648143064697078577197114704698036892011168587170428606123810996229006033839851239018430334963289998388389768580583915513150728603815632100438635095369070053932463259405278767206806542298076626099588824902237912321901791243390464114506209658055095993864285733681211270729115184109483496545035384357016924211198786478652281476055217773212952010074128556086916481747031478097037514460361478951406206809955441107788438087598071033745561686458486726428514081596492696287462438356588391400063097737207582675671623770276743427451723645565137245729764840023102832117654122489462458197799212482949533199095488556901339410458532445680339120272930628693034361159050928053757361932586259851967879666491384367545085307331518401240324365557549673146232592179636300917115562479361855239634759927918915162866597620234833359649057612494964650124638131281997821396604018871036937687742282435343954372786058267456239587840367608766619279183901978335142232836633260467728550080441194510730690311732913295020908494106808345676935245681404360020163288608666256825018297412149901302327376417998020086776146642796067869248032977351568109520658452667828465694070599200667130194306158207971404362968904046720557258269700010600415255219446585798468722078174414381388088444574302433685480633434001857668320722333867309587010002455586324738585749120056543797939847042668099212657217931912160777318626396006965317980454782942527998438687464834807578539068725201751873433375171700872161149785183196563372714169817121129448427482610199928826411808112493593052370813410141149234197789161770089667126274225911487189894609840225094240909996656655309800062061939489206517062600247667242231652703215906845056764185593299943811775657464458696879585770690578114590967289715459791467462349464116039126099732006765134034598635123412912724299936966213303383558976655065643612331364515015130843608632513875649289404745384875121202182512136257044590826959927085757449099404208276322812790731794103928381090796575571199049715004634287664057189991717777722542733419931966851584229993703668672281938501050602028651568269196267377783023532573549763802044918554933900074724346190809812467649174176930408615735099052647396993428888069256861271392119729632018452358442543966985944270219489956439531576662580173690514100379003489119980159716733568615740139638444718837385177823269690373922588285002021730842336849114693236690829126635850133211355263044869686562590181144317271532937875278178193534443637411709824990924276174298638536499618444908337525201864907985293476772781483779959652893552830791074633189182873487993340469699739866769101996999955251123529270584777766042893404572765488584410620890683080681520275906048306378068523849118805750456584578885013783227854205357446911393697356513949161492548351343110501948392810696875656045331346451452175213550396900206377250453425755538533592325608081342668042526622891619985173349579390468981062626728692548387853614769469752091350952270250482189166381929174269802319886423114169670882697114651403985004464017921173429445024467650627636972332368091184484557375259363852218519967876102918382813183
  | _ => 0

def digit (w value i : Nat) : Nat := (value / (2^w)^i) % 2^w

def mark (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, m => (if m.testBit 0 then 1 else 0) + 2^w * mark w n (m >>> 1)

def unitDigits (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, i => 2^i + 2^w * unitDigits w n (i+1)

def identityWord (w n : Nat) := unitDigits w n 0

def step (n : Nat) (m : Nat) (v : (Nat × Nat) × Nat) : Nat :=
  let i := v.2
  let mid := m ^^^ (digit width m i * mark width n v.1.2)
  if v.1.1 < n then mid ^^^ (digit width mid v.1.1 <<< (width*i)) else mid

def encoding (n : Nat) := (pivots n).zipIdx.reverse.foldl (step n) (identityWord width n)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPackedData ====

-- ==== begin CRTPivots ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix Placement

def sweep (r : Rows) (i mask : Nat) : Rows :=
  let src := Matrix.read r i
  Array.ofFn fun j : Fin r.size => if mask.testBit j.val then Matrix.read r j.val ^^^ src else Matrix.read r j.val

def pivotBack (n : Nat) (r : Rows) (v : (Nat × Nat) × Nat) : Rows :=
  let mid := sweep r v.2 v.1.2
  if v.1.1 < n then applyPair mid (v.1.1,v.2) else mid

def fastBasis (n : Nat) : Rows := (pivots n).zipIdx.reverse.foldl (pivotBack n) (units n)

@[simp] theorem sweep_size (r : Rows) (i m : Nat) : (sweep r i m).size = r.size := by simp [sweep]

@[simp] theorem pivotBack_size (n : Nat) (r : Rows) (v : (Nat × Nat) × Nat) :
    (pivotBack n r v).size = r.size := by unfold pivotBack; dsimp only; split <;> simp

theorem apply_read (r : Rows) (i j q : Nat) (hb : j < r.size) :
    Matrix.read (applyPair r (i,j)) q =
      if q = j then Matrix.read r j ^^^ Matrix.read r i else Matrix.read r q := by
  by_cases e : q = j
  · subst q; simp [applyPair,Matrix.read,hb]
  · simp [applyPair,Matrix.read,e,Ne.symm e]

private theorem read_sweep_list (r : Rows) (i q : Nat) (xs : List Nat) (nd : xs.Nodup)
    (sep : i ∉ xs) (bounds : ∀ j ∈ xs, j < r.size) :
    Matrix.read (applyOps (xs.map (fun j => (i,j))) r) q =
      if q ∈ xs then Matrix.read r q ^^^ Matrix.read r i else Matrix.read r q := by
  induction xs generalizing r with
  | nil => simp [applyOps]
  | cons j xs ih =>
    change Matrix.read (applyOps (xs.map (fun z => (i,z))) (applyPair r (i,j))) q = _
    have hj := bounds j (by simp)
    have distinct : i ≠ j := fun e => sep (by simp [e])
    have rest : i ∉ xs := fun h => sep (List.mem_cons_of_mem _ h)
    rw [ih _ (List.nodup_cons.mp nd).2 rest (by simpa only [applyPair_size] using
      (fun k hk => bounds k (List.mem_cons_of_mem _ hk) : ∀ k ∈ xs, k < r.size))]
    by_cases eq : q = j
    · subst q; simp [apply_read _ _ _ _ hj, (List.nodup_cons.mp nd).1]
    · simp [apply_read _ _ _ _ hj,eq,distinct]

private theorem backward_row (n i donor mask : Nat) (r : Rows) (size : r.size = n) (off : mask.testBit i = false) :
    applyOps (elimStep n i (donor,mask)).reverse r = pivotBack n r ((donor,mask),i) := by
  let xs := (selected n mask).reverse
  have nd : xs.Nodup := List.nodup_reverse.mpr (List.Nodup.filter _ List.nodup_range)
  have sep : i ∉ xs := by simp [xs,selected,off]
  have bound : ∀ j ∈ xs, j < r.size := fun j hj => size ▸ List.mem_range.mp (List.mem_filter.mp (List.mem_reverse.mp hj)).1
  have fast : applyOps (xs.map (fun j => (i,j))) r = sweep r i mask := by
    apply Array.ext
    · simp
    · intro q hq _
      have inside : q < r.size := by simpa only [applyOps_size] using hq
      have step := read_sweep_list r i q xs nd sep bound
      have live : q < n := size ▸ inside
      have correct : Matrix.read (applyOps (xs.map (fun j => (i,j))) r) q = Matrix.read (sweep r i mask) q := by
        simpa [xs,selected,live,sweep,Matrix.read,inside] using step
      simpa only [Matrix.read,Array.getElem?_eq_getElem hq, Array.getElem?_eq_getElem (by simpa using inside : q < (sweep r i mask).size),Option.getD_some] using correct
  unfold elimStep pivotBack
  dsimp only
  rw [List.reverse_append,←List.map_reverse]
  change applyOps (xs.map (fun j => (i,j)) ++ _) r = _
  rw [show ∀ ys zs (a : Rows), applyOps (ys++zs) a = applyOps zs (applyOps ys a) from fun _ _ _ => List.foldl_append,fast]
  split <;> rfl

theorem fast_basis_correct (n : Nat) (hn : UsedWidth n) : applyOps (basisNetwork n) (units n) = fastBasis n := by
  let rows := (pivots n).zipIdx
  have all : ∀ v ∈ rows.reverse, v.1.2.testBit v.2 = false := by
    intro v hv
    obtain ⟨⟨donor,mask⟩,i⟩ := v
    have ok := of_decide_eq_true (List.all_eq_true.mp (good_pivots n hn) _ (List.mem_reverse.mp hv))
    exact ok.2.2
  have fold (xs : List ((Nat × Nat) × Nat)) (r : Rows) (size : r.size = n)
      (h : ∀ v ∈ xs, v.1.2.testBit v.2 = false) :
      applyOps (xs.flatMap (fun (row,i) => (elimStep n i row).reverse)) r = xs.foldl (pivotBack n) r := by
    induction xs generalizing r with
    | nil => rfl
    | cons v xs ih =>
      obtain ⟨⟨donor,mask⟩,i⟩ := v
      rw [List.flatMap_cons]
      unfold applyOps
      rw [List.foldl_append]
      change applyOps _ (applyOps (elimStep n i (donor,mask)).reverse r) = xs.foldl _ _
      rw [backward_row n i donor mask r size (h _ (List.mem_cons_self ..))]
      apply ih _ ((pivotBack_size ..).trans size) (fun z hz => h z (List.mem_cons_of_mem _ hz))
  simpa only [basisNetwork,fastBasis,List.reverse_flatMap,Function.comp_def,rows] using
    fold rows.reverse (units n) (by simp [units]) all

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTPivots ====

-- ==== begin CRTPacked ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix Placement

theorem digit_bound (w a i : Nat) : digit w a i < 2^w := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem digit_zero (w lo hi : Nat) (h : lo < 2^w) : digit w (lo+2^w*hi) 0 = lo := by
  simp [digit,Nat.mod_eq_of_lt h]

theorem digit_succ (w lo hi i : Nat) (h : lo < 2^w) : digit w (lo+2^w*hi) (i+1) = digit w hi i := by
  simp only [digit,pow_succ']
  rw [←Nat.div_div_eq_div_mul,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt h,Nat.zero_add]

theorem digit_xor (w a b i : Nat) : digit w (a ^^^ b) i = digit w a i ^^^ digit w b i := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [digit,←Nat.pow_mul,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow,Nat.testBit_xor]
  cases decide (j<w) <;> simp

theorem digit_mark_mul (w n mask v q : Nat) (sv : v < 2^w) (hq : q < n) :
    digit w (v*mark w n mask) q = if mask.testBit q then v else 0 := by
  induction n generalizing mask q with
  | zero => omega
  | succ n ih =>
    have eq : v*mark w (n+1) mask = (if mask.testBit 0 then v else 0) + 2^w*(v*mark w n (mask>>>1)) := by
      rw [mark,Nat.mul_add,Nat.mul_left_comm v (2^w)]
      cases mask.testBit 0 <;> simp
    have low : (if mask.testBit 0 then v else 0) < 2^w := by split <;> first | exact sv | exact Nat.two_pow_pos _
    rw [eq]
    cases q with
    | zero => exact digit_zero _ _ _ low
    | succ q =>
      rw [digit_succ _ _ _ _ low,ih _ _ (by omega),Nat.testBit_shiftRight, Nat.one_add]

theorem digit_single (w v i q : Nat) (sv : v < 2^w) :
    digit w (v <<< (w*i)) q = if q = i then v else 0 := by
  induction i generalizing q with
  | zero =>
    simp only [Nat.mul_zero,Nat.shiftLeft_zero]
    cases q with
    | zero => simp [digit,Nat.mod_eq_of_lt sv]
    | succ q =>
      have h := digit_succ w v 0 q sv
      simpa [digit] using h
  | succ i ih =>
    have e : v <<< (w*(i+1)) = 0 + 2^w*(v <<< (w*i)) := by
      rw [Nat.mul_succ,Nat.shiftLeft_eq,Nat.pow_add,Nat.shiftLeft_eq,Nat.zero_add]; ac_rfl
    rw [e]
    cases q with
    | zero => simpa using digit_zero w 0 _ (Nat.two_pow_pos w)
    | succ q => simpa only [Nat.succ.injEq,ih] using digit_succ w 0 (v <<< (w*i)) q (Nat.two_pow_pos w)

theorem digit_units (w n start q : Nat) (bound : start+n ≤ w) (hq : q < n) :
    digit w (unitDigits w n start) q = 2^(start+q) := by
  induction n generalizing start q with
  | zero => omega
  | succ n ih =>
    have low : 2^start < 2^w := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [unitDigits]
    cases q with
    | zero => simpa using digit_zero w (2^start) _ low
    | succ q =>
      rw [digit_succ _ _ _ _ low,ih _ _ (by omega) (by omega),show start+1+q = start+(q+1) by omega]

def Matches (x : Nat) (r : Rows) : Prop := ∀ q < r.size, Matrix.read r q = digit width x q

theorem matches_step (n : Nat) (x : Nat) (r : Rows) (v : (Nat × Nat) × Nat) (size : r.size = n)
    (hi : v.2 < n) (agree : Matches x r) : Matches (step n x v) (pivotBack n r v) := by
  let i := v.2
  let mask := v.1.2
  let y := x ^^^ (digit width x i * mark width n mask)
  have mid : Matches y (sweep r i mask) := by
    intro q hq
    have sq : q < r.size := by simpa only [sweep_size] using hq
    have si : i < r.size := size ▸ hi
    simp only [sweep,Matrix.read] at hq
    change Matrix.read (sweep r i mask) q = digit width (x ^^^ (digit width x i * mark width n mask)) q
    rw [digit_xor,digit_mark_mul _ _ _ _ _ (digit_bound ..) (size ▸ sq)]
    have readRow : Matrix.read (sweep r i mask) q = if mask.testBit q then Matrix.read r q ^^^ Matrix.read r i else Matrix.read r q := by
      simp [sweep,Matrix.read,sq]
    rw [readRow,agree q sq,agree i si]
    cases mask.testBit q <;> simp
  change Matches (if v.1.1 < n then y ^^^ (digit width y v.1.1 <<< (width*i)) else y)
    (if v.1.1 < n then applyPair (sweep r i mask) (v.1.1,i) else sweep r i mask)
  split
  · rename_i inside
    intro q hq
    have sz : (sweep r i mask).size = n := (sweep_size ..).trans size
    have sq : q < (sweep r i mask).size := by simpa only [applyPair_size] using hq
    rw [apply_read _ _ _ _ (sz ▸ hi),digit_xor,digit_single _ _ _ _ (digit_bound ..),
      mid q sq,mid i (sz ▸ hi),mid v.1.1 (sz ▸ inside)]
    by_cases hit : q = i <;> simp [hit]
  · exact mid

theorem encoding_matches (n : Nat) (hn : UsedWidth n) (bound : n ≤ width) : Matches (encoding n) (fastBasis n) := by
  have fold (xs : List ((Nat × Nat) × Nat)) (x : Nat) (r : Rows) (size : r.size = n)
      (agree : Matches x r) (good : ∀ v ∈ xs, v.2 < n) :
      Matches (xs.foldl (step n) x) (xs.foldl (pivotBack n) r) := by
    induction xs generalizing x r with
    | nil => exact agree
    | cons v xs ih =>
      exact ih (step n x v) (pivotBack n r v) ((pivotBack_size ..).trans size)
        (matches_step n x r v size (good _ (List.mem_cons_self ..)) agree) (fun a ha => good a (List.mem_cons_of_mem _ ha))
  apply fold _ _ _ (by simp [units])
  · intro q hq
    have sq : q < n := by simpa [units] using hq
    simpa [units,Matrix.read,sq,identityWord] using (digit_units width n 0 q (by simpa using bound) sq).symm
  · intro v hv
    obtain ⟨⟨donor,mask⟩,i⟩ := v
    have h := of_decide_eq_true (List.all_eq_true.mp (good_pivots n hn) _ (List.mem_reverse.mp hv))
    exact h.1

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPacked ====

-- ==== begin CRTBasisReceipt ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

/-- Spread four bits across four 144-bit lanes with two fixed masks. -/
def spreadFour (x : Nat) : Nat :=
  let pairs := (x ||| (x <<< (2*(width-1)))) &&& (3 ||| (3 <<< (2*width)))
  (pairs ||| (pairs <<< (width-1))) &&& (1 ||| (1 <<< width) ||| (1 <<< (2*width)) ||| (1 <<< (3*width)))

private theorem four_checked : ∀ a : Fin 16, spreadFour a.val = mark width 4 a.val := by decide +kernel

private theorem mark_congr (n a b : Nat) (eq : ∀ i < n, a.testBit i = b.testBit i) : mark width n a = mark width n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [mark,eq 0 (Nat.zero_lt_succ _)]
    rw [ih (a>>>1) (b>>>1) (fun i hi => by simp only [Nat.testBit_shiftRight]; exact eq _ (by omega))]

private theorem four (a : Nat) : mark width 4 a = spreadFour (a%16) := by
  rw [four_checked ⟨a%16,Nat.mod_lt _ (by decide)⟩]
  apply mark_congr
  intro i hi
  change a.testBit i = (a % 2^4).testBit i
  rw [Nat.testBit_mod_two_pow]
  simp [hi]

private theorem mark_add (n m bits : Nat) :
    mark width (n+m) bits = mark width n bits + 2^(width*n) * mark width m (bits>>>n) := by
  induction n generalizing bits with
  | zero => simp [mark]
  | succ n ih =>
    rw [Nat.succ_add,mark,ih,mark,←Nat.shiftRight_add,Nat.one_add,Nat.mul_succ,Nat.pow_add]
    ring

def spreadChunks (r : Nat) : Nat → Nat → Nat
  | 0, a => mark width r a
  | c+1, a => spreadFour (a%16) + (spreadChunks r c (a>>>4) <<< (4*width))

private theorem spreadChunks_eq (r c bits : Nat) : mark width (4*c+r) bits = spreadChunks r c bits := by
  induction c generalizing bits with
  | zero => simp [spreadChunks]
  | succ c ih =>
    rw [show 4*(c+1)+r = 4+(4*c+r) by omega,mark_add,four,ih,spreadChunks,Nat.shiftLeft_eq]
    simp [Nat.mul_comm]

def capture (w value i : Nat) : Nat := (value >>> (w*i)) &&& (2^w-1)

theorem capture_eq (w value i : Nat) : capture w value i = digit w value i := by
  simp only [capture,digit,Nat.and_two_pow_sub_one_eq_mod,Nat.shiftRight_eq_div_pow,Nat.pow_mul]

def quickStep (n : Nat) (bits : Nat) (v : (Nat × Nat) × Nat) : Nat :=
  let i := v.2
  let marks := spreadChunks (n%4) (n/4) v.1.2
  let mid := bits ^^^ (capture width bits i * marks)
  if v.1.1<n then mid ^^^ (capture width mid v.1.1 <<< (width*i)) else mid

private theorem quickStep_eq (n : Nat) : quickStep n = step n := by
  funext bits v
  unfold quickStep step
  simp only [capture_eq,←spreadChunks_eq,Nat.div_add_mod]

def quickEncoding (n : Nat) := (pivots n).zipIdx.reverse.foldl (quickStep n) (identityWord width n)

theorem quickEncoding_eq (n : Nat) : quickEncoding n = encoding n := by
  simp only [quickEncoding,encoding,quickStep_eq]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix Packed
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

private theorem packed_identity (n : Nat) (hn : UsedWidth n) : encoding n = basisWord n := by
  rw [←quickEncoding_eq]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem recorded (n : Nat) (hn : UsedWidth n) :
    n ≤ width ∧ (encoded n).size = n ∧ ∀ i : Fin n, Matrix.read (encoded n) i.val = digit width (basisWord n) i.val := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem coordinates_checked (n : Nat) (hn : UsedWidth n) : CoordinatesOK n := by
  obtain ⟨bound,sz,data⟩ := recorded n hn
  have checks := encoding_matches n hn bound
  rw [packed_identity n hn] at checks
  have fs : (fastBasis n).size = n := by rw [←fast_basis_correct n hn,applyOps_size]; simp [units]
  unfold CoordinatesOK
  rw [fast_basis_correct n hn]
  apply Array.ext (fs.trans sz.symm)
  intro q hf he
  have equal := (checks q hf).trans (data ⟨q,fs ▸ hf⟩).symm
  simpa only [Matrix.read,Array.getElem?_eq_getElem hf,Array.getElem?_eq_getElem he,Option.getD_some] using equal

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBasisReceipt ====

-- ==== begin CRTFastField ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Field Matrix

/-- Once the slot is known, only one group of scalar terms can contribute. -/
def fastScalar (p : Nat) (mir : Bool) (slot : Nat) (data : Nat → Nat) (q : Nat) : Nat :=
  if 1 ≤ slot ∧ slot ≤ 16 then
    let d := fieldDegree p
    (selected d (rowMask p mir q >>> ((slot-1)*d))).foldl (fun a j => a ^^^ data j) (data q)
  else data q

private theorem zeros (n a : Nat) : (List.replicate n 0).foldl Nat.xor a = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,List.foldl_cons,show Nat.xor a 0 = a from Nat.xor_zero a,ih]

theorem scalar_fast (p : Nat) (mir : Bool) (slot : Nat) (data : Nat → Nat) (q : Nat) :
    scalarRow p mir (fun k => decide (slot = k+1)) data q = fastScalar p mir slot data q := by
  let js := fun k => selected (fieldDegree p) (rowMask p mir q >>> (k*fieldDegree p))
  have all (ks : List Nat) (nd : ks.Nodup) (a : Nat) :
      (ks.flatMap (fun k => (js k).map fun j => if decide (slot=k+1) then data j else 0)).foldl Nat.xor a =
      if 1 ≤ slot ∧ slot-1 ∈ ks then (js (slot-1)).foldl (fun v j => v ^^^ data j) a else a := by
    induction ks generalizing a with
    | nil => simp
    | cons k ks ih =>
      rw [List.flatMap_cons,List.foldl_append,ih (List.nodup_cons.mp nd).2]
      by_cases eq : slot = k+1
      · subst slot
        simp [List.nodup_cons.mp nd,List.foldl_map]
        rfl
      · have no : 1 ≤ slot → slot-1 ≠ k := by omega
        by_cases low : 1 ≤ slot <;> simp [eq,low,no,zeros]
  unfold scalarRow accumulate fastScalar
  change _ = if 1 ≤ slot ∧ slot ≤ 16 then (js (slot-1)).foldl _ (data q) else data q
  rw [all (List.range 16) List.nodup_range]
  simp only [List.mem_range]
  by_cases valid : 1 ≤ slot ∧ slot ≤ 16
  · rw [if_pos valid,if_pos (by omega)]
  · rw [if_neg valid,if_neg (by omega)]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTFastField ====

-- ==== begin CRTPackedActions ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix Field

def pack (w : Nat) : List Nat → Nat
  | [] => 0
  | a::xs => a + 2^w * pack w xs

def codedWord (n dim k : Nat) := pack width (coded n dim k).toList

def put (x q value : Nat) := x ^^^ ((digit width x q ^^^ value) <<< (width*q))

def replace (x : Nat) (indices : List Nat) (value : Nat → Nat) := indices.foldl (fun acc q => put acc q (value q)) x

def scalarWord (x p : Nat) (mir : Bool) (slot off : Nat) : Nat :=
  let d := fieldDegree p
  let localData := fun j => digit width x (off+j)
  replace x ((List.range d).map (off+·)) (fun q => fastScalar p mir slot localData (q-off))

def cxWord (x : Nat) (op : Wire × Wire) := x ^^^ (digit width x op.1 <<< (width*op.2))

def stageWord (n x slot off d m h : Nat) (mir : Bool) :=
  if m ≤ 2^h then x else if enabled n slot h then (oriented mir (editPairs off d m h)).foldl cxWord x else x

def r8StepWord (n x slot off : Nat) (st : R8Step) : Nat :=
  if r8Enabled n slot st.tags then (r8Ops off st).foldl cxWord x else x

def primaryWord (n x off p m slot : Nat) (mir : Bool) :=
  let d := fieldDegree p
  let scalar := (List.range m).foldl (fun a j => scalarWord a p mir slot (off+d*j)) x
  if d == 8 && m == 2 then (pascalR8Steps mir).foldl (fun a st => r8StepWord n a slot off st) scalar
  else (oriented mir (List.range 4)).foldl (fun a h => stageWord n a slot off d m h mir) scalar

def componentWord (n : Nat) (mir : Bool) (slot : Nat) : Nat → List (Nat × Nat) → Nat → Nat
  | _, [], x => x
  | off, (p,m)::ps, x => componentWord n mir slot (off+fieldDegree p*m) ps (primaryWord n x off p m slot mir)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPackedActions ====

-- ==== begin CRTPrototype ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix

def prototype : Nat → Rows
  | 11 => #[19891781826937379155528292012389348046057, 26751016939674406450538047878730502544698, 9945890913468689577764146006194674023028, 14335269661968236889415737841593606611112, 3583817415492059222353934460398401652778, 2778256082484571133056277085397870717472]
  | 13 => #[15776240759295162778522438492584655346873, 31552481518590325557044876985169310693746, 7888120379647581389261219246292327673436, 14303366242839227460136622698029229148328, 2945749032911870636771631589110852397090, 736437258227967659192907897277713099272]
  | 19 => #[40006995905761713665020287229952780727697, 10445392358955229623541529622652388974258, 20890784717910459247083059245304777948516, 41781569435820918494166118490609555897032]
  | 21 => #[6913673486647638622747928531947036677201, 13827346973295277245495857063894073354402, 23506489854601971317342957008619924702484, 3456836743323819311373964265973518338600]
  | 25 => #[9167965271024970566755654085954890144497, 18335930542049941133511308171909780288994, 36671861084099882267022616343819560577988, 26362054118452546945033801918610610605432]
  | 31 => #[23885626787740712790203327282952504133169, 25290663657607813542568228887832063199826, 28100737397342015047298032097591181333140, 33720884876810418056757638517109417599768, 723806872355779175460706887362197094944, 3406149987556607884520973587586809858562, 851537496889151971130243396896702464640, 11580909957692466807371310197795153519112]
  | 37 => #[27932194474876813705862654941247809506593, 12308245983873504088413360131229287946818, 8936042180094617128646825586564267571620, 17872084360189234257293651173128535143240, 35744168720378468514587302346257070286480]
  | 41 => #[36094934679621090185235730441252256902817, 28633726393362057047159511131238182739266, 13711309820843990771007072511210034412164, 19912769411375303377136920048129646992296, 39825538822750606754273840096259293984592]
  | 47 => #[30658970243285579744134829468376532194721, 37488565857482452575888569478124830015202, 2147662105671554075591347169113162475620, 29442814043761456597689682242727298581864, 15329485121642789872067414734188266097360]
  | 55 => #[26577339978445334316881955795361126411489, 27966559955322353983857018769224893216034, 36162927218825386740466089659602859951780, 28769711471770650157620229567939388837192, 35066741472162728820096952773313728738928]
  | 59 => #[29302661214131106759681126940329769575777, 41564138030242591077700874207736609271714, 39572133094605058832089798664206887477060, 21280070249030678600253205989750735084520, 14651330607065553379840563470164884787888]
  | 61 => #[12960823162984049230176067084423683502689, 25921646325968098460352134168847367005378, 21198763180058997619339976184866689137636, 30815457268108921413459970064887262578088, 6480411581492024615088033542211841751344]
  | 67 => #[5612898168739760699118325677947147851841, 16508956679978163768089428834160722520258, 33017913359956327536178857668321445040516, 22479683754032531749045765585376559014664, 1403224542184940174779581419486786962960, 2806449084369880349559162838973573925920]
  | 73 => #[5540409574916258348366490672861666378305, 11080819149832516696732981345723332756610, 22161638299665033393465962691446665513220, 6137069067599547708959805053015999680584, 12274138135199095417919610106031999361168, 24548276270398190835839220212063998722336]
  | 87 => #[27362919031636673446739759945993092909377, 38359814407180529648487051612759219067842, 16712370790895707898330997585915954495172, 33424741581791415796661995171831908990344, 6840729757909168361684939986498273227344, 13681459515818336723369879972996546454688]
  | 91 => #[27372219399588054867180962274776991481665, 38305291753722314268414382140296848687554, 33054440541564505213516814529327366308740, 6197333074470603536525635454041888143432, 39510162074307106209279202882143996170192, 35464181182734089095246456013021661274016]
  | 97 => #[38200792174768201734171875260307186560961, 32845441383656280145031800769348042055554, 22134739801432436966751651787429753044740, 713336636984750610191353823593175023112, 1426673273969501220382707647186350046224, 40878467570324162528741912505786758813664]
  | 103 => #[38258357778774199124717167290533158753217, 5681976867193784513574609413500699653186, 27577712907874688609168381682885250644804, 11599282849869253895024813614504170223240, 23198565699738507790049627229008340446480, 40907250372327161224014558520899744909792]
  | 109 => #[38238675932949108488738639650430836089281, 32921208900018093654165329549595341112194, 16718705178551462680998185954322089879236, 6162425061542662956099276761555451669576, 12324850123085325912198553523110903339152, 19119337966474554244369319825215418044640]
  | 115 => #[16494610391059644869125081907946136850113, 27408010022837731364564513908734468641602, 11259877079795339405817078066202606216836, 22519754159590678811634156132405212433672, 17741038247179463671969115915000199926992, 30025376678469884096218515829606233958240]
  | 117 => #[16443077378215551972977953031434699092673, 32886154756431103945955906062869398185346, 38489061122212814880900440187688792750532, 33421979278545506438488930624111254434696, 39554728637608372533982710439920260797904, 29999610172047837648144951391350515079520]
  | 257 => #[43556142965880123323311949751266331066367, 14518714321960041107770649917088777022122, 26133685779528073993987169850759798639820, 2903742864392008221554129983417755404424, 38431890852247167638216426251117350940912, 11102546246204737317706967583656123605152, 22034284088621709445910751050640614539456, 170808403787765189503184116671632670848, 338958311018522360492699998064329424640, 225972207345681573661799998709552949760, 271166648814817888394159998451463539712, 180777765876545258929439998967642359808, 319019586840962221640188233472310046720, 212679724560641481093458822314873364480, 255215669472769777312150586777848037376, 170143779648513184874767057851898691584]
  | 313 => #[20587904885963616363440185356714713970945, 41175809771927232726880370713429427941890, 38795476577974342130448791675592524817412, 30120868495474515782654579864382903267592, 4604813216334664944122908100978077145872, 13462523852215482876258010607405922012960, 26925047704430965752516021214811844025920, 10293952442981808181720092678357356985472]
  | 471 => #[12761683044446859915504946222260308626177, 37603149969025162811728073319071680421122, 41006996528519712355110547713119341834500, 38457850091159301386909145674972352602632, 24341008765972543683850384107703124397840, 5125874566064964044388818464139917729312, 20289823233726321533760005767584502871872, 28158913005163491619408447986763319846272]
  | _ => #[]

def prototypeWord (p m dim k : Nat) : Nat :=
  pack width (((prototype p).toList.take (fieldDegree p*m)).map (clipShift dim k))

def prototypeTest (p m slot : Nat) (mir : Bool) : Bool :=
  let dim := 135 - (slot - 1)
  primaryWord (fieldDegree p*m) (prototypeWord p m dim (entryShift mir slot)) 0 p m slot mir ==
    prototypeWord p m dim (exitShift mir slot)

def UsedPrimary (p m : Nat) : Prop :=
  p = 11 ∧ m = 1 ∨ p = 11 ∧ m = 2 ∨ p = 13 ∧ m = 1 ∨ p = 13 ∧ m = 2 ∨ p = 19 ∧ m = 1 ∨ p = 21 ∧ m = 1 ∨ p = 25 ∧ m = 1 ∨ p = 31 ∧ m = 1 ∨ p = 31 ∧ m = 2 ∨ p = 37 ∧ m = 1 ∨ p = 41 ∧ m = 1 ∨ p = 47 ∧ m = 1 ∨ p = 55 ∧ m = 1 ∨ p = 59 ∧ m = 1 ∨ p = 61 ∧ m = 1 ∨ p = 67 ∧ m = 1 ∨ p = 73 ∧ m = 1 ∨ p = 87 ∧ m = 1 ∨ p = 91 ∧ m = 1 ∨ p = 97 ∧ m = 1 ∨ p = 103 ∧ m = 1 ∨ p = 109 ∧ m = 1 ∨ p = 115 ∧ m = 1 ∨ p = 117 ∧ m = 1 ∨ p = 257 ∧ m = 1 ∨ p = 257 ∧ m = 2 ∨ p = 313 ∧ m = 1 ∨ p = 471 ∧ m = 1

set_option synthInstance.maxSize 1024 in
instance (p m : Nat) : Decidable (UsedPrimary p m) := by unfold UsedPrimary; infer_instance

def tableOK (n : Nat) : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | off, (p,m)::ps => decide (UsedPrimary p m) &&
      (List.range (fieldDegree p*m)).all (fun j =>
        Matrix.read (encoded n) (off+j) == (Matrix.read (prototype p) j &&& (2^n-1))) &&
      tableOK n (off+fieldDegree p*m) ps

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPrototype ====

-- ==== begin CRTPrototypeReceipt ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

private theorem p11m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 11 1 s.val b = true := by decide +kernel

private theorem p11m2 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 11 2 s.val b = true := by decide +kernel

private theorem p13m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 13 1 s.val b = true := by decide +kernel

private theorem p13m2 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 13 2 s.val b = true := by decide +kernel

private theorem p19m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 19 1 s.val b = true := by decide +kernel

private theorem p21m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 21 1 s.val b = true := by decide +kernel

private theorem p25m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 25 1 s.val b = true := by decide +kernel

private theorem p31m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 31 1 s.val b = true := by decide +kernel

private theorem p31m2 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 31 2 s.val b = true := by decide +kernel

private theorem p37m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 37 1 s.val b = true := by decide +kernel

private theorem p41m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 41 1 s.val b = true := by decide +kernel

private theorem p47m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 47 1 s.val b = true := by decide +kernel

private theorem p55m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 55 1 s.val b = true := by decide +kernel

private theorem p59m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 59 1 s.val b = true := by decide +kernel

private theorem p61m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 61 1 s.val b = true := by decide +kernel

private theorem p67m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 67 1 s.val b = true := by decide +kernel

private theorem p73m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 73 1 s.val b = true := by decide +kernel

private theorem p87m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 87 1 s.val b = true := by decide +kernel

private theorem p91m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 91 1 s.val b = true := by decide +kernel

private theorem p97m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 97 1 s.val b = true := by decide +kernel

private theorem p103m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 103 1 s.val b = true := by decide +kernel

private theorem p109m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 109 1 s.val b = true := by decide +kernel

private theorem p115m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 115 1 s.val b = true := by decide +kernel

private theorem p117m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 117 1 s.val b = true := by decide +kernel

private theorem p257m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 257 1 s.val b = true := by decide +kernel

private theorem p257m2 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 257 2 s.val b = true := by decide +kernel
private theorem p313m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 313 1 s.val b = true := by decide +kernel
private theorem p471m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 471 1 s.val b = true := by decide +kernel

theorem prototype_checked (p m : Nat) (hm : UsedPrimary p m) (slot : Fin 17) (mir : Bool) :
    prototypeTest p m slot.val mir = true := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact p11m1 slot mir
  · exact p11m2 slot mir
  · exact p13m1 slot mir
  · exact p13m2 slot mir
  · exact p19m1 slot mir
  · exact p21m1 slot mir
  · exact p25m1 slot mir
  · exact p31m1 slot mir
  · exact p31m2 slot mir
  · exact p37m1 slot mir
  · exact p41m1 slot mir
  · exact p47m1 slot mir
  · exact p55m1 slot mir
  · exact p59m1 slot mir
  · exact p61m1 slot mir
  · exact p67m1 slot mir
  · exact p73m1 slot mir
  · exact p87m1 slot mir
  · exact p91m1 slot mir
  · exact p97m1 slot mir
  · exact p103m1 slot mir
  · exact p109m1 slot mir
  · exact p115m1 slot mir
  · exact p117m1 slot mir
  · exact p257m1 slot mir
  · exact p257m2 slot mir
  · exact p313m1 slot mir
  · exact p471m1 slot mir

theorem prototype_size (p m : Nat) (hm : UsedPrimary p m) : fieldDegree p*m ≤ (prototype p).size := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel

theorem table_checked (n : Nat) (hn : UsedWidth n) : 15 ≤ n ∧ n ≤ 135 ∧ tableOK n 0 (schedule n) = true := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPrototypeReceipt ====

-- ==== begin CRTPackedRun ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix Placement Field

theorem digit_pack (xs : List Nat) (q : Nat) (hq : q < xs.length)
    (bound : ∀ v ∈ xs, v < 2^width) : digit width (pack width xs) q = (xs[q]?).getD 0 := by
  induction xs generalizing q with
  | nil => simp at hq
  | cons a xs ih =>
    rw [pack]
    have low := bound a (List.mem_cons_self ..)
    cases q with
    | zero => exact digit_zero _ _ _ low
    | succ q =>
      rw [digit_succ _ _ _ _ low]
      apply ih _ (by simpa using hq) (fun v hv => bound v (List.mem_cons_of_mem _ hv))

theorem coded_matches (n dim k : Nat) (hd : dim ≤ width) : Matches (codedWord n dim k) (coded n dim k) := by
  have bound : ∀ v ∈ (coded n dim k).toList, v < 2^width := by
    intro v hv
    simp only [coded,Array.toList_map,List.mem_map] at hv
    obtain ⟨a,_,rfl⟩ := hv
    exact lt_of_le_of_lt Nat.and_le_right (lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by decide : 0<1))
      (Nat.pow_le_pow_right (by decide) hd))
  intro q hq
  simpa only [codedWord,Matrix.read,Array.getElem?_toList] using
    (digit_pack (coded n dim k).toList q (by simpa using hq) bound).symm

theorem digit_put (x i q v : Nat) (hv : v < 2^width) : digit width (put x i v) q =
    if q = i then v else digit width x q := by
  rw [put,digit_xor,digit_single _ _ _ _ (Nat.xor_lt_two_pow (digit_bound ..) hv)]
  by_cases e : q=i <;> simp [e]

private theorem digit_replace (x q : Nat) (xs : List Nat) (v : Nat → Nat) (bound : ∀ j ∈ xs, v j < 2^width) :
    digit width (replace x xs v) q = if q ∈ xs then v q else digit width x q := by
  induction xs generalizing x with
  | nil => simp [replace]
  | cons a xs ih =>
    change digit width (replace (put x a (v a)) xs v) q = _
    rw [ih _ (fun j hj => bound j (List.mem_cons_of_mem _ hj)),digit_put _ _ _ _ (bound a (List.mem_cons_self ..))]
    by_cases ha : q=a <;> by_cases hx : q∈xs <;> simp [ha,hx]

private theorem fast_bound (p : Nat) (mir : Bool) (slot : Nat) (v : Nat → Nat) (q : Nat)
    (h : ∀ j, v j < 2^width) : fastScalar p mir slot v q < 2^width := by
  have fold (xs : List Nat) (a : Nat) (ha : a < 2^width) : xs.foldl (fun w j => w ^^^ v j) a < 2^width := by
    induction xs generalizing a with
    | nil => exact ha
    | cons j xs ih => exact ih _ (Nat.xor_lt_two_pow ha (h j))
  unfold fastScalar
  split
  · exact fold _ _ (h q)
  · exact h q

theorem digit_scalar (p : Nat) (mir : Bool) (slot off x q : Nat) :
    digit width (scalarWord x p mir slot off) q = if off ≤ q ∧ q < off+fieldDegree p then
      fastScalar p mir slot (fun j => digit width x (off+j)) (q-off) else digit width x q := by
  unfold scalarWord
  rw [digit_replace _ _ _ _ (fun j _ => fast_bound _ _ _ _ _ (fun _ => digit_bound ..))]
  have within : q ∈ (List.range (fieldDegree p)).map (off+·) ↔ off ≤ q ∧ q < off+fieldDegree p := by
    constructor
    · rintro hit
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hit
      exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (List.mem_range.mp hj) _⟩
    · rintro ⟨lo,hi⟩
      exact List.mem_map.mpr ⟨q-off,List.mem_range.mpr ((Nat.sub_lt_iff_lt_add lo).mpr (Nat.add_comm off _ ▸ hi)),Nat.add_sub_of_le lo⟩
  simp only [within]

theorem digit_cx (x a b q : Nat) : digit width (cxWord x (a,b)) q =
    if q = b then digit width x q ^^^ digit width x a else digit width x q := by
  rw [cxWord,digit_xor,digit_single _ _ _ _ (digit_bound ..)]
  by_cases eq : q = b <;> simp [eq]

private theorem scalar_matches (p : Nat) (mir : Bool) (slot off x : Nat) (r : Rows)
    (endp : off+fieldDegree p ≤ r.size) (h : Matches x r) :
    Matches (scalarWord x p mir slot off) (scalarRows r p mir slot off) := by
  intro q hq
  have sq : q < r.size := by simpa only [scalarRows_size] using hq
  let d := fieldDegree p
  let data := fun j => digit width x (off+j)
  let v := fun t => fastScalar p mir slot data (t-off)
  let xs := (List.range d).map (off+·)
  change Matrix.read (scalarRows r p mir slot off) q = digit width (replace x xs v) q
  rw [scalar_read sq,digit_replace _ _ _ _ (fun j _ => fast_bound _ _ _ _ _ (fun _ => digit_bound ..))]
  have loc : q ∈ xs ↔ off ≤ q ∧ q < off+fieldDegree p := by
    constructor
    · rintro hq
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
      exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (List.mem_range.mp hj) _⟩
    · rintro ⟨lo,hi⟩
      exact List.mem_map.mpr ⟨q-off,List.mem_range.mpr ((Nat.sub_lt_iff_lt_add lo).mpr (Nat.add_comm off d ▸ hi)),Nat.add_sub_of_le lo⟩
  simp only [loc]
  split
  · rename_i live
    have jBound : q-off < d := (Nat.sub_lt_iff_lt_add live.1).mpr (Nat.add_comm off d ▸ live.2)
    change scalarRow p mir _ _ _ = fastScalar p mir slot data (q-off)
    rw [←scalar_fast]
    apply accumulate_congr
    · exact h _ (lt_of_lt_of_le (Nat.add_lt_add_left jBound _) endp)
    · intro k j hj
      dsimp only
      rw [show Matrix.read r (off+j) = data j from h _ (lt_of_lt_of_le (Nat.add_lt_add_left hj _) endp)]
  · exact h q sq

private theorem cx_matches (x : Nat) (r : Rows) (p : Wire × Wire) (ha : p.1 < r.size) (hb : p.2 < r.size)
    (h : Matches x r) : Matches (cxWord x p) (applyPair r p) := by
  obtain ⟨a,b⟩ := p
  intro q hq
  have sq : q < r.size := by simpa only [applyPair_size] using hq
  rw [apply_read _ _ _ _ hb,cxWord,digit_xor,digit_single _ _ _ _ (digit_bound ..)]
  by_cases eq : q=b <;> simp [eq,h q sq,h a ha,h b hb]

private theorem fold_matches {α} (xs : List α) (f : Nat → α → Nat) (g : Rows → α → Rows) (n x : Nat) (r : Rows)
    (size : r.size=n) (h : Matches x r) (keep : ∀ r a, (g r a).size = r.size)
    (step : ∀ a∈xs, ∀ x r, r.size = n → Matches x r → Matches (f x a) (g r a)) :
    Matches (xs.foldl f x) (xs.foldl g r) := by
  induction xs generalizing x r with
  | nil => exact h
  | cons a xs ih =>
    exact ih _ _ ((keep r a).trans size) (step a (List.mem_cons_self ..) x r size h)
      (fun b hb => step b (List.mem_cons_of_mem _ hb))

private theorem stage_matches (n x slot off d m h : Nat) (mir : Bool) (r : Rows) (size : r.size=n)
    (endp : off+d*m ≤ n) (agree : Matches x r) :
    Matches (stageWord n x slot off d m h mir) (stageRows r slot off d m h mir) := by
  unfold stageWord stageRows
  rw [size]
  by_cases short : m ≤ 2^h
  · simpa only [if_pos short] using agree
  · simp only [if_neg short]
    split
    · apply fold_matches _ _ applyPair n _ _ size agree (fun _ _ => applyPair_size ..)
      intro p hp z a sz matcha
      obtain ⟨ha,hb⟩ := edit_bounds a off d m h mir (sz ▸ endp) p hp
      exact cx_matches z a p ha hb matcha
    · exact agree

private theorem r8Step_matches (n x slot off : Nat) (st : R8Step) (hg : r8StepGood st = true)
    (r : Rows) (size : r.size = n) (endp : off + 16 ≤ n) (agree : Matches x r) :
    Matches (r8StepWord n x slot off st) (r8StepRows r slot off st) := by
  unfold r8StepWord r8StepRows
  rw [size]
  split
  · apply fold_matches _ _ applyPair n _ _ size agree (fun _ _ => applyPair_size ..)
    intro p hp z a sz matcha
    obtain ⟨ha, hb, _⟩ := r8Ops_bounds a off st hg (sz ▸ endp) p hp
    exact cx_matches z a p ha hb matcha
  · exact agree

private theorem primary_matches (n x off p m slot : Nat) (mir : Bool) (r : Rows) (size : r.size=n)
    (endp : off+fieldDegree p*m ≤ n) (agree : Matches x r) :
    Matches (primaryWord n x off p m slot mir) (primaryRows r off p m slot mir) := by
  let d := fieldDegree p
  have scalar := fold_matches (List.range m) (fun a j => scalarWord a p mir slot (off+d*j))
    (fun a j => scalarRows a p mir slot (off+d*j)) n _ _ size agree (fun _ _ => scalarRows_size ..) (by
      intro j hj z a sz matcha
      have kj := Nat.mul_le_mul_left (fieldDegree p) (show j+1 ≤ m from List.mem_range.mp hj)
      rw [Nat.mul_succ] at kj
      exact scalar_matches p mir slot _ _ a (by dsimp [d]; rw [sz]; omega) matcha)
  unfold primaryWord primaryRows; dsimp only
  by_cases h82 : (fieldDegree p == 8 && m == 2) = true
  · have h82' := h82; simp only [Bool.and_eq_true, beq_iff_eq] at h82'
    have h16 : fieldDegree p * m = 16 := by rw [h82'.1, h82'.2]
    rw [if_pos h82, if_pos h82]
    unfold r8Rows
    apply fold_matches (pascalR8Steps mir) (fun a st => r8StepWord n a slot off st)
      (fun a st => r8StepRows a slot off st) n _ (scalars r p m off slot mir) ((scalars_size ..).trans size) scalar
      (fun _ _ => r8StepRows_size ..)
    exact fun st hst z a sz ma => r8Step_matches n z slot off st (List.all_eq_true.mp (pascalR8Steps_good mir) st hst) a sz (by omega) ma
  · rw [if_neg h82, if_neg h82]
    apply fold_matches (oriented mir (List.range 4)) _ (fun a h => stageRows a slot off d m h mir)
      n _ (scalars r p m off slot mir) ((scalars_size ..).trans size) scalar (fun _ _ => stageRows_size ..)
    exact fun h _ z a sz ma => stage_matches n z slot off d m h mir a sz endp ma

private theorem components_match (n x off slot : Nat) (mir : Bool) (ps : List (Nat × Nat)) (r : Rows)
    (size : r.size=n) (endp : off+extent ps ≤ n) (agree : Matches x r) :
    Matches (componentWord n mir slot off ps x) (componentRows mir slot off ps r) := by
  induction ps generalizing x r off with
  | nil => exact agree
  | cons pair tail ih =>
    obtain ⟨p,m⟩ := pair
    change off+(fieldDegree p*m+extent tail) ≤ n at endp
    exact ih _ _ _ ((primaryRows_size ..).trans size) (by omega)
      (primary_matches n x off p m slot mir r size (by omega) agree)

theorem action_of_digits (n slot : Nat) (hn : UsedWidth n) (bound : n ≤ width) (mir : Bool)
    (tested : ∀ q < n, digit width (componentWord n mir slot 0 (schedule n) (codedWord n (n-(slot-1)) (entryShift mir slot))) q =
      digit width (codedWord n (n-(slot-1)) (exitShift mir slot)) q) : ActionOK n slot mir := by
  let dim := n - (slot - 1)
  have hdim : dim ≤ width := by omega
  have src (k : Nat) : (coded n dim k).size = n := by
    rw [←encode_of_receipt n dim k (coordinates_checked n hn),applyOps_size,plain_size]
  let input := coded n dim (entryShift mir slot)
  let out := componentRows mir slot 0 (schedule n) input
  have exactRun : Matches (componentWord n mir slot 0 (schedule n) (codedWord n dim (entryShift mir slot))) out :=
    components_match n _ 0 slot mir (schedule n) input (src _) (by rw [schedule_extent n hn]; omega)
      (coded_matches n dim _ hdim)
  have outSize : out.size = n := (componentRows_size ..).trans (src _)
  change out = coded n dim (exitShift mir slot)
  apply Array.ext (outSize.trans (src _).symm)
  intro q ho he
  have result := (exactRun q ho).trans ((tested q (outSize ▸ ho)).trans (coded_matches n dim _ hdim q he).symm)
  simpa only [Matrix.read,Array.getElem?_eq_getElem ho,Array.getElem?_eq_getElem he,Option.getD_some] using result

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPackedRun ====

-- ==== begin CRTSlice ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix Field

structure Slice (f : Nat → Nat) (off len original bank block : Nat) : Prop where
  same : ∀ i < len, digit width bank (off+i) = f (digit width block i)
  exterior : ∀ q, (q < off ∨ off+len ≤ q) → digit width bank q = digit width original q

private theorem scalar_linear (p : Nat) (mir : Bool) (slot i : Nat) (hi : i < fieldDegree p) (f : Nat → Nat)
    (fz : f 0 = 0) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (u v : Nat → Nat)
    (rel : ∀ j < fieldDegree p, u j = f (v j)) :
    fastScalar p mir slot u i = f (fastScalar p mir slot v i) := by
  rw [←scalar_fast,←scalar_fast]
  unfold scalarRow
  rw [map_accumulate p mir i f Nat.xor Nat.xor fx]
  apply accumulate_congr
  · exact rel i hi
  · intro k j hj
    by_cases hot : slot=k+1
    · simpa [hot] using rel j hj
    · simpa [hot] using fz.symm

theorem slice_scalar (p : Nat) (mir : Bool) (slot off len j original bank block : Nat) (f : Nat → Nat)
    (fz : f 0 = 0) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (endp : j+fieldDegree p ≤ len)
    (h : Slice f off len original bank block) :
    Slice f off len original (scalarWord bank p mir slot (off+j)) (scalarWord block p mir slot j) := by
  constructor
  · intro t ht
    rw [digit_scalar,digit_scalar]
    by_cases inside : j ≤ t ∧ t < j+fieldDegree p
    · have outer : off+j ≤ off+t ∧ off+t < off+j+fieldDegree p := by omega
      rw [if_pos outer, if_pos inside, show off+t-(off+j)=t-j by omega]
      apply scalar_linear _ _ _ _ ((Nat.sub_lt_iff_lt_add inside.1).mpr (Nat.add_comm j _ ▸ inside.2)) f fz fx
      intro z hz
      rw [Nat.add_assoc]
      exact h.same _ (by omega)
    · rw [if_neg inside, if_neg (show ¬(off+j ≤ off+t ∧ off+t < off+j+fieldDegree p) by omega)]
      exact h.same t ht
  · intro q exterior
    rw [digit_scalar,if_neg (by omega)]
    exact h.exterior q exterior

private theorem slice_cx (f : Nat → Nat) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (off len original bank block a b : Nat) (ha : a < len) (hb : b < len)
    (h : Slice f off len original bank block) :
    Slice f off len original (cxWord bank (off+a,off+b)) (cxWord block (a,b)) := by
  constructor
  · intro q hq
    rw [digit_cx,digit_cx]
    by_cases eq : q=b <;> simp [eq,h.same _ hq,h.same a ha,h.same b hb,fx]
  · intro q external
    rw [digit_cx,if_neg (by omega)]
    exact h.exterior q external

private theorem parity_map (xs : List Nat) (n s : Nat) :
    xorAt (flags n s) (xs.map (n+·)) = xorAt (fun k => decide (k<16 ∧ s=k+1)) xs := by
  induction xs with
  | nil => rfl
  | cons k xs ih => simp [xorAt,ih,flags]

theorem enabled_same (n m slot h : Nat) : enabled n slot h = enabled m slot h := by
  simp only [enabled,tagSources,parity_map]

private theorem shift_edits (off d m h : Nat) : editPairs off d m h =
    (editPairs 0 d m h).map (fun (a,b) => (off+a,off+b)) := by
  simp [editPairs,List.map_flatMap,List.map_map,Function.comp_def,Nat.add_assoc]

private theorem slice_stage (f : Nat → Nat) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (n off d m original bank block slot h : Nat) (mir : Bool) (prev : Slice f off (d*m) original bank block) :
    Slice f off (d*m) original (stageWord n bank slot off d m h mir) (stageWord (d*m) block slot 0 d m h mir) := by
  unfold stageWord
  rw [enabled_same n (d*m)]
  by_cases small : m ≤ 2^h
  · simpa only [if_pos small] using prev
  simp only [if_neg small]
  split
  · let ops := oriented mir (editPairs 0 d m h)
    have bounds : ∀ p ∈ ops, p.1 < d*m ∧ p.2 < d*m := by
      intro p hp
      simpa only [units,Array.size_ofFn] using edit_bounds (units (d*m)) 0 d m h mir (by simp [units]) p hp
    have shape : oriented mir (editPairs off d m h) = ops.map (fun (a,b) => (off+a,off+b)) := by
      rw [shift_edits]
      cases mir <;> simp [oriented,ops]
    rw [shape,List.foldl_map]
    change Slice f off (d*m) original (ops.foldl _ bank) (ops.foldl _ block)
    have run (xs : List (Nat × Nat)) (z t : Nat) (hz : Slice f off (d*m) original z t)
        (loc : ∀ e ∈ xs, e.1 < d*m ∧ e.2 < d*m) :
        Slice f off (d*m) original (xs.foldl (fun acc e => cxWord acc (off+e.1,off+e.2)) z) (xs.foldl cxWord t) := by
      induction xs generalizing z t with
      | nil => exact hz
      | cons e xs ih =>
        obtain ⟨a,b⟩ := e
        obtain ⟨ha,hb⟩ := loc (a,b) (List.mem_cons_self ..)
        exact ih _ _ (slice_cx f fx off _ original z t a b ha hb hz)
          (fun w hw => loc w (List.mem_cons_of_mem _ hw))
    exact run ops bank block prev bounds
  · exact prev

theorem r8Enabled_same (n m slot : Nat) (tags : List Nat) : r8Enabled n slot tags = r8Enabled m slot tags := by
  simp only [r8Enabled, parity_map]

private theorem shift_r8Ops (off : Nat) (st : R8Step) :
    r8Ops off st = (r8Ops 0 st).map (fun (a,b) => (off+a, off+b)) := by
  simp [r8Ops, List.map_append, List.map_reverse]

private theorem slice_r8Step (f : Nat → Nat) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (n off original bank block slot : Nat) (st : R8Step) (hg : Placement.r8StepGood st = true)
    (prev : Slice f off 16 original bank block) :
    Slice f off 16 original (r8StepWord n bank slot off st) (r8StepWord 16 block slot 0 st) := by
  unfold r8StepWord
  rw [r8Enabled_same n 16]
  split
  · have bounds : ∀ p ∈ r8Ops 0 st, p.1 < 16 ∧ p.2 < 16 := by
      intro p hp
      obtain ⟨h1, h2, _⟩ := r8Ops_bounds (units 16) 0 st hg (by simp [units]) p hp
      simpa [units] using And.intro h1 h2
    rw [shift_r8Ops, List.foldl_map]
    have run (xs : List (Nat × Nat)) (z t : Nat) (hz : Slice f off 16 original z t)
        (loc : ∀ e ∈ xs, e.1 < 16 ∧ e.2 < 16) :
        Slice f off 16 original (xs.foldl (fun acc e => cxWord acc (off+e.1,off+e.2)) z) (xs.foldl cxWord t) := by
      induction xs generalizing z t with
      | nil => exact hz
      | cons e xs ih =>
        obtain ⟨a,b⟩ := e
        obtain ⟨ha,hb⟩ := loc (a,b) (List.mem_cons_self ..)
        exact ih _ _ (slice_cx f fx off 16 original z t a b ha hb hz)
          (fun w hw => loc w (List.mem_cons_of_mem _ hw))
    exact run (r8Ops 0 st) bank block prev bounds
  · exact prev

theorem primary_slice (f : Nat → Nat) (fz : f 0 = 0) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (n off p m slot original bank block : Nat) (mir : Bool) (prev : Slice f off (fieldDegree p*m) original bank block) :
    Slice f off (fieldDegree p*m) original (primaryWord n bank off p m slot mir)
      (primaryWord (fieldDegree p*m) block 0 p m slot mir) := by
  let d := fieldDegree p
  have fold {α} (xs : List α) (g u : Nat → α → Nat) (b l : Nat) (rel : Slice f off (d*m) original b l)
      (one : ∀ a ∈ xs, ∀ b l, Slice f off (d*m) original b l → Slice f off (d*m) original (g b a) (u l a)) :
      Slice f off (d*m) original (xs.foldl g b) (xs.foldl u l) := by
    induction xs generalizing b l with
    | nil => exact rel
    | cons a xs ih => exact ih _ _ (one a (List.mem_cons_self ..) b l rel) (fun z hz => one z (List.mem_cons_of_mem _ hz))
  have sc : Slice f off (d*m) original
      ((List.range m).foldl (fun a j => scalarWord a p mir slot (off+d*j)) bank)
      ((List.range m).foldl (fun a j => scalarWord a p mir slot (0+d*j)) block) := by
    apply fold _ _ _ _ _ prev
    intro j hj b l carry
    have h := Nat.mul_le_mul_left d (show j+1 ≤ m from List.mem_range.mp hj)
    rw [Nat.mul_succ] at h
    simpa only [Nat.zero_add] using slice_scalar p mir slot off (d*m) (d*j) original b l f fz fx h carry
  unfold primaryWord; dsimp only
  by_cases h82 : (fieldDegree p == 8 && m == 2) = true
  · have h82' := h82; simp only [Bool.and_eq_true, beq_iff_eq] at h82'
    have h16 : d * m = 16 := by change fieldDegree p * m = 16; rw [h82'.1, h82'.2]
    rw [if_pos h82, if_pos h82]
    apply fold (pascalR8Steps mir) (fun a st => r8StepWord n a slot off st)
      (fun a st => r8StepWord (d*m) a slot 0 st) _ _ sc
    intro st hst b l carry
    rw [h16] at carry ⊢
    exact slice_r8Step f fx n off original b l slot st (List.all_eq_true.mp (Placement.pascalR8Steps_good mir) st hst) carry
  · rw [if_neg h82, if_neg h82]
    apply fold _ _ _ _ _ sc
    exact fun h _ b l carry => slice_stage f fx n off d m original b l slot h mir carry

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTSlice ====

-- ==== begin CRTTemplateAction ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix Placement

private theorem prototype_digit (p m dim k : Nat) (use : UsedPrimary p m) (hd : dim ≤ width) (q : Nat) (hq : q < fieldDegree p*m) :
    digit width (prototypeWord p m dim k) q = clipShift dim k (Matrix.read (prototype p) q) := by
  let xs := ((prototype p).toList.take (fieldDegree p*m)).map (clipShift dim k)
  have bound : ∀ a ∈ xs, a < 2^width := by
    intro a ha
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
    exact lt_of_le_of_lt Nat.and_le_right (lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by decide : 0<1))
      (Nat.pow_le_pow_right (by decide) hd))
  have len : xs.length = fieldDegree p*m := by simp [xs,Nat.min_eq_left (prototype_size p m use)]
  have h := digit_pack xs q (len ▸ hq) bound
  have inList : q < (prototype p).size := lt_of_lt_of_le hq (prototype_size p m use)
  simpa [xs,prototypeWord,Matrix.read,List.getElem?_map,List.getElem?_take,hq,inList] using h

private theorem clip_factor (n sh k v : Nat) (high : n ≤ 135) (hk : k ≤ sh) :
    clipShift (n-sh) k (v &&& (2^n-1)) = clipShift (n-sh) 0 (clipShift (135-sh) k v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [clipShift,Nat.testBit_and,Nat.testBit_two_pow_sub_one,Nat.testBit_shiftRight, Nat.zero_add]
  by_cases h : i < n-sh
  · simp [h,show k+i<n by omega,show i<135-sh by omega]
  · simp [h]

private theorem shift_le_slot (mir : Bool) (slot : Fin 17) :
    entryShift mir slot.val ≤ slot.val - 1 ∧ exitShift mir slot.val ≤ slot.val - 1 := by
  cases mir <;> simp [entryShift,exitShift]

private theorem digits_source (n sh off p m k : Nat) (use : UsedPrimary p m) (high : n ≤ 135)
    (sk : k ≤ sh) (size : (coded n (n-sh) k).size = n) (endp : off+fieldDegree p*m ≤ n)
    (table : ∀ j < fieldDegree p*m, Matrix.read (encoded n) (off+j) = (Matrix.read (prototype p) j &&& (2^n-1))) :
    ∀ j < fieldDegree p*m, digit width (codedWord n (n-sh) k) (off+j) = clipShift (n-sh) 0 (digit width (prototypeWord p m (135-sh) k) j) := by
  intro j hj
  have inner : off+j < n := by omega
  have sz : (encoded n).size = n := by simpa only [coded, Array.size_map] using size
  have h := (coded_matches n (n-sh) k (by unfold width; omega) (off+j) (by rwa [size])).symm
  rw [h,prototype_digit p m (135-sh) k use (by unfold width; omega) j hj]
  have readMap : Matrix.read (coded n (n-sh) k) (off+j) = clipShift (n-sh) k (Matrix.read (encoded n) (off+j)) := by
    simp [Matrix.read,coded,show off+j < (encoded n).size by rwa [sz]]
  rw [readMap,table j hj,clip_factor n sh k _ high sk]

theorem template_action (n : Nat) (hn : UsedWidth n) (slot : Fin 17) (mir : Bool) : ActionOK n slot.val mir := by
  obtain ⟨_low,high,checked⟩ := table_checked n hn
  let sh := slot.val - 1
  let dim := n - sh
  let pdim := 135 - sh
  let a := entryShift mir slot.val
  let b := exitShift mir slot.val
  let src := codedWord n dim a
  let dst := codedWord n dim b
  let crop := clipShift dim 0
  have sz (k : Nat) : (coded n dim k).size = n := by
    rw [←encode_of_receipt n dim k (coordinates_checked n hn),applyOps_size,plain_size]
  have ks := shift_le_slot mir slot
  have sweep (ps : List (Nat × Nat)) (off bank : Nat) (endp : off+extent ps = n) (hc : tableOK n off ps = true)
      (inv : ∀ q<n, digit width bank q = if q<off then digit width dst q else digit width src q) :
      ∀ q<n, digit width (componentWord n mir slot.val off ps bank) q = digit width dst q := by
    induction ps generalizing off bank with
    | nil =>
      change off+0 = n at endp
      intro q hq
      simpa only [componentWord,if_pos (show q<off by omega)] using inv q hq
    | cons pair tail ih =>
      obtain ⟨p,m⟩ := pair
      let len := fieldDegree p*m
      change off+(len+extent tail) = n at endp
      have endHead : off+len ≤ n := by omega
      simp only [tableOK,Bool.and_eq_true] at hc
      obtain ⟨⟨ok,tbl⟩,rest⟩ := hc
      have valid : UsedPrimary p m := of_decide_eq_true ok
      have rows (j : Nat) (hj : j<len) := beq_iff_eq.mp (List.all_eq_true.mp tbl j (List.mem_range.mpr hj))
      have left := digits_source n sh off p m a valid high ks.1 (sz _) endHead rows
      have right := digits_source n sh off p m b valid high ks.2 (sz _) endHead rows
      have before : Slice crop off len bank bank (prototypeWord p m pdim a) := by
        refine ⟨?_,fun _ _ => rfl⟩
        intro j hj
        rw [inv _ (by omega),if_neg (by omega)]
        exact left j hj
      have after := primary_slice crop (clip_zero dim 0) (clip_xor dim 0) n off p m slot.val bank bank _ mir before
      have expected : primaryWord len (prototypeWord p m pdim a) 0 p m slot.val mir = prototypeWord p m pdim b :=
        beq_iff_eq.mp (prototype_checked p m valid slot mir)
      rw [expected] at after
      change ∀ q<n, digit width (componentWord n mir slot.val (off+len) tail _) q = digit width dst q
      apply ih _ _ (by omega) rest
      intro q hq
      by_cases earlier : q < off
      · rw [after.exterior q (Or.inl earlier),inv q hq,if_pos earlier,if_pos (by omega)]
      · by_cases contained : q < off+len
        · have j : q-off < len := by omega
          have pos : off+(q-off) = q := Nat.add_sub_of_le (Nat.le_of_not_lt earlier)
          rw [if_pos contained,←pos,after.same _ j,right _ j]
        · rw [after.exterior q (Or.inr (Nat.le_of_not_lt contained)),inv q hq,if_neg earlier,if_neg contained]
  apply action_of_digits n slot.val hn (by unfold width; omega) mir
  exact sweep (schedule n) 0 src (by rw [schedule_extent n hn]; omega) checked (by simp [src])

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTTemplateAction ====

-- ==== begin CRTBarrelCorrect ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Partial

/-- The forward barrel shifts every bank word with clear high padding, and its measured mirror
restores every forward image. Both preserve the exterior and the incoming phase on every tape. -/
theorem barrel_result (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool)
    (slot : Fin 17) (v : Nat) (s : State) (tape : List Bool)
    (small : v < 2^(barrelWidth (start j) - (slot.val - 1)))
    (input : HighBankBarrel.holds (Shadow7.bankW (start j)) (barrelWidth (start j))
      (v <<< entryShift mir slot.val) s)
    (tag : ∀ k : Fin 16, s.basis (tagsP.getD k.val 1560) = decide (slot.val = k.val+1))
    (scratch : ∀ k < 10, s.basis (Shadow7.poolW (start j) (17+k)) = false) :
    HighBankBarrel.Result (Shadow7.bankW (start j)) (barrelWidth (start j))
      (v <<< exitShift mir slot.val) s (run (barrel (start j) mir) tape s) := by
  let n := barrelWidth (start j)
  have hn : UsedWidth n := usedWidth j lo hi
  exact barrel_result_of_matrix j lo hi mir slot v s tape (coordinates_checked n hn)
    (Packed.template_action n hn slot mir) small input tag scratch

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrelCorrect ====

-- ==== begin DeadJoinSemantic (credited to spariev 65b176b3) ====
-- Generic semantic factoring for the specialized leave; circuit definitions above are unchanged.
section

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-- Generic trajectory facts, independent of the admission structure in Main. -/
structure RawValid (s : State) (gs : List Gate) : Prop where
  physical : ∀ g ∈ gs, proper g = true
  prepared : Prepared s gs
  ready : Ready s gs

theorem RawValid.tail {s : State} {g : Gate} {gs : List Gate} (v : RawValid s (g::gs)) :
    RawValid (transition g s) gs :=
  ⟨fun x hx => v.physical x (List.mem_cons_of_mem _ hx),v.prepared.2,v.ready.2⟩

theorem RawValid.default_run {s : State} {gs : List Gate} (v : RawValid s gs) (m : List Bool) :
    run (GateMirror.forward gs) m s = run (GateMirror.forward gs) [] s := by
  induction gs generalizing s m with
  | nil => rfl
  | cons g gs ih =>
    change run ([front g] ++ GateMirror.forward gs) m s = run ([front g] ++ GateMirror.forward gs) [] s
    simp only [run_append,run_take,List.drop_nil]
    rw [head_default g s v.prepared.1 (v.physical _ List.mem_cons_self)]
    exact ih v.tail _

theorem RawValid.parts {s : State} {a b : List Gate} (ok : RawValid s (a++b)) :
    RawValid s a ∧ RawValid (run (GateMirror.forward a) [] s) b := by
  induction a generalizing s with
  | nil => exact ⟨⟨by simp,trivial,trivial⟩,ok⟩
  | cons g gs ih =>
    obtain ⟨left,right⟩ := ih ok.tail
    refine ⟨⟨fun x hx => ok.physical x (List.mem_append_left _ hx),⟨ok.prepared.1,left.prepared⟩,⟨ok.ready.1,left.ready⟩⟩,?_⟩
    change RawValid (run ([front g]++GateMirror.forward gs) [] s) b
    simpa only [run_append,run_take,List.drop_nil] using right

theorem RawValid.undo_run {s : State} {a : List Gate} (v : RawValid s a) (m n : List Bool) :
    run (GateMirror.inverse a) n (run (GateMirror.forward a) m s) = s :=
  invert a s v.physical v.prepared v.ready m n

theorem raw_append {s : State} {a b : List Gate} (va : RawValid s a)
    (vb : RawValid (run (GateMirror.forward a) [] s) b) : RawValid s (a++b) := by
  induction a generalizing s with
  | nil => exact vb
  | cons g gs ih =>
    have after : RawValid (run (GateMirror.forward gs) [] (transition g s)) b := by
      change RawValid (run ([front g]++GateMirror.forward gs) [] s) b at vb
      rw [run_append,run_take,List.drop_nil] at vb
      exact vb
    have rest := ih va.tail after
    exact ⟨fun x hx => by
      rcases List.mem_cons.mp hx with rfl | ht
      · exact va.physical _ List.mem_cons_self
      · exact rest.physical x ht,
      ⟨va.prepared.1,rest.prepared⟩,⟨va.ready.1,rest.ready⟩⟩

theorem raw_replace (a b c : List Gate) (fwd rev : Program) (s : State) (v : RawValid s (a++(b++c)))
    (same : ∀ t, run fwd t (run (GateMirror.forward a) [] s) = run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s))
    (back : ∀ t, run rev t (run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s)) = run (GateMirror.forward a) [] s) :
    (∀ m, run (GateMirror.forward a ++ fwd ++ GateMirror.forward c) m s = run (GateMirror.forward (a++(b++c))) m s) ∧
    (∀ m n, run (GateMirror.inverse c ++ rev ++ GateMirror.inverse a) n (run (GateMirror.forward a ++ fwd ++ GateMirror.forward c) m s) = s) := by
  obtain ⟨va,vbc⟩ := v.parts
  obtain ⟨vb,vc⟩ := vbc.parts
  let u := run (GateMirror.forward a) [] s
  let z := run (GateMirror.forward b) [] u
  have emitted (m : List Bool) : run (GateMirror.forward a ++ fwd ++ GateMirror.forward c) m s = run (GateMirror.forward c) [] z := by
    simp only [run_append,run_take,va.default_run,same]
    exact vc.default_run _
  have old (m : List Bool) : run (GateMirror.forward (a++(b++c))) m s = run (GateMirror.forward c) [] z := by
    simp only [forward_app,run_append,va.default_run,vb.default_run]
    exact vc.default_run _
  refine ⟨fun m => (emitted m).trans (old m).symm,?_⟩
  intro m n
  rw [emitted]
  have undoC (l : List Bool) : run (GateMirror.inverse c) l (run (GateMirror.forward c) [] z) = z := vc.undo_run [] l
  have undoB (l : List Bool) : run rev l z = u := back l
  simp only [run_append,run_take,undoC,undoB]
  exact va.undo_run [] _

theorem high_pair_identity (a sh tu : Wire) (s : State) (m : List Bool)
    (nd : [a,sh,tu].Nodup)
    (prepared : Prepared s [.cx sh tu,.cx tu sh,.pop a tu sh])
    (zero : s.basis sh = false) :
    run (GateMirror.forward [.cx sh tu,.cx tu sh,.pop a tu sh]) m s = s := by
  obtain ⟨has,hat,hst⟩ : a≠sh ∧ a≠tu ∧ sh≠tu := by simpa [and_assoc] using nd
  have clean : if s.basis a then s.basis sh=false else s.basis tu=false := by
    cases ha : s.basis a
    · have hv := prepared.2.2.1
      change (transition (.cx tu sh) (transition (.cx sh tu) s)).basis sh =
        ((transition (.cx tu sh) (transition (.cx sh tu) s)).basis a &&
          (transition (.cx tu sh) (transition (.cx sh tu) s)).basis tu) at hv
      simpa [transition,front,run,writeBit,Function.update,zero,ha,has,hat,hst,Ne.symm hst] using hv
    · simpa [ha] using zero
  have result := pair_runM false a sh tu nd s m clean
  change run (pairM false a sh tu) m s = s
  apply State.extensionality
  · exact result.1
  · funext q
    by_cases es : q=sh
    · subst q; exact result.2.2.1.trans zero.symm
    · by_cases et : q=tu
      · subst q; simpa [zero] using result.2.1
      · exact result.2.2.2 q es et

theorem raw_delete_identity {s : State} {a b c : List Gate} (v : RawValid s (a++(b++c)))
    (id : run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s) =
      run (GateMirror.forward a) [] s) : RawValid s (a++c) := by
  obtain ⟨va,vbc⟩ := v.parts
  obtain ⟨vb,vc⟩ := vbc.parts
  rw [id] at vc
  exact raw_append va vc

theorem raw_drop_identity (a b c : List Gate) (s : State) (v : RawValid s (a++(b++c)))
    (id : ∀ m, run (GateMirror.forward b) m (run (GateMirror.forward a) [] s) = run (GateMirror.forward a) [] s) :
    RawValid s (a++c) ∧
    (∀ m, run (GateMirror.forward (a++c)) m s = run (GateMirror.forward (a++(b++c))) m s) := by
  have w := raw_delete_identity v (id [])
  refine ⟨w,?_⟩
  intro m
  calc
    run (GateMirror.forward (a++c)) m s = run (GateMirror.forward (a++c)) [] s := w.default_run m
    _ = run (GateMirror.forward (a++(b++c))) [] s := by
      simp only [forward_app,run_append,run_take,List.drop_nil,id []]
    _ = run (GateMirror.forward (a++(b++c))) m s := (v.default_run m).symm

theorem dest_forward (gs : List Gate) :
    (GateMirror.forward gs).map LeaveReadoutFrame.destination = gs.map target := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [GateMirror.forward,List.map_cons] at ih ⊢
    rw [ih]
    cases g <;> rfl

theorem post_keeps (j : Fin 26) (hi : j.val≤24) (s : State) (m : List Bool) :
    (run (GateMirror.forward (postEntry (start j))) m s).basis (Shadow7.a0P (start j) - 1 + 16) =
      s.basis (Shadow7.a0P (start j) - 1 + 16) := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  rintro hit
  obtain ⟨g,hg,e⟩ := List.mem_map.mp hit
  exact of_decide_eq_true (List.all_eq_true.mp (post_keeps_checked j hi) g hg) e

theorem pair_zero (j : Fin 26) (hi : j.val≤24) (s : State)
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j))) [] s).basis (Shadow7.a0P (start j) - 1 + 16) = false) :
    (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false := by
  rw [forward_app,run_append,run_take,List.drop_nil,post_keeps j hi]
  exact zero

theorem raw_reference_pair (j : Fin 26) (hi : j.val≤24) (s : State)
    (valid : RawValid s (referenceOps (start j)))
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false) :
    RawValid s (shortenedOps (start j)) ∧
    (∀ m, run (GateMirror.forward (shortenedOps (start j))) m s = run (GateMirror.forward (referenceOps (start j))) m s) := by
  let a := LeaveJ7.entryOps (start j) ++ postEntry (start j)
  have shape : referenceOps (start j) = a ++ (pair16 (start j) ++ afterWord (start j)) := by
    rw [reference_shape j hi]; simp only [a,List.append_assoc]
  rw [shape] at valid
  have vb := valid.parts.2.parts.1
  have same (m : List Bool) : run (GateMirror.forward (pair16 (start j))) m
      (run (GateMirror.forward a) [] s) = run (GateMirror.forward a) [] s :=
    high_pair_identity _ _ _ _ m (pair_layout_checked j hi) vb.prepared zero
  obtain ⟨w,pair⟩ := raw_drop_identity a (pair16 (start j)) (afterWord (start j)) s valid same
  exact ⟨w,by simpa only [shortenedOps,a,shape,List.append_assoc] using pair⟩

theorem raw_prefix_replace {s : State} {a b anew : List Gate}
    (v : RawValid s (a++b)) (phys : ∀ g∈anew,proper g=true) (ready : Ready s anew)
    (same : ∀ m,run (GateMirror.forward anew) m s=run (GateMirror.forward a) [] s) :
    RawValid s (anew++b) ∧
    (∀ m,run (GateMirror.forward (anew++b)) m s=run (GateMirror.forward (a++b)) m s) := by
  have quiet (m : List Bool) : (run (GateMirror.forward anew) m s).phase=s.phase :=
    (congrArg State.phase (same m)).trans (no_phase a s)
  have va : RawValid s anew := ⟨phys,all_prepared anew s phys quiet,ready⟩
  have vb := v.parts.2
  rw [←same []] at vb
  have w := raw_append va vb
  refine ⟨w,?_⟩
  intro m
  calc
    run (GateMirror.forward (anew++b)) m s = run (GateMirror.forward (anew++b)) [] s := w.default_run m
    _ = run (GateMirror.forward (a++b)) [] s := by
      simp only [forward_app,run_append,run_take,List.drop_nil,same]
    _ = run (GateMirror.forward (a++b)) m s := (v.default_run m).symm

theorem scan_ready (s h : Nat) (st : State) : Ready st (DeadScan.fix0M s h) :=
  ready_plain _ (by simp [DeadScan.fix0M,Shadow7.fix0P,plainGate]) st

theorem raw_scan_join_valid (j : Fin 26) (hi : j.val≤24) (s : State)
    (original : RawValid s (referenceOps (start j)))
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false)
    (scanEq : ∀ m, run (GateMirror.forward (DeadScan.fix0M (start j) (Shadow7.sbP (start j)))) m s =
      run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s) :
    RawValid s (scanShortenedOps (start j)) ∧
    (∀ m,run (GateMirror.forward (scanShortenedOps (start j))) m s=
      run (GateMirror.forward (referenceOps (start j))) m s) := by
  obtain ⟨v,same⟩ := raw_reference_pair j hi s original zero
  rw [shortened_scan_shape] at v
  have phys : ∀ x∈DeadScan.fix0M (start j) (Shadow7.sbP (start j)),proper x=true :=
    fun x hx => List.all_eq_true.mp (scan_physical j hi) x hx
  obtain ⟨w,eq⟩ := raw_prefix_replace v phys (scan_ready _ _ s) scanEq
  refine ⟨w,?_⟩
  intro m
  exact (eq m).trans (by rw [←shortened_scan_shape]; exact same m)

theorem flag_geometry : ∀ j : Fin 26, j.val≤24 →
    (Shadow7.e0P (start j)+3 : Wire) ≠ Shadow7.e0P (start j)+4 ∧
    (Shadow7.e0P (start j)+6 : Wire) ≠ Shadow7.e0P (start j)+3 ∧
    (Shadow7.e0P (start j)+6 : Wire) ≠ Shadow7.e0P (start j)+4 ∧
    (Shadow7.e0P (start j)+3 : Wire) ≠ 1559 ∧ (Shadow7.e0P (start j)+4 : Wire) ≠ 1559 := by decide +kernel

theorem raw_all_valid (j : Fin 26) (hi : j.val≤24) (s : State)
    (original : RawValid s (referenceOps (start j)))
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false)
    (scanEq : ∀ m, run (GateMirror.forward (DeadScan.fix0M (start j) (Shadow7.sbP (start j)))) m s =
      run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s)
    (rel : FlagLeave.Rel (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) (Shadow7.e0P (start j)+6) false s) :
    RawValid s (allOps (start j)) ∧
    (∀ m,run (GateMirror.forward (allOps (start j))) m s=run (GateMirror.forward (referenceOps (start j))) m s) ∧
    run (GateMirror.forward (beforeAll (start j))) [] s =
      run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s := by
  obtain ⟨fu,cf,cu,fl,ul⟩ := flag_geometry j hi
  obtain ⟨v,same⟩ := raw_scan_join_valid j hi s original zero scanEq
  obtain ⟨phys,prepared,ready,eq⟩ := FlagLeave.cut_valid _ _ _ 1559 2 false
    (scanShortenedOps (start j)) s ⟨fu,cf,cu⟩ fl ul (all_checked j hi) rel v.physical v.prepared v.ready
  have w : RawValid s (allOps (start j)) := ⟨phys,prepared,ready⟩
  refine ⟨w,?_,?_⟩
  · intro m
    exact (w.default_run m).trans (eq.trans ((v.default_run m).symm.trans (same m)))
  · rw [scan_shortened_shape] at v
    have vb := v.parts.1
    have flagEq := (FlagLeave.cut_valid _ _ _ 1559 2 false (beforeScan (start j)) s ⟨fu,cf,cu⟩ fl ul
      (before_all_checked j hi) rel vb.physical vb.prepared vb.ready).2.2.2
    apply flagEq.trans
    have before_shape : CRTBarrel.beforeReference (start j) =
        Shadow7.fix0P (start j) (Shadow7.sbP (start j)) ++ beforeScanTail (start j) := by
      simp only [CRTBarrel.beforeReference,beforeScanTail,List.append_assoc]
    rw [beforeScan,before_shape,forward_app,forward_app,run_append,run_append,run_take,run_take,
      List.drop_nil,scanEq []]
    simp only [List.drop_nil]

theorem raw_crt_all_pair (j : Fin 26) (hi : j.val≤24) (s : State)
    (original : RawValid s (referenceOps (start j)))
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false)
    (scanEq : ∀ m, run (GateMirror.forward (DeadScan.fix0M (start j) (Shadow7.sbP (start j)))) m s =
      run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s)
    (rel : FlagLeave.Rel (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) (Shadow7.e0P (start j)+6) false s)
    (barrelSame : ∀ m, run (CRTBarrel.barrel (start j) false) m (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s) =
      run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s))
    (barrelBack : ∀ n, run (CRTBarrel.barrel (start j) true) n
      (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s)) =
      run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s) :
    (∀ m,run (GateMirror.forward (beforeAll (start j)) ++ CRTBarrel.barrel (start j) false ++ GateMirror.forward (afterAll (start j))) m s=
      run (GateMirror.forward (referenceOps (start j))) m s) ∧
    (∀ m n,run (GateMirror.inverse (afterAll (start j)) ++ CRTBarrel.barrel (start j) true ++ GateMirror.inverse (beforeAll (start j))) n
      (run (GateMirror.forward (beforeAll (start j)) ++ CRTBarrel.barrel (start j) false ++ GateMirror.forward (afterAll (start j))) m s)=s) := by
  obtain ⟨v,same,beforeEq⟩ := raw_all_valid j hi s original zero scanEq rel
  rw [all_split j hi] at v
  have same' : ∀ m, run (CRTBarrel.barrel (start j) false) m (run (GateMirror.forward (beforeAll (start j))) [] s) =
      run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (beforeAll (start j))) [] s) := by
    simpa only [beforeEq] using barrelSame
  have back' : ∀ n, run (CRTBarrel.barrel (start j) true) n
      (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (beforeAll (start j))) [] s)) =
      run (GateMirror.forward (beforeAll (start j))) [] s := by
    simpa only [beforeEq] using barrelBack
  obtain ⟨f,r⟩ := raw_replace _ _ _ _ _ s v same' back'
  exact ⟨fun m => (f m).trans (by rw [←all_split j hi]; exact same m),r⟩

end ECDSAAdd.Entrant.StairPacket.DeadJoin

end
-- ==== end DeadJoinSemantic ====

-- ==== begin FlagCut57Semantic (credited to ercumentyildirim ae9d602d) ====
section
namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

theorem raw_swap_mid {s : State} {a b b' c : List Gate}
    (v : RawValid s (a ++ (b ++ c)))
    (vb' : RawValid (run (GateMirror.forward a) [] s) b')
    (eq : run (GateMirror.forward b') [] (run (GateMirror.forward a) [] s) =
          run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s)) :
    RawValid s (a ++ (b' ++ c)) ∧
    (∀ m, run (GateMirror.forward (a ++ (b' ++ c))) m s = run (GateMirror.forward (a ++ (b ++ c))) m s) := by
  obtain ⟨va, vbc⟩ := v.parts
  obtain ⟨vb, vc⟩ := vbc.parts
  have vc' : RawValid (run (GateMirror.forward b') [] (run (GateMirror.forward a) [] s)) c := by
    rwa [eq]
  have w : RawValid s (a ++ (b' ++ c)) := raw_append va (raw_append vb' vc')
  refine ⟨w, fun m => ?_⟩
  calc
    run (GateMirror.forward (a ++ (b' ++ c))) m s
        = run (GateMirror.forward (a ++ (b' ++ c))) [] s := w.default_run m
    _ = run (GateMirror.forward (a ++ (b ++ c))) [] s := by
        simp only [forward_app, run_append, run_take, List.drop_nil, eq]
    _ = run (GateMirror.forward (a ++ (b ++ c))) m s := (v.default_run m).symm

theorem keeps_of_targets57 (gs : List Gate) (q : Wire) (h : ∀ g ∈ gs, target g ≠ q) (m : List Bool) (t : State) :
    (run (GateMirror.forward gs) m t).basis q = t.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  intro hit
  obtain ⟨g, hg, e⟩ := List.mem_map.mp hit
  exact h g hg e

theorem swap_make57 (t x y : Wire) (u : State) (hxy : x ≠ y) (htx : t ≠ x) (hty : t ≠ y) (hy : u.basis y = false) :
    run (GateMirror.forward [.make t x y, .cx y x]) [] u =
    run (GateMirror.forward [.cx x y, .ccx t y x, .cx x y]) [] u := by
  obtain ⟨ph, f⟩ := u
  simp only at hy
  simp only [GateMirror.forward, List.map, GateMirror.front, run, State.mk.injEq, true_and]
  funext q
  by_cases hqx : q = x
  · subst hqx
    cases h1 : f q <;> cases h2 : f t <;>
      simp [writeBit, Function.update_apply, hxy, htx, hty, Ne.symm hxy, Ne.symm htx, Ne.symm hty, h1, h2, hy]
  · by_cases hqy : q = y
    · subst hqy
      cases h1 : f x <;> cases h2 : f t <;>
        simp [writeBit, Function.update_apply, hxy, htx, hty, Ne.symm hxy, Ne.symm htx, Ne.symm hty, h1, h2, hy, hqx]
    · simp [writeBit, Function.update_apply, hqx, hqy]

theorem row0_distinct57 : ∀ j : Fin 26, j.val ≤ 24 →
    (Shadow7.a0P (start j) - 1 + 0 : Wire) ≠ Shadow7.e0P (start j) + 6 ∧
    (tagsP.getD 0 0 : Wire) ≠ Shadow7.a0P (start j) - 1 + 0 ∧
    (tagsP.getD 0 0 : Wire) ≠ Shadow7.e0P (start j) + 6 := by decide +kernel

theorem pre5Cut_targets : ∀ j : Fin 26, j.val ≤ 24 →
    (beforePre5Cut (start j)).all (fun g => decide (target g ≠ Shadow7.e0P (start j) + 6)) = true := by decide +kernel

theorem lowRest7_1558 (s : Nat) (t : State) :
    (run (GateMirror.forward (lowRest7 s)) [] t).basis 1558 = false := by
  obtain ⟨X, hX⟩ : ∃ X, lowRest7 s =
      X ++ [.pop (Shadow7.b0P s - 1) 1557 1558, .cx (Shadow7.a0P s - 1) 1557, .x 1557] := ⟨_, rfl⟩
  rw [hX, forward_app, run_append, run_take, List.drop_nil]
  generalize run (GateMirror.forward X) [] t = u
  obtain ⟨ph, f⟩ := u
  simp [GateMirror.forward, GateMirror.front, GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, writeBit, Function.update_apply]

theorem storeHead7_targets : ∀ j : Fin 26, j.val ≤ 24 →
    ((storeHead7 (start j)).drop 1).all (fun g => decide (target g ≠ 1558)) = true := by decide +kernel

theorem afterPre7Tail_1558 (j : Fin 26) (hi : j.val ≤ 24) (t : State) :
    (run (GateMirror.forward (afterPre7Tail (start j))) [] t).basis 1558 = true := by
  have hT := List.all_eq_true.mp (storeHead7_targets j hi)
  have e : storeHead7 (start j) = [.x 1558] ++ (storeHead7 (start j)).drop 1 := rfl
  rw [afterPre7Tail, forward_app, run_append, run_take, List.drop_nil, e, forward_app, run_append, run_take, List.drop_nil]
  rw [keeps_of_targets57 _ _ (fun g hg => of_decide_eq_true (hT g hg))]
  have z := lowRest7_1558 (start j) t
  generalize run (GateMirror.forward (lowRest7 (start j))) [] t = u at z ⊢
  obtain ⟨ph, f⟩ := u
  simp only at z
  simp [GateMirror.forward, GateMirror.front, run, writeBit, Function.update_apply, z]

theorem chainMid7_targets (s : Nat) : ∀ g ∈ chainMid7 s, target g ≠ 1558 := by
  have hb : AllAT (fun _ => True) (fun q => q ≠ 1558)
      [GateMirror.Gate.cx (Shadow7.storeW s (Shadow7.liveW s - Shadow7.lowsP s + 1)) 1557, GateMirror.Gate.x 1557] :=
    allAT_cons (ok_cx (A := fun _ => True) (T := fun q => q ≠ 1558) trivial (by decide))
      (allAT_cons (ok_x (A := fun _ => True) (T := fun q => q ≠ 1558) (by decide)) allAT_nil)
  have h := allAT_chainG (A := fun _ => True) (T := fun q => q ≠ 1558) (Shadow7.storeW s)
    (fun i => if i = 0 then Shadow7.a0P s + Shadow7.lowsP s - 2 else Shadow7.bankW s (Shadow7.lowsP s + i - 1)) _ hb
    1 (Shadow7.liveW s - Shadow7.lowsP s)
    (fun k h1 h2 => ⟨trivial, fun hk => by
      simp only [Shadow7.storeW, Partial.storeW]; split_ifs <;> ((try unfold Wire at *); omega)⟩)
    (fun _ _ _ => trivial)
  intro g hg
  exact (h g hg).2

theorem make_cx_1558 (top : Wire) (u : State) (h1558 : u.basis 1558 = true) :
    run (GateMirror.forward [.cx top 1559]) [] u =
    run (GateMirror.forward [.make 1558 top 1559]) [] u := by
  simp [GateMirror.forward, GateMirror.front, run, writeBit, h1558]

theorem pop_cx_1558 (top : Wire) (u : State) (h1558 : u.basis 1558 = true)
    (val : ValueOK u (.pop 1558 top 1559)) :
    run (GateMirror.forward [.cx top 1559]) [] u =
    run (GateMirror.forward [.pop 1558 top 1559]) [] u := by
  change u.basis 1559 = (u.basis 1558 && u.basis top) at val
  rw [h1558, Bool.true_and] at val
  simp [GateMirror.forward, GateMirror.front, GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, writeBit, val]

end ECDSAAdd.Entrant.StairPacket.DeadJoin

-- ==== begin KeptParity semantics (credited to GordoAR a2ce2c3a) ====
namespace ECDSAAdd.Entrant.StairPacket.KeptParity
open Arithmetic Partial GateMirror Challenge

set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

/-- The digit is active on one of the first eight rows when it is set. -/
def relation (v : BasisState) : Prop :=
  (v 1 && v 0) = (v 0 ^^ (v 2 && v 0) ^^ (v 3 && v 0) ^^ (v 4 && v 0) ^^ (v 5 && v 0) ^^ (v 6 && v 0) ^^ (v 7 && v 0) ^^ (v 8 && v 0))

def tag (k : LeaveSelector.Mode) (i : Nat) := LeaveSelector.enabled k && decide (i = LeaveSelector.key k)
def digitBit (k : LeaveSelector.Mode) (cross sign : Bool) :=
  ((LeaveSelector.enabled k ^^ cross) ^^ sign) ^^ (cross && sign)

private theorem finiteModes : ∀ (k : LeaveSelector.Mode) (cross sign : Bool),
    (k.val = 0 → cross = false ∧ sign = false) → (8 ≤ LeaveSelector.key k → sign = true) →
    let digit := digitBit k cross sign
    (tag k 0 && digit) = (digit ^^ (tag k 1 && digit) ^^ (tag k 2 && digit) ^^ (tag k 3 && digit) ^^ (tag k 4 && digit) ^^ (tag k 5 && digit) ^^ (tag k 6 && digit) ^^ (tag k 7 && digit)) := by decide +kernel

theorem relationOfMode (v : BasisState) (k : LeaveSelector.Mode) (cross sign : Bool)
    (inactive : k.val = 0 → cross = false ∧ sign = false) (high : 8 ≤ LeaveSelector.key k → sign = true)
    (digit : v 0 = digitBit k cross sign) (ports : ∀ i, i < 8 → v (i+1) = tag k i) : relation v := by
  unfold relation
  rw [ports 0 (by decide), ports 1 (by decide), ports 2 (by decide), ports 3 (by decide), ports 4 (by decide), ports 5 (by decide), ports 6 (by decide), ports 7 (by decide), digit]
  exact finiteModes k cross sign inactive high

private def shifted (s : State) (x : Bool) : State :=
  ⟨s.phase, writeBit s.basis 9 (s.basis 9 ^^ x)⟩

private def bareStep (h y : Wire) (s : State) : State :=
  ⟨s.phase, writeBit s.basis y (s.basis y ^^ (s.basis h && s.basis 0))⟩

private theorem twice (a b c d : Bool) : (((a ^^ b) ^^ c) ^^ (c ^^ d)) = (a ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem liftedStep (h y : Wire) (hn : h ≠ 9) (yn : y ≠ 9) (s : State) (x : Bool)
    (tail : Program) (m : List Bool) :
    run (.CX y 9 :: .CCX h 0 y :: .CX y 9 :: tail) m (shifted s x) =
      run tail m (shifted (bareStep h y s) (x ^^ (s.basis h && s.basis 0))) := by
  simp only [run]
  apply congrArg (run tail m)
  apply State.extensionality
  · rfl
  funext q
  by_cases endBit : q = 9
  · subst q
    simp [shifted, bareStep, writeBit, Function.update_of_ne, hn, yn, Ne.symm yn, twice]
  · by_cases dataBit : q = y
    · subst q
      simp [shifted, bareStep, writeBit, Function.update_of_ne, hn, yn, Ne.symm yn]
    · simp [shifted, bareStep, writeBit, Function.update_of_ne, endBit, dataBit]

private def bare (i : Nat) (n : Nat) : Program :=
  match n with
  | 0 => []
  | n+1 => .CCX (i+2) 0 (i+10) :: bare (i+1) n

private def lifted (i : Nat) (n : Nat) : Program :=
  match n with
  | 0 => []
  | n+1 => .CX (i+10) 9 :: .CCX (i+2) 0 (i+10) :: .CX (i+10) 9 :: lifted (i+1) n

private def parity (v : BasisState) (i n : Nat) (x : Bool) : Bool :=
  match n with
  | 0 => x
  | n+1 => parity v (i+1) n (x ^^ (v (i+2) && v 0))

private theorem ladder (v : BasisState) (m : List Bool) (i n : Nat) (bound : i+n ≤ 7)
    (s : State) (keep : ∀ q : Nat, q ≤ 8 → s.basis q = v q) (x : Bool) :
    run (lifted i n) m (shifted s x) = shifted (run (bare i n) m s) (parity v i n x) := by
  induction n generalizing i s x with
  | zero => rfl
  | succ n ih =>
    have hn : (i+2 : Wire) ≠ 9 := by unfold Wire at *; omega
    have yn : (i+10 : Wire) ≠ 9 := by unfold Wire at *; omega
    simp only [lifted, bare, parity, liftedStep _ _ hn yn, run]
    rw [← keep (i+2) (by omega), ← keep 0 (by decide)]
    apply ih (i+1) (by omega) (bareStep (i+2) (i+10) s)
    intro q hq
    have ne : (q : Wire) ≠ i+10 := by unfold Wire at *; omega
    simpa [bareStep, writeBit, Function.update_of_ne ne] using keep q hq

private theorem parity_left (v : BasisState) (i n : Nat) (a b : Bool) :
    parity v i n (a ^^ b) = (a ^^ parity v i n b) := by
  induction n generalizing i b with
  | zero => rfl
  | succ n ih => simp only [parity, Bool.xor_assoc, ih]

private theorem shift_shift (s : State) (a b : Bool) : shifted (shifted s a) b = shifted s (a ^^ b) := by
  apply State.extensionality
  · rfl
  funext q
  by_cases h : q = 9
  · subst q; simp [shifted, writeBit, Bool.xor_assoc]
  · simp [shifted, writeBit, Function.update_of_ne h]

private theorem shift_zero (s : State) : shifted s false = s := by
  apply State.extensionality
  · rfl
  funext q
  by_cases h : q = 9
  · subst q; simp [shifted, writeBit]
  · simp [shifted, writeBit, Function.update_of_ne h]

theorem same (s : State) (m : List Bool) (mode : relation s.basis) :
    run (GateMirror.forward replacement) m s = run (GateMirror.forward old) m s := by
  have newProgram : GateMirror.forward replacement = .CX 0 9 :: lifted 0 7 := rfl
  have oldProgram : GateMirror.forward old = .CCX 1 0 9 :: bare 0 7 := rfl
  rw [newProgram, oldProgram]
  let top := s.basis 1 && s.basis 0
  let t := shifted s top
  change run (lifted 0 7) m (shifted s (s.basis 0)) = run (bare 0 7) m t
  have prepared : shifted t (top ^^ s.basis 0) = shifted s (s.basis 0) := by
    rw [show shifted t _ = shifted s (top ^^ (top ^^ s.basis 0)) from shift_shift _ _ _]
    congr 1
    cases top <;> cases s.basis 0 <;> rfl
  have keep (q : Nat) (hq : q ≤ 8) : t.basis q = s.basis q := by
    have ne : (q : Wire) ≠ 9 := by unfold Wire at *; omega
    simp [t, shifted, writeBit, Function.update_of_ne ne]
  have parityEq : parity s.basis 0 7 (s.basis 0) = top := mode.symm
  rw [← prepared, ladder s.basis m 0 7 (by decide) t keep, parity_left, parityEq, Bool.xor_self, shift_zero]

private theorem geometry : ∀ j : Fin 26, j.val ≤ 24 → ∀ (a b : Fin 17), port (start j) a = port (start j) b → a = b := by
  decide +kernel

private theorem rename_eq (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b)
    (p q : Program) (hp : wires p ⊆ S) (hq : wires q ⊆ S)
    (mp mq : List Bool) (t s : State) (hph : t.phase = s.phase)
    (hb : ∀ a ∈ S, t.basis a = s.basis (f a))
    (heq : run p mp t = run q mq t) :
    run (renameProgram f p) mp s = run (renameProgram f q) mq s := by
  have rp := run_rename_pool f S hf p hp mp t s hph hb
  have rq := run_rename_pool f S hf q hq mq t s hph hb
  have hph_eq : (run (renameProgram f p) mp s).phase = (run (renameProgram f q) mq s).phase := by
    rw [rp.1, rq.1, heq]
  have hb_eq : (run (renameProgram f p) mp s).basis = (run (renameProgram f q) mq s).basis := by
    funext w
    by_cases hw : w ∈ S.image f
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      rw [rp.2 a ha, rq.2 a ha, heq]
    · rw [run_rename_pool_outside f S p hp mp s w hw, run_rename_pool_outside f S q hq mq s w hw]
  cases h1 : run (renameProgram f p) mp s
  cases h2 : run (renameProgram f q) mq s
  rw [h1, h2] at hph_eq hb_eq
  simp only at hph_eq hb_eq
  rw [hph_eq, hb_eq]

set_option maxRecDepth 16000 in
/-- The parity pass runs like the kept pass, and is a valid trajectory, when `relation` holds at its input. -/
theorem placed_pair (j : Fin 26) (hi : j.val ≤ 24) (s : State) (h : relation (fun q => s.basis (port (start j) q))) :
    (∀ m, run (GateMirror.forward (placed (start j))) m s = run (GateMirror.forward (Shadow7.moveKept (start j))) [] s) ∧
    DeadJoin.RawValid s (placed (start j)) := by
  let f := port (start j)
  let t : State := ⟨s.phase, fun q => s.basis (f q)⟩
  have inj (a : Wire) (ha : a ∈ Finset.range 17) (b : Wire) (hb : b ∈ Finset.range 17)
      (eq : f a = f b) : a = b :=
    congrArg Fin.val (geometry j hi ⟨a, Finset.mem_range.mp ha⟩ ⟨b, Finset.mem_range.mp hb⟩ eq)
  have sameF (m : List Bool) : run (GateMirror.forward (placed (start j))) m s =
      run (GateMirror.forward (Shadow7.moveKept (start j))) [] s := by
    have eq : run (GateMirror.forward replacement) m t = run (GateMirror.forward old) [] t :=
      (same t m h).trans (run_take (GateMirror.forward old) m t).symm
    have boundedNew : wires (GateMirror.forward replacement) ⊆ Finset.range 17 := by decide
    have boundedOld : wires (GateMirror.forward old) ⊆ Finset.range 17 := by decide
    exact rename_eq f (Finset.range 17) inj _ _ boundedNew boundedOld m [] t s rfl (fun _ _ => rfl) eq
  have phys : ∀ g ∈ placed (start j), proper g = true := List.all_eq_true.mp (physical j hi)
  refine ⟨sameF, ⟨phys, ?_, ready_plain _ (by rfl) _⟩⟩
  exact all_prepared _ s phys (fun m => (congrArg State.phase (sameF m)).trans (no_phase _ s))

end ECDSAAdd.Entrant.StairPacket.KeptParity

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
-- ==== end KeptParity semantics ====

theorem raw_crt_all_pair57 (j : Fin 26) (hi : j.val ≤ 24) (s : State)
    (original : RawValid s (referenceOps (start j)))
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false)
    (scanEq : ∀ m, run (GateMirror.forward (DeadScan.fix0M (start j) (Shadow7.sbP (start j)))) m s =
      run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s)
    (rel : FlagLeave.Rel (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) (Shadow7.e0P (start j) + 6) false s)
    (zero6 : s.basis (Shadow7.e0P (start j) + 6) = false)
    (barrelSame : ∀ m, run (CRTBarrel.barrel (start j) false) m (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s) =
      run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s))
    (barrelBack : ∀ n, run (CRTBarrel.barrel (start j) true) n
      (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s)) =
      run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s)
    (keptRel : KeptParity.relation (fun q => (run (GateMirror.forward (CRTBarrel.beforeReference (start j) ++
      (Shadow7.leaveBarrel (start j) ++ keptHead (start j)))) [] s).basis (KeptParity.port (start j) q))) :
    (∀ m, run (GateMirror.forward (before5 (start j)) ++ CRTBarrel.barrel (start j) false ++ GateMirror.forward (after7K (start j))) m s =
      run (GateMirror.forward (referenceOps (start j))) m s) ∧
    (∀ m n, run (GateMirror.inverse (after7K (start j)) ++ CRTBarrel.barrel (start j) true ++ GateMirror.inverse (before5 (start j))) n
      (run (GateMirror.forward (before5 (start j)) ++ CRTBarrel.barrel (start j) false ++ GateMirror.forward (after7K (start j))) m s) = s) := by
  obtain ⟨v0, same0, beforeEq⟩ := raw_all_valid j hi s original zero scanEq rel
  -- Step 1: FlagCut5 (row0Old -> row0New inside beforeAll)
  have shape0 : allOps (start j) =
      beforePre5Cut (start j) ++ (row0Old (start j) ++ (beforePost5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ afterAll (start j)))) := by
    rw [all_split j hi, beforeAll_split5 j hi]
    simp only [List.append_assoc]
  rw [shape0] at v0
  have hy6 : (run (GateMirror.forward (beforePre5Cut (start j))) [] s).basis (Shadow7.e0P (start j) + 6) = false :=
    (keeps_of_targets57 _ _ (fun g hg => of_decide_eq_true (List.all_eq_true.mp (pre5Cut_targets j hi) g hg)) [] s).trans zero6
  obtain ⟨hxy, htx, hty⟩ := row0_distinct57 j hi
  have eqRow0 : run (GateMirror.forward (row0New (start j))) [] (run (GateMirror.forward (beforePre5Cut (start j))) [] s) =
      run (GateMirror.forward (row0Old (start j))) [] (run (GateMirror.forward (beforePre5Cut (start j))) [] s) :=
    swap_make57 _ _ _ _ hxy htx hty hy6
  have vRow0 : RawValid (run (GateMirror.forward (beforePre5Cut (start j))) [] s) (row0New (start j)) :=
    ⟨fun x hx => List.all_eq_true.mp (row0New_proper j hi) x hx, ⟨trivial, trivial, trivial⟩, ⟨hy6, trivial, trivial⟩⟩
  obtain ⟨v5, same5⟩ := raw_swap_mid v0 vRow0 eqRow0
  have before5Eq : run (GateMirror.forward (before5 (start j))) [] s =
      run (GateMirror.forward (beforeAll (start j))) [] s := by
    rw [before5, beforeAll_split5 j hi]
    simp only [forward_app, run_append, run_take, List.drop_nil, eqRow0]
  -- Step 2: FlagCut7 part A (.make 1558 top 1559 -> .cx top 1559)
  let pre7 := before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (afterPre7HeadCut (start j) ++ afterPre7Tail (start j)))
  have shape5 : beforePre5Cut (start j) ++ (row0New (start j) ++ (beforePost5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ afterAll (start j)))) =
      pre7 ++ ([.make 1558 (topW7 (start j)) 1559] ++ (chainMid7 (start j) ++ ([.pop 1558 (topW7 (start j)) 1559] ++ afterPost7 (start j)))) := by
    rw [afterAll_split7 j hi]
    simp only [pre7, before5, List.append_assoc]
  rw [shape5] at v5
  have h1558A : (run (GateMirror.forward pre7) [] s).basis 1558 = true := by
    have sp : pre7 = (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ afterPre7HeadCut (start j))) ++ afterPre7Tail (start j) := by
      simp only [pre7, List.append_assoc]
    rw [sp, forward_app, run_append, run_take, List.drop_nil]
    exact afterPre7Tail_1558 j hi _
  have vCxA : RawValid (run (GateMirror.forward pre7) [] s) [.cx (topW7 (start j)) 1559] :=
    ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact top_cx_proper j hi, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  obtain ⟨v7a, same7a⟩ := raw_swap_mid v5 vCxA (make_cx_1558 _ _ h1558A)
  -- Step 3: FlagCut7 part B (.pop 1558 top 1559 -> .cx top 1559)
  let pre7b := pre7 ++ ([.cx (topW7 (start j)) 1559] ++ chainMid7 (start j))
  have shape7a : pre7 ++ ([.cx (topW7 (start j)) 1559] ++ (chainMid7 (start j) ++ ([.pop 1558 (topW7 (start j)) 1559] ++ afterPost7 (start j)))) =
      pre7b ++ ([.pop 1558 (topW7 (start j)) 1559] ++ afterPost7 (start j)) := by
    simp only [pre7b, List.append_assoc]
  rw [shape7a] at v7a
  have h1558B : (run (GateMirror.forward pre7b) [] s).basis 1558 = true := by
    simp only [pre7b, forward_app, run_append, run_take, List.drop_nil]
    rw [keeps_of_targets57 _ 1558 (chainMid7_targets (start j))]
    rw [keeps_of_targets57 [.cx (topW7 (start j)) 1559] 1558 (fun g hg => by
      rw [List.mem_singleton.mp hg]; simp [target])]
    exact h1558A
  have valB : ValueOK (run (GateMirror.forward pre7b) [] s) (.pop 1558 (topW7 (start j)) 1559) :=
    v7a.parts.2.parts.1.prepared.1
  have vCxB : RawValid (run (GateMirror.forward pre7b) [] s) [.cx (topW7 (start j)) 1559] :=
    ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact top_cx_proper j hi, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  obtain ⟨v7, same7b⟩ := raw_swap_mid v7a vCxB (pop_cx_1558 _ _ h1558B valB)
  -- Step 4: Splice in the CRT barrel
  have shape7 : pre7b ++ ([.cx (topW7 (start j)) 1559] ++ afterPost7 (start j)) =
      before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after7 (start j)) := by
    simp only [pre7b, pre7, after7, List.append_assoc]
  rw [shape7] at v7
  have bEq : run (GateMirror.forward (before5 (start j))) [] s =
      run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s :=
    before5Eq.trans beforeEq
  have same' : ∀ m, run (CRTBarrel.barrel (start j) false) m (run (GateMirror.forward (before5 (start j))) [] s) =
      run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (before5 (start j))) [] s) := by
    simpa only [bEq] using barrelSame
  have back' : ∀ n, run (CRTBarrel.barrel (start j) true) n
      (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (before5 (start j))) [] s)) =
      run (GateMirror.forward (before5 (start j))) [] s := by
    simpa only [bEq] using barrelBack
  -- Step 3b: KeptParity (GordoAR a2ce2c3a): the kept pass inside after7 -> the parity pass
  have shapeK : before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after7 (start j)) =
      (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ keptHead (start j))) ++
        (Shadow7.moveKept (start j) ++ afterRest7 (start j)) := by
    rw [after7_kept j hi]
    simp only [List.append_assoc]
  rw [shapeK] at v7
  have keptIn : run (GateMirror.forward (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ keptHead (start j)))) [] s =
      run (GateMirror.forward (CRTBarrel.beforeReference (start j) ++ (Shadow7.leaveBarrel (start j) ++ keptHead (start j)))) [] s := by
    simp only [forward_app, run_append, run_take, List.drop_nil, bEq]
  have relK : KeptParity.relation (fun q => (run (GateMirror.forward (before5 (start j) ++
      (Shadow7.leaveBarrel (start j) ++ keptHead (start j)))) [] s).basis (KeptParity.port (start j) q)) := by
    rw [keptIn]
    exact keptRel
  obtain ⟨keptF, keptV⟩ := KeptParity.placed_pair j hi _ relK
  obtain ⟨v7K, same7K⟩ := raw_swap_mid v7 keptV (keptF [])
  have shapeK2 : (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ keptHead (start j))) ++
      (KeptParity.placed (start j) ++ afterRest7 (start j)) =
      before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after7K (start j)) := by
    simp only [after7K, List.append_assoc]
  rw [shapeK2] at v7K
  obtain ⟨f, r⟩ := raw_replace _ _ _ _ _ s v7K same' back'
  refine ⟨fun m => ?_, r⟩
  have h1 := f m
  rw [← shapeK2] at h1
  have hK := same7K m
  rw [← shapeK, ← shape7] at hK
  have h2 := (same7b m)
  rw [← shape7a] at h2
  have h3 := (same7a m)
  rw [← shape5] at h3
  have h4 := (same5 m)
  rw [← shape0] at h4
  exact h1.trans (hK.trans (h2.trans (h3.trans (h4.trans (same0 m)))))

end ECDSAAdd.Entrant.StairPacket.DeadJoin
end
-- ==== end FlagCut57Semantic ====

-- ==== begin ScanRowGordo (margin 16, credited to GordoAR e2530dcd) ====
section
namespace ECDSAAdd.Entrant.StairPacket.ScanRowGordo
open Arithmetic GateMirror Partial Challenge MeasuredCodec5
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem pre5_prefix (s : Nat) :
    DeadJoin.beforePre5 s = (firstRows s (Shadow7.sbP s) ++ cell s (Shadow7.sbP s)) ++
      ((DeadScan.fix0M s (Shadow7.sbP s)).drop 50 ++ leaveFix1 s (Shadow7.sbP s) ++
        Shadow7.fix2P s (Shadow7.sbP s) ++ leaveFix3 s (Shadow7.sbP s) ++
        leaveFix4 s (Shadow7.sbP s) ++ (Shadow7.fix5P s (Shadow7.sbP s)).take 27) := rfl

private theorem prefix_cut_noop : ∀ j : Fin 26, j.val ≤ 24 →
    let s := start j; let h := Shadow7.sbP s
    FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 2 (firstRows s h ++ cell s h) =
      firstRows s h ++ cell s h ∧
    FlagLeave.removed (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 2 (firstRows s h ++ cell s h) = [] := by
  decide +kernel

theorem before5_split (j : Fin 26) (hi : j.val ≤ 24) :
    DeadJoin.before5 (start j) =
      firstRows (start j) (Shadow7.sbP (start j)) ++
        (cell (start j) (Shadow7.sbP (start j)) ++ before5Tail (start j)) := by
  obtain ⟨hc, hr⟩ := prefix_cut_noop j hi
  unfold DeadJoin.before5 DeadJoin.beforePre5Cut before5Tail
  rw [pre5_prefix, FlagLeave.cut_append, hc, hr]
  simp only [List.length_nil, Nat.sub_zero, List.append_assoc]

private theorem fwd_app (a b : List Gate) :
    GateMirror.forward (a ++ b) = GateMirror.forward a ++ GateMirror.forward b := List.map_append

private theorem inv_app (a b : List Gate) :
    inverse (a ++ b) = inverse b ++ inverse a := DeadJoin.inverse_append a b

theorem before5Row_counts (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (before5Row (start j))) + 1 =
      toffoliCount (GateMirror.forward (DeadJoin.before5 (start j))) ∧
    toffoliCount (inverse (before5Row (start j))) =
      toffoliCount (inverse (DeadJoin.before5 (start j))) ∧
    measurementCount (GateMirror.forward (before5Row (start j))) =
      measurementCount (GateMirror.forward (DeadJoin.before5 (start j))) + 1 ∧
    measurementCount (inverse (before5Row (start j))) =
      measurementCount (inverse (DeadJoin.before5 (start j))) ∧
    gateSlots (GateMirror.forward (before5Row (start j))) =
      gateSlots (GateMirror.forward (DeadJoin.before5 (start j))) + 5 ∧
    gateSlots (inverse (before5Row (start j))) =
      gateSlots (inverse (DeadJoin.before5 (start j))) + 4 := by
  let s := start j; let h := Shadow7.sbP s
  have cells :
      toffoliCount (GateMirror.forward (shortCell s h)) + 1 = toffoliCount (GateMirror.forward (cell s h)) ∧
      toffoliCount (inverse (shortCell s h)) = toffoliCount (inverse (cell s h)) ∧
      measurementCount (GateMirror.forward (shortCell s h)) = measurementCount (GateMirror.forward (cell s h)) + 1 ∧
      measurementCount (inverse (shortCell s h)) = measurementCount (inverse (cell s h)) ∧
      gateSlots (GateMirror.forward (shortCell s h)) = gateSlots (GateMirror.forward (cell s h)) + 5 ∧
      gateSlots (inverse (shortCell s h)) = gateSlots (inverse (cell s h)) + 4 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨a,b,c,d,e,f⟩ := cells
  rw [before5_split j hi, before5Row]
  simp only [s, h, fwd_app, inv_app, toffoliCount_append,
    measurementCount_append, gateSlots_append] at a b c d e f ⊢
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem before5Row_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val ≤ 24)
    (covered : AllW P (DeadJoin.before5 (start j))) :
    AllW P (before5Row (start j)) := by
  let s := start j; let b := Shadow7.sbP s
  rw [before5_split j hi, allW_append_iff, allW_append_iff] at covered
  have hz : P (b+1579) :=
    covered.1 (.cx (s+b+47) (b+1579)) (List.mem_cons_self ..) _ (by simp [Gate.wires])
  have onCell := covered.2.1 (.ccx (s+30) (b+801) (s+b+46)) (by simp [cell, s, b])
  have hc := onCell (s+30) (by simp [Gate.wires])
  have hy := onCell (b+801) (by simp [Gate.wires])
  have hx := onCell (s+b+46) (by simp [Gate.wires])
  have sub : AllW P (shortCell s b) := by
    intro gate hg q hq
    simp only [shortCell, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;> aesop
  rw [before5Row, allW_append_iff, allW_append_iff]
  exact ⟨covered.1, sub, covered.2.2⟩

theorem before5Row_proper (j : Fin 26) (hi : j.val ≤ 24)
    (old : ∀ g ∈ DeadJoin.before5 (start j), proper g = true) :
    ∀ g ∈ before5Row (start j), proper g = true := by
  have physical : ∀ i : Fin 26, (shortCell (start i) (Shadow7.sbP (start i))).all proper = true := by decide +kernel
  have keep := List.all_eq_true.mpr old
  rw [before5_split j hi] at keep
  simp only [List.all_append, Bool.and_eq_true] at keep
  apply List.all_eq_true.mp
  simp only [before5Row, List.all_append, Bool.and_eq_true]
  exact ⟨keep.1, physical j, keep.2.2⟩

def oldRow : List Gate := [.cx 1 2, .ccx 0 2 1, .cx 1 2]
def newRow : List Gate := [.cx 1 2, .cx 2 1, .cx 3 1, .pop 0 2 1, .cx 3 1, .cx 2 1, .cx 1 2]

private def packed (a b c d : Bool) := a.toNat + 2*b.toNat + 4*c.toNat + 8*d.toNat
private theorem packed_bits : ∀ a b c d : Bool, let x := packed a b c d
    x < 16 ∧ x.testBit 0 = a ∧ x.testBit 1 = b ∧ x.testBit 2 = c ∧ x.testBit 3 = d := by decide
private theorem forward_check : ∀ (x : Fin 16) (p m : Bool),
    (sim (GateMirror.forward oldRow) [] p x.val).2.testBit 2 = x.val.testBit 3 →
    sim (GateMirror.forward newRow) [m] p x.val = sim (GateMirror.forward oldRow) [] p x.val := by decide +kernel
private theorem return_check : ∀ (x : Fin 16) (p : Bool),
    (sim (GateMirror.forward oldRow) [] p x.val).2.testBit 2 = x.val.testBit 3 →
    sim (GateMirror.forward oldRow ++ GateMirror.inverse newRow) [] p x.val = (p,x.val) := by decide +kernel

private abbrev sites : Finset Wire := Finset.range 4
private theorem old_sites : wires (GateMirror.forward oldRow) ⊆ sites := by decide
private theorem new_sites : wires (GateMirror.forward newRow) ⊆ sites := by decide
private theorem return_sites : wires (GateMirror.forward oldRow ++ GateMirror.inverse newRow) ⊆ sites := by decide

private theorem run_rename_eq_of_eq (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b)
    (p q : Program) (hp : wires p ⊆ S) (hq : wires q ⊆ S)
    (mp mq : List Bool) (t s : State) (hph : t.phase = s.phase)
    (hb : ∀ a ∈ S, t.basis a = s.basis (f a))
    (heq : run p mp t = run q mq t) :
    run (renameProgram f p) mp s = run (renameProgram f q) mq s := by
  have rp := run_rename_pool f S hf p hp mp t s hph hb
  have rq := run_rename_pool f S hf q hq mq t s hph hb
  have hph_eq : (run (renameProgram f p) mp s).phase = (run (renameProgram f q) mq s).phase := by
    rw [rp.1, rq.1, heq]
  have hb_eq : (run (renameProgram f p) mp s).basis = (run (renameProgram f q) mq s).basis := by
    funext w
    by_cases hw : w ∈ S.image f
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      rw [rp.2 a ha, rq.2 a ha, heq]
    · rw [run_rename_pool_outside f S p hp mp s w hw, run_rename_pool_outside f S q hq mq s w hw]
  cases h1 : run (renameProgram f p) mp s
  cases h2 : run (renameProgram f q) mq s
  rw [h1, h2] at hph_eq hb_eq
  simp only at hph_eq hb_eq
  rw [hph_eq, hb_eq]

theorem placed_pair (f : Wire → Wire) (inj : ∀ a ∈ sites, ∀ b ∈ sites, f a = f b → a=b)
    (s : State) (companion : (run (renameProgram f (GateMirror.forward oldRow)) [] s).basis (f 2) = s.basis (f 3)) :
    (∀ m, run (renameProgram f (GateMirror.forward newRow)) m s = run (renameProgram f (GateMirror.forward oldRow)) [] s) ∧
    (∀ n, run (renameProgram f (GateMirror.inverse newRow)) n (run (renameProgram f (GateMirror.forward oldRow)) [] s) = s) := by
  let x := packed (s.basis (f 0)) (s.basis (f 1)) (s.basis (f 2)) (s.basis (f 3))
  obtain ⟨lt,h0,h1,h2,h3⟩ := packed_bits (s.basis (f 0)) (s.basis (f 1)) (s.basis (f 2)) (s.basis (f 3))
  let t : State := ⟨s.phase, bitsOf x⟩
  have reads : ∀ q ∈ sites, t.basis q = s.basis (f q) := by
    intro q hq
    have hq' : q < 4 := Finset.mem_range.mp hq
    change x.testBit q = s.basis (f q)
    interval_cases q <;> assumption
  have physical := (run_rename_pool f sites inj _ old_sites [] t s rfl reads).2 2 (by decide)
  have allowed : (sim (GateMirror.forward oldRow) [] s.phase x).2.testBit 2 = x.testBit 3 := by
    have eq := physical.symm.trans (companion.trans (reads 3 (by decide)).symm)
    simpa only [t,run_sim,bitsOf] using eq
  constructor
  · intro m
    have trimmed : run (GateMirror.forward newRow) m t = run (GateMirror.forward newRow) [m.headD false] t := by cases m <;> rfl
    apply run_rename_eq_of_eq f sites inj _ _ new_sites old_sites m [] t s rfl reads
    rw [trimmed]
    simpa only [t,run_sim] using congrArg (fun y : Bool × Nat => State.mk y.1 (bitsOf y.2))
      (forward_check ⟨x,lt⟩ s.phase (m.headD false) allowed)
  · intro n
    have local_eq : run (GateMirror.forward oldRow ++ GateMirror.inverse newRow) n t = run [] [] t := by
      have trimmed : run (GateMirror.forward oldRow ++ GateMirror.inverse newRow) n t = run (GateMirror.forward oldRow ++ GateMirror.inverse newRow) [] t := rfl
      rw [trimmed]
      simpa only [t,run_sim,sim] using congrArg (fun y : Bool × Nat => State.mk y.1 (bitsOf y.2))
        (return_check ⟨x,lt⟩ s.phase allowed)
    have eq := run_rename_eq_of_eq f sites inj _ [] return_sites (by decide) n [] t s rfl reads local_eq
    change run (renameProgram f (GateMirror.forward oldRow) ++ renameProgram f (GateMirror.inverse newRow)) n s = s at eq
    rw [run_append] at eq
    exact eq

private theorem split_scan (s h : Nat) :
    Shadow7.fix0P s h = firstRows s h ++ (cell s h ++ (suffix s h ++ lastTwo h)) := rfl

private theorem lastTwo_zero (h : Nat) (t : State)
    (clean : (run (GateMirror.forward (lastTwo h)) [] t).basis (h+801) = false) :
    t.basis (h+801) = t.basis (h+1579) := by
  simp [lastTwo, GateMirror.forward, front, run, writeBit] at clean
  cases hb : t.basis (h+801) <;> cases hn : t.basis (h+1579) <;> simp_all

private theorem geometry : ∀ i : Fin 26, i.val ≤ 24 →
    let s := start i; let h := Shadow7.sbP s
    (suffix s h).all (fun g => decide (target g ≠ h+801)) = true ∧
    (suffix s h).all (fun g => decide (target g ≠ h+1579)) = true ∧
    (cell s h).all (fun g => decide (target g ≠ h+1579)) = true := by decide +kernel

private theorem ports_injective : ∀ j : Fin 26, j.val ≤ 24 →
    ∀ a ∈ sites, ∀ b ∈ sites,
      port (start j) (Shadow7.sbP (start j)) a = port (start j) (Shadow7.sbP (start j)) b → a = b := by
  have finite : ∀ (j : Fin 26) (a b : Fin 4),
      port (start j) (Shadow7.sbP (start j)) a.val = port (start j) (Shadow7.sbP (start j)) b.val → a = b := by
    decide +kernel
  intro j _ a ha b hb eq
  exact congrArg Fin.val (finite j ⟨a, Finset.mem_range.mp ha⟩ ⟨b, Finset.mem_range.mp hb⟩ eq)

private theorem firstRows_pure : ∀ j : Fin 26, j.val ≤ 24 →
    (firstRows (start j) (Shadow7.sbP (start j))).all (fun g => match g with | .make _ _ _ | .pop _ _ _ => false | _ => true) = true := by
  decide +kernel

private theorem pure_list_roundtrip (gs : List Gate)
    (hp : gs.all (fun g => match g with | .make _ _ _ | .pop _ _ _ => false | _ => true) = true)
    (phys : ∀ g ∈ gs, proper g = true) :
    (∀ m s, run (GateMirror.forward gs) m s = run (GateMirror.forward gs) [] s) ∧
    (∀ m s, run (inverse gs) m (run (GateMirror.forward gs) [] s) = s) ∧
    (∀ m s, run (GateMirror.forward gs) [] (run (inverse gs) m s) = s) := by
  induction gs with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons g tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hp
    obtain ⟨fih, rih, rih2⟩ := ih hp.2 (fun x hx => phys x (List.mem_cons_of_mem g hx))
    have pg := phys g (List.mem_cons_self ..)
    have hstep : (∀ m s, run (GateMirror.forward [g]) m s = run (GateMirror.forward [g]) [] s) ∧
        (∀ m s, run (inverse [g]) m (run (GateMirror.forward [g]) [] s) = s) ∧
        (∀ m s, run (GateMirror.forward [g]) [] (run (inverse [g]) m s) = s) := by
      cases g with
      | x a => refine ⟨fun _ _ => rfl, fun _ s => ?_, fun _ s => ?_⟩ <;>
          (obtain ⟨ph, f⟩ := s; simp [GateMirror.forward, inverse, front, back, run, writeBit])
      | cx a b =>
        simp only [proper, decide_eq_true_eq] at pg
        refine ⟨fun _ _ => rfl, fun _ s => ?_, fun _ s => ?_⟩ <;>
          (obtain ⟨ph, f⟩ := s; simp [GateMirror.forward, inverse, front, back, run, writeBit, pg, Ne.symm pg])
      | ccx a b c =>
        simp only [proper, decide_eq_true_eq] at pg
        refine ⟨fun _ _ => rfl, fun _ s => ?_, fun _ s => ?_⟩ <;>
          (obtain ⟨ph, f⟩ := s; simp [GateMirror.forward, inverse, front, back, run, writeBit, pg.1, pg.2, Ne.symm pg.1, Ne.symm pg.2])
      | make _ _ _ => simp at hp
      | pop _ _ _ => simp at hp
    have fcons : GateMirror.forward (g :: tl) = GateMirror.forward [g] ++ GateMirror.forward tl := rfl
    have icons : inverse (g :: tl) = inverse tl ++ inverse [g] := DeadJoin.inverse_append [g] tl
    refine ⟨fun m s => ?_, fun m s => ?_, fun m s => ?_⟩
    · rw [fcons, run_append, run_append, List.take_nil, List.drop_nil, hstep.1, fih]
    · rw [fcons, icons, run_append, run_append, List.take_nil, List.drop_nil, rih, hstep.2.1]
    · rw [fcons, icons, run_append, run_append, List.take_nil, List.drop_nil, hstep.2.2, rih2]

section
attribute [local irreducible] run

theorem companion_eq_sign (j : Fin 26) (hj : j.val ≤ 24) (t : State) (u v : Nat) (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) t.basis)
    (fresh : t.basis (Shadow7.e0P (start j) + 5) = false)
    (small : u < 2^15 * 2^(Shadow7.sbP (start j))) :
    let s := start j; let h := Shadow7.sbP s
    let before := run (GateMirror.forward (firstRows s h)) [] t
    (run (GateMirror.forward (cell s h)) [] before).basis (h+801) = before.basis (h+1579) := by
  let s := start j; let h := Shadow7.sbP s
  have scan := ((LeaveJ7.inputScan_result j (Nat.zero_le _) hj t [] u v G sg ready fresh).2.2.1
    15 (by decide)).2
  have pos : Shadow7.b0P (start j) - 1 + 15 = h + 801 := by
    simp only [Shadow7.b0P, h, s]; omega
  have clean : (run (GateMirror.forward (Shadow7.fix0P s h)) [] t).basis (h+801) = false := by
    rw [← pos, scan]
    apply Nat.testBit_lt_two_pow
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (lt_of_le_of_lt (Nat.sub_le _ _) small)
  let before := run (GateMirror.forward (firstRows s h)) [] t
  let after := run (GateMirror.forward (cell s h)) [] before
  let tailState := run (GateMirror.forward (suffix s h)) [] after
  rw [split_scan, fwd_app, fwd_app, fwd_app, run_append, run_append, run_append] at clean
  simp only [List.take_nil, List.drop_nil] at clean
  have tailEq := lastTwo_zero h tailState clean
  obtain ⟨clearB, clearN, cellN⟩ := geometry j hj
  have keeps (gs : List Gate) (q : Wire) (a : State)
      (safe : gs.all (fun g => decide (target g ≠ q)) = true) :
      (run (GateMirror.forward gs) [] a).basis q = a.basis q :=
    DeadJoin.keeps_of_targets57 gs q
      (fun g hg => of_decide_eq_true ((List.all_eq_true.mp safe) g hg)) [] a
  exact (keeps _ _ after clearB).symm.trans
    (tailEq.trans ((keeps _ _ after clearN).trans (keeps _ _ before cellN)))

theorem cell_pair (j : Fin 26) (hj : j.val ≤ 24) (t : State) (u v : Nat) (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) t.basis)
    (fresh : t.basis (Shadow7.e0P (start j) + 5) = false)
    (small : u < 2^15 * 2^(Shadow7.sbP (start j))) :
    let s := start j; let h := Shadow7.sbP s
    let before := run (GateMirror.forward (firstRows s h)) [] t
    (∀ m, run (GateMirror.forward (shortCell s h)) m before = run (GateMirror.forward (cell s h)) [] before) ∧
    (∀ n, run (inverse (shortCell s h)) n (run (GateMirror.forward (cell s h)) [] before) = before) := by
  let s := start j; let h := Shadow7.sbP s
  let before := run (GateMirror.forward (firstRows s h)) [] t
  have sign := companion_eq_sign j hj t u v G sg ready fresh small
  have oldP : renameProgram (port s h) (GateMirror.forward oldRow) = GateMirror.forward (cell s h) := by
    simp only [oldRow, cell, port, GateMirror.forward, front, renameProgram, renameInstr, List.map_cons, List.map_nil, List.append_nil, List.cons_append]
  have newP : renameProgram (port s h) (GateMirror.forward newRow) = GateMirror.forward (shortCell s h) := by
    simp only [newRow, shortCell, port, GateMirror.forward, front, GateMirror.erase, renameProgram, renameInstr, renameCorrection, List.map_cons, List.map_nil, List.append_nil, List.cons_append]
  have invP : renameProgram (port s h) (inverse newRow) = inverse (shortCell s h) := by
    simp only [newRow, shortCell, port, inverse, GateMirror.forward, back, front, GateMirror.erase, renameProgram, renameInstr, renameCorrection, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.append_nil]
  obtain ⟨fwd, rev⟩ := placed_pair (port s h) (ports_injective j hj) before (by rw [oldP]; exact sign)
  rw [oldP, newP] at fwd; rw [oldP, invP] at rev
  exact ⟨fwd, rev⟩

theorem before5Row_pair (j : Fin 26) (hi : j.val ≤ 24) (s : State) (u v : Nat) (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (small : u < 2^15 * 2^(Shadow7.sbP (start j)))
    (phys : ∀ g ∈ DeadJoin.before5 (start j), proper g = true)
    (orig_det : ∀ m, run (GateMirror.forward (DeadJoin.referenceOps (start j))) m s =
      run (GateMirror.forward (DeadJoin.referenceOps (start j))) [] s)
    (fwd5 : ∀ m, run (GateMirror.forward (DeadJoin.before5 (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (DeadJoin.after7K (start j))) m s =
      run (GateMirror.forward (DeadJoin.referenceOps (start j))) m s)
    (rev5 : ∀ m n, run (inverse (DeadJoin.after7K (start j)) ++ CRTBarrel.barrel (start j) true ++
        inverse (DeadJoin.before5 (start j))) n
      (run (GateMirror.forward (DeadJoin.before5 (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (DeadJoin.after7K (start j))) m s) = s) :
    (∀ m, run (GateMirror.forward (before5Row (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (DeadJoin.after7K (start j))) m s =
      run (GateMirror.forward (DeadJoin.referenceOps (start j))) m s) ∧
    (∀ m n, run (inverse (DeadJoin.after7K (start j)) ++ CRTBarrel.barrel (start j) true ++
        inverse (before5Row (start j))) n
      (run (GateMirror.forward (before5Row (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (DeadJoin.after7K (start j))) m s) = s) := by
  let st := start j; let h := Shadow7.sbP st
  have sp := before5_split j hi
  have pFR : ∀ g ∈ firstRows st h, proper g = true := fun g hg => phys g (by rw [sp]; exact List.mem_append_left _ hg)
  have pC : ∀ g ∈ cell st h, proper g = true := fun g hg => phys g (by rw [sp]; exact List.mem_append_right _ (List.mem_append_left _ hg))
  obtain ⟨fFR, rFR, rFR2⟩ := pure_list_roundtrip (firstRows st h) (firstRows_pure j hi) pFR
  obtain ⟨fC, rC, rC2⟩ := pure_list_roundtrip (cell st h) rfl pC
  obtain ⟨cFwd, cRev⟩ := cell_pair j hi s u v G sg ready fresh small
  have hmcF : measurementCount (GateMirror.forward (firstRows st h)) = 0 := by
    have := firstRows_pure j hi
    revert this; generalize firstRows st h = l; intro hl
    induction l with
    | nil => rfl
    | cons g tl ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hl
      have h1 : measurementCount (GateMirror.forward [g]) = 0 := by cases g <;> simp_all [GateMirror.forward, front, measurementCount]
      change measurementCount (GateMirror.forward [g] ++ GateMirror.forward tl) = 0
      rw [measurementCount_append, h1, ih hl.2]
  have hmcC : measurementCount (GateMirror.forward (cell st h)) = 0 := rfl
  have hFwd : ∀ m, run (GateMirror.forward (before5Row st) ++ CRTBarrel.barrel st false ++
      GateMirror.forward (DeadJoin.after7K st)) m s =
      run (GateMirror.forward (DeadJoin.referenceOps st)) m s := by
    intro m
    let m' := m.drop (measurementCount (GateMirror.forward (shortCell st h)))
    have h5m := fwd5 m'
    rw [before5Row, fwd_app, fwd_app]
    simp only [List.append_assoc]
    rw [run_append, run_append, fFR, hmcF, List.drop_zero, cFwd]
    rw [sp, fwd_app, fwd_app] at h5m
    simp only [List.append_assoc] at h5m
    rw [run_append, run_append, fFR, hmcF, List.drop_zero, fC, hmcC, List.drop_zero] at h5m
    exact h5m.trans ((orig_det m').trans (orig_det m).symm)
  refine ⟨hFwd, fun m n => ?_⟩
  rw [hFwd m, orig_det m, ← orig_det [], ← fwd5 []]
  let endS := run (GateMirror.forward (DeadJoin.before5 st) ++ CRTBarrel.barrel st false ++
    GateMirror.forward (DeadJoin.after7K st)) [] s
  have hrev := rev5 [] n
  change run (inverse (DeadJoin.after7K st) ++ CRTBarrel.barrel st true ++ inverse (DeadJoin.before5 st)) n endS = s at hrev
  let midP := inverse (DeadJoin.after7K st) ++ CRTBarrel.barrel st true ++ inverse (before5Tail st)
  have hInv5 : inverse (DeadJoin.after7K st) ++ CRTBarrel.barrel st true ++ inverse (DeadJoin.before5 st) =
      midP ++ (inverse (cell st h) ++ inverse (firstRows st h)) := by
    rw [sp, inv_app, inv_app]; simp only [midP, st, h, List.append_assoc]
  have hInvR : inverse (DeadJoin.after7K st) ++ CRTBarrel.barrel st true ++ inverse (before5Row st) =
      midP ++ (inverse (shortCell st h) ++ inverse (firstRows st h)) := by
    rw [before5Row, inv_app, inv_app]; simp only [midP, st, h, List.append_assoc]
  rw [hInv5, run_append, run_append] at hrev
  have hMid : run midP (n.take (measurementCount midP)) endS =
      run (GateMirror.forward (cell st h)) [] (run (GateMirror.forward (firstRows st h)) [] s) := by
    have h1 := congrArg (run (GateMirror.forward (firstRows st h)) []) hrev
    rw [rFR2] at h1
    have h2 := congrArg (run (GateMirror.forward (cell st h)) []) h1
    rw [rC2] at h2
    exact h2
  rw [hInvR, run_append, run_append, hMid, cRev, rFR]

end

end ECDSAAdd.Entrant.StairPacket.ScanRowGordo
end
-- ==== end ScanRowGordo ====



-- ==== begin SplitLeafSquare (folded into CRT to keep 18 modules; credited to dadon 568bda28) ====

/-! # Split 65-bit Karatsuba leaves for the concrete square -/

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.SplitLeafSquare
open Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
  StairSquareContract StairSquareAssembly StairSquareHolesCore StairSquareDirectFold
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Common wire definitions and allowed-site table -/

abbrev hs : List Wire := StairSqLoopA.hostDomain

/-- All non-hole, non-flag/swap wires in the concrete square layout and external pool. -/
def allowedWires : List Wire :=
  (K0.wires ++ E0 ++ [G0, D0]).filter (fun q => !hs.contains q && q != 4761 && q != 4834 && q != 4875)

theorem K0_eq : K0 = StairSquareBChecks.K4DQ.LBF := StairSquareBChecks.K4DQ.LB_eq

def E0F : List Wire := List.range' 5093 51 ++ List.range' 5399 246 ++ List.range' 5648 3

theorem E0_eq : E0 = E0F := by
  change (List.range' 978 51).map Baselines.layout.core.poolWire ++
      (List.range' 1284 246).map Baselines.layout.core.poolWire ++
      (List.range' 1533 3).map Baselines.layout.core.poolWire = E0F
  rw [StairSquareBChecks.K4DQ.blk 978 51 (by decide),
      StairSquareBChecks.K4DQ.blk 1284 246 (by decide),
      StairSquareBChecks.K4DQ.blk 1533 3 (by decide)]
  rfl

theorem G0_eq : G0 = 4113 := by decide +kernel
theorem D0_eq : D0 = 5655 := StairSquareBChecks.K4DQ.pw_lt 1540 (by decide)

private theorem holesA_lit : StairSqLoopA.holes = List.range' 4840 35 ++ List.range' 4876 4 := by
  rw [StairSqLoopA.holes, List.map_append, StairSquareBChecks.K4DQ.blk 725 35 (by decide),
      StairSquareBChecks.K4DQ.blk 761 4 (by decide)]

private theorem hs_lit : hs = (List.range' 4840 35 ++ List.range' 4876 4) ++ List.range' 4835 5 := by
  rw [hs, StairSqLoopA.hostDomain, holesA_lit, StairSquareBChecks.K4DQ.blk 720 5 (by decide)]

theorem allowedWires_eq :
    allowedWires = (StairSquareBChecks.K4DQ.LBF.wires ++ E0F ++ [4113, 5655]).filter
      (fun q => !((List.range' 4840 35 ++ List.range' 4876 4) ++ List.range' 4835 5).contains q &&
        q != 4761 && q != 4834 && q != 4875) := by
  rw [allowedWires, K0_eq, E0_eq, G0_eq, D0_eq, hs_lit]

private theorem sub_allowedWires (L : List Wire)
    (hIn : ∀ q ∈ L, q ∈ K0.wires ++ E0 ++ [G0, D0])
    (hOut : ∀ q ∈ L, q ∉ 4761 :: 4834 :: 4875 :: hs) :
    ∀ q ∈ L, q ∈ allowedWires := by
  intro q hq
  rw [allowedWires, List.mem_filter]
  refine ⟨hIn q hq, ?_⟩
  have ho := hOut q hq
  simp only [List.mem_cons, not_or] at ho
  simp [ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

private theorem not_mem_allowedWires_4834 : (4834 : Wire) ∉ allowedWires := by
  rw [allowedWires, List.mem_filter]; simp

private theorem not_mem_allowedWires_4875 : (4875 : Wire) ∉ allowedWires := by
  rw [allowedWires, List.mem_filter]; simp

private theorem hosts88_fast : LowAccCarryDevelop.hosts88 =
    FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
      (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4) := by
  rw [LowAccCarryDevelop.hosts88, LowAccCarryDevelop.loans88]
  change FullBTemp.hostR K0 :: FullBTemp.hostP K0 :: (FullBTemp.loans K0 ++ (accReg K0).take 4) = _
  rw [K0_eq]

private theorem hostsBSup_fast : ReorderedBSupportResearch.hosts =
    StairSquareBChecks.K4DQ.LBF.core.sumCarry ::
      (FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4)) := by
  rw [ReorderedBSupportResearch.hosts, hosts88_fast]
  change K0.core.sumCarry :: _ = _
  rw [K0_eq]

private theorem hostsB95_fast : B95Research.hosts =
    (StairSquareBChecks.K4DQ.LBF.core.sumCarry ::
      (FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4))) ++
      [4757, 4758, 4759, 4505, 4506, 4507] := by
  rw [B95Research.hosts, hostsBSup_fast]

private theorem keepKB_fast : B95Research.keepK =
    ((StairSquareBChecks.K4DQ.LBF.core.sumCarry ::
      (FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4))) ++
      [4757, 4758, 4759, 4505, 4506, 4507]).filter
      (fun q => !(((FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4)).take 44).contains q)) := by
  rw [B95Research.keepK, hostsB95_fast, hosts88_fast]

private theorem hsC_fast : C163Low4Middle.hs =
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4 := by
  change (K0.core.work.drop 165 ++ [D0]) ++ K0.core.work.take 4 = _
  rw [K0_eq, D0_eq]

private theorem hostsCFix_fast : ReorderedCFixed.hosts =
    StairSquareBChecks.K4DQ.LBF.core.work.getD 163 0 ::
    StairSquareBChecks.K4DQ.LBF.core.work.getD 164 0 ::
    StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 ::
    ((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4) := by
  rw [ReorderedCFixed.hosts, hsC_fast]
  change K0.core.work.getD 163 0 :: K0.core.work.getD 164 0 :: K0.core.product.getD 1 0 :: _ = _
  rw [K0_eq]

private theorem hostsC105_fast : C105Research.hosts =
    (StairSquareBChecks.K4DQ.LBF.core.work.getD 163 0 ::
     StairSquareBChecks.K4DQ.LBF.core.work.getD 164 0 ::
     StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 ::
     ((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4)) ++
      [4757, 4758, 4759, 4505, 4506, 4507] := by
  rw [C105Research.hosts, hostsCFix_fast]

private theorem keepKC_fast : C105Research.keepK =
    ((StairSquareBChecks.K4DQ.LBF.core.work.getD 163 0 ::
      StairSquareBChecks.K4DQ.LBF.core.work.getD 164 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 ::
      ((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4)) ++
      [4757, 4758, 4759, 4505, 4506, 4507]).filter
      (fun q => !((((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4).take 44).contains q)) := by
  rw [C105Research.keepK, hostsC105_fast, hsC_fast]

private def hsAF : List Wire :=
  ((((StairSquareBChecks.K4DQ.LBF.core.work.drop 163).take 33 ++ (StairSquareBChecks.K4DQ.LBF.core.work.drop 255).take 1 ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 227).take 28 ++ (StairSquareBChecks.K4DQ.LBF.core.work.drop 201).take 10 ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 212).take 15 ++ (StairSquareBChecks.K4DQ.LBF.core.work.drop 211).take 1 ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 196).take 5) ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 161).take 2) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4) ++ [5655]

private theorem hsA_fast : ReorderedAFixed.hs = hsAF := by
  rw [show ReorderedAFixed.hs = A161Low4Geometry.hs100 from rfl, A161Low4Geometry.hs100,
      A161Low4Geometry.hs99, A161Low4Geometry.loans93, hsAF]
  change ((((K0.core.work.drop 163).take 33 ++ (K0.core.work.drop 255).take 1 ++
      (K0.core.work.drop 227).take 28 ++ (K0.core.work.drop 201).take 10 ++
      (K0.core.work.drop 212).take 15 ++ (K0.core.work.drop 211).take 1 ++
      (K0.core.work.drop 196).take 5) ++
      (K0.core.work.drop 161).take 2) ++ K0.core.work.take 4) ++ [D0] = _
  rw [K0_eq, D0_eq]

private theorem hostsAFix_fast : ReorderedAFixed.hosts =
    StairSquareBChecks.K4DQ.LBF.core.sumCarry :: (StairSquareBChecks.K4DQ.LBF.core.product.drop 256).getD 1 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 :: hsAF := by
  rw [ReorderedAFixed.hosts, hsA_fast]
  change K0.core.sumCarry :: (K0.core.product.drop 256).getD 1 0 :: K0.core.product.getD 1 0 :: _ = _
  rw [K0_eq]

private theorem hostsA109_fast : A109Research.hosts =
    (StairSquareBChecks.K4DQ.LBF.core.sumCarry :: (StairSquareBChecks.K4DQ.LBF.core.product.drop 256).getD 1 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 :: hsAF) ++ [4757, 4758, 4759, 4505, 4506, 4507] := by
  rw [A109Research.hosts, hostsAFix_fast]

private theorem keepKA_fast : A109Research.keepK =
    ((StairSquareBChecks.K4DQ.LBF.core.sumCarry :: (StairSquareBChecks.K4DQ.LBF.core.product.drop 256).getD 1 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 :: hsAF) ++ [4757, 4758, 4759, 4505, 4506, 4507]).filter
      (fun q => !((hsAF.take 44).contains q)) := by
  rw [A109Research.keepK, hostsA109_fast, hsA_fast]

/-- Spilled T5 wires inside `K0.core.work` (evicted from carry caches during the body). -/
def workTA : List Wire :=
  (A109Research.keepK.filter (fun q => (K0.core.work.drop 163).contains q)).take 32

def workTB : List Wire :=
  (B95Research.keepK.filter (fun q => (K0.core.work.drop 207).contains q)) ++
  (K0.core.work.drop 196).take 2 ++ [D0]

def workTC : List Wire := (K0.core.work.drop 209).take 34

/-- Twenty-wire swap moving `work[196..197]` and `work[207..224]` off `StairSquareBEFoldK.efold` onto clean `work[225..255]` hosts. -/
def efSwapB : List (Wire × Wire) :=
  ((B95Research.keepK.filter (fun q => (K0.core.work.drop 207).contains q && !((K0.core.work.drop 225).contains q))) ++
    (K0.core.work.drop 196).take 2).zip
    ((LowAccCarryDevelop.hosts88.take 44).filter (fun q => (K0.core.work.drop 225).contains q))

theorem workTA_def :
    workTA = (A109Research.keepK.filter (fun q => (StairSquareBChecks.K4DQ.LBF.core.work.drop 163).contains q)).take 32 := by
  rw [workTA, K0_eq]

theorem workTB_def :
    workTB = (B95Research.keepK.filter (fun q => (StairSquareBChecks.K4DQ.LBF.core.work.drop 207).contains q)) ++
      (StairSquareBChecks.K4DQ.LBF.core.work.drop 196).take 2 ++ [5655] := by
  rw [workTB, K0_eq, D0_eq]

theorem workTC_def :
    workTC = (StairSquareBChecks.K4DQ.LBF.core.work.drop 209).take 34 := by
  rw [workTC, K0_eq]

theorem efSwapB_def :
    efSwapB = ((B95Research.keepK.filter (fun q =>
        (StairSquareBChecks.K4DQ.LBF.core.work.drop 207).contains q &&
        !((StairSquareBChecks.K4DQ.LBF.core.work.drop 225).contains q))) ++
      (StairSquareBChecks.K4DQ.LBF.core.work.drop 196).take 2).zip
      ((LowAccCarryDevelop.hosts88.take 44).filter (fun q => (StairSquareBChecks.K4DQ.LBF.core.work.drop 225).contains q)) := by
  rw [efSwapB, K0_eq]

private def workTAF : List Wire :=
  [4738, 4739, 4740, 4741, 4742, 4743, 4744, 4745, 4746, 4747, 4748, 4749, 4750, 4751, 4752, 4753,
   4754, 4755, 4702, 4703, 4704, 4705, 4706, 4707, 4708, 4709, 4710, 4711, 4713, 4714, 4715, 4716]

private def workTBF : List Wire :=
  [4747, 4748, 4749, 4750, 4751, 4752, 4753, 4754, 4755, 4708, 4709, 4710, 4711, 4712, 4714, 4715,
   4716, 4717, 4718, 4719, 4720, 4721, 4722, 4723, 4724, 4725, 4726, 4727, 4713, 4697, 4698, 5655]

private def workTCF : List Wire := List.range' 4710 34

private def efSwapBF : List (Wire × Wire) :=
  [(4708, 4756), (4709, 4728), (4710, 4729), (4711, 4730), (4712, 4731),
   (4714, 4732), (4715, 4733), (4716, 4734), (4717, 4735), (4718, 4736),
   (4719, 4737), (4720, 4738), (4721, 4739), (4722, 4740), (4723, 4741),
   (4724, 4742), (4725, 4743), (4713, 4744), (4697, 4745), (4698, 4746)]

theorem workTA_lit : workTA = workTAF := by rw [workTA_def, keepKA_fast]; decide +kernel
theorem workTB_lit : workTB = workTBF := by rw [workTB_def, keepKB_fast]; decide +kernel
theorem workTC_lit : workTC = workTCF := by rw [workTC_def]; decide +kernel
theorem efSwapB_lit : efSwapB = efSwapBF := by rw [efSwapB_def, keepKB_fast, hosts88_fast]; decide +kernel

theorem work_T_geometry :
    workTA.length = 32 ∧ workTA.Nodup ∧
    workTB.length = 32 ∧ workTB.Nodup ∧
    workTC.length = 34 ∧ workTC.Nodup ∧
    efSwapB.length = 20 ∧
    (holesOf efSwapB ++ hostsOf efSwapB).Nodup ∧
    (∀ q ∈ workTA, q ∈ A109Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
    (∀ q ∈ workTB.take 31, q ∈ B95Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
    (∀ q ∈ workTC, q ∈ C105Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
    (∀ q ∈ workTA, q ∈ allowedWires) ∧
    (∀ q ∈ workTB, q ∈ allowedWires) ∧
    (∀ q ∈ workTC, q ∈ allowedWires) ∧
    (∀ ab ∈ efSwapB, ab.1 ∈ workTB ∧ ab.2 ∈ K0.core.work.drop 207 ∧
      ab.2 ∈ LowAccCarryDevelop.hosts88.take 44 ∧ ab.2 ∉ workTB ∧ ab.2 ∈ allowedWires ∧ ab.2 ≠ K0.core.normFlag) ∧
    (∀ q ∈ workTB, q ∉ holesOf efSwapB → q ∉ StairSquareBEFold.carryB K0) := by
  have hAllowedAll : ∀ q ∈ workTA ++ workTB ++ workTC ++ hostsOf efSwapB, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, hs_lit]; decide +kernel))
  have hAllowedA : ∀ q ∈ workTA, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hAllowedB : ∀ q ∈ workTB, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hAllowedC : ∀ q ∈ workTC, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hAllowedEf : ∀ q ∈ hostsOf efSwapB, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hRest : workTA.length = 32 ∧ workTA.Nodup ∧
      workTB.length = 32 ∧ workTB.Nodup ∧
      workTC.length = 34 ∧ workTC.Nodup ∧
      efSwapB.length = 20 ∧
      (holesOf efSwapB ++ hostsOf efSwapB).Nodup ∧
      (∀ q ∈ workTA, q ∈ A109Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
      (∀ q ∈ workTB.take 31, q ∈ B95Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
      (∀ q ∈ workTC, q ∈ C105Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
      (∀ ab ∈ efSwapB, ab.1 ∈ workTB ∧ ab.2 ∈ K0.core.work.drop 207 ∧
        ab.2 ∈ LowAccCarryDevelop.hosts88.take 44 ∧ ab.2 ∉ workTB ∧ ab.2 ≠ K0.core.normFlag) ∧
      (∀ q ∈ workTB, q ∉ holesOf efSwapB → q ∉ StairSquareBEFold.carryB K0) := by
    rw [workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, keepKA_fast, keepKB_fast, keepKC_fast, hosts88_fast, K0_eq]; decide +kernel
  refine ⟨hRest.1, hRest.2.1, hRest.2.2.1, hRest.2.2.2.1, hRest.2.2.2.2.1, hRest.2.2.2.2.2.1,
    hRest.2.2.2.2.2.2.1, hRest.2.2.2.2.2.2.2.1, hRest.2.2.2.2.2.2.2.2.1, hRest.2.2.2.2.2.2.2.2.2.1,
    hRest.2.2.2.2.2.2.2.2.2.2.1, hAllowedA, hAllowedB, hAllowedC, ?_, hRest.2.2.2.2.2.2.2.2.2.2.2.2⟩
  intro ab hab
  have hr := hRest.2.2.2.2.2.2.2.2.2.2.2.1 ab hab
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hAllowedEf ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩), hr.2.2.2.2⟩

/-! ## Clean-sum diagonal leaf wrappers (`makeC` / `clearC`) -/

section CleanDiag
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical

theorem makeC_clean (Q : KRegs) (w : Q.W) (he : Q.bank.length = 2 * Q.h) (hh : Q.h = 32 ∨ Q.h = 33)
    (hn : Q.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue Q.dst s.basis = 0) (hS0 : regValue Q.S s.basis = 0)
    (hT0 : regValue Q.T s.basis = 0) (hz0 : regValue Q.z s.basis = 0)
    (hp0 : regValue Q.pad s.basis = 0) (hc0 : regValue Q.carry s.basis = 0)
    (hi0 : s.basis Q.cin = false) :
    (run (LowZero18Diagonal.makeC Q) m s).phase = s.phase ∧
    regValue Q.dst (run (LowZero18Diagonal.makeC Q) m s).basis = (regValue Q.bank s.basis) ^ 2 ∧
    regValue Q.T (run (LowZero18Diagonal.makeC Q) m s).basis = 2 * regValue Q.lo s.basis * regValue Q.hi s.basis ∧
    ∀ q, q ∉ Q.dst → q ∉ Q.T → (run (LowZero18Diagonal.makeC Q) m s).basis q = s.basis q := by
  have hX0 : regValue (Q.S ++ Q.T) s.basis = 0 := by rw [regValue_append, hS0, hT0]; simp
  have r := LowZero18Diagonal.diag_sq_cl_make Q w he hh hn Q.z (fun _ h => h) s m hd0 hX0 hp0 hc0 hz0 hi0
  refine ⟨r.1, r.2.1, ?_, ?_⟩
  · rw [r.2.2.1.2, Q.lo_mod w, Q.hi_div w]
  · intro q hd hT
    by_cases hS : q ∈ Q.S
    · exact ((regValue_zero Q.S _).mp r.2.2.1.1 q hS).trans ((regValue_zero Q.S _).mp hS0 q hS).symm
    · exact r.2.2.2 q hd (fun hx => (List.mem_append.mp hx).elim hS hT)

theorem clearC_clean (Q : KRegs) (w : Q.W) (he : Q.bank.length = 2 * Q.h) (hh : Q.h = 32 ∨ Q.h = 33)
    (hn : Q.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue Q.dst s.basis = (regValue Q.bank s.basis) ^ 2)
    (hS0 : regValue Q.S s.basis = 0)
    (hT0 : regValue Q.T s.basis = 2 * regValue Q.lo s.basis * regValue Q.hi s.basis)
    (hz0 : regValue Q.z s.basis = 0) (hp0 : regValue Q.pad s.basis = 0)
    (hc0 : regValue Q.carry s.basis = 0) (hi0 : s.basis Q.cin = false) :
    (run (LowZero18Diagonal.clearC Q) m s).phase = s.phase ∧
    regValue Q.dst (run (LowZero18Diagonal.clearC Q) m s).basis = 0 ∧
    regValue Q.T (run (LowZero18Diagonal.clearC Q) m s).basis = 0 ∧
    ∀ q, q ∉ Q.dst → q ∉ Q.T → (run (LowZero18Diagonal.clearC Q) m s).basis q = s.basis q := by
  have hI : Q.invC (regValue Q.bank s.basis) s.basis := by
    refine ⟨hS0, ?_⟩
    rw [hT0, Q.lo_mod w, Q.hi_div w]
  have r := RawClearSquare.diag_sq_cl_clear Q w he hh hn Q.z (fun _ h => h) s m hd0 hI hp0 hc0 hz0 hi0
  have hST := (regValue_append Q.S Q.T _).symm.trans r.2.2.1
  have hST0 := Nat.add_eq_zero_iff.mp hST
  have hS1 : regValue Q.S (run (LowZero18Diagonal.clearC Q) m s).basis = 0 := hST0.1
  have hT1 : regValue Q.T (run (LowZero18Diagonal.clearC Q) m s).basis = 0 :=
    (Nat.mul_eq_zero.mp hST0.2).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
  refine ⟨r.1, r.2.1, hT1, ?_⟩
  intro q hd hT
  by_cases hS : q ∈ Q.S
  · exact ((regValue_zero Q.S _).mp hS1 q hS).trans ((regValue_zero Q.S _).mp hS0 q hS).symm
  · exact r.2.2.2 q hd (fun hx => (List.mem_append.mp hx).elim hS hT)

theorem makeC_physical (Q : KRegs) (w : Q.W) (hn : Q.all.Nodup) :
    GatePhysical (LowZero18Diagonal.makeC Q) :=
  (gatePhysical_append _ _).mpr ⟨LowZero18Diagonal.make_physical Q w hn, Q.scl1591_physical w hn⟩

theorem clearC_physical (Q : KRegs) (w : Q.W) (hn : Q.all.Nodup) :
    GatePhysical (LowZero18Diagonal.clearC Q) :=
  (gatePhysical_append _ _).mpr
    ⟨Q.smkT_physical w hn (Q.piece_physical hn).1, LowZero18Diagonal.clear_physical Q w hn⟩

theorem makeC_support (Q : KRegs) (w : Q.W) :
    wires (LowZero18Diagonal.makeC Q) ⊆ Q.all.toFinset := by
  rw [LowZero18Diagonal.makeC, wires_append]
  exact Finset.union_subset (LowZero18Diagonal.make_support Q w) (Q.scl1591_support w)

theorem clearC_support (Q : KRegs) (w : Q.W) :
    wires (LowZero18Diagonal.clearC Q) ⊆ Q.all.toFinset := by
  rw [LowZero18Diagonal.clearC, RawClearSquare.clearC, wires_append]
  exact Finset.union_subset (Q.smkT_support w (Q.piece_support w).1) (LowZero18Diagonal.clear_support Q w)

theorem makeC_counts (Q : KRegs) (w : Q.W) (he : Q.bank.length = 2 * Q.h) :
    toffoliCount (LowZero18Diagonal.makeC Q) = DiagSq.cost Q - 11 - DiagSq.parR Q ∧
    measurementCount (LowZero18Diagonal.makeC Q) = DiagSq.cost Q - 4 - DiagSq.parR Q + (Q.bank.length - Q.h) := by
  have m := LowZero18Diagonal.make_counts Q w he
  have sc := Q.scl1591_counts w
  simp only [LowZero18Diagonal.makeC, toffoliCount_append, measurementCount_append]
  exact ⟨by omega, by omega⟩

theorem diag32_counts (Q : KRegs) (w : Q.W) (hh : Q.h = 32) (hb : Q.bank.length = 64) :
    toffoliCount (LowZero18Diagonal.makeC Q) = toffoliCount (LowZero18Diagonal.make Q) ∧
    measurementCount (LowZero18Diagonal.makeC Q) = measurementCount (LowZero18Diagonal.make Q) + 32 ∧
    toffoliCount (LowZero18Diagonal.clearC Q) = toffoliCount (LowZero18Diagonal.clear Q) + 31 ∧
    measurementCount (LowZero18Diagonal.clearC Q) = measurementCount (LowZero18Diagonal.clear Q) + 32 := by
  have sc := Q.scl1591_counts w
  have sm := Q.smkT_counts w
  have pc := Q.piece_counts w
  simp only [LowZero18Diagonal.makeC, LowZero18Diagonal.clearC, LowZero18Diagonal.clear, RawClearSquare.clearC,
    toffoliCount_append, measurementCount_append]
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem diag33_counts (Q : KRegs) (w : Q.W) (hh : Q.h = 33) (hb : Q.bank.length = 66) :
    toffoliCount (LowZero18Diagonal.makeC Q) = toffoliCount (LowZero18Diagonal.make Q) ∧
    measurementCount (LowZero18Diagonal.makeC Q) = measurementCount (LowZero18Diagonal.make Q) + 33 ∧
    toffoliCount (LowZero18Diagonal.clearC Q) = toffoliCount (LowZero18Diagonal.clear Q) + 32 ∧
    measurementCount (LowZero18Diagonal.clearC Q) = measurementCount (LowZero18Diagonal.clear Q) + 33 := by
  have sc := Q.scl1591_counts w
  have sm := Q.smkT_counts w
  have pc := Q.piece_counts w
  simp only [LowZero18Diagonal.makeC, LowZero18Diagonal.clearC, LowZero18Diagonal.clear, RawClearSquare.clearC,
    toffoliCount_append, measurementCount_append]
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem diag33_exact (Q : KRegs) (w : Q.W) (hh : Q.h = 33) (hb : Q.bank.length = 66) :
    toffoliCount (LowZero18Diagonal.makeC Q) + toffoliCount (LowZero18Diagonal.clearC Q) = 3881 ∧
    measurementCount (LowZero18Diagonal.makeC Q) + measurementCount (LowZero18Diagonal.clearC Q) = 4152 := by
  have he : Q.bank.length = 2 * Q.h := by omega
  have ⟨mt, mm⟩ := LowZero18Diagonal.make_counts Q w he
  have ⟨ct, cm⟩ := RawClearSquare.clear_counts Q w he
  have ⟨d1, d2, d3, d4⟩ := diag33_counts Q w hh hb
  have hc : DiagSq.cost Q = 2048 := by simp only [DiagSq.cost, hb, hh]; decide +kernel
  have hlo : Q.lo.length = 33 := by simp [KRegs.lo, hb, hh]
  have hhi : Q.hi.length = 33 := by simp [KRegs.hi, hb, hh]
  have hS : Q.S.length = 34 := by have := w.S; omega
  have hp : DiagSq.parR Q = 2 := by simp only [DiagSq.parR, hlo, hhi, hS]; decide +kernel
  rw [hc, hp] at mt mm
  rw [hc, hh] at ct
  rw [hc] at cm
  change toffoliCount (LowZero18Diagonal.clearC Q) = toffoliCount (RawClearSquare.clear Q) + 32 at d3
  change measurementCount (LowZero18Diagonal.clearC Q) = measurementCount (RawClearSquare.clear Q) + 33 at d4
  exact ⟨by omega, by omega⟩

theorem tsq65_exact (xs dst pad carry : List Wire) (cin : Wire)
    (hx : xs.length = 65) (hd : dst.length = 130) (hp : 1 ≤ pad.length) (hc : 129 ≤ carry.length) :
    toffoliCount (TrimMid.tsqM xs dst pad carry cin) +
      toffoliCount (PlainKnownClear.program xs dst pad carry cin) = 4286 ∧
    measurementCount (TrimMid.tsqM xs dst pad carry cin) +
      measurementCount (PlainKnownClear.program xs dst pad carry cin) = 4413 := by
  have q := TrimSquare3.tsq3_counts xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have qm := TrimMid.tsqM_counts_rel xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have q4 := TrimSquare4.tsqcM4_counts xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have qn := PlainKnownClear.program_counts xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have hk : signedSquareRowsCount 65 + 130 - 3 = 2207 := by decide +kernel
  rw [hx, hd] at q
  rw [hx, TrimMid.par_65] at qm qn
  exact ⟨by omega, by omega⟩

end CleanDiag

/-! ## Split-65 Karatsuba core (`R` + `R8` + three clean-sum diagonal leaves) -/

/-- Configuration of one 128- or 129-bit split Karatsuba leaf with `R8.z` reusing `R.S.take 62`. -/
structure SplitCfg where
  n : Nat
  src : List Wire
  dst : List Wire
  workT : List Wire
  zReal4 : List Wire
  zpad : Wire
  zdst0 : Wire
  zdst1 : Wire
  carry : List Wire
  T1 : List Wire
  T2 : List Wire
  T5 : List Wire

namespace SplitCfg
variable (c : SplitCfg)

def bank : List Wire := K0.inputBank.take c.n
def S : List Wire := ((LowZero18LowK.ktmp K0).take 66).take (c.n - 63)
def T : List Wire := (E0.take 132).take (2 * (c.n - 63))

def R : KRegs :=
  { h := 64, bank := c.bank, dst := c.dst, S := c.S, T := c.T,
    z := c.zReal4 ++ List.range' 20000 58, pad := K0.leafPad, carry := c.carry, cin := K0.core.cin }

def R8 : KRegs :=
  { h := 64, bank := c.bank, dst := c.dst, S := List.range' 20100 (c.n - 63), T := c.T,
    z := c.S.take 62, pad := K0.leafPad, carry := c.carry, cin := K0.core.cin }

def qCarry : List Wire := c.carry.take 100
def qZ30 : List Wire := (c.carry.drop 100).take 30
def qZ31 : List Wire := (c.carry.drop 100).take 31
def qS33 : List Wire := (c.carry.drop 131).take 33
def qS34 : List Wire := (c.carry.drop 131).take 34

def Q1 : KRegs :=
  { h := 32, bank := c.R.lo, dst := c.R.dlo, S := c.qS33, T := c.T1,
    z := c.qZ30, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }

def Q2 : KRegs :=
  if c.n = 128 then
    { h := 32, bank := c.R.hi, dst := c.R.dhi, S := c.qS33, T := c.T2,
      z := c.qZ30, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }
  else
    { h := 33, bank := c.R.hi ++ [c.zpad], dst := c.R.dhi ++ [c.zdst0, c.zdst1], S := c.qS34, T := c.T2,
      z := c.qZ31, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }

def Q5 : KRegs :=
  if c.n = 128 then
    { h := 33, bank := c.S ++ [c.zpad], dst := c.T ++ [c.zdst0, c.zdst1], S := c.qS34, T := c.T5,
      z := c.qZ31, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }
  else
    { h := 33, bank := c.S, dst := c.T, S := c.qS34, T := c.T5,
      z := c.qZ31, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }

/-- Wires that remain non-zero between `make` and `clear` (in addition to `dst`). -/
def liveT : List Wire := c.T ++ c.T1 ++ c.T2 ++ c.T5

/-- All real wires (all `< 20000`) used by `make` and `clear`. -/
def realAll : List Wire :=
  K0.core.cin :: c.bank ++ c.dst ++ c.S ++ c.T ++ c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++
    K0.leafPad ++ c.carry ++ c.T1 ++ c.T2 ++ c.T5

/-- All scratch wires that must start zero and return to zero after `make`. -/
def cleanScratch : List Wire :=
  c.S ++ c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++ K0.leafPad ++ c.carry

def make : Program :=
  LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5 ++ c.R.m6h ++ c.R.m7k ++ c.R.scl1591 ++ c.R8.m8z

def clear : Program :=
  c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    LowZero18Diagonal.clearC c.Q5 ++ c.R.scl1591 ++
    LowZero18Diagonal.clearC c.Q2 ++ LowZero18Diagonal.clearC c.Q1

end SplitCfg

/-! ### Concrete configurations for Branches A, B, and C -/

private def cleanRem (n : Nat) (wT : List Wire) : List Wire :=
  (K0.leafCarry.filter (fun q => !wT.contains q)) ++
  (if n = 128 then [(LowZero18LowK.ktmp K0).getD 65 0] else []) ++
  [(LowZero18LowK.ktmp K0).getD 66 0] ++
  ((LowZero18LowK.ktmp K0).drop 113).take 10

def cfgA : SplitCfg :=
  let rem := cleanRem 128 workTA
  { n := 128, src := K0.core.low, dst := K0.core.product.take 256, workT := workTA,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0.drop 132).take 66, T2 := (E0.drop 232).take 66,
    T5 := [E0.getD 231 0] ++ (E0.drop 198).take 33 ++ workTA ++ [E0.getD 298 0, E0.getD 299 0] }

def cfgB : SplitCfg :=
  let rem := cleanRem 128 workTB
  { n := 128, src := K0.core.high, dst := K0.core.product.take 256, workT := workTB,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0.drop 132).take 66, T2 := (E0.drop 232).take 66,
    T5 := [E0.getD 231 0] ++ (E0.drop 198).take 33 ++ workTB ++ [E0.getD 298 0, E0.getD 299 0] }

def cfgC : SplitCfg :=
  let rem := cleanRem 129 workTC
  { n := 129, src := K0.core.sum, dst := K0.core.product, workT := workTC,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0.drop 132).take 66, T2 := (E0.drop 232).take 68,
    T5 := (E0.drop 198).take 34 ++ workTC }

/-! ### Fast `K4DQ.LBF` / `E0F` / literal mirrors for kernel evaluation -/

private def cleanRemF (n : Nat) (wT : List Wire) : List Wire :=
  (StairSquareBChecks.K4DQ.LBF.leafCarry.filter (fun q => !wT.contains q)) ++
  (if n = 128 then [(LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).getD 65 0] else []) ++
  [(LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).getD 66 0] ++
  ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).drop 113).take 10

private def cfgAF : SplitCfg :=
  let rem := cleanRemF 128 workTAF
  { n := 128, src := StairSquareBChecks.K4DQ.LBF.core.low, dst := StairSquareBChecks.K4DQ.LBF.core.product.take 256, workT := workTAF,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0F.drop 132).take 66, T2 := (E0F.drop 232).take 66,
    T5 := [E0F.getD 231 0] ++ (E0F.drop 198).take 33 ++ workTAF ++ [E0F.getD 298 0, E0F.getD 299 0] }

private def cfgBF : SplitCfg :=
  let rem := cleanRemF 128 workTBF
  { n := 128, src := StairSquareBChecks.K4DQ.LBF.core.high, dst := StairSquareBChecks.K4DQ.LBF.core.product.take 256, workT := workTBF,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0F.drop 132).take 66, T2 := (E0F.drop 232).take 66,
    T5 := [E0F.getD 231 0] ++ (E0F.drop 198).take 33 ++ workTBF ++ [E0F.getD 298 0, E0F.getD 299 0] }

private def cfgCF : SplitCfg :=
  let rem := cleanRemF 129 workTCF
  { n := 129, src := StairSquareBChecks.K4DQ.LBF.core.sum, dst := StairSquareBChecks.K4DQ.LBF.core.product, workT := workTCF,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0F.drop 132).take 66, T2 := (E0F.drop 232).take 68,
    T5 := (E0F.drop 198).take 34 ++ workTCF }

private theorem cfgA_fast : cfgA = cfgAF := by rw [cfgA, cfgAF, cleanRem, cleanRemF, workTA_lit, K0_eq, E0_eq]
private theorem cfgB_fast : cfgB = cfgBF := by rw [cfgB, cfgBF, cleanRem, cleanRemF, workTB_lit, K0_eq, E0_eq]
private theorem cfgC_fast : cfgC = cfgCF := by rw [cfgC, cfgCF, cleanRem, cleanRemF, workTC_lit, K0_eq, E0_eq]

private theorem SplitCfg.bank_fast (c : SplitCfg) :
    c.bank = StairSquareBChecks.K4DQ.LBF.inputBank.take c.n := by rw [SplitCfg.bank, K0_eq]
private theorem SplitCfg.S_fast (c : SplitCfg) :
    c.S = ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) := by rw [SplitCfg.S, K0_eq]
private theorem SplitCfg.T_fast (c : SplitCfg) :
    c.T = (E0F.take 132).take (2 * (c.n - 63)) := by rw [SplitCfg.T, E0_eq]
private theorem SplitCfg.liveT_fast (c : SplitCfg) :
    c.liveT = (E0F.take 132).take (2 * (c.n - 63)) ++ c.T1 ++ c.T2 ++ c.T5 := by
  rw [SplitCfg.liveT, SplitCfg.T_fast]
private theorem SplitCfg.realAll_fast (c : SplitCfg) :
    c.realAll = StairSquareBChecks.K4DQ.LBF.core.cin :: StairSquareBChecks.K4DQ.LBF.inputBank.take c.n ++
      c.dst ++ ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) ++
      (E0F.take 132).take (2 * (c.n - 63)) ++ c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++
      StairSquareBChecks.K4DQ.LBF.leafPad ++ c.carry ++ c.T1 ++ c.T2 ++ c.T5 := by
  rw [SplitCfg.realAll, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]
private theorem SplitCfg.cleanScratch_fast (c : SplitCfg) :
    c.cleanScratch = ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) ++
      c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++ StairSquareBChecks.K4DQ.LBF.leafPad ++ c.carry := by
  rw [SplitCfg.cleanScratch, SplitCfg.S_fast, K0_eq]
private def SplitCfg.RF (c : SplitCfg) : KRegs :=
  { h := 64, bank := StairSquareBChecks.K4DQ.LBF.inputBank.take c.n, dst := c.dst,
    S := ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63),
    T := (E0F.take 132).take (2 * (c.n - 63)), z := c.zReal4 ++ List.range' 20000 58,
    pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.carry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.R8F (c : SplitCfg) : KRegs :=
  { h := 64, bank := StairSquareBChecks.K4DQ.LBF.inputBank.take c.n, dst := c.dst,
    S := List.range' 20100 (c.n - 63), T := (E0F.take 132).take (2 * (c.n - 63)),
    z := (((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63)).take 62,
    pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.carry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.Q1F (c : SplitCfg) : KRegs :=
  { h := 32, bank := c.RF.lo, dst := c.RF.dlo, S := c.qS33, T := c.T1, z := c.qZ30,
    pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.Q2F (c : SplitCfg) : KRegs :=
  if c.n = 128 then
    { h := 32, bank := c.RF.hi, dst := c.RF.dhi, S := c.qS33, T := c.T2, z := c.qZ30,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }
  else
    { h := 33, bank := c.RF.hi ++ [c.zpad], dst := c.RF.dhi ++ [c.zdst0, c.zdst1],
      S := c.qS34, T := c.T2, z := c.qZ31,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.Q5F (c : SplitCfg) : KRegs :=
  if c.n = 128 then
    { h := 33, bank := ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) ++ [c.zpad],
      dst := (E0F.take 132).take (2 * (c.n - 63)) ++ [c.zdst0, c.zdst1],
      S := c.qS34, T := c.T5, z := c.qZ31,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }
  else
    { h := 33, bank := ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63),
      dst := (E0F.take 132).take (2 * (c.n - 63)),
      S := c.qS34, T := c.T5, z := c.qZ31,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private theorem SplitCfg.R_fast (c : SplitCfg) : c.R = c.RF := by
  rw [SplitCfg.R, SplitCfg.RF, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]
private theorem SplitCfg.R8_fast (c : SplitCfg) : c.R8 = c.R8F := by
  rw [SplitCfg.R8, SplitCfg.R8F, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]
private theorem SplitCfg.Q1_fast (c : SplitCfg) : c.Q1 = c.Q1F := by
  rw [SplitCfg.Q1, SplitCfg.Q1F, SplitCfg.R_fast, K0_eq]
private theorem SplitCfg.Q2_fast (c : SplitCfg) : c.Q2 = c.Q2F := by
  rw [SplitCfg.Q2, SplitCfg.Q2F, SplitCfg.R_fast, K0_eq]
private theorem SplitCfg.Q5_fast (c : SplitCfg) : c.Q5 = c.Q5F := by
  rw [SplitCfg.Q5, SplitCfg.Q5F, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]

/-- Valid geometry bundle for a concrete `SplitCfg`. -/
structure CfgValid (c : SplitCfg) : Prop where
  hn : c.n = 128 ∨ c.n = 129
  realNd : c.realAll.Nodup
  realLt : ∀ q ∈ c.realAll, q < 20000
  realAllowed : ∀ q ∈ c.realAll, q ∈ allowedWires
  bankLen : c.bank.length = c.n
  dstLen : c.dst.length = 2 * c.n
  sLen : c.S.length = c.n - 63
  tLen : c.T.length = 2 * (c.n - 63)
  z4Len : c.zReal4.length = 4
  carryLen : c.carry.length = 193
  padLen : K0.leafPad.length = 1
  t1Len : c.T1.length = 66
  t2Len : c.T2.length = if c.n = 128 then 66 else 68
  t5Len : c.T5.length = 68

theorem cfgA_valid : CfgValid cfgA := by
  have hnd : cfgA.realAll.Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [SplitCfg.realAll_fast, cfgA_fast]; decide +kernel)
  have hlt : ∀ q ∈ cfgA.realAll, q < 20000 := fun q hq =>
    of_decide_eq_true (List.all_eq_true.mp (by simp only [SplitCfg.realAll_fast, cfgA_fast]; decide +kernel :
      cfgA.realAll.all (fun x => decide (x < 20000)) = true) q hq)
  have hall : ∀ q ∈ cfgA.realAll, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgA_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgA_fast, hs_lit]; decide +kernel))
  refine ⟨Or.inl rfl, hnd, hlt, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cfgA_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq, E0_eq]; decide +kernel)

theorem cfgB_valid : CfgValid cfgB := by
  have hnd : cfgB.realAll.Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [SplitCfg.realAll_fast, cfgB_fast]; decide +kernel)
  have hlt : ∀ q ∈ cfgB.realAll, q < 20000 := fun q hq =>
    of_decide_eq_true (List.all_eq_true.mp (by simp only [SplitCfg.realAll_fast, cfgB_fast]; decide +kernel :
      cfgB.realAll.all (fun x => decide (x < 20000)) = true) q hq)
  have hall : ∀ q ∈ cfgB.realAll, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgB_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgB_fast, hs_lit]; decide +kernel))
  refine ⟨Or.inl rfl, hnd, hlt, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cfgB_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq, E0_eq]; decide +kernel)

theorem cfgC_valid : CfgValid cfgC := by
  have hnd : cfgC.realAll.Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [SplitCfg.realAll_fast, cfgC_fast]; decide +kernel)
  have hlt : ∀ q ∈ cfgC.realAll, q < 20000 := fun q hq =>
    of_decide_eq_true (List.all_eq_true.mp (by simp only [SplitCfg.realAll_fast, cfgC_fast]; decide +kernel :
      cfgC.realAll.all (fun x => decide (x < 20000)) = true) q hq)
  have hall : ∀ q ∈ cfgC.realAll, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgC_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgC_fast, hs_lit]; decide +kernel))
  refine ⟨Or.inr rfl, hnd, hlt, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq, E0_eq]; decide +kernel)

/-! ### Generic support, physicality, correctness, and counts for any valid `SplitCfg` -/

section SplitCore
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical

private def zeroHigh (s : State) : State :=
  { phase := s.phase, basis := fun q => if 20000 ≤ q then false else s.basis q }

private theorem run_below20000 (P : Program) (hsub : ∀ q ∈ wires P, q < 20000) (s : State) (m : List Bool) :
    (run P m s).phase = (run P m (zeroHigh s)).phase ∧
    ∀ q, q < 20000 → (run P m s).basis q = (run P m (zeroHigh s)).basis q := by
  have loc := ECDSAAdd.run_measured_locality P (wires P) (Finset.Subset.refl _) s (zeroHigh s) m rfl
    (fun q hq => by simp [zeroHigh, Nat.not_le.mpr (hsub q hq)])
  exact ⟨loc.1, fun q hq => by
    by_cases hw : q ∈ wires P
    · exact loc.2 q hw
    · rw [run_preserves_outside P m s q hw, run_preserves_outside P m (zeroHigh s) q hw]
      simp [zeroHigh, Nat.not_le.mpr hq]⟩

private theorem run_ge20000 (P : Program) (hsub : ∀ q ∈ wires P, q < 20000) (s : State) (m : List Bool)
    (q : Wire) (hq : 20000 ≤ q) : (run P m s).basis q = s.basis q :=
  run_preserves_outside P m s q (fun hw => absurd (hsub q hw) (Nat.not_lt.mpr hq))

private theorem list_nodup_of_count_le {A B : List Wire} (hB : B.Nodup) (h : ∀ q, A.count q ≤ B.count q) : A.Nodup :=
  List.nodup_iff_count_le_one.mpr (fun q => (h q).trans (List.nodup_iff_count_le_one.mp hB q))

theorem cfg_R_W (c : SplitCfg) (v : CfgValid c) : c.R.W := by
  rcases v.hn with hn | hn <;>
    exact ⟨by simp [SplitCfg.R], by simp [SplitCfg.R, v.bankLen, hn], by simp [SplitCfg.R, v.bankLen, hn],
      by simp [SplitCfg.R, v.dstLen, v.bankLen], by simp [SplitCfg.R, v.sLen, v.bankLen, hn],
      by simp [SplitCfg.R, v.tLen, v.sLen], by simp [SplitCfg.R, v.z4Len],
      by simp [SplitCfg.R, v.padLen], by simp [SplitCfg.R, v.bankLen, v.carryLen, hn]⟩

theorem cfg_R8_W (c : SplitCfg) (v : CfgValid c) : c.R8.W := by
  rcases v.hn with hn | hn <;>
    exact ⟨by simp [SplitCfg.R8], by simp [SplitCfg.R8, v.bankLen, hn], by simp [SplitCfg.R8, v.bankLen, hn],
      by simp [SplitCfg.R8, v.dstLen, v.bankLen], by simp [SplitCfg.R8, v.bankLen, hn],
      by simp [SplitCfg.R8, v.tLen, hn], by simp [SplitCfg.R8, v.sLen, hn],
      by simp [SplitCfg.R8, v.padLen], by simp [SplitCfg.R8, v.bankLen, v.carryLen, hn]⟩

theorem cfg_Q1_W (c : SplitCfg) (v : CfgValid c) : c.Q1.W ∧ c.Q1.bank.length = 2 * c.Q1.h := by
  have hlo : c.R.lo.length = 64 := by simp [KRegs.lo, SplitCfg.R, v.bankLen]; rcases v.hn with h | h <;> omega
  have hdlo : c.R.dlo.length = 128 := by simp [KRegs.dlo, SplitCfg.R, v.dstLen]; rcases v.hn with h | h <;> omega
  refine ⟨⟨by simp [SplitCfg.Q1], by simp [SplitCfg.Q1, hlo], by simp [SplitCfg.Q1, hlo],
    by simp [SplitCfg.Q1, hdlo, hlo], by simp [SplitCfg.Q1, SplitCfg.qS33, v.carryLen, hlo],
    by simp [SplitCfg.Q1, SplitCfg.qS33, v.carryLen, v.t1Len],
    by simp [SplitCfg.Q1, SplitCfg.qZ30, v.carryLen], by simp [SplitCfg.Q1, v.padLen],
    by simp [SplitCfg.Q1, SplitCfg.qCarry, v.carryLen, hlo]⟩, by simp [SplitCfg.Q1, hlo]⟩

theorem cfg_Q2_W (c : SplitCfg) (v : CfgValid c) :
    c.Q2.W ∧ c.Q2.bank.length = 2 * c.Q2.h ∧ (c.Q2.h = 32 ∨ c.Q2.h = 33) := by
  rcases v.hn with hn | hn
  · have hhi : c.R.hi.length = 64 := by simp [KRegs.hi, SplitCfg.R, v.bankLen, hn]
    have hdhi : c.R.dhi.length = 128 := by simp [KRegs.dhi, SplitCfg.R, v.dstLen, hn]
    have ht2 : c.T2.length = 66 := by simpa [hn] using v.t2Len
    refine ⟨⟨by simp [SplitCfg.Q2, hn], by simp [SplitCfg.Q2, hn, hhi], by simp [SplitCfg.Q2, hn, hhi],
      by simp [SplitCfg.Q2, hn, hdhi, hhi], by simp [SplitCfg.Q2, hn, SplitCfg.qS33, v.carryLen, hhi],
      by simp [SplitCfg.Q2, hn, SplitCfg.qS33, v.carryLen, ht2],
      by simp [SplitCfg.Q2, hn, SplitCfg.qZ30, v.carryLen], by simp [SplitCfg.Q2, hn, v.padLen],
      by simp [SplitCfg.Q2, hn, SplitCfg.qCarry, v.carryLen, hhi]⟩,
      by simp [SplitCfg.Q2, hn, hhi], Or.inl (by simp [SplitCfg.Q2, hn])⟩
  · have hne : c.n ≠ 128 := by omega
    have hhi : c.R.hi.length = 65 := by simp [KRegs.hi, SplitCfg.R, v.bankLen, hn]
    have hdhi : c.R.dhi.length = 130 := by simp [KRegs.dhi, SplitCfg.R, v.dstLen, hn]
    have ht2 : c.T2.length = 68 := by simpa [hne] using v.t2Len
    refine ⟨⟨by simp [SplitCfg.Q2, hne], by simp [SplitCfg.Q2, hne, hhi], by simp [SplitCfg.Q2, hne, hhi],
      by simp [SplitCfg.Q2, hne, hdhi, hhi], by simp [SplitCfg.Q2, hne, SplitCfg.qS34, v.carryLen, hhi],
      by simp [SplitCfg.Q2, hne, SplitCfg.qS34, v.carryLen, ht2],
      by simp [SplitCfg.Q2, hne, SplitCfg.qZ31, v.carryLen], by simp [SplitCfg.Q2, hne, v.padLen],
      by simp [SplitCfg.Q2, hne, SplitCfg.qCarry, v.carryLen, hhi]⟩,
      by simp [SplitCfg.Q2, hne, hhi], Or.inr (by simp [SplitCfg.Q2, hne])⟩

theorem cfg_Q5_W (c : SplitCfg) (v : CfgValid c) :
    c.Q5.W ∧ c.Q5.bank.length = 2 * c.Q5.h ∧ c.Q5.h = 33 := by
  rcases v.hn with hn | hn
  · have hS : c.S.length = 65 := by rw [v.sLen, hn]
    have hT : c.T.length = 130 := by rw [v.tLen, hn]
    refine ⟨⟨by simp [SplitCfg.Q5, hn], by simp [SplitCfg.Q5, hn, hS], by simp [SplitCfg.Q5, hn, hS],
      by simp [SplitCfg.Q5, hn, hT, hS], by simp [SplitCfg.Q5, hn, SplitCfg.qS34, v.carryLen, hS],
      by simp [SplitCfg.Q5, hn, SplitCfg.qS34, v.carryLen, v.t5Len],
      by simp [SplitCfg.Q5, hn, SplitCfg.qZ31, v.carryLen], by simp [SplitCfg.Q5, hn, v.padLen],
      by simp [SplitCfg.Q5, hn, SplitCfg.qCarry, v.carryLen, hS]⟩,
      by simp [SplitCfg.Q5, hn, hS], by simp [SplitCfg.Q5, hn]⟩
  · have hne : c.n ≠ 128 := by omega
    have hS : c.S.length = 66 := by rw [v.sLen, hn]
    have hT : c.T.length = 132 := by rw [v.tLen, hn]
    refine ⟨⟨by simp [SplitCfg.Q5, hne], by simp [SplitCfg.Q5, hne, hS], by simp [SplitCfg.Q5, hne, hS],
      by simp [SplitCfg.Q5, hne, hT, hS], by simp [SplitCfg.Q5, hne, SplitCfg.qS34, v.carryLen, hS],
      by simp [SplitCfg.Q5, hne, SplitCfg.qS34, v.carryLen, v.t5Len],
      by simp [SplitCfg.Q5, hne, SplitCfg.qZ31, v.carryLen], by simp [SplitCfg.Q5, hne, v.padLen],
      by simp [SplitCfg.Q5, hne, SplitCfg.qCarry, v.carryLen, hS]⟩,
      by simp [SplitCfg.Q5, hne, hS], by simp [SplitCfg.Q5, hne]⟩

private theorem count_take_drop_split3 (l : List Wire) (q : Wire) :
    (l.take 100).count q + ((l.drop 100).take 31).count q + ((l.drop 131).take 34).count q ≤ l.count q := by
  have s1 := congrArg (List.count q) (List.take_append_drop 100 l)
  have s2 := congrArg (List.count q) (List.take_append_drop 31 (l.drop 100))
  have d3 : (l.drop 100).drop 31 = l.drop 131 := by simp [List.drop_drop]
  rw [d3] at s2
  have s3 := (List.take_sublist 34 (l.drop 131)).count_le q
  simp only [List.count_append] at s1 s2
  omega

theorem cfg_nodups (c : SplitCfg) (v : CfgValid c) :
    c.R.all.Nodup ∧ c.R8.all.Nodup ∧ c.Q1.all.Nodup ∧ c.Q2.all.Nodup ∧ c.Q5.all.Nodup := by
  have hr := v.realNd
  have count_q (q : Wire) :
      c.qCarry.count q + c.qZ30.count q + c.qS33.count q ≤ c.carry.count q ∧
      c.qCarry.count q + c.qZ31.count q + c.qS34.count q ≤ c.carry.count q := by
    have h : c.qCarry.count q + c.qZ31.count q + c.qS34.count q ≤ c.carry.count q :=
      count_take_drop_split3 c.carry q
    have h30 : c.qZ30.count q ≤ c.qZ31.count q := by
      have : c.qZ30 = c.qZ31.take 30 := by simp [SplitCfg.qZ30, SplitCfg.qZ31, List.take_take]
      rw [this]; exact (List.take_sublist 30 _).count_le q
    have h33 : c.qS33.count q ≤ c.qS34.count q := by
      have : c.qS33 = c.qS34.take 33 := by simp [SplitCfg.qS33, SplitCfg.qS34, List.take_take]
      rw [this]; exact (List.take_sublist 33 _).count_le q
    exact ⟨by omega, h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply List.nodup_iff_count_le_one.mpr; intro q
    by_cases hq : q < 20000
    · have hr0 : (List.range' 20000 58).count q = 0 :=
        List.count_eq_zero.mpr (fun h => Nat.not_le.mpr hq (List.mem_range'_1.mp h).1)
      have hc := List.nodup_iff_count_le_one.mp hr q
      simp only [KRegs.all, SplitCfg.R, SplitCfg.realAll, List.count_cons, List.count_append, hr0] at hc ⊢; omega
    · have hreal0 : c.realAll.count q = 0 := List.count_eq_zero.mpr (fun h => hq (v.realLt q h))
      have hr1 := List.nodup_iff_count_le_one.mp (List.nodup_range' (s := 20000) (n := 58)) q
      simp only [KRegs.all, SplitCfg.R, SplitCfg.realAll, List.count_cons, List.count_append] at hreal0 ⊢; omega
  · apply List.nodup_iff_count_le_one.mpr; intro q
    by_cases hq : q < 20000
    · have hr0 : (List.range' 20100 (c.n - 63)).count q = 0 :=
        List.count_eq_zero.mpr (fun h => Nat.not_le.mpr (Nat.lt_trans hq (by decide : 20000 < 20100)) (List.mem_range'_1.mp h).1)
      have hc := List.nodup_iff_count_le_one.mp hr q
      have ht := (List.take_sublist 62 c.S).count_le q
      simp only [KRegs.all, SplitCfg.R8, SplitCfg.realAll, List.count_cons, List.count_append, hr0] at hc ⊢; omega
    · have hreal0 : c.realAll.count q = 0 := List.count_eq_zero.mpr (fun h => hq (v.realLt q h))
      have hr1 := List.nodup_iff_count_le_one.mp (List.nodup_range' (s := 20100) (n := c.n - 63)) q
      have ht := (List.take_sublist 62 c.S).count_le q
      simp only [KRegs.all, SplitCfg.R8, SplitCfg.realAll, List.count_cons, List.count_append] at hreal0 ⊢; omega
  · apply list_nodup_of_count_le hr; intro q
    have h1 := (List.take_sublist 64 c.bank).count_le q
    have h2 := (List.take_sublist (2 * 64) c.dst).count_le q
    have h3 := (count_q q).1
    simp only [KRegs.all, SplitCfg.Q1, SplitCfg.R, KRegs.lo, KRegs.dlo, SplitCfg.realAll,
      List.count_cons, List.count_append]; omega
  · apply list_nodup_of_count_le hr; intro q
    have h1 := (List.drop_sublist 64 c.bank).count_le q
    have h2 := (List.drop_sublist (2 * 64) c.dst).count_le q
    have h3 := count_q q
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_true, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.realAll,
        List.count_cons, List.count_append]; omega
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_false, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.realAll,
        List.count_cons, List.count_append, List.count_nil]; omega
  · apply list_nodup_of_count_le hr; intro q
    have h3 := (count_q q).2
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_true, SplitCfg.realAll,
        List.count_cons, List.count_append, List.count_nil]; omega
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_false, SplitCfg.realAll,
        List.count_cons, List.count_append]; omega

theorem cfg_physical (c : SplitCfg) (v : CfgValid c) :
    GatePhysical c.make ∧ GatePhysical c.clear := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := (cfg_Q1_W c v).1; have w2 := (cfg_Q2_W c v).1; have w5 := (cfg_Q5_W c v).1
  obtain ⟨nR, nR8, n1, n2, n5⟩ := cfg_nodups c v
  have pR := c.R.piece_physical nR
  have p6 : GatePhysical c.R.m6h := c.R.m6h_physical wR nR (by
    have h := pR.2.2.1; simp only [gatePhysical_append] at h; exact h.1.1)
  have pc6 : GatePhysical c.R.c6h := c.R.c6h_physical wR nR (by
    have h := pR.2.2.2.1; simp only [gatePhysical_append] at h; exact h.2)
  refine ⟨?_, ?_⟩
  · simp only [SplitCfg.make, gatePhysical_append]
    exact ⟨⟨⟨⟨⟨⟨⟨makeC_physical c.Q1 w1 n1, makeC_physical c.Q2 w2 n2⟩, pR.1⟩,
      makeC_physical c.Q5 w5 n5⟩, p6⟩, c.R.m7k_physical wR nR⟩, c.R.scl1591_physical wR nR⟩,
      c.R8.m8z_physical nR8⟩
  · simp only [SplitCfg.clear, gatePhysical_append]
    exact ⟨⟨⟨⟨⟨⟨⟨c.R8.c8z_physical wR8 nR8, c.R.smkT_physical wR nR pR.1⟩,
      c.R.c7t_physical nR⟩, pc6⟩, clearC_physical c.Q5 w5 n5⟩,
      c.R.scl1591_physical wR nR⟩, clearC_physical c.Q2 w2 n2⟩, clearC_physical c.Q1 w1 n1⟩

private theorem take_z_in_z4 (c : SplitCfg) (v : CfgValid c) (k : Nat) (hk : k ≤ 4) :
    ∀ q ∈ c.R.z.take k, q ∈ c.zReal4 := by
  intro q hq
  have e : c.R.z.take k = c.zReal4.take k := by
    rw [SplitCfg.R, List.take_append_of_le_length (by rw [v.z4Len]; omega)]
  rw [e] at hq
  exact List.mem_of_mem_take hq

theorem cfg_support (c : SplitCfg) (v : CfgValid c) :
    wires c.make ⊆ c.realAll.toFinset ∧ wires c.clear ⊆ c.realAll.toFinset := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := (cfg_Q1_W c v).1; have w2 := (cfg_Q2_W c v).1; have w5 := (cfg_Q5_W c v).1
  have mCin : K0.core.cin ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mBank {q} (h : q ∈ c.bank) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mDst {q} (h : q ∈ c.dst) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mS {q} (h : q ∈ c.S) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT {q} (h : q ∈ c.T) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mZ4 {q} (h : q ∈ c.zReal4) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mZpad : c.zpad ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mZdst0 : c.zdst0 ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mZdst1 : c.zdst1 ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mPad {q} (h : q ∈ K0.leafPad) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mCarry {q} (h : q ∈ c.carry) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT1 {q} (h : q ∈ c.T1) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT2 {q} (h : q ∈ c.T2) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT5 {q} (h : q ∈ c.T5) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have sQ1 : c.Q1.all.toFinset ⊆ c.realAll.toFinset := by
    intro q hq
    simp only [KRegs.all, SplitCfg.Q1, SplitCfg.R, KRegs.lo, KRegs.dlo, SplitCfg.qCarry, SplitCfg.qZ30,
      SplitCfg.qS33, List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h | h | h | h
    · exact mCin
    · exact mBank (List.mem_of_mem_take h)
    · exact mDst (List.mem_of_mem_take h)
    · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
    · exact mT1 h
    · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
    · exact mPad h
    · exact mCarry (List.mem_of_mem_take h)
  have sQ2 : c.Q2.all.toFinset ⊆ c.realAll.toFinset := by
    intro q hq
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_true, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.qCarry,
        SplitCfg.qZ30, SplitCfg.qS33, List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
      rcases hq with rfl | h | h | h | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mDst (List.mem_of_mem_drop h)
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT2 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_false, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.qCarry,
        SplitCfg.qZ31, SplitCfg.qS34, List.mem_toFinset, List.mem_cons, List.mem_append, List.mem_singleton,
        List.mem_nil_iff, or_false, or_assoc] at hq
      rcases hq with rfl | h | rfl | h | rfl | rfl | h | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mZpad
      · exact mDst (List.mem_of_mem_drop h)
      · exact mZdst0
      · exact mZdst1
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT2 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
  have sQ5 : c.Q5.all.toFinset ⊆ c.realAll.toFinset := by
    intro q hq
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_true, SplitCfg.qCarry, SplitCfg.qZ31, SplitCfg.qS34,
        List.mem_toFinset, List.mem_cons, List.mem_append, List.mem_singleton,
        List.mem_nil_iff, or_false, or_assoc] at hq
      rcases hq with rfl | h | rfl | h | rfl | rfl | h | h | h | h | h
      · exact mCin
      · exact mS h
      · exact mZpad
      · exact mT h
      · exact mZdst0
      · exact mZdst1
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT5 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_false, SplitCfg.qCarry, SplitCfg.qZ31, SplitCfg.qS34,
        List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
      rcases hq with rfl | h | h | h | h | h | h | h
      · exact mCin
      · exact mS h
      · exact mT h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT5 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
  obtain ⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10⟩ := c.R.lens wR
  have sSmk : wires c.R.smk ⊆ c.realAll.toFinset := by
    have w3 := copyRegister_wires_subset none c.R.lo (c.R.S.take c.R.h)
    have w4 := addInPlace_wires (c.R.hi ++ c.R.zS) c.R.S (c.R.carry.take (c.R.S.length - 1)) c.R.cin
      (by simp [L1, L5, wR.S]) (by simp [SplitCfg.R, v.carryLen, v.sLen]; rcases v.hn with hn | hn <;> omega)
    intro q hq
    simp only [KRegs.smk, KRegs.m3, KRegs.m4, wires_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · have h := w3 hq
      simp only [Option.toList_none, List.nil_append, List.mem_toFinset, List.mem_append] at h
      rcases h with h | h
      · exact mBank (List.mem_of_mem_take h)
      · exact mS (List.mem_of_mem_take h)
    · rw [w4] at hq
      simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
      rcases hq with rfl | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mZ4 (take_z_in_z4 c v 1 (by decide) q h)
      · exact mS h
      · exact mCarry (List.mem_of_mem_take h)
  have sSmkT : wires c.R.smkT ⊆ c.realAll.toFinset := by
    intro q hq
    rcases Finset.mem_union.mp (c.R.smkT_wires hq) with h | h
    · exact sSmk h
    · rw [Finset.mem_singleton.mp h]
      exact mT (DiagSq.getD_in c.T 1 (by have := v.tLen; rcases v.hn with hn | hn <;> omega))
  have sScl : wires c.R.scl1591 ⊆ c.realAll.toFinset := by
    have a := FrontierSumCleanup1591Primitive.sub_support (c.R.hi ++ c.R.zS) c.R.S c.R.sumExpected1591
      (c.R.carry.take (c.R.S.length - 1)) c.R.cin
    have p := copyRegister_wires_subset none c.R.lo (c.R.S.take c.R.h)
    intro q hq
    simp only [KRegs.scl1591, wires_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · have h := a hq
      simp only [KRegs.sumExpected1591, KRegs.lo, KRegs.hi, KRegs.zS, List.mem_toFinset,
        List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mZ4 (take_z_in_z4 c v 1 (by decide) q h)
      · exact mS h
      · exact mBank (List.mem_of_mem_take h)
      · exact mZ4 (take_z_in_z4 c v (c.R.S.length - c.R.lo.length)
          (by rw [L0, wR.S]; rcases v.hn with hn | hn <;> simp [SplitCfg.R, v.bankLen, hn]) q h)
      · exact mCarry (List.mem_of_mem_take h)
    · have h := p hq
      simp only [Option.toList_none, List.nil_append, List.mem_toFinset, List.mem_append] at h
      rcases h with h | h
      · exact mBank (List.mem_of_mem_take h)
      · exact mS (List.mem_of_mem_take h)
  have hL6 : (c.R.dlo ++ c.R.zA).length = c.R.T.length := by
    rw [List.length_append, L2, L6]; simp [SplitCfg.R, v.tLen]; rcases v.hn with hn | hn <;> omega
  have hC6 : (c.R.carry.take (c.R.T.length - 1)).length + 1 = c.R.T.length := by
    simp [SplitCfg.R, v.carryLen, v.tLen]; rcases v.hn with hn | hn <;> omega
  have sM6 : wires c.R.m6 ⊆ c.realAll.toFinset := by
    have w6 := subInPlace_wires (c.R.dlo ++ c.R.zA) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL6 hC6
    intro q hq; rw [KRegs.m6, w6] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_take h)
    · exact mZ4 (take_z_in_z4 c v (c.R.T.length - 2 * c.R.h) (by simp [SplitCfg.R, v.tLen]; rcases v.hn with hn | hn <;> omega) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  have sC6 : wires c.R.c6 ⊆ c.realAll.toFinset := by
    have w6 := addInPlace_wires (c.R.dlo ++ c.R.zA) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL6 hC6
    intro q hq; rw [KRegs.c6, w6] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_take h)
    · exact mZ4 (take_z_in_z4 c v (c.R.T.length - 2 * c.R.h) (by simp [SplitCfg.R, v.tLen]; rcases v.hn with hn | hn <;> omega) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  have hL7 : (c.R.dhi ++ c.R.zB).length = c.R.T.length := by
    rw [List.length_append, L3, L7]; simp [SplitCfg.R, v.bankLen, v.tLen]; rcases v.hn with hn | hn <;> omega
  have sM7 : wires c.R.m7 ⊆ c.realAll.toFinset := by
    have w7 := subInPlace_wires (c.R.dhi ++ c.R.zB) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL7 hC6
    intro q hq; rw [KRegs.m7, w7] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_drop h)
    · exact mZ4 (take_z_in_z4 c v 2 (by decide) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  have sC7 : wires c.R.c7 ⊆ c.realAll.toFinset := by
    have w7 := addInPlace_wires (c.R.dhi ++ c.R.zB) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL7 hC6
    intro q hq; rw [KRegs.c7, w7] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_drop h)
    · exact mZ4 (take_z_in_z4 c v 2 (by decide) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  obtain ⟨_, _, _, _, M4, _, _, _, _, _, _⟩ := c.R8.lens wR8
  have hL8 : (c.R8.T ++ c.R8.zM).length = c.R8.dmid.length := by
    rw [List.length_append, KRegs.zM, List.length_take, M4]; simp [SplitCfg.R8, v.tLen, v.sLen, v.bankLen]; rcases v.hn with hn | hn <;> omega
  have hC8 : (c.R8.carry.take (c.R8.dmid.length - 1)).length + 1 = c.R8.dmid.length := by
    rw [List.length_take, M4]; simp [SplitCfg.R8, v.carryLen, v.bankLen]; rcases v.hn with hn | hn <;> omega
  have sM8 : wires c.R8.m8 ⊆ c.realAll.toFinset := by
    have w8 := addInPlace_wires (c.R8.T ++ c.R8.zM) c.R8.dmid (c.R8.carry.take (c.R8.dmid.length - 1)) c.R8.cin hL8 hC8
    intro q hq; rw [KRegs.m8, w8] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mT h
    · exact mS (List.mem_of_mem_take (List.mem_of_mem_take h))
    · exact mDst (List.mem_of_mem_drop h)
    · exact mCarry (List.mem_of_mem_take h)
  have sC8 : wires c.R8.c8 ⊆ c.realAll.toFinset := by
    have w8 := subInPlace_wires (c.R8.T ++ c.R8.zM) c.R8.dmid (c.R8.carry.take (c.R8.dmid.length - 1)) c.R8.cin hL8 hC8
    intro q hq; rw [KRegs.c8, w8] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mT h
    · exact mS (List.mem_of_mem_take (List.mem_of_mem_take h))
    · exact mDst (List.mem_of_mem_drop h)
    · exact mCarry (List.mem_of_mem_take h)
  refine ⟨?_, ?_⟩
  · simp only [SplitCfg.make, wires_append, Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨(makeC_support c.Q1 w1).trans sQ1, (makeC_support c.Q2 w2).trans sQ2⟩, sSmk⟩,
      (makeC_support c.Q5 w5).trans sQ5⟩, (c.R.m6h_wires_smk wR).trans (Finset.union_subset sM6 sSmk)⟩,
      (c.R.m7k_wires wR).trans sM7⟩, sScl⟩, (c.R8.m8z_wires wR8).trans sM8⟩
  · simp only [SplitCfg.clear, wires_append, Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨(c.R8.c8z_wires wR8).trans sC8, sSmkT⟩, c.R.c7t_wires.trans sC7⟩,
      (c.R.c6h_wires wR).trans sC6⟩, (clearC_support c.Q5 w5).trans sQ5⟩, sScl⟩,
      (clearC_support c.Q2 w2).trans sQ2⟩, (clearC_support c.Q1 w1).trans sQ1⟩

private theorem regValue_snoc_zero (r : List Wire) (z : Wire) (b : BasisState) (hz : b z = false) :
    regValue (r ++ [z]) b = regValue r b := by
  simp [regValue_append, regValue, hz]

private theorem regValue_snoc2_lt (r : List Wire) (z0 z1 : Wire) (b : BasisState)
    (hlt : regValue (r ++ [z0, z1]) b < 2 ^ r.length) :
    b z0 = false ∧ b z1 = false ∧ regValue r b = regValue (r ++ [z0, z1]) b := by
  have h := regValue_append r [z0, z1] b
  rw [h] at hlt
  have h01 : regValue [z0, z1] b = 0 := by
    by_contra hne
    have hpos : 1 ≤ regValue [z0, z1] b := Nat.one_le_iff_ne_zero.mpr hne
    have : 2 ^ r.length ≤ 2 ^ r.length * regValue [z0, z1] b := Nat.le_mul_of_pos_right _ hpos
    omega
  have hb0 : b z0 = false := (regValue_zero [z0, z1] b).mp h01 z0 (by simp)
  have hb1 : b z1 = false := (regValue_zero [z0, z1] b).mp h01 z1 (by simp)
  exact ⟨hb0, hb1, by rw [h, h01]; simp⟩

private theorem dmid_val (c : SplitCfg) (v : CfgValid c) (b : BasisState) :
    regValue c.R8.dmid b = regValue c.R8.dlo b / 2 ^ 64 + 2 ^ 64 * regValue c.R8.dhi b := by
  have hd : 128 ≤ c.dst.length := by rw [v.dstLen]; rcases v.hn with h | h <;> omega
  have h1 : c.R8.dmid = (c.dst.take 128).drop 64 ++ c.dst.drop 128 := by
    have e := congrArg (List.drop 64) (List.take_append_drop 128 c.dst)
    rw [List.drop_append_of_le_length (by simp [hd])] at e
    exact e.symm
  have hlen : ((c.dst.take 128).drop 64).length = 64 := by simp [hd]
  have hdiv : regValue ((c.dst.take 128).drop 64) b = regValue (c.dst.take 128) b / 2 ^ 64 := by
    have ea := regValue_append ((c.dst.take 128).take 64) ((c.dst.take 128).drop 64) b
    rw [List.take_append_drop] at ea
    have hl64 : ((c.dst.take 128).take 64).length = 64 := by simp [hd]
    have hlt := regValue_lt ((c.dst.take 128).take 64) b
    rw [hl64] at ea hlt
    rw [ea, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [h1, regValue_append, hlen, hdiv]; rfl

private theorem realAll_count (c : SplitCfg) (x : Wire) :
    c.realAll.count x =
      [K0.core.cin].count x + c.bank.count x + c.dst.count x + c.S.count x + c.T.count x +
      c.zReal4.count x + [c.zpad].count x + [c.zdst0].count x + [c.zdst1].count x +
      K0.leafPad.count x + c.carry.count x + c.T1.count x + c.T2.count x + c.T5.count x := by
  have h1 : c.realAll = ([K0.core.cin] ++ c.bank) ++ c.dst ++ c.S ++ c.T ++ c.zReal4 ++
      ([c.zpad] ++ [c.zdst0] ++ [c.zdst1]) ++ K0.leafPad ++ c.carry ++ c.T1 ++ c.T2 ++ c.T5 := by
    simp only [SplitCfg.realAll, List.cons_append, List.nil_append]
  rw [h1]
  simp only [List.count_append]
  omega

/-- Exact postcondition of `c.make` on a clean initial state. -/
theorem cfg_make_correct (c : SplitCfg) (v : CfgValid c) (s : State) (m : List Bool)
    (hd0 : regValue c.dst s.basis = 0)
    (hT0 : regValue c.liveT s.basis = 0)
    (hSc0 : regValue c.cleanScratch s.basis = 0)
    (hi0 : s.basis K0.core.cin = false) :
    let a := regValue c.R.lo s.basis
    let b := regValue c.R.hi s.basis
    let u := run c.make m s
    u.phase = s.phase ∧
    regValue c.dst u.basis = (regValue c.bank s.basis) ^ 2 ∧
    regValue c.T u.basis = 2 * a * b ∧
    regValue c.T1 u.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) ∧
    regValue c.T2 u.basis = 2 * (b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h) ∧
    regValue c.T5 u.basis = 2 * ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) ∧
    ∀ q, q ∉ c.dst → q ∉ c.liveT → u.basis q = s.basis q := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  obtain ⟨nR, nR8, n1, n2, n5⟩ := cfg_nodups c v
  have sup := cfg_support c v; have hr := v.realNd
  have dj {A B : List Wire} (h : ∀ q, A.count q + B.count q ≤ c.realAll.count q) : ∀ q ∈ A, q ∉ B := kdis hr h
  have zOf (r : List Wire) (sub : ∀ q ∈ r, q ∈ c.cleanScratch) : regValue r s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hSc0 q (sub q hq))
  have zLive (r : List Wire) (sub : ∀ q ∈ r, q ∈ c.liveT) : regValue r s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hT0 q (sub q hq))
  have hS0 : regValue c.S s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hz40 : regValue c.zReal4 s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hpad0 : regValue K0.leafPad s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hcar0 : regValue c.carry s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hzpad0 : s.basis c.zpad = false := (regValue_zero _ _).mp hSc0 c.zpad (by simp [SplitCfg.cleanScratch])
  have hzd0 : s.basis c.zdst0 = false := (regValue_zero _ _).mp hSc0 c.zdst0 (by simp [SplitCfg.cleanScratch])
  have hzd1 : s.basis c.zdst1 = false := (regValue_zero _ _).mp hSc0 c.zdst1 (by simp [SplitCfg.cleanScratch])
  have hT_0 : regValue c.T s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have hT1_0 : regValue c.T1 s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have hT2_0 : regValue c.T2 s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have hT5_0 : regValue c.T5 s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have bv := c.R.bank_value wR s.basis
  obtain ⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10⟩ := c.R.lens wR
  generalize ha : regValue c.R.lo s.basis = a
  generalize hb : regValue c.R.hi s.basis = b
  have aLt : a < 2 ^ 64 := by rw [← ha]; simpa [L0] using regValue_lt c.R.lo s.basis
  have bLt : b < 2 ^ (c.n - 64) := by
    rw [← hb]; have h := regValue_lt c.R.hi s.basis
    rw [L1, show c.R.bank.length = c.n from v.bankLen, show c.R.h = 64 from rfl] at h; exact h
  have realStep (P : Program) (hp : wires P ⊆ c.realAll.toFinset) : ∀ q ∈ wires P, q < 20000 :=
    fun q hq => v.realLt q (List.mem_toFinset.mp (hp hq))
  obtain ⟨a7, r8, e8⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5 ++ c.R.m6h ++ c.R.m7k ++ c.R.scl1591) c.R8.m8z m s
  obtain ⟨a6, r7, e7⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5 ++ c.R.m6h ++ c.R.m7k) c.R.scl1591 a7 s
  obtain ⟨a5, r6, e6⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5 ++ c.R.m6h) c.R.m7k a6 s
  obtain ⟨a4, r5, e5⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5) c.R.m6h a5 s
  obtain ⟨a3, r4, e4⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk)
    (LowZero18Diagonal.makeC c.Q5) a4 s
  obtain ⟨a2, r3, e3⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2) c.R.smk a3 s
  obtain ⟨r1, r2, e2⟩ := kseq (LowZero18Diagonal.makeC c.Q1) (LowZero18Diagonal.makeC c.Q2) a2 s
  dsimp only
  rw [SplitCfg.make, e8, e7, e6, e5, e4, e3, e2]
  have st1 := makeC_clean c.Q1 w1.1 w1.2 (Or.inl rfl) n1 s r1
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hd0 q (List.mem_of_mem_take h)))
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    hT1_0
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    hpad0
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_take h)))
    hi0
  generalize hs1 : run (LowZero18Diagonal.makeC c.Q1) r1 s = s1 at st1 ⊢
  have F1 : ∀ q, q ∉ c.R.dlo → q ∉ c.T1 → s1.basis q = s.basis q := st1.2.2.2
  have h_hi_bank (q : Wire) : c.R.hi.count q ≤ c.bank.count q := (List.drop_sublist 64 c.bank).count_le q
  have h_dhi_dst (q : Wire) : c.R.dhi.count q ≤ c.dst.count q := (List.drop_sublist 128 c.dst).count_le q
  have mLo {q : Wire} (h : q ∈ c.R.lo) : q ∈ c.bank := List.mem_of_mem_take (show q ∈ c.bank.take 64 from h)
  have mHi {q : Wire} (h : q ∈ c.R.hi) : q ∈ c.bank := List.mem_of_mem_drop (show q ∈ c.bank.drop 64 from h)
  have mDlo {q : Wire} (h : q ∈ c.R.dlo) : q ∈ c.dst := List.mem_of_mem_take (show q ∈ c.dst.take 128 from h)
  have mDhi {q : Wire} (h : q ∈ c.R.dhi) : q ∈ c.dst := List.mem_of_mem_drop (show q ∈ c.dst.drop 128 from h)
  have bLtR : b < 2 ^ (c.R.bank.length - c.R.h) := by simpa [SplitCfg.R, v.bankLen] using bLt
  have s1_T1 : regValue c.T1 s1.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) := by
    have h := st1.2.2.1; rw [c.Q1.lo_mod w1.1, c.Q1.hi_div w1.1] at h; simpa [SplitCfg.Q1, ha] using h
  have s1_dlo : regValue c.R.dlo s1.basis = a ^ 2 := by simpa [SplitCfg.Q1, ha] using st1.2.1
  have o_dlo {r : List Wire} (h : ∀ q, r.count q + c.dst.count q ≤ c.realAll.count q) : ∀ q ∈ r, q ∉ c.R.dlo :=
    fun q hq hd => dj h q hq (mDlo hd)
  have o_dhi {r : List Wire} (h : ∀ q, r.count q + c.dst.count q ≤ c.realAll.count q) : ∀ q ∈ r, q ∉ c.R.dhi :=
    fun q hq hd => dj h q hq (mDhi hd)
  have dlo_dhi : ∀ q ∈ c.R.dhi, q ∉ c.R.dlo := by
    intro q h1 h2
    have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
    rw [← List.take_append_drop 128 c.dst] at hnd
    exact (List.nodup_append.mp hnd).2.2 q h2 q h1 rfl
  have s1_keep (r : List Wire) (hd : ∀ q ∈ r, q ∉ c.R.dlo) (ht : ∀ q ∈ r, q ∉ c.T1) :
      regValue r s1.basis = regValue r s.basis := regValue_congr _ _ _ (fun q hq => F1 q (hd q hq) (ht q hq))
  have s1_eq (q : Wire) (hd : q ∉ c.dst) (ht : q ∉ c.T1) : s1.basis q = s.basis q :=
    F1 q (fun h => hd (mDlo h)) ht
  have s1_Q2_bank : regValue c.Q2.bank s1.basis = b := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q2, hn, if_true]
      rw [s1_keep _ (o_dlo (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega))
        (dj (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega)), hb]
    · simp only [SplitCfg.Q2, hn, if_false]
      rw [regValue_snoc_zero _ _ _ ((s1_eq c.zpad
        (dj (A := [c.zpad]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzpad0)]
      rw [s1_keep _ (o_dlo (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega))
        (dj (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega)), hb]
  have s1_Q2_dst0 : regValue c.Q2.dst s1.basis = 0 := by
    have hdhi0 : regValue c.R.dhi s1.basis = 0 :=
      (s1_keep _ dlo_dhi (dj (fun q => by clear * - c q h_dhi_dst; have := h_dhi_dst q; rw [realAll_count]; omega))).trans
        ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hd0 q (mDhi h)))
    by_cases hn : c.n = 128
    · simpa [SplitCfg.Q2, hn] using hdhi0
    · simp only [SplitCfg.Q2, hn, if_false, regValue_append, hdhi0, zero_add]
      have b0 : s1.basis c.zdst0 = false := (s1_eq _
        (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd0
      have b1 : s1.basis c.zdst1 = false := (s1_eq _
        (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd1
      simp [regValue, b0, b1]
  have s1_car0 : regValue c.carry s1.basis = 0 :=
    (s1_keep _ (o_dlo (fun q => by clear * - c q; rw [realAll_count]; omega))
      (dj (fun q => by clear * - c q; rw [realAll_count]; omega))).trans hcar0
  have s1_pad0 : regValue K0.leafPad s1.basis = 0 :=
    (s1_keep _ (o_dlo (fun q => by clear * - c q; rw [realAll_count]; omega))
      (dj (fun q => by clear * - c q; rw [realAll_count]; omega))).trans hpad0
  have s1_cin0 : s1.basis K0.core.cin = false :=
    (s1_eq _ (dj (A := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s1_T2_0 : regValue c.T2 s1.basis = 0 :=
    (s1_keep _ (o_dlo (fun q => by clear * - c q; rw [realAll_count]; omega))
      (dj (fun q => by clear * - c q; rw [realAll_count]; omega))).trans hT2_0
  have st2 := makeC_clean c.Q2 w2.1 w2.2.1 w2.2.2 n2 s1 r2 s1_Q2_dst0
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s1_T2_0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s1_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s1_cin0)
  generalize hs2 : run (LowZero18Diagonal.makeC c.Q2) r2 s1 = s2 at st2 ⊢
  have s2_dhi : regValue c.R.dhi s2.basis = b ^ 2 := by
    by_cases hn : c.n = 128
    · have h := st2.2.1; rw [s1_Q2_bank] at h; simpa [SplitCfg.Q2, hn] using h
    · have h := st2.2.1; rw [s1_Q2_bank] at h; simp only [SplitCfg.Q2, hn, if_false] at h
      have hlt : regValue (c.R.dhi ++ [c.zdst0, c.zdst1]) s2.basis < 2 ^ c.R.dhi.length := by
        rw [h, L3]; rcases v.hn with h128 | h129
        · exact absurd h128 hn
        · simp only [SplitCfg.R, v.bankLen, h129] at bLt ⊢
          have : b ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left bLt (by decide)
          simpa [← Nat.pow_mul] using this
      exact (regValue_snoc2_lt c.R.dhi c.zdst0 c.zdst1 s2.basis hlt).2.2.trans h
  have s2_zd0 : s2.basis c.zdst0 = false ∧ s2.basis c.zdst1 = false := by
    by_cases hn : c.n = 128
    · have f := st2.2.2.2
      have eq0 : s2.basis c.zdst0 = s1.basis c.zdst0 := f _ (by simp [SplitCfg.Q2, hn]; exact o_dhi (r := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
      have eq1 : s2.basis c.zdst1 = s1.basis c.zdst1 := f _ (by simp [SplitCfg.Q2, hn]; exact o_dhi (r := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
      exact ⟨eq0.trans ((s1_eq _ (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
        eq1.trans ((s1_eq _ (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
    · have h := st2.2.1; rw [s1_Q2_bank] at h; simp only [SplitCfg.Q2, hn, if_false] at h
      have hlt : regValue (c.R.dhi ++ [c.zdst0, c.zdst1]) s2.basis < 2 ^ c.R.dhi.length := by
        rw [h, L3]; rcases v.hn with h128 | h129
        · exact absurd h128 hn
        · simp only [SplitCfg.R, v.bankLen, h129] at bLt ⊢
          have : b ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left bLt (by decide)
          simpa [← Nat.pow_mul] using this
      have p := regValue_snoc2_lt c.R.dhi c.zdst0 c.zdst1 s2.basis hlt
      exact ⟨p.1, p.2.1⟩
  have s2_T2 : regValue c.T2 s2.basis = 2 * (b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h) := by
    have h := st2.2.2.1
    rw [c.Q2.lo_mod w2.1, c.Q2.hi_div w2.1, s1_Q2_bank] at h
    by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using h
  have F2 : ∀ q, q ∉ c.dst → q ∉ c.T1 → q ∉ c.T2 → s2.basis q = s.basis q := by
    intro q hd ht1 ht2
    by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
    · rcases hzd with rfl | rfl
      · exact s2_zd0.1.trans hzd0.symm
      · exact s2_zd0.2.trans hzd1.symm
    · have hq2d : q ∉ c.Q2.dst := by
        by_cases hn : c.n = 128
        · simp [SplitCfg.Q2, hn]; exact fun h => hd (mDhi h)
        · simp only [SplitCfg.Q2, hn, if_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | rfl | rfl)
          · exact hd (mDhi h)
          · exact hzd (Or.inl rfl)
          · exact hzd (Or.inr rfl)
      have hq2t : q ∉ c.Q2.T := by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using ht2
      exact (st2.2.2.2 q hq2d hq2t).trans (s1_eq q hd ht1)
  have s2_dlo : regValue c.R.dlo s2.basis = a ^ 2 := by
    rw [regValue_congr _ _ s1.basis (fun q hq => by
      have hnot_dhi : q ∉ c.R.dhi := fun h => dlo_dhi q h hq
      have hnot_z0 : q ≠ c.zdst0 := fun h => dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst0 (by simp) (h ▸ mDlo hq)
      have hnot_z1 : q ≠ c.zdst1 := fun h => dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst1 (by simp) (h ▸ mDlo hq)
      have hnot_t2 : q ∉ c.T2 := dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq)
      apply st2.2.2.2
      · by_cases hn : c.n = 128
        · simpa [SplitCfg.Q2, hn] using hnot_dhi
        · simp [SplitCfg.Q2, hn, hnot_dhi, hnot_z0, hnot_z1]
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using hnot_t2), s1_dlo]
  have s2_T1 : regValue c.T1 s2.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) := by
    rw [regValue_congr _ _ s1.basis (fun q hq => by
      have hnot_dst : q ∉ c.dst := fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q h hq
      have hnot_z0 : q ≠ c.zdst0 := fun h => dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst0 (by simp) (h ▸ hq)
      have hnot_z1 : q ≠ c.zdst1 := fun h => dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst1 (by simp) (h ▸ hq)
      have hnot_t2 : q ∉ c.T2 := dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq
      apply st2.2.2.2
      · by_cases hn : c.n = 128
        · simp [SplitCfg.Q2, hn]; exact fun h => hnot_dst (mDhi h)
        · simp [SplitCfg.Q2, hn, hnot_z0, hnot_z1]; exact fun h => hnot_dst (mDhi h)
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using hnot_t2), s1_T1]
  have sup_parts : (∀ q ∈ wires c.R.smk, q < 20000) ∧ (∀ q ∈ wires c.R.m6h, q < 20000) ∧
      (∀ q ∈ wires c.R.m7k, q < 20000) ∧ (∀ q ∈ wires c.R.scl1591, q < 20000) ∧
      (∀ q ∈ wires c.R8.m8z, q < 20000) := by
    have sm := sup.1
    simp only [SplitCfg.make, wires_append, Finset.union_subset_iff] at sm
    exact ⟨realStep _ sm.1.1.1.1.1.2, realStep _ sm.1.1.1.2, realStep _ sm.1.1.2, realStep _ sm.1.2, realStep _ sm.2⟩
  have mk_zh_z (t : State) (ht : ∀ q ∈ c.zReal4, t.basis q = false) : regValue c.R.z (zeroHigh t).basis = 0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    simp only [SplitCfg.R, List.mem_append] at hq
    rcases hq with hq | hq
    · simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]; exact ht q hq
    · simp only [zeroHigh, (List.mem_range'_1.mp hq).1, if_true]
  have st3_zh := c.R.smk_correct wR nR (zeroHigh s2) r3
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.S at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hS0 q hq)))
    (mk_zh_z s2 (fun q hq => (F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq)))
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq)))
    (by
      change (zeroHigh s2).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      exact (F2 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0)
  have loc3 := run_below20000 c.R.smk sup_parts.1 s2 r3
  generalize hs3 : run c.R.smk r3 s2 = s3 at loc3 ⊢
  have s3_F (q : Wire) (hS : q ∉ c.S) : s3.basis q = s2.basis q := by
    by_cases hq : q < 20000
    · rw [loc3.2 q hq, st3_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs3]; exact run_ge20000 c.R.smk sup_parts.1 s2 r3 q (Nat.le_of_not_lt hq)
  have s3_S : regValue c.S s3.basis = a + b := by
    have e1 := regValue_congr c.S s3.basis (run c.R.smk r3 (zeroHigh s2)).basis (fun q hq => loc3.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))
    rw [e1, show c.S = c.R.S from rfl, st3_zh.2.1]
    have elo : regValue c.R.lo (zeroHigh s2).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        exact F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s2).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        exact F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
    rw [elo, ehi]
  have F3 : ∀ q, q ∉ c.dst → q ∉ c.S → q ∉ c.T1 → q ∉ c.T2 → s3.basis q = s.basis q :=
    fun q hd hS ht1 ht2 => (s3_F q hS).trans (F2 q hd ht1 ht2)
  have s3_Q5_bank : regValue c.Q5.bank s3.basis = a + b := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true]
      rw [regValue_snoc_zero _ _ _ ((F3 c.zpad
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzpad0), s3_S]
    · simpa [SplitCfg.Q5, hn] using s3_S
  have s3_car0 : regValue c.carry s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hcar0
  have s3_T0 : regValue c.T s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT_0
  have s3_Q5_dst0 : regValue c.Q5.dst s3.basis = 0 := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true, regValue_append, s3_T0, zero_add]
      have b0 : s3.basis c.zdst0 = false := (F3 _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0
      have b1 : s3.basis c.zdst1 = false := (F3 _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1
      simp [regValue, b0, b1]
    · simpa [SplitCfg.Q5, hn] using s3_T0
  have s3_T5_0 : regValue c.T5 s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT5_0
  have s3_pad0 : regValue K0.leafPad s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hpad0
  have s3_cin0 : s3.basis K0.core.cin = false :=
    (F3 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have st4 := makeC_clean c.Q5 w5.1 w5.2.1 (Or.inr w5.2.2) n5 s3 r4 s3_Q5_dst0
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s3_T5_0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s3_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s3_cin0)
  generalize hs4 : run (LowZero18Diagonal.makeC c.Q5) r4 s3 = s4 at st4 ⊢
  have s4_T : regValue c.T s4.basis = (a + b) ^ 2 := by
    by_cases hn : c.n = 128
    · have h := st4.2.1; rw [s3_Q5_bank] at h; simp only [SplitCfg.Q5, hn, if_true] at h
      have hlt : regValue (c.T ++ [c.zdst0, c.zdst1]) s4.basis < 2 ^ c.T.length := by
        rw [h, v.tLen, hn]; simp only [hn] at bLt
        have hab : a + b < 2 ^ 65 := by omega
        have : (a + b) ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left hab (by decide)
        simpa [← Nat.pow_mul] using this
      exact (regValue_snoc2_lt c.T c.zdst0 c.zdst1 s4.basis hlt).2.2.trans h
    · have h := st4.2.1; rw [s3_Q5_bank] at h; simpa [SplitCfg.Q5, hn] using h
  have s4_zd0 : s4.basis c.zdst0 = false ∧ s4.basis c.zdst1 = false := by
    by_cases hn : c.n = 128
    · have h := st4.2.1; rw [s3_Q5_bank] at h; simp only [SplitCfg.Q5, hn, if_true] at h
      have hlt : regValue (c.T ++ [c.zdst0, c.zdst1]) s4.basis < 2 ^ c.T.length := by
        rw [h, v.tLen, hn]; simp only [hn] at bLt
        have hab : a + b < 2 ^ 65 := by omega
        have : (a + b) ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left hab (by decide)
        simpa [← Nat.pow_mul] using this
      have p := regValue_snoc2_lt c.T c.zdst0 c.zdst1 s4.basis hlt
      exact ⟨p.1, p.2.1⟩
    · have eq0 : s4.basis c.zdst0 = s3.basis c.zdst0 := st4.2.2.2 _
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      have eq1 : s4.basis c.zdst1 = s3.basis c.zdst1 := st4.2.2.2 _
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      exact ⟨eq0.trans ((F3 _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
        eq1.trans ((F3 _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
  have s4_T5 : regValue c.T5 s4.basis = 2 * ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) := by
    have h := st4.2.2.1
    rw [c.Q5.lo_mod w5.1, c.Q5.hi_div w5.1, s3_Q5_bank, w5.2.2] at h
    by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using h
  have s4_F (q : Wire) (hT : q ∉ c.T) (hT5 : q ∉ c.T5) : s4.basis q = s3.basis q := by
    by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
    · rcases hzd with rfl | rfl
      · exact s4_zd0.1.trans ((F3 _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0).symm
      · exact s4_zd0.2.trans ((F3 _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1).symm
    · apply st4.2.2.2
      · by_cases hn : c.n = 128
        · simp only [SplitCfg.Q5, hn, if_true, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | rfl | rfl)
          · exact hT h
          · exact hzd (Or.inl rfl)
          · exact hzd (Or.inr rfl)
        · simpa [SplitCfg.Q5, hn] using hT
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using hT5
  have F4 : ∀ q, q ∉ c.dst → q ∉ c.S → q ∉ c.liveT → s4.basis q = s.basis q := by
    intro q hd hS hL
    have hT : q ∉ c.T := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT1 : q ∉ c.T1 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT2 : q ∉ c.T2 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT5 : q ∉ c.T5 := fun h => hL (by simp [SplitCfg.liveT, h])
    exact (s4_F q hT hT5).trans (F3 q hd hS hT1 hT2)
  have s4_dlo : regValue c.R.dlo (zeroHigh s4).basis = a ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDlo hq, true_or, or_true])), if_false]
      exact (s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))))).trans s2_dlo
  have s4_lo_zh : regValue c.R.lo (zeroHigh s4).basis = a :=
    (regValue_congr _ _ s.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
      exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mLo hq)))).trans ha
  have s4_hi_zh : regValue c.R.hi (zeroHigh s4).basis = b :=
    (regValue_congr _ _ s.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
      exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mHi hq)))).trans hb
  have s4_S_zh : regValue c.R.S (zeroHigh s4).basis = a + b :=
    (regValue_congr _ _ s3.basis (fun q hq => by
      change q ∈ c.S at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s3_S
  have s4_T_zh : regValue c.R.T (zeroHigh s4).basis = (a + b) ^ 2 :=
    (regValue_congr _ _ s4.basis (fun q hq => by
      change q ∈ c.T at hq; simp [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true]))])).trans s4_T
  have s4_car_zh : regValue c.R.carry (zeroHigh s4).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s4_cin_zh : (zeroHigh s4).basis c.R.cin = false := by
    change (zeroHigh s4).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0
  have s4_z_zh : regValue c.R.z (zeroHigh s4).basis = 0 := mk_zh_z s4 (fun q hq =>
    (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))
  have s4_zA_zh : regValue c.R.zA (zeroHigh s4).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s4_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have hTl := wR.T; have hSl := wR.S; have hhR := wR.hh; have h4R := wR.h4; have hclR := wR.carry
  have ex : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
  have sumLt : a + b < 2 ^ c.R.S.length := by
    have hp : 2 ^ c.R.h ≤ 2 ^ (c.R.bank.length - c.R.h) := Nat.pow_le_pow_right (by decide) (by clear * - hhR; omega)
    have hq : 2 ^ c.R.S.length = 2 * 2 ^ (c.R.bank.length - c.R.h) := by rw [hSl, pow_succ]; ring
    have haR : a < 2 ^ c.R.h := aLt
    clear * - haR bLtR hp hq; omega
  have sqLt : (a + b) ^ 2 < 2 ^ c.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have st5_zh : (run c.R.m6h r5 (zeroHigh s4)).phase = (zeroHigh s4).phase ∧
      regValue c.R.T (run c.R.m6h r5 (zeroHigh s4)).basis = 2 * a * b + b ^ 2 ∧
      ∀ q, q ∉ c.R.T → (run c.R.m6h r5 (zeroHigh s4)).basis q = (zeroHigh s4).basis q := by
    rw [c.R.m6h_square_run wR nR (zeroHigh s4) r5
      (fun q hq => (regValue_zero _ _).mp s4_car_zh q (List.mem_of_mem_take hq))
      s4_cin_zh a b aLt bLtR s4_T_zh s4_dlo s4_zA_zh s4_S_zh s4_lo_zh s4_hi_zh]
    unfold KRegs.m6
    obtain ⟨p, f, val⟩ := BalancedInverse.subInPlace_any_correct (c.R.dlo ++ c.R.zA) c.R.T
      (c.R.carry.take (c.R.T.length - 1)) c.R.cin
      (knd nR (fun q => by have := c.R.counts q; simp only [KRegs.all, List.count_cons, List.count_append]; omega))
      (by rw [List.length_append, L2, L6]; omega)
      (by rw [List.length_take]; omega)
      (zeroHigh s4) r5 (fun q hq => (regValue_zero _ _).mp s4_car_zh q (List.mem_of_mem_take hq))
    refine ⟨p, ?_, f⟩
    rw [val, regValue_append, s4_dlo, s4_zA_zh, s4_T_zh, s4_cin_zh]
    simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false, Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [ex]; omega) sqLt, ex]; omega
  have loc5 := run_below20000 c.R.m6h sup_parts.2.1 s4 r5
  generalize hs5 : run c.R.m6h r5 s4 = s5 at loc5 ⊢
  have s5_F (q : Wire) (hT : q ∉ c.T) : s5.basis q = s4.basis q := by
    by_cases hq : q < 20000
    · rw [loc5.2 q hq, st5_zh.2.2 q hT]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs5]; exact run_ge20000 c.R.m6h sup_parts.2.1 s4 r5 q (Nat.le_of_not_lt hq)
  have s5_T : regValue c.T s5.basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ _ (fun q hq => loc5.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st5_zh.2.1
  have s5_dhi : regValue c.R.dhi (zeroHigh s5).basis = b ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDhi hq, true_or, or_true])), if_false]
      exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
        ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
          (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))))).trans s2_dhi
  have s5_T_zh : regValue c.R.T (zeroHigh s5).basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ s5.basis (fun q hq => by
      change q ∈ c.T at hq; simp [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true]))])).trans s5_T
  have s5_car_zh : regValue c.R.carry (zeroHigh s5).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      rw [s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s5_cin_zh : (zeroHigh s5).basis c.R.cin = false := by
    change (zeroHigh s5).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    rw [s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))]
    exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0
  have s5_z_zh : regValue c.R.z (zeroHigh s5).basis = 0 := mk_zh_z s5 (fun q hq => by
    rw [s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
    exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))
  have s5_zB_zh : regValue c.R.zB (zeroHigh s5).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s5_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have xv5 : regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis = b ^ 2 := by
    rw [regValue_append, s5_dhi, s5_zB_zh]; simp
  have st6_zh : (run c.R.m7k r6 (zeroHigh s5)).phase = (zeroHigh s5).phase ∧
      regValue c.R.T (run c.R.m7k r6 (zeroHigh s5)).basis = 2 * a * b ∧
      ∀ q, q ∉ c.R.T → (run c.R.m7k r6 (zeroHigh s5)).basis q = (zeroHigh s5).basis q := by
    have hcl7 : ∀ q ∈ c.R.carry.take (c.R.T.length - 1), (zeroHigh s5).basis q = false :=
      fun q hq => (regValue_zero _ _).mp s5_car_zh q (List.mem_of_mem_take hq)
    have hnc7 : ((zeroHigh s5).basis ((c.R.dhi ++ c.R.zB).headD 0) && !(zeroHigh s5).basis (c.R.T.headD 0)) = false := by
      have hT := LowZero.head_bit c.R.T [] (zeroHigh s5).basis (c.R.T_ne wR)
      rw [List.append_nil] at hT
      rw [LowZero.head_bit c.R.dhi c.R.zB (zeroHigh s5).basis (c.R.dhi_ne wR), hT, s5_dhi, s5_T_zh,
        show 2 * a * b + b ^ 2 = b ^ 2 + 2 * (a * b) by ring, Nat.add_mul_mod_self_left]
      cases decide (b ^ 2 % 2 = 1) <;> rfl
    have h17 : (zeroHigh s5).basis ((c.R.dhi ++ c.R.zB).tail.headD 0) = false := by
      rw [KRegs.bit1 c.R.dhi c.R.zB (zeroHigh s5).basis (c.R.dhi_two wR), s5_dhi, KRegs.sq_bit1]; rfl
    have hA7 : c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis < 2 ^ (c.R.T.length - 1) :=
      fun _ => by rw [xv5, hTl, hSl]; exact KRegs.sq_trim_bound c.R.bank.length c.R.h b bLtR
    have hb7 : c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis ≤ regValue c.R.T (zeroHigh s5).basis % 2 ^ (c.R.T.length - 1) :=
      fun tc => by
        have tb := KRegs.trim_bound c.R.bank.length c.R.h a b tc aLt bLtR
        rw [xv5, s5_T_zh, hTl, hSl, Nat.mod_eq_of_lt tb]; omega
    have hab7 : a * b < 2 ^ c.R.bank.length := by
      have e : 2 ^ c.R.bank.length = 2 ^ c.R.h * 2 ^ (c.R.bank.length - c.R.h) := by rw [← pow_add]; congr 1; omega
      rw [e]; exact Nat.mul_lt_mul'' aLt bLtR
    have p2b : 2 ^ (c.R.bank.length + 1) = 2 * 2 ^ c.R.bank.length := by rw [pow_succ]; ring
    have HT : c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis < 2 ^ (c.R.T.length - 1) ∧
        regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis ≤ regValue c.R.T (zeroHigh s5).basis % 2 ^ (c.R.T.length - 1) ∧
        regValue c.R.T (zeroHigh s5).basis % 2 ^ (c.R.T.length - 1) < regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis + 2 ^ (c.R.T.length - 2) := by
      intro tc
      refine ⟨hA7 tc, hb7 tc, ?_⟩
      have tc' : 2 * c.R.h + 1 ≤ c.R.bank.length := tc
      have tb := KRegs.trim_bound c.R.bank.length c.R.h a b tc aLt bLtR
      have hpw : 2 ^ (c.R.bank.length + 1) ≤ 2 ^ (c.R.T.length - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [xv5, s5_T_zh, hTl, hSl, Nat.mod_eq_of_lt tb]
      rw [hTl, hSl] at hpw
      rw [show 2 * a * b + b ^ 2 = 2 * (a * b) + b ^ 2 by ring]; omega
    have HF : ¬c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis ≤ regValue c.R.T (zeroHigh s5).basis ∧
        regValue c.R.T (zeroHigh s5).basis < regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis + 2 ^ (c.R.T.length - 1) := by
      intro _
      have hpw : 2 ^ (c.R.bank.length + 1) ≤ 2 ^ (c.R.T.length - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [xv5, s5_T_zh, show 2 * a * b + b ^ 2 = 2 * (a * b) + b ^ 2 by ring]
      constructor <;> omega
    rw [c.R.m7k_run wR nR (zeroHigh s5) r6 hcl7 hnc7 s5_cin_zh h17 HT HF]
    obtain ⟨p, f, val⟩ := c.R.m7t_correct wR nR (zeroHigh s5) r6 hcl7 hnc7 s5_cin_zh h17 hA7 hb7
    refine ⟨p, ?_, f⟩
    rw [val, xv5, s5_T_zh, s5_cin_zh]
    simp only [Bool.toNat_false, Nat.sub_zero]
    rw [ksubmod _ _ _ (by omega) (by rw [ex] at sqLt; omega)]; omega
  have loc6 := run_below20000 c.R.m7k sup_parts.2.2.1 s5 r6
  generalize hs6 : run c.R.m7k r6 s5 = s6 at loc6 ⊢
  have s6_F (q : Wire) (hT : q ∉ c.T) : s6.basis q = s5.basis q := by
    by_cases hq : q < 20000
    · rw [loc6.2 q hq, st6_zh.2.2 q hT]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs6]; exact run_ge20000 c.R.m7k sup_parts.2.2.1 s5 r6 q (Nat.le_of_not_lt hq)
  have s6_T : regValue c.T s6.basis = 2 * a * b :=
    (regValue_congr _ _ _ (fun q hq => loc6.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st6_zh.2.1
  have s6_S_zh : regValue c.R.S (zeroHigh s6).basis = regValue c.R.lo (zeroHigh s6).basis + regValue c.R.hi (zeroHigh s6).basis := by
    have eS : regValue c.R.S (zeroHigh s6).basis = a + b :=
      (regValue_congr _ _ s3.basis (fun q hq => by
        change q ∈ c.S at hq
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
        exact (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
          ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
            (s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
              (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))))).trans s3_S
    have elo : regValue c.R.lo (zeroHigh s6).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)),
          s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))]
        exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mLo hq)))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s6).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)),
          s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))]
        exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mHi hq)))).trans hb
    rw [eS, elo, ehi]
  have st7_zh := c.R.scl1591_correct wR nR (zeroHigh s6) r7 s6_S_zh
    (mk_zh_z s6 (fun q hq => by
      rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq)))
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq)))
    (by
      change (zeroHigh s6).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      rw [s6_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp)),
        s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))]
      exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0)
  have loc7 := run_below20000 c.R.scl1591 sup_parts.2.2.2.1 s6 r7
  generalize hs7 : run c.R.scl1591 r7 s6 = s7 at loc7 ⊢
  have s7_F (q : Wire) (hS : q ∉ c.S) : s7.basis q = s6.basis q := by
    by_cases hq : q < 20000
    · rw [loc7.2 q hq, st7_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs7]; exact run_ge20000 c.R.scl1591 sup_parts.2.2.2.1 s6 r7 q (Nat.le_of_not_lt hq)
  have s7_S0 : regValue c.S s7.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => loc7.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st7_zh.2.1
  have s7_dlo : regValue c.R8.dlo s7.basis = a ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq =>
      (s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq)))))))).trans s2_dlo
  have s7_dhi : regValue c.R8.dhi s7.basis = b ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq =>
      (s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))))))).trans s2_dhi
  have s7_T : regValue c.R8.T s7.basis = 2 * a * b :=
    (regValue_congr _ _ s6.basis (fun q hq => by
      change q ∈ c.T at hq
      exact s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s6_T
  have s7_z8 : regValue c.R8.z s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s7_S0 q (List.mem_of_mem_take (show q ∈ c.S.take 62 from hq)))
  have s7_zM : regValue c.R8.zM s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s7_z8 q (List.mem_of_mem_take (show q ∈ c.R8.z.take _ from hq)))
  have s7_car : regValue c.R8.carry s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      rw [s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s7_cin : s7.basis c.R8.cin = false := by
    change s7.basis K0.core.cin = false
    rw [s7_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp)),
      s6_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp)),
      s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))]
    exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0
  obtain ⟨p8, f8, v8⟩ := c.R8.m8z_correct wR8 nR8 s7 r8 (a * b)
    (fun q hq => (regValue_zero _ _).mp s7_car q (List.mem_of_mem_take hq))
    (by rw [s7_T]; ring) s7_cin
  generalize hs8 : run c.R8.m8z r8 s7 = s8 at p8 f8 v8 ⊢
  have s8_F (q : Wire) (hd : q ∉ c.dst) : s8.basis q = s7.basis q :=
    f8 q (fun h => hd (List.mem_of_mem_drop (show q ∈ c.dst.drop 64 from h)))
  have st8_dmid : regValue c.R8.dmid s8.basis = 2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2) := by
    have hm := dmid_val c v s7.basis; rw [s7_dlo, s7_dhi] at hm
    rw [v8, regValue_append, s7_T, s7_zM, hm, s7_cin]
    simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false]
    apply Nat.mod_eq_of_lt
    have bv64 : regValue c.R.bank s.basis = a + 2 ^ 64 * b := by
      simpa only [show c.R.h = 64 from rfl, ha, hb] using bv
    have hlt : a + 2 ^ 64 * b < 2 ^ c.n := by
      have hbl : c.n = c.R.bank.length := v.bankLen.symm
      rw [← bv64, hbl]; exact regValue_lt c.R.bank s.basis
    have hsq : (a + 2 ^ 64 * b) ^ 2 < 2 ^ (2 * c.n) := by
      have := Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0); simpa [← Nat.pow_mul, Nat.mul_comm] using this
    have hle : 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) ≤ (a + 2 ^ 64 * b) ^ 2 := by
      have h1 : 2 ^ 64 * (a ^ 2 / 2 ^ 64) ≤ a ^ 2 := Nat.mul_div_le (a ^ 2) (2 ^ 64)
      have h2 : (a + 2 ^ 64 * b) ^ 2 = a ^ 2 + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
      have h3 : 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) =
          2 ^ 64 * (a ^ 2 / 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
      rw [h2, h3]; exact Nat.add_le_add_right h1 _
    have hdmid : c.R8.dmid.length = 2 * c.n - 64 := by simp [KRegs.dmid, SplitCfg.R8, v.dstLen]
    rw [hdmid]
    have hpow : 2 ^ 64 * 2 ^ (2 * c.n - 64) = 2 ^ (2 * c.n) := by rw [← Nat.pow_add]; congr 1; rcases v.hn with h | h <;> omega
    exact Nat.lt_of_mul_lt_mul_left (hpow.symm ▸ Nat.lt_of_le_of_lt hle hsq)
  refine ⟨p8.trans (loc7.1.trans (st7_zh.1.trans (loc6.1.trans (st6_zh.1.trans (loc5.1.trans (st5_zh.1.trans (st4.1.trans (loc3.1.trans (st3_zh.1.trans (st2.1.trans st1.1)))))))))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hsplit := regValue_append (c.dst.take 64) c.R8.dmid s8.basis
    rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst] at hsplit
    have hlo64 : regValue (c.dst.take 64) s8.basis = a ^ 2 % 2 ^ 64 := by
      have e : regValue (c.dst.take 64) s8.basis = regValue (c.dst.take 64) s7.basis :=
        regValue_congr _ _ _ (fun q hq => by
          apply f8
          have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
          rw [← List.take_append_drop 64 c.dst] at hnd
          exact fun hm => (List.nodup_append.mp hnd).2.2 q hq q hm rfl)
      rw [e, show c.dst.take 64 = c.R8.dlo.take 64 from by simp [KRegs.dlo, SplitCfg.R8, List.take_take],
        regValue_take_mod c.R8.dlo 64 (by simp [KRegs.dlo, SplitCfg.R8, v.dstLen]; rcases v.hn with h | h <;> omega), s7_dlo]
    have hlen64 : (c.dst.take 64).length = 64 := by simp [v.dstLen]; rcases v.hn with h | h <;> omega
    have bv64 : regValue c.R.bank s.basis = a + 2 ^ 64 * b := by
      simpa only [show c.R.h = 64 from rfl, ha, hb] using bv
    rw [hsplit, hlen64, hlo64, st8_dmid, show c.bank = c.R.bank from rfl, bv64]
    have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
    have hring : a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) =
        (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
    rw [hring, hdiv]; ring
  · exact (regValue_congr _ _ s7.basis (fun q hq => s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s7_T
  · exact (regValue_congr _ _ s2.basis (fun q hq =>
      (s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))))))).trans s2_T1
  · exact (regValue_congr _ _ s2.basis (fun q hq =>
      (s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))))))).trans s2_T2
  · exact (regValue_congr _ _ s4.basis (fun q hq =>
      (s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))))).trans s4_T5
  · intro q hd hL
    have hT : q ∉ c.T := fun h => hL (by simp [SplitCfg.liveT, h])
    rw [s8_F q hd]
    by_cases hS : q ∈ c.S
    · exact ((regValue_zero _ _).mp s7_S0 q hS).trans ((regValue_zero _ _).mp hS0 q hS).symm
    · exact (s7_F q hS).trans ((s6_F q hT).trans ((s5_F q hT).trans (F4 q hd hS hL)))

/-- Exact postcondition of `c.clear` restoring `dst` and `liveT` to 0. -/
theorem cfg_clear_correct (c : SplitCfg) (v : CfgValid c) (s : State) (m : List Bool)
    (hd0 : regValue c.dst s.basis = (regValue c.bank s.basis) ^ 2)
    (hT : regValue c.T s.basis = 2 * regValue c.R.lo s.basis * regValue c.R.hi s.basis)
    (hT1 : regValue c.T1 s.basis = 2 * (regValue c.R.lo s.basis % 2 ^ 32) * (regValue c.R.lo s.basis / 2 ^ 32))
    (hT2 : regValue c.T2 s.basis = 2 * (regValue c.R.hi s.basis % 2 ^ c.Q2.h) * (regValue c.R.hi s.basis / 2 ^ c.Q2.h))
    (hT5 : regValue c.T5 s.basis = 2 * ((regValue c.R.lo s.basis + regValue c.R.hi s.basis) % 2 ^ 33) *
      ((regValue c.R.lo s.basis + regValue c.R.hi s.basis) / 2 ^ 33))
    (hSc0 : regValue c.cleanScratch s.basis = 0)
    (hi0 : s.basis K0.core.cin = false) :
    let u := run c.clear m s
    u.phase = s.phase ∧
    regValue c.dst u.basis = 0 ∧
    regValue c.liveT u.basis = 0 ∧
    ∀ q, q ∉ c.dst → q ∉ c.liveT → u.basis q = s.basis q := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  obtain ⟨nR, nR8, n1, n2, n5⟩ := cfg_nodups c v
  have sup := cfg_support c v; have hr := v.realNd
  have dj {A B : List Wire} (h : ∀ q, A.count q + B.count q ≤ c.realAll.count q) : ∀ q ∈ A, q ∉ B := kdis hr h
  have zOf (r : List Wire) (sub : ∀ q ∈ r, q ∈ c.cleanScratch) : regValue r s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hSc0 q (sub q hq))
  have hS0 : regValue c.S s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hz40 : regValue c.zReal4 s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hpad0 : regValue K0.leafPad s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hcar0 : regValue c.carry s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hzpad0 : s.basis c.zpad = false := (regValue_zero _ _).mp hSc0 c.zpad (by simp [SplitCfg.cleanScratch])
  have hzd0 : s.basis c.zdst0 = false := (regValue_zero _ _).mp hSc0 c.zdst0 (by simp [SplitCfg.cleanScratch])
  have hzd1 : s.basis c.zdst1 = false := (regValue_zero _ _).mp hSc0 c.zdst1 (by simp [SplitCfg.cleanScratch])
  have bv := c.R.bank_value wR s.basis
  obtain ⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10⟩ := c.R.lens wR
  generalize ha : regValue c.R.lo s.basis = a at hT hT1 hT5 ⊢
  generalize hb : regValue c.R.hi s.basis = b at hT hT2 hT5 ⊢
  have aLt : a < 2 ^ 64 := by rw [← ha]; simpa [L0] using regValue_lt c.R.lo s.basis
  have bLt : b < 2 ^ (c.n - 64) := by
    rw [← hb]; have h := regValue_lt c.R.hi s.basis
    rw [L1, show c.R.bank.length = c.n from v.bankLen, show c.R.h = 64 from rfl] at h; exact h
  have realStep (P : Program) (hp : wires P ⊆ c.realAll.toFinset) : ∀ q ∈ wires P, q < 20000 :=
    fun q hq => v.realLt q (List.mem_toFinset.mp (hp hq))
  have sup_parts : (∀ q ∈ wires c.R8.c8z, q < 20000) ∧ (∀ q ∈ wires c.R.smkT, q < 20000) ∧
      (∀ q ∈ wires c.R.c7t, q < 20000) ∧ (∀ q ∈ wires c.R.c6h, q < 20000) ∧
      (∀ q ∈ wires c.R.scl1591, q < 20000) := by
    have sc := sup.2
    simp only [SplitCfg.clear, wires_append, Finset.union_subset_iff] at sc
    exact ⟨realStep _ sc.1.1.1.1.1.1.1, realStep _ sc.1.1.1.1.1.1.2, realStep _ sc.1.1.1.1.1.2,
      realStep _ sc.1.1.1.1.2, realStep _ sc.1.1.2⟩
  obtain ⟨a7, r8, e8⟩ := kseq (c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    LowZero18Diagonal.clearC c.Q5 ++ c.R.scl1591 ++ LowZero18Diagonal.clearC c.Q2)
    (LowZero18Diagonal.clearC c.Q1) m s
  obtain ⟨a6, r7, e7⟩ := kseq (c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    LowZero18Diagonal.clearC c.Q5 ++ c.R.scl1591) (LowZero18Diagonal.clearC c.Q2) a7 s
  obtain ⟨a5, r6, e6⟩ := kseq (c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    LowZero18Diagonal.clearC c.Q5) c.R.scl1591 a6 s
  obtain ⟨a4, r5, e5⟩ := kseq (c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h)
    (LowZero18Diagonal.clearC c.Q5) a5 s
  obtain ⟨a3, r4, e4⟩ := kseq (c.R8.c8z ++ c.R.smkT ++ c.R.c7t) c.R.c6h a4 s
  obtain ⟨a2, r3, e3⟩ := kseq (c.R8.c8z ++ c.R.smkT) c.R.c7t a3 s
  obtain ⟨r1, r2, e2⟩ := kseq c.R8.c8z c.R.smkT a2 s
  dsimp only
  rw [SplitCfg.clear, e8, e7, e6, e5, e4, e3, e2]
  have mLo {q : Wire} (h : q ∈ c.R.lo) : q ∈ c.bank := List.mem_of_mem_take (show q ∈ c.bank.take 64 from h)
  have mHi {q : Wire} (h : q ∈ c.R.hi) : q ∈ c.bank := List.mem_of_mem_drop (show q ∈ c.bank.drop 64 from h)
  have mDlo {q : Wire} (h : q ∈ c.R.dlo) : q ∈ c.dst := List.mem_of_mem_take (show q ∈ c.dst.take 128 from h)
  have mDhi {q : Wire} (h : q ∈ c.R.dhi) : q ∈ c.dst := List.mem_of_mem_drop (show q ∈ c.dst.drop 128 from h)
  have bLtR : b < 2 ^ (c.R.bank.length - c.R.h) := by simpa [SplitCfg.R, v.bankLen] using bLt
  have hTl := wR.T; have hSl := wR.S; have hhR := wR.hh; have h4R := wR.h4; have hclR := wR.carry
  have ex : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
  have sumLt : a + b < 2 ^ c.R.S.length := by
    have hp : 2 ^ c.R.h ≤ 2 ^ (c.R.bank.length - c.R.h) := Nat.pow_le_pow_right (by decide) (by clear * - hhR; omega)
    have hq : 2 ^ c.R.S.length = 2 * 2 ^ (c.R.bank.length - c.R.h) := by rw [hSl, pow_succ]; ring
    have haR : a < 2 ^ c.R.h := aLt
    clear * - haR bLtR hp hq; omega
  have sqLt : (a + b) ^ 2 < 2 ^ c.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have bv64 : regValue c.R.bank s.basis = a + 2 ^ 64 * b := by
    simpa only [show c.R.h = 64 from rfl, ha, hb] using bv
  have hdmid_init : regValue c.R8.dmid s.basis = 2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2) := by
    have hsplit := regValue_append (c.dst.take 64) c.R8.dmid s.basis
    rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst] at hsplit
    have hlen64 : (c.dst.take 64).length = 64 := by simp [v.dstLen]; rcases v.hn with h | h <;> omega
    rw [hsplit, hlen64, show c.bank = c.R.bank from rfl, bv64] at hd0
    have hlt64 : regValue (c.dst.take 64) s.basis < 2 ^ 64 := by have := regValue_lt (c.dst.take 64) s.basis; rwa [hlen64] at this
    have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
    have hmod_lt : a ^ 2 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    have hsq : (a + 2 ^ 64 * b) ^ 2 = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by
      calc (a + 2 ^ 64 * b) ^ 2 = a ^ 2 + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
      _ = (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by rw [hdiv]
      _ = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by ring
    rw [hsq] at hd0
    have hdivq := congrArg (· / 2 ^ 64) hd0
    dsimp only at hdivq
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 64), Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 64),
      Nat.div_eq_of_lt hlt64, Nat.div_eq_of_lt hmod_lt] at hdivq
    simpa only [Nat.zero_add] using hdivq
  obtain ⟨p1, f1, v1⟩ := c.R8.c8z_correct wR8 nR8 s r1
    (fun q hq => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_take hq))
    (by
      rw [LowZero.head_false_of_even c.R8.T c.R8.zM s.basis (a * b)
        (by rw [show c.R8.T = c.T from rfl, hT]; ring) (c.R8.T_ne wR8)]
      rfl)
    hi0
  generalize hs1 : run c.R8.c8z r1 s = s1 at p1 f1 v1 ⊢
  have s1_F (q : Wire) (hd : q ∉ c.dst) : s1.basis q = s.basis q :=
    f1 q (fun h => hd (List.mem_of_mem_drop (show q ∈ c.dst.drop 64 from h)))
  have st1_dmid : regValue c.R8.dmid s1.basis = a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2 := by
    have s_zM : regValue c.R8.zM s.basis = 0 :=
      (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hS0 q
        (List.mem_of_mem_take (show q ∈ c.S.take 62 from List.mem_of_mem_take (show q ∈ c.R8.z.take _ from hq))))
    have hlt : 2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2) < 2 ^ c.R8.dmid.length := by
      rw [← hdmid_init]; exact regValue_lt c.R8.dmid s.basis
    rw [v1, regValue_append, show c.R8.T = c.T from rfl, hT, s_zM, hdmid_init, show c.R8.cin = K0.core.cin from rfl, hi0]
    simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false, Nat.sub_zero]
    rw [ksubmod _ _ _ (Nat.le_add_right _ _) hlt]
    exact Nat.add_sub_cancel_left _ _
  have s1_dst_eq : regValue c.dst s1.basis = a ^ 2 + 2 ^ 128 * b ^ 2 := by
    have hsplit := regValue_append (c.dst.take 64) c.R8.dmid s1.basis
    rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst] at hsplit
    have hlen64 : (c.dst.take 64).length = 64 := by simp [v.dstLen]; rcases v.hn with h | h <;> omega
    have hlo64 : regValue (c.dst.take 64) s1.basis = a ^ 2 % 2 ^ 64 := by
      have e : regValue (c.dst.take 64) s1.basis = regValue (c.dst.take 64) s.basis :=
        regValue_congr _ _ _ (fun q hq => by
          apply f1
          have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
          rw [← List.take_append_drop 64 c.dst] at hnd
          exact fun hm => (List.nodup_append.mp hnd).2.2 q hq q hm rfl)
      rw [e]
      have hsp := regValue_append (c.dst.take 64) c.R8.dmid s.basis
      rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst, hlen64] at hsp
      rw [hsp, hdmid_init, show c.bank = c.R.bank from rfl, bv64] at hd0
      have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
      have hsq : (a + 2 ^ 64 * b) ^ 2 = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by
        calc (a + 2 ^ 64 * b) ^ 2 = a ^ 2 + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
        _ = (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by rw [hdiv]
        _ = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by ring
      rw [hsq] at hd0
      exact Nat.add_right_cancel hd0
    rw [hsplit, hlen64, hlo64, st1_dmid]
    have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
    calc a ^ 2 % 2 ^ 64 + 2 ^ 64 * (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)
        = (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 128 * b ^ 2 := by ring
      _ = a ^ 2 + 2 ^ 128 * b ^ 2 := by rw [hdiv]
  have s1_dlo : regValue c.R.dlo s1.basis = a ^ 2 := by
    have h128 := regValue_append c.R.dlo c.R.dhi s1.basis
    rw [show c.R.dlo ++ c.R.dhi = c.dst from List.take_append_drop 128 c.dst, L2, show c.R.h = 64 from rfl, s1_dst_eq] at h128
    have ha2 : a ^ 2 < 2 ^ 128 := by have := Nat.pow_lt_pow_left aLt (by decide : 2 ≠ 0); simpa [← Nat.pow_mul] using this
    have hdloLt : regValue c.R.dlo s1.basis < 2 ^ 128 := by have := regValue_lt c.R.dlo s1.basis; rwa [L2, show c.R.h = 64 from rfl] at this
    have hmod := congrArg (· % 2 ^ 128) h128
    dsimp only at hmod
    rw [show (2 : Nat) ^ (2 * 64) = 2 ^ 128 from rfl,
      Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdloLt, Nat.mod_eq_of_lt ha2] at hmod
    exact hmod.symm
  have s1_dhi : regValue c.R.dhi s1.basis = b ^ 2 := by
    have h128 := regValue_append c.R.dlo c.R.dhi s1.basis
    rw [show c.R.dlo ++ c.R.dhi = c.dst from List.take_append_drop 128 c.dst, L2, show c.R.h = 64 from rfl,
      show (2 : Nat) ^ (2 * 64) = 2 ^ 128 from rfl, s1_dst_eq, s1_dlo] at h128
    exact (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2 ^ 128) (Nat.add_left_cancel h128)).symm
  have mk_zh_z (t : State) (ht : ∀ q ∈ c.zReal4, t.basis q = false) : regValue c.R.z (zeroHigh t).basis = 0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    simp only [SplitCfg.R, List.mem_append] at hq
    rcases hq with hq | hq
    · simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]; exact ht q hq
    · simp only [zeroHigh, (List.mem_range'_1.mp hq).1, if_true]
  have s1_T_zh : regValue c.R.T (zeroHigh s1).basis = 2 * regValue c.R.lo (zeroHigh s1).basis * regValue c.R.hi (zeroHigh s1).basis := by
    have eT : regValue c.R.T (zeroHigh s1).basis = 2 * a * b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        change q ∈ c.T at hq
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
        exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT
    have elo : regValue c.R.lo (zeroHigh s1).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s1).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
    rw [eT, elo, ehi]
  have s1_S0_zh : regValue c.R.S (zeroHigh s1).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.S at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hS0 q hq))
  have s1_car0_zh : regValue c.R.carry (zeroHigh s1).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s1_cin0_zh : (zeroHigh s1).basis c.R.cin = false := by
    change (zeroHigh s1).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    exact (s1_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s1_z0_zh : regValue c.R.z (zeroHigh s1).basis = 0 :=
    mk_zh_z s1 (fun q hq => (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))
  have smkT_eq := c.R.smkT_run wR nR (zeroHigh s1) r2 s1_T_zh s1_S0_zh s1_cin0_zh
  have st2_zh := c.R.smk_correct wR nR (zeroHigh s1) r2 s1_S0_zh s1_z0_zh s1_car0_zh s1_cin0_zh
  rw [← smkT_eq] at st2_zh
  have loc2 := run_below20000 c.R.smkT sup_parts.2.1 s1 r2
  generalize hs2 : run c.R.smkT r2 s1 = s2 at loc2 ⊢
  have s2_F (q : Wire) (hS : q ∉ c.S) : s2.basis q = s1.basis q := by
    by_cases hq : q < 20000
    · rw [loc2.2 q hq, st2_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs2]; exact run_ge20000 c.R.smkT sup_parts.2.1 s1 r2 q (Nat.le_of_not_lt hq)
  have s2_S : regValue c.S s2.basis = a + b := by
    have e1 := regValue_congr c.S s2.basis (run c.R.smkT r2 (zeroHigh s1)).basis
      (fun q hq => loc2.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))
    rw [e1, show c.S = c.R.S from rfl, st2_zh.2.1]
    have elo : regValue c.R.lo (zeroHigh s1).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s1).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
    rw [elo, ehi]
  have s2_dhi_zh : regValue c.R.dhi (zeroHigh s2).basis = b ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDhi hq, true_or, or_true])), if_false]
      exact s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))).trans s1_dhi
  have s2_T_zh : regValue c.R.T (zeroHigh s2).basis = 2 * a * b :=
    (regValue_congr _ _ s.basis (fun q hq => by
      change q ∈ c.T at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))).trans hT
  have s2_z_zh : regValue c.R.z (zeroHigh s2).basis = 0 :=
    mk_zh_z s2 (fun q hq => (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq)))
  have s2_zB_zh : regValue c.R.zB (zeroHigh s2).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s2_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have s2_car_zh : regValue c.R.carry (zeroHigh s2).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq)))
  have s2_cin_zh : (zeroHigh s2).basis c.R.cin = false := by
    change (zeroHigh s2).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    exact (s2_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
      ((s1_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0)
  have xv2 : regValue (c.R.dhi ++ c.R.zB) (zeroHigh s2).basis = b ^ 2 := by
    rw [regValue_append, s2_dhi_zh, s2_zB_zh]; simp
  have st3_zh : (run c.R.c7t r3 (zeroHigh s2)).phase = (zeroHigh s2).phase ∧
      regValue c.R.T (run c.R.c7t r3 (zeroHigh s2)).basis = 2 * a * b + b ^ 2 ∧
      ∀ q, q ∉ c.R.T → (run c.R.c7t r3 (zeroHigh s2)).basis q = (zeroHigh s2).basis q := by
    obtain ⟨p, f, val⟩ := c.R.c7t_correct wR nR (zeroHigh s2) r3
      (fun q hq => (regValue_zero _ _).mp s2_car_zh q (List.mem_of_mem_take hq))
      (by
        have hT' := LowZero.head_false_of_even c.R.T [] (zeroHigh s2).basis (a * b) (by rw [s2_T_zh]; ring) (c.R.T_ne wR)
        rw [List.append_nil] at hT'
        rw [hT']; exact Bool.and_false _)
      s2_cin_zh
      (by rw [KRegs.bit1 c.R.dhi c.R.zB (zeroHigh s2).basis (c.R.dhi_two wR), s2_dhi_zh, KRegs.sq_bit1]; rfl)
      (fun _ => by rw [xv2, hTl, hSl]; exact KRegs.sq_trim_bound c.R.bank.length c.R.h b bLtR)
      (fun tc => by
        have tb := KRegs.trim_bound c.R.bank.length c.R.h a b tc aLt bLtR
        rw [xv2, s2_T_zh, hTl, hSl, Nat.mod_eq_of_lt (by clear * - tb; omega)]; clear * - tb; omega)
    refine ⟨p, ?_, f⟩
    rw [val, xv2, s2_T_zh, s2_cin_zh]
    simp only [Bool.toNat_false, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by clear * - ex sqLt; omega)]; ring
  have loc3 := run_below20000 c.R.c7t sup_parts.2.2.1 s2 r3
  generalize hs3 : run c.R.c7t r3 s2 = s3 at loc3 ⊢
  have s3_F (q : Wire) (hT' : q ∉ c.T) : s3.basis q = s2.basis q := by
    by_cases hq : q < 20000
    · rw [loc3.2 q hq, st3_zh.2.2 q hT']; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs3]; exact run_ge20000 c.R.c7t sup_parts.2.2.1 s2 r3 q (Nat.le_of_not_lt hq)
  have s3_T : regValue c.T s3.basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ _ (fun q hq => loc3.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st3_zh.2.1
  have s3_dlo_zh : regValue c.R.dlo (zeroHigh s3).basis = a ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDlo hq, true_or, or_true])), if_false]
      exact (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))))).trans s1_dlo
  have s3_T_zh : regValue c.R.T (zeroHigh s3).basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ s3.basis (fun q hq => by
      change q ∈ c.T at hq; simp [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true]))])).trans s3_T
  have s3_z_zh : regValue c.R.z (zeroHigh s3).basis = 0 :=
    mk_zh_z s3 (fun q hq => (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))))
  have s3_zA_zh : regValue c.R.zA (zeroHigh s3).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s3_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have s3_car_zh : regValue c.R.carry (zeroHigh s3).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))))
  have s3_cin_zh : (zeroHigh s3).basis c.R.cin = false := by
    change (zeroHigh s3).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    exact (s3_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
      ((s2_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
      ((s1_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0))
  have st4_zh : (run c.R.c6h r4 (zeroHigh s3)).phase = (zeroHigh s3).phase ∧
      regValue c.R.T (run c.R.c6h r4 (zeroHigh s3)).basis = (a + b) ^ 2 ∧
      ∀ q, q ∉ c.R.T → (run c.R.c6h r4 (zeroHigh s3)).basis q = (zeroHigh s3).basis q := by
    have hn6 : (c.R.cin :: ((c.R.dlo ++ c.R.zA) ++ c.R.T ++ c.R.carry.take (c.R.T.length - 1))).Nodup :=
      knd nR (fun q => by
        have := c.R.counts q
        clear * - this
        simp only [KRegs.all, List.count_cons, List.count_append] at this ⊢; omega)
    rw [c.R.c6h_run wR hn6 (zeroHigh s3) r4
      (fun q hq => (regValue_zero _ _).mp s3_car_zh q (List.mem_of_mem_take hq))
      s3_cin_zh (c.R.c6c_bits wR (zeroHigh s3).basis a b s3_T_zh s3_dlo_zh)]
    unfold KRegs.c6
    obtain ⟨p, f, val⟩ := addInPlace_correct (c.R.dlo ++ c.R.zA) c.R.T
      (c.R.carry.take (c.R.T.length - 1)) c.R.cin hn6
      (by rw [List.length_append, L2, L6]; omega)
      (by rw [List.length_take]; omega)
      (zeroHigh s3) r4 (fun q hq => (regValue_zero _ _).mp s3_car_zh q (List.mem_of_mem_take hq))
    refine ⟨p, ?_, f⟩
    rw [val, regValue_append, s3_dlo_zh, s3_zA_zh, s3_T_zh, s3_cin_zh]
    simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by linarith only [ex, sqLt]), ex]; ring
  have loc4 := run_below20000 c.R.c6h sup_parts.2.2.2.1 s3 r4
  generalize hs4 : run c.R.c6h r4 s3 = s4 at loc4 ⊢
  have s4_F (q : Wire) (hT' : q ∉ c.T) : s4.basis q = s3.basis q := by
    by_cases hq : q < 20000
    · rw [loc4.2 q hq, st4_zh.2.2 q hT']; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs4]; exact run_ge20000 c.R.c6h sup_parts.2.2.2.1 s3 r4 q (Nat.le_of_not_lt hq)
  have s4_T : regValue c.T s4.basis = (a + b) ^ 2 :=
    (regValue_congr _ _ _ (fun q hq => loc4.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st4_zh.2.1
  have s4_out (q : Wire) (hd : q ∉ c.dst) (hS : q ∉ c.S) (hT' : q ∉ c.T) : s4.basis q = s.basis q :=
    (s4_F q hT').trans ((s3_F q hT').trans ((s2_F q hS).trans (s1_F q hd)))
  have s4_S : regValue c.S s4.basis = a + b :=
    (regValue_congr _ _ s2.basis (fun q hq =>
      (s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))).trans s2_S
  have s4_Q5_bank : regValue c.Q5.bank s4.basis = a + b := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true]
      rw [regValue_snoc_zero _ _ _ ((s4_out c.zpad
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzpad0), s4_S]
    · simpa [SplitCfg.Q5, hn] using s4_S
  have s4_Q5_dst : regValue c.Q5.dst s4.basis = (regValue c.Q5.bank s4.basis) ^ 2 := by
    rw [s4_Q5_bank]
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true, regValue_append, s4_T]
      have b0 : s4.basis c.zdst0 = false := (s4_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0
      have b1 : s4.basis c.zdst1 = false := (s4_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1
      simp [regValue, b0, b1]
    · simpa [SplitCfg.Q5, hn] using s4_T
  have s4_car0 : regValue c.carry s4.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s4_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s4_pad0 : regValue K0.leafPad s4.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s4_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hpad0 q hq))
  have s4_cin0 : s4.basis K0.core.cin = false :=
    (s4_out _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s4_T5 : regValue c.T5 s4.basis = 2 * ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) :=
    (regValue_congr _ _ s.basis (fun q hq => s4_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT5
  have st5 := clearC_clean c.Q5 w5.1 w5.2.1 (Or.inr w5.2.2) n5 s4 r5 s4_Q5_dst
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by
      rw [c.Q5.lo_mod w5.1, c.Q5.hi_div w5.1, s4_Q5_bank, w5.2.2]
      by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s4_T5)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s4_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s4_cin0)
  generalize hs5 : run (LowZero18Diagonal.clearC c.Q5) r5 s4 = s5 at st5 ⊢
  have s5_T0 : regValue c.T s5.basis = 0 := by
    have h := st5.2.1
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true, regValue_append] at h; omega
    · simpa [SplitCfg.Q5, hn] using h
  have s5_T5_0 : regValue c.T5 s5.basis = 0 := by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using st5.2.2.1
  have s5_zd0 : s5.basis c.zdst0 = false ∧ s5.basis c.zdst1 = false := by
    by_cases hn : c.n = 128
    · have h := st5.2.1; simp only [SplitCfg.Q5, hn, if_true] at h
      exact ⟨(regValue_zero _ _).mp h c.zdst0 (by simp), (regValue_zero _ _).mp h c.zdst1 (by simp)⟩
    · exact ⟨(st5.2.2.2 _ (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
        ((s4_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
        (st5.2.2.2 _ (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
        ((s4_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
  have s5_F (q : Wire) (hT' : q ∉ c.T) (hT5' : q ∉ c.T5) : s5.basis q = s4.basis q := by
    by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
    · rcases hzd with rfl | rfl
      · exact s5_zd0.1.trans ((s4_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0).symm
      · exact s5_zd0.2.trans ((s4_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1).symm
    · apply st5.2.2.2
      · by_cases hn : c.n = 128
        · simp only [SplitCfg.Q5, hn, if_true, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | rfl | rfl)
          · exact hT' h
          · exact hzd (Or.inl rfl)
          · exact hzd (Or.inr rfl)
        · simpa [SplitCfg.Q5, hn] using hT'
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using hT5'
  have s5_S_zh : regValue c.R.S (zeroHigh s5).basis = regValue c.R.lo (zeroHigh s5).basis + regValue c.R.hi (zeroHigh s5).basis := by
    have eS : regValue c.R.S (zeroHigh s5).basis = a + b :=
      (regValue_congr _ _ s4.basis (fun q hq => by
        change q ∈ c.S at hq
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
        exact s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s4_S
    have elo : regValue c.R.lo (zeroHigh s5).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))).trans
          (s4_out q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
            (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
            (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s5).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))).trans
          (s4_out q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
            (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
            (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))))).trans hb
    rw [eS, elo, ehi]
  have st6_zh := c.R.scl1591_correct wR nR (zeroHigh s5) r6 s5_S_zh
    (mk_zh_z s5 (fun q hq => (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s4_out q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))))
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp s4_car0 q hq)))
    (by
      change (zeroHigh s5).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      exact (s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans s4_cin0)
  have loc6 := run_below20000 c.R.scl1591 sup_parts.2.2.2.2 s5 r6
  generalize hs6 : run c.R.scl1591 r6 s5 = s6 at loc6 ⊢
  have s6_F (q : Wire) (hS : q ∉ c.S) : s6.basis q = s5.basis q := by
    by_cases hq : q < 20000
    · rw [loc6.2 q hq, st6_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs6]; exact run_ge20000 c.R.scl1591 sup_parts.2.2.2.2 s5 r6 q (Nat.le_of_not_lt hq)
  have s6_S0 : regValue c.S s6.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => loc6.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st6_zh.2.1
  have s6_out (q : Wire) (hd : q ∉ c.dst) (hT' : q ∉ c.T) (hT5' : q ∉ c.T5) : s6.basis q = s.basis q := by
    by_cases hS : q ∈ c.S
    · exact ((regValue_zero _ _).mp s6_S0 q hS).trans ((regValue_zero _ _).mp hS0 q hS).symm
    · exact (s6_F q hS).trans ((s5_F q hT' hT5').trans (s4_out q hd hS hT'))
  have s6_Q2_bank : regValue c.Q2.bank s6.basis = b := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q2, hn, if_true]
      exact (regValue_congr _ _ s.basis (fun q hq => s6_out q
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
    · simp only [SplitCfg.Q2, hn, if_false]
      rw [regValue_snoc_zero _ _ _ ((s6_out c.zpad
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzpad0)]
      exact (regValue_congr _ _ s.basis (fun q hq => s6_out q
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
  have s6_dhi : regValue c.R.dhi s6.basis = b ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq =>
      (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
        (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))))))).trans s1_dhi
  have s6_Q2_dst : regValue c.Q2.dst s6.basis = (regValue c.Q2.bank s6.basis) ^ 2 := by
    rw [s6_Q2_bank]
    by_cases hn : c.n = 128
    · simpa [SplitCfg.Q2, hn] using s6_dhi
    · simp only [SplitCfg.Q2, hn, if_false, regValue_append, s6_dhi]
      have b0 : s6.basis c.zdst0 = false := (s6_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0
      have b1 : s6.basis c.zdst1 = false := (s6_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1
      simp [regValue, b0, b1]
  have s6_car0 : regValue c.carry s6.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s6_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s6_pad0 : regValue K0.leafPad s6.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s6_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hpad0 q hq))
  have s6_cin0 : s6.basis K0.core.cin = false :=
    (s6_out _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s6_T2 : regValue c.T2 s6.basis = 2 * (b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h) :=
    (regValue_congr _ _ s.basis (fun q hq => s6_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT2
  have st7 := clearC_clean c.Q2 w2.1 w2.2.1 w2.2.2 n2 s6 r7 s6_Q2_dst
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by
      rw [c.Q2.lo_mod w2.1, c.Q2.hi_div w2.1, s6_Q2_bank]
      by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s6_T2)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s6_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s6_cin0)
  generalize hs7 : run (LowZero18Diagonal.clearC c.Q2) r7 s6 = s7 at st7 ⊢
  have s7_dhi0 : regValue c.R.dhi s7.basis = 0 := by
    have h := st7.2.1
    by_cases hn : c.n = 128
    · simpa [SplitCfg.Q2, hn] using h
    · simp only [SplitCfg.Q2, hn, if_false, regValue_append] at h; omega
  have s7_T2_0 : regValue c.T2 s7.basis = 0 := by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using st7.2.2.1
  have s7_zd0 : s7.basis c.zdst0 = false ∧ s7.basis c.zdst1 = false := by
    by_cases hn : c.n = 128
    · exact ⟨(st7.2.2.2 _ (by simp [SplitCfg.Q2, hn]; exact fun h => dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp) (mDhi h))
        (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
        ((s6_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
        (st7.2.2.2 _ (by simp [SplitCfg.Q2, hn]; exact fun h => dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp) (mDhi h))
        (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
        ((s6_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
    · have h := st7.2.1; simp only [SplitCfg.Q2, hn, if_false] at h
      exact ⟨(regValue_zero _ _).mp h c.zdst0 (by simp), (regValue_zero _ _).mp h c.zdst1 (by simp)⟩
  have s7_F (q : Wire) (hd : q ∉ c.R.dhi) (hT2' : q ∉ c.T2) : s7.basis q = s6.basis q := by
    by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
    · rcases hzd with rfl | rfl
      · exact s7_zd0.1.trans ((s6_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0).symm
      · exact s7_zd0.2.trans ((s6_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1).symm
    · apply st7.2.2.2
      · by_cases hn : c.n = 128
        · simpa [SplitCfg.Q2, hn] using hd
        · simp only [SplitCfg.Q2, hn, if_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | rfl | rfl)
          · exact hd h
          · exact hzd (Or.inl rfl)
          · exact hzd (Or.inr rfl)
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using hT2'
  have dlo_dhi : ∀ q ∈ c.R.dlo, q ∉ c.R.dhi := by
    intro q h1 h2
    have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
    rw [← List.take_append_drop 128 c.dst] at hnd
    exact (List.nodup_append.mp hnd).2.2 q h1 q h2 rfl
  have s7_dlo : regValue c.R.dlo s7.basis = a ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq =>
      (s7_F q (dlo_dhi q hq) (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))))))))).trans s1_dlo
  have s7_out (q : Wire) (hd : q ∉ c.dst) (hT' : q ∉ c.T) (hT2' : q ∉ c.T2) (hT5' : q ∉ c.T5) : s7.basis q = s.basis q :=
    (s7_F q (fun h => hd (mDhi h)) hT2').trans (s6_out q hd hT' hT5')
  have s7_lo : regValue c.Q1.bank s7.basis = a :=
    (regValue_congr _ _ s.basis (fun q hq => s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
  have s7_T1 : regValue c.T1 s7.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) :=
    (regValue_congr _ _ s.basis (fun q hq => s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT1
  have s7_car0 : regValue c.carry s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s7_pad0 : regValue K0.leafPad s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hpad0 q hq))
  have s7_cin0 : s7.basis K0.core.cin = false :=
    (s7_out _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have st8 := clearC_clean c.Q1 w1.1 w1.2 (Or.inl rfl) n1 s7 r8 (by rw [s7_lo]; exact s7_dlo)
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp s7_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by rw [c.Q1.lo_mod w1.1, c.Q1.hi_div w1.1, s7_lo]; exact s7_T1)
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp s7_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    s7_pad0
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp s7_car0 q (List.mem_of_mem_take h)))
    s7_cin0
  generalize hs8 : run (LowZero18Diagonal.clearC c.Q1) r8 s7 = s8 at st8 ⊢
  have s8_F (q : Wire) (hd : q ∉ c.R.dlo) (hT1' : q ∉ c.T1) : s8.basis q = s7.basis q := st8.2.2.2 q hd hT1'
  refine ⟨st8.1.trans (st7.1.trans (loc6.1.trans (st6_zh.1.trans (st5.1.trans (loc4.1.trans (st4_zh.1.trans (loc3.1.trans (st3_zh.1.trans (loc2.1.trans (st2_zh.1.trans p1)))))))))),
    ?_, ?_, ?_⟩
  · have h128 := regValue_append c.R.dlo c.R.dhi s8.basis
    rw [show c.R.dlo ++ c.R.dhi = c.dst from List.take_append_drop 128 c.dst] at h128
    have hdhi : regValue c.R.dhi s8.basis = 0 :=
      (regValue_congr _ _ s7.basis (fun q hq => s8_F q (fun h => dlo_dhi q h hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))).trans s7_dhi0
    rw [h128, show c.R.dlo = c.Q1.dst from rfl, st8.2.1, hdhi]; simp
  · have hT_z : regValue c.T s8.basis = 0 :=
      (regValue_congr _ _ s5.basis (fun q hq =>
        (s8_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq (mDlo h))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s7_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq (mDhi h))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
          (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))))).trans s5_T0
    have hT2_z : regValue c.T2 s8.basis = 0 :=
      (regValue_congr _ _ s7.basis (fun q hq => s8_F q
        (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo h) hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s7_T2_0
    have hT5_z : regValue c.T5 s8.basis = 0 :=
      (regValue_congr _ _ s5.basis (fun q hq =>
        (s8_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo h) hq)
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s7_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi h) hq)
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
          (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))))).trans s5_T5_0
    simp only [SplitCfg.liveT, regValue_append, hT_z, show c.T1 = c.Q1.T from rfl, st8.2.2.1, hT2_z, hT5_z]
    simp
  · intro q hd hL
    have hT' : q ∉ c.T := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT1' : q ∉ c.T1 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT2' : q ∉ c.T2 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT5' : q ∉ c.T5 := fun h => hL (by simp [SplitCfg.liveT, h])
    exact (s8_F q (fun h => hd (mDlo h)) hT1').trans (s7_out q hd hT' hT2' hT5')

theorem cfg_counts_H (c : SplitCfg) (v : CfgValid c) (hn : c.n = 128) (src dst : List Wire)
    (hs : src.length = 128) (hd : dst.length = 256) :
    let oldK := LowZero18LowK.kg K0 E0 src dst
    toffoliCount c.make + toffoliCount c.clear + 374 =
      toffoliCount (LowZero18Square.make K0 oldK) + toffoliCount (LowZero18Square.clear K0 oldK) ∧
    measurementCount c.make + measurementCount c.clear + 197 =
      measurementCount (LowZero18Square.make K0 oldK) + measurementCount (LowZero18Square.clear K0 oldK) := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  have wOld := LowZero18LowK.oregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wiOld := LowZero18LowK.iregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wjOld := LowZero18LowK.jregsH_W K0 hwK E0 src dst hs (by omega) hext.len
  have m8_R8 := c.R8.m8z_counts wR8; have c8_R8 := c.R8.c8z_counts wR8
  have m8_R := c.R.m8z_counts wR; have c8_R := c.R.c8z_counts wR
  have bR : c.R.bank.length = 128 := by simp [SplitCfg.R, v.bankLen, hn]
  have bOld : (LowZero18LowK.oregs K0 E0 src dst).bank.length = 128 := by
    simp [LowZero18LowK.oregs, (K0.measured_bank_widths hwK).1, hs]
  have hOldH : (LowZero18LowK.oregs K0 E0 src dst).h = 64 := rfl
  have biOld : (LowZero18LowK.iregs K0 E0 src dst).bank.length = 64 := by
    simp [LowZero18LowK.iregs, KRegs.lo, bOld, hOldH]
  have bjOld : (LowZero18LowK.jregsH K0 E0 src dst).bank.length = 64 := by
    simp [LowZero18LowK.jregsH, KRegs.hi, bOld, hOldH]
  have oldEq : LowZero18LowK.kg K0 E0 src dst = LowZero18LowK.kgH K0 E0 src dst := by simp [LowZero18LowK.kg, hs]
  have om := LowZero18KG.make_counts (LowZero18LowK.kgH K0 E0 src dst) wOld
  have oc := LowZero18KG.clear_counts (LowZero18LowK.kgH K0 E0 src dst) wOld
  have pm := LowZero18Square.patchKG_counts K0 (LowZero18LowK.kg K0 E0 src dst)
  let K :=
    { LowZero18LowK.kgH K0 E0 src dst with
      R := c.R, X1 := [], X2 := [], X5 := [],
      Q1 := LowZero18Diagonal.makeC c.Q1, Q1c := LowZero18Diagonal.clearC c.Q1,
      Q2 := LowZero18Diagonal.makeC c.Q2, Q2c := LowZero18Diagonal.clearC c.Q2,
      Q5 := LowZero18Diagonal.makeC c.Q5, Q5c := LowZero18Diagonal.clearC c.Q5,
      I1 := fun _ _ => True, I2 := fun _ _ => True, I5 := fun _ _ => True }
  have nm := LowZero18KG.make_counts K wR
  have nc := LowZero18KG.clear_counts K wR
  have m8z_eq : toffoliCount c.R8.m8z = toffoliCount c.R.m8z ∧ measurementCount c.R8.m8z = measurementCount c.R.m8z ∧
      toffoliCount c.R8.c8z = toffoliCount c.R.c8z ∧ measurementCount c.R8.c8z = measurementCount c.R.c8z := by
    have lR := c.R.m8z_lens wR; have lR8 := c.R8.m8z_lens wR8
    have hd8 : c.R8.dmid.length = c.R.dmid.length := by simp [KRegs.dmid, SplitCfg.R8, SplitCfg.R]
    have a1 := addInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have a2 := addInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have s1 := subInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have s2 := subInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have m8t : toffoliCount c.R8.m8 = toffoliCount c.R.m8 := by simp only [KRegs.m8, a1.1, a2.1]; rw [hd8]
    have m8m : measurementCount c.R8.m8 = measurementCount c.R.m8 := by simp only [KRegs.m8, a1.2, a2.2]; rw [hd8]
    have c8t : toffoliCount c.R8.c8 = toffoliCount c.R.c8 := by simp only [KRegs.c8, s1.1, s2.1]; rw [hd8]
    have c8m : measurementCount c.R8.c8 = measurementCount c.R.c8 := by simp only [KRegs.c8, s1.2, s2.2]; rw [hd8]
    exact ⟨by linarith only [m8_R8.1, m8_R.1, m8t], by linarith only [m8_R8.2, m8_R.2, m8m],
      by linarith only [c8_R8.1, c8_R.1, c8t], by linarith only [c8_R8.2, c8_R.2, c8m]⟩
  have hNewM : toffoliCount c.make = toffoliCount (LowZero18KG.make K) ∧
      measurementCount c.make = measurementCount (LowZero18KG.make K) := by
    simp only [SplitCfg.make, LowZero18KG.make, K, toffoliCount_append, measurementCount_append, m8z_eq.1, m8z_eq.2.1]
    exact ⟨by ring, by ring⟩
  have hNewC : toffoliCount c.clear = toffoliCount (LowZero18KG.clear K) ∧
      measurementCount c.clear = measurementCount (LowZero18KG.clear K) := by
    simp only [SplitCfg.clear, LowZero18KG.clear, K, toffoliCount_append, measurementCount_append, m8z_eq.2.2.1, m8z_eq.2.2.2]
    exact ⟨by ring, by ring⟩
  have c_eq32 (A B : KRegs) (wA : A.W) (wB : B.W) (hA : A.h = 32) (hB : B.h = 32)
      (bA : A.bank.length = 64) (bB : B.bank.length = 64) :
      DiagSq.cost A = DiagSq.cost B ∧ DiagSq.parR A = DiagSq.parR B := by
    have sA : A.S.length = 33 := by have := wA.S; omega
    have sB : B.S.length = 33 := by have := wB.S; omega
    have loA : A.lo.length = 32 := by simp [KRegs.lo, bA, hA]
    have loB : B.lo.length = 32 := by simp [KRegs.lo, bB, hB]
    have hiA : A.hi.length = 32 := by simp [KRegs.hi, bA, hA]
    have hiB : B.hi.length = 32 := by simp [KRegs.hi, bB, hB]
    exact ⟨by simp [DiagSq.cost, bA, bB, hA, hB], by simp [DiagSq.parR, loA, loB, hiA, hiB, sA, sB]⟩
  have eQ1 := c_eq32 c.Q1 (LowZero18LowK.iregs K0 E0 src dst) w1.1 wiOld rfl rfl
    (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]) biOld
  have eQ2 := c_eq32 c.Q2 (LowZero18LowK.jregsH K0 E0 src dst) w2.1 wjOld
    (by simp [SplitCfg.Q2, hn]) rfl (by simp [SplitCfg.Q2, hn, KRegs.hi, SplitCfg.R, v.bankLen]) bjOld
  have q1_m := makeC_counts c.Q1 w1.1 w1.2; have q1_c := RawClearSquare.clear_counts c.Q1 w1.1 w1.2
  have q1_d := diag32_counts c.Q1 w1.1 rfl (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn])
  have qi_m := makeC_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_c := RawClearSquare.clear_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_d := diag32_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld rfl biOld
  have hQ1 : toffoliCount K.Q1 + toffoliCount K.Q1c =
      toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q1 + toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q1c ∧
      measurementCount K.Q1 + measurementCount K.Q1c =
      measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q1 + measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q1c := by
    have b1 : c.Q1.bank.length = 64 := by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]
    have h1 : c.Q1.h = 32 := rfl
    have hi : (LowZero18LowK.iregs K0 E0 src dst).h = 32 := rfl
    have ⟨_, _, q1d3, q1d4⟩ := q1_d
    have ⟨_, _, qid3, qid4⟩ := qi_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q1) = toffoliCount (RawClearSquare.clear c.Q1) + 31 at q1d3
    change measurementCount (LowZero18Diagonal.clearC c.Q1) = measurementCount (RawClearSquare.clear c.Q1) + 32 at q1d4
    change toffoliCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      toffoliCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 31 at qid3
    change measurementCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      measurementCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 32 at qid4
    simp only [K, LowZero18LowK.kgH]
    rw [b1, h1] at q1_m; rw [h1] at q1_c; rw [biOld, hi] at qi_m; rw [hi] at qi_c
    exact ⟨by clear * - q1_m q1_c q1d3 qi_m qi_c qid3 eQ1; omega,
      by clear * - q1_m q1_c q1d4 qi_m qi_c qid4 eQ1; omega⟩
  have q2_m := LowZero18Diagonal.make_counts c.Q2 w2.1 w2.2.1; have q2_c := RawClearSquare.clear_counts c.Q2 w2.1 w2.2.1
  have q2_d := diag32_counts c.Q2 w2.1 (by simp [SplitCfg.Q2, hn]) (by simp [SplitCfg.Q2, hn, KRegs.hi, SplitCfg.R, v.bankLen])
  have qj_m := LowZero18Diagonal.make_counts (LowZero18LowK.jregsH K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have qj_c := RawClearSquare.clear_counts (LowZero18LowK.jregsH K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have hQ2 : toffoliCount K.Q2 + toffoliCount K.Q2c =
      toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q2 + toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q2c + 31 ∧
      measurementCount K.Q2 + measurementCount K.Q2c =
      measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q2 + measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q2c + 64 := by
    have h2 : c.Q2.h = 32 := by simp [SplitCfg.Q2, hn]
    have hj : (LowZero18LowK.jregsH K0 E0 src dst).h = 32 := rfl
    have ⟨q2d1, q2d2, q2d3, q2d4⟩ := q2_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q2) = toffoliCount (RawClearSquare.clear c.Q2) + 31 at q2d3
    change measurementCount (LowZero18Diagonal.clearC c.Q2) = measurementCount (RawClearSquare.clear c.Q2) + 32 at q2d4
    simp only [K, LowZero18LowK.kgH, LowZero18Diagonal.clear]
    rw [h2] at q2_c; rw [hj] at qj_c
    exact ⟨by clear * - q2_m q2_c q2d1 q2d3 qj_m qj_c eQ2; omega,
      by clear * - q2_m q2_c q2d2 q2d4 qj_m qj_c eQ2; omega⟩
  have q5_e := diag33_exact c.Q5 w5.1 w5.2.2 (by rw [w5.2.1, w5.2.2])
  have q5_old := tsq65_exact (LowZero18LowK.oregs K0 E0 src dst).S (LowZero18LowK.oregs K0 E0 src dst).T
    (LowZero18LowK.oregs K0 E0 src dst).pad (LowZero18LowK.oregs K0 E0 src dst).carry
    (LowZero18LowK.oregs K0 E0 src dst).cin
    (by have hOS := wOld.S; rw [bOld, hOldH] at hOS; omega)
    (by have hOT := wOld.T; have hOS := wOld.S; rw [bOld, hOldH] at hOS; omega)
    wOld.pad (by have := wOld.carry; omega)
  have hQ5 : toffoliCount K.Q5 + toffoliCount K.Q5c + 405 =
      toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q5 + toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q5c ∧
      measurementCount K.Q5 + measurementCount K.Q5c + 261 =
      measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q5 + measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q5c := by
    simp only [K, LowZero18LowK.kgH]
    exact ⟨by clear * - q5_e q5_old; omega, by clear * - q5_e q5_old; omega⟩
  have hOldT : toffoliCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.make (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.1, oldEq]
  have hOldM : measurementCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.make (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.2.1, oldEq]
  have hOldCT : toffoliCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.clear (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.2.2.1, oldEq]
  have hOldCM : measurementCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.clear (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.2.2.2, oldEq]
  dsimp only
  rw [hNewM.1, hNewM.2, hNewC.1, hNewC.2, hOldT, hOldM, hOldCT, hOldCM]
  have hKR : K.R = c.R := rfl
  have hOR : (LowZero18LowK.kgH K0 E0 src dst).R = LowZero18LowK.oregs K0 E0 src dst := rfl
  have ht1 : ¬c.R.trimOK := by simp only [KRegs.trimOK, bR, show c.R.h = 64 from rfl]; decide
  have ht2 : ¬(LowZero18LowK.oregs K0 E0 src dst).trimOK := by simp only [KRegs.trimOK, bOld, hOldH]; decide
  rw [hKR] at nm nc; simp only [ht1, if_false] at nm nc; rw [bR, show c.R.h = 64 from rfl] at nm nc
  rw [hOR] at om oc; simp only [ht2, if_false] at om oc; rw [bOld, hOldH] at om oc
  exact ⟨by clear * - nm nc om oc hQ1 hQ2 hQ5; omega,
    by clear * - nm nc om oc hQ1 hQ2 hQ5; omega⟩

theorem cfg_counts_S (c : SplitCfg) (v : CfgValid c) (hn : c.n = 129) (src dst : List Wire)
    (hs : src.length = 129) (hd : dst.length = 258) :
    let oldK := LowZero18LowK.kg K0 E0 src dst
    toffoliCount c.make + toffoliCount c.clear + 373 =
      toffoliCount (LowZero18Square.make K0 oldK) + toffoliCount (LowZero18Square.clear K0 oldK) ∧
    measurementCount c.make + measurementCount c.clear + 195 =
      measurementCount (LowZero18Square.make K0 oldK) + measurementCount (LowZero18Square.clear K0 oldK) := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  have wOld := LowZero18LowK.oregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wiOld := LowZero18LowK.iregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wjOld := LowZero18LowK.jregsS_W K0 hwK E0 src dst hs (by omega) hext.len
  have m8_R8 := c.R8.m8z_counts wR8; have c8_R8 := c.R8.c8z_counts wR8
  have m8_R := c.R.m8z_counts wR; have c8_R := c.R.c8z_counts wR
  have bR : c.R.bank.length = 129 := by simp [SplitCfg.R, v.bankLen, hn]
  have bOld : (LowZero18LowK.oregs K0 E0 src dst).bank.length = 129 := by
    simp [LowZero18LowK.oregs, (K0.measured_bank_widths hwK).1, hs]
  have hOldH : (LowZero18LowK.oregs K0 E0 src dst).h = 64 := rfl
  have biOld : (LowZero18LowK.iregs K0 E0 src dst).bank.length = 64 := by
    simp [LowZero18LowK.iregs, KRegs.lo, bOld, hOldH]
  have bjOld : (LowZero18LowK.jregsS K0 E0 src dst).bank.length = 66 := by
    have hOS := wOld.S; simp [LowZero18LowK.jregsS, hOS, bOld, hOldH]
  have oldEq : LowZero18LowK.kg K0 E0 src dst = LowZero18LowK.kgS K0 E0 src dst := by simp [LowZero18LowK.kg, hs]
  have om := LowZero18KG.make_counts (LowZero18LowK.kgS K0 E0 src dst) wOld
  have oc := LowZero18KG.clear_counts (LowZero18LowK.kgS K0 E0 src dst) wOld
  have pm := LowZero18Square.patchKG_counts K0 (LowZero18LowK.kg K0 E0 src dst)
  let K :=
    { LowZero18LowK.kgH K0 E0 src dst with
      R := c.R, X1 := [], X2 := [], X5 := [],
      Q1 := LowZero18Diagonal.makeC c.Q1, Q1c := LowZero18Diagonal.clearC c.Q1,
      Q2 := LowZero18Diagonal.makeC c.Q2, Q2c := LowZero18Diagonal.clearC c.Q2,
      Q5 := LowZero18Diagonal.makeC c.Q5, Q5c := LowZero18Diagonal.clearC c.Q5,
      I1 := fun _ _ => True, I2 := fun _ _ => True, I5 := fun _ _ => True }
  have nm := LowZero18KG.make_counts K wR
  have nc := LowZero18KG.clear_counts K wR
  have m8z_eq : toffoliCount c.R8.m8z = toffoliCount c.R.m8z ∧ measurementCount c.R8.m8z = measurementCount c.R.m8z ∧
      toffoliCount c.R8.c8z = toffoliCount c.R.c8z ∧ measurementCount c.R8.c8z = measurementCount c.R.c8z := by
    have lR := c.R.m8z_lens wR; have lR8 := c.R8.m8z_lens wR8
    have hd8 : c.R8.dmid.length = c.R.dmid.length := by simp [KRegs.dmid, SplitCfg.R8, SplitCfg.R]
    have a1 := addInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have a2 := addInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have s1 := subInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have s2 := subInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have m8t : toffoliCount c.R8.m8 = toffoliCount c.R.m8 := by simp only [KRegs.m8, a1.1, a2.1]; rw [hd8]
    have m8m : measurementCount c.R8.m8 = measurementCount c.R.m8 := by simp only [KRegs.m8, a1.2, a2.2]; rw [hd8]
    have c8t : toffoliCount c.R8.c8 = toffoliCount c.R.c8 := by simp only [KRegs.c8, s1.1, s2.1]; rw [hd8]
    have c8m : measurementCount c.R8.c8 = measurementCount c.R.c8 := by simp only [KRegs.c8, s1.2, s2.2]; rw [hd8]
    exact ⟨by linarith only [m8_R8.1, m8_R.1, m8t], by linarith only [m8_R8.2, m8_R.2, m8m],
      by linarith only [c8_R8.1, c8_R.1, c8t], by linarith only [c8_R8.2, c8_R.2, c8m]⟩
  have hNewM : toffoliCount c.make = toffoliCount (LowZero18KG.make K) ∧
      measurementCount c.make = measurementCount (LowZero18KG.make K) := by
    simp only [SplitCfg.make, LowZero18KG.make, K, toffoliCount_append, measurementCount_append, m8z_eq.1, m8z_eq.2.1]
    exact ⟨by ring, by ring⟩
  have hNewC : toffoliCount c.clear = toffoliCount (LowZero18KG.clear K) ∧
      measurementCount c.clear = measurementCount (LowZero18KG.clear K) := by
    simp only [SplitCfg.clear, LowZero18KG.clear, K, toffoliCount_append, measurementCount_append, m8z_eq.2.2.1, m8z_eq.2.2.2]
    exact ⟨by ring, by ring⟩
  have hne : c.n ≠ 128 := by omega
  have c_eq (A B : KRegs) (wA : A.W) (wB : B.W) (h : Nat) (hA : A.h = h) (hB : B.h = h)
      (bA : A.bank.length = 2 * h) (bB : B.bank.length = 2 * h) :
      DiagSq.cost A = DiagSq.cost B ∧ DiagSq.parR A = DiagSq.parR B := by
    have sA : A.S.length = h + 1 := by have := wA.S; omega
    have sB : B.S.length = h + 1 := by have := wB.S; omega
    have loA : A.lo.length = h := by simp [KRegs.lo, bA, hA]; omega
    have loB : B.lo.length = h := by simp [KRegs.lo, bB, hB]; omega
    have hiA : A.hi.length = h := by simp [KRegs.hi, bA, hA]; omega
    have hiB : B.hi.length = h := by simp [KRegs.hi, bB, hB]; omega
    exact ⟨by simp [DiagSq.cost, bA, bB, hA, hB], by simp [DiagSq.parR, loA, loB, hiA, hiB, sA, sB]⟩
  have eQ1 := c_eq c.Q1 (LowZero18LowK.iregs K0 E0 src dst) w1.1 wiOld 32 rfl rfl
    (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]) biOld
  have eQ5 := c_eq c.Q5 (LowZero18LowK.jregsS K0 E0 src dst) w5.1 wjOld 33 w5.2.2 rfl
    (by rw [w5.2.1, w5.2.2]) bjOld
  have q1_m := makeC_counts c.Q1 w1.1 w1.2; have q1_c := RawClearSquare.clear_counts c.Q1 w1.1 w1.2
  have q1_d := diag32_counts c.Q1 w1.1 rfl (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn])
  have qi_m := makeC_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_c := RawClearSquare.clear_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_d := diag32_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld rfl biOld
  have hQ1 : toffoliCount K.Q1 + toffoliCount K.Q1c =
      toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q1 + toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q1c ∧
      measurementCount K.Q1 + measurementCount K.Q1c =
      measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q1 + measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q1c := by
    have b1 : c.Q1.bank.length = 64 := by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]
    have h1 : c.Q1.h = 32 := rfl
    have hi : (LowZero18LowK.iregs K0 E0 src dst).h = 32 := rfl
    have ⟨_, _, q1d3, q1d4⟩ := q1_d
    have ⟨_, _, qid3, qid4⟩ := qi_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q1) = toffoliCount (RawClearSquare.clear c.Q1) + 31 at q1d3
    change measurementCount (LowZero18Diagonal.clearC c.Q1) = measurementCount (RawClearSquare.clear c.Q1) + 32 at q1d4
    change toffoliCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      toffoliCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 31 at qid3
    change measurementCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      measurementCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 32 at qid4
    simp only [K, LowZero18LowK.kgS]
    rw [b1, h1] at q1_m; rw [h1] at q1_c; rw [biOld, hi] at qi_m; rw [hi] at qi_c
    exact ⟨by clear * - q1_m q1_c q1d3 qi_m qi_c qid3 eQ1; omega,
      by clear * - q1_m q1_c q1d4 qi_m qi_c qid4 eQ1; omega⟩
  have q2_e := diag33_exact c.Q2 w2.1 (by simp [SplitCfg.Q2, hne]) (by simp [SplitCfg.Q2, hne, KRegs.hi, SplitCfg.R, v.bankLen, hn])
  have q2_old := tsq65_exact (LowZero18LowK.oregs K0 E0 src dst).hi (LowZero18LowK.oregs K0 E0 src dst).dhi
    (LowZero18LowK.oregs K0 E0 src dst).pad (LowZero18LowK.oregs K0 E0 src dst).carry
    (LowZero18LowK.oregs K0 E0 src dst).cin
    (by simp [KRegs.hi, bOld, hOldH]) (by simp [KRegs.dhi, LowZero18LowK.oregs, hd, hOldH]) wOld.pad (by have := wOld.carry; omega)
  have hQ2 : toffoliCount K.Q2 + toffoliCount K.Q2c + 405 =
      toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q2 + toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q2c ∧
      measurementCount K.Q2 + measurementCount K.Q2c + 261 =
      measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q2 + measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q2c := by
    simp only [K, LowZero18LowK.kgS]
    exact ⟨by clear * - q2_e q2_old; omega, by clear * - q2_e q2_old; omega⟩
  have q5_m := LowZero18Diagonal.make_counts c.Q5 w5.1 w5.2.1; have q5_c := RawClearSquare.clear_counts c.Q5 w5.1 w5.2.1
  have q5_d := diag33_counts c.Q5 w5.1 w5.2.2 (by rw [w5.2.1, w5.2.2])
  have qj_m := LowZero18Diagonal.make_counts (LowZero18LowK.jregsS K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have qj_c := RawClearSquare.clear_counts (LowZero18LowK.jregsS K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have hQ5 : toffoliCount K.Q5 + toffoliCount K.Q5c =
      toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q5 + toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q5c + 32 ∧
      measurementCount K.Q5 + measurementCount K.Q5c =
      measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q5 + measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q5c + 66 := by
    have h5 : c.Q5.h = 33 := w5.2.2
    have hj : (LowZero18LowK.jregsS K0 E0 src dst).h = 33 := rfl
    have ⟨q5d1, q5d2, q5d3, q5d4⟩ := q5_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q5) = toffoliCount (RawClearSquare.clear c.Q5) + 32 at q5d3
    change measurementCount (LowZero18Diagonal.clearC c.Q5) = measurementCount (RawClearSquare.clear c.Q5) + 33 at q5d4
    simp only [K, LowZero18LowK.kgS, LowZero18Diagonal.clear]
    rw [h5] at q5_c; rw [hj] at qj_c
    exact ⟨by clear * - q5_m q5_c q5d1 q5d3 qj_m qj_c eQ5; omega,
      by clear * - q5_m q5_c q5d2 q5d4 qj_m qj_c eQ5; omega⟩
  have hOldT : toffoliCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.make (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.1, oldEq]
  have hOldM : measurementCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.make (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.2.1, oldEq]
  have hOldCT : toffoliCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.clear (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.2.2.1, oldEq]
  have hOldCM : measurementCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.clear (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.2.2.2, oldEq]
  dsimp only
  rw [hNewM.1, hNewM.2, hNewC.1, hNewC.2, hOldT, hOldM, hOldCT, hOldCM]
  have hKR : K.R = c.R := rfl
  have hOR : (LowZero18LowK.kgS K0 E0 src dst).R = LowZero18LowK.oregs K0 E0 src dst := rfl
  have ht1 : c.R.trimOK := by simp only [KRegs.trimOK, bR, show c.R.h = 64 from rfl]; decide
  have ht2 : (LowZero18LowK.oregs K0 E0 src dst).trimOK := by simp only [KRegs.trimOK, bOld, hOldH]; decide
  rw [hKR] at nm nc; simp only [ht1, if_true] at nm nc; rw [bR, show c.R.h = 64 from rfl] at nm nc
  rw [hOR] at om oc; simp only [ht2, if_true] at om oc; rw [bOld, hOldH] at om oc
  exact ⟨by clear * - nm nc om oc hQ1 hQ2 hQ5; omega,
    by clear * - nm nc om oc hQ1 hQ2 hQ5; omega⟩

end SplitCore

/-! ### Slot bounds for the concrete split Karatsuba kernels -/

section SplitSlots
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

private theorem addInPlace_slots_eq : ∀ (x y cs : List Wire) (c : Wire),
    x.length = y.length → x.length - 1 ≤ cs.length → 1 ≤ x.length →
    Challenge.gateSlots (addInPlace x y cs c) = 12 * x.length - 10
  | [a], [b], _, c, _, _, _ => by
      simp [addInPlace, Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots]
  | a :: a' :: as, b :: b' :: bs, d :: ds, c, hxy, hcs, _ => by
      simp only [List.length_cons] at hxy hcs
      have ih := addInPlace_slots_eq (a' :: as) (b' :: bs) ds d
        (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega) (by simp)
      simp only [addInPlace, Challenge.gateSlots_append, Baselines.majority_gateSlots,
        Baselines.eraseCarry_gateSlots, Baselines.gateSlots_cons, Baselines.gateSlots_nil,
        Challenge.instructionSlots, List.length_cons] at ih ⊢
      omega
  | [], _, _, _, _, _, hx => by simp at hx
  | [_], [], _, _, hxy, _, _ => by simp at hxy
  | [_], _ :: _ :: _, _, _, hxy, _, _ => by simp at hxy
  | _ :: _ :: _, [], _, _, hxy, _, _ => by simp at hxy
  | _ :: _ :: _, [_], _, _, hxy, _, _ => by simp at hxy
  | _ :: _ :: _, _ :: _ :: _, [], _, _, hcs, _ => by simp at hcs

private theorem m8z_slots_eq (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.m8z = 12 * (R.dmid.length - 1) - 9 := by
  have l := R.m8z_lens w
  have h1 := l.1; have h2 := l.2.1; have h3 := l.2.2
  have ha := addInPlace_slots_eq (R.T ++ R.zM).tail R.dmid.tail (R.carry.take (R.dmid.length - 1)).tail R.cin
    (by simp only [List.length_tail, h1])
    (by simp only [List.length_tail, h1]; omega)
    (by simp only [List.length_tail, h1]; omega)
  simp only [KRegs.m8z, LowZero.addLow0, Challenge.gateSlots_append, ha, List.length_tail, h1,
    Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots, List.length_nil]
  omega

private theorem c8z_slots_eq (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.c8z = 2 * R.dmid.length + 12 * (R.dmid.length - 1) - 7 := by
  have l := R.m8z_lens w
  have h1 := l.1; have h2 := l.2.1; have h3 := l.2.2
  have ha := addInPlace_slots_eq (R.T ++ R.zM).tail R.dmid.tail (R.carry.take (R.dmid.length - 1)).tail R.cin
    (by simp only [List.length_tail, h1])
    (by simp only [List.length_tail, h1]; omega)
    (by simp only [List.length_tail, h1]; omega)
  simp only [KRegs.c8z, LowZero.subLowNC, LowZero.addLowNC, Challenge.gateSlots_append, ha,
    Baselines.notRegister_gateSlots, List.length_tail, h1,
    Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots, List.length_nil]
  omega

private theorem diagC_slots_bound (R : KRegs) (w : R.W) (he : R.bank.length = 2 * R.h) (hh : R.h ≤ 33) :
    Challenge.gateSlots (LowZero18Diagonal.makeC R) + Challenge.gateSlots (LowZero18Diagonal.clearC R) ≤ 601600 := by
  have dt := LowZero18Diagonal.tiny_slots R w he hh
  have ot := R.tiny_slots w hh (by omega) (by omega)
  have ms := R.make_sub_slots w
  have sc := R.scl1591_slots
  have sk := R.smkT_slots
  simp only [LowZero18Diagonal.makeC, LowZero18Diagonal.clearC, RawClearSquare.clearC, LowZero18Diagonal.clear,
    Challenge.gateSlots_append] at dt ⊢
  clear * - dt ot ms sc sk; omega

theorem cfg_slots_bound (c : SplitCfg) (v : CfgValid c) :
    Challenge.gateSlots c.make + Challenge.gateSlots c.clear ≤ 1830000 := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  have q1 := diagC_slots_bound c.Q1 w1.1 w1.2 (by change 32 ≤ 33; decide)
  have q2 := diagC_slots_bound c.Q2 w2.1 w2.2.1 (by rcases w2.2.2 with h | h <;> omega)
  have q5 := diagC_slots_bound c.Q5 w5.1 w5.2.1 (by omega)
  have m8 := m8z_slots_eq c.R wR; have m8' := m8z_slots_eq c.R8 wR8
  have c8 := c8z_slots_eq c.R wR; have c8' := c8z_slots_eq c.R8 wR8
  have hd8 : c.R8.dmid.length = c.R.dmid.length := by simp [KRegs.dmid, SplitCfg.R8, SplitCfg.R]
  have ad := c.R.adder_slots wR rfl (by simp only [SplitCfg.R, v.bankLen]; rcases v.hn with h | h <;> omega)
  let K :=
    { LowZero18LowK.kgH K0 E0 c.src c.dst with
      R := c.R, X1 := [], X2 := [], X5 := [],
      Q1 := LowZero18Diagonal.makeC c.Q1, Q1c := LowZero18Diagonal.clearC c.Q1,
      Q2 := LowZero18Diagonal.makeC c.Q2, Q2c := LowZero18Diagonal.clearC c.Q2,
      Q5 := LowZero18Diagonal.makeC c.Q5, Q5c := LowZero18Diagonal.clearC c.Q5,
      I1 := fun _ _ => True, I2 := fun _ _ => True, I5 := fun _ _ => True }
  have st := LowZero18KG.steps_slots2 K wR
  have hM : Challenge.gateSlots c.make = Challenge.gateSlots (LowZero18KG.make K) := by
    simp only [SplitCfg.make, LowZero18KG.make, K, Challenge.gateSlots_append, m8, m8', hd8]; ring
  have hC : Challenge.gateSlots c.clear = Challenge.gateSlots (LowZero18KG.clear K) := by
    simp only [SplitCfg.clear, LowZero18KG.clear, K, Challenge.gateSlots_append, c8, c8', hd8]; ring
  rw [hM, hC]
  dsimp only [K] at st ⊢
  clear * - q1 q2 q5 ad st; omega

end SplitSlots

/-! ## Direct-fold renaming helper (moves `workT` onto `K0.core.pad.take workT.length`) -/

section FoldMove
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq

private theorem directFold_rename_run (pairs : List (Wire × Wire)) (f : MeasuredSquareFold)
    (hcnt : ∀ q, f.src.count q ≤ K0.core.product.count q)
    (hlen : f.src.length = 256) (hcan : f.canonical = true) (hsh : f.shift = 0)
    (hholes : ∀ ab ∈ pairs, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out)
    (hhosts : ∀ ab ∈ pairs, ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out)
    (base : BasisState) (hv : K0.MeasuredFoldView base f) (hc : K0.PairClean base)
    (O : Nat) (hO : O < SquareReduction.p) (s : State) (m : List Bool)
    (hf : SquareFrame K0.core.out base O s.basis) :
    run (hostRename pairs (directFoldQTq K0 f)) m s = run (directFoldQTq K0 f) m s := by
  have hn := (List.nodup_cons.mp controlND).2
  have cleanIn := K0.squareFrame_clean hn base s.basis O hf hc
  have frame := directFoldQ_frameTq K0 hwK hn base f hv hcan hc hlen hsh O hO s m hf
  have cleanOut := K0.squareFrame_clean hn base (run (directFoldQTq K0 f) m s).basis
    ((measuredFoldPayload base f + (SquareReduction.p - 1 - O)) % SquareReduction.p) frame.2 hc
  apply hostRename_run_eq pairs (directFoldQTq K0 f) s m
  · intro ab hab; exact (regValue_zero _ _).mp cleanIn.work ab.1 (hholes ab hab).1
  · intro ab hab; exact (regValue_zero _ _).mp cleanIn.pad ab.2 (List.mem_append_left _ (hhosts ab hab).1)
  · intro ab hab; exact (regValue_zero _ _).mp cleanOut.work ab.1 (hholes ab hab).1
  · intro ab hab
    exact directFoldQ_free K0 hn f hcnt ab.2 (by simp [directFree, (hhosts ab hab).1])

private theorem directFold_rename_support (pairs : List (Wire × Wire)) (f : MeasuredSquareFold)
    (hcnt : ∀ q, f.src.count q ≤ K0.core.product.count q)
    (hnd : (holesOf pairs ++ hostsOf pairs).Nodup)
    (hhosts : ∀ ab ∈ pairs, ab.2 ∈ K0.core.pad) :
    wires (hostRename pairs (directFoldQTq K0 f)) ⊆
      (wires (directFoldQTq K0 f) \ (holesOf pairs).toFinset) ∪ (hostsOf pairs).toFinset := by
  have hn := (List.nodup_cons.mp controlND).2
  exact hostRename_support pairs (directFoldQTq K0 f) hnd (fun ab hab =>
    directFoldQ_free K0 hn f hcnt ab.2 (by simp [directFree, hhosts ab hab]))

end FoldMove

/-! ## Branch A body (`keepA` = 33 carries, avoids `workTA` and `hs`) -/

section BodyA
open ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq

private theorem la_eq_K0 : ReorderedAFixed.L = K0 := rfl

def keepA : List Wire := A109Research.keepK.filter (fun q => !workTA.contains q)

theorem keepA_geometry : keepA.Nodup ∧ keepA.length = 33 ∧
    (∀ q ∈ keepA, q ∈ A109Research.hosts) ∧
    (∀ q ∈ workTA, q ∉ keepA) ∧
    (∀ i, i < 44 → ReorderedAFixed.hs.getD i 0 ∉ keepA) ∧
    (∀ q ∈ keepA, q ∈ allowedWires) := by
  have hall : ∀ q ∈ keepA, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [keepA, keepKA_fast, workTA_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [keepA, keepKA_fast, workTA_lit, hs_lit]; decide +kernel))
  have hr : keepA.Nodup ∧ keepA.length = 33 ∧
      (∀ q ∈ keepA, q ∈ A109Research.hosts) ∧
      (∀ q ∈ workTA, q ∉ keepA) ∧
      (∀ i, i < 44 → ReorderedAFixed.hs.getD i 0 ∉ keepA) := by
    rw [keepA, keepKA_fast, hostsA109_fast, hsA_fast, workTA_lit]; decide +kernel
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, hall⟩

def rawFA : Program := ReorderedGenericCache.cachedAdd 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
def newFA : Program := A109Research.head ++ A109LowEraseResearch.clear ++ rawFA ++ A109Research.top
def newIA : Program := A109Research.preInv ++ ReorderedConsumedSub.consumed 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
def coreA : Program := (newFA ++ A109Research.M ++ newIA) ++ (A109LowEraseResearch.clear ++ A109Research.tail)
def restA : Program := A109LowEraseResearch.clear ++ rawFA ++ A109Research.top ++ A109Research.M ++ newIA ++ A109LowEraseResearch.clear ++ A109Research.tail
def loopPCA : Program := SignAHead.head ++ restA
def loopA : Program := hostRename (StairSqLoopA.pairs hs) loopPCA
def foldPairsA : List (Wire × Wire) := workTA.zip (K0.core.pad.take 32)
def dF1A : Program := hostRename foldPairsA (directFoldQTq K0 (negP K0))
def dF2A : Program := hostRename foldPairsA (directFoldQTq K0 (rot128F K0))
def bodyA : Program := (dF1A ++ (dF2A ++ loopA)) ++ ReorderedRecordPadding.program 7 K0.core.cin
def bodyAPlain : Program := A109SignResearch.directBody loopA

theorem foldPairsA_geom :
    (holesOf foldPairsA ++ hostsOf foldPairsA).Nodup ∧
    holesOf foldPairsA = workTA ∧
    hostsOf foldPairsA = K0.core.pad.take 32 ∧
    (∀ ab ∈ foldPairsA, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out ∧ ab.2 ∈ allowedWires) ∧
    (∀ q ∈ hostsOf foldPairsA, q ∉ hs ∧ q ≠ ControlLoan1589BFFold.eU K0 ∧ q ∈ K0.wires ∧ q ∈ allowedWires) := by
  have hall : ∀ q ∈ hostsOf foldPairsA, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsA, workTA_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [foldPairsA, workTA_lit, K0_eq, hs_lit]; decide +kernel))
  have hK : ∀ q ∈ hostsOf foldPairsA, q ∈ K0.wires :=
    StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsA, workTA_lit, K0_eq]; decide +kernel)
  have hr : (holesOf foldPairsA ++ hostsOf foldPairsA).Nodup ∧
      holesOf foldPairsA = workTA ∧
      hostsOf foldPairsA = K0.core.pad.take 32 ∧
      (∀ ab ∈ foldPairsA, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out) ∧
      (∀ q ∈ hostsOf foldPairsA, q ∉ hs ∧ q ≠ ControlLoan1589BFFold.eU K0) := by
    rw [foldPairsA, workTA_lit, K0_eq, hs_lit]; decide +kernel
  refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_, ?_⟩
  · intro ab hab; have h := hr.2.2.2.1 ab hab
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hall ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩)⟩
  · intro q hq; have h := hr.2.2.2.2 q hq
    exact ⟨h.1, h.2, hK q hq, hall q hq⟩

private theorem keepA_sub (q : Wire) (hq : q ∈ keepA) : q ∈ A109Research.hosts := keepA_geometry.2.2.1 q hq

private theorem core_plainA (s : State) (m : List Bool)
    (hz : ∀ q ∈ ReorderedBPrefixResearch.pad, s.basis q = false) (hb : ∀ q ∈ ReorderedBPrefixResearch.bank, s.basis q = false)
    (hi : s.basis ReorderedBPrefixResearch.cin = false) (ha : regValue ReorderedBPrefixResearch.acc s.basis = 0)
    (zero : ∀ q ∈ ReorderedAFixed.hosts, s.basis q = false)
    (after : WReady ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src
      (regValue ReorderedBPrefixResearch.src s.basis) (middleState A109Research.oldF A109Research.oldM s m))
    (flag : (run A109Research.oldF (m.take (measurementCount A109Research.oldF)) s).basis 4762 = false) :
    run coreA m s = run (A109Research.oldF ++ A109Research.oldM ++
      ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) m s := by
  let H := regValue ReorderedBPrefixResearch.src s.basis
  let vs := ReorderedCacheBits.values 4 33 H (976 * H / 1024)
  have keepSubK (q : Wire) (hq : q ∈ keepA) : q ∈ A109Research.keepK := (List.mem_filter.mp hq).1
  have fwdM : measurementCount newFA = measurementCount A109Research.F := by
    have h := (ReorderedGenericCache.count_balance 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide)).2.1
    simp only [newFA, rawFA, A109Research.F, A109Research.rawF, measurementCount_append]; rw [h]
  have invM : measurementCount newIA = measurementCount A109Research.I := by
    have h := ReorderedConsumedSub.measurement_eq 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide)
    simp only [newIA, A109Research.I, A109Research.rawI, measurementCount_append]; rw [h]
  have fwdVal : (((A109Research.cs.drop 4).take 33).map (run (carryPrefix (4 + 33) A109Research.xs A109Research.ys A109Research.cs ReorderedBPrefixResearch.cin) []
      (run (A109Research.head ++ A109LowEraseResearch.clear)
        ((m.take (measurementCount A109Research.F)).take (measurementCount (A109Research.head ++ A109LowEraseResearch.clear))) s)).basis) = vs := by
    let m0 := (m.take (measurementCount A109Research.F)).take (measurementCount (A109Research.head ++ A109LowEraseResearch.clear))
    let u := run A109Research.head m0 s
    let t := run (A109Research.head ++ A109LowEraseResearch.clear) m0 s
    have te : t = A109LowEraseResearch.erase u := A109Research.prefix_erased s m0 hz hb hi ha
    have hH : H < 2 ^ 128 := by simpa only [H, ReorderedBPrefixResearch.source_length] using regValue_lt ReorderedBPrefixResearch.src s.basis
    have ready := ReorderedHeadArithmeticResearch.ready ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank
      ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.source_length ReorderedBPrefixResearch.fits s m0 hz hb hi ha
    have eb (q : Wire) (hq : q ∈ A109Research.domain) : t.basis q = u.basis q := by
      rw [te]; exact A109LowEraseResearch.bit_same _ q (A109Research.domain_away_low q hq)
    have er (r : List Wire) (sub : ∀ q ∈ r, q ∈ A109Research.domain) : regValue r t.basis = regValue r u.basis :=
      regValue_congr _ _ _ (fun q hq => eb q (sub q hq))
    exact ReorderedCacheBits.forward_values 4 33 H (((2 ^ 138 - 48 * H) % 2 ^ 138) / 1024) (976 * H / 1024)
      A109Research.xs A109Research.ys A109Research.cs ReorderedBPrefixResearch.cin t
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide) A109Research.raw_nd
      (fun q hq => (eb q (A109Research.c_in q hq)).trans (ready.1 q hq))
      ((eb _ A109Research.cin_in).trans ready.2.1)
      ((er _ A109Research.x_in).trans ready.2.2.1)
      ((er _ A109Research.y_in).trans ready.2.2.2)
      (fun j hj => by simpa only [show 128 + 10 = 138 by decide] using ReorderedCacheArithmetic.high_add_low 128 (4 + j + 1) H (by omega) hH)
  have forward : run newFA (m.take (measurementCount A109Research.F)) s =
      scatterState keepA vs (run A109Research.F (m.take (measurementCount A109Research.F)) s) := by
    have h := CacheBetweenFrameResearch.forward (A109Research.head ++ A109LowEraseResearch.clear) A109Research.top
      33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide) keepA_geometry.1
      (fun q hq bad => A109Research.geometry.2.2 q (keepA_sub q hq) (by clear * - bad; simp only [A109Research.domain, List.mem_cons, List.mem_append] at bad ⊢; tauto))
      (fun q hq => A109Research.rawF_off q (keepA_sub q hq)) (fun q hq => A109Research.top_off q (keepA_sub q hq))
      s (m.take (measurementCount A109Research.F))
      (fun q hq => A109Research.prefix_zeroK s _ hz hb hi ha zero q (keepSubK q hq))
    rw [fwdVal] at h; exact h
  have mid := A109Research.middle_erased s m hz hb hi ha after flag
  have cacheEq : run (newFA ++ A109Research.M ++ newIA) m s = run (A109Research.F ++ A109Research.M ++ A109Research.I) m s := by
    apply CacheFromCleanForwardResearch.equivalent A109Research.F newFA A109Research.M A109Research.I newIA keepA vs
      fwdM (fun q hq => A109Research.middle_fresh q (keepA_sub q hq))
      (fun q hq => A109Research.I_off q (keepA_sub q hq)) keepA_geometry.1 s m
      (fun q hq => A109Research.forward_zeroK s _ hz hb hi ha zero q (keepSubK q hq)) forward
    rw [mid]
    let ms := middleState A109Research.oldF A109Research.oldM s m
    let mr := m.drop (measurementCount A109Research.F + measurementCount A109Research.M)
    let t := scatterState keepA vs (A109LowEraseResearch.erase ms)
    have comm : run A109Research.preInv mr t = scatterState keepA vs (A109LowEraseResearch.erase (run A109Research.preInv mr ms)) := by
      rw [show t = scatterState keepA vs (A109LowEraseResearch.erase ms) from rfl,
        run_scatter A109Research.preInv keepA vs _ _ (fun q hq => A109Research.preInv_off q (keepA_sub q hq)),
        A109LowEraseResearch.commute A109Research.preInv mr ms (fun q hq => A109Research.preInv_off q (A109Research.low_hosts q hq))]
    have bits (q : Wire) (hq : q ∈ A109Research.domain) : (run A109Research.preInv mr t).basis q = (run A109Research.preInv mr ms).basis q := by
      rw [comm, scatter_outside keepA vs _ q (fun bad => A109Research.geometry.2.2 q (keepA_sub q bad) hq)]
      exact A109LowEraseResearch.bit_same _ q (A109Research.domain_away_low q hq)
    have regs (r : List Wire) (sub : ∀ q ∈ r, q ∈ A109Research.domain) :
        regValue r (run A109Research.preInv mr t).basis = regValue r (run A109Research.preInv mr ms).basis :=
      regValue_congr _ _ _ (fun q hq => bits q (sub q hq))
    have rr := A109Research.pre_raw_ready H ms mr after
    have saved : keepA.map t.basis = vs := scatter_saved_map keepA vs _ keepA_geometry.1
      (by simp only [vs, ReorderedCacheBits.values, List.length_map, keepA_geometry.2.1, List.length_range])
    have same : keepA.map (run A109Research.preInv mr t).basis = keepA.map t.basis :=
      List.map_congr_left (fun q hq => run_preserves_outside A109Research.preInv mr t q (A109Research.preInv_off q (keepA_sub q hq)))
    simp only [newIA, A109Research.I, A109Research.rawI, ControlledBorrowResearch.run_cat]
    exact ReorderedConsumedSub.frame 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide)
      (by rw [A109Research.raw_lengths.1, A109Research.raw_lengths.2.1])
      (by rw [A109Research.raw_lengths.2.1, A109Research.raw_lengths.2.2])
      A109Research.raw_nd keepA_geometry.1 keepA_geometry.2.1 (fun q hq => A109Research.geometry.2.2 q (keepA_sub q hq))
      (run A109Research.preInv mr t) _ (fun q hq => (bits q (A109Research.c_in q hq)).trans (rr.1 q hq))
      ((bits _ A109Research.cin_in).trans rr.2.1) H (976 * H / 1024)
      ((regs _ A109Research.x_in).trans rr.2.2.1) ((regs _ A109Research.y_in).trans rr.2.2.2) (same.trans saved)
  have eq := ClearContextResearch.append_at (newFA ++ A109Research.M ++ newIA)
    (A109Research.F ++ A109Research.M ++ A109Research.I) (A109LowEraseResearch.clear ++ A109Research.tail) s m
    (by simp only [measurementCount_append, fwdM, invM]) cacheEq
  have shape : (A109Research.F ++ A109Research.M ++ A109Research.I) ++ (A109LowEraseResearch.clear ++ A109Research.tail) =
      A109Research.F ++ A109Research.M ++ (A109Research.I ++ A109LowEraseResearch.clear ++ A109Research.tail) := by
    have g (A B C D E : Program) : (A ++ B ++ C) ++ (D ++ E) = A ++ B ++ (C ++ D ++ E) := by simp only [List.append_assoc]
    exact g _ _ _ _ _
  exact eq.trans ((congrArg (fun P => run P m s) shape).trans (A109Research.plain_loop s m hz hb hi ha after flag))

private theorem coreA_frame (base : BasisState) (hc : ReorderedAFixed.L.PairClean base)
    (hsum : base A161Low4FixedFold.q = false) (hV : base A161Low4FixedFold.r = false)
    (hP : base A161Low4FixedFold.p = false) (hd : base ReorderedAFixed.d = false)
    (O : Nat) (hO : O < SquareReduction.p) :
    Triple (SquareFrame ReorderedAFixed.L.core.out base O) coreA
      (SquareFrame ReorderedAFixed.L.core.out base
        (((if base ReorderedAFixed.g then A161Low4Facts.Klow - 4294968272 * regValue ReorderedAFixed.src base
           else 4294968272 * regValue ReorderedAFixed.src base) + (SquareReduction.p - 1 - O)) % SquareReduction.p)) := by
  intro s m hf
  have clean := ReorderedAFixed.L.squareFrame_clean ReorderedAFixed.hn base s.basis O hf hc
  have hzFull : ∀ u ∈ accZ ReorderedAFixed.L, s.basis u = false := by
    intro u hu; rcases accZ_mem ReorderedAFixed.L u hu with hu | hu
    · exact (regValue_zero _ _).mp clean.pad u hu
    · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
  have hz : ∀ u ∈ ReorderedAFixed.pad, s.basis u = false := fun u hu => hzFull u ((FullPadDevelop.pad_sublist ReorderedAFixed.L).subset hu)
  have hb : ∀ u ∈ ReorderedAFixed.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
  have ha : regValue ReorderedAFixed.acc s.basis = 0 := A161Low4Ghost.ghostAcc_zero ReorderedAFixed.L s.basis clean
  have zeroU : ∀ u ∈ ReorderedAFixed.hs, s.basis u = false := fun u hu =>
    (hf.2 u (A161Low4FixedFold.hostClean base hc hd u hu).1).trans (A161Low4FixedFold.hostClean base hc hd u hu).2
  have zeroOld : ∀ u ∈ ReorderedAFixed.hosts, s.basis u = false := by
    have qz : s.basis ReorderedAFixed.q = false := (hf.2 ReorderedAFixed.q (by decide)).trans hsum
    have rz : s.basis ReorderedAFixed.r = false := (hf.2 ReorderedAFixed.r (by decide)).trans hV
    have pz : s.basis ReorderedAFixed.p = false := (hf.2 ReorderedAFixed.p (by decide)).trans hP
    change ∀ u ∈ ReorderedAFixed.q :: ReorderedAFixed.r :: ReorderedAFixed.p :: ReorderedAFixed.hs, s.basis u = false
    rw [List.forall_mem_cons, List.forall_mem_cons, List.forall_mem_cons]
    exact ⟨qz, rz, pz, zeroU⟩
  have offHs : ∀ u ∈ ReorderedAFixed.hs, u ∉ wires (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) :=
    fun u hu => (ReorderedAFixed.off_plain u (StairSqLoopA.hosts_of_hs u hu)).1
  have goodOriginal : WReady ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
      (regValue ReorderedAFixed.src s.basis)
      (middleState (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
        (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g) s m) := by
    rw [ReorderedARetape.a_middle_eq ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
      (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g) ReorderedAFixed.lengths.1 ReorderedAFixed.lengths.2.2.2 ReorderedAFixed.fits s m hz hb clean.cin ha]
    exact ReorderedAFixed.good_old base hc O hO s _ hf
  have middleEq := A161Low4FixedFold.cert100.middle_eq ReorderedAFixed.hs (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g)
    A161Low4FixedFold.checked.out (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) s m zeroU offHs
  have knownEq := AKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
  have goodKnown : WReady ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
      (regValue ReorderedAFixed.src s.basis)
      (middleState (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) KnownAMidStaged.body s m) := by
    rw [knownEq, middleEq]; exact goodOriginal
  have buildFrame := ReorderedAPlain.build_triple ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
    ReorderedAFixed.lengths.1 ReorderedAFixed.lengths.2.2.2 ReorderedAFixed.fits s.basis hz hb clean.cin s
    (m.take (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src))) ⟨ha, fun _ _ => rfl⟩
  have flag : (run (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
      (m.take (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src))) s).basis 4762 = false :=
    (buildFrame.2.2 4762 (by decide +kernel)).trans clean.modFlag
  have plainNew := core_plainA s m hz hb clean.cin ha zeroOld goodKnown flag
  have midEq : run KnownAMidStaged.body (m.drop (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)))
      (run (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) m s) =
      run A161Low4FixedFold.checked.out (m.drop (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)))
      (run (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) m s) := by
    simpa only [middleState, run_take] using knownEq
  have ctxt := ReorderedKnownA.context_eq (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
    A161Low4FixedFold.checked.out KnownAMidStaged.body (ReorderedAPlain.unbuild ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
    s m AKnownMiddleResearch.measurements midEq
  have middleReplace := A161Low4FixedFold.cert100.surround_eq ReorderedAFixed.hs (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g)
    A161Low4FixedFold.checked.out (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
    (ReorderedAPlain.unbuild ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) s m zeroU offHs
  exact ReorderedAFixed.transport _ s _ _ (plainNew.trans (ctxt.trans middleReplace)) (ReorderedAFixed.plain_frame base hc O hO s m hf)

private theorem keepA_cached_wires : wires rawFA ⊆ A109Research.domain.toFinset ∪ keepA.toFinset :=
  (ReorderedSupport.cached 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
    (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
    (by rw [A109Research.raw_lengths.2.2]; decide)
    (by rw [A109Research.raw_lengths.1, A109Research.raw_lengths.2.1])
    (by rw [A109Research.raw_lengths.2.1, A109Research.raw_lengths.2.2])).1

private theorem keepA_consumed_wires :
    wires (ReorderedConsumedSub.consumed 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin) ⊆
      A109Research.domain.toFinset ∪ keepA.toFinset :=
  ReorderedSupport.consumed 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
    (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
    (by rw [A109Research.raw_lengths.2.2]; decide)
    (by rw [A109Research.raw_lengths.1, A109Research.raw_lengths.2.1])
    (by rw [A109Research.raw_lengths.2.1, A109Research.raw_lengths.2.2])

theorem loopPCA_off (h : Wire) (hh : h ∈ ReorderedAFixed.hosts) (hk : h ∉ keepA) : h ∉ wires loopPCA := by
  have hA : h ∈ A109Research.hosts := List.mem_append.mpr (Or.inl hh)
  have hb : h ∉ wires (ReorderedAPlain.build ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedAFixed.off_plain h hh).1
  rw [A109Research.plain_split] at hb
  simp only [wires_append, Finset.mem_union, not_or] at hb
  have ht : h ∉ wires (ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedAFixed.off_plain h hh).2
  rw [A109Research.unbuild_split] at ht
  simp only [wires_append, Finset.mem_union, not_or] at ht
  have clearOff : h ∉ wires A109LowEraseResearch.clear := by
    rw [StairSqLoopA.clear_wires]; intro bad
    exact A109Research.old_away h hh ((by decide : ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire) ⊆ A109Research.ports) (List.mem_toFinset.mp bad))
  have out : h ∉ A109Research.domain.toFinset ∪ keepA.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]; exact ⟨A109Research.geometry.2.2 h hA, hk⟩
  simp only [loopPCA, restA, newIA, wires_append, Finset.mem_union, not_or, and_assoc]
  exact ⟨fun bad => hb.1 (SignAHeadSupport.support bad), clearOff, fun bad => out (keepA_cached_wires bad),
    A109Research.top_off h hA, A109Research.middle_fresh h hA, A109Research.preInv_off h hA,
    fun bad => out (keepA_consumed_wires bad), clearOff, ht.2⟩

theorem loopPCA_support : wires loopPCA ⊆ A109Research.S := by
  have hh : wires SignAHead.head ⊆ A109Research.S := by
    apply Finset.Subset.trans ?_ A109Research.old_prefix_support
    rw [A109Research.oldPrefix, wires_append]
    exact Finset.subset_union_left
  have ks : A109Research.domain.toFinset ∪ keepA.toFinset ⊆ A109Research.S := by
    intro q hq; apply A109Research.raw_domain_in
    simp only [Finset.mem_union, List.mem_toFinset] at hq ⊢
    rcases hq with h | h; exact Or.inl h; exact Or.inr (keepA_sub q h)
  simp only [loopPCA, restA, newIA, wires_append, Finset.union_subset_iff]
  exact ⟨hh,
    ⟨⟨⟨⟨⟨⟨A109Research.clear_support, keepA_cached_wires.trans ks⟩, A109Research.endpoint_support.1⟩,
      A109Research.middle_support⟩, ⟨A109Research.endpoint_support.2.1, keepA_consumed_wires.trans ks⟩⟩,
      A109Research.clear_support⟩, A109Research.endpoint_support.2.2⟩⟩

theorem loopPCA_physical : GatePhysical loopPCA := by
  have f := ReorderedPhysical.cached 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
    (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
    (by rw [A109Research.raw_lengths.2.2]; decide)
    A109Research.raw_nd (fun q hq bad => A109Research.geometry.2.2 q (keepA_sub q hq) (A109Research.c_in q bad))
  have n := notRegister_physical A109Research.ys
  simp only [loopPCA, restA, newIA, ReorderedConsumedSub.consumed, gatePhysical_append]
  exact ⟨SignAHeadResources.physical,
    ⟨⟨⟨⟨⟨⟨A109LowEraseResearch.physical, f.1⟩, A109Research.endpoint_physical.2.1⟩,
      AAliasesResearch.physical⟩, ⟨A109Research.endpoint_physical.2.2.1, ⟨⟨n, f.2⟩, n⟩⟩⟩,
      A109LowEraseResearch.physical⟩, A109Research.endpoint_physical.2.2.2⟩⟩

theorem loopA_pairs_free : ∀ ab ∈ StairSqLoopA.pairs hs, ab.2 ∉ wires loopPCA := by
  intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
  apply loopPCA_off _ (StairSqLoopA.hosts_of_hs _ (StairSqLoopA.holes_geometry44.2.2 y hy))
  have h := List.idxOf_lt_length_of_mem hy; rw [StairSqLoopA.hostDomain_length44] at h
  exact keepA_geometry.2.2.2.2.1 _ h

theorem loopA_support : wires loopA ⊆ A109Research.S := by
  intro q hq
  have sub := hostRename_support (StairSqLoopA.pairs hs) loopPCA (StairSqLoopA.pairs_nodup44 hs (List.Sublist.refl _)) loopA_pairs_free hq
  rcases Finset.mem_union.mp sub with h | h
  · exact loopPCA_support (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopA.pairs_snd] at h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact A109Research.raw_domain_in (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (StairSqLoopA.hosts_of_hs _ (StairSqLoopA.holes_geometry44.2.2 y hy))))))

theorem loopA_avoids_hs : ∀ q ∈ hs, q ∉ wires loopA := by
  intro q hq
  have h := hostRename_avoids (StairSqLoopA.pairs hs) loopPCA (StairSqLoopA.pairs_nodup44 hs (List.Sublist.refl _)) loopA_pairs_free
  rw [StairSqLoopA.pairs_fst] at h; exact h q hq

theorem loopA_avoids_workTA : ∀ q ∈ workTA, q ∉ wires loopA := by
  intro q hq bad
  have sub := hostRename_support (StairSqLoopA.pairs hs) loopPCA (StairSqLoopA.pairs_nodup44 hs (List.Sublist.refl _)) loopA_pairs_free bad
  rcases Finset.mem_union.mp sub with h | h
  · have hm : ∀ x ∈ workTA, x ∈ ReorderedAFixed.hosts := by rw [workTA_lit, hostsAFix_fast]; decide +kernel
    exact loopPCA_off q (hm q hq) (keepA_geometry.2.2.2.1 q hq) (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopA.pairs_snd] at h
    have dis : ∀ x ∈ workTA, x ∉ hs.map StairSqLoopA.hostOf := by simp only [workTA_lit, StairSqLoopA.hostOf, show StairSqLoopA.hostDomain = hs from rfl, hs_lit, hsA_fast]; decide +kernel
    exact dis q hq (List.mem_toFinset.mp h)

theorem loopA_counts :
    toffoliCount loopA = toffoliCount A109SignResearch.loop + 79 ∧
    measurementCount loopA = measurementCount A109SignResearch.loop := by
  have hr := hostRename_counts (StairSqLoopA.pairs hs) loopPCA
  have rel : toffoliCount loopPCA + 33 = toffoliCount StairSqLoopA.loopNC ∧
      measurementCount loopPCA = measurementCount StairSqLoopA.loopNC := by
    have cb := ReorderedGenericCache.count_balance 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide) (by rw [A109Research.raw_lengths.2.2]; decide)
    rw [loopPCA, restA, rawFA, newIA, StairSqLoopA.loopNC, StairSqLoopA.suffixNC,
      A109Research.I, A109Research.rawI, A109Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [toffoliCount_append, measurementCount_append]
    exact ⟨by omega, by omega⟩
  have nc := StairSqLoopA.loopNC_counts
  rw [loopA, hr.1, hr.2]
  exact ⟨by omega, by omega⟩

theorem loopA_slots : Challenge.gateSlots loopA = Challenge.gateSlots A109SignResearch.loop + 231 := by
  have hr := hostRename_slots (StairSqLoopA.pairs hs) loopPCA
  have rel : Challenge.gateSlots loopPCA + 99 = Challenge.gateSlots StairSqLoopA.loopNC := by
    have sc := ReorderedSlots.cache 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide) keepA_geometry.2.1
    rw [loopPCA, restA, rawFA, newIA, StairSqLoopA.loopNC, StairSqLoopA.suffixNC,
      A109Research.I, A109Research.rawI, A109Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [Challenge.gateSlots_append]
    omega
  have nc := StairSqLoopA.loopNC_slots
  rw [loopA, hr]
  omega

theorem loopA_frame : A109SignResearch.DirectLoopFrame loopA := by
  have pcFrame : A109SignResearch.DirectLoopFrame loopPCA := by
    intro base hc hsum hV hP hd O hO s m hf
    have clean := ReorderedAFixed.L.squareFrame_clean ReorderedAFixed.hn base s.basis O hf hc
    have hz : ∀ u ∈ ReorderedAFixed.pad, s.basis u = false := by
      intro u hu; rcases accZ_mem ReorderedAFixed.L u ((FullPadDevelop.pad_sublist ReorderedAFixed.L).subset hu) with hu' | hu'
      · exact (regValue_zero _ _).mp clean.pad u hu'
      · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu')
    have hb : ∀ u ∈ ReorderedAFixed.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
    have ha : regValue ReorderedAFixed.acc s.basis = 0 := A161Low4Ghost.ghostAcc_zero ReorderedAFixed.L s.basis clean
    have hhead : ∀ a b : List Bool, run SignAHead.head a s = run (ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) b s :=
      fun a b => ReorderedFrameUnique.program_eq ReorderedAFixed.acc s.basis 0 ((2 ^ 138 - 48 * regValue ReorderedAFixed.src s.basis) % 2 ^ 138) _ _
        (SignAHead.frame s.basis hz hb clean.cin)
        (ReorderedAHead.head_triple ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src ReorderedAFixed.lengths.1 ReorderedAFixed.lengths.2.2.2.le ReorderedAFixed.fits s.basis hz hb clean.cin)
        s a b ⟨ha, fun _ _ => rfl⟩
    have eq := SignRetape.replace SignAHead.head (ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) restA s m hhead
    have hheadEq : A109Research.head = ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src := rfl
    have hcoreEq : coreA = ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src ++ restA := by
      rw [coreA, newFA, restA, hheadEq]
      have g (A B C D E F G H : Program) : (((A ++ B ++ C ++ D) ++ E ++ F) ++ (G ++ H)) = A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H) := by simp only [List.append_assoc]
      exact g _ _ _ _ _ _ _ _
    have eq' : run loopPCA m s = run coreA (SignRetape.tape SignAHead.head (ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) m) s := by
      rw [loopPCA, hcoreEq]; exact eq
    exact ReorderedAFixed.transport _ s _ _ eq' (coreA_frame base hc hsum hV hP hd O hO s _ hf)
  intro base hc hsum hV hP hd O hO s m hf
  have r := pcFrame base hc hsum hV hP hd O hO s m hf
  have hEq : run loopA m s = run loopPCA m s := by
    apply hostRename_run_eq (StairSqLoopA.pairs hs) loopPCA s m
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      have hg := StairSqLoopA.holes_geometry44.2.1 y hy
      exact (hf.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact (hf.2 _ (A161Low4FixedFold.hostClean base hc hd _ (StairSqLoopA.holes_geometry44.2.2 y hy)).1).trans
        (A161Low4FixedFold.hostClean base hc hd _ (StairSqLoopA.holes_geometry44.2.2 y hy)).2
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      have hg := StairSqLoopA.holes_geometry44.2.1 y hy
      exact (r.2.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · exact loopA_pairs_free
  rw [hEq]; exact r

theorem bodyA_wires_plain : wires bodyA ⊆ wires bodyAPlain ∪ (K0.core.pad.take 32).toFinset := by
  have sp1 := directFold_rename_support foldPairsA (negP K0) (negP_count K0) foldPairsA_geom.1 (fun ab hab => (foldPairsA_geom.2.2.2.1 ab hab).2.2.1)
  have sp2 := directFold_rename_support foldPairsA (rot128F K0) (rot128F_count K0) foldPairsA_geom.1 (fun ab hab => (foldPairsA_geom.2.2.2.1 ab hab).2.2.1)
  rw [foldPairsA_geom.2.2.1] at sp1 sp2
  intro q hq
  simp only [bodyA, wires_append, Finset.mem_union] at hq
  rcases hq with (b | b | b) | b
  · rcases Finset.mem_union.mp (sp1 b) with h | h
    · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, wires_append, Finset.mem_union]; left; left; exact (Finset.mem_sdiff.mp h).1)
    · exact Finset.mem_union_right _ h
  · rcases Finset.mem_union.mp (sp2 b) with h | h
    · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, wires_append, Finset.mem_union]; left; right; left; exact (Finset.mem_sdiff.mp h).1)
    · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, wires_append, Finset.mem_union]; left; right; right; exact b)
  · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, wires_append, Finset.mem_union]; right; exact b)

theorem bodyA_ok : BodyAOK bodyA := by
  have s0 := A109SignResearch.direct_body_support_S loopA loopA_support
  have e0 := A109SignResearch.direct_body_eU_free_S loopA loopA_support
  refine ⟨?_, ?_, ?_⟩
  · intro q hq; rcases Finset.mem_union.mp (bodyA_wires_plain hq) with h | h
    · exact s0 h
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsA_geom.2.2.2.2 q (by rw [foldPairsA_geom.2.2.1]; exact List.mem_toFinset.mp h)).2.2.1))
  · intro bad; rcases Finset.mem_union.mp (bodyA_wires_plain bad) with h | h
    · exact e0 h
    · exact (foldPairsA_geom.2.2.2.2 _ (by rw [foldPairsA_geom.2.2.1]; exact List.mem_toFinset.mp h)).2.1 rfl
  · intro base M hM hP hc hsum O hO hg hd s m hf
    have rawRef := A109SignResearch.direct_body_frame loopA loopA_frame base M hM hP hc hsum O hO hg hd s m hf
    have views := accA_views K0 hwK base M hM hP
    have hv1 : K0.MeasuredFoldView base (negP K0) := views (.inl (negP K0)) (by simp [accAMix])
    have hv2 : K0.MeasuredFoldView base (rot128F K0) := views (.inl (rot128F K0)) (by simp [accAMix])
    have mc1 : measurementCount dF1A = measurementCount (directFoldQTq K0 (negP K0)) := (hostRename_counts foldPairsA (directFoldQTq K0 (negP K0))).2
    have mc2 : measurementCount dF2A = measurementCount (directFoldQTq K0 (rot128F K0)) := (hostRename_counts foldPairsA (directFoldQTq K0 (rot128F K0))).2
    have eq1 : run dF1A m s = run (directFoldQTq K0 (negP K0)) m s :=
      directFold_rename_run foldPairsA (negP K0) (negP_count K0) (negP_length K0 hwK) rfl rfl
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).1, (foldPairsA_geom.2.2.2.1 ab hab).2.1⟩)
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).2.2.1, (foldPairsA_geom.2.2.2.1 ab hab).2.2.2.1⟩)
        base hv1 hc O hO s m hf
    have hn := (List.nodup_cons.mp controlND).2
    have f1 := directFoldQ_frameTq K0 hwK hn base (negP K0) hv1 rfl hc (negP_length K0 hwK) rfl O hO s m hf
    have eq2 : run dF2A (m.drop (measurementCount (directFoldQTq K0 (negP K0)))) (run (directFoldQTq K0 (negP K0)) m s) =
        run (directFoldQTq K0 (rot128F K0)) (m.drop (measurementCount (directFoldQTq K0 (negP K0)))) (run (directFoldQTq K0 (negP K0)) m s) :=
      directFold_rename_run foldPairsA (rot128F K0) (rot128F_count K0) (rot128F_length K0 hwK) rfl rfl
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).1, (foldPairsA_geom.2.2.2.1 ab hab).2.1⟩)
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).2.2.1, (foldPairsA_geom.2.2.2.1 ab hab).2.2.2.1⟩)
        base hv2 hc _ (Nat.mod_lt _ (by norm_num [SquareReduction.p, SquareReduction.B, SquareReduction.c])) _ _ f1.2
    have bodyEq : run bodyA m s = run bodyAPlain m s := by
      simp only [bodyA, bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
        ControlledBorrowResearch.run_cat, measurementCount_append, mc1, mc2]
      rw [eq1, eq2]
    rw [bodyEq]; exact rawRef

theorem bodyA_avoids_workTA : ∀ q ∈ workTA, q ∉ wires bodyA := by
  intro q hq bad
  have hn := (List.nodup_cons.mp controlND).2
  have a1 := hostRename_avoids foldPairsA (directFoldQTq K0 (negP K0)) foldPairsA_geom.1
    (fun ab hab => directFoldQ_free K0 hn (negP K0) (negP_count K0) ab.2 (by simp [directFree, (foldPairsA_geom.2.2.2.1 ab hab).2.2.1]))
  have a2 := hostRename_avoids foldPairsA (directFoldQTq K0 (rot128F K0)) foldPairsA_geom.1
    (fun ab hab => directFoldQ_free K0 hn (rot128F K0) (rot128F_count K0) ab.2 (by simp [directFree, (foldPairsA_geom.2.2.2.1 ab hab).2.2.1]))
  rw [foldPairsA_geom.2.1] at a1 a2
  simp only [bodyA, wires_append, Finset.mem_union] at bad
  rcases bad with (b | b | b) | b
  · exact a1 q hq b
  · exact a2 q hq b
  · exact loopA_avoids_workTA q hq b
  · exact (by rw [workTA_lit, K0_eq]; decide +kernel : ∀ x ∈ workTA, x ≠ K0.core.cin) q hq (Finset.mem_singleton.mp (padding_wires 7 K0.core.cin b))

theorem bodyA_avoids_hs : ∀ q ∈ hs, q ∉ wires bodyA := by
  intro q hq bad
  rcases Finset.mem_union.mp (bodyA_wires_plain bad) with h | h
  · exact A109SignResearch.direct_body_holes loopA hs (fun x hx => (StairSqLoopA.holes_geometry44.2.1 x hx).1) loopA_avoids_hs q hq h
  · exact (foldPairsA_geom.2.2.2.2 q (by rw [foldPairsA_geom.2.2.1]; exact List.mem_toFinset.mp h)).1 hq

theorem bodyA_physical : GatePhysical bodyA := by
  have p0 := A109SignResearch.direct_body_physical loopA (hostRename_physical _ _ loopPCA_physical)
  simp only [A109SignResearch.directBody, A109SignResearch.directRawBody, gatePhysical_append] at p0
  simp only [bodyA, dF1A, dF2A, gatePhysical_append]
  exact ⟨⟨hostRename_physical _ _ p0.1.1, ⟨hostRename_physical _ _ p0.1.2.1, p0.1.2.2⟩⟩, p0.2⟩

theorem bodyA_counts :
    toffoliCount bodyA = toffoliCount A109SignResearch.body + 79 ∧
    measurementCount bodyA = measurementCount A109SignResearch.body := by
  have c0 := A109SignResearch.direct_body_counts loopA
  have cl := loopA_counts
  have r1 := hostRename_counts foldPairsA (directFoldQTq K0 (negP K0))
  have r2 := hostRename_counts foldPairsA (directFoldQTq K0 (rot128F K0))
  have eqT : toffoliCount bodyA = toffoliCount (A109SignResearch.directBody loopA) := by
    simp only [bodyA, dF1A, dF2A, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
      toffoliCount_append, r1.1, r2.1]
  have eqM : measurementCount bodyA = measurementCount (A109SignResearch.directBody loopA) := by
    simp only [bodyA, dF1A, dF2A, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
      measurementCount_append, r1.2, r2.2]
  rw [eqT, eqM]
  exact ⟨by omega, by omega⟩

theorem bodyA_slots : Challenge.gateSlots bodyA + 793 = Challenge.gateSlots A109SignResearch.body := by
  have s0 := A109SignResearch.direct_body_slots loopA
  have sl := loopA_slots
  have r1 := hostRename_slots foldPairsA (directFoldQTq K0 (negP K0))
  have r2 := hostRename_slots foldPairsA (directFoldQTq K0 (rot128F K0))
  have eqS : Challenge.gateSlots bodyA = Challenge.gateSlots (A109SignResearch.directBody loopA) := by
    simp only [bodyA, dF1A, dF2A, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
      Challenge.gateSlots_append, r1, r2]
  rw [eqS]
  omega

theorem bodyAPlain_coarse :
    wires bodyAPlain ⊆ insert D0 (G0 :: K0.wires).toFinset :=
  A109SignResearch.direct_body_coarse_S loopA loopA_support

theorem bodyAPlain_fine :
    wires bodyAPlain ⊆ insert D0 (wires (InverseCarryDevelop.hostedADual K0
      (LowZero18Square.foldPerm K0 E0) G0)) :=
  A109SignResearch.direct_body_fine_S loopA loopA_support

end BodyA

/-! ## Branch B body (`keepB` = 19 carries, `efSwapB` = 20 swaps, avoids `workTB`, `hs`, `normFlag`) -/

section BodyB
open ControlLoan1589BFFold ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical LocalRebuild.improved directFoldQTq ControlLoan1589BFFold.eAddLo ControlLoan1589BFFold.eSubK ParkCarryDevelop.program ParkCarry10Develop.rebuild

private theorem lb_eq_K0 : StairSqBodyB.LB = K0 := rfl
private theorem cb_eq_G0 : StairSqBodyB.cB = G0 := rfl

def keepB : List Wire := (B95Research.keepK.filter (fun q => !workTB.contains q)).take 19

theorem keepB_geometry : keepB.Nodup ∧ keepB.length = 19 ∧
    (∀ q ∈ keepB, q ∈ B95Research.hosts) ∧
    (∀ q ∈ workTB, q ∉ keepB) ∧
    (∀ i, i < 44 → LowAccCarryDevelop.hosts88.getD i 0 ∉ keepB) ∧
    (4761 : Wire) ∉ keepB ∧
    (∀ q ∈ keepB, q ∈ allowedWires) := by
  have hall : ∀ q ∈ keepB, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [keepB, keepKB_fast, workTB_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [keepB, keepKB_fast, workTB_lit, hs_lit]; decide +kernel))
  have hr : keepB.Nodup ∧ keepB.length = 19 ∧
      (∀ q ∈ keepB, q ∈ B95Research.hosts) ∧
      (∀ q ∈ workTB, q ∉ keepB) ∧
      (∀ i, i < 44 → LowAccCarryDevelop.hosts88.getD i 0 ∉ keepB) ∧
      (4761 : Wire) ∉ keepB := by rw [keepB, keepKB_fast, hostsB95_fast, hosts88_fast, workTB_lit]; decide +kernel
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, hall⟩

def rawFB : Program := ReorderedGenericCache.cachedAdd 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
def newFB : Program := B95Research.head ++ B95LowEraseResearch.clear ++ rawFB ++ B95Research.top
def newIB : Program := B95Research.preInv ++ ReorderedConsumedSub.consumed 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
def coreB : Program := (newFB ++ B95Research.M ++ newIB) ++ (B95LowEraseResearch.clear ++ B95Research.tail)
def restB : Program := B95LowEraseResearch.clear ++ rawFB ++ B95Research.top ++ B95Research.M ++ newIB ++ B95LowEraseResearch.clear ++ B95Research.tail
def loopPCB : Program := KnownBHeadResearch.output ++ restB
def loopB : Program := hostRename (StairSqLoopB.pairs hs) loopPCB
def foldPairsB : List (Wire × Wire) := (workTB.take 31).zip (K0.core.pad.take 31)
def dF1B : Program := hostRename foldPairsB (directFoldQTq K0 (negP K0))
def dF2B : Program := hostRename foldPairsB (directFoldQTq K0 (rot128F K0))
def efoldB : Program := hostRename efSwapB StairSquareBEFoldK.efold
def bodyB : Program :=
  StairSquareBBody.bodyG K0 dF1B dF2B loopB efoldB LocalRebuild.improved ++
    ReorderedRecordPadding.program 4 K0.core.cin

theorem foldPairsB_geom :
    (holesOf foldPairsB ++ hostsOf foldPairsB).Nodup ∧
    holesOf foldPairsB = workTB.take 31 ∧
    hostsOf foldPairsB = K0.core.pad.take 31 ∧
    (∀ ab ∈ foldPairsB, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out ∧ ab.2 ∈ allowedWires) ∧
    (∀ q ∈ hostsOf foldPairsB, q ∉ hs ∧ q ≠ K0.core.normFlag ∧ q ∈ K0.wires ∧ q ∈ allowedWires) := by
  have hall : ∀ q ∈ hostsOf foldPairsB, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsB, workTB_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [foldPairsB, workTB_lit, K0_eq, hs_lit]; decide +kernel))
  have hK : ∀ q ∈ hostsOf foldPairsB, q ∈ K0.wires :=
    StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsB, workTB_lit, K0_eq]; decide +kernel)
  have hr : (holesOf foldPairsB ++ hostsOf foldPairsB).Nodup ∧
      holesOf foldPairsB = workTB.take 31 ∧
      hostsOf foldPairsB = K0.core.pad.take 31 ∧
      (∀ ab ∈ foldPairsB, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out) ∧
      (∀ q ∈ hostsOf foldPairsB, q ∉ hs ∧ q ≠ K0.core.normFlag) := by
    rw [foldPairsB, workTB_lit, K0_eq, hs_lit]; decide +kernel
  refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_, ?_⟩
  · intro ab hab; have h := hr.2.2.2.1 ab hab
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hall ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩)⟩
  · intro q hq; have h := hr.2.2.2.2 q hq
    exact ⟨h.1, h.2, hK q hq, hall q hq⟩

private theorem keepB_sub (q : Wire) (hq : q ∈ keepB) : q ∈ B95Research.hosts := keepB_geometry.2.2.1 q hq

private theorem core_plainB (s : State) (m : List Bool)
    (hz : ∀ q ∈ ReorderedBPrefixResearch.pad, s.basis q = false) (hb : ∀ q ∈ ReorderedBPrefixResearch.bank, s.basis q = false)
    (hi : s.basis ReorderedBPrefixResearch.cin = false) (ha : regValue ReorderedBPrefixResearch.acc s.basis = 0)
    (zero : ∀ q ∈ ReorderedBSupportResearch.hosts, s.basis q = false)
    (after : WReady ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src
      (regValue ReorderedBPrefixResearch.src s.basis) (middleState B95Research.oldF B95Research.oldM s m))
    (flag : (run B95Research.oldF (m.take (measurementCount B95Research.oldF)) s).basis 4762 = false) :
    run coreB m s = run (B95Research.oldF ++ B95Research.oldM ++
      ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) m s := by
  let H := regValue ReorderedBPrefixResearch.src s.basis
  let vs := ReorderedCacheBits.values 4 19 H (976 * H / 1024)
  have fwdM : measurementCount newFB = measurementCount B95Research.F := by
    have h := (ReorderedGenericCache.count_balance 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide)).2.1
    simp only [newFB, rawFB, B95Research.F, B95Research.rawF, measurementCount_append]; rw [h]
  have invM : measurementCount newIB = measurementCount B95Research.I := by
    have h := ReorderedConsumedSub.measurement_eq 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide)
    simp only [newIB, B95Research.I, B95Research.rawI, measurementCount_append]; rw [h]
  have fwdVal : (((B95Research.cs.drop 4).take 19).map (run (carryPrefix (4 + 19) B95Research.xs B95Research.ys B95Research.cs ReorderedBPrefixResearch.cin) []
      (run (B95Research.head ++ B95LowEraseResearch.clear)
        ((m.take (measurementCount B95Research.F)).take (measurementCount (B95Research.head ++ B95LowEraseResearch.clear))) s)).basis) = vs := by
    let m0 := (m.take (measurementCount B95Research.F)).take (measurementCount (B95Research.head ++ B95LowEraseResearch.clear))
    let u := run B95Research.head m0 s
    let t := run (B95Research.head ++ B95LowEraseResearch.clear) m0 s
    have te : t = B95LowEraseResearch.erase u := B95Research.prefix_erased s m0 hz hb hi ha
    have hH : H < 2 ^ 128 := by simpa only [H, ReorderedBPrefixResearch.source_length] using regValue_lt ReorderedBPrefixResearch.src s.basis
    have ready := ReorderedHeadArithmeticResearch.ready ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank
      ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.source_length ReorderedBPrefixResearch.fits s m0 hz hb hi ha
    have eb (q : Wire) (hq : q ∈ B95Research.domain) : t.basis q = u.basis q := by
      rw [te]; exact B95LowEraseResearch.bit_same _ q (B95Research.domain_away_low q hq)
    have er (r : List Wire) (sub : ∀ q ∈ r, q ∈ B95Research.domain) : regValue r t.basis = regValue r u.basis :=
      regValue_congr _ _ _ (fun q hq => eb q (sub q hq))
    exact ReorderedCacheBits.forward_values 4 19 H (((2 ^ 138 - 48 * H) % 2 ^ 138) / 1024) (976 * H / 1024)
      B95Research.xs B95Research.ys B95Research.cs ReorderedBPrefixResearch.cin t
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide) B95Research.raw_nd
      (fun q hq => (eb q (B95Research.c_in q hq)).trans (ready.1 q hq))
      ((eb _ B95Research.cin_in).trans ready.2.1)
      ((er _ B95Research.x_in).trans ready.2.2.1)
      ((er _ B95Research.y_in).trans ready.2.2.2)
      (fun j hj => by simpa only [show 128 + 10 = 138 by decide] using ReorderedCacheArithmetic.high_add_low 128 (4 + j + 1) H (by omega) hH)
  have forward : run newFB (m.take (measurementCount B95Research.F)) s =
      scatterState keepB vs (run B95Research.F (m.take (measurementCount B95Research.F)) s) := by
    have h := CacheBetweenFrameResearch.forward (B95Research.head ++ B95LowEraseResearch.clear) B95Research.top
      19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide) keepB_geometry.1
      (fun q hq bad => B95Research.geometry.2.2 q (keepB_sub q hq) (by clear * - bad; simp only [B95Research.domain, List.mem_cons, List.mem_append] at bad ⊢; tauto))
      (fun q hq => B95Research.rawF_off q (keepB_sub q hq)) (fun q hq => B95Research.top_off q (keepB_sub q hq))
      s (m.take (measurementCount B95Research.F))
      (fun q hq => B95Research.prefix_zero s _ hz hb hi ha zero q (keepB_sub q hq))
    rw [fwdVal] at h; exact h
  have mid := B95Research.middle_erased s m hz hb hi ha after flag
  have cacheEq : run (newFB ++ B95Research.M ++ newIB) m s = run (B95Research.F ++ B95Research.M ++ B95Research.I) m s := by
    apply CacheFromCleanForwardResearch.equivalent B95Research.F newFB B95Research.M B95Research.I newIB keepB vs
      fwdM (fun q hq => B95Research.middle_fresh q (keepB_sub q hq))
      (fun q hq => B95Research.I_off q (keepB_sub q hq)) keepB_geometry.1 s m
      (fun q hq => B95Research.forward_zero s _ hz hb hi ha zero q (keepB_sub q hq)) forward
    rw [mid]
    let ms := middleState B95Research.oldF B95Research.oldM s m
    let mr := m.drop (measurementCount B95Research.F + measurementCount B95Research.M)
    let t := scatterState keepB vs (B95LowEraseResearch.erase ms)
    have comm : run B95Research.preInv mr t = scatterState keepB vs (B95LowEraseResearch.erase (run B95Research.preInv mr ms)) := by
      rw [show t = scatterState keepB vs (B95LowEraseResearch.erase ms) from rfl,
        run_scatter B95Research.preInv keepB vs _ _ (fun q hq => B95Research.preInv_off q (keepB_sub q hq)),
        B95LowEraseResearch.commute B95Research.preInv mr ms (fun q hq => B95Research.preInv_off q (B95Research.low_hosts q hq))]
    have bits (q : Wire) (hq : q ∈ B95Research.domain) : (run B95Research.preInv mr t).basis q = (run B95Research.preInv mr ms).basis q := by
      rw [comm, scatter_outside keepB vs _ q (fun bad => B95Research.geometry.2.2 q (keepB_sub q bad) hq)]
      exact B95LowEraseResearch.bit_same _ q (B95Research.domain_away_low q hq)
    have regs (r : List Wire) (sub : ∀ q ∈ r, q ∈ B95Research.domain) :
        regValue r (run B95Research.preInv mr t).basis = regValue r (run B95Research.preInv mr ms).basis :=
      regValue_congr _ _ _ (fun q hq => bits q (sub q hq))
    have rr := B95Research.pre_raw_ready H ms mr after
    have saved : keepB.map t.basis = vs := scatter_saved_map keepB vs _ keepB_geometry.1
      (by simp only [vs, ReorderedCacheBits.values, List.length_map, keepB_geometry.2.1, List.length_range])
    have same : keepB.map (run B95Research.preInv mr t).basis = keepB.map t.basis :=
      List.map_congr_left (fun q hq => run_preserves_outside B95Research.preInv mr t q (B95Research.preInv_off q (keepB_sub q hq)))
    simp only [newIB, B95Research.I, B95Research.rawI, ControlledBorrowResearch.run_cat]
    exact ReorderedConsumedSub.frame 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide)
      (by rw [B95Research.raw_lengths.1, B95Research.raw_lengths.2.1])
      (by rw [B95Research.raw_lengths.2.1, B95Research.raw_lengths.2.2])
      B95Research.raw_nd keepB_geometry.1 keepB_geometry.2.1 (fun q hq => B95Research.geometry.2.2 q (keepB_sub q hq))
      (run B95Research.preInv mr t) _ (fun q hq => (bits q (B95Research.c_in q hq)).trans (rr.1 q hq))
      ((bits _ B95Research.cin_in).trans rr.2.1) H (976 * H / 1024)
      ((regs _ B95Research.x_in).trans rr.2.2.1) ((regs _ B95Research.y_in).trans rr.2.2.2) (same.trans saved)
  have eq := ClearContextResearch.append_at (newFB ++ B95Research.M ++ newIB)
    (B95Research.F ++ B95Research.M ++ B95Research.I) (B95LowEraseResearch.clear ++ B95Research.tail) s m
    (by simp only [measurementCount_append, fwdM, invM]) cacheEq
  have shape : (B95Research.F ++ B95Research.M ++ B95Research.I) ++ (B95LowEraseResearch.clear ++ B95Research.tail) =
      B95Research.F ++ B95Research.M ++ (B95Research.I ++ B95LowEraseResearch.clear ++ B95Research.tail) := by
    have g (A B C D E : Program) : (A ++ B ++ C) ++ (D ++ E) = A ++ B ++ (C ++ D ++ E) := by simp only [List.append_assoc]
    exact g _ _ _ _ _
  exact eq.trans ((congrArg (fun P => run P m s) shape).trans (B95Research.plain_loop s m hz hb hi ha after flag))

private theorem keepB_cached_wires : wires rawFB ⊆ B95Research.domain.toFinset ∪ keepB.toFinset :=
  (ReorderedSupport.cached 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
    (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
    (by rw [B95Research.raw_lengths.2.2]; decide)
    (by rw [B95Research.raw_lengths.1, B95Research.raw_lengths.2.1])
    (by rw [B95Research.raw_lengths.2.1, B95Research.raw_lengths.2.2])).1

private theorem keepB_consumed_wires :
    wires (ReorderedConsumedSub.consumed 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin) ⊆
      B95Research.domain.toFinset ∪ keepB.toFinset :=
  ReorderedSupport.consumed 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
    (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
    (by rw [B95Research.raw_lengths.2.2]; decide)
    (by rw [B95Research.raw_lengths.1, B95Research.raw_lengths.2.1])
    (by rw [B95Research.raw_lengths.2.1, B95Research.raw_lengths.2.2])

theorem loopPCB_off (h : Wire) (hh : h ∈ ReorderedBSupportResearch.hosts) (hk : h ∉ keepB) : h ∉ wires loopPCB := by
  have hA : h ∈ B95Research.hosts := List.mem_append.mpr (Or.inl hh)
  have hb : h ∉ wires (ReorderedAPlain.build ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedBSupportResearch.plain_free h hh).1
  rw [B95Research.plain_split] at hb
  simp only [wires_append, Finset.mem_union, not_or] at hb
  have ht : h ∉ wires (ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedBSupportResearch.plain_free h hh).2
  rw [B95Research.unbuild_split] at ht
  simp only [wires_append, Finset.mem_union, not_or] at ht
  have clearOff : h ∉ wires B95LowEraseResearch.clear := by
    rw [StairSqLoopB.clear_wires]; intro bad
    exact B95Research.old_away h hh ((by decide : ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire) ⊆ B95Research.ports) (List.mem_toFinset.mp bad))
  have out : h ∉ B95Research.domain.toFinset ∪ keepB.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]; exact ⟨B95Research.geometry.2.2 h hA, hk⟩
  simp only [loopPCB, restB, newIB, wires_append, Finset.mem_union, not_or, and_assoc]
  exact ⟨fun bad => hb.1 (KnownBHeadResearch.support bad), clearOff, fun bad => out (keepB_cached_wires bad),
    B95Research.top_off h hA, B95Research.middle_fresh h hA, B95Research.preInv_off h hA,
    fun bad => out (keepB_consumed_wires bad), clearOff, ht.2⟩

theorem loopPCB_support : wires loopPCB ⊆ B95Research.S := by
  have ks : B95Research.domain.toFinset ∪ keepB.toFinset ⊆ B95Research.S := by
    intro q hq; apply B95Research.raw_domain_in
    simp only [Finset.mem_union, List.mem_toFinset] at hq ⊢
    rcases hq with h | h; exact Or.inl h; exact Or.inr (keepB_sub q h)
  simp only [loopPCB, restB, newIB, wires_append, Finset.union_subset_iff]
  exact ⟨KnownBHeadResearch.support.trans B95Research.endpoint_support.1,
    ⟨⟨⟨⟨⟨⟨B95Research.clear_support, keepB_cached_wires.trans ks⟩, B95Research.endpoint_support.2.1⟩,
      B95Research.middle_support⟩, ⟨B95Research.endpoint_support.2.2.1, keepB_consumed_wires.trans ks⟩⟩,
      B95Research.clear_support⟩, B95Research.endpoint_support.2.2.2⟩⟩

theorem loopPCB_physical : GatePhysical loopPCB := by
  have f := ReorderedPhysical.cached 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
    (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
    (by rw [B95Research.raw_lengths.2.2]; decide)
    B95Research.raw_nd (fun q hq bad => B95Research.geometry.2.2 q (keepB_sub q hq) (B95Research.c_in q bad))
  have n := notRegister_physical B95Research.ys
  simp only [loopPCB, restB, newIB, ReorderedConsumedSub.consumed, gatePhysical_append]
  exact ⟨KnownBHeadResearch.physical B95Research.endpoint_physical.1,
    ⟨⟨⟨⟨⟨⟨B95LowEraseResearch.physical, f.1⟩, B95Research.endpoint_physical.2.1⟩,
      B95AliasesResearch.physical⟩, ⟨B95Research.endpoint_physical.2.2.1, ⟨⟨n, f.2⟩, n⟩⟩⟩,
      B95LowEraseResearch.physical⟩, B95Research.endpoint_physical.2.2.2⟩⟩

theorem loopB_pairs_free : ∀ ab ∈ StairSqLoopB.pairs hs, ab.2 ∉ wires loopPCB := by
  intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
  apply loopPCB_off _ (StairSqLoopB.hosts_of_88 _ (StairSqLoopB.holes_geometry44.2.2 y hy))
  have h := List.idxOf_lt_length_of_mem hy; rw [StairSqLoopA.hostDomain_length44] at h
  exact keepB_geometry.2.2.2.2.1 _ h

theorem loopB_support : wires loopB ⊆ B95Research.S := by
  intro q hq
  have sub := hostRename_support (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free hq
  rcases Finset.mem_union.mp sub with h | h
  · exact loopPCB_support (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopB.pairs_snd] at h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact B95Research.raw_domain_in (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (StairSqLoopB.hosts_of_88 _ (StairSqLoopB.holes_geometry44.2.2 y hy))))))

theorem loopB_avoids_hs : ∀ q ∈ hs, q ∉ wires loopB := by
  intro q hq
  have h := hostRename_avoids (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free
  rw [StairSqLoopB.pairs_fst] at h; exact h q hq

theorem loopB_avoids_workTB : ∀ q ∈ workTB, q ∉ wires loopB := by
  intro q hq bad
  by_cases hD : q = D0
  · subst hD
    have park := ParkCarry10Develop.body_support StairSqBodyB.LB LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup StairSqBodyB.cB
    have hsup := park (FullB99OptTemp.actual_subset (loopB_support bad))
    rw [lb_eq_K0, cb_eq_G0] at hsup
    exact (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (List.mem_toFinset.mp hsup)
  · have sub := hostRename_support (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free bad
    rcases Finset.mem_union.mp sub with h | h
    · have hm : ∀ x ∈ workTB, x ≠ D0 → x ∈ ReorderedBSupportResearch.hosts := by rw [workTB_lit, D0_eq, hostsBSup_fast]; decide +kernel
      exact loopPCB_off q (hm q hq hD) (keepB_geometry.2.2.2.1 q hq) (Finset.mem_sdiff.mp h).1
    · rw [StairSqLoopB.pairs_snd] at h
      have dis : ∀ x ∈ workTB, x ∉ hs.map StairSqLoopB.hostOf := by simp only [workTB_lit, StairSqLoopB.hostOf, show StairSqLoopA.hostDomain = hs from rfl, hs_lit, hosts88_fast]; decide +kernel
      exact dis q hq (List.mem_toFinset.mp h)

theorem loopB_normFlag : K0.core.normFlag ∉ wires loopB := by
  have hM := StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.middle_norm _ (List.mem_singleton_self _)
  have hb := StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.build_norm _ (List.mem_singleton_self _)
  have hu := StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.unbuild_norm _ (List.mem_singleton_self _)
  rw [B95Research.plain_split] at hb; rw [B95Research.unbuild_split] at hu
  simp only [wires_append, Finset.mem_union, not_or] at hb hu
  have clearOff : K0.core.normFlag ∉ wires B95LowEraseResearch.clear := by
    rw [StairSqLoopB.clear_wires]; intro h
    exact (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel : K0.core.normFlag ∉ ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire)) (List.mem_toFinset.mp h)
  have out : K0.core.normFlag ∉ B95Research.domain.toFinset ∪ keepB.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]
    exact ⟨fun h => hb.2.1 (by rw [B95Research.raw_wires]; exact List.mem_toFinset.mpr h), keepB_geometry.2.2.2.2.2.1⟩
  have pcNF : K0.core.normFlag ∉ wires loopPCB := by
    have hI := hu.1; simp only [B95Research.I, wires_append, Finset.mem_union, not_or] at hI
    simp only [loopPCB, restB, newIB, wires_append, Finset.mem_union, not_or, and_assoc]
    exact ⟨fun h => hb.1 (KnownBHeadResearch.support h), clearOff, fun h => out (keepB_cached_wires h),
      hb.2.2, hM, hI.1, fun h => out (keepB_consumed_wires h), clearOff, hu.2⟩
  intro bad
  have sub := hostRename_support (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free bad
  rcases Finset.mem_union.mp sub with h | h
  · exact pcNF (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopB.pairs_snd] at h
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    have hm := StairSqLoopB.holes_geometry44.2.2 y hy; rw [hyx] at hm
    exact (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel : K0.core.normFlag ∉ LowAccCarryDevelop.hosts88) hm

theorem loopB_counts :
    toffoliCount loopB = toffoliCount B95Research.loop + 79 ∧
    measurementCount loopB = measurementCount B95Research.loop := by
  have hr := hostRename_counts (StairSqLoopB.pairs hs) loopPCB
  have rel : toffoliCount loopPCB + 19 = toffoliCount StairSqLoopB.loopNC ∧
      measurementCount loopPCB = measurementCount StairSqLoopB.loopNC := by
    have cb := ReorderedGenericCache.count_balance 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide) (by rw [B95Research.raw_lengths.2.2]; decide)
    rw [loopPCB, restB, rawFB, newIB, StairSqLoopB.loopNC, StairSqLoopB.restNC,
      B95Research.I, B95Research.rawI, B95Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [toffoliCount_append, measurementCount_append]
    exact ⟨by omega, by omega⟩
  have nc := StairSqLoopB.loopNC_counts
  rw [loopB, hr.1, hr.2]
  exact ⟨by omega, by omega⟩

theorem loopB_slots : Challenge.gateSlots loopB = Challenge.gateSlots B95Research.loop + 231 := by
  have hr := hostRename_slots (StairSqLoopB.pairs hs) loopPCB
  have rel : Challenge.gateSlots loopPCB + 57 = Challenge.gateSlots StairSqLoopB.loopNC := by
    have sc := ReorderedSlots.cache 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide) keepB_geometry.2.1
    rw [loopPCB, restB, rawFB, newIB, StairSqLoopB.loopNC, StairSqLoopB.restNC,
      B95Research.I, B95Research.rawI, B95Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [Challenge.gateSlots_append]
    omega
  have nc := StairSqLoopB.loopNC_slots
  rw [loopB, hr]
  omega

theorem loopB_frame (base : BasisState) (clean : K0.PairClean base) (hsum : base K0.core.sumCarry = false)
    (O E O' : Nat) (hE : E < 2 ^ 129)
    (mid : Triple (BState K0 base O E (4294968272 * regValue (hiReg K0) base)) (FullBTemp.middle K0 G0)
      (BState K0 base O' E (4294968272 * regValue (hiReg K0) base))) :
    Triple (BState K0 base O E 0) loopB (BState K0 base O' E 0) := by
  have pcFrame : Triple (BState K0 base O E 0) loopPCB (BState K0 base O' E 0) := by
    intro s m hsB
    obtain ⟨hzFull, hb, hi, _, _⟩ := zero_regs K0 LowAccCarryDevelop.layout_nodup base clean O E 0 s.basis hsB
    have hz : ∀ q ∈ ReorderedBPrefixResearch.pad, s.basis q = false := fun q hq => hzFull q ((FullPadDevelop.pad_sublist K0).subset hq)
    have ha : regValue LowAccCarryDevelop.ga s.basis = 0 := LowAccCarryDevelop.ga_bstate_value base s.basis clean O E 0 hsB (by decide)
    have small : regValue ReorderedBPrefixResearch.acc s.basis = 0 := by
      rw [regValue_take_mod LowAccCarryDevelop.ga 161 (by rw [LowAccCarryDevelop.ga_length]; decide), ha]; rfl
    have headEq : run loopPCB m s = run coreB m s := by
      have cl : ∀ q ∈ KnownBHeadResearch.clean, s.basis q = false := by
        intro q hq; simp only [KnownBHeadResearch.clean, List.mem_append, List.mem_singleton] at hq
        rcases hq with ((hq | hq) | hq) | rfl
        · exact (regValue_zero _ _).mp small q hq
        · exact hz q hq
        · exact hb q hq
        · exact hi
      have hheadEq : B95Research.head = KnownBHeadResearch.original := by
        unfold B95Research.head KnownBHeadResearch.original; rfl
      have shape : coreB = KnownBHeadResearch.original ++ restB := by
        rw [coreB, newFB, restB, hheadEq]
        have g (A B C D E F G H : Program) : (((A ++ B ++ C ++ D) ++ E ++ F) ++ (G ++ H)) = A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H) := by simp only [List.append_assoc]
        exact g _ _ _ _ _ _ _ _
      exact (ClearContextResearch.append_at KnownBHeadResearch.output KnownBHeadResearch.original restB s m
        KnownBHeadResearch.measurements (KnownBHeadResearch.run_eq s m cl)).trans (congrArg (fun P => run P m s) shape.symm)
    rw [headEq]
    have zero : ∀ q ∈ ReorderedBSupportResearch.hosts, s.basis q = false := by
      intro q hq; rcases List.mem_cons.mp hq with rfl | hq
      · have away := ParkCarryDevelop.sumCarry_off_regs K0 LowAccCarryDevelop.layout_nodup
        exact (hsB.2.2.2 _ away.1 away.2.1 away.2.2).trans hsum
      · exact LowAccCarryDevelop.initial_hosts_zero base s.basis clean O E hsB q hq
    have good := fun r => ReorderedBReadyResearch.original_ready base clean O E O' mid s r hsB
    have hc : ExtraCarryDomain.Clean s.basis := ⟨bstate_clean K0 LowAccCarryDevelop.layout_nodup base clean O E s.basis hsB, by change regValue (eReg K0) s.basis < 2 ^ 129; rw [hsB.2.1]; exact hE⟩
    have ready : WReady ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank
        ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src (regValue ReorderedBPrefixResearch.src s.basis)
        (middleState B95Research.oldF B95Research.oldM s m) :=
      BRelocatedReadyResearch.patched_after s m hc hz hb hi ha zero good
    have f := ReorderedAPlain.build_triple ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src
      ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.source_length ReorderedBPrefixResearch.fits s.basis hz hb hi s
      (m.take (measurementCount B95Research.oldF)) ⟨small, fun _ _ => rfl⟩
    have flag0 := (f.2.2 4762 (by simp only [ReorderedBPrefixResearch.acc, ReorderedBPrefixResearch.pad, ReorderedBPrefixResearch.bank, ReorderedBPrefixResearch.cin, ReorderedBPrefixResearch.src, ReorderedBPrefixResearch.ga, LowAccCarryDevelop.ga, LowAccCarryDevelop.L, FullBReady.L, show Baselines.layout.dialogStreamedSquareWide = K0 from rfl, K0_eq]; decide +kernel)).trans hc.1.modFlag
    have e : B95Research.oldF = ReorderedAPlain.build ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
        ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src := rfl
    have flag : (run B95Research.oldF (m.take (measurementCount B95Research.oldF)) s).basis 4762 = false :=
      (congrArg (fun P => (run P (m.take (measurementCount B95Research.oldF)) s).basis 4762 = false) e).mpr flag0
    have one := core_plainB s m hz hb hi small zero ready flag
    have two : run BPatchedLoopResearch.core m s =
        run (B95Research.oldF ++ B95Research.oldM ++ ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) m s := by
      simpa only [BPatchedLoopResearch.core, B95Research.oldF, B95Research.oldM] using
        HighCachedLoopBResearch.loop_eq ReorderedBPrefixResearch.acc ReorderedBMiddlePatchesResearch.output
          ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.fits rfl s m hz hb hi small
          ReorderedBSupportResearch.fresh (fun q hq => (ReorderedBSupportResearch.plain_free q hq).1)
          (fun q hq => (ReorderedBSupportResearch.plain_free q hq).2) ReorderedBMiddlePatchesResearch.fresh zero ready
    rw [one.trans two.symm]
    exact BPatchedLoopResearch.core_frame base clean hsum O E O' hE mid s m hsB
  intro s m hsB
  have r := pcFrame s m hsB
  have zIn := (zero_regs K0 LowAccCarryDevelop.layout_nodup base clean O E 0 s.basis hsB).2.2.2.1
  have zOut := (zero_regs K0 LowAccCarryDevelop.layout_nodup base clean O' E 0 (run loopPCB m s).basis r.2).2.2.2.1
  have hOut : ∀ q ∈ hs, (run loopPCB m s).basis q = false := fun q hq => zOut q (StairSqLoopB.holes_geometry44.2.1 q hq)
  have hEq : run loopB m s = run loopPCB m s := by
    apply hostRename_run_eq (StairSqLoopB.pairs hs) loopPCB s m
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact zIn y (StairSqLoopB.holes_geometry44.2.1 y hy)
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact LowAccCarryDevelop.initial_hosts_zero base s.basis clean O E hsB _ (StairSqLoopB.holes_geometry44.2.2 y hy)
    · intro ab hab; obtain ⟨y, hy, he⟩ := List.mem_map.mp hab
      have h1 : ab.1 = y := by rw [← he]
      rw [h1]; exact hOut y hy
    · exact loopB_pairs_free
  rw [hEq]; exact r

private def efCheckB : List Wire :=
  [4726, 4727, 4728, 4729, 4730, 4731, 4732, 4733, 4734, 4735, 4736, 4737, 4738, 4739, 4740, 4741,
   4742, 4743, 4744, 4745, 4746, 4747, 4748, 4749, 4750, 4751, 4752, 4753, 4754, 4755, 4756]

private theorem efold_avoids_check : ∀ q ∈ efCheckB, q ∉ wires StairSquareBEFoldK.efold := by
  have hflip : ∀ q ∈ efCheckB, q ∉ wires (ControlLoan1589BFFold.eFlip K0 G0) :=
    StairSquareBChecks.touchedAny_spec _ _
      (StairSquareBChecks.K2Hit.touchedAny_of_mask _ _ (by rw [K0_eq, G0_eq]; decide +kernel))
  have hfill : ∀ q ∈ efCheckB, q ∉ StairSquareBChecks.K2Fill.efillS K0 :=
    StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [K0_eq]; decide +kernel)
  have hsup := StairSquareBChecks.K2Fill.efill_support K0 hwK LowAccCarryDevelop.layout_nodup
  have h3 : ∀ q ∈ efCheckB,
      q ∉ (StairSquareBEFold.coreB K0).out ++ (StairSquareBEFold.coreB K0).carry ++
        [(StairSquareBEFold.coreB K0).high, (StairSquareBEFold.coreB K0).cin,
         (StairSquareBEFold.coreB K0).flag] ++ ECDSAAdd.Entrant.accReg K0 :=
    StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [K0_eq]; decide +kernel)
  intro q hq bad
  simp only [StairSquareBEFoldK.efold, StairSquareBEFold.eFoldB, StairSquareBEFold.accFoldB,
    lb_eq_K0, cb_eq_G0, wires_append, Finset.mem_union] at bad
  rcases bad with hw | ((hw | hw) | hw) | hw
  · exact hflip q hq hw
  · exact hfill q hq (List.mem_toFinset.mp (hsup.1 hw))
  · have hs := StairSquareBMapped.qprogM_support (StairSquareBEFold.coreB K0)
      (StairSquareBEFold.bitsB K0) SquareReduction.p hw
    rw [StairSquareBEFold.bitsB_wires] at hs
    exact h3 q hq (List.mem_toFinset.mp hs)
  · exact hfill q hq (List.mem_toFinset.mp (hsup.2 hw))
  · exact hflip q hq hw

/-- `efoldB` satisfies `StairSqBodyB.EFoldOK` AND avoids `workTB`, `hs`, and `normFlag`. -/
theorem efoldB_hostFree : ∀ ab ∈ efSwapB, ab.2 ∉ wires StairSquareBEFoldK.efold := fun ab hab =>
  efold_avoids_check ab.2 ((by rw [efSwapB_lit]; decide +kernel : ∀ p ∈ efSwapB, p.2 ∈ efCheckB) ab hab)

theorem efoldB_ok : StairSqBodyB.EFoldOK efoldB := by
  have baseOK := StairSqBodyB.efold_ok
  refine ⟨?_, ?_, ?_, hostRename_physical _ _ baseOK.2.2.2⟩
  · intro b clean O E hO s m hsB
    have r := baseOK.1 b clean O E hO s m hsB
    have hEq : run efoldB m s = run StairSquareBEFoldK.efold m s := by
      apply hostRename_run_eq efSwapB StairSquareBEFoldK.efold s m
      · intro ab hab
        have h1 : ab.1 ∈ LowAccCarryDevelop.hosts88 := (by rw [efSwapB_lit, hosts88_fast]; decide +kernel : ∀ x ∈ holesOf efSwapB, x ∈ LowAccCarryDevelop.hosts88) ab.1 (List.mem_map.mpr ⟨ab, hab, rfl⟩)
        exact LowAccCarryDevelop.initial_hosts_zero b s.basis clean O E hsB ab.1 h1
      · intro ab hab
        have h2 : ab.2 ∈ LowAccCarryDevelop.hosts88 := List.mem_of_mem_take (work_T_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ab hab).2.2.1
        exact LowAccCarryDevelop.initial_hosts_zero b s.basis clean O E hsB ab.2 h2
      · intro ab hab
        have h1 : ab.1 ∈ LowAccCarryDevelop.hosts88 := (by rw [efSwapB_lit, hosts88_fast]; decide +kernel : ∀ x ∈ holesOf efSwapB, x ∈ LowAccCarryDevelop.hosts88) ab.1 (List.mem_map.mpr ⟨ab, hab, rfl⟩)
        exact LowAccCarryDevelop.initial_hosts_zero b (run StairSquareBEFoldK.efold m s).basis clean _ E r.2 ab.1 h1
      · exact efoldB_hostFree
    rw [hEq]; exact r
  · intro q hq
    have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree hq
    rcases Finset.mem_union.mp sub with h | h
    · exact baseOK.2.1 (Finset.mem_sdiff.mp h).1
    · have subK : ∀ x ∈ hostsOf efSwapB, x ∈ K0.wires := by rw [efSwapB_lit, K0_eq]; decide +kernel
      rw [lb_eq_K0, cb_eq_G0]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem G0 (subK q (List.mem_toFinset.mp h)))
  · intro q hq bad
    have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
    rcases Finset.mem_union.mp sub with h | h
    · exact baseOK.2.2.1 q hq (Finset.mem_sdiff.mp h).1
    · exact (by rw [efSwapB_lit, holesA_lit]; decide +kernel : ∀ x ∈ StairSqLoopA.holes, x ∉ hostsOf efSwapB) q hq (List.mem_toFinset.mp h)

theorem efoldB_avoids_workTB : ∀ q ∈ workTB, q ∉ wires efoldB := by
  intro q hq bad
  by_cases hD : q = D0
  · subst hD
    have hsup := efoldB_ok.2.1 bad
    rw [lb_eq_K0, cb_eq_G0] at hsup
    exact (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (List.mem_toFinset.mp hsup)
  · by_cases hh : q ∈ holesOf efSwapB
    · exact hostRename_avoids efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree q hh bad
    · have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
      rcases Finset.mem_union.mp sub with h | h
      · exact efold_avoids_check q ((by rw [workTB_lit, D0_eq, efSwapB_lit]; decide +kernel : ∀ x ∈ workTB, x ≠ D0 → x ∉ holesOf efSwapB → x ∈ efCheckB) q hq hD hh) (Finset.mem_sdiff.mp h).1
      · exact (by rw [workTB_lit, efSwapB_lit]; decide +kernel : ∀ x ∈ workTB, x ∉ hostsOf efSwapB) q hq (List.mem_toFinset.mp h)

theorem efoldB_avoids_hs : ∀ q ∈ hs, q ∉ wires efoldB := by
  intro q hq bad
  have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
  rcases Finset.mem_union.mp sub with h | h
  · exact StairSquareBEFoldK.efold_avoids q hq (Finset.mem_sdiff.mp h).1
  · exact (by rw [efSwapB_lit, hs_lit]; decide +kernel : ∀ x ∈ hs, x ∉ hostsOf efSwapB) q hq (List.mem_toFinset.mp h)

theorem efoldB_normFlag : K0.core.normFlag ∉ wires efoldB := by
  intro bad
  have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
  rcases Finset.mem_union.mp sub with h | h
  · exact StairSquareBEFoldK.efold_normFlag (Finset.mem_sdiff.mp h).1
  · exact (by rw [efSwapB_lit, K0_eq]; decide +kernel : K0.core.normFlag ∉ hostsOf efSwapB) (List.mem_toFinset.mp h)

theorem bodyB_ok : BodyBOK bodyB := by
  have hn := LowAccCarryDevelop.layout_nodup
  have hcw : G0 ∉ K0.wires := (List.nodup_cons.mp controlND).1
  have sup : wires bodyB ⊆ (G0 :: K0.wires).toFinset := by
    have sp1 := directFold_rename_support foldPairsB (negP K0) (negP_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
    have sp2 := directFold_rename_support foldPairsB (rot128F K0) (rot128F_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
    have direct_in_K0 (f : MeasuredSquareFold) (hc : ∀ q, f.src.count q ≤ K0.core.product.count q) :
        wires (directFoldQTq K0 f) ⊆ K0.wires.toFinset := by
      intro q hq
      have h1 := List.count_pos_iff.mpr (List.mem_toFinset.mp (directFoldQ_supportTq K0 f hq))
      have h2 := hc q
      simp only [directWires, List.count_append, List.count_cons, List.count_nil] at h1
      exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by
        simp only [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires,
          List.count_append, List.count_cons, List.count_nil]; omega))
    have f1 : wires dF1B ⊆ (G0 :: K0.wires).toFinset := by
      intro q hq; rcases Finset.mem_union.mp (sp1 hq) with h | h
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (direct_in_K0 (negP K0) (negP_count K0) (Finset.mem_sdiff.mp h).1)))
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).2.2.1)
    have f2 : wires dF2B ⊆ (G0 :: K0.wires).toFinset := by
      intro q hq; rcases Finset.mem_union.mp (sp2 hq) with h | h
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (direct_in_K0 (rot128F K0) (rot128F_count K0) (Finset.mem_sdiff.mp h).1)))
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).2.2.1)
    have park := ParkCarry10Develop.body_support StairSqBodyB.LB LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup StairSqBodyB.cB
    have fl : wires loopB ⊆ (G0 :: K0.wires).toFinset := by
      rw [← lb_eq_K0, ← cb_eq_G0]
      exact loopB_support.trans (fun q hq => park (FullB99OptTemp.actual_subset hq))
    have fpad : wires (ReorderedRecordPadding.program 4 K0.core.cin) ⊆ (G0 :: K0.wires).toFinset := by
      intro q hq; rw [Finset.mem_singleton.mp (padding_wires 4 K0.core.cin hq)]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (by simp [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires]))
    have r0 := StairSqBodyB.bodyB_support44 hs (List.Sublist.refl _)
    simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
      lb_eq_K0, cb_eq_G0, wires_append, Finset.union_subset_iff] at r0
    simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
      wires_append, Finset.union_subset_iff]
    have heSup : wires efoldB ⊆ (G0 :: K0.wires).toFinset := by rw [← lb_eq_K0, ← cb_eq_G0]; exact efoldB_ok.2.1
    exact ⟨⟨f1, f2, ⟨r0.1.2.2.1.1, fl, r0.1.2.2.1.2.2.1, r0.1.2.2.1.2.2.2⟩, heSup, r0.1.2.2.2.2⟩, fpad⟩
  refine ⟨sup, ?_⟩
  intro base M hM hP hc hsum O hO hg hSource
  have hb : M ^ 2 < 2 ^ 256 := by simpa using square_bound M 128 hM
  have views := accA_views K0 hwK base M hM hP
  have v1 : K0.MeasuredFoldView base (negP K0) := views (.inl (negP K0)) (by simp [accAMix])
  have v2 : K0.MeasuredFoldView base (rot128F K0) := views (.inl (rot128F K0)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP K0) = M ^ 2 := by
    simp only [measuredFoldPayload, negP, pow_zero, Nat.mul_one]
    rw [K0.product_take_value hwK base (M ^ 2) hP 256 (by omega), Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F K0) = (M ^ 2 / 2 ^ 128) % 2 ^ 128 + 2 ^ 128 * (M ^ 2 % 2 ^ 128) := by
    simp only [measuredFoldPayload, rot128F, pow_zero, Nat.mul_one]
    exact K0.rotated128_value hwK base (M ^ 2) hP
  have f1 : ∀ O0, O0 < SquareReduction.p → Triple (SquareFrame K0.core.out base O0) dF1B
      (SquareFrame K0.core.out base ((M ^ 2 + (SquareReduction.p - 1 - O0)) % SquareReduction.p)) := by
    intro O0 hO0 s m hf
    have eq1 := directFold_rename_run foldPairsB (negP K0) (negP_count K0) (negP_length K0 hwK) rfl rfl
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).1, (foldPairsB_geom.2.2.2.1 ab hab).2.1⟩)
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).2.2.1, (foldPairsB_geom.2.2.2.1 ab hab).2.2.2.1⟩)
      base v1 hc O0 hO0 s m hf
    rw [dF1B, eq1]
    have h := directFoldQ_frameTq K0 hwK hn base (negP K0) v1 rfl hc (negP_length K0 hwK) rfl O0 hO0 s m hf
    rwa [pay1] at h
  have f2 : ∀ O0, O0 < SquareReduction.p → Triple (SquareFrame K0.core.out base O0) dF2B
      (SquareFrame K0.core.out base
        (((M ^ 2 / 2 ^ 128) % 2 ^ 128 + 2 ^ 128 * (M ^ 2 % 2 ^ 128) + (SquareReduction.p - 1 - O0)) % SquareReduction.p)) := by
    intro O0 hO0 s m hf
    have eq2 := directFold_rename_run foldPairsB (rot128F K0) (rot128F_count K0) (rot128F_length K0 hwK) rfl rfl
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).1, (foldPairsB_geom.2.2.2.1 ab hab).2.1⟩)
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).2.2.1, (foldPairsB_geom.2.2.2.1 ab hab).2.2.2.1⟩)
      base v2 hc O0 hO0 s m hf
    rw [dF2B, eq2]
    have h := directFoldQ_frameTq K0 hwK hn base (rot128F K0) v2 rfl hc (rot128F_length K0 hwK) rfl O0 hO0 s m hf
    rwa [pay2] at h
  have raw := StairSquareBBody.frameG StairSqBodyB.LB LowAccCarryDevelop.layout_widths hn StairSqBodyB.cB LowAccCarryDevelop.control_outside
    loopB (by rw [lb_eq_K0]; exact loopB_frame)
    efoldB (fun b clean O0 E0 hO0 => efoldB_ok.1 b clean O0 E0 hO0)
    LocalRebuild.improved
    (fun b outB clean O0 E0 B0 hb old => LocalRebuildLift.transfer b outB clean O0 E0 B0 hb old)
    base M hM (by rw [lb_eq_K0]; exact hP) (by rw [lb_eq_K0]; exact hc) (by rw [lb_eq_K0]; exact hsum) O hO
    (by rw [cb_eq_G0]; exact hg) (by rw [lb_eq_K0, cb_eq_G0]; exact hSource)
    dF1B dF2B (by rw [lb_eq_K0]; exact f1) (by rw [lb_eq_K0]; exact f2)
  rw [lb_eq_K0, cb_eq_G0] at raw
  show Triple _ (StairSquareBBody.bodyG K0 dF1B dF2B loopB efoldB LocalRebuild.improved ++
    ReorderedRecordPadding.program 4 K0.core.cin) _
  apply raw.seq
  intro t r ht
  have hz : t.basis K0.core.cin = false :=
    (ht.2 K0.core.cin (K0.pairAuxAway hn _ (by simp)).2).trans hc.cin
  rw [ReorderedRecordPadding.run_zero 4 K0.core.cin t r hz]
  exact ⟨rfl, ht⟩

theorem bodyB_avoids_workTB : ∀ q ∈ workTB, q ∉ wires bodyB := by
  intro q hq bad
  by_cases hD : q = D0
  · subst hD
    exact (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (List.mem_toFinset.mp (bodyB_ok.support bad))
  have hq31 : q ∈ workTB.take 31 := (by rw [workTB_lit, D0_eq]; decide +kernel : ∀ x ∈ workTB, x ≠ D0 → x ∈ workTB.take 31) q hq hD
  have hn := LowAccCarryDevelop.layout_nodup
  have a1 := hostRename_avoids foldPairsB (directFoldQTq K0 (negP K0)) foldPairsB_geom.1
    (fun ab hab => directFoldQ_free K0 hn (negP K0) (negP_count K0) ab.2 (by simp [directFree, (foldPairsB_geom.2.2.2.1 ab hab).2.2.1]))
  have a2 := hostRename_avoids foldPairsB (directFoldQTq K0 (rot128F K0)) foldPairsB_geom.1
    (fun ab hab => directFoldQ_free K0 hn (rot128F K0) (rot128F_count K0) ab.2 (by simp [directFree, (foldPairsB_geom.2.2.2.1 ab hab).2.2.1]))
  rw [foldPairsB_geom.2.1] at a1 a2
  have offEAdd : ∀ x ∈ workTB, x ∉ wires (ControlLoan1589BFFold.eAddLo K0) :=
    StairSquareBChecks.touchedAny_spec _ _
      (StairSquareBChecks.K2Hit.touchedAny_of_mask _ _ (by rw [workTB_lit, K0_eq]; decide +kernel))
  have offPark : ∀ x ∈ workTB, x ∉ wires (ParkCarryDevelop.program (ControlLoan1589BFFold.eU K0) K0.core.sumCarry) :=
    StairSquareBChecks.touchedAny_spec _ _
      (StairSquareBChecks.K2Hit.touchedAny_of_mask _ _ (by rw [workTB_lit, K0_eq]; decide +kernel))
  have offESub : ∀ x ∈ workTB, x ∉ wires (ControlLoan1589BFFold.eSubK K0) := fun x hx hw =>
    StairSquareBChecks.LT48B.disj_of_maskL _ _
      (by rw [workTB_lit, show StairSquareBChecks.LB = K0 from rfl, K0_eq]; decide +kernel) x hx
      (List.mem_toFinset.mp (StairSquareBChecks.eSubK_support (by rw [show StairSquareBChecks.LB = K0 from rfl]; exact hw)))
  have offReb : ∀ x ∈ workTB, x ∉ wires LocalRebuild.improved := by
    intro x hx hw
    have hact : x ∈ wires LocalRebuild.actual := LocalRebuildResources.support hw
    rw [LocalRebuild.literal, LocalRebuild.program] at hact
    simp only [wires_append, Finset.mem_union] at hact
    rcases hact with (((h | h) | (h | h)) | ((h | h) | (h | (h | h)))) | (((h | h) | (h | h)) | ((h | h) | (h | (h | h))))
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk0 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk1 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk2 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk3 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk4 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk5 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk6 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk7 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk8 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk9 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk10 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk11 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk12 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk13 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk14 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk15 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk16 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk17 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
  simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, wires_append, Finset.mem_union] at bad
  rcases bad with ((b | b | (b | b | b | b) | b | b) | b)
  · exact a1 q hq31 b
  · exact a2 q hq31 b
  · exact offEAdd q hq b
  · exact loopB_avoids_workTB q hq b
  · exact offPark q hq b
  · exact offESub q hq b
  · exact efoldB_avoids_workTB q hq b
  · exact offReb q hq b
  · exact (by rw [workTB_lit, K0_eq]; decide +kernel : ∀ x ∈ workTB, x ≠ K0.core.cin) q hq (Finset.mem_singleton.mp (padding_wires 4 K0.core.cin b))

theorem bodyB_avoids_hs : ∀ q ∈ hs, q ∉ wires bodyB := by
  intro q hq bad
  have sp1 := directFold_rename_support foldPairsB (negP K0) (negP_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have sp2 := directFold_rename_support foldPairsB (rot128F K0) (rot128F_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have h44 := StairSqBodyB.bodyB_avoids44 hs (List.Sublist.refl _) q hq
  simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
    StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, wires_append, Finset.mem_union, not_or] at h44
  simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, wires_append, Finset.mem_union] at bad
  rcases bad with ((b | b | (b | b | b | b) | b | b) | b)
  · rcases Finset.mem_union.mp (sp1 b) with h | h
    · exact h44.1.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).1 hq
  · rcases Finset.mem_union.mp (sp2 b) with h | h
    · exact h44.1.2.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).1 hq
  · exact h44.1.2.2.1.1 b
  · exact loopB_avoids_hs q hq b
  · exact h44.1.2.2.1.2.2.1 b
  · exact h44.1.2.2.1.2.2.2 b
  · exact efoldB_avoids_hs q hq b
  · exact h44.1.2.2.2.2 b
  · exact h44.2 b

theorem bodyB_normFlag : K0.core.normFlag ∉ wires bodyB := by
  have sp1 := directFold_rename_support foldPairsB (negP K0) (negP_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have sp2 := directFold_rename_support foldPairsB (rot128F K0) (rot128F_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have hnf := StairSqBodyB.bodyB_normFlag44 hs (List.Sublist.refl _)
    (StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.middle_norm _ (List.mem_singleton_self _))
  simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
    StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, wires_append, Finset.mem_union, not_or] at hnf
  intro bad
  simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, wires_append, Finset.mem_union] at bad
  rcases bad with ((b | b | (b | b | b | b) | b | b) | b)
  · rcases Finset.mem_union.mp (sp1 b) with h | h
    · exact hnf.1.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 _ (List.mem_toFinset.mp h)).2.1 rfl
  · rcases Finset.mem_union.mp (sp2 b) with h | h
    · exact hnf.1.2.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 _ (List.mem_toFinset.mp h)).2.1 rfl
  · exact hnf.1.2.2.1.1 b
  · exact loopB_normFlag b
  · exact hnf.1.2.2.1.2.2.1 b
  · exact hnf.1.2.2.1.2.2.2 b
  · exact efoldB_normFlag b
  · exact hnf.1.2.2.2.2 b
  · exact hnf.2 b

theorem bodyB_physical : GatePhysical bodyB := by
  have p0 := StairSqBodyB.bodyB_physical hs
  simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
    StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, gatePhysical_append] at p0
  simp only [bodyB, dF1B, dF2B, efoldB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, gatePhysical_append]
  exact ⟨⟨hostRename_physical _ _ p0.1.1, hostRename_physical _ _ p0.1.2.1,
    ⟨p0.1.2.2.1.1, hostRename_physical _ _ loopPCB_physical, p0.1.2.2.1.2.2.1, p0.1.2.2.1.2.2.2⟩,
    hostRename_physical _ _ StairSquareBEFoldK.efold_physical, p0.1.2.2.2.2⟩, p0.2⟩

theorem bodyB_counts :
    toffoliCount bodyB = toffoliCount B95PaddedResearch.body + 89 ∧
    measurementCount bodyB = measurementCount B95PaddedResearch.body := by
  have c0 := StairSqBodyB.bodyB_counts hs
  have cl_old := StairSqLoopB.loopB_counts hs
  have cl_new := loopB_counts
  have r1 := hostRename_counts foldPairsB (directFoldQTq K0 (negP K0))
  have r2 := hostRename_counts foldPairsB (directFoldQTq K0 (rot128F K0))
  have re := hostRename_counts efSwapB StairSquareBEFoldK.efold
  simp only [bodyB, dF1B, dF2B, efoldB, StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG,
    LowAccCarryDevelop.foldFor, StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, toffoliCount_append, measurementCount_append,
    r1.1, r1.2, r2.1, r2.2, re.1, re.2] at c0 ⊢
  exact ⟨by linarith only [c0.1, cl_old.1, cl_new.1], by linarith only [c0.2, cl_old.2, cl_new.2]⟩

theorem bodyB_slots : Challenge.gateSlots bodyB + 793 ≤ Challenge.gateSlots B95PaddedResearch.body := by
  have s0 := StairSqBodyB.bodyB_slots hs
  have sl_old := StairSqLoopB.loopB_slots hs
  have sl_new := loopB_slots
  have r1 := hostRename_slots foldPairsB (directFoldQTq K0 (negP K0))
  have r2 := hostRename_slots foldPairsB (directFoldQTq K0 (rot128F K0))
  have re := hostRename_slots efSwapB StairSquareBEFoldK.efold
  simp only [bodyB, dF1B, dF2B, efoldB, StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG,
    LowAccCarryDevelop.foldFor, StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, Challenge.gateSlots_append, r1, r2, re] at s0 ⊢
  linarith only [s0, sl_old, sl_new]

end BodyB

/-! ## Branch C body (`keepC` = 27 carries, avoids `workTC` and `hs`) -/

section BodyC
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq

private theorem lc_eq_K0 : C163Low4Middle.L = K0 := rfl

def keepC : List Wire := C105Research.keepK.filter (fun q => !workTC.contains q)

theorem keepC_geometry : keepC.Nodup ∧ keepC.length = 27 ∧
    (∀ q ∈ keepC, q ∈ C105Research.hosts) ∧
    (∀ q ∈ workTC, q ∉ keepC) ∧
    (∀ i, i < 44 → C163Low4Middle.hs.getD i 0 ∉ keepC) ∧
    (∀ q ∈ keepC, q ∈ allowedWires) := by
  have hall : ∀ q ∈ keepC, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [keepC, keepKC_fast, workTC_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [keepC, keepKC_fast, workTC_lit, hs_lit]; decide +kernel))
  have hr : keepC.Nodup ∧ keepC.length = 27 ∧
      (∀ q ∈ keepC, q ∈ C105Research.hosts) ∧
      (∀ q ∈ workTC, q ∉ keepC) ∧
      (∀ i, i < 44 → C163Low4Middle.hs.getD i 0 ∉ keepC) := by
    rw [keepC, keepKC_fast, hostsC105_fast, hsC_fast, workTC_lit]; decide +kernel
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, hall⟩

def rawFC : Program := ReorderedGenericCache.cachedAdd 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
def newFC : Program := C105Research.head ++ C105LowEraseResearch.clear ++ rawFC ++ C105Research.top
def newIC : Program := C105Research.preInv ++ ReorderedConsumedSub.consumed 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
def coreC : Program := (newFC ++ C105Research.M ++ newIC) ++ (C105LowEraseResearch.clear ++ C105Research.tail)
def restC : Program := C105LowEraseResearch.clear ++ rawFC ++ C105Research.top ++ C105Research.M ++ newIC ++ C105LowEraseResearch.clear ++ C105Research.tail
def loopPCC : Program := SignCHead.head ++ restC
def loopC : Program := hostRename (StairSqLoopC.pairs hs) loopPCC
def foldPairsC : List (Wire × Wire) := workTC.zip (K0.core.pad.take 34)
def dFC : Program := hostRename foldPairsC (directFoldQTq K0 (negRot K0))
def bodyC : Program := (dFC ++ loopC) ++ ReorderedRecordPadding.program 7 K0.core.cin
def bodyCPlain : Program := C105SignResearch.directBody loopC

theorem foldPairsC_geom :
    (holesOf foldPairsC ++ hostsOf foldPairsC).Nodup ∧
    holesOf foldPairsC = workTC ∧
    hostsOf foldPairsC = K0.core.pad.take 34 ∧
    (∀ ab ∈ foldPairsC, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out ∧ ab.2 ∈ allowedWires) ∧
    (∀ q ∈ hostsOf foldPairsC, q ∉ hs ∧ q ∈ K0.wires ∧ q ∈ allowedWires) := by
  have hall : ∀ q ∈ hostsOf foldPairsC, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsC, workTC_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [foldPairsC, workTC_lit, K0_eq, hs_lit]; decide +kernel))
  have hK : ∀ q ∈ hostsOf foldPairsC, q ∈ K0.wires :=
    StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsC, workTC_lit, K0_eq]; decide +kernel)
  have hr : (holesOf foldPairsC ++ hostsOf foldPairsC).Nodup ∧
      holesOf foldPairsC = workTC ∧
      hostsOf foldPairsC = K0.core.pad.take 34 ∧
      (∀ ab ∈ foldPairsC, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out) ∧
      (∀ q ∈ hostsOf foldPairsC, q ∉ hs) := by rw [foldPairsC, workTC_lit, K0_eq, hs_lit]; decide +kernel
  refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_, ?_⟩
  · intro ab hab; have h := hr.2.2.2.1 ab hab
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hall ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩)⟩
  · intro q hq; exact ⟨hr.2.2.2.2 q hq, hK q hq, hall q hq⟩

private theorem keepC_sub (q : Wire) (hq : q ∈ keepC) : q ∈ C105Research.hosts := keepC_geometry.2.2.1 q hq

private theorem core_plainC (s : State) (m : List Bool)
    (hz : ∀ q ∈ C105PrefixResearch.pad, s.basis q = false) (hb : ∀ q ∈ C105PrefixResearch.bank, s.basis q = false)
    (hi : s.basis C105PrefixResearch.cin = false) (ha : regValue C105PrefixResearch.acc s.basis = 0)
    (zero : ∀ q ∈ ReorderedCFixed.hosts, s.basis q = false)
    (after : WReady C105PrefixResearch.acc C105PrefixResearch.pad C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src
      (regValue C105PrefixResearch.src s.basis) (middleState C105Research.oldF C105Research.oldM s m))
    (flag : (run C105Research.oldF (m.take (measurementCount C105Research.oldF)) s).basis 4762 = false) :
    run coreC m s = run (C105Research.oldF ++ C105Research.oldM ++
      ReorderedCPlain.unbuild C105PrefixResearch.acc C105PrefixResearch.pad C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src) m s := by
  let H := regValue C105PrefixResearch.src s.basis
  let vs := ReorderedCacheBits.values 4 27 H (976 * H / 1024)
  have keepSubK (q : Wire) (hq : q ∈ keepC) : q ∈ C105Research.keepK := (List.mem_filter.mp hq).1
  have fwdM : measurementCount newFC = measurementCount C105Research.F := by
    have h := (ReorderedGenericCache.count_balance 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide)).2.1
    simp only [newFC, rawFC, C105Research.F, C105Research.rawF, measurementCount_append]; rw [h]
  have invM : measurementCount newIC = measurementCount C105Research.I := by
    have h := ReorderedConsumedSub.measurement_eq 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide)
    simp only [newIC, C105Research.I, C105Research.rawI, measurementCount_append]; rw [h]
  have fwdVal : (((C105Research.cs.drop 4).take 27).map (run (carryPrefix (4 + 27) C105Research.xs C105Research.ys C105Research.cs C105PrefixResearch.cin) []
      (run (C105Research.head ++ C105LowEraseResearch.clear)
        ((m.take (measurementCount C105Research.F)).take (measurementCount (C105Research.head ++ C105LowEraseResearch.clear))) s)).basis) = vs := by
    let m0 := (m.take (measurementCount C105Research.F)).take (measurementCount (C105Research.head ++ C105LowEraseResearch.clear))
    let u := run C105Research.head m0 s
    let t := run (C105Research.head ++ C105LowEraseResearch.clear) m0 s
    have te : t = C105LowEraseResearch.erase u := C105Research.prefix_erased s m0 hz hb hi ha
    have hH : H < 2 ^ 130 := by simpa only [H, C105PrefixResearch.source_length] using regValue_lt C105PrefixResearch.src s.basis
    have ready := CHeadArithmeticResearch.ready C105PrefixResearch.acc C105PrefixResearch.pad C105PrefixResearch.bank
      C105PrefixResearch.cin C105PrefixResearch.src C105PrefixResearch.acc_length C105PrefixResearch.source_length C105PrefixResearch.fits s m0 hz hb hi ha
    have eb (q : Wire) (hq : q ∈ C105Research.domain) : t.basis q = u.basis q := by
      rw [te]; exact C105LowEraseResearch.bit_same _ q (C105Research.domain_away_low q hq)
    have er (r : List Wire) (sub : ∀ q ∈ r, q ∈ C105Research.domain) : regValue r t.basis = regValue r u.basis :=
      regValue_congr _ _ _ (fun q hq => eb q (sub q hq))
    exact ReorderedCacheBits.forward_values 4 27 H (((2 ^ 140 - 48 * H) % 2 ^ 140) / 1024) (976 * H / 1024)
      C105Research.xs C105Research.ys C105Research.cs C105PrefixResearch.cin t
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide) C105Research.raw_nd
      (fun q hq => (eb q (C105Research.c_in q hq)).trans (ready.1 q hq))
      ((eb _ C105Research.cin_in).trans ready.2.1)
      ((er _ C105Research.x_in).trans ready.2.2.1)
      ((er _ C105Research.y_in).trans ready.2.2.2)
      (fun j hj => by simpa only [show 130 + 10 = 140 by decide] using ReorderedCacheArithmetic.high_add_low 130 (4 + j + 1) H (by omega) hH)
  have forward : run newFC (m.take (measurementCount C105Research.F)) s =
      scatterState keepC vs (run C105Research.F (m.take (measurementCount C105Research.F)) s) := by
    have h := CacheBetweenFrameResearch.forward (C105Research.head ++ C105LowEraseResearch.clear) C105Research.top
      27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide) keepC_geometry.1
      (fun q hq bad => C105Research.geometry.2.2 q (keepC_sub q hq) (by clear * - bad; simp only [C105Research.domain, List.mem_cons, List.mem_append] at bad ⊢; tauto))
      (fun q hq => C105Research.rawF_off q (keepC_sub q hq)) (fun q hq => C105Research.top_off q (keepC_sub q hq))
      s (m.take (measurementCount C105Research.F))
      (fun q hq => C105Research.prefix_zeroK s _ hz hb hi ha zero q (keepSubK q hq))
    rw [fwdVal] at h; exact h
  have mid := C105Research.middle_erased s m hz hb hi ha after flag
  have cacheEq : run (newFC ++ C105Research.M ++ newIC) m s = run (C105Research.F ++ C105Research.M ++ C105Research.I) m s := by
    apply CacheFromCleanForwardResearch.equivalent C105Research.F newFC C105Research.M C105Research.I newIC keepC vs
      fwdM (fun q hq => C105Research.middle_fresh q (keepC_sub q hq))
      (fun q hq => C105Research.I_off q (keepC_sub q hq)) keepC_geometry.1 s m
      (fun q hq => C105Research.forward_zeroK s _ hz hb hi ha zero q (keepSubK q hq)) forward
    rw [mid]
    let ms := middleState C105Research.oldF C105Research.oldM s m
    let mr := m.drop (measurementCount C105Research.F + measurementCount C105Research.M)
    let t := scatterState keepC vs (C105LowEraseResearch.erase ms)
    have comm : run C105Research.preInv mr t = scatterState keepC vs (C105LowEraseResearch.erase (run C105Research.preInv mr ms)) := by
      rw [show t = scatterState keepC vs (C105LowEraseResearch.erase ms) from rfl,
        run_scatter C105Research.preInv keepC vs _ _ (fun q hq => C105Research.preInv_off q (keepC_sub q hq)),
        C105LowEraseResearch.commute C105Research.preInv mr ms (fun q hq => C105Research.preInv_off q (C105Research.low_hosts q hq))]
    have bits (q : Wire) (hq : q ∈ C105Research.domain) : (run C105Research.preInv mr t).basis q = (run C105Research.preInv mr ms).basis q := by
      rw [comm, scatter_outside keepC vs _ q (fun bad => C105Research.geometry.2.2 q (keepC_sub q bad) hq)]
      exact C105LowEraseResearch.bit_same _ q (C105Research.domain_away_low q hq)
    have regs (r : List Wire) (sub : ∀ q ∈ r, q ∈ C105Research.domain) :
        regValue r (run C105Research.preInv mr t).basis = regValue r (run C105Research.preInv mr ms).basis :=
      regValue_congr _ _ _ (fun q hq => bits q (sub q hq))
    have rr := C105Research.pre_raw_ready H ms mr after
    have saved : keepC.map t.basis = vs := scatter_saved_map keepC vs _ keepC_geometry.1
      (by simp only [vs, ReorderedCacheBits.values, List.length_map, keepC_geometry.2.1, List.length_range])
    have same : keepC.map (run C105Research.preInv mr t).basis = keepC.map t.basis :=
      List.map_congr_left (fun q hq => run_preserves_outside C105Research.preInv mr t q (C105Research.preInv_off q (keepC_sub q hq)))
    simp only [newIC, C105Research.I, C105Research.rawI, ControlledBorrowResearch.run_cat]
    exact ReorderedConsumedSub.frame 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide)
      (by rw [C105Research.raw_lengths.1, C105Research.raw_lengths.2.1])
      (by rw [C105Research.raw_lengths.2.1, C105Research.raw_lengths.2.2])
      C105Research.raw_nd keepC_geometry.1 keepC_geometry.2.1 (fun q hq => C105Research.geometry.2.2 q (keepC_sub q hq))
      (run C105Research.preInv mr t) _ (fun q hq => (bits q (C105Research.c_in q hq)).trans (rr.1 q hq))
      ((bits _ C105Research.cin_in).trans rr.2.1) H (976 * H / 1024)
      ((regs _ C105Research.x_in).trans rr.2.2.1) ((regs _ C105Research.y_in).trans rr.2.2.2) (same.trans saved)
  have eq := ClearContextResearch.append_at (newFC ++ C105Research.M ++ newIC)
    (C105Research.F ++ C105Research.M ++ C105Research.I) (C105LowEraseResearch.clear ++ C105Research.tail) s m
    (by simp only [measurementCount_append, fwdM, invM]) cacheEq
  have shape : (C105Research.F ++ C105Research.M ++ C105Research.I) ++ (C105LowEraseResearch.clear ++ C105Research.tail) =
      C105Research.F ++ C105Research.M ++ (C105Research.I ++ C105LowEraseResearch.clear ++ C105Research.tail) := by
    have g (A B C D E : Program) : (A ++ B ++ C) ++ (D ++ E) = A ++ B ++ (C ++ D ++ E) := by simp only [List.append_assoc]
    exact g _ _ _ _ _
  exact eq.trans ((congrArg (fun P => run P m s) shape).trans (C105Research.plain_loop s m hz hb hi ha after flag))

private theorem coreC_frame (base : BasisState) (hc : C163Low4Middle.L.PairClean base)
    (hp : base C163Low4Middle.p = false) (hd : base C163Low4Middle.d = false) (O : Nat) (hO : O < SquareReduction.p) :
    Triple (SquareFrame C163Low4Middle.L.core.out base O) coreC
      (SquareFrame C163Low4Middle.L.core.out base
        (((if base C163Low4Middle.g then C163Low4Facts.Klow - C163Fold.payload C163Low4Middle.L base
           else C163Fold.payload C163Low4Middle.L base) + (SquareReduction.p - 1 - O)) % SquareReduction.p)) := by
  intro s m hf
  have len := C163Low4Middle.lengths; have fit := C163Low4Middle.fits
  have clean := C163Low4Middle.L.squareFrame_clean C163Low4Middle.hn base s.basis O hf hc
  have hz : ∀ u ∈ C163Low4Middle.pad, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
  have hb : ∀ u ∈ C163Low4Middle.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
  have ha : regValue C163Low4Middle.ga s.basis = 0 := C163Low4Ghost.ghostAcc_zero C163Low4Middle.L s.basis clean
  have zeroU : ∀ u ∈ C163Low4Middle.hs, s.basis u = false := StairSqLoopC.hs_zero base hc hd O s hf
  have zeroOld : ∀ u ∈ ReorderedCFixed.hosts, s.basis u = false := by
    have qz : s.basis C163Low4Middle.q = false := (regValue_zero _ _).mp clean.work C163Low4Middle.q (by decide)
    have rz : s.basis C163Low4Middle.r = false := (regValue_zero _ _).mp clean.work C163Low4Middle.r (by decide)
    have pz : s.basis C163Low4Middle.p = false := (hf.2 C163Low4Middle.p (by decide)).trans hp
    intro u hu; simp only [ReorderedCFixed.hosts, List.mem_cons] at hu
    rcases hu with rfl | rfl | rfl | hu; exact qz; exact rz; exact pz; exact zeroU u hu
  have offHs : ∀ u ∈ C163Low4Middle.hs, u ∉ wires (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) :=
    fun u hu => (ReorderedCFixed.off_plain u (StairSqLoopC.hosts_of_hs u hu)).1
  have goodOld := fun record => C163Low4Middle.good base hc O hO s record hf
  have goodSpecial : WReady C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
      (regValue C163Low4Middle.src s.basis)
      (middleState (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) C163Low4Middle.specialChecked.out s m) := by
    rw [ReorderedRetape.c_middle_eq C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
      C163Low4Middle.specialChecked.out len.1 len.2.2.2 fit s m hz hb clean.cin ha]
    exact goodOld _
  have middleEq := C163Low4Middle.bank_cert.middle_eq C163Low4Middle.hs C163Low4Middle.specialChecked.out C163Low4Middle.bankChecked.out
    (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) s m zeroU offHs
  have knownEq := CKKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
  have goodKnown : WReady C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
      (regValue C163Low4Middle.src s.basis)
      (middleState (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) KnownCMidStaged.body s m) := by
    rw [knownEq, middleEq]; exact goodSpecial
  have buildFrame := ReorderedCPlain.build_triple C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
    len.1 len.2.2.2 fit s.basis hz hb clean.cin s
    (m.take (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src))) ⟨ha, fun _ _ => rfl⟩
  have flag : (run (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
      (m.take (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src))) s).basis 4762 = false :=
    (buildFrame.2.2 4762 (by simp only [C163Low4Middle.ga, C163Low4Middle.pad, C163Low4Middle.bank, C163Low4Middle.src, C163Low4Middle.L, C163Middle.L, show Baselines.layout.dialogStreamedSquareWide = K0 from rfl, K0_eq]; decide +kernel)).trans clean.modFlag
  have plainNew := core_plainC s m hz hb clean.cin ha zeroOld goodKnown flag
  have midEq : run KnownCMidStaged.body (m.drop (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)))
      (run (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) m s) =
      run C163Low4Middle.bankChecked.out (m.drop (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)))
      (run (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) m s) := by
    simpa only [middleState, run_take] using knownEq
  have ctxt := ReorderedKnownA.context_eq (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
    C163Low4Middle.bankChecked.out KnownCMidStaged.body (ReorderedCPlain.unbuild C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
    s m CKKnownMiddleResearch.measurements midEq
  have middleReplace := C163Low4Middle.bank_cert.surround_eq C163Low4Middle.hs C163Low4Middle.specialChecked.out C163Low4Middle.bankChecked.out
    (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
    (ReorderedCPlain.unbuild C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) s m zeroU offHs
  have plainEq := ReorderedRetape.c_loop_eq C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src C163Low4Middle.specialChecked.out
    len.1 len.2.2.2 fit s m hz hb clean.cin ha goodOld
  let record := ReorderedRetape.tape (measurementCount (C163NarrowAcc.build8 C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src))
    (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)) m
  have oldFrame := C163Low4Middle.frame base hc hp hd O hO s record hf
  rw [C163Low4Middle.eq_plain base hc hp hd O hO s record hf] at oldFrame
  exact ReorderedCFixed.transport _ s _ _ (plainNew.trans (ctxt.trans (middleReplace.trans plainEq))) oldFrame

private theorem keepC_cached_wires : wires rawFC ⊆ C105Research.domain.toFinset ∪ keepC.toFinset :=
  (ReorderedSupport.cached 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
    (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
    (by rw [C105Research.raw_lengths.2.2]; decide)
    (by rw [C105Research.raw_lengths.1, C105Research.raw_lengths.2.1])
    (by rw [C105Research.raw_lengths.2.1, C105Research.raw_lengths.2.2])).1

private theorem keepC_consumed_wires :
    wires (ReorderedConsumedSub.consumed 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin) ⊆
      C105Research.domain.toFinset ∪ keepC.toFinset :=
  ReorderedSupport.consumed 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
    (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
    (by rw [C105Research.raw_lengths.2.2]; decide)
    (by rw [C105Research.raw_lengths.1, C105Research.raw_lengths.2.1])
    (by rw [C105Research.raw_lengths.2.1, C105Research.raw_lengths.2.2])

theorem loopPCC_off (h : Wire) (hh : h ∈ ReorderedCFixed.hosts) (hk : h ∉ keepC) : h ∉ wires loopPCC := by
  have hA : h ∈ C105Research.hosts := List.mem_append.mpr (Or.inl hh)
  have hb : h ∉ wires (ReorderedCPlain.build C105PrefixResearch.acc C105PrefixResearch.pad
      C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src) := (ReorderedCFixed.off_plain h hh).1
  rw [C105Research.plain_split] at hb
  simp only [wires_append, Finset.mem_union, not_or] at hb
  have ht : h ∉ wires (ReorderedCPlain.unbuild C105PrefixResearch.acc C105PrefixResearch.pad
      C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src) := (ReorderedCFixed.off_plain h hh).2
  rw [C105Research.unbuild_split] at ht
  simp only [wires_append, Finset.mem_union, not_or] at ht
  have clearOff : h ∉ wires C105LowEraseResearch.clear := by
    rw [StairSqLoopC.clear_wires]; intro bad
    exact C105Research.old_away h hh ((by decide : ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire) ⊆ C105Research.ports) (List.mem_toFinset.mp bad))
  have out : h ∉ C105Research.domain.toFinset ∪ keepC.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]; exact ⟨C105Research.geometry.2.2 h hA, hk⟩
  simp only [loopPCC, restC, newIC, wires_append, Finset.mem_union, not_or, and_assoc]
  exact ⟨fun bad => hb.1 (SignCHeadSupport.support bad), clearOff, fun bad => out (keepC_cached_wires bad),
    C105Research.top_off h hA, C105Research.middle_fresh h hA, C105Research.preInv_off h hA,
    fun bad => out (keepC_consumed_wires bad), clearOff, ht.2⟩

theorem loopPCC_support : wires loopPCC ⊆ C105Research.S := by
  have hh : wires SignCHead.head ⊆ C105Research.S := by
    apply Finset.Subset.trans ?_ C105Research.old_prefix_support
    rw [C105Research.oldPrefix, wires_append]
    exact Finset.subset_union_left
  have ks : C105Research.domain.toFinset ∪ keepC.toFinset ⊆ C105Research.S := by
    intro q hq; apply C105Research.raw_domain_in
    simp only [Finset.mem_union, List.mem_toFinset] at hq ⊢
    rcases hq with h | h; exact Or.inl h; exact Or.inr (keepC_sub q h)
  simp only [loopPCC, restC, newIC, wires_append, Finset.union_subset_iff]
  exact ⟨hh,
    ⟨⟨⟨⟨⟨⟨C105Research.clear_support, keepC_cached_wires.trans ks⟩, C105Research.endpoint_support.1⟩,
      C105Research.middle_support⟩, ⟨C105Research.endpoint_support.2.1, keepC_consumed_wires.trans ks⟩⟩,
      C105Research.clear_support⟩, C105Research.endpoint_support.2.2⟩⟩

theorem loopPCC_physical : GatePhysical loopPCC := by
  have f := ReorderedPhysical.cached 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
    (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
    (by rw [C105Research.raw_lengths.2.2]; decide)
    C105Research.raw_nd (fun q hq bad => C105Research.geometry.2.2 q (keepC_sub q hq) (C105Research.c_in q bad))
  have n := notRegister_physical C105Research.ys
  simp only [loopPCC, restC, newIC, ReorderedConsumedSub.consumed, gatePhysical_append]
  exact ⟨SignCHeadResources.physical,
    ⟨⟨⟨⟨⟨⟨C105LowEraseResearch.physical, f.1⟩, C105Research.endpoint_physical.1⟩,
      CKAliasesResearch.physical⟩, ⟨C105Research.endpoint_physical.2.1, ⟨⟨n, f.2⟩, n⟩⟩⟩,
      C105LowEraseResearch.physical⟩, C105Research.endpoint_physical.2.2⟩⟩

theorem loopC_pairs_free : ∀ ab ∈ StairSqLoopC.pairs hs, ab.2 ∉ wires loopPCC := by
  intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
  apply loopPCC_off _ (StairSqLoopC.hosts_of_hs _ (StairSqLoopC.holes_geometry44.2.2 y hy))
  have h := List.idxOf_lt_length_of_mem hy; rw [StairSqLoopA.hostDomain_length44] at h
  exact keepC_geometry.2.2.2.2.1 _ h

theorem loopC_support : wires loopC ⊆ C105Research.S := by
  intro q hq
  have sub := hostRename_support (StairSqLoopC.pairs hs) loopPCC (StairSqLoopC.pairs_nodup44 hs (List.Sublist.refl _)) loopC_pairs_free hq
  rcases Finset.mem_union.mp sub with h | h
  · exact loopPCC_support (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopC.pairs_snd] at h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact C105Research.raw_domain_in (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (StairSqLoopC.hosts_of_hs _ (StairSqLoopC.holes_geometry44.2.2 y hy))))))

theorem loopC_avoids_hs : ∀ q ∈ hs, q ∉ wires loopC := by
  intro q hq
  have h := hostRename_avoids (StairSqLoopC.pairs hs) loopPCC (StairSqLoopC.pairs_nodup44 hs (List.Sublist.refl _)) loopC_pairs_free
  rw [StairSqLoopC.pairs_fst] at h; exact h q hq

theorem loopC_avoids_workTC : ∀ q ∈ workTC, q ∉ wires loopC := by
  intro q hq bad
  have sub := hostRename_support (StairSqLoopC.pairs hs) loopPCC (StairSqLoopC.pairs_nodup44 hs (List.Sublist.refl _)) loopC_pairs_free bad
  rcases Finset.mem_union.mp sub with h | h
  · have hm : ∀ x ∈ workTC, x ∈ ReorderedCFixed.hosts := by rw [workTC_lit, hostsCFix_fast]; decide +kernel
    exact loopPCC_off q (hm q hq) (keepC_geometry.2.2.2.1 q hq) (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopC.pairs_snd] at h
    have dis : ∀ x ∈ workTC, x ∉ hs.map StairSqLoopC.hostOf := by simp only [workTC_lit, StairSqLoopC.hostOf, show StairSqLoopA.hostDomain = hs from rfl, hs_lit, hsC_fast]; decide +kernel
    exact dis q hq (List.mem_toFinset.mp h)

theorem loopC_counts :
    toffoliCount loopC = toffoliCount C105SignResearch.loop + 81 ∧
    measurementCount loopC = measurementCount C105SignResearch.loop := by
  have hr := hostRename_counts (StairSqLoopC.pairs hs) loopPCC
  have rel : toffoliCount loopPCC + 27 = toffoliCount StairSqLoopC.loopNC ∧
      measurementCount loopPCC = measurementCount StairSqLoopC.loopNC := by
    have cb := ReorderedGenericCache.count_balance 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide) (by rw [C105Research.raw_lengths.2.2]; decide)
    rw [loopPCC, restC, rawFC, newIC, StairSqLoopC.loopNC, StairSqLoopC.suffixNC,
      C105Research.I, C105Research.rawI, C105Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [toffoliCount_append, measurementCount_append]
    exact ⟨by omega, by omega⟩
  have nc := StairSqLoopC.loopNC_counts
  rw [loopC, hr.1, hr.2]
  exact ⟨by omega, by omega⟩

theorem loopC_slots : Challenge.gateSlots loopC = Challenge.gateSlots C105SignResearch.loop + 237 := by
  have hr := hostRename_slots (StairSqLoopC.pairs hs) loopPCC
  have rel : Challenge.gateSlots loopPCC + 81 = Challenge.gateSlots StairSqLoopC.loopNC := by
    have sc := ReorderedSlots.cache 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide) keepC_geometry.2.1
    rw [loopPCC, restC, rawFC, newIC, StairSqLoopC.loopNC, StairSqLoopC.suffixNC,
      C105Research.I, C105Research.rawI, C105Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [Challenge.gateSlots_append]
    omega
  have nc := StairSqLoopC.loopNC_slots
  rw [loopC, hr]
  omega

theorem loopC_frame : C105SignResearch.DirectLoopFrame loopC := by
  have pcFrame : C105SignResearch.DirectLoopFrame loopPCC := by
    intro base hc hp hd O hO s m hf
    have clean := C163Low4Middle.L.squareFrame_clean C163Low4Middle.hn base s.basis O hf hc
    have hz : ∀ u ∈ C163Low4Middle.pad, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
    have hb : ∀ u ∈ C163Low4Middle.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
    have ha : regValue C163Low4Middle.ga s.basis = 0 := C163Low4Ghost.ghostAcc_zero C163Low4Middle.L s.basis clean
    have hhead : ∀ a b : List Bool, run SignCHead.head a s = run (ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) b s :=
      fun a b => ReorderedFrameUnique.program_eq C163Low4Middle.ga s.basis 0 ((2 ^ 140 - 48 * regValue C163Low4Middle.src s.basis) % 2 ^ 140) _ _
        (SignCHead.frame s.basis hz hb clean.cin)
        (ReorderedCHead.head_triple C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src C163Low4Middle.lengths.1 C163Low4Middle.lengths.2.2.2.le C163Low4Middle.fits s.basis hz hb clean.cin)
        s a b ⟨ha, fun _ _ => rfl⟩
    have eq := SignRetape.replace SignCHead.head (ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) restC s m hhead
    have hheadEq : C105Research.head = ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src := rfl
    have hcoreEq : coreC = ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src ++ restC := by
      rw [coreC, newFC, restC, hheadEq]
      have g (A B C D E F G H : Program) : (((A ++ B ++ C ++ D) ++ E ++ F) ++ (G ++ H)) = A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H) := by simp only [List.append_assoc]
      exact g _ _ _ _ _ _ _ _
    have eq' : run loopPCC m s = run coreC (SignRetape.tape SignCHead.head (ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) m) s := by
      rw [loopPCC, hcoreEq]; exact eq
    exact ReorderedCFixed.transport _ s _ _ eq' (coreC_frame base hc hp hd O hO s _ hf)
  intro base hc hp hd O hO s m hf
  have r := pcFrame base hc hp hd O hO s m hf
  have hEq : run loopC m s = run loopPCC m s := by
    apply hostRename_run_eq (StairSqLoopC.pairs hs) loopPCC s m
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      have hg := StairSqLoopC.holes_geometry44.2.1 y hy
      exact (hf.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact StairSqLoopC.hs_zero base hc hd O s hf _ (StairSqLoopC.holes_geometry44.2.2 y hy)
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      have hg := StairSqLoopC.holes_geometry44.2.1 y hy
      exact (r.2.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · exact loopC_pairs_free
  rw [hEq]; exact r

theorem bodyC_wires_plain : wires bodyC ⊆ wires bodyCPlain ∪ (K0.core.pad.take 34).toFinset := by
  have sp := directFold_rename_support foldPairsC (negRot K0) (negRot_count K0) foldPairsC_geom.1 (fun ab hab => (foldPairsC_geom.2.2.2.1 ab hab).2.2.1)
  rw [foldPairsC_geom.2.2.1] at sp
  intro q hq
  simp only [bodyC, wires_append, Finset.mem_union] at hq
  rcases hq with (b | b) | b
  · rcases Finset.mem_union.mp (sp b) with h | h
    · exact Finset.mem_union_left _ (by simp only [bodyCPlain, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, wires_append, Finset.mem_union]; left; left; exact (Finset.mem_sdiff.mp h).1)
    · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ (by simp only [bodyCPlain, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, wires_append, Finset.mem_union]; left; right; exact b)
  · exact Finset.mem_union_left _ (by simp only [bodyCPlain, C105SignResearch.directBody, wires_append, Finset.mem_union]; right; exact b)

theorem bodyC_ok : BodyCOK bodyC := by
  have s0 : wires bodyCPlain ⊆ insert D0 (G0 :: K0.wires).toFinset := by
    have h := C105SignResearch.direct_body_coarse_S loopC loopC_support
    rw [lc_eq_K0] at h
    exact h
  refine ⟨?_, ?_⟩
  · intro q hq; rcases Finset.mem_union.mp (bodyC_wires_plain hq) with h | h
    · exact s0 h
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsC_geom.2.2.2.2 q (by rw [foldPairsC_geom.2.2.1]; exact List.mem_toFinset.mp h)).2.1))
  · intro base M hP hc hg hd O hO s m hf
    have rawRef := C105SignResearch.direct_body_frame loopC loopC_frame base M hP hc hg hd O hO s m hf
    have views := accC_views K0 hwK base M hP
    have hv : K0.MeasuredFoldView base (negRot K0) := views (.inl (negRot K0)) (by simp [accCMix])
    have mc : measurementCount dFC = measurementCount (directFoldQTq K0 (negRot K0)) := (hostRename_counts foldPairsC (directFoldQTq K0 (negRot K0))).2
    have eq1 : run dFC m s = run (directFoldQTq K0 (negRot K0)) m s :=
      directFold_rename_run foldPairsC (negRot K0) (negRot_count K0) (negRot_length K0 hwK) rfl rfl
        (fun ab hab => ⟨(foldPairsC_geom.2.2.2.1 ab hab).1, (foldPairsC_geom.2.2.2.1 ab hab).2.1⟩)
        (fun ab hab => ⟨(foldPairsC_geom.2.2.2.1 ab hab).2.2.1, (foldPairsC_geom.2.2.2.1 ab hab).2.2.2.1⟩)
        base hv hc O hO s m hf
    have bodyEq : run bodyC m s = run bodyCPlain m s := by
      simp only [bodyC, bodyCPlain, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
        ControlledBorrowResearch.run_cat, measurementCount_append, mc]
      rw [eq1]
    rw [bodyEq]; exact rawRef

theorem bodyC_avoids_workTC : ∀ q ∈ workTC, q ∉ wires bodyC := by
  intro q hq bad
  have hn := (List.nodup_cons.mp controlND).2
  have a1 := hostRename_avoids foldPairsC (directFoldQTq K0 (negRot K0)) foldPairsC_geom.1
    (fun ab hab => directFoldQ_free K0 hn (negRot K0) (negRot_count K0) ab.2 (by simp [directFree, (foldPairsC_geom.2.2.2.1 ab hab).2.2.1]))
  rw [foldPairsC_geom.2.1] at a1
  simp only [bodyC, wires_append, Finset.mem_union] at bad
  rcases bad with (b | b) | b
  · exact a1 q hq b
  · exact loopC_avoids_workTC q hq b
  · exact (by rw [workTC_lit, K0_eq]; decide +kernel : ∀ x ∈ workTC, x ≠ K0.core.cin) q hq (Finset.mem_singleton.mp (padding_wires 7 K0.core.cin b))

theorem bodyC_avoids_hs : ∀ q ∈ hs, q ∉ wires bodyC := by
  intro q hq bad
  rcases Finset.mem_union.mp (bodyC_wires_plain bad) with h | h
  · exact C105SignResearch.direct_body_holes loopC hs (fun x hx => (StairSqLoopC.holes_geometry44.2.1 x hx).1) loopC_avoids_hs q hq h
  · exact (foldPairsC_geom.2.2.2.2 q (by rw [foldPairsC_geom.2.2.1]; exact List.mem_toFinset.mp h)).1 hq

theorem bodyC_physical : GatePhysical bodyC := by
  have p0 := C105SignResearch.direct_body_physical loopC (hostRename_physical _ _ loopPCC_physical)
  simp only [C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, gatePhysical_append] at p0
  simp only [bodyC, dFC, gatePhysical_append]
  exact ⟨⟨hostRename_physical _ _ p0.1.1, p0.1.2⟩, p0.2⟩

theorem bodyC_counts :
    toffoliCount bodyC = toffoliCount C105SignResearch.body + 81 ∧
    measurementCount bodyC = measurementCount C105SignResearch.body := by
  have c0 := C105SignResearch.direct_body_counts loopC
  have cl := loopC_counts
  have r1 := hostRename_counts foldPairsC (directFoldQTq K0 (negRot K0))
  have eqT : toffoliCount bodyC = toffoliCount (C105SignResearch.directBody loopC) := by
    simp only [bodyC, dFC, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
      toffoliCount_append, r1.1]
  have eqM : measurementCount bodyC = measurementCount (C105SignResearch.directBody loopC) := by
    simp only [bodyC, dFC, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
      measurementCount_append, r1.2]
  rw [eqT, eqM]
  exact ⟨by omega, by omega⟩

theorem bodyC_slots : Challenge.gateSlots bodyC + 275 = Challenge.gateSlots C105SignResearch.body := by
  have s0 := C105SignResearch.direct_body_slots loopC
  have sl := loopC_slots
  have r1 := hostRename_slots foldPairsC (directFoldQTq K0 (negRot K0))
  have eqS : Challenge.gateSlots bodyC = Challenge.gateSlots (C105SignResearch.directBody loopC) := by
    simp only [bodyC, dFC, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
      Challenge.gateSlots_append, r1]
  rw [eqS]
  omega

theorem bodyCPlain_fine :
    wires bodyCPlain ⊆ insert C163Low4Middle.d
      (wires (OwnDiagAll12Square.bodyCKTq C163Low4Middle.L C163Low4Middle.g)) :=
  C105SignResearch.direct_body_fine_S loopC loopC_support

end BodyC

/-! ## Branch wrappers (`brC`, `brB`, `brA`) and top-level assembly -/

section Branches
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical LocalRebuild.improved directFoldQTq

/-- Generic parked-copy split-65 wrapper around any `SplitCfg` and body. -/
def withSplitPark (c : SplitCfg) (keepBits : Nat) (parkHosts : List Wire) (body : Program) : Program :=
  copyRegister (some G0) c.src c.bank ++
  c.make ++
  eraseMask G0 (c.src.take keepBits) (c.bank.take keepBits) ++
  ParkCopy.dummies parkHosts ++
  ParkCopy.move (c.bank.drop keepBits) parkHosts ++
  renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body) ++
  CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits) ++
  ParkCopy.move parkHosts (c.bank.drop keepBits) ++
  c.clear ++
  eraseMask G0 c.src c.bank

def brC : Program :=
  OwnDiagAll12Square.gPrep K0 ++
  withSplitPark cfgC 124 (ParkCopyS.hostsS E0) bodyC ++
  OwnDiagAll12Square.gClear K0

def brB : Program :=
  withSplitPark cfgB 119 (ParkCopy.hosts E0) bodyB

def brA : Program :=
  withSplitPark cfgA 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA

private theorem pull_swap_invol (a b : Wire) (s : State) :
    pullState (Equiv.swap a b) (pullState (Equiv.swap a b) s) = s := by
  apply State.extensionality
  · rfl
  · funext q; simp [pullState]

private theorem pull_swap_fix (a b : Wire) (s : State) (h : s.basis a = s.basis b) :
    pullState (Equiv.swap a b) s = s := by
  apply State.extensionality
  · rfl
  · funext q
    simp only [pullState, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; exact h.symm
    · subst h2; exact h
    · rfl

private theorem swap_run_eq (a b : Wire) (P : Program) (s : State) (m : List Bool)
    (h0 : s.basis a = s.basis b) (h1 : (run P m s).basis a = (run P m s).basis b) :
    run (renameProgram (Equiv.swap a b) P) m s = run P m s := by
  have hr := ECDSAAdd.run_rename (Equiv.swap a b) (Equiv.swap a b).injective P m s
  rw [pull_swap_fix a b s h0] at hr
  have h2 := congrArg (pullState (Equiv.swap a b)) hr
  rw [pull_swap_invol, pull_swap_fix a b (run P m s) h1] at h2
  exact h2

private theorem state_eq_of_out (u v : State) (hp : u.phase = v.phase)
    (ho : regValue K0.core.out u.basis = regValue K0.core.out v.basis)
    (hf : ∀ q, q ∉ K0.core.out → u.basis q = v.basis q) : u = v := by
  apply State.extensionality _ _ hp
  funext q
  by_cases hq : q ∈ K0.core.out
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    have h1 := RawClearCarryProbe.register_bit K0.core.out i u.basis hi
    have h2 := RawClearCarryProbe.register_bit K0.core.out i v.basis hi
    have hg : K0.core.out.getD i 0 = K0.core.out[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [hg] at h1 h2
    rw [h1, h2, ho]
  · exact hf q hq

private theorem even_bit0_false (r : List Wire) (b : BasisState) (k : Nat)
    (hr : 0 < r.length) (hv : regValue r b = 2 * k) : b (r.getD 0 0) = false := by
  have hb := RawClearCarryProbe.register_bit r 0 b hr
  rw [hv] at hb
  simpa using hb

private theorem hi_bit_false (r : List Wire) (b : BasisState) (i : Nat)
    (hi : i < r.length) (hlt : regValue r b < 2 ^ i) : b (r.getD i 0) = false := by
  have hb := RawClearCarryProbe.register_bit r i b hi
  have hdiv : regValue r b / 2 ^ i = 0 := Nat.div_eq_of_lt hlt
  rw [hdiv] at hb
  simpa using hb

/-- Core correctness theorem for `withSplitPark` when `body` avoids `E0` and `c.workT`. -/
private theorem withSplitPark_correct (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program) (V : Nat)
    (hkLen : keepBits + parkHosts.length = c.n)
    (hkPos : 0 < keepBits)
    (hsrcLen : c.src.length = c.n)
    (hParkNd : parkHosts.Nodup)
    (hParkIn : ∀ h ∈ parkHosts, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0)
    (hParkDisBank : ∀ h ∈ parkHosts, h ∉ c.bank)
    (hParkDisSrc : ∀ h ∈ parkHosts, h ∉ c.src)
    (hParkDisDst : ∀ h ∈ parkHosts, h ∉ c.dst)
    (hParkDisOut : ∀ h ∈ parkHosts, h ∉ K0.core.out)
    (hParkDisG0 : G0 ∉ parkHosts)
    (hParkDisSw : ∀ h ∈ parkHosts, h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478)
    (hSrcDis : (G0 :: c.src ++ c.bank).Nodup)
    (hE0DisBank : ∀ q ∈ E0, q ∉ c.bank)
    (hWorkTSub : ∀ q ∈ c.workT, q ∈ K0.core.work ∨ q = D0)
    (hBodyDisE0 : ∀ q ∈ E0, q ∉ wires body)
    (hBodyDisWorkT : ∀ q ∈ c.workT, q ∉ wires body)
    (hBodyDisEU : ControlLoan1589BFFold.eU K0 ∈ parkHosts → ControlLoan1589BFFold.eU K0 ∉ wires body)
    (hLiveSub : ∀ q ∈ c.liveT, q ∈ E0 ∨ q ∈ c.workT)
    (hLiveDisBank : ∀ q ∈ c.liveT, q ∉ c.bank)
    (hLiveDisSrc : ∀ q ∈ c.liveT, q ∉ c.src)
    (hLiveDisOut : ∀ q ∈ c.liveT, q ∉ K0.core.out)
    (hScSub : ∀ q ∈ c.cleanScratch, q ∈ K0.foldPad ∨ q ∈ K0.core.work)
    (hScDisBank : ∀ q ∈ c.cleanScratch, q ∉ c.bank)
    (hScDisSrc : ∀ q ∈ c.cleanScratch, q ∉ c.src)
    (hScDisOut : ∀ q ∈ c.cleanScratch, q ∉ K0.core.out)
    (hScDisPark : ∀ q ∈ c.cleanScratch, q ∉ parkHosts)
    (hDstDisBank : ∀ q ∈ c.dst, q ∉ c.bank)
    (hDstDisSrc : ∀ q ∈ c.dst, q ∉ c.src)
    (hDstDisOut : ∀ q ∈ c.dst, q ∉ K0.core.out)
    (hBankDisOut : ∀ q ∈ c.bank, q ∉ K0.core.out)
    (hSrcDisOut : ∀ q ∈ c.src, q ∉ K0.core.out)
    (hG0Out : G0 ∉ c.bank ∧ G0 ∉ c.dst ∧ G0 ∉ c.liveT ∧ G0 ∉ c.cleanScratch ∧ G0 ∉ K0.core.out)
    (hCacheEq : LowZero18Square.cacheWire K0 c.dst = c.dst.headD 0)
    (hParkZeroAfterMake : ∀ s0 : State, ∀ m0 : List Bool,
      regValue c.dst s0.basis = 0 → regValue c.liveT s0.basis = 0 →
      regValue c.cleanScratch s0.basis = 0 → s0.basis K0.core.cin = false →
      (ControlLoan1589BFFold.eU K0 ∈ parkHosts → s0.basis (ControlLoan1589BFFold.eU K0) = false) →
      (∀ q ∈ E0, s0.basis q = false) →
      (∀ h ∈ parkHosts, (run c.make m0 s0).basis h = false) ∧
      (run c.make m0 s0).basis 5093 = false ∧ (run c.make m0 s0).basis 5478 = false)
    (s : State) (records : List Bool) (hc : K0.PairClean s.basis)
    (hd0 : regValue c.dst s.basis = 0) (he0 : regValue E0 s.basis = 0)
    (hd0_bit : s.basis D0 = false)
    (heu0 : ControlLoan1589BFFold.eU K0 ∈ parkHosts → s.basis (ControlLoan1589BFFold.eU K0) = false)
    (callback : ∀ t : State, ∀ m : List Bool,
      regValue c.dst t.basis = (if s.basis G0 then regValue c.src s.basis else 0) ^ 2 →
      (∀ q, q ∉ c.dst → t.basis q = s.basis q) →
      (run body m t).phase = t.phase ∧ regValue K0.core.out (run body m t).basis = V ∧
      ∀ q, q ∉ K0.core.out → (run body m t).basis q = t.basis q) :
    (run (withSplitPark c keepBits parkHosts body) records s).phase = s.phase ∧
    regValue K0.core.out (run (withSplitPark c keepBits parkHosts body) records s).basis = V ∧
    ∀ q, q ∉ K0.core.out → (run (withSplitPark c keepBits parkHosts body) records s).basis q = s.basis q := by
  have hbankLen : c.bank.length = c.n := v.bankLen
  have hsrc_bank : c.src.length = c.bank.length := by omega
  have hkeepLe : keepBits ≤ c.n := by omega
  have hE0_all : ∀ q ∈ E0, s.basis q = false := (regValue_zero _ _).mp he0
  have hWork_all : ∀ q ∈ K0.core.work, s.basis q = false := (regValue_zero _ _).mp hc.work
  have hPad_all : ∀ q ∈ K0.foldPad, s.basis q = false := (regValue_zero _ _).mp hc.pad
  have hSc0_s : regValue c.cleanScratch s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (hScSub q hq).elim (hPad_all q) (hWork_all q))
  have hLive0_s : regValue c.liveT s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (hLiveSub q hq).elim (hE0_all q) (fun hw => (hWorkTSub q hw).elim (hWork_all q) (fun h => h ▸ hd0_bit)))
  have hSwMem : (4834 : Wire) ∈ K0.foldPad ∧ (4875 : Wire) ∈ K0.foldPad ∧
      (4834 : Wire) ∉ K0.core.out ∧ (5093 : Wire) ∉ K0.core.out ∧
      (4875 : Wire) ∉ K0.core.out ∧ (5478 : Wire) ∉ K0.core.out ∧
      (4834 : Wire) ∉ allowedWires ∧ (4875 : Wire) ∉ allowedWires :=
    have h6 : (4834 : Wire) ∈ K0.foldPad ∧ (4875 : Wire) ∈ K0.foldPad ∧
        (4834 : Wire) ∉ K0.core.out ∧ (5093 : Wire) ∉ K0.core.out ∧
        (4875 : Wire) ∉ K0.core.out ∧ (5478 : Wire) ∉ K0.core.out := by rw [K0_eq]; decide +kernel
    ⟨h6.1, h6.2.1, h6.2.2.1, h6.2.2.2.1, h6.2.2.2.2.1, h6.2.2.2.2.2, not_mem_allowedWires_4834, not_mem_allowedWires_4875⟩
  have h4834_0 : s.basis 4834 = false := hPad_all 4834 hSwMem.1
  have h4875_0 : s.basis 4875 = false := hPad_all 4875 hSwMem.2.1
  have h4834_notReal : (4834 : Wire) ∉ c.realAll := fun h => hSwMem.2.2.2.2.2.2.1 (v.realAllowed _ h)
  have h4875_notReal : (4875 : Wire) ∉ c.realAll := fun h => hSwMem.2.2.2.2.2.2.2 (v.realAllowed _ h)
  have h5093_notBank : (5093 : Wire) ∉ c.bank := hE0DisBank 5093 (by rw [E0_eq]; decide +kernel)
  have h5478_notBank : (5478 : Wire) ∉ c.bank := hE0DisBank 5478 (by rw [E0_eq]; decide +kernel)
  have hCin_notBank : K0.core.cin ∉ c.bank :=
    kdis v.realNd (r := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; simp only [List.count_cons, List.count_nil]; omega) _ (by simp)
  have hCin_notDst : K0.core.cin ∉ c.dst :=
    kdis v.realNd (r := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; simp only [List.count_cons, List.count_nil]; omega) _ (by simp)
  have hCin_notLive : K0.core.cin ∉ c.liveT :=
    kdis v.realNd (r := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append, List.count_cons, List.count_nil]; omega) _ (by simp)
  have hCin_notPark : K0.core.cin ∉ parkHosts := fun hp =>
    (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel : K0.core.cin ∉ E0 ∧ K0.core.cin ≠ ControlLoan1589BFFold.eU K0) |>
      fun h => (hParkIn _ hp).elim h.1 h.2
  have hCin_notOut : K0.core.cin ∉ K0.core.out := by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  have hParkDisReal : ∀ h ∈ parkHosts, h ∉ c.dst ∧ h ∉ c.bank := fun h hh => ⟨hParkDisDst h hh, hParkDisBank h hh⟩
  let P := if s.basis G0 then regValue c.src s.basis else 0
  let pA := copyRegister (some G0) c.src c.bank
  let pM := c.make
  let pE1 := eraseMask G0 (c.src.take keepBits) (c.bank.take keepBits)
  let pD := ParkCopy.dummies parkHosts
  let pMI := ParkCopy.move (c.bank.drop keepBits) parkHosts
  let pB := renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)
  let pC1 := CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits)
  let pMO := ParkCopy.move parkHosts (c.bank.drop keepBits)
  let pCL := c.clear
  let pE := eraseMask G0 c.src c.bank
  obtain ⟨r9, mE, eE⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1 ++ pMO ++ pCL) pE records s
  obtain ⟨r8, mCL, eCL⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1 ++ pMO) pCL r9 s
  obtain ⟨r7, mMO, eMO⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1) pMO r8 s
  obtain ⟨r6, mC1, eC1⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB) pC1 r7 s
  obtain ⟨r5, mB, eB⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI) pB r6 s
  obtain ⟨r4, mMI, eMI⟩ := kseq (pA ++ pM ++ pE1 ++ pD) pMI r5 s
  obtain ⟨r3, mD, eD⟩ := kseq (pA ++ pM ++ pE1) pD r4 s
  obtain ⟨r2, mE1, eE1⟩ := kseq (pA ++ pM) pE1 r3 s
  obtain ⟨mA, mM, eM⟩ := kseq pA pM r2 s
  rw [show withSplitPark c keepBits parkHosts body = pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1 ++ pMO ++ pCL ++ pE from rfl,
    eE, eCL, eMO, eC1, eB, eMI, eD, eE1, eM]
  -- 1. pA: copy controlled src into bank
  have hndSB : (c.src ++ c.bank).Nodup := (List.nodup_cons.mp hSrcDis).2
  have hG0B : ∀ x ∈ some G0, x ∉ c.bank := fun x hx => by
    cases Option.some.inj hx; exact hG0Out.1
  have hBank0_s : regValue c.bank s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => hWork_all q (List.mem_of_mem_take (List.mem_of_mem_take hq)))
  have stA := copyRegister_correct (some G0) c.src c.bank hsrc_bank hndSB hG0B s mA
  generalize hsA : run pA mA s = sA at stA ⊢
  have sA_bank : regValue c.bank sA.basis = P := by
    have h := stA.2.2
    rw [hBank0_s, Nat.zero_xor] at h
    simpa [P] using h
  have sA_out (q : Wire) (hb : q ∉ c.bank) : sA.basis q = s.basis q := stA.2.1 q hb
  have hTakeA : regValue (c.bank.take keepBits) sA.basis =
      if s.basis G0 = true then regValue (c.src.take keepBits) s.basis else 0 := by
    have eA := regValue_append (c.bank.take keepBits) (c.bank.drop keepBits) sA.basis
    rw [List.take_append_drop, sA_bank] at eA
    have eS := regValue_append (c.src.take keepBits) (c.src.drop keepBits) s.basis
    rw [List.take_append_drop] at eS
    have hlenT : (c.bank.take keepBits).length = keepBits := by simp [hbankLen, hkeepLe]
    have hlenS : (c.src.take keepBits).length = keepBits := by simp [hsrcLen, hkeepLe]
    have hltA : regValue (c.bank.take keepBits) sA.basis < 2 ^ keepBits := by
      simpa [hlenT] using regValue_lt (c.bank.take keepBits) sA.basis
    have hltS : regValue (c.src.take keepBits) s.basis < 2 ^ keepBits := by
      simpa [hlenS] using regValue_lt (c.src.take keepBits) s.basis
    cases hg : s.basis G0
    · simp only [P, hg, Bool.false_eq_true, if_false] at eA ⊢
      omega
    · simp only [P, hg, if_true] at eA ⊢
      rw [hlenT] at eA; rw [hlenS] at eS
      have m1 : regValue (c.bank.take keepBits) sA.basis = regValue c.src s.basis % 2 ^ keepBits := by
        rw [eA, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hltA]
      have m2 : regValue (c.src.take keepBits) s.basis = regValue c.src s.basis % 2 ^ keepBits := by
        rw [eS, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hltS]
      exact m1.trans m2.symm
  -- 2. pM: c.make computes dst = P^2 and liveT
  have sA_dst0 : regValue c.dst sA.basis = 0 := (regValue_congr _ _ s.basis (fun q hq => sA_out q (hDstDisBank q hq))).trans hd0
  have sA_live0 : regValue c.liveT sA.basis = 0 := (regValue_congr _ _ s.basis (fun q hq => sA_out q (hLiveDisBank q hq))).trans hLive0_s
  have sA_sc0 : regValue c.cleanScratch sA.basis = 0 := (regValue_congr _ _ s.basis (fun q hq => sA_out q (hScDisBank q hq))).trans hSc0_s
  have sA_cin0 : sA.basis K0.core.cin = false := (sA_out _ hCin_notBank).trans hc.cin
  have stM := cfg_make_correct c v sA mM sA_dst0 sA_live0 sA_sc0 sA_cin0
  have hZeros := hParkZeroAfterMake sA mM sA_dst0 sA_live0 sA_sc0 sA_cin0
    (fun hm => (sA_out _ (hParkDisBank _ hm)).trans (heu0 hm))
    (fun q hq => (sA_out q (hE0DisBank q hq)).trans (hE0_all q hq))
  generalize hsM : run pM mM sA = sM at stM hZeros ⊢
  have sM_dst : regValue c.dst sM.basis = P ^ 2 := by rw [stM.2.1, sA_bank]
  have sM_out (q : Wire) (hd : q ∉ c.dst) (hl : q ∉ c.liveT) : sM.basis q = sA.basis q := stM.2.2.2.2.2.2 q hd hl
  have hSrcDisBank : ∀ q ∈ c.src, q ∉ c.bank := fun q hq hb => (List.nodup_append.mp hndSB).2.2 q hq q hb rfl
  -- 3. pE1: erase bank.take keepBits
  have hndMask : (G0 :: c.src.take keepBits ++ c.bank.take keepBits).Nodup :=
    list_nodup_of_count_le hSrcDis (fun q => by
      have a := (List.take_sublist keepBits c.src).count_le q
      have b := (List.take_sublist keepBits c.bank).count_le q
      simp only [List.count_cons, List.count_append]; omega)
  have stE1 := eraseMask_correct G0 (c.src.take keepBits) (c.bank.take keepBits)
    (by simp [hsrcLen, hbankLen]) hndMask sM mE1 (by
      have e1 : regValue (c.bank.take keepBits) sM.basis = regValue (c.bank.take keepBits) sA.basis :=
        regValue_congr _ _ _ (fun q hq => sM_out q (fun h => hDstDisBank _ h (List.mem_of_mem_take hq))
          (fun h => hLiveDisBank _ h (List.mem_of_mem_take hq)))
      have e2 : sM.basis G0 = s.basis G0 := (sM_out _ hG0Out.2.1 hG0Out.2.2.1).trans (sA_out _ hG0Out.1)
      have e3 : regValue (c.src.take keepBits) sM.basis = regValue (c.src.take keepBits) s.basis :=
        regValue_congr _ _ _ (fun q hq => (sM_out q (fun h => hDstDisSrc _ h (List.mem_of_mem_take hq))
          (fun h => hLiveDisSrc _ h (List.mem_of_mem_take hq))).trans (sA_out q (hSrcDisBank _ (List.mem_of_mem_take hq))))
      rw [e1, e2, e3]; exact hTakeA)
  generalize hsE1 : run pE1 mE1 sM = sE1 at stE1 ⊢
  have sE1_park0 : ∀ h ∈ parkHosts, sE1.basis h = false := fun h hh =>
    (stE1.2.1 h (fun hb => hParkDisBank h hh (List.mem_of_mem_take hb))).trans (hZeros.1 h hh)
  -- 4. pD: dummies on zero parkHosts (no-op on state!)
  have stD : run pD mD sE1 = sE1 := ParkCopy.dummies_run parkHosts sE1 mD sE1_park0
  rw [stD]
  -- 5. pMI: move bank.drop keepBits into parkHosts
  have hDropLen : (c.bank.drop keepBits).length = parkHosts.length := by simp [hbankLen]; omega
  have hBankNd : c.bank.Nodup := (List.nodup_append.mp hndSB).2.1
  have hndMP : (c.bank.drop keepBits ++ parkHosts).Nodup :=
    List.nodup_append.mpr ⟨hBankNd.sublist (List.drop_sublist _ _), hParkNd,
      fun q hq r hr heq => hParkDisBank r hr (heq ▸ List.mem_of_mem_drop hq)⟩
  have stMI := ParkCopy.move_correct (c.bank.drop keepBits) parkHosts hDropLen hndMP sE1 mMI
    ((regValue_zero _ _).mpr sE1_park0)
  generalize hsMI : run pMI mMI sE1 = sMI at stMI ⊢
  -- Helper: track sMI vs s outside dst ∪ liveT ∪ parkHosts
  have hBankZero_MI : regValue c.bank sMI.basis = 0 := by
    rw [← List.take_append_drop keepBits c.bank, regValue_append]
    have h1 : regValue (c.bank.take keepBits) sMI.basis = 0 := by
      rw [regValue_congr _ _ sE1.basis (fun q hq => by
        have hnD : q ∉ c.bank.drop keepBits := by
          have := hBankNd; rw [← List.take_append_drop keepBits c.bank] at this
          exact fun hd => (List.nodup_append.mp this).2.2 q hq q hd rfl
        exact stMI.2.1 q hnD (fun hp => hParkDisBank q hp (List.mem_of_mem_take hq)))]
      exact stE1.2.2
    rw [h1, stMI.2.2.2]; simp
  have sMI_eq_s (q : Wire) (hd : q ∉ c.dst) (hl : q ∉ c.liveT) (hp : q ∉ parkHosts) :
      sMI.basis q = s.basis q := by
    by_cases hb : q ∈ c.bank
    · exact ((regValue_zero _ _).mp hBankZero_MI q hb).trans ((regValue_zero _ _).mp hBank0_s q hb).symm
    · have h1 := stMI.2.1 q (fun h => hb (List.mem_of_mem_drop h)) hp
      have h2 := stE1.2.1 q (fun h => hb (List.mem_of_mem_take h))
      exact h1.trans (h2.trans ((sM_out q hd hl).trans (sA_out q hb)))
  have sMI_eq_sM_dst (q : Wire) (hd : q ∈ c.dst) : sMI.basis q = sM.basis q := by
    have hnb : q ∉ c.bank := fun hb => hDstDisBank q hd hb
    have hnp : q ∉ parkHosts := fun hp => hParkDisDst q hp hd
    exact (stMI.2.1 q (fun h => hnb (List.mem_of_mem_drop h)) hnp).trans
      (stE1.2.1 q (fun h => hnb (List.mem_of_mem_take h)))
  -- 6. pB: renameProgram foldPerm (bodySwap body) = body on sMI
  have sMI_4834 : sMI.basis 4834 = false :=
    (sMI_eq_s 4834 (fun h => h4834_notReal (by simp [SplitCfg.realAll, h]))
      (fun h => h4834_notReal (by clear * - h; simp only [SplitCfg.realAll, SplitCfg.liveT, List.mem_cons, List.mem_append] at h ⊢; tauto))
      (fun h => (hParkDisSw _ h).1 rfl)).trans h4834_0
  have sMI_4875 : sMI.basis 4875 = false :=
    (sMI_eq_s 4875 (fun h => h4875_notReal (by simp [SplitCfg.realAll, h]))
      (fun h => h4875_notReal (by clear * - h; simp only [SplitCfg.realAll, SplitCfg.liveT, List.mem_cons, List.mem_append] at h ⊢; tauto))
      (fun h => (hParkDisSw _ h).2.2.1 rfl)).trans h4875_0
  have sMI_5093 : sMI.basis 5093 = false :=
    ((stMI.2.1 5093 (fun h => h5093_notBank (List.mem_of_mem_drop h)) (fun h => (hParkDisSw _ h).2.1 rfl)).trans
      (stE1.2.1 5093 (fun h => h5093_notBank (List.mem_of_mem_take h)))).trans hZeros.2.1
  have sMI_5478 : sMI.basis 5478 = false :=
    ((stMI.2.1 5478 (fun h => h5478_notBank (List.mem_of_mem_drop h)) (fun h => (hParkDisSw _ h).2.2.2 rfl)).trans
      (stE1.2.1 5478 (fun h => h5478_notBank (List.mem_of_mem_take h)))).trans hZeros.2.2
  -- Build clean reference state t for callback
  let t : State := { phase := sMI.phase, basis := fun q => if q ∈ c.dst then sM.basis q else s.basis q }
  have t_dst : regValue c.dst t.basis = P ^ 2 := by
    rw [regValue_congr c.dst t.basis sM.basis (fun q hq => by simp [t, hq]), sM_dst]
  have cb := callback t mB t_dst (fun q hq => by simp [t, hq])
  have body_dis_live : ∀ q ∈ wires body, q ∉ c.liveT := fun q hq hl =>
    (hLiveSub q hl).elim (fun h => hBodyDisE0 q h hq) (fun h => hBodyDisWorkT q h hq)
  have body_dis_park : ∀ q ∈ wires body, q ∉ parkHosts := fun q hq hp =>
    (hParkIn q hp).elim (fun h => hBodyDisE0 q h hq) (fun h => hBodyDisEU (h ▸ hp) (h ▸ hq))
  have locB := ECDSAAdd.run_measured_locality body (wires body) (Finset.Subset.refl _) sMI t mB rfl
    (fun q hq => by
      by_cases hd : q ∈ c.dst
      · simp [t, hd]; exact sMI_eq_sM_dst q hd
      · simp [t, hd]; exact sMI_eq_s q hd (body_dis_live q hq) (body_dis_park q hq))
  have runBody_phase : (run body mB sMI).phase = sMI.phase := locB.1.trans cb.1
  have runBody_out : regValue K0.core.out (run body mB sMI).basis = V := by
    rw [regValue_congr K0.core.out (run body mB sMI).basis (run body mB t).basis (fun q hq => by
      by_cases hw : q ∈ wires body
      · exact locB.2 q hw
      · rw [run_preserves_outside body mB sMI q hw, run_preserves_outside body mB t q hw]
        have hnd : q ∉ c.dst := fun h => hDstDisOut q h hq
        simp only [t, hnd, if_false]
        exact sMI_eq_s q hnd (fun h => hLiveDisOut q h hq) (fun h => hParkDisOut q h hq))]
    exact cb.2.1
  have runBody_keep (q : Wire) (ho : q ∉ K0.core.out) : (run body mB sMI).basis q = sMI.basis q := by
    by_cases hw : q ∈ wires body
    · rw [locB.2 q hw, cb.2.2 q ho]
      by_cases hd : q ∈ c.dst
      · simp [t, hd]; exact (sMI_eq_sM_dst q hd).symm
      · simp [t, hd]; exact (sMI_eq_s q hd (body_dis_live q hw) (body_dis_park q hw)).symm
    · exact run_preserves_outside body mB sMI q hw
  have hFoldPerm : LowZero18Square.foldPerm K0 E0 = Equiv.swap 4834 5093 := by
    ext x; rw [StairSquareSites.LT48K.foldPerm_eq, Equiv.swap_apply_def]; rfl
  have hSqSwap : R2SqEp760.sqSwap K0 E0 = Equiv.swap 4875 5478 := by
    ext x; rw [StairSquareSites.LT48K.sqSwap_eq, Equiv.swap_apply_def]; rfl
  have eqSq : run (R2SqEp760.bodySwap K0 E0 body) mB sMI = run body mB sMI := by
    rw [R2SqEp760.bodySwap, hSqSwap]
    exact swap_run_eq 4875 5478 body sMI mB (sMI_4875.trans sMI_5478.symm)
      ((runBody_keep 4875 hSwMem.2.2.2.2.1).trans (sMI_4875.trans (sMI_5478.symm.trans (runBody_keep 5478 hSwMem.2.2.2.2.2.1).symm)))
  have eqPB : run pB mB sMI = run body mB sMI := by
    change run (renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)) mB sMI = _
    rw [hFoldPerm]
    refine (swap_run_eq 4834 5093 (R2SqEp760.bodySwap K0 E0 body) sMI mB
      (sMI_4834.trans sMI_5093.symm) ?_).trans eqSq
    rw [eqSq, runBody_keep 4834 hSwMem.2.2.1, runBody_keep 5093 hSwMem.2.2.2.1, sMI_4834, sMI_5093]
  generalize hsB : run pB mB sMI = sB at eqPB ⊢
  have sB_phase : sB.phase = sMI.phase := by rw [eqPB]; exact runBody_phase
  have sB_out : regValue K0.core.out sB.basis = V := by rw [eqPB]; exact runBody_out
  have sB_keep (q : Wire) (ho : q ∉ K0.core.out) : sB.basis q = sMI.basis q := by rw [eqPB]; exact runBody_keep q ho
  -- 7. pC1: CachedSquareCopy restores bank.take keepBits
  have sB_dst : regValue c.dst sB.basis = P ^ 2 := by
    rw [regValue_congr c.dst sB.basis sM.basis (fun q hq => (sB_keep q (hDstDisOut q hq)).trans (sMI_eq_sM_dst q hq)), sM_dst]
  have sB_G0 : sB.basis G0 = s.basis G0 :=
    (sB_keep G0 hG0Out.2.2.2.2).trans (sMI_eq_s G0 hG0Out.2.1 hG0Out.2.2.1 hParkDisG0)
  have sB_src : regValue c.src sB.basis = regValue c.src s.basis :=
    regValue_congr c.src sB.basis s.basis (fun q hq =>
      (sB_keep q (hSrcDisOut q hq)).trans
      (sMI_eq_s q (fun h => hDstDisSrc _ h hq) (fun h => hLiveDisSrc _ h hq) (fun h => hParkDisSrc _ h hq)))
  have hCached : sB.basis (LowZero18Square.cacheWire K0 c.dst) =
      (sB.basis G0 && sB.basis ((c.src.take keepBits).headD 0)) := by
    rw [hCacheEq, ParkCopy.headD_take c.src keepBits hkPos]
    have hsq := CachedSquareCopy.square_head c.src c.dst G0 sB (by omega) (by rw [v.dstLen]; omega)
      (by rw [sB_dst, sB_G0, sB_src])
    exact hsq
  have eqC1 : run pC1 mC1 sB = run (copyRegister (some G0) (c.src.take keepBits) (c.bank.take keepBits)) mC1 sB :=
    CachedSquareCopy.run_eq G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits) sB mC1 hCached
  have hndSB_k : (c.src.take keepBits ++ c.bank.take keepBits).Nodup := (List.nodup_cons.mp hndMask).2
  have hG0B_k : ∀ x ∈ some G0, x ∉ c.bank.take keepBits := fun x hx hb => hG0B x hx (List.mem_of_mem_take hb)
  have stC1 := copyRegister_correct (some G0) (c.src.take keepBits) (c.bank.take keepBits)
    (by simp [hsrcLen, hbankLen]) hndSB_k hG0B_k sB mC1
  rw [← eqC1] at stC1
  generalize hsC1 : run pC1 mC1 sB = sC1 at stC1 ⊢
  have sB_bk0 : regValue (c.bank.take keepBits) sB.basis = 0 := by
    rw [regValue_congr _ _ sMI.basis (fun q hq => sB_keep q (hBankDisOut q (List.mem_of_mem_take hq)))]
    exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hBankZero_MI q (List.mem_of_mem_take hq))
  have sC1_bk : regValue (c.bank.take keepBits) sC1.basis = regValue (c.bank.take keepBits) sA.basis := by
    have h := stC1.2.2
    rw [sB_bk0, Nat.zero_xor] at h
    have hsrc_k : regValue (c.src.take keepBits) sB.basis = regValue (c.src.take keepBits) s.basis :=
      regValue_congr _ _ s.basis (fun q hq =>
        (sB_keep q (hSrcDisOut q (List.mem_of_mem_take hq))).trans
        (sMI_eq_s q (fun h' => hDstDisSrc _ h' (List.mem_of_mem_take hq))
          (fun h' => hLiveDisSrc _ h' (List.mem_of_mem_take hq))
          (fun h' => hParkDisSrc _ h' (List.mem_of_mem_take hq))))
    rw [h]; simp only [copyValue, sB_G0, hsrc_k]; exact hTakeA.symm
  -- 8. pMO: move parkHosts back into bank.drop keepBits
  have hndPM : (parkHosts ++ c.bank.drop keepBits).Nodup := (List.perm_append_comm.nodup_iff).mp hndMP
  have hDropNotTake : ∀ q ∈ c.bank.drop keepBits, q ∉ c.bank.take keepBits := by
    intro q hd ht
    have := hBankNd; rw [← List.take_append_drop keepBits c.bank] at this
    exact (List.nodup_append.mp this).2.2 q ht q hd rfl
  have sC1_drop0 : regValue (c.bank.drop keepBits) sC1.basis = 0 :=
    (regValue_congr _ _ sMI.basis (fun q hq =>
      (stC1.2.1 q (hDropNotTake q hq)).trans (sB_keep q (hBankDisOut q (List.mem_of_mem_drop hq))))).trans stMI.2.2.2
  have stMO := ParkCopy.move_correct parkHosts (c.bank.drop keepBits) hDropLen.symm hndPM sC1 mMO sC1_drop0
  generalize hsMO : run pMO mMO sC1 = sMO at stMO ⊢
  -- Key state invariants on sMO before c.clear!
  have sMO_eq_sM_of_not_out (q : Wire) (ho : q ∉ K0.core.out) (hb : q ∉ c.bank) : sMO.basis q = sM.basis q := by
    by_cases hp : q ∈ parkHosts
    · have h0_mo : sMO.basis q = false := (regValue_zero _ _).mp stMO.2.2.2 q hp
      have h0_m : sM.basis q = false := hZeros.1 q hp
      exact h0_mo.trans h0_m.symm
    · have h1 := stMO.2.1 q hp (fun h => hb (List.mem_of_mem_drop h))
      have h2 := stC1.2.1 q (fun h => hb (List.mem_of_mem_take h))
      have h3 := sB_keep q ho
      have h4 := stMI.2.1 q (fun h => hb (List.mem_of_mem_drop h)) hp
      have h5 := stE1.2.1 q (fun h => hb (List.mem_of_mem_take h))
      exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have sMO_bank : regValue c.bank sMO.basis = P := by
    rw [← List.take_append_drop keepBits c.bank, regValue_append]
    have h1 : regValue (c.bank.take keepBits) sMO.basis = regValue (c.bank.take keepBits) sA.basis := by
      rw [regValue_congr _ _ sC1.basis (fun q hq =>
        stMO.2.1 q (fun hp => hParkDisBank q hp (List.mem_of_mem_take hq)) (fun hd => hDropNotTake q hd hq)), sC1_bk]
    have h2 : regValue (c.bank.drop keepBits) sMO.basis = regValue (c.bank.drop keepBits) sA.basis := by
      rw [stMO.2.2.1]
      rw [regValue_congr parkHosts sC1.basis sMI.basis (fun q hq =>
        (stC1.2.1 q (fun ht => hParkDisBank q hq (List.mem_of_mem_take ht))).trans (sB_keep q (hParkDisOut q hq)))]
      rw [stMI.2.2.1]
      exact regValue_congr _ _ sA.basis (fun q hq =>
        (stE1.2.1 q (hDropNotTake q hq)).trans
          (sM_out q (fun h => hDstDisBank _ h (List.mem_of_mem_drop hq))
            (fun h => hLiveDisBank _ h (List.mem_of_mem_drop hq))))
    rw [h1, h2, ← regValue_append, List.take_append_drop, sA_bank]
  have sMO_bank_bit (q : Wire) (hq : q ∈ c.bank) : sMO.basis q = sA.basis q := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    have b1 := RawClearCarryProbe.register_bit c.bank i sMO.basis hi
    have b2 := RawClearCarryProbe.register_bit c.bank i sA.basis hi
    have hg : c.bank.getD i 0 = c.bank[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [hg] at b1 b2; rw [b1, b2, sMO_bank, sA_bank]
  have sMO_lo : regValue c.R.lo sMO.basis = regValue c.R.lo sA.basis :=
    regValue_congr _ _ _ (fun q hq => sMO_bank_bit q (List.mem_of_mem_take hq))
  have sMO_hi : regValue c.R.hi sMO.basis = regValue c.R.hi sA.basis :=
    regValue_congr _ _ _ (fun q hq => sMO_bank_bit q (List.mem_of_mem_drop hq))
  have sMO_dst : regValue c.dst sMO.basis = (regValue c.bank sMO.basis) ^ 2 := by
    rw [regValue_congr c.dst sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q (hDstDisOut q hq) (hDstDisBank q hq)),
      sM_dst, sMO_bank]
  have sMO_T : regValue c.T sMO.basis = 2 * regValue c.R.lo sMO.basis * regValue c.R.hi sMO.basis := by
    rw [regValue_congr c.T sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.1, sMO_lo, sMO_hi]
  have sMO_T1 : regValue c.T1 sMO.basis = 2 * (regValue c.R.lo sMO.basis % 2 ^ 32) * (regValue c.R.lo sMO.basis / 2 ^ 32) := by
    rw [regValue_congr c.T1 sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.2.1, sMO_lo]
  have sMO_T2 : regValue c.T2 sMO.basis = 2 * (regValue c.R.hi sMO.basis % 2 ^ c.Q2.h) * (regValue c.R.hi sMO.basis / 2 ^ c.Q2.h) := by
    rw [regValue_congr c.T2 sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.2.2.1, sMO_hi]
  have sMO_T5 : regValue c.T5 sMO.basis = 2 * ((regValue c.R.lo sMO.basis + regValue c.R.hi sMO.basis) % 2 ^ 33) *
      ((regValue c.R.lo sMO.basis + regValue c.R.hi sMO.basis) / 2 ^ 33) := by
    rw [regValue_congr c.T5 sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.2.2.2.1, sMO_lo, sMO_hi]
  have sMO_sc0 : regValue c.cleanScratch sMO.basis = 0 := by
    rw [regValue_congr c.cleanScratch sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q (hScDisOut q hq) (hScDisBank q hq))]
    refine (regValue_congr c.cleanScratch sM.basis sA.basis (fun q hq => sM_out q
      (kdis v.realNd (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.cleanScratch, List.count_cons, List.count_append, List.count_nil]; omega) q hq)
      (kdis v.realNd (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.cleanScratch, SplitCfg.liveT, List.count_cons, List.count_append, List.count_nil]; omega) q hq))).trans sA_sc0
  have sMO_cin0 : sMO.basis K0.core.cin = false :=
    (sMO_eq_sM_of_not_out K0.core.cin hCin_notOut hCin_notBank).trans
      ((sM_out K0.core.cin hCin_notDst hCin_notLive).trans sA_cin0)
  -- 9. pCL: c.clear uncomputes dst and liveT to 0
  have stCL := cfg_clear_correct c v sMO mCL sMO_dst sMO_T sMO_T1 sMO_T2 sMO_T5 sMO_sc0 sMO_cin0
  generalize hsCL : run pCL mCL sMO = sCL at stCL ⊢
  -- 10. pE: eraseMask erases bank back to 0
  have stE := eraseMask_correct G0 c.src c.bank hsrc_bank hSrcDis sCL mE (by
    have e1 : regValue c.bank sCL.basis = P :=
      (regValue_congr c.bank sCL.basis sMO.basis (fun q hq =>
        stCL.2.2.2 q (fun h => hDstDisBank _ h hq) (fun h => hLiveDisBank _ h hq))).trans sMO_bank
    have e2 : sCL.basis G0 = s.basis G0 :=
      (stCL.2.2.2 G0 hG0Out.2.1 hG0Out.2.2.1).trans
        ((sMO_eq_sM_of_not_out G0 hG0Out.2.2.2.2 hG0Out.1).trans
          ((sM_out G0 hG0Out.2.1 hG0Out.2.2.1).trans (sA_out G0 hG0Out.1)))
    have e3 : regValue c.src sCL.basis = regValue c.src s.basis :=
      regValue_congr c.src sCL.basis s.basis (fun q hq =>
        (stCL.2.2.2 q (fun h => hDstDisSrc _ h hq) (fun h => hLiveDisSrc _ h hq)).trans
          ((sMO_eq_sM_of_not_out q (hSrcDisOut q hq) (hSrcDisBank q hq)).trans
            ((sM_out q (fun h => hDstDisSrc _ h hq) (fun h => hLiveDisSrc _ h hq)).trans
              (sA_out q (hSrcDisBank q hq)))))
    rw [e1, e2, e3])
  generalize hsE : run pE mE sCL = sE at stE ⊢
  refine ⟨?_, ?_, ?_⟩
  · exact stE.1.trans (stCL.1.trans (stMO.1.trans (stC1.1.trans (sB_phase.trans
      (stMI.1.trans (stE1.1.trans (stM.1.trans stA.1)))))))
  · rw [regValue_congr K0.core.out sE.basis sB.basis (fun q hq =>
      (stE.2.1 q (fun h => hBankDisOut q h hq)).trans
      ((stCL.2.2.2 q (fun h => hDstDisOut q h hq) (fun h => hLiveDisOut q h hq)).trans
      ((stMO.2.1 q (fun h => hParkDisOut q h hq) (fun h => hBankDisOut q (List.mem_of_mem_drop h) hq)).trans
       (stC1.2.1 q (fun h => hBankDisOut q (List.mem_of_mem_take h) hq)))))]
    exact sB_out
  · intro q ho
    by_cases hb : q ∈ c.bank
    · exact ((regValue_zero _ _).mp stE.2.2 q hb).trans ((regValue_zero _ _).mp hBank0_s q hb).symm
    · rw [stE.2.1 q hb]
      by_cases hd : q ∈ c.dst
      · exact ((regValue_zero _ _).mp stCL.2.1 q hd).trans ((regValue_zero _ _).mp hd0 q hd).symm
      · by_cases hl : q ∈ c.liveT
        · exact ((regValue_zero _ _).mp stCL.2.2.1 q hl).trans ((regValue_zero _ _).mp hLive0_s q hl).symm
        · exact (stCL.2.2.2 q hd hl).trans ((sMO_eq_sM_of_not_out q ho hb).trans ((sM_out q hd hl).trans (sA_out q hb)))

/-! ### Zero-bit proofs for parked hosts and swap hosts after `make` -/

private theorem getD_take {α : Type} (l : List α) (n i : Nat) (d : α) (hi : i < n) :
    (l.take n).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

private theorem getD_drop {α : Type} (l : List α) (k i : Nat) (d : α) :
    (l.drop k).getD i d = l.getD (k + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem cfg128_zeros (c : SplitCfg) (v : CfgValid c) (hn : c.n = 128)
    (hT5_0 : c.T5.getD 0 0 = E0.getD 231 0)
    (hT5_66 : c.T5.getD 66 0 = E0.getD 298 0)
    (hT5_67 : c.T5.getD 67 0 = E0.getD 299 0)
    (hT_eq : c.T = E0.take 130) (hT1_eq : c.T1 = (E0.drop 132).take 66) (hT2_eq : c.T2 = (E0.drop 232).take 66)
    (parkHosts : List Wire)
    (hParkSub : ∀ h ∈ parkHosts, h ∈ ParkCopy.hosts E0 ∨ h = ControlLoan1589BFFold.eU K0)
    (h130_not : E0.getD 130 0 ∉ c.dst ∧ E0.getD 130 0 ∉ c.liveT)
    (h131_not : E0.getD 131 0 ∉ c.dst ∧ E0.getD 131 0 ∉ c.liveT)
    (heU_not : ControlLoan1589BFFold.eU K0 ∉ c.dst ∧ ControlLoan1589BFFold.eU K0 ∉ c.liveT)
    (s0 : State) (m0 : List Bool)
    (hd0 : regValue c.dst s0.basis = 0) (hT0 : regValue c.liveT s0.basis = 0)
    (hSc0 : regValue c.cleanScratch s0.basis = 0) (hi0 : s0.basis K0.core.cin = false)
    (heu0 : ControlLoan1589BFFold.eU K0 ∈ parkHosts → s0.basis (ControlLoan1589BFFold.eU K0) = false)
    (he0 : ∀ q ∈ E0, s0.basis q = false) :
    (∀ h ∈ parkHosts, (run c.make m0 s0).basis h = false) ∧
    (run c.make m0 s0).basis 5093 = false ∧ (run c.make m0 s0).basis 5478 = false := by
  have st := cfg_make_correct c v s0 m0 hd0 hT0 hSc0 hi0
  set u := run c.make m0 s0
  set a := regValue c.R.lo s0.basis
  set b := regValue c.R.hi s0.basis
  have haLt : a < 2 ^ 64 := by
    have : c.R.lo.length = 64 := by simp [KRegs.lo, SplitCfg.R, v.bankLen, hn]
    simpa [this] using regValue_lt c.R.lo s0.basis
  have hbLt : b < 2 ^ 64 := by
    have : c.R.hi.length = 64 := by simp [KRegs.hi, SplitCfg.R, v.bankLen, hn]
    simpa [this] using regValue_lt c.R.hi s0.basis
  have hQ2h : c.Q2.h = 32 := by simp [SplitCfg.Q2, hn]
  have hElen : E0.length = 300 := by rw [E0_eq]; decide +kernel
  have h5093 : E0.getD 0 0 = 5093 := by rw [E0_eq]; decide +kernel
  have h5478 : E0.getD 130 0 = 5478 := by rw [E0_eq]; decide +kernel
  have bT0 : u.basis (E0.getD 0 0) = false := by
    have e : c.T.getD 0 0 = E0.getD 0 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact even_bit0_false c.T u.basis (a * b) (by rw [v.tLen, hn]; decide) (by rw [st.2.2.1]; ring)
  have bT129 : u.basis (E0.getD 129 0) = false := by
    have e : c.T.getD 129 0 = E0.getD 129 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; refine hi_bit_false c.T u.basis 129 (by rw [v.tLen, hn]; decide) ?_
    rw [st.2.2.1, Nat.mul_assoc]; have : a * b < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' haLt hbLt; omega
  have bT130 : u.basis (E0.getD 130 0) = false :=
    (st.2.2.2.2.2.2 _ h130_not.1 h130_not.2).trans (he0 _ (DiagSq.getD_in E0 130 (by omega)))
  have bT131 : u.basis (E0.getD 131 0) = false :=
    (st.2.2.2.2.2.2 _ h131_not.1 h131_not.2).trans (he0 _ (DiagSq.getD_in E0 131 (by omega)))
  have bT1_0 : u.basis (E0.getD 132 0) = false := by
    have e : c.T1.getD 0 0 = E0.getD 132 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false c.T1 u.basis ((a % 2 ^ 32) * (a / 2 ^ 32)) (by rw [v.t1Len]; decide) (by rw [st.2.2.2.1]; ring)
  have bT1_65 : u.basis (E0.getD 197 0) = false := by
    have e : c.T1.getD 65 0 = E0.getD 197 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false c.T1 u.basis 65 (by rw [v.t1Len]; decide) ?_
    rw [st.2.2.2.1, Nat.mul_assoc]
    have h1 : a % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h2 : a / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (a % 2 ^ 32) * (a / 2 ^ 32) < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT2_0 : u.basis (E0.getD 232 0) = false := by
    have e : c.T2.getD 0 0 = E0.getD 232 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false c.T2 u.basis ((b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h))
      (by have := v.t2Len; simp [hn] at this; omega) (by rw [st.2.2.2.2.1]; ring)
  have bT2_65 : u.basis (E0.getD 297 0) = false := by
    have e : c.T2.getD 65 0 = E0.getD 297 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false c.T2 u.basis 65 (by have := v.t2Len; simp [hn] at this; omega) ?_
    rw [st.2.2.2.2.1, hQ2h, Nat.mul_assoc]
    have h1 : b % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h2 : b / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (b % 2 ^ 32) * (b / 2 ^ 32) < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT5_0 : u.basis (E0.getD 231 0) = false := by
    rw [← hT5_0]; exact even_bit0_false c.T5 u.basis (((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33))
      (by rw [v.t5Len]; decide) (by rw [st.2.2.2.2.2.1]; ring)
  have bT5_lt : regValue c.T5 u.basis < 2 ^ 66 := by
    rw [st.2.2.2.2.2.1, Nat.mul_assoc]
    have h1 : (a + b) % 2 ^ 33 < 2 ^ 33 := Nat.mod_lt _ (by decide)
    have h2 : (a + b) / 2 ^ 33 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) < 2 ^ 33 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT5_66 : u.basis (E0.getD 298 0) = false := by
    rw [← hT5_66]; exact hi_bit_false c.T5 u.basis 66 (by rw [v.t5Len]; decide) bT5_lt
  have bT5_67 : u.basis (E0.getD 299 0) = false := by
    rw [← hT5_67]; exact hi_bit_false c.T5 u.basis 67 (by rw [v.t5Len]; decide) (by omega)
  refine ⟨?_, by rwa [← h5093], by rwa [← h5478]⟩
  intro h hh
  rcases hParkSub h hh with hp | rfl
  · simp only [ParkCopy.hosts, ParkCopy.hostIdx, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [bT129, bT131, bT1_0, bT1_65, bT5_0, bT2_0, bT2_65, bT5_66, bT5_67]
  · exact (st.2.2.2.2.2.2 _ heU_not.1 heU_not.2).trans (heu0 hh)

private theorem cfgC_zeros (s0 : State) (m0 : List Bool)
    (hd0 : regValue cfgC.dst s0.basis = 0) (hT0 : regValue cfgC.liveT s0.basis = 0)
    (hSc0 : regValue cfgC.cleanScratch s0.basis = 0) (hi0 : s0.basis K0.core.cin = false)
    (_ : ControlLoan1589BFFold.eU K0 ∈ ParkCopyS.hostsS E0 → s0.basis (ControlLoan1589BFFold.eU K0) = false)
    (_ : ∀ q ∈ E0, s0.basis q = false) :
    (∀ h ∈ ParkCopyS.hostsS E0, (run cfgC.make m0 s0).basis h = false) ∧
    (run cfgC.make m0 s0).basis 5093 = false ∧ (run cfgC.make m0 s0).basis 5478 = false := by
  have st := cfg_make_correct cfgC cfgC_valid s0 m0 hd0 hT0 hSc0 hi0
  set u := run cfgC.make m0 s0
  set a := regValue cfgC.R.lo s0.basis
  set b := regValue cfgC.R.hi s0.basis
  have hbl : cfgC.bank.length = 129 := cfgC_valid.bankLen
  have ht2 : cfgC.T2.length = 68 := cfgC_valid.t2Len
  have haLt : a < 2 ^ 64 := by
    have : cfgC.R.lo.length = 64 := by simp only [KRegs.lo, SplitCfg.R, List.length_take, hbl]; decide
    simpa [this] using regValue_lt cfgC.R.lo s0.basis
  have hbLt : b < 2 ^ 65 := by
    have : cfgC.R.hi.length = 65 := by simp only [KRegs.hi, SplitCfg.R, List.length_drop, hbl]
    simpa [this] using regValue_lt cfgC.R.hi s0.basis
  have hQ2h : cfgC.Q2.h = 33 := by simp [SplitCfg.Q2, cfgC]
  have hT_eq : cfgC.T = E0.take 132 := by simp [SplitCfg.T, cfgC]
  have hT1_eq : cfgC.T1 = (E0.drop 132).take 66 := rfl
  have hT2_eq : cfgC.T2 = (E0.drop 232).take 68 := rfl
  have h5093 : E0.getD 0 0 = 5093 := by rw [E0_eq]; decide +kernel
  have h5478 : E0.getD 130 0 = 5478 := by rw [E0_eq]; decide +kernel
  have bT0 : u.basis (E0.getD 0 0) = false := by
    have e : cfgC.T.getD 0 0 = E0.getD 0 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact even_bit0_false cfgC.T u.basis (a * b) (by rw [cfgC_valid.tLen]; decide) (by rw [st.2.2.1]; ring)
  have hT_lt : regValue cfgC.T u.basis < 2 ^ 130 := by
    rw [st.2.2.1, Nat.mul_assoc]; have : a * b < 2 ^ 64 * 2 ^ 65 := Nat.mul_lt_mul'' haLt hbLt; omega
  have bT130 : u.basis (E0.getD 130 0) = false := by
    have e : cfgC.T.getD 130 0 = E0.getD 130 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact hi_bit_false cfgC.T u.basis 130 (by rw [cfgC_valid.tLen]; decide) hT_lt
  have bT131 : u.basis (E0.getD 131 0) = false := by
    have e : cfgC.T.getD 131 0 = E0.getD 131 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact hi_bit_false cfgC.T u.basis 131 (by rw [cfgC_valid.tLen]; decide) (by omega)
  have bT1_0 : u.basis (E0.getD 132 0) = false := by
    have e : cfgC.T1.getD 0 0 = E0.getD 132 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false cfgC.T1 u.basis ((a % 2 ^ 32) * (a / 2 ^ 32)) (by rw [cfgC_valid.t1Len]; decide) (by rw [st.2.2.2.1]; ring)
  have bT1_65 : u.basis (E0.getD 197 0) = false := by
    have e : cfgC.T1.getD 65 0 = E0.getD 197 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false cfgC.T1 u.basis 65 (by rw [cfgC_valid.t1Len]; decide) ?_
    rw [st.2.2.2.1, Nat.mul_assoc]
    have h1 : a % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h2 : a / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (a % 2 ^ 32) * (a / 2 ^ 32) < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT2_0 : u.basis (E0.getD 232 0) = false := by
    have e : cfgC.T2.getD 0 0 = E0.getD 232 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false cfgC.T2 u.basis ((b % 2 ^ cfgC.Q2.h) * (b / 2 ^ cfgC.Q2.h))
      (by omega) (by rw [st.2.2.2.2.1]; ring)
  have bT2_67 : u.basis (E0.getD 299 0) = false := by
    have e : cfgC.T2.getD 67 0 = E0.getD 299 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false cfgC.T2 u.basis 67 (by omega) ?_
    rw [st.2.2.2.2.1, hQ2h, Nat.mul_assoc]
    have h1 : b % 2 ^ 33 < 2 ^ 33 := Nat.mod_lt _ (by decide)
    have h2 : b / 2 ^ 33 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (b % 2 ^ 33) * (b / 2 ^ 33) < 2 ^ 33 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  refine ⟨?_, by rwa [← h5093], by rwa [← h5478]⟩
  intro h hh
  simp only [ParkCopyS.hostsS, ParkCopyS.hostIdxS, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl
  exacts [bT131, bT1_0, bT1_65, bT2_0, bT2_67]

/-! ### Branch equivalences (`brC`, `brB`, `brA`) and `coreOK` -/

private theorem mask_union_mem (A B C : List Nat)
    (h : A.all (fun q => (StairSquareBChecks.LT48B.maskL B).testBit q || (StairSquareBChecks.LT48B.maskL C).testBit q) = true) :
    ∀ q ∈ A, q ∈ B ∨ q ∈ C := by
  intro q hq
  have t := List.all_eq_true.mp h q hq
  simp only [Bool.or_eq_true, StairSquareBChecks.LT48B.testBit_maskL, decide_eq_true_eq] at t
  exact t

private theorem cfgA_geom :
    118 + (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).length = cfgA.n ∧
    cfgA.src.length = cfgA.n ∧
    (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).Nodup ∧
    (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ∉ cfgA.bank ∧ h ∉ cfgA.src ∧ h ∉ cfgA.dst ∧
      h ∉ K0.core.out ∧ h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0) ∧
    (G0 :: cfgA.src ++ cfgA.bank).Nodup ∧
    (∀ q ∈ E0, q ∉ cfgA.bank) ∧
    (∀ q ∈ cfgA.workT, q ∈ K0.core.work) ∧
    (∀ q ∈ cfgA.liveT, (q ∈ E0 ∨ q ∈ cfgA.workT) ∧ q ∉ cfgA.bank ∧ q ∉ cfgA.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgA.cleanScratch, (q ∈ K0.foldPad ∨ q ∈ K0.core.work) ∧ q ∉ cfgA.bank ∧ q ∉ cfgA.src ∧
      q ∉ K0.core.out ∧ q ∉ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) ∧
    (∀ q ∈ cfgA.dst, q ∉ cfgA.bank ∧ q ∉ cfgA.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgA.bank, q ∉ K0.core.out) ∧
    (∀ q ∈ cfgA.src, q ∉ K0.core.out) ∧
    (G0 ∉ cfgA.bank ∧ G0 ∉ cfgA.dst ∧ G0 ∉ cfgA.liveT ∧ G0 ∉ cfgA.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgA.dst = cfgA.dst.headD 0 ∧
    (E0.getD 130 0 ∉ cfgA.dst ∧ E0.getD 130 0 ∉ cfgA.liveT ∧ E0.getD 131 0 ∉ cfgA.dst ∧ E0.getD 131 0 ∉ cfgA.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ cfgA.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgA.liveT) ∧
    (cfgA.T5.getD 0 0 = E0.getD 231 0 ∧ cfgA.T5.getD 66 0 = E0.getD 298 0 ∧ cfgA.T5.getD 67 0 = E0.getD 299 0) := by
  have hS : 118 + (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).length = cfgA.n ∧
      cfgA.src.length = cfgA.n ∧ (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).Nodup ∧
      (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
      (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
      G0 ∉ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0) ∧
      (G0 ∉ cfgA.bank ∧ G0 ∉ cfgA.dst ∧ G0 ∉ cfgA.liveT ∧ G0 ∉ cfgA.cleanScratch ∧ G0 ∉ K0.core.out) ∧
      LowZero18Square.cacheWire K0 cfgA.dst = cfgA.dst.headD 0 ∧
      (E0.getD 130 0 ∉ cfgA.dst ∧ E0.getD 130 0 ∉ cfgA.liveT ∧ E0.getD 131 0 ∉ cfgA.dst ∧ E0.getD 131 0 ∉ cfgA.liveT ∧
        ControlLoan1589BFFold.eU K0 ∉ cfgA.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgA.liveT) ∧
      (cfgA.T5.getD 0 0 = E0.getD 231 0 ∧ cfgA.T5.getD 66 0 = E0.getD 298 0 ∧ cfgA.T5.getD 67 0 = E0.getD 299 0) := by
    simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  have hnd : (G0 :: cfgA.src ++ cfgA.bank).Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPB := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPS := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPD := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) cfgA.dst (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPO := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hEB := StairSquareBChecks.LT48B.disj_of_maskL E0 cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hWW := StairSquareBChecks.LT48B.sub_of_maskL cfgA.workT K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLU := mask_union_mem cfgA.liveT E0 cfgA.workT (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLB := StairSquareBChecks.LT48B.disj_of_maskL cfgA.liveT cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLS := StairSquareBChecks.LT48B.disj_of_maskL cfgA.liveT cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLO := StairSquareBChecks.LT48B.disj_of_maskL cfgA.liveT K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSU := mask_union_mem cfgA.cleanScratch K0.foldPad K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSB := StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSS := StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSO := StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSP := StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDB := StairSquareBChecks.LT48B.disj_of_maskL cfgA.dst cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDS := StairSquareBChecks.LT48B.disj_of_maskL cfgA.dst cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDO := StairSquareBChecks.LT48B.disj_of_maskL cfgA.dst K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hBO := StairSquareBChecks.LT48B.disj_of_maskL cfgA.bank K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSrO := StairSquareBChecks.LT48B.disj_of_maskL cfgA.src K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1,
    fun h hh => ⟨hPB h hh, hPS h hh, hPD h hh, hPO h hh, hS.2.2.2.2.1 h hh⟩,
    hS.2.2.2.2.2.1, hnd, hEB, hWW,
    fun q hq => ⟨hLU q hq, hLB q hq, hLS q hq, hLO q hq⟩,
    fun q hq => ⟨hSU q hq, hSB q hq, hSS q hq, hSO q hq, hSP q hq⟩,
    fun q hq => ⟨hDB q hq, hDS q hq, hDO q hq⟩, hBO, hSrO,
    hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.2⟩

private theorem cfgB_geom :
    119 + (ParkCopy.hosts E0).length = cfgB.n ∧
    cfgB.src.length = cfgB.n ∧
    (ParkCopy.hosts E0).Nodup ∧
    (∀ h ∈ ParkCopy.hosts E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopy.hosts E0, h ∉ cfgB.bank ∧ h ∉ cfgB.src ∧ h ∉ cfgB.dst ∧
      h ∉ K0.core.out ∧ h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopy.hosts E0 ∧
    (G0 :: cfgB.src ++ cfgB.bank).Nodup ∧
    (∀ q ∈ E0, q ∉ cfgB.bank) ∧
    (∀ q ∈ cfgB.workT, q ∈ K0.core.work ∨ q = D0) ∧
    (∀ q ∈ cfgB.liveT, (q ∈ E0 ∨ q ∈ cfgB.workT) ∧ q ∉ cfgB.bank ∧ q ∉ cfgB.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgB.cleanScratch, (q ∈ K0.foldPad ∨ q ∈ K0.core.work) ∧ q ∉ cfgB.bank ∧ q ∉ cfgB.src ∧
      q ∉ K0.core.out ∧ q ∉ ParkCopy.hosts E0) ∧
    (∀ q ∈ cfgB.dst, q ∉ cfgB.bank ∧ q ∉ cfgB.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgB.bank, q ∉ K0.core.out) ∧
    (∀ q ∈ cfgB.src, q ∉ K0.core.out) ∧
    (G0 ∉ cfgB.bank ∧ G0 ∉ cfgB.dst ∧ G0 ∉ cfgB.liveT ∧ G0 ∉ cfgB.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgB.dst = cfgB.dst.headD 0 ∧
    (E0.getD 130 0 ∉ cfgB.dst ∧ E0.getD 130 0 ∉ cfgB.liveT ∧ E0.getD 131 0 ∉ cfgB.dst ∧ E0.getD 131 0 ∉ cfgB.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ cfgB.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgB.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ ParkCopy.hosts E0) ∧
    (cfgB.T5.getD 0 0 = E0.getD 231 0 ∧ cfgB.T5.getD 66 0 = E0.getD 298 0 ∧ cfgB.T5.getD 67 0 = E0.getD 299 0) := by
  have hS : 119 + (ParkCopy.hosts E0).length = cfgB.n ∧
      cfgB.src.length = cfgB.n ∧ (ParkCopy.hosts E0).Nodup ∧
      (∀ h ∈ ParkCopy.hosts E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
      (∀ h ∈ ParkCopy.hosts E0, h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
      G0 ∉ ParkCopy.hosts E0 ∧
      (G0 ∉ cfgB.bank ∧ G0 ∉ cfgB.dst ∧ G0 ∉ cfgB.liveT ∧ G0 ∉ cfgB.cleanScratch ∧ G0 ∉ K0.core.out) ∧
      LowZero18Square.cacheWire K0 cfgB.dst = cfgB.dst.headD 0 ∧
      (E0.getD 130 0 ∉ cfgB.dst ∧ E0.getD 130 0 ∉ cfgB.liveT ∧ E0.getD 131 0 ∉ cfgB.dst ∧ E0.getD 131 0 ∉ cfgB.liveT ∧
        ControlLoan1589BFFold.eU K0 ∉ cfgB.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgB.liveT ∧
        ControlLoan1589BFFold.eU K0 ∉ ParkCopy.hosts E0) ∧
      (cfgB.T5.getD 0 0 = E0.getD 231 0 ∧ cfgB.T5.getD 66 0 = E0.getD 298 0 ∧ cfgB.T5.getD 67 0 = E0.getD 299 0) := by
    simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  have hnd : (G0 :: cfgB.src ++ cfgB.bank).Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPB := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPS := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPD := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) cfgB.dst (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPO := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hEB := StairSquareBChecks.LT48B.disj_of_maskL E0 cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hWW : ∀ q ∈ cfgB.workT, q ∈ K0.core.work ∨ q = D0 := by
    have h := mask_union_mem cfgB.workT K0.core.work [D0] (by simp only [cfgB_fast, workTB_lit, K0_eq, D0_eq]; decide +kernel)
    intro q hq; exact (h q hq).imp_right List.mem_singleton.mp
  have hLU := mask_union_mem cfgB.liveT E0 cfgB.workT (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLB := StairSquareBChecks.LT48B.disj_of_maskL cfgB.liveT cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLS := StairSquareBChecks.LT48B.disj_of_maskL cfgB.liveT cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLO := StairSquareBChecks.LT48B.disj_of_maskL cfgB.liveT K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSU := mask_union_mem cfgB.cleanScratch K0.foldPad K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSB := StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSS := StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSO := StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSP := StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch (ParkCopy.hosts E0) (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDB := StairSquareBChecks.LT48B.disj_of_maskL cfgB.dst cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDS := StairSquareBChecks.LT48B.disj_of_maskL cfgB.dst cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDO := StairSquareBChecks.LT48B.disj_of_maskL cfgB.dst K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hBO := StairSquareBChecks.LT48B.disj_of_maskL cfgB.bank K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSrO := StairSquareBChecks.LT48B.disj_of_maskL cfgB.src K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1,
    fun h hh => ⟨hPB h hh, hPS h hh, hPD h hh, hPO h hh, hS.2.2.2.2.1 h hh⟩,
    hS.2.2.2.2.2.1, hnd, hEB, hWW,
    fun q hq => ⟨hLU q hq, hLB q hq, hLS q hq, hLO q hq⟩,
    fun q hq => ⟨hSU q hq, hSB q hq, hSS q hq, hSO q hq, hSP q hq⟩,
    fun q hq => ⟨hDB q hq, hDS q hq, hDO q hq⟩, hBO, hSrO,
    hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.2⟩

private theorem cfgC_geom :
    124 + (ParkCopyS.hostsS E0).length = cfgC.n ∧
    cfgC.src.length = cfgC.n ∧
    (ParkCopyS.hostsS E0).Nodup ∧
    (∀ h ∈ ParkCopyS.hostsS E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopyS.hostsS E0, h ∉ cfgC.bank ∧ h ∉ cfgC.src ∧ h ∉ cfgC.dst ∧
      h ∉ K0.core.out ∧ h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopyS.hostsS E0 ∧
    (G0 :: cfgC.src ++ cfgC.bank).Nodup ∧
    (∀ q ∈ E0, q ∉ cfgC.bank) ∧
    (∀ q ∈ cfgC.workT, q ∈ K0.core.work) ∧
    (∀ q ∈ cfgC.liveT, (q ∈ E0 ∨ q ∈ cfgC.workT) ∧ q ∉ cfgC.bank ∧ q ∉ cfgC.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgC.cleanScratch, (q ∈ K0.foldPad ∨ q ∈ K0.core.work) ∧ q ∉ cfgC.bank ∧ q ∉ cfgC.src ∧
      q ∉ K0.core.out ∧ q ∉ ParkCopyS.hostsS E0) ∧
    (∀ q ∈ cfgC.dst, q ∉ cfgC.bank ∧ q ∉ cfgC.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgC.bank, q ∉ K0.core.out) ∧
    (∀ q ∈ cfgC.src, q ∉ K0.core.out) ∧
    (G0 ∉ cfgC.bank ∧ G0 ∉ cfgC.dst ∧ G0 ∉ cfgC.liveT ∧ G0 ∉ cfgC.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgC.dst = cfgC.dst.headD 0 ∧
    ControlLoan1589BFFold.eU K0 ∉ ParkCopyS.hostsS E0 := by
  have hS : 124 + (ParkCopyS.hostsS E0).length = cfgC.n ∧
      cfgC.src.length = cfgC.n ∧ (ParkCopyS.hostsS E0).Nodup ∧
      (∀ h ∈ ParkCopyS.hostsS E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
      (∀ h ∈ ParkCopyS.hostsS E0, h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
      G0 ∉ ParkCopyS.hostsS E0 ∧
      (G0 ∉ cfgC.bank ∧ G0 ∉ cfgC.dst ∧ G0 ∉ cfgC.liveT ∧ G0 ∉ cfgC.cleanScratch ∧ G0 ∉ K0.core.out) ∧
      LowZero18Square.cacheWire K0 cfgC.dst = cfgC.dst.headD 0 ∧
      ControlLoan1589BFFold.eU K0 ∉ ParkCopyS.hostsS E0 := by
    simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  have hnd : (G0 :: cfgC.src ++ cfgC.bank).Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPB := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPS := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPD := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) cfgC.dst (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPO := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hEB := StairSquareBChecks.LT48B.disj_of_maskL E0 cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hWW := StairSquareBChecks.LT48B.sub_of_maskL cfgC.workT K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLU := mask_union_mem cfgC.liveT E0 cfgC.workT (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLB := StairSquareBChecks.LT48B.disj_of_maskL cfgC.liveT cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLS := StairSquareBChecks.LT48B.disj_of_maskL cfgC.liveT cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLO := StairSquareBChecks.LT48B.disj_of_maskL cfgC.liveT K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSU := mask_union_mem cfgC.cleanScratch K0.foldPad K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSB := StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSS := StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSO := StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSP := StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch (ParkCopyS.hostsS E0) (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDB := StairSquareBChecks.LT48B.disj_of_maskL cfgC.dst cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDS := StairSquareBChecks.LT48B.disj_of_maskL cfgC.dst cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDO := StairSquareBChecks.LT48B.disj_of_maskL cfgC.dst K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hBO := StairSquareBChecks.LT48B.disj_of_maskL cfgC.bank K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSrO := StairSquareBChecks.LT48B.disj_of_maskL cfgC.src K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1,
    fun h hh => ⟨hPB h hh, hPS h hh, hPD h hh, hPO h hh, hS.2.2.2.2.1 h hh⟩,
    hS.2.2.2.2.2.1, hnd, hEB, hWW,
    fun q hq => ⟨hLU q hq, hLB q hq, hLS q hq, hLO q hq⟩,
    fun q hq => ⟨hSU q hq, hSB q hq, hSS q hq, hSO q hq, hSP q hq⟩,
    fun q hq => ⟨hDB q hq, hDS q hq, hDO q hq⟩, hBO, hSrO,
    hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2⟩

private theorem e0_dis_bodyA : ∀ q ∈ E0, q ∉ wires bodyA := fun q hq hw => by
  have hs := bodyA_ok.support hw
  rcases Finset.mem_insert.mp hs with rfl | hmem
  · exact (by rw [E0_eq, D0_eq]; decide +kernel : D0 ∉ E0) hq
  · exact hext.away q hq (List.mem_toFinset.mp hmem)

private theorem e0_dis_bodyB : ∀ q ∈ E0, q ∉ wires bodyB := fun q hq hw =>
  hext.away q hq (List.mem_toFinset.mp (bodyB_ok.support hw))

private theorem e0_dis_bodyC : ∀ q ∈ E0, q ∉ wires bodyC := fun q hq hw => by
  have hs := bodyC_ok.support hw
  rcases Finset.mem_insert.mp hs with rfl | hmem
  · exact (by rw [E0_eq, D0_eq]; decide +kernel : D0 ∉ E0) hq
  · exact hext.away q hq (List.mem_toFinset.mp hmem)

private theorem eU_zero_of_prod0 (b : BasisState) (hp0 : regValue K0.core.product b = 0) :
    b (ControlLoan1589BFFold.eU K0) = false := by
  have hm : ControlLoan1589BFFold.eU K0 ∈ K0.core.product := by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  exact (regValue_zero _ _).mp hp0 _ hm

private theorem prod_eq_of_take256 (b : BasisState) (hp256 : b (K0.core.product.getD 256 0) = false)
    (hp257 : b (K0.core.product.getD 257 0) = false) :
    regValue K0.core.product b = regValue (K0.core.product.take 256) b := by
  have hl : K0.core.product.length = 258 := hwK.core.product
  have hdrop : K0.core.product.drop 256 = [K0.core.product.getD 256 0, K0.core.product.getD 257 0] := by
    apply List.ext_getElem (by simp [hl])
    intro i hi1 hi2
    have hi : i = 0 ∨ i = 1 := by simp [hl] at hi1; omega
    rcases hi with rfl | rfl <;> simp [List.getD_eq_getElem?_getD, hl]
  have h0 : regValue [K0.core.product.getD 256 0, K0.core.product.getD 257 0] b = 0 := by
    simp only [regValue, List.foldr_cons, List.foldr_nil, hp256, hp257]; rfl
  conv_lhs => rw [← List.take_append_drop 256 K0.core.product, regValue_append, hdrop, h0]
  simp

theorem brA_run_eq (t : State) (m : List Bool) (pre : BranchPre t) :
    run brA m t = run (recBrA bodyA) m t := by
  have g := cfgA_geom
  have h128 : regValue K0.core.low t.basis < 2 ^ 128 := by
    simpa [K0.core.low_length hwK.core] using regValue_lt K0.core.low t.basis
  let M := if t.basis G0 then regValue K0.core.low t.basis else 0
  let O := regValue K0.core.out t.basis
  let V := A161Low4Offsets.resAFlow (M ^ 2) O (t.basis G0)
  have hMlt : M < 2 ^ 128 := by dsimp only [M]; split_ifs <;> omega
  have hRec := A161Low4Branch.swapped_correct K0 hwK E0 G0 controlND
    (regValue K0.core.low t.basis) O pre.outLt t m rfl rfl pre.prod0 pre.clean pre.sum0 hext pre.ext0
    D0 (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (B3CarryPort.pool1540_facts L0 hw0 hn0).2.1 pre.d0
    bodyA bodyA_ok.support bodyA_ok.eUfree bodyA_ok.frame
  have hNew := withSplitPark_correct cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA V
    g.1 (by decide) g.2.1 g.2.2.1 g.2.2.2.1
    (fun h hh => (g.2.2.2.2.1 h hh).1) (fun h hh => (g.2.2.2.2.1 h hh).2.1)
    (fun h hh => (g.2.2.2.2.1 h hh).2.2.1) (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.1)
    g.2.2.2.2.2.1 (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.2) g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.1
    (fun q hq => Or.inl (g.2.2.2.2.2.2.2.2.1 q hq)) e0_dis_bodyA bodyA_avoids_workTA (fun _ => bodyA_ok.eUfree)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2) g.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun s0 m0 hd0 hT0 hSc0 hi0 heu0 he0 =>
      cfg128_zeros cfgA cfgA_valid rfl g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        (by simp [SplitCfg.T, cfgA, List.take_take]) rfl rfl _
        (fun h hh => by simp only [ParkCopy10.hosts10, List.mem_append, List.mem_singleton] at hh; exact hh)
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2⟩
        s0 m0 hd0 hT0 hSc0 hi0 heu0 he0)
    t m pre.clean
    ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp pre.prod0 q (List.mem_of_mem_take hq)))
    pre.ext0 pre.d0 (fun _ => eU_zero_of_prod0 t.basis pre.prod0)
    (fun t' m' hdst hkeep => by
      have h256_dis : ∀ q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh, K0.core.workHigh,
          K0.core.cin, K0.core.normFlag, K0.core.modFlag, K0.core.product.getD 256 0, K0.core.product.getD 257 0,
          K0.core.sumCarry, D0, G0], q ∉ cfgA.dst :=
        StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [cfgA_fast, K0_eq, D0_eq, G0_eq]; decide +kernel)
      have h256_in : K0.core.product.getD 256 0 ∈ K0.core.product ∧ K0.core.product.getD 257 0 ∈ K0.core.product :=
        ⟨DiagSq.getD_in _ 256 (by rw [hwK.core.product]; decide), DiagSq.getD_in _ 257 (by rw [hwK.core.product]; decide)⟩
      have hprod : regValue K0.core.product t'.basis = M ^ 2 := by
        rw [prod_eq_of_take256 t'.basis
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.1))
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.2))]
        exact hdst
      have hpc : K0.PairClean t'.basis := ⟨
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.pad,
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.work,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.productHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.outHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.workHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.cin,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.normFlag,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.modFlag⟩
      have hG : t'.basis G0 = t.basis G0 := hkeep G0 (h256_dis _ (by simp))
      have hout : regValue K0.core.out t'.basis = O :=
        regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.2 hq))
      have hfr := bodyA_ok.frame t'.basis M hMlt hprod hpc ((hkeep _ (h256_dis _ (by simp))).trans pre.sum0) O pre.outLt
        (fun hg => by rw [hG] at hg; simp [M, hg]) ((hkeep _ (h256_dis _ (by simp))).trans pre.d0)
        t' m' ⟨hout, fun _ _ => rfl⟩
      rw [hG] at hfr
      exact ⟨hfr.1, hfr.2.1, hfr.2.2⟩)
  exact state_eq_of_out _ _ (hNew.1.trans hRec.1.symm)
    (by simpa [V, M, O, recBrA, A161Low4Branch.branch] using hNew.2.1.trans hRec.2.1.symm)
    (fun q hq => (hNew.2.2 q hq).trans (hRec.2.2 q hq).symm)

theorem brB_run_eq (t : State) (m : List Bool) (pre : BranchPre t) :
    run brB m t = run (recBrB bodyB) m t := by
  have g := cfgB_geom
  have h128 : regValue K0.core.high t.basis < 2 ^ 128 := by
    simpa [K0.core.high_length hwK.core] using regValue_lt K0.core.high t.basis
  let M := if t.basis G0 then regValue K0.core.high t.basis else 0
  let O := regValue K0.core.out t.basis
  let V := ControlLoan1589BFFold.resBF (M ^ 2) O (t.basis G0)
  have hMlt : M < 2 ^ 128 := by dsimp only [M]; split_ifs <;> omega
  have hRec := StairSquareAssembly.recBrB_correct bodyB bodyB_ok (regValue K0.core.high t.basis) O
    pre.outLt t m rfl rfl pre.prod0 pre.clean pre.sum0 pre.ext0
  have hNew := withSplitPark_correct cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB V
    g.1 (by decide) g.2.1 g.2.2.1 g.2.2.2.1
    (fun h hh => (g.2.2.2.2.1 h hh).1) (fun h hh => (g.2.2.2.2.1 h hh).2.1)
    (fun h hh => (g.2.2.2.2.1 h hh).2.2.1) (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.1)
    g.2.2.2.2.2.1 (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.2) g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.1 e0_dis_bodyB bodyB_avoids_workTB
    (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2) g.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun s0 m0 hd0 hT0 hSc0 hi0 heu0 he0 =>
      cfg128_zeros cfgB cfgB_valid rfl g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        (by simp [SplitCfg.T, cfgB, List.take_take]) rfl rfl _ (fun _ hh => Or.inl hh)
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1⟩
        s0 m0 hd0 hT0 hSc0 hi0 heu0 he0)
    t m pre.clean
    ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp pre.prod0 q (List.mem_of_mem_take hq)))
    pre.ext0 pre.d0 (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2)
    (fun t' m' hdst hkeep => by
      have h256_dis : ∀ q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh, K0.core.workHigh,
          K0.core.cin, K0.core.normFlag, K0.core.modFlag, K0.core.product.getD 256 0, K0.core.product.getD 257 0,
          K0.core.sumCarry, G0], q ∉ cfgB.dst :=
        StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [cfgB_fast, K0_eq, G0_eq]; decide +kernel)
      have h256_in : K0.core.product.getD 256 0 ∈ K0.core.product ∧ K0.core.product.getD 257 0 ∈ K0.core.product :=
        ⟨DiagSq.getD_in _ 256 (by rw [hwK.core.product]; decide), DiagSq.getD_in _ 257 (by rw [hwK.core.product]; decide)⟩
      have hprod : regValue K0.core.product t'.basis = M ^ 2 := by
        rw [prod_eq_of_take256 t'.basis
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.1))
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.2))]
        exact hdst
      have hpc : K0.PairClean t'.basis := ⟨
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.pad,
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.work,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.productHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.outHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.workHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.cin,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.normFlag,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.modFlag⟩
      have hG : t'.basis G0 = t.basis G0 := hkeep G0 (h256_dis _ (by simp))
      have hout : regValue K0.core.out t'.basis = O :=
        regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.2 hq))
      have hhi : regValue K0.core.high t'.basis = regValue K0.core.high t.basis :=
        regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.1 hq))
      have hg0 : t'.basis G0 = false → M = 0 := fun hg => by rw [hG] at hg; simp [M, hg]
      have hfr := bodyB_ok.frame t'.basis M hMlt hprod hpc ((hkeep _ (h256_dis _ (by simp))).trans pre.sum0) O pre.outLt
        hg0 (by rw [hG, hhi]) t' m' ⟨hout, fun _ _ => rfl⟩
      rw [ControlLoan1589BFFold.bO4_eq M O (t'.basis G0) hMlt hg0 pre.outLt, hG] at hfr
      exact ⟨hfr.1, hfr.2.1, hfr.2.2⟩)
  exact state_eq_of_out _ _ (hNew.1.trans hRec.1.symm)
    (by simpa [V, M, O] using hNew.2.1.trans hRec.2.1.symm)
    (fun q hq => (hNew.2.2 q hq).trans (hRec.2.2 q hq).symm)

theorem brC_run_eq (t : State) (m : List Bool) (pre : BranchPre t) :
    run brC m t = run (recBrC bodyC) m t := by
  have g := cfgC_geom
  have nd := (List.nodup_cons.mp controlND).2
  have dis := K0.measured_sum_disjoint nd
  have ctrlAway : G0 ∉ K0.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp controlND G0
    have pos := List.count_pos_iff.mpr bad
    have sumBound := K0.measured_sum_count G0
    simp only [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, List.count_append, List.count_cons,
      List.count_nil, beq_self_eq_true, if_true] at h sumBound
    omega
  set A := regValue K0.core.low t.basis
  set B := regValue K0.core.sum t.basis
  set O := regValue K0.core.out t.basis
  have hLowLt : A < 2 ^ 128 := by
    simpa [A, K0.core.low_length hwK.core] using regValue_lt K0.core.low t.basis
  have hSumEq : B = regValue K0.core.high t.basis := by
    simp [B, CuccaroStreamedSquareLayout.sum, regValue_append, regValue, pre.sum0]
  have hHiLt : regValue K0.core.high t.basis < 2 ^ 128 := by
    simpa [K0.core.high_length hwK.core] using regValue_lt K0.core.high t.basis
  have hSumBd : A + B < 2 ^ 129 := by rw [hSumEq]; omega
  let midNew := withSplitPark cfgC 124 (ParkCopyS.hostsS E0) bodyC
  obtain ⟨r1, mC, eC⟩ := kseq (OwnDiagAll12Square.gPrep K0 ++ midNew) (OwnDiagAll12Square.gClear K0) m t
  obtain ⟨mP, mM, eM⟩ := kseq (OwnDiagAll12Square.gPrep K0) midNew r1 t
  have hbrC : run brC m t = run (OwnDiagAll12Square.gClear K0) mC (run midNew mM (run (OwnDiagAll12Square.gPrep K0) mP t)) := by
    change run ((OwnDiagAll12Square.gPrep K0 ++ midNew) ++ OwnDiagAll12Square.gClear K0) m t = _
    rw [eC, eM]
  have hprep := OwnDiagAll12Square.gPrep_frame K0 hwK nd t.basis A B rfl hSumBd
    (PairClean.corePad K0 t.basis pre.clean) pre.clean.cin pre.clean.work t mP ⟨rfl, fun _ _ => rfl⟩
  generalize hu : run (OwnDiagAll12Square.gPrep K0) mP t = u at hbrC hprep ⊢
  have u_prod0 : regValue K0.core.product u.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans pre.prod0
  have u_out : regValue K0.core.out u.basis = O :=
    regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))
  have u_ctrl : u.basis G0 = t.basis G0 := hprep.2.2 G0 ctrlAway
  have u_clean : K0.PairClean u.basis := by
    have keep (q : Wire) (hq : q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh,
        K0.core.workHigh, K0.core.cin, K0.core.normFlag, K0.core.modFlag]) : u.basis q = t.basis q :=
      hprep.2.2 q (K0.measured_sum_aux_away nd q hq)
    exact ⟨(regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans pre.clean.pad,
      (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans pre.clean.work,
      (keep _ (by simp)).trans pre.clean.productHigh, (keep _ (by simp)).trans pre.clean.outHigh,
      (keep _ (by simp)).trans pre.clean.workHigh, (keep _ (by simp)).trans pre.clean.cin,
      (keep _ (by simp)).trans pre.clean.normFlag, (keep _ (by simp)).trans pre.clean.modFlag⟩
  have u_ext0 : regValue E0 u.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => hext.away q hq (OwnDiagAll12Square.sum_in K0 G0 q bad)))).trans pre.ext0
  have u_d0 : u.basis D0 = false :=
    (hprep.2.2 D0 (fun bad => (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (OwnDiagAll12Square.sum_in K0 G0 D0 bad))).trans pre.d0
  let M := if t.basis G0 then A + B else 0
  let V := C163Low4Offsets.resCFlow (t.basis G0) (M ^ 2) O
  have hM_eq : (if u.basis G0 = true then regValue cfgC.src u.basis else 0) = M := by
    change (if u.basis G0 = true then regValue K0.core.sum u.basis else 0) = M
    rw [u_ctrl, hprep.2.1]
  have used := withSplitPark_correct cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC V
    g.1 (by decide) g.2.1 g.2.2.1 g.2.2.2.1
    (fun h hh => (g.2.2.2.2.1 h hh).1) (fun h hh => (g.2.2.2.2.1 h hh).2.1)
    (fun h hh => (g.2.2.2.2.1 h hh).2.2.1) (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.1)
    g.2.2.2.2.2.1 (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.2) g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.1
    (fun q hq => Or.inl (g.2.2.2.2.2.2.2.2.1 q hq)) e0_dis_bodyC bodyC_avoids_workTC
    (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2) g.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    cfgC_zeros u mM u_clean u_prod0 u_ext0 u_d0
    (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (fun t' m' hdst hkeep => by
      have haux : ∀ q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh, K0.core.workHigh,
            K0.core.cin, K0.core.normFlag, K0.core.modFlag, D0, G0], q ∉ cfgC.dst :=
        StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [cfgC_fast, K0_eq, D0_eq, G0_eq]; decide +kernel)
      have hpc : K0.PairClean t'.basis := ⟨
        (regValue_congr _ _ _ (fun q hq => hkeep q (haux q (by simp [hq])))).trans u_clean.pad,
        (regValue_congr _ _ _ (fun q hq => hkeep q (haux q (by simp [hq])))).trans u_clean.work,
        (hkeep _ (haux _ (by simp))).trans u_clean.productHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.outHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.workHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.cin,
        (hkeep _ (haux _ (by simp))).trans u_clean.normFlag,
        (hkeep _ (haux _ (by simp))).trans u_clean.modFlag⟩
      have hG : t'.basis G0 = t.basis G0 := (hkeep G0 (haux _ (by simp))).trans u_ctrl
      have hout : regValue K0.core.out t'.basis = O :=
        (regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.2 hq))).trans u_out
      have hdstM : regValue K0.core.product t'.basis = M ^ 2 := by rw [← hM_eq]; exact hdst
      have hfr := bodyC_ok.frame t'.basis M hdstM hpc (fun hg => by rw [hG] at hg; simp [M, hg])
        ((hkeep _ (haux _ (by simp))).trans u_d0) O pre.outLt t' m' ⟨hout, fun _ _ => rfl⟩
      rw [hG] at hfr
      exact ⟨hfr.1, hfr.2.1, hfr.2.2⟩)
  change (run midNew mM u).phase = u.phase ∧ regValue K0.core.out (run midNew mM u).basis = V ∧
    ∀ q, q ∉ K0.core.out → (run midNew mM u).basis q = u.basis q at used
  generalize hv : run midNew mM u = v at hbrC used ⊢
  let restoreBase : BasisState := fun q => if q ∈ K0.core.out then v.basis q else t.basis q
  have lowOutAway (q : Wire) (hq : q ∈ K0.core.low) : q ∉ K0.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, List.count_append, List.count_cons, List.count_nil] at h
    omega
  have lowRestore : regValue K0.core.low restoreBase = A :=
    regValue_congr _ _ _ (fun q hq => by simp [restoreBase, lowOutAway q hq])
  have padRestore : regValue K0.core.pad restoreBase = 0 :=
    (regValue_congr _ _ _ (fun q hq => by
      have away := (K0.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad, hq])).2
      simp [restoreBase, away])).trans (PairClean.corePad K0 t.basis pre.clean)
  have cinRestore : restoreBase K0.core.cin = false := by
    have away := (K0.pairAuxAway nd K0.core.cin (by simp)).2
    simp [restoreBase, away, pre.clean.cin]
  have workRestore : regValue K0.core.work restoreBase = 0 :=
    (regValue_congr _ _ _ (fun q hq => by
      have away := (K0.pairAuxAway nd q (by simp [hq])).2
      simp [restoreBase, away])).trans pre.clean.work
  have clearPre : SquareFrame K0.core.sum restoreBase (A + B) v.basis := by
    refine ⟨(regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans hprep.2.1, ?_⟩
    intro q hq
    by_cases outSite : q ∈ K0.core.out
    · simp [restoreBase, outSite]
    · simp only [restoreBase, if_neg outSite]
      exact (used.2.2 q outSite).trans (hprep.2.2 q hq)
  have cleared := OwnDiagAll12Square.gClear_frame K0 hwK nd restoreBase A B lowRestore hSumBd padRestore cinRestore workRestore v mC clearPre
  generalize hout : run (OwnDiagAll12Square.gClear K0) mC v = out at hbrC cleared ⊢
  have hNew : out.phase = t.phase ∧ regValue K0.core.out out.basis = V ∧ ∀ q, q ∉ K0.core.out → out.basis q = t.basis q := by
    refine ⟨cleared.1.trans (used.1.trans hprep.1), ?_, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => by
        have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
        simpa [restoreBase, hq] using same)).trans used.2.1
    · intro q hq
      by_cases sumSite : q ∈ K0.core.sum
      · exact (regValue_eq_iff K0.core.sum out.basis t.basis).mp cleared.2.1 q sumSite
      · have same := cleared.2.2 q sumSite
        simpa [restoreBase, hq] using same
  have hRec := SumSavedCBranch.branch_correct K0 hwK E0 G0 controlND A B O pre.outLt t m rfl rfl hSumBd rfl
    pre.prod0 pre.clean hext pre.ext0 D0 (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (B3CarryPort.pool1540_facts L0 hw0 hn0).2.1
    pre.d0 bodyC bodyC_ok.support bodyC_ok.frame
  rw [hbrC]
  exact state_eq_of_out _ _ (hNew.1.trans hRec.1.symm)
    (by simpa [V, M, recBrC] using hNew.2.1.trans hRec.2.1.symm)
    (fun q hq => (hNew.2.2 q hq).trans (hRec.2.2 q hq).symm)

/-- Top-level core correctness of the split-65 concrete square core. -/
theorem coreOK : CoreOK L0 (coreN brC brB brA) :=
  coreN_coreOK bodyA bodyB bodyC brC brB brA bodyA_ok bodyB_ok bodyC_ok brC_run_eq brB_run_eq brA_run_eq

/-! ### Exact Toffoli, measurement, and gate-slot counts -/

theorem brA_counts :
    toffoliCount brA + 293 = toffoliCount (recBrA A109SignResearch.body) ∧
    measurementCount brA + 197 = measurementCount (recBrA A109SignResearch.body) := by
  have hk := cfg_counts_H cfgA cfgA_valid rfl K0.core.low (K0.core.product.take 256)
    (K0.core.low_length hwK.core) (by rw [List.length_take, hwK.core.product]; decide)
  have hb := bodyA_counts
  have hc := InnerLinearCopy.copy_counts118 G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.low.take 118) ((K0.inputBank.take K0.core.low.length).take 118)
    (by simp [K0.core.low_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.low_length hwK.core])
  have hbl : K0.core.low.length = 128 := K0.core.low_length hwK.core
  dsimp only at hk
  simp only [brA, withSplitPark, recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10,
    ParkCopy10.pA, ParkCopy10.pM, ParkCopy10.pE1, ParkCopy10.pD, ParkCopy10.pMI, ParkCopy10.pB,
    ParkCopy10.pC1, ParkCopy10.pMO, ParkCopy10.pCL, ParkCopy10.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgA, hbl, toffoliCount_append, measurementCount_append,
    renameProgram_counts] at hk hc ⊢
  exact ⟨by clear * - hk hb hc; omega, by clear * - hk hb hc; omega⟩

theorem brB_counts :
    toffoliCount brB + 283 = toffoliCount (recBrB B95PaddedResearch.body) ∧
    measurementCount brB + 197 = measurementCount (recBrB B95PaddedResearch.body) := by
  have hk := cfg_counts_H cfgB cfgB_valid rfl K0.core.high (K0.core.product.take 256)
    (K0.core.high_length hwK.core) (by rw [List.length_take, hwK.core.product]; decide)
  have hb := bodyB_counts
  have hc := InnerLinearCopy.copy_counts G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.high.take 119) ((K0.inputBank.take K0.core.high.length).take 119)
    (by simp [K0.core.high_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.high_length hwK.core])
  have hbl : K0.core.high.length = 128 := K0.core.high_length hwK.core
  dsimp only at hk
  simp only [brB, withSplitPark, recBrB, ParkCopy.withLowK2P,
    ParkCopy.pA, ParkCopy.pM, ParkCopy.pE1, ParkCopy.pD, ParkCopy.pMI, ParkCopy.pB,
    ParkCopy.pC1, ParkCopy.pMO, ParkCopy.pCL, ParkCopy.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgB, hbl, toffoliCount_append, measurementCount_append,
    renameProgram_counts] at hk hc ⊢
  exact ⟨by clear * - hk hb hc; omega, by clear * - hk hb hc; omega⟩

theorem brC_counts :
    toffoliCount brC + 289 = toffoliCount (recBrC C105SignResearch.body) ∧
    measurementCount brC + 195 = measurementCount (recBrC C105SignResearch.body) := by
  have hk := cfg_counts_S cfgC cfgC_valid rfl K0.core.sum K0.core.product
    (K0.core.sum_length hwK.core) hwK.core.product
  have hb := bodyC_counts
  have srcCount (q : Wire) : K0.core.sum.count q ≤ (K0.core.y ++ [K0.core.sumCarry]).count q := by
    have h1 := (List.take_sublist 128 (K0.core.y.drop 128)).count_le q
    have h2 := (List.drop_sublist 128 K0.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum, CuccaroStreamedSquareLayout.high, List.count_append] at h1 ⊢; omega
  have hall := LowZero18LowK.kg_nodup K0 G0 controlND E0 K0.core.sum K0.core.product srcCount (fun _ => le_rfl) hext.nodup hext.away
  have sp := LowZero18LowK.kg_spec K0 hwK E0 K0.core.sum K0.core.product
    (by rw [K0.core.sum_length hwK.core]; decide) (by rw [K0.core.sum_length hwK.core])
    (by rw [K0.core.sum_length hwK.core, hwK.core.product]) hext.len hall
  have hcl := SumSavedSquare.clear_counts K0 hwK E0 K0.core.sum K0.core.product hext.len (K0.core.sum_length hwK.core) sp hall
  have hbl : K0.core.sum.length = 129 := K0.core.sum_length hwK.core
  dsimp only at hk
  simp only [brC, withSplitPark, recBrC, SumSavedCBranch.branch, SumSavedPark.withLowK2S, SumSavedPark.pCL,
    ParkCopyS.pA, ParkCopyS.pM, ParkCopyS.pE1, ParkCopyS.pD, ParkCopyS.pMI, ParkCopyS.pB,
    ParkCopyS.pC1, ParkCopyS.pMO, ParkCopyS.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgC, hbl, toffoliCount_append, measurementCount_append,
    renameProgram_counts] at hk hcl ⊢
  exact ⟨by clear * - hk hb hcl; omega, by clear * - hk hb hcl; omega⟩

theorem square_counts (k : Fp) :
    toffoliCount (squareN brC brB brA k) + 865 = toffoliCount (A161Generic.squareEntry L0 k) ∧
    measurementCount (squareN brC brB brA k) + 589 = measurementCount (A161Generic.squareEntry L0 k) := by
  have cA := brA_counts; have cB := brB_counts; have cC := brC_counts
  have e1 : toffoliCount (StairSquareEntryR.entryRH (k - (C163Low4Offsets.delta : Fp))) =
        toffoliCount (E1ReflectedPlacement.entryR L0 (k - (C163Low4Offsets.delta : Fp))) ∧
      measurementCount (StairSquareEntryR.entryRH (k - (C163Low4Offsets.delta : Fp))) =
        measurementCount (E1ReflectedPlacement.entryR L0 (k - (C163Low4Offsets.delta : Fp))) :=
    StairSquareEntryR.entryRH_counts _
  rw [recordSquare_eq, SumSavedB95Square.program, StairSquareAssembly.fastCore_eq, StairSquareFinal.branchBF760_rec]
  simp only [squareN, placedN, coreN, SquareCarryLoan719BF.place,
    toffoliCount_append, measurementCount_append, renameProgram_counts]
  exact ⟨by clear * - cA cB cC e1; omega, by clear * - cA cB cC e1; omega⟩

theorem brA_slots_le :
    Challenge.gateSlots brA ≤ Challenge.gateSlots (recBrA A109SignResearch.body) + 1830000 := by
  have hk := cfg_slots_bound cfgA cfgA_valid
  have hb := bodyA_slots
  have hc := InnerLinearCopy.copy_slots118 G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.low.take 118) ((K0.inputBank.take K0.core.low.length).take 118)
    (by simp [K0.core.low_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.low_length hwK.core])
  have hbl : K0.core.low.length = 128 := K0.core.low_length hwK.core
  simp only [brA, withSplitPark, recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10,
    ParkCopy10.pA, ParkCopy10.pM, ParkCopy10.pE1, ParkCopy10.pD, ParkCopy10.pMI, ParkCopy10.pB,
    ParkCopy10.pC1, ParkCopy10.pMO, ParkCopy10.pCL, ParkCopy10.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgA, hbl, Challenge.gateSlots_append, Baselines.rename_gateSlots] at hk hc ⊢
  clear * - hk hb hc; omega

theorem brB_slots_le :
    Challenge.gateSlots brB ≤ Challenge.gateSlots (recBrB B95PaddedResearch.body) + 1830000 := by
  have hk := cfg_slots_bound cfgB cfgB_valid
  have hb := bodyB_slots
  have hc := InnerLinearCopy.copy_slots G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.high.take 119) ((K0.inputBank.take K0.core.high.length).take 119)
    (by simp [K0.core.high_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.high_length hwK.core])
  have hbl : K0.core.high.length = 128 := K0.core.high_length hwK.core
  simp only [brB, withSplitPark, recBrB, ParkCopy.withLowK2P,
    ParkCopy.pA, ParkCopy.pM, ParkCopy.pE1, ParkCopy.pD, ParkCopy.pMI, ParkCopy.pB,
    ParkCopy.pC1, ParkCopy.pMO, ParkCopy.pCL, ParkCopy.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgB, hbl, Challenge.gateSlots_append, Baselines.rename_gateSlots] at hk hc ⊢
  clear * - hk hb hc; omega

theorem brC_slots_le :
    Challenge.gateSlots brC ≤ Challenge.gateSlots (recBrC C105SignResearch.body) + 1830000 := by
  have hk := cfg_slots_bound cfgC cfgC_valid
  have hb := bodyC_slots
  have hbl : K0.core.sum.length = 129 := K0.core.sum_length hwK.core
  simp only [brC, withSplitPark, recBrC, SumSavedCBranch.branch, SumSavedPark.withLowK2S, SumSavedPark.pCL,
    ParkCopyS.pA, ParkCopyS.pM, ParkCopyS.pE1, ParkCopyS.pD, ParkCopyS.pMI, ParkCopyS.pB,
    ParkCopyS.pC1, ParkCopyS.pMO, ParkCopyS.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgC, hbl, Challenge.gateSlots_append, Baselines.rename_gateSlots] at hk ⊢
  clear * - hk hb; omega

theorem square_slots_le (k : Fp) :
    Challenge.gateSlots (squareN brC brB brA k) ≤ Challenge.gateSlots (A161Generic.squareEntry L0 k) + 5490000 := by
  have sA := brA_slots_le; have sB := brB_slots_le; have sC := brC_slots_le
  have e := squareN_slots brC brB brA k
  have r : Challenge.gateSlots (A161Generic.squareEntry L0 k) =
      Challenge.gateSlots (recBrC C105SignResearch.body) + Challenge.gateSlots (recBrB B95PaddedResearch.body) +
        Challenge.gateSlots (recBrA A109SignResearch.body) +
        Challenge.gateSlots (E1ReflectedPlacement.entryR L0 (k - (C163Low4Offsets.delta : Fp))) := by
    rw [recordSquare_eq, SumSavedB95Square.program, StairSquareAssembly.fastCore_eq, StairSquareFinal.branchBF760_rec]
    simp only [SquareCarryLoan719BF.place, Challenge.gateSlots_append, Baselines.rename_gateSlots]
  rw [e, r]; clear * - sA sB sC; omega

/-! ### Physicality, wire support, and hole avoidance -/

private theorem dummies_physical (hs : List Wire) : GatePhysical (ParkCopy.dummies hs) := by
  rw [GatePhysical]
  intro x hx
  simp only [ParkCopy.dummies, List.mem_map] at hx
  rcases hx with ⟨a, _, rfl⟩
  simp [RecordedQuantum.PhysicalInstr]

private theorem dummies_wires (hs : List Wire) : wires (ParkCopy.dummies hs) ⊆ hs.toFinset := by
  induction hs with
  | nil => simp [ParkCopy.dummies, wires]
  | cons a hs ih =>
    intro q hq
    rw [ParkCopy.dummies, List.map_cons, wires] at hq
    rcases Finset.mem_union.mp hq with h | h
    · simp [Instr.wires, ECDSAAdd.correctionWires] at h; simp [h]
    · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (ih h)))

private theorem move_physical (a b : List Wire) (hnd : (a ++ b).Nodup) :
    GatePhysical (ParkCopy.move a b) := by
  have hnd' : (b ++ a).Nodup := (List.perm_append_comm.nodup_iff).mp hnd
  simp only [ParkCopy.move, gatePhysical_append]
  exact ⟨copyRegister_physical none a b hnd (by simp), copyRegister_physical none b a hnd' (by simp)⟩

private theorem move_wires (a b : List Wire) : wires (ParkCopy.move a b) ⊆ (a ++ b).toFinset := by
  intro q hq
  simp only [ParkCopy.move, wires_append, Finset.mem_union] at hq
  rcases hq with h | h
  · have := copyRegister_wires_subset none a b h
    simpa [Option.toList_none] using this
  · have := copyRegister_wires_subset none b a h
    simp only [Option.toList_none, List.nil_append, List.mem_toFinset, List.mem_append] at this ⊢
    exact this.symm

private theorem withSplitPark_physical (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program) (hbody : GatePhysical body)
    (hkLen : keepBits + parkHosts.length = c.n) (hkPos : 0 < keepBits) (hsrcLen : c.src.length = c.n)
    (hParkNd : parkHosts.Nodup) (hParkDisBank : ∀ h ∈ parkHosts, h ∉ c.bank)
    (hSrcDis : (G0 :: c.src ++ c.bank).Nodup)
    (hCacheNotBank : LowZero18Square.cacheWire K0 c.dst ∉ c.bank) :
    GatePhysical (withSplitPark c keepBits parkHosts body) := by
  have hbankLen : c.bank.length = c.n := v.bankLen
  have hndSB : (c.src ++ c.bank).Nodup := (List.nodup_cons.mp hSrcDis).2
  have hG0B : ∀ x ∈ some G0, x ∉ c.bank := fun x hx => by
    cases Option.some.inj hx; exact fun hb => (List.nodup_cons.mp hSrcDis).1 (List.mem_append_right _ hb)
  have hndMask : (G0 :: c.src.take keepBits ++ c.bank.take keepBits).Nodup :=
    list_nodup_of_count_le hSrcDis (fun q => by
      have a := (List.take_sublist keepBits c.src).count_le q
      have b := (List.take_sublist keepBits c.bank).count_le q
      simp only [List.count_cons, List.count_append]; omega)
  have hndMP : (c.bank.drop keepBits ++ parkHosts).Nodup :=
    List.nodup_append.mpr ⟨((List.nodup_append.mp hndSB).2.1).sublist (List.drop_sublist _ _), hParkNd,
      fun q hq r hr heq => hParkDisBank r hr (heq ▸ List.mem_of_mem_drop hq)⟩
  have hndPM : (parkHosts ++ c.bank.drop keepBits).Nodup := (List.perm_append_comm.nodup_iff).mp hndMP
  have hcfg := cfg_physical c v
  have hHeadIn : (c.bank.take keepBits).headD 0 ∈ c.bank := by
    rw [ParkCopy.headD_take c.bank keepBits hkPos]
    have hpos : 0 < c.bank.length := by omega
    have h0 : c.bank.headD 0 = c.bank.getD 0 0 := by cases c.bank <;> simp
    rw [h0]; exact DiagSq.getD_in c.bank 0 hpos
  have hC1 : GatePhysical (CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 c.dst)
      (c.src.take keepBits) (c.bank.take keepBits)) :=
    CachedSquareCopy.physical G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits)
      (fun heq => hCacheNotBank (heq ▸ hHeadIn))
      (copyRegister_physical (some G0) (c.src.take keepBits) (c.bank.take keepBits)
        (List.nodup_cons.mp hndMask).2 (fun x hx hb => hG0B x hx (List.mem_of_mem_take hb)))
  have hB : GatePhysical (renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)) :=
    gatePhysical_rename _ (LowZero18Square.foldPerm K0 E0).injective _
      (gatePhysical_rename _ (R2SqEp760.sqSwap K0 E0).injective _ hbody)
  simp only [withSplitPark, gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨copyRegister_physical (some G0) c.src c.bank hndSB hG0B,
    hcfg.1⟩, eraseMask_physical G0 _ _⟩,
    dummies_physical parkHosts⟩, move_physical _ _ hndMP⟩, hB⟩, hC1⟩,
    move_physical _ _ hndPM⟩, hcfg.2⟩, eraseMask_physical G0 c.src c.bank⟩

theorem brA_physical : GatePhysical brA :=
  withSplitPark_physical cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA bodyA_physical
    cfgA_geom.1 (by decide) cfgA_geom.2.1 cfgA_geom.2.2.1 (fun h hh => (cfgA_geom.2.2.2.2.1 h hh).1)
    cfgA_geom.2.2.2.2.2.2.1 (by simp only [cfgA_fast, SplitCfg.bank_fast, K0_eq]; decide +kernel)

theorem brB_physical : GatePhysical brB :=
  withSplitPark_physical cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB bodyB_physical
    cfgB_geom.1 (by decide) cfgB_geom.2.1 cfgB_geom.2.2.1 (fun h hh => (cfgB_geom.2.2.2.2.1 h hh).1)
    cfgB_geom.2.2.2.2.2.2.1 (by simp only [cfgB_fast, SplitCfg.bank_fast, K0_eq]; decide +kernel)

theorem brC_physical : GatePhysical brC := by
  have hr := StairSquareFinal.record_branches_physical.1
  simp only [recBrC, SumSavedCBranch.branch, gatePhysical_append] at hr
  simp only [brC, gatePhysical_append]
  exact ⟨⟨hr.1.1, withSplitPark_physical cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC bodyC_physical
    cfgC_geom.1 (by decide) cfgC_geom.2.1 cfgC_geom.2.2.1 (fun h hh => (cfgC_geom.2.2.2.2.1 h hh).1)
    cfgC_geom.2.2.2.2.2.2.1 (by simp only [cfgC_fast, SplitCfg.bank_fast, K0_eq]; decide +kernel)⟩, hr.2⟩

theorem square_physical (k : Fp) : GatePhysical (squareN brC brB brA k) :=
  squareN_physical brC brB brA k brC_physical brB_physical brA_physical

private theorem withSplitPark_support_aux (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program)
    (hSrcAllowed : ∀ q ∈ c.src, q ∈ allowedWires)
    (hParkAllowed : ∀ q ∈ parkHosts, q ∈ allowedWires)
    (hCacheAllowed : LowZero18Square.cacheWire K0 c.dst ∈ allowedWires) :
    wires (withSplitPark c keepBits parkHosts body) ⊆
      wires (renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)) ∪ allowedWires.toFinset := by
  have hG0A : G0 ∈ allowedWires :=
    sub_allowedWires [G0] (fun q hq => by simp [List.mem_singleton.mp hq])
      (fun q hq => by rw [List.mem_singleton.mp hq, G0_eq, hs_lit]; decide +kernel) G0 (by simp)
  have hReal : c.realAll.toFinset ⊆ allowedWires.toFinset := fun q hq =>
    List.mem_toFinset.mpr (v.realAllowed q (List.mem_toFinset.mp hq))
  have hBankA : ∀ q ∈ c.bank, q ∈ allowedWires := fun q hq => v.realAllowed q (by simp [SplitCfg.realAll, hq])
  have hcfg := cfg_support c v
  intro q hq
  simp only [withSplitPark, wires_append, Finset.mem_union] at hq
  rcases hq with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := copyRegister_wires_subset (some G0) c.src c.bank h
    simp only [Option.toList_some, List.singleton_append, List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, List.not_mem_nil, false_or] at w
    rcases w with rfl | w | w
    · exact hG0A
    · exact hSrcAllowed q w
    · exact hBankA q w
  · exact Finset.mem_union_right _ (hReal (hcfg.1 h))
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := eraseMask_wires_subset G0 (c.src.take keepBits) (c.bank.take keepBits) h
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at w
    rcases w with rfl | w | w
    · exact hG0A
    · exact hSrcAllowed q (List.mem_of_mem_take w)
    · exact hBankA q (List.mem_of_mem_take w)
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (hParkAllowed q (List.mem_toFinset.mp (dummies_wires _ h))))
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := move_wires (c.bank.drop keepBits) parkHosts h
    simp only [List.mem_toFinset, List.mem_append] at w
    rcases w with w | w
    · exact hBankA q (List.mem_of_mem_drop w)
    · exact hParkAllowed q w
  · exact Finset.mem_union_left _ h
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := CachedSquareCopy.wires_subset G0 (LowZero18Square.cacheWire K0 c.dst)
      (c.src.take keepBits) (c.bank.take keepBits) h
    rcases Finset.mem_union.mp w with wc | hc
    · have w2 := copyRegister_wires_subset (some G0) (c.src.take keepBits) (c.bank.take keepBits) wc
      simp only [Option.toList_some, List.singleton_append, List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, List.not_mem_nil, false_or] at w2
      rcases w2 with rfl | w2 | w2
      · exact hG0A
      · exact hSrcAllowed q (List.mem_of_mem_take w2)
      · exact hBankA q (List.mem_of_mem_take w2)
    · rw [Finset.mem_singleton.mp hc]; exact hCacheAllowed
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := move_wires parkHosts (c.bank.drop keepBits) h
    simp only [List.mem_toFinset, List.mem_append] at w
    rcases w with w | w
    · exact hParkAllowed q w
    · exact hBankA q (List.mem_of_mem_drop w)
  · exact Finset.mem_union_right _ (hReal (hcfg.2 h))
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := eraseMask_wires_subset G0 c.src c.bank h
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at w
    rcases w with rfl | w | w
    · exact hG0A
    · exact hSrcAllowed q w
    · exact hBankA q w

private theorem rename_wires_pad (f : Wire → Wire) {P Q : Program} (L : List Wire)
    (h : wires P ⊆ wires Q ∪ L.toFinset)
    (hf : ∀ x ∈ L, f x = x) :
    wires (renameProgram f P) ⊆ wires (renameProgram f Q) ∪ L.toFinset := by
  intro q hq
  rw [renameProgram_support, Finset.mem_image] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  rcases Finset.mem_union.mp (h hx) with hQ | hL
  · exact Finset.mem_union_left _ (by rw [renameProgram_support]; exact Finset.mem_image_of_mem f hQ)
  · rw [hf x (List.mem_toFinset.mp hL)]; exact Finset.mem_union_right _ hL

private theorem perm_fixes_allowed :
    (∀ x ∈ K0.core.pad.take 34, LowZero18Square.foldPerm K0 E0 x = x) ∧
    (∀ x ∈ K0.core.pad.take 34, R2SqEp760.sqSwap K0 E0 x = x) ∧
    (∀ q ∈ K0.core.pad.take 34, q ∈ allowedWires) ∧
    (∀ q ∈ cfgA.src, q ∈ allowedWires) ∧ (∀ q ∈ cfgB.src, q ∈ allowedWires) ∧ (∀ q ∈ cfgC.src, q ∈ allowedWires) ∧
    (∀ q ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), q ∈ allowedWires) ∧
    (∀ q ∈ ParkCopy.hosts E0, q ∈ allowedWires) ∧ (∀ q ∈ ParkCopyS.hostsS E0, q ∈ allowedWires) ∧
    LowZero18Square.cacheWire K0 cfgA.dst ∈ allowedWires ∧
    LowZero18Square.cacheWire K0 cfgB.dst ∈ allowedWires ∧
    LowZero18Square.cacheWire K0 cfgC.dst ∈ allowedWires := by
  have h1 : ∀ x ∈ K0.core.pad.take 34, StairSquareSites.LT48K.swF 4834 5093 x = x := by
    rw [K0_eq]; decide +kernel
  have h2 : ∀ x ∈ K0.core.pad.take 34, StairSquareSites.LT48K.swF 4875 5478 x = x := by
    rw [K0_eq]; decide +kernel
  have hAll : ∀ q ∈ K0.core.pad.take 34 ++ cfgA.src ++ cfgB.src ++ cfgC.src ++
      ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0) ++ ParkCopy.hosts E0 ++ ParkCopyS.hostsS E0 ++
      [LowZero18Square.cacheWire K0 cfgA.dst, LowZero18Square.cacheWire K0 cfgB.dst,
        LowZero18Square.cacheWire K0 cfgC.dst], q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by
        simp only [cfgA_fast, cfgB_fast, cfgC_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by
        simp only [cfgA_fast, cfgB_fast, cfgC_fast, K0_eq, E0_eq, hs_lit]; decide +kernel))
  refine ⟨fun x hx => by rw [StairSquareSites.LT48K.foldPerm_eq]; exact h1 x hx,
    fun x hx => by rw [StairSquareSites.LT48K.sqSwap_eq]; exact h2 x hx,
    fun q hq => hAll q (by simp [hq]), fun q hq => hAll q (by simp [hq]),
    fun q hq => hAll q (by simp [hq]), fun q hq => hAll q (by simp [hq]),
    fun q hq => hAll q (by simp [hq]), fun q hq => hAll q (by simp [hq]),
    fun q hq => hAll q (by simp [hq]),
    hAll _ (by simp), hAll _ (by simp), hAll _ (by simp)⟩

theorem brA_support : wires brA ⊆ wires (recBrA bodyAPlain) ∪ allowedWires.toFinset := by
  have pa := perm_fixes_allowed
  have hbase := withSplitPark_support_aux cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA
    pa.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.2.1
  have hbody : wires bodyA ⊆ wires bodyAPlain ∪ (K0.core.pad.take 34).toFinset := by
    intro q hq
    rcases Finset.mem_union.mp (bodyA_wires_plain hq) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_of_mem_take (by
        have : K0.core.pad.take 32 = (K0.core.pad.take 34).take 32 := by simp [List.take_take]
        rw [← this]; exact List.mem_toFinset.mp h)))
  have hB1 := rename_wires_pad (R2SqEp760.sqSwap K0 E0) (K0.core.pad.take 34) hbody pa.2.1
  have hB2 := rename_wires_pad (LowZero18Square.foldPerm K0 E0) (K0.core.pad.take 34) hB1 pa.1
  intro q hq
  rcases Finset.mem_union.mp (hbase hq) with h | h
  · rcases Finset.mem_union.mp (hB2 h) with hP | hA
    · refine Finset.mem_union_left _ ?_
      simp only [recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10, ParkCopy10.pB, R2SqEp760.bodySwap,
        wires_append, Finset.mem_union]
      left; left; left; left; right; exact hP
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (pa.2.2.1 q (List.mem_toFinset.mp hA)))
  · exact Finset.mem_union_right _ h

theorem brB_support : wires brB ⊆ wires (recBrB bodyB) ∪ allowedWires.toFinset := by
  have pa := perm_fixes_allowed
  have hbase := withSplitPark_support_aux cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB
    pa.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.2.2.1
  intro q hq
  rcases Finset.mem_union.mp (hbase hq) with h | h
  · refine Finset.mem_union_left _ ?_
    simp only [recBrB, ParkCopy.withLowK2P, ParkCopy.pB, R2SqEp760.bodySwap, wires_append, Finset.mem_union]
    left; left; left; left; right; exact h
  · exact Finset.mem_union_right _ h

theorem brC_support : wires brC ⊆ wires (recBrC bodyCPlain) ∪ allowedWires.toFinset := by
  have pa := perm_fixes_allowed
  have hbase := withSplitPark_support_aux cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC
    pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.2.2.2
  have hB1 := rename_wires_pad (R2SqEp760.sqSwap K0 E0) (K0.core.pad.take 34) bodyC_wires_plain pa.2.1
  have hB2 := rename_wires_pad (LowZero18Square.foldPerm K0 E0) (K0.core.pad.take 34) hB1 pa.1
  intro q hq
  simp only [brC, wires_append, Finset.mem_union] at hq
  rcases hq with (h | h) | h
  · refine Finset.mem_union_left _ ?_
    simp only [recBrC, SumSavedCBranch.branch, wires_append, Finset.mem_union]; left; left; exact h
  · rcases Finset.mem_union.mp (hbase h) with hb | ha
    · rcases Finset.mem_union.mp (hB2 hb) with hP | hA
      · refine Finset.mem_union_left _ ?_
        simp only [recBrC, SumSavedCBranch.branch, SumSavedPark.withLowK2S, ParkCopyS.pB, R2SqEp760.bodySwap,
          wires_append, Finset.mem_union]
        left; right; left; left; left; left; right; exact hP
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (pa.2.2.1 q (List.mem_toFinset.mp hA)))
    · exact Finset.mem_union_right _ ha
  · refine Finset.mem_union_left _ ?_
    simp only [recBrC, SumSavedCBranch.branch, wires_append, Finset.mem_union]; right; exact h

private theorem hs_not_allowed : ∀ q ∈ hs, q ∉ allowedWires := fun q hq ha => by
  rw [allowedWires, List.mem_filter] at ha
  have h := ha.2
  simp [hq] at h

private theorem hs_fix_perms : ∀ q ∈ hs, LowZero18Square.foldPerm K0 E0 q = q ∧ R2SqEp760.sqSwap K0 E0 q = q := by
  have h1 : ∀ q ∈ hs, StairSquareSites.LT48K.swF 4834 5093 q = q ∧ StairSquareSites.LT48K.swF 4875 5478 q = q := by rw [hs_lit]; decide +kernel
  intro q hq; rw [StairSquareSites.LT48K.foldPerm_eq, StairSquareSites.LT48K.sqSwap_eq]; exact h1 q hq

private theorem withSplitPark_avoids (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program) (hba : ∀ q ∈ hs, q ∉ wires body)
    (hSrcAllowed : ∀ q ∈ c.src, q ∈ allowedWires)
    (hParkAllowed : ∀ q ∈ parkHosts, q ∈ allowedWires)
    (hCacheAllowed : LowZero18Square.cacheWire K0 c.dst ∈ allowedWires) :
    ∀ q ∈ hs, q ∉ wires (withSplitPark c keepBits parkHosts body) := by
  have hsup := withSplitPark_support_aux c v keepBits parkHosts body hSrcAllowed hParkAllowed hCacheAllowed
  intro q hq hw
  rcases Finset.mem_union.mp (hsup hw) with hB | hA
  · rw [R2SqEp760.bodySwap, renameProgram_support, renameProgram_support, Finset.mem_image] at hB
    obtain ⟨y, hy, hyq⟩ := hB
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hfix := hs_fix_perms q hq
    have hx1 : R2SqEp760.sqSwap K0 E0 x = q := (LowZero18Square.foldPerm K0 E0).injective (hyq.trans hfix.1.symm)
    have hx2 : x = q := (R2SqEp760.sqSwap K0 E0).injective (hx1.trans hfix.2.symm)
    exact hba q hq (hx2 ▸ hx)
  · exact hs_not_allowed q hq (List.mem_toFinset.mp hA)

theorem brA_avoids : ∀ q ∈ hs, q ∉ wires brA :=
  withSplitPark_avoids cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA
    bodyA_avoids_hs perm_fixes_allowed.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.2.1

theorem brB_avoids : ∀ q ∈ hs, q ∉ wires brB :=
  withSplitPark_avoids cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB
    bodyB_avoids_hs perm_fixes_allowed.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.2.2.1

theorem brC_avoids : ∀ q ∈ hs, q ∉ wires brC := by
  have hmid := withSplitPark_avoids cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC
    bodyC_avoids_hs perm_fixes_allowed.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.2.2.2
  have sl := OwnDiagAll12Square.sum_lengths K0 hwK
  have hgp := addInPlace_wires (OwnDiagAll12Square.sumSrc K0) K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (by omega) (by omega)
  have hgc := subInPlace_wires (OwnDiagAll12Square.sumSrc K0) K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (by omega) (by omega)
  have hnot : ∀ q ∈ hs, q ∉ K0.core.cin :: ((OwnDiagAll12Square.sumSrc K0 ++ K0.core.sum) ++ OwnDiagAll12Square.sumBank K0) := by
    simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  intro q hq hw
  simp only [brC, wires_append, Finset.mem_union] at hw
  rcases hw with (h | h) | h
  · rw [OwnDiagAll12Square.gPrep, hgp, List.mem_toFinset] at h; exact hnot q hq h
  · exact hmid q hq h
  · rw [OwnDiagAll12Square.gClear, hgc, List.mem_toFinset] at h; exact hnot q hq h

end Branches

end ECDSAAdd.Entrant.SplitLeafSquare
end

-- ==== end SplitLeafSquare ====
