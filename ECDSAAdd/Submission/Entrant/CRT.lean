import ECDSAAdd.Framework.Syntax
import ECDSAAdd.Submission.Entrant.Stair44Stock
import ECDSAAdd.Framework.Semantics
import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Framework.RecordedPaths

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
  | 31 => [(257,1), (7,1), (11,1), (19,1), (25,1), (31,1), (73,1)]
  | 39 => [(257,1), (21,1), (11,2), (13,1), (19,1), (25,1), (31,1), (73,1)]
  | 46 => [(257,1), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (73,1), (1193,1)]
  | 54 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (73,1), (1193,1)]
  | 61 => [(257,1), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (73,1), (1193,1), (1571,1)]
  | 69 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (73,1), (1193,1), (1571,1)]
  | 76 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (313,1), (471,1), (1193,1)]
  | 84 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (87,1), (313,1), (1193,1), (1571,1)]
  | 91 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (313,1), (471,1), (1193,1), (1571,1)]
  | 99 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1), (313,1), (1193,1), (1571,1), (2047,1)]
  | 106 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (87,1), (91,1), (97,1), (313,1), (1193,1), (1571,1), (2047,1)]
  | 113 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1), (91,1), (313,1), (471,1), (1193,1), (1571,1), (2047,1)]
  | 120 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (313,1), (471,1), (1193,1), (1571,1), (2047,1)]
  | 128 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1), (313,1), (471,1), (1193,1), (1571,1)]
  | _ => []

/-- Pivot donor and row-target mask for each binary elimination column. -/
def pivots : Nat → List (Nat × Nat)
  | 31 => [
      (31,35792128), (31,107376385), (31,178959873), (31,536867079),
      (31,600858369), (31,1738721811), (31,956782869), (31,1223403391),
      (27,1262390785), (26,1284609283), (15,1076751111), (31,1383354633),
      (31,675235864), (31,1319836218), (31,626103637), (16,1218536419),
      (31,692381415), (31,677387033), (21,1912242310), (22,1514609173),
      (23,646853674), (26,1293707348), (31,1267930693), (29,1662541767),
      (31,104106428), (26,1708288954), (31,1129700233), (31,347763906),
      (30,1813971202), (31,1480903093), (31,848160026)]
  | 39 => [
      (39,9162723584), (39,27488236289), (39,45813617921), (39,137437433607),
      (39,153819313153), (39,445114133523), (39,244935844117), (39,313191273343),
      (39,323171922945), (39,33002579970), (39,307138937093), (39,132704743946),
      (39,510957995285), (15,39357046591), (39,443565779819), (39,178684052419),
      (17,385726462137), (39,436095543013), (39,142868022273), (29,412970585091),
      (39,82286219268), (39,102447526925), (34,409777828893), (39,381403058228),
      (26,222910296140), (27,322594965666), (30,121931244937), (39,460685099568),
      (39,476866576609), (39,462784074406), (38,319995145502), (38,370515392130),
      (35,313318576605), (39,518077257412), (39,495404507606), (39,81798252999),
      (38,296595909390), (38,399247318696), (39,201896981988)]
  | 46 => [
      (46,69864820992), (46,209594462977), (46,349324104961), (46,1047971843847),
      (46,1187458544641), (46,3560332569619), (46,5871772524821), (46,17562615452543),
      (46,17701302023169), (46,35325936363522), (46,29450328424709), (46,58840460177930),
      (46,54489695339797), (32,26461918191423), (22,28302994117716), (46,47798668302231),
      (46,51789199607686), (46,17509259011813), (46,33430797264545), (46,56971969601429),
      (26,65986471086163), (46,67906060632446), (32,58436453253512), (32,54879315686505),
      (46,46616041787154), (45,66447711429722), (46,23636959828357), (46,5400946699232),
      (46,56375460320768), (46,29025864721985), (46,20968736379947), (36,35708879366246),
      (46,30015400840643), (44,69035788999957), (45,65121338829526), (45,44769052680335),
      (46,69724311502723), (40,34402595829158), (46,3940640752042), (46,26401071494898),
      (46,19973661979300), (46,46069651276728), (46,18055019894711), (46,58222026087381),
      (45,51011293107158), (46,18578991649204)]
  | 54 => [
      (54,17885394173952), (54,53656182521857), (54,89426970869761), (54,268280792023047),
      (54,303989387427841), (54,911445137817619), (54,1503173766348821), (54,4496029555818623),
      (54,4531533317996545), (54,13574098963595523), (54,7539284076921093), (54,13311980139710223),
      (54,16711792434675985), (54,2079846207525683), (54,2714325791085909), (54,7579501756121087),
      (18,13269785967329281), (19,5868753297866754), (54,11717990171017220), (54,7268443740962824),
      (39,14953939766411285), (54,6176574053220415), (34,8659332894490731), (31,11389522795888873),
      (29,13966060896911788), (47,16027983665824478), (54,13092109120898435), (54,16047830987704688),
      (54,14805823938040943), (44,11116966088294060), (44,194423156271914), (54,13607295652652986),
      (54,9931255419213678), (54,8966829795557563), (54,9619678701222865), (43,8544791523970942),
      (54,2519678255255368), (54,10605646081714039), (54,4565894063984044), (54,13251732340170282),
      (53,13819319533637198), (54,15015620309256253), (54,4222528161183556), (54,6914592065905426),
      (54,16157340129358319), (50,1137904327841237), (51,2275808655682474), (52,4551617311364948),
      (54,4680037411569418), (54,15084370857382329), (54,4598758997644030), (54,10181769544390831),
      (54,12407525901609312), (54,5350013080566984)]
  | 61 => [
      (61,2254034342023424), (61,6762103026070273), (61,11270171710117121), (61,33810515129880327),
      (61,38318583570985985), (61,114955717531380755), (61,191590897050870037), (61,574770945159631743),
      (61,579278985957061633), (61,1158555531940685826), (61,1815893062029492485), (61,251832683799917066),
      (61,1080355772433384725), (37,1372192858215014207), (22,791287453245314132), (61,503680904731105175),
      (61,1731039513475057542), (61,1218783973143602917), (61,665350722451908257), (61,2116263123005644693),
      (26,1934155785318385747), (61,2089591432110096766), (37,2210885606459425160), (56,2104937180498359401),
      (61,404563882420244242), (61,1403347185707356211), (61,2135462592491559301), (61,1085540342926830560),
      (61,891126354751435862), (61,2153050006390961741), (61,1471096307552965675), (32,2008222534367213658),
      (45,1261968484448734659), (61,1398843846526313855), (61,1446992742292546306), (60,1466609705177565785),
      (61,2086261939477978289), (49,1857179438356427688), (61,1682368491068338843), (61,331100463541130964),
      (61,1071358538745687913), (61,2114761361885619014), (46,441990084980086448), (59,1828549505193159499),
      (61,2049604007060519406), (50,2134153722211250606), (47,1517347390080169935), (56,1123965795322353131),
      (54,2112403516543314197), (61,870590253047307686), (56,234589944108388463), (61,1415019905490325522),
      (57,220569803371683171), (61,1572500928213870424), (61,44536647126190962), (57,1100654787634923465),
      (61,1759481013258708173), (61,1216995865800056437), (59,759066555345246264), (60,1169286674406070481),
      (61,89313809505301095)]
  | 69 => [
      (69,577032791557996544), (69,1731098374673989633), (69,2885163957789982721), (69,8655491873249361927),
      (69,9809557394172411905), (69,29428663688033468435), (69,49047269645022724117), (69,147141361960865693823),
      (69,148295420405007843329), (69,444885614267283210499), (69,464868623879550271749), (69,485229473921211565839),
      (69,586218905395877970193), (69,320002274110849880883), (69,54274167918407521621), (69,130522679280354164735),
      (18,169904099769688784897), (19,339146723723346182146), (69,403321036653557972996), (69,491953611976929705992),
      (44,454729598174442618901), (69,460789790192762290239), (34,448187101115360936043), (47,469603513498281246953),
      (48,56940073380790141356), (43,518387111808195822135), (69,317910125167153972271), (69,371834707839317576622),
      (57,25345924737577850653), (65,190524545173316710504), (59,131326414849856339781), (69,205762688001938026763),
      (69,440296075112221484714), (69,46338259503487778626), (47,445479157301461115383), (69,454724805449977908353),
      (59,510433139946592405488), (69,175633538272150559905), (42,51820076168081270867), (51,157355410748852081628),
      (69,443620518188294396387), (44,27575603762642170035), (63,232617026686060015483), (69,501666172045132474774),
      (46,547288910933330241369), (59,154182503425840833608), (51,489054482903793140196), (69,391732500287689324245),
      (52,199974625551219760729), (57,127293230495720505312), (69,106438318358691265827), (69,219060212632490351592),
      (69,53119595183359040213), (54,226104555586361131504), (69,430950662108017517643), (57,197963928531621211376),
      (69,246162631813304010520), (69,279882947416515559763), (60,573202608278911393384), (69,427072981863020056757),
      (68,323859049407508105679), (69,236176473431231736787), (63,435166282421073734668), (65,574085010600517704893),
      (69,349875294263939581559), (66,95377065177172559945), (67,190754130354345119890), (69,417703414717365556836),
      (69,172842360545043771081)]
  | 76 => [
      (76,74076350456290934784), (76,222229051368872804353), (76,370381752281454673921), (76,1111145256844243435527),
      (76,1259297957694632361985), (76,3777893872560872620051), (76,6296488767296119046165), (76,18889465454966800056447),
      (76,19024997913319987019777), (76,56939704318091220418819), (76,31590293052209760567557), (76,55810716169348774102799),
      (76,70070232037423839248657), (76,8722765670480838071091), (76,11388977790330263115093), (76,31796310539406235631615),
      (18,55703003139867229290497), (19,24571931853517957365762), (76,49143862441223059931140), (76,30477493667172181868552),
      (45,62789405605066063544341), (76,25957951228346676215871), (34,36355580709718872227947), (48,47774186432323832578281),
      (34,58563012491694972862892), (44,19510309090934281142839), (48,73241800132543204558772), (76,36494916132387799764865),
      (46,34373895110530567773992), (76,72493764581521765707584), (37,63955160731318791332930), (49,2121471962168797095446),
      (52,67868459447709859108341), (37,13601403084657617309590), (76,68518115545222806859705), (58,22679569014315697994573),
      (76,73616998342598009615060), (40,70357557042147595129517), (47,71658457092162765485283), (56,15072832296103332188682),
      (70,65099994529891146527734), (75,57443855023525624219732), (74,71168652257876289636074), (54,5185902078316862536884),
      (76,44992156127044920431027), (73,9924419815297546836531), (76,63828234279078682336173), (52,6590747372140995769572),
      (76,70955687724209243078905), (76,17045320877225965641916), (76,36849409924044979707498), (76,73138548333176085944024),
      (70,41599825533360715545363), (66,43068091010300027116055), (56,7493382147492389408881), (65,13341619193818312902796),
      (58,58365798529431218504228), (76,35214276133725923639683), (60,69709357396339843791137), (65,58484712092465085369686),
      (76,51425934024976603276264), (71,32887723580400001827169), (76,33104652467406475695541), (67,38296889858277314785097),
      (68,21068288003804187931548), (76,36025837590999785556369), (76,73789463575119009415332), (73,54641693468330830731723),
      (76,54504485109738964269360), (73,54815748058359080712390), (71,54920246122803150630191), (76,61765088246402104915169),
      (76,38231521991561556063401), (75,46298900611847570742241), (76,15848662951310832203636), (76,5708022376063080480319)]
  | 84 => [
      (84,18907985876931629350912), (84,56723957630794888052737), (84,94539929384658146754561), (84,283619788153974319677447),
      (84,321435759907775385436161), (84,964307279722803131842579), (84,1607178705068007616479253), (84,4821536114357101292355711),
      (84,4859337604755859145293825), (84,14578005895449487263858947), (84,15232820350587795157549317), (84,15899992479503871498782479),
      (84,19209220862086900101480721), (84,10485833492073652336923443), (84,1778458977678302891021653), (84,4276962709958363394834431),
      (18,5567423163659896304697345), (19,11113148993121438056054786), (84,13216022680492684754288644), (84,16120333870525486238531592),
      (45,14900588383483273823977493), (84,15099171635614054281576511), (34,14686204868190853745279083), (48,15387960450584221141500137),
      (49,1865800799851969963098540), (44,16986517956144526819525175), (84,10417267423518698809263151), (84,12184279569391786270788526),
      (62,830541733569221975938845), (75,6243100073805349734854760), (79,4303300037238333137846085), (84,104398737884420883011198),
      (84,14427619175069841021970090), (66,18826884963946813758160894), (84,5792224085654681463748987), (84,14900430014942284270488705),
      (45,4899952493586293894171976), (62,9786391545884259736971305), (58,13555552130291203801127224), (84,14761152872767400695080008),
      (43,3764331626120597240569364), (84,15828428596729726994269906), (75,270102034997999802799220), (84,4574608672012200172738512),
      (84,18918071955732903143672476), (84,12880632305641020002026331), (84,3689823373269954698761137), (65,13304966244271190971993434),
      (84,10991348993859897975281259), (84,3870469646521090238719922), (84,7677888213813199131643495), (58,7259790385658338743301291),
      (84,4111023973728654817349887), (84,4724766416966426458243968), (84,15877417617847873457890591), (84,2324908454860255360534700),
      (81,14231932322947982269951324), (84,13327164823418410003785683), (84,2291553184915416999576334), (84,2136264585890441798945848),
      (84,16591640662324960803206982), (63,4359922514458933763890281), (84,13984884209532645216838159), (84,10308690949476750973871204),
      (79,16324557477893777700618225), (84,1629978101768887399722054), (84,9645335406304319926880110), (84,6648037512683948266655402),
      (84,9065240613691208064981640), (76,12353080344742321747281195), (79,5533025011555295245075711), (84,12137934535352275623661083),
      (83,13650580528805714030511397), (84,17991725620406043720596241), (80,14368432542687875048052713), (82,16355913750927677489586417),
      (80,18141032267861354302387856), (80,9457253597170049583777609), (84,14546095975908074420314970), (84,6626982056229139694471529),
      (81,7842360130227463998781894), (84,1611469837820915221525622), (84,12472179628820032770778557), (84,3066683568870316258941169)]
  | 91 => [
      (91,2420222082443566300332032), (91,7260666247330698900996097), (91,12101110412217831501660161), (91,36303331236653494384394247),
      (91,41143775401540564792115201), (91,123431326204613199892578323), (91,205718876975044574218092565), (91,617156630898016994408464511),
      (91,621996671215143632235724801), (91,1865985684383940180958970115), (91,1949799310596453374493982981), (91,2035199171509223302188762895),
      (91,2458779512882127743548981521), (91,1342186788273695274551153459), (91,227642501376839629835408725), (91,547451952403078590091984895),
      (18,712630878033883147592269825), (19,1422483065686117747491602434), (91,1691650899419365832149434372), (91,2063402728059906944267190280),
      (50,1907276352692016980190101525), (91,1932694114183483247443247167), (34,1879834102263842664381874283), (53,1969660008298447052890243305),
      (34,238823477044207263727485356), (49,2174272953558011652653646391), (53,1100048381814323954396170164), (91,392859802871381840946597761),
      (61,811080263785340610598674216), (38,799117999703551351896682600), (91,1713470791197587210846763882), (91,13362853365719757800527486),
      (46,1754839522709543447495614199), (56,257527893996354081608627452), (88,2343897506213891235063881681), (91,703085392248500396735638835),
      (79,2428267172786718514920151041), (78,2195737149606560797474860760), (91,2275966750337085509974588123), (46,2097444849111994867776632607),
      (80,850530295424973174464847119), (91,987557920816440185537663115), (71,1040143158938562294183414861), (68,767404393330081053960365204),
      (91,1049451669403527782027594456), (91,1546943687560088975318654519), (73,2183784637718278276778879422), (55,2101040892505979246231045459),
      (91,1934058953651011684047897938), (67,1049356373796984499480181478), (91,2455410976036314534795487654), (91,54431637321014975975269235),
      (64,1936246653278561719386672161), (67,1963442135298121411348770354), (60,20593420660593327147408622), (91,57843405530535169850436340),
      (82,2057970512040780150391110950), (63,157860281140154877439723436), (61,17616449242812149853702728), (91,2049291676818094752382574435),
      (76,869018622380696247029744374), (91,796779815514944184342280879), (82,740254284238900576119996126), (74,927396099296662413133745665),
      (91,2367006781558781494135399263), (73,1138421127282330220285808848), (71,814446983986292952437878371), (78,820096894999940907033060953),
      (91,432659093601290746760192451), (91,2341608317065940964841724024), (91,1558140431513667577933562358), (88,1222023297710846998558440481),
      (91,1281031104470501532841034497), (91,2207747455369956469195373811), (89,1924394203213291841907307720), (91,2069336553371692899896343421),
      (91,1536570937782812692974448627), (91,327752704937660760529318823), (91,356285814098982512988647352), (91,1180432499793496153484024535),
      (91,1103537145410631310070852866), (91,1148034184834785040892255290), (91,1559753210114112721930861770), (91,1222687257175689445222111550),
      (91,475340887880748017979641791), (91,1811121641225450565389398991), (91,1876762833384867750775022063), (91,678704877228344346529270691),
      (91,1320352261722994493838496536), (91,1342429243107334898368064750), (91,903125256078155112365178191)]
  | 99 => [
      (99,619575075190751656229797888), (99,1858725225572254968689393665), (99,3097875375953758281148989441), (99,9293626127861274843326382087),
      (99,10532776278242778093593034753), (99,31598328834728325786295336979), (99,52663881388190842065648680981), (99,157991644164545409468700229759),
      (99,159230793851523550814038982657), (99,477692381333168482640564519171), (99,472142605218948694614137372933), (99,149680574493232444882867193615),
      (99,170831450469326572299567038737), (99,508509932798394961224681067315), (99,416004763887173476835189396821), (99,19324933415642067093155708927),
      (18,20604168189445896659113607169), (19,41207642064197436352866287618), (99,82126955318610859163471839236), (99,163923935869527011908716068872),
      (50,429423042440655729301733572629), (99,20290214120905732868020305983), (52,469030263425298539292144631915), (53,350210475832538619129356681449),
      (52,607269294895074293583193047468), (99,317053488426643958354993480688), (99,6603920828699380361616098931), (99,66548492310291854968566712818),
      (99,58034971016773782465432722091), (99,486280303046560187389701930542), (99,59945285351326736368647956402), (99,435820438546641729967295540071),
      (63,509894792802688811700090120520), (99,226363283355657872693869483794), (81,149906001168383700071017155456), (99,557473447983842331491556857009),
      (71,26414622994019074438489150305), (99,100523452641743546194203753047), (66,64506098043940443930968544709), (43,195680695113712707768658242440),
      (99,273766484494661332257182722730), (99,439635090896983819726643496405), (99,425122475664398553254239392719), (99,311326942652204390600252418178),
      (85,632733314509530718480720987775), (99,609692508222312432507038721002), (69,38342788167189631845487867592), (69,287348221080888629375864733246),
      (99,48830073437489784404171243068), (82,200717150470580269685070748144), (97,303116868039685181102777760773), (99,470928912052172517420240784149),
      (82,147681237557761828652205930868), (83,16569763552013746953500615012), (75,146863396519721383880779044979), (99,771321345329789962077614086),
      (99,288965334089339043176977017108), (99,360056566774398920140554755802), (99,41283907658632198110779242339), (90,294141794173593196867046347183),
      (99,387460067242383840614395228209), (99,436987824624401313679853748301), (99,195285506611165166844053445400), (99,259766045571171761376186680597),
      (77,394369968206013251323569415730), (74,99959825775695362400232068059), (78,368581859349229980740050760631), (84,582449128002291537501157941808),
      (98,531299556251850495923606074230), (99,118057639359451760433758797107), (99,450159309462866743935934290189), (95,615736555906377953251868073998),
      (99,539186528625361833707248511815), (89,342646324596541960844159149692), (90,289071584145874107988805266449), (99,91917463140813297895201103408),
      (99,307239777209824328781146618314), (99,158296787789846698427685088958), (79,219300985332503122555339793670), (82,344155950765403906100676910305),
      (85,268142318237162485915837753183), (99,308741326120650809983887937911), (99,293944000688360186330393355007), (84,123859821237657378862851835538),
      (99,152243475440219695663686199457), (97,525662730227295195653086521002), (99,402208460867555172080844835502), (99,163251895620279922185314743114),
      (93,235352784162450574251751648736), (99,170138653211417842625086576589), (91,211673333180618079942780773614), (99,195509668194089988151174127358),
      (99,152471106602362146910361984858), (99,364055993778009554859772310829), (95,285576153385052111949765306760), (99,271099884613006966758457645347),
      (98,392882192411173962281239958435), (98,411120559473313395233131598095), (99,18350358423042143281344428405)]
  | 106 => [
      (106,79305609624416192352167723008), (106,237916828873248577056503169025), (106,396528048122080961760838615041), (106,1189584144366242885282395258887),
      (106,1348195363615075269924537761793), (106,4044586090845225809250588819475), (106,6740976817917980150968581423125), (106,20222930453314100051976675065983),
      (106,20381541613125363524663915118593), (106,61144624810555285455173215781123), (106,60434253468000042467214783414533), (106,19159113535084872259731925501711),
      (106,21866425660088911272374702244113), (106,65089271398250079490112303076147), (106,53248609777652772492676951250261), (106,2473591477037945277537237041151),
      (18,2637333528359683722534110625793), (19,5274578184295528718388191297538), (106,10512250280727876378188050333700), (106,20982263791190830375181500809224),
      (45,54966149432280856738725980602389), (106,2597147407654895596425323675711), (47,60035873718376795176657778049131), (48,44826940906416924537740897878249),
      (49,77730469746427755408817639915948), (106,40582846518516705589182271063024), (106,37992958971728369125245856973871), (106,35385667290442406700416454495150),
      (106,7428476290228194802042896325291), (106,62243878789920530196013226278446), (106,53586273436555505468097762974656), (42,364346489957972038637441095445),
      (106,39920027690499186742385026433583), (106,28974500269577121151345432270610), (102,8625917164999358714328917150120), (106,79266009471446345653115744951577),
      (106,20504471648899396675628182021407), (50,75440810621255757548534922915022), (42,25940095388443634082941323529995), (106,71163155260344158573108900527668),
      (106,5769062321662753357426615366365), (105,55543772008937218931361838260566), (106,60853911140453798806745609511076), (106,52335256126464978993360778357146),
      (106,78103667520717947785584199262864), (106,50243052118700417315121832661824), (86,45311475215700561610174240096345), (106,54444456655755589155726763731230),
      (92,46800694073821287254888865070817), (72,19963694709315244988988977019126), (106,46529974449410068082954822059739), (106,1400238972789414824333223291683),
      (106,29519246595264001449208491199967), (106,57957478951194247951584473572220), (106,17722852927101732180667971783646), (81,29770477761634392119782750121554),
      (106,41286693802558858946401027599126), (67,18817881326604279665995687400551), (102,26416257516592264549247749092595), (106,31854571125743601671563241979031),
      (91,50763106800043444987819144903452), (87,68916047323352384030132097175569), (106,495073395880642718719731369137), (71,21223929781222489197542896780303),
      (91,77319530755812273428678136682257), (106,4414110941975559503392828543707), (95,17481240795631410978117122799583), (106,62002075532374804644288255813507),
      (106,22292183863946258473791090774510), (100,4943518034182200351234904980610), (106,21495954162179206623057352127396), (106,27319034274871317363192736207497),
      (94,75653855149119640180904556751559), (106,41380670078360274178579536271192), (80,25703924265509880744489579868261), (76,51421320741320495579760953146163),
      (82,13001957157680350112209928661430), (106,60935917128621823001109230521762), (106,9938856848212120131651435339216), (90,16899205438182616358883942284288),
      (88,80645359843715319038534501154148), (85,15600672399499677112380528878905), (98,56891530401513821532006443709411), (105,47900798748703343801532751049792),
      (106,79851780449229223368105375515344), (94,30887242992758913505815765915047), (106,72240992607019589607352932422882), (97,54164303860736699992943093891298),
      (90,25969174365748749446109040159659), (91,24782741654770370539477076596040), (106,73524072134050106111235156262069), (106,45378963867298033129009280402192),
      (103,18086121676885128462286154874533), (95,64777635333422880561153974171507), (98,10704102298681551544600475096066), (105,63481279993986517616194518923873),
      (106,22185171983633359080534758661486), (106,40942457676549729511623824826950), (99,41501166434063481790397643334495), (104,24691396492567363758359272182678),
      (106,76551958800402028149607832751481), (106,27089000002916832275765752013410), (103,12761637021787158714705079373551), (105,44680416514521977140723197176214),
      (105,48074447302690131827689633044830), (106,4399246347945575466968985169471)]
  | 113 => [
      (113,10151118031475523430598541639680), (113,30453354094426570291795624919041), (113,50755590157377617152992708198401), (113,152266770472132851458978004008967),
      (113,172569006535083898320112894345217), (113,517707019605251694951844199268371), (113,862845032675252753698507982962709), (113,2588535098025702893746574574420095),
      (113,2608837332434575975775286842425345), (113,7826511979570870502184942307311875), (113,7735584436967414880120577395523845), (113,2452366533046439622326372869605135),
      (113,2798902481386763103300626545705233), (113,8331426739383785659952635916260147), (113,6815822050512675477165791979574613), (113,316619712053553331889667225649151),
      (18,337578694536677058916319082315777), (19,675146007557550924778305605861378), (113,1345568035925064822823623734591492), (113,2685729765256219580894677221507080),
      (50,7035667131605976348587119975137301), (113,332434868750241241223207665467455), (52,7684591835465130619063945701032043), (53,5737848440425573101626864161063145),
      (54,9949500131553008501047156936540588), (113,5194604354040906522289726183965680), (113,4863098749788744286048826501825583), (113,4529365419326455788948467613567918),
      (113,950844966063653645163116299492011), (113,7967216480980450444810889752100398), (113,6859042995398840082129016057781184), (47,46636344586915926064265401046805),
      (113,5109763549397215134332883355730479), (113,3708736039676359700435756200826642), (109,1104117405353749802416029266020776), (113,10146049216862043406468350307736857),
      (113,2624572365243455326070847878472991), (54,9656423763788161603551838067403982), (82,7781891638482698990989475205342149), (113,588463722939759056393357775295226),
      (113,6627777645718337560426512859202530), (113,3812292918525860080849777963937215), (113,2443680022891114793160322934423223), (106,9994055989769969707041104480835295),
      (113,417539991492912951803698502958211), (110,2085375322181246506402721629749848), (79,2910791628843867317467341356384805), (75,6063747573434503975337747522540456),
      (113,4740694565520825021890386929014470), (52,9640180645499667864521335794989028), (98,1705356288290636787964640955335219), (99,4204567486592932991905135347096495),
      (54,6318034330954086769440091074803037), (84,5643358101900001433410966760756879), (62,9445730114474217402565538862638136), (113,6062648618633363018833571443996175),
      (113,653805901950402417192492313656298), (113,1951229260638644733647387136177084), (61,5416842971724929511412491797117368), (113,5759403374421225771145366054385377),
      (61,8309594495990613098845062134267378), (93,8134626425078803934766455013393302), (92,5455697880718300173703469244960021), (113,9474023415083941859592641675396775),
      (113,8653483179072860559120124501702103), (90,4954963643593925312072759610780993), (113,3010215865074889038420351569745051), (79,4613049181474363998678028897033806),
      (102,8111553059609403005109812250715512), (82,5455587386950598351382835961261351), (91,8090556721211736816405689659482652), (83,6968503497048277131700438855735952),
      (96,2119828486954207757842628957278807), (113,8927688246730167362798091142958418), (113,2617486723716420696863928679141220), (113,684905441064002766944189888055983),
      (84,64493222626016593973630285621625), (110,2200806601336021694067464818079234), (113,5219442909649097488510898565468935), (87,55424935407268817475420830605758),
      (113,926878910350105585469753450605164), (96,9593989850087814037553286334580096), (98,7544371823823073106368166912588187), (113,3436332572628213938172882758352411),
      (94,6645491189386693501163008131733996), (113,7726038351769278707888233023545926), (113,5178728171021034541797340084255178), (88,6503057240396960606257469837241637),
      (107,4488097897163009161517312110180506), (105,2915563270564183482361170710235904), (113,9239588770016703770634665511715461), (113,2928803044528266051522326276217900),
      (105,8887520055511083827458550576662300), (100,8885048617555837726656303526446529), (110,7317728848592750844960602676946938), (113,7526450568944747422265189908858592),
      (111,3655959260095899352690784585467857), (113,3133772023038124023186327353343003), (113,5090339768191537986414151713961993), (113,6858226641445661514976323602187609),
      (113,114800018091972042923195298191599), (108,5585076512712019114532531552144179), (105,6534058395463275453690442790697055), (111,4852856986493557152010005416513918),
      (110,6576758383583002622032214592227263), (110,4151203106944381799039493688864299), (111,4927496308340504798693071165460101), (110,1363612243741133546835832718536082),
      (111,9369661843793680512618876543678029), (112,5727811515390609944017813073268077), (113,1200989052613450170552392019978121), (112,7558603177510339540492931152056967),
      (113,4902292662523148607494968919586649)]
  | 120 => [
      (120,1299343108028866999096968083472384), (120,3898029324086600997290904250417153), (120,6496715540144334995484840417361921), (120,19490146620433004986454521131499527),
      (120,22088832836490738984648395105501185), (120,66266498509472216953944662292037651), (120,110444164182443207350362044071215125), (120,331332492547299372272262088509030527),
      (120,333931178551625264952446824050130945), (120,1001793533385088452577850198757146883), (120,990154807931840590033292506586939653), (120,313902916229950125735194039290693391),
      (120,358259517617513956473843249850679569), (120,1066422622641127276329537364583191347), (120,872425222465621079905153249329878357), (120,40527323142856728277903273659170815),
      (18,43210072900708055805972080982491137), (19,86418688967363350001531365975654402), (120,172232708598417392592889661620224004), (120,343773409952785667550688272847994888),
      (45,900565392845561602915582488019795989), (120,42551663200022498549109698672394303), (47,983627754939534296639090878174658667), (48,734444600374474684729053692622864617),
      (49,1273536016838785241527771436159861164), (120,664909357317242729533823819768136688), (120,622476639972959592781104232849671215), (120,579758773673790142192416591872658350),
      (120,121708155656155126429154837663521451), (120,1019803709565509423678211193761054254), (120,877957503411064421830357031466326976), (42,5969452107114054402309747572578069),
      (120,654049734322852246266610974454612527), (120,474718213078573504273412965138503442), (116,141327027885280747827840490734029224), (120,1298694299758339607666940845044800793),
      (120,335945262751160038729105917918586143), (49,1236022241764884560756146590513540302), (67,996082129725784900249424222443267013), (99,75323356536303445537601882718950138),
      (120,94520317944841893896486223606166237), (114,1228909695806374700932205816082144384), (67,239048173270633347205820206200851562), (120,857460836158879103124446639351720346),
      (120,325497284383750746556496079668902582), (120,440870334382706874217646620261399336), (120,356174894397600038299275346250901553), (104,372220515251643062932804116114165851),
      (120,786692152131347595232394705045864722), (120,1220111532376244913650525157091006028), (120,141171774241924062899299438186316059), (59,773357049507914877789694624891497896),
      (72,28629491720800054075073268128564184), (88,347803234367887663336905711327298455), (58,221878613171514908638358780116841830), (120,787995216561479320783711327117600347),
      (120,354159592785429910383933333759722491), (64,462160176549863592120260714943031764), (120,302454394525190736110813386073824739), (76,1105267037422422287401338650229147931),
      (75,892783563377560319381430683946631257), (120,663510901188556470187076029739082391), (104,381713149547044472664808926492297946), (120,879997529026941444374561474893054030),
      (75,1061351576673362639633099617830297107), (120,952253841407521907440515095631753179), (120,929223157231335536322387883202504271), (88,24496217540192035558658677772720367),
      (120,722608580755378189431174877457602693), (81,233923422453345523511946512538781246), (120,1275448081675487971919753026414148655), (96,1255319344001315998715512083829385840),
      (120,246073800514844185012553197525118906), (105,1162304085219100611541630898567143522), (119,699958218433097398459771424478337624), (78,44513232254392268315040744041238883),
      (120,777445014939450117666531952890484280), (93,1110360211186223452674214200911034518), (86,188673175890077783301785300972397980), (96,932391862649701777835361383614180565),
      (120,1280216705449205776140913688430049110), (120,907886816982853379357380389374970088), (92,817979304685657791693031672558421575), (117,1283130265688180941389220542805625710),
      (97,141100822147631732586278311110347137), (120,1013713538689156647436013690884452154), (120,1152573537388410508997576332697593749), (120,544809524158326833823230474033705659),
      (120,736958687864184392173999516922628072), (90,99774438253685866243809343714251086), (120,753627864117602352133457945418030173), (105,1240132789351261114690454399670850984),
      (106,665403787897700975280099888935331458), (120,980997451689886811498403096597197348), (97,992681001119097469742187201896153693), (108,644186307393572108249354515329238248),
      (120,678342861192520723949895871449718482), (103,981846773201455771275132755978187407), (120,420129432991655967877853828439529729), (120,490166786089604949164932576049545708),
      (101,63841979154113319760227872187034413), (120,979388597247370361881929056305986216), (106,352083273984504871825043983458237539), (120,1045540524689038934278846569915341648),
      (120,764132403720101970418426887309958449), (120,780076046687364441447461973026403827), (120,531266017334892857536993498403501823), (120,42863193879325826940797798534973245),
      (120,269519376215006698453295448001893529), (120,699734932909621941418068222908331806), (113,1034539973663205063479886881447486281), (116,930974135136398569668264955203179223),
      (120,510639225668342197654430105100219493), (114,358144996163694459876933622513195917), (118,380688320808131091224267659338284258), (120,1004161609881967731963276378178770742),
      (118,367765018922128930684023090928997228), (120,713054677568665680655201452181744561), (119,881554638506061779136799126605023315), (120,452947517347835370470005819585587907)]
  | 128 => [
      (128,332632790180847147897332469446279168), (128,997898370542541443691997408338837505), (128,1663163950904235739486662347231395841), (128,4989491852712707218459987041573601287),
      (128,5654757433074401514254651918273216513), (128,16964272299223204542763955231795183635), (128,28273787161213953395533657049250463765), (128,84821361477728917084689201374816305279),
      (128,85486571556924504164569615195302068225), (128,256459119656534113196943743114041819395), (128,267978376729219939715376880944459022597), (128,279715644237043581293540712915903710991),
      (128,337932083065607136857359856056901107985), (128,184468747547337165795042720859461718835), (128,31286947157182543914549688579969586517), (128,75241223410645093505821230540083134463),
      (18,97943242088258416052605896613604622337), (19,195504583878441635750656137275612069890), (128,232498729259532053215547623469890928644), (128,283591911536699950360658133527373545480),
      (45,262134065897370791417493783314881118229), (128,265627456438869322011781802576266068031), (47,258362431716816897826744230778071875691), (48,270708010235749249214532763114818568425),
      (47,32823648748343511036727033799253950892), (128,77426701048085099420173029036308562928), (128,227720353302141110998655596018869143155), (128,175207279558528712719062306486635071986),
      (128,258802632676793537972255603233569577643), (128,213765607404052380410916457263294987822), (128,288161990216368210646483904419442354098), (128,36033886181151815413440352323340053351),
      (120,265238796713627091288141981805793847624), (128,151717786455254171647987638432333053530), (53,63362753349137356443284720387579251584), (128,130378925360235701776774207879630700025),
      (65,142724892202045949995747422090817354281), (128,137609101929879298916495238907817867863), (67,23896212593918903280126869832452856213), (61,27559159336229840159975661524644822605),
      (77,226320871408542207101254110589595848626), (64,220184733940733504924245070578609496269), (97,136685933754177308951327284752670010007), (128,333567408073831711582783125675764729731),
      (94,60327989536908528872379149774575397955), (63,194183521259850101493674106728181599872), (128,10650280784777253830905840149057667810), (128,206965789546895050091424430280263395103),
      (128,265530166556893509833050151401609271719), (103,332600602943569097222058345784975069548), (109,22414684771411503919618394767405175903), (128,257561050909188066011391895515460880006),
      (60,148083007288026942163327295092952833203), (61,42397384005629780350880080837150119911), (128,316132115381238301008462787576192976404), (128,249762770431439562034149616270459099174),
      (62,306991850850872617572411663901071195459), (79,257885263354941958003594442814020506188), (128,55612407338125778742415608980916097220), (94,217869884210405075043769515533865984182),
      (63,154427309503270845314869267132564284370), (128,290784799939836448310506738186474752050), (119,66177170190783919520602423516202284074), (128,281910438071375624422934444479735977302),
      (121,222834806874687244463712692246110031590), (110,116953744974589198551637686993007458050), (128,299730970703976499540496840751905387526), (114,300520584482021064755709740653276879043),
      (128,127700422822808083977292639817906422777), (86,264209052250416136247324404707131095875), (97,139777522127770010834558013807508461266), (127,330716900647042446037122601592872676939),
      (81,273867552140787757512088755196791172406), (96,192407929875539081315426848810235587752), (102,133217246384461303708401376549458161395), (86,183460095595551890724295526633339402838),
      (128,124617356710117661353605949773906510459), (128,107928187216423150913929187861576330971), (128,61063894668655631858821858493726677276), (128,307720354945084543808915512823685304078),
      (128,250120187525736567335012115800448964891), (126,165553428165089955535586153014205459418), (106,179885099867038551169086921768819218211), (90,207076443031602803534438368557855360488),
      (89,20777620709977449050688621528249913106), (128,148774739362789191230019755585912000206), (128,96412525806637954794121319757512973948), (128,337716867124394097280968382489211779118),
      (112,187115352269903960297910866683068231263), (128,231059445087663596718936905408996265778), (128,258143458337396309389779954229116359380), (110,335206723234354108979448897250578880804),
      (128,19715736530765923240197256234162207623), (128,289122001155431154573687658511760364615), (115,207691601886147730226911942759261652381), (105,123239214766113347200987525344912841222),
      (119,71724634386636636109942145865000506740), (113,82863920146795681818725352532919816046), (121,295099980933885748926912336542270936983), (128,266377182110041099682521855969175902755),
      (104,81358525707729229296640824245559638817), (114,175645870055414679399480354991639110785), (114,20015091785937817893871952988656876384), (113,220315751334436691302172076845590118862),
      (119,134020500904894509310288810340423214606), (128,124197974116260046700237004410733348251), (126,304858900634587087004954063377649676756), (128,184018329118519769556172367222530666564),
      (128,336554541308498195151244850339743996492), (110,195413919989733699106193490456345095012), (128,270223142725746350753805328355409194602), (128,288417368615137989968362015391183508825),
      (128,256365763122566922712854028309417948261), (128,57954295809489224669065243668836641074), (128,51260491271580715774063522717587117624), (128,229495067527936177827848192634444879621),
      (128,2716932070407912565991453551084334150), (121,94766132392641646630963471478681927758), (121,221598972225179574695482666602642620489), (121,67948748635333189767231839796408525724),
      (121,14610635128319292538092436478426695623), (128,101734470610865574199195908639951244064), (128,108736443997484458150030109450629153673), (125,133324700765794782041345386914263737275),
      (128,312017793034313216658553753579861270421), (126,109375390721290221500500349494264558874), (128,38895173170926279131905358532261025852), (128,135423829056942686439695056224813953191)]
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
  | 1193, false => [1227316578898899697248833524463799068781391645696, 993131520466897774368198058845195913664134125568, 524761403602892631800361886382930956886942430208, 556201289978811289824378622072161501893417263104, 1112402579957623877722971877852383059016109048832, 474055470901554483387621498342510395422854447104, 948110941803110264850696779358184713978565035008, 884164693789409604400022983088036795730794774528, 306829144044492496835761263294787486472652718080, 613658289450114462622928190778866962119784924160]
  | 1193, true => [1036783722729269994784513103650070325898000204800, 612065806766507603680348370584661460891601996800, 1224130219736440297927860645992443563354153293824, 144445319734914840183390435546952678974792675328, 288890638107372281492568193626303852396811411456, 1192786605492564816726071258946432212285197434880, 922645719756767733609774252918267835023076982784, 1408054389184069030376956315188744468451560194048, 1354608534833810049446523543414214507769052397568, 1249142680029421842496205905192942690271473958912]
  | 1571, false => [1059534441212338394727200739901652069144342824960, 1158778702261269603671941431190839215275731064832, 856055767191637587214412663373456592024710950912, 250609897052372257492791094258860692890685825024, 501219794104744514986820128557006767156857193472, 127064852646215295094776027577972066248479047680, 254129705292431889532656438056184535622984335360, 509686658277569740215260912455744582401029177344, 1019374710351714388595707321040730742449670718464, 1260518039270955394064887886116305734060941509632]
  | 1571, true => [1181209465247127624106555731659858759399517979648, 476204971465339314094625608119031425181623520256, 950982693876844497429763959748096041005685413888, 440462356627539097144577273770179299868265164800, 879497466922171174752962025577081812871255449600, 1431424565675582789991549014474062954391419797504, 1399920246328887226700702650689307112053122629632, 1338338856689328932801806665821978500550996721664, 1215177471204130093984194390406505188546482405376, 589891109458440179951899137098466686528842366976]
  | 2047, false => [35699321203688184192805927426393939856233334784, 59975077516639285212017022655147772868206533632, 108515456098178922160775028003885043186575356928, 182793690406724892426039935939589178800440632320, 399835747528504376624225942626264592175396340736, 788247935605472628826732804903552649472906462208, 103570674428506215028061545847407163873824015360, 195717789405476305634094828641186270159130985472, 380012019359416486213264246912638913530273989632, 748600479267295551198245380071338479756082938880]
  | 2047, true => [275996463764044513351950377803138196232337884160, 460468926308365212075532539565973713594104679424, 827987998860675792437797069237131955550784329728, 102953146762545435310017548977429178363211689984, 115810933793318690975235994978602775973053620224, 140099260162159242424614562163739445535003164672, 5988208233477480547909884626830264644634509312, 285472406452026061149381040395084901767367557120, 480135132427639507363811232794698214228919975936, 868749049866245017608980837364077756610850848768]
  | 471, true => [9367455389391041106394642083152494848, 12072990206188763508193833572811047680, 28117657431239025963930976349034219008, 57569735155121502609875207111970524160, 108425950549963797921285720607598876672, 215522673183681536419572931442049036288, 88088844312693359604556431086171774976, 174827507303748157749887098463088295936]
  | 471, false => [257048253033682677601934886936900993536, 88574477695036615835485239415962928896, 91904071195901608150842409912829807616, 183813314326713291046184091686338763008, 283057442741692334309474518517414965248, 224498098349029708062005899248762249472, 192282211806401519189661953759841009920, 298000695939803426885384380317186621696]
  | _, _ => []

/-- Exact T, M, forward slots and inverse slots for the physical barrel. -/
def measuredCosts : Nat → Nat × Nat × Nat × Nat
  | 31 => (59,11,2101,2101)
  | 39 => (78,17,3158,3154)
  | 46 => (94,14,3847,3843)
  | 54 => (114,14,4857,4853)
  | 61 => (132,19,6176,6197)
  | 69 => (152,19,7360,7381)
  | 76 => (169,20,8511,8433)
  | 84 => (189,26,10669,10580)
  | 91 => (207,25,11988,11935)
  | 99 => (227,31,14113,14049)
  | 106 => (244,38,16394,16390)
  | 113 => (262,37,17972,17947)
  | 120 => (279,44,20462,20516)
  | 128 => (299,62,24256,24244)
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
  | 1193 => (25,0,300,300)
  | 1571 => (25,0,296,296)
  | 2047 => (25,0,281,281)
  | _ => (0,0,0,0)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrelData ====

-- ==== begin TickCutH3 ====
section

/- New H3 proof draft. Strict compilation is required before any reuse claim. -/
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Core
open ECDSAAdd Arithmetic IntegerPacket
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem ready_range (p : IntegerPacket.Shape) (i : Nat) (z : SkywalkRails.State)
    (s : BasisState) (h : IntegerPacket.ready p i z s) :
    (-((2^(p.mid+1):Nat):Int) ≤ z.a ∧ z.a < ((2^(p.mid+1):Nat):Int)) ∧
    (-((2^(p.mid+1):Nat):Int) ≤ z.b ∧ z.b < ((2^(p.mid+1):Nat):Int)) := by
  have la : (IntegerPacket.ports p i).a.length=p.mid+2 := by
    simp [IntegerPacket.ports,SkywalkIntegerLayout.a,SkywalkIntegerLayout.ah,Nat.add_assoc,Nat.add_comm]
    omega
  have lb : (IntegerPacket.ports p i).b.length=p.mid+2 := by
    simp [IntegerPacket.ports,SkywalkIntegerLayout.b,SkywalkIntegerLayout.bh,Nat.add_assoc,Nat.add_comm]
    omega
  have a := signedDecode_range (IntegerPacket.ports p i).a.length
    (regValue (IntegerPacket.ports p i).a s) (by rw [la]; omega) (regValue_lt _ _)
  have b := signedDecode_range (IntegerPacket.ports p i).b.length
    (regValue (IntegerPacket.ports p i).b s) (by rw [lb]; omega) (regValue_lt _ _)
  change -((2^((IntegerPacket.ports p i).a.length-1):Nat):Int) ≤
    signedRegValue (IntegerPacket.ports p i).a s ∧
    signedRegValue (IntegerPacket.ports p i).a s <
      ((2^((IntegerPacket.ports p i).a.length-1):Nat):Int) at a
  change -((2^((IntegerPacket.ports p i).b.length-1):Nat):Int) ≤
    signedRegValue (IntegerPacket.ports p i).b s ∧
    signedRegValue (IntegerPacket.ports p i).b s <
      ((2^((IntegerPacket.ports p i).b.length-1):Nat):Int) at b
  simp only [h.1,la] at a
  simp only [h.2.1,lb] at b
  simpa only [show p.mid+2-1=p.mid+1 by omega] using And.intro a b

theorem next_a_range (n : Nat) (z : SkywalkRails.State)
    (ha : -((2^(n+1):Nat):Int) ≤ z.a ∧ z.a < ((2^(n+1):Nat):Int))
    (hb : -((2^(n+1):Nat):Int) ≤ z.b ∧ z.b < ((2^(n+1):Nat):Int)) :
    -((2^n:Nat):Int) ≤ (SkywalkTrace.next z).a ∧
      (SkywalkTrace.next z).a < ((2^n:Nat):Int) := by
  have power : ((2^(n+1):Nat):Int)=2*((2^n:Nat):Int) := by
    rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [power] at ha hb
  simp only [SkywalkTrace.next,SkywalkRails.railsOf,SkywalkRails.step]
  unfold SkywalkRails.route
  split <;> dsimp only <;> omega

theorem ports_a_shape (p : IntegerPacket.Shape) (i : Nat) :
    (IntegerPacket.ports p i).a =
      List.range' (p.start+i+16) p.mid ++ [p.start+i+16+p.mid,p.start+i+16+p.mid+1] := by
  let b := p.start+i+16
  have slide : List.range' b p.mid ++ [b+p.mid] = b::List.range' (b+1) p.mid := by
    calc
      _ = List.range' b (p.mid+1) := List.range'_append_1
      _ = _ := List.range'_succ
  calc
    _ = (b::List.range' (b+1) p.mid) ++ [b+p.mid+1] := by
      simp [IntegerPacket.ports,SkywalkIntegerLayout.a,SkywalkIntegerLayout.ah,b,Nat.add_assoc]
    _ = (List.range' b p.mid ++ [b+p.mid]) ++ [b+p.mid+1] := by rw [slide]
    _ = _ := by simp [b,List.append_assoc]

/-- Every old forward tick leaves equal top two cells in its next A rail.
This derives the extra invariant from retained ready/one and signed bounds. -/
theorem one_top_pair (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1)
    (s : State) (m : List Bool) (ready : IntegerPacket.ready p i z s.basis) :
    (run (skywalkIntegerTick (IntegerPacket.ports p i)) m s).basis
        (p.start+i+17+p.mid+1) =
      (run (skywalkIntegerTick (IntegerPacket.ports p i)) m s).basis
        (p.start+i+17+p.mid) := by
  let out := run (skywalkIntegerTick (IntegerPacket.ports p i)) m s
  have post := (IntegerPacket.one p hi z odd s m ready).2
  have range := ready_range p i z s.basis ready
  have bounds := next_a_range p.mid z range.1 range.2
  have value : signedRegValue (IntegerPacket.ports p (i+1)).a out.basis = (SkywalkTrace.next z).a := post.1
  rw [ports_a_shape] at value
  have same := ECDSAAdd.Entrant.W.top_pair_eq
    (List.range' (p.start+(i+1)+16) p.mid)
    (p.start+(i+1)+16+p.mid) (p.start+(i+1)+16+p.mid+1)
    out.basis (SkywalkTrace.next z).a value
    (by simpa only [List.length_range'] using bounds.1)
    (by simpa only [List.length_range'] using bounds.2)
  simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using same

end ECDSAAdd.Entrant.StairPacket.TickCut.Core

end

section

/- Draft local identity only. This file does not select an H3 caller or claim 700 T.
The admitted forward invariant and routed-walk transport remain required. -/
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Core
open ECDSAAdd Arithmetic
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-- At the second CCX site, x already holds the first CCX's output. -/
def affineErase (k p q x y : Wire) : Program :=
  [.CX p y,.CX q y,.CX x y,.measureX y [] [.CZ k q],.CX p y,.CX q y,.CX x y]

/-- Both measurement branches reproduce the old CCX under the affine AND relation. -/
theorem affineErase_same (k p q x y : Wire) (hky : k≠y) (hpy : p≠y)
    (hqy : q≠y) (hxy : x≠y) (s : State) (m : List Bool)
    (known : (((s.basis y ^^ s.basis p) ^^ s.basis q) ^^ s.basis x) =
      (s.basis k && s.basis q)) :
    run (affineErase k p q x y) m s = run [.CCX k q y] [] s := by
  apply State.extensionality
  · cases hm : m.headD false <;>
      cases hk : s.basis k <;> cases hp : s.basis p <;>
      cases hq : s.basis q <;> cases hx : s.basis x <;> cases hy : s.basis y <;>
      simp_all [affineErase,run,measureAndCorrect,correct,writeBit,Function.update_apply]
  · funext w
    by_cases hw : w=y
    · subst w
      cases hm : m.headD false <;>
        cases hk : s.basis k <;> cases hp : s.basis p <;>
        cases hq : s.basis q <;> cases hx : s.basis x <;> cases hy : s.basis y <;>
        simp_all [affineErase,run,measureAndCorrect,correct,writeBit,Function.update_apply]
    · cases hm : m.headD false <;>
        simp [affineErase,run,measureAndCorrect,correct,writeBit,Function.update_apply,
          hw,hky,hpy,hqy,hxy,hm]


/-- Split a copy tape at equal-length register prefixes. -/
theorem copy_append (control : Option Wire) (a b a' b' : List Wire)
    (hlen : a.length=b.length) :
    copyRegister control (a++a') (b++b') =
      copyRegister control a b ++ copyRegister control a' b' := by
  induction a generalizing b with
  | nil =>
    have hb : b=[] := List.eq_nil_of_length_eq_zero hlen.symm
    subst b
    rfl
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      have htail : xs.length=ys.length := by simpa using hlen
      simpa only [List.cons_append,copyRegister,List.append_assoc] using
        congrArg (fun P : Program => [copyGate control x y]++P) (ih ys htail)

/-- Keep all low controlled copies and the first of the high pair. -/
def swapHigh (k : Wire) (a b : List Wire) (p q x y : Wire) : Program :=
  copyRegister none (b++[x,y]) (a++[p,q]) ++
    copyRegister (some k) a b ++ [.CCX k p x] ++ affineErase k p q x y ++
    copyRegister none (b++[x,y]) (a++[p,q])

/-- The old inverse swap has precisely the adjacent CCX pair selected by H3. -/
theorem swap_tail (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length) :
    swapRegisters k (a++[p,q]) (b++[x,y]) =
      copyRegister none (b++[x,y]) (a++[p,q]) ++
        copyRegister (some k) a b ++ [.CCX k p x,.CCX k q y] ++
        copyRegister none (b++[x,y]) (a++[p,q]) := by
  unfold swapRegisters
  rw [copy_append (some k) a b [p,q] [x,y] hlen]
  simp only [copyRegister,copyGate,List.append_assoc,List.cons_append,List.nil_append,List.append_nil]

/-- Exact syntax deltas; no admissibility or semantic hypothesis is hidden here. -/
theorem swapHigh_counts (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length) :
    toffoliCount (swapHigh k a b p q x y)+1 =
        toffoliCount (swapRegisters k (a++[p,q]) (b++[x,y])) ∧
    measurementCount (swapHigh k a b p q x y) =
        measurementCount (swapRegisters k (a++[p,q]) (b++[x,y]))+1 ∧
    Challenge.gateSlots (swapHigh k a b p q x y) =
        Challenge.gateSlots (swapRegisters k (a++[p,q]) (b++[x,y]))+7 := by
  have hf := copyRegister_counts none (b++[x,y]) (a++[p,q]) (by simp [hlen])
  have hl := copyRegister_counts (some k) a b hlen
  have ho := copyRegister_counts (some k) (a++[p,q]) (b++[x,y]) (by simp [hlen])
  change toffoliCount (copyRegister none (b++[x,y]) (a++[p,q]))=0 ∧
    measurementCount (copyRegister none (b++[x,y]) (a++[p,q]))=0 at hf
  change toffoliCount (copyRegister (some k) a b)=a.length ∧
    measurementCount (copyRegister (some k) a b)=0 at hl
  change toffoliCount (copyRegister (some k) (a++[p,q]) (b++[x,y]))=(a++[p,q]).length ∧
    measurementCount (copyRegister (some k) (a++[p,q]) (b++[x,y]))=0 at ho
  constructor
  · simp only [swapHigh,swapRegisters,toffoliCount_append,hf.1,hl.1,ho.1,
      affineErase,toffoliCount,List.length_append,List.length_cons,List.length_nil]
    omega
  constructor
  · simp only [swapHigh,swapRegisters,measurementCount_append,hf.2,hl.2,ho.2,
      affineErase,measurementCount]
  · have affineSlots : Challenge.gateSlots (affineErase k p q x y)=8 := rfl
    have oneSlot : Challenge.gateSlots [.CCX k p x]=1 := rfl
    simp only [swapHigh,swapRegisters,Challenge.gateSlots_append,affineSlots,oneSlot,
      Baselines.copyRegister_gateSlots,List.length_append,List.length_cons,List.length_nil,
      hlen,Nat.min_self]
    omega


/-- A measurement-free suffix is independent of its supplied tape. -/
theorem no_measure (P : Program) (h : measurementCount P=0) (s : State) (m : List Bool) :
    run P m s=run P [] s := by
  have same := run_take P m s
  simpa only [h,List.take_zero] using same.symm

theorem append_no_measure (P Q : Program) (hQ : measurementCount Q=0)
    (s : State) (m : List Bool) :
    run (P++Q) m s=run Q [] (run P m s) := by
  rw [run_append,run_take]
  exact no_measure Q hQ _ _

def suffixOld (k p q x y : Wire) (P : Program) : Program :=
  [.CCX k q y] ++ P ++ [.CX x p,.CX y q]

def suffixNew (k p q x y : Wire) (P : Program) : Program :=
  affineErase k p q x y ++ P ++ [.CX x p,.CX y q]

/-- The output top-pair invariant gives the affine relation at the last CCX.
P is the final swap's low CX layer; it leaves these four high wires alone. -/
theorem suffix_same (k p q x y : Wire) (P : Program)
    (distinct : [k,p,q,x,y].Nodup) (noP : measurementCount P=0)
    (frame : ∀(t : State)(m : List Bool)(w : Wire),w∈[p,q,x,y] →
      (run P m t).basis w=t.basis w)
    (s : State) (m : List Bool)
    (top : (run (suffixOld k p q x y P) [] s).basis p =
      (run (suffixOld k p q x y P) [] s).basis q) :
    run (suffixNew k p q x y P) m s=run (suffixOld k p q x y P) [] s := by
  simp only [List.nodup_cons,List.nodup_nil,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true] at distinct
  have hky : k≠y := by tauto
  have hpy : p≠y := by tauto
  have hqy : q≠y := by tauto
  have hxy : x≠y := by tauto
  have hpq : p≠q := by tauto
  have hxp : x≠p := by tauto
  have hxq : x≠q := by tauto
  have hqp : q≠p := Ne.symm hpq
  let t := run [.CCX k q y] [] s
  let u := run P [] t
  have up : u.basis p=s.basis p := by
    rw [frame t [] p (by simp)]
    simp [t,run,writeBit,Function.update_apply,hpy]
  have uq : u.basis q=s.basis q := by
    rw [frame t [] q (by simp)]
    simp [t,run,writeBit,Function.update_apply,hqy]
  have ux : u.basis x=s.basis x := by
    rw [frame t [] x (by simp)]
    simp [t,run,writeBit,Function.update_apply,hxy]
  have uy : u.basis y=(s.basis y ^^ (s.basis k && s.basis q)) := by
    rw [frame t [] y (by simp)]
    simp [t,run,writeBit,Function.update_apply]
  have out : run (suffixOld k p q x y P) [] s=run [.CX x p,.CX y q] [] u := by
    simp only [suffixOld,run_append,List.take_nil,List.drop_nil]
    rfl
  rw [out] at top
  have bits : (s.basis p ^^ s.basis x)=
      (s.basis q ^^ (s.basis y ^^ (s.basis k && s.basis q))) := by
    simpa only [run,writeBit,Function.update_apply,hpq,hqp,hxp,hxq,
      hpy,hqy,Ne.symm hpy,Ne.symm hqy,if_false,if_true,up,uq,ux,uy] using top
  have known : (((s.basis y ^^ s.basis p) ^^ s.basis q) ^^ s.basis x)=
      (s.basis k && s.basis q) := by
    cases hk : s.basis k <;> cases hp : s.basis p <;> cases hq : s.basis q <;>
      cases hx : s.basis x <;> cases hy : s.basis y <;> simp_all
  have localSame := affineErase_same k p q x y hky hpy hqy hxy s m known
  have noTail : measurementCount (P++[.CX x p,.CX y q])=0 := by
    simp [noP,measurementCount]
  change run (affineErase k p q x y ++ (P++[.CX x p,.CX y q])) m s = _
  rw [append_no_measure _ _ noTail,localSame]
  symm
  exact append_no_measure [.CCX k q y] (P++[.CX x p,.CX y q]) noTail s []


/-- Common prefix ending with the retained first high CCX. -/
def swapFront (k : Wire) (a b : List Wire) (p q x y : Wire) : Program :=
  copyRegister none (b++[x,y]) (a++[p,q]) ++
    copyRegister (some k) a b ++ [.CCX k p x]

theorem swap_old_shape (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length) :
    swapRegisters k (a++[p,q]) (b++[x,y]) =
      swapFront k a b p q x y ++ suffixOld k p q x y (copyRegister none b a) := by
  rw [swap_tail k a b p q x y hlen]
  simp only [swapFront,suffixOld,copy_append none b a [x,y] [p,q] hlen.symm,
    copyRegister,copyGate,List.append_assoc,
    List.cons_append,List.nil_append,List.append_nil]

theorem swap_new_shape (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length) :
    swapHigh k a b p q x y =
      swapFront k a b p q x y ++ suffixNew k p q x y (copyRegister none b a) := by
  unfold swapHigh
  simp only [swapFront,suffixNew,copy_append none b a [x,y] [p,q] hlen.symm,
    copyRegister,copyGate,List.append_assoc,
    List.cons_append,List.nil_append,List.append_nil]

/-- Generic optimized inverse-swap equality from its OLD output A high-pair fact. -/
theorem swapHigh_same (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length)
    (nd : (k::((a++[p,q])++(b++[x,y]))).Nodup)
    (s : State) (m : List Bool)
    (top : (run (swapRegisters k (a++[p,q]) (b++[x,y])) [] s).basis p =
      (run (swapRegisters k (a++[p,q]) (b++[x,y])) [] s).basis q) :
    run (swapHigh k a b p q x y) m s =
      run (swapRegisters k (a++[p,q]) (b++[x,y])) [] s := by
  have small : [k,p,q,x,y].Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp nd w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ndba : (b++a).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp nd w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have outside : ∀w∈[p,q,x,y],w∉a := by
    intro w hw ha
    have count := List.nodup_iff_count.mp nd w
    have positive := List.count_pos_iff.mpr ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl
    all_goals
      simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at count
      omega
  have frame : ∀(t : State)(n : List Bool)(w : Wire),w∈[p,q,x,y] →
      (run (copyRegister none b a) n t).basis w=t.basis w := by
    intro t n w hw
    exact (copyRegister_correct none b a hlen.symm ndba (by simp) t n).2.1 w (outside w hw)
  have hf := copyRegister_counts none (b++[x,y]) (a++[p,q]) (by simp [hlen])
  have hl := copyRegister_counts (some k) a b hlen
  have noFront : measurementCount (swapFront k a b p q x y)=0 := by
    simp only [swapFront,measurementCount_append,hf.2,hl.2,measurementCount]
  let u := run (swapFront k a b p q x y) [] s
  have topU : (run (suffixOld k p q x y (copyRegister none b a)) [] u).basis p =
      (run (suffixOld k p q x y (copyRegister none b a)) [] u).basis q := by
    rw [swap_old_shape k a b p q x y hlen,run_append] at top
    simpa only [List.take_nil,List.drop_nil] using top
  have hc := copyRegister_counts none b a hlen.symm
  have same := suffix_same k p q x y (copyRegister none b a) small hc.2 frame u m topU
  rw [swap_new_shape k a b p q x y hlen,swap_old_shape k a b p q x y hlen]
  simp only [run_append,noFront,List.take_zero,List.drop_zero,List.take_nil,List.drop_nil]
  exact same

/-- A measured receiver prefix uses identical old records; only the new final
swap measurement consumes an additional record, after all old measurements. -/
theorem prefix_swapHigh_same (P : Program) (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length)
    (nd : (k::((a++[p,q])++(b++[x,y]))).Nodup)
    (s : State) (m : List Bool)
    (top : (run (P++swapRegisters k (a++[p,q]) (b++[x,y])) m s).basis p =
      (run (P++swapRegisters k (a++[p,q]) (b++[x,y])) m s).basis q) :
    run (P++swapHigh k a b p q x y) m s =
      run (P++swapRegisters k (a++[p,q]) (b++[x,y])) m s := by
  have hf := copyRegister_counts none (b++[x,y]) (a++[p,q]) (by simp [hlen])
  have ho := copyRegister_counts (some k) (a++[p,q]) (b++[x,y]) (by simp [hlen])
  have noSwap : measurementCount (swapRegisters k (a++[p,q]) (b++[x,y]))=0 := by
    simp only [swapRegisters,measurementCount_append,hf.2,ho.2]
  rw [append_no_measure P _ noSwap s m] at top
  have same := swapHigh_same k a b p q x y hlen nd (run P m s)
    (m.drop (measurementCount P)) top
  rw [run_append,run_take,same]
  symm
  exact append_no_measure P _ noSwap s m

end ECDSAAdd.Entrant.StairPacket.TickCut.Core

end

section

/- Concrete H3 facade draft; compilation and caller integration remain pending. -/
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Receiver
open ECDSAAdd Arithmetic IntegerPacket TickCut.Core
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def lowA (p : IntegerPacket.Shape) (i : Nat) := List.range' (p.start+i+17) (p.mid-1)
def lowB (p : IntegerPacket.Shape) := List.range' 787 (p.mid-1)
def highP (p : IntegerPacket.Shape) (i : Nat) : Wire := p.start+i+16+p.mid
def highQ (p : IntegerPacket.Shape) (i : Nat) : Wire := p.start+i+17+p.mid
def highX (p : IntegerPacket.Shape) : Wire := 786+p.mid
def highY (p : IntegerPacket.Shape) : Wire := 787+p.mid

theorem range_two (b n : Nat) (hn : 1≤n) :
    List.range' b n ++ [b+n] = List.range' b (n-1) ++ [b+(n-1),b+n] := by
  cases n with
  | zero => omega
  | succ r =>
    change List.range' b (r+1) ++ [b+(r+1)] =
      List.range' b r ++ [b+r,b+(r+1)]
    have eq : List.range' b r ++ [b+r] = List.range' b (r+1) := by
      simpa only [List.range'_one] using (List.range'_append_1 (s:=b) (m:=r) (n:=1))
    rw [←eq]
    simp only [List.append_assoc,List.singleton_append]

theorem ah_shape (p : IntegerPacket.Shape) (i : Nat) (hm : 1≤p.mid) :
    (IntegerPacket.ports p i).ah = lowA p i ++ [highP p i,highQ p i] := by
  have h := range_two (p.start+i+17) p.mid hm
  have hp : p.start+i+17+(p.mid-1)=highP p i := by dsimp [highP]; omega
  rw [hp] at h
  simpa only [IntegerPacket.ports,SkywalkIntegerLayout.ah,lowA,highQ,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem bh_shape (p : IntegerPacket.Shape) (i : Nat) (hm : 1≤p.mid) :
    (IntegerPacket.ports p i).bh = lowB p ++ [highX p,highY p] := by
  have h := range_two 787 p.mid hm
  have hp : 787+(p.mid-1)=highX p := by dsimp [highX]; omega
  rw [hp] at h
  simpa only [IntegerPacket.ports,SkywalkIntegerLayout.bh,lowB,highY,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem low_lengths (p : IntegerPacket.Shape) (i : Nat) : (lowA p i).length=(lowB p).length := by
  simp only [lowA,lowB,List.length_range']

theorem swap_nodup (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length) (hm : 1≤p.mid) :
    ((IntegerPacket.ports p i).a0::((lowA p i++[highP p i,highQ p i])++
      (lowB p++[highX p,highY p]))).Nodup := by
  have nd := SkywalkIntegerLayout.route_nodup _ (IntegerPacket.ok p ⟨i,hi⟩)
  change ((IntegerPacket.ports p i).a0::(IntegerPacket.ports p i).b0::
    ((IntegerPacket.ports p i).ah++(IntegerPacket.ports p i).bh)).Nodup at nd
  rw [ah_shape p i hm,bh_shape p i hm] at nd
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp nd w
  simp only [List.count_cons] at h ⊢
  omega

def receiverPrefix (L : SkywalkIntegerLayout) (n : Nat) : Program :=
  [.CX L.previous L.a0] ++ ECDSAAdd.Entrant.W.ReverseCarry.narrowReceiver
    (narrowSkywalkRecordLayout L n) n ++ skywalkSignedHalf L.aSign L.ext ++ [.CX L.a0 L.b0]

def receiverHigh (p : IntegerPacket.Shape) (i : Nat) : Program :=
  receiverPrefix (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length ++
    swapHigh (IntegerPacket.ports p i).a0 (lowA p i) (lowB p)
      (highP p i) (highQ p i) (highX p) (highY p)

theorem receiverHigh_same (p : IntegerPacket.Shape) (i : Nat)
    (hi : i<p.length) (hm : 1≤p.mid) (s : State) (m : List Bool)
    (top : (run (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
        (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length) m s).basis (highP p i) =
      (run (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
        (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length) m s).basis (highQ p i)) :
    run (receiverHigh p i) m s = run (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
      (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length) m s := by
  have same := prefix_swapHigh_same
    (receiverPrefix (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length)
    (IntegerPacket.ports p i).a0 (lowA p i) (lowB p)
    (highP p i) (highQ p i) (highX p) (highY p)
    (low_lengths p i) (swap_nodup p i hi hm) s m
    (by simpa only [receiverPrefix,ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick,
      ah_shape p i hm,bh_shape p i hm] using top)
  simpa only [receiverHigh,receiverPrefix,ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick,
    ah_shape p i hm,bh_shape p i hm] using same

theorem receiverHigh_counts (p : IntegerPacket.Shape) (i : Nat) (hm : 1≤p.mid) :
    toffoliCount (receiverHigh p i)+1 = toffoliCount
      (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
        (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length) ∧
    measurementCount (receiverHigh p i) = measurementCount
      (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
        (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length)+1 ∧
    Challenge.gateSlots (receiverHigh p i) = Challenge.gateSlots
      (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
        (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length)+7 := by
  have counts := swapHigh_counts (IntegerPacket.ports p i).a0 (lowA p i) (lowB p)
    (highP p i) (highQ p i) (highX p) (highY p) (low_lengths p i)
  simp only [receiverHigh,receiverPrefix,ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick,
    ah_shape p i hm,bh_shape p i hm,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append]
  omega

def readyPlus (p : IntegerPacket.Shape) (i : Nat) (z : SkywalkRails.State) (b : BasisState) : Prop :=
  IntegerPacket.ready p i z b ∧ ((0 < i) → (b (highP p i)=b (highQ p i)))

theorem onePlus (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Triple (readyPlus p i z) (skywalkIntegerTick (IntegerPacket.ports p i))
      (readyPlus p (i+1) (SkywalkTrace.next z)) := by
  intro s m h
  have old := IntegerPacket.one p hi z odd s m h.1
  refine ⟨old.1,old.2,?_⟩
  intro positive
  have top := one_top_pair p i hi z odd s m h.1
  simpa only [highP,highQ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using top.symm

def receiverSelected (p : IntegerPacket.Shape) (i : Nat) : Program :=
  if i=0 then ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
    (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length else receiverHigh p i

theorem singleHigh (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length) (hm : 1≤p.mid)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Restores (readyPlus p i z) (skywalkIntegerTick (IntegerPacket.ports p i))
      (receiverSelected p i) := by
  intro s m n h
  have old := IntegerPacket.singleR p ⟨i,hi⟩ z odd s m n h.1
  by_cases zero : i=0
  · simpa only [receiverSelected,zero,if_true] using old
  · simp only [receiverSelected,zero,if_false]
    rw [receiverHigh_same p i hi hm]
    · exact old
    · rw [old]
      exact h.2 (by omega)

def backHigh (p : IntegerPacket.Shape) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => backHigh p (i+1) n ++ receiverSelected p i

private theorem composeHigh {P Q : BasisState → Prop} {A B I J : Program}
    (stage : Triple P A Q) (left : Restores P A I) (right : Restores Q B J) :
    Restores P (A++B) (J++I) := by
  intro s enc dec p
  rw [run_append J I,run_append A B]
  rw [right _ _ _ (stage _ _ p).2]
  exact left _ _ _ p

/-- Stronger ready predicate carries the preceding-tick invariant through the
old forward trajectory. Tick zero keeps the original receiver. -/
theorem roundtripHigh (p : IntegerPacket.Shape) (i n : Nat) (bound : i+n≤p.length)
    (hm : 1≤p.mid) (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Restores (readyPlus p i z) (IntegerPacket.seq p i n) (backHigh p i n) := by
  induction n generalizing i z with
  | zero =>
    intro s a b h
    simp [IntegerPacket.seq,backHigh,run]
  | succ n ih =>
    rw [IntegerPacket.seq,backHigh]
    apply composeHigh (onePlus p i (by omega) z odd)
    · exact singleHigh p i (by omega) hm z odd
    · exact ih (i+1) (by omega) (SkywalkTrace.next z) (IntegerPacket.nextOdd z odd)

end ECDSAAdd.Entrant.StairPacket.TickCut.Receiver

end

section

/- New H3 hosted transport draft. No selected caller is changed by this probe. -/
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Hosted
open ECDSAAdd Arithmetic IntegerPacket TickCut.Receiver
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

theorem semanticPlus (p : IntegerPacket.Shape) (i n : Nat) (bound : i+n≤p.length)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Triple (readyPlus p i z) (IntegerPacket.seq p i n)
      (readyPlus p (i+n) (SkywalkTrace.next^[n] z)) := by
  induction n generalizing i z with
  | zero =>
    intro s m h
    simpa [IntegerPacket.seq,run] using And.intro (rfl : s.phase=s.phase) h
  | succ n ih =>
    have a := onePlus p i (by omega) z odd
    have b := ih (i+1) (by omega) (SkywalkTrace.next z) (IntegerPacket.nextOdd z odd)
    simpa only [IntegerPacket.seq,Function.iterate_succ_apply,show i+(n+1)=i+1+n by omega] using a.seq b

def onRailsPlus (j : Fin 26) (i : Nat) (z : SkywalkRails.State) (b : BasisState) :=
  readyPlus (Shadow7.shape j) i z (mappedBasis j b)

def unroutedHigh (j : Fin 26) (i n : Nat) : Program :=
  renameProgram (windowNet j) (backHigh (Shadow7.shape j) i n)

theorem routeFramePlus (j : Fin 26) (i n : Nat) (bound : i+n≤15)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Triple (onRailsPlus j i z) (Shadow7.routed j i n)
      (onRailsPlus j (i+n) (SkywalkTrace.next^[n] z)) := by
  intro s m ready
  have h := semanticPlus (Shadow7.shape j) i n bound z odd (pullState (windowNet j) s) m ready
  rw [←Shadow7.pull_routed j i n bound m s] at h
  exact h

theorem routeUndoHigh (j : Fin 26) (i n : Nat) (bound : i+n≤15)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Restores (onRailsPlus j i z) (Shadow7.routed j i n) (unroutedHigh j i n) := by
  intro s m t ready
  have forward := Shadow7.pull_routed j i n bound m s
  let actual := run (Shadow7.routed j i n) m s
  have bk : pullState (windowNet j) (run (unroutedHigh j i n) t actual)=
      run (backHigh (Shadow7.shape j) i n) t (pullState (windowNet j) actual) := by
    rw [unroutedHigh,run_rename _ (netInjective j)]
  have hm : 1≤(Shadow7.shape j).mid := by simp [Shadow7.shape]
  have fin := roundtripHigh (Shadow7.shape j) i n bound hm z odd
    (pullState (windowNet j) s) m t ready
  change pullState (windowNet j) actual=_ at forward
  rw [forward,fin] at bk
  apply congrArg₂ State.mk (congrArg State.phase bk)
  funext q
  have h := congrArg (fun x : State => x.basis (windowNet j q)) bk
  change (run (unroutedHigh j i n) t actual).basis (windowNet j (windowNet j q))=
    s.basis (windowNet j (windowNet j q)) at h
  have inv : windowNet j (windowNet j q)=q := by
    apply OB5.sig_invol
    have hj := j.isLt
    simp [start]; omega
  rwa [inv] at h

theorem watch_a (j : Fin 26) (q : Wire)
    (hq : q∈(IntegerPacket.ports (Shadow7.shape j) 1).a) :
    windowNet j q∈Shadow7.watch j := by
  unfold Shadow7.watch
  dsimp only
  apply List.mem_map.mpr
  refine ⟨q,?_,rfl⟩
  simp only [List.mem_append]
  tauto

/-- Archive administration preserves the stronger first successor invariant
because the stock watch contains its entire A rail. -/
theorem watch_congrPlus (j : Fin 26) (s t : State)
    (agree : ∀q∈Shadow7.watch j,t.basis q=s.basis q)
    (z : SkywalkRails.State) (active : onRailsPlus j 1 z s.basis) :
    onRailsPlus j 1 z t.basis := by
  have old := (Shadow7.watch_congr j s t agree z active.1).1
  refine ⟨old,?_⟩
  intro positive
  have hm : 1≤(Shadow7.shape j).mid := by simp [Shadow7.shape]
  have hp : highP (Shadow7.shape j) 1∈(IntegerPacket.ports (Shadow7.shape j) 1).a := by
    simp only [SkywalkIntegerLayout.a,ah_shape _ _ hm,List.mem_cons,List.mem_append]
    simp
  have hq : highQ (Shadow7.shape j) 1∈(IntegerPacket.ports (Shadow7.shape j) 1).a := by
    simp only [SkywalkIntegerLayout.a,ah_shape _ _ hm,List.mem_cons,List.mem_append]
    simp
  change t.basis (windowNet j (highP (Shadow7.shape j) 1))=
    t.basis (windowNet j (highQ (Shadow7.shape j) 1))
  rw [agree _ (watch_a j _ hp),agree _ (watch_a j _ hq)]
  exact active.2 positive

def unbodyHigh (j : Fin 26) (reverse : Program) : Program :=
  unroutedHigh j 1 14 ++ (reverse ++ unroutedHigh j 0 1)

/-- The selected new reverse body restores the untouched old forward body.
Both invariant propagation and archive administration use retained old semantics. -/
theorem body_runHigh (j : Fin 26) (admin reverse : Program) (s : State) (m : List Bool)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) (active : Shadow7.onRails j 0 z s.basis)
    (mid : let src:=run (Shadow7.routed j 0 1) m s
      Shadow7.AdminResult j reverse src (run admin (m.drop (measurementCount (Shadow7.routed j 0 1))) src)) :
    let out:=run (Shadow7.body j admin) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unbodyHigh j reverse) n out=s := by
  let src := run (Shadow7.routed j 0 1) m s
  let t := m.drop (measurementCount (Shadow7.routed j 0 1))
  let pre := run admin t src
  let n := t.drop (measurementCount admin)
  have strong0 : onRailsPlus j 0 z s.basis := ⟨active,by intro bad; omega⟩
  have head := routeFramePlus j 0 1 (by decide) z odd s m strong0
  have valid : onRailsPlus j 1 (SkywalkTrace.next z) src.basis := head.2
  have pass := watch_congrPlus j src pre mid.unchanged _ valid
  have oldPass := Shadow7.watch_congr j src pre mid.unchanged _ valid.1
  have span := Shadow7.split_run j z odd s m n active pre oldPass.1 oldPass.2
  have last := routeFramePlus j 1 14 (by decide) (SkywalkTrace.next z)
    (IntegerPacket.nextOdd z odd) pre n pass
  dsimp only [Shadow7.body,unbodyHigh]
  simp only [run_append,run_take]
  refine ⟨last.1.trans (mid.phase.trans head.1),span.1,span.2,?_⟩
  intro r
  have endBack := routeUndoHigh j 1 14 (by decide) (SkywalkTrace.next z)
    (IntegerPacket.nextOdd z odd) pre n r pass
  change run (unroutedHigh j 0 1) _ (run reverse _
    (run (unroutedHigh j 1 14) r (run (Shadow7.routed j 1 14) n pre)))=s
  rw [endBack,mid.undo]
  exact routeUndoHigh j 0 1 (by decide) z odd s m _ strong0

end ECDSAAdd.Entrant.StairPacket.TickCut.Hosted

end

section

namespace ECDSAAdd.Entrant.StairPacket.TickCut.Static
open ECDSAAdd Arithmetic RecordedQuantum IntegerPacket TickCut.Core TickCut.Receiver TickCut.Hosted
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem swapHigh_support (k : Wire) (a b : List Wire) (p q x y : Wire) :
    wires (swapHigh k a b p q x y) ⊆ (k::((a++[p,q])++(b++[x,y]))).toFinset := by
  let target := (k::((a++[p,q])++(b++[x,y]))).toFinset
  have back : wires (copyRegister none (b++[x,y]) (a++[p,q])) ⊆ target := by
    intro w hw
    have h := copyRegister_wires_subset none (b++[x,y]) (a++[p,q]) hw
    simp only [target,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,
      Option.toList_none,List.nil_append,or_false] at h ⊢
    tauto
  have low : wires (copyRegister (some k) a b) ⊆ target := by
    intro w hw
    have h := copyRegister_wires_subset (some k) a b hw
    simp only [target,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,
      Option.toList_some,List.singleton_append,or_false] at h ⊢
    tauto
  have first : wires [.CCX k p x] ⊆ target := by
    intro w hw
    simp [target,wires,Instr.wires] at hw ⊢
    tauto
  have aff : wires (affineErase k p q x y) ⊆ target := by
    intro w hw
    simp [target,affineErase,wires,Instr.wires,correctionWires] at hw ⊢
    tauto
  intro w hw
  simp only [swapHigh,wires_append,Finset.mem_union] at hw
  rcases hw with (((h|h)|h)|h)|h
  · exact back h
  · exact low h
  · exact first h
  · exact aff h
  · exact back h

theorem swapHigh_physical (k : Wire) (a b : List Wire) (p q x y : Wire)
    (nd : (k::((a++[p,q])++(b++[x,y]))).Nodup) : GatePhysical (swapHigh k a b p q x y) := by
  have full := (List.nodup_cons.mp nd).2
  have back := copyRegister_physical none (b++[x,y]) (a++[p,q])
    (List.nodup_append_comm.mpr full) (by simp)
  have ndab : (a++b).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp nd w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have low := copyRegister_physical (some k) a b ndab (by
    intro c hc hb
    cases hc
    apply (List.nodup_cons.mp nd).1
    simp [hb])
  have small : [k,p,q,x,y].Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp nd w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.nodup_nil,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true] at small
  have first : GatePhysical [.CCX k p x] := by
    simp_all [GatePhysical,PhysicalInstr,ProperGate]
  have aff : GatePhysical (affineErase k p q x y) := by
    simp_all [affineErase,GatePhysical,PhysicalInstr,ProperGate]
  simp only [swapHigh,gatePhysical_append]
  exact ⟨⟨⟨⟨back,low⟩,first⟩,aff⟩,back⟩

theorem receiverHigh_support (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length) (hm : 1≤p.mid) :
    wires (receiverHigh p i) ⊆ (IntegerPacket.ports p i).wires.toFinset := by
  let L := IntegerPacket.ports p i
  have valid := IntegerPacket.ok p ⟨i,hi⟩
  have hn : 0<L.half.length := by simp [SkywalkIntegerLayout.half]
  have old := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_support L L.half.length valid hn le_rfl
  have front : wires (receiverPrefix L L.half.length) ⊆ L.wires.toFinset := by
    intro w hw
    apply old
    change w∈wires (receiverPrefix L L.half.length ++ swapRegisters L.a0 L.ah L.bh)
    rw [wires_append,Finset.mem_union]
    exact Or.inl hw
  have tail := swapHigh_support L.a0 (lowA p i) (lowB p)
    (highP p i) (highQ p i) (highX p) (highY p)
  have tailInside : wires (swapHigh L.a0 (lowA p i) (lowB p)
      (highP p i) (highQ p i) (highX p) (highY p)) ⊆ L.wires.toFinset := by
    intro w hw
    have h := tail hw
    rw [←ah_shape p i hm,←bh_shape p i hm] at h
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  intro w hw
  simp only [receiverHigh,wires_append,Finset.mem_union] at hw
  exact hw.elim (fun h=>front h) (fun h=>tailInside h)

theorem receiverHigh_physical (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length) (hm : 1≤p.mid) :
    GatePhysical (receiverHigh p i) := by
  let L := IntegerPacket.ports p i
  have valid := IntegerPacket.ok p ⟨i,hi⟩
  have hn : 0<L.half.length := by simp [SkywalkIntegerLayout.half]
  have old := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_physical L L.half.length valid hn le_rfl
  change GatePhysical (receiverPrefix L L.half.length ++ swapRegisters L.a0 L.ah L.bh) at old
  have front := (gatePhysical_append _ _).mp old |>.1
  have tail := swapHigh_physical L.a0 (lowA p i) (lowB p)
    (highP p i) (highQ p i) (highX p) (highY p) (swap_nodup p i hi hm)
  exact (gatePhysical_append _ _).mpr ⟨front,tail⟩

/-- Every positive-index reverse span saves exactly one T per tick. -/
theorem backHigh_counts (p : IntegerPacket.Shape) (i n : Nat)
    (hm : 1≤p.mid) (positive : 0 < i) :
    toffoliCount (backHigh p i n)+n = toffoliCount (IntegerPacket.backR p i n) ∧
    measurementCount (backHigh p i n) = measurementCount (IntegerPacket.backR p i n)+n ∧
    Challenge.gateSlots (backHigh p i n) = Challenge.gateSlots (IntegerPacket.backR p i n)+7*n := by
  induction n generalizing i with
  | zero => simp [backHigh,IntegerPacket.backR,toffoliCount,measurementCount,Challenge.gateSlots]
  | succ n ih =>
    have tail := ih (i+1) (by omega)
    have point := receiverHigh_counts p i hm
    have nonzero : ¬i=0 := by omega
    simp only [backHigh,IntegerPacket.backR,receiverSelected,nonzero,if_false,
      toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
    omega

end ECDSAAdd.Entrant.StairPacket.TickCut.Static

end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Tail
open ECDSAAdd Arithmetic IntegerPacket TickCut.Receiver TickCut.Hosted TickCut.Static
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def selected (j : Fin 26) (a n : Nat) : Program :=
  if a=1 ∧ n=14 then unroutedHigh j 1 14 else Shadow7.unrouted j a n

theorem head_eq (j : Fin 26) : unroutedHigh j 0 1=Shadow7.unrouted j 0 1 := by
  rw [(Shadow7.fixed_route j 0 1 (by decide)).2]
  simp [unroutedHigh,backHigh,receiverSelected,IntegerPacket.backR]

def unbodySelected (j : Fin 26) (reverse : Program) :=
  selected j 1 14 ++ (reverse ++ selected j 0 1)

theorem unbody_eq (j : Fin 26) (reverse : Program) :
    unbodySelected j reverse=unbodyHigh j reverse := by
  simp only [unbodySelected,selected,unbodyHigh,show (1:Nat)=1 ∧ (14:Nat)=14 from ⟨rfl,rfl⟩,
    and_true,if_true,show ¬((0:Nat)=1 ∧ (1:Nat)=14) by omega,if_false]
  rw [head_eq]

theorem body_runSelected (j : Fin 26) (admin reverse : Program) (s : State) (m : List Bool)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) (active : Shadow7.onRails j 0 z s.basis)
    (mid : let src:=run (Shadow7.routed j 0 1) m s
      Shadow7.AdminResult j reverse src (run admin (m.drop (measurementCount (Shadow7.routed j 0 1))) src)) :
    let out:=run (Shadow7.body j admin) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unbodySelected j reverse) n out=s := by
  simpa only [unbody_eq] using body_runHigh j admin reverse s m z odd active mid

theorem tail_counts (j : Fin 26) :
    toffoliCount (unroutedHigh j 1 14)+14=toffoliCount (Shadow7.unrouted j 1 14) ∧
    measurementCount (unroutedHigh j 1 14)=measurementCount (Shadow7.unrouted j 1 14)+14 ∧
    Challenge.gateSlots (unroutedHigh j 1 14)=Challenge.gateSlots (Shadow7.unrouted j 1 14)+98 := by
  have hm : 1≤(Shadow7.shape j).mid := by simp [Shadow7.shape]
  have c := backHigh_counts (Shadow7.shape j) 1 14 hm (by decide)
  rw [(Shadow7.fixed_route j 1 14 (by decide)).2]
  simpa only [unroutedHigh,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    Baselines.rename_gateSlots] using c

theorem selected_t (j : Fin 26) (a n : Nat) :
    toffoliCount (selected j a n)=toffoliCount (Shadow7.unrouted j a n) -
      (if a=1 ∧ n=14 then 14 else 0) := by
  by_cases h : a=1 ∧ n=14
  · rcases h with ⟨rfl,rfl⟩
    have c := (tail_counts j).1
    simp only [selected,if_pos (show (1:Nat)=1 ∧ (14:Nat)=14 from ⟨rfl,rfl⟩),and_true,if_true]
    omega
  · simp only [selected,h,if_false,Nat.sub_zero]

theorem selected_m (j : Fin 26) (a n : Nat) :
    measurementCount (selected j a n)=measurementCount (Shadow7.unrouted j a n) +
      (if a=1 ∧ n=14 then 14 else 0) := by
  by_cases h : a=1 ∧ n=14
  · rcases h with ⟨rfl,rfl⟩
    simpa only [selected,if_pos (show (1:Nat)=1 ∧ (14:Nat)=14 from ⟨rfl,rfl⟩),and_true,if_true] using (tail_counts j).2.1
  · simp only [selected,h,if_false,Nat.add_zero]

theorem selected_slots (j : Fin 26) (a n : Nat) :
    Challenge.gateSlots (selected j a n)=Challenge.gateSlots (Shadow7.unrouted j a n) +
      (if a=1 ∧ n=14 then 98 else 0) := by
  by_cases h : a=1 ∧ n=14
  · rcases h with ⟨rfl,rfl⟩
    simpa only [selected,if_pos (show (1:Nat)=1 ∧ (14:Nat)=14 from ⟨rfl,rfl⟩),and_true,if_true] using (tail_counts j).2.2
  · simp only [selected,h,if_false,Nat.add_zero]

end ECDSAAdd.Entrant.StairPacket.TickCut.Tail

end
-- ==== end TickCutH3 ====

-- ==== begin CRTBarrel ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Arithmetic.MappedCompressed

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

def fieldDegree (p : Nat) : Nat := Nat.log2 p




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

def order33_1193 : Program := [
  .CX 19 16,
  .CX 21 16,
  .CX 23 16,
  .CX 25 16,
  .CX 27 16,
  .CX 29 16,
  .CX 31 16,
  .CX 33 16,
  .CX 9 8,
  .CX 9 7,
  .CX 9 6,
  .CX 9 5,
  .CX 9 0,
  .CX 8 9,
  .CX 8 7,
  .CX 8 6,
  .CX 8 5,
  .CX 8 4,
  .CX 8 2,
  .CX 8 1,
  .CX 9 8,
  .CX 7 9,
  .CX 7 5,
  .CX 7 4,
  .CX 7 2,
  .CX 9 7,
  .CX 6 7,
  .CX 6 3,
  .CX 7 6,
  .CX 5 9,
  .CX 5 4,
  .CX 9 5,
  .CX 4 8,
  .CX 8 4,
  .CX 3 6,
  .CX 6 3,
  .CX 2 4,
  .CX 4 2,
  .CX 1 2,
  .CX 2 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 20 16,
  .CX 21 16,
  .CX 24 16,
  .CX 25 16,
  .CX 28 16,
  .CX 29 16,
  .CX 32 16,
  .CX 33 16,
  .CX 9 8,
  .CX 9 7,
  .CX 9 3,
  .CX 9 2,
  .CX 9 1,
  .CX 9 0,
  .CX 8 9,
  .CX 8 7,
  .CX 8 6,
  .CX 9 8,
  .CX 7 9,
  .CX 7 8,
  .CX 7 6,
  .CX 8 7,
  .CX 6 7,
  .CX 6 5,
  .CX 6 4,
  .CX 7 6,
  .CX 5 7,
  .CX 5 6,
  .CX 5 4,
  .CX 6 5,
  .CX 4 5,
  .CX 4 3,
  .CX 4 2,
  .CX 5 4,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 4 3,
  .CX 2 3,
  .CX 2 1,
  .CX 2 0,
  .CX 3 2,
  .CX 1 3,
  .CX 1 2,
  .CX 1 0,
  .CX 2 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 19 16,
  .CX 21 16,
  .CX 22 16,
  .CX 24 16,
  .CX 27 16,
  .CX 29 16,
  .CX 30 16,
  .CX 32 16,
  .CX 9 8,
  .CX 9 5,
  .CX 9 3,
  .CX 9 2,
  .CX 9 1,
  .CX 8 7,
  .CX 8 5,
  .CX 8 4,
  .CX 8 1,
  .CX 7 8,
  .CX 7 1,
  .CX 8 7,
  .CX 6 9,
  .CX 6 1,
  .CX 9 6,
  .CX 5 7,
  .CX 5 6,
  .CX 5 4,
  .CX 6 5,
  .CX 4 5,
  .CX 4 1,
  .CX 4 0,
  .CX 5 4,
  .CX 3 9,
  .CX 3 4,
  .CX 3 2,
  .CX 3 0,
  .CX 4 3,
  .CX 1 5,
  .CX 1 4,
  .CX 1 0,
  .CX 4 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 20 16,
  .CX 21 16,
  .CX 24 16,
  .CX 25 16,
  .CX 26 16,
  .CX 27 16,
  .CX 30 16,
  .CX 31 16,
  .CX 9 6,
  .CX 9 5,
  .CX 9 4,
  .CX 9 1,
  .CX 8 7,
  .CX 8 5,
  .CX 8 3,
  .CX 7 8,
  .CX 7 4,
  .CX 7 3,
  .CX 7 2,
  .CX 7 1,
  .CX 7 0,
  .CX 8 7,
  .CX 6 9,
  .CX 6 1,
  .CX 6 0,
  .CX 9 6,
  .CX 5 9,
  .CX 5 7,
  .CX 5 4,
  .CX 5 3,
  .CX 5 1,
  .CX 5 0,
  .CX 7 5,
  .CX 3 9,
  .CX 3 8,
  .CX 3 7,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 1 9,
  .CX 1 8,
  .CX 1 0,
  .CX 8 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 22 16,
  .CX 23 16,
  .CX 24 16,
  .CX 25 16,
  .CX 30 16,
  .CX 31 16,
  .CX 32 16,
  .CX 33 16,
  .CX 9 8,
  .CX 9 7,
  .CX 9 6,
  .CX 9 3,
  .CX 9 1,
  .CX 9 0,
  .CX 8 9,
  .CX 8 4,
  .CX 8 3,
  .CX 8 0,
  .CX 9 8,
  .CX 7 9,
  .CX 7 8,
  .CX 7 6,
  .CX 7 4,
  .CX 7 3,
  .CX 7 2,
  .CX 8 7,
  .CX 5 9,
  .CX 5 8,
  .CX 5 7,
  .CX 5 6,
  .CX 4 9,
  .CX 4 8,
  .CX 4 3,
  .CX 4 0,
  .CX 8 4,
  .CX 3 9,
  .CX 3 8,
  .CX 3 7,
  .CX 3 2,
  .CX 3 1,
  .CX 7 3,
  .CX 2 7,
  .CX 2 4,
  .CX 2 1,
  .CX 2 0,
  .CX 4 2,
  .CX 1 7,
  .CX 1 4,
  .CX 1 2,
  .CX 1 0,
  .CX 2 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 9 6,
  .CX 9 5,
  .CX 9 1,
  .CX 9 0,
  .CX 8 9,
  .CX 8 5,
  .CX 8 4,
  .CX 8 3,
  .CX 8 2,
  .CX 8 1,
  .CX 8 0,
  .CX 9 8,
  .CX 7 8,
  .CX 7 5,
  .CX 7 4,
  .CX 7 3,
  .CX 7 2,
  .CX 8 7,
  .CX 6 9,
  .CX 6 8,
  .CX 6 3,
  .CX 6 1,
  .CX 5 7,
  .CX 5 2,
  .CX 5 1,
  .CX 5 0,
  .CX 4 9,
  .CX 4 7,
  .CX 4 5,
  .CX 4 3,
  .CX 5 4,
  .CX 3 9,
  .CX 3 8,
  .CX 3 6,
  .CX 3 1,
  .CX 6 3,
  .CX 2 8,
  .CX 2 7,
  .CX 2 6,
  .CX 2 5,
  .CX 2 1,
  .CX 1 8,
  .CX 1 7,
  .CX 1 6,
  .CX 1 5,
  .CX 1 2,
  .CX 2 1,
  .CX 26 16,
  .CX 27 16,
  .CX 28 16,
  .CX 29 16,
  .CX 30 16,
  .CX 31 16,
  .CX 32 16,
  .CX 33 16
]

def order33_1571 : Program := [
  .CX 19 16,
  .CX 21 16,
  .CX 23 16,
  .CX 25 16,
  .CX 27 16,
  .CX 29 16,
  .CX 31 16,
  .CX 33 16,
  .CX 9 8,
  .CX 9 7,
  .CX 9 6,
  .CX 9 5,
  .CX 9 0,
  .CX 8 9,
  .CX 8 7,
  .CX 8 6,
  .CX 8 5,
  .CX 8 4,
  .CX 8 2,
  .CX 8 1,
  .CX 9 8,
  .CX 7 9,
  .CX 7 5,
  .CX 7 4,
  .CX 7 2,
  .CX 9 7,
  .CX 6 7,
  .CX 6 3,
  .CX 7 6,
  .CX 5 9,
  .CX 5 4,
  .CX 9 5,
  .CX 4 8,
  .CX 8 4,
  .CX 3 6,
  .CX 6 3,
  .CX 2 4,
  .CX 4 2,
  .CX 1 2,
  .CX 2 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 20 16,
  .CX 21 16,
  .CX 24 16,
  .CX 25 16,
  .CX 28 16,
  .CX 29 16,
  .CX 32 16,
  .CX 33 16,
  .CX 9 8,
  .CX 9 7,
  .CX 9 6,
  .CX 9 5,
  .CX 9 4,
  .CX 9 3,
  .CX 8 9,
  .CX 8 7,
  .CX 8 6,
  .CX 9 8,
  .CX 7 9,
  .CX 7 8,
  .CX 7 6,
  .CX 8 7,
  .CX 6 7,
  .CX 6 5,
  .CX 6 4,
  .CX 7 6,
  .CX 5 7,
  .CX 5 6,
  .CX 5 4,
  .CX 6 5,
  .CX 4 5,
  .CX 4 3,
  .CX 4 2,
  .CX 5 4,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 4 3,
  .CX 2 3,
  .CX 2 1,
  .CX 2 0,
  .CX 3 2,
  .CX 1 3,
  .CX 1 2,
  .CX 1 0,
  .CX 2 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 19 16,
  .CX 21 16,
  .CX 22 16,
  .CX 24 16,
  .CX 27 16,
  .CX 29 16,
  .CX 30 16,
  .CX 32 16,
  .CX 9 8,
  .CX 9 7,
  .CX 9 5,
  .CX 9 4,
  .CX 9 2,
  .CX 9 0,
  .CX 8 9,
  .CX 8 5,
  .CX 8 4,
  .CX 9 8,
  .CX 7 9,
  .CX 7 8,
  .CX 7 5,
  .CX 7 3,
  .CX 7 1,
  .CX 6 7,
  .CX 6 3,
  .CX 6 2,
  .CX 7 6,
  .CX 5 9,
  .CX 5 8,
  .CX 5 4,
  .CX 8 5,
  .CX 4 5,
  .CX 4 1,
  .CX 4 0,
  .CX 5 4,
  .CX 3 7,
  .CX 3 6,
  .CX 3 2,
  .CX 6 3,
  .CX 1 5,
  .CX 1 4,
  .CX 1 0,
  .CX 4 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 20 16,
  .CX 21 16,
  .CX 24 16,
  .CX 25 16,
  .CX 26 16,
  .CX 27 16,
  .CX 30 16,
  .CX 31 16,
  .CX 9 8,
  .CX 9 7,
  .CX 9 6,
  .CX 9 5,
  .CX 9 1,
  .CX 8 9,
  .CX 8 1,
  .CX 8 0,
  .CX 9 8,
  .CX 7 8,
  .CX 7 6,
  .CX 7 5,
  .CX 7 1,
  .CX 5 9,
  .CX 5 7,
  .CX 5 6,
  .CX 5 2,
  .CX 5 1,
  .CX 3 8,
  .CX 3 7,
  .CX 3 5,
  .CX 3 4,
  .CX 3 1,
  .CX 3 0,
  .CX 1 9,
  .CX 1 8,
  .CX 1 0,
  .CX 8 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 22 16,
  .CX 23 16,
  .CX 24 16,
  .CX 25 16,
  .CX 30 16,
  .CX 31 16,
  .CX 32 16,
  .CX 33 16,
  .CX 9 4,
  .CX 9 2,
  .CX 8 9,
  .CX 8 6,
  .CX 8 3,
  .CX 8 1,
  .CX 8 0,
  .CX 7 9,
  .CX 7 1,
  .CX 7 0,
  .CX 5 7,
  .CX 5 4,
  .CX 5 3,
  .CX 4 9,
  .CX 4 8,
  .CX 4 7,
  .CX 4 3,
  .CX 4 0,
  .CX 7 4,
  .CX 3 9,
  .CX 3 8,
  .CX 3 7,
  .CX 3 4,
  .CX 3 0,
  .CX 4 3,
  .CX 2 9,
  .CX 2 7,
  .CX 2 6,
  .CX 2 3,
  .CX 2 1,
  .CX 3 2,
  .CX 1 9,
  .CX 1 7,
  .CX 1 6,
  .CX 1 3,
  .CX 1 2,
  .CX 2 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 9 8,
  .CX 9 7,
  .CX 9 6,
  .CX 9 5,
  .CX 9 4,
  .CX 9 3,
  .CX 8 9,
  .CX 8 7,
  .CX 8 5,
  .CX 8 4,
  .CX 8 3,
  .CX 8 2,
  .CX 8 1,
  .CX 8 0,
  .CX 9 8,
  .CX 7 9,
  .CX 7 6,
  .CX 7 4,
  .CX 7 2,
  .CX 7 1,
  .CX 6 7,
  .CX 6 5,
  .CX 6 3,
  .CX 6 0,
  .CX 7 6,
  .CX 5 9,
  .CX 5 6,
  .CX 4 9,
  .CX 4 8,
  .CX 4 7,
  .CX 4 6,
  .CX 4 5,
  .CX 4 1,
  .CX 3 9,
  .CX 3 7,
  .CX 3 6,
  .CX 3 5,
  .CX 3 0,
  .CX 2 9,
  .CX 2 8,
  .CX 2 7,
  .CX 2 6,
  .CX 2 5,
  .CX 2 4,
  .CX 2 1,
  .CX 1 9,
  .CX 1 8,
  .CX 1 7,
  .CX 1 6,
  .CX 1 5,
  .CX 1 4,
  .CX 1 2,
  .CX 2 1,
  .CX 26 16,
  .CX 27 16,
  .CX 28 16,
  .CX 29 16,
  .CX 30 16,
  .CX 31 16,
  .CX 32 16,
  .CX 33 16
]

def order11_2047 : Program := [
  .CX 19 16,
  .CX 21 16,
  .CX 23 16,
  .CX 25 16,
  .CX 27 16,
  .CX 29 16,
  .CX 31 16,
  .CX 33 16,
  .CX 9 8,
  .CX 9 7,
  .CX 9 6,
  .CX 9 5,
  .CX 9 0,
  .CX 8 9,
  .CX 8 7,
  .CX 8 6,
  .CX 8 5,
  .CX 8 4,
  .CX 8 2,
  .CX 8 1,
  .CX 9 8,
  .CX 7 9,
  .CX 7 5,
  .CX 7 4,
  .CX 7 2,
  .CX 9 7,
  .CX 6 7,
  .CX 6 3,
  .CX 7 6,
  .CX 5 9,
  .CX 5 4,
  .CX 9 5,
  .CX 4 8,
  .CX 8 4,
  .CX 3 6,
  .CX 6 3,
  .CX 2 4,
  .CX 4 2,
  .CX 1 2,
  .CX 2 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 20 16,
  .CX 21 16,
  .CX 24 16,
  .CX 25 16,
  .CX 28 16,
  .CX 29 16,
  .CX 32 16,
  .CX 33 16,
  .CX 9 6,
  .CX 9 4,
  .CX 9 2,
  .CX 8 9,
  .CX 8 7,
  .CX 8 6,
  .CX 9 8,
  .CX 7 9,
  .CX 7 8,
  .CX 7 6,
  .CX 8 7,
  .CX 6 7,
  .CX 6 5,
  .CX 6 4,
  .CX 7 6,
  .CX 5 7,
  .CX 5 6,
  .CX 5 4,
  .CX 6 5,
  .CX 4 5,
  .CX 4 3,
  .CX 4 2,
  .CX 5 4,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 4 3,
  .CX 2 3,
  .CX 2 1,
  .CX 2 0,
  .CX 3 2,
  .CX 1 3,
  .CX 1 2,
  .CX 1 0,
  .CX 2 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 19 16,
  .CX 21 16,
  .CX 22 16,
  .CX 24 16,
  .CX 27 16,
  .CX 29 16,
  .CX 30 16,
  .CX 32 16,
  .CX 9 6,
  .CX 9 5,
  .CX 9 3,
  .CX 9 1,
  .CX 8 9,
  .CX 8 7,
  .CX 8 6,
  .CX 8 5,
  .CX 8 4,
  .CX 7 9,
  .CX 7 8,
  .CX 7 6,
  .CX 8 7,
  .CX 6 7,
  .CX 6 5,
  .CX 6 4,
  .CX 6 3,
  .CX 6 2,
  .CX 5 7,
  .CX 5 6,
  .CX 5 4,
  .CX 6 5,
  .CX 4 5,
  .CX 4 3,
  .CX 4 2,
  .CX 4 1,
  .CX 4 0,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 4 3,
  .CX 2 3,
  .CX 2 1,
  .CX 1 3,
  .CX 1 2,
  .CX 1 0,
  .CX 2 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 20 16,
  .CX 21 16,
  .CX 24 16,
  .CX 25 16,
  .CX 26 16,
  .CX 27 16,
  .CX 30 16,
  .CX 31 16,
  .CX 9 8,
  .CX 9 5,
  .CX 9 4,
  .CX 8 9,
  .CX 8 5,
  .CX 8 1,
  .CX 7 8,
  .CX 7 5,
  .CX 7 4,
  .CX 7 2,
  .CX 6 7,
  .CX 6 3,
  .CX 6 2,
  .CX 6 1,
  .CX 6 0,
  .CX 5 9,
  .CX 5 8,
  .CX 5 4,
  .CX 8 5,
  .CX 4 5,
  .CX 4 2,
  .CX 5 4,
  .CX 3 7,
  .CX 3 6,
  .CX 3 2,
  .CX 6 3,
  .CX 2 4,
  .CX 4 2,
  .CX 1 2,
  .CX 1 0,
  .CX 2 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 22 16,
  .CX 23 16,
  .CX 24 16,
  .CX 25 16,
  .CX 30 16,
  .CX 31 16,
  .CX 32 16,
  .CX 33 16,
  .CX 9 8,
  .CX 9 6,
  .CX 9 5,
  .CX 9 4,
  .CX 9 2,
  .CX 9 1,
  .CX 9 0,
  .CX 8 9,
  .CX 8 6,
  .CX 9 8,
  .CX 7 8,
  .CX 7 4,
  .CX 7 3,
  .CX 7 2,
  .CX 7 1,
  .CX 8 7,
  .CX 6 8,
  .CX 8 6,
  .CX 5 9,
  .CX 5 7,
  .CX 5 6,
  .CX 5 4,
  .CX 5 3,
  .CX 5 1,
  .CX 5 0,
  .CX 4 6,
  .CX 4 1,
  .CX 6 4,
  .CX 3 4,
  .CX 3 2,
  .CX 4 3,
  .CX 2 9,
  .CX 2 7,
  .CX 2 6,
  .CX 2 5,
  .CX 2 3,
  .CX 2 1,
  .CX 2 0,
  .CX 3 2,
  .CX 1 6,
  .CX 1 0,
  .CX 6 1,
  .CCX 16 0 1,
  .CCX 16 2 3,
  .CCX 16 4 5,
  .CCX 16 6 7,
  .CCX 16 8 9,
  .CX 9 7,
  .CX 9 5,
  .CX 9 4,
  .CX 8 9,
  .CX 8 6,
  .CX 8 5,
  .CX 8 4,
  .CX 9 8,
  .CX 7 8,
  .CX 7 6,
  .CX 8 7,
  .CX 6 9,
  .CX 6 5,
  .CX 6 4,
  .CX 9 6,
  .CX 5 9,
  .CX 5 4,
  .CX 9 5,
  .CX 3 9,
  .CX 3 8,
  .CX 3 7,
  .CX 3 6,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 3 0,
  .CX 2 3,
  .CX 3 2,
  .CX 1 2,
  .CX 1 0,
  .CX 2 1,
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
  if p == 1193 then return if mirror then order33_1193.reverse else order33_1193
  if p == 1571 then return if mirror then order33_1571.reverse else order33_1571
  if p == 2047 then return if mirror then order11_2047.reverse else order11_2047
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

def fieldPlace (n offset d q : Nat) : Wire :=
  if q < d then offset + q else if q < 18 then n + 16 + (q-8) else n + (q-18)

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
    renameProgram (fieldPlace n (offset+d*j) d) (fieldCore p mirror)
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

-- ==== begin SelectorReceiver (credited to spariev 59c20890 LeaveCutsCore150: DI7Affine + PBReceiver selector half; margin-16 port) ====
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.DI7Affine
open Arithmetic GateMirror DeadJoin
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

abbrev Expr := Bool × List Wire

def parity (qs : List Wire) (s : BasisState) : Bool :=
  qs.foldr (fun q b => s q ^^ b) false

def eval (e : Expr) (s : BasisState) : Bool := e.1 ^^ parity e.2 s

def toggleOld (q : Wire) : List Wire → List Wire
  | [] => [q]
  | x::xs => if q=x then xs else x::toggleOld q xs

theorem parity_toggleOld (q : Wire) (qs : List Wire) (s : BasisState) :
    parity (toggleOld q qs) s = (s q ^^ parity qs s) := by
  induction qs with
  | nil => simp [toggleOld,parity]
  | cons x xs ih =>
    by_cases h : q=x
    · subst x; simp [toggleOld,parity,Bool.xor_assoc]
    · rw [toggleOld,if_neg h]
      change (s x ^^ parity (toggleOld q xs) s) = (s q ^^ (s x ^^ parity xs s))
      rw [ih]
      cases s q <;> cases s x <;> cases parity xs s <;> rfl

/-- Normalize parity without permuting unaffected wires. -/
def toggle (q : Wire) (qs : List Wire) : List Wire :=
  if qs.contains q then toggleOld q qs else q::qs

theorem parity_toggle (q : Wire) (qs : List Wire) (s : BasisState) :
    parity (toggle q qs) s = (s q ^^ parity qs s) := by
  unfold toggle
  split
  · exact parity_toggleOld q qs s
  · rfl

def add (a b : Expr) : Expr :=
  (a.1 ^^ b.1, a.2.foldr toggle b.2)

theorem eval_add (a b : Expr) (s : BasisState) :
    eval (add a b) s = (eval a s ^^ eval b s) := by
  obtain ⟨ac,aq⟩ := a
  obtain ⟨bc,bq⟩ := b
  have h : parity (aq.foldr toggle bq) s = (parity aq s ^^ parity bq s) := by
    induction aq with
    | nil => simp [parity]
    | cons q qs ih =>
      change parity (toggle q (qs.foldr toggle bq)) s = (s q ^^ parity qs s ^^ parity bq s)
      rw [parity_toggle,ih,Bool.xor_assoc]
  simp only [add,eval,h]
  cases ac <;> cases bc <;> cases parity aq s <;> cases parity bq s <;> rfl

/-- Pull back one wire through a default mirror transition. Nonlinear targets
are rejected; erased targets pull back to zero. -/
def wirePull (g : Gate) (q : Wire) : Option Expr :=
  if q ≠ target g then some (false,[q]) else
  match g with
  | .x t => some (true,[t])
  | .cx c t => some (false,[t,c])
  | .pop _ _ _ => some (false,[])
  | _ => none

theorem wirePull_sound (g : Gate) (q : Wire) (e : Expr)
    (h : wirePull g q = some e) (s : State) :
    eval e s.basis = (transition g s).basis q := by
  unfold wirePull at h
  split_ifs at h with hq
  · cases h
    cases g <;> simp only [target] at hq <;> simp [eval,parity,transition,front,erase,run,measureAndCorrect,
      ECDSAAdd.correct,writeBit,Function.update_of_ne hq]
  · have eq : q=target g := by simpa using hq
    cases g <;> simp only [target] at eq <;> subst q
    all_goals try { simp at h }
    all_goals cases h
    all_goals simp [eval,parity,transition,front,erase,run,measureAndCorrect,
      ECDSAAdd.correct,writeBit,Bool.xor_comm]

def pullTerms (g : Gate) : List Wire → Option Expr
  | [] => some (false,[])
  | q::qs => do
      let a ← wirePull g q
      let b ← pullTerms g qs
      pure (add a b)

theorem pullTerms_sound (g : Gate) (qs : List Wire) (e : Expr)
    (h : pullTerms g qs = some e) (s : State) :
    eval e s.basis = parity qs (transition g s).basis := by
  induction qs generalizing e with
  | nil => simp [pullTerms] at h; subst e; rfl
  | cons q qs ih =>
    simp only [pullTerms] at h
    cases ha : wirePull g q with
    | none => simp [ha] at h
    | some a =>
      cases hb : pullTerms g qs with
      | none => simp [ha,hb] at h
      | some b =>
        simp [ha,hb] at h
        subst e
        rw [eval_add,wirePull_sound g q a ha s,ih b hb]
        rfl

def stepSlow (g : Gate) (e : Expr) : Option Expr := do
  let b ← pullTerms g e.2
  pure (add (e.1,[]) b)

theorem stepSlow_sound (g : Gate) (e out : Expr) (h : stepSlow g e = some out) (s : State) :
    eval out s.basis = eval e (transition g s).basis := by
  simp only [stepSlow] at h
  cases hb : pullTerms g e.2 with
  | none => simp [hb] at h
  | some b =>
    simp [hb] at h; subst out
    rw [eval_add,pullTerms_sound g e.2 b hb s]
    simp [eval,parity]

/-- An untouched affine support needs no normalization or symbolic substitution. -/
def step (g : Gate) (e : Expr) : Option Expr :=
  if e.2.contains (target g) then stepSlow g e else some e

theorem parity_same (qs : List Wire) (a b : BasisState) (h : ∀q∈qs,a q=b q) :
    parity qs a=parity qs b := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change (a q ^^ parity qs a)=(b q ^^ parity qs b)
    rw [h q List.mem_cons_self,ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem step_sound (g : Gate) (e out : Expr) (h : step g e = some out) (s : State) :
    eval out s.basis = eval e (transition g s).basis := by
  unfold step at h
  split at h
  · exact stepSlow_sound g e out h s
  · have absent : ¬target g ∈ e.2 := by simpa using ‹¬e.2.contains (target g) = true›
    cases h
    unfold eval
    congr 1
    apply parity_same
    intro q hq
    have neq : q ≠ target g := fun eq => absent (eq ▸ hq)
    cases g <;> simp only [target] at neq <;>
      simp [transition,front,erase,run,measureAndCorrect,ECDSAAdd.correct,
        writeBit,Function.update_of_ne neq]

def pull : List Gate → Expr → Option Expr
  | [], e => some e
  | g::gs, e => do
      let b ← pull gs e
      step g b

theorem pull_sound (gs : List Gate) (e out : Expr) (h : pull gs e = some out) (s : State) :
    eval out s.basis = eval e (run (GateMirror.forward gs) [] s).basis := by
  induction gs generalizing out s with
  | nil => simp [pull] at h; subst out; rfl
  | cons g gs ih =>
    simp only [pull] at h
    cases hb : pull gs e with
    | none => simp [hb] at h
    | some b =>
      simp only [hb,Option.bind_some] at h
      rw [step_sound g b out h s,ih b hb (transition g s)]
      change _ = eval e (run ([front g] ++ GateMirror.forward gs) [] s).basis
      rw [run_append,run_take,List.drop_nil]
      rfl

end ECDSAAdd.Entrant.StairPacket.DI7Affine
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.StairPacket.DI7Affine
open Arithmetic Partial GateMirror
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem update_nested (f : BasisState) (t : Wire) (a b : Bool) :
    Function.update (Function.update f t a) t b = Function.update f t b := by
  funext q
  by_cases h : q=t
  · subst q; simp
  · simp [Function.update_of_ne h]

def cxs (qs : List Wire) (t : Wire) : List Gate := qs.map (fun q => .cx q t)
def clear (c : Bool) (qs : List Wire) (t : Wire) : List Gate :=
  (if c then [Gate.x t] else []) ++ cxs qs t

theorem parity_congr (qs : List Wire) (a b : BasisState) (h : ∀ q∈qs,a q=b q) :
    parity qs a=parity qs b := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change (a q ^^ parity qs a) = (b q ^^ parity qs b)
    rw [h q List.mem_cons_self,ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem cxs_run (qs : List Wire) (t : Wire) (away : ∀ q∈qs,q≠t) (s : State) (m : List Bool) :
    run (GateMirror.forward (cxs qs t)) m s =
      ⟨s.phase,writeBit s.basis t (s.basis t ^^ parity qs s.basis)⟩ := by
  induction qs generalizing s m with
  | nil =>
    simp only [cxs,List.map_nil,GateMirror.forward,List.map_nil,run,parity,List.foldr_nil,Bool.xor_false]
    cases s
    simp [writeBit]
  | cons q qs ih =>
    have qt := away q List.mem_cons_self
    have tail := fun x hx => away x (List.mem_cons_of_mem _ hx)
    have p : parity qs (writeBit s.basis t (s.basis t ^^ s.basis q))=parity qs s.basis :=
      parity_congr qs _ _ (fun x hx => Function.update_of_ne (tail x hx) _ _)
    change run ([Instr.CX q t] ++ GateMirror.forward (cxs qs t)) m s = _
    rw [run_append,run_take]
    change run (GateMirror.forward (cxs qs t)) _ ⟨s.phase,writeBit s.basis t (s.basis t ^^ s.basis q)⟩ = _
    rw [ih tail]
    rw [p]
    simp only [writeBit,Function.update_self,update_nested]
    simp only [parity,List.foldr_cons,Bool.xor_assoc]

theorem clear_run (c : Bool) (qs : List Wire) (t : Wire) (away : ∀ q∈qs,q≠t) (s : State) (m : List Bool) :
    run (GateMirror.forward (clear c qs t)) m s =
      ⟨s.phase,writeBit s.basis t (s.basis t ^^ (c ^^ parity qs s.basis))⟩ := by
  cases c with
  | false => simpa [clear] using cxs_run qs t away s m
  | true =>
    have p : parity qs (writeBit s.basis t (!s.basis t))=parity qs s.basis :=
      parity_congr qs _ _ (fun x hx => Function.update_of_ne (away x hx) _ _)
    simp only [clear,if_true,forward_app,run_append,run_take]
    change run (GateMirror.forward (cxs qs t)) _ ⟨s.phase,writeBit s.basis t (!s.basis t)⟩ = _
    rw [cxs_run qs t away]
    rw [p]
    simp only [writeBit,Function.update_self,update_nested]
    congr 1
    cases s.basis t <;> cases parity qs s.basis <;> rfl

end ECDSAAdd.Entrant.StairPacket.DI7Affine
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror Challenge DI7Affine
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def selectorPop (s : Nat) : Gate := .pop 1560 (OB5.sig (s+14) (s+1048)) 1565
def selectorSources (s : Nat) : List Wire := [1559,1561,1562,1563,1564,Shadow7.e0P s+7]
def selectorExpr (s : Nat) : Expr := (false,1565::selectorSources s)
/-- The flag-cut kept-pass suffix that holds the selector pop (`leaveFix12`). -/
def selCut (s : Nat) : List Gate := FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 1 (afterPre7Rest s)
def selPre (s : Nat) : List Gate := (selCut s).takeWhile (fun g => g != selectorPop s)
def selPost (s : Nat) : List Gate := (selCut s).drop ((selPre s).length + 1)
def receiver (t : Wire) (c : Bool) (qs : List Wire) : List Gate :=
  (if c then [Gate.x t] else []) ++ qs.map (fun q => Gate.cx q t)
theorem clear_receiver (c : Bool) (qs : List Wire) (t : Wire) : clear c qs t = receiver t c qs := rfl

/-- `afterRest7` with the selector pop replaced by its XOR receiver. -/
def afterRest7S (s : Nat) : List Gate :=
  (selPre s ++ (receiver 1565 false (selectorSources s) ++ selPost s)) ++ (afterPre7Tail s ++
    ([.cx (topW7 s) 1559] ++ (chainMid7 s ++ ([.cx (topW7 s) 1559] ++ afterPost7 s))))

/-- Selector receiver (spariev 59c20890): `after7K` with the selector pop replaced by its XOR receiver. -/
def after7S (s : Nat) : List Gate := keptHead s ++ (KeptParity.placed s ++ afterRest7S s)

private theorem sel_split_first (gs : List Gate) (g : Gate) (present : g ∈ gs) :
    gs = gs.takeWhile (fun x => x != g) ++ g :: gs.drop ((gs.takeWhile (fun x => x != g)).length+1) := by
  induction gs with
  | nil => simp at present
  | cons x xs ih =>
    by_cases h : x=g
    · subst x; simp
    · have member : g∈xs := by simpa [h,Ne.symm h] using present
      simpa [List.takeWhile_cons,h,Ne.symm h,Nat.add_assoc] using congrArg (List.cons x) (ih member)

theorem sel_present : ∀ j : Fin 26, j.val ≤ 24 → selectorPop (start j) ∈ selCut (start j) := by decide +kernel

theorem selCut_shape (j : Fin 26) (hi : j.val ≤ 24) :
    selCut (start j) = selPre (start j) ++ (selectorPop (start j) :: selPost (start j)) :=
  sel_split_first _ _ (sel_present j hi)

def selTail (s : Nat) : List Gate := afterPre7Tail s ++
  ([.cx (topW7 s) 1559] ++ (chainMid7 s ++ ([.cx (topW7 s) 1559] ++ afterPost7 s)))

theorem after7K_sel (j : Fin 26) (hi : j.val ≤ 24) :
    after7K (start j) = (keptHead (start j) ++ (KeptParity.placed (start j) ++ selPre (start j))) ++
      (selectorPop (start j) :: (selPost (start j) ++ selTail (start j))) := by
  have e : afterRest7 (start j) = selCut (start j) ++ selTail (start j) := rfl
  rw [after7K, e, selCut_shape j hi]
  simp only [List.append_assoc, List.cons_append]

theorem after7S_sel (s : Nat) :
    after7S s = (keptHead s ++ (KeptParity.placed s ++ selPre s)) ++
      (receiver 1565 false (selectorSources s) ++ (selPost s ++ selTail s)) := by
  simp only [after7S, afterRest7S, selTail, List.append_assoc]
set_option linter.unnecessarySimpa false in
theorem recv_counts (a b : List Gate) (x y t : Wire) (qs : List Wire) (c : Bool) :
    toffoliCount (GateMirror.forward (a ++ (receiver t c qs ++ b))) =
      toffoliCount (GateMirror.forward (a ++ (Gate.pop x y t :: b))) ∧
    toffoliCount (GateMirror.inverse (a ++ (receiver t c qs ++ b))) + 1 =
      toffoliCount (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) ∧
    measurementCount (GateMirror.forward (a ++ (receiver t c qs ++ b))) + 1 =
      measurementCount (GateMirror.forward (a ++ (Gate.pop x y t :: b))) ∧
    measurementCount (GateMirror.inverse (a ++ (receiver t c qs ++ b))) =
      measurementCount (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) ∧
    gateSlots (GateMirror.forward (a ++ (receiver t c qs ++ b))) + 2 =
      gateSlots (GateMirror.forward (a ++ (Gate.pop x y t :: b))) + qs.length + c.toNat ∧
    gateSlots (GateMirror.inverse (a ++ (receiver t c qs ++ b))) + 1 =
      gateSlots (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) + qs.length + c.toNat := by
  have hm : (qs.map (fun q => Gate.cx q t)).countP isMake = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simpa [isMake] using ih
  have hp : (qs.map (fun q => Gate.cx q t)).countP isPop = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simpa [isPop] using ih
  have hc : (qs.map (fun q => Gate.cx q t)).countP isCCX = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simpa [isCCX] using ih
  cases c <;> simp [toffoli_forward,toffoli_inverse,meas_forward,meas_inverse,slots_forward,slots_inverse,
    receiver,List.countP_append,List.countP_cons,isMake,isPop,isCCX,hm,hp,hc,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]


theorem after7S_counts (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (after7S (start j))) = toffoliCount (GateMirror.forward (after7K (start j))) ∧
    toffoliCount (inverse (after7S (start j))) + 1 = toffoliCount (inverse (after7K (start j))) ∧
    measurementCount (GateMirror.forward (after7S (start j))) + 1 = measurementCount (GateMirror.forward (after7K (start j))) ∧
    measurementCount (inverse (after7S (start j))) = measurementCount (inverse (after7K (start j))) ∧
    gateSlots (GateMirror.forward (after7S (start j))) + 2 = gateSlots (GateMirror.forward (after7K (start j))) + 6 ∧
    gateSlots (inverse (after7S (start j))) + 1 = gateSlots (inverse (after7K (start j))) + 6 := by
  rw [after7S_sel, after7K_sel j hi]
  have c := recv_counts (keptHead (start j) ++ (KeptParity.placed (start j) ++ selPre (start j)))
    (selPost (start j) ++ selTail (start j)) 1560 (OB5.sig (start j+14) (start j+1048)) 1565
    (selectorSources (start j)) false
  simpa only [selectorPop, selectorSources, List.length_cons, List.length_nil, Bool.toNat_false, Nat.add_zero] using c

theorem recv_wiresCovered : ∀ j : Fin 26, j.val ≤ 24 → (receiver 1565 false (selectorSources (start j))).all (fun g =>
    g.wires.all (fun q => ((after7K (start j)).flatMap Gate.wires).contains q)) = true := by decide +kernel

theorem recv_physical : ∀ j : Fin 26, j.val ≤ 24 →
    (receiver 1565 false (selectorSources (start j))).all proper = true := by decide +kernel

theorem after7S_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val ≤ 24)
    (h : AllW P (afterAll (start j))) : AllW P (after7S (start j)) := by
  have old := after7K_allW j hi h
  have whole := old
  rw [after7K_sel j hi, allW_append_iff] at old
  have recv : AllW P (receiver 1565 false (selectorSources (start j))) := by
    intro g hg q hq
    have inc := List.all_eq_true.mp (List.all_eq_true.mp (recv_wiresCovered j hi) g hg) q hq
    obtain ⟨k, hk, hw⟩ := List.mem_flatMap.mp (List.contains_iff_mem.mp inc)
    exact whole k hk q hw
  rw [after7S_sel]
  exact allW_append_iff.mpr ⟨old.1, allW_append_iff.mpr ⟨recv, fun g hg => old.2 g (List.mem_cons_of_mem _ hg)⟩⟩

theorem after7S_proper (j : Fin 26) (hi : j.val ≤ 24)
    (h : Proper (afterAll (start j))) : Proper (after7S (start j)) := by
  have keep : (after7K (start j)).all proper = true := List.all_eq_true.mpr (after7K_proper j hi h)
  rw [after7K_sel j hi] at keep
  simp only [List.all_append, List.all_cons, Bool.and_eq_true] at keep
  have all : (after7S (start j)).all proper = true := by
    rw [after7S_sel]
    simp only [List.all_append, Bool.and_eq_true]
    exact ⟨keep.1, recv_physical j hi, keep.2.2⟩
  intro g hg
  exact List.all_eq_true.mp all g hg

end ECDSAAdd.Entrant.StairPacket.DeadJoin
end
-- ==== end SelectorReceiver defs ====

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
def afterPart (s : Nat) : List GateMirror.Gate := DeadJoin.after7S s
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

def params : WindowFold.Pieces Program :=
  { Shadow7.params with leave := leave, leaveInv := unleave, unrouted := TickCut.Tail.selected }

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
  p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 19 ∨ p = 21 ∨ p = 25 ∨ p = 31 ∨ p = 37 ∨ p = 41 ∨ p = 47 ∨ p = 55 ∨ p = 59 ∨ p = 61 ∨ p = 67 ∨ p = 73 ∨ p = 87 ∨ p = 91 ∨ p = 97 ∨ p = 103 ∨ p = 109 ∨ p = 115 ∨ p = 117 ∨ p = 257 ∨ p = 313 ∨ p = 471 ∨ p = 1193 ∨ p = 1571 ∨ p = 2047

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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases mir <;> decide +kernel

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

def fieldScope (d q : Nat) : Prop := q < d ∨ (if d ≤ 8 then 8 else 16) ≤ q ∧ q < 34

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

theorem field_place_maps {n off d : Nat} (small : d ≤ 10) (endp : off+d ≤ n) :
    (∀ q, fieldScope d q → fieldPlace n off d q < n+26) ∧
    (∀ a, fieldScope d a → ∀ b, fieldScope d b → fieldPlace n off d a = fieldPlace n off d b → a = b) := by
  constructor
  · intro q hq
    unfold fieldScope at hq
    simp only [fieldPlace]
    split_ifs at hq ⊢ <;> (try unfold Wire at *) <;> omega
  · intro a ha b hb he
    unfold fieldScope at ha hb
    simp only [fieldPlace] at he
    split_ifs at ha hb he <;> (try unfold Wire at *) <;> omega

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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases mir <;> decide +kernel

theorem used_degree (p : Nat) (hp : UsedField p) : 0 < fieldDegree p ∧ fieldDegree p ≤ 10 := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

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
    have bounds := field_place_maps (n := n) (off := off+fieldDegree p*j) (d := fieldDegree p) small (by omega)
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

private theorem field_tested_1193 : ∀ mir : Bool, fieldTest 1193 mir = true := by decide +kernel

private theorem field_tested_1571 : ∀ mir : Bool, fieldTest 1571 mir = true := by decide +kernel

private theorem field_tested_2047 : ∀ mir : Bool, fieldTest 2047 mir = true := by decide +kernel

theorem field_tested (p : Nat) (hp : UsedField p) (mir : Bool) : fieldTest p mir = true := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · cases mir <;> decide +kernel
  · exact field_tested_257 mir
  · exact field_tested_313 mir
  · exact field_tested_471 mir
  · exact field_tested_1193 mir
  · exact field_tested_1571 mir
  · exact field_tested_2047 mir

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

theorem fieldPool_iff {d q : Nat} (sd : d ≤ 10) : q ∈ fieldPool d ↔ fieldScope d q := by
  simp only [fieldPool,Finset.mem_filter,Finset.mem_range]
  unfold fieldScope
  split_ifs <;> omega

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
    run (renameProgram (fieldPlace r.size off (fieldDegree p)) (fieldCore p mir)) m (frame r x dim slot ph) =
      frame (scalarRows r p mir slot off) x dim slot ph := by
  let d := fieldDegree p
  let f := fieldPlace r.size off d
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
    · have inside : off+q < r.size := by omega
      simpa [frame,Matrix.basis,f,fieldPlace,left,inside,data] using val q left
    · obtain hq := hq.resolve_left left
      have hq34 : q < 34 := hq.2
      by_cases mid : q < 18
      · simp [frame,Matrix.basis,f,fieldPlace,inputColumn,left,flags,mid,
          show ¬18≤q by omega,show ¬r.size+16+(q-8)<r.size by omega,
          show ¬r.size+16+(q-8)<r.size+16 by omega]
      · have inside : r.size+(q-18) < r.size+16 := by omega
        simp [frame,Matrix.basis,f,fieldPlace,inputColumn,left,flags,mid,
          show 18≤q by omega,hq34,inside,tags]
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
    · have inside : off+a < r.size := by omega
      have inSlice : off ≤ off+a ∧ off+a < off+fieldDegree p := ⟨by omega, Nat.add_lt_add_left left _⟩
      rw [output_bit p mir a left row dim x _ data tags val]
      simp [frame,Matrix.basis,f,fieldPlace,left,inside,scalar_read inside,inSlice,data]
    · rw [outputColumn,if_neg left]
      rw [point a shape]
      have edge : r.size ≤ f a := by
        obtain ⟨a8,_⟩ := shape.resolve_left left
        unfold f fieldPlace
        simp only [left,if_false]
        split_ifs at a8 ⊢ <;> (try unfold Wire at *) <;> omega
      simp only [frame,Matrix.basis,scalarRows_size,if_neg (Nat.not_lt_of_ge edge)]
  · rw [run_rename_pool_outside f (fieldPool d) (fieldCore p mir) sub m _ q inPool]
    by_cases inside : q < r.size
    · have outsideSlice : ¬(off ≤ q ∧ q < off+fieldDegree p) := by
        rintro ⟨lower,upper⟩
        apply inPool
        have sq : q-off < d := (Nat.sub_lt_iff_lt_add lower).mpr (Nat.add_comm off d ▸ upper)
        refine Finset.mem_image.mpr ⟨q-off,(fieldPool_iff sd).mpr (Or.inl sq),?_⟩
        simpa only [f,fieldPlace,if_pos sq] using Nat.add_sub_of_le lower
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
  have scalar := run_parts (List.range m) (fun j => renameProgram (fieldPlace r.size (off+d*j) d) (fieldCore p mir))
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
      1840700269, 920350134, 490370281, 659463482,
      1318926964, 2059990417, 257498802, 514997604,
      1029995208, 1299749617, 452015586, 904031172,
      649874808, 1662567985, 623462994, 692736660,
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
      5584820966481, 11169641932962, 18988391286036, 37976782572072,
      43218598786281, 45989021785402, 21609299393140, 41556344986809,
      12743945795954, 55962544582236, 67501766014353, 8437720751794,
      16875441503588, 33750883007176, 42590195456753, 14811646735842,
      29623293471684, 21295097728376, 54479027750449, 20429635406418,
      22699594896020, 27239513875224, 39659879301697, 8951014425730,
      17902028851460, 4957484912712, 9914969825424, 19829939650848,
      8806250292225, 17612500584450, 35225001168900, 8867869525000,
      17735739050000, 44257586033696, 18146427889728, 45081246397568,
      19793748617472, 39587497234944]
  | 54 => #[
      18014398509481983, 12009599006321322, 3602879701896396, 2401919801264264,
      13775716507250928, 9183811004833952, 211934100111552, 141289400074368,
      280379743338240, 186919828892160, 224303794670592, 149535863113728,
      263886817259520, 175924544839680, 211109453807616, 140739635871744,
      4861028169225297, 9722056338450594, 5718856669676820, 11437713339353640,
      5531980644644073, 14893794043272506, 11773189577063028, 14326411413052601,
      10638424316623218, 16170404961267292, 14141250601547153, 6271255952563890,
      12542511905127780, 7070625300773576, 8486839496776433, 16973678993552866,
      15932959477623748, 13250619003129208, 1743328888014385, 2905548146690642,
      5229986664043156, 9878863698748184, 2291459692986945, 4582919385973890,
      9165838771947780, 2538232275308616, 5076464550617232, 10152929101234464,
      6553099458814977, 13106198917629954, 8197999325777924, 12675241821504520,
      7336085133527056, 9966250515084320, 1918102520686656, 7574536873407616,
      15149073746815232, 12283748984148480]
  | 61 => #[
      2305843009213693951, 768614336404564650, 922337203685477580, 614891469123651720,
      1220740416642543856, 45212608023797920, 54255129628557504, 36170086419038336,
      1464027307437266001, 622211605660838050, 366006826859316500, 732013653718633000,
      708093522514441449, 1906405637538880826, 1506968265864067700, 1833780660870732985,
      1361718312527772018, 2069811835042213468, 2211897868758349201, 276487233594793650,
      552974467189587300, 1105948934379174600, 1395595524726889201, 485348040240084450,
      970696080480168900, 697797762363444600, 1785168781326730801, 669438292997524050,
      743820325552804500, 892584390663365400, 1685444194648706337, 1065045380083718722,
      787141276634511780, 1574282553269023560, 842722097324353168, 1173227362809315905,
      40611716404937858, 81223432809875716, 1299574924958011464, 293306840702328976,
      586613681404657952, 1934093739973387265, 1562344470733080578, 818845932252467204,
      895380768786121736, 1790761537572243472, 820614183441773600, 1641228366883547200,
      1682913598255232128, 1059984187296770304, 2119968374593540608, 1673922907243117569,
      1823685188398842882, 1341527367583991812, 377211725954289672, 754423451908579344,
      273162944251247648, 546325888502495296, 1092651777004990592, 2185303554009981184,
      836961453621558784]
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
      166807837940020476324, 333615675880040952648, 76935541401376253584, 10396599399664091713,
      20793198799328183426, 41586397598656366852, 75086551219796217928, 150173102439592435856,
      300346204879184871712, 87250285080880063489, 174500570161760126978, 349001140323520253956,
      26259653870136755208, 52519307740273510416, 19267358257151325216, 38534716514302650432,
      10906285635110007936, 21812571270220015872, 43625142540440031744, 144636189478492142593,
      156315166805716337666, 312630333611432675332, 34964856864159698952, 69929713728319397904,
      4884848962678635552, 9769697925357271104, 19539395850714542208, 39078791701429084416,
      72318094739246071296]
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
      1330764723157003739280, 2661529446314007478560, 364902440192748714241, 729804880385497428482,
      1459609760770994856964, 2610810666086822949128, 4885542149500071648016, 9490345770763384016672,
      18980691541526768033344, 37961383083053536066688, 485960121773281463041, 865274190725617409282,
      1319528729227806961924, 2639057458455613923848, 4804837028446383148816, 9609674056892766297632,
      19105784479159985207104, 38021911923843802441088, 87250285080880063489, 174500570161760126978,
      349001140323520253956, 616555464228842406920, 1233110928457684813840, 2380450599691973932064,
      4760901199383947864128, 9455639251374400435328, 18911278502748800870656, 37822557005497601741312]
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
      9142866413275825882429697, 18285732826551651764859394, 17228652539269236734419972, 13376352690152922068136200,
      2044947862749186803964688, 5978561580117994934128416, 11957123160235989868256832, 4571433206637912941214848,
      17605069498423118236722177, 15867325883012169678145538, 12391838652190272560992260, 12165432615336434912887816,
      4988052116838803030476816, 8238187596724353226617888, 16476375193448706453235776, 7036336965761406478414976,
      14072673931522812956829952, 8802534749211559118361088, 7178141690151339216960513, 17000675653497528485643266,
      14658538193160990175987716, 9974263272487913556676616, 605713431141760318054416, 5971437302437629051354144,
      11942874604875258102708288, 4542936095916449410117760, 9085872191832898820235520, 13260477401992703006129664]
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
      174425993793634794114945096, 348851987587269588229890192, 697703975174539176459780384, 47828492640943959473027329,
      95656985281887918946054658, 191313970563775837892109316, 342204175625332057588216072, 640357780619273391048825616,
      1243918600865498269833252640, 11957123160235989868256832, 23914246320471979736513664, 63695765081067547923794689,
      113413218726788125069532418, 172953269597347114113364228, 345906539194694228226728456, 629779598992524332081647376,
      1259559197985048664163294752, 28353304681697031267383104, 31847882540533773961897344, 1758458249743489129813615617,
      1041036420916217709828982786, 2082072841832435419657965572, 263622003095179303251772424, 527244006190358606503544848,
      2097262003890803567118890016, 1718643929210846584439531584, 2076717340146006553575388288, 1677554601721252557352528128,
      879229124871744564906807808, 1999487892415060219132738561, 810056013320694267092894722, 1620112026641388534185789444,
      764343974712016518573330440, 1528687949424033037146660880, 2346451824076359711282510880, 2217023569581958872766773312,
      1958167060593157195735298176, 1440454042615553841672347904, 2237683985492910384465493504]
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
      498286819449691507290701194400, 564548486406774349313473673473, 495271672699433997878595744258, 356718045284753295008839885828,
      485614699575494399818044911880, 268035406266261412769259658000, 149796723315111131257728159520, 299593446630222262515456319040,
      599186893260444525030912638080, 115648941863998474420533044225, 231297883727996948841066088450, 462595767455993897682132176900,
      225568709153034389334892381192, 451137418306068778669784762384, 165505347189560999853803287584, 331010694379121999707606575168,
      93684280247264146896110580864, 187368560494528293792221161728, 374737120989056587584442323456, 608590107142251394919703608321,
      75086458370443510761040348162, 150172916740887021522080696324, 300345833481774043044161392648, 600691666963548086088322785296,
      41960533081208528508054486048, 83921066162417057016108972096, 167842132324834114032217944192, 335684264649668228064435888384,
      621207703628183047834027605504, 317377104356115079759189249025, 317686740555486899349198214146, 318306012954230538529216144388,
      319544557751717816889252004872, 322021647346692373609323725840, 326975826536641487049467167776, 336884184916539713929754051648,
      356700901676336167690327819392, 396334335195929075211475354880, 475601202235114890253770425856]
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
      26170851101486026353480324240020, 31405021321783231624176389088024, 33346065089998851755679624271937, 59353992144561016586213335705794,
      37578345874515351476637666267524, 75156691749030702953275332535048, 69183745083454724210761659926032, 57237851752302766725734314708000,
      41279268077882068964589317685825, 1428897741157456233389630227586, 2857795482314912466779260455172, 45724727717038599468468167282760,
      10319817019470517241147329421456, 20639634038941034482294658842912, 66914404850767311892409969068353, 37216247832752470425323618261954,
      18374830136167139351673994903236, 36749660272334278703347989806472, 16728601212691827973102492267088, 33457202425383655946204984534176,
      57636489419645635752800172719937, 70476738385473365779034285228482, 59823838356340049862279565312900, 64755391140767299142793988421704,
      14409122354911408938200043179984, 28818244709822817876400086359968, 9060390475229210101854465601473, 18120780950458420203708931202946,
      36241561900916840407417862405892, 72483123801833680814835724811784, 63836609189060679933882444479504, 45095014444917945898821735372768,
      6268976187433806656048638097665, 12537952374867613312097276195330, 25075904749735226624194552390660, 44853385707563523452202657100040,
      2803336606722720215762666068752, 783622023429225832006079762208, 1567244046858451664012159524416, 3134488093716903328024319048832,
      749474241978113175168884646913, 1498948483956226350337769293826, 2997896967912452700675538587652, 5296171110065951995321705202696,
      10592342220131903990643410405392, 20447914950841231423801054573600, 40895829901682462847602109147200, 93684280247264146896110580864,
      187368560494528293792221161728, 374737120989056587584442323456, 1242415407256366095668055211009, 1342737058598672912257743553538,
      2685474117197345824515487107076, 5370948234394691649030974214152, 10741896468789383298061948428304, 20324370136732878952455305772064,
      40648740273465757904910611544128, 167842132324834114032217944192, 335684264649668228064435888384, 621207703628183047834027605504,
      951202404470229780507540851713, 1585337340783716300845901419522, 2853607213410689341522622555140, 5390146958664635422876064826376,
      10463226449172527585582949368848, 20609385430188311910996718453792, 40901703392219880561824256623680, 356700901676336167690327819392,
      396334335195929075211475354880, 475601202235114890253770425856]
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
      4851404057602561519194345291921480, 2204909359549291814724503182069712, 4409818719098583629449006364139424, 1304343190821140713788672720402689,
      2608686381642281427577345440805378, 5217372763284562855154690881610756, 1342927600341270430584826739405064, 3978155618922450123309423918127888,
      9249562401288590939151952666185504, 8114531085507526621242912673930816, 5844468453945397985424832689421440, 3902571375221826407039339864476417,
      6505236370573492108792234164739330, 1320743545586370388073690958459140, 2641487091172740776147381916918280, 9169065974035096499182974261038864,
      7953538231000537741304955863637536, 9414754380445614469993803035014976, 7143582546145740832050166261458304, 5842083440093659195271977255019521,
      1299573163117663133482961851598850, 2599146326235326266965923703197700, 654333278426919405561633746355208, 1308666556853838811123267492710416,
      8457930310069936127785857589556256, 6531266903070216998510722520672320, 8518705717813948842204741650707584, 6652817718558242427348490642974976,
      2921041720046829597635988627509760, 9736799025160058169590348672498689, 650379844375452126478569784706050, 1300759688750904252957139569412100,
      2601519377501808505914279138824200, 5203038755003617011828558277648400, 9755880979889534682447135923059744, 9127168242709414107833279187679296,
      7869742768349172958605565716918400, 5354891819628690660150138775396608, 10060696371114856713325670665469440, 1948062524355030590479443664309249,
      3246770873925050984132406107182082, 5844187573065091771438330992927748, 654427254275518088989188105978888, 659500333766025981151894990521360,
      669646492747041765477308759606304, 689938810709073334128136297776192, 730523446633136471429791374115968, 811692718481262746033101526795520,
      974031262177515295239721832154624]
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
      857566448893494111550843264696996500, 1029079738672192933861011917636395800, 897570535845883718452269443533051969, 1274200325293542497048952539123230914,
      1219172654802169121194098017966117252, 1109117313819422369484388975651889928, 889006631853928866064970891023435280, 448785267922941859226134721766525984,
      187288484728990103422845613190185537, 374576969457980206845691226380371074, 749153938915960413691382452760742148, 23411060591123762927855701648773192,
      46822121182247525855711403297546384, 93644242364495051711422806595092768, 760738404180203014891610122199812417, 952904819427388228987467189035293634,
      1316427887745544184335224071462485700, 1303627779706172495766641082644626824, 522491599991279721948854295620039248, 1044983199982559443897708591240078496,
      756510385067212345767289484135972673, 928599188393558945374084198159040962, 527970381002202017844361336037737348, 472158121325737048086939014921730120,
      189127596266803086441822371033993168, 378255192533606172883644742067986336, 108803905504462789364154910363791297, 217607811008925578728309820727582594,
      435215622017851157456619641455165188, 870431244035702314913239282910330376, 411634492286488756922671505540316176, 719015950644689331133980985322067936,
      517604092750470799792481544281166785, 856413209054072783738037862506935362, 219679325038994033096603248941726532, 439358650077988066193206497883453064,
      878717300155976132386412995766906128, 258802046375235399896240772140583392, 821687246839323906021607092737177857, 314146497893731939139407125194011138,
      628292995787463878278814250388022276, 562110988322102654311878430295175432, 367438935716360384120444166963534608, 102710905854915488252700886592147232,
      205421811709830976505401773184294464, 410843623419661953010803546368588928, 1094284911667535628398443569000696577, 619196265677683152275390801012710658,
      312858555057676028099903470711664900, 625717110115352056199806941423329800, 185707159164219235869219849454522128, 371414318328438471738439698909044256,
      487106065365649756294799465323263808, 547142455833767814199221784500348288, 483533394425297801020077639543268353, 967066788850595602040155279086536706,
      604905581916275331176503497892728836, 935267767814695892541050973005972488, 541307539844475912178294885731600400, 735379490504945804122055343680369696,
      141530985224975735340303627080394816, 558902172722505677466437352548037760, 1117804345445011354932874705096075520, 906380695105106836961942349911806464,
      1224734263922309723245726489710001153, 312188191356465109838308349537911810, 624376382712930219676616699075823620, 1248752765425860439353233398151647240,
      1168277535066805005802659736022949904, 217447755321282639823666989091863584, 434895510642565279647333978183727168, 869791021285130559294667956367454336,
      410354046785345245685528852454564096, 612367131961154861622863244855000576, 1948062524355030590479443664309249, 3246770873925050984132406107182082,
      5844187573065091771438330992927748, 11039020971345173346050180764419080, 21428687767905336495273880307401744, 42208021361025662793721279393367072,
      83766688547266315390616077565297728, 166884022919747620584405673909159040, 333118691664710230971984866596881664, 665588029154635451747143251972326912]
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
      197583309825061043301314288186187993748, 32930551637510173883552381364364665624, 168380298004745283704331959038856468545, 175403067773117521847447677435848370370,
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
      180960714585912777950786980047581384464, 21639062250887092438199352663394557472, 213163585390952189420903929110178395968, 255758917646537615411730177358326506880,
      312852112403880527933414736805424243713, 285421857886822592403454866179080275970, 230561348852706721343535124926392340484, 236208623021744805396514900642626962440,
      132134879122551147329655193853485713424, 60550639300826160084793373056295875616, 121101278601652320169586746112591751232, 124177105780719681857520493958620083328,
      248354211561439363715040987917240166656, 156426056201940263966707368402712121856, 123513709876134570030395976035501702145, 304705399226102200004810125153736819714,
      269128431531265936546245642875705427972, 197974496141593409629116678319642644488, 55666625362248355794858749207517077520, 20155867692095020733380772893297032224,
      40311735384190041466761545786594064448, 80623470768380082933523091573188128896, 161246941536760165867046183146376257792, 231898038398536516746885291733634956800]
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
  | 31 => 2129917273750201232991211575846355010352118899165478610449818878348517044510003826965075644763265078148572651909240140854801888604854550992569324044045825750565988086242202115456114212965290991073208958104977242667547986434596779022612250648266567767430958948155645128552884511382990138546233188059544412823976300561786153659888213157868845088933840722810352373002937654852545956256042778481602228885971275736835716679977321183366053645780420470121343628080005654461904860464248611440238139027176950650618818375286374045156522925335933126632401435191117078295494312335528830768908101029353667313321783250451314715207546095460758383476705781488880989883223044061260506187790982424052542718419826063189858661825423169367432515572970811735634356304775855773561646161280203780446137561826270910918926890125501850432831999418695619840352430622459128573593717131460239220252754406645418364379405928501967678633507234919951236564508514063041419203877936694248104574078916910598952436160763325586720792971026583254299544320010476466383601517778872508263977044109158541836125195009545017777267708194065946259574939677586558525317661092086664456821236910928294345106877461181153904485682404132836742515178942749143059155297413258551874805446408212781323147455199590562059063208284155669433416675542561061580144063283199
  | 39 => 66709502961343665485124629215248935765392639528500155646844127244492998350538572766046356857449067304872836238252796773138780444129786071689512818182131730933027768326575717269188621301515539964451105564613762196265727761116008466388638844610652912095229049894816787100453988072199025224635190920271817965253908266454425956623213699094116827454881383524482795434215401303370001923461081188238067165977429579838980049692184386216070054445924665411315282288931951119430226325609872634361487983629896776944966596226052857852297149947607638252656048616905674150432145009784855058024737558049313927680837779943272135680842902899272895311965364061287496389444622402285254002395268421458080915869182622387087835953513079581440750422765493227420598711222435061402935139260829378505752913205148107613297985075314810529899357475985827791215947090739791133167575878440801961682506197352627700737088808540162643009176304564533907131704220356718303705246923406308633642034531531966395780966950028480965489876741436269149118039485975410301162025405067219542573063806828999741914559122128844968705984084575829060474439974672896389825889487664478457602967102661653289979711831184612033143767560713417822643184935694167742147036357069083785865218780521493865983748253843904250226257710581090901366250025921421982518278778973807901083252753825208320083307899792763600360739561486929782498720295138623687607108683610254709761259573715035541188014669388924044729055493382947979803101499677801807763045685207155091819040359435503312626768628445242073992308326690524739867761285658189025004005173224200865734725415787227338361235149174061223242862806317638852034208991488652607487
  | 46 => 187038042515221429053042567994885150591713294654494187608319226451455151973786040490372749454501799132717580337655078948008897637213055935624271979905951101722741793436432278441285582186929839606101701557845782429752702939842441712435107976861128285718819932926663421657059367528864170563417071994566083399092882895855077502914844318429207282049380719459970357915116478166485629758535920263743419311341516881528967306508597225931785234807276871695802670201215425427557576550305057037673630743688396024477584472437347532228638975803379324309734128701429618026849192932542812335813399302794764577850786148598441962400372803138932913271684377978975779421473267370132784628903533337162039866976966896969162550564921691915537307835217759168006455817145266057750911345946134533260828514341399988363828867250586830850163195155840337680664121666969560925358475009258266547014001747495459805094160777878553018765770546913966900840508641923668934820422131100253723873633987938023727383918932799569576301625617878398304862524775763786419017732128112560869008339938965211953102640297683833488651531975279611314538710953958969964701072790037406730443327976151543724659854693389687593712109756966466063449316688219877787029103312757636441670097631139767093757094352312504868532332922348820617438372736039643229599343508694139038174387182867370244640179826675464869171277044507100606589479683008190044295626487351131091346812070713127793638489847787813481456183399650185901954808436417043933810963546318751324866004062887100153891161862431542456598138668806713384975927073597298184268766199621364733439620987546553975220489124922911136992516665914390205110478468206088543318209789428198172219283302476707219686087484233009940902369076361273809813604643367947461594032304924640082002902743527058685746658928985013349804092107808648364525285326662463102736743986380919148324307279665954253284194809291264038667416811487906178375388873002828591096039638295624612511991079042505768959
  | 54 => 3550241044996737118679120696768099697497120831051386119832679213472614827891648698753117670697451930075070512483872645739319801955306587140552941608883249910344418124104183809954764809639499054711765793546853812944557299767699813106571933744418934529954337549816128184933315318010920627576416216407143380461792156081496806644469616740151013793428875939905873879736682022609466995101252474960704748257931239705836186972194499998337934304845812944770586071260437604942691540660663817335271463871103736814618419687301539600560514082231179004115573891132388415915299436054855949152127388999036175139155819860193121592042765893088105674896827036133126029131365765472423270169093419735929166434082994294789322165310924461246039190684336326306259610801429515742912537903403494565379972644639019263548448016448434472162791427104454651677014614833796312403881374157093443637632376995383852353876256445586609514192375916229371828619722919118449573827607534916210550813355935447666134095436168728243227169960181839349244023806307857380189122960726603778585531014311003582109499535473947621115815069325311208163514899481494383070730312309101910550501454228967231616956801960086197072923217373797626115768205811834824756539519823187028863625231373442940461317610593665307906221149609984788983497244177047299200144082834875170236379600781658305942398699508338526059769957678729893657221630572532961729421895997091203951468915044238249885547823589265606365133394562342130237028401841881342344465215344550253701667225714105248253833608138179720077167744600824381383324110370185190715368182290259454995218224710787458759044292467614375949194382550510103323962465382254330204648213638579912631723163495678497807550911640911536425122582902152283104655292614897983266561696603218909820458637841203061752396202162768864867889583757031042633058583719226919950204000459886593006615391801787678215708125161875079211456451720000800425021299897471443019763593929306146141909403679467193855769419775613203945095122205737341222824349666126476201146431727230813511856642923090659188363651743860081849164433482575580226363271282199112610730794700890579057453297918906496873589214955337693856138762579066047300195530724641386673942667726249638315414716634415559242058994444368791145684764923957440284394780129967078493484972627954155018369630207
  | 61 => 663541352632638747459462944642133967906903337229129021617806612579188737558113100855514445316399491014851512910852425056131725008637783236864841140616250584193952888295782939730553129007364192689048331372643790148638992942030876382480505091283209327556314072609151629075387938301347518030122179351988808389482314071947831052926631270137376845131176533409340689363889168865559013860125427493267023113895401581362421100595979783432287392681629581339843362988329171091026115070453047468855450330899614152126518992817939199762090240286780234360676866553859822002177564085774172886050736163246919409445180844601507800525853690770801860607503252059527528222344468249555437686642896606734021960703286771241624087388783628803975791442597090476907176594168949018303429609338561903689425781708881231946446209342327351347667351954093466563682729854892290976972667783605520407215416693430939804195681406489539218834064592032715540557481601811108630318231496866429108069442159549012883810328974122119812882425129235083056339952912241479461987600145954109270254158343227024413064348301909746565506168366813311759287355988342081942734968477888839696554196549298716572752981390520041891847439738941846176650394846499005484552871046555919100107221737002106355911704005476206756389007328675459448501828432612409956411741596828496757502307069884895214666639885990661330977044554534997731036898278069235999148733521278691718972617859531755058760097823788983801252357849089582555688846356362286514152466051884729941423309723441566208120013266503212620865631789594006751932506973082791071410675179319704578286307310913798216004299201638375828840840685916430860977728079860424857583126726465987149280810859718362994299536580914602713501933621440900925681551354541267682697345412234876950869924422343057325074363768459949542817472020158402763051631290115129888189594627203445529718188530444276561714675649249102184141397361125043821626493212861756338088833232342821272025941874382682578822659503979641684775960714302236553590900436245562028297419246621607096187877182426160934475280884401225869088415593232546032869503828682915669479208914409678940743377981672760684826630799333457502403715453967569997794971879333860980748916769266630600593412407160419738821880105913817999053646269149028425864967537144742339032935822566525831910775700782619132976705372182217372742478482004391278960279975453536841356215262046414347290447974329423300818345094810323480812315369863967204978776827706525341228299484804352335888407970974545726904062986900671153008350616880260872624641554100012574616417096427081969213081425032520335201863583286822362608041983
  | 69 => 3507232182504241794195060073185424864289493664777420326454375509602643020341968490552585659783713499334536264880932856708222291827945865933209702133632614442122317766509032054466358551308324988279352375450652310655286831662577016849917513946956391620319888399140860805721880384328069290879526988193929398044178892945956005267852455290034054997808426963884310482951722619407475085507680364563509080374739830284486833074906492007109721506087332422993078813538726704395331351446863520340487599620694265690802296695534724386267616877412458135094403445866207835430813368620936288136010453285099751956709202932862085786598851836059632030941111235894362505789175445856139391457256430517111131540653268791561096726249169710806893973801859057162673925930955546613045260991739131485196048344411672249490181467858552041773072813814988379532207323294616677378464373954007596882598446752393489777443922167781744288814068100388662976163575707579610132030450925439759964575072379880301612349012655228677294730421185942579389059016024005422883334167247998293182087851815881615951767841431399776941775724763225514586803682512670039366055059612617519381311788089655807406354252617963059601212577286835349735196933634757194878212025150339828729105325968728147536262305133001559384118199712268143215353367494155977247966483652888289420146281368303069960779395353762099663819428906164986150714721641759548872529708512573194606862074022072169322164553998363208944573740097628201850685037393269278163654041912887270942890918779129536577975189895311369303240795646655920356347019821829093548708737625176754709927672320365755205014203870268691556077967680738569625410921021770395999906110915842480232542332203147855293969835287993788331668316503822246513936109566590538954645788032409141049959624850721189161804126185172216919623757553361169628930000914100524199748370679167279047169976613744720144736897151029932170206852791745948646977058295296065328733858418658232429798648695454368992289697761125594092465550605119209555906354434015100590791846428332610434995545141373448764685539809537130578334669394721283660250468087263477001450050166965306929031833064310957167473199073603426061405492455074176313915008086001730275799839608031049049760501569000494600745023210046263083134548007073974886852885999978543622957286616743920977156235863028523037557884577147080625548178690349758543244602821683768921428599134407041563027009326356007092437455288663911298985593576403316075024320360764331321209387586725942091834714928487859008387153712557030914122121121914788656868093975262023396274755003386769825780861131928071723796813347790843373586116283489462644810553904821052420908462747368886874840992043332639940047441583945607818725039853344826293259118298383099443278844394064412496599153331937663979438746619524950281925426206882930007748054328900899067715045437506211454956527732925105772105380972542404195052171575558169764944138412497559146078394353948633458525182451594126454193599987843071
  | 76 => 5031576233850665282121253144071470518620628698173517545099651498658668385982238037736539140987900125703338133802264509380026587922956405014549448020337942276029170301136113232661777658070349987563002138068177243373545430051353189903785873487138348056176809017296380119643013030966924795912328774532362453820076552946655122274859983664036190909830723926870752746128600517877243154303585523884942403275031355208346254792421479329441343542907699308923405534765439136729587202047885846235562479830365946779048846338477366938426201109952775917197715396573851203116049316949857971106970613530106787532182564832499292583974378531922459518976461110657157554735487905347791930006578993640446885420371901841515934985713112623640327239146190127526222015554270146673983968285789796395386663592975421364241512639164736665279656900836068261032268644195371480414794646095330564215537966304666412924439106057815694707438552019130055186276151149834368759768947364981029373878813700293742672116456616252006710489204048417589140549044061120399373735946338529007281561673296851723639296179187765457048006308330415519396215703915536503197133127038481859251310155028803777004378568688226214898550237003103260385720706779379608072564284876255682816717923807871547219557205059105570518317577015580373285729296220993827300043585847585193389569898253206040340838494609316835020074128181692181844926117008384802880140570152716784916486549918376693860293172989426038117021198509231302236564548787884669766647540324799939579023984252636638328723600164512218363951765373711658483493746610052427389972992806441662009001214121502177982456570849022941971307045289613330291408390415517223506202189062729880273566550619047409817343510912159200608971816606695309606628931576804949578594034937393442036305089813849017071892480589879790576686760573083077186937799412050369661373012439973355715206631750498276698199413870520425567603392872493775668884421236616007282756223012345640513358435681186794916015556445703308650561195549991843531557546376954982520734910866154740788419252169544329195794616457194586997509919837103587525391446163760165269751483145943763678685050867641696784435111208728922022562834160694076248120774785345393122237707994950903864342625346961667987744425138602971925292702324130883645606259637822658290231538601034908710040659341359897379461537895187008106622541324614915946114291645231967608521222924383019652530296164387955585193861952979378086515973139399785205028118748814133986384348757957496451865462370877902810161260330793153829085167234265749616937149204123896249631040852120275407901722820950543085278154407809164254877141039387737594372378502367985532872398595542561201539126787514991974977399703871345801569231489572996055432217461025609471769084151430448369759756918191824853592556758214203537039925356607982114660280471109822000957939529429831198343268704669649137957969614289798454697868113739147622175943276596601087112531903599035253433810969009728780965553275859849479346330225308675631883336159614050713897109184235414594116654192268739716349261693713004424448968959176174620310890900657903122164121442478143427745763995028355769944743043093155537996120812603590838639987447370979383945701935611321111598378368028948211321094521479354136572045643328890882534001646501887
  | 84 => 107911402168433851208127462052757757004119361654938193366927791136595754960673106571205267830775780854498564464722239101375040441177561537990162494006746564636767831233720851592442792470550806526472270900174549679391590382910131129645845913300762132581428101836163783129900658182785074642870906950889830930293138448045367607896126437243692404375554408911584074437627656079682470904901380319634767485164982050517116413607939678121574374800219201151226668291524866832207316353030159495079295758043386073702058155019220418659558718438925640774690697765148237406669484327683200435422703225076637829176648946570256282785523628680045844919987010774939314839222298389930319958126485717991434617520336122410721129825222513388518378108095665733230936413081245848982501461825862338232527263561068874750807987894111519890365400121058559246578313508144652926311575378765950248670160687766559147704829097991422718445088816832149612408456710002553739379290073609488430964607094613779846774803075877106029973304468499266401264484271766777831301929398834989664197346225970470728914011442154195797516466604564050730742001691428215015199620211503623161652312763861185445907637066446067183272088013277808779277391248182761157123112310844186994021436693023716176220108594559453346686683351318471588673256421747961983493826325261921738839538535901383336894574902900029102621857422362439922792219855444671548184680777671031264793479249548091499047198690823478445610991223237176262660146862366871760990907254759409659216291454696641252945705698546689738255755923472687090684860136069921518916720375534763294392624018999924785579246766117187642705436473063033087026523135523411797758055922796158587421893703743831931276994076506172339877626704563709881235897287538213974731908164379894087703530496339596160108090810154878205941701954407961940558561305041739573617361755021926398636126584140123904758608229708815173589368483852668226418195739446988603618542550620884189629471818254572825768346147033503652216568098175307408023604386350915560410158722905959311331389599262340639715068386447946620316559896410299856130324351457664344462006415585523480960847812698528214054011986566502896032576958164782133300640507974977776488274363154836965685580657733988713115206396732913708055411531441577017099182681712597844643506239147163277027249164450502496022002230188962808638992793188152719227634313097304461329483943795498437588834915644142392399478442087266370046866140698206619584217355631448446580077111690750648381483401011198496904729749607051955856842956872145019512247317929578654354004371886508163060649308066101617016479448471659355536315796690949409274747658368503958328996815751381104866344452151136425113632128395068210715093579155724629683580951828280590264306569760202431975947189561221462301089515767102577361454695486838013350978605267461052112510801067751602980191963356083402578686628446480911112443135760411406010905201296188106278539362530035947487443599541672174180042960876183486531865220289487181679758860661503250073094519263690586391894599739901630158886186662483067861277654310437892547021803520379760601254516234200329328225580342759716799106786402604051141671884863970081652079269270157013346841560781009036383139121103375373802800869937271522964291409154691198062921718316961708747350206978941903569756720545835566087926789383847113565566153528608841748282727980626017700830891906575946238279860464102648378072819382269227142694224636873290803478160848159234515869483728740661980369612546162238448036150755375346278565706809214955630309762182376142320122687600117500655388991129053911360714885911401560342641473750763137138687
  | 91 => 49950812740967115965866629470435141462112845383999955559006818958645113041734957749617199268724010048827025398305013122772681994654471083110207116680662436422365562437382154112101354270177668731158395528958442705913850471680714667595214616897295784891200511580175496850791138097661940652823657457539311265730607915371675360111473264744467348077844898221443360751595152566578208258643169238143497637447370699260439125589378916708569889368867628544696031502823739895151875529146907422921377114615724244829640537308445403326030572304616115719270550335234471929723927941514979099479981074756648209234700582430900997758736389256936635270760045143359149285081668188172262318507082286937291803732992382257614802901143601810637400891471174516834848555813402122865397536318026827971379821959247475224305729705059188572419700081185978751981767657821430887462628753139534165727109546008426316261760795641933975447057603372458322836919069123647458316737818022964402403430390177856818271074049806927750065040252361827135585975874429977604350387336397832693410930674781216842477617343337594873023245278911946537363884491932582883468368618481842868394315592755619792492987872603534844792078225511159075192239148374599671629448160148746605745171944564321078292673132087003082907922138900740317466561043056949017657272794898148065199344056689110422600651354421330449539769237382381202853556908305228859005468003966239896590660344451222799756310358844618891757384835543290403049628490544527381212534971369579519452590644093857385869216037210693054349813840982369778227100599318888852590585981653108059070312251589383105761437448220917704168182401889505488758503134192833310038510359581751747034411396853613470335401579515293895820454091997038368412540785555446051932119625111484582976748271601127816789142346541631387111035364290970831066132939523794613644694511267191889509341839000336951647734486058231658446225991922129906141825110334259116461103418431985466587981859838675351958551297851945074829014284365571000974601157342153131165945195104473839898724606747501110414336469754253716752729965860143193686649792459734205206135671772377082243795856113715021426497788442783166068927704310131612386987592125921151357756432120845215323726710641708212284538893017865935186308796273742443346266159259593604845241844900156872103891966077331267804330176216776185844666520804550187388500204798919142742446986692799891346465237503586610532101776594200235205008884570269764580592813073108617020300997113593247450198751377481680765477899026047452110336931162458573475372244115853119709677975477589404671207591392649688927730660097754888542601303146072228606465972520020828225636716690291115646131003074824621180626360973102135543738136487866068829458360368476560310068677815916736305659610712012942851288066870377529388239575228240763919304274451197693903709039701175383534518192708870446576558410068265712457250176201124505485585080735804641200148484917649522753922577092161959796929555891851096348206876671993902423296100298731516338336889040146084407222655280972130541334627309887489708903808717411082866109736055688673908102860184837324568310758076712058554677134650176851150393834036450892145830982992257982877349881557476691411756555632918094336178325804457481214173389973402458174194566165539476440167909445290366830606788719386197771315376007817546578311292801605036897674285000490647235614370152706283651020349615357573667195438622694583964050716105015790980994346604096896194995478443207836732812998685895501360710567841179783752091016842729651905898462806562293924728015882242871370293498700362544069209228717738099180356862383518883441790020920264651617160395059770504885286479266699191630554608849164230962739251834603101753082177796505351714083608377078934403402380153513747724123488984666875064697825904080139734312370693405056414516785445519580075712850642054105235178121404404637844881850425780658028683701913978983088028658460892350906367
  | 99 => 649444067321173815551160695098853706389818427288825562536617505800075139167778812584009142976775387924947810438166374812246854069824502571840042334065492597650307337756708700349580129851038584468292150143283319361944618178883204653133199681806486465438319417262820538991685834076791359637707323640183070848772299737578429820662776120779454549510575458855843227985619599803701860281090301872994455653115509892730138460195845297597535286605047888726978601800627544397548672805154288814001574202436715570329911421031721387507011852865580471977028346694625007083879352062967143327475045269947177366286588406653712467368249443350986676827305285893157918011016870569078099049334843215883895082253678377528197265017562744700377521549520406218138999467238704271676548274063859754193400396424105451795547374597759746400016477644360902650209529589821186874205106619167016732318953213362495733531046709441219379556542221906588230971989913184242739970359754491842704421768972083888752674570491313723588570553946107822021971993613141704748362673984049748806617272463236944943381898007023811367668101612017277725826204264443624970803902476618418964596539557705082154994629609788425691085524354164215196280878257490537445405496946773052765254299605489942144388005628855017388395273606890708030494597491433071548707091921857771144898093689212355092218869108588792757396520735199552893476811711510306379833852482866380413744310493725252500909725155845891710437191699391486721793985477342404734555350035974714490232968322348143702835852930256978426235434980443534158267208981176213390805490950220792482782760233385887516465673145742285004276088800510148518638538230051628698831793902160772407926092991526310190421508140574253383090592865848736326085875871340371545108709707560284000492430628457311022385246561399661474510496553883148044524714319647652841257685855055486420398866417271685934237282789502990022487532492535104667073283411404987079186407620046554815237985918798567643620191940178116771695121860240224884407645842586904463205210822569035584069677911795401974992253705321543297670056879851994573132103701421786223816675852972711854825408664971271507047312654167490960724290759814056706701110474987343625355564139734771119654778214772425661709907900704848001719846594655748850524325109159538920450978356948760538616414392250383225203123256688592964418437072975462759400601440905682260452312132502856758814456857183480981752793260824811331021784794525864211054354051153692976920583113708309516083887247906076169708029164480301166342478718240215015922166027830484454790869520662547504830932696202621969953518716750820538838948982601072791741619853346694553475826726750780911123239643243103001315648642183094938778920479551558315773176680419111305643397096356214053277464419514699395446115857710884209431730848160517786713365364574799327499419822234760845913898344854376346367274214421011446156664362973699723611219999620039474040174682680279054937517950980239498422042141850394722274972869489113046106302848652940154248116640858174880165777298978561762213152677117037409377713130822105838806584201243397479308779577855085786359867664569854366155336983000929046548843477329850034558607963473590438605648176864430812945553177600491525732092308613817139156327938052987215129201183185053453054216714403177795937408443430589842950761332989385131014998725037243720487048333848009829459999998056461259320464760741406587490748060787137406254040464310840551436253766190830596417859276624420987210712936744532369993233743270297496377037107063181749315625986433800723051791195944322716314715998113148358183169013519331239068347998415445233935155516236372905841159166011874570564821879765868109944730834508691508779979927645625078605665770983065484256019115405231366367195486173710511219054064533032573130453718005401243672659447645911752104817966755600747766541855930533085846111565339823851147815158646181554118329024799160242660437782311963366160445864841238960651392050943189826972404735286749827287150031930936174753983133932703215731940923126470226116941940569534600033874074189082321530386639692055500629896955292128596313848616315260277976824713295405508009966343783984002646303359431823924393062759053995493092590611018921555885872578218819750475817500289133082932915596529138216012827590655
  | 106 => 1781465364532980181073568719171135699059716622873288377391076345458946697966220011541349815204680183081143809318951868277913217956003366858411233116012776127729227207096058566191463612962752240636858306526022201113766374097873212468063367329033863883993676878669726200076136133895570245352089756161207729111469705058677456065671385605214620802193432363588274214587003684426684622192203931063108406036985066054410640714414749894212705779295659751591255840070621459675762700345025554711680506837605505772495413334029035237357983702919690786543091186202051069931560632247427134936387976430280284975190935763731221946455777526844288738259608219770713818465257925189637709979255737130316145406132720343128468924990085080349226456203156528221131997803506702202696826997860398584469153038738482787278603336852380708843955821666247000565946751968510772498096976915784401090490995464371532022450353841390166198614136618590887416606931938378416486515812947517715313149654773698876428076372273388981443498927486965788334892685529118219957337270411828811852241554090175195870539610403261137062945852593130826279235427228953114267859689055870087162746024546598654478847174990904899994083912500993462475169144055146343050307819184058630642179644790925395815630338975602934512805491954293729907409805662411387542731036735082357331428280697907051127989859663077375526112438160084529071069417025945613237725202884974109778911591125538959846979357276137449208992172904803776368573077967010649863006835956453258471565232780853594668176936719962037698543239997156919094723478730765987099707699988704444720427513709205432740087008918270656900272824565439650867688612090720064279077195224516312948770584655495892317060102497816557531995754608553084068002464548534398535303861441132826901369580385466623897134287586778628820881445964750632935650417199010641299787098791281589726905723822500355186136294425195915662844737625909687594552671328132160312832875502257664753773449138481876195094380269921233096245275308628430088419642596904372548467561734466801294284092219652854967846030839426686818425882162438295637631370908276075715140500114029678712296481759407259363978979894430039938718102275250514014766980681399852388903602286345830780994458445212101158156011668931142917525155638260249191715240022981544424276022182254138665883040648198433821308782737184374963004545453692497744032664752590784759213631026250420457847666900333722546694387144102167477013394162075146644537450703198902586049147735706173775315219728789181919143935682121156194576706925919422565210735304506579342046064149373622381450694054218696968638618360681265690446411502793408624508242031084892904130664504754168589361974115875416983466826221235684892430742107617846029355562229994837395023611761248101490824882456778226243878921509375540145177270585155675631808288783739389426383519295468532263227378499303497523585364035606965026212507043055200274969862565940505142826979009902473021144099825462557936713930262257880879920049926487865568466971549718595641665875386307655751420843873841212999154438102470757685704550479366680861461177041485830655160875978638868463064911384100709942163653864742323743806685978427424521576898484535289593292985155407094640133982715519330972089377776107513699464136210750462112653646663221725579848138282943544350488564833777728562784421948072939288071492320671251831014686249069110911661128248448601332900058845006011842239824185447237743575480994739539681136399894128628154727641104861830152245948738156702069870606333995567827849910272210672157046903664353530168772494088444238075655928717456899235551879064099688108985164765686230946622286676324919818089989459763387467079300536916688956988617353018666673086406866886673264592755490453507736088849794219541537553985877285646721954300431130227307046988562840032701380713498974693168273126240395951111243750888212626609379757977647333763516378020313814658376815694062397102586203999208123071513151645933152076645414019573465309269547855446007214108592679934046913349532891828497147366240427150432914550618836545855329420263995859167422084092016516697720854607434870616528082880448644134436735533030740974907066407388249830362578329083579694978746213176595256031951979843071749537032303013764845982238936493047334601593547350843449311098677310168760893546336783578346574586046348170090439616218393549636020483319220515508760482133398848749060386903483283249774577591157456800946664472556336186400556545716558509922475864884916653583499748289326975638355900295741644782964411947753036873210770625437437086765910447362070672926395921675709051637334015
  | 113 => 10007900174424785971811267528613807184779845276164778865926914894788718026826224617842413359609965312422017653368396937833773263631976462690791349082115115868418588486416129054446346604956276646922162419278550435635631782224979888982292732132667111436565126888023545295935253145273800231936824958081907233950646899983591286144277988894741032133229540014411970640675917864485879427900687257858129496734823296865907426688312133837714081576383467827271702753834961750942282231182859137761070851463324359345515991524756476248853418639805490632892339254799034094997059321803897266547570372876530854995971578896230013371148197246419526607841658171186488090073239217868170871988077332067499020681399162809221636216377109681220394936022511870336418823943698464327832277042983770625357829143627613432020653609147294111182739730195986888734293865899211287539406699354138997719357263016220565723664516777570405630365503485682988960064730485286879376858737872441610241373686127161829499222290376242782066209967498366563877459029795096260147407581953081583059860382853031192678570546127858420055570060394104824619758877155271399328458911447098889598245050323363748463739410798014576879459551035646271282718207676095652368163752967738788691578236940728439990436928327464959269093798214937422889425065278661344422621670939990233077350249711456554396053477566294237216126701628910761093537000182341395223973514522013978239137757786686484756247268140484413399917494716127487699164687177825907646561778527136292433364058780243723227869077119077424570024616320880915263725953924733849775466454919443036940939215863346468479305901694791358071604234131468979186231803019645502517762657259541926310629021807694335603105379673997300040893009267820935860460471567825204674334332313865463773667999076802092862769216330250530613205295158024679658124261014586203918461463951934140304534889936115634001464927784153224303636732097576966941475147907255168088919972892107955218910053036289711079614308187091307432559181343808276969110000658955838244691479975914669203574334445457627462152007475495287493549506553460134554152932406889045636272816809612057824950886224167507211054135550956516022084852690441377131757366329952240845113997925478382379613901419014347261671550508401918123867864377087579341005216406019211425965213170482934903441253678925646751583667237110625307942747019931110806215684035176783631210524951005430049090764236694273684234928362792608431010468134521819769831208810784185867306623365631097993559484964846082736607094751063656081833940682830191700450867157274761965140191935053350226709137408337708837233252522392669536474710733066815886586069484771503552924867340711165889982358164106959266623690694889218071390637228189369020451445053994755946146291610458989720602948326243156715389873877964739932413776105575291184979237083747782018419847430178893243850756558894558748781351323301596717880586949398172457556972947480908494688938148069617120902154786254289629051519068540226179849127647191023270560664144983375579558878515198790323376224675868919591478845916584293838013533399797102022692811517969796053510280316377952371340172100500442348039684146305099811191382041874810348879350507775932888045436433019606002901037516681933450567674198124219865915005238375015253399208169914397531173601318766063134864007538938355384960797519032375274148670850641529318387583062174951417716264358417375056402307744037174681453651692749782170956421221626129876408521288653187520739874662967693835226849226568788694073179400836454981440399329776497348550304552638655895767040126165123427503771124849519793076430252587606385442873694254666536782637757942829717440087485492211932110290014281181010221043273531984000313655044197076332364433644863383242915587786080992412529569128676981841118246308444472013597521649693012146178340414515948304808197660208382118451432344899295513016408035672858970855784427067748862339109105572180910009734662631070236823081179449569785816281966592189377635962644648491475717525871399281586620405261066490901689772526486913936951772484164155261762910020505333484625441023758465017562376535255843578535874875314777221287402492814858843272554543163032897202235286838475465822274612262966557283335265621065810475272131225758907238754918416539796973746783477745331894010861574984472101629616852688297573731827103127364178629299541108520076345638491898373937407791544143353147037424706108620794876088489150681308042717775037133315605231385840704257461604236066019854643254006951721108869514191617773902983608682746022125156137555118313845474256811285306093169176647081822071355205470863087449956943645636777972917484298843177471561235882224976745496021697647988908461210054255108566164385158176354235895062412528678698962290858865077649628983198537049781810720433543961126268103680210732046361086308980008421362725352181175847908417694727776072846306663948509246757945704506349412417535
  | 120 => 18759065525207094274827031047376803566285839658032933833905543140612806607707913872745033389230612650743508298493004276134698204122467257855862226853127999763351023279308109573426671193345762187885027233995007253327787502916108498370845104435597265421206049656111757882689483529461418007696656642322299281272584184625328067273809276318572207765255379890059839743567879297418018968735285671264629494944126504562823589011572637907902601069024315509799832580982619679346844531104267494568013203530648528279263702635301949020470643756875094453463257803870302406668557822421792758361649132806914117198118774751611732299107599240262869694368243621206712264769538604679645440350938043747211658473024460663242647562296487780125644576972591727196077098473433652829361443970003889371174488919608514331658529295188926586690282492652143674643851624861119357672116625066445449026487052519606570497909225806010151108596427406089527068461792366885681884663762016681162985430032594234706178754257332838301194696887295955258643029553561985243736398585214168157341919441171973849732339575142506377543454331611107569035198504835624534175893437019692869145884945260393084807808872362250180040976248352500935315959796396737574558850561009564878036745186260532109426475976430529602063647275865183430888345574145385869516588076349170409464392567007365599805325682258229688592920067373425344208552547682198440923594860712015801856997051211884160407401808008002165325512478311038230121035128535389371902017556124148517520974216740330366113284405208030564669493218302613394501098800114186840388249515801103456140577929055735257082168892221320494709243999186120741337176312181136379653451398268796934365091128282127004184651045510553238374975997635864561443706624860791904179382446418545471783735859299331246814435349727258865701622508296429482814063030935861960067185718805194246093115280731594635625857258258270129059579183434311747713962938532842514708325644288393632349594229610511967722166481521351911884101835291729376843925992564334841736932936720997873369912984101933493405608569812019054459854742421168679998274602855766937889511570703825580735183999222543506041612974045940982739439982932601975834489261211905009572744494000365209002018527867881079864297468247551967277256574452166603614821206147924931223936338877429906124776910821480761788916641953693208789489895041886829980382188822448125042795861285940518863375050927324757858664321630545098016822294176148816186219435881365024311375427952478912601733958859450485398216484131622066460071141849391102991426740135722343830969418759901011698659958639556747603961586764041746789379296742665248779372079812902150153428845577588137924251651928342655446038077179126203295239971305257107518297825756773194820123856554682450064522433010116162191261211727905041662341328626207086629684679359425138169446786504034429848096480647200438049053050248064508111677879103776804050287110703423629152782926909377991550992692584251840681349222991683146213882130803642671571488645556077125231780099271886942571519916217230170532583428688232232125659013441720185280987395736615673009866937867063343773105034655729910241404079693643587886647862201086560920208302846754082047222683270112588356864082074905218894409853339731569527559066863756632434378509201758764999038400220400998656050446422621470366800048863608268906222522556579487088319352793375144591905899590323460136674603530256799462400413516198366628095111600895593302225134687738508613649310565392674130896358189771748959745706836262039029817692595130770788910661532868214845643659758116642671471770087163888727889097467373883110381956187827444663955481122304013807092136026411540264563783983407317572070726184040337507140160336404757493385653144523781654186413048228102198192844163347248905098180324303677243638160877761035505705774492511737934988189441798876288061939197139091392986330826564015042772656200815053351849064034238517612123670239554318998215755803147023570716560743257746281865690687893280965692372162778965959358400121542691373700551840218850369879410271139563784885772280266712543241476071877799418324629662017447549374366825592082823409475185414706219676390659360829290837765082729495904949461590221041765548208212370636517256285432674016237979513472996490592521132804652258482040145712295979131867884784444095471199437085345426831992743535543266365053753478885748585434743474440035298315828973405790363852437555137355395005152242252568049934583066295401854040955200810339620419930599678051071289734594541476865291183381773084290157941093802954370355188602986655878850335184409847081339514314357776812028895952152516496394780390130852141427699852460711902307892436944793841466333407119326876253637822102763737451411293853099905673625939741696809758220792529865945039189654865155309658836875245747048307004446195272704271231133731767995893303281791382819781771701243022091978765583207363677408856537065014339151475371357602219426871875534186986819442229276364235459938058886740763137833352028776784529542330045271098150288468698844626389473720983413655199244477820197532618655235953807243390411854244780569381296012141322537847256554943773523837331844812439153039903631977513062729976605816376494768783359
  | 128 => 399813797893000791860615636805638640285803128812211456716659884081670092251874112696353496275577306445980882824223576344372767002678988002253374244930722121626992320829428049637671021183746514857617162965128374356533117052256958473463439448744335130598677751878960599257550947652735754670666003272516151194104638576958835417726001618514034039349121472048471425204209819108685415089887698469524781330453656932032202637010495019752608262752270207924816048460728594903298559745279160422013565265253282672491380588056253517700863972500439452989551866117047624762843705746336369111389740539307471571827117895112270893619378889812848851850584122900164601469626543576093161203782671409025313294590921333089246890788385267454740230640369862865059161909108530646484035346545911141312668168331903502224072932858002027965967938900068331777095218427164228304334747344881788746977599215730154179916590509666168085867788172907664872131094465696483901536577152236002276812306522273348739101967113259428221699899879718357763531806902722151619072681962573644735419050124409587352955492448110964363974051244659393966636728903136991024480734148859119185333356546400217976327794767174962732783485588886298372393978864035971064383553738772260185972659460498368300567217997749314766122275882915915498262087106429595823120053928381995760670773306105667830760414669086027031142439389807423755903274631010041979937282403273703297662780842318896383643225944731415207367699817777965402726174821542925826928639405137714989174051854768684667334458293771895520638744135603815497719806296862427022007226774818058230230394938834980098961214371016819665580921108548504414986961454204986837291254788273128427991873215638628278321030816277465880111787956502298105875820379138784686959221059026814226817395678503154867894015849585821992312947997338450998529624305557346291262927530100778492015985901989025921416344137360578991762523677464328011070458881064347470302183887108203506767911723421907663103619883650230608287349165964659742377161909216789034727205651129115596327884307232200928352931041670079593090502424937981978980320666272777617504810965516198058157752689233095061780982027609487106865089134179445815033056323535222542358495578693751246700858342659064969930173566475194579388055212852276483661977393186630867938949401190154892561281420984718190422497166208879161914226426148492013954447780421754236591586388369159747408630680333795306953658117404850951503273027111514545599591795140974030241566037775515826595682749479201591277344110993868558012505800958812582655002811608146836956544592939955768706072715158372995381330437652095057246291373460463648305863339227036865818470044601608729580777919906137389276142658176568387528933081860249093099808235716168945901527316213449072029777228260222144791863417018045403948519441271378612529751532068471451040697923390829966792644010466045595485388109173625404890005246208536881262107198014996579403197748381768056948773304607265256292658491817951508792789344223716983988157086507955738260786962158710630185563726356314076004198274089079474513981596192983194515771277392972340188151889567903244181615286802905621799260382106565164504277181392673978114708523368840644921451985108211105886652066442724092751849806313507335939767858438624862918445149188348227212944866587366639906522171401409369767602959840747594562064325991288386771906222416545938719593099124519307191342623327662557304928383633656335318294322816225033173018950786315683588150673970454610395752240781206408983969687466351491944347985202205836500138283512634762457411376909910184452242735499039577822645328666341264393037900049649038658842087420718382481956562725966124881074392422270443230823404587641594013070376182883929356090784038257855004494843154898532068354772768347338338787542411883009053716666712964903894390365460443886705714111767091993591329771882023636334273099559265533632796076130145999640921821837237735766761433762536583058210769674349555137772561292605447589220495906228236930721272776157657997431095927770233736348231415987921960835865683556162077130072374660608467991079682575773092095582710609654636511180770272455431238337400343267483297310526014121334052697961222008455777372999198466818569110734887821776848524045182656050529062259130996260216612815744927129781248158358147011952013071170452819231175243553213934404804119283779886571464895704388316356560407460987858975568209142957750804585437715944614177001931858820187670537449811984076577478443615355371057924902075492918092741846540938010175398683239683915091067738122923866684751679885702600363509274502222889121205328503919113478457360095630520975779634180218226109827212988389192082500037981757694028001955832515348021560196617978191295884940393307073309915618986490055386410771227668270062056618288024088209369814511089811691452289294779486602930995118721815808444009149406315120308137540265664371422698063964480732911536385537438817014804386657621146502061139765588069006041837322481974430163859591148994649405415750904023696444216174540770084906227327763392055821345137089860389255331839505436749148452989139030319276147460542279997381588978283245585861559692699660399731435569692607596781296259845762446914598477741171735005001674928710486905556132784137525931881429866737233885886650305521178864077711597939541406460642277174442516075015765647295241349688708272268778803545955411854913136903730047003546448209981170699060980384675433685620637818980266394087358955015330034174244696107271087667761875042790658387680210655608863319137317417577798222974646307676688956260351
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
  | 7 => #[31111530689914373802365678393761665047405, 37333836827897248562838814072513998056886]
  | 1193 => #[6437934716980772870274157670577252049921, 12875869433961545740548315341154504099842, 25751738867923091481096630682309008199684, 1937620457626437122713387937801468019720, 3875240915252874245426775875602936039440, 1421680106984580013938291802783368721440, 2843360213969160027876583605566737442880, 804741839622596608784269708822156506240, 1609483679245193217568539417644313012480, 3218967358490386435137078835288626024960]
  | 1571 => #[10672267084425226937395008806420316257281, 11534023507617071494296172170402087797762, 23068047015234142988592344340804175595524, 2579951064588162653872738930342020124680, 5159902129176325307745477860684040249360, 360438234613033484196755380325065243680, 720876469226066968393510760650130487360, 1441752938452133936787021521300260974720, 2883505876904267873574043042600521949440, 5336133542212613468697504403210158128640]
  | 2047 => #[8170766438152402225770292478986942417921, 13617944063587337042950487464978237363202, 24512299314457206677310877436960827253764, 2744866850316822622719707629659675968520, 2766144887916177836849317766323704464400, 2808700963114888265108538039651761456160, 2893813113512309121626978586307875439680, 3064037414307150834663859679620103406720, 3404486015896834260737621866244559340800, 4085383219076201112885146239493471208960]
  | _ => #[]

def prototypeWord (p m dim k : Nat) : Nat :=
  pack width (((prototype p).toList.take (fieldDegree p*m)).map (clipShift dim k))

def prototypeTest (p m slot : Nat) (mir : Bool) : Bool :=
  let dim := 135 - (slot - 1)
  primaryWord (fieldDegree p*m) (prototypeWord p m dim (entryShift mir slot)) 0 p m slot mir ==
    prototypeWord p m dim (exitShift mir slot)

def UsedPrimary (p m : Nat) : Prop :=
  p = 7 ∧ m = 1 ∨ p = 11 ∧ m = 1 ∨ p = 11 ∧ m = 2 ∨ p = 13 ∧ m = 1 ∨ p = 13 ∧ m = 2 ∨ p = 19 ∧ m = 1 ∨ p = 21 ∧ m = 1 ∨ p = 25 ∧ m = 1 ∨ p = 31 ∧ m = 1 ∨ p = 31 ∧ m = 2 ∨ p = 37 ∧ m = 1 ∨ p = 41 ∧ m = 1 ∨ p = 47 ∧ m = 1 ∨ p = 55 ∧ m = 1 ∨ p = 59 ∧ m = 1 ∨ p = 61 ∧ m = 1 ∨ p = 67 ∧ m = 1 ∨ p = 73 ∧ m = 1 ∨ p = 87 ∧ m = 1 ∨ p = 91 ∧ m = 1 ∨ p = 97 ∧ m = 1 ∨ p = 103 ∧ m = 1 ∨ p = 109 ∧ m = 1 ∨ p = 115 ∧ m = 1 ∨ p = 117 ∧ m = 1 ∨ p = 257 ∧ m = 1 ∨ p = 257 ∧ m = 2 ∨ p = 313 ∧ m = 1 ∨ p = 471 ∧ m = 1 ∨ p = 1193 ∧ m = 1 ∨ p = 1571 ∧ m = 1 ∨ p = 2047 ∧ m = 1

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
private theorem p7m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 7 1 s.val b = true := by decide +kernel
private theorem p1193m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 1193 1 s.val b = true := by decide +kernel
private theorem p1571m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 1571 1 s.val b = true := by decide +kernel
private theorem p2047m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 2047 1 s.val b = true := by decide +kernel

theorem prototype_checked (p m : Nat) (hm : UsedPrimary p m) (slot : Fin 17) (mir : Bool) :
    prototypeTest p m slot.val mir = true := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact p7m1 slot mir
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
  · exact p1193m1 slot mir
  · exact p1571m1 slot mir
  · exact p2047m1 slot mir

theorem prototype_size (p m : Nat) (hm : UsedPrimary p m) : fieldDegree p*m ≤ (prototype p).size := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel

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

end ECDSAAdd.Entrant.StairPacket.DeadJoin

-- ==== begin SelectorReceiver semantics (credited to spariev 59c20890) ====
namespace ECDSAAdd.Entrant.StairPacket.DI7Affine
open Arithmetic Partial GateMirror DeadJoin
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
theorem clear_valid (c : Bool) (qs : List Wire) (t : Wire) (away : ∀ q∈qs,q≠t) (s : State) :
    RawValid s (clear c qs t) := by
  have phys : Proper (clear c qs t) := by
    intro g hg
    simp only [clear,List.mem_append] at hg
    rcases hg with hx | hc
    · cases c <;> simp_all [proper]
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
      simpa [proper] using away q hq
  have plain : ∀ g∈clear c qs t,plainGate g=true := by
    intro g hg
    simp only [clear,List.mem_append] at hg
    rcases hg with hx | hc
    · cases c <;> simp_all [plainGate]
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
      rfl
  exact ⟨phys,all_prepared _ s phys (fun m => by simp only [clear_run c qs t away]),ready_plain _ (List.all_eq_true.mpr plain) s⟩

/-- Replace a prepared pop with its preserved XOR receiver, transporting the
whole basis, phase, and both independent inverse measurement tapes. -/
theorem raw_replace_pop (a b : List Gate) (x y t : Wire) (c : Bool) (qs : List Wire)
    (s : State) (v : RawValid s (a ++ (Gate.pop x y t :: b)))
    (away : ∀ q∈qs,q≠t)
    (rel : eval (c,t::qs) (run (GateMirror.forward a) [] s).basis=false) :
    RawValid s (a ++ (clear c qs t ++ b)) ∧
    (∀ m,run (GateMirror.forward (a ++ (clear c qs t ++ b))) m s=
      run (GateMirror.forward (a ++ (Gate.pop x y t :: b))) m s) := by
  let u := run (GateMirror.forward a) [] s
  have va := v.parts.1
  have vb := v.parts.2.tail
  have e : run (GateMirror.forward (clear c qs t)) [] u = transition (Gate.pop x y t) u := by
    rw [clear_run c qs t away]
    have z : (u.basis t ^^ (c ^^ parity qs u.basis))=false := by
      change (c ^^ (u.basis t ^^ parity qs u.basis))=false at rel
      have shuffle (c t p : Bool) : (c ^^ (t ^^ p)) = (t ^^ (c ^^ p)) := by
        cases c <;> cases t <;> cases p <;> rfl
      rw [←shuffle]; exact rel
    simp only [z,transition,front,erase,run,measureAndCorrect,ECDSAAdd.correct,
      List.headD,Bool.false_and,Bool.xor_false,Bool.false_eq_true,if_false]
  rw [←e] at vb
  have w := raw_append va (raw_append (clear_valid c qs t away u) vb)
  refine ⟨w,?_⟩
  intro m
  rw [w.default_run m,v.default_run m]
  simp only [forward_app,run_append,run_take,List.drop_nil]
  change run (GateMirror.forward b) [] (run (GateMirror.forward (clear c qs t)) [] u) =
    run (GateMirror.forward b) [] (transition (Gate.pop x y t) u)
  rw [e]

end ECDSAAdd.Entrant.StairPacket.DI7Affine

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge DI7Affine
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem keeps_targets (gs : List Gate) (q : Wire) (h : ∀ g∈gs,target g≠q) (s : State) :
    (run (GateMirror.forward gs) [] s).basis q=s.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  rintro hit
  obtain ⟨g,hg,eq⟩ := List.mem_map.mp hit
  exact h g hg eq

theorem expr_kept (gs : List Gate) (e : Expr)
    (h : gs.all (fun g => !e.2.contains (target g))=true) (s : State) :
    eval e (run (GateMirror.forward gs) [] s).basis=eval e s.basis := by
  unfold eval
  rw [parity_congr e.2 _ _]
  intro q hq
  apply keeps_targets
  intro g hg eq
  have hh := List.all_eq_true.mp h g hg
  simp only [Bool.not_eq_true'] at hh
  have mem : e.2.contains (target g)=true := List.contains_iff_mem.mpr (eq ▸ hq)
  rw [mem] at hh
  contradiction

theorem sel_pre_pull : ∀ j : Fin 26, j.val ≤ 24 →
    pull (keptHead (start j) ++ (KeptParity.placed (start j) ++ selPre (start j))) (selectorExpr (start j)) =
      some (selectorExpr (start j)) := by decide +kernel

theorem sel_before_pull : ∀ j : Fin 26, j.val ≤ 24 →
    pull (before5 (start j)) (selectorExpr (start j)) = some (false,[Shadow7.e0P (start j)+7]) := by decide +kernel

theorem sel_barrel_quiet : ∀ j : Fin 26, j.val ≤ 24 →
    (Shadow7.leaveBarrel (start j)).all (fun g => !(selectorExpr (start j)).2.contains (target g)) = true := by
  decide +kernel

theorem sel_away : ∀ j : Fin 26, j.val ≤ 24 → (selectorSources (start j)).all (fun q => decide (q ≠ 1565)) = true := by
  decide +kernel

/-- The selector relation in front of the selector pop of the CRT chain: `1565 ⊕ 1559 ⊕ 1561..1564 ⊕ e0P+7 = 0`. -/
theorem sel_rel (j : Fin 26) (hi : j.val ≤ 24) (s : State) (zero7 : s.basis (Shadow7.e0P (start j)+7) = false) :
    eval (selectorExpr (start j))
      (run (GateMirror.forward (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++
        (keptHead (start j) ++ (KeptParity.placed (start j) ++ selPre (start j)))))) [] s).basis = false := by
  rw [forward_app, run_append, run_take, List.drop_nil, forward_app, run_append, run_take, List.drop_nil]
  rw [← pull_sound _ _ _ (sel_pre_pull j hi), expr_kept _ _ (sel_barrel_quiet j hi),
    ← pull_sound _ _ _ (sel_before_pull j hi)]
  simpa [eval, parity] using zero7

end ECDSAAdd.Entrant.StairPacket.DeadJoin
-- ==== end SelectorReceiver semantics ====

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
      (Shadow7.leaveBarrel (start j) ++ keptHead (start j)))) [] s).basis (KeptParity.port (start j) q)))
    (zero7 : s.basis (Shadow7.e0P (start j) + 7) = false) :
    (∀ m, run (GateMirror.forward (before5 (start j)) ++ CRTBarrel.barrel (start j) false ++ GateMirror.forward (after7S (start j))) m s =
      run (GateMirror.forward (referenceOps (start j))) m s) ∧
    (∀ m n, run (GateMirror.inverse (after7S (start j)) ++ CRTBarrel.barrel (start j) true ++ GateMirror.inverse (before5 (start j))) n
      (run (GateMirror.forward (before5 (start j)) ++ CRTBarrel.barrel (start j) false ++ GateMirror.forward (after7S (start j))) m s) = s) := by
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
  -- Step 3c: selector receiver (spariev 59c20890 Core150): pop 1560 (sig s+1048) 1565 -> cx q 1565
  have shapeS : before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after7K (start j)) =
      (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (keptHead (start j) ++ (KeptParity.placed (start j) ++
        selPre (start j))))) ++ (Gate.pop 1560 (OB5.sig (start j+14) (start j+1048)) 1565 :: (selPost (start j) ++ selTail (start j))) := by
    rw [after7K_sel j hi]; simp only [List.append_assoc, selectorPop]
  rw [shapeS] at v7K
  obtain ⟨v7S, same7S⟩ := DI7Affine.raw_replace_pop _ _ 1560 (OB5.sig (start j+14) (start j+1048)) 1565 false
    (selectorSources (start j)) s v7K (fun q hq => of_decide_eq_true (List.all_eq_true.mp (sel_away j hi) q hq))
    (sel_rel j hi s zero7)
  have shapeS2 : (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (keptHead (start j) ++ (KeptParity.placed (start j) ++
      selPre (start j))))) ++ (DI7Affine.clear false (selectorSources (start j)) 1565 ++ (selPost (start j) ++ selTail (start j))) =
      before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after7S (start j)) := by
    rw [after7S_sel, ← clear_receiver]; simp only [List.append_assoc]
  rw [shapeS2] at v7S
  obtain ⟨f, r⟩ := raw_replace _ _ _ _ _ s v7S same' back'
  refine ⟨fun m => ?_, r⟩
  have h0 := f m
  rw [← shapeS2] at h0
  have hS := same7S m
  rw [← shapeS, ← shapeK2] at hS
  have h1 := h0.trans hS
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
        GateMirror.forward (DeadJoin.after7S (start j))) m s =
      run (GateMirror.forward (DeadJoin.referenceOps (start j))) m s)
    (rev5 : ∀ m n, run (inverse (DeadJoin.after7S (start j)) ++ CRTBarrel.barrel (start j) true ++
        inverse (DeadJoin.before5 (start j))) n
      (run (GateMirror.forward (DeadJoin.before5 (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (DeadJoin.after7S (start j))) m s) = s) :
    (∀ m, run (GateMirror.forward (before5Row (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (DeadJoin.after7S (start j))) m s =
      run (GateMirror.forward (DeadJoin.referenceOps (start j))) m s) ∧
    (∀ m n, run (inverse (DeadJoin.after7S (start j)) ++ CRTBarrel.barrel (start j) true ++
        inverse (before5Row (start j))) n
      (run (GateMirror.forward (before5Row (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (DeadJoin.after7S (start j))) m s) = s) := by
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
      GateMirror.forward (DeadJoin.after7S st)) m s =
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
    GateMirror.forward (DeadJoin.after7S st)) [] s
  have hrev := rev5 [] n
  change run (inverse (DeadJoin.after7S st) ++ CRTBarrel.barrel st true ++ inverse (DeadJoin.before5 st)) n endS = s at hrev
  let midP := inverse (DeadJoin.after7S st) ++ CRTBarrel.barrel st true ++ inverse (before5Tail st)
  have hInv5 : inverse (DeadJoin.after7S st) ++ CRTBarrel.barrel st true ++ inverse (DeadJoin.before5 st) =
      midP ++ (inverse (cell st h) ++ inverse (firstRows st h)) := by
    rw [sp, inv_app, inv_app]; simp only [midP, st, h, List.append_assoc]
  have hInvR : inverse (DeadJoin.after7S st) ++ CRTBarrel.barrel st true ++ inverse (before5Row st) =
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







































/-! ## Clean-sum diagonal leaf wrappers (`makeC` / `clearC`) -/

section CleanDiag
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical












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




def make : Program :=
  LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5 ++ c.R.m6h ++ c.R.m7k ++ c.R.scl1591 ++ c.R8.m8z

def clear : Program :=
  c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    LowZero18Diagonal.clearC c.Q5 ++ c.R.scl1591 ++
    LowZero18Diagonal.clearC c.Q2 ++ LowZero18Diagonal.clearC c.Q1

end SplitCfg

/-! ### Concrete configurations for Branches A, B, and C -/





/-! ### Fast `K4DQ.LBF` / `E0F` / literal mirrors for kernel evaluation -/
















/-! ### Generic support, physicality, correctness, and counts for any valid `SplitCfg` -/

section SplitCore
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical























end SplitCore

/-! ### Slot bounds for the concrete split Karatsuba kernels -/

section SplitSlots
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires






end SplitSlots

/-! ## Direct-fold renaming helper (moves `workT` onto `K0.core.pad.take workT.length`) -/

section FoldMove
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq



end FoldMove

/-! ## Branch A body (`keepA` = 33 carries, avoids `workTA` and `hs`) -/

section BodyA
open ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq






























end BodyA

/-! ## Branch B body (`keepB` = 19 carries, `efSwapB` = 20 swaps, avoids `workTB`, `hs`, `normFlag`) -/

section BodyB
open ControlLoan1589BFFold ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical LocalRebuild.improved directFoldQTq ControlLoan1589BFFold.eAddLo ControlLoan1589BFFold.eSubK ParkCarryDevelop.program ParkCarry10Develop.rebuild



































end BodyB

/-! ## Branch C body (`keepC` = 27 carries, avoids `workTC` and `hs`) -/

section BodyC
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq





























end BodyC

/-! ## Branch wrappers (`brC`, `brB`, `brA`) and top-level assembly -/

section Branches
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical LocalRebuild.improved directFoldQTq












/-! ### Zero-bit proofs for parked hosts and swap hosts after `make` -/





/-! ### Branch equivalences (`brC`, `brB`, `brA`) and `coreOK` -/














/-! ### Exact Toffoli, measurement, and gate-slot counts -/









/-! ### Physicality, wire support, and hole avoidance -/






















end Branches

end ECDSAAdd.Entrant.SplitLeafSquare
end

-- ==== end SplitLeafSquare ====

-- ==== begin MixedBase (V3-fold: 36 declarations moved verbatim from MainP1 / OddField) ====
-- MixedBase (VAST3 split of MainP1): declarations the Mixed20* modules need, moved verbatim

section
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairPacket.FredCut
open ECDSAAdd ECDSAAdd.Arithmetic
theorem range_split2 (k : Nat) : List.range (k+2) = List.range k ++ [k, k+1] := by
  rw [List.range_succ, List.range_succ, List.append_assoc]; rfl

end ECDSAAdd.Entrant.StairPacket.FredCut
end

section
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairPacket.FredCut
open ECDSAAdd ECDSAAdd.Arithmetic
/-- The leave's low close ends with the two controlled swaps of its last two rows. -/
theorem lowClose_split (s : Nat) (hL : 2 ≤ Shadow7.lowsP s) :
    ∃ V, Shadow7.leaveLowClose s = V ++
      (Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 2)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 2)) ++
       Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1))) := by
  have hr : List.range (Shadow7.lowsP s) = List.range (Shadow7.lowsP s - 2) ++ [Shadow7.lowsP s - 2, Shadow7.lowsP s - 1] := by
    have e := range_split2 (Shadow7.lowsP s - 2)
    rwa [show Shadow7.lowsP s - 2 + 2 = Shadow7.lowsP s by omega, show Shadow7.lowsP s - 2 + 1 = Shadow7.lowsP s - 1 by omega] at e
  refine ⟨Partial.xsG ((List.range 15).map (s+16+·)) ++
      (List.range (Shadow7.lowsP s)).map (fun i => GateMirror.Gate.cx (Shadow7.e0P s + 5) (Shadow7.b0P s - 1 + i)) ++
      (List.range (Shadow7.lowsP s - 2)).flatMap
        (fun i => Partial.cswapG (s+30) (Shadow7.b0P s - 1 + i) (Shadow7.a0P s - 1 + i)), ?_⟩
  unfold Shadow7.leaveLowClose
  simp only []
  rw [hr, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

end ECDSAAdd.Entrant.StairPacket.FredCut
end

section
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairPacket.FredCut
open ECDSAAdd ECDSAAdd.Arithmetic
theorem suffix_after (s : Nat) :
    (Shadow7.leaveLowClose s ++ Shadow7.leaveClose s) <:+ CRTBarrel.afterPart s := by
  unfold CRTBarrel.afterPart DeadJoin.after7S DeadJoin.afterRest7S DeadJoin.afterPost7
  simp only [List.append_assoc, List.cons_append]
  repeat (first
    | (with_reducible exact List.suffix_refl _)
    | refine List.IsSuffix.trans ?_ (List.suffix_append _ _)
    | refine List.IsSuffix.trans ?_ (List.suffix_cons _ _))

end ECDSAAdd.Entrant.StairPacket.FredCut
end

section
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairPacket.FredCut
open ECDSAAdd ECDSAAdd.Arithmetic
/-- The window leave (CRT barrel leave) as prefix ++ (two controlled swaps ++ leaveClose). -/
theorem leave_shape (k : Fin 26) (hk : k.val ≤ 24) (hL : 2 ≤ Shadow7.lowsP (start k)) :
    ∃ X, CRTBarrel.params.leave k = X ++ (GateMirror.forward
      (Partial.cswapG (start k + 30) (Shadow7.b0P (start k) - 1 + (Shadow7.lowsP (start k) - 2))
          (Shadow7.a0P (start k) - 1 + (Shadow7.lowsP (start k) - 2)) ++
        Partial.cswapG (start k + 30) (Shadow7.b0P (start k) - 1 + (Shadow7.lowsP (start k) - 1))
          (Shadow7.a0P (start k) - 1 + (Shadow7.lowsP (start k) - 1))) ++
      GateMirror.forward (Shadow7.leaveClose (start k))) := by
  obtain ⟨Z, hZ⟩ := suffix_after (start k)
  obtain ⟨V, hV⟩ := lowClose_split (start k) hL
  refine ⟨GateMirror.forward (CRTBarrel.before (start k)) ++ CRTBarrel.barrel (start k) false ++
    GateMirror.forward Z ++ GateMirror.forward V, ?_⟩
  show CRTBarrel.leave k = _
  unfold CRTBarrel.leave
  simp only [if_pos hk]
  rw [← hZ, hV]
  simp only [GateMirror.forward, List.map_append, List.append_assoc]


end ECDSAAdd.Entrant.StairPacket.FredCut
end

section
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairPacket.FredCut
open ECDSAAdd ECDSAAdd.Arithmetic
open ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket
/-- Ends of the reverse walk use the inverse window pieces. -/
theorem inv_app (a b : List GateMirror.Gate) : GateMirror.inverse (a ++ b) = GateMirror.inverse b ++ GateMirror.inverse a := by
  simp only [GateMirror.inverse, List.map_append, List.reverse_append]

end ECDSAAdd.Entrant.StairPacket.FredCut
end

section
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairPacket.FredCut
open ECDSAAdd ECDSAAdd.Arithmetic
open ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket
/-- The reverse leave: inverse leaveClose, then the swapped block, then the rest. -/
def Dblk (s : Nat) : Program := GateMirror.inverse
  (Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 2)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 2)) ++
   Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1)))

end ECDSAAdd.Entrant.StairPacket.FredCut
end

section
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairPacket.FredCut
open ECDSAAdd ECDSAAdd.Arithmetic
open ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket
theorem unleave_shape (k : Fin 26) (hk : k.val ≤ 24) (hL : 2 ≤ Shadow7.lowsP (start k)) :
    ∃ R, CRTBarrel.params.leaveInv k = GateMirror.inverse (Shadow7.leaveClose (start k)) ++ (Dblk (start k) ++ R) := by
  obtain ⟨Z, hZ⟩ := suffix_after (start k)
  obtain ⟨V, hV⟩ := lowClose_split (start k) hL
  refine ⟨GateMirror.inverse V ++ GateMirror.inverse Z ++ CRTBarrel.barrel (start k) true ++
    GateMirror.inverse (CRTBarrel.before (start k)), ?_⟩
  show CRTBarrel.unleave k = _
  unfold CRTBarrel.unleave
  simp only [if_pos hk]
  rw [← hZ, hV]
  simp only [Dblk, inv_app, List.append_assoc]

end ECDSAAdd.Entrant.StairPacket.FredCut
end




-- MixedBase (VAST3 split of MainP1): declarations the Mixed20* modules need, moved verbatim

section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem split_ops (s : Nat) :
    Shadow7.leaveMoveOps s = CRTBarrel.beforeReference s ++ (Shadow7.leaveBarrel s ++ CRTBarrel.afterReference s) := by
  simp only [Shadow7.leaveMoveOps, CRTBarrel.beforeReference, CRTBarrel.afterReference, List.append_assoc]

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem forward_append (a b : List Gate) :
    GateMirror.forward (a ++ b) = GateMirror.forward a ++ GateMirror.forward b := by
  simp only [GateMirror.forward, List.map_append]

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem inverse_append (a b : List Gate) : inverse (a ++ b) = inverse b ++ inverse a := by
  simp only [inverse, List.map_append, List.reverse_append]

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem parts_counts (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (CRTBarrel.before (start j))) +
      toffoliCount (GateMirror.forward (CRTBarrel.afterPart (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3*Shadow7.lowsP (start j) + 97 ∧
    toffoliCount (inverse (CRTBarrel.afterPart (start j))) + toffoliCount (inverse (CRTBarrel.before (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 128 ∧
    measurementCount (GateMirror.forward (CRTBarrel.before (start j))) +
      measurementCount (GateMirror.forward (CRTBarrel.afterPart (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 88 ∧
    measurementCount (inverse (CRTBarrel.afterPart (start j))) +
      measurementCount (inverse (CRTBarrel.before (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 57 ∧
    gateSlots (GateMirror.forward (CRTBarrel.before (start j))) +
      gateSlots (GateMirror.forward (CRTBarrel.afterPart (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 10*Shadow7.lowsP (start j) + 650 + 3*Shadow7.wpP (start j + 15) ∧
    gateSlots (inverse (CRTBarrel.afterPart (start j))) + gateSlots (inverse (CRTBarrel.before (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 11*Shadow7.lowsP (start j) + 619 + 3*Shadow7.wpP (start j + 15) := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := ScanRowGordo.before5Row_counts j (by omega)
  dsimp only [CRTBarrel.before, CRTBarrel.afterPart] at *
  obtain ⟨t1, t2, m1, m2, s1, s2⟩ := Shadow7.leaveMove_counts j (by omega) (by omega)
  obtain ⟨b1, b2, c1, c2, d1, d2⟩ := (Shadow7.counts_leaveBarrel (start j)).programs
  rw [Shadow7.leaveMoveP, split_ops, forward_append, forward_append] at t1 m1 s1
  rw [Shadow7.leaveMoveInvP, split_ops, inverse_append, inverse_append] at t2 m2 s2
  simp only [toffoliCount_append, measurementCount_append, gateSlots_append] at t1 t2 m1 m2 s1 s2
  obtain ⟨f1,f2,g1,g2,h1,h2⟩ := DeadJoin.all_local_deltas57 j (by omega)
  obtain ⟨k1,k2,k3,k4,k5,k6⟩ := DeadJoin.after7K_counts j (by omega)
  obtain ⟨q1,q2,q3,q4,q5,q6⟩ := DeadJoin.after7S_counts j (by omega)
  have afterEq : DeadJoin.afterReference (start j) = CRTBarrel.afterReference (start j) := by rfl
  rw [afterEq] at f1 f2 g1 g2 h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · clear * - j t1 b1 f1 r1 k1 q1
    omega
  · clear * - j t2 b2 f2 r2 k2 q2
    omega
  · clear * - j m1 c1 g1 r3 k3 q3
    omega
  · clear * - j m2 c2 g2 r4 k4 q4
    omega
  · clear * - j s1 d1 h1 r5 k5 q5
    omega
  · clear * - j s2 d2 h2 r6 k6 q6
    omega

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-- The rebuilt leave and its mirror: the Shadow7 counts with the barrel stage replaced by the CRT barrel. -/
theorem leave_metrics (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    toffoliCount (CRTBarrel.leave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3*Shadow7.lowsP (start j) + 97 + CRTBarrel.barrelT (start j) false ∧
    toffoliCount (CRTBarrel.unleave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 128 + CRTBarrel.barrelT (start j) true ∧
    measurementCount (CRTBarrel.leave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 88 + CRTBarrel.barrelM (start j) false ∧
    measurementCount (CRTBarrel.unleave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 57 + CRTBarrel.barrelM (start j) true ∧
    gateSlots (CRTBarrel.leave j) = 6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 10*Shadow7.lowsP (start j) + 650 +
      3*Shadow7.wpP (start j + 15) + CRTBarrel.barrelSlots (start j) false ∧
    gateSlots (CRTBarrel.unleave j) = 6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 11*Shadow7.lowsP (start j) + 619 +
      3*Shadow7.wpP (start j + 15) + CRTBarrel.barrelSlots (start j) true := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := parts_counts j h0 h1
  obtain ⟨f1, f2, f3⟩ := CRTBarrel.barrel_metrics j h0 h1 false
  obtain ⟨g1, g2, g3⟩ := CRTBarrel.barrel_metrics j h0 h1 true
  simp only [CRTBarrel.leave, CRTBarrel.unleave, h1, ↓reduceIte, toffoliCount_append,
    measurementCount_append, gateSlots_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem barrel_box (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (mir : Bool) :
    ∀ q ∈ wires (CRTBarrel.barrel (start j) mir), leaveBox (start j) q := by
  obtain ⟨w1, w2⟩ := start_win7 j (Nat.zero_le _) (by omega)
  intro q hq
  rcases CRTBarrel.barrel_wires j h0 h1 mir q hq with ⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩ | ht
  · have bc := Shadow7.bank_cases w1 (by omega) hi
    have r := Shadow7.rail_win w1 (by omega)
    unfold leaveBox; ((try unfold Wire at *); omega)
  · have pc := Shadow7.pool_cases (i := 17+k) w1 (by omega)
    unfold leaveBox; ((try unfold Wire at *); omega)
  · have t : ∀ q ∈ tagsP, 1556 ≤ q ∧ q ≤ 1576 := by decide
    have := t q ht; unfold leaveBox; ((try unfold Wire at *); omega)

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem parts_box (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    AllW (leaveBox (start j)) (CRTBarrel.before (start j)) ∧ AllW (leaveBox (start j)) (CRTBarrel.afterPart (start j)) := by
  have a := Shadow7.allW_leaveMove (start j) (Shadow7.leaveOps_box j (by omega) (by omega))
  rw [split_ops, allW_append_iff, allW_append_iff] at a
  exact ⟨ScanRowGordo.before5Row_allW j h1 (DeadJoin.before5_allW j h1 (show AllW _ (DeadJoin.beforeAll (start j)) from FlagLeave.cut_allW (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 2 (DeadJoin.beforeScan (start j)) (DeadJoin.before_scan_allW _ a.1))),
    DeadJoin.after7S_allW j h1 (show AllW _ (DeadJoin.afterAll (start j)) from FlagLeave.cut_allW (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 1 (DeadJoin.afterShort (start j)) (DeadJoin.after_short_allW j h1 a.2.2))⟩

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem leave_eq (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    CRTBarrel.leave j = GateMirror.forward (CRTBarrel.before (start j)) ++ CRTBarrel.barrel (start j) false ++
      GateMirror.forward (CRTBarrel.afterPart (start j)) ∧
    CRTBarrel.unleave j = inverse (CRTBarrel.afterPart (start j)) ++ CRTBarrel.barrel (start j) true ++
      inverse (CRTBarrel.before (start j)) := by
  simp only [CRTBarrel.leave, CRTBarrel.unleave, h1, ↓reduceIte, and_self]

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-- `WindowCovered.leaveBox_dom` through block 22 (start 405), as `WindowCovered7.leaveBox_dom405`. -/
theorem cov_of_box {P : Program} {s : Nat} (lo : 45 ≤ s) (hi : s ≤ 405) (h : ∀ q ∈ wires P, leaveBox s q) :
    WindowCovered.CoveredW P := by
  intro q hq
  have b := h q hq
  rw [WindowCovered.dom_iff]; unfold leaveBox at b; omega

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem leave_cov (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    WindowCovered.CoveredW (CRTBarrel.leave j) ∧ WindowCovered.CoveredW (CRTBarrel.unleave j) := by
  obtain ⟨pb, pa⟩ := parts_box j h0 h1
  obtain ⟨bf, bi⟩ := allW_programs pb
  obtain ⟨af, ai⟩ := allW_programs pa
  obtain ⟨w1, w2⟩ := start_win7 j (Nat.zero_le _) (by omega)
  have cbf := cov_of_box w1 (by omega) bf
  have caf := cov_of_box w1 (by omega) af
  have cbi := cov_of_box w1 (by omega) bi
  have cai := cov_of_box w1 (by omega) ai
  have cb0 := cov_of_box w1 (by omega) (barrel_box j h0 h1 false)
  have cb1 := cov_of_box w1 (by omega) (barrel_box j h0 h1 true)
  rw [(leave_eq j h0 h1).1, (leave_eq j h0 h1).2]
  exact ⟨WindowCovered.appW (WindowCovered.appW cbf cb0) caf, WindowCovered.appW (WindowCovered.appW cai cb1) cbi⟩

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end

section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror HighBankJoin HighBankReassemble SkywalkNat IntegerHigh Shadow HighBankSum LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step
theorem dest_forward (gs : List Gate) : (GateMirror.forward gs).map LeaveReadoutFrame.destination = gs.map target := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [GateMirror.forward, List.map_cons] at ih ⊢
    rw [ih]; cases g <;> rfl

end ECDSAAdd.Entrant.StairPacket.LeaveJ7
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket
namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
open GateMirror Partial
structure Valid (s : State) (gs : List Gate) : Prop where
  physical : ∀ g ∈ gs, proper g = true
  prepared : Prepared s gs
  ready : Ready s gs

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket
namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
open GateMirror Partial
theorem Valid.tail {s : State} {g : Gate} {gs : List Gate} (v : Valid s (g::gs)) :
    Valid (transition g s) gs :=
  ⟨fun x hx => v.physical x (List.mem_cons_of_mem _ hx),v.prepared.2,v.ready.2⟩

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket
namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
open GateMirror Partial
theorem Valid.default_run {s : State} {gs : List Gate} (v : Valid s gs) (m : List Bool) :
    run (GateMirror.forward gs) m s = run (GateMirror.forward gs) [] s := by
  induction gs generalizing s m with
  | nil => rfl
  | cons g gs ih =>
    change run ([front g] ++ GateMirror.forward gs) m s = run ([front g] ++ GateMirror.forward gs) [] s
    simp only [run_append,run_take,List.drop_nil]
    rw [head_default g s v.prepared.1 (v.physical _ (List.mem_cons_self ..))]
    exact ih v.tail _

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket
namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
open GateMirror Partial
theorem Valid.parts {s : State} {a b : List Gate} (ok : Valid s (a++b)) :
    Valid s a ∧ Valid (run (GateMirror.forward a) [] s) b := by
  induction a generalizing s with
  | nil => exact ⟨⟨by simp,trivial,trivial⟩,ok⟩
  | cons g gs ih =>
    obtain ⟨left,right⟩ := ih ok.tail
    refine ⟨⟨fun x hx => ok.physical x (List.mem_append_left _ hx),⟨ok.prepared.1,left.prepared⟩,⟨ok.ready.1,left.ready⟩⟩,?_⟩
    change Valid (run ([front g]++GateMirror.forward gs) [] s) b
    simpa only [run_append,run_take,List.drop_nil] using right

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket
namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
open GateMirror Partial
theorem Valid.undo_run {s : State} {a : List Gate} (v : Valid s a) (m n : List Bool) :
    run (GateMirror.inverse a) n (run (GateMirror.forward a) m s) = s := invert a s v.physical v.prepared v.ready m n

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.LeaveSplice
end

section
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
theorem backward_sub : wires EnterProof17.backward ⊆ Finset.range 13 := by decide +kernel
end NativeJ7
end ECDSAAdd.Entrant.StairPacket
end
end

section
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
theorem enterInvCover (j : Fin 26) : wires (Shadow7.enterInvP j) ⊆ (EnterJ7.ports j).toFinset := by
  rw [EnterJ7.emittedInv j,renameProgram_support]
  intro q hq
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hq
  have lt:w<(EnterJ7.ports j).length:=Finset.mem_range.mp (backward_sub hw)
  rw [List.mem_toFinset,EnterJ7.map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem lt,Option.getD_some]
  exact List.getElem_mem lt

end NativeJ7
end ECDSAAdd.Entrant.StairPacket
end
end

section
section
namespace ECDSAAdd.Entrant.StairPacket.WindowCovered7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairPacket.WindowCovered
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP Shadow7.leaveP Shadow7.leaveInvP Shadow7.leaveMoveP Shadow7.leaveMoveInvP Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.exitLoadP Shadow7.exitRestoreP
/-- Routed ports of block `j` (dadon's `PartialSites.portsPass` decides, generic). -/
theorem ports_dom {j : Fin 26} (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) {a q : Nat} (ha : a < 15)
    (hq : q∈(IntegerPacket.ports (Shadow7.shape j) a).wires) : domainW (net j a q) = true := by
  have hj := j.isLt
  simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false] at hq
  rw [dom_iff]
  unfold net OB5.sig start
  split
  all_goals
    repeat' first | cases_type And | cases_type Or
    all_goals try simp only [Wire] at *
    all_goals omega

end ECDSAAdd.Entrant.StairPacket.WindowCovered7
end
end

section
section
namespace ECDSAAdd.Entrant.StairPacket.WindowPhysicalW7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.WindowPhysicalW
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1 ReducedWindowArchives.restore0 ReducedWindowArchives.restore1
/-- Every gate of the leave is proper (no control on its target): par-c1's segment lemmas, without the state
hypotheses of `leave_ready`. -/
theorem leave_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) : ∀ g ∈ Shadow7.leaveOps (start j), proper g = true := by
  obtain ⟨w1,w2⟩ := start_win7 j h0 h1
  rw [Shadow7.leaveOps_split, Shadow7.leaveMidOps_eq]
  exact proper_append (proper_append (Shadow7.head_ok j h0 h1).2
    (proper_append (proper_append (Shadow7.lowRest_ok w1 w2).2 (Shadow7.storeMapped_ok w1 w2).2) (Shadow7.lowClose_ok w1 w2).2)) (Shadow7.close_ok w1 w2).2

end ECDSAAdd.Entrant.StairPacket.WindowPhysicalW7
end
end

section
section
namespace ECDSAAdd.Entrant.StairPacket.WindowPhysicalW7
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant.StairPacket.Partial ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Entrant.StairPacket.GateMirror ECDSAAdd.Entrant.StairArchiveGates ECDSAAdd.Entrant.StairPacket.WindowPhysicalW
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1 ReducedWindowArchives.restore0 ReducedWindowArchives.restore1
/-- The move leave (`leaveMoveOps`): every gate is proper. -/
theorem leaveMove_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    ∀ g ∈ Shadow7.leaveMoveOps (start j), proper g = true := by
  obtain ⟨w1, w2⟩ := start_win7 j h0 h1
  exact Shadow7.leaveMove_proper_of w1 w2 (leave_proper j h0 h1)

end ECDSAAdd.Entrant.StairPacket.WindowPhysicalW7
end
end

section
section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Tail
open ECDSAAdd Arithmetic IntegerPacket TickCut.Receiver TickCut.Hosted TickCut.Static
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
theorem back_physical (p : IntegerPacket.Shape) (i n : Nat) (bound : i+n≤p.length) (hm : 1≤p.mid) :
    GatePhysical (backHigh p i n) := by
  induction n generalizing i with
  | zero => simp [backHigh,GatePhysical]
  | succ n ih =>
    have h := ih (i+1) (by omega)
    have hv := IntegerPacket.ok p ⟨i,by omega⟩
    have hn : 0<(IntegerPacket.ports p i).half.length := by simp [SkywalkIntegerLayout.half]
    have point : GatePhysical (receiverSelected p i) := by
      unfold receiverSelected
      split
      · exact ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_physical _ _ hv hn le_rfl
      · exact receiverHigh_physical p i (by omega) hm
    exact (gatePhysical_append _ _).mpr ⟨h,point⟩

end ECDSAAdd.Entrant.StairPacket.TickCut.Tail
end
end

section
section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Tail
open ECDSAAdd Arithmetic IntegerPacket TickCut.Receiver TickCut.Hosted TickCut.Static
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
theorem tail_physical (j : Fin 26) : GatePhysical (unroutedHigh j 1 14) := by
  have hm : 1≤(Shadow7.shape j).mid := by simp [Shadow7.shape]
  exact gatePhysical_rename _ (netInjective j) _ (back_physical (Shadow7.shape j) 1 14 (by simp [Shadow7.shape]) hm)

end ECDSAAdd.Entrant.StairPacket.TickCut.Tail
end
end

section
section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Tail
open ECDSAAdd Arithmetic IntegerPacket TickCut.Receiver TickCut.Hosted TickCut.Static
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
theorem tail_covered (j : Fin 26) (h0 : 0≤j.val) (h1 : j.val≤24) :
    WindowCovered.CoveredW (unroutedHigh j 1 14) := by
  have hm : 1≤(Shadow7.shape j).mid := by simp [Shadow7.shape]
  have all (a n : Nat) (bound : a+n≤15) :
      WindowCovered.CoveredW (renameProgram (windowNet j) (backHigh (Shadow7.shape j) a n)) := by
    induction n generalizing a with
    | zero => intro q hq; simp [backHigh,renameProgram,wires] at hq
    | succ n ih =>
      have ha : a<15 := by omega
      have hv := IntegerPacket.ok (Shadow7.shape j) ⟨a,ha⟩
      have hn : 0<(IntegerPacket.ports (Shadow7.shape j) a).half.length := by simp [SkywalkIntegerLayout.half]
      have sub : wires (receiverSelected (Shadow7.shape j) a) ⊆
          (IntegerPacket.ports (Shadow7.shape j) a).wires.toFinset := by
        unfold receiverSelected
        split
        · exact ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_support _ _ hv hn le_rfl
        · exact receiverHigh_support (Shadow7.shape j) a ha hm
      have point : WindowCovered.CoveredW (renameProgram (windowNet j)
          (receiverSelected (Shadow7.shape j) a)) := by
        intro q hq
        rw [renameProgram_support] at hq
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hq
        have mem := List.mem_toFinset.mp (sub hw)
        have dom := WindowCovered7.ports_dom h0 h1 ha mem
        rwa [Shadow7.stable ha mem] at dom
      have tail := ih (a+1) (by omega)
      simpa only [backHigh,renameProgram,List.map_append] using WindowCovered.appW tail point
  exact all 1 14 (by decide)

end ECDSAAdd.Entrant.StairPacket.TickCut.Tail
end
end

section
section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Tail
open ECDSAAdd Arithmetic IntegerPacket TickCut.Receiver TickCut.Hosted TickCut.Static
theorem selected14_eq (j : Fin 26) : selected j 1 14 = unroutedHigh j 1 14 := by
  rw [selected, if_pos (show (1:Nat)=1 ∧ (14:Nat)=14 from ⟨rfl,rfl⟩)]

end ECDSAAdd.Entrant.StairPacket.TickCut.Tail
end
end

section
section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Tail
open ECDSAAdd Arithmetic IntegerPacket TickCut.Receiver TickCut.Hosted TickCut.Static
theorem selected14_phys (j : Fin 26) : GatePhysical (selected j 1 14) := by
  rw [selected14_eq]; exact tail_physical j

end ECDSAAdd.Entrant.StairPacket.TickCut.Tail
end
end

section
section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Tail
open ECDSAAdd Arithmetic IntegerPacket TickCut.Receiver TickCut.Hosted TickCut.Static
theorem selected14_cov (j : Fin 26) (h : j.val ≤ 24) : WindowCovered.CoveredW (selected j 1 14) := by
  rw [selected14_eq]; exact tail_covered j (Nat.zero_le _) h

end ECDSAAdd.Entrant.StairPacket.TickCut.Tail
end
end

section
section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem parts_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.before (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPart (start j), proper g = true) := by
  have p := WindowPhysicalW7.leaveMove_proper j (by omega) (by omega)
  rw [split_ops] at p
  exact ⟨ScanRowGordo.before5Row_proper j h1 (DeadJoin.before5_proper j h1 (show Proper (DeadJoin.beforeAll (start j)) from FlagLeave.cut_proper (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 2 (DeadJoin.beforeScan (start j)) (DeadJoin.before_scan_proper _ (fun g hg => p g (List.mem_append_left _ hg))))),
    DeadJoin.after7S_proper j h1 (show Proper (DeadJoin.afterAll (start j)) from FlagLeave.cut_proper (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 1 (DeadJoin.afterShort (start j)) (DeadJoin.after_short_proper j h1 (fun g hg => p g (List.mem_append_right _ (List.mem_append_right _ hg)))))⟩

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end
end

section
section
namespace ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem leave_phys (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    GatePhysical (CRTBarrel.leave j) ∧ GatePhysical (CRTBarrel.unleave j) := by
  obtain ⟨pb, pa⟩ := parts_proper j h0 h1
  have b := physical_of_proper _ pb
  have a := physical_of_proper _ pa
  rw [(leave_eq j h0 h1).1, (leave_eq j h0 h1).2]
  exact ⟨WindowPhysicalW.appP (WindowPhysicalW.appP b.1 (CRTBarrel.barrel_phys j h0 h1 false)) a.1,
    WindowPhysicalW.appP (WindowPhysicalW.appP a.2 (CRTBarrel.barrel_phys j h0 h1 true)) b.2⟩

end ECDSAAdd.Entrant.StairPacket.CRTWindow
end
end
-- ==== end MixedBase ====
