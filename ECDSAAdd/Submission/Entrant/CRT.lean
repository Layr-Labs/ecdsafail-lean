import ECDSAAdd.Framework.Syntax
import ECDSAAdd.Submission.Entrant.Stair44Stock
import ECDSAAdd.Framework.Semantics
import ECDSAAdd.Framework.WireRenamePool

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
  (Shadow7.fix0P s h).take 54 ++ [.pop (s+30) (h+803) (s+h+48)] ++ (Shadow7.fix0P s h).drop 55

theorem fix0M_inverse (s h : Nat) : GateMirror.inverse (fix0M s h) =
    GateMirror.inverse (Shadow7.fix0P s h) := rfl

def lowerPairs (j : Fin 26) : List (Wire×Wire) :=
  (List.range 17).map (fun i => (Shadow7.a0P (start j) - 1 + i, Shadow7.b0P (start j) - 1 + i))

theorem fix0M_emitted : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    GateMirror.forward (fix0M (start j) (Shadow7.sbP (start j))) =
    scanM (Shadow7.a0P (start j)+16) (Shadow7.b0P (start j)+16) (start j+30)
      (Shadow7.e0P (start j)+5) (lowerPairs j) := by decide +kernel

theorem scanPairs_split (j : Fin 26) : scanPairs j = lowerPairs j ++
    [(Shadow7.a0P (start j)+16,Shadow7.b0P (start j)+16)] := by
  revert j
  decide +kernel

theorem physical_geometry : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    let a := Shadow7.a0P (start j)+16
    let b := Shadow7.b0P (start j)+16
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
    toffoliCount (GateMirror.forward (fix0M s h)) = 17 ∧
    measurementCount (GateMirror.forward (fix0M s h)) = 1 ∧
    Challenge.gateSlots (GateMirror.forward (fix0M s h)) = 75 := by
  simp [fix0M,Shadow7.fix0P,GateMirror.forward,GateMirror.front,GateMirror.erase,toffoliCount,measurementCount,Challenge.gateSlots,Challenge.instructionSlots]

end ECDSAAdd.Entrant.StairPacket.DeadScan

end

-- ==== CRT: merged by merge4.py from CRTBarrelData, CRTBarrel, CRTBitCount, CRTDomain, CRTResources, CRTBarrelMetrics, CRTLinear, CRTMeasurement, CRTPlacement, CRTShapeData, CRTPhysical, CRTBarrelChecks, CRTField, CRTFieldCases, CRTFieldRows, CRTMatrix, CRTFieldRun, CRTTriangle, CRTComponents, CRTCoordinates, CRTWindowRun, CRTBarrelRun, CRTPackedData, CRTPivots, CRTPacked, CRTBasisReceipt, CRTFastField, CRTPackedActions, CRTPrototype, CRTPrototypeReceipt, CRTPackedRun, CRTSlice, CRTTemplateAction, CRTBarrelCorrect ====

-- ==== begin CRTBarrelData ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

/-- Irreducible polynomial and multiplicity for each primary component. -/
def schedule : Nat → List (Nat × Nat)
  | 31 => [(257,1), (21,1), (11,1), (13,1), (19,1), (31,1), (37,1)]
  | 39 => [(257,2), (21,1), (11,1), (13,1), (19,1), (31,1), (37,1)]
  | 46 => [(257,2), (21,1), (11,1), (13,1), (19,1), (31,1), (73,1), (109,1)]
  | 54 => [(257,1), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (91,1), (109,1)]
  | 61 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (109,1)]
  | 69 => [(257,2), (21,1), (11,1), (13,1), (19,1), (31,1), (37,1), (67,1), (73,1), (91,1), (97,1), (109,1)]
  | 76 => [(257,2), (21,1), (11,1), (13,1), (19,1), (31,1), (67,1), (73,1), (87,1), (91,1), (97,1), (109,1), (117,1)]
  | 84 => [(257,1), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1)]
  | 91 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (117,1)]
  | 99 => [(257,1), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (41,1), (55,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1)]
  | 106 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,2), (37,1), (55,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1)]
  | 113 => [(257,2), (21,1), (11,1), (13,1), (19,1), (31,1), (37,1), (41,1), (55,1), (59,1), (61,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1)]
  | 114 => [(257,1), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (41,1), (47,1), (55,1), (59,1), (61,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1)]
  | 120 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,2), (37,1), (41,1), (47,1), (55,1), (59,1), (61,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (117,1)]
  | 121 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,2), (37,1), (41,1), (55,1), (59,1), (61,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1)]
  | 128 => [(257,2), (21,1), (11,2), (13,2), (19,1), (25,1), (31,1), (37,1), (41,1), (47,1), (55,1), (59,1), (61,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1)]
  | 30 => [(257,1), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1)]
  | 37 => [(257,1), (21,1), (11,1), (13,1), (19,1), (31,1), (37,1), (73,1)]
  | 38 => [(257,1), (21,1), (11,1), (13,1), (19,1), (31,1), (67,1), (73,1)]
  | 45 => [(257,2), (21,1), (11,1), (13,1), (19,1), (31,1), (37,1), (73,1)]
  | 53 => [(257,1), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1)]
  | 60 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (73,1), (313,1), (471,1)]
  | 68 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (87,1), (91,1), (97,1)]
  | 75 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1), (91,1), (313,1)]
  | 83 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1), (91,1), (313,1), (471,1)]
  | 90 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (313,1), (471,1)]
  | 98 => [(257,2), (21,1), (11,1), (13,1), (19,1), (31,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (313,1), (471,1)]
  | 105 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,1), (37,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1), (313,1)]
  | 112 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,2), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1), (313,1), (471,1)]
  | 119 => [(257,2), (21,1), (11,1), (13,1), (19,1), (31,1), (37,1), (41,1), (47,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1), (313,1), (471,1)]
  | 127 => [(257,2), (21,1), (11,1), (13,1), (19,1), (25,1), (31,2), (37,1), (41,1), (47,1), (67,1), (73,1), (87,1), (91,1), (97,1), (103,1), (109,1), (115,1), (117,1), (313,1), (471,1)]
  | _ => []

/-- Pivot donor and row-target mask for each binary elimination column. -/
def pivots : Nat → List (Nat × Nat)
  | 31 => [
      (31,71602432), (31,214807297), (31,358012161), (31,1073565447),
      (31,1200321537), (31,1532734483), (31,2116706581), (31,301241215),
      (31,844215297), (31,1667459074), (31,1729970437), (31,1576677898),
      (31,502220053), (14,645652287), (31,1452452715), (31,1407522711),
      (31,877014830), (31,254404325), (31,2121954675), (31,285384597),
      (31,570769194), (31,1137344084), (31,195938469), (31,456546799),
      (31,973175675), (31,2020556371), (31,1756607491), (29,634706949),
      (30,1269413898), (31,1407239191), (31,491136063)]
  | 39 => [
      (39,18330222592), (39,54990667777), (39,91651112961), (39,274832752647),
      (39,307282313217), (39,392380022803), (39,541876879381), (39,77117718655),
      (39,216119181313), (39,348745826563), (39,442872627461), (39,252991768335),
      (39,311982883089), (39,333638210355), (39,286564619605), (39,361947430911),
      (18,450146598913), (19,298963173378), (39,133976555524), (39,248827084808),
      (22,18987941909), (39,55673028671), (39,110171652222), (39,200959000727),
      (39,500778467769), (39,537700467570), (39,278677096051), (29,366726154901),
      (29,542832661337), (39,204023603393), (39,423820094885), (39,224259978991),
      (39,448519957982), (39,295744494524), (39,71790212867), (39,143580425734),
      (39,287160851468), (39,4550430491), (39,9100860982)]
  | 46 => [
      (46,1117841850368), (46,3353525551105), (46,5589209251841), (46,16767507169287),
      (46,18998979985409), (46,56965689245715), (46,62062988427285), (46,41308803760255),
      (46,2844639166465), (46,7255053238531), (46,11609787597061), (46,33753736677135),
      (46,38434112602385), (46,12342366769971), (46,32206761563477), (46,43809836597247),
      (18,4727934025729), (19,9455833448450), (46,17691802861572), (46,35364479696904),
      (22,62708330594325), (46,41888654491711), (46,36497134583934), (46,60863077089431),
      (46,58173599318457), (46,6550654681970), (46,67709663643251), (29,46838272297621),
      (29,4958059041625), (46,59045075558593), (46,41758585351589), (46,2388923496175),
      (46,4777846992350), (46,9555693984700), (46,54841213171459), (46,68194836994309),
      (46,18741929816586), (46,37483859633172), (46,45280905316392), (46,69671089705040),
      (42,57229614501851), (42,4508066226102), (46,11178305691866), (45,36742244184323),
      (45,36064529808816), (46,3849487541462)]
  | 54 => [
      (54,285942888042752), (54,857828664128257), (54,1429714440213761), (54,4289143320170247),
      (54,4861028853314561), (54,14583084516879379), (54,15826119666852117), (54,10496275647861631),
      (54,803001712358401), (54,1368027444766722), (54,2830411103027461), (54,5656971700744714),
      (54,12081137932256533), (14,5440718092623679), (54,3451574916655979), (54,12805145396320151),
      (54,15754885056573230), (54,7066711306659557), (54,11457047123621235), (54,6104696091746197),
      (54,11835558200688426), (54,16071291933720148), (23,10292787063670949), (24,10500786032972106),
      (25,11144999005004436), (54,9715243569126599), (54,12513385235023837), (54,15175080786923450),
      (54,2180673670225780), (54,10658166905448001), (54,3409118112338987), (54,6818236224677974),
      (54,13636472449355948), (54,11742647932685705), (54,17740966085532434), (54,5359230580176420),
      (54,4869918384912061), (54,9739836769824122), (40,7471209966256435), (54,2156292853897633),
      (54,5379514027699152), (54,14227989003183569), (54,4365358496541717), (45,5034454624056383),
      (45,12705800233583723), (54,7411176229539005), (54,5072742278440339), (54,10145484556880678),
      (54,13737279280615559), (54,16983111176073609), (53,9396301718025109), (54,15322642070144056),
      (53,12686451456776439), (54,8594453849461500)]
  | 61 => [
      (61,36600836273537024), (61,109802508820611073), (61,183004181367685121), (61,549012543982469127),
      (61,622214154336600065), (61,1866633968526032915), (61,2033577408390561813), (61,1353843087441592447),
      (61,93004561080713217), (61,237772766204330243), (61,380499675532493061), (61,1105708118416557839),
      (61,1259535140164534545), (61,404555252921209651), (61,1055491761584280917), (61,1435651317312749567),
      (18,154976768700448769), (19,309943916639551490), (61,579374403115024388), (61,1158748488603795464),
      (22,2055233829668716565), (61,1372719169163690047), (61,1196200040641462398), (61,1994517307737964695),
      (61,1906165351053853113), (61,214510128088613746), (61,2219100393213986419), (29,1534721786520078997),
      (29,162419747652703065), (61,1934800690035630273), (61,1368529333930782117), (61,1435501934416681802),
      (61,1211988085302755451), (61,1631915278627223065), (36,1936406904089139933), (37,265412089834747322),
      (61,530814421503798132), (61,1416685395134736193), (39,887935536545759019), (61,1469779033964380541),
      (42,774281326030521223), (42,573220012518505183), (61,2158095273297479791), (44,590557094452356839),
      (45,1181114188904713678), (46,1646718987010939804), (47,1992460631665227576), (48,129839982301310576),
      (61,2296297056877859834), (61,2180083678747824873), (61,1500080835337664315), (61,140035634818219167),
      (53,2098736644795198423), (54,918852760864675758), (61,1879078817298601570), (57,745101054550491105),
      (58,1490202109100982210), (61,644796723985678406), (61,1289593447971356812), (61,18217256010039677),
      (61,36434512020079354)]
  | 69 => [
      (69,9369774777202442240), (69,28109324331607326721), (69,46848873886012211201), (69,140546621657916047367),
      (69,159286171208110047233), (69,477858513094863224851), (69,524035346840126816277), (69,350097622833250369663),
      (69,24046027595243126785), (69,56929101089045676291), (69,96421079454165762309), (69,282334465203080267535),
      (69,314783507507694338321), (69,104954652421135733555), (69,273357904423175918933), (69,363347822351245869055),
      (18,43131652480148176897), (19,81795733528614797314), (69,149778646710425223172), (69,299557293401724420104),
      (22,529240609735234093077), (69,356383575867777810495), (69,311539209132130041982), (69,513474216257025147031),
      (69,484154764285139550649), (69,55193761317334942578), (69,570614162173564487283), (29,395554751591455459989),
      (29,42429556124382991193), (69,492693127086995480769), (69,346085833454419013029), (69,18816427595018516207),
      (69,37513509799911714270), (69,75027018998528007100), (69,459639407189932095235), (69,140046021579118702086),
      (69,280006791424666164236), (69,123626587142242307867), (69,247124788159999909430), (40,53108750285160811375),
      (41,92434233910754219742), (69,277230546281434266466), (43,533613974420313734571), (44,287805723930311523158),
      (69,390959181408632429328), (46,306880135853706987121), (47,438516203007173233890), (48,475840492209114257860),
      (69,506926556637022773471), (69,37344056023176919205), (69,74688112046353838410), (69,291158072570798008761),
      (69,577848574311244485490), (55,451773773217873108015), (55,264998746376064769722), (69,380253630318872796048),
      (69,511800046383573079675), (59,534420971249699750611), (59,355945887043659925365), (69,224094355587261566009),
      (62,512120178017156108781), (69,263089553069905421948), (69,148727588879965214899), (69,432719078860473855091),
      (65,260520579476863300757), (66,521041158953726601514), (69,324516408152928553650), (69,411420960727520605093),
      (69,123032003124880033467)]
  | 76 => [
      (76,1199331170253485965312), (76,3597993510760457895937), (76,5996655851267429826561), (76,17989967553802168893447),
      (76,20388629894304929939457), (76,61165889682883539107859), (76,38827000732950640787477), (76,25492617146331152187519),
      (76,74425362286620645326849), (76,61504621932728993906947), (76,48597098513871078162693), (76,17092952011519987287823),
      (76,21880212217383400571153), (76,63961856654284830217011), (76,56034522078674364470613), (76,5449062593282860613631),
      (18,14253362754081158070273), (19,28497790366501578473474), (76,56967956629306638073860), (76,25391541704788302364680),
      (22,27031500268121253806101), (76,69187080848055002398783), (76,1803669428402028150910), (76,25819375309392948166807),
      (76,75345579162182748799417), (76,13096894218092812567410), (76,4683003937908682065523), (29,6694065452322523515541),
      (29,10710185809242140250969), (76,21055442596393931317441), (76,63263525030803529887141), (76,49622483397709724104431),
      (76,39034549748182942707166), (76,65082591668474361076668), (76,18628153422590218057475), (76,21231807241227323627781),
      (76,53728535634184381007113), (76,56332208220393565850130), (76,13781922657264152586549), (76,27065451498581512376938),
      (42,14303346368886562167237), (43,28606304513411496162186), (44,57185223974495091713812), (44,49057847982678546690297),
      (76,16689050120130906476811), (76,68670081634490189424515), (76,55011196980720229394093), (48,8402121856809363631095),
      (76,38532485060797914050883), (76,60105081512820448168305), (76,20542404795388188955362), (76,41075707815929462138308),
      (53,55780947104209202950355), (54,51324339666096016810406), (55,42438506675604057146188), (56,60610609752619350853272),
      (57,23223179844032860458288), (76,35675844920906133436150), (59,35146289228149373300253), (60,68761498698180853816378),
      (76,45460792538188302846547), (76,35769656659236326385281), (76,71539313318472652770562), (76,15962113225012785355268),
      (65,6543761359754268388093), (76,17870657827046165741319), (76,32765347845894732174579), (76,46469816698901086021871),
      (76,70508392604171357278686), (76,48505916387568423564139), (76,14500182344906545051137), (76,29000364689813090102274),
      (76,58000729379626180204548), (74,22477201543056539092489), (75,44954403086113078184978), (76,15863704966140110188069)]
  | 84 => [
      (84,307028779584667781468416), (84,921086338754003344405249), (84,1535143897923338907342081), (84,4605431693770016721555207),
      (84,5219489252939352041550849), (84,15658467758818054081588243), (84,9855047140713937777615125), (84,6467707430298962657317759),
      (84,19243851643357963293406209), (84,3499586831751408114690050), (84,12477279063621727007097093), (84,11958567519757183575798282),
      (84,1287644776442159757739285), (14,3854918508989453593993023), (84,8477573529408208316312427), (84,13476246554058856897779607),
      (84,13873677214431211516473134), (84,14041482203263632203704037), (84,12271728447463442903364979), (84,4048666433761729128341397),
      (84,8097294797188433180966698), (84,15828858123317623866949204), (23,8375425572243803948828837), (24,16516872069292080940945738),
      (25,7714553168196547370230420), (84,9622008527206185950518471), (84,16989650917630884169320413), (84,1637920181676419481210810),
      (84,3268428211577948150177652), (84,11648097481788849773028929), (84,3391586752137791387554859), (84,6783144122791613809993814),
      (84,13566245029041203372708012), (84,8659168978730487247801737), (84,17085495652533166996986642), (84,1744016758776247139448356),
      (84,18786840196515103918192317), (84,2817063078894114784537978), (40,11439552422334644018790707), (84,2423115620615630655756705),
      (84,18687817476452012526627792), (84,17745636555989320735335889), (84,1337565748179579648928789), (84,3840588965448310121903167),
      (84,7449737584350705381173374), (84,14665979720433235778654460), (84,5339838453142274265665005), (84,10461045516528915831757786),
      (84,6957840319191551651037307), (84,13915680638383103302074614), (84,12411402223241739483546092), (52,16698216569637680839574201),
      (53,8303327175808258615903602), (84,11763640291376813544819589), (84,10767890260064242361686565), (84,15580876385229862108902474),
      (84,5996261783247384874018964), (84,11603858739312241743417640), (84,17465277177359324453642832), (84,2228133026122722203878560),
      (64,12778558223216807292573637), (84,3568547466881244533241935), (63,18153139249514864413402971), (84,14866935165759746582686189),
      (84,9897379829796845125438670), (84,5689580640490086700204271), (67,7015582006113465407729339), (84,17336132101474692837389261),
      (69,5004016199544980817447201), (84,4454490564786976468160308), (84,3693344170245890002097993), (84,7386688340491780004195986),
      (84,8472262877873011849549871), (84,16944525755746023699099742), (84,1550285836800716974809276), (84,3100571673601433949618552),
      (84,6201143347202867899237104), (84,9758763627275451775278911), (84,18383170267421255752410273), (84,14645736566906790629813731),
      (84,12459896559252368312811367), (82,5932198005700775167367791), (83,11864396011401550334735582), (84,5951932474169336486962092)]
  | 91 => [
      (91,39299683786837622632022016), (91,117899051360512867896066049), (91,196498418934188113160110081), (91,589495256802564339359744007),
      (91,668094624376239522430844929), (91,2004283873128710072808767507), (91,1272269905098236017843961877), (91,835235114112455186326945919),
      (91,2438900236983881330960171009), (91,2015838207264350842684113155), (91,1592556271024372605530669317), (91,559974541509338095375091471),
      (91,717300349906938975301468433), (91,2095922052773846254711149363), (91,1836194336088568054519502165), (91,178518621608311253981167615),
      (18,467246772428632682650664961), (19,933535052035185796238016514), (91,1867055960529271600797712388), (91,831773814885756153502892040),
      (22,885645649272808405157085205), (91,2267015845806116739928227903), (91,59188036412985648097394814), (91,845971070480605246702157975),
      (91,2468640615485003520118686137), (91,428592386686277864029029234), (91,153296196609828396576474739), (29,218946723056796818749065877),
      (29,351160841680393440102781785), (91,690234476164633815897153729), (91,2072774366336294179093966245), (91,1222965988921143210585807690),
      (91,793863635428702867525599355), (91,104908833764381986905634329), (36,1811960388471537086517271261), (37,1590861871605473846850860474),
      (91,1517287894329220776195222388), (91,1958345836204315680282863425), (39,943269213732425313772732203), (91,1571669844282785151534203261),
      (42,515692328442682813362504583), (42,1518378457666698355577682655), (91,268241597472287759613331567), (44,2253626169661187772289607399),
      (45,58391132514287119341374926), (46,104985588303375797482003356), (47,188451500078297764708693816), (48,311347108641399114560859760),
      (91,1237824421605192571526239226), (91,1081093292463124556101718761), (91,1765677357526679733003892539), (91,2013858394073886581099101343),
      (53,267367777740230895016405975), (54,479724770579274541708203950), (91,224885646206529973275809378), (58,940692727193115872095911905),
      (59,1881380748160649939042467778), (91,2360852941828326666532863911), (91,1043920016916045894946750666), (91,2023162502482709129046720916),
      (91,548646214850389410689859025), (64,290493147931955113608657399), (65,569227603321564810635211758), (66,1117025107543867171290671068),
      (91,2168489638099543205498703800), (91,197603250313100097544232816), (91,2079163122910968025131665583), (72,1247701255350548747078985489),
      (72,2069855899830265155016183330), (72,1226800314932598443932621892), (72,2432203587331314525401987208), (72,350528449645195803647439120),
      (91,700169094391612113994703392), (74,867313285846109714790793585), (91,1733682098395645500538847970), (78,2301494130545880201826649269),
      (91,1824598954071544480672385928), (91,290514085541608624015382002), (91,970845947951518930224901555), (80,308826645776552682556372023),
      (91,374907384200572743233461337), (91,1060411194806382760700339435), (91,2120822389612765521400678870), (91,471881773446011752421334825),
      (91,943763546892023504842669650), (91,2329851495478631402173943411), (91,1906925895432453912658530965), (91,1689529200375585602824465241),
      (89,865752855467174539476867265), (90,1731505710934349078953734530), (91,391516555983798059138843700)]
  | 99 => [
      (99,10060719049430392651905274112), (99,30182157148291177955715822337), (99,50303595247151963259526370561), (99,150910785741455889778578640647),
      (99,171032223840316675082146247681), (99,513096671520949972677217201171), (99,322930184706914308469876744469), (99,211933837076036414465983681407),
      (99,630582530649553732343417648129), (99,114674461302830136757835753474), (99,408855480356756742012174942469), (99,391858340487403401757322785290),
      (99,42193544034456693803062347029), (14,126317969702566396214382419775), (99,277793129411648165762739383147), (99,441589647083400611155721656215),
      (99,454612654962481969243521167150), (99,460111288836542676085018060517), (99,402119997766482091880639788403), (99,132666701701504349697181130645),
      (99,265332155914270583591415398186), (99,518680022984871897184263110228), (23,274445945151284946156512987301), (24,541224863966562927425187713354),
      (25,252790478215464492636661293716), (99,315293975419492304428948004039), (99,556716881268928825784453236701), (99,53671368513172925877407584186),
      (99,107099855636986215325553663860), (99,381684858283257015328961144385), (99,111135514694051176712422904875), (99,290036235155172184010868653181),
      (33,491860646060200066007274532049), (99,446154876458306613003720237400), (99,90900183288290534985055254467), (99,127838417065744664329955475943),
      (99,238808636080507221394557567950), (99,602356954739132869886619977339), (99,133072252028243130976531713270), (99,265905136096530978228437916140),
      (41,560416189957666799828968845887), (42,58420020488144898435604898942), (43,99304685287323111592948320508), (44,198505402601673881241651614200),
      (99,337580998594085796684651162380), (46,577165071957871015004134996653), (47,15182577452022260927402931546), (99,32984087980625771836189777902),
      (49,603437048024346500303092598129), (50,129606437507793764601595464418), (99,247215200560590454560641318768), (52,276854153888163456760726824119),
      (99,453763834993238359702346558937), (54,521000050640206582141282090757), (99,434240992312320813117086480228), (56,100116086268356758753945612231),
      (99,38031966610818029917860351555), (59,240711158017780133621585816783), (60,481353218369182918594404833694), (99,370337620043316719654193130146),
      (99,228962864005822180817888583701), (99,68681391101966191870859097467), (99,119633998396079435766137252598), (99,71044671093961212637620418909),
      (99,142089286109820441198203925178), (99,273496492376756781010082061353), (99,544362306091930144858966571090), (99,248984148361673553313891578020),
      (99,497968278424176985507907952968), (72,319827866153142235691088167839), (73,530476545947863284856772003646), (74,316173902319996406811319406204),
      (99,16806867338503242199075541275), (99,26546354335539362242818777654), (99,45445043936196580326446285932), (80,225040359780710363842210551743),
      (99,443116249030348300837585661822), (78,452712908072710194254711316220), (99,20431570465523402838034211588), (99,625748506008051617647802535755),
      (99,132801688342762969109760621466), (99,71187501662390771490162097693), (99,142375003324781542980324195386), (99,284750006649563085960648390772),
      (99,557584840421004386775392710888), (99,55493007213723258237135086032), (99,618703627208976335712247320767), (99,608594517220892258869976199777),
      (99,157512360813499002426302063810), (92,440993064060693915209858572071), (91,513202936540706799743190529994), (99,333457668143281967397519194423),
      (99,227988764325812376974883646000), (99,163335725534321068018870019283), (99,326671451068642136037740038566), (98,322121541938341876905367959455),
      (98,321377547107090955382097415149), (98,332733448079990492468488139529), (99,22893983894374398770316214977)]
  | 106 => [
      (106,1287772038327090259315601244160), (106,3863316114981270778496559546369), (106,6438860191635451296578006220801), (106,19316580574906353892482677145607),
      (106,21892124651560534408302907621377), (106,65676373954681596483005030596627), (106,41335063642485031585507417587733), (106,27127531145732661033292346359935),
      (106,80714563923142877672423004897281), (106,66197272830101766620374668083459), (106,52333501485664863031400885125381), (106,18826096993590635081503111644943),
      (106,23640530517717500715378640224529), (106,68615120634430558230169235166003), (106,60064147776347110158176108221781), (106,5875057397804752655322779189247),
      (18,15431230509593647034793469411329), (19,30861970270862388333536913915906), (106,61723933300231737149248610762756), (106,27482285691842778017666915368968),
      (22,27945622964877405710523480473621), (106,73654480813604601774095348990015), (106,1515832321785907204693631565950), (106,27073606833507455325840875126935),
      (106,81026896606363943642544152838585), (106,14084367741979631190692599038834), (106,4297387306548806894380251285107), (29,7143600145346038290300720712341),
      (29,12579001784422728921909311378265), (106,22141144743218987387127714619585), (106,67652531068803358235482250374565), (106,40220432802831228607874164513610),
      (106,25799084267161217206809947406459), (106,2965348295286580106880064665113), (36,58704861232424692179316875254493), (37,52728774765733708593693014996410),
      (106,50690593785883093718392465746804), (106,64048483388862455709323419805505), (106,31005603446051336962233803570987), (40,51490911928773396483481964609917),
      (41,48130248141014467417375792104186), (106,3363108818006079023114288134181), (106,69446998340779780179127084676665), (106,60321696600371946813328108460619),
      (106,55656023834276205423113466098838), (106,44395501151016270033856165996844), (106,64705481318637149748622938919512), (48,68248148784303914995748857276925),
      (106,39812092467165847150603496248314), (51,25948889855484842492951610400243), (51,45551375438455132211674830665199), (106,71045212953927084855309299164631),
      (54,43717642548046250095309723647363), (106,24748260051144253642439720093317), (106,49159369989425032385588545031434), (106,78587166016917586860711215573661),
      (106,19291192176154530535783892145466), (106,23365227133718148660585536486383), (106,51795814392087373089130314835525), (62,17312542622797830965893642775247),
      (63,33733311475226347563401982367134), (106,35696357744619081772576568905081), (106,36947813290106637860665164256888), (106,73895193858833531140029633441008),
      (65,17916968992083546618505295103277), (66,35822636945605335683485436873306), (67,71634439573573148786221480416436), (106,77704542025954622525735080574428),
      (106,2192573392322600776970332110485), (106,8614381606908277139277673114327), (106,10346269957176474547994329743955), (106,31035841235526436484838421300981),
      (75,72062950721638968862484158615481), (74,16898157911290177286475987688737), (106,53679942199822365151075136190376), (106,68832804364500115356074130163763),
      (106,75943801253371401662932641818013), (106,3948656473774529823269281155898), (106,7896824541517935336351981016692), (106,15782817107692123595298594696424),
      (106,31534995199411934028793436068304), (106,60911022970310164858162799489952), (83,39285342618631664939863881773437), (106,76332006075907516491040264479482),
      (106,24823409198996912552795208070281), (106,11746461234799805190586576748385), (87,77536711669691604079506242283697), (106,37842967082745827778425097432992),
      (93,10171167480326548634817905698451), (90,20336145260456670368261315775782), (106,40659911120520486933773640309324), (106,16792569496556736124196567106913),
      (106,80271217139736067781689737933692), (106,58993317383727065297834792755014), (95,53837438648788404351914928701159), (96,43024696685937109227497993928142),
      (106,28885124673080650938947688334930), (106,62151725866018271385383289031135), (106,29229656714919337658513837659070), (106,58459313429838675317027675318140),
      (101,28989395346455715514930642323577), (102,57978790692911431029861284647154), (106,21686694690620366531559981562223), (106,65806168782586549043780195973799),
      (106,14275443616682935611222564941325), (106,28550887233365871222445129882650)]
  | 113 => [
      (113,164834820905867553208210962841600), (113,494504462717602659624632888524801), (113,824174104529337766041054814208001), (113,2472522313588013298123164322037767),
      (113,2802191955399748404539582036836353), (113,8406575866199244522038047156207635), (113,5290888146238084147288091723366421), (113,3472323986653780458388992849805439),
      (113,10331464182162288667641900457852929), (113,8473250922253026072284181557084419), (113,6698688190165102515569035737039109), (113,2409740415179601313376762821609231),
      (113,3025987906267840352942269111795985), (113,8782735441207111338388246111654707), (113,7688210915372429664968195412661589), (113,752007346919008002740476499165183),
      (18,1975197505227986496124577912193025), (19,3950332194670385792314409043361794), (113,7900663462429662199682383441035268), (113,3517732568555875811946582048243720),
      (22,3577039739504307794514992234299413), (113,9427773544141389197777001603072063), (113,194026537188596118571736247435390), (113,3465421674688954088682772615331991),
      (113,10371442765614584593928596290601401), (113,1802799070973392962860324534485874), (113,550065575238247169623842291385971), (29,914380818604292794772101193337493),
      (29,1610112228406109034083974221730649), (113,2834066527132030189123698061025473), (113,8659523976806829769587685522238885), (113,6959486619037671323005458521765615),
      (113,5357261075933491870799044680838622), (113,8929670106745636689525654796819388), (113,2481502080646640406691994971649795), (113,4959655233489532873674724475891206),
      (113,9886351545598009614962636972022796), (113,383356236702537106961408791809819), (113,766712464666299230940751753125430), (40,1290682324938920410600475290733423),
      (113,1592790463218030516810581311266225), (42,4500849649974249301951011001312979), (43,8877468622217329001604079646100902), (113,9497884471938335558593473894115047),
      (113,8673032405621117995245825574485495), (113,5173013867725468228994180927814638), (113,10069679604662398997222550328244188), (113,9803534099385333672999945070137935),
      (113,2241657868019976942180535517488286), (51,5647688384395097778347907170259029), (113,3179438129890802801433415540535551), (113,6325917344050528841063478279528958),
      (53,1998945206302536187297795210466045), (113,6808355598919975376336234690708816), (113,8410329783258267192409431227137447), (113,5305996222183340234478007096084201),
      (113,1050398869184103546055313914556533), (113,10247236753295705283256596104781133), (113,1830711048388199001391457877703322), (60,6047655235624699218280658038425747),
      (113,10310457507245553983900701990326566), (113,2770024831219745141542362684341241), (113,5538663160979274754764138723440626), (113,7992680263557597826780010682314724),
      (113,3814822277123099423585366584713160), (113,8755750693772217524024399117565301), (113,6947172477029218924417633192396703), (113,5423903643333408988034295566470974),
      (113,9062938848320101161833403372871292), (113,4461730126853636937652747090672888), (113,8919479976667368113293658169833968), (113,211623912409139592491063000992669),
      (113,622511075545400560284418450758823), (113,1038592246867128926903767079795022), (75,2194352291601928691178096960141569), (113,3577959376316138124849242828406942),
      (113,9630918329814510888861190146755135), (78,5546623100474699541283614062406723), (113,8007031040368196285238020156938374), (82,8700289178871994652972954471521615),
      (113,4412635778301295322792038711246679), (82,1173263847807278893198038692636200), (113,1738281591985225875399367350733209), (113,7672784516569252135985632023446061),
      (113,787561094608951000821715880216183), (87,6362555163092371515587719405473475), (88,9640797573585689500827569596341638), (113,3885220753582419933507185151681703),
      (113,1751817639764742591070122545183873), (113,7905987879860456203364220328234189), (113,3528441443509369506225386596374938), (113,6930949722702315847845835083690804),
      (113,752599265796284358144703427949375), (113,1386871270877514928093448966071934), (113,9958439336524899182146378224598997), (113,5548544033456655955754667886726275),
      (113,3134110705134213623601513893844357), (113,6268221410268427247203027787688714), (113,9339428006761259943831370091419156), (100,531355406429595858890593948027809),
      (113,221602778631017140701490868009834), (113,1207270185886380064740802772249143), (113,2414540371772760129481605544498286), (106,3498219711296883758652430346180229),
      (105,8891690768810747770872250796344790), (113,2690585997665218374962715830253045), (113,2492423524906695211985667822183824), (108,3082130523070145399165956537619977),
      (109,6164261046140290798331913075239954), (113,6817595626087184012849448518733357), (112,5507744172577473598524468642217573), (112,7448818946194958625834618908760715),
      (113,3546327550097907726593586286793559)]
  | 114 => [
      (114,329669641811735106416420770320640), (114,989008925435205319249262310961921), (114,1648348209058675532082103851603201), (114,4945044627176026596246311554338567),
      (114,5604383910799496809079152852038657), (114,16813151732398489044078426429565971), (114,10581776292476168294579772095881493), (114,6944647973307560916800135723520895),
      (114,20662928364324577335263419222307841), (114,3757652747971137377389796823099394), (114,13397376380330205031132128142508293), (114,12840414101091234815151390877954570),
      (114,1382598050921077085920123734148373), (14,4139187231213695883667128176074559), (114,9102725264560887375896546515266411), (114,14470009555628870637487867673515927),
      (114,14896747477810608359312159500807982), (114,15076926712595831329754945369532133), (114,13176668086812084971136392671950195), (114,4347222481354894895008818214903701),
      (114,8694404084998818109780647962033962), (114,16996106993168282074063262976736852), (23,8993044730717304931283162763217061), (24,17734856342456333670911590262346058),
      (25,8283438390164340102584813456138900), (114,10331552986545923939647048425938119), (114,18242498765420259433229504001017821), (114,1758703403439650184443771351863226),
      (114,3509448069512764270267376389070708), (114,12507049436225766933027078444623425), (114,3641688545494669370516111071990827), (114,9503907353564682178499837729700989),
      (33,16117289650100634764419493211581649), (114,14619602991785790933094214453076312), (114,2978617205990703718585602815997891), (114,4189009250410321129439784891744743),
      (114,7825281387086060351047338147775438), (114,19738032692891905560429147858175611), (114,4360511554461470887658493128543478), (114,8713179499611127397777555908073964),
      (114,18363717712532826507432044595687999), (114,1914307231355532392202792572118142), (114,3254015927495004381534817990920444), (114,6504625032451648936541590824260088),
      (114,8599944277749633711100674151766323), (114,2064787413147776692205018982041765), (114,4129572988478022100419705033822538), (114,8030927995827117733489391688163988),
      (114,17818790741557558484453415488097677), (114,8149735091475485549808859831933722), (114,14760316570293863463262314471482763), (52,824815668876518613166273555738269),
      (53,1581541538863404059359047116414266), (54,2745663313607703537475999400245876), (114,17490730702735199830209895421455127), (114,583914461026697645343265726130965),
      (114,757110127574139761072885083395626), (114,1752064883704729251702904215062337), (114,3501990007049563755973446970936962), (114,6612036430477427386565763702791428),
      (61,19849385448502724534992558678133785), (62,4971876986139220859765268435015730), (63,9942128534556213246833237106569316), (114,14765375964874670456971314919688350),
      (114,10727136671196645897200345308374495), (114,17882428233336257584765316374023102), (67,2173667922542894235186657919128171), (114,3281949389642489426915925680649917),
      (114,6014645892684154296499212920274705), (114,19139509544885488126326361594291685), (114,10091901291718777131614983905333261), (114,20183769797369326314486749779173402),
      (114,7552140987233597965527193049127923), (74,18759622857676116339288073771740181), (114,5215314113290531193276592071738329), (114,9973379899149348380156882904560525),
      (114,12110912177777474287724151890742461), (114,20652118410517815837088776262195578), (114,14849382185900161649218400965279785), (114,827620697416729826557452873056379),
      (114,1569040554390733524957059273883894), (114,2727360476740274909592841155838444), (83,17336779724283981667269101539934749), (114,4889726023795861805887833911691234),
      (86,17065637347999212771847139328084451), (87,9702745171311805934632406427014086), (88,18830881904288713333966260858595212), (89,338723326870239721353056961056536),
      (114,4395052627518130168105462027173703), (114,8717611486335708467312831339789966), (91,18484641742242015390424231196364099), (114,1672696377725282787546768429816454),
      (93,16464338922892578429474798928017487), (94,5745178374491005573254294319952030), (95,11241897231337278183815234811650364), (114,17081626309921134394906636592208126),
      (97,14811420587504750199426465443928681), (98,15420083850052418184483868174824658), (99,14203521222709553703725003482294692), (100,11445877414365398015424118076658504),
      (101,16725902309220688221968271762368144), (114,9487652864025365595496051970491393), (114,5369204394820305908207247401990117), (114,15679027200941301048661470809282607),
      (114,7019162877500597588586240075346014), (114,18829402208735660564712335859504985), (114,339170746752247549361729352740530), (114,678341493504495098723458705481060),
      (114,6614894211765788937996702471267231), (114,13229788423531577875993404942534462), (114,15874589214152512857731553078226403), (114,232716530720223529910707369277529),
      (114,465433061440447059821414738555058), (114,930866122880894119642829477110116)]
  | 120 => [
      (120,21098857075951122977852139999657984), (120,63296571227853368933556969754787841), (120,105494285379755614889260699998289921), (120,316482856139266844667784848653352967),
      (120,358680570291169090623486317680656385), (120,1076041710873501606451072032693813267), (120,683044704260241538592186543290515477), (120,448413437447978942176921941907275903),
      (120,1309374594506554982581557477919490049), (120,1082244896778457992778553252294623491), (120,854997137636173160285909946663698693), (120,300634042796899317915529112981341967),
      (120,385097693032458317237236342903079185), (120,1125239583953607230830918066449355571), (120,985799327825101930707180879477019989), (120,95841455191834888246369952643121151),
      (18,250851200842814211995797102932525057), (19,501187814770098081946274804157382658), (120,1002368036284388082384777061645418500), (120,446555166575436489171963836448636936),
      (22,475477387433926459056201707506958357), (120,1217094864656383826516925309301751871), (120,31776335088531114808912358760382590), (120,454177260134539253007963299859857559),
      (120,1325341338635673553167821916459303353), (120,230098785516517791887456215898391410), (120,82300268880047674107855661081757299), (29,117546126886911342303140151672769173),
      (29,188528041331636825410230393381655385), (120,370566812712349743752583108353925313), (120,1112812264425187523990131500437040549), (120,656574865817076868329670692305558346),
      (120,426202293956243290349829221428887675), (120,56322501259940982473658797706163737), (36,972788826266586780097064119343569629), (37,854087463874856766197616931832444346),
      (120,814587735595089031514753426906114932), (120,1051378915094413748946011370584631105), (120,506413803038051827575060397666959147), (40,843783822662999056426306303800082813),
      (41,788326732251151297281697214510859002), (120,58020890448277541865697188210309157), (120,1125220709532601182122029163524814393), (120,985859406881963281286561045404359243),
      (120,911998405220676874410661085846516886), (120,735229535216716340990735325207357740), (120,1075677178413382568019914491333759576), (120,1114287083049719612903682472239000061),
      (120,879575278634042878906559715697211911), (51,417131339065162537676551270691905011), (120,613799850818825431869519418854298139), (120,563070621398205843958471512364535864),
      (120,509008850440033284425634631609162165), (120,1011724996371527819992162801020187498), (120,454212606374142174725305498273081044), (120,873552223964163100153328678215404968),
      (120,687396794521441510428610804411636560), (120,681821308315950773348671235877943043), (120,452394647103162565755900839649597701), (60,227202018261990386460149191218103561),
      (120,1090460609733159483434071944015691025), (120,63725046814882070601515277474493753), (120,361472892408677097668398818117850457), (120,1073500323137156523333971687399604203),
      (66,52796439689832292976223402469354127), (66,483716254840035901797520006067825352), (120,1277248569496315213415649511802022470), (68,745155919618141330742315495726705555),
      (120,344416817197519664985287613101063349), (70,72552334049822281104113871179780857), (120,1112408798580002308466202382181397204), (120,543258380685947068998603886179144355),
      (120,841360877233717454045804198349099543), (120,783333794810307973564909446109570094), (75,485340883445276352939756375690353227), (76,970552545757491940744897681197708438),
      (77,867732165256897133294142217443240236), (120,1020779196378841673969685885490950952), (79,671442834058332301200073256363553785), (80,1114417078021554216956837609965742066),
      (81,662383096663456033608848102821449700), (120,1088267205333264931808480751947564071), (120,1127595042814179033987168700475245453), (120,531172670550729704143920524913018650),
      (120,1217894386273152525434042320423326321), (120,40654234258282029256971696919487714), (120,1184534361475857465283750026087563095), (120,146765596936226466289771954018844334),
      (120,293531193872452932579543908037688668), (120,586928050205662733547796587811961528), (120,367701374083306736805931959351329799), (92,1067731093582452535978995523142011913),
      (93,411612103455903444173794878307670034), (94,791096870099622642396057310578290724), (95,1187127895336917135356864073794740296), (120,1016690961202063742488125941916021939),
      (98,945315323176113075303365861944896897), (98,45945715401186853929448888667862659), (120,132121091766728209890308795698125701), (100,774966787594152174333098772092385165),
      (101,1321472513412771933010855705699086106), (120,1302061903339136337169520136771935649), (120,515559795593960912636804301324189153), (106,846756496644168271705553304473994787),
      (107,773502893666696772980859290614303814), (120,320418406550566572970700841076319054), (107,1124038480864776243775507519650087103), (120,647764280866852661287594284737706499),
      (120,358509103571360995714599339126666695), (120,717018207142721991429198678253333390), (111,683855128736784343667844604194284251), (120,750014302752033207118917799837266033),
      (113,615646552297897654409655279593947705), (120,320832032004161772153935093471494596), (120,1169050443357209091235731087261107651), (120,1284685690999027848720397715342954053),
      (118,1058932655480502530619524074592344393), (120,380114575309490587785151041196535320), (120,169687846798695458745814498781784929), (120,45591902732937997502813079558919099)]
  | 121 => [
      (121,42197714151902093621301730327199744), (121,126593142455706280863905740737413121), (121,210988570759510468106508651635998721), (121,632965712278531404319528703566479367),
      (121,717361140582335591562129353248866305), (121,2152083421747006597641737429236580371), (121,1354467365436949541705749241513705493), (121,888914940583367797347584269278707839),
      (121,2644854830633545898916324138280091649), (121,2169152236096774674504752812187910403), (121,1714864176682266243985669932175327493), (121,616893546285977936224450206097999631),
      (121,774652904004567130353220230165102865), (121,2248380272949020502627390375560680243), (121,1968181994335341994231855215180846421), (121,192513880811266048701564726227730431),
      (18,505650561338364543007891112210989057), (19,1011285041835618762832488706570977282), (121,2022569846381993523118686869108293636), (121,900539537550304207858324923538735112),
      (22,915722173313102795395837580986875925), (121,2413510027300195634630911969470644287), (121,49670793520280606354363322533281918), (121,887147948720372246702789662606819479),
      (121,2655089347997333656045722234695254457), (121,461516562169188598492244875041440626), (121,140816787260991275423705732998170227), (29,234081489562698955461657573935352469),
      (29,412188730471963912725497413820289881), (121,725521030945799728415666124869411009), (121,2216838138062548421014448593342655909), (121,1317943142083173705813871736650390346),
      (121,845384393266338730293421614204321915), (121,97168532939950613376333285424870937), (36,1923640892864092360931823308569631453), (37,1727816491523562175744619539523024314),
      (121,1661029377175817235223751936132213620), (121,2098740703686244972356149997391931201), (121,1015991613720210291559764678995443499), (40,1687254202082046708186751325981344125),
      (41,1577131971084761938969077187644687098), (121,110202349748423199928238323425376293), (121,2275639241630671908652320830554535481), (121,1976621354200988006331948043514845771),
      (121,1823736589001562804889631287702008982), (121,1454751781716501104223455886368729388), (121,2120269211849102058465501778437001816), (121,2236355339364070652401079442695088637),
      (121,1773396546139649630058866442062248455), (51,850293222784527284403888563405594099), (121,1210813374371831235493963574095204891), (121,1158603191581722303994053722288017464),
      (53,1005688115234452556828481116717128117), (54,2011179583453013277755115156490564458), (121,906620166509865441588536342901188308), (121,992311136955082857711515602597282211),
      (121,1913035432410415088247998818211267398), (59,1793136356453010496649234206273298939), (121,352403843157690766233382233365029389), (121,2144689070454919371764575370648455148),
      (121,457880617463457392068734716049844687), (121,915757036208464069298304703841883038), (63,177252498927740680737746951690849541), (64,354504921103198925781916859635997194),
      (65,700558180397107286227410486592549908), (121,2508877884766041260587256135439305523), (121,2373604622910400284800460360273086303), (69,1250626012387619620081843671619871177),
      (70,2500410224704090496575937460235158418), (121,1964236844871115770832982580667409791), (121,2364353245479905681015090952397483027), (72,1122776404880358566035813566851774959),
      (121,1347047622074447288825555865397595413), (74,1031579687230118726755890523123486747), (121,1690530956938626337391266660431441965), (76,544707286725828675551555525154197623),
      (121,1630406550086506602145382007015002287), (78,2268594492748056260530070549970153769), (121,157801519710101598512805672738046652), (121,1713261110943271903869221845456688643),
      (121,1640012484953770202003912517906148358), (84,781231605406043749974079097160257039), (121,1314910769026928798834529869100467218), (121,226702756643485118943960373178257448),
      (121,1488325154371934651029496300684654163), (121,1796855660568914406390238809839043321), (121,363799974603512503390036761153439499), (121,2453200826142754580302124915082726639),
      (121,1675998155357610963034827638756940583), (121,1565846191379241221855164540262168142), (121,2645208412001487838534490053969996956), (92,2442262733766552886542206851854467347),
      (121,2475166907983276232428709826929525557), (94,2375071771314536931695616389895980921), (95,305537431723261413369127921979559666), (96,610233143447971282415662033030749668),
      (121,799699974511959656704918539427193866), (98,453510617393155128890839995308959667), (121,835834413854593693396530377065221990), (121,2276415668667867499221050359695652377),
      (121,2472283926993088157907798592497980749), (121,156621113309748388856913257413880474), (121,260670220926831647974955239494407476), (121,1821572541837803542185207207117237433),
      (121,358919935636733444090050668243056075), (121,686037053014941068955352046469639062), (121,1361040475205495629200076788239685420), (121,2212586821167261297350598624174648920),
      (121,1309795527213626017582899450817240240), (113,2232834985037666115344919732392411893), (121,1298368886369087377286236703960565226), (121,1403614508207885303321658456717692478),
      (121,2298383924279357499047328273171815548), (121,2041381725866768982326756286624989159), (121,2373663314537289101054806235640169923), (121,1366332313703480295689725738547055535),
      (121,838224372745228939467265228271230193), (121,1676448745490457878934530456542460386), (120,1538313361540607867390165825886339465), (121,1980603205961706881243797816144179551),
      (121,993515294105287652274031320460562810)]
  | 128 => [
      (128,5401307411443467983526637900393414656), (128,16203922234330403950579913702270763009), (128,27006537057217339917633189501967073281), (128,81019611171652019752899568508783755271),
      (128,91822225994538955719952840324503830529), (128,275466677983616844498180938619117371411), (128,173371822775929541338394986016642498581), (128,113781112394671078060853423696359129215),
      (128,338541418321093875060955860536667734017), (128,277651486220387158336959530175976898819), (128,219502614615330079230068787485648093445), (128,78962373924605175836534833352319698703),
      (128,99155571712584592685322278777097617681), (128,287792674937474624335947554787170652979), (128,251927295274923775261445239081178305877), (128,24641776743842054233479947666482757631),
      (18,64723271851310661505309442661799952385), (19,129444485354959201642437601123393601538), (128,258888940336895170958844125246350426116), (128,115269060806438938605850382748352512008),
      (22,117212438184077157810630071218145132565), (128,308929283494425041232813568125728391231), (128,6357861570595917613472249375987990654), (25,113554937436207647578008134686059462807),
      (128,339851436543658707974148220827012235705), (128,59074119957656140607091376604228748146), (28,45184100467341259192509159523649389825), (28,90259953432376327545110877714994301442),
      (128,171463790688596760424015835557429253124), (128,155388733659608608086716258469760809229), (128,310777467315359533421860685495532155418), (128,205590138898058099304462358759294086947),
      (128,163941901798758684384134177102001870161), (128,321154556762067415166137138988785347234), (128,73291791162109167607257035685482222916), (128,24095183346772256138839734370845114329),
      (37,117175522974336020792575288899083004643), (128,308926551587320085543320238838143762213), (128,314531060959797784486209150020327096687), (128,17615266298753276418064713075602850526),
      (42,99941132656673872899693199486717039563), (128,193344494065719123656241401603196266390), (128,59413735988001137084630745029406096241), (128,303911977970242151039455087664416500229),
      (47,138993733666288214497388799506197928345), (48,277985662198054029730644384088736445234), (128,40983256347194460748186922185549627389), (48,109054231714152567052067619754889455203),
      (128,204240384387758903521425450125070578492), (128,29871051893200567832808951228844739805), (128,58292936078250613734108241587464051130), (52,145202053988018107464633426836937254419),
      (128,184742971213786852709657221247739658066), (128,150936367623324495320825447481009018001), (128,96942595703385241837635819263503233429), (128,193775453746521337328794446585778135850),
      (128,329064875678420530311225235327431460436), (128,80025879129500309044549078996164250792), (128,264565047379735370288964639290991652497), (62,300863064859361485771705668570788424419),
      (63,31379579164156070136298189291265775046), (128,268866253151614979974562213919576670575), (128,95348804131770494201878162879586992862), (128,181254088062076887398846860410196788668),
      (128,309855834497916387848787766166135170809), (128,8159050774956860550545397119427923442), (128,303447399482556320723993335343243374831), (128,37929369050252175277126965812454842846),
      (128,75823020494941991005570657838394688444), (70,208946502780033287869422227726693477491), (71,316871059583831480263978992747336784102), (128,165679241129699020655464734060626134361),
      (128,142968467710199980245705104016114882317), (128,239669966503061765239565821000058210523), (128,288433847628941201757774180318345312119), (128,135456250470075584093419543470474555118),
      (128,270911963773209321474630202712965832156), (128,116336995349837123770122941259389554963), (128,223616809757199343060142485737190629926), (128,176025645381478021559682658864323183692),
      (83,302599204546529065184144609345465189465), (84,27231645869762968341852515011583215794), (85,54345136872715957476004092974573949284), (128,108688306351622989487521726798591959752),
      (128,217376612282346365618014160131481683344), (128,197023243370964339965164403532443454240), (90,103737910107206989835624034739018182865), (91,206348473078632047399937078291904946594),
      (128,168046403231693513101072742602432815846), (128,128681251808123980316705354326651577454), (91,190818355299825203743704817448734619661), (128,115697592930963915752560810872885776824),
      (93,311744837921966815301353072003368758119), (94,8306344044727253174412938920740542158), (95,15059522009235672382771269179751837084), (128,31439527775174881177496148954221710838),
      (97,261559066128399440315801442155062126149), (128,181866731621874579465454019156593996279), (128,123527023677113899758664982276012460321), (128,246944502059958476845370225447829148226),
      (128,88592143195389707626012284972642926567), (128,137355129866037679363767258268046992557), (128,59413273478418608784452601782444593721), (128,250292705193019216307486815015758135057),
      (128,97925587229781627157898518724862027073), (128,195795357268334004918790334614184938114), (128,326589648238885136462914518306945799428), (108,21518626567941433075699698647741354191),
      (109,43037253135882866151399397295482708382), (128,106277294448573920558167419130007787621), (128,308760841337435145047974866165764784807), (128,314695809773274620823365364513372309481),
      (128,17946741485487940110979481297786114002), (128,35893482970975880221958962595572228004), (128,65390056212236852805568353713545297736), (128,130780112424473705611136707427090595472),
      (128,64654868393527304782596149728067313699), (128,129309736787054609565192299456134627398), (128,258619473574109219130384598912269254796), (121,135854056604165285111021439646851850555),
      (128,332956185825425328595949460902863446613), (128,149343920558792269196313126520982816178), (125,216641678868267488342236440835441569525), (124,67858080956852644668819242523516236575),
      (128,313607869226544950240962026265142934484), (128,264843718506063290390903994689491681123), (128,25811235327356160024698964480205777895), (128,51622470654712320049397928960411555790)]
  | 30 => [
      (30,71602432), (30,214807297), (30,358012161), (30,1073565447),
      (30,973829121), (30,878423059), (30,552231189), (30,494179199),
      (30,668054529), (30,904095746), (30,811417861), (30,481964554),
      (30,518997269), (14,624680767), (30,684895083), (30,1051006871),
      (30,122040110), (30,824829669), (30,670725491), (30,302161813),
      (30,574963498), (30,1053458004), (23,1018022053), (24,89887050),
      (25,179774100), (30,702028999), (30,165611485), (30,331222970),
      (30,662445940), (30,475735617)]
  | 37 => [
      (37,2219086080), (37,6657258241), (37,11095430401), (37,33285820167),
      (37,37707543553), (37,111054400531), (37,62246248725), (37,77610652543),
      (37,80301110273), (37,8109910018), (37,76891898117), (37,33788932618),
      (37,127203755285), (14,9235586879), (37,110974118763), (37,76569450391),
      (37,33089269550), (37,107628586725), (37,4269438323), (37,6727835541),
      (37,13455671082), (37,26907147860), (37,40998127781), (37,114273180143),
      (37,104052390779), (37,126574607955), (37,100540855299), (29,127336242181),
      (30,136560883722), (37,55094330391), (37,133635122239), (37,120259863663),
      (37,2149330097), (37,4298660194), (37,8597320388), (37,17194640776),
      (37,34389281552)]
  | 38 => [
      (38,4366569728), (38,13099709185), (38,21832848641), (38,65498074887),
      (38,74214765569), (38,222522223635), (38,121771811093), (38,158543942527),
      (38,159825114113), (38,14686578690), (38,154201309445), (38,67746017802),
      (38,256388318485), (14,20912529215), (38,219153607531), (38,151999813527),
      (38,67650334510), (38,215539640037), (38,8497296755), (38,12968959893),
      (38,25937919786), (38,51871645268), (38,84887324837), (38,228962228719),
      (38,207668476795), (38,250994441811), (29,198117143555), (30,91291609094),
      (31,182583218188), (38,164421532701), (38,23900387386), (38,244813915247),
      (35,34917178565), (36,69834357130), (37,139668714260), (38,4459521576),
      (38,8919043152), (38,17838086304)]
  | 45 => [
      (45,568086036480), (45,1704258109441), (45,2840430182401), (45,8521169960967),
      (45,9653131149313), (45,28429926531091), (45,15935039668245), (45,19868327018623),
      (45,20557084295169), (45,21239466754307), (45,19684326113541), (45,24442247579407),
      (45,33847087530257), (45,8030219604787), (45,10182169269589), (45,30048761380863),
      (18,10895507062785), (19,21189684101122), (45,2882755624964), (45,5746385223688),
      (22,1118499569685), (45,3354207911999), (45,6707241418878), (45,12295586906263),
      (45,32386615673273), (45,34072805114738), (45,20619642209907), (29,21257447082645),
      (29,18135018705753), (45,24393279414465), (45,34508680555941), (45,6271573931759),
      (45,12543147863518), (45,24485000305596), (45,31407871604483), (45,32579173445126),
      (45,34921777126412), (45,7701131824923), (45,15402263649846), (45,2347731823),
      (45,4695463646), (45,9390927292), (45,18781854584), (45,37563709168),
      (45,75127418336)]
  | 53 => [
      (53,142972016693504), (53,428916050080513), (53,714860083467521), (53,2144580249931527),
      (53,2430524040377345), (53,7291538939554835), (53,343837380337941), (53,925587421303679),
      (53,1489198973563905), (53,2822266863970306), (53,4864026578075909), (53,2708706432791050),
      (53,6323711723390229), (14,4936508259426111), (53,8697194568919915), (53,4440675112523671),
      (53,8760372974989102), (53,1517708049508069), (53,7463450166588787), (53,1132535933476757),
      (53,2265071837593386), (53,4530143578717780), (23,2576708665198757), (24,5151319440200010),
      (25,4374037823693460), (53,1265321689750727), (53,1015355130447837), (53,2028576735891386),
      (53,4057153471782772), (53,4980212623943233), (53,1427630655362091), (53,4282311071759485),
      (33,7739591573023953), (53,988861738688856), (53,445961955096515), (53,8816522049520103),
      (53,6112361263203278), (53,8935587172091515), (53,5908487833980150), (40,8366693162719243),
      (53,5095236050299386), (42,841357176339433), (53,2130161182968891), (44,3889557328094111),
      (53,8520644731875564), (46,369908393198969), (53,6759394886748341), (53,6852115672522465),
      (49,695009487840035), (50,1390018975680070), (51,2780037951360140), (52,5560075902720280),
      (53,77067272300059)]
  | 60 => [
      (60,4521485021544448), (60,13564455064633345), (60,22607425107722241), (60,67822275202580487),
      (60,76865183052726273), (60,230595026133712915), (60,384309142092840981), (60,1152913934535295103),
      (60,964765824180355073), (60,780399896453644547), (60,147924928711360773), (60,433782818787297039),
      (60,724867649466597649), (60,248476003945616179), (60,402866189557372245), (60,1061105155212017663),
      (18,1056609563703508993), (19,13574130785320962), (60,27128745145925636), (60,54257172665597960),
      (22,1101183467078877205), (60,917539772084191295), (60,293880875504763006), (60,248830118021496983),
      (60,404214050692071865), (60,804912138076423026), (60,594678890680747635), (29,410348276694715029),
      (29,226050959453262681), (60,1010665839814320321), (60,183204671897562533), (60,362044334172461898),
      (60,972929518412628091), (60,143522056147547673), (36,316584383816981213), (37,633149251302569402),
      (60,932627372461747060), (60,866737441589782337), (60,1003012072776236843), (60,819158421390721405),
      (60,447140693568552401), (60,894281387137104802), (60,410338142996526916), (60,820676285993053832),
      (47,954632993510870195), (47,512446415095109990), (47,1020811443027915468), (60,87342122753746328),
      (51,682433594362264445), (60,616087386109538204), (51,151115352933874979), (60,230121690969727776),
      (60,804979323874232187), (60,3488416143722893), (60,6976832287445786), (60,13953664574891572),
      (60,27907329149783144), (60,55814658299566288), (60,111629316599132576), (60,223258633198265152)]
  | 68 => [
      (68,4684887397766332416), (68,14054662193298997249), (68,23424436988831662081), (68,70273310966374400007),
      (68,79643085699714121729), (68,238929256576117899283), (68,240819229844463222805), (68,282617288604320465023),
      (68,179147092432675733505), (68,50835055697368908035), (68,133993979515616100613), (68,180271988232364492559),
      (68,37979935418360070417), (68,111919211745468683059), (68,188165229089649923413), (68,116369464616313389055),
      (18,199621266837637169153), (19,256280267103990710274), (68,70574875065079300100), (68,141149749812532346888),
      (22,112323202191114698773), (68,188649146308290871359), (68,229364052030845223038), (68,198085604372175585431),
      (68,145221842447260778937), (68,290442717324289114994), (68,255642996157199877747), (29,261505562231319104149),
      (29,177187943850373092185), (68,123321732669726859457), (68,154233632867773410725), (68,165503732028686392138),
      (68,171733107062332850299), (68,193272309840833394201), (36,226826886861020519133), (37,15487165963730793914),
      (68,30878630297941011316), (68,274686161583960057665), (39,151343065987832446763), (40,155903845350173245014),
      (68,10301661428121535226), (43,177986050509270186021), (43,185366183321658029251), (68,240065488061298339087),
      (45,142422936469718715325), (68,158228499968051961031), (47,274280061681412731443), (68,200002107991498388252),
      (49,125441777705609130093), (68,270431101016483230929), (52,260529372009576855829), (68,82899032672650785322),
      (68,51161956636005166955), (54,59112241538004075415), (55,114405430591997970222), (68,244718458627175069903),
      (57,220417178931989789563), (68,294989787531213436662), (59,72180846067034988641), (68,213655379761453635157),
      (68,231707147324258290891), (68,25304122897914730902), (63,178318478664844312357), (68,41504752740403118447),
      (66,222898766305603747323), (68,109144029023133366343), (68,21518474568119612722), (68,84545076915523151633)]
  | 75 => [
      (75,149916396435163643904), (75,449749189305490931713), (75,749581982175818219521), (75,2248745946527334072327),
      (75,2548578739335468417025), (75,7645736209511921483795), (75,12576155794620853321749), (75,37673100034913185497215),
      (75,8389038102456651022337), (75,10628732893360574890243), (75,31884136479201733902597), (75,11966809630071634790159),
      (75,35895236795659169366289), (75,6532893829152335139635), (75,17236907726460775896405), (75,23056010662173223124991),
      (18,23211311139469028229121), (19,527123013927930691586), (75,930230423883442290692), (75,1860460847449258328072),
      (22,19384755396497866293269), (75,27877717663870040866879), (75,9700832904689101963390), (75,9585366293976001740951),
      (75,28406505331943980728761), (75,27445763128873213625202), (75,1687321965767177733747), (29,4383681274406088542869),
      (29,7293327685108452889433), (75,15604637695316609540289), (75,25595829614838725045669), (75,14740852391189594954570),
      (75,1215814793188616044667), (75,32895599334419559331353), (36,11095383153028189706973), (37,22188960344188984079802),
      (75,3201725458353471318900), (75,17201672468639589951297), (39,26979070999351670177579), (75,33517366292316252504445),
      (42,4153129166558646797191), (42,16770356936474392230623), (75,25348344740520411039855), (44,21535759140066614273767),
      (45,4088467992005272063438), (46,7971684993943087192988), (47,15943330018439481472824), (48,31886660036878962945648),
      (75,2441481884037757457402), (75,23774484759949439406825), (75,32195968405853084333883), (75,6535619699686806158495),
      (53,36824754269124615269335), (54,30029876332953782048686), (75,36511804653172511430242), (58,11048183073385434071009),
      (59,21964933095245687586754), (75,30666281538408190885799), (75,26886352214801200021706), (75,12599571657082680836500),
      (75,19828466762559961447889), (64,23927345505388748126711), (65,18487474445431890080750), (66,36974948890863780161500),
      (75,30304901303330761199544), (75,24159036317011448405872), (75,2411738219834297436335), (75,11595313378910283360017),
      (75,23190626757820566720034), (75,30841435381569350645111), (73,9931994897930175464413), (74,19863989795860350928826),
      (75,13148173632999871586813), (74,27373616707529555705895), (75,4673703773333016194784)]
  | 83 => [
      (83,37928848259392325353472), (83,113786544778176976060417), (83,189644241296961626767361), (83,568932723890884759715847),
      (83,644790420409607217479681), (83,1934371261220327168671763), (83,3223785364145979598635029), (83,9671300725088989421437055),
      (83,8093080456775289256869889), (83,6546383945184949550645507), (83,1240809956093830908608773), (83,3638744268473959158908687),
      (83,6080524334868805042897169), (83,2084374146291796229165875), (83,3379561843529648168047957), (83,8901104998457106224873471),
      (18,8863481367071444868268033), (19,113863918602799415820290), (83,227603821601626412548100), (83,455207643202935198842888),
      (22,9237444129958045323427861), (83,7697000885844173867909183), (83,2465331403996904613085310), (83,2087426618756619895767191),
      (83,3390731441135131372880313), (83,6752095634735247997928306), (83,4988506327876112523396723), (29,3442266480803507804113557),
      (29,1896239920832966538367833), (83,8478085374997720832483521), (83,1536753104133125193428389), (83,3037055401427762531720010),
      (83,8161465097191935545311355), (83,1204042487086091572327961), (36,2655620613560029509376733), (37,5311239421158191623419322),
      (83,7823440621090485945199476), (83,7270756590156414638188353), (39,8413901944575841569701675), (83,6871504033487562521936253),
      (42,306384584070215940473735), (42,4361347521176547988830943), (83,5049946282513822918412399), (44,1948261284150881861461735),
      (45,3857539518013635766439374), (46,7714873785037204075944860), (47,3000478947192055256528696), (48,6000957894384110513057392),
      (83,5442607670149869043635194), (83,3197204761248351023010537), (83,9552486797871057835145019), (83,4653344238843417696435359),
      (53,6157011716068184812219351), (54,5583532860187656553355182), (83,300964327693872643397218), (58,7793508146842560746242017),
      (59,2855384822817032815804354), (83,748465986934594263367591), (83,6675978360095261660905674), (83,6926144102578243273687444),
      (83,6555583679054148937203153), (64,6899692944563592179268087), (65,7083147732818421129769966), (66,6119382978826966815401948),
      (83,5659365748883947855925176), (83,9582228797645173360926576), (83,531316784301234561370287), (83,2391668020745211471062801),
      (83,4783336041490422942125602), (83,7171059557480472913753463), (73,8925759914555820338922461), (74,586547967740217776572346),
      (83,3035462722669572808352253), (74,2898572438292273845633063), (83,5822629210668735919468256), (83,2066746550658519592295849),
      (83,4133493101317039184591698), (83,8266986202634078369183396), (83,3176141856731235290034401), (83,6352283713462470580068802),
      (82,5515381987206661971484205), (83,6131926575634282586071539), (83,4413996103107730736021602)]
  | 90 => [
      (90,4854892577182572398837760), (90,14564677731547717196513281), (90,24274462885912861994188801), (90,72823388657738585861980167),
      (90,82533173812103668466712577), (90,247599521436310482375671827), (90,412655381487638410877272085), (90,1237935894684091188927201407),
      (90,1035913838520447133099032577), (90,837954173281851125903851779), (90,158835159757868956261810437), (90,465765120442085084321548047),
      (90,778315394114570097491247377), (90,266802602580949884635124531), (90,432582534799726841454466389), (90,1139343341598535465559883775),
      (18,1134539007249828181584379905), (19,14571413211066573650395138), (90,29142384436474004398669828), (90,58256139526145293946978312),
      (22,1182389478931060932600987669), (90,985207733060593372584935487), (90,315565876327902126488289406), (90,267182839249213517781729431),
      (90,434004809611399500333121977), (90,864250615501467192843699058), (90,638532088145163441241523827), (29,440600891280067461343677077),
      (29,242728633815822896945763161), (90,1085197875049840884364419265), (90,196698229013455585684057509), (90,388730616978302255036554058),
      (90,1044669393713607264335167611), (90,154110786517993380795627033), (36,339927972180051097615391453), (37,679848127495864953099892154),
      (90,1001389944635250918971108212), (90,930661534741412452507674433), (39,1076973606693351535977529131), (40,519037522071384311080353366),
      (90,918768875813520633256936186), (43,998852114906033875350747173), (43,401389530493895990709155011), (90,919514354037925132319026447),
      (45,946604111724355260507769789), (90,708313219656411282005089479), (47,233072672042093020934697523), (90,241126003504863152226661148),
      (49,245826159334514060089159789), (90,261783770965264260845991121), (52,280515618013648060385392917), (90,561030797867584774267859498),
      (90,802991838204921466847686507), (54,353433772606412959910118295), (55,706860162696143951989409582), (90,446828200144343022472378575),
      (57,699628554735187789042105211), (90,1196327431123930851195123446), (59,454577135857214370775146593), (90,103479954654976400257226325),
      (90,564819170038676419395226827), (90,1124972203882105878717471126), (63,1004333011837642612901019429), (90,652395856556909764733698415),
      (66,98441789156951391669976571), (90,569194024874031665207965767), (90,675766533146448287259948338), (90,306144315227696889612068625),
      (90,509704043860298213290267333), (70,907470469930817190732658511), (71,780572674919798772438199966), (72,724568682666274155979726140),
      (73,1226260556807032536453855864), (90,683575720578622977541418991), (75,706822289800809669667575227), (76,1176695118957152021092739958),
      (77,240187905227932244799084268), (90,245184670546410559041013241), (90,499501910135960518132619495), (90,999003820271921036265238990),
      (90,378246192177839548361086627), (90,756492384355679096722173254), (83,1136186336734191985966133171), (90,9263539149798156882304870),
      (90,1132194786056882658838811007), (87,1090607361798126228778446055), (90,1116349067768131214569117655), (90,9478322173470709149797712),
      (89,874153595217624576662765607), (90,592866505587082040467511680)]
  | 98 => [
      (98,1242852499758734959407333376), (98,3728557499276204878222000129), (98,6214262498793674797036666881), (98,18642787496381024390989414407),
      (98,21128492495898494305593196545), (98,63385477487695482885528879123), (98,105638876367267047756370346005), (98,316909747903816046409810116735),
      (98,265193220110415896623487188993), (98,214512863417596779195071922435), (98,40659965795880356851573063941), (98,119238051751777068246405744399),
      (98,199248620990437871554301853969), (98,68300091040976021710574916403), (98,110739453562897009360871167317), (98,291673347695780854844731916287),
      (18,290438011640985645196399345665), (19,3729999422612570765969063938), (98,7459998817601037835419254788), (98,14916595742000234357332115464),
      (22,302691065334495070431589236757), (98,252211438947692489473232142399), (98,80781370004784125627676360830), (98,68397915015628018540323733655),
      (98,111109562300246369234992038329), (98,221248466962362857488806708082), (98,163463164043505487737351505523), (29,112795851125593779302187731605),
      (29,62138415179118683791098975065), (98,277808572452739295861736022209), (98,50355959890111007527962766757), (98,149553268915786242073526515439),
      (98,297903581082947811555367939550), (98,68642969264740425188360772540), (98,226457403506048627109370771203), (98,16150567342462734593772017925),
      (98,214125961489621471915134027017), (98,177999420175560232792547396114), (98,297787192569665395993863235893), (98,68247182049813311542996193898),
      (42,108191465101761270895880772037), (43,216382929520604786702879961994), (44,172911107003754423467684161300), (44,36727435195355823034299166969),
      (98,49227847101568118718863167755), (98,94174729477049455808176269187), (98,26411221532248057849708258989), (48,79223638403793331376399117303),
      (98,133168440445026285998277030211), (98,289537576009844201505353632113), (98,7413843484276337856169906914), (98,13323782778681700329350768068),
      (53,170028407981527717969158844627), (54,244735432375743690899095511462), (55,115579122429397751024186737484), (56,231158127436334331226374375064),
      (57,202160252470396582056987135280), (98,306262406778444280815967696630), (59,198153503246697730765154184733), (60,187095040001940524082553478202),
      (98,255594837716851212686576912979), (98,154574184441398635267842811521), (98,307644465163196671842351140098), (98,48587976655121622384050346500),
      (98,252422769516650542761964874493), (98,81662157369182272262778934778), (68,90603660165154241821810262281), (69,181207320330308483643620524562),
      (98,69516025186842749980485365465), (98,250986712787184048327398578335), (71,309124138907587191330507666451), (98,273463366849899501557111544885),
      (73,221687386943281494290903196767), (74,219299390968763034163812223166), (75,224435155141155280770075955580), (98,54277902260444038373609614977),
      (98,114393772118265066677234549351), (98,228787544236530133354469098702), (98,207477350614464241562423331228), (98,189461021651129390941951890232),
      (98,78280743957528062315896339069), (98,156561487915056124631792678138), (83,48098203754781389934353757689), (98,131635302041545899713230921227),
      (98,300134800900778951601973037551), (98,64241564790988244172625286110), (98,267458806956173885976781669793), (98,127635340987457661511751469890),
      (98,255270681974915323023502939780), (98,93355570710657493406001016072), (98,213291637282917043278669742977), (95,41920556367300203022896268419),
      (96,83841112734600406045792536838), (97,167682225469200812091585073676), (98,207229906071713207953457101971), (98,243338290099422459518479918382),
      (97,203268402797687803098957199353), (98,1583936660760008225202873774)]
  | 105 => [
      (105,160971504790886273359518171136), (105,482914514372658820078554513409), (105,804857523954431366797590855681), (105,2414572571863294100392651980807),
      (105,2736515581445066647049495379969), (105,8209546744335199932654002372627), (105,13549520173601665973315403055125), (105,40459346341543821271973867225215),
      (105,9031199834259994243773360308225), (105,11538146950550357123826079170819), (105,34328780076251383028485661655301), (105,12871732048001429401290294429455),
      (105,38551059893099885066406613549329), (105,7106092208744383890030516704051), (105,18498246491935004268524649911637), (105,24730661425930560735448148180991),
      (18,24907782151568052095519439454209), (19,535646260770864128285478486018), (105,1071292507398187156579278651396), (105,1955152239584224528883314065416),
      (22,20812359873590532627337421586453), (105,29933645513202462420854040887359), (105,10302621736857851982828105760894), (105,10194082940172529456899681616023),
      (105,30581870062911810213410332279225), (105,29341928661023858880988708995954), (105,1751412909896918567909340677747), (29,4609185769861210564668960344725),
      (29,7788928289258105729235124032345), (105,16681158551322110475409784119489), (105,27545078079679217366676890021285), (105,15765731710642368585779892640586),
      (105,1318039436687528651627374968955), (105,35183095852222597489158237435417), (36,11998882309234230121801883114205), (37,23871434642493624930050992354746),
      (105,3426587891587155096353347169140), (105,18506028397428198306601351604033), (39,28899608974422787903226881605419), (105,36070153968836894806478826996093),
      (42,4469982147289625160935878722439), (42,18002907402847340961400420793055), (105,27111232473199755644317615032431), (44,23121093344833959166582159271655),
      (45,4282944070797653356934405213646), (46,8562742809194140396606771272604), (47,17125464098711752339383287232312), (48,34246645908273173655790342794864),
      (105,2613059193556391563807134766074), (105,25578701843734892338117175677673), (105,34655962795840364068854456661819), (105,7103263465623519492871972224159),
      (53,39470670209100349579511511968727), (54,32196669523999838791583768631214), (105,39152245023115107139139152860770), (58,11786671465491200686782026891233),
      (59,23572840013135216106022226657218), (105,32952262707964746090454206955431), (105,28904893499140479053709195706570), (105,13599749982144237989288980185492),
      (105,21268165093006545171509691039185), (64,25688126592712987681274295269879), (65,19843432746056226654901516202990), (66,39685103208833108981341475760092),
      (105,32623629377988114852808998899640), (105,25842969635857179701288574361456), (105,2668485950864937075757073451183), (72,12598680283528290898654929479441),
      (72,25169622968328977262655755243042), (72,869254881611350179949762288708), (72,1738488366180166477537061320840), (72,3192185491615859893963086262544),
      (105,6384370095426821008432872350240), (74,8771401692239171680439951737201), (105,17540906844319891048404921451234), (78,37383564462280393010525278291125),
      (105,20558515292559909035585260882824), (105,13487221700211255354180477228530), (105,7510083010495702257666768858547), (80,4930443718726031165601909191735),
      (105,5252915808445841411006626946137), (105,15754466381120913070989505651947), (105,31508932762241826141979011303894), (105,36792475391223452131223889846057),
      (105,36981539700856780294230474636882), (86,15206632042746063831446036467315), (105,30144012126947557453101513415910), (105,4208449556325638275921003411391),
      (105,22895858527856087940019235161127), (105,29993412239487053311409582596887), (105,10706907395101688639634828084782), (105,5429355845279408502037123426053),
      (105,10858711690558817004074246852106), (96,27022981592730247183588896307985), (96,12609924468828122134041971331367), (96,29898278048986579528928557385035),
      (105,15742310458212370509323531218323), (105,7044707642837818630696500669089), (105,14089415285675637261393001338178), (105,28178830571351274522786002676356),
      (105,31539452231403070917079601173805), (105,6767495511920401246285827025535), (105,13534991023840802492571654051070), (105,27069982047681604985143308102140),
      (105,2330283208156713757814638128863)]
  | 112 => [
      (112,20362895356047113560498736529408), (112,61088686068141340682045965402113), (112,101814476780235567802493682647041), (112,305443430340706703410229706424327),
      (112,346169221052800930528416207470593), (112,1038507663158402791585550231666707), (112,1730779576397192819017984138870805), (112,5192244122101947868746172679258239),
      (112,4344951255098587467845034698932225), (112,3514625934907014161905651227230467), (112,666201497354979145077222759727365), (112,1953547187974561075399677701785359),
      (112,3264461066530817210362309774475537), (112,1119085574305214065260662232388403), (112,1814383577970966169863459335116117), (112,4778731587571107829995474740281343),
      (18,4758537738330274905247870612668417), (19,61115051941340443335352290639874), (112,122230103875609116121121012318212), (112,244366491363612157351869735239688),
      (22,4959314123227802849756676522049557), (112,4132295972297890327271890212552767), (112,1323507935105787503547765057519742), (112,1120629569670928138046881259782295),
      (112,1820425389756454572836244432683449), (112,3624939873780509264901909349794674), (112,2678153774136968955245844143212147), (29,1848003866817232613859793564928661),
      (29,1018014944327212574060275857691481), (112,4551600330493635230203525568995521), (112,825068923185906425641876345679269), (112,1630475634147454818208617127926602),
      (112,4381659494107104575898827991154811), (112,646346245639313081886009133348377), (36,1425768113410234044732986267065053), (37,2851473061832480671816205533820346),
      (112,4200172081901689355302731002375028), (112,3903475658099834820549447213999937), (112,4517144736497882228067719610203947), (40,3689151215245370794136726617162109),
      (41,3853625598726753325651681270498042), (112,4189430061715224727331408244668453), (112,4847405258282037870398607334209081), (112,238745853901953966374806080515186),
      (112,460457652738272175347249451751652), (112,899974668230381201708208018928072), (112,2853233261808606789589148017065093), (112,4206178517386277350122844599548170),
      (112,1677250374864428514852525476877323), (112,5008087900056268383325000467561501), (112,1215458276431637315541141396551738), (112,2411347196583015315428317741772916),
      (112,4806926499285025134782917187854568), (112,320019391438147558374593449411024), (112,3554357629487220544944150640768659), (112,776026583206343530482677857901493),
      (112,4618859097714808564276460620677625), (58,3862783475492000500184669199578465), (59,3486542395860111447212381989071554), (112,949153382312693494513039759401751),
      (112,4072954963518109605841018528189449), (112,1453283958790381370597889405851666), (112,1434416028087753366624772096588845), (112,1389899364051246156011880475145299),
      (112,2762620790732874097276310660081830), (112,317363625499477867480428620225861), (112,4355359335391879349704985445267075), (112,2499943782707772394139068655725830),
      (112,4999824179016970754041249117231628), (71,4817211045814301925164619735646875), (71,4452546491863641682832243013022645), (112,3722717908517636717229392300544489),
      (112,1087112101803632965592717820331555), (112,2150851895665557951595340175313990), (112,4301690146487621367774842735696012), (76,4962223647142126269917291691484145),
      (77,1286121482106286790669337558730722), (112,4102062792372178778221830978689743), (83,4998181003464770608050647695416905), (80,1213936279399221005727376311172242),
      (112,2404498130400846427805084722362660), (112,1766626759767800951315771992107447), (112,2470267791492684033522571866447284), (112,757283865399406793829503975191986),
      (112,1590758809955273269053239056469573), (112,4273433392690378935369126158209743), (112,2339894849525746870647238615246238), (112,4679736467629804469942656568150844),
      (112,553803651596295527543033973741176), (112,1107464940088073236354454548196592), (93,3504549334288850384914729972641663), (92,717665682752690876027404821131649),
      (112,4085629997790567177695693047774716), (112,3566204877824569467541614596274053), (112,4791182616546595113187209034956169), (112,313304044224376842630524232203026),
      (97,2544696343184312161829427138778451), (98,5089392686368624323658854277556902), (112,1918252473728663512084387501998111), (103,4593985612188950323847809954054177),
      (112,989308890642866326032509388477710), (112,3280976737199490913964591177695089), (103,1714609607093703030475864439663503), (112,2820879650821055929157800311849554),
      (112,2813201255685999784746022376559515), (112,1477186964593600886863512083920045), (112,2954373929187201773727024167840090), (109,4690942455092016397856333574629493),
      (109,4660114813507561941233731356590686), (112,3911272846364764237490620366181896), (112,3354499027803041376280940797575385), (112,998019226401132168899634715300225)]
  | 119 => [
      (119,2606450605574030535759652279353344), (119,7819351816722091607278956838060033), (119,13032253027870152678798261396766721), (119,39096759083610458036394784069713927),
      (119,44309660294758519107914084417536001), (119,132928980884275557323323359611322387), (119,221539785778840680834481778478612501), (119,664607247629049327199481342419206271),
      (119,556153760652619195884298347658674177), (119,449872119668097812723880715632967939), (119,85273791661437330569988109924303109), (119,250054040060743817651057346641397519),
      (119,417851016515944602926857335257235729), (119,143242953511067400353256285556380467), (119,232241097980283669742615868682343765), (119,611677643209101802239223066827653119),
      (18,609092830506275187872255759745286145), (19,7822726648491576747048753088167938), (119,15645453296077966863649752030904324), (119,31278910894542356141104756972060680),
      (22,634792207773158764769360157725753365), (119,528933884454129961890920908252446783), (119,169409015693540800454425528443469950), (119,143440584917878801669786300898017431),
      (119,233014449888826185323233523994788281), (119,463992303843905185907498154605020018), (119,342803683089532026271429909560886899), (29,236544494952605774574240648310098581),
      (29,130305912873883209479899807466722137), (119,582604842303185309465652352514072769), (119,105608822167796022481714371199593893), (119,313633696074917183741468068199511791),
      (119,624754153516750044534430983021096414), (119,143963122542881349619830440144591804), (119,474915044211379494461664972887275267), (119,487806935585938454153404966574714374),
      (119,420453864519078550109669429021170700), (119,91362488430973854245969643116826395), (119,182724976861939174532041697054170678), (40,151003799931144634470346719369333615),
      (119,203778924747325069107087842066079153), (42,546513922131380562551204641686791891), (43,299184352261615348699042433661619622), (119,133883319866707477913944212309239527),
      (45,87932715390038605660513252761845239), (46,172699628341647348477494366935809006), (119,343218627779680669202601635606099932), (48,488700150001000773853261046591138209),
      (119,393202137337940884016079109374119231), (50,609282618747893643378608272814596253), (51,8834101868984175197176860675850554), (119,14696041735916748770537501846881102),
      (53,583531895731886750288217635667174913), (54,61511987282212441760967036452981762), (119,105366703253315891648167780342700656), (119,356299249625840216905425156066346727),
      (119,512683182762795157976295944702070222), (58,45952956933088440739892367103660213), (59,89238497172632589384473614237639018), (60,178473979535715086577658257116119764),
      (119,643666553551552597357778827063574366), (119,516501317530924195734954703373731871), (64,408079941793628210288243329408440353), (64,473832278887368091054618338214813820),
      (119,583837364568355371191492326778753222), (119,129619345860884173278254972043852117), (119,494088179979750359554552414932384701), (68,309137785797473179216427770934378093),
      (119,618275450276816605507485014698065114), (70,380269601987076699329354235333131011), (119,373005053947450308724795967941259743), (119,236515547015035508138676815679281341),
      (119,473030823099518971172231231719518586), (119,50626528310728288898784792266558543), (119,99234953036016240051241607560992926), (119,198469873865644182658954686362104124),
      (119,396932653229300598051355820473606776), (119,602164365859205142378892049430922480), (119,67126508768344696441833690891913696), (119,147538041252805749860370903934228079),
      (119,292246416494973527483701238304976094), (119,437108827152208608676951195112841997), (119,352391777931705704983658162568840730), (119,564031830117982066687608244991986740),
      (119,442593641429348794983962165110383811), (119,197462877634744115895283328430208301), (119,394925475495039353294624529658341978), (119,600324034380981043185451401817216180),
      (119,462875513650036183881453422491928817), (119,466232755319740122637957919847879138), (119,459733248802368936869765280346940356), (93,78144967360681224893090139179902481),
      (94,156283121099386223053147233580076066), (95,312559428576796219373261422380423236), (96,625110775881015983784088303277912200), (119,55842973736839333342002895106034467),
      (119,321691860538337064389933879841753347), (98,434196075315242503223365823145053507), (99,398489284933083106064721728495688326), (100,597075140812575348431019348316402956),
      (101,77248690776062335791323436440119832), (102,152479281796561330375464121377281072), (119,141613606171355148237825331813912623), (119,593630988106073258364841005733647583),
      (119,653586437921333306812503770365705569), (119,511610891171709526744645068400389661), (119,241781105133927495395450439253154874), (119,483562210267854990790900878506309748),
      (119,424529398818820494400364890609119464), (110,538952265904409048891991646394076539), (119,60065936896485253770676648933799517), (114,437904469083098339881380807834581815),
      (119,116723810291445240298007832620485977), (114,567774192586452660220570068276145372), (119,510883540455442590509178999693009551), (118,346210709034199624965840015611832209),
      (117,572982303426419294331754334402158301), (119,483387834762042574947965625909529556), (119,129156464882395046219400221411062991)]
  | 127 => [
      (127,667251355026951817154470707354206208), (127,2001754065080855451463412671818432513), (127,3336256775134759085772353536771031041), (127,10008770325404277257317063358971576327),
      (127,11343273035458180891626001962707976193), (127,34029819106374542674770777417745956883), (127,56714185159383214293627333050856701973), (127,170139455393036627763067225759045320831),
      (127,142375362727070514146380374621690331137), (127,115167262635033040057313465535614091523), (127,21830090665327956625916952924114911493), (127,64013834255550417318670679663963801359),
      (127,106969860228081818349275477163397677329), (127,36670196098833254490433608473410474803), (127,59453721082952619454109659572219483477), (127,156589476661530061373241107850320642047),
      (18,155927764609606448095297473661482827777), (19,2002618022013843647244480782041350146), (127,4005236043795959517094333228114771972), (127,8007401189002843172122817704035876872),
      (22,162506805189928643780956199946799087637), (127,135407074420257270244075752071710572607), (127,43368708017546444916332934124718129278), (127,36720789738976973227465292902974292119),
      (127,59651699171539503442747783726967095737), (127,118782029784039727592319529373098181490), (127,87757742870920198725486058953990407795), (29,60555390707867078291005605635826190997),
      (29,33358313695714101626854350724538110809), (127,149146839629615439223207001664849518785), (127,27035858474955781755318880126745537957), (127,53427425579743799483001042128536787786),
      (127,143578218302901602743154135955924451451), (127,21179473777109011067355247393904506393), (36,46719569540226549177906493069914069725), (37,93437069290126726654023341598590481850),
      (127,137631238779754556794602698377099701108), (127,127909090364615387399802435641114715969), (127,148017798725562604849289270776700174123), (40,120886107021160310182350099214743339389),
      (41,126275603619078252974979216398008910586), (127,137279244262284483865185909698695034917), (127,158839775503385816937357015572041856569), (127,152351708568990856764881563371747318347),
      (127,19581932446297531825873998945334408342), (127,39161723563106502495051865679382341932), (127,77681427727512485125353911050288026200), (127,47875160976452208460310961818951313917),
      (127,143620662939637921706716274743277238791), (51,31383072577459873701767572565827657203), (127,14934228200082074251063606740952633883), (127,50345641788782967711916731182192906296),
      (127,99321832575783483937394741795970816437), (127,168736035054368259277582826838097802090), (127,30565340829021620125711598111295301332), (127,60323229627753806096843620601332026792),
      (127,120127756897683027689094223431593990992), (58,106947061713768622992225019497287431939), (127,100974189527984789190498143250408631814), (127,137502823693994421786996309051255883017),
      (127,12608646587732115042024798737309262109), (127,83576385449079455709931912230213036341), (127,108789309120933646948896938647556274533), (127,133132498862501932521333800061571832261),
      (68,95664439940504035372560397797364738639), (127,1020640569560439539038088282392907099), (67,134572723107887893417959329478106579827), (127,137027369661623513487636194144335410719),
      (127,9847421686274914085919934872014013698), (72,138648417047204753627710137316505069229), (73,79099074277680203010276439065721654618), (74,158194752885832646222458829833696877236),
      (127,35618520757817881054959007026836081009), (127,117987006163217848819338837974509388071), (127,73534785337414146264232858232169599371), (127,5234655479976406601261943817245602003),
      (127,9952677416803125171790219478325354918), (78,18058234504757784116692175655352038303), (127,28323436592044468312011716058866918514), (80,52609657162132443415740973425168104315),
      (127,111672113755624337857901779006139175368), (85,57459427404432215498417497663377731101), (85,166559524022444776131478280268483768871), (85,78064508667554984288105384775659031123),
      (85,125357971983374486946692157661236918971), (127,165784390287474723433747530677425380203), (127,146598399100654474159576619872832630205), (88,20864722839454758429326245207652510461),
      (127,41726078793344580504577903934545483258), (127,61822361617509948492764778569539245299), (127,123644654148062184547027175568753797606), (127,108384982310749286861435698772912853964),
      (127,96474830814796801253699056805787641752), (127,95380742055590107856770478947644748819), (127,133752609413047766522799612832137635878), (127,46187013240681126163458890663987302476),
      (127,92373531463802863203336496865372905624), (127,130101261982605627973634807742402347312), (127,62625546303909470587163254027366187005), (100,119604083353030555525670481129642312295),
      (101,118185665314320068348802826978294334670), (127,2857360777443417160452970012017069394), (127,7140140179179402524456147307852356621), (127,13472878196856639352675802436510988314),
      (127,26945310180701998368602278033493684276), (127,158875457414687972368177070691728995833), (107,152914348543563546114901454403609615883), (108,18050835999692805746128680256524631062),
      (127,42059723956252686401698347009663308766), (127,116193428406973731249684470695173521819), (127,92758205842658145326741099353124832054), (112,139606795351553250097390811431448739053),
      (113,76506321345906829576951046170144930266), (114,153012642691813659153902092340289860532), (115,18247424296193031824129956129885120360), (116,36494848592386063648259912259770240720),
      (127,44928889041657459182127648832349697425), (127,23625893751459130978664856495384521991), (127,6247619337329169563595308698769304233), (127,61607195739729015698493751785370330613),
      (127,123214391479458031396987503570740661226), (127,42614859446204647314232747958367517131), (127,85229718892409294628465495916735034262), (124,23045621952747305498794638191435843891),
      (125,46091243905494610997589276382871687782), (126,92182487810989221995178552765743375564), (127,79988197000275070448306928261829988653)]
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
  | 31 => (60,15,2498,2519)
  | 39 => (80,15,3182,3203)
  | 46 => (97,16,4026,3955)
  | 54 => (116,32,6373,6267)
  | 61 => (134,31,7241,7121)
  | 69 => (155,39,9298,9263)
  | 76 => (172,46,11060,10996)
  | 84 => (191,62,13901,13889)
  | 91 => (209,61,15090,15109)
  | 99 => (230,77,18479,18492)
  | 106 => (248,72,19502,19528)
  | 113 => (267,83,22151,22182)
  | 114 => (269,92,23136,23156)
  | 120 => (285,86,24051,24077)
  | 121 => (287,87,24659,24690)
  | 128 => (307,98,26812,26828)
  | 30 => (56,14,2272,2268)
  | 37 => (75,15,2957,2978)
  | 38 => (75,16,3225,3147)
  | 45 => (93,15,3799,3820)
  | 53 => (112,31,6161,6097)
  | 60 => (129,14,5380,5376)
  | 68 => (149,38,9104,9100)
  | 75 => (167,37,9931,9906)
  | 83 => (187,37,11387,11362)
  | 90 => (204,44,13677,13731)
  | 98 => (225,52,16016,15997)
  | 105 => (242,67,18507,18520)
  | 112 => (260,62,19589,19577)
  | 119 => (279,73,22496,22485)
  | 127 => (299,77,25244,25233)
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
  (if 224 ≤ s+15 ∧ s+15 ≤ 286 then min 256 (511-(s+15)) else if 257 ≤ s+15 then 512-(s+15) else min 257 (Partial.railP (s+15))) - (Shadow7.sbP s + 1)

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
  Shadow7.fix8P s b ++ Shadow7.leaveJoinMove s ++ Shadow7.fix10P s b ++
    Partial.leaveFix11 s b ++ Partial.leaveFix12 s b ++ Shadow7.leaveLowStore s ++
    Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

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
    if i < 16 then some (tagsP.getD i 0) else none, Shadow7.a0P s + i, Shadow7.bankW s i⟩

def lastCol (s : Nat) : HighBankJoin.Column :=
  ⟨false,none,Shadow7.a0P s+16,Shadow7.bankW s 16⟩

theorem cols_split : ∀ j : Fin 26, j.val≤24 →
    Shadow7.columnsP (start j) = cols16 (start j) ++ [lastCol (start j)] := by
  intro j hi
  have high : ¬16 < Shadow7.lowsP (start j) := by revert j; decide +kernel
  simp only [Shadow7.columnsP,cols16,List.range_succ,List.map_append,List.map_cons,List.map_nil,
    decide_eq_false high,show ¬16<16 by decide,if_false,lastCol]

def postEntry (s : Nat) : List Gate :=
  leaveFix3 s (Shadow7.sbP s) ++ leaveFix4 s (Shadow7.sbP s) ++
  Shadow7.leaveFix5Move s (Shadow7.sbP s) ++ Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++
  Shadow7.fix8P s (Shadow7.sbP s) ++ keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s+i) 1613 0 8 ++ wordOpen 1614 (cols16 s)

def pair16 (s : Nat) : List Gate :=
  [.cx (Shadow7.a0P s+16) (Shadow7.bankW s 16),.cx (Shadow7.bankW s 16) (Shadow7.a0P s+16),
   .pop 1614 (Shadow7.bankW s 16) (Shadow7.a0P s+16)]

def afterWord (s : Nat) : List Gate :=
  wordClose 1614 (cols16 s) ++ Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++
  leaveFix12 s (Shadow7.sbP s) ++ Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++
  Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

theorem post_keeps_checked : ∀ j : Fin 26, j.val≤24 →
    (postEntry (start j)).all (fun g => decide (target g ≠ Shadow7.a0P (start j)+16)) = true := by
  decide +kernel


theorem pair_layout_checked : ∀ j : Fin 26, j.val≤24 →
  [1614,Shadow7.a0P (start j)+16,Shadow7.bankW (start j) 16].Nodup := by decide +kernel

def shortenedOps (s : Nat) : List Gate :=
  LeaveJ7.entryOps s ++ postEntry s ++ afterWord s



-- Explicit 3d shape; cached 83c has a different kept width.

def referenceOps (s : Nat) : List Gate :=
  Shadow7.fix0P s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s) ++
  leaveFix3 s (Shadow7.sbP s) ++ leaveFix4 s (Shadow7.sbP s) ++ Shadow7.leaveFix5Move s (Shadow7.sbP s) ++
  Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++ Shadow7.fix8P s (Shadow7.sbP s) ++
  (keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s+i) 1613 0 8 ++ wordGM 1614 (Shadow7.columnsP s)) ++
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
  (keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s+i) 1613 0 8 ++ wordGM 1614 (cols16 s)) ++
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
  (keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s+i) 1613 0 8 ++ wordGM 1614 (Shadow7.columnsP s)) ++
  Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++ leaveFix12 s (Shadow7.sbP s) ++
  Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

def afterOpen (s : Nat) : List Gate :=
  Shadow7.fix8P s (Shadow7.sbP s) ++ keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s+i) 1613 0 8 ++
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
  have shape : Shadow7.fix0P s h = (Shadow7.fix0P s h).take 54 ++
      [.ccx (s+30) (h+803) (s+h+48)] ++ (Shadow7.fix0P s h).drop 55 := rfl
  rcases List.mem_append.mp hg with pre | tail
  · rcases List.mem_append.mp pre with head | cell
    · exact ⟨g,List.mem_of_mem_take head,rfl,rfl⟩
    · have eg : g = .pop (s+30) (h+803) (s+h+48) := List.mem_singleton.mp cell
      subst g
      refine ⟨.ccx (s+30) (h+803) (s+h+48),?_,rfl,rfl⟩
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

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

def before (s : Nat) : List GateMirror.Gate := DeadJoin.beforeAll s
def afterPart (s : Nat) : List GateMirror.Gate := DeadJoin.afterAll s

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

def params : WindowFold.Pieces Program := { Shadow7.params with leave := leave, leaveInv := unleave }

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
  n = 30 ∨ n = 38 ∨ n = 45 ∨ n = 53 ∨ n = 60 ∨ n = 68 ∨ n = 75 ∨ n = 83 ∨ n = 90 ∨ n = 98 ∨ n = 105 ∨ n = 112 ∨ n = 119 ∨ n = 127

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

private theorem place_nodup : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    ((List.range (barrelWidth (start j)+26)).map (place (start j))).Nodup := by decide +kernel

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
      490370281, 659463482, 1318926964, 388914361,
      777828722, 1268199004, 2059990417, 257498802,
      514997604, 1029995208, 1662567985, 623462994,
      692736660, 831283992, 784846113, 1569692226,
      366541220, 733082440, 1466164880]
  | 39 => #[
      549755813887, 183251937962, 329853488332, 36650387592,
      485078659312, 140133834912, 278111764672, 2155905152,
      4278255360, 2852170240, 3422604288, 2281736192,
      4026593280, 2684395520, 3221274624, 2147516416,
      87262827601, 174525655202, 296693613844, 43631413800,
      337645303017, 359289232698, 168822651508, 324658945209,
      99562076530, 437207379548, 431556720017, 191383543474,
      382767086948, 215778360008, 53202175537, 88670292562,
      159606526612, 301478994712, 71651806497, 143303612994,
      352553859492, 155351905096, 310703810192]
  | 46 => #[
      70368744177663, 46912496118442, 14073748835532, 9382499223688,
      53811392606448, 35874261737632, 827867578560, 551911719040,
      69273510805248, 46182340536832, 13197562137600, 8798374758400,
      52780584726528, 35187056484352, 3221274624, 2147516416,
      5584820966481, 11169641932962, 18988391286036, 37976782572072,
      43218598786281, 45989021785402, 21609299393140, 41556344986809,
      12743945795954, 55962544582236, 67501766014353, 8437720751794,
      16875441503588, 33750883007176, 54479027750449, 20429635406418,
      22699594896020, 27239513875224, 39659879301697, 8951014425730,
      17902028851460, 4957484912712, 9914969825424, 19829939650848,
      57026054005185, 43683363832706, 66695732766404, 11600561597512,
      23201123195024, 28513027002592]
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
      5076464550617232, 10152929101234464, 9963426261843777, 10606933195047362,
      3199467880612740, 15162689070839880, 2490856565460944, 4981713130921888,
      11878975075852737, 5743551642223490, 840751918720708, 13452030699531336,
      8889662889580688, 5939487537926368]
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
      1299574924958011464, 293306840702328976, 586613681404657952, 2245664390251618753,
      2185485771289543554, 253042331051468484, 1742834287609801800, 1179825566005909648,
      2275753699732656352]
  | 69 => #[
      590295810358705651711, 196765270119568550570, 236118324143482260684, 157412216095654840456,
      312509546660491227376, 11574427654092267680, 13889313184910721216, 9259542123273814144,
      18374966859414961920, 12249977906276641280, 14699973487531969536, 9799982325021313024,
      17294086455919964160, 11529390970613309440, 13835269164735971328, 9223512776490647552,
      93697747675985024081, 187395495351970048162, 318572342098349081876, 46848873837992512040,
      385783876061201331433, 539167826784329571642, 488039843209953491572, 529871829770806647993,
      469447849182907644274, 264935914885403323996, 463380499711497139601, 205496515053613555378,
      410993030107227110756, 231690249855748569800, 57125401002455385649, 95209001670758976082,
      171376203007366156948, 323710605680580518680, 153871082802752507169, 307742165605505014338,
      166807837940020476324, 333615675880040952648, 76935541401376253584, 18255828490050148417,
      19017238714023618754, 38034477428047237508, 76068954856094475016, 152137909712188950032,
      304275819424377900064, 10396599399664091713, 20793198799328183426, 41586397598656366852,
      75086551219796217928, 150173102439592435856, 300346204879184871712, 16222922084795629377,
      20997381196741558722, 41994762393483117444, 81620387937024227400, 151629683110875320272,
      303259366221750640544, 9667514144154628033, 19335028288309256066, 38670056576618512132,
      77340113153237024264, 154680226306474048528, 299981662251430139872, 13774879436320088513,
      27549758872640177026, 41758216496897959620, 77835653591661702216, 155671307183323404432,
      302035344897512870112]
  | 76 => #[
      75557863725914323419135, 50371909150609548946090, 60446290980731458735308, 40297527320487639156872,
      4444580219171430789360, 2963053479447620526240, 3555664175337144631488, 2370442783558096420992,
      70853872209904093167360, 47235914806602728778240, 56683097767923274533888, 37788731845282183022592,
      17294086455919964160, 11529390970613309440, 13835269164735971328, 9223512776490647552,
      5996655851263041541201, 11993311702526083082402, 20388629894294341240084, 40777259788588682480168,
      49380336135833770423529, 69013481828394185170234, 62469099930874046921332, 67823594210663250943161,
      60089324695412178467186, 33911797105331625471580, 72479469363473586648465, 9059933670434198331058,
      18119867340868396662116, 36239734681736793324232, 58496410626514314905137, 21936153984942868089426,
      24373504427714297877140, 29248205313257157452568, 57276949433284498364481, 20679370601268721428674,
      41358741202537442857348, 7159618679160562295560, 14319237358321124591120, 28638474716642249182240,
      5323058892628014957121, 10646117785256029914242, 21292235570512059828484, 38444314224535663579208,
      1330764723157003739280, 2661529446314007478560, 21856159557443124513089, 65549743688945976040386,
      72647456114931919650500, 69737048503949515881864, 43242971752317942837840, 10928079778721562256544,
      73803199216923002093377, 4153068053707681120706, 8306136107415362241412, 57340313992731472443464,
      37340265735709331378128, 74680531471418662756256, 37198303566742610685889, 74396607133485221371778,
      73235350541056119324420, 70912837356197915229704, 66267810986481507040272, 56378083646328467052512,
      4145845551947259650497, 8291691103894519300994, 15979745096181950555844, 29002330361168238636104,
      58004660722336477272208, 39851854638930791534816, 44284060367407662314177, 13010257008901001209218,
      60841390162998792681924, 46124916600083261944712, 51512197100793411589584, 59920962046660992866656]
  | 84 => #[
      19342813113834066795298815, 12895208742556044530199210, 15474250491067253436239052, 10316166994044835624159368,
      1137812536107886282076400, 758541690738590854717600, 910250028886309025661120, 606833352590872683774080,
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
      6393509830784577442583489, 19163979228651362665346114, 13287006897937001913645892, 7231200682039937031992968,
      14462401364079874063985936, 3196754915392288721291744, 10355573176002209568072129, 1368333238170352340845442,
      13087490169679359902066372, 15971711576529090480073800, 12600610039224114164848784, 14849193144918138181685472,
      14995301932353152437767873, 5636754796464513254773570, 11273509592929026509547140, 3204206072023986223795464,
      11080595256033161711342800, 17169057523093609616533344, 5560008112359153271911105, 11120016224718306543822210,
      8447764263739488692206020, 16895528527478977384412040, 18638746673675716972697040, 12451410613096610033604960]
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
      749876091470612676403040480, 1262842860511573494966334145, 49805642452386440134419842, 1323759056004456030772525508,
      171638033438151511746802568, 1566063795780401060596602320, 1869361469541167022382291296]
  | 99 => #[
      633825300114114700748351602687, 211275100038038233582783867562, 380295180068468820449010961612, 42255020007607646716556773512,
      74567682366366435382159012080, 49711788244244290254772674720, 59654145893093148305727209664, 39769430595395432203818139776,
      100607190494303920753706603601, 201214380988607841507413207202, 342064447680633330562602452244, 50303595247151960376853301800,
      578927045773522088872510125289, 144731761443380522218127531322, 289463522886761044436255062644, 459149036303138208416128720057,
      284472772492161716083905837426, 229574518151569104208064360028, 497551022966254412446946620817, 220650202899310476742956228274,
      441300405798620953485912456548, 248775511483127206223473310408, 298604118712777753088543464177, 597208237425555506177086928354,
      560591174736996311605822254020, 466214709413446226918447533432, 61337932269107874265969509937, 102229887115179790443282516562,
      184013796807323622797908529812, 347581616191611287507160556312, 330435634218965018537215118625, 27045968323815336326078634562,
      358217104334427977691327691172, 82608908554741254634303779656, 165217817109482509268607559312, 328555945234135717640058728097,
      23286590354156734531765853506, 46573180708313469063531707012, 399051636365591279784190483368, 164277972617067858820029364048,
      333357645410118202523088841953, 346438308082184245245088904482, 360217438567330381029811914404, 86609577020546061311272226120,
      483591472762116451635720222320, 387149484064887316765340932161, 408239233948349416616636655810, 182653167782584132484921708932,
      365306335565168264969843417864, 96787371016221829191335233040, 193574742032443658382670466080, 80623570464613415946463511105,
      161247140929226831892927022210, 322494281858453663785854044420, 89306108822341014586851889224, 178612217644682029173703778448,
      357224435289364058347407556896, 362748338785268313833050786113, 454380426133817781919225306050, 627721732971927730720150027972,
      621618165829740760691948453256, 249143409724845753645350597200, 498286819449691507290701194400, 592212409375312685448528478017,
      122130072806633995967257330114, 244260145613267991934514660228, 105210529127599666462124947528, 464965752400885521736307920848,
      296106204687656342724264239008, 186836273631604291377543163841, 373672547263208582755086327682, 113519794412302464761821052676,
      227039588824604929523642105352, 454079177649209859047284210704, 93418136815802145688771581920, 168791780741146851433220051905,
      506220583168266179395635360834, 546621842790734830570262887236, 459418385467354960392174171784, 285011470820595220035996740880,
      401308540427630776090785827296, 531338088997083983009631248833, 428850877880053265270910894978, 349015464503077746547478603460,
      513645031136326338772844833864, 393464762158537976797338065040, 582581694555599341878991425760, 455364158814700119580567195329,
      535376018119495765273535402818, 436926736124876829798719202948, 240028172135638958849086803208, 292300329558402616505471751376,
      227682079407350059790283597664, 251326730796158389024589427393, 502653461592316778049178854786, 602962618148699269631746898372,
      572099936183283838515142194056, 424941557231380455076097086928, 125663365398079194512294713696]
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
      793056093984425041014555280000, 10785562878188180557797951808008, 33289351240152929457451498458401, 66578702480305858914902996916802,
      65008397715974127454023191165348, 48887157017341573212257377186632, 16644675620076464728725749229200, 32658447951229967940689020579041,
      53587763517667819108106623530274, 16839675241534312600486953584292, 33679350483068625200973907168584, 56894043182918324818239012861552,
      33346065089998851755679624271937, 59353992144561016586213335705794, 37578345874515351476637666267524, 75156691749030702953275332535048,
      69183745083454724210761659926032, 57237851752302766725734314708000, 41279268077882068964589317685825, 1428897741157456233389630227586,
      2857795482314912466779260455172, 45724727717038599468468167282760, 10319817019470517241147329421456, 20639634038941034482294658842912,
      66914404850767311892409969068353, 37216247832752470425323618261954, 18374830136167139351673994903236, 36749660272334278703347989806472,
      16728601212691827973102492267088, 33457202425383655946204984534176, 57636489419645635752800172719937, 70476738385473365779034285228482,
      59823838356340049862279565312900, 64755391140767299142793988421704, 14409122354911408938200043179984, 28818244709822817876400086359968,
      9060390475229210101854465601473, 18120780950458420203708931202946, 36241561900916840407417862405892, 72483123801833680814835724811784,
      63836609189060679933882444479504, 45095014444917945898821735372768, 78129303694777255043480467182529, 8745949484651757289124206195778,
      61393850653745746102412016745284, 41658062892884810509035028346504, 2186487371162939322281051548944, 79629471054691968369634736163296,
      39194681395958080728659079012801, 78389362791916161457318158025602, 47252087672947565601925497202372, 25866657035700914368706908941384,
      51733314071401828737413817882768, 19597340697979040364329539506400, 5525966559727617725567380016833, 16381008520972363283982325470018,
      32762017041944726567964650940036, 65524034083889453135929301880072, 44660071337546431668890083939536, 2762983279863808862783690008416,
      52225001340153563850389420847809, 23320364265700446004989836551554, 17716245721229796189837240170948, 35432491442459592379674480341896,
      39088284864192377200725544850896, 26112500670076781925194710423904]
  | 113 => #[
      10384593717069655257060992658440191, 3461531239023218419020330886146730, 4153837486827862102824397063376076, 2769224991218574735216264708917384,
      4886867631562190709205173015736560, 3257911754374793806136782010491040, 3909494105249752567364138412589248, 2606329403499835044909425608392832,
      5172093368812902229197692841557760, 3448062245875268152798461894371840, 4137674695050321783358154273246208, 2758449796700214522238769515497472,
      4867852582412143274539005027348480, 3245235054941428849692670018232320, 3894282065929714619631204021878784, 2596188043953143079754136014585856,
      5604383910799496487937678577570897, 824174104529337718814364496701602, 6593392836234701750514915973612820, 2802191955399748243968839288785448,
      9485140717953385904087205892748521, 2371285179488346476021801473187130, 4742570358976692952043602946374260, 7522697810790616406689852949421241,
      4660801904511577556318713240402290, 3761348905395308203344926474710620, 5919158203488569330000554212521361, 7230265848604605701913189688090290,
      4075937980139556146765386717740388, 8151875960279112293530773435480776, 2009921364594126823947288901633585, 3349868940990211373245481502722642,
      6029764093782380471841866704900756, 1004960682297063411973644450816792, 5063326932945767194596369817390369, 10126653865891534389192739634780738,
      5825212725153048527855042556393892, 1265831733236441798649092454347592, 2531663466472883597298184908695184, 8068924626397914276244155960946337,
      5753255535726173295427319263452482, 1121917354382691333793645868464772, 9805676444401720011856783484066728, 9226759171733784766652574309693264,
      7739974097338864729040644509265121, 7923162689734515943599640122504482, 2288469550850521400082579097618084, 4576939101701042800165158195236168,
      3869987048669432364520322254632560, 6585145826525656070333324766881121, 9369545637304419392312182909595554, 8354497557539183527563373160750916,
      2342386409326104848078045727398888, 8484869771797655663697158712660656, 9051990036827288126306284990231137, 7719386356584920995551577322022082,
      6642219383745854405845677268155364, 6180202085010552039230378668033448, 9718291876948471691683638824335664, 4495476177893366345024074907195457,
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
      3920335144571197503323066957338976]
  | 114 => #[
      20769187434139310514121985316880383, 13846124956092873676081323544586922, 4153837486827862102824397063376076, 2769224991218574735216264708917384,
      4886867631562190709205173015736560, 3257911754374793806136782010491040, 3909494105249752567364138412589248, 2606329403499835044909425608392832,
      5604383910799496487937678577570897, 11208767821598992975875357155141794, 6593392836234701750514915973612820, 13186785672469403501029831947225640,
      9485140717953385904087205892748521, 12755878896558001733082794131627322, 4742570358976692952043602946374260, 7522697810790616406689852949421241,
      15045395621581232813379705898842482, 3761348905395308203344926474710620, 16303751920558224587061546870961553, 7230265848604605701913189688090290,
      14460531697209211403826379376180580, 8151875960279112293530773435480776, 9784659761980301413205392234158833, 19569319523960602826410784468317666,
      18369451613781895138699583619754948, 15276923598059805963663688775519608, 2009921364594126823947288901633585, 3349868940990211373245481502722642,
      6029764093782380471841866704900756, 11389554399366718669034637109256984, 5063326932945767194596369817390369, 10126653865891534389192739634780738,
      16209806442222703784916035214834084, 11650425450306097055710085112787784, 2531663466472883597298184908695184, 18453518343467569533305148619386529,
      16137849252795828552488311921892674, 11506511071452346590854638526904964, 20190270161471375268917776142506920, 19611352888803440023713566968133456,
      14982694983045950807793230631343521, 16385361523983414273005273201852130, 3509856944532568049155435829487716, 19322564321365970587539796645496168,
      17875941208592630660957607974111952, 7739974097338864729040644509265121, 18307756406804171200660632780944674, 12673063267920176657143571756058276,
      4576939101701042800165158195236168, 3869987048669432364520322254632560, 16969739543595311327394317425321313, 9369545637304419392312182909595554,
      18739091274608838784624365819191108, 2342386409326104848078045727398888, 18869463488867310920758151371100848, 19436583753896943383367277648671329,
      18103980073654576252612569980462274, 6642219383745854405845677268155364, 6180202085010552039230378668033448, 9718291876948471691683638824335664,
      4495476177893366345024074907195457, 7279891811044555687511434793527490, 14559783622089111375022869587054980, 8350379810038912235923753857229576,
      16700759620077824471847507714459152, 12632331806016338429573030112037920, 365797821736308795747745338262081, 731595643472617591495490676524162,
      1463191286945235182990981353048324, 2641873156984452413733716331892808, 5283746313968904827467432663785616, 10567492627937809654934865327571232,
      13047656551187836383218650792118593, 18291384891119255851977849775676354, 7969079394767621945538996499021508, 15938158789535243891077992998043016,
      3261914137796959095804662698029648, 6523828275593918191609325396059296, 8819637438197167258898012728278849, 14754941291429282752716844216304066,
      8740695148719254991311703115727748, 15235997774672216776255337950361672, 2204909359549291814724503182069712, 4409818719098583629449006364139424,
      4957968333766236793544983779389377, 9915936667532473587089967558778754, 19831873335064947174179935117557508, 18894559235990583834237884918234632,
      17019931037841857154353784519588880, 12863577883952773653833484548134880, 19143594331127347453553896676037569, 4876524254361052659036464514839618,
      11987450697600927955383395772922692, 3205713961062545396644806228965000, 6411427922125090793289612457930000, 9571797165563673726776948338018784,
      5718269370418425799433889439097281, 11436538740836851598867778878194562, 7754567737060582326701880985888452, 20227146622272764656620169189813320,
      19685105810406218799118353062746256, 13243728402278868156777937377988832, 12499490282409156598877074172202689, 14132938092662534978351269220537154,
      7496688751185759442580553124193924, 14993377502371518885161106248387848, 19110125098770116630179306292794576, 6249745141204578299438537086101344,
      7840670289142395006646133914677953, 15681340578284790013292267829355906, 18353014527422339859438152402729412, 15936841620705369204754319488578440,
      18861164397052942530623774738273744, 14304928861640852760384059615779168]
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
      857566448893494111550843264696996500, 1029079738672192933861011917636395800, 706842648784940601035846569689645600, 667862355653418141419899148567054850,
      831579586805812471806878317281936000, 675658414279722633343088632791573000, 1126599448376468534957183576928931105, 923970900968021197010560093577517634,
      971592428412630987434527359791331748, 613956861040346101965247659302318920, 1227913722080692203930495318604637840, 1077682077484572405753526399780286113,
      826136159184228938603245739280227650, 323044322583542004302684418280110724, 934034517263601037890285130085243816, 538841038742286202876763199890143056,
      326520506495135608519623010384549281, 348692360470212382498957038271938274, 958892478914940851698766760405985380, 413937125570012870355857517666223464,
      827874251140025740711715035332446928, 755430721726354043237432115916958945, 932152003508933833822027986723681570, 1279593496750418118018584676085761700,
      1229958997715920363133362291891178824, 377715360863177021618716057958479472, 1159275048421257389604103509853742433, 507830044056647871731239830514724770,
      1015660088113295743462479661029449540, 459264509960390936158761722698767336, 579637524210628694802051754926871216, 850204081119469363948246690323886689,
      371180166454022854992686320367428802, 235103281159278270061187515753839588, 1293869823001647803914793468314617256, 425102040559734681974123345161943344,
      897570535845883718452269443533051969, 1274200325293542497048952539123230914, 1219172654802169121194098017966117252, 1109117313819422369484388975651889928,
      889006631853928866064970891023435280, 448785267922941859226134721766525984, 187288484728990103422845613190185537, 374576969457980206845691226380371074,
      749153938915960413691382452760742148, 23411060591123762927855701648773192, 46822121182247525855711403297546384, 93644242364495051711422806595092768,
      760738404180203014891610122199812417, 952904819427388228987467189035293634, 1316427887745544184335224071462485700, 1303627779706172495766641082644626824,
      522491599991279721948854295620039248, 1044983199982559443897708591240078496, 756510385067212345767289484135972673, 928599188393558945374084198159040962,
      527970381002202017844361336037737348, 472158121325737048086939014921730120, 189127596266803086441822371033993168, 378255192533606172883644742067986336,
      108803905504462789364154910363791297, 217607811008925578728309820727582594, 435215622017851157456619641455165188, 870431244035702314913239282910330376,
      411634492286488756922671505540316176, 719015950644689331133980985322067936, 517604092750470799792481544281166785, 856413209054072783738037862506935362,
      219679325038994033096603248941726532, 439358650077988066193206497883453064, 878717300155976132386412995766906128, 258802046375235399896240772140583392,
      774178204433572914821947346163671489, 219128413082229956740087632046998402, 1004675564575747487004557176196146884, 124073083792969317227230095774215240,
      248146167585938634454460191548430480, 1051703100109244393862877203222008032, 527070356142625157859695766836687553, 1054140712285250315719391533673375106,
      1264504260575780970706757271415552452, 1199780525366646068509707482550760328, 891167036630903984123747158047249872, 263535178071312578929847883418343776]
  | 121 => #[
      2658455991569831745807614120560689151, 886151997189943915269204706853563050, 1063382396627932698323045648224275660, 708921597751955132215363765482850440,
      1251038113679920821556524292028559600, 834025409119947214371016194685706400, 1000830490943936657245219433622847680, 667220327295957771496812955748565120,
      1334400089153728775133004753121902336, 3448062245875268152798461894371840, 4137674695050321783358154273246208, 2758449796700214522238769515497472,
      4867852582412143274539005027348480, 3245235054941428849692670018232320, 3894282065929714619631204021878784, 2596188043953143079754136014585856,
      1687908566076083648131818489244882001, 717361140582335550456022857929074850, 421977141519020912032954622311220500, 843954283038041824065909244622441000,
      1214098011898033395723162354271810793, 1632752498759424221834597648848297274, 607049005949016697861581177135905396, 962905319781198900056301177525918905,
      1925810639562397800112602355051837810, 481452659890599450028150588762959452, 2550144618885554107309943755530368401, 318768077360694263413742969441296050,
      637536154721388526827485938882592100, 1275072309442777053654971877765184200, 1609012092190707211000598261633948401, 559568192811582676193582402707207650,
      1119136385623165352387164805414415300, 804506046095353605500299130816974200, 2058159477344385867722023835272791601, 771809804004144700395758938227296850,
      857566448893494111550843264696996500, 1029079738672192933861011917636395800, 706842648784940601035846569689645600, 667862355653418141419899148567054850,
      831579586805812471806878317281936000, 675658414279722633343088632791573000, 2455827444161384407860990637209275681, 2253198896752937069914367153857862210,
      971592428412630987434527359791331748, 1943184856825261974869054719582663496, 1227913722080692203930495318604637840, 1077682077484572405753526399780286113,
      2155364154969144811507052799560572226, 1652272318368457877206491478560455300, 934034517263601037890285130085243816, 1868069034527202075780570260170487632,
      755430721726354043237432115916958945, 2261379999293849706725835047004026146, 2608821492535333990922391736366106276, 2559186993500836236037169352171523400,
      1706943356648092894522523118238824048, 1159275048421257389604103509853742433, 1837058039841563744635046890795069346, 1015660088113295743462479661029449540,
      1788492505745306809062568782979111912, 579637524210628694802051754926871216, 850204081119469363948246690323886689, 1700408162238938727896493380647773378,
      235103281159278270061187515753839588, 1293869823001647803914793468314617256, 1754330036344650554877930405442287920, 897570535845883718452269443533051969,
      2603428321078458369952759599403575490, 2548400650587084994097905078246461828, 2438345309604338242388196035932234504, 2218234627638844738968777951303779856,
      1778013263707857732129941782046870560, 187288484728990103422845613190185537, 374576969457980206845691226380371074, 749153938915960413691382452760742148,
      1352639056376039635831662761929117768, 46822121182247525855711403297546384, 93644242364495051711422806595092768, 2089966399965118887795417182480156993,
      952904819427388228987467189035293634, 1316427887745544184335224071462485700, 2632855775491088368670448142924971400, 522491599991279721948854295620039248,
      1044983199982559443897708591240078496, 756510385067212345767289484135972673, 2257827184178474818277891258439385538, 1857198376787117890748168396318081924,
      472158121325737048086939014921730120, 189127596266803086441822371033993168, 378255192533606172883644742067986336, 1438031901289378662267961970644135873,
      217607811008925578728309820727582594, 435215622017851157456619641455165188, 870431244035702314913239282910330376, 1740862488071404629826478565820660752,
      2048243946429605204037788045602412512, 517604092750470799792481544281166785, 856413209054072783738037862506935362, 1548907320823909906000410309222071108,
      439358650077988066193206497883453064, 878717300155976132386412995766906128, 1588030042160151272800047832420927968, 2103406200218488787725754406444016065,
      1548356408867145829643894692327342978, 2333903560360663359908364236476491460, 124073083792969317227230095774215240, 248146167585938634454460191548430480,
      2380931095894160266766684263502352608, 1549419360408718134643903987621351105, 1987205744335897033819939874324173634, 1315955497101962321832265628087658116,
      2631910994203924643664531256175316232, 1161415433976432194906888498721215696, 774709680204359067321951993810675552, 527070356142625157859695766836687553,
      1054140712285250315719391533673375106, 2593732256360696843610564331695897028, 2529008521151561941413514542831104904, 2220395032415819857027554218327594448,
      1592763173856228451833654943698688352]
  | 128 => #[
      340282366920938463463374607431768211455, 226854911280625642308916404954512140970, 272225893536750770770699685945414569164, 181483929024500513847133123963609712776,
      320265757102059730318470218759311257840, 213510504734706486878980145839540838560, 256212605681647784254776175007449006272, 170808403787765189503184116671632670848,
      338958311018522360492699998064329424640, 225972207345681573661799998709552949760, 271166648814817888394159998451463539712, 180777765876545258929439998967642359808,
      319019586840962221640188233472310046720, 212679724560641481093458822314873364480, 255215669472769777312150586777848037376, 170143779648513184874767057851898691584,
      108026148228869353480436383311672448081, 216052296457738706960872766623344896162, 27006537057217338370109095827918112020, 54013074114434676740218191655836224040,
      155404545522948274652564781346791781609, 208992319841206300394828499052582051130, 77702272761474137326282390673395890804, 43410251288821423954004329459341729960,
      180993746282674587720188386080719538218, 55997147117063425349280225943725025824, 123251880931993459207206550723317619897, 246503761863986918414413101446635239794,
      61625940465996729603603275361658809948, 11506832159811994674889185894964267176, 223490097544362929064634729656706705442, 55872524386090732266158682414176676360,
      193958976011913439805458160435899987345, 236921351327075719640291399699342630578, 133560335733212975817208191966917049700, 267120671466425951634416383933834099400,
      320623731080570516707914292728916646641, 300965095240202569952453978026065081826, 261647823559466676441533348620361952196, 160311865540285258353957146364458323320,
      65861103275020347767104762728729331249, 109768505458367246278507937881215552082, 197583309825061043301314288186187993748, 32930551637510173883552381364364665624,
      29040387359859701865937131842816167201, 58080774719719403731874263685632334402, 88700640150217078599085793338294073764, 177401280300434157198171586676588147528,
      14520193679929850932968565921408083600, 25003786001613058118022053484826488481, 50007572003226116236044106969652976962, 100015144006452232472088213939305953924,
      176392129960872496261192817087090727848, 12501893000806529059011026742413244240, 33557220401118032431114799517393163681, 57505496179221594917362660630326755042,
      105967904145923294811099524522553206884, 178530488560748739839466003595232396648, 16778610200559016215557399758696581840, 35315358612134166738736415683205917921,
      63405867805399979860300959819899876642, 92996325205909613348381271835429537444, 185992650411819226696762543670859074888, 17657679306067083369368207841602958960,
      38377658930398901830910701197703390561, 49689265888098535169172101060887474082, 99378531776197070338344202121774948164, 182563499932493865523980328981105974248,
      19188829465199450915455350598851695280, 30093219988387618567832002016491467361, 60186439976775237135664004032982934722, 101256430960812884610750524097060027364,
      190044245224459701756255396028123547048, 15046609994193809283916001008245733680, 168380298004745283704331959038856468545, 175403067773117521847447677435848370370,
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
      37153660146768509539109547898984856004, 74307320293537019078219095797969712008, 81974074779510772231255977835148269008, 54761883005252863367985937354912471392]
  | 30 => #[
      1073741823, 715827882, 214748364, 143165576,
      821096688, 547397792, 12632256, 8421504,
      289739857, 579479714, 340870420, 681740840,
      490370281, 659463482, 245185140, 388914361,
      777828722, 194457180, 986248593, 257498802,
      514997604, 1029995208, 226007793, 452015586,
      904031172, 649874808, 588826161, 623462994,
      692736660, 831283992]
  | 37 => #[
      137438953471, 45812984490, 54975581388, 36650387592,
      72761798896, 2694881440, 3233857728, 2155905152,
      87262827601, 37086701730, 21815706900, 43631413800,
      62767396073, 84411325754, 31383698036, 49781038265,
      99562076530, 24890519132, 19239859601, 53944590002,
      107889180004, 78339406536, 53202175537, 88670292562,
      22167573140, 26601087768, 71651806497, 5864659522,
      77675952548, 17912951624, 35825903248, 77460701761,
      17482450050, 34964900100, 9682587720, 19365175440,
      38730350880]
  | 38 => #[
      274877906943, 183251937962, 54975581388, 36650387592,
      210200752368, 140133834912, 3233857728, 2155905152,
      87262827601, 174525655202, 21815706900, 43631413800,
      62767396073, 84411325754, 168822651508, 49781038265,
      99562076530, 162329472604, 156678813073, 191383543474,
      107889180004, 215778360008, 53202175537, 88670292562,
      159606526612, 26601087768, 41974831169, 112980863170,
      225961726340, 177045545736, 79213184528, 158426369056,
      77460701761, 154921403522, 34964900100, 9682587720,
      19365175440, 38730350880]
  | 45 => #[
      35184372088831, 11728124029610, 14073748835532, 9382499223688,
      18627020517616, 689889648800, 827867578560, 551911719040,
      34089138716416, 10997968448000, 13197562137600, 8798374758400,
      17596212637696, 2684395520, 3221274624, 2147516416,
      5584820966481, 11169641932962, 18988391286036, 2792410483240,
      8034226697449, 10804649696570, 21609299393140, 6371972897977,
      12743945795954, 20778172493404, 32317393925521, 8437720751794,
      16875441503588, 33750883007176, 19294655661617, 20429635406418,
      22699594896020, 27239513875224, 7218477387041, 14436954774082,
      31688635251108, 28192898413384, 21201424737936, 4475507212865,
      8951014425730, 17902028851460, 4957484912712, 9914969825424,
      19829939650848]
  | 53 => #[
      9007199254740991, 3002399751580330, 3602879701896396, 2401919801264264,
      4768517252509936, 176611750092960, 211934100111552, 141289400074368,
      4861028169225297, 714857083709602, 5718856669676820, 2430514084612648,
      5531980644644073, 5886594788531514, 2765990322322036, 5319212158311609,
      1631225061882226, 7163205706526300, 5134051346806161, 6271255952563890,
      3535312650386788, 7070625300773576, 8486839496776433, 7966479738811874,
      6925760222882756, 4243419748388216, 1743328888014385, 2905548146690642,
      5229986664043156, 871664444007192, 1097934012140833, 2195868024281666,
      3514941472045476, 7029882944090952, 5052566633440912, 7242799944898625,
      3041087265384642, 6082174530769284, 3157149806797576, 6314299613595152,
      3621399972449312, 2291459692986945, 4582919385973890, 158639517206788,
      2538232275308616, 5076464550617232, 1145729846493472, 1414629757864257,
      4234955737357250, 7619408760307396, 6231618265873800, 2605457253151312,
      5210914506302624]
  | 60 => #[
      1152921504606846975, 768614336404564650, 922337203685477580, 614891469123651720,
      67818912035696880, 45212608023797920, 54255129628557504, 36170086419038336,
      1081144290312257280, 720762860208171520, 864915432249805824, 576610288166537216,
      263886817259520, 175924544839680, 211109453807616, 140739635871744,
      311105802830419025, 622211605660838050, 366006826859316500, 732013653718633000,
      708093522514441449, 753484132932033850, 354046761257220724, 680859156263886009,
      208796807920925042, 916890330435366492, 1058976364151502225, 276487233594793650,
      552974467189587300, 1105948934379174600, 242674020120042225, 485348040240084450,
      970696080480168900, 697797762363444600, 632247276719883825, 669438292997524050,
      743820325552804500, 892584390663365400, 20305858202468929, 40611716404937858,
      81223432809875716, 146653420351164488, 293306840702328976, 586613681404657952,
      579244736985069825, 5567969363292674, 11135938726585348, 596379656921395464,
      613734480861010704, 648866344426557216, 144811184246267456, 289622368492534912,
      580168333798886145, 583062270482177282, 586527957574021380, 20134410541195784,
      613118749651799824, 73315994696752672, 722226319923967808, 866544919202866560]
  | 68 => #[
      295147905179352825855, 196765270119568550570, 236118324143482260684, 157412216095654840456,
      17361641481138401520, 11574427654092267680, 13889313184910721216, 9259542123273814144,
      18374966859414961920, 12249977906276641280, 14699973487531969536, 9799982325021313024,
      17294086455919964160, 11529390970613309440, 13835269164735971328, 9223512776490647552,
      93697747675985024081, 187395495351970048162, 23424436918996256020, 46848873837992512040,
      90635970881848505577, 244019921604976745786, 192891938030600665716, 234723924591453822137,
      174299944003554818418, 264935914885403323996, 168232594532144313745, 205496515053613555378,
      115845124927874284900, 231690249855748569800, 278096756630370163441, 261045608081387501026,
      226943310983422176196, 139048378315185081720, 57125401002455385649, 95209001670758976082,
      171376203007366156948, 28562700501227692824, 18255828490050148417, 19017238714023618754,
      38034477428047237508, 76068954856094475016, 152137909712188950032, 9127914245025074208,
      10396599399664091713, 20793198799328183426, 41586397598656366852, 75086551219796217928,
      150173102439592435856, 5198299699832045856, 15214574171015399745, 26908739129648700354,
      41071440811124489924, 82142881622248979848, 151377596132430262864, 7607287085507699872,
      16222922084795629377, 20997381196741558722, 41994762393483117444, 81620387937024227400,
      151629683110875320272, 8111461042397814688, 9667514144154628033, 19335028288309256066,
      38670056576618512132, 77340113153237024264, 154680226306474048528, 4833757072077314016]
  | 75 => #[
      37778931862957161709567, 12592977287652387236522, 22667359117774297025740, 2518595457530477447304,
      4444580219171430789360, 2963053479447620526240, 3555664175337144631488, 2370442783558096420992,
      33074940346946931457792, 9456982943645567068672, 18904165904966112824320, 9799982325021313024,
      17294086455919964160, 11529390970613309440, 13835269164735971328, 9223512776490647552,
      5996655851263041541201, 11993311702526083082402, 20388629894294341240084, 2998327925631520770600,
      11601404272876608713961, 31234549965437023460666, 24690168067916885211764, 30044662347706089233593,
      22310392832455016757618, 33911797105331625471580, 34700537500516424938897, 9059933670434198331058,
      18119867340868396662116, 36239734681736793324232, 7951942291293543635697, 15903884582587087271394,
      31807769165174174542788, 22865437077125352672632, 20717478763557153195569, 21936153984942868089426,
      24373504427714297877140, 29248205313257157452568, 15501562152129099451681, 31003124304258198903362,
      30271894166234008713636, 22764856469510855717704, 7750781076064549725840, 19498017570327336654913,
      20679370601268721428674, 3579809339580281147780, 7159618679160562295560, 14319237358321124591120,
      28638474716642249182240, 5323058892628014957121, 10646117785256029914242, 21292235570512059828484,
      665382361578501869640, 1330764723157003739280, 2661529446314007478560, 21856159557443124513089,
      27770811825988814330818, 34868524251974757940932, 31958116640992354172296, 5464039889360781128272,
      10928079778721562256544, 36024267353965840383809, 4153068053707681120706, 8306136107415362241412,
      19561382129774310733896, 37340265735709331378128, 36901599608461501046688, 364902440192748714241,
      729804880385497428482, 1459609760770994856964, 2610810666086822949128, 4885542149500071648016,
      9490345770763384016672, 18980691541526768033344, 182451220096374357120]
  | 83 => #[
      9671406556917033397649407, 3223802185639011132549802, 5802843934150220038589644, 644760437127802226509960,
      1137812536107886282076400, 758541690738590854717600, 910250028886309025661120, 606833352590872683774080,
      1204221828098618944454400, 802814552065745962969600, 963377462478895155563520, 642251641652596770375680,
      1133385249975170771251200, 755590166650113847500800, 906708199980136617000960, 604472133320091078000640,
      5219489252939351357461585, 767571948961669317273762, 6140575591693354538190100, 2609744626469675678730792,
      6320683025386722614211817, 8833725674034455701790010, 7996044791151878005930612, 8681420058964896120724665,
      7691433561012758843799922, 4340710029482448060362332, 5512645657629304872826257, 6733709805276808982634162,
      3796013053636584567618916, 7592026107273169135237832, 9112674521263969515641585, 8553942485610905633633762,
      7436478414304777869618116, 4556337260631984757820792, 1871885140048458076964401, 3119808566747430128274002,
      5615655420145374230893204, 935942570024229038482200, 2357795337655473125444897, 4715590675310946250889794,
      7548279334894709188917668, 5425152112872384980185928, 1178897668827736562722448, 3079591498469857435129921,
      9163180881436901855144130, 8654955205956770312638852, 7638503854996507227628296, 5605601153075981057607184,
      1539795749234928717564960, 2725406153025543658046017, 5450812306051087316092034, 1230218055185141234534660,
      340675769128192957255752, 681351538256385914511504, 1362703076512771829023008, 2893054981142187414440257,
      8074683298635864258468802, 8761801784595079112851140, 7852197012273124828052872, 7976818662973321901847120,
      6282230769029610406044832, 3171675611979410262277953, 9222212442615255138255298, 8773018328313476878861188,
      4968601456177162494687304, 3210770542224110914981840, 6421541084448221829963680, 9142866413275825882429697,
      8614326269634618367209986, 7557245982352203336770564, 3704946133235888670486792, 2044947862749186803964688,
      5978561580117994934128416, 2285716603318956470607424, 4571433206637912941214848, 5667325739565347537898241,
      7027746600700757695388930, 8539358129757546353324292, 7407309702598059308999176, 1138172792917161234435856,
      2276345585834322468871712, 9010491567862964472084288, 2833662869782673768949120]
  | 90 => #[
      1237940039285380274899124223, 825293359523586849932749482, 247588007857076054979824844, 165058671904717369986549896,
      291280009243618888211558640, 194186672829079258807705760, 233024007394895110569246912, 155349338263263407046164608,
      929659251292133825118797568, 619772834194755883412531712, 963377462478895155563520, 642251641652596770375680,
      1133385249975170771251200, 755590166650113847500800, 906708199980136617000960, 604472133320091078000640,
      334047312188118486877541457, 668094624376236973755082914, 392996837868374690444166420, 785993675736749380888332840,
      809047427249500494619112681, 1130716886276410329829121338, 1023493733267440384759118452, 1111221767547506703452757177,
      984503495809633132006390130, 555610883773753351726378588, 1137067212816922212397806993, 296875906512787810912116402,
      593751813025575621824232804, 1187503626051151243648465608, 260569245001106837854526193, 521138490002213675709052386,
      1042276980004427351418104772, 749254642143243556376825208, 678870344124240795912422961, 718803893778607901554330194,
      798670993087342112838144660, 958405191704810535405773592, 912191807848670996814174273, 956961023459306174824786114,
      675982007633232074750448004, 114023975981083874601771784, 228047951962167749203543568, 456095903924335498407087136,
      157467911063698078020436545, 314935822127396156040873090, 629871644254792312081746180, 174425993793634794114945096,
      348851987587269588229890192, 697703975174539176459780384, 31907274651893287607388481, 56431716083221031246715842,
      86133054239931346294046404, 172266108479862692588092808, 317461828484318390626628176, 634923656968636781253256352,
      477070596900914046747098945, 811948956666729027143156162, 385957874048077779387188100, 1223565827627723370598512712,
      738237668867918649136336848, 238535298450457023373549472, 1145267738797250142674530241, 1052595438309120010449936258,
      867250837332859746000748292, 496561635380339217102372360, 993123270760678434204744720, 572633869398625071337265120,
      431935398335134046939157441, 1141047139831027236792677442, 690285465882129339749104452, 142630892478878404599084680,
      285261784957756809198169360, 215967699167567023469578720, 47828492640943959473027329, 95656985281887918946054658,
      191313970563775837892109316, 342204175625332057588216072, 640357780619273391048825616, 5978561580117994934128416,
      11957123160235989868256832, 23914246320471979736513664, 63695765081067547923794689, 113413218726788125069532418,
      172953269597347114113364228, 345906539194694228226728456, 629779598992524332081647376, 21619158699668389264170528,
      28353304681697031267383104, 31847882540533773961897344]
  | 98 => #[
      316912650057057350374175801343, 211275100038038233582783867562, 63382530011411470074835160268, 42255020007607646716556773512,
      74567682366366435382159012080, 49711788244244290254772674720, 59654145893093148305727209664, 39769430595395432203818139776,
      78919881726271091143763623680, 52613254484180727429175749120, 63135905381016872915010898944, 42090603587344581943340599296,
      74277535742372791664718704640, 49518357161581861109812469760, 59422028593898233331774963712, 39614685729265488887849975808,
      100607190494303920753706603601, 201214380988607841507413207202, 25151797623575980188426650900, 50303595247151960376853301800,
      262014395716464738498334323945, 144731761443380522218127531322, 289463522886761044436255062644, 142236386246080858041952918713,
      284472772492161716083905837426, 229574518151569104208064360028, 180638372909197062072770819473, 220650202899310476742956228274,
      124387755741563603111736655204, 248775511483127206223473310408, 61337932269107874265969509937, 102229887115179790443282516562,
      184013796807323622797908529812, 30668966134553937132984754968, 70236834007829966391165130817, 91326583891292066242460854466,
      182653167782584132484921708932, 48393685508110914595667616520, 96787371016221829191335233040, 193574742032443658382670466080,
      80623570464613415946463511105, 161247140929226831892927022210, 5581631801396313411678243076, 89306108822341014586851889224,
      178612217644682029173703778448, 40311785232306707973231755552, 45835688728210963458874984769, 137467776076760431545049504706,
      310809082914870380345974226628, 304705515772683410317772651912, 249143409724845753645350597200, 181374169392634156916525393056,
      275299759318255335074352676673, 122130072806633995967257330114, 244260145613267991934514660228, 105210529127599666462124947528,
      148053102343828171362132119504, 296106204687656342724264239008, 186836273631604291377543163841, 56759897206151232380910526338,
      113519794412302464761821052676, 227039588824604929523642105352, 137166527592152508673108409360, 93418136815802145688771581920,
      168791780741146851433220051905, 189307933111208829021459559490, 229709192733677480196087085892, 142505735410297610017998370440,
      285011470820595220035996740880, 84395890370573425716610025952, 214425438940026632635455447489, 111938227822995914896735093634,
      32102814446020396173302802116, 196732381079268988398669032520, 76552112101480626423162263696, 265669044498541991504815624416,
      138451508757642769206391393985, 218463368062438414899359601474, 120014086067819479424543401604, 240028172135638958849086803208,
      292300329558402616505471751376, 227682079407350059790283597664, 247635836349716998939297872129, 178359022642376647504419942914,
      39805395227695944634664084484, 168702049518437049443869110536, 268035406266261412769259658000, 149796723315111131257728159520,
      299593446630222262515456319040, 282274243203387174656736836736, 109002419222194531739046726401, 287315502332935011901666352386,
      168532798612409064500394258692, 20152947167760778626612716040, 149182584313238157319976554256, 298365168626476314639953108512,
      230285200611762428162504488768, 54501209611097265869523363200]
  | 105 => #[
      40564819207303340847894502572031, 13521606402434446949298167524010, 16225927682921336339157801028812, 10817285121947557559438534019208,
      19089326685789807457832707092720, 12726217790526538305221804728480, 15271461348631845966266165674176, 10180974232421230644177443782784,
      20361329485377941515091014909696, 52613254484180727429175749120, 63135905381016872915010898944, 42090603587344581943340599296,
      74277535742372791664718704640, 49518357161581861109812469760, 59422028593898233331774963712, 39614685729265488887849975808,
      6438860191635450928237222630481, 12877720383270901856474445260962, 21892124651560533156006556943636, 3219430095817725464118611315240,
      33537842651707486527786793465065, 18525665464752706843920324009274, 37051330929505413687840648018548, 18206257439498349829369973595321,
      36412514878996699658739947190642, 29385538323400845338632238083676, 37259418429584907055851339576721, 9728029704611030987968230268594,
      19456059409222061975936460537188, 38912118818444123951872921074376, 8538333020196268862817114299121, 17076666040392537725634228598242,
      34153332080785075451268457196484, 24551576113749804855355808435576, 22245223436263122400458275604017, 23553765991337423718132291816018,
      26170851101486026353480324240020, 31405021321783231624176389088024, 33289351240152929457451498458401, 26013883273002518067008494344770,
      24443578508670786606128688593316, 8322337810038232364362874614600, 16644675620076464728725749229200, 33346065089998851755679624271937,
      18789172937257675738318833133762, 37578345874515351476637666267524, 34591872541727362105380829963016, 28618925876151383362867157354000,
      16673032544999425877839812135968, 714448870578728116694815113793, 1428897741157456233389630227586, 2857795482314912466779260455172,
      5159908509735258620573664710728, 10319817019470517241147329421456, 20639634038941034482294658842912, 26349585643463971044515466496321,
      37216247832752470425323618261954, 18374830136167139351673994903236, 36749660272334278703347989806472, 16728601212691827973102492267088,
      33457202425383655946204984534176, 17071670212342294904905670147905, 29911919178170024931139782656450, 19259019149036709014385062740868,
      24190571933463958294899485849672, 14409122354911408938200043179984, 28818244709822817876400086359968, 9060390475229210101854465601473,
      18120780950458420203708931202946, 36241561900916840407417862405892, 31918304594530339966941222239752, 23271789981757339085987941907472,
      4530195237614605050927232800736, 37564484487473914195585964610497, 8745949484651757289124206195778, 20829031446442405254517514173252,
      1093243685581469661140525774472, 2186487371162939322281051548944, 39064651847388627521740233591264, 39194681395958080728659079012801,
      37824543584612820609423655453570, 6687268465644224754030994630340, 25866657035700914368706908941384, 11168494864098487889519315310736,
      19597340697979040364329539506400, 5525966559727617725567380016833, 16381008520972363283982325470018, 32762017041944726567964650940036,
      24959214876586112288034799308040, 4095252130243090820995581367504, 2762983279863808862783690008416, 11660182132850223002494918275777,
      23320364265700446004989836551554, 17716245721229796189837240170948, 35432491442459592379674480341896, 39088284864192377200725544850896,
      26112500670076781925194710423904, 6268976187433806656048638097665, 12537952374867613312097276195330, 25075904749735226624194552390660,
      4288566500260182604308154528008, 2803336606722720215762666068752, 783622023429225832006079762208, 1567244046858451664012159524416,
      3134488093716903328024319048832]
  | 112 => #[
      5192296858534827628530496329220095, 3461531239023218419020330886146730, 4153837486827862102824397063376076, 2769224991218574735216264708917384,
      4886867631562190709205173015736560, 3257911754374793806136782010491040, 3909494105249752567364138412589248, 2606329403499835044909425608392832,
      5172093368812902229197692841557760, 3448062245875268152798461894371840, 4137674695050321783358154273246208, 2758449796700214522238769515497472,
      4867852582412143274539005027348480, 3245235054941428849692670018232320, 3894282065929714619631204021878784, 2596188043953143079754136014585856,
      412087052264668859407182248350801, 824174104529337718814364496701602, 1401095977699874121984419644392724, 2802191955399748243968839288785448,
      4292843859418558275556709563528425, 2371285179488346476021801473187130, 4742570358976692952043602946374260, 2330400952255788778159356620201145,
      4660801904511577556318713240402290, 3761348905395308203344926474710620, 726861344953741701470057883301265, 2037968990069778073382693358870194,
      4075937980139556146765386717740388, 2959579101744284665000277106260680, 4592362903445473784674895904938737, 3992428948356119940819295480657378,
      2792561038177412253108094632094660, 4892329880990150706602696117079416, 2009921364594126823947288901633585, 3349868940990211373245481502722642,
      837467235247552843311370375680660, 1004960682297063411973644450816792, 690276024204043555699068915712544, 3248357760960204967995618426882562,
      812089440240051241998904606720640, 659822670195041634124109992960520, 4495476177893366345024074907195457, 2087594952509728058980938464307394,
      4175189905019456117961876928614788, 3158082951504084607393257528009480, 1123869044473341586256018726798864, 2247738088946683172512037453597728,
      365797821736308795747745338262081, 731595643472617591495490676524162, 1463191286945235182990981353048324, 2641873156984452413733716331892808,
      91449455434077198936936334565520, 182898910868154397873872669131040, 2663062834118181126157658133678401, 2714494315514772966386360788016066,
      2776782536232794317008500169801412, 361268213930761005486504010382728, 3261914137796959095804662698029648, 1331531417059090563078829066839200,
      3627340579662339630367516399058753, 4370347574359627495655851557863874, 3548398290184427362781206786507652, 4851404057602561519194345291921480,
      2204909359549291814724503182069712, 4409818719098583629449006364139424, 4957968333766236793544983779389377, 4723639808997645958559471229558658,
      4254982759460464288588446129897220, 3317668660386100948646395930574344, 1443040462237374268762295531928592, 2478984166883118396772491889694688,
      3566703755522864567962407688377281, 4876524254361052659036464514839618, 1602856980531272698322403114482500, 3205713961062545396644806228965000,
      1219131063590263164759116128709904, 4379500307028846098246452008798688, 525972511883598170903393109877185, 1051945023767196341806786219754370,
      2562270878525754698171384656668356, 4650256046668281771028680202153032, 4108215234801735913526864075085968, 2859134685209212899716944719548640,
      2114896565339501341816081513762497, 3748344375592879721290276562096962, 2304391892650931814050056794973828, 4608783785301863628100113589947656,
      3533234523165633744587817305134288, 1057448282669750670908040756881248, 2648373430607567378115637585457857, 104450002680307127700778841695618,
      2776123951817856973846663415069124, 359951045100886319162830500918152, 3284273821448459645032285750613456, 3920335144571197503323066957338976,
      1304343190821140713788672720402689, 2608686381642281427577345440805378, 25075904749735226624194552390660, 1342927600341270430584826739405064,
      3978155618922450123309423918127888, 4057265542753763310621456336965408, 2922234226972698992712416344710720, 652171595410570356894336360201344,
      3902571375221826407039339864476417, 1312939512038664480261737835519234, 1320743545586370388073690958459140, 2641487091172740776147381916918280,
      3976769115500268870652477931818768, 2761241372465710112774459534417440, 4222457521910786841463306705794880, 1951285687610913203519669932238208]
  | 119 => #[
      664613997892457936451903530140172287, 221537999297485978817301176713390762, 398768398735474761871142118084103372, 44307599859497195763460235342678152,
      586424115787462885104620761888387312, 169411411227489277919112664545534112, 336216493051478720793315903482675392, 2606329403499835044909425608392832,
      5172093368812902229197692841557760, 3448062245875268152798461894371840, 4137674695050321783358154273246208, 2758449796700214522238769515497472,
      4867852582412143274539005027348480, 3245235054941428849692670018232320, 3894282065929714619631204021878784, 2596188043953143079754136014585856,
      358680570291167775228011428964537425, 52747142689877614004119327788902562, 421977141519020912032954622311220500, 179340285145583887614005714482268712,
      549484014005575459271258824131638505, 303524502974508348930790588567952698, 607049005949016697861581177135905396, 298291321888740963604397647385746617,
      596582643777481927208795294771493234, 481452659890599450028150588762959452, 556302625208180297954233165109851537, 318768077360694263413742969441296050,
      637536154721388526827485938882592100, 610458311550319117203068347625011912, 64317483667012058366313244852274737, 107195806111686763943855408087124562,
      192952451001036175098939734556824212, 364465740779734997409108387496223512, 461985450484010598505280046788758817, 259356903075563260558656563437345346,
      306978430520173050982623829651159460, 613956861040346101965247659302318920, 563299724188234267478591788464465552, 413068079592114469301622869640113825,
      161522161291771002151342209140055362, 323044322583542004302684418280110724, 269420519371143101438381599945071528, 538841038742286202876763199890143056,
      326520506495135608519623010384549281, 348692360470212382498957038271938274, 294278481022482915246863230265813092, 413937125570012870355857517666223464,
      163260253247567804259811505192274640, 232956537953425782000365913392879681, 609586327401084560597049008983058626, 554558656909711184742194487825944964,
      444503315926964433032485445511717640, 224392633961470929613067360883262992, 448785267922941859226134721766525984, 187288484728990103422845613190185537,
      374576969457980206845691226380371074, 84539941023502477239478922620569860, 23411060591123762927855701648773192, 46822121182247525855711403297546384,
      93644242364495051711422806595092768, 96124406287745078439706592059640129, 288290821534930292535563658895121346, 651813889853086247883320541322313412,
      639013781813714559314737552504454536, 522491599991279721948854295620039248, 380369202090101507445805061099906208, 91896387174754409315385953995800385,
      263985190501101008922180668018868674, 527970381002202017844361336037737348, 472158121325737048086939014921730120, 189127596266803086441822371033993168,
      378255192533606172883644742067986336, 108803905504462789364154910363791297, 217607811008925578728309820727582594, 435215622017851157456619641455165188,
      205817246143244378461335752770158088, 411634492286488756922671505540316176, 54401952752231394682077455181895648, 517604092750470799792481544281166785,
      191799211161614847286134332366763074, 219679325038994033096603248941726532, 439358650077988066193206497883453064, 214103302263518195934509465626733840,
      258802046375235399896240772140583392, 109564206541114978370043816023499201, 219128413082229956740087632046998402, 340061566683289550552653646055974596,
      124073083792969317227230095774215240, 248146167585938634454460191548430480, 387089102216786457410973673081835744, 220191364623802261740096927341006529,
      657977748550981160916132814043829058, 651341499209504385380362097947485828, 638069000526550834308820665754799368, 496801436083974258454984968581043408,
      110095682311901130870048463670503264, 527070356142625157859695766836687553, 389526714392792379267488003533202818, 599890262683323034254853741275380164,
      535166527474188132057803952410588040, 226553038738446047671843627907077584, 263535178071312578929847883418343776, 157073248946865969569703562597005569,
      314146497893731939139407125194011138, 628292995787463878278814250388022276, 562110988322102654311878430295175432, 367438935716360384120444166963534608,
      102710905854915488252700886592147232, 205421811709830976505401773184294464, 410843623419661953010803546368588928, 429670913775077691946540038860524289,
      619196265677683152275390801012710658, 312858555057676028099903470711664900, 625717110115352056199806941423329800, 185707159164219235869219849454522128,
      371414318328438471738439698909044256, 487106065365649756294799465323263808, 547142455833767814199221784500348288]
  | 127 => #[
      170141183460469231731687303715884105727, 56713727820156410577229101238628035242, 102084710076281539039012382229530463436, 11342745564031282115445820247725607048,
      150124573641590498586782915043427152112, 43369321274237255147292842123656732832, 86071422221178552523088871291564900544, 667220327295957771496812955748565120,
      168817127558053128761012694348445318912, 55831023885212341930112694993668844032, 101025465354348656662472694735579433984, 10636582416076027197752695251758254080,
      148878403380492989908500929756425940992, 42538541100172249361771518598989258752, 85074486012300545580463283061963931648, 2596188043953143079754136014585856,
      108026148228869353480436383311672448081, 45911112997269475229185462907460790434, 27006537057217338370109095827918112020, 54013074114434676740218191655836224040,
      155404545522948274652564781346791781609, 38851136380737068663141195336697945402, 77702272761474137326282390673395890804, 123251880931993459207206550723317619897,
      76362578403517686682725797730751134066, 61625940465996729603603275361658809948, 23817792551444208073770856720015881617, 66780167866606487908604095983458524850,
      133560335733212975817208191966917049700, 96979488005956719902729080217949993672, 150482547620101284976226989013032540913, 130823911779733338220766674310180976098,
      91506640098997444709846044904477846468, 160311865540285258353957146364458323320, 65861103275020347767104762728729331249, 109768505458367246278507937881215552082,
      27442126364591811569626984470303888020, 32930551637510173883552381364364665624, 43242138513902248533957672498660672032, 3326318347223249887227513269127744002,
      831579586805812471806878317281936000, 11309482380559049616573545115034329608, 29040387359859701865937131842816167201, 58080774719719403731874263685632334402,
      88700640150217078599085793338294073764, 7260096839964925466484282960704041800, 14520193679929850932968565921408083600, 25003786001613058118022053484826488481,
      50007572003226116236044106969652976962, 100015144006452232472088213939305953924, 6250946500403264529505513371206622120, 12501893000806529059011026742413244240,
      33557220401118032431114799517393163681, 57505496179221594917362660630326755042, 105967904145923294811099524522553206884, 8389305100279508107778699879348290920,
      16778610200559016215557399758696581840, 168380298004745283704331959038856468545, 5261884312648290115760373719964264642, 10523768625296580231520747439928529284,
      21047537250593160463041494879857058568, 42095074501186320926082989759714117136, 84190149002372641852165979519428234272, 95891704181242932952496953953374995009,
      21642224902016634173306604190865884290, 43284449804033268346613208381731768580, 11986463022655366619062119244171874376, 23972926045310733238124238488343748752,
      47945852090621466476248476976687497504, 140329677961596369669791351451635992897, 78048128574952508857408276685295279042, 38534811769723188625641821759312133828,
      77069623539446377251283643518624267656, 35082419490399092417447837862908998224, 70164838980798184834895675725817996448, 149630045912977790110993680235534565185,
      23525475116737128784738804222924898754, 47050950233474257569477608445849797508, 72250469893711194184892520270060337224, 37407511478244447527748420058883641296,
      74815022956488895055496840117767282592, 89167079623093826273919227949146877889, 8192975785718420816151152182409650050, 16385951571436841632302304364819300100,
      32771903142873683264604608729638600200, 65543806285747366529209217459277200400, 44583539811546913136959613974573438944, 146732683629091216819211258175119070145,
      67317812998299866428928390876524164162, 14841187278673068635038480912025516868, 29682374557346137270076961824051033736, 59364749114692274540153923648102067472,
      73366341814545608409605629087559535072, 127050837804000580840683618072796406209, 83960492147531929949679932429708706690, 44869199425477971292830190165447517892,
      37342456965770613758533827783623863368, 74684913931541227517067655567247726736, 63525418902000290420341809036398203104, 161056778854598622883100751221262700225,
      15279485702185055762858010477127619394, 30558971404370111525716020954255238788, 61117942808740223051432041908510477576, 46355167290663571873636328548252931280,
      80528389427299311441550375610631350112, 109523766010505726735971874709824942785, 48906348560542221740256445703765779842, 37153660146768509539109547898984856004,
      74307320293537019078219095797969712008, 81974074779510772231255977835148269008, 54761883005252863367985937354912471392, 821687246839323906021607092737177857,
      1643374493678647812043214185474355714, 3286748987357295624086428370948711428, 5879022971461766145927106671416553736, 11001262901995687367350900649206291216,
      21370358838413569454713613851077660448, 42740717676827138909427227702155320896, 85481435353654277818854455404310641792, 1094284911667535628398443569000696577,
      1948424261462599025179197861293055234, 2971314546627507773907517591272354052, 5942629093255015547815035182544708104, 10819531125443546219099676331697278736,
      21639062250887092438199352663394557472, 43022401930482957689216625394294290240, 85617734186068383680042873642442401152]
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
  | 31 => 41282318555054306947109672621668262434339709778086773485222455334063532725479485969895330414945322302049099901710212093160151066963178856848295190471232484682659260871624912196741802487374249781223385786774930672375028822188813151909689764506829945004173817326890308118889515236437579667193650046880260551537953939909215296953521891836794943313249541507661695202930689329667067926965996110667037532951527447107787842596425703186663100485439057833427114939124377391684408240778539597021355883770900454408567798522968551324944817880895857447308629984544121686988888738306140945999650428761230257353798412302076955830000022698805923834036659356922286181387073283049482025362200825178251222744332961560744470767035814212317948769124273456955394347045554871779592381345118326268133753583280309627781690779346791465440355578347823327129790118852513240263377398460269516655578602432434100034526194863796153807176730824421877696263361931525641234837124409401042027953171555998664623647268170830120016484026712197758683154058546462993725351351686389060596417568629347764164637498411559065436940086995456538906511713482107420134003520624611718505026143251907300589571490833756086307236516761006694207828573243678989081819784404852391663741760285794581543972510814901025517616901298244450044065519966272262184222486167551
  | 39 => 535159023225042988667385509499909886953251246001027417868296748443577450408543930900640592250650631242051430056376697241484027454806979830504585682212470622036470136862270077232459018537102810964257357148014361847965008381804543883759158756205334433089903561588494937839745640292292020243223022791194398145587677430410303078243521891793095458603266576808379217248453537888344477420417941211675908202464018880168412020923597206841091745214242272085514212904530311687007782215549509600408367891053891520139906027182476124469143430270247805666037347559725970530267853545358309231190416796387928560654747145712675447270107749441440568846311588155794405843855375011271905771471828605920894719370221784457406775178729846120323252687753329186480922536946619693144517052078730182322685400400093699760183829582502825467566562002034981966052644810749901939165094389536720653322932800461514844460300740718737634713461171507956304856678640656947926185662291576988294438654040419641715525535004469002596034324607619072741725796769701261315439150833177583829445988442429865970910710253146408340811438215311997278777905207902744075823075480448174075451809216369050986457455008957022138587913569055819505153175436980456495119979109403744809803633317895089675352468353804141147316455116321864611521257488449236038865999937394079159509400105396585411156633156567328159399664133894369318993229046000840229759350003216003050566921288568046439972312371140373476760267893825032911156119872833840861520981816786094735284523211209141164423505226482667572071087597569392518844318881066901997658966003455872507886116127130766332332528590525637127239961447035293005755631816211704053759
  | 46 => 134714774341455110963156158303345676048730310443787229234649891983590244857727585941273395024440617075766072413481977370060607520604508806547110117853436311291018948843126984943971541020253497584991884355883769235992338947074192051930482515116724480611183782154422753617753512833511750159974012463014124832642825606367359254834584436525760241780346977152077245032715288982420843062507952630902640865035692350706852428966200357801827770577845235271017755672191964803693327107019810371049697895060032525045311538553730369962096066391277675140938230491501526663978468733769699502526349218465140300476171792070351151613734171955707437200930965185901499055095147500726886012271863127917869680947694460472106851238227436003549760545239565404537089876236546372004034568498078227069237682620509940998322668237332682376473569508590530464430005593312203448555239852013348335517796515595362084707191643703907003286337538579760117762945679048140086215790238311526318943285648614249173245242981669410889875837604778261305173765536044975931485450857685028743399084599623339767225811802842654857639901919487991275026729107272478693395682344249982192978060333465513399109255248119677882642731509355401377169677535298215529090810142359347664815779414397577098346936514129865069925989482455249139192718421230114860483756474142762715080159508074437921911822072312420782829300858105220736570337948204217733475278977945668785089286442448457029172107361223152253104407454420848887681896873969851452544067357768439873068795768981712043501383295573985898785156214621415324464562560697026472757773555224290913355450556415996581237859258427807815870631775999388535604398709291650477628415492236605804598240719790974321598734544969232525377374109892730462087502087775727171571920215877503332138413872240069383259652669564558441005824314333625254504059834704239030952141255387035089437713405517008266403414954814529850368708186877286852947274143974459694999310509911904873354579548880901242879
  | 54 => 1716626778242045626809113060353692986769679350556920531300478775735546159507777926330602096920003315378225716442551979943418879054611912070173623155072235561553865095285153281892502392362628228506447439587620836302888865438285668033366944213226300502364989523228529547670397730155220530515762182214205171340550341867869417015493409298544072174577443030704238998136464890865049303564562977447609950798612580279761971156500951626150083764966075274878264738229490205924519623289537670540951177097347594991952851811056557562082879262827400631935282806988364466935142910858358980215030915120189481287856375290241404618356431461675231787228742350630039180627154275763528274769699625376921858401140376853244908130587460493507337339625805564462982649494963089325514799527283729952477746642545484485126684465485058628878234231827091605226206026603416034967070575236474507618690476866471342662789947442500241220793763354321660680859686426618910814692668052383522821490398547042304954874685499104549534673794950393630004240646855691987731732256106130268786624055042217504977390442673390272571653899604255778579048881119402055848685901888253598502969886940228907594917175071546061790425900814837930782650070563968306886045022371127659172873327951427628917091106728549778915233544128649612093008679504043119832594080248199532997069580291647589873269053396719721844470145394552872942439064584597478439887199213347526670520654917489265962166898085038454011876072691239631238989016233446797253608921111531615402068296552455912673596344759159281435846281050205482169960803738802973753926116497624383063752131757049298808614955891940284364396045508936508255284462619225704302892440922224122033856297538170448807034970105943087779805061863765017692825539936901922910450153407466836450866150131203718538714263183470601299320197719234865238984011449760513649272207161838868098838329543642807695948978569644021109539919974641852436025740169367932525046187059797012299403141409174898479107481233472067454767895892696195289570209554496925664665329237720540488965760439984864439953967933434404110216306891785167986267881389018412929728794861751150357440742693995668034582744797820481835660085868978129368005180622031191014760483758834452090220803069564669072548989322756926435900685936190510448645696782852678765341058462903288235324080127
  | 61 => 1804212943911903671611064387237149733037392734465133424271409170633268397510420589507075420397730002982373599154089956197044829682987081691241553899258184567905969901408381140686542389207699269889709891141463556954332013286363580755412780398266765035238002319787153044648605157216790894027589570068192998946968474609964896258834838541389817425124479525146105290531408443028130798072805546350911180873916592380382174218618950879325478907416543477117322957232854107718991103173203750875112351121142980426330539458471890865967258353005114225976428412461817625642267385426213702388683304854096957092024213958145768049031748618008354183179304750199825359994610191307066075575527565701659695640868006013154484246048926679786632766331292476449374024292328450549844560945584228391518146844285138729492458329168721669769300074890533937766269463412037227910500366695374848886883155295306968871021527801409920923543078158709112919226695283187232170759149240165814949614144018187200803148270569609812426850889786911851007290172139023040709516747202138068479399830062390047013696321325396441106338950981662168357439548097928051555926940951545810735520890957954013428986938606700670410786438777252807453928801064700760296406259164590646086830300160104289341555612751274565036302169478007622262088468144355308753225846230656027116791090200170934975778382775237054329204264503719834614948285064816058521765697305805430897521473413568676674135984901373507888531588133345021136989291101933712226507089541060776088433108553404488048627600811188871097873766566146225134576315467860190220936614795870955331224153703427448074619966550554307812679793949424013741276824106180714746664323888726025404209184326486874685206739879829792124131858045741746745444337856909317252018917269757422902677609576847473718901866254491267187980721363764362638289480583429171669031128231128865715399253554260485957170452315729844385310663509372969830023522154428946889500857222952020550119454856012758832356444584576393281261794839091322350951759124498298269226285666522695786348564576089435105366911338407842907090871917640214734770389828460403697219554108789548338246380932793792449628664045634269205621842829852568086394810594945305405787720822501912535325969310106379222306089341101635768497199734282572017603697108965713045988101882354184094118612699156496125762065337040577682229848474066463023347299054529241863990578617052795122131810131364604793439315696084903041789673660442254187812432943952625590905800120314088364894071652076705977824922594243890367291139387980640557737263871425022101121903708830825694644540710470667000775147345685015335285030911
  | 69 => 14647898091035479412597374376558637494136223911552505653020525712727467597856619405624531970398706730053107166400922240639190759897604973879759356317725322855613844292583604311309604103915506907341388286882279242427215511215423630230810841404314662761294667718243724871283694690243626486109885109351999945315235313677776676360848888723640684786311220955769596616710605414486683476333000253818080808725732830170047500681718313391281041836540823792332073660647233486183198403830016616790684281535960241728945901116839839373624964473121706890949485251019045056686412270082053012988421502199301641351735557969535889373195033494436367273598920353094520364516435885364316537394304037234392081277683551390768822946390971541338392268229893331433047469430055178168529343849377628678232046513494417761425671142979120551033679053906022106836278098001925032103175030557017535026814139672754808349395903608567484319433266559292543210340038876800414419967715606082734555927457985537673181303640427615610479627109570887597791107241347353618760914679505653373287472619665077077046196616447748345431900356628356310144403242609327347944536950320121237137678772996490254245162784104393047440418451093947116917090406762893904754707921037620694017488718570252240348929312193310335079189949063444433667437618898052018810066341501186018316659948946659158509215564473684553037036270906290884852929672987778026508955563364502876261845837154328876697968710358797745465253555700148262351289633849407918782198100168156867972282809290519126784895407369383296202208036225643616077106777248162753899146548894946971635680381547365569439524788122481613490335357185203097257157441921331378612176308019523588557922653493677723870050252680759714468827830182745936371022321354350558990487125655690754853063903170734306255915009100757353557450733742137584014228537763233788210385372526546037527117094162419533585262558876993875265915236700909947554974735354529699054614387372676192966909343405350950621488359815441019407750810799084807057642179703072167387585179407685091800220368026000115781535575953100688233500439069466368414512095620419584033689738529241099031481170687117997456271108816199556044762841819392320169969632816676304585032978263827079067403849990225209572307981905307374297576675291323781437662455303137947727022566103779762741463552420443511220304486564068094567291769699859445045254489698593173173866858975889520876240705696627254828065017825873695073930399207394253278371877467232438017148370804457636645666982443054257783225038617608901258285952988328503023930224306980861620669274203523782894419147391692550237469713171796665220920053036407306468588229353538428756078703502872596373574056010637126849594277179611542250498406858976039506075175014809066140244829973252000480698994139429828738868382127979266188570991796065598953325842681020158628148493948171001297564362740462731884429831180299879258913377328049537100287663600546175233543480559516015734935318897160890179121765049958399
  | 76 => 7971351289116276725362416523216881891027095731999137439243738654065948863385330628494187003273922615250978322572775810071699820972302967543388960942567536142322822070761205459974680787964005398625126543730984952332299766425363817855912927398870529622773632643139044459775784270147435274004845714893359219054609730510257134855024274545694126270410135218248479763519277414936907132989222615395012728686357134594426197742467059093956930314265741323743725024348118046226478617013677256633838250846594265178324595990859184527946839141354441811828967066126726095826924326308511491830293893327537410680331699437717889214641868767443478502762316089554238033203813926796659805391984265389809019375804247712206950852457814819446567181834412622297154051568574792281046893185065013271272063280394769033511394883550115053238328376858341760258145732025267364823760580325152880083035515757782599876916923986996784544880794116936632780454963884215402688791454230770102521819047403734830533500522735470129544763912057261624090848691093035917948704804936711362371450646759046036098060807276482706173885216904738135208013801135189321544402686031185903111746661724085826241190630117223821382873077566270530496332595147339311445677926516635049153051838173235879142669811542931517447762113785183705553052597122403732743197848686670487803536171994309417778072292150742646251060273977857474530678731445593685124309653543836620492013224351924937231894987087547610481411113799247233700809976194410948641612988333863030913077932848449161620798638108565871664421886603619178875980923955706001355131454145893890823939785634892278893579467259391896571402134831467600865383919617123847504021580087997701565765545451720121864081198394363876900971215991551765053658597104143183032804971507160700232330317638625948526532785760010958462426992022475792244410915350115661871832344842129286991487542086661474863461839496172574577072578008479394835008899553827465431632946100098829482827989406731872335825596051077624943769935656567038935463952819401075455871338018092259804480750418434512586464913621531670573495040477981208466966072979407410959325309384025081161303897522591504104706180507665897346875686912180932136176306006397492135816390374261325695395683368213557978299352803400406470674104540841362033711925252873829675510865132864782979864655092335791407872790486703848362634133726243552626986227681829315151451758098189424678989062306441701888062814179374196197659218880252894868686882588815754798267392327687133710274550706086044931189799294972064192163582226133711741889143026700359123163088574246540100517659270595420443342844682292145811701669289503166734480292340212111796970546125464371861502435862320037264227003690541150212637814955578685691260033665064622663848668951621972196241409883873814059875797284767862476607027332904759658814154129324616855051513235935717752667448995600898420515003327393740518406951968104852993432259497090504915086195405393136320155821388031771071384621191037838635086781555367643526287186794698670545085964594870379679635365735932584019156266527043640672276604112429008574875585185309451066551643596516987573594395222050868183163946805742671470389655242338480725542818192989639141980347805005349534310790112564101600325579200684261332557585461073202520786719482052607
  | 84 => 101327360810724541200943187719513069791060753280597570613561981217240982168249421174196630960871661387785811664461138683314897052251537514454029663713876110124258577519023888896421026378813220088741293976221429335356270031990849153113996629227489783573387387492422565810127121167548566419288446043740399463005477813583646647989304499077564631344338538619711677647146095081202786475421974139292059669358658663812954808709720629643727918755663624729279842475684586534001810140395846825894351456747866972378503631639836338572789503507483857081887806997417195145650200851258096538508139575456135498172992284921788494029733122173127037878161732650068830105395804867289607904002701559505117723670703995170490502115622433172621246934743742826038913254210239527969906276550309305949582938808960079042183136043769607615449742541759323643897905045386576042382178406266470555013529845286092466053339556943953305183662885093168219833134454108153476634708350348327828166459159330916935469166864632594445976966103800406846218290467128806400950485183691977856188950352949629219849092567937091636794992401342039308718785895846315147430627877904147371967051912471902029848559422498034971229453780728619922518832692740626569946901398152452660116906106324107486112017247038125957765158955973829366652805526882724115880383893367257639619535895078123961144926266736682076386216210191240946998239147218890190631887897224076159159844520978436166501033972621039507811873347260407692013903300512914460006175541039891047539281545365990657104861558850745252204782561130579758895936934138137183073751756697232282187022966677561814842223636370486832808603475281101083685728974150241077145570739594405623532704714715917244158654184928707961307234640932614072408698948971295170013368435073477284325322681622257231729341060066448530880303921479138116387637238896743992057416563347042202520180350876002568964937524035390667399809090773963944012463653745994771676358339920147882778954124313443890673807830761633147873281152229462706663648445135308385357527941593309806390783103244318847677605244271146875013700861179722178635197721256102275489491639413195076205179873631386436890500914062063916776282259395015855871601634464445602998185274961861633447264195470343695727026080972532339156101369264665593160412943648749009171600574396874419604917828799160155479240921173070739790414555084057216025053700760549128831404301420265455680915621983444120961647925526984193877661681154704288830820876958172444009820450181761336395922387742214052099538962711756921050745046111476704732130574242179684929400715145279532620861367239266753568133322430015682431064821464269064335529473043186992362976761295621203271997680609547692803366439531424914754674223374854399169497738581992575251945012541348742730214881895731059102010354720881693389337390417434765861066413250540590689150671725410656322312041953554641884550677844335714177601139360314007347009422108984124192387916701963436536171423815043022641570933777212010564524012751807884105458040757879411857449335051763270072443564242122178319285064146331226915694463685324470873009674809082060103895689113970767529034737466746730569057758064121003561460079250613599538565387004064495209893948372406021459376200131481780560060632336641008315135302477664542047713935065974628145922569532627108025808753412499990998611416108934851813466532989715999713822102168450100866064258218193496066090794044590869581925523834118628865715579395281301880483052862854224976780648094040866140565824360174505628145366424850476355521032818893899236799379194500016708773523702540361108278792685284752911027985735260647975128446544572087009279
  | 91 => 41728914947595391343475725751457530194080976322125273401668160154420773987956278316085889360786787723549608405105749694681968589871182337733858141782693184249243830315706186849982711184394112961250936558501357368592814534021109384399148659149065714668616272852810387901199077669887514457593193960110153342753104853556119248092473330319393895410254627385424246310437368841990106346273871049363280499388255850689791766073419635251769199512470207839344627086796731638446421879614309254267002655830267879262182658375713237367528088698800770695410024248522285264364368184384015812624043854325518384998779187526902519540324145965268892550115415128598801316565947610997328191291622859318122777756239703055158551108784614003050306612908226472411338430835182273960918411223942941664649160769966694970401248105189407371483131153114380543233631520637823989760522495389242412725861455796543677244626071774793711023401697291007070387491285708560576002538502321132741522096176822274050698394241102512867209598226070496429295503119676064853557855689544213546837081928939700958024516503913554990082260299764216881102976647575328941499305593085265901140319509580187964926048762237912920131654993831117323732338133896222872543975504336115710941632811466911503573053620270487288697398580665233538774438095864234680885343178192240367921287829595111389386501252355821704983709949469675657992175766111092179896627781952799118787728040616728610159357765339967046524705778544231828976736786910317746571894816336012378592488558781628237244102422760725874309692196053747479625437074052059456825076136799577075263602662662324728838167253701638160617193964266855133861687955123221311023628803849740257031848445593894114816187475033930470418913758912243833613353617399770008967723749215072868193914276091447908975950213332395405010484705148039463062335324863577181200586157872843746053022906849767684623435784607383915365376741223063569779829353168864521999138571259755128421143853076606431509043662852686106051827161833804572312391928104791399430587653917495578050370877222014113476863161920349220541579049358786837968731355682358688038014149398468932360339074594557682395259231859543885288703097565284559953243274264043490544012862458469474481135031946430228772966972890899925339915241442724934894465329987172450147113674136749152582505351789593436898672265399008083091312109766222217556061930239853834369342739935530545345970201740943445333556992514939599368124659028031901909471840242064797593966098384111393581028081781466019591216899822901560032288477882450161163694011481517001901906428922309483993014075714232080196168405212862975739392406528444565333300722815463790656990163403959030998490788218865610354842283772549141888960750354238964801238993147084562652820169851642688425632157706239845290135749862682411266515428694411162236115197835264077046275856241382214455877810460215257971114578236592124193717644915167250177570889614356855966658031591206780284097377870379467056005240421764269375845419257164860925025832345415514931007273519382523011644127000040504932052903934014342311629162193487748702181246121936537706487052464724652935283919943385870282710601396452559839797094835751824671172764812555777067528591839322372654984316600234331364199722087327104131958882518809813995318023953940668806714119324457560337288219936896758265730696645348156888174321291442662789696506247907859690854996265058014072702496819652862854242332844739440020019236688344435885759903401359112900554666624678010575748515738124210824368198210197054240517812046556471098684081886641364294067968007065064720758259053923160745465389966207249276583078091937978112471550707247773073203639421807371500662740020200310746634338923105294675159509419410791773704051860560394874165140829883214601458647403485219959157931375021069376743807798825512029898538882391392205099970630779441749365521309718577746952924368029769922043598786214110134455662007745875988604099085040130981887
  | 99 => 171596132965724932381145962232519298483961074830098474930095336578337661834942362922822652432122797743417182681801588260598428864965018578119017481726200953757207652511439117680940867115251353119044982175472112159533252856251576428795901759969335706359291283467920915912414201541494969111366411027391517355307301171361845671499366579381245349242843721900764468093202352177699158409400571432240014557761466223437320369320410745956460024451387454911769077543768965226285555511210290511777907106862978936349767500882605747474611200228264075378447852597107661050209118683585252837380107812371635298611035220824080048775786609355036085569063781905196492991720217986369782200812425584030596434927199783487439480864958723169558686608180689332843431762772045696206496827568499290372175638506256696671358653890837544827033562639787375684388437940305087770098775971651956684844664450665874260913802108472812708623788180370965133225880658775567977812931128762725627550792482859978207337324249793764883326494230813923885987081462740500804759708183965719223403620784246717341423832038316862720446757708360978900023114592832601231208342162083994797691398685048878482713150503591267734101910572508771985664135437632184077438258633989921728847264496628161604358186762920252957364810472083261036063839372080881422679722978707155915228742060437904033625570149285338534462792493156472442778706825009680920253113889983477664780717869850825218050913128409159383267738056011312043751546475980902142700966782923439529963663724442972689919960175083950668554094537466219527327372157173030676663673303838372233400087524974116031250228237820292869930097279313302500247312799769086261523636366317141137377758405457782850739636257792386144371359242127159375522422885198849321898822293459037776687991504851928767723484371185429756676201637488296961794797521090434275912250518927427106048169296780759833691834017211213767275103109732363110432727921981082159798770204958707492394950220404208776899760803472560130774357923433941768264097627036213163539099259636356678103866160892728656010357089082138916127292537090237279844622921262123264521117162903755731193107978714895946451135226622979446513555413169446724915179346921829989771237092945716497578837578772293326147905932550165686109877235961915274963584153457013306912389285457439213501070292371964006032756636520926779916046359921329772514084268257440642198271450367773886918624941997744316226985225723766528059006299031134082205287416403558688681391724701058639639839782340542435933196412816942943102736084155481615912560938519325205876586736528553920428485708917627892779664735226203126816932403811290296474381454085519088969337675955577273979489578451669404991173789736275279796485120528259675237187925975625009474484975247090014633394873185774623791230104333069568206072608722238657331569262624030926957890803396907456949712586010330314847199306588099039726679143994331921086838051050669606516060842249764497160410701065225910885867222021974719507224428037051309699989288790788352011246595347538842968349934465093677789231983018155867717170540709698073801002530526097011069765400326901637638320578471473766522557819909616387600034635408784611907982932896881741378643929734100647001258420343696672071285583558800827679014922476603578367953662672042177578765765117376135067030713983133733935849555046418823449635096903371428576667449260682993853080218993571935933528099796400339020171836753900544745483534924833271178167776883413311730900714630521921763798313062897612233414598429503819141276999197916652918242381035020509521799507608322920072766440574645693298937098663243963119475661814014892620115453560421742568880497015976112765941806803124477165560238546927001150371953289617859240512213730243783211392646343805876815601055066266394047537307090773103466720963411594341975668363227426179517870664122734019941481758018828431364497455668461722394069496250905365704832849487913561096981331535282650567459712988556310117129413504765527911983009238640674263424721656735803120638761535254479299153619165723084277799009302694014541668698421679796833044855444205352985329450915541717113293205613238301569582737472627123545926310611476545884358385964025559522538648588062383543462883616131023031457550103021593956057855296211080033737221971602649308924477439
  | 106 => 97809919963342428553882206452913784626798994275674830899557201865815133166675532076008233226337611376335334726319894056866815398412486428840921195082879475211496457732981923720973987509660369162505479250804331850565805343135144063955697224802193319761671555532103317961949011620542807779045074303032121901552660142965862089140091035635085933270080260102413146936724371824958835448207787178586873922113376014518777321687731011434664745010440025318756231484645672120318055013811958392874287791986859805491618730692874506365707800999764444144960187021138707707523242226049377013933480028598010926315985314724930537619277014776043795355819222613720202710321915741253121860752550304784035058405932019914520125600928345913113182130740058625026906451787634587632567024694746111089242919534632977937516732152011168334909581106845280791108101820431507911605319216020507093951694417955777199800475227048635855615522306011679439584009152867324708545525791955482291342487678398732886825865216032271728143536173844878191541322639574774158498768206061145087767085520620166804332918556444416635019981133304018456456065908257676080856702346282672011395486752023100131222036127444354619252938944393058913944231009041788320985038569282480659568675061756129962185977211268540866870651105103830310127374460530736137171618389145803579192590861124237555739678904963126028514134845903231217482235686418055431413608087199862036415284010400394015258140916467696640596646674911730281310886620386543836094659125036590066008150309304913800238375452185959809825693334041095785501776385533487982069565692365456994595714732274724985753219801968484636807020676071403471299407549610156997497502388297550232616857079047774474276515867175934774061410492006573669494535538542847152462204868746700306180036562438644557614252779325463567379847522887135486185259862660858984287872863489256981322414094375688243124274761547216311855303113249404519611655910933558230996000383833680156897174214530644639836315025972414354363148262841140465592873851669480816445614439166995778152943753360510956521059466469335123874897474217915637524319193955523256952598275053461772186413806821635793944103526490811669387736185080547833924898918125999230925249525076394075425522460101589556370665806178681073466438413503091991448695208032623155287698121698227158826110088813892877693374372061247312181788743609747826905491735121576044599944004210459451360707289259171620794153770981154644270428669511587532427109290516719953905740838900590995591018623172019108996478804461450253997313661178402763034591042065365145230872172130763653685075157341789488444154966605046988679761326075918930926218038180872288158347522502562155212461282207806433520106917535283770483328591343238211095266110272755233310749265919071003924396985356848098189710873338647833821515843816984111241249556823065352768187441585588639824314025310436288934480135926083772902917546679912791859464959295153585991336271853136642780878261766030286811635355846459569251778616289198087035126322452128344808874070224849159676475695811901635431864268332365216419586251076350811602168357341611158691279129216168048483500323133787786987632298988442643445419612629557922091269057869952847893890980623452455300866753114821059393383499837675506995687716571087105255030530812232283532832635476349368862318540642410146400427764320449211342863345974715084617647993468254168977787283136465583355559375799798782393266387118007424386366974423427556446029127694144400094913439998867517165076225830511300339810745236875931399248192739311610236496606046106692611390120161337371232974214604796970230637914710033679697934363532422873996051952956194731495285466424941289098893458951401123790629098328586075093235763269317645815240036968415676479752321549972723090262423740522426921797906046482534361018762599356846626033152506951725121985024426360989890701409535007195005604258832599723581146864950602479214120211787013009617225133311354743093467225335809639555285815492803307648033916442560828890610875400903940477765849310087403509122173031091522422206245806732932449716775044414174732997583738002111644585917981453981813910251381313653648050702787906034575131518217988270080404358013244007376273739730904176340205727696132570910865298538730836062824358652309353261638332858563781059574375120221424121853387968050560631793702258952789168009136697963266006507147671229465217968548147471389423721729205244981042983426106552477499207879726423033304008791206163066147010042338401881181035676466886068416567742411632838027656787890252264807838978596341991564177498828887926444055236453733571369384280063
  | 113 => 40280352695709809077943924918713218935058040824234866983897461865959000618894536181288792781680157661109058328577630371259173305105906059203841084503123831052080925823177122350996518031007455482325302660026439316777393645370780210452864732393853084826772042733189842046125370799924791725154551778788692105262571309405595735999370641959252152126434662107999247515701434928739042091152063421490518431004856012605220146564404568974886372764493853760462988337005057585453050569563565532736144811053149296011403693375478780392529298805806051540554549584538907522420424454053323886233728990200648538971168705172743432334654671163688412550829272594107867661048460452755370971997728594232288462358612671731703112536296200105334094264076721987608453821547157121326858947951359287378305205302959273037795060067785702708479156190767466823080208231272394803888206836106747121505657050600077508397164597304935584018169937336987488100005129234170560090566949712756513723129348587195559569210578788298120554958736612758801301922905197272393837030269531648207596062387637157513350490791236070452949205866737054153780588852721199093318227980773140691238185968853771268377318547488290740637316485201160328673440559094558563023146308687195823195317080071900640002975331390462952050588000554969005645344691650655451810826557131682540675330767231411970100333422932475101597030368355000896583792622470031494839471239203193686230338636329114656780468852152063346837564352237443803361061098338979973163308796015878361245433847245456040973836754757673231237892156689732635308940406372266301272453122125958185062548791142931450259285728367400272738596959773816299923660163289966882737367234456250331383969473650423638224068393572079367055227852392131173156981682324961944188137333812301709664186108221160691056497490628389480963318603920909628329627708170153524216626620693588394676611987773502489354614457859245723726169604907777586007238294819391756140458475818820593626415064517792113007879173906648292326612173725850204262992751474392500104609635642225116829726505913920730236958914401799716433213976140509165334426201434159269256309980639423784162228543213117786888289825123968134208037218950662880321906461556723783854579843361506473028108907556343444444910311157041466361552869022417766079417510011281265177234805790475766698308327870302384478907532365369684693555468006252042747451143459149475038651617710479160254687260960645270164648542238756486450702413437940048970943116671463698125423915841637828206305432283331881791264611067045234663113084976533086815088410152482655959388774890276339909028020858291267464892451399296453638574644886214348283446708347179176204322449098085823035002181153249540832805980043361131044016176085070719521123934246878297531232665392915653125165958701727253148924331062563636919851341120713779589644207897263936443781162699892340832856619081732826909512438215611706092882153014134602503840190499233692172501202565961360546091860174479286345606579633431341243317726314260153330473741816579320161444710099901049497061525250945653650033569311148483496130927552231626854466709646834216400427796838425357012092746157006757421040930696295574972960959081381951452137175203473030452114193377268833372256590186422016076376223180255918214642749691346349318875122293696152980053979145180193381348372660080501188312899896566429535671662064238362905954856723192159345306092059616331500025607847362681656445540211586047322793502707122557953435976967432526251086660714698964867123127408772815574493425587859075637668226321569749433018554534335025303059348641764752050570263440036968454938886752681201384371143591118045408756892280692204001890051195706412941123485953829373070323531198824126315284333154446283292393829398802001096958199143667948645571107450944555924673633452952488415219614216482306104103187337625776075296941165456127840383372620054600574507256841879160256528936013493045915505460595360746571598506595167199169249841489396975778026105821965678897537297783711690818577301555328452540627702267673052778208497101846398025864518518882042051101465793485765922291296220160805868612052895072098293678369955023769282142725412954336702842036733689830923737445336781774706583542545531664916756467381939100597751260005648985044292244210800238415286236537292066886425960085319017489825474145456365349581719614945804734808641214413832100855730503772933773278285224253253444739999206168142808436296820743480762756843522349913411573326199472950026812489704221141316005815877652616205837740866980024541567388120413328091258614698295648523175772859695111365138423812106167995315178908804937772806690863242329730584990683097033863725998156078925106740960691941286341333657385375376221919978337915297940864783236479997153532770080781073884883009854028808652720776314113518249731293537422056257261587415928526033255298239120362997929276927937668026031861893040734745380626623845003769793216511
  | 114 => 3277744872688434097457537721685541969162142290459622233043698398491210600080079828259270054655090234007923605162835155409686209261318365777292714242934537092383355555141272231265197870646516897978972342291322100612009247639532336038840664788560310100890952811725982703651644434113199222270079347055365500280405769425702589274449141263396979476604262143350526334803466962069374799788035158301986068701645783508321288333524085487357430784554179781357535156598419158456683878530385286332400964573971459456378692331657238387120285347363336355107660953555111501073374289820640254631813560175401948534503132504417869612101172464086549762969267903762917778927849885097715722524545511029615818551473513280629716460170754082419802257514808785487773699353207319066226235421415140838331358655662274743425396769650730622231871168724817727986736200852516566874285743623707376706665764444524260097562785973914519893191159073295187192095371624537031256670020986119026538765622827677955755415834450671822685091608419590734358852911566336008968275656883898543074715233876500783287841309597779300589816539752614285757114831540590510403727467423879899778913486070678554390170336796715655802264200756059748179591370663860731666647297111753269685694318422771885923671900940853709033583798157195139404936808912320938498812103100604627677947473147134315534548566332926753006937588660255538074929273326452150172841279904758665427705168047605109454802425575297670363054742650670580680401661757955250316934196763726209898279764142853173887832555146044510023894968329827166375602709338808137898500922357337806008900504680046418357653163763976186517328463095376257404150742090552433721364956159235988064606564615222201408171742378822760356559387231620223725496186387756976670637484589507737182365879968947967035407205218922670717045991520722020460501225103869035894319652643254231905530786237474504442470262181314900043220431512165431840288887446677015205143071752110630844974535535233494094501333493979365237304000945043866435202551762208572939833303136512427776899695639974699815835925154874168622537187368391480615791692457713444771429007117677632234451333763031194665032422294508888784228520983172059002574046885158732720002121713762278796720074915276106193812048319285300694169073853848354892785261800412653712157741145831702536580941772463560152177507898002961853013038871727199509337815380050756147612824299984799871506851832468401393798190732400662495985949032773554664051000881811818462972386094705946334874726750031186361193046753604575118954364827601474354692070136838430536270581202500499084855215450107620839634972739782746235224335497335252608915613892448812148456512860085142057913192585067863499302950009572986419918856667504394158899693067872600572463422824467852258978068650924359032516439425797903861039229573348065769628970175807386874027776732521998136160598664579869526943274122387604995624934111294794170052474084289865857177825253944957816532260574261813644004034546368488217548624418738896187752896470770341399296410466095213023375585342495209408738989503567704621914630031911088501208179444180984477634855928229893907673917737611202832727469559175840208751296470016166600327217169703421570447024793802611356068449079850715352525210112144246569811854705653003626941141196918611456013335996607760030538642329361780579164370615268552939352818525748404200621484727617224388779972845416609868787705508772107751642644863992043131514407520043522787953388877333216065963291152719944824471952557011119655184925972423525068643033431363977036775742809549315769122658562726571083170358391058279522930691221363059451712750112321702920759154273399287308998990235417584540773606774193350948783556942312739765122334943483426054861130103504970084430865727477901342784189487457297098862536992928162499797082271651698540383352821793263342055161576081007147562328170432271216184532964872566381166143443758724641526607640104846430826705289579228232784372987237826085294972743287590953807019001549358854093221076525078883029346078416336590364284939856419511526175021021545323197854376145423170844460602405437665639051255087557992241922576827974854459626665249736643761989203728417565310770879185437015033597690529883191786363184385259361386957710984393564934809121746418858907959094125829994767214700050957762523701376010103615629350957427376535917979676415327927464743302662313674008239483200494204884251334311559657190890839323146791548063427257805323461697432830985384989643843891215870832801275318822765852610352429083043261407232353210836337445495905340528748740110396001619409381956423083388086024751206466516554662543758630173926315737110338661984433626093237230717209621877488244943598793485284379262675559595782867747213752556611497995068600386661805099124897374300967994798516106310834229586192567553501518221179547201712783010186538379830076901640691453841972472162136228421242850389862506451137799511411433978368736967075502567541805173111259135
  | 120 => 7427527925818980258916738827223430701167904849716875928830481459018766593139723335197942618699355533675543580501631001730561031933455751401301981256154455065796957917430441704253577202716344799489566660112507395429848880057326038595348960608373108217914255679590138079043527611085851531871896588926880530769613951188518751510419016996472717460776235038383655630175599837195782919988223927159672194825624801725462849696684102929578396143284538144262265826261023038140340315555903536560052389528087954063476409809640960280463918719215982286439875530337046051762514360475903689924700732365168771155611650494297463284343847428667363351533935706651482980564130899154317249165466284413881197240423777857967021947058249391020621944230074439620555645666684177015236494892057871849356432694650105919683629880043958570944592799185072668329557064233417923744086717402075647288933092317739251688534365373882768446507135128955606022189449326490873309235798058071416215853741815451185555183628308691845281837830592242872994183815242699200912911231282422929900821683086458364614882939049229131465384543215031271130011315043768772388946410572645571048311983846641667465879839283200042650655531677362451924308261104486333679726963376107897389386409388384698760604762961578502097238004699406852605843869284030692596563422007725063035360375842758446322026329919580333154220146484046586952567488783726141587096782516007423047221215206637354386329203841087235579012024802466220034134140608541325286526295126127589288232242593807155973497769170414182794980328921539518746982029194466108299561035823787886862923133528458140179971622177137210166880989801920729262443167910066834942503223941143561031712466157732709153718658693141319227816075297025655100789964061515052753743857952640479576018534779936100038326434249413918772296858392514669098343931354692222741650675732436930036035275581499463112706551945021893639101322315447015461838279053091538977896815920937455816882802090363504412842797805233333620564225534301114534395960041311152356763005660813013579197138005350852491526906196253182002406034733791267712176375648102361720351058129964230552598089600994754106996796718748227194622133791519158310498862941814215868657544033699589989800418093586723277731469546469239769203047751914733952044443240299319972965438745746097704671487836753572568720993941574317443382829525716107988226351675438424801651145498251603951776457852398444888475440297245602115651313703902767103868168798263304896018063008179073531919949903588331480640821656385587154761354243786380488496622530415311289486974890594996752733719102884261643218732395333294861462128000652363851526523759143747561256354189887751882613885374531239964164746169575741927377385387637179477875870865115684312607518969813580066640339075135242191588711546713688341340800493838007490827322774740981026946188572777535662773450258205456028688027993443954570210883221517385722614803109324572348647444869218893401927330863416577942670572581558947053805416165705623860174425720953831182882928052904561365137911687330505286197685768700550557777179186754637819470028192216402714657794829507222356819454599806596816082166915554459520002460875508077302168482416133751188558445339416306391798412900912888470102650296979170883734437634068647545877412098635094245923129582795314537531026998588795567625232505229023408037442440646898576483675637586146471130304820969430189974835337866897655897695558151734915768085811347894495511379804743486900313394712787025427242498296036796217553774711446707903201795919241444579510498163758372640936334567644489996291310824401730888782262782899409311141597927875136636672857781971975303818699061917155856120415443170954973848368224180297027053293507129932611828837585964654605479992547728530219184074115486908324843445172327538649100432453701296770116250771006240362329345394644996400549086297949647794293639375251480230988934887405251746050817876555892522796460216107305337247241037349223824301222491728544424595118592301110432274284576271751918859748444955640308972035516983474887171436319319881911684423061599994390347989231429398350343920087286558177496734944675650746717385751989846557545308618240972279124795843567381194385193233687276405120444958813887703922901028716347600572657541501486858908512036214071673954164458844934694326259143269175709315015853105695031276699960905397151587473499706696381367008888950071141677846811268596538059564510206626975132644795965136836835592654736578057567643382155101632602816322867210898904298285551463056968342561417252558767463169100906896493342065189699577442557589923021001459016951325073957953724819001488403733036897904552292478281579149270621810320029325662324968701479645296734766417884652849635767294869820040974440433524968214223568334402446952088368658513591775191226548081048387813756657437220290700342091628600103269107358123513971685389485307383632969228107734428350517526412669089617861627639061232677640425960207459068228307586890994854497463151908331790689108640045758944833413321533509359461534578289290994218878415239841060694340274803585657002726294378285659759204591837270546987463025295746898580219114330442931407512674778236285551208546197971998816721740787022456302812004351
  | 121 => 1001097275515055373566607470590888555183378414340818354248946891342614065153424632511959563681939094344210880175660301524942586708281227128672075636988298872243311391883481715009139700594523568198690402013154406932180047056669501509665581696748792765367765810981761349189976526384307247591829348877239907619353263739355231760667867970069034777621007651711646124871610396991123247400262056619416392545380261666641207498830558022616541704064068420034617756989524836213714921252722351484521597037521563264161799201186076342778159342227428895420408043940194710352529113886694061207331273996008544786489952158264518601842825472748353657395854668453669565569983295435389744606288160736655300691620848334592132221183993042652560202639094223497722391842070542193436015555973738059697216319668013925390394559662050774371061165798874426952373945453137394353587338291832504306476174444533471515188013349041305637880900905087642126377881029614779249843814129670539024927067027994411354433965433615284880700171426358136550648179747101190432894416958551482275887905600980934870403597268624614539352824958569935428540727110763515231192492316484347197463964269722897937953969036062906626083115484359153288363776386838235377151558360562414763515093852665810823444823638205064411490788795146581358909755940227292923544450199755906286504595434157704357549005147901812618522778053854307508562045485068540423666385892389482192988812690810470435369483448432506224844141154786535963389621104491211876758370277595313702559306147289601548296049807047709763481887433412565383122275787440559703355092073508209102816739651450001907830883871690928356007110945703505080815689539952491294057805930835594678555438027974272757092488861121872926983420105070094599384890229783788245246345602315873843596522646632737656004041753713864081488857693532147701632962157946692841636084371264905072166651902357752888177031026092815125912556114423440416143374828769838144614090573618912177247025262032754057463691642080896969705710902927953888431592034189348028223429919682316471050342114445631130814885696650474999123396475997393644786336416402500150338798075042581178666180236404546704284402873860320074144974287795536538840360566642757280805019605897252595945899329303422170038459172740270005022719781003805422271842915035843147243084916475570591843258823649876003660972553506882674179083068264760689471092608589226068926935736042227521519379090654618746156418760853880200637528509521144690772867914405570161765088361769282475069934910172266684954533499051607088376447884896377493210432438918534456567202699726555715670478335850792014965031780884664044892283995190792558092806597842828458784202560580442991308659668787063304745564686722745556431072067066616205017415009296455718493217166214069167353809366620461715763152292063891164461745079324871870661085326981440695117308726182036086197038812416854707456170764902543898659391004882448483607228770888486222912694329703130683032727605440102689108344845235179889124505842022581776259336061500630939462162906575606588722098985542390478398354100626963382745747177930149610487953032336658841814136436948508089112794595215353822744005550042913595050919127749734936441404879161962493121203971021651005069367680845971827439883935954598381483459939092051785295096027828864847367142042237923610643996566077824910247722545399957810133563041804723534107607784440838297435763561865873528515639970942890104140552588377800889418372056368820982984689155751851025188742579447059939214842449697500398053444750021784937675348604495832443517602590003552585951377322532910000672322479649821158774995187105958803036750184543420724676251813996178005204139854165433907950831270896044138354230161417341605940243262965238833359350557416870696429871244456513303761575335942937917844616840889010443937405650218015191169195999936524962357280642630648945224995572516574800898200034398705113033851157037885472954225101985776255159556128817514759917756140907231613998878709445461142656548220722962271178020707059758922208652796392594571712666726640889028025398099925677291307195187631852416424574114989369232159227355259034182534073671315878370458784385220800069750155331422902497074021332245674699932910918011298762734464470837447537855639028519938470349438242514351997376757962150171262789124843268912007637278230720916451303146674858034735889831914530161102101322976490261693189029349074476768508581578414752608044943246031338289457649840164568215936068565162994804081103883566010753798910598068739914783412079787990052117729987952638291392114268514224120427863355437477293550068314838949748772242214620632347448445910417668629933434926379831144188412757677782421634873871921475114092941922107083887125560802688661041946039800923304465508351280763265002135707809551134112513182705696680312631476381016246317093923750178551415863209352294500465366749245104275091092914410132239463408139174945989860370329447049837350907962258966325583760042591066221579081048535764605942753439720372688694204743990960121438538894204255571915847504098319741493519665190541848966794228914641865926509109917790044782277910907919093392911822631878652729133553971696945729799065970679515040742752020207275819360095477606127654979145279711529249110978576396171897123321719061217279
  | 128 => 94414582267723474179005806606629297247612892773428658994213664976330387504088115362259616920964788047066077160466737861983020353068145204527413753810223887050123596341282562379024894864258838766418885720661911101313970734514112800772968389248627441759110454802170744741017692547881471430068391077015107093912971183366778979162431168940122609191631900456280395516407575237194808084478107155384633419388144657338036671804948775836234879367209829384566894807381816238167822228693941035407884996382967790172144050652805087698592987393292567413463600195690674694267723652888810201103120627598676853906653434664180154393613803200200308373729296993240182287809064150617630998374535951455363519366674964937878839650532540624764788360811900457783163511305819287104063781277057779822275150808269962222883790527769149282826683041016863284760271067200010881109894547571191583618709288841321023712438086822715515356863284714003597395785418850994461426196035636402979090015147920162086626419510858019183074977593217840964231824209337580283206911961599072945782293935528017531558635264422700293337964221200780332287879651566458360399312884101462655300420975273505698390835073648765981543638627009602631374891674491021111409011637340720478115809400087725931029202795803245152219361563623774469702449624447768050354692531093679949559176436116167459767770217832928213213078415800972255990189953714334493825741827878789315114490999091405519494623983672743384568000858885411343054549171123902350151746398277340569459340090422833442426235760178048959312097634437498939313558972587698993400095599425820751065901821200826744188013766146923821545969179369818563373879768952041746723814651894349046670038059917751787382587268038365536508749098802243782147330326287238270424383718355843666979298176259306925681344594102425213081532835390086462949751374782468199268845439433434257478979138057452340835993153490001209195302827159155594438233748607298857769401902601285253565821246988883392237844458045891362079101326584786710405099511786406726023434423735583803335390048825065304779701093590427007055406764598816498689069374313660871795300792752639849109872317816296148233080833486600939440096825055690377672489993232389656348421968091432027275634056957547795667318935360168201359249602614207492453715770589294592513315008075417874502810184877236498211199426647596944294183843556871538362871451149073721603448008258847842925373423760185374521519234828164308467080728982694696643706939985907608462501428964467364919080465991040446662572157244521403987635315650583900458315816948789150493510364455901326921541229790333128250315570028663870007819448602886913027374413326693127774690558109483438505723948880643617628742765658951587330490190647416845808956460628923307168968513230827871374000785296218616444454909346822846783080776257715731800041626991321303082507551169740513959629759102343956872201619222213944522681887677741543599266215709729575445956232315161983142101745681491327257288465631405060704444965389641587800587182315709758315194881810703622693679567589094287256852945201726479852328832175971473500490532669913188344832273601970083471829633609879497952467661178191887940096569951193584364228011490906231478644933496148576819563132229156259760543762334750547299229090665984668124597381414226150746868218090646261612180506920764337481884619042866822082112635266412087099872967990040158058701089089585621166277652593489272867463819121805152819034528677343704202327824736424270296434607398780555431363885749237733198614655369029612841114396648599330909366472170704626530904155328331169618044572201286116312515729804228755261457041893049325587060804250606877571931545894425300969203171410787134436053564361804550638583860324739970831657944267306719793072601405626826499726531521550330828530712554951185725323730657091966890662567338803336907044943794198289141327577694640039456388001504327779629852356693453260619651285682310342387189403913954125130422004906714305649183948916715476009165998321134424996112768348983187674880248822764721252493112105018195810140327893842685678691372344868504107233855987779178900257077177574923652299798389760482903244927099127509616839246472970653945205608858330726386341012560612245178941011692806852105541600935678833397944035746816063773353873831947533980876978478967110198149748115476189043684246633317276543754347472542007765391015299924612553885733259085499670121653525868317071646060828416925676359430217427451707275259890467204091311882503528144226400760381601088158114042448052262674292329148622088245276573452011320182961499472357528286058361392384973727714398712064237616414126009912119078903315419170111941747103574440241209631641001214743313340549484458206255840017377141102345341733137407778013565655754975357364797299063995583814708201749933317990648611893023767067545088203497035450900901271850555899428734166741654818605261282511389083804472924480323579219087339979496398531204214385398012917546893196639953126794790552024484997142496892788757357966974561408855978422463149335736178911808050302745272541562070240498620821237047745961909540756209463932745243907241535338684647450283920957645374002062530438197951010186834282633231392766373774892564200939578093766756453381635400853773790442758720980798301545553475441624447754951770327687604866558523032889149754744344758582949034742059638862444957475248313473830251691536495892124202595061925339256052045360711998424755202604981241626304578269290724829444441142533200981633764952540322591517662243956614531093116558363460869541711914882736936709206863004243884769279
  | 30 => 1049569761870940577660326663407690198166155237983122401296730194962912478888885026049839253781101184303937402076421362620670435285732199663963288139651903574506107643005746564699810443336264744098833431803577368335037475292456940383708181959008821145102391544729088558090543175057836085516979460511756965967245596249391872277396498256967310497513519520768434284136940755665940515525972992085494041612895951158887000519586183485436773906906568503202583911790182232279310796849756755147926756589830908661152863470947425529142844177782928427996209778847534680708720090220768535296203668700349216391437767474499052585962908769111876961920108199397131948818414625042690541278473987290802031313211506462910133242698862255513875782717630205747632968670449625584915966966071029544700482738145654124210328352796208142416446439805706147431836885167697908726412850455114627448592343435825764755874086443170404139861419802766060483753796744243475460686435133665769020325627747898370276021673446034207181364503431721954116657310288983441620512991370880665004897878171282393464878164785438660755625904450490208910932794998207891175675966518666813255140241565731989353765466236962458592046859493808967345932299014154528121302880638011592918551891005966474324636516037802828712902655
  | 37 => 134137112600900209142818575679147411366109983212455643581085378099731471153940316450084789618553099018932459194182673596652824064036532248997309849946745823657357237224097534525477537372751817848393982926511596577182065155655708479798598935336510805714759095433269596114450296779909620753633314981982299027572110658167073679046585384966432092272447545348946255234504426867448128545875946103756379126540755344671342542801350704821763043265783660283918912702418331256032238100565386082746016259461338024882977778925229613998164145815943473362632743976988599090938085128934598961386668095347434674214436946766632635692247326453712499031802421532182131660086254649179648066269498972066165189101106763779263819053881832688731864101126226091329771170508988944094639123780417700940471000666821172593389461927367391537861747819796873429885027982394953518741450094443713084109933421994660789194436251589388323341021541678284028698913081278924247392807574700216920607273115559155945595698452763772370745088026146910197719660127400303365483895069583182187701923819057773013571049106823724861248600997419907371934959486444917409190016243119326760494246034756269279753762352987511090644151020463955804068686639491252067303703026231053702751873669964021528472462905634404710727117441307630267002728334968167708445700360441857592530666982646036228230537856588326591582526476970631057266124000139899782212459429751539536202146783139953409303739732773643309303227271245378822129857725286785642937841716694033668629528888766489272463740144484597369185702889756617321835251032887443780009983
  | 38 => 2991357569779286885603727098425458558997136899600846056389119382217530891371137667092337288946102326546229145762259753923915578936045711855554275134707795626682375304042960312215258575482299857553199980861698331058435166499008138909031869623832829180865722936437709948640113070294105026037540451133566101764635760202509611996559105234231338711278326245739136380085999142998463996407631097119173821409716037272722630342765184390255578994530432969534217918495350542233072343666318393763859842372840095111290150843007511681459390866062674395680469427222374191745120502287043956959671445149830924194397011831529477583062789293933683740028294585974980264442335397207479778302417108483969115957782814036700299535104823379180614129525743726836937560298277527082710188884900141531070977477688608425527223967385730060823574007418343419093302743402294651648057240423669655387394554927821843399301999162554912369215633048226027163066865363454147399046629771780610383077495412558105627213518353423613592502149095058671819039770701605227066376901674100270095672614440372362962957043452946288023420268684781186420730213064198059167869152528244522809159331091795831015787764449387197074650299688697884820860049662844095977161948363208869500820028943489307835484943986169594727767928069943614736527972440845349080730974343223235339401248195322260852223904877492583984241494792903518478050473783742248372653345877025521556666368868789597274829632330264673691061516910826239601786364450600237393382258780819850406451869186728779609298487950680739088366850219372476698492737314233043300944110482265430466151357223905659171194345095167
  | 45 => 4201205443116207701738271920745925788881072626725458429324300562201585611985419248696148516252981305949968455480429250551505297634079599646689930548815818361248505945951779674954597186898468241303474559204274954835407093887616311914081422893022444577861228102007409446981481020212520492676127126371756002127897358799828362604478181612799504982528077703084009036005035981381612197961498728875651107080227480010997978999451511075375548532831060536721022418867527152778218798785882492257284195596304500278061592158248418099820957732237205805734393739468885730130549034446912339669789638200861058482493549824373662756085784899179892518076320257309753894322727455349395743237297720135801396283853950710870209090074608770580456789267485326594543906259278870043202951575628902076110094069316149299857458340327912425987785049648141519635280305547237080458087016142777698471269745576714972994511551241559517442722014603545485032795684038118156667335293385307114735570284046816372031759762389667678697524232487353762666873644321053248745022614296222810742429939342671654581450204204918364841820620144342443841284630229536619803814078030604502491733554364811828188993980144414285747461443465305453548124401857015208604850227680606190389648289023101682888384813772345032086876323387411813570415055307887071777879457084269441352200321820857676789154967119119776184724408122069437913565308892365650278934445534298124896419309838573094799027656333095533012358966317323531031594681394087236932305040512868750548044683550172443431893546206235403146216191291155486387489394317186399831339847637796938830592809932510188581328926528166124330910878213539513484048984258476730798495413324030161067147148421313495015889985798470733739636393002461657402758048747736781754717287466770248789164785431010272239998264330646280535488332900632021771338008637397721579811071686392641960309954178837674537954735760116073759245309119067744325690432946175
  | 53 => 67533845477127720823448289412610197674002669157266175598062359258668227652543887349484715360406762049042843244200662610774003952189019124416370900560204982652950112687395870098715093939741763108181113022918614738479239490923733451326512854038483330370384791103261766895490555733999469831427400066337808293834326124978052261891018863267027869340015300828186973734789605503233953944035548928074583339140200421940060339755394505994022803331535850323825990962561547526406200252689031557081952721850289900900698148061164831047432781930221128431467865744625299648125795938359220131892815897934534210323886592261255830326308648909222447114542554641109305381271974219692200334979749883902740898919206333065964316900822860357924908754297417791598505000331362288658422372449098227204749458509012088356672917702778381217492870151319036004274362112757356569384451608565070944625935876007115489312394532623543668737261891554130423868912741106865823341775379175779609313343584178271293795423083652522062479720953354017904527856072083172040559670603833943359747884553997122576292320590033617222762131079519719926958826055516158327362337958067567418142774216596242478325258762401914483967813689487323659763516398083043297251330198524335145143305320919322081440080366390683841988389297441820497168050438759293898950655639481216591241595967316643068270460405905576336338188631002846139619002880670263509456488779473302692792777751419723037636368592207357928068353854769783452413218227112278267104067964680356464718439040555348347121017098900675225455951933026205908694202679078303617595816830361886486529430897879438572873867941998080905100491217661978045600808998656414095638890274957322799935503635749554346278055844182425830340507962484626535786531585626844727196709312328954163201785028748797286215866931743061255839256007653952248417974231197614162319763471795045792365330288492618873486955893291616819741412559981469285934496546592084289978774673716356999555254963891383395052288274714689660493824627230817668914440466317014465583999141762757943361701961111974148720904016472956884768960261381026276308432044895768000878849564434656643800920668520586667545027177204605513820539094701724207894276683263979726342759969195956869899513890786578295637089518555043094835122237796174004223
  | 60 => 30805924123709654519574676575414289012583630163953850810201535575982837582297487059003953722291938267164099368751858180452687759155305084348655268852926809303235866992722785668328941822220303815307096568642958282025860581590950964219548466131790421991978735657845362807300596537951682836878595677082287844294839586124409062675068628890270872684823462458598183720442561070456627064786112091601508493473360641205669406841446393302675320070564360772555901305447029306243166071440753463199137443667680323385818296204072694095763323054907134712369223779442522454851220391598532076972754512228985147673284652908488311254161211450755816279927145078935511765507980862932049506902460471215495693786046493846367571246770830817006465448711548221040544988779461603361977595918729707410169040074020018890642846777273760354268051846339861262068132016855596369904337984026874150974737043368621463995701326829685598689622611893107672027803291672172420774127301089879543562257837087578025167017797222288419176646749872314819588489903924209355132382049211469200800197928602014339648663142584792191759824804885747570897713909050218515904034117966684617380261721103404802991964464483307662415980292295812409137144545238574345962048275987643594093516627291924653919718638739011110315563751210491211584245799366235722992582287881325880080379083719230309810509867829812339709439302563362907208041884138207365370378861202726984059094309953188988939350367949528033102868415364061552674636188023280770752314154156928659916268106571109708543882933000909328949452830597273445027882980319386986417459323340376467792504799404865092549975845675265619162724484329940796332160602859114395888895967555807136205048219806312139916117939774262983965876577492114907828627870143783056885429713885681674188752566255372742552803794795322246516747105555266765455118441715414108585965409027404433533095121528549835093952473814357066897732552655957328515614491347189364178214746160732162327246083501397764367019204439250474761339234817435842750716745799590566007113961796543391950357209707515281110935743848264305492414611104681140520439965009492645903830436452322753862504468073758881171204874676184905715528168281873696450944214673695522019033281128263824060603259964274413809900933655114478487623202608918680538722664809570928456098475372202690329419131985777798313966137613136264567752289040506318706854366076585600185257920618082879367484964477894864389814460522327999971927813577930506430479491078345052711759542758521805057862528618689410673002955780317835775445775168459703732106128215307728458079293765761105919
  | 68 => 10511942740261851814839265583531408786060580684613473152334586500299040471799519147719349657303944673907661693564542232190139096481134754809664140939083686119466093381306920729808072311158602763291351546654915819799675831206481902856378395918822760346267908769191360434379442163969093232541245543526214510060823195826559164137626847065137255213334730300821590740977875339355055934278294829860372425800621271009738752943205291760199664889080654974554525997878328179510309156789951090216158896375854688812920071011153419734368058947322934774244577074740339537155560438826988897180037701289711540696823274924943406430574533898549832992681369632994457967344819978865273508085350870423243376515325008750630789343508600108139861952953702227041368323829273107753365533604177096520864691350019807259471546728726754040248438869891439137480958183104558617488918222522007453746000244924542968970428660750679554881314124381070974865775755577347964719475341663020834364540136126181228448169214279881840581931730565411010221592038089158303179649250760682696978001545447816598922482738968833961079883582908118525827340028316113637439273890068946769967786524623359549164748146859582462201584424180826073037409863292465392451303101569439817461825955160471516274945544012971230773413441046395985637173262423566562835567242014779385081361799838929848396053062733044176453471842882505046555550051007238883802366352230948379407248725920149216848916460803180790063143863350298206464141638291210948491176017337534212518298951471874693131474216917466928532768708359750488720839011583654206533242601634031189268135704459129110444109223369631998804209724371085906726609187870273117261850729502203365412018698641150669959293838788901962615174802404854037171775635100076859831530784140595194896036861896082344567887831242037945055026303082724134584033525923275504286989391299887013065606963584408009819189426827503788492819314052289591552888574668826950454438777315821331813580742179060916584016769075136419661724579715801200268618935377350862822121773731415006234446278391361325508781846805619223629958306309268199964439921990450090222283812351444513919570356367065090837132143946974056434528450909302247582378118713619236421023513681959592162528145833938518591463111121215808132034098335868348384749789490758310008244157910840012101935182865184878730490082746060659810419261575344817482251053048968032240182725599315015063300032257772433289039533921858058173840290522750056986502880338349016263455457615076465852066039910335402241528532484222299356224402207010919904832352421998779000228721594133127344765917562359759146956200733955981284438513495015473371125190817876174927131972772889566133003610072481682028678559223440891238856695886224955822179714741643934656832456898112100745434120367636735456231200819061067480934422635718277699168987402871622758317653415167743380465947191291680524662995250501976219049222391596212031856873949248521070706687
  | 75 => 1088380036875919937374738274570304463315213678010736478288430332199237601844827573415865594148304040206342297288014750919469162605824850323605974965362992143317365423381487704684812901010466693297505327849866600394151652911084729725572072503732731895302286341609014664792356402634596991372191983291632321114025377924222444105755293240550667522273631545017910372450551704251080308041183018536222326246619848429464332664175794446696765685077520686176031496378874618914154340295845474090152218321379439821387454794121449273655216590518974232775638801662249288684118017981133560238400296983228628707909781361185252781049710517575756410694198293175503084547204126684287327874278891336629383312688814199158091285679207690999145147906387340416423599163764025272693740863697710857900689116222852530323842148370541421201870354192978483618109715948230366124286415249075610624277744842918598508817099971889799264431864293533777302098755251038589586438628170997263778644868389821233414106150539420410430091863639562788854686527733282169376624214932278280612479902795510596197931298815379391948586762677496110801613894732618689270874630243648695232476233733104880019475494036698854094391088566939087514821026407149434865016710561123520116594344530828850258494013144946341086267834746927321806723544530594868874101129028804215565142328882123771048909209559084434539761539481393011079710324314574777371327826222747177444821962764040248322229040699393553514719434979008548483330062462358565321732560067275724500947608152225454257282507642161337951741092584119015470206044660073133905340513966140408309196997250868549460340818557191265842553254511807944739909757869912164628248671945134582170773333293130689860478424793643275111408757846758506780299421188500105126774583199764065617263492938833659388419057249782361548638224917062652590057497168488653899807750749319761775012788049289942297910781990742191426524654021859568306391395422540142098139608066900561760262076783891394669076776242541746536382614061370930662345122846361356278010361597983342891134697964367987472002264594718878228566123183169280889749431883632403157680564765277206670921469721283063501209875041639829544694323740075406836194378970829110616129226987582182830174865274154907924941908172068798764481558134774515199263110910549480556014923548841682930727436638403789789920451663983485628918861595381911916603379736329170219602630064560323975168249520132914058660407594975094259694599143898947275043534541442311987820715922349148096302430212289414674440341997584647256351426943838421125769434751401206839845493781703455247865085117921290803498983755043646854432249726427850995133576135515999561415861811033121353816551097629283117828866656122526780588108462924387061393301280702486924091335347829940136667025380495220499467564093760565693390301396509837239361660457756632943911454786201463974580163665467765473613965848149537552208826705031933942401993182979253375692591284819964604061815836617713758479321309890075514631274048664577082565154162965303488586315234464628280609210381278807013525478593227537639108867091099594245586422231839721267349755307459539908258817934958867139310763196013498661830392550638679005625258769636259514941222750548416610726870687656562888015871
  | 83 => 1034039144840398231786188117909713276901574176754912405749211344106711905932399720273026340420793829873602744428727473946846521484042620971448770339951535082771513520399451545043225902818817654929953017711752584680385225117803625779372058990766018924950171796546904164201344315359602332070869774153693820213164695032082138107563493925573197651288488418328628553778877441929231059990515326297518852104875725452278888125877684592133008967480829482506019181365775689845305283710047086603464172573526510606174042199105479477201184793581772898853555576585057644211020941598462869146236689292757500316720410530922203083798905474687296165335555056107207817938623032420674790555313048869352848884539856308384603486159223742525562041232154143535743896865955481346395547016792918117266773855817551776732481873132620966901753129312700368082374274660991215858771547400143822203244129400011676354212590996233384447618464746267189059875705027229305820644560279734516889861546064464839800882276723182180523012738794383753260520599809517749553175053446239110725376691408007594866893562446172707785094420602681544966038041736104091797526629694157855389631481576481326296204751070261137121119019635800704796363105023932184992270879328041360484280262856045398992142673839320843617487539208755920904891854110436656139340282219520696956646986636905541046228784952867404489225919949956459423680282673968065393909821473112473938193853607298326883447024583568534252522899292348472126866810609835609813021900169950331878340631352851593309979513896238702899234302064409077853351952541690157727475181312505240880103515777665077678247117379936549477011361205803008654449131435514731651078686721312002923690463349400383111893582416072728619758832812847463615129981006393110008017556915560892273735729531588638075368701837992794533625873051457086050717912852190427354475616489918809790888877729474346590988329455184410078662670755397336939480683316428962898443807682764296497691872182799688677333584475644099830489131201475457986780712881057581571555349514687808731504491730696494009586346939727517261677999201249078492054698615585008470352454563094679365824387647145383489466865270837348173015233637441690416524713780055954928318592389490328335255985426527653305332596172756123989759491061658497564416209375004248738050013747711648107134128592991607911234949621805210043301633112509616216297502143967700971530915633071467951765376438223703081552222682617357395518264157542195210822221447352927027326614806314979297356168086184014483789338666642702062861123205743719961553631053871930708790875734441846877183682091919640766832505629520697061229907264578904524754640416146359663378305654880316252259191921367657368081657459426054299142927181768882433418589240913799109026593349232516876974073971291903739809342000868351463541128087768401692090592497066159027461250973858729243216400915563661165948326679910971018144320761956593411922080004477216544712739574682619135166376471923812914036977738668803508799878239560140000864951621290732050489888956010483975313257508559744173517518631174557174608137460044735521647202340472040213938605727104333056742914601637365716887399876387058441114109121303070559427381340405282064428748342625914816948009827191598171327543163867561379690560409984302653607542929644989768676989214469318353958576923135246656035134658592451075125960189957276288709083998022052864100502995592679440613642898904369072515896856661351932925097628869259858807785078463020505865431728807273615606353633606696509947714629612275871967031733517949957985946909000273580350282653482041595764286500634623
  | 90 => 31879022219469789743482293258662784074245206570809149126005948693256304467897159260833170446585373630722177629985177392372484630032766739560286382298274453992128737374781926851025915272291183967631764774856940709260187004253408587775070516150764574189279859096710839434093590792313947076981522897309323430576097804502071232501898293255967450647111496468821136833448967809148648502207209898561509337030931733096033176076493263914073581129039543725524628515823927387765511042117864885039917439268509193396482173385735798270609541068668495391602960239910315631377584201878928626367054866879290114683849690286090731226811038595666811809074238163680630694841578136879877517442856328583086123599483761769749310419744228300391686206626317992952365929688694651290466523009158935843984113319179833271470564027314715622632441523605860772754690884644612803277694122795240968701410326498011666781396932670896448255981396391371334776553719982110154456912245955631383224515109764097206601792994548844122541461742875914485577363667069344530363903849385958780021550107262850208414738842279123020524071414425282467469221802600650124290119158193432593077560318598303921346488545000350664297675202710646980876438637861637840003862504010706975106561681681789663693656206314825012434705638478478109849474849050797924091472968306823310322173808434539800509044928234987112646843525491375034733842701039585005688828713932101671855003384791201687804282982407231816951102337824696203673666232078937567478690013469732473247434340171883550905643296805323162635435911600225362376262803368765389587319229074981520705912251181075004253881173051337901269572232719680153842463475365339301139373518017464906450925254344036365524168433055539827073749912195402033621431839486889578018872658806878251900456179585739433793856665668384700425004255504747183074090003709759897507662108934039464955589355290398532940426734419696102442987381540992867294529971186053803584899275428907453371410576355871378370965442990861727269385796383471027187403144067971420274422069154550286733393484264865680172587917798292631372040940637677680325613503442578286141605036248443014067715043877463515280536027596403126873898810948898256499656669042978241402494435828344093673906045602079930893571375263709379452347590214297797364220811444325972990087971841284879439891630795302369245020155061597568543575002005711946484199044635533683501795049039319993355982073540643843219187292804435683834436517850424608858618772482210105360285594589934286728304463925335813060617025140812363693867525042848358366163492304707331622270909591085567363187079469729358170500370684374223903187942247340365279763288469932819050343850619842472506315579718670874099554905143597945643434650566433862363789658109991404899220431543241958942487359004694889463390429177075272390846836337980656904500791060032933626251370229839850046631131815292335234286080145731608926537925765598313294916341522796751695065669564984156049837189524617623546411356461189314318379942152346804642408544589670165344282160725768083578380736762933646431951922074803856987679605057531047664180179051909143347554610076163403562197051644115994112713776894619783179629698712671996342076567295664579338268270895804499975969019866619696451991300768231038665733319634265563297932388014142637705683674541563800102480232638288268731485782978541773997551696166526376741828047672855888674856588462394440359118558158631175634454763160165550806787941532142236988723713793868727851526927187898337202634753615323264781985473622389987030779353444982500255929726248584739081930138875162629924338324084807545635166986402011078762345282862014277260922328909438383035595398209433814057557158319622660650622965548149204061423167132684786269897299450522186030550204271281209068693135078012290488190458527583823308581087118028714806807374260400400948366921212865764197193683849924115151636297779324652320018583781375
  | 98 => 3337225671296438954652165941707106987931747842581457680013733950914600603782042108391599236663881629170054953383446668047208657229794167867525750713420067715698865916475788037029372314334685688510266723432981490444671297362568060184997766861530612636476414266993659106313269220380606490476989579488225498723152198958065996474918650162949705702105393215652325844278223721415246277703644749020425177991300489276847731477755059219590929238537953538730698916291762897939746126191942351825343106855909851583389308852155009232014617630955547592652631526515465851324393901589251068867496100716276261092714364502287682380596189509178033744637645375787341470567567410760951002722962080629920163487885000593466448332803271474561411325900337048510241589990858960173774308670443025802636053717356560873078865473042375841944160837130601416631906856230964933993654714918542077914524718327073944095373967282827769965760981159389727671601179423464603318208328585458805488949915100878225381044899326305076337376085191287226576079563627163249918274959344872595160721793553375880620647495763557807026285960909328392257198577947555491588101423049059769980244351919656667967016646074103899136678764115935052997731339726573791125069392430987511925888736685723385736634656605218358771314591070195165431589790081632012432315533772595991819414716837110367960918511855692017991423507235674496911232016048055893555771346143105229726339448055114895750714859196896237962307198982122781681129957461597443304666961717205803684977385760541035769334249021031871550252681492119938655669439450035555806124139161981462222326155309147794676959889275162609619112980269881644635509116149970169793217355754998998757921437793912656963520291255784135539746471111826818873252973017741403675967313145623708190863262831219325132666404816206432588093093327487786345501217616918135999105637220889234191228179362053046171272767014380961411349320286621697005841627860015663689452817561450892773393325239387121878534240465051738894173950857400449240801764879420592185482262022623932969820855926766455993824231153883879749722451169566673756981541353720489361559014926375422928541427603585785399073664285467841025716364050986624700440779184756352423076578960144764594878267545880155016144600196574063846339987564267554748412955473350221955225540884866078778353033013261323787523703580095246839475630978983496588503543927188526379154010615529795537162123473108725784074105999694010681188589500572206336331566831199773453047733199510360347786341334288240359125700601400800954465996864623342092011354089340454138851792401856618482183548407567605932352937549491830796035736294550536321893536886917665701533253111968302272033645743664476719706138361538703084682406492273299523088540162431455622484428824360625408468348230259985807309272695139666241621256406984720066233154911335944760663624307411971868720710215021521621076790637425781899603283523894359513966983296010679628657777330770628362226405185438465491189326793104913572263004482020386394753789938900570797760866503170270084911298294215858524551086798314113589266945010197114805361665149921402033273700441669866685488444477219040977341539909034009214261224582133958988956775804766222359120354696322591654465650081920407224201259594861744043508235759935748488061290223222304624698072650931271723780133393184093868622043721981573436670960096765655587488058427803921896994829807607057192826859911720256982821638425064017275443160969233496479557614929760915916144772373506997999089223357717262413102547114202553623231101140943780931823136667666284270730126912863907168593792421842433140280413620960175933997469926277244109177637414400134693904912852607544792351182625608610636216777169637448843417221587868176641086415846751818744044651900627621059718582441515719397602983484472900272075827994077635936791944234776148986532589874290298733389510881030620436967051801923676832430987373714867734714713281402786510267050686352686817175792907939409552291674412312060461237691248957202470992825164649714038084692672999135087137999423176604575393952564297597221450126803212296741678516226924732617359757267075783445495703844591922501260016458905205321472746373091737002863382849229974891312717079630147061845723666775646053008502317850975797247
  | 105 => 526479770288743237037568258243557762581606166392809081194100185667242174344553538328390074796669460403015831432251887532728392481724577058884973143446920121958327000640560398134827951417086663654229050629431264286456607025588767874171351867058233272885646616336151680306520617976147742213596734122431980738328885274234237576120922849134232018802035359388029928729323474798760435581827118145369408207568493064352477087795365857127608267548100003110577987586091087734327081040335114742037895296588961342358251149941528695858642762385501694007751425314800379932771189205149610303048008040557110937873535110946767454605631508125222802063930595382033950442585659692501040449684528188686497849687162420907981277836290548790041740934073915170256706616650072712448254323009898556424398486441141422190230622383191825229713329501848968526745187560111345143370679283368371665038605819565769947271366407958810291243010536243896063542135186736274459344475146020543520717433096227077381849689670479665053870306869051797606547299679715218477243477030944500745002382929326251091449341807150347865051702928510278019600033579992060962292333979169277498533708522170866842329052285094909775358074492829102355782510534949774519138640292186256646845716161427903818216283437079273189844240213027971663594890356898936152940183154436843186441962881751544563437538315734739558926770068092076387095513700672691607099379739720229858568077035238107478271528861166015781535942670765526154760864463293486768875925086505345095301767746106370674988864325112448069876157592892130677271970185077386046604496554348891456531487571673312442495273445545269140738877372614197355930863022721321745129120111621207890537397383793006816588450616215794654120369109521242549038626567009432703715780462630900743014359532497081035246584014974354829428050267758007837560439554247592449140318938508375670659817630886752730559747207893060207711885653139226034653559068101631414838051127196214363371958890097260949590011639268308161097561977068578929204617204160377329583079134154648426893284499286014151777758840715430522179074038047568841385998737327625865246324629856138280339948959640937690774567830494799436272995712400713391051128821078869289538026907114877500164302693902279446020522181163171759254641131457492867497290635644820799518875171930249547211485492013613163445048237862604472158303247356688063554884180609576878159639894587100834853677408930066911178916266912810722813752151601614540342075377331992245957769516387631470643875452683835296742093652988195693055778327412113609212070799510268559366623659331239254659683534181618773776427238766768864065642587714579900901750049055529975967624352057632500106967068450811567723578524883333419527017877565782735359658711737991726519819102921084460651588784010972034325906605494107941306464155169513170337711178706308730595964906020050455488592607793054145667192298972093504369010130241517758784825997108219633303884260100004462004478474852874422437778199554304901064989939448977307698776340185610608125642456310978497757061933232374522375052615175286389698950742896174240292550978789350270609422087900135176257029304054795555904225508658848155484597166485866546380819211819815509111716484288636307836386712558163716427269321935505000611290282922085581242148764155050770897076267948175175538922868552078176844746250362617140532350546599794605918751219793417283352169920599814045854281553378988521675331554790652017927197540291269007907681094923588917283686512305975528453500080831307982169368232604085855806622374301332762346426631896862262881074144323367187943206326410327678781911772185843336909999483703551225742665974269793620799919586679677528937228650993652620133183260098227045101699607902824975941479771598084051504883239012494811849172350107319831611767834076334221309484322263017626375438486755777941309062198783526839511413386779370266423252766367281619274292662987302940553167418398325952262301703393954629218853893445285248547277927587795832320841024076672915152712639482561449643056458261956399390326928101750155936663088093775631153039986511071757622179099448770483281832417749824767315635335439268524050330781966209476517699163261070868408731237836644189591943983438206743205832423771272040184326068016668013549845164217809957101291740570767562160650520000527293267116152254877227490142655200068531416768140744021177003687355837422336850467745662496113637292629426876193912549641216294361363126211965307065794647463309631253632660231788460233348697697815951922886228004014985531861909350046329278133262623159139434495
  | 112 => 899024551686846093233651600387804702215944823172678675281647937583561943128935856422613053935997335571547328530645161269240637016035663686044201821091082258086020266968403028657290351303206583708160820754521399484012718882172084036406267736563676787277258759914400032039397793025555184083364278588244741397309355556166396421931669335155198170145911315277614383667512435921185815961849495448515781404892246866913520228132698666626428211079594526893333775000110567770935058606889844573326142841438854415518407146456220984959026463570221014368097904250058398527836676370186345355042942983432765996374423032291461761846062375955432120658341582673209764227387993578240728708506660900652206502211433341369478247427707727106975683754054476346856414633923886473011861371840205230911899470636637273234096578089467923401969602908380007320114126150845583314343211533621849952247789762029611402291606799105941143734983482170056159447660322780436538411276646776886108343122385176670860398401288620808878304187290111219384584348992625439877391834605070551021834856399543596147290802735497548704021661477411396500187430698190116889194799979701153413765498621283279133414247183745565015022021090233351025976782447040791373716115873307396605851206052072570444787710832672321006810981993692005505807176752105450507036142264392125446875968906416147193979927203263109527269665473949763414960378978626142904491411414366244248563758622606870787919128732331509837080170225899611582868408270359322044700671533120110139036463751714874086803236310986583972516255736653370895036108726394863353758658974688723588950296776581760840340761813589591512356115698880907693513487491478858844456766259172608828496309106193625711444785881316965432015617667665698055895957031587609826402158359264816044853722101639468940753228471394411220878932206508459847893998171243728320145442697431170303392423436198750461671384013046344512844719838705353021047916767435385882028865266018254678146672676570453255876918297663834070538478753958024447208118469382524830849471723177688837041076147927055430571504834926106568772131689227567655840626995058205123474541926489643993605505954594320299903449739613533683560682464424036994028690463565916245448747263890345571345614066087656753424120685963967972637464312929604361869862647262837142104038281042224506345973734859376315496187302636648973175475205642564622455958915371891466612686356711446956066452250389250873034137201813514020012955363456282405680115840134799908580488817195620916852131400713722226149672824047952859232635487947875806383118883912351104466844980162101798035394244845153240551078620375110322620471496811048375126415697586063220744664526170555115059638176703391695967806319551523157229164376510613010596787754720556609607406429118991370564211737867822265574613430591594056464608219920775916184603833542357541214478345373785083651869017401726484095748123352620819004819952863367052593344329080622848768107352844430174142296623479695776819367064044452719308880535985085224196416577218922525588504560764025382912126696441000926097272843727008058979316207718347617752978725821503262126115299190505927103255053811421119663291147612694695241227359189905334095036009349271117287127867698312593084985996331270382309759192100822067061284247274890807215245487092910854885282899462722918737882227282692414683634478542049934146946114683508195735552183376975955612273739593594770209633127370651507756548022000581358017007792855694884313949809075916132740241552107612822719535484612061300753198036705033898644275129447361093809415205903548820080296261668865761663339040289016208823176860857588640400807648518995705310144505641685852732792585847422754444104210575379602209580068618914559815461925928737019340649666994332121943954978864340295361266414270534099943441405950411085221470405418010652824954252032960063152653439604856694162779619366549555640467693622639107179195054214462030703996482672945839922816624712890021677528832819667173522458283167266903548702835172953700780480079879350863569401573086690217428480418074772353029124320345497197417163119372572011872571761804312790930223696376163495672655999063734711724670372975912715989642331841018571538683842054383916092999670785724124009677508521338628637710173116745232027838124508873539844113989001953440353851823380029386272497329314258533775412289879277325670465530240716847960574400159119319113163481628465194312479094777017955887547862362915764650138259434790660178916961214421868512865233239866577507386717524258563869977729215419054807100118894875113572957510739365678601755995202155078421357551942896858704378999758780719092660738834768547109083861118917460990387034613093616267988183857553670699345824743985758739172742249197587318022634130575189753798553513686305787807216299211247987577078560388324829975677481593229181232197872291166691171835323520275690578544069921734655
  | 119 => 691491327675059653375018369432635821083100579769472453612508899422600417561042224464139554100969377792129544710413721409183180158196670350969043076195153824969577140390948826859241936678245640431243334730467699450232029688983230668042255682315979558292559701703311936587296143436986185675881386031793926334146444995978838091918924901947554702129980765045445723900605103432437171515492691445509846203859145982242011833777455752467843996695338305968309087998005180598664818674730811978857349522739517839620909138133435672994050305548586390954902756526604580104058731740332978798057463888251278057510511376032812952679882067268077830696242411668527960276242144197480680624946437691805798005955723802516492209286385412045718770338775372303551133425163958054036684999074507911533028093609443095079663166020244251686037029138734703213032038524577569849544105861436420330851941309117304991376249888214559057811133553228164471448181613003569404192306648134186259840913225381017922116846600389906930417520690220950366890041217960594379866572477917256850872952539680471259053853094633152288114984753271843344292466091436563522509673971037378253438053101593814148953623205068118864420174020895681213769135836838690641292384518590570203746452163137476814713216245157171093156941098452343469855286001106233949927410463316605941430210594226156357581430223437100878500818901481355007468262930291377421358539876176275005936192104806955525537448689083480143092471120780220364442809712832113170226871930609839295153798410999371795599494496887694362515640354085934926534762986178463143717454127508473067114214582034136594877763317066720494612311990552453654694631891046964465047138953198969961684201188312162037816569507266877428314739031020714995493743006211517102794152219463977338517904165176117508011900788488055204395246522611461978666550253752935687900068125551508940620078265912408477176087885684721147052746004123703911700087867877153640507233168049307248473640793140168675797286397686683533792907425613709858179566337027582086024064795754517843347962766551351992466871603270256915963548853537910733727069157350807885480650592277005602053764659089454343483779194188899786911789663725037657284076685051388327712588168812232815741860074190233061529555362937874884792020431496770417257093824533314831663244647770143259003543471371711453319911692875585893211080702504240283838246380801013559457907259817575399536638731667621433189623589834309274800280155004098994204741759425430222634393556252179317649669555476822652998530462268409393006185237866788765262467781876835395354124482022945116470141677651965386860930584951762003156949094656628384775167890413493437868925571984194863948869338719796703790999556432552987193466002725730011103009370091652582273348252164460920275175437081362180865577504102955760642505809188603813866244590717271609644447158506694905663421030129972406126969369981171833120338305312144150474680055810293643311983392318627595794536860962025102609155425176467984135382127886457407347405008781964203752888404452968347508470059059053882795564582298795627039866223789176141723950392669561904327523680448336399111026820411011564713126834214703667537770151380350885586725924871970493374672665036075569694117788068404838329872529446502761233825807170119482212049890506080866122486155519570688579788546899368635478126770752205155429339008139976566495343800124175135389098030963795501615887622864120929170503262994809991393752636224464949893069330958599993038850170298555183318901942532659632921759435625111527463096525514585855661446546154271063515835731330783368149955600662983007522660514223491367559719777899204578222038081267847221656985505270284548742747613547981279229536725285709559433653292502714491926918039719434138145317085406518169440088778571247300620175380938817018297749350785081489077139627952662689078012745852473216964726179216780030755546473831762983463646841341191238946680184643312407288725064445376359643028908557617161868793553717344970558400352404330098299493637314946121976732663538874488086819715603556703962976885965872439735811959974811160440933839820635066942214601327964532240099358565839542517799694018464836984024889849093520643093612783681313331247910167141485507985272037396715542795983346450421503299766454383517897063300022360173146539535270614543830311905123322538621580001901433904418283401839985159590538412355627209070527994745015104380998372839737813889750420945294465794259737643557430549977552155502532567539580333599212606777603317102275346434084708809703810539729513256630689535937971322315622186426151940676907098328538662633497535505488572582195749008240048197796493369633941735264889834283456292190992885360429646286408066191497541120530199069093150591529980892562794548074569540011933623963872795745895630666982037275629445596911450118541060564888000235137538151346979839700185750763411296681563493033249540695919953715134891899161505967934448010078298850768930654188654838605053555881501219099186355851286190231497947748198025278193979692245357471352017583549871515927074853221040429264472769595414402091055829789209079173899876056769093495060049497522511400208432937967488331184844305712271534850047
  | 127 => 6619193203487761646069478401699740371656388778257529767043444696052315969211397135764837842335592557541851372279509590016377610532900264001605181929522523403511530896501613365290771190314965980055512245043717807266202534447406767844320229252834199857969009689171963602177194026154144496473348962394538129239244507966201217256818376432451816599729257128672011342128868021188787442635741650495355276741874954360603095783492641624455668468803956863692344729709303026936418647563087440758272565744683465933351602303262716821290228336546538583105414627421802626627010618534615994930503851400639347085896835473596608520108451773834400902854270325744499362020326609540084469134809220743892521572380681054936407760533956807037081469858438202172936925132079771067086481930608533321791483184434142801055474333962762981642732436519609309079399090057320696143103475165880651775197486733912067030122990843775861290267178033493609737678900751993157058801033020904948165419514399580653515917645056688244323428880881193824395414586630336732815137579000195900113628209110777860232102666483163287898924556056407751147411462379509138781231669623777568410552516436816094095817037653817615786623334643317040307022474205223464241781234892449906056635847372713216348363369408048192631987951491759539926222822759146793713125673036373522078045809385475514166488175147961014210026058056306675562582628829243695154779815886071648151940348355056599658432512665738806819358255783743522338025858403573067184979750684061311850688060734731354087281019632092994160909508233864234215010289843482968998676030803150307858556085952181350552777196179718140263717195399593106540502440790844970110797250316331109280710096206163564223485130042918571630465640147152553364056585764786911546216832114436209482908119038019816629273444828942886649646023337754794397550871352062338722953745149621512179034577960470059403407089624943118587324424206593055095282481701454052176877495713499306616274311849765226585683855557112668924431708467520399240481498515416898106605792738768992524144397345714639311030445583834996266300186941660394293140579156576333248362831237430514744310956420577905222637007590525433067940340588079477064368733245983121583432926676789976664871940921008678599598969930257620082124964239982152031991962677292440888027313173715851190562441211658344574291262316282333960067113113739602148847302516966395234136441140521446434373843739544891403314107476175506125644722644972843362450993070655503968141825407089265649022854418950339121063657666345584206398105837568061815170661292651719834067276319970957308762802559933904954171612144332494883595495909611564709033919986772327614887739088508523254932588790755878489651250721240871408471462725383936296462624944243635405562829288797263349449203008580381518835217038108389597001707573756527797672543343810435228337123870269484956570814944936118480389832149179927141418090840926133484973809244735776257588031729817336657291196756531344339481329855717003648891033267298346196697947177544771165399501341016254471187449532142726143951833208201793372385555403439873060083951273727917698829571189668597553553553048678318096450233907689329586764492100849277985256837685072234658235705901127122376327077347223519264526887577457844130612417722911972441954929915912890253258939769789185536509188695231435304972449483223733961874341023001131102329035974771909383654160175860289000177162199022739761225938771051719886393675949739134591137837359184987153087820515067394883570506894990147457833099371277838188309167977233868125438450154523196366576194639152249915510105819787237264099398445609187929482750967293180573600602358714613187502254915915067856569651902884538508693610779699934243239217690531700723324233304279726228652332908444594958607530033504662791746381203807297194801774070767254191184941439759513664447130020471957745183240392029224217923872820518904565636436033259428884775549638271943737183279726149172203978708280874971474898085683154842684140063826706461397602137754835793067908156873112904972870191055693289885395707252939685194398522984416734245843839516007425764334670598347635472903103654348136706827122851680746781076961351573113898166647054390346189706428954469991468156321241127247877861225304064809126904309760826018953008577071307230164216315149368921419223835708794351480264458901287649909218694743985911396554762685083792809865910479789661535249709846726231909677932828500865826984465723824348027668459605223343916003046420635541757447344619530433775979043445912390251586984077499245694803500801472600268247536178685778057289076246056830980890333932834167035463104807950161649901665890937983946560928307109292566806192279407263307643998601594505794169764941440108266676705165668677841293112858785932550580938863591277034562980803533542092506246752327526321039125355387642517273443581110251662890851269349977680088087883311487567324628989719715669692507912389522113439558537887277579338429909893994738971628483425934926828660656002282681194701744370463607601771114251043465227309624177188165036157528857072536959505020482456971380303146909440194461793667003252683015040519609003823274896506873038258863422270339867520444684431787374213886542461868899464641516676655736072358049139783111064148160741130065653979755090732278607853170777141832209927557787431123431275991195786969237626736019698818890614073610576173039568004844831496452526648422580103070411833204208801801120461101068441821177240684208568309889560782410910166576333274727881517246815731388818698264379391
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
    (run (GateMirror.forward (postEntry (start j))) m s).basis (Shadow7.a0P (start j)+16) =
      s.basis (Shadow7.a0P (start j)+16) := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  rintro hit
  obtain ⟨g,hg,e⟩ := List.mem_map.mp hit
  exact of_decide_eq_true (List.all_eq_true.mp (post_keeps_checked j hi) g hg) e

theorem pair_zero (j : Fin 26) (hi : j.val≤24) (s : State)
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j))) [] s).basis (Shadow7.a0P (start j)+16) = false) :
    (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j)+16) = false := by
  rw [forward_app,run_append,run_take,List.drop_nil,post_keeps j hi]
  exact zero

theorem raw_reference_pair (j : Fin 26) (hi : j.val≤24) (s : State)
    (valid : RawValid s (referenceOps (start j)))
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j)+16) = false) :
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
      (Shadow7.a0P (start j)+16) = false)
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
      (Shadow7.a0P (start j)+16) = false)
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
      (Shadow7.a0P (start j)+16) = false)
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
