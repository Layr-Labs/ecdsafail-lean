import ECDSAAdd.Submission.Entrant.ZeroFlag

/-! An AND chain held open around a middle program.

`zeroWith Q c bs` computes the measured AND chain of `zeroControlled` (each
work bit holds the control and the complement of every earlier input), runs
`Q` while the chain is live, and then erases the chain by measurement.  When
`Q` preserves every chain wire and its effect elsewhere depends only on the
last chain wire and on non-chain wires, the whole block acts as `Q` with the
last chain wire holding `c ∧ all inputs clear`, and restores the chain. -/
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic

def nAnd (c a t : Wire) : Program := [.X a, .CCX c a t, .X a]

def nAndErase (c a t : Wire) : Program :=
  [.X a, .measureX t [] [.CZ c a], .X a]

def zeroWith (Q : Program) : Wire → List ZeroBit → Program
  | _, [] => Q
  | c, b::bs => nAnd c b.input b.work ++ zeroWith Q b.work bs ++ nAndErase c b.input b.work

def chainLast : Wire → List ZeroBit → Wire
  | c, [] => c
  | _, b::bs => chainLast b.work bs

def chainWires (c : Wire) (bs : List ZeroBit) : List Wire := c::bs.flatMap ZeroBit.wires

theorem nAnd_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (s : State) (m : List Bool) :
    run (nAnd c a t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && !s.basis a))⟩ := by
  simp only [nAnd, run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=a
  · subst w; simp [writeBit, hca, hat]
  · by_cases ht : w=t
    · subst w; simp [writeBit, hca, Ne.symm hat]
    · simp [writeBit, hw, ht, hca]

theorem nAndErase_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (hct : c≠t) (s : State) (m : List Bool)
    (hq : s.basis t = (s.basis c && !s.basis a)) :
    run (nAndErase c a t) m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  simp only [nAndErase, run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect, correct, writeBit, hca, hat, hat.symm, hct, hq]
  all_goals
    funext w
    by_cases hw : w=a
    · subst w; simp [hat]
    · simp [Function.update_apply, hw]

theorem chainLast_mem (c : Wire) (bs : List ZeroBit) : chainLast c bs ∈ chainWires c bs := by
  induction bs generalizing c with
  | nil => simp [chainLast, chainWires]
  | cons b bs ih =>
    have h := ih b.work
    simp only [chainLast, chainWires, List.mem_cons, List.flatMap_cons, List.mem_append,
      ZeroBit.wires] at h ⊢
    rcases h with h | h
    · exact Or.inr (Or.inl (by simp [h]))
    · exact Or.inr (Or.inr h)

theorem chainLast_work (c : Wire) (b : ZeroBit) (bs : List ZeroBit) :
    chainLast c (b::bs) ∈ (b::bs).map ZeroBit.work := by
  induction bs generalizing c b with
  | nil => simp [chainLast]
  | cons b' bs ih =>
    have h := ih b.work b'
    simp only [chainLast, List.map_cons, List.mem_cons] at h ⊢
    exact Or.inr h

theorem all_congr' {l : List ZeroBit} {f g : ZeroBit → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- Generic run equation for a chain held open around `Q`. -/
theorem zeroWith_run (Q : Program) (F : BasisState → BasisState) (Pre : BasisState → Prop)
    (c : Wire) (bs : List ZeroBit)
    (hnd : (chainWires c bs).Nodup)
    (hQ : ∀ s m, Pre s.basis → run Q m s = ⟨s.phase, F s.basis⟩)
    (hPre : ∀ B B', (∀ q, q ∉ chainWires c bs → B q = B' q) → Pre B → Pre B')
    (hFS : ∀ B q, q ∈ chainWires c bs → F B q = B q)
    (hFdep : ∀ B B', (∀ q, q ∉ chainWires c bs → B q = B' q) →
      B (chainLast c bs) = B' (chainLast c bs) →
      ∀ q, q ∉ chainWires c bs → F B q = F B' q)
    (s : State) (m : List Bool) (hz : ∀ b ∈ bs, s.basis b.work = false) (hs : Pre s.basis) :
    run (zeroWith Q c bs) m s =
      ⟨s.phase, writeBit (F (writeBit s.basis (chainLast c bs)
        (s.basis c && bs.all (fun b => !s.basis b.input)))) (chainLast c bs)
        (s.basis (chainLast c bs))⟩ := by
  induction bs generalizing c s m with
  | nil =>
    simp only [zeroWith, chainLast, List.all_nil, Bool.and_true]
    rw [hQ s m hs]
    congr 1
    have hw : writeBit s.basis c (s.basis c) = s.basis := by
      funext q; by_cases h : q = c <;> simp [writeBit, h]
    rw [hw]
    funext q
    by_cases h : q = c
    · subst q; simp [writeBit, hFS s.basis c (by simp [chainWires])]
    · simp [writeBit, h]
  | cons b bs ih =>
    have hn : (c::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hnd
    have hni := hn
    simp only [List.nodup_cons, List.mem_cons, not_or] at hni
    have hca : c ≠ b.input := hni.1.1
    have hcw : c ≠ b.work := hni.1.2.1
    have hiw : b.input ≠ b.work := hni.2.1.1
    have hnd' : (chainWires b.work bs).Nodup := List.nodup_cons.mpr ⟨hni.2.2.1, hni.2.2.2⟩
    have hbin (b' : ZeroBit) (hb' : b' ∈ bs) : b'.input ∈ bs.flatMap ZeroBit.wires :=
      List.mem_flatMap.mpr ⟨b', hb', by simp [ZeroBit.wires]⟩
    have hbwk (b' : ZeroBit) (hb' : b' ∈ bs) : b'.work ∈ bs.flatMap ZeroBit.wires :=
      List.mem_flatMap.mpr ⟨b', hb', by simp [ZeroBit.wires]⟩
    have hwbs : b.work ∉ bs.flatMap ZeroBit.wires := hni.2.2.1
    have hsub (q : Wire) (hq : q ∈ chainWires b.work bs) : q ∈ chainWires c (b::bs) := by
      simp only [chainWires, List.mem_cons, List.flatMap_cons, List.mem_append, ZeroBit.wires,
        List.not_mem_nil, or_false] at hq ⊢
      tauto
    have hlast : chainLast c (b::bs) = chainLast b.work bs := rfl
    have hFS' : ∀ B q, q ∈ chainWires b.work bs → F B q = B q :=
      fun B q hq => hFS B q (hsub q hq)
    have hFdep' : ∀ B B', (∀ q, q ∉ chainWires b.work bs → B q = B' q) →
        B (chainLast b.work bs) = B' (chainLast b.work bs) →
        ∀ q, q ∉ chainWires b.work bs → F B q = F B' q := by
      intro B B' hBB hl q hq
      by_cases hqS : q ∈ chainWires c (b::bs)
      · rw [hFS B q hqS, hFS B' q hqS]; exact hBB q hq
      · exact hFdep B B' (fun q' hq' => hBB q' (fun h => hq' (hsub q' h))) (hlast ▸ hl) q hqS
    let s1 : State := ⟨s.phase, writeBit s.basis b.work (s.basis b.work ^^ (s.basis c && !s.basis b.input))⟩
    have hz1 : ∀ b' ∈ bs, s1.basis b'.work = false := by
      intro b' hb'
      have hne : b'.work ≠ b.work := fun h => hwbs (h ▸ hbwk b' hb')
      simp [s1, writeBit, hne, hz b' (by simp [hb'])]
    have hw0 : s.basis b.work = false := hz b (by simp)
    have hPre' : ∀ B B', (∀ q, q ∉ chainWires b.work bs → B q = B' q) → Pre B → Pre B' :=
      fun B B' hBB => hPre B B' (fun q hq => hBB q (fun h => hq (hsub q h)))
    have hs1 : Pre s1.basis := by
      apply hPre s.basis s1.basis _ hs
      intro q hq
      have hqw : q ≠ b.work := fun h => hq (h ▸ by simp [chainWires, ZeroBit.wires])
      simp [s1, writeBit, hqw]
    have hrec := ih b.work hnd' hPre' hFS' hFdep' s1 m hz1 hs1
    have hval : (s1.basis b.work && bs.all (fun b' => !s1.basis b'.input)) =
        (s.basis c && (b::bs).all (fun b' => !s.basis b'.input)) := by
      have hall : bs.all (fun b' => !s1.basis b'.input) = bs.all (fun b' => !s.basis b'.input) := by
        apply all_congr'
        intro b' hb'
        have hne : b'.input ≠ b.work := fun h => hwbs (h ▸ hbin b' hb')
        simp [s1, writeBit, hne]
      rw [hall]
      simp [s1, writeBit, hw0, Bool.and_assoc]
    rw [hval] at hrec
    set v := s.basis c && (b::bs).all (fun b' => !s.basis b'.input) with hv
    set ℓ := chainLast b.work bs with hℓ
    let t : BasisState := writeBit (F (writeBit s1.basis ℓ v)) ℓ (s1.basis ℓ)
    have ht : ∀ q ∈ chainWires c (b::bs), t q = s1.basis q := by
      intro q hq
      by_cases hql : q = ℓ
      · subst q; simp [t, writeBit]
      · simp only [t, writeBit, Function.update_of_ne hql]
        rw [hFS _ q hq]
        simp [writeBit, hql]
    have e1 : s1.basis b.work = (s.basis c && !s.basis b.input) := by
      simp [s1, writeBit, hw0]
    have e2 : s1.basis c = s.basis c := by simp [s1, writeBit, hcw]
    have e3 : s1.basis b.input = s.basis b.input := by simp [s1, writeBit, hiw]
    have hmeas : t b.work = (t c && !t b.input) := by
      rw [ht b.work (by simp [chainWires, ZeroBit.wires]), ht c (by simp [chainWires]),
        ht b.input (by simp [chainWires, ZeroBit.wires]), e1, e2, e3]
    rw [zeroWith, run_append, run_take, run_append, run_take]
    simp only [measurementCount_append, show measurementCount (nAnd c b.input b.work) = 0 from rfl,
      Nat.zero_add, List.drop_zero]
    rw [show run (nAnd c b.input b.work) m s = s1 from nAnd_run _ _ _ hca hiw s m]
    rw [show run (zeroWith Q b.work bs) m s1 = ⟨s1.phase, t⟩ from hrec]
    rw [nAndErase_run _ _ _ hca hiw hcw _ _ hmeas, hlast]
    congr 1
    funext q
    by_cases hqS : q ∈ chainWires c (b::bs)
    · by_cases hqw : q = b.work
      · subst q
        simp only [writeBit, Function.update_self]
        by_cases hl : b.work = ℓ
        · rw [← hl]; simp [hw0]
        · rw [Function.update_of_ne hl, hFS _ _ hqS]; simp [writeBit, hl, hw0]
      · simp only [writeBit, Function.update_of_ne hqw]
        rw [show t q = s1.basis q from ht q hqS]
        by_cases hql : q = ℓ
        · subst q; simp [s1, writeBit, hqw]
        · rw [Function.update_of_ne hql, hFS _ _ hqS]; simp [s1, writeBit, hql, hqw]
    · have hqw : q ≠ b.work := fun h => hqS (h ▸ by simp [chainWires, ZeroBit.wires])
      have hql : q ≠ ℓ := fun h => hqS (h ▸ hsub _ (chainLast_mem b.work bs))
      simp only [writeBit, Function.update_of_ne hqw, t, Function.update_of_ne hql]
      apply hFdep _ _ _ _ q hqS
      · intro q' hq'
        have hq'w : q' ≠ b.work := fun h => hq' (h ▸ by simp [chainWires, ZeroBit.wires])
        by_cases hq'l : q' = ℓ
        · subst q'; simp [writeBit]
        · simp [writeBit, Function.update_of_ne hq'l, s1, Function.update_of_ne hq'w]
      · rw [hlast]; simp [writeBit]

end ECDSAAdd.Entrant
