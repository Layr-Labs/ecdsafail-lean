import ECDSAAdd.Arithmetic.LiteralSkywalkSeedPool
import ECDSAAdd.Arithmetic.SkywalkShared

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Canonical shared seed values transfer without materializing any constant.
The initial orientation supplies clean Cin and the first history site supplies One. -/
theorem literalSkywalkSeedSharedBridge_values (w : Nat → Wire) (A B C : Nat)
    (s : BasisState) (hin : SkywalkSeedValues (skywalkSharedSeed w) A B C s)
    (hOne : s (w 1028)=false) :
    LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) A B s :=
  ⟨hin.a,hin.b,hin.carry,hin.orientation,hOne,hin.orientation⟩

/-- Register-value restoration plus the checked executable frame gives a
complete outsider-of-A frame, including the old constant bank and Cin. -/
private theorem old_values_outsideA (L : SkywalkSeedLayout) (A A' B C : Nat)
    (s t : BasisState) (hin : SkywalkSeedValues L A B C s)
    (hout : SkywalkSeedValues L A' B C t)
    (hf : ∀q,q∉L.usedWires → t q=s q) : ∀q,q∉L.a → t q=s q := by
  intro q hqa
  by_cases he : q=L.cin
  · subst q
    exact hout.cin.trans hin.cin.symm
  by_cases hqb : q∈L.b
  · exact (regValue_eq_iff _ _ _).mp (hout.b.trans hin.b.symm) q hqb
  by_cases hqc : q∈L.constant
  · exact (regValue_eq_iff _ _ _).mp (hout.constant.trans hin.constant.symm) q hqc
  by_cases hqd : q∈L.carry
  · exact (regValue_eq_iff _ _ _).mp (hout.carry.trans hin.carry.symm) q hqd
  apply hf q
  simp only [SkywalkSeedLayout.usedWires,List.mem_cons,List.mem_append]
  tauto

/-- Actual old seed instructions preserve all sites outside A on canonical inputs. -/
theorem literalSkywalkSeedSharedBridge_oldSeed_outsideA (w : Nat → Wire) (p x : Nat)
    (hn : (skywalkSharedWires w).Nodup) (hp : p<2^256) (hx : x<2^256)
    (s : State) (m : List Bool) (hin : SkywalkSeedValues (skywalkSharedSeed w) 0 x 0 s.basis) :
    ∀q,q∉(skywalkSharedSeed w).a →
      (run (skywalkSeed (skywalkSharedSeed w) p) m s).basis q=s.basis q := by
  have hw := skywalkShared_seed_widths w
  have hl := skywalkShared_seed_nodup w hn
  have h := (skywalkSeed_spec (skywalkSharedSeed w) 258 p x hw hl
    (by decide) hp hx s m hin).2
  exact old_values_outsideA _ 0 (p+x) x 0 _ _ hin h
    (fun q hq => (skywalkSeed_frame (skywalkSharedSeed w) 258 p hw s m q hq).1)

/-- Actual independently measured old unseed has the same complete frame. -/
theorem literalSkywalkSeedSharedBridge_oldUnseed_outsideA (w : Nat → Wire) (p x : Nat)
    (hn : (skywalkSharedWires w).Nodup) (hp : p<2^256) (hx : x<2^256)
    (s : State) (m : List Bool)
    (hin : SkywalkSeedValues (skywalkSharedSeed w) (p+x) x 0 s.basis) :
    ∀q,q∉(skywalkSharedSeed w).a →
      (run (skywalkUnseed (skywalkSharedSeed w) p) m s).basis q=s.basis q := by
  have hw := skywalkShared_seed_widths w
  have hl := skywalkShared_seed_nodup w hn
  have h := (skywalkUnseed_spec (skywalkSharedSeed w) 258 p x hw hl
    (by decide) hp hx s m hin).2
  exact old_values_outsideA _ (p+x) 0 x 0 _ _ hin h
    (fun q hq => (skywalkSeed_frame (skywalkSharedSeed w) 258 p hw s m q hq).2)

/-- Equality of the mutable word and the full outsider frame determines State. -/
private theorem same_word_state (a : List Wire) (s t u : State) (V : Nat)
    (htp : t.phase=s.phase) (hup : u.phase=s.phase)
    (htv : regValue a t.basis=V) (huv : regValue a u.basis=V)
    (htf : ∀q,q∉a → t.basis q=s.basis q)
    (huf : ∀q,q∉a → u.basis q=s.basis q) : t=u := by
  apply congrArg₂ State.mk
  · exact htp.trans hup.symm
  · funext q
    by_cases hq : q∈a
    · exact (regValue_eq_iff _ _ _).mp (htv.trans huv.symm) q hq
    · exact (htf q hq).trans (huf q hq).symm

/-- A reusable exact State comparison for the actual seed emissions. -/
theorem literalSkywalkSeedSharedBridge_state_eq (a : List Wire) (s t u : State) (V : Nat)
    (htp : t.phase=s.phase) (hup : u.phase=s.phase)
    (htv : regValue a t.basis=V) (huv : regValue a u.basis=V)
    (htf : ∀q,q∉a → t.basis q=s.basis q)
    (huf : ∀q,q∉a → u.basis q=s.basis q) : t=u :=
  same_word_state a s t u V htp hup htv huv htf huf

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.literalSkywalkSeedSharedBridge_oldSeed_outsideA
#print axioms ECDSAAdd.Arithmetic.literalSkywalkSeedSharedBridge_oldUnseed_outsideA
