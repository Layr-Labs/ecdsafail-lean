import ECDSAAdd.Arithmetic.LiteralSkywalkSeedSharedBridgeSupport

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Bank-free and original seed emissions have identical full State outputs.
Their measurement records are arbitrary and need not agree. -/
theorem literalSkywalkSeedSharedBridge_seed_eq (w : Nat → Wire) (p x : Nat)
    (hn : (skywalkSharedWires w).Nodup) (hp : p<2^256) (hx : x<2^256)
    (s : State) (mNew mOld : List Bool)
    (hin : SkywalkSeedValues (skywalkSharedSeed w) 0 x 0 s.basis)
    (hOne : s.basis (w 1028)=false) :
    run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) mNew s=
      run (skywalkSeed (skywalkSharedSeed w) p) mOld s := by
  have nInput := literalSkywalkSeedSharedBridge_values w 0 x 0 s.basis hin hOne
  have nv := literalSkywalkPoolSeed_valid w (skywalkShared_integer_nodup w hn)
  have nw := literalSkywalkPoolSeed_widths w
  have ow := skywalkShared_seed_widths w
  have ov := skywalkShared_seed_nodup w hn
  have n := literalSkywalkSeed_spec (literalSkywalkPoolSeed w) 258 p x nw nv
    (by decide) hp hx s mNew nInput
  have o := skywalkSeed_spec (skywalkSharedSeed w) 258 p x ow ov
    (by decide) hp hx s mOld hin
  exact literalSkywalkSeedSharedBridge_state_eq (skywalkSharedSeed w).a s _ _ (p+x)
    n.1 o.1 n.2.a o.2.a
    (literalSkywalkSeed_preserves_outsideA (literalSkywalkPoolSeed w) 258 p x nw nv
      (by decide) hp hx s mNew nInput)
    (literalSkywalkSeedSharedBridge_oldSeed_outsideA w p x hn hp hx s mOld hin)

/-- The independently measured bank-free unseed agrees with original cleanup
on every canonical old seed value, including all phase and work bits. -/
theorem literalSkywalkSeedSharedBridge_unseed_eq (w : Nat → Wire) (p x : Nat)
    (hn : (skywalkSharedWires w).Nodup) (hp : p<2^256) (hx : x<2^256)
    (s : State) (mNew mOld : List Bool)
    (hin : SkywalkSeedValues (skywalkSharedSeed w) (p+x) x 0 s.basis)
    (hOne : s.basis (w 1028)=false) :
    run (literalSkywalkUnseed (literalSkywalkPoolSeed w) p) mNew s=
      run (skywalkUnseed (skywalkSharedSeed w) p) mOld s := by
  have nInput := literalSkywalkSeedSharedBridge_values w (p+x) x 0 s.basis hin hOne
  have nv := literalSkywalkPoolSeed_valid w (skywalkShared_integer_nodup w hn)
  have nw := literalSkywalkPoolSeed_widths w
  have ow := skywalkShared_seed_widths w
  have ov := skywalkShared_seed_nodup w hn
  have n := literalSkywalkUnseed_spec (literalSkywalkPoolSeed w) 258 p x nw nv
    (by decide) hp hx s mNew nInput
  have o := skywalkUnseed_spec (skywalkSharedSeed w) 258 p x ow ov
    (by decide) hp hx s mOld hin
  exact literalSkywalkSeedSharedBridge_state_eq (skywalkSharedSeed w).a s _ _ 0
    n.1 o.1 n.2.a o.2.a
    (literalSkywalkUnseed_preserves_outsideA (literalSkywalkPoolSeed w) 258 p x nw nv
      (by decide) hp hx s mNew nInput)
    (literalSkywalkSeedSharedBridge_oldUnseed_outsideA w p x hn hp hx s mOld hin)

/-- The bank-free emission retains the original caller-facing seed contract,
including the old constant bank, old Cin, and clean loaned One. -/
theorem literalSkywalkSeedSharedBridge_seed_spec (w : Nat → Wire) (p x : Nat)
    (hn : (skywalkSharedWires w).Nodup) (hp : p<2^256) (hx : x<2^256) :
    Triple (fun s => SkywalkSeedValues (skywalkSharedSeed w) 0 x 0 s ∧ s (w 1028)=false)
      (literalSkywalkSeed (literalSkywalkPoolSeed w) p)
      (fun s => SkywalkSeedValues (skywalkSharedSeed w) (p+x) x 0 s ∧ s (w 1028)=false) := by
  intro s m hin
  have he := literalSkywalkSeedSharedBridge_seed_eq w p x hn hp hx s m m hin.1 hin.2
  have o := skywalkSeed_spec (skywalkSharedSeed w) 258 p x
    (skywalkShared_seed_widths w) (skywalkShared_seed_nodup w hn)
    (by decide) hp hx s m hin.1
  have nInput := literalSkywalkSeedSharedBridge_values w 0 x 0 s.basis hin.1 hin.2
  have n := literalSkywalkSeed_spec (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w)
    (literalSkywalkPoolSeed_valid w (skywalkShared_integer_nodup w hn))
    (by decide) hp hx s m nInput
  refine ⟨?_,?_,n.2.one⟩
  · rw [he]
    exact o.1
  · rw [he]
    exact o.2

/-- Original clean carry/constant/Cin/orientation values survive independently
measured bank-free unseed, enabling reuse of the old restoration interface. -/
theorem literalSkywalkSeedSharedBridge_unseed_spec (w : Nat → Wire) (p x : Nat)
    (hn : (skywalkSharedWires w).Nodup) (hp : p<2^256) (hx : x<2^256) :
    Triple (fun s => SkywalkSeedValues (skywalkSharedSeed w) (p+x) x 0 s ∧ s (w 1028)=false)
      (literalSkywalkUnseed (literalSkywalkPoolSeed w) p)
      (fun s => SkywalkSeedValues (skywalkSharedSeed w) 0 x 0 s ∧ s (w 1028)=false) := by
  intro s m hin
  have he := literalSkywalkSeedSharedBridge_unseed_eq w p x hn hp hx s m m hin.1 hin.2
  have o := skywalkUnseed_spec (skywalkSharedSeed w) 258 p x
    (skywalkShared_seed_widths w) (skywalkShared_seed_nodup w hn)
    (by decide) hp hx s m hin.1
  have nInput := literalSkywalkSeedSharedBridge_values w (p+x) x 0 s.basis hin.1 hin.2
  have n := literalSkywalkUnseed_spec (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w)
    (literalSkywalkPoolSeed_valid w (skywalkShared_integer_nodup w hn))
    (by decide) hp hx s m nInput
  refine ⟨?_,?_,n.2.one⟩
  · rw [he]
    exact o.1
  · rw [he]
    exact o.2

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.literalSkywalkSeedSharedBridge_seed_eq
#print axioms ECDSAAdd.Arithmetic.literalSkywalkSeedSharedBridge_unseed_eq
#print axioms ECDSAAdd.Arithmetic.literalSkywalkSeedSharedBridge_seed_spec
#print axioms ECDSAAdd.Arithmetic.literalSkywalkSeedSharedBridge_unseed_spec
