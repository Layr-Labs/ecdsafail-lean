import ECDSAAdd.Arithmetic.Paper935.RenamedFreshCertificate

namespace ECDSAAdd.Arithmetic.Paper935

/-- Exchange the second and third 256-bit hosts, fixing x and all auxiliary
addresses. This is physical relabeling, not a circuit that overwrites data. -/
def swapYA (q : Wire) : Wire :=
  if 256≤q ∧ q<512 then q+256 else if 512≤q ∧ q<768 then q-256 else q

theorem swapYA_involutive : Function.Involutive swapYA := by
  intro q
  unfold swapYA
  split_ifs <;> dsimp only [Wire] at * <;> omega

def hostSwap : ArenaPermutation :=
  ⟨⟨swapYA,swapYA,swapYA_involutive,swapYA_involutive⟩,by
    intro q
    change swapYA q∈arenaWires ↔ q∈arenaWires
    simp only [arenaWires,Finset.mem_range,swapYA]
    split_ifs <;> dsimp only [Wire] at * <;> omega⟩

theorem hostSwap_apply (q : Wire) : hostSwap.equiv q=swapYA q := rfl

theorem hostSwap_x : xHost.image hostSwap.equiv=xHost := by
  ext q
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    simp only [xHost,Finset.mem_Ico] at ha ⊢
    change 0≤swapYA a ∧ swapYA a<256
    simp only [swapYA]
    split_ifs <;> dsimp only [Wire] at * <;> omega
  · intro h
    refine Finset.mem_image.mpr ⟨q,h,?_⟩
    simp only [xHost,Finset.mem_Ico] at h
    change swapYA q=q
    simp only [swapYA]
    split_ifs <;> dsimp only [Wire] at * <;> omega

theorem hostSwap_y : yHost.image hostSwap.equiv=aHost := by
  ext q
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    simp only [yHost,Finset.mem_Ico] at ha
    change swapYA a∈aHost
    simp only [aHost,Finset.mem_Ico]
    simp only [swapYA]
    split_ifs <;> dsimp only [Wire] at * <;> omega
  · intro h
    have bounds : 512≤q ∧ q<768 := Finset.mem_Ico.mp h
    refine Finset.mem_image.mpr ⟨q-256,?_,?_⟩
    · simp only [yHost,Finset.mem_Ico]; dsimp only [Wire] at *; omega
    · rw [hostSwap_apply]
      simp only [swapYA]
      split_ifs <;> dsimp only [Wire] at * <;> omega

theorem hostSwap_a : aHost.image hostSwap.equiv=yHost := by
  ext q
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    simp only [aHost,Finset.mem_Ico] at ha
    change swapYA a∈yHost
    simp only [yHost,Finset.mem_Ico]
    simp only [swapYA]
    split_ifs <;> dsimp only [Wire] at * <;> omega
  · intro h
    have bounds : 256≤q ∧ q<512 := Finset.mem_Ico.mp h
    refine Finset.mem_image.mpr ⟨q+256,?_,?_⟩
    · simp only [aHost,Finset.mem_Ico]; dsimp only [Wire] at *; omega
    · change swapYA (q+256)=q
      simp only [swapYA]
      split_ifs <;> dsimp only [Wire] at * <;> omega

theorem hostSwap_aux (q : Wire) (hq : 768≤q) : hostSwap.equiv q=q := by
  change swapYA q=q
  simp only [swapYA]
  split_ifs <;> dsimp only [Wire] at * <;> omega

theorem hostSwap_seedBefore : (seedBefore.renamed hostSwap).live=xHost∪yHost := by
  change (xHost∪aHost).image hostSwap.equiv=xHost∪yHost
  rw [Finset.image_union,hostSwap_x,hostSwap_a]

/-- The physical entry permits x/y data and requires the new f host A and
auxiliary sites to be clear. This is exactly the transported old precondition. -/
theorem hostSwap_entry (s : BasisState) :
    seedBefore.Ready (fun q => s (hostSwap.equiv q)) ↔
      ∀q∈arenaWires,q∉xHost∪yHost → s q=false := by
  rw [←Arena.renamed_ready]
  change (∀q∈arenaWires,q∉(seedBefore.renamed hostSwap).live → s q=false) ↔ _
  rw [hostSwap_seedBefore]

theorem hostSwap_seed_rows :
    seedG.toFinset.image hostSwap.equiv=xHost ∧ seedF.toFinset.image hostSwap.equiv=aHost := by
  have hg : seedG.toFinset=xHost := by ext q; simp [seedG,xHost]
  have hf : seedF.toFinset=yHost := by
    ext q
    simp only [seedF,yHost,List.mem_toFinset,List.mem_range',Finset.mem_Ico]
    dsimp only [Wire] at *
    constructor
    · rintro ⟨i,hi,he⟩; omega
    · intro hq
      exact ⟨q-256,by omega,by omega⟩
  rw [hg,hf,hostSwap_x,hostSwap_y]
  exact ⟨rfl,rfl⟩

/-- In the swapped placement the isolated retained output host is y. -/
theorem hostSwap_output_isolated (p k : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) :
    Disjoint yHost (recordedWires (renameRecordedProgram hostSwap.equiv
      (seededAuthorWalkProgram p slots ++ embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p) ++
      embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p).reverse ++
      seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) k slots))) := by
  rw [←hostSwap_a]
  exact renamedEndpoint_aHost_isolated hostSwap p k slots compiled

theorem hostSwap_full_certificate (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (m : List Bool) (s : State)
    (h : EndpointSlotCertificate p k slots E m (pullState hostSwap.equiv s)) :
    RenamedFullCertificate hostSwap p k slots E m s :=
  endpointSlotCertificate_renamed hostSwap p k slots E m s h

theorem hostSwap_fresh_certificate (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (O : Finset Wire) (v : BasisState) (m : List Bool) (s : State)
    (h : EndpointOutputCertificate p k slots E O (fun q => v (hostSwap.equiv q)) m (pullState hostSwap.equiv s)) :
    RenamedFreshOutputCertificate hostSwap p k slots E O v m s :=
  endpointOutputCertificate_renamed hostSwap p k slots E O v m s h

theorem hostSwap_owned_certificate (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (O : Finset Wire) (v : BasisState) (m : List Bool) (s : State)
    (h : EndpointOwnedOutputCertificate p k slots E O (fun q => v (hostSwap.equiv q)) m (pullState hostSwap.equiv s)) :
    RenamedOwnedOutputCertificate hostSwap p k slots E O v m s :=
  endpointOwnedOutputCertificate_renamed hostSwap p k slots E O v m s h

end ECDSAAdd.Arithmetic.Paper935
