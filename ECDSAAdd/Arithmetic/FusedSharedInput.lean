import ECDSAAdd.Arithmetic.FusedShared

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] wireBlock

private theorem fused_input_one (w : Nat → Wire) (s : Nat) :
    wireBlock w s 1=[w s] := by simp [wireBlock,List.range']

/-- Exact correspondence to the old field ports. The four additional padding
sites are borrowed explicitly; none is assumed absent from the full pool. -/
theorem fusedSharedPorts_views (w : Nat → Wire) (g : Wire) :
    (fusedSharedPorts w g).source=(skywalkSharedField w).a++[w 1027] ∧
    (fusedSharedPorts w g).target=(skywalkSharedField w).z++[w 769] ∧
    (fusedSharedPorts w g).constant=(skywalkSharedField w).constant++[w 2055] ∧
    (fusedSharedPorts w g).carry=(skywalkSharedField w).carry++[w 2054,w 2313] ∧
    (fusedSharedPorts w g).A.Sublist (skywalkSharedField w).mask := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [fusedSharedPorts_source]
    change wireBlock w 770 258=wireBlock w 770 257++[w 1027]
    simpa only [fused_input_one,Nat.reduceAdd] using (wireBlock_append w 770 257 1).symm
  · change (fusedSharedPorts w g).targetLow++[w 2312,w 769]=
      (wireBlock w 2056 256++[w 2312])++[w 769]
    rw [fusedSharedPorts_targetLow,List.append_assoc]
    rfl
  · change wireBlock w 1540 256++[w 1796,w 2055]=wireBlock w 1540 257++[w 2055]
    have hb := wireBlock_append w 1540 256 1
    simp only [fused_input_one,Nat.reduceAdd] at hb
    rw [show [w 1796,w 2055]=[w 1796]++[w 2055] from rfl,←List.append_assoc,hb]
  · change wireBlock w 1798 257++[w 2313]=wireBlock w 1798 256++[w 2054,w 2313]
    have hb := wireBlock_append w 1798 256 1
    simp only [fused_input_one,Nat.reduceAdd] at hb
    rw [←hb,List.append_assoc]
    rfl
  · change (wireBlock w 512 256).Sublist (wireBlock w 512 257)
    have hs := List.sublist_append_left (wireBlock w 512 256) (wireBlock w 768 1)
    have hb := wireBlock_append w 512 256 1
    norm_num only at hb
    rw [hb] at hs
    exact hs

/-- Canonical old field inputs and explicit clean padding suffice for every
full-width packed input, including the shared carry extension and guard bits. -/
theorem fusedSharedPorts_input (w : Nat → Wire) (g : Wire) (s : BasisState) (X Y : Nat)
    (hy : regValue (skywalkSharedField w).a s=Y)
    (hx : regValue (skywalkSharedField w).z s=X)
    (hk : regValue (skywalkSharedField w).work s=0)
    (hu : regValue (skywalkSharedUnused w) s=0) :
    regValue (fusedSharedPorts w g).source s=Y ∧
    regValue (fusedSharedPorts w g).target s=X ∧
    regValue (fusedSharedPorts w g).constant s=0 ∧
    regValue (fusedSharedPorts w g).carry s=0 ∧
    regValue (fusedSharedPorts w g).A s=0 ∧ s (fusedSharedPorts w g).cin=false := by
  have clean := (regValue_zero _ _).mp hk
  have unused := (regValue_zero _ _).mp hu
  have h769 : s (w 769)=false := unused _ (by simp [skywalkSharedUnused])
  have h1027 : s (w 1027)=false := unused _ (by simp [skywalkSharedUnused])
  have h2054 : s (w 2054)=false := unused _ (by simp [skywalkSharedUnused])
  have h2055 : s (w 2055)=false := unused _ (by simp [skywalkSharedUnused])
  have hconstant : regValue (skywalkSharedField w).constant s=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact clean q (by simp [ModInPlaceLayout.work,ModAddCoreLayout.work,hq])
  have hcarry : regValue (skywalkSharedField w).carry s=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact clean q (by simp [ModInPlaceLayout.work,ModAddCoreLayout.work,hq])
  have hflag : s (w 2313)=false := clean _ (by
    simp [skywalkSharedField,ModInPlaceLayout.work])
  have hcin : s (w 1797)=false := clean _ (by
    simp [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work])
  have hv := fusedSharedPorts_views w g
  refine ⟨?_,?_,?_,?_,?_,hcin⟩
  · rw [hv.1,regValue_append,hy]
    simp [regValue,h1027]
  · rw [hv.2.1,regValue_append,hx]
    simp [regValue,h769]
  · rw [hv.2.2.1,regValue_append,hconstant]
    simp [regValue,h2055]
  · rw [hv.2.2.2.1,regValue_append,hcarry]
    simp [regValue,h2054,hflag]
  · apply (regValue_zero _ _).mpr
    intro q hq
    have hm := hv.2.2.2.2.subset hq
    exact clean q (by simp [ModInPlaceLayout.work,hm])

/-- Complete physical shared-field kernel. The borrowed target guard is
restored as well, so the frame is outside the original target, not merely
outside the larger packed signed word. -/
theorem fusedSharedKernel_correct (w : Nat → Wire) (g : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hg : g∉fusedSharedIds.map w)
    (X Y : Nat) (hX : X<p) (hY : Y<p) (s : State) (record : List Bool)
    (hy : regValue (skywalkSharedField w).a s.basis=Y)
    (hx : regValue (skywalkSharedField w).z s.basis=X)
    (hk : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0) :
    (run (fusedSharedPorts w g).program record s).phase=s.phase ∧
    (∀ q,q∉(skywalkSharedField w).z →
      (run (fusedSharedPorts w g).program record s).basis q=s.basis q) ∧
    regValue (skywalkSharedField w).z (run (fusedSharedPorts w g).program record s).basis=
      FusedSignedHalf.result p (s.basis g) X Y := by
  have hi := fusedSharedPorts_input w g s.basis X Y hy hx hk hu
  have hfit : p+1<2^(fusedSharedPorts w g).A.length := by
    change p+1<2^(wireBlock w 512 256).length
    rw [wireBlock_length]
    norm_num [p]
  obtain ⟨out,hout⟩ : ∃ out : State, run (fusedSharedPorts w g).program record s=out := ⟨_,rfl⟩
  have hc := (fusedSharedPorts w g).correct (fusedSharedPorts_widths w g)
    (fusedSharedPorts_nodup w g hn hg) (fusedSharedPorts_early w g) hfit
    X Y hX hY s record hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2
  rw [hout] at hc
  let Z := FusedSignedHalf.result p (s.basis g) X Y
  have hz : Z<2^256 := by
    have hb := (FusedSignedHalf.result_spec p X Y (s.basis g) (by norm_num [p]) hX hY).1
    have hp : p<2^256 := by norm_num [p]
    exact hb.trans hp
  have ht : regValue ((fusedSharedPorts w g).targetLow++[w 2312,w 769]) out.basis=Z := hc.2.2
  have hzlow : Z<2^(fusedSharedPorts w g).targetLow.length := by
    rw [fusedSharedPorts_targetLow,wireBlock_length]
    exact hz
  have guards := fusedCanonicalGuards (fusedSharedPorts w g).targetLow (w 2312) (w 769)
    out.basis Z hzlow ht
  have htarget : (skywalkSharedField w).z=(fusedSharedPorts w g).targetLow++[w 2312] := by
    rw [fusedSharedPorts_targetLow,skywalkShared_field_z]
    simpa only [fused_input_one,Nat.reduceAdd] using (wireBlock_append w 2056 256 1).symm
  rw [hout]
  refine ⟨hc.1,?_,?_⟩
  · intro q hq
    by_cases h769 : q=w 769
    · subst q
      have hzero : s.basis (w 769)=false := (regValue_zero _ _).mp hu _ (by simp [skywalkSharedUnused])
      exact guards.2.2.trans hzero.symm
    · apply hc.2.1 q
      rw [(fusedSharedPorts_views w g).2.1]
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hq,h769⟩
  · rw [htarget,regValue_append,guards.1]
    simp [regValue,guards.2.1]
    rfl

end ECDSAAdd.Arithmetic
