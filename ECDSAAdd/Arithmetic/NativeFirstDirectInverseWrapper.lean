import ECDSAAdd.Arithmetic.NativeFirstDirectInverseProof
import ECDSAAdd.Arithmetic.NativeFirstDirectLayout
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run mappedAdd hAdd kAdd kTail forward inverse

private theorem copy_away (w : Nat → Wire) (q : Wire)
    (hs : q∉wireBlock w 771 255) (hd : q∉wireBlock w 1 255) :
    q∉wires (lowCopy w) := by
  rw [lowCopy,copyRegister_wires none (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length])]
  split_ifs
  · simp
  · simpa only [Option.toList_none,List.nil_append,List.mem_toFinset,
      List.mem_append,not_or] using And.intro hs hd

private theorem front_away (w : Nat → Wire) (q : Wire)
    (h0 : q≠w 0) (hb : q≠w 770) (he : q≠w 1028)
    (hs : q∉wireBlock w 771 255) (hd : q∉wireBlock w 1 255) :
    q∉wires (inverseFront w) := by
  have flags : q∉wires [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)] := by
    simp [wires,Instr.wires,h0,hb,he]
  rw [inverseFront,wires_append,Finset.mem_union,not_or]
  exact ⟨flags,copy_away w q hs hd⟩

private theorem middle_away (w : Nat → Wire) (q : Wire)
    (hb : q≠w 770) (he : q≠w 1028) (hr : q∉wireBlock w 770 258) :
    q∉wires (inverseMiddle w) := by
  have first : q∉wires [.CX (w 1028) (w 770)] := by
    simp [wires,Instr.wires,hb,he]
  have rot : q∉wires (rotateRight (wireBlock w 770 258)) := by
    rw [(rotate_wires (wireBlock w 770 258)).1]
    split_ifs
    · simp
    · simpa only [List.mem_toFinset] using hr
  rw [inverseMiddle,wires_append,Finset.mem_union,not_or]
  exact ⟨first,rot⟩

/-- Existing seed readiness suffices. The stronger primitive needs no bound
on x and no extension-zero assumption; all original data and spectators return. -/
theorem inverse_forward_ready (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (s : State) (mF mI : List Bool)
    (ready : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis) :
    run (inverse w) mI (run (forward w) mF s)=s := by
  have bank : regValue (wireBlock w 1540 257) s.basis=0 := ready.carry
  have clean : ∀q∈wireBlock w 1540 256,s.basis q=false := by
    intro q hq
    exact (regValue_zero _ _).mp bank q (block_subset w 1540 256 257 (by omega) q hq)
  have cin : s.basis (w 1797)=false := ready.cin
  refine inverse_forward w s mF mI (h_inputs_nd w hn) (k_inputs_nd w hn)
    (fun i => h_sources_fresh w hn i) (fun i => k_sources_fresh w hn i)
    (block_not_mem w hn 1028 4 253 (by omega) (by omega) (by omega))
    ?_ (copy_inputs_nd w hn) (block_nodup w hn 770 258 (by omega))
    (index_ne w hn 770 1028 (by omega) (by omega) (by omega))
    (index_ne w hn 1028 0 (by omega) (by omega) (by omega))
    ?_ (block_subset w 1540 252 256 (by omega)) ?_ clean cin
  · simp only [List.mem_cons,not_or]
    exact ⟨index_ne w hn 1028 770 (by omega) (by omega) (by omega),
      block_not_mem w hn 1028 771 257 (by omega) (by omega) (by omega)⟩
  · intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    have h0 := index_ne w hn j 0 (by omega) (by omega) (by omega)
    have hb := index_ne w hn j 770 (by omega) (by omega) (by omega)
    have he := index_ne w hn j 1028 (by omega) (by omega) (by omega)
    exact ⟨front_away w (w j) h0 hb he
        (block_not_mem w hn j 771 255 (by omega) (by omega) (by omega))
        (block_not_mem w hn j 1 255 (by omega) (by omega) (by omega)),
      block_not_mem w hn j 4 253 (by omega) (by omega) (by omega),
      middle_away w (w j) hb he
        (block_not_mem w hn j 770 258 (by omega) (by omega) (by omega))⟩
  · exact front_away w (w 1797)
      (index_ne w hn 1797 0 (by omega) (by omega) (by omega))
      (index_ne w hn 1797 770 (by omega) (by omega) (by omega))
      (index_ne w hn 1797 1028 (by omega) (by omega) (by omega))
      (block_not_mem w hn 1797 771 255 (by omega) (by omega) (by omega))
      (block_not_mem w hn 1797 1 255 (by omega) (by omega) (by omega))

/-- Numerical post equality must also include phase and the outside frame.
The G bit is already included in the complete A word. -/
theorem prefix_post_unique (w : Nat → Wire) (s t : State)
    (phase : s.phase=t.phase)
    (a : regValue (wireBlock w 0 258) s.basis=regValue (wireBlock w 0 258) t.basis)
    (b : regValue (wireBlock w 770 258) s.basis=regValue (wireBlock w 770 258) t.basis)
    (e : s.basis (w 1028)=t.basis (w 1028))
    (outside : ∀q,q∉wireBlock w 0 258++wireBlock w 770 258++[w 1028] →
      s.basis q=t.basis q) : s=t := by
  apply congrArg₂ State.mk phase
  funext q
  by_cases ha : q∈wireBlock w 0 258
  · exact (regValue_eq_iff _ _ _).mp a q ha
  by_cases hb : q∈wireBlock w 770 258
  · exact (regValue_eq_iff _ _ _).mp b q hb
  by_cases he : q=w 1028
  · subst q; exact e
  exact outside q (by simp [ha,hb,he])

/-- The caller may replace the actual forward output by any complete State
proved equal to it, with independently chosen inverse outcomes. No extra
original-x register or an erasure oracle appears in this interface. -/
theorem inverse_forward_transport (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (s t : State) (mF mI : List Bool)
    (ready : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (post : t=run (forward w) mF s) : run (inverse w) mI t=s := by
  rw [post]
  exact inverse_forward_ready w hn x s mF mI ready

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.inverse_forward_ready
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.prefix_post_unique
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.inverse_forward_transport
