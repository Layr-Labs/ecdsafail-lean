import ECDSAAdd.Submission.Entrant.KAddCallerStructureDraft
import ECDSAAdd.Submission.Entrant.AffineCarryTail52Draft

/-! SOURCE ONLY. Exact syntax/footprint bridge at the254-bit boundary.
No MF, phase replacement, complete-candidate or resource claim is made here.
The imported tail52 source has its own separate qualification obligation. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1CarrySplice52Research
open Arithmetic RecordedQuantum Challenge AdderSpineBridgeResearch
open KAddCallerBridgeResearch HighOutputTailStructuredResearch AffineCarryTail52Research

attribute [local irreducible] ECDSAAdd.wires

def lowPrefix52 (w : Nat → Wire) : Program :=
  adderPrefix (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797)

def lowSuffix52 (w : Nat → Wire) : Program :=
  adderSuffix (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797)

def lowPorts52 (w : Nat → Wire) : List Wire :=
  spinePorts (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797)

private theorem lastCarry_append52 (xs ys : List Wire) (cin : Wire) :
    lastCarry (xs++ys) cin=lastCarry ys (lastCarry xs cin) := by
  induction xs generalizing cin with
  | nil => rfl
  | cons x xs ih => exact ih x

private theorem prefix_append52 (xs ys cs tx ty tc : List Wire) (cin : Wire)
    (hy : xs.length=ys.length) (hc : xs.length=cs.length) :
    adderPrefix (xs++tx) (ys++ty) (cs++tc) cin=
      adderPrefix xs ys cs cin++adderPrefix tx ty tc (lastCarry cs cin) := by
  induction xs generalizing ys cs cin with
  | nil =>
      have ey : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy.symm)
      have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc.symm)
      subst ys;subst cs
      rfl
  | cons a xs ih =>
      cases ys with
      | nil => simp at hy
      | cons b ys =>
          cases cs with
          | nil => simp at hc
          | cons z cs =>
              have hy' : xs.length=ys.length := by simpa using hy
              have hc' : xs.length=cs.length := by simpa using hc
              simp only [List.cons_append,adderPrefix,lastCarry,
                ih ys cs z hy' hc',List.append_assoc]

private theorem suffix_append52 (xs ys cs tx ty tc : List Wire) (cin : Wire)
    (hy : xs.length=ys.length) (hc : xs.length=cs.length) :
    adderSuffix (xs++tx) (ys++ty) (cs++tc) cin=
      adderSuffix tx ty tc (lastCarry cs cin)++adderSuffix xs ys cs cin := by
  induction xs generalizing ys cs cin with
  | nil =>
      have ey : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy.symm)
      have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc.symm)
      subst ys;subst cs
      simp only [List.nil_append,lastCarry,adderSuffix,List.append_nil]
  | cons a xs ih =>
      cases ys with
      | nil => simp at hy
      | cons b ys =>
          cases cs with
          | nil => simp at hc
          | cons z cs =>
              have hy' : xs.length=ys.length := by simpa using hy
              have hc' : xs.length=cs.length := by simpa using hc
              simp only [List.cons_append,adderSuffix,lastCarry,
                ih ys cs z hy' hc',List.append_assoc]

/-- Only four finite data bits are unfolded. No private tail-module theorem is used. -/
private theorem old_tail_add52 (p : Ports) :
    oldTail p=addInPlace (xs p) (ys p) (zs p) p.cin := by rfl

/-- Derive the four-bit cut by factoring the CHECKED two-bit add_split.
The prefix and measured suffix lists stay symbolic throughout this proof. -/
theorem add_split_four52 (lx ly lc : List Wire) (cin : Wire) (p : Ports)
    (hy : lx.length=ly.length) (hc : lx.length=lc.length)
    (hcin : lastCarry lc cin=p.cin) :
    addInPlace (lx++xs p) (ly++ys p) (lc++zs p) cin=
      adderPrefix lx ly lc cin++oldTail p++adderSuffix lx ly lc cin := by
  have last2 : lastCarry (lc++[p.z0,p.z1]) cin=p.z1 := by
    rw [lastCarry_append52]
    rfl
  have middle :
      adderPrefix [p.a0,p.a1] [p.b0,p.b1] [p.z0,p.z1] p.cin++
        oldLeafAt p.a2 p.b2 p.z1 p.a3 p.b3 p.z2++
        adderSuffix [p.a0,p.a1] [p.b0,p.b1] [p.z0,p.z1] p.cin=oldTail p := by
    symm
    rw [old_tail_add52]
    simpa only [xs,ys,zs,lastCarry] using add_split
      [p.a0,p.a1] [p.b0,p.b1] [p.z0,p.z1] p.cin p.a2 p.a3 p.b2 p.b3 p.z2 rfl rfl
  have h := add_split (lx++[p.a0,p.a1]) (ly++[p.b0,p.b1]) (lc++[p.z0,p.z1])
    cin p.a2 p.a3 p.b2 p.b3 p.z2
    (by simp only [List.length_append,List.length_cons,List.length_nil];omega)
    (by simp only [List.length_append,List.length_cons,List.length_nil];omega)
  rw [prefix_append52 lx ly lc [p.a0,p.a1] [p.b0,p.b1] [p.z0,p.z1] cin hy hc,
    suffix_append52 lx ly lc [p.a0,p.a1] [p.b0,p.b1] [p.z0,p.z1] cin hy hc,
    last2,hcin] at h
  rw [←middle]
  simpa only [xs,ys,zs,List.append_assoc] using h

/-- The actual incoming tail carry is bit253 at1793, never bit252 or1792. -/
theorem lastCarry_low25452 (w : Nat → Wire) :
    lastCarry (wireBlock w 1540 254) (w 1797)=w 1793 := by
  have block : wireBlock w 1540 254=wireBlock w 1540 253++[w 1793] := by
    rw [←wireBlock_append w 1540 253 1]
    rfl
  rw [block,lastCarry_append52]
  rfl

/-- Literal read_add258, with actual four-bit ports and unchanged measured unwind. -/
theorem literal_split_four52 (w : Nat → Wire) :
    literalKAdd w=lowPrefix52 w++oldTail (actualPorts w)++lowSuffix52 w := by
  have hx : wireBlock w 0 258=wireBlock w 0 254++xs (actualPorts w) := by
    rw [←wireBlock_append w 0 254 4]
    rfl
  have hy : wireBlock w 770 258=wireBlock w 770 254++ys (actualPorts w) := by
    rw [←wireBlock_append w 770 254 4]
    rfl
  have hc : wireBlock w 1540 257=wireBlock w 1540 254++zs (actualPorts w) := by
    rw [←wireBlock_append w 1540 254 3]
    rfl
  rw [literalKAdd,read_add,hx,hy,hc]
  simpa only [lowPrefix52,lowSuffix52] using add_split_four52
    (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254)
    (w 1797) (actualPorts w) (by simp [wireBlock_length]) (by simp [wireBlock_length])
    (by simpa only [actualPorts] using lastCarry_low25452 w)

theorem lowPrefix_records52 (w : Nat → Wire) : measurementCount (lowPrefix52 w)=0 := by
  exact prefix_records _ _ _ _

/-- Finite pool Nodup suffices; global injectivity of the placement is not assumed. -/
theorem lowPorts_avoid_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : (254 ≤ i ∧ i < 258) ∨ (1024 ≤ i ∧ i < 1029) ∨ (1794 ≤ i ∧ i < 1797)) :
    w i∉lowPorts52 w := by
  have ir : i<1798 := by omega
  intro h
  simp only [lowPorts52,spinePorts,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h
  · have e := skywalkPool_index_inj w hn i 1797 ir (by decide) h
    omega
  all_goals
    obtain ⟨j,hj,hji⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have jr : j<1798 := by omega
    have e := skywalkPool_index_inj w hn j i jr ir hji
    omega

theorem lowPrefix_avoid_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : (254 ≤ i ∧ i < 258) ∨ (1024 ≤ i ∧ i < 1029) ∨ (1794 ≤ i ∧ i < 1797)) :
    w i∉wires (lowPrefix52 w) := by
  intro h
  exact lowPorts_avoid_pool52 w hn i hi
    (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

/-- Stronger than no-write: the measured low suffix does not touch these ports. -/
theorem lowSuffix_avoid_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : (254 ≤ i ∧ i < 258) ∨ (1024 ≤ i ∧ i < 1029) ∨ (1794 ≤ i ∧ i < 1797)) :
    w i∉wires (lowSuffix52 w) := by
  intro h
  exact lowPorts_avoid_pool52 w hn i hi
    (List.mem_toFinset.mp (suffix_support _ _ _ _ h))

theorem lowPrefix_keeps_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : (254 ≤ i ∧ i < 258) ∨ (1024 ≤ i ∧ i < 1029) ∨ (1794 ≤ i ∧ i < 1797))
    (s : State) (m : List Bool) :
    (run (lowPrefix52 w) m s).basis (w i)=s.basis (w i) := by
  apply run_preserves_outside
  exact lowPrefix_avoid_pool52 w hn i hi

/-- In particular b255..257 (indices1025..1027) survive the whole low unwind. -/
theorem lowSuffix_keeps_high_sum52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (j : Nat) (hj : 255 ≤ j ∧ j < 258) (s : State) (m : List Bool) :
    (run (lowSuffix52 w) m s).basis (w (770+j))=s.basis (w (770+j)) := by
  apply run_preserves_outside
  exact lowSuffix_avoid_pool52 w hn (770+j) (Or.inr (Or.inl ⟨by omega,by omega⟩))

end ECDSAAdd.Entrant.E1CarrySplice52Research
