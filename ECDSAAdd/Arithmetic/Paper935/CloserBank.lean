import ECDSAAdd.Arithmetic.Paper935.CloserPair
import ECDSAAdd.Arithmetic.Paper935.CloserEncoding

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

private theorem growRow_inactive (sign : Wire) (extra : List Wire)
    (s : State) (m : List Bool) (hs : s.basis sign=false) :
    run (growRow sign extra) m s=s := by
  induction extra with
  | nil => rfl
  | cons q qs ih =>
    simp only [growRow,List.flatMap_cons,resizeBit,List.singleton_append,run,hs,Bool.xor_false]
    have same : writeBit s.basis q (s.basis q)=s.basis := Function.update_eq_self q s.basis
    rw [same]
    exact ih

/-- The author endpoint closer, with commuting affine fan gates grouped together. -/
def closerProgram (b : WindowBank) (p : Nat) : Program :=
  shrinkRow b.g.sign b.g.payload ++
    closerPair b.f.sign b.gv.sign b.f.payload b.gv.payload p

def closerPayloads (b : WindowBank) : List Wire :=
  b.f.payload++b.g.payload++b.gv.payload

private theorem pair_geometry (b : WindowBank)
    (geometry : (b.rows.flatMap WindowRow.wires).Nodup) :
    (b.f.sign::b.gv.sign::b.f.payload++b.gv.payload).Nodup := by
  rw [List.nodup_iff_count_le_one] at geometry ⊢
  intro q
  have h := geometry q
  simp only [WindowBank.rows,List.flatMap_cons,List.flatMap_nil,WindowRow.wires,
    List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

/-- All released payload bits have been physically cleared; fv and f's sign
remain intact. No endpoint bit is reset by the allocator. -/
theorem closerProgram_clear (b : WindowBank) (p : Nat)
    (geometry : (b.rows.flatMap WindowRow.wires).Nodup)
    (fwidth : 1<2^b.f.payload.length) (positive : 0<p)
    (pwidth : p<2^b.gv.payload.length) (s : State) (m : List Bool)
    (gzero : b.g.value s.basis=0) (funit : (b.f.value s.basis).natAbs=1)
    (gvValue : b.gv.value s.basis=b.f.value s.basis*p) :
    let out := run (closerProgram b p) m s
    out.phase=s.phase ∧ (∀ q∈closerPayloads b,out.basis q=false) ∧
      out.basis b.gv.sign=false ∧
      ∀ q∉b.gv.sign::closerPayloads b,out.basis q=s.basis q := by
  have gz := closer_row_zero b.g s.basis gzero
  have first : run (shrinkRow b.g.sign b.g.payload) m s=s := by
    rw [shrinkRow_eq]
    exact growRow_inactive _ _ s m gz.1
  have gvMag : (b.gv.value s.basis).natAbs=p := by
    rw [gvValue,Int.natAbs_mul,funit,Int.natAbs_natCast,Nat.one_mul]
  have pair := closerPair_clear b.f.sign b.gv.sign b.f.payload b.gv.payload p
    (pair_geometry b geometry) fwidth positive pwidth s m
    (closer_row_magnitude b.f s.basis 1 (by omega) fwidth funit)
    (closer_row_magnitude b.gv s.basis p positive pwidth gvMag)
    (closer_signs b.f b.gv s.basis p positive gvValue)
  have count : measurementCount (shrinkRow b.g.sign b.g.payload)=0 := by
    exact (rowWindow_cost b.g.sign b.g.payload).2.2.2
  dsimp only at pair ⊢
  rw [closerProgram,run_append,run_take,first,count,List.drop_zero]
  refine ⟨pair.1,?_,pair.2.2.1,?_⟩
  · intro q hq
    simp only [closerPayloads,List.mem_append] at hq
    rcases hq with (hf | hg) | hgv
    · exact pair.2.1 q (List.mem_append_left _ hf)
    · have away : q∉b.gv.sign::b.f.payload++b.gv.payload := by
        intro bad
        have counts := (List.nodup_iff_count_le_one.mp geometry) q
        have gcount : 0<b.g.payload.count q := List.count_pos_iff.mpr hg
        simp only [WindowBank.rows,List.flatMap_cons,List.flatMap_nil,WindowRow.wires,
          List.count_append,List.count_cons,List.count_nil] at counts
        simp only [List.mem_append,List.mem_cons] at bad
        rcases bad with (eq | hf) | hv
        · subst q; simp at counts; omega
        · have := List.count_pos_iff.mpr hf; omega
        · have := List.count_pos_iff.mpr hv; omega
      exact (pair.2.2.2 q away).trans (gz.2 q hg)
    · exact pair.2.1 q (List.mem_append_right _ hgv)
  · intro q hq
    apply pair.2.2.2 q
    intro h
    apply hq
    simp only [closerPayloads,List.mem_append,List.mem_cons] at h ⊢
    tauto

theorem closerProgram_proper (b : WindowBank) (p : Nat)
    (geometry : (b.rows.flatMap WindowRow.wires).Nodup) :
    ProperProgram (closerProgram b p) := by
  have away : b.g.sign∉b.g.payload := by
    intro h
    have counts := (List.nodup_iff_count_le_one.mp geometry) b.g.sign
    have positive := List.count_pos_iff.mpr h
    simp only [WindowBank.rows,List.flatMap_cons,List.flatMap_nil,WindowRow.wires,
      List.count_append,List.count_cons,List.count_nil] at counts
    simp at counts
    omega
  rw [closerProgram,properProgram_append]
  exact ⟨properProgram_reverse _ (growRow_proper _ _ away),
    closerPair_proper _ _ _ _ _ (pair_geometry b geometry)⟩

/-- Unclosing restores every bit and the phase before any reverse divstep.
The caller must first restore the closer output if its freed wires were reused. -/
theorem closerProgram_roundtrip (b : WindowBank) (p : Nat)
    (geometry : (b.rows.flatMap WindowRow.wires).Nodup) (s : State) (m n : List Bool) :
    run (closerProgram b p).reverse n (run (closerProgram b p) m s)=s :=
  run_reverse_proper _ (closerProgram_proper b p geometry) s m n

end ECDSAAdd.Arithmetic.Paper935
