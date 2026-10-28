import ECDSAAdd.Arithmetic.TerminalParityChain
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityMeasure
open BalancedCleanupOffset
attribute [local irreducible] mappedMajority mappedSum mappedEraseCarry wires

private theorem chain_facts (bits : List MappedBit) (xs ys cs ds : List Wire)
    (cinC cinB target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    toffoliCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 2) ∧
    measurementCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 1) ∧
    wires (chain bits xs ys cs ds cinC cinB target)⊆
      wires (BalancedCleanupOffset.chain bits xs ys cs ds cinC cinB target) := by
  induction ys generalizing bits xs cs ds cinC cinB with
  | nil =>
    have b := List.eq_nil_of_length_eq_zero (by simpa using hb)
    have x := List.eq_nil_of_length_eq_zero (by simpa using hx)
    have c := List.eq_nil_of_length_eq_zero (by simpa using hc)
    have d := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst bits xs cs ds
    simp [chain,BalancedCleanupOffset.chain,flipBelow,toffoliCount,measurementCount]
  | cons y ys ih =>
    cases bits with
    | nil => simp at hb
    | cons b bits =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
        cases cs with
        | nil => simp at hc
        | cons c cs =>
          cases ds with
          | nil => simp at hd
          | cons d ds =>
            cases ys with
            | nil =>
              have be := List.eq_nil_of_length_eq_zero (by simpa using hb)
              have xe := List.eq_nil_of_length_eq_zero (by simpa using hx)
              have ce := List.eq_nil_of_length_eq_zero (by simpa using hc)
              have de := List.eq_nil_of_length_eq_zero (by simpa using hd)
              subst bits xs cs ds
              have emittedLeaf := leaf_counts b a y cinC cinB d target
              refine ⟨?_,?_,?_⟩
              · simpa only [chain,List.length_cons,List.length_nil] using emittedLeaf.1
              · simpa only [chain,List.length_cons,List.length_nil] using emittedLeaf.2
              · intro q hq
                simp only [chain,leaf,program,BalancedCleanupOffset.chain,compareChain,
                  wires_append,Finset.mem_union] at hq ⊢
                simp only [majority,eraseCarry,flipBelow,wires,Instr.wires,correctionWires,
                  Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq ⊢
                tauto
            | cons y' ys =>
              cases bits with
              | nil => simp at hb
              | cons b' bits =>
                have emitted : chain (b::b'::bits) (a::xs) (y::y'::ys) (c::cs) (d::ds) cinC cinB target=
                    prepareHead b a y cinC cinB c d++chain (b'::bits) xs (y'::ys) cs ds c d target++
                    releaseHead b a y cinC cinB c d := rfl
                have original : BalancedCleanupOffset.chain (b::b'::bits) (a::xs) (y::y'::ys)
                    (c::cs) (d::ds) cinC cinB target=
                    prepareHead b a y cinC cinB c d++BalancedCleanupOffset.chain (b'::bits)
                      xs (y'::ys) cs ds c d target++releaseHead b a y cinC cinB c d := by
                  rw [BalancedCleanupOffset.chain]
                  simp only [prepareHead,releaseHead,List.append_assoc]
                have tail := ih (b'::bits) xs cs ds c d (by simpa using hb)
                  (by simpa using hx) (by simpa using hc) (by simpa using hd)
                rcases mappedBit_counts b y cinC c with ⟨mt,mm,et,em,st,sm⟩
                have majT : toffoliCount (majority a y cinB d)=1 := by simp [majority,toffoliCount]
                have majM : measurementCount (majority a y cinB d)=0 := by simp [majority,measurementCount]
                have eraseT : toffoliCount (eraseCarry a y cinB d)=0 := rfl
                have eraseM : measurementCount (eraseCarry a y cinB d)=1 := rfl
                refine ⟨?_,?_,?_⟩
                · simp only [emitted,prepareHead,releaseHead,toffoliCount_append,
                    mt,et,st,majT,eraseT,tail.1]
                  simp [toffoliCount,List.length_cons]
                  omega
                · simp only [emitted,prepareHead,releaseHead,measurementCount_append,
                    mm,em,sm,majM,eraseM,tail.2.1]
                  simp [measurementCount,List.length_cons]
                  omega
                · intro q hq
                  have recurse : q∈wires (chain (b'::bits) xs (y'::ys) cs ds c d target) →
                      q∈wires (BalancedCleanupOffset.chain (b'::bits) xs (y'::ys) cs ds c d target) := fun h => tail.2.2 h
                  simp only [emitted,original,prepareHead,releaseHead,
                    wires_append,Finset.mem_union,or_assoc] at hq ⊢
                  tauto

theorem chain_counts (bits : List MappedBit) (xs ys cs ds : List Wire)
    (cinC cinB target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    toffoliCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 2) ∧
    measurementCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 1) := by
  have facts := chain_facts bits xs ys cs ds cinC cinB target hb hx hc hd
  exact ⟨facts.1,facts.2.1⟩

theorem chain_support (bits : List MappedBit) (xs ys cs ds : List Wire)
    (cinC cinB target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    wires (chain bits xs ys cs ds cinC cinB target)⊆
      wires (BalancedCleanupOffset.chain bits xs ys cs ds cinC cinB target) :=
  (chain_facts bits xs ys cs ds cinC cinB target hb hx hc hd).2.2

end ECDSAAdd.Arithmetic.TerminalParityMeasure
#print axioms ECDSAAdd.Arithmetic.TerminalParityMeasure.chain_counts
#print axioms ECDSAAdd.Arithmetic.TerminalParityMeasure.chain_support
