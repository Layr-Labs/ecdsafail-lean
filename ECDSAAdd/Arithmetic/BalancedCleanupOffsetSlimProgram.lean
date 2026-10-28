import ECDSAAdd.Arithmetic.BalancedCleanupOffsetPrefix
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetHead
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetSupport

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
open BalancedCleanupOffset
attribute [local irreducible] mappedMajority mappedSum mappedEraseCarry wires

/-- The final offset carry is never read. The comparison still emits its
independent measured carry cleanup; no outcome or phase premise is assumed. -/
def chain : List MappedBit → List Wire → List Wire → List Wire → List Wire →
    Wire → Wire → Wire → Program
  | [b],[a],[y],[_c],[d],cinC,cinB,target =>
      mappedSum b y cinC++[.X y]++compareChain none [a] [y] [d] cinB target++
      [.X y]++mappedSum b y cinC
  | b::bits,a::as,y::ys,c::cs,d::ds,cinC,cinB,target =>
      prepareHead b a y cinC cinB c d++chain bits as ys cs ds c d target++
      releaseHead b a y cinC cinB c d
  | [],[],[],[],[],_,cinB,target => flipBelow none cinB target
  | _,_,_,_,_,_,_,_ => []

def program (L : Layout) : Program :=
  front L++chain (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity++
    (front L).reverse

private theorem chain_facts (bits : List MappedBit) (xs ys cs ds : List Wire)
    (cinC cinB target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    toffoliCount (chain bits xs ys cs ds cinC cinB target)=
      2*ys.length-(if ys.length=0 then 0 else 1) ∧
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
              have sum := mappedBit_counts b y cinC c
              have comparator := compareChain_counts none [a] [y] [d] cinB target rfl rfl
              refine ⟨?_,?_,?_⟩
              · simp only [chain,toffoliCount_append,sum.2.2.2.2.1,comparator.1]
                norm_num [toffoliCount]
              · simp only [chain,measurementCount_append,sum.2.2.2.2.2,comparator.2]
                norm_num [measurementCount]
              · intro q hq
                simp only [chain,BalancedCleanupOffset.chain,compareChain,wires_append,
                  Finset.mem_union] at hq ⊢
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
      2*ys.length-(if ys.length=0 then 0 else 1) ∧
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

theorem front_counts (L : Layout) : toffoliCount (front L)=0 ∧ measurementCount (front L)=0 := by
  have rotate := rotate_counts L.r
  have s := signComplement_counts L.sign L.y
  have l := signComplement_counts L.lower L.y
  have r := signComplement_counts L.lower L.r
  simp only [front,view,BalancedCleanup.prepareSign,toffoliCount_append,measurementCount_append,
    rotate.2.2.1,rotate.2.2.2,s.1,s.2,l.1,l.2,r.1,r.2]
  norm_num [toffoliCount,measurementCount]

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=511 ∧ measurementCount (program L)=511 := by
  have hOC : L.offsetCarry.length=256 := hw.2
  have width := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have carry : L.carry.length=256 := hw.1.2.2
  have aligned := chain_counts (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity
    (by simp [offsetBits,width.2.1]) (by omega) (by omega) (by omega)
  simp only [program,toffoliCount_append,measurementCount_append,toffoliCount_reverse,
    measurementCount_reverse,(front_counts L).1,(front_counts L).2,aligned.1,aligned.2,width.2.1]
  norm_num

theorem support (L : Layout) (hw : L.Widths) : wires (program L)⊆L.wires.toFinset := by
  have hOC : L.offsetCarry.length=256 := hw.2
  have width := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have carry : L.carry.length=256 := hw.1.2.2
  have subset := chain_support (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity
    (by simp [offsetBits,width.2.1]) (by omega) (by omega) (by omega)
  have old := BalancedCleanupOffset.program_support L hw
  rw [BalancedCleanupOffset.program_sandwich] at old
  simp only [program,wires_append,wires_reverse,Finset.union_subset_iff] at old ⊢
  exact ⟨⟨old.1.1,subset.trans old.1.2⟩,old.2⟩

end ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim.chain_counts
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim.counts
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim.support
