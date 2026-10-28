import ECDSAAdd.Arithmetic.Paper935.HmrSourceCallPorts
namespace ECDSAAdd.Arithmetic.Paper935
/-- A list inventory avoids reconstructing a large deduplicated union during
finite membership checks. The explicit flag list is bound by equality below. -/
def hmrSupportList (L : HmrRowMulLayout) (flags : List Wire) : List Wire :=
  flags ++ (L.row.sign :: L.row.payload ++ L.y ++ L.out ++ L.anc)

theorem hmrSupportList_mem (L : HmrRowMulLayout) (flags : List Wire)
    (hf : flags.toFinset = L.flags) (q : Wire) :
    q ∈ hmrSupportList L flags ↔ q ∈ L.support := by
  simp [hmrSupportList,HmrRowMulLayout.support,HmrRowMulLayout.data,
    HmrRowMulLayout.scratch, ← hf, or_comm, or_left_comm]

def s2SupportList : List Wire := hmrSupportList s2HmrSourceLayout [851,804]
def s6SupportList : List Wire := hmrSupportList s6HmrSourceLayout [784,856]

theorem s2SupportList_mem (q : Wire) : q ∈ s2SupportList ↔ q ∈ s2HmrSourceLayout.support :=
  hmrSupportList_mem _ _ (by decide +kernel) q

theorem s6SupportList_mem (q : Wire) : q ∈ s6SupportList ↔ q ∈ s6HmrSourceLayout.support :=
  hmrSupportList_mem _ _ (by decide +kernel) q
end ECDSAAdd.Arithmetic.Paper935
