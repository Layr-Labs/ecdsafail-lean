import ECDSAAdd.Submission.Entrant.TerminalFivePermutation

namespace ECDSAAdd.Entrant.TerminalFivePreTransport
open ECDSAAdd Arithmetic MappedCompressed CompactCertificates
open TerminalFiveDomain
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run wires

def perm := TerminalFivePermutation.perm

theorem pre_supp (g s : Bool) (uv : Nat×Nat) (q : Wire) (hq : q∉sites) :
    pre g s uv.1 uv.2 q=false := by
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
  simp_all [pre]

theorem sitesTable : sites.all (fun q=>decide (perm.symm q<40))=true := by decide +kernel

def preDense (g s : Bool) (uv : Nat×Nat) : Nat :=
  encN_t8 (fun q=>pre g s uv.1 uv.2 (perm q)) (List.range 40)

theorem pre_pull (g s : Bool) (uv : Nat×Nat) :
    pullState perm ⟨false,pre g s uv.1 uv.2⟩ = ⟨false,MeasuredCodec5.bitsOf (preDense g s uv)⟩ := by
  have supp : ∀q : Wire,pre g s uv.1 uv.2 (perm q)=true → q∈List.range 40 := by
    intro q yes
    have member : perm q∈sites := by
      by_contra no
      rw [pre_supp g s uv (perm q) no] at yes
      contradiction
    have table := sitesTable
    simp only [List.all_eq_true,decide_eq_true_eq] at table
    have small := table (perm q) member
    simpa only [List.mem_range,Equiv.symm_apply_apply] using small
  have enc := tb_enc_t8 (fun q=>pre g s uv.1 uv.2 (perm q)) (List.range 40) supp
  apply State.extensionality
  · rfl
  · change (fun q=>pre g s uv.1 uv.2 (perm q))=tbN_t8 (preDense g s uv)
    exact enc

end ECDSAAdd.Entrant.TerminalFivePreTransport
