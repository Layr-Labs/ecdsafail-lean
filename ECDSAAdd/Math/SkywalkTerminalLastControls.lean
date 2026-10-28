import ECDSAAdd.Math.SkywalkTerminationBudget
import ECDSAAdd.Math.SkywalkTrace

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.SkywalkTrace
open SkywalkRails Secp256k1

/-- Index an actual record without unfolding a fixed512-element trace. The
default is arbitrary because every index in the statement is in range. -/
theorem trace_getD_code (n : Nat) (r : SkywalkRails.State) (i : Nat)
    (hi : i<n) (default : Bool×Bool) :
    (trace n r).getD i default=code (next^[i] r) := by
  induction n generalizing r i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h := ih (next r) i (by omega)
      simpa only [trace,Function.iterate_succ_apply] using h

attribute [local irreducible] Nat.iterate trace next

theorem code_terminal (g s : Bool) : code (encode g s 0 1)=(true,false) := by
  have h := SkywalkRails.terminal_step g s (1 : Int) (by norm_num) (by norm_num)
  simp only [code,h]

/-- The old orientation and smaller sign are existential and unconstrained.
Only the proven terminal logical values feed the terminal-step theorem. -/
theorem code_after_budget (p x n : Nat) (g s : Bool) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<2^n) (hc : x.Coprime p) :
    code (next^[2*n-1] (encode g s (x : Int) (p : Int)))=(true,false) := by
  have terminal := SkywalkNat.terminates_2n_sub_one p x n hp0 hx0 hpodd hp hx hc
  obtain ⟨G,S,encoded⟩ := iter_encoded (2*n-1) g s (SkywalkNat.init x p) hp0 hpodd
  change next^[2*n-1] (encode g s (x : Int) (p : Int))=
    encode G S ((SkywalkNat.step^[2*n-1] (SkywalkNat.init x p)).u : Int)
      ((SkywalkNat.step^[2*n-1] (SkywalkNat.init x p)).v : Int) at encoded
  rw [terminal.1,terminal.2] at encoded
  rw [encoded]
  exact code_terminal G S

private theorem canonical_coprime (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p) :
    x.Coprime ECDSAAdd.p := by
  apply Nat.Coprime.symm
  apply Secp256k1.p_prime.coprime_iff_not_dvd.mpr
  intro hd
  exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)

theorem code511 (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p) :
    code (next^[511] (encode false false (x : Int) (ECDSAAdd.p : Int)))=(true,false) := by
  have h := code_after_budget ECDSAAdd.p x 256 false false
    (by norm_num [ECDSAAdd.p]) hx0 (by norm_num [ECDSAAdd.p])
    (by norm_num [ECDSAAdd.p]) (hx.trans (by norm_num [ECDSAAdd.p]))
    (canonical_coprime x hx0 hx)
  simpa only [Nat.reduceMul,Nat.reduceSub] using h

/-- Actual last record of the unchanged512-round trace, for the entire
canonical nonzero domain. No sampled convergence or tie convention is used. -/
theorem trace512_last (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (default : Bool×Bool) :
    (trace 512 (encode false false (x : Int) (ECDSAAdd.p : Int))).getD 511 default=
      (true,false) := by
  rw [trace_getD_code 512 _ 511 (by decide) default]
  exact code511 x hx0 hx

theorem unit_trace512_last (default : Bool×Bool) :
    (trace 512 (encode false false (1 : Int) (ECDSAAdd.p : Int))).getD 511 default=
      (true,false) :=
  trace512_last 1 (by omega) (by norm_num [ECDSAAdd.p]) default

end ECDSAAdd.SkywalkTrace
#print axioms ECDSAAdd.SkywalkTrace.code_after_budget
#print axioms ECDSAAdd.SkywalkTrace.trace512_last
#print axioms ECDSAAdd.SkywalkTrace.unit_trace512_last
