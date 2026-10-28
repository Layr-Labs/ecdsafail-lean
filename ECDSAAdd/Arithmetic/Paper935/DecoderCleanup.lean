import ECDSAAdd.Arithmetic.Paper935.DecoderFive

namespace ECDSAAdd.Arithmetic.Paper935

theorem clearHistoryControls_away (frozen fire active second sigma port : Wire)
    (rb : List ZeroBit) (k : Nat)
    (core : [frozen,fire,active,second,sigma,port].Nodup)
    (compare : port∉frozen::fire::rb.flatMap ZeroBit.wires) :
    port∉wires (clearHistoryControls frozen fire active second sigma rb k) := by
  simp only [clearHistoryControls,wires_append,wires_reverse,equalConstant_wires,
    Finset.mem_union,not_or,List.mem_toFinset]
  refine ⟨?_,compare⟩
  simp [historyControlCore,wires,Instr.wires]
  simp_all [eq_comm]

end ECDSAAdd.Arithmetic.Paper935
