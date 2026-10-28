import ECDSAAdd.Arithmetic.Paper935.WindowResizePhase

namespace ECDSAAdd.Arithmetic.Paper935

/-- Every physical signed row fits its own payload width, including width zero. -/
theorem WindowRow.value_fits (r : WindowRow) (s : BasisState) :
    PayloadFits r.payload.length (r.value s) := by
  have hb := regValue_lt r.wires s
  unfold WindowRow.value signedRegValue signedDecode
  simp only [WindowRow.wires,List.length_append,List.length_singleton,Nat.add_sub_cancel] at *
  unfold PayloadFits
  split
  · rename_i h
    have hp : 0 < (2^r.payload.length:Nat) := Nat.two_pow_pos _
    constructor <;> omega
  · rename_i h
    simp only [Nat.pow_succ] at hb ⊢
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    constructor <;> omega

/-- Decoder views need public low-bit prefixes even at the narrow ends of
 the walk. This planner allocates and sign-copies the missing bits. -/
def planDecoderRow (A : Arena) (r : WindowRow) (minimum : Nat) :=
  planRowResize A r (max minimum r.payload.length)

theorem planDecoderRow_exists (A : Arena) (r : WindowRow) (minimum : Nat)
    (hn : (r.sign::r.payload).Nodup) (ho : (r.sign::r.payload).toFinset⊆A.live)
    (hc : A.live.card+(minimum-r.payload.length)≤935) :
    ∃ B out p,planDecoderRow A r minimum=some (B,out,p) := by
  apply planRowResize_exists A r _ hn ho
  have h : max minimum r.payload.length-r.payload.length=minimum-r.payload.length := by omega
  simpa only [h] using hc

theorem planDecoderRow_correct (A B : Arena) (r out : WindowRow) (minimum : Nat)
    (p : Program) (h : planDecoderRow A r minimum=some (B,out,p))
    (s : State) (m : List Bool) (hr : A.Ready s.basis) :
    minimum≤out.payload.length ∧ r.payload.length≤out.payload.length ∧
    B.Ready (run p m s).basis ∧ out.value (run p m s).basis=r.value s.basis ∧
    (run p m s).phase=s.phase ∧
    B.live.card≤A.live.card+(minimum-r.payload.length) := by
  have hc := planRowResize_correct A B r out _ p h s m hr
    ((r.value_fits s.basis).mono (Nat.le_max_right _ _))
  have hb := planRowResize_live_bound A B r out _ p h
  refine ⟨by rw [hc.1]; exact Nat.le_max_left _ _,
    by rw [hc.1]; exact Nat.le_max_right _ _,hc.2.2.2.1,hc.2.2.2.2,
    planRowResize_phase A B r out _ p h s m,?_⟩
  have he : max minimum r.payload.length-r.payload.length=minimum-r.payload.length := by omega
  simpa only [he] using hb

/-- Padding is a proper, zero-measurement sign-copy stream. Its exact inverse
returns the borrowed wires after the decoder has restored the padded rows. -/
theorem planDecoderRow_roundtrip (A B : Arena) (r out : WindowRow) (minimum : Nat)
    (p : Program) (h : planDecoderRow A r minimum=some (B,out,p))
    (s : State) (m n : List Bool) : run p.reverse n (run p m s)=s :=
  run_reverse_proper p (planRowResize_resources A B r out _ p h).1 s m n

end ECDSAAdd.Arithmetic.Paper935
