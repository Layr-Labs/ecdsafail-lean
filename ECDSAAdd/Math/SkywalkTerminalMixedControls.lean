import ECDSAAdd.Math.SkywalkTerminalLastControls

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.SkywalkTrace
open SkywalkRails Secp256k1
attribute [local irreducible] Nat.iterate trace next

private theorem map_getD_read {α β : Type} (read : α → β) (rs : List α)
    (i : Nat) (default : α) :
    (rs.map read).getD i (read default)=read (rs.getD i default) := by
  induction rs generalizing i with
  | nil => rfl
  | cons r rs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

/-- Generic physical-record bridge. Instantiate α=Wire×Wire and read with
the caller's two basis reads. This stays below arithmetic/kernel imports. -/
theorem record_index511_controls {α : Type} (rs : List α) (read : α → Bool×Bool)
    (default : α) (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (hr : rs.map read=trace 512 (encode false false (x : Int) (ECDSAAdd.p : Int))) :
    read (rs.getD 511 default)=(true,false) := by
  have h : (rs.map read).getD 511 (read default)=(true,false) := by
    rw [hr]
    exact trace512_last x hx0 hx _
  rw [map_getD_read] at h
  exact h

private theorem selected_zip_map {α : Type} (rs : List α) (cs : List (Bool×Bool))
    (read : α → Bool×Bool) (enabled : Bool) (hlen : rs.length=cs.length) :
    (rs.zip cs).map (fun l => if enabled then read l.1 else l.2)=
      if enabled then rs.map read else cs := by
  induction rs generalizing cs with
  | nil =>
    cases cs with
    | nil => cases enabled <;> rfl
    | cons c cs => simp at hlen
  | cons r rs ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have ht : rs.length=cs.length := by simpa using hlen
      have tail := ih cs ht
      have lifted := congrArg (List.cons (if enabled then read r else c)) tail
      cases enabled <;> simpa only [List.zip_cons_cons,List.map_cons,
        Bool.false_eq_true,if_false,if_true] using lifted

/-- The exact effective-control list used by the mixed transcript selects
the actual trace or the divisor-one trace. Both have the same final letter. -/
theorem mixed_controls_index511 {α : Type} (rs : List α) (read : α → Bool×Bool)
    (enabled : Bool) (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (hr : rs.map read=trace 512 (encode false false (x : Int) (ECDSAAdd.p : Int)))
    (default : Bool×Bool) :
    ((rs.zip (trace 512 (encode false false (1 : Int) (ECDSAAdd.p : Int)))).map
      (fun l => if enabled then read l.1 else l.2)).getD 511 default=(true,false) := by
  have len : rs.length=512 := by
    have h := congrArg List.length hr
    simpa only [List.length_map,trace_length] using h
  rw [selected_zip_map rs _ read enabled (by simpa only [trace_length] using len)]
  cases enabled
  · exact unit_trace512_last default
  · rw [hr]
    exact trace512_last x hx0 hx default

/-- Pointwise form for the actual mixed letter at index511. In arithmetic,
the pair read is componentwise mixedTranscriptBit; Bool cases identify it
with this pair selector. The index/default do not change record dependencies. -/
theorem mixed_letter_index511 {α : Type} (rs : List α) (read : α → Bool×Bool)
    (enabled : Bool) (default : α) (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (hr : rs.map read=trace 512 (encode false false (x : Int) (ECDSAAdd.p : Int))) :
    let letter := (rs.zip (trace 512 (encode false false (1 : Int) (ECDSAAdd.p : Int)))).getD
      511 (default,(false,false))
    (if enabled then read letter.1 else letter.2)=(true,false) := by
  dsimp only
  have h := mixed_controls_index511 rs read enabled x hx0 hx hr
    (if enabled then read default else (false,false))
  have selected := map_getD_read
    (fun l : α×(Bool×Bool) => if enabled then read l.1 else l.2)
    (rs.zip (trace 512 (encode false false (1 : Int) (ECDSAAdd.p : Int))))
    511 (default,(false,false))
  rw [selected] at h
  exact h

end ECDSAAdd.SkywalkTrace
#print axioms ECDSAAdd.SkywalkTrace.record_index511_controls
#print axioms ECDSAAdd.SkywalkTrace.mixed_controls_index511
#print axioms ECDSAAdd.SkywalkTrace.mixed_letter_index511
