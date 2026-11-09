import ECDSAAdd.Submission.Entrant.ParkAWorkLoan
import ECDSAAdd.Submission.Entrant.ParkAData
import ECDSAAdd.Submission.Entrant.ParkAProgramBool

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant

/-! Proof-local constructors. The selected runtime definitions remain unchanged. -/
namespace ParkAInputFast

/-- Append the caller's suffix while constructing each recursive output only once. -/
def mappedAddTail : List MappedBit → List Wire → List Wire → Wire → Program → Program
  | b::b'::bits, y::y'::ys, c::cs, cin, tail =>
      mappedMajority b y cin c ++
        mappedAddTail (b'::bits) (y'::ys) cs c
          (mappedEraseCarry b y cin c ++ (mappedSum b y cin ++ tail))
  | [b], [y], _, cin, tail => mappedSum b y cin ++ tail
  | _, _, _, _, tail => tail

/-- Exact syntax equality, including every malformed-length fallback. -/
theorem mappedAddTail_eq (bits : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (tail : Program) :
    mappedAddTail bits ys carry cin tail = mappedAdd bits ys carry cin ++ tail := by
  induction bits generalizing ys carry cin tail with
  | nil => cases ys <;> cases carry <;> rfl
  | cons b bits ih =>
      cases bits with
      | nil =>
          cases ys with
          | nil => rfl
          | cons y ys => cases ys <;> rfl
      | cons b' bits =>
          cases ys with
          | nil => rfl
          | cons y ys =>
              cases ys with
              | nil => rfl
              | cons y' ys =>
                  cases carry with
                  | nil => rfl
                  | cons c cs =>
                      change mappedMajority b y cin c ++
                        mappedAddTail (b'::bits) (y'::ys) cs c
                          (mappedEraseCarry b y cin c ++ (mappedSum b y cin ++ tail)) =
                        (((mappedMajority b y cin c ++ mappedAdd (b'::bits) (y'::ys) cs c) ++
                          mappedEraseCarry b y cin c) ++ mappedSum b y cin) ++ tail
                      rw [ih]
                      simp only [List.append_assoc]

def eraseLtTail : List Wire → List Wire → List Wire → Wire → Wire → Program → Program
  | a::a'::as, b::b'::bs, c::cs, cin, target, tail =>
      borrowMajority a b cin c ++
        eraseLtTail (a'::as) (b'::bs) cs c target (eraseBorrow a b cin c ++ tail)
  | [a], [b], _, cin, target, tail => eraseBorrow a b cin target ++ tail
  | _, _, _, _, _, tail => tail

theorem eraseLtTail_eq (xs ys carry : List Wire) (cin target : Wire) (tail : Program) :
    eraseLtTail xs ys carry cin target tail = eraseLtChain xs ys carry cin target ++ tail := by
  induction xs generalizing ys carry cin target tail with
  | nil => cases ys <;> cases carry <;> rfl
  | cons a xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => rfl
          | cons b ys => cases ys <;> rfl
      | cons a' xs =>
          cases ys with
          | nil => rfl
          | cons b ys =>
              cases ys with
              | nil => rfl
              | cons b' ys =>
                  cases carry with
                  | nil => rfl
                  | cons c cs =>
                      change borrowMajority a b cin c ++
                        eraseLtTail (a'::xs) (b'::ys) cs c target (eraseBorrow a b cin c ++ tail) =
                        ((borrowMajority a b cin c ++
                          eraseLtChain (a'::xs) (b'::ys) cs c target) ++ eraseBorrow a b cin c) ++ tail
                      rw [ih]
                      simp only [List.append_assoc]

/-- The original qprogTq syntax with only its three recursive constructors replaced. -/
def qprogFast (K : MeasuredCanonicalModLayout) (p : Nat) : Program :=
  notRegister K.out ++
    mappedAddTail (mappedRead K.src false ++ [({wire := none, flip := false} : MappedBit)])
      K.extended K.carry K.cin [] ++
    [.CX K.high K.flag, .X K.flag] ++
    mappedAddTail (mappedConstant (some K.flag) K.out.length p) K.out
      (K.carry.take (K.out.length - 1)) K.cin [] ++
    [.CX K.flag K.high] ++ [.X K.high, .X K.flag] ++
    eraseLtTail K.out K.src (K.carry.take (K.out.length - 1)) K.cin K.flag []

theorem qprogFast_eq (K : MeasuredCanonicalModLayout) (p : Nat) :
    qprogFast K p = qprogTq K p := by
  simp only [qprogFast, mappedAddTail_eq, eraseLtTail_eq, List.append_nil,
    qprogTq, MeasuredCanonicalModLayout.sum, mappedConstAdd]

def aMiddleFast (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK ++
    (qprogFast L.measuredCore SquareReduction.p ++
      maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK)

theorem aMiddleFast_eq (L : CuccaroStreamedSquareWideLayout) (g : Wire) :
    aMiddleFast L g = InverseCarryDevelop.aMiddle L g := by
  rw [aMiddleFast, qprogFast_eq, InverseCarryDevelop.aMiddle]

theorem fast_input_bool : ParkAProgramBool.programEq ParkAData.p0
    (ParkAInputFast.aMiddleFast Baselines.layout.dialogStreamedSquareWide
      Baselines.layout.core.generic) = true := by
  decide +kernel

theorem original_input_eq : ParkAData.p0 =
    InverseCarryDevelop.aMiddle Baselines.layout.dialogStreamedSquareWide
      Baselines.layout.core.generic :=
  (ParkAProgramBool.programEq_sound _ _ fast_input_bool).trans
    (ParkAInputFast.aMiddleFast_eq _ _)

end ParkAInputFast
