import ProteinFolding.Common.Complexity

/-! Little-endian binary subtraction, including noncanonical all-zero words.
The operation retains its input length. These arithmetic identities support
the finite-state binary/unary comparator; no machine claim is made here. -/

namespace ProteinFolding.TM2Arithmetic

open Computability

def bitValue : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitValue bs

def decrement : Bool → List Bool → List Bool × Bool
  | borrow, [] => ([], borrow)
  | borrow, b :: bs =>
    let out := decrement (borrow && !b) bs
    ((if borrow then !b else b) :: out.1, out.2)

theorem decrement_false (bs : List Bool) : decrement false bs = (bs, false) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [decrement, ih]

theorem decrement_length (borrow : Bool) (bs : List Bool) :
    (decrement borrow bs).1.length = bs.length := by
  induction bs generalizing borrow with
  | nil => rfl
  | cons b bs ih => simp [decrement, ih]

theorem decrement_spec (bs : List Bool) :
    if (decrement true bs).2 then bitValue bs = 0
      else bitValue (decrement true bs).1 + 1 = bitValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true => simp [decrement, decrement_false, bitValue]; omega
    | false =>
      cases hc : (decrement true bs).2
      · simp [decrement, hc, bitValue] at ih ⊢
        omega
      · simp [decrement, hc, bitValue] at ih ⊢
        omega

theorem decrement_underflow_iff (bs : List Bool) :
    (decrement true bs).2 = true ↔ bitValue bs = 0 := by
  have hs := decrement_spec bs
  cases hc : (decrement true bs).2 <;> simp [hc] at hs ⊢ <;> omega

theorem decrement_success (bs : List Bool) (h : (decrement true bs).2 = false) :
    bitValue (decrement true bs).1 + 1 = bitValue bs := by
  simpa [h] using decrement_spec bs

theorem bitValue_encodePosNum (p : PosNum) : bitValue (encodePosNum p) = (p : ℕ) := by
  induction p with
  | one => rfl
  | bit0 p ih => simp [encodePosNum, bitValue, ih]; omega
  | bit1 p ih => simp [encodePosNum, bitValue, ih]; omega

theorem bitValue_encodeNum (n : Num) : bitValue (encodeNum n) = (n : ℕ) := by
  cases n with
  | zero => rfl
  | pos p => exact bitValue_encodePosNum p

theorem bitValue_encodeNat (n : ℕ) : bitValue (encodeNat n) = n := by
  change bitValue (encodeNum (n : Num)) = n
  rw [bitValue_encodeNum, Num.to_of_nat]

end ProteinFolding.TM2Arithmetic
