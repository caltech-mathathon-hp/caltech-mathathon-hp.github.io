import ProteinFolding.Cubic.MainTheorem

/-! Small encoding and framework checks; none proves an HP complexity claim.
Mathlib's `Nat.binaryRec` uses equality transports, so raw `decide` does not
normalize its natural-to-Num conversion. The existing `Num.of_to_nat` lemma
exposes the explicit binary digits before the final `rfl`/`decide` checks. -/

namespace ProteinFolding.ComplexityExamples

open Residue Computability

private theorem naturalBits (n : Num) : encodeNat (n : ℕ) = encodeNum n := by
  simp only [encodeNat, Num.of_to_nat]

private theorem bits0 : encodeNat 0 = [] := naturalBits .zero
private theorem bits1 : encodeNat 1 = [true] := naturalBits (.pos .one)
private theorem bits2 : encodeNat 2 = [false, true] := naturalBits (.pos (.bit0 .one))
private theorem bits5 : encodeNat 5 = [true, false, true] :=
  naturalBits (.pos (.bit1 (.bit0 .one)))
private theorem bits8 : encodeNat 8 = [false, false, false, true] :=
  naturalBits (.pos (.bit0 (.bit0 (.bit0 .one))))

example : hpEncoding.decode (hpEncoding.encode ⟨[H, P, H], -5⟩) =
    some (HPInstance.mk [H, P, H] (-5)) := by
  have h : encodeSigned (-5) = [true, true, false, true] := by
    change true :: encodeNat 5 = _
    rw [bits5]
  simp only [hpEncoding, pairEncoding, sequenceEncoding, signedEncoding, wordEncoding, h]
  rfl

example : hpEncoding.decode (hpEncoding.encode ⟨[], 0⟩) =
    some (HPInstance.mk [] 0) := by
  have h : encodeSigned 0 = [false] := by
    change false :: encodeNat 0 = _
    rw [bits0]
  simp only [hpEncoding, pairEncoding, sequenceEncoding, signedEncoding, wordEncoding, h]
  rfl

example : perfectEncoding.decode (perfectEncoding.encode ([H], 1)) =
    some ([H], 1) := by
  simp only [perfectEncoding, pairEncoding, sequenceEncoding, wordEncoding,
    finEncodingNatBool, encodingNatBool, bits1]
  rfl

example : perfectEncoding.decode (perfectEncoding.encode ([], 0)) =
    some ([], 0) := by
  simp only [perfectEncoding, pairEncoding, sequenceEncoding, wordEncoding,
    finEncodingNatBool, encodingNatBool, bits0]
  rfl

-- Distinguish signs and side lengths; do not conflate different instances.
example : hpEncoding.encode ⟨[H, P], -5⟩ ≠ hpEncoding.encode ⟨[H, P], 5⟩ := by
  unfold hpEncoding pairEncoding sequenceEncoding signedEncoding wordEncoding
  decide

example : perfectEncoding.encode ([H], 1) ≠ perfectEncoding.encode ([H], 2) := by
  simp only [perfectEncoding, pairEncoding, sequenceEncoding, wordEncoding,
    finEncodingNatBool, encodingNatBool, bits1, bits2]
  decide

-- 8 occupies four magnitude bits, not eight unary symbols.
example : (hpEncoding.encode ⟨[H, P], 8⟩).length = 8 := by
  have h : encodeSigned 8 = [false, false, false, false, true] := by
    change false :: encodeNat 8 = _
    rw [bits8]
  simp only [hpEncoding, pairEncoding, sequenceEncoding, signedEncoding, wordEncoding, h]
  rfl

example : (perfectEncoding.encode ([H], 8)).length = 6 := by
  simp only [perfectEncoding, pairEncoding, sequenceEncoding, wordEncoding,
    finEncodingNatBool, encodingNatBool, bits8]
  rfl

-- Generic encoding helpers also round-trip on concrete inputs.
example : (wordEncoding Bool).decode ((wordEncoding Bool).encode [true, false]) =
    some [true, false] := rfl

example : signedEncoding.decode (signedEncoding.encode (-8)) = some (-8) := by
  have h : encodeSigned (-8) = [true, false, false, false, true] := by
    change true :: encodeNat 8 = _
    rw [bits8]
  simp only [signedEncoding, h]
  rfl

example : sequenceEncoding.decode (sequenceEncoding.encode [H, P]) = some [H, P] := rfl

example :
    (pairEncoding (wordEncoding Bool) signedEncoding).decode
      ((pairEncoding (wordEncoding Bool) signedEncoding).encode ([true], -2)) =
        some ([true], -2) := by
  have h : encodeSigned (-2) = [true, false, true] := by
    change true :: encodeNat 2 = _
    rw [bits2]
  simp only [pairEncoding, wordEncoding, signedEncoding, h]
  rfl

example : (wordEncoding Bool).encode [true] ≠ (wordEncoding Bool).encode [false] := by
  unfold wordEncoding
  decide

example : sequenceEncoding.encode [H] ≠ sequenceEncoding.encode [P] := by
  unfold sequenceEncoding wordEncoding
  decide

example : signedEncoding.encode (-8) ≠ signedEncoding.encode 8 := by
  unfold signedEncoding
  decide

example :
    (pairEncoding (wordEncoding Bool) signedEncoding).encode ([true], -2) ≠
      (pairEncoding (wordEncoding Bool) signedEncoding).encode ([false], -2) := by
  unfold pairEncoding wordEncoding signedEncoding
  decide

-- Finite-word certificates meet InNP's surjectivity requirement directly.
example : Function.Surjective (wordEncoding Bool).encode := fun w => ⟨w, rfl⟩

-- The optional reflexivity check uses mathlib's actual identity machine.
example {A : Type} (ea : FinEncoding A) (L : A → Prop) : KarpReduces ea ea L L :=
  ⟨id, ⟨Turing.idComputableInPolyTime ea⟩, fun _ => Iff.rfl⟩

end ProteinFolding.ComplexityExamples
