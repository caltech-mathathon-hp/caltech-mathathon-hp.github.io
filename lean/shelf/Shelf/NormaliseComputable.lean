import ProteinFolding.Cubic.Proofs.PackingWordComputableSource
import ProteinFolding.Common.TM2Conditional
import ProteinFolding.Cubic.Proofs.VerifierPerfectEquality
import Shelf.Source

/-!
# A Turing machine for the normalisation

Section 3 of the paper normalises the instance before it writes the string:
every size and the capacity are multiplied by 6, and if the number of bins is
even, one item of size `B` and one bin are added. This file shows that a Turing
machine does this in polynomial time, for numbers written in unary
(`Packing.instanceEncoding`). The machines for the single steps are the ones of
the team's library.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Computability Turing TM2CompositionPoly TM2ProductMap

/-- The letter substitution that multiplies unary numbers by 6: a `true` becomes
six `true`s, a separator `false` stays. -/
def sixLetter : Bool → List Bool
  | true => [true, true, true, true, true, true]
  | false => [false]

/-- Substituting `sixLetter` in the unary code of `n` gives the unary code of `6 n`. -/
theorem sixLetter_unary (n : ℕ) :
    (unaryEncodeNat n).flatMap sixLetter = unaryEncodeNat (6 * n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, sixLetter, ih, Nat.mul_succ]

/-- Substituting `sixLetter` in the code of a list of sizes multiplies every size by 6. -/
theorem sixLetter_items (xs : List ℕ) :
    (Packing.itemEncoding.encode xs).flatMap sixLetter =
      Packing.itemEncoding.encode (xs.map (6 * ·)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [Packing.itemEncoding, SAT.encTerminated, List.flatMap_cons] at *
    simp [List.flatMap_append, sixLetter_unary, sixLetter, ih]

/-- A machine that multiplies every size by 6. -/
noncomputable def scaleItemsComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding Packing.itemEncoding
      (fun I : Packing.Instance => I.sizes.map (6 * ·)) := by
  apply Packing.ofCode (f := fun I : Packing.Instance => I.sizes.map (6 * ·))
  simpa only [Function.comp_def, sixLetter_items] using
    compose (Packing.toCode Packing.sizesComputable)
      (TM2WordSubstitution.flatMapComputable sixLetter 6 (by intro b; cases b <;> decide))

/-- A machine that multiplies the capacity by 6. -/
noncomputable def scaleCapacityComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat
      (fun I : Packing.Instance => 6 * I.capacity) := by
  apply Packing.ofCode (f := fun I : Packing.Instance => 6 * I.capacity)
  simpa only [Function.comp_def, unaryFinEncodingNat, sixLetter_unary] using
    compose (Packing.toCode Packing.capacityComputable)
      (TM2WordSubstitution.flatMapComputable sixLetter 6 (by intro b; cases b <;> decide))

/-- A machine for `Packing.scale 6`: sizes and capacity multiplied by 6. -/
noncomputable def scaleComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding Packing.instanceEncoding
      (Packing.scale 6) := by
  let h := pairComputable scaleItemsComputable
    (pairComputable scaleCapacityComputable Packing.binsComputable)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => h.outputsFun I }

/-- A machine for the item list of `Packing.pad`: the capacity put in front of the sizes. -/
noncomputable def padItemsComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding Packing.itemEncoding
      (fun I : Packing.Instance => I.capacity :: I.sizes) :=
  Packing.ofCode (f := fun I : Packing.Instance => I.capacity :: I.sizes)
    CubicPacking.WordGenerator.paddedItemCodeComputable

/-- A machine for `Packing.pad`: one item of size `B` and one bin more. -/
noncomputable def padComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding Packing.instanceEncoding Packing.pad := by
  let h := pairComputable padItemsComputable
    (pairComputable Packing.capacityComputable
      (CubicPacking.WordGenerator.add Packing.binsComputable
        (CubicPacking.WordGenerator.natConstant _ 1)))
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => h.outputsFun I }

/-- A machine that decides whether the number of bins is even, by comparing
`2 (m / 2)` with `m`. -/
noncomputable def evenBinsComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding finEncodingBoolBool
      (fun I : Packing.Instance => decide (Even I.bins)) := by
  let hhalf := compose Packing.binsComputable CubicPacking.UnaryHalf.computable
  let hdouble := CubicPacking.WordGenerator.add hhalf hhalf
  let h := compose (pairComputable hdouble Packing.binsComputable)
    PerfectUnaryEquality.unaryEqualityComputable
  have heq : ∀ n : ℕ, (n / 2 + n / 2 = n) = Even n := by
    intro n; rw [Nat.even_iff]; apply propext; omega
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => by simpa [heq] using h.outputsFun I }

/-- The normalisation of Section 3 is computed by a Turing machine in polynomial
time. -/
noncomputable def normaliseComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding Packing.instanceEncoding normalise := by
  let h := TM2Conditional.iteComputable evenBinsComputable
    (compose scaleComputable padComputable) scaleComputable
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => by
        simpa [normalise, padOdd, Packing.scale] using h.outputsFun I }

end ProteinFolding.Shelf
