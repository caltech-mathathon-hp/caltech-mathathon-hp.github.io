import Shelf.FoldBasics
import Shelf.Word

/-!
# Where the pieces of the string are

Section 4 of the paper says that it "uses only these features of `S`": the long
run `A`, the fillers `F₁` and `F₂`, the separators, the items, and the lengths of
the tethers. `Anatomy S J` records exactly these features, as positions of
letters in `S`. Theorem 12 is proved for any string with an anatomy, and
`shelfAnatomy` shows that the string of the reduction has one. So the counting
of letters and the geometry never meet in one proof.

Letters are numbered from 0, as in `Shelf.FoldBasics`.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue

/-- Letter `i` is an isolated `H`: an `H` with a `P` on either side. -/
def Isolated (S : Sequence) (i : ℕ) : Prop :=
  1 ≤ i ∧ S[i - 1]? = some P ∧ S[i]? = some H ∧ S[i + 1]? = some P

/-- `P D(r) P` is a factor of `S`, and the first `H` of this dense run is letter
`o`. The `H`'s of the run are the letters `o, o + 3, …, o + 3 (r - 1)`; each of
them is isolated, which also says that the two letters between consecutive ones
are `P`'s. -/
def RunAt (S : Sequence) (o r : ℕ) : Prop :=
  ∀ t, t < r → Isolated S (o + 3 * t)

/-- The sites of the `H`'s of a dense run, in their order. -/
def runSites {N : ℕ} (f : Fold cubicLattice N) (o r : ℕ) : List Site :=
  (List.range r).map fun t => site f (o + 3 * t)

/-- The features of the string that the proof of Theorem 12 uses. Here
`n = side J`, `m = J.bins`, `B = J.capacity`, and the items are numbered by
`Fin J.sizes.length`. -/
structure Anatomy (S : Sequence) (J : Packing.Instance) where
  /-- first `H` of the long run `A` -/
  oA : ℕ
  /-- first `H` of the filler `F₁` -/
  oF₁ : ℕ
  /-- the separator `σ_{j+1}`, for `j = 0, …, m` -/
  oSep : ℕ → ℕ
  /-- first `H` of the filler `F₂` -/
  oF₂ : ℕ
  /-- first `H` of the item `I_{i+1}` -/
  oItem : Fin J.sizes.length → ℕ
  runA : RunAt S oA (9 * side J - 10)
  runF₁ : RunAt S oF₁ (side J - 2)
  sep : ∀ j, j ≤ J.bins → Isolated S (oSep j)
  runF₂ : RunAt S oF₂ (side J - 2)
  runItem : ∀ i, RunAt S (oItem i) (J.sizes.get i)
  /-- The tether `P^n` from the last `H` of `F₁` to the first separator. -/
  tetherF₁ : oSep 0 = oF₁ + 3 * (side J - 3) + side J + 1
  tetherF₁_P : ∀ t, oF₁ + 3 * (side J - 3) < t → t < oSep 0 → S[t]? = some P
  /-- The inner tethers `P^(B+6)` between consecutive separators. -/
  tetherSep : ∀ j, j < J.bins → oSep (j + 1) = oSep j + J.capacity + 7
  tetherSep_P : ∀ j, j < J.bins → ∀ t, oSep j < t → t < oSep (j + 1) → S[t]? = some P
  /-- The tether `P^n` from the last separator to the first `H` of `F₂`. -/
  tetherF₂ : oF₂ = oSep J.bins + side J + 1
  tetherF₂_P : ∀ t, oSep J.bins < t → t < oF₂ → S[t]? = some P
  /-- The pieces come in the order `A`, `F₁`, separators, `F₂`, items. -/
  A_before_F₁ : oA + 3 * (9 * side J - 10) ≤ oF₁
  F₂_before_items : ∀ i, oF₂ + 3 * (side J - 2) ≤ oItem i
  items_in_order : ∀ i i', i < i' → oItem i + 3 * J.sizes.get i ≤ oItem i'

end ProteinFolding.Shelf
