import ProteinFolding.Common.Statement

/-! Cubic-lattice problem statements from Berger--Leighton (1998).
The original declaration names are retained for compatibility. -/

namespace ProteinFolding

open scoped BigOperators

/-- The sites of the three-dimensional integer lattice. -/
abbrev Site := Fin 3 → ℤ

/-- Manhattan distance on the cubic lattice. -/
def latticeDistance (x y : Site) : ℕ :=
  ∑ k : Fin 3, (x k - y k).natAbs

theorem latticeDistance_comm (x y : Site) : latticeDistance x y = latticeDistance y x := by
  apply Finset.sum_congr rfl
  intro k _
  rw [← Int.natAbs_neg (x k - y k), Int.neg_sub]

/-- The fixed infinite graph Z³: a step changes exactly one coordinate by ±1. -/
def cubicLattice : SimpleGraph Site where
  Adj x y := latticeDistance x y = 1
  symm := by
    intro x y h
    rw [latticeDistance_comm y x]
    exact h
  loopless := by
    intro x
    simp [latticeDistance]

instance : DecidableRel cubicLattice.Adj :=
  fun x y => inferInstanceAs (Decidable (latticeDistance x y = 1))

/-- The finite input to HP STRING-FOLD when the graph is fixed to Z³. -/
structure HPInstance where
  sequence : Sequence
  minBonds : ℤ
  deriving Repr

def HPInstance.Accepts (I : HPInstance) : Prop :=
  HPStringFold (G := cubicLattice) I.sequence I.minBonds

/-- The set of yes-instances; no encoding or complexity claim is implicit. -/
def hpLanguage : Set HPInstance := {I | I.Accepts}

/-- The n × n × n lattice cube with lower corner a. For n = 0 it is empty. -/
def cube (a : Site) (n : ℕ) : Set Site :=
  {p | ∀ k : Fin 3, a k ≤ p k ∧ p k < a k + (n : ℤ)}

instance (p a : Site) (n : ℕ) : Decidable (p ∈ cube a n) :=
  inferInstanceAs
    (Decidable (∀ k : Fin 3, a k ≤ p k ∧ p k < a k + (n : ℤ)))

/-- The sites occupied by H residues in a fold. -/
def hydrophobicSites (S : Sequence) (f : Fold cubicLattice S.length) : Set Site :=
  {p | ∃ i : Fin S.length, S.get i = Residue.H ∧ f.pos i = p}

/-- Exact filling, not merely containment: every cube site is occupied by H,
and every H is in the cube. Injectivity also excludes P from these sites. -/
def PacksCube (S : Sequence) (f : Fold cubicLattice S.length) (n : ℕ) : Prop :=
  ∃ a : Site, hydrophobicSites S f = cube a n

/-- The well-formed inputs to PERFECT HP STRING-FOLD. A natural side length
implements the meaningful nonnegative integer sizes; zero is permitted. -/
structure PerfectInstance where
  side : ℕ
  sequence : Sequence
  count_eq : hydrophobicCount sequence = side ^ 3

def PerfectInstance.Accepts (I : PerfectInstance) : Prop :=
  ∃ f : Fold cubicLattice I.sequence.length, PacksCube I.sequence f I.side

def perfectLanguage : Set PerfectInstance := {I | I.Accepts}

/-- A total predicate on raw inputs: an incorrect H count makes it false. -/
def PerfectHPStringFold (S : Sequence) (n : ℕ) : Prop :=
  hydrophobicCount S = n ^ 3 ∧
    ∃ f : Fold cubicLattice S.length, PacksCube S f n

/-- The number of internal lattice edges in an n × n × n cube.
Natural subtraction also gives zero for the empty cube. -/
def cubeBondThreshold (n : ℕ) : ℤ := (3 * n ^ 2 * (n - 1) : ℕ)

/-- Theorem 3.2 of the paper, recorded as a proposition for future proof.
This is a definition of a target, NOT a proof or an axiom. -/
def PerfectIffThreshold : Prop :=
  ∀ I : PerfectInstance,
    I.Accepts ↔ HPStringFold (G := cubicLattice) I.sequence (cubeBondThreshold I.side)

end ProteinFolding
