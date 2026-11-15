import ProteinFolding.Common.Contacts

/-!
# Single-chain HP folding on the square lattice

Crescenzi, Goldman, Papadimitriou, Piccolboni, Yannakakis,
*On the Complexity of Protein Folding*, J. Comput. Biol. 5(3), 423-465 (1998),
DOI: 10.1089/cmb.1998.5.423. In the saved full author manuscript:
- Introduction and Section 2: square lattice, injective folding, contact score.
- Section 2: losses (non-backbone edges with exactly one H endpoint).
- Section 3, Theorem 3: the single-string decision problem is NP-complete.

We use H/P for 1/0. All positions, including P's, are self-avoiding. The graph
is fixed and infinite, with no obstacles, pinned sites, or bounding box as input.
Empty and one-residue words are allowed. Thresholds are signed integers.
These are definitions only; the complexity targets are in `MainTheorem`.
-/

namespace ProteinFolding.Square

open scoped BigOperators

abbrev Site := Fin 2 → ℤ

def latticeDistance (x y : Site) : ℕ :=
  ∑ k : Fin 2, (x k - y k).natAbs

theorem latticeDistance_comm (x y : Site) : latticeDistance x y = latticeDistance y x := by
  apply Finset.sum_congr rfl
  intro k _
  rw [← Int.natAbs_neg (x k - y k), Int.neg_sub]

/-- The four-neighbour square lattice Z². Diagonal steps are excluded. -/
def squareLattice : SimpleGraph Site where
  Adj x y := latticeDistance x y = 1
  symm := by
    intro x y h
    rwa [latticeDistance_comm]
  loopless := by
    intro x
    simp [latticeDistance]

instance : DecidableRel squareLattice.Adj :=
  fun x y => inferInstanceAs (Decidable (latticeDistance x y = 1))

/-- The paper's score counts each non-backbone H-H contact exactly once. -/
def score (S : Sequence) (f : Fold squareLattice S.length) : ℕ :=
  contactCount S f

def energy (S : Sequence) (f : Fold squareLattice S.length) : ℤ :=
  -(score S f : ℤ)

def IsOptimal (S : Sequence) (f : Fold squareLattice S.length) : Prop :=
  ∀ g : Fold squareLattice S.length, energy S f ≤ energy S g

/-- The contact-threshold decision version of the introductory optimization problem. -/
def HPStringFold (S : Sequence) (m : ℤ) : Prop :=
  ∃ f : Fold squareLattice S.length, m ≤ (score S f : ℤ)

structure HPInstance where
  sequence : Sequence
  minContacts : ℤ
  deriving Repr

def HPInstance.Accepts (I : HPInstance) : Prop :=
  HPStringFold I.sequence I.minContacts

def hpLanguage : Set HPInstance := {I | I.Accepts}

/-- The four distinct adjacent sites, indexed east, west, north, south. -/
def step (p : Site) (d : Fin 4) : Site :=
  fun k => if k = 0 then
    if d = 0 then p 0 + 1 else if d = 1 then p 0 - 1 else p 0
  else
    if d = 2 then p 1 + 1 else if d = 3 then p 1 - 1 else p 1

/-- A loss is represented by its unique H endpoint and outward direction.
The other endpoint can be P or unoccupied, but cannot be H or a backbone neighbour.
Quantification over sequence positions is finite, including for an empty word. -/
def lossEdges (S : Sequence) (f : Fold squareLattice S.length) :
    Finset (Fin S.length × Fin 4) :=
  (hydrophobicIndices S ×ˢ Finset.univ).filter fun id =>
    (∀ j : Fin S.length, S.get j = Residue.H → f.pos j ≠ step (f.pos id.1) id.2) ∧
    (∀ j : Fin S.length, id.1.val + 1 = j.val ∨ j.val + 1 = id.1.val →
      f.pos j ≠ step (f.pos id.1) id.2)

def lossCount (S : Sequence) (f : Fold squareLattice S.length) : ℕ :=
  (lossEdges S f).card

/-- The paper's literal single-string decision formulation: at most E losses. -/
def HPLossFold (S : Sequence) (E : ℤ) : Prop :=
  ∃ f : Fold squareLattice S.length, (lossCount S f : ℤ) ≤ E

structure LossInstance where
  sequence : Sequence
  maxLosses : ℤ
  deriving Repr

def LossInstance.Accepts (I : LossInstance) : Prop :=
  HPLossFold I.sequence I.maxLosses

def lossLanguage : Set LossInstance := {I | I.Accepts}

end ProteinFolding.Square
