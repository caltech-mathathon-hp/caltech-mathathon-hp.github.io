import ProteinFolding.Common.Statement
import Mathlib.Data.Fin.VecNotation

/-!
# HP folding on the tetrahedral (diamond) lattice

This is the coordinate model D in Section 2 of the supplied
`HP_tetrahedral_proof (2).md` (14 November 2026).

The graph is fixed and infinite. An input contains only a finite H/P word and
a signed bond threshold; no scaffold, pinned sites, obstacles or bounding box
are part of the problem. All residues must occupy different lattice sites.
Following the manuscript, H-H backbone bonds contribute to the score.

The shared `Sequence`, `Fold`, `bondCount` and `HPStringFold` definitions are
reused. The complexity target is defined in `Tetrahedral.MainTheorem`.
-/

namespace ProteinFolding.Tetrahedral

/-- Ambient integer coordinates, before restricting to the diamond lattice. -/
abbrev Coordinates := Fin 3 → ℤ

def coordinateSum (p : Coordinates) : ℤ := p 0 + p 1 + p 2

/-- The even sublattice A: all coordinates even, with sum divisible by four. -/
def InASublattice (p : Coordinates) : Prop :=
  (∀ k, p k % 2 = 0) ∧ coordinateSum p % 4 = 0

/-- The odd sublattice B: all coordinates odd, with sum congruent to three. -/
def InBSublattice (p : Coordinates) : Prop :=
  (∀ k, p k % 2 = 1) ∧ coordinateSum p % 4 = 3

instance decidableInASublattice : DecidablePred InASublattice :=
  fun p => inferInstanceAs (Decidable
    ((∀ k, p k % 2 = 0) ∧ coordinateSum p % 4 = 0))

instance decidableInBSublattice : DecidablePred InBSublattice :=
  fun p => inferInstanceAs (Decidable
    ((∀ k, p k % 2 = 1) ∧ coordinateSum p % 4 = 3))

/-- The sites D = A ∪ B. These congruences also cover negative coordinates. -/
def IsLatticeSite (p : Coordinates) : Prop :=
  InASublattice p ∨ InBSublattice p

instance decidableIsLatticeSite : DecidablePred IsLatticeSite :=
  fun p => inferInstanceAs (Decidable (InASublattice p ∨ InBSublattice p))

/-- Only valid diamond-lattice sites can occur in a fold. -/
abbrev Site := {p : Coordinates // IsLatticeSite p}

/-- The manuscript's t₁, t₂, t₃, t₄, indexed by 0, 1, 2, 3. -/
def bondVector (d : Fin 4) : Coordinates :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]] d

/-- An oriented bond from A to B: y = x + t_d. -/
def DirectedBond (x y : Site) : Prop :=
  InASublattice x.val ∧ InBSublattice y.val ∧
    ∃ d : Fin 4, ∀ k : Fin 3, y.val k = x.val k + bondVector d k

instance decidableDirectedBond : DecidableRel DirectedBond :=
  fun x y => inferInstanceAs (Decidable
    (InASublattice x.val ∧ InBSublattice y.val ∧
      ∃ d : Fin 4, ∀ k : Fin 3, y.val k = x.val k + bondVector d k))

theorem sublattices_disjoint (p : Coordinates) :
    InASublattice p → ¬ InBSublattice p := by
  intro hA hB
  exact zero_ne_one ((hA.1 0).symm.trans (hB.1 0))

/-- The undirected diamond lattice: A-sites step by +t_d and B-sites by -t_d.
This is the four-neighbour graph of the manuscript, not the FCC lattice. -/
def tetrahedralLattice : SimpleGraph Site where
  Adj x y := DirectedBond x y ∨ DirectedBond y x
  symm := by
    intro x y h
    exact h.elim Or.inr Or.inl
  loopless := by
    intro x h
    rcases h with h | h
    · exact sublattices_disjoint x.val h.1 h.2.1
    · exact sublattices_disjoint x.val h.1 h.2.1

instance decidableTetrahedralAdj : DecidableRel tetrahedralLattice.Adj :=
  fun x y => inferInstanceAs (Decidable (DirectedBond x y ∨ DirectedBond y x))

/-- A self-avoiding fold attaining at least m H-H bonds, including backbone
bonds. The shared definition counts each unordered pair exactly once. -/
def HPStringFold (S : Sequence) (m : ℤ) : Prop :=
  ProteinFolding.HPStringFold (G := tetrahedralLattice) S m

/-- The finite input: a word and a signed threshold. Empty words are allowed. -/
structure HPInstance where
  sequence : Sequence
  minBonds : ℤ
  deriving Repr

def HPInstance.Accepts (I : HPInstance) : Prop :=
  HPStringFold I.sequence I.minBonds

def hpLanguage : Set HPInstance := {I | I.Accepts}

end ProteinFolding.Tetrahedral
