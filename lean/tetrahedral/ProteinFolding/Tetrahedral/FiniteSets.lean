import ProteinFolding.Tetrahedral.Geometry
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Finite sets of sites: internal bonds and edge boundary

The manuscript's e(S) counts each internal edge once. We orient such edges
from A to B, which gives a canonical representative. Boundary edges are
counted at their unique endpoint in S. The basic identity is
`4 * |S| = 2 * e(S) + |∂S|`.
-/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

/-- Neighbours of p that lie in the finite occupied set S. -/
def internalNeighbours (S : Finset Site) (p : Site) : Finset Site :=
  (neighbours p).filter (fun q => q ∈ S)

/-- Neighbours of p outside the occupied set. -/
def externalNeighbours (S : Finset Site) (p : Site) : Finset Site :=
  (neighbours p).filter (fun q => q ∉ S)

/-- The A-to-B endpoints of all internal bonds, with each edge counted once. -/
def internalEdges (S : Finset Site) : Finset (Site × Site) :=
  (S ×ˢ S).filter (fun pq => DirectedBond pq.1 pq.2)

def internalEdgeCount (S : Finset Site) : ℕ := (internalEdges S).card

/-- Each outgoing boundary bond is counted at its unique endpoint in S. -/
def boundaryCount (S : Finset Site) : ℕ :=
  ∑ p ∈ S, (externalNeighbours S p).card

theorem internalNeighbours_eq_filter (S : Finset Site) (p : Site) :
    internalNeighbours S p = S.filter (fun q => tetrahedralLattice.Adj p q) := by
  ext q
  simp [internalNeighbours, and_comm]

theorem neighbour_partition (S : Finset Site) (p : Site) :
    (internalNeighbours S p).card + (externalNeighbours S p).card = 4 := by
  simpa [internalNeighbours, externalNeighbours] using
    Finset.filter_card_add_filter_neg_card_eq_card (s := neighbours p) (p := fun q => q ∈ S)

theorem directedBond_asymm {p q : Site} (h : DirectedBond p q) : ¬ DirectedBond q p := by
  intro h'
  exact sublattices_disjoint p.val h.1 h'.2.1

theorem internalNeighbour_card (S : Finset Site) (p : Site) :
    (internalNeighbours S p).card =
      (S.filter (fun q => DirectedBond p q)).card +
        (S.filter (fun q => DirectedBond q p)).card := by
  rw [internalNeighbours_eq_filter]
  have heq : S.filter (fun q => tetrahedralLattice.Adj p q) =
      S.filter (fun q => DirectedBond p q) ∪ S.filter (fun q => DirectedBond q p) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    change (_ ∧ (DirectedBond p q ∨ DirectedBond q p)) ↔ _
    exact and_or_left
  rw [heq, Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (by
    intro q h h'
    exact directedBond_asymm (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp h').2)

theorem internalEdgeCount_eq_sum (S : Finset Site) :
    internalEdgeCount S = ∑ p ∈ S, (S.filter (fun q => DirectedBond p q)).card := by
  simp only [internalEdgeCount, internalEdges, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]

/-- Counting internal incidences counts each internal edge at both ends. -/
theorem sum_internalNeighbours (S : Finset Site) :
    (∑ p ∈ S, (internalNeighbours S p).card) = 2 * internalEdgeCount S := by
  simp_rw [internalNeighbour_card]
  rw [Finset.sum_add_distrib]
  have hswap : (∑ p ∈ S, (S.filter (fun q => DirectedBond q p)).card) =
      ∑ p ∈ S, (S.filter (fun q => DirectedBond p q)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap, ← internalEdgeCount_eq_sum]
  omega

/-- Section 2's degree/boundary identity, for every finite set of lattice sites. -/
theorem degree_boundary_identity (S : Finset Site) :
    4 * S.card = 2 * internalEdgeCount S + boundaryCount S := by
  have h := Finset.sum_congr (s₁ := S) rfl (fun p _ => neighbour_partition S p)
  simp only [Finset.sum_add_distrib, sum_internalNeighbours] at h
  simpa [boundaryCount, Nat.mul_comm] using h.symm

/-- The elementary degree-four bound, before the sharper isoperimetric theorem. -/
theorem internalEdgeCount_le_twice_card (S : Finset Site) :
    internalEdgeCount S ≤ 2 * S.card := by
  have h := degree_boundary_identity S
  omega

end ProteinFolding.Tetrahedral
