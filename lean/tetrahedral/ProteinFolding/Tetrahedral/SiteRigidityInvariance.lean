import ProteinFolding.Tetrahedral.SiteRigidity
import ProteinFolding.Tetrahedral.SharpBound

/-! Geometric invariance and the converse of the extremal classification. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

theorem internalNeighbours_image_of_embedding (S : Finset Site) (f : Site → Site)
    (hadj : ∀ p q, tetrahedralLattice.Adj (f p) (f q) ↔ tetrahedralLattice.Adj p q)
    (p : Site) :
    internalNeighbours (S.image f) (f p) = (internalNeighbours S p).image f := by
  rw [internalNeighbours_eq_filter, internalNeighbours_eq_filter]
  ext q
  constructor
  · intro hq
    have h := Finset.mem_filter.mp hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h.1
    exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, (hadj p r).mp h.2⟩, rfl⟩
  · intro hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    have h := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨r, h.1, rfl⟩, (hadj p r).mpr h.2⟩

theorem internalEdgeCount_image_of_embedding (S : Finset Site) (f : Site → Site)
    (hf : Function.Injective f)
    (hadj : ∀ p q, tetrahedralLattice.Adj (f p) (f q) ↔ tetrahedralLattice.Adj p q) :
    internalEdgeCount (S.image f) = internalEdgeCount S := by
  have hsum : (∑ q ∈ S.image f, (internalNeighbours (S.image f) q).card) =
      ∑ p ∈ S, (internalNeighbours S p).card := by
    rw [Finset.sum_image (fun p _ q _ heq => hf heq)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [internalNeighbours_image_of_embedding S f hadj p,
      Finset.card_image_of_injective _ hf]
  rw [sum_internalNeighbours, sum_internalNeighbours] at hsum
  omega

theorem boundaryCount_image_of_embedding (S : Finset Site) (f : Site → Site)
    (hf : Function.Injective f)
    (hadj : ∀ p q, tetrahedralLattice.Adj (f p) (f q) ↔ tetrahedralLattice.Adj p q) :
    boundaryCount (S.image f) = boundaryCount S := by
  have h₁ := degree_boundary_identity S
  have h₂ := degree_boundary_identity (S.image f)
  rw [Finset.card_image_of_injective _ hf,
    internalEdgeCount_image_of_embedding S f hf hadj] at h₂
  omega

theorem internalEdgeCount_normalize (S : Finset Site) (c : Site) :
    internalEdgeCount (S.image (normalizeSite c)) = internalEdgeCount S :=
  internalEdgeCount_image_of_embedding S (normalizeSite c) (normalizeSite_injective c)
    (adj_normalizeSite_iff c)

theorem boundaryCount_normalize (S : Finset Site) (c : Site) :
    boundaryCount (S.image (normalizeSite c)) = boundaryCount S :=
  boundaryCount_image_of_embedding S (normalizeSite c) (normalizeSite_injective c)
    (adj_normalizeSite_iff c)

/-- Full equality classification: the maximizers are precisely normalized
octahedra. -/
theorem contact_maximizer_iff_normalizes_to_octahedron (S : Finset Site) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m) :
    internalEdgeCount S = 2 * octahedralNumber m - 2 * m ^ 2 ↔
      ∃ c ∈ S, S.image (normalizeSite c) = octahedron m := by
  constructor
  · exact contact_maximizer_normalizes_to_octahedron S m hm hcard
  · rintro ⟨c, hc, heq⟩
    have h := internalEdgeCount_normalize S c
    rw [heq, octahedron_edge_threshold] at h
    exact h.symm

theorem boundary_minimizer_iff_normalizes_to_octahedron (S : Finset Site) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m) :
    boundaryCount S = 4 * m ^ 2 ↔
      ∃ c ∈ S, S.image (normalizeSite c) = octahedron m := by
  rw [← extremal_iff_boundary_minimum S m hcard]
  exact contact_maximizer_iff_normalizes_to_octahedron S m hm hcard

end ProteinFolding.Tetrahedral
