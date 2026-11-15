import ProteinFolding.Tetrahedral.IntegerIsoperimetry
import ProteinFolding.Tetrahedral.OctahedralEdges

/-! The exact extremal value at N_m, including an octahedral maximizer.
The classification of all maximizing sets is a separate rigidity step. -/

namespace ProteinFolding.Tetrahedral

theorem octahedron_edge_threshold (m : ℕ) : internalEdgeCount (octahedron m) =
    2 * octahedralNumber m - 2 * m ^ 2 := by
  have h := octahedron_internalEdgeCount_add m
  omega

theorem edge_maximum_octahedron (S : Finset Site) (m : ℕ) (hm : 0 < m)
    (hcard : S.card = octahedralNumber m) :
    internalEdgeCount S ≤ internalEdgeCount (octahedron m) := by
  rw [octahedron_edge_threshold]
  exact internalEdgeCount_octahedral_bound S m hm hcard

theorem boundary_minimum_octahedron (S : Finset Site) (m : ℕ) (hm : 0 < m)
    (hcard : S.card = octahedralNumber m) :
    boundaryCount (octahedron m) ≤ boundaryCount S := by
  rw [octahedron_boundaryCount]
  exact boundaryCount_ge_octahedral S m hm hcard

/-- The sharp bound is attained at every positive octahedral size. -/
theorem octahedral_edge_maximum_attained (m : ℕ) (hm : 0 < m) :
    ∃ T : Finset Site, T.card = octahedralNumber m ∧
      internalEdgeCount T = 2 * octahedralNumber m - 2 * m ^ 2 ∧
      ∀ S : Finset Site, S.card = octahedralNumber m → internalEdgeCount S ≤ internalEdgeCount T :=
  ⟨octahedron m, octahedron_card m, octahedron_edge_threshold m,
    fun S hS => edge_maximum_octahedron S m hm hS⟩

theorem extremal_iff_boundary_minimum (S : Finset Site) (m : ℕ)
    (hcard : S.card = octahedralNumber m) :
    internalEdgeCount S = 2 * octahedralNumber m - 2 * m ^ 2 ↔
      boundaryCount S = 4 * m ^ 2 := by
  constructor
  · exact extremal_boundaryCount S m hcard
  · intro hboundary
    have hN : m ^ 2 ≤ octahedralNumber m := by unfold octahedralNumber; omega
    have h := degree_boundary_identity S
    rw [hcard, hboundary] at h
    omega

end ProteinFolding.Tetrahedral
