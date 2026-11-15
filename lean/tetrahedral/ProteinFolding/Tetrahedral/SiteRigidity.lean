import ProteinFolding.Tetrahedral.SiteRigidityContainment
import ProteinFolding.Tetrahedral.LayerRigidityRectangleNormalization
import ProteinFolding.Tetrahedral.IntegerIsoperimetry

/-! Every site set attaining the octahedral contact bound is an octahedron,
up to the lattice translation or sublattice reflection used by normalizeSite. -/

namespace ProteinFolding.Tetrahedral

theorem site_extremal_normalizes_to_octahedron (S : Finset Site) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m)
    (hRuns : totalRuns S = 2 * m ^ 2) :
    ∃ c ∈ S, S.image (normalizeSite c) = octahedron m := by
  have hN := octahedralNumber_pos m hm
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨center, hactive, hleft, hright, hcentralcard, hleftstep, hrightstep⟩ :=
    site_extremal_signed_imbalances S hne m hm hcard hRuns
  obtain ⟨c, hc, hcentral⟩ := tight_square_layer_normalizes_all S center m hm
    hleft hright hcentralcard
  refine ⟨c, (Finset.mem_filter.mp hc).1, ?_⟩
  apply site_image_eq_octahedron_of_signed_imbalances S (normalizeSite c)
    (normalizeSite_injective c) (fun p q hpq => (adj_normalizeSite_iff c p q).mpr hpq)
    m center hcard ?_ hleftstep hrightstep
  intro p hp
  have him : normalizeSite c p ∈ (finiteLayer S center).image (normalizeSite c) :=
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  rw [hcentral] at him
  exact (Finset.mem_filter.mp him).1

/-- The equality classification in Theorem 5 for internal contacts. -/
theorem contact_maximizer_normalizes_to_octahedron (S : Finset Site) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m)
    (hedges : internalEdgeCount S = 2 * octahedralNumber m - 2 * m ^ 2) :
    ∃ c ∈ S, S.image (normalizeSite c) = octahedron m :=
  site_extremal_normalizes_to_octahedron S m hm hcard (extremal_totalRuns S m hcard hedges)

theorem boundary_minimizer_normalizes_to_octahedron (S : Finset Site) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m)
    (hboundary : boundaryCount S = 4 * m ^ 2) :
    ∃ c ∈ S, S.image (normalizeSite c) = octahedron m := by
  apply site_extremal_normalizes_to_octahedron S m hm hcard
  have h := boundaryCount_eq_twice_totalRuns S
  omega

end ProteinFolding.Tetrahedral
