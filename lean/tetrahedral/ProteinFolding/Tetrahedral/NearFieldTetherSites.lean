import ProteinFolding.Tetrahedral.NearFieldTetherFamily
import ProteinFolding.Tetrahedral.RoutingSeparation

/-! The actual finite occupied set of all tether P-sites and its uniform
low-height bound, for integration with far-field obstacle avoidance. -/

namespace ProteinFolding.Tetrahedral.NearField

def tetherSites (p : ConstructionParameters) : Finset Site :=
  Finset.univ.biUnion (fun t : TetherIndex p => foldSites (tetherFold p t))

theorem mem_tetherSites (p : ConstructionParameters) (q : Site) :
    q ∈ tetherSites p ↔ ∃ t : TetherIndex p, ∃ i : Fin (tetherCount p t), (tetherFold p t).pos i = q := by
  simp [tetherSites, mem_foldSites]

theorem tetherSites_outside (p : ConstructionParameters) {q : Site} (hq : q ∈ tetherSites p) :
    q ∉ octahedron p.side := by
  obtain ⟨t, i, rfl⟩ := (mem_tetherSites p q).mp hq
  exact tetherFold_outside p t i

theorem tetherSites_mem_solid (p : ConstructionParameters) {q : Site} (hq : q ∈ tetherSites p) :
    q ∈ skinSolid p.side (2 * p.bins + 3) := by
  obtain ⟨t, i, rfl⟩ := (mem_tetherSites p q).mp hq
  exact tetherFold_mem_solid p t i

theorem tetherSites_rho_lt (p : ConstructionParameters) {q : Site} (hq : q ∈ tetherSites p) :
    FarField.rho (octRadius p.side) q < 20 * (p.side : ℤ) + 21 := by
  have hK : p.bins ≤ p.side := by have h := p.family_side_bound; omega
  have h := nearSolid_rho_lt_farFieldHeight p.side p.bins hK (tetherSites_mem_solid p hq)
  simpa only [farFieldHeight, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

end ProteinFolding.Tetrahedral.NearField
