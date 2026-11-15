import ProteinFolding.Tetrahedral.BulkAcyclicity
import ProteinFolding.Tetrahedral.PathCoverMass

/-! The actual canonical bulk graph supplies disjoint paths of at least
three sites, with surface endpoints and exactly the required bulk mass. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

local instance bulkCanonicalComponentFinite (m : ℕ) : Finite (bulkFiniteGraph m).ConnectedComponent :=
  Finite.of_surjective (bulkFiniteGraph m).connectedComponentMk (fun c => c.exists_rep)
noncomputable local instance bulkCanonicalComponentFintype (m : ℕ) :
    Fintype (bulkFiniteGraph m).ConnectedComponent := Fintype.ofFinite _

theorem bulkCanonical_degree_bound (m : ℕ) (hm : 50 ≤ m) :
    ∀ p ∈ bulkInterior m, (bulkCoverNeighbours m p).card ≤ 2 :=
  fun p _ => bulkCoverNeighbours_card_le_two m (by omega) p

theorem bulkCanonical_minimum_degree (m : ℕ) (hm : 50 ≤ m) :
    ∀ p ∈ bulkInterior m, 1 ≤ (bulkCoverNeighbours m p).card :=
  fun p hp => bulkCover_minimum_degree_split m (by omega) p hp

theorem bulkCanonical_componentLength_ge_three (m : ℕ) (hm : 50 ≤ m)
    (c : (bulkFiniteGraph m).ConnectedComponent) : 3 ≤ bulkComponentLength m c := by
  apply bulkComponentLength_ge_three m (bulkCanonical_degree_bound m hm) (bulkFiniteGraph_acyclic m hm)
    (bulkCanonical_minimum_degree m hm) _ c
  intro p q hpq hp hq
  exact bulkCover_no_leaf_pair_split m (by omega) hpq hp hq

theorem bulkCanonical_component_ends_surface (m : ℕ) (hm : 50 ≤ m)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    OctSurfaceSite m (componentMaxPath (bulkFiniteGraph m) c).start.val ∧
      OctSurfaceSite m (componentMaxPath (bulkFiniteGraph m) c).finish.val := by
  have hd := bulkFinite_degree_le_two m (bulkCanonical_degree_bound m hm)
  have hmin : ∀ p : BulkVertex m, 1 ≤ (bulkFiniteGraph m).degree p := by
    intro p
    rw [bulkFinite_degree]
    exact bulkCanonical_minimum_degree m hm p.val p.property
  have hends := componentFold_end_degrees (bulkFiniteGraph m) hd (bulkFiniteGraph_acyclic m hm) hmin c
  rw [bulkFinite_degree, bulkFinite_degree] at hends
  exact ⟨bulkCover_degree_one_surface_split m (by omega) _
      (componentMaxPath (bulkFiniteGraph m) c).start.property hends.1,
    bulkCover_degree_one_surface_split m (by omega) _
      (componentMaxPath (bulkFiniteGraph m) c).finish.property hends.2⟩

theorem bulkCanonical_component_covers (m : ℕ) (hm : 50 ≤ m)
    (c : (bulkFiniteGraph m).ConnectedComponent) (p : Site) :
    (∃ i, (bulkComponentFold m c).pos i = p) ↔
      ∃ hp : p ∈ bulkInterior m, (bulkFiniteGraph m).connectedComponentMk ⟨p, hp⟩ = c :=
  bulkComponentFold_covers m (bulkCanonical_degree_bound m hm) c p

theorem bulkCanonical_component_disjoint (m : ℕ) (hm : 50 ≤ m)
    {c d : (bulkFiniteGraph m).ConnectedComponent} (hne : c ≠ d) :
    Disjoint (Set.range (bulkComponentFold m c).pos) (Set.range (bulkComponentFold m d).pos) :=
  bulkComponentFolds_disjoint m (bulkCanonical_degree_bound m hm) hne

theorem bulkCanonical_mass (m : ℕ) (hm : 50 ≤ m) :
    (∑ c : (bulkFiniteGraph m).ConnectedComponent, bulkComponentLength m c) + 24 * m =
      octahedralNumber m + 42 :=
  sum_bulkComponentLength_mass m (by omega) (bulkCanonical_degree_bound m hm)

end ProteinFolding.Tetrahedral
