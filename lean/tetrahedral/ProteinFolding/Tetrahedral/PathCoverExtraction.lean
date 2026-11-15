import ProteinFolding.Tetrahedral.BulkCoverConstruction
import ProteinFolding.Tetrahedral.FinitePathMinimum

/-! Restrict the actual canonical cover graph to its finite bulk vertex set
and lift component paths back to physical sites. The outstanding degree and
acyclicity properties remain explicit inputs to the general extraction. -/

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 2000000

open SimpleGraph
open scoped BigOperators

abbrev BulkVertex (m : ℕ) := {p : Site // p ∈ bulkInterior m}

def bulkFiniteGraph (m : ℕ) : SimpleGraph (BulkVertex m) :=
  (bulkCoverGraph m).induce {p | p ∈ bulkInterior m}

instance (m : ℕ) : DecidableRel (bulkFiniteGraph m).Adj := fun p q =>
  inferInstanceAs (Decidable ((bulkCoverGraph m).Adj p.val q.val))

@[simp] theorem bulkFiniteGraph_adj (m : ℕ) (p q : BulkVertex m) :
    (bulkFiniteGraph m).Adj p q ↔ (bulkCoverGraph m).Adj p.val q.val := Iff.rfl

theorem bulkFinite_neighbours_image (m : ℕ) (p : BulkVertex m) :
    ((bulkFiniteGraph m).neighborFinset p).image Subtype.val = bulkCoverNeighbours m p.val := by
  ext q
  simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, bulkFiniteGraph_adj,
    mem_bulkCoverNeighbours]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact hr
  · intro hadj
    exact ⟨⟨q, (bulkCoverGraph_support m hadj).2⟩, hadj, rfl⟩

theorem bulkFinite_degree (m : ℕ) (p : BulkVertex m) :
    (bulkFiniteGraph m).degree p = (bulkCoverNeighbours m p.val).card := by
  have h := congrArg Finset.card (bulkFinite_neighbours_image m p)
  rw [Finset.card_image_of_injective _ Subtype.val_injective,
    SimpleGraph.card_neighborFinset_eq_degree] at h
  exact h

theorem bulkFinite_degree_le_two (m : ℕ)
    (hdegree : ∀ p ∈ bulkInterior m, (bulkCoverNeighbours m p).card ≤ 2) :
    ∀ p : BulkVertex m, (bulkFiniteGraph m).degree p ≤ 2 := by
  intro p
  rw [bulkFinite_degree]
  exact hdegree p.val p.property

def bulkLiftFold (m n : ℕ) (f : Fold (bulkFiniteGraph m) n) : Fold tetrahedralLattice n where
  pos i := (f.pos i).val
  injective_pos := by
    intro i j hij
    exact f.injective_pos (Subtype.ext hij)
  consecutive i j hij := bulkCoverBond_adj m (f.consecutive i j hij)

noncomputable def bulkComponentLength (m : ℕ) (c : (bulkFiniteGraph m).ConnectedComponent) : ℕ :=
  (componentMaxPath (bulkFiniteGraph m) c).walk.length + 1

noncomputable def bulkComponentFold (m : ℕ) (c : (bulkFiniteGraph m).ConnectedComponent) :
    Fold tetrahedralLattice (bulkComponentLength m c) :=
  bulkLiftFold m _ (componentFold (bulkFiniteGraph m) c)

theorem bulkComponentFold_inside (m : ℕ) (c : (bulkFiniteGraph m).ConnectedComponent)
    (i : Fin (bulkComponentLength m c)) :
    (bulkComponentFold m c).pos i ∈ bulkInterior m :=
  ((componentFold (bulkFiniteGraph m) c).pos i).property

theorem bulkComponentFold_covers (m : ℕ)
    (hdegree : ∀ p ∈ bulkInterior m, (bulkCoverNeighbours m p).card ≤ 2)
    (c : (bulkFiniteGraph m).ConnectedComponent) (p : Site) :
    (∃ i, (bulkComponentFold m c).pos i = p) ↔
      ∃ hp : p ∈ bulkInterior m, (bulkFiniteGraph m).connectedComponentMk ⟨p, hp⟩ = c := by
  have hd := bulkFinite_degree_le_two m hdegree
  constructor
  · rintro ⟨i, hi⟩
    have hp : p ∈ bulkInterior m := hi ▸ bulkComponentFold_inside m c i
    refine ⟨hp, ?_⟩
    apply (componentFold_covers (bulkFiniteGraph m) hd c ⟨p, hp⟩).mp
    exact ⟨i, Subtype.ext hi⟩
  · rintro ⟨hp, hpc⟩
    obtain ⟨i, hi⟩ := (componentFold_covers (bulkFiniteGraph m) hd c ⟨p, hp⟩).mpr hpc
    exact ⟨i, congrArg Subtype.val hi⟩

theorem bulkComponentFolds_disjoint (m : ℕ)
    (hdegree : ∀ p ∈ bulkInterior m, (bulkCoverNeighbours m p).card ≤ 2)
    {c d : (bulkFiniteGraph m).ConnectedComponent} (hne : c ≠ d) :
    Disjoint (Set.range (bulkComponentFold m c).pos) (Set.range (bulkComponentFold m d).pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨i, hi⟩ ⟨j, hj⟩
  obtain ⟨hp, hc⟩ := (bulkComponentFold_covers m hdegree c p).mp ⟨i, hi⟩
  obtain ⟨hp', hd⟩ := (bulkComponentFold_covers m hdegree d p).mp ⟨j, hj⟩
  exact hne (hc.symm.trans hd)

local instance (m : ℕ) : Finite (bulkFiniteGraph m).ConnectedComponent :=
  Finite.of_surjective (bulkFiniteGraph m).connectedComponentMk (fun c => c.exists_rep)

noncomputable local instance (m : ℕ) : Fintype (bulkFiniteGraph m).ConnectedComponent := Fintype.ofFinite _

theorem sum_bulkComponentLength (m : ℕ)
    (hdegree : ∀ p ∈ bulkInterior m, (bulkCoverNeighbours m p).card ≤ 2) :
    (∑ c : (bulkFiniteGraph m).ConnectedComponent, bulkComponentLength m c) = (bulkInterior m).card := by
  have h := sum_componentPath_vertex_count (bulkFiniteGraph m) (bulkFinite_degree_le_two m hdegree)
  simpa only [bulkComponentLength, Fintype.card_coe] using h

theorem bulkComponentLength_ge_three (m : ℕ)
    (hdegree : ∀ p ∈ bulkInterior m, (bulkCoverNeighbours m p).card ≤ 2)
    (hacyclic : (bulkFiniteGraph m).IsAcyclic)
    (hnonzero : ∀ p ∈ bulkInterior m, 1 ≤ (bulkCoverNeighbours m p).card)
    (hnoPair : ∀ p q, (bulkFiniteGraph m).Adj p q →
      (bulkCoverNeighbours m p.val).card = 1 → (bulkCoverNeighbours m q.val).card ≠ 1)
    (c : (bulkFiniteGraph m).ConnectedComponent) : 3 ≤ bulkComponentLength m c := by
  apply componentPath_vertex_count_ge_three (bulkFiniteGraph m)
    (bulkFinite_degree_le_two m hdegree) hacyclic
  · intro p
    rw [bulkFinite_degree]
    exact hnonzero p.val p.property
  · intro p q hpq hp hq
    rw [bulkFinite_degree] at hp hq
    exact hnoPair p q hpq hp hq

end ProteinFolding.Tetrahedral
