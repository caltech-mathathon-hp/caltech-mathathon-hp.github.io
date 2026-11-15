import ProteinFolding.Tetrahedral.BulkVertexPatches

/-! A four-neighbour evaluator, proved equivalent to the actual canonical graph.
It avoids enumerating the whole solid when checking a fixed local certificate. -/

namespace ProteinFolding.Tetrahedral

def bulkFastDeleted (m : ℕ) (p : Site) : Prop :=
  InOctahedron m p ∧ ∃ k j : Fin 4, k ≠ j ∧
    ((InASublattice p.val ∧ tetraCoordinate m p.val k = octRadius m ∧
      tetraCoordinate m p.val j = -octRadius m) ∨
     (InBSublattice p.val ∧ tetraCoordinate m p.val j = -(2 * (m : ℤ) - 1) ∧
      tetraCoordinate m p.val k = 2 * (m : ℤ) - 3))

instance (m : ℕ) (p : Site) : Decidable (bulkFastDeleted m p) := by
  unfold bulkFastDeleted
  infer_instance

def bulkFastInterior (m : ℕ) (p : Site) : Prop := InOctahedron m p ∧ ¬bulkFastDeleted m p
instance (m : ℕ) (p : Site) : Decidable (bulkFastInterior m p) := by unfold bulkFastInterior; infer_instance

theorem bulkDeleted_fast_iff (m : ℕ) (p : Site) : p ∈ bulkDeletedEdges m ↔ bulkFastDeleted m p := by
  constructor
  · intro h
    have hf := Finset.mem_filter.mp h
    obtain ⟨k, j, hkj, hedge⟩ := hf.2
    refine ⟨(mem_octahedron m p).mp hf.1, k, j, hkj, ?_⟩
    rcases hedge with ⟨⟨_, hA, hk⟩, hj⟩ | ⟨⟨_, hB, hj⟩, hk⟩
    · exact Or.inl ⟨hA, hk, hj⟩
    · exact Or.inr ⟨hB, hj, hk⟩
  · rintro ⟨hinside, k, j, hkj, hedge⟩
    have hp := (mem_octahedron m p).mpr hinside
    apply Finset.mem_filter.mpr
    refine ⟨hp, k, j, hkj, ?_⟩
    rcases hedge with ⟨hA, hk, hj⟩ | ⟨hB, hj, hk⟩
    · exact Or.inl ⟨⟨hp, hA, hk⟩, hj⟩
    · exact Or.inr ⟨⟨hp, hB, hj⟩, hk⟩

theorem bulkInterior_fast_iff (m : ℕ) (p : Site) : p ∈ bulkInterior m ↔ bulkFastInterior m p := by
  simp only [bulkInterior, Finset.mem_sdiff, mem_octahedron, bulkDeleted_fast_iff, bulkFastInterior]

def bulkFastBaseDirections (m : ℕ) (p : Site) : Finset (Fin 4) :=
  Finset.univ.filter (fun d => bulkFastInterior m (step p d) ∧ bulkRho m p ≠ bulkRho m (step p d))

theorem bulkBaseNeighbours_fast_image (m : ℕ) (p : Site) :
    bulkBaseNeighbours m p = (bulkFastBaseDirections m p).image (step p) := by
  apply Finset.Subset.antisymm
  · intro q hq
    have hparts := Finset.mem_inter.mp hq
    have hrung := (bulkRungGraph_adj_iff m p q).mpr hparts.1
    obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp hrung.1
    exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (bulkInterior_fast_iff m _).mp hparts.2, hrung.2⟩, rfl⟩
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    have hdparts := (Finset.mem_filter.mp hd).2
    exact Finset.mem_inter.mpr
      ⟨(bulkRungGraph_adj_iff m p _).mp ⟨step_adj p d, hdparts.2⟩,
        (bulkInterior_fast_iff m _).mpr hdparts.1⟩

theorem bulkBaseNeighbours_fast_card (m : ℕ) (p : Site) :
    (bulkBaseNeighbours m p).card = (bulkFastBaseDirections m p).card := by
  rw [bulkBaseNeighbours_fast_image, Finset.card_image_of_injective _ (step_injective p)]

def bulkFastDanglingDirections (m : ℕ) (p : Site) : Finset (Fin 4) :=
  Finset.univ.filter (fun d => ¬InOctahedron m (step p d))

theorem bulkDanglingDirections_fast_eq (m : ℕ) (p : Site) :
    octDanglingDirections m p = bulkFastDanglingDirections m p := by
  ext d
  simp only [octDanglingDirections, bulkFastDanglingDirections, Finset.mem_filter,
    Finset.mem_univ, true_and, mem_octahedron]

def bulkFastDamaged (m : ℕ) (p : Site) : Prop :=
  bulkFastInterior m p ∧ ∃ d : Fin 4,
    bulkFastDeleted m (step p d) ∧ bulkRho m p ≠ bulkRho m (step p d)

instance (m : ℕ) (p : Site) : Decidable (bulkFastDamaged m p) := by unfold bulkFastDamaged; infer_instance

theorem bulkDamaged_fast_iff (m : ℕ) (p : Site) : p ∈ bulkDamaged m ↔ bulkFastDamaged m p := by
  constructor
  · intro h
    have hf := Finset.mem_filter.mp h
    obtain ⟨q, hq⟩ := hf.2
    have hparts := Finset.mem_inter.mp hq
    have hrung := (bulkRungGraph_adj_iff m p q).mpr hparts.1
    obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp hrung.1
    exact ⟨(bulkInterior_fast_iff m p).mp hf.1, d, (bulkDeleted_fast_iff m _).mp hparts.2, hrung.2⟩
  · rintro ⟨hp, d, hdel, hrho⟩
    apply Finset.mem_filter.mpr
    refine ⟨(bulkInterior_fast_iff m p).mpr hp, step p d, ?_⟩
    exact Finset.mem_inter.mpr
      ⟨(bulkRungGraph_adj_iff m p _).mp ⟨step_adj p d, hrho⟩, (bulkDeleted_fast_iff m _).mpr hdel⟩

def bulkFastPotential (m : ℕ) (d w : Site) : Prop :=
  bulkFastInterior m w ∧ bulkRuleNeighbour m d w ∧
    (bulkFastBaseDirections m w).card ≤ 1 ∧ 0 < (bulkFastDanglingDirections m w).card

instance (m : ℕ) (d w : Site) : Decidable (bulkFastPotential m d w) := by unfold bulkFastPotential; infer_instance

theorem bulkPotential_fast_iff (m : ℕ) (d w : Site) :
    bulkPotentialTarget m d w ↔ bulkFastPotential m d w := by
  unfold bulkPotentialTarget bulkFastPotential
  rw [bulkInterior_fast_iff, bulkBaseNeighbours_fast_card, bulkDanglingDirections_fast_eq]
  constructor
  · rintro ⟨hi, hr, _, hb, hf⟩
    exact ⟨hi, hr, hb, hf⟩
  · rintro ⟨hi, hr, hb, hf⟩
    refine ⟨hi, hr, ?_, hb, hf⟩
    intro hbase
    have hRung := (bulkRungGraph_adj_iff m d w).mpr (Finset.mem_inter.mp hbase).1
    exact hRung.2 (bulkRuleNeighbour_rho m hr).symm

def bulkFastClaimantDirections (m : ℕ) (w : Site) : Finset (Fin 4) :=
  Finset.univ.filter (fun d => bulkFastDamaged m (step w d) ∧ bulkFastPotential m (step w d) w)

set_option maxHeartbeats 1200000 in
theorem bulkClaimants_fast_card (m : ℕ) (w : Site) :
    (bulkClaimants m w).card = (bulkFastClaimantDirections m w).card := by
  rw [bulkClaimants_eq_neighbour_filter, neighbours, Finset.filter_image,
    Finset.card_image_of_injective _ (step_injective w)]
  congr 1
  ext d
  simp only [bulkFastClaimantDirections, Finset.mem_filter, Finset.mem_univ, true_and,
    bulkDamaged_fast_iff, bulkPotential_fast_iff]

def bulkFastMerge (m : ℕ) (d w : Site) : Prop :=
  bulkFastDamaged m d ∧ bulkFastPotential m d w ∧ (bulkFastClaimantDirections m w).card = 1

instance (m : ℕ) (d w : Site) : Decidable (bulkFastMerge m d w) := by unfold bulkFastMerge; infer_instance

theorem bulkMerge_fast_iff (m : ℕ) (d w : Site) : bulkMerge m d w ↔ bulkFastMerge m d w := by
  unfold bulkMerge bulkFastMerge
  rw [bulkDamaged_fast_iff, bulkPotential_fast_iff, bulkClaimants_fast_card]

def bulkFastCoverBond (m : ℕ) (p q : Site) : Prop :=
  bulkFastInterior m p ∧ bulkFastInterior m q ∧
    (bulkPatchAdded m p q ∨
      (((bulkRungGraph m).Adj p q ∨ bulkFastMerge m p q ∨ bulkFastMerge m q p) ∧ ¬bulkPatchRemoved m p q))

instance (m : ℕ) (p q : Site) : Decidable (bulkFastCoverBond m p q) := by
  unfold bulkFastCoverBond bulkPatchAdded bulkPatchRemoved bulkRungGraph
  infer_instance

set_option maxHeartbeats 1200000 in
theorem bulkCoverBond_fast_iff (m : ℕ) (p q : Site) : bulkCoverBond m p q ↔ bulkFastCoverBond m p q := by
  unfold bulkCoverBond bulkFastCoverBond bulkMergedBond
  rw [bulkInterior_fast_iff, bulkInterior_fast_iff, bulkMerge_fast_iff, bulkMerge_fast_iff]

def bulkFastCoverDirections (m : ℕ) (p : Site) : Finset (Fin 4) :=
  Finset.univ.filter (fun d => bulkFastCoverBond m p (step p d))

set_option maxHeartbeats 1200000 in
theorem bulkCoverNeighbours_fast_card (m : ℕ) (p : Site) :
    (bulkCoverNeighbours m p).card = (bulkFastCoverDirections m p).card := by
  unfold bulkCoverNeighbours neighbours
  rw [Finset.filter_image, Finset.card_image_of_injective _ (step_injective p)]
  congr 1
  ext d
  simp only [bulkFastCoverDirections, Finset.mem_filter, Finset.mem_univ, true_and]
  exact bulkCoverBond_fast_iff m p (step p d)

end ProteinFolding.Tetrahedral
