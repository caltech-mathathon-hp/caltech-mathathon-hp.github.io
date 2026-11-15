import ProteinFolding.Tetrahedral.BulkEdgeRungTransfer

/-! Actual finite base-neighbour and damaged-end data in far-edge boxes. -/

namespace ProteinFolding.Tetrahedral

theorem bulkEdgeReanchor_mem_image (m M t T : ℕ) (F : OctEdgeFrame) (A : Finset Site) (p : Site) :
    bulkEdgeReanchor m M t T F p ∈ A.image (bulkEdgeReanchor m M t T F) ↔ p ∈ A := by
  constructor
  · intro hp
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hp
    have hqp := bulkEdgeReanchor_injective m M t T F heq
    rwa [← hqp]
  · intro hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem bulkEdgeReanchor_rung_inter_image (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 3 ≤ t) (htm : t + D + 4 ≤ m) (hT : D + 3 ≤ T) (hTM : T + D + 4 ≤ M)
    (hp : InBulkEdgeBox m F t D p) (A B : Finset Site)
    (hAB : ∀ q, InBulkEdgeBox m F t (D + 1) q → (bulkEdgeReanchor m M t T F q ∈ B ↔ q ∈ A)) :
    (bulkRungNeighbours m p ∩ A).image (bulkEdgeReanchor m M t T F) =
      bulkRungNeighbours M (bulkEdgeReanchor m M t T F p) ∩ B := by
  have hp1 : InBulkEdgeBox m F t (D + 1) p := bulkEdgeBox_mono m F t (by omega) hp
  apply Finset.Subset.antisymm
  · intro q' hq'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    have hqparts := Finset.mem_inter.mp hq
    have hqrung := (bulkRungGraph_adj_iff m p q).mpr hqparts.1
    have hqbox := bulk_adjacent_in_edge_box m F t D hp hqrung.1
    apply Finset.mem_inter.mpr
    refine ⟨?_, (hAB q hqbox).mpr hqparts.2⟩
    apply (bulkRungGraph_adj_iff M _ _).mp
    exact (bulkEdgeReanchor_rung_iff m M t T F (D + 1) p q
      (by omega) (by omega) (by omega) (by omega) hp1 hqbox).mpr hqrung
  · intro q' hq'
    have hqparts := Finset.mem_inter.mp hq'
    have hqrung := (bulkRungGraph_adj_iff M _ q').mpr hqparts.1
    have hp' := bulkEdgeReanchor_in_box m M t T F D p hp
    have hqbox' := bulk_adjacent_in_edge_box M F T D hp' hqrung.1
    let q := bulkEdgeReanchor M m T t F q'
    have hqbox : InBulkEdgeBox m F t (D + 1) q := bulkEdgeReanchor_in_box M m T t F (D + 1) q' hqbox'
    have hqeq : bulkEdgeReanchor m M t T F q = q' := bulkEdgeReanchor_inverse M m T t F q'
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_inter.mpr ⟨?_, ?_⟩, hqeq⟩
    · apply (bulkRungGraph_adj_iff m p q).mp
      apply (bulkEdgeReanchor_rung_iff m M t T F (D + 1) p q
        (by omega) (by omega) (by omega) (by omega) hp1 hqbox).mp
      rwa [hqeq]
    · apply (hAB q hqbox).mp
      rw [hqeq]
      exact hqparts.2

theorem bulkEdgeReanchor_base_image (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 3 ≤ t) (htm : t + D + 4 ≤ m) (hT : D + 3 ≤ T) (hTM : T + D + 4 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    (bulkBaseNeighbours m p).image (bulkEdgeReanchor m M t T F) =
      bulkBaseNeighbours M (bulkEdgeReanchor m M t T F p) := by
  apply bulkEdgeReanchor_rung_inter_image m M t T F D p ht htm hT hTM hp
  intro q hq
  exact bulkEdgeReanchor_interior_iff m M t T F (D + 1) q
    (by omega) (by omega) (by omega) (by omega) hq

theorem bulkEdgeReanchor_base_card (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 3 ≤ t) (htm : t + D + 4 ≤ m) (hT : D + 3 ≤ T) (hTM : T + D + 4 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    (bulkBaseNeighbours M (bulkEdgeReanchor m M t T F p)).card = (bulkBaseNeighbours m p).card := by
  rw [← bulkEdgeReanchor_base_image m M t T F D p ht htm hT hTM hp,
    Finset.card_image_of_injective _ (bulkEdgeReanchor_injective m M t T F)]

theorem bulkEdgeReanchor_mem_base_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p q : Site)
    (ht : D + 3 ≤ t) (htm : t + D + 4 ≤ m) (hT : D + 3 ≤ T) (hTM : T + D + 4 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    bulkEdgeReanchor m M t T F q ∈ bulkBaseNeighbours M (bulkEdgeReanchor m M t T F p) ↔
      q ∈ bulkBaseNeighbours m p := by
  rw [← bulkEdgeReanchor_base_image m M t T F D p ht htm hT hTM hp, bulkEdgeReanchor_mem_image]

theorem bulkEdgeReanchor_damaged_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 3 ≤ t) (htm : t + D + 4 ≤ m) (hT : D + 3 ≤ T) (hTM : T + D + 4 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    bulkEdgeReanchor m M t T F p ∈ bulkDamaged M ↔ p ∈ bulkDamaged m := by
  have himage := bulkEdgeReanchor_rung_inter_image m M t T F D p ht htm hT hTM hp
    (bulkDeletedEdges m) (bulkDeletedEdges M)
    (fun q hq => bulkEdgeReanchor_deleted_iff m M t T F (D + 1) q
      (by omega) (by omega) (by omega) (by omega) hq)
  have hnonempty : (bulkRungNeighbours M (bulkEdgeReanchor m M t T F p) ∩ bulkDeletedEdges M).Nonempty ↔
      (bulkRungNeighbours m p ∩ bulkDeletedEdges m).Nonempty := by
    rw [← himage]
    exact Finset.image_nonempty
  simp only [bulkDamaged, Finset.mem_filter, hnonempty,
    bulkEdgeReanchor_interior_iff m M t T F D p (by omega) (by omega) (by omega) (by omega) hp]

theorem bulkEdgeReanchor_potential_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (d w : Site)
    (ht : D + 3 ≤ t) (htm : t + D + 4 ≤ m) (hT : D + 3 ≤ T) (hTM : T + D + 4 ≤ M)
    (hd : InBulkEdgeBox m F t D d) (hw : InBulkEdgeBox m F t D w) :
    bulkPotentialTarget M (bulkEdgeReanchor m M t T F d) (bulkEdgeReanchor m M t T F w) ↔
      bulkPotentialTarget m d w := by
  unfold bulkPotentialTarget
  rw [bulkEdgeReanchor_interior_iff m M t T F D w (by omega) (by omega) (by omega) (by omega) hw,
    bulkEdgeReanchor_rule_iff m M t T F D d w (by omega) (by omega) (by omega) (by omega) hd,
    bulkEdgeReanchor_mem_base_iff m M t T F D d w ht htm hT hTM hd,
    bulkEdgeReanchor_base_card m M t T F D w ht htm hT hTM hw,
    bulkEdgeReanchor_danglingDirections_eq m M t T F D w ht htm hT hTM hw]

end ProteinFolding.Tetrahedral
