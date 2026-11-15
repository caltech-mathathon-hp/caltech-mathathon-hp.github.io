import ProteinFolding.Tetrahedral.BulkVertexSigns

/-! Local finite neighbour and merge data commute with vertex reanchoring. -/

namespace ProteinFolding.Tetrahedral

theorem bulkReanchorSite_inverse (m n : ℕ) (v : Fin 6) (p : Site) :
    bulkReanchorSite n m v (bulkReanchorSite m n v p) = p := by
  apply Subtype.ext
  funext k
  rw [bulkReanchorSite_coordinates, bulkReanchorSite_coordinates]
  omega

theorem bulkVertexBox_mono (m : ℕ) (v : Fin 6) {D E : ℕ} (hDE : D ≤ E) {p : Site}
    (hp : InBulkVertexBox m v D p) : InBulkVertexBox m v E p := by
  intro k
  have h := hp k
  omega

theorem bulkReanchor_mem_image (m n : ℕ) (v : Fin 6) (A : Finset Site) (p : Site) :
    bulkReanchorSite m n v p ∈ A.image (bulkReanchorSite m n v) ↔ p ∈ A := by
  constructor
  · intro hp
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hp
    have hqp := bulkReanchorSite_injective m n v heq
    rwa [← hqp]
  · intro hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem bulkReanchor_rung_inter_image (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 3 ≤ m) (hn : D + 3 ≤ n) (hp : InBulkVertexBox m v D p)
    (A B : Finset Site)
    (hAB : ∀ q, InBulkVertexBox m v (D + 1) q →
      (bulkReanchorSite m n v q ∈ B ↔ q ∈ A)) :
    (bulkRungNeighbours m p ∩ A).image (bulkReanchorSite m n v) =
      bulkRungNeighbours n (bulkReanchorSite m n v p) ∩ B := by
  have hp1 : InBulkVertexBox m v (D + 1) p := bulkVertexBox_mono m v (by omega) hp
  apply Finset.Subset.antisymm
  · intro q' hq'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    have hqparts := Finset.mem_inter.mp hq
    have hqrung := (bulkRungGraph_adj_iff m p q).mpr hqparts.1
    have hqbox := bulk_adjacent_in_vertex_box m v D hp hqrung.1
    apply Finset.mem_inter.mpr
    refine ⟨?_, (hAB q hqbox).mpr hqparts.2⟩
    apply (bulkRungGraph_adj_iff n _ _).mp
    exact (bulkReanchor_rung_iff m n v (D + 1) p q (by omega) (by omega) hp1 hqbox).mpr hqrung
  · intro q' hq'
    have hqparts := Finset.mem_inter.mp hq'
    have hqrung := (bulkRungGraph_adj_iff n _ q').mpr hqparts.1
    have hp' := bulkReanchorSite_in_box m n v D p hp
    have hqbox' := bulk_adjacent_in_vertex_box n v D hp' hqrung.1
    let q := bulkReanchorSite n m v q'
    have hqbox : InBulkVertexBox m v (D + 1) q := bulkReanchorSite_in_box n m v (D + 1) q' hqbox'
    have hqeq : bulkReanchorSite m n v q = q' := bulkReanchorSite_inverse n m v q'
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_inter.mpr ⟨?_, ?_⟩, hqeq⟩
    · apply (bulkRungGraph_adj_iff m p q).mp
      apply (bulkReanchor_rung_iff m n v (D + 1) p q (by omega) (by omega) hp1 hqbox).mp
      rwa [hqeq]
    · apply (hAB q hqbox).mp
      rw [hqeq]
      exact hqparts.2

theorem bulkReanchor_base_image (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 3 ≤ m) (hn : D + 3 ≤ n) (hp : InBulkVertexBox m v D p) :
    (bulkBaseNeighbours m p).image (bulkReanchorSite m n v) =
      bulkBaseNeighbours n (bulkReanchorSite m n v p) := by
  apply bulkReanchor_rung_inter_image m n v D p hm hn hp
  intro q hq
  exact bulkReanchor_interior_iff m n v (D + 1) q (by omega) (by omega) hq

theorem bulkReanchor_base_card (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 3 ≤ m) (hn : D + 3 ≤ n) (hp : InBulkVertexBox m v D p) :
    (bulkBaseNeighbours n (bulkReanchorSite m n v p)).card = (bulkBaseNeighbours m p).card := by
  rw [← bulkReanchor_base_image m n v D p hm hn hp,
    Finset.card_image_of_injective _ (bulkReanchorSite_injective m n v)]

theorem bulkReanchor_mem_base_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p q : Site)
    (hm : D + 3 ≤ m) (hn : D + 3 ≤ n) (hp : InBulkVertexBox m v D p) :
    bulkReanchorSite m n v q ∈ bulkBaseNeighbours n (bulkReanchorSite m n v p) ↔
      q ∈ bulkBaseNeighbours m p := by
  rw [← bulkReanchor_base_image m n v D p hm hn hp, bulkReanchor_mem_image]

theorem bulkReanchor_damaged_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 3 ≤ m) (hn : D + 3 ≤ n) (hp : InBulkVertexBox m v D p) :
    bulkReanchorSite m n v p ∈ bulkDamaged n ↔ p ∈ bulkDamaged m := by
  have himage := bulkReanchor_rung_inter_image m n v D p hm hn hp
    (bulkDeletedEdges m) (bulkDeletedEdges n)
    (fun q hq => bulkReanchor_deleted_iff m n v (D + 1) q (by omega) (by omega) hq)
  have hnonempty : (bulkRungNeighbours n (bulkReanchorSite m n v p) ∩ bulkDeletedEdges n).Nonempty ↔
      (bulkRungNeighbours m p ∩ bulkDeletedEdges m).Nonempty := by
    rw [← himage]
    exact Finset.image_nonempty
  simp only [bulkDamaged, Finset.mem_filter, hnonempty,
    bulkReanchor_interior_iff m n v D p (by omega) (by omega) hp]

theorem bulkReanchor_potential_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (d w : Site)
    (hm : D + 3 ≤ m) (hn : D + 3 ≤ n)
    (hd : InBulkVertexBox m v D d) (hw : InBulkVertexBox m v D w) :
    bulkPotentialTarget n (bulkReanchorSite m n v d) (bulkReanchorSite m n v w) ↔
      bulkPotentialTarget m d w := by
  unfold bulkPotentialTarget
  rw [bulkReanchor_interior_iff m n v D w (by omega) (by omega) hw,
    bulkReanchor_rule_iff m n v D d w (by omega) (by omega) hd,
    bulkReanchor_mem_base_iff m n v D d w hm hn hd,
    bulkReanchor_base_card m n v D w hm hn hw,
    bulkReanchor_danglingDirections_eq m n v D w hm hn hw]

set_option maxHeartbeats 1200000 in
theorem bulkReanchor_claimants_image (m n : ℕ) (v : Fin 6) (D : ℕ) (w : Site)
    (hm : D + 4 ≤ m) (hn : D + 4 ≤ n) (hw : InBulkVertexBox m v D w) :
    (bulkClaimants m w).image (bulkReanchorSite m n v) =
      bulkClaimants n (bulkReanchorSite m n v w) := by
  have hw1 : InBulkVertexBox m v (D + 1) w := bulkVertexBox_mono m v (by omega) hw
  apply Finset.Subset.antisymm
  · intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    have hdparts := Finset.mem_filter.mp hd
    have hdAdj : tetrahedralLattice.Adj d w := hdparts.2.2.1.1
    have hdbox := bulk_adjacent_in_vertex_box m v D hw hdAdj.symm
    apply Finset.mem_filter.mpr
    exact ⟨(bulkReanchor_damaged_iff m n v (D + 1) d (by omega) (by omega) hdbox).mpr hdparts.1,
      (bulkReanchor_potential_iff m n v (D + 1) d w (by omega) (by omega) hdbox hw1).mpr hdparts.2⟩
  · intro d' hd'
    have hdparts := Finset.mem_filter.mp hd'
    have hdAdj : tetrahedralLattice.Adj d' (bulkReanchorSite m n v w) := hdparts.2.2.1.1
    have hw' := bulkReanchorSite_in_box m n v D w hw
    have hdbox' := bulk_adjacent_in_vertex_box n v D hw' hdAdj.symm
    let d := bulkReanchorSite n m v d'
    have hdbox : InBulkVertexBox m v (D + 1) d := bulkReanchorSite_in_box n m v (D + 1) d' hdbox'
    have hdeq : bulkReanchorSite m n v d = d' := bulkReanchorSite_inverse n m v d'
    apply Finset.mem_image.mpr
    refine ⟨d, Finset.mem_filter.mpr ⟨?_, ?_⟩, hdeq⟩
    · apply (bulkReanchor_damaged_iff m n v (D + 1) d (by omega) (by omega) hdbox).mp
      rw [hdeq]
      exact hdparts.1
    · apply (bulkReanchor_potential_iff m n v (D + 1) d w (by omega) (by omega) hdbox hw1).mp
      rw [hdeq]
      exact hdparts.2

theorem bulkReanchor_claimants_card (m n : ℕ) (v : Fin 6) (D : ℕ) (w : Site)
    (hm : D + 4 ≤ m) (hn : D + 4 ≤ n) (hw : InBulkVertexBox m v D w) :
    (bulkClaimants n (bulkReanchorSite m n v w)).card = (bulkClaimants m w).card := by
  rw [← bulkReanchor_claimants_image m n v D w hm hn hw,
    Finset.card_image_of_injective _ (bulkReanchorSite_injective m n v)]

theorem bulkReanchor_merge_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (d w : Site)
    (hm : D + 4 ≤ m) (hn : D + 4 ≤ n)
    (hd : InBulkVertexBox m v D d) (hw : InBulkVertexBox m v D w) :
    bulkMerge n (bulkReanchorSite m n v d) (bulkReanchorSite m n v w) ↔ bulkMerge m d w := by
  unfold bulkMerge
  rw [bulkReanchor_damaged_iff m n v D d (by omega) (by omega) hd,
    bulkReanchor_potential_iff m n v D d w (by omega) (by omega) hd hw,
    bulkReanchor_claimants_card m n v D w hm hn hw]

theorem bulkReanchor_mergedBond_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p q : Site)
    (hm : D + 4 ≤ m) (hn : D + 4 ≤ n)
    (hp : InBulkVertexBox m v D p) (hq : InBulkVertexBox m v D q) :
    bulkMergedBond n (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) ↔ bulkMergedBond m p q := by
  unfold bulkMergedBond
  rw [bulkReanchor_rung_iff m n v D p q (by omega) (by omega) hp hq,
    bulkReanchor_merge_iff m n v D p q hm hn hp hq,
    bulkReanchor_merge_iff m n v D q p hm hn hq hp]

theorem bulkReanchor_neighbours_image (m n : ℕ) (v : Fin 6) (p : Site) :
    (neighbours p).image (bulkReanchorSite m n v) = neighbours (bulkReanchorSite m n v p) := by
  unfold neighbours
  rw [Finset.image_image]
  congr 1
  funext d
  exact bulkReanchorSite_step m n v p d

theorem bulkReanchor_filtered_neighbours_image (m n : ℕ) (v : Fin 6) (p : Site)
    (P Q : Site → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ q ∈ neighbours p, Q (bulkReanchorSite m n v q) ↔ P q) :
    ((neighbours p).filter P).image (bulkReanchorSite m n v) =
      (neighbours (bulkReanchorSite m n v p)).filter Q := by
  rw [← bulkReanchor_neighbours_image, Finset.filter_image]
  apply congrArg (fun A : Finset Site => A.image (bulkReanchorSite m n v))
  apply Finset.filter_congr
  intro q hq
  exact (hPQ q hq).symm

theorem bulkMergedNeighbours_eq_filter (m : ℕ) (p : Site) :
    bulkMergedNeighbours m p = (neighbours p).filter
      (fun q => q ∈ bulkInterior m ∧ bulkMergedBond m p q) := by
  ext q
  rw [mem_bulkMergedNeighbours]
  simp only [Finset.mem_filter, mem_neighbours]
  constructor
  · intro h
    exact ⟨bulkMergedBond_adj m h.2, h⟩
  · exact fun h => h.2

theorem bulkReanchor_mergedNeighbours_image (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 5 ≤ m) (hn : D + 5 ≤ n) (hp : InBulkVertexBox m v D p) :
    (bulkMergedNeighbours m p).image (bulkReanchorSite m n v) =
      bulkMergedNeighbours n (bulkReanchorSite m n v p) := by
  rw [bulkMergedNeighbours_eq_filter, bulkMergedNeighbours_eq_filter]
  apply bulkReanchor_filtered_neighbours_image
  intro q hq
  have hqbox := bulk_adjacent_in_vertex_box m v D hp ((mem_neighbours p q).mp hq)
  have hpbox : InBulkVertexBox m v (D + 1) p := bulkVertexBox_mono m v (by omega) hp
  exact and_congr (bulkReanchor_interior_iff m n v (D + 1) q (by omega) (by omega) hqbox)
    (bulkReanchor_mergedBond_iff m n v (D + 1) p q (by omega) (by omega) hpbox hqbox)

theorem bulkReanchor_mergedNeighbours_card (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 5 ≤ m) (hn : D + 5 ≤ n) (hp : InBulkVertexBox m v D p) :
    (bulkMergedNeighbours n (bulkReanchorSite m n v p)).card = (bulkMergedNeighbours m p).card := by
  rw [← bulkReanchor_mergedNeighbours_image m n v D p hm hn hp,
    Finset.card_image_of_injective _ (bulkReanchorSite_injective m n v)]

end ProteinFolding.Tetrahedral
