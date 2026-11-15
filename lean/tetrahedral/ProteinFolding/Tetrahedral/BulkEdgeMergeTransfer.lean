import ProteinFolding.Tetrahedral.BulkEdgeNeighbourTransfer
import ProteinFolding.Tetrahedral.BulkEdgePatchFree

/-! The actual simultaneous merge graph and final cover transfer along far edges. -/

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 1200000 in
theorem bulkEdgeReanchor_claimants_image (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (w : Site)
    (ht : D + 4 ≤ t) (htm : t + D + 5 ≤ m) (hT : D + 4 ≤ T) (hTM : T + D + 5 ≤ M)
    (hw : InBulkEdgeBox m F t D w) :
    (bulkClaimants m w).image (bulkEdgeReanchor m M t T F) =
      bulkClaimants M (bulkEdgeReanchor m M t T F w) := by
  have hw1 : InBulkEdgeBox m F t (D + 1) w := bulkEdgeBox_mono m F t (by omega) hw
  apply Finset.Subset.antisymm
  · intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    have hdparts := Finset.mem_filter.mp hd
    have hdAdj : tetrahedralLattice.Adj d w := hdparts.2.2.1.1
    have hdbox := bulk_adjacent_in_edge_box m F t D hw hdAdj.symm
    apply Finset.mem_filter.mpr
    exact ⟨(bulkEdgeReanchor_damaged_iff m M t T F (D + 1) d
        (by omega) (by omega) (by omega) (by omega) hdbox).mpr hdparts.1,
      (bulkEdgeReanchor_potential_iff m M t T F (D + 1) d w
        (by omega) (by omega) (by omega) (by omega) hdbox hw1).mpr hdparts.2⟩
  · intro d' hd'
    have hdparts := Finset.mem_filter.mp hd'
    have hdAdj : tetrahedralLattice.Adj d' (bulkEdgeReanchor m M t T F w) := hdparts.2.2.1.1
    have hw' := bulkEdgeReanchor_in_box m M t T F D w hw
    have hdbox' := bulk_adjacent_in_edge_box M F T D hw' hdAdj.symm
    let d := bulkEdgeReanchor M m T t F d'
    have hdbox : InBulkEdgeBox m F t (D + 1) d := bulkEdgeReanchor_in_box M m T t F (D + 1) d' hdbox'
    have hdeq : bulkEdgeReanchor m M t T F d = d' := bulkEdgeReanchor_inverse M m T t F d'
    apply Finset.mem_image.mpr
    refine ⟨d, Finset.mem_filter.mpr ⟨?_, ?_⟩, hdeq⟩
    · apply (bulkEdgeReanchor_damaged_iff m M t T F (D + 1) d
        (by omega) (by omega) (by omega) (by omega) hdbox).mp
      rw [hdeq]
      exact hdparts.1
    · apply (bulkEdgeReanchor_potential_iff m M t T F (D + 1) d w
        (by omega) (by omega) (by omega) (by omega) hdbox hw1).mp
      rw [hdeq]
      exact hdparts.2

theorem bulkEdgeReanchor_claimants_card (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (w : Site)
    (ht : D + 4 ≤ t) (htm : t + D + 5 ≤ m) (hT : D + 4 ≤ T) (hTM : T + D + 5 ≤ M)
    (hw : InBulkEdgeBox m F t D w) :
    (bulkClaimants M (bulkEdgeReanchor m M t T F w)).card = (bulkClaimants m w).card := by
  rw [← bulkEdgeReanchor_claimants_image m M t T F D w ht htm hT hTM hw,
    Finset.card_image_of_injective _ (bulkEdgeReanchor_injective m M t T F)]

theorem bulkEdgeReanchor_merge_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (d w : Site)
    (ht : D + 4 ≤ t) (htm : t + D + 5 ≤ m) (hT : D + 4 ≤ T) (hTM : T + D + 5 ≤ M)
    (hd : InBulkEdgeBox m F t D d) (hw : InBulkEdgeBox m F t D w) :
    bulkMerge M (bulkEdgeReanchor m M t T F d) (bulkEdgeReanchor m M t T F w) ↔ bulkMerge m d w := by
  unfold bulkMerge
  rw [bulkEdgeReanchor_damaged_iff m M t T F D d (by omega) (by omega) (by omega) (by omega) hd,
    bulkEdgeReanchor_potential_iff m M t T F D d w (by omega) (by omega) (by omega) (by omega) hd hw,
    bulkEdgeReanchor_claimants_card m M t T F D w ht htm hT hTM hw]

theorem bulkEdgeReanchor_mergedBond_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p q : Site)
    (ht : D + 4 ≤ t) (htm : t + D + 5 ≤ m) (hT : D + 4 ≤ T) (hTM : T + D + 5 ≤ M)
    (hp : InBulkEdgeBox m F t D p) (hq : InBulkEdgeBox m F t D q) :
    bulkMergedBond M (bulkEdgeReanchor m M t T F p) (bulkEdgeReanchor m M t T F q) ↔ bulkMergedBond m p q := by
  unfold bulkMergedBond
  rw [bulkEdgeReanchor_rung_iff m M t T F D p q (by omega) (by omega) (by omega) (by omega) hp hq,
    bulkEdgeReanchor_merge_iff m M t T F D p q ht htm hT hTM hp hq,
    bulkEdgeReanchor_merge_iff m M t T F D q p ht htm hT hTM hq hp]

theorem bulkEdgeReanchor_neighbours_image (m M t T : ℕ) (F : OctEdgeFrame) (p : Site) :
    (neighbours p).image (bulkEdgeReanchor m M t T F) = neighbours (bulkEdgeReanchor m M t T F p) := by
  unfold neighbours
  rw [Finset.image_image]
  congr 1
  funext d
  exact bulkEdgeReanchor_step m M t T F p d

theorem bulkEdgeReanchor_filtered_neighbours_image (m M t T : ℕ) (F : OctEdgeFrame) (p : Site)
    (P Q : Site → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ q ∈ neighbours p, Q (bulkEdgeReanchor m M t T F q) ↔ P q) :
    ((neighbours p).filter P).image (bulkEdgeReanchor m M t T F) =
      (neighbours (bulkEdgeReanchor m M t T F p)).filter Q := by
  rw [← bulkEdgeReanchor_neighbours_image, Finset.filter_image]
  apply congrArg (fun A : Finset Site => A.image (bulkEdgeReanchor m M t T F))
  apply Finset.filter_congr
  intro q hq
  exact (hPQ q hq).symm

theorem bulkEdgeReanchor_mergedNeighbours_image (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 5 ≤ t) (htm : t + D + 6 ≤ m) (hT : D + 5 ≤ T) (hTM : T + D + 6 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    (bulkMergedNeighbours m p).image (bulkEdgeReanchor m M t T F) =
      bulkMergedNeighbours M (bulkEdgeReanchor m M t T F p) := by
  rw [bulkMergedNeighbours_eq_filter, bulkMergedNeighbours_eq_filter]
  apply bulkEdgeReanchor_filtered_neighbours_image
  intro q hq
  have hqbox := bulk_adjacent_in_edge_box m F t D hp ((mem_neighbours p q).mp hq)
  have hpbox : InBulkEdgeBox m F t (D + 1) p := bulkEdgeBox_mono m F t (by omega) hp
  exact and_congr (bulkEdgeReanchor_interior_iff m M t T F (D + 1) q
      (by omega) (by omega) (by omega) (by omega) hqbox)
    (bulkEdgeReanchor_mergedBond_iff m M t T F (D + 1) p q
      (by omega) (by omega) (by omega) (by omega) hpbox hqbox)

theorem bulkEdgeReanchor_mergedNeighbours_card (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 5 ≤ t) (htm : t + D + 6 ≤ m) (hT : D + 5 ≤ T) (hTM : T + D + 6 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    (bulkMergedNeighbours M (bulkEdgeReanchor m M t T F p)).card = (bulkMergedNeighbours m p).card := by
  rw [← bulkEdgeReanchor_mergedNeighbours_image m M t T F D p ht htm hT hTM hp,
    Finset.card_image_of_injective _ (bulkEdgeReanchor_injective m M t T F)]

theorem bulkCoverNeighbours_empty_of_not_interior (m : ℕ) (p : Site) (hp : p ∉ bulkInterior m) :
    bulkCoverNeighbours m p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  exact hp (bulkCoverGraph_support m ((mem_bulkCoverNeighbours m p q).mp hq)).1

theorem bulkEdgeReanchor_coverNeighbours_card (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hT : D + 8 ≤ T) (hTM : T + D + 9 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    (bulkCoverNeighbours M (bulkEdgeReanchor m M t T F p)).card = (bulkCoverNeighbours m p).card := by
  have hp' := bulkEdgeReanchor_in_box m M t T F D p hp
  have hnotOld := bulkFarEdgeBox_not_patchSupport m F t D p ht htm hp
  have hnotNew := bulkFarEdgeBox_not_patchSupport M F T D _ hT hTM hp'
  have hI := bulkEdgeReanchor_interior_iff m M t T F D p (by omega) (by omega) (by omega) (by omega) hp
  by_cases hpI : p ∈ bulkInterior m
  · rw [bulkCoverNeighbours_eq_merged_of_not_support m p hpI hnotOld,
      bulkCoverNeighbours_eq_merged_of_not_support M _ (hI.mpr hpI) hnotNew]
    exact bulkEdgeReanchor_mergedNeighbours_card m M t T F D p
      (by omega) (by omega) (by omega) (by omega) hp
  · have hpI' : bulkEdgeReanchor m M t T F p ∉ bulkInterior M := fun h => hpI (hI.mp h)
    rw [bulkCoverNeighbours_empty_of_not_interior m p hpI,
      bulkCoverNeighbours_empty_of_not_interior M _ hpI']

end ProteinFolding.Tetrahedral
