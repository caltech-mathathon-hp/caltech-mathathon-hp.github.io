import ProteinFolding.Tetrahedral.BulkSegmentEdgeTransfer
import ProteinFolding.Tetrahedral.BulkSegmentCoordinateTransfer

/-! Exact segment statistics under complete far-edge transport. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkSegment_edge_projected (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ)
    (A : Finset Site) (p : BulkVertex m) (q : BulkVertex M) (rank : Site → ℕ)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hT : D + 8 ≤ T) (hTM : T + D + 9 ≤ M)
    (hbox : ∀ r ∈ A, InBulkEdgeBox m F t D r)
    (h : BulkSegmentFiniteCheck m A p.val rank) (hq : q.val = bulkEdgeReanchor m M t T F p.val) :
    (bulkSegmentSites M q).image Subtype.val = A.image (bulkEdgeReanchor m M t T F) := by
  ext r
  rw [bulkSegmentSites_image_component, hq]
  exact (bulkSegmentFiniteCheck_edge_component m M t T F D A p.val rank ht htm hT hTM hbox h r).symm

theorem bulkSegment_edge_xValues_shift (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ)
    (A : Finset Site) (p : BulkVertex m) (q : BulkVertex M) (rank : Site → ℕ)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hT : D + 8 ≤ T) (hTM : T + D + 9 ≤ M)
    (hbox : ∀ r ∈ A, InBulkEdgeBox m F t D r)
    (h : BulkSegmentFiniteCheck m A p.val rank) (hq : q.val = bulkEdgeReanchor m M t T F p.val) :
    bulkSegmentXValues M q = (bulkSegmentXValues m p).image
      (fun x => x + ((bulkEdgeAnchor M F T).val 0 - (bulkEdgeAnchor m F t).val 0)) := by
  rw [bulkSegment_projected_xValues M q _
      (bulkSegment_edge_projected m M t T F D A p q rank ht htm hT hTM hbox h hq),
    bulkSegmentFiniteCheck_xValues m p A rank h, Finset.image_image, Finset.image_image]
  congr 1
  funext r
  change (bulkEdgeReanchor m M t T F r).val 0 =
    r.val 0 + ((bulkEdgeAnchor M F T).val 0 - (bulkEdgeAnchor m F t).val 0)
  rw [bulkEdgeReanchor_coordinates]
  omega

theorem bulkSegment_edge_xhat_shift (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ)
    (A : Finset Site) (p : BulkVertex m) (q : BulkVertex M) (rank : Site → ℕ)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hT : D + 8 ≤ T) (hTM : T + D + 9 ≤ M)
    (hbox : ∀ r ∈ A, InBulkEdgeBox m F t D r)
    (h : BulkSegmentFiniteCheck m A p.val rank) (hq : q.val = bulkEdgeReanchor m M t T F p.val) :
    bulkSegmentXhat M q = bulkSegmentXhat m p +
      2 * ((bulkEdgeAnchor M F T).val 0 - (bulkEdgeAnchor m F t).val 0) := by
  have hmono : Monotone (fun x : ℤ => x +
      ((bulkEdgeAnchor M F T).val 0 - (bulkEdgeAnchor m F t).val 0)) := by
    intro x y hxy
    change x + ((bulkEdgeAnchor M F T).val 0 - (bulkEdgeAnchor m F t).val 0) ≤
      y + ((bulkEdgeAnchor M F T).val 0 - (bulkEdgeAnchor m F t).val 0)
    omega
  unfold bulkSegmentXhat
  simp only [bulkSegment_edge_xValues_shift m M t T F D A p q rank ht htm hT hTM hbox h hq,
    Finset.min'_image hmono, Finset.max'_image hmono]
  ring

theorem bulkSegment_edge_row (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ)
    (A : Finset Site) (p : BulkVertex m) (q : BulkVertex M) (rank : Site → ℕ)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hT : D + 8 ≤ T) (hTM : T + D + 9 ≤ M)
    (hbox : ∀ r ∈ A, InBulkEdgeBox m F t D r)
    (h : BulkSegmentFiniteCheck m A p.val rank) (hq : q.val = bulkEdgeReanchor m M t T F p.val) :
    BulkRowSegment M q ↔ BulkRowSegment m p := by
  rw [bulkSegment_projected_row M q _
      (bulkSegment_edge_projected m M t T F D A p q rank ht htm hT hTM hbox h hq),
    bulkSegmentFiniteCheck_row m p A rank h]
  constructor
  · rintro ⟨r, hr, hd, hz⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    refine ⟨s, hs, ?_, ?_⟩
    · exact (bulkEdgeReanchor_damaged_iff m M t T F D s (by omega) (by omega)
        (by omega) (by omega) (hbox s hs)).mp hd
    · exact ((bulkEdgeReanchor_zeros m M t T F D s (by omega) (by omega)
        (by omega) (by omega) (hbox s hs)).2).mp hz
  · rintro ⟨r, hr, hd, hz⟩
    refine ⟨bulkEdgeReanchor m M t T F r, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_, ?_⟩
    · exact (bulkEdgeReanchor_damaged_iff m M t T F D r (by omega) (by omega)
        (by omega) (by omega) (hbox r hr)).mpr hd
    · exact ((bulkEdgeReanchor_zeros m M t T F D r (by omega) (by omega)
        (by omega) (by omega) (hbox r hr)).2).mpr hz

end ProteinFolding.Tetrahedral
