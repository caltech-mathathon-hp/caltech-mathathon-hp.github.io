import ProteinFolding.Tetrahedral.BulkSegments
import ProteinFolding.Tetrahedral.BulkSegmentCertificates

/-! Exact component certificates compute the manuscript's segment statistics. -/

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 2000000

theorem bulkSegmentGraph_site_adj (m : ℕ) (p q : BulkVertex m) :
    (bulkSegmentGraph m).Adj p q ↔ (bulkSiteSegmentGraph m).Adj p.val q.val := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2⟩
  · intro h
    exact ⟨h.1, bulkCoverBond_adj m h.1, h.2⟩

theorem bulkSegmentSites_image_component (m : ℕ) (p : BulkVertex m) (q : Site) :
    q ∈ (bulkSegmentSites m p).image Subtype.val ↔
      (bulkSiteSegmentGraph m).Reachable p.val q := by
  apply finset_image_component_iff_of_complete_stars
    (bulkSegmentGraph m) (bulkSiteSegmentGraph m) (bulkSegmentSites m p) p Subtype.val
  · exact (mem_bulkSegmentSites m p p).mpr (.refl _)
  · intro x hx y hadj
    exact (mem_bulkSegmentSites m p y).mpr
      (((mem_bulkSegmentSites m p x).mp hx).trans hadj.reachable)
  · intro x hx
    exact (mem_bulkSegmentSites m p x).mp hx
  · intro x _ y hadj
    exact (bulkSegmentGraph_site_adj m x y).mp hadj
  · intro x _ y hadj
    have hy : y ∈ bulkInterior m := (bulkCoverGraph_support m hadj.1).2
    exact ⟨⟨y, hy⟩, (bulkSegmentGraph_site_adj m x ⟨y, hy⟩).mpr hadj, rfl⟩

theorem bulkSegmentFiniteCheck_sites (m : ℕ) (p : BulkVertex m) (A : Finset Site)
    (rank : Site → ℕ) (h : BulkSegmentFiniteCheck m A p.val rank) :
    (bulkSegmentSites m p).image Subtype.val = A := by
  ext q
  exact (bulkSegmentSites_image_component m p q).trans
    (bulkSegmentFiniteCheck_component m A p.val rank h q).symm

theorem bulkSegmentFiniteCheck_xValues (m : ℕ) (p : BulkVertex m) (A : Finset Site)
    (rank : Site → ℕ) (h : BulkSegmentFiniteCheck m A p.val rank) :
    bulkSegmentXValues m p = A.image (fun q => q.val 0) := by
  rw [← bulkSegmentFiniteCheck_sites m p A rank h, Finset.image_image]
  rfl

theorem bulkSegmentFiniteCheck_xhat (m : ℕ) (p : BulkVertex m) (A : Finset Site)
    (rank : Site → ℕ) (h : BulkSegmentFiniteCheck m A p.val rank)
    (hx : (A.image (fun q => q.val 0)).Nonempty) :
    bulkSegmentXhat m p =
      (A.image (fun q => q.val 0)).min' hx + (A.image (fun q => q.val 0)).max' hx := by
  unfold bulkSegmentXhat
  simp only [bulkSegmentFiniteCheck_xValues m p A rank h]

theorem bulkSegmentFiniteCheck_row (m : ℕ) (p : BulkVertex m) (A : Finset Site)
    (rank : Site → ℕ) (h : BulkSegmentFiniteCheck m A p.val rank) :
    BulkRowSegment m p ↔ ∃ q ∈ A, q ∈ bulkDamaged m ∧ bulkZ q = 0 := by
  have hsites := bulkSegmentFiniteCheck_sites m p A rank h
  unfold BulkRowSegment
  rw [← hsites]
  constructor
  · rintro ⟨q, hq, hD, hZ⟩
    exact ⟨q.val, Finset.mem_image.mpr ⟨q, hq, rfl⟩, hD, hZ⟩
  · rintro ⟨q, hq, hD, hZ⟩
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨r, hr, hD, hZ⟩

end ProteinFolding.Tetrahedral
