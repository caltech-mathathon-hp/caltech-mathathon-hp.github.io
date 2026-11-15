import ProteinFolding.Tetrahedral.NearFieldBulkXRowClassification
import ProteinFolding.Tetrahedral.NearFieldBulkXRowDegree

/-! Uniform degree two for the actual second-row owners appearing in the
generic PPP-column classification, with arbitrary edge frame and index. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem edgeASecondRow_bulk_degree (m : ℕ) (hm : 30 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hx : columnOpposite F.k = F.j) (hA : InASublattice (octEdgeZigzag m F r).val)
    (hp : edgeASecondRowOwner m F r ∈ bulkInterior m) :
    (bulkCoverNeighbours m (edgeASecondRowOwner m F r)).card = 2 := by
  have hm1 : 1 ≤ m := by omega
  have hmod := edgeZigzag_A_even hm1 F r hA
  have hr : r = 2 * (r / 2) := by omega
  obtain ⟨k, reverse, hF⟩ := xRowFrames_exhaustive F hx
  subst F
  have hsite := xRowSite_eq_owner m hm1 k reverse false (r / 2)
  simp only [Bool.false_eq_true, ite_false] at hsite
  rw [← hr] at hsite
  rw [← hsite] at hp ⊢
  exact xRowSite_degree m hm k reverse false (r / 2) hp

theorem edgeBSecondRow_bulk_degree (m : ℕ) (hm : 30 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hx : columnOpposite F.j = F.k) (hB : InBSublattice (octEdgeZigzag m F r).val)
    (hp : edgeBSecondRowOwner m F r ∈ bulkInterior m) :
    (bulkCoverNeighbours m (edgeBSecondRowOwner m F r)).card = 2 := by
  have hm1 : 1 ≤ m := by omega
  have hmod := edgeZigzag_B_odd hm1 F r hB
  have hr : r = 2 * (r / 2) + 1 := by omega
  obtain ⟨k, reverse, hF⟩ := xRowFrames_exhaustive F (xRowOpposite_symmetric F.k F.j hx)
  subst F
  have hsite := xRowSite_eq_owner m hm1 k reverse true (r / 2)
  simp only [ite_true] at hsite
  rw [← hr] at hsite
  rw [← hsite] at hp ⊢
  exact xRowSite_degree m hm k reverse true (r / 2) hp

end ProteinFolding.Tetrahedral.NearField
