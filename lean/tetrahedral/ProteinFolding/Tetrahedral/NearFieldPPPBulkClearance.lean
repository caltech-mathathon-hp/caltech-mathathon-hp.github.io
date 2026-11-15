import ProteinFolding.Tetrahedral.NearFieldBulkXRowOwners
import ProteinFolding.Tetrahedral.NearFieldBorrowedBulkClearance

/-! Every actual bulk endpoint column avoids every edge PPP. The endpoints
are deleted H-edge sites; the only other possible column owners have bulk
degree two by the complete X-plane second-row theorem. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem edgePPPFold_ne_bulkEndColumn (m : ℕ) (hm : 30 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m)
    (hC : C.owner ∈ bulkInterior m) (hend : (bulkCoverNeighbours m C.owner).card = 1)
    (s : Fin 3) (n : ℕ) : (edgePPPFold m F r).pos s ≠ C.point n := by
  intro heq
  have hm1 : 1 ≤ m := by omega
  rcases edgePPPFold_column_owner hm1 F r hr C n s heq.symm with h | h | h | h
  · have hd := edgeZigzag_mem_deleted hm1 F r (by omega)
    rw [← h] at hd
    exact (Finset.mem_sdiff.mp hC).2 hd
  · have hd := edgeZigzag_mem_deleted hm1 F (r + 2) hr
    rw [← h] at hd
    exact (Finset.mem_sdiff.mp hC).2 hd
  · have hI : edgeASecondRowOwner m F r ∈ bulkInterior m := by rw [← h.2.2]; exact hC
    have hd := edgeASecondRow_bulk_degree m hm F r h.1 h.2.1 hI
    rw [← h.2.2] at hd
    exact (by decide : (2 : ℕ) ≠ 1) (hd.symm.trans hend)
  · have hI : edgeBSecondRowOwner m F r ∈ bulkInterior m := by rw [← h.2.2]; exact hC
    have hd := edgeBSecondRow_bulk_degree m hm F r h.1 h.2.1 hI
    rw [← h.2.2] at hd
    exact (by decide : (2 : ℕ) ≠ 1) (hd.symm.trans hend)

end ProteinFolding.Tetrahedral.NearField
