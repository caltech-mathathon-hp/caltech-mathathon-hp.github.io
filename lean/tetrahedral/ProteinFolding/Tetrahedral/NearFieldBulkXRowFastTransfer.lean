import ProteinFolding.Tetrahedral.NearFieldBulkXRowTransfers
import ProteinFolding.Tetrahedral.BulkEdgeMergeTransfer
import ProteinFolding.Tetrahedral.BulkFastLocal

/-! Logical halfspace versions of the checked interior transfer. They avoid
reducing enumerated octahedra while transporting local certificates. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem vertex_fastInterior_iff (m M : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hM : D + 2 ≤ M) (hp : InBulkVertexBox m v D p) :
    bulkFastInterior M (bulkReanchorSite m M v p) ↔ bulkFastInterior m p :=
  (bulkInterior_fast_iff M _).symm.trans
    ((bulkReanchor_interior_iff m M v D p hm hM hp).trans (bulkInterior_fast_iff m p))

theorem edge_fastInterior_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    bulkFastInterior M (bulkEdgeReanchor m M t T F p) ↔ bulkFastInterior m p :=
  (bulkInterior_fast_iff M _).symm.trans
    ((bulkEdgeReanchor_interior_iff m M t T F D p ht htm hT hTM hp).trans (bulkInterior_fast_iff m p))

end ProteinFolding.Tetrahedral.NearField
