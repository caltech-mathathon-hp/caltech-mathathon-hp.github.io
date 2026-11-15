import ProteinFolding.Tetrahedral.PathCoverExtraction
import ProteinFolding.Tetrahedral.BulkFastLocal

/-! Every cover edge is supported on the bulk, so passing to the finite induced
graph preserves reachability exactly. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def bulkLiftToFinite (m : ℕ) (fallback : BulkVertex m) (p : Site) : BulkVertex m :=
  if h : bulkFastInterior m p then ⟨p, (bulkInterior_fast_iff m p).mpr h⟩ else fallback

@[simp] theorem bulkLiftToFinite_val (m : ℕ) (fallback p : BulkVertex m) :
    bulkLiftToFinite m fallback p.val = p := by
  simp only [bulkLiftToFinite, dif_pos ((bulkInterior_fast_iff m p.val).mp p.property)]

def bulkLiftToFiniteHom (m : ℕ) (fallback : BulkVertex m) :
    bulkCoverGraph m →g bulkFiniteGraph m where
  toFun := bulkLiftToFinite m fallback
  map_rel' := by
    intro p q hpq
    have hp : bulkFastInterior m p :=
      (bulkInterior_fast_iff m p).mp (bulkCoverGraph_support m hpq).1
    have hq : bulkFastInterior m q :=
      (bulkInterior_fast_iff m q).mp (bulkCoverGraph_support m hpq).2
    change (bulkCoverGraph m).Adj (bulkLiftToFinite m fallback p).val
      (bulkLiftToFinite m fallback q).val
    simpa only [bulkLiftToFinite, dif_pos hp, dif_pos hq] using hpq

theorem bulkFinite_reachable_iff (m : ℕ) (p q : BulkVertex m) :
    (bulkFiniteGraph m).Reachable p q ↔ (bulkCoverGraph m).Reachable p.val q.val := by
  constructor
  · rintro ⟨walk⟩
    exact ⟨walk.map ⟨Subtype.val, fun h => h⟩⟩
  · rintro ⟨walk⟩
    have h : (bulkFiniteGraph m).Reachable
        (bulkLiftToFinite m p p.val) (bulkLiftToFinite m p q.val) :=
      ⟨walk.map (bulkLiftToFiniteHom m p)⟩
    simpa only [bulkLiftToFinite_val] using h

end ProteinFolding.Tetrahedral
