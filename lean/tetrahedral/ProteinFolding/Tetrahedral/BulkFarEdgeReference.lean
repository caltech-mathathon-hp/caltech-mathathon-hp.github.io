import ProteinFolding.Tetrahedral.BulkEdgeCoordinates
import ProteinFolding.Tetrahedral.BulkFastLocal

/-! A finite far-edge reference certificate for damaged-end degrees. -/

namespace ProteinFolding.Tetrahedral

abbrev BulkEdgeFrameCode := Fin 4 × Fin 4 × Fin 4 × Fin 4

def ValidBulkEdgeFrameCode (q : BulkEdgeFrameCode) : Prop :=
  q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.2 ∧
    q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧ q.2.2.1 ≠ q.2.2.2

instance (q : BulkEdgeFrameCode) : Decidable (ValidBulkEdgeFrameCode q) := by
  unfold ValidBulkEdgeFrameCode
  infer_instance

def bulkEdgeFrameCodeEquiv : OctEdgeFrame ≃ {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} where
  toFun F := ⟨(F.k, F.j, F.a, F.b), F.kj, F.ka, F.kb, F.ja, F.jb, F.ab⟩
  invFun q := ⟨q.val.1, q.val.2.1, q.val.2.2.1, q.val.2.2.2,
    q.property.1, q.property.2.1, q.property.2.2.1, q.property.2.2.2.1,
    q.property.2.2.2.2.1, q.property.2.2.2.2.2⟩
  left_inv := by intro F; cases F; rfl
  right_inv := by intro q; apply Subtype.ext; rfl

local instance : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

def bulkEdgeCandidate (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4) (hm : 1 ≤ m) : Site :=
  match odd with
  | false => step (bulkClosedEdgeAnchor m F t hm) d
  | true => step (step (bulkClosedEdgeAnchor m F t hm) F.a) d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem bulkFarEdge_reference_damaged_degree (F : OctEdgeFrame) (odd : Bool) (d : Fin 4) :
    bulkFastDamaged 21 (bulkEdgeCandidate 21 F 10 odd d (by decide)) →
      2 ≤ (bulkFastCoverDirections 21 (bulkEdgeCandidate 21 F 10 odd d (by decide))).card := by
  revert F odd d
  decide

end ProteinFolding.Tetrahedral
