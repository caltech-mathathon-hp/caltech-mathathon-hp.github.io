import ProteinFolding.Tetrahedral.BulkSegmentQuickCertificates
import ProteinFolding.Tetrahedral.BulkJointPlanes

/-! Six literal complete row segments at the far-edge reference size.
The four source components have explicit joints to the next listed row. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def bulkFarZRoot (i : Fin 6) : Site :=
  match i.val with
  | 0 => ⟨![25, 77, 1], by decide⟩
  | 1 => ⟨![26, 76, 2], by decide⟩
  | 2 => ⟨![28, 74, 2], by decide⟩
  | 3 => ⟨![-25, 27, 1], by decide⟩
  | 4 => ⟨![-26, 28, 2], by decide⟩
  | _ => ⟨![-28, 30, 2], by decide⟩

def bulkFarZOther (i : Fin 6) : Site :=
  match i.val with
  | 0 => ⟨![24, 78, 2], by decide⟩
  | 1 => ⟨![27, 75, 1], by decide⟩
  | 2 => ⟨![29, 73, 1], by decide⟩
  | 3 => ⟨![-24, 26, 2], by decide⟩
  | 4 => ⟨![-27, 29, 1], by decide⟩
  | _ => ⟨![-29, 31, 1], by decide⟩

def bulkFarZSupport (i : Fin 6) : Finset Site := {bulkFarZRoot i, bulkFarZOther i}
def bulkFarZRank (i : Fin 6) (p : Site) : ℕ := if p = bulkFarZRoot i then 0 else 1
def bulkFarZPrev (i : Fin 6) (_ : Site) : Site := bulkFarZRoot i

theorem bulkFarZ_reference_quick (i : Fin 6) :
    BulkSegmentQuickCheck 27 (bulkFarZSupport i) (bulkFarZRoot i) (bulkFarZRank i) (bulkFarZPrev i) := by
  revert i
  decide

theorem bulkFarZ_reference_finite (i : Fin 6) :
    BulkSegmentFiniteCheck 27 (bulkFarZSupport i) (bulkFarZRoot i) (bulkFarZRank i) :=
  bulkSegmentQuickCheck_sound 27 _ _ _ _ (bulkFarZ_reference_quick i)

def bulkFarZFrom (i : Fin 4) : Fin 6 := if i.val < 2 then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩
def bulkFarZTo (i : Fin 4) : Fin 6 := ⟨(bulkFarZFrom i).val + 1, by fin_cases i <;> decide⟩
def bulkFarZJointSource (i : Fin 4) : Site :=
  if i.val % 2 = 0 then bulkFarZRoot (bulkFarZFrom i) else bulkFarZOther (bulkFarZFrom i)
def bulkFarZJointTarget (i : Fin 4) : Site := bulkFarZRoot (bulkFarZTo i)

theorem bulkFarZ_reference_joint (i : Fin 4) :
    bulkFarZJointSource i ∈ bulkFarZSupport (bulkFarZFrom i) ∧
      bulkFarZJointTarget i ∈ bulkFarZSupport (bulkFarZTo i) ∧
      bulkFastCoverBond 27 (bulkFarZJointSource i) (bulkFarZJointTarget i) := by
  revert i
  decide

def bulkFarZPositiveFrame (F : OctEdgeFrame) : Prop := F.k = 0 ∧ F.j = 3
def bulkFarZNegativeFrame (F : OctEdgeFrame) : Prop := F.k = 3 ∧ F.j = 0
instance (F : OctEdgeFrame) : Decidable (bulkFarZPositiveFrame F) := by unfold bulkFarZPositiveFrame; infer_instance
instance (F : OctEdgeFrame) : Decidable (bulkFarZNegativeFrame F) := by unfold bulkFarZNegativeFrame; infer_instance

local instance bulkFarZDataFrameFintype : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

theorem bulkFarZ_reference_boxes (F : OctEdgeFrame) (i : Fin 6) :
    ((bulkFarZPositiveFrame F ∧ i.val < 3) ∨ (bulkFarZNegativeFrame F ∧ 3 ≤ i.val)) →
      ∀ p ∈ bulkFarZSupport i, InBulkEdgeBox 27 F 13 5 p := by
  unfold InBulkEdgeBox
  revert F i
  decide

theorem bulkFarZ_reference_row (i : Fin 6) :
    ∃ p ∈ bulkFarZSupport i, bulkFastDamaged 27 p ∧ bulkZ p = 0 := by
  revert i
  decide

end ProteinFolding.Tetrahedral
