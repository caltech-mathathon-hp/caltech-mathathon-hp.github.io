import ProteinFolding.Tetrahedral.BulkCoverPathCertificates

/-! Explicit escape walks for the ten near-vertex local maxima at size50.
Their complete uniform coverage is proved separately. -/

namespace ProteinFolding.Tetrahedral

def bulkNearEscapePath (i : Fin 10) : List Site :=
  match i.val with
  | 0 => [⟨![-95, 97, 1], by decide⟩,
      ⟨![-94, 98, 0], by decide⟩,
      ⟨![-95, 99, -1], by decide⟩,
      ⟨![-94, 100, -2], by decide⟩,
      ⟨![-93, 99, -3], by decide⟩,
      ⟨![-92, 100, -4], by decide⟩]
  | 1 => [⟨![-2, 4, -2], by decide⟩,
      ⟨![-1, 5, -1], by decide⟩,
      ⟨![-2, 6, 0], by decide⟩,
      ⟨![-1, 7, 1], by decide⟩,
      ⟨![-2, 8, 2], by decide⟩,
      ⟨![-3, 9, 1], by decide⟩,
      ⟨![-4, 8, 0], by decide⟩,
      ⟨![-3, 7, -1], by decide⟩,
      ⟨![-4, 6, -2], by decide⟩,
      ⟨![-5, 7, -3], by decide⟩,
      ⟨![-6, 8, -2], by decide⟩,
      ⟨![-5, 9, -1], by decide⟩,
      ⟨![-6, 10, 0], by decide⟩,
      ⟨![-5, 11, 1], by decide⟩,
      ⟨![-4, 10, 2], by decide⟩,
      ⟨![-5, 9, 3], by decide⟩,
      ⟨![-4, 8, 4], by decide⟩,
      ⟨![-3, 7, 3], by decide⟩,
      ⟨![-2, 6, 4], by decide⟩,
      ⟨![-1, 5, 3], by decide⟩]
  | 2 => [⟨![1, 5, 1], by decide⟩,
      ⟨![2, 4, 2], by decide⟩,
      ⟨![3, 5, 3], by decide⟩,
      ⟨![4, 6, 2], by decide⟩,
      ⟨![3, 7, 1], by decide⟩,
      ⟨![2, 6, 0], by decide⟩,
      ⟨![3, 5, -1], by decide⟩,
      ⟨![4, 6, -2], by decide⟩,
      ⟨![5, 7, -1], by decide⟩,
      ⟨![4, 8, 0], by decide⟩,
      ⟨![5, 9, 1], by decide⟩,
      ⟨![6, 8, 2], by decide⟩,
      ⟨![5, 7, 3], by decide⟩]
  | 3 => [⟨![-3, 101, -91], by decide⟩,
      ⟨![-2, 100, -90], by decide⟩,
      ⟨![-3, 99, -89], by decide⟩,
      ⟨![-2, 98, -88], by decide⟩,
      ⟨![-1, 97, -89], by decide⟩,
      ⟨![-2, 96, -90], by decide⟩,
      ⟨![-1, 95, -91], by decide⟩,
      ⟨![-2, 94, -92], by decide⟩,
      ⟨![-3, 93, -91], by decide⟩,
      ⟨![-4, 94, -90], by decide⟩,
      ⟨![-3, 95, -89], by decide⟩,
      ⟨![-4, 96, -88], by decide⟩,
      ⟨![-3, 97, -87], by decide⟩,
      ⟨![-4, 98, -86], by decide⟩,
      ⟨![-5, 99, -87], by decide⟩,
      ⟨![-4, 100, -88], by decide⟩,
      ⟨![-5, 101, -89], by decide⟩,
      ⟨![-4, 102, -90], by decide⟩]
  | 4 => [⟨![3, 101, -93], by decide⟩,
      ⟨![2, 100, -94], by decide⟩,
      ⟨![1, 99, -93], by decide⟩,
      ⟨![2, 98, -92], by decide⟩,
      ⟨![3, 97, -93], by decide⟩,
      ⟨![2, 96, -94], by decide⟩,
      ⟨![1, 97, -95], by decide⟩,
      ⟨![0, 98, -94], by decide⟩,
      ⟨![-1, 99, -95], by decide⟩,
      ⟨![-2, 100, -94], by decide⟩,
      ⟨![-3, 99, -93], by decide⟩,
      ⟨![-2, 98, -92], by decide⟩,
      ⟨![-1, 97, -93], by decide⟩,
      ⟨![-2, 96, -94], by decide⟩,
      ⟨![-3, 95, -93], by decide⟩,
      ⟨![-4, 96, -92], by decide⟩,
      ⟨![-3, 97, -91], by decide⟩,
      ⟨![-4, 98, -90], by decide⟩,
      ⟨![-5, 99, -91], by decide⟩,
      ⟨![-4, 100, -92], by decide⟩,
      ⟨![-3, 101, -91], by decide⟩,
      ⟨![-2, 100, -90], by decide⟩,
      ⟨![-3, 99, -89], by decide⟩,
      ⟨![-2, 98, -88], by decide⟩,
      ⟨![-1, 97, -89], by decide⟩,
      ⟨![-2, 96, -90], by decide⟩,
      ⟨![-1, 95, -91], by decide⟩,
      ⟨![-2, 94, -92], by decide⟩,
      ⟨![-3, 93, -91], by decide⟩,
      ⟨![-4, 94, -90], by decide⟩,
      ⟨![-3, 95, -89], by decide⟩,
      ⟨![-4, 96, -88], by decide⟩,
      ⟨![-3, 97, -87], by decide⟩,
      ⟨![-4, 98, -86], by decide⟩,
      ⟨![-5, 99, -87], by decide⟩,
      ⟨![-4, 100, -88], by decide⟩,
      ⟨![-5, 101, -89], by decide⟩,
      ⟨![-4, 102, -90], by decide⟩]
  | 5 => [⟨![-3, 95, 91], by decide⟩,
      ⟨![-2, 96, 90], by decide⟩,
      ⟨![-3, 97, 89], by decide⟩,
      ⟨![-2, 98, 88], by decide⟩,
      ⟨![-1, 99, 89], by decide⟩,
      ⟨![-2, 100, 90], by decide⟩,
      ⟨![-1, 101, 91], by decide⟩,
      ⟨![-2, 102, 92], by decide⟩,
      ⟨![-3, 103, 91], by decide⟩,
      ⟨![-4, 102, 90], by decide⟩,
      ⟨![-3, 101, 89], by decide⟩,
      ⟨![-4, 100, 88], by decide⟩,
      ⟨![-3, 99, 87], by decide⟩,
      ⟨![-4, 98, 86], by decide⟩,
      ⟨![-5, 97, 87], by decide⟩,
      ⟨![-4, 96, 88], by decide⟩,
      ⟨![-5, 95, 89], by decide⟩,
      ⟨![-4, 94, 90], by decide⟩]
  | 6 => [⟨![3, 95, 93], by decide⟩,
      ⟨![2, 94, 92], by decide⟩,
      ⟨![1, 95, 91], by decide⟩,
      ⟨![2, 96, 90], by decide⟩,
      ⟨![1, 97, 89], by decide⟩,
      ⟨![2, 98, 88], by decide⟩,
      ⟨![3, 99, 89], by decide⟩,
      ⟨![2, 100, 90], by decide⟩,
      ⟨![3, 101, 91], by decide⟩,
      ⟨![2, 102, 92], by decide⟩,
      ⟨![1, 101, 93], by decide⟩,
      ⟨![0, 100, 92], by decide⟩,
      ⟨![1, 99, 91], by decide⟩,
      ⟨![0, 98, 90], by decide⟩,
      ⟨![-1, 97, 91], by decide⟩,
      ⟨![0, 96, 92], by decide⟩,
      ⟨![-1, 95, 93], by decide⟩,
      ⟨![-2, 94, 92], by decide⟩,
      ⟨![-1, 93, 91], by decide⟩,
      ⟨![0, 94, 90], by decide⟩,
      ⟨![-1, 95, 89], by decide⟩,
      ⟨![0, 96, 88], by decide⟩,
      ⟨![-1, 97, 87], by decide⟩,
      ⟨![0, 98, 86], by decide⟩,
      ⟨![1, 99, 87], by decide⟩,
      ⟨![0, 100, 88], by decide⟩,
      ⟨![1, 101, 89], by decide⟩,
      ⟨![0, 102, 90], by decide⟩,
      ⟨![1, 103, 91], by decide⟩,
      ⟨![2, 104, 90], by decide⟩,
      ⟨![3, 103, 89], by decide⟩,
      ⟨![2, 102, 88], by decide⟩,
      ⟨![3, 101, 87], by decide⟩,
      ⟨![2, 100, 86], by decide⟩,
      ⟨![3, 99, 85], by decide⟩,
      ⟨![2, 98, 84], by decide⟩,
      ⟨![1, 97, 85], by decide⟩,
      ⟨![2, 96, 86], by decide⟩,
      ⟨![1, 95, 87], by decide⟩,
      ⟨![2, 94, 88], by decide⟩,
      ⟨![1, 93, 89], by decide⟩,
      ⟨![2, 92, 90], by decide⟩,
      ⟨![3, 93, 91], by decide⟩,
      ⟨![4, 94, 90], by decide⟩,
      ⟨![3, 95, 89], by decide⟩,
      ⟨![4, 96, 88], by decide⟩,
      ⟨![3, 97, 87], by decide⟩,
      ⟨![4, 98, 86], by decide⟩,
      ⟨![5, 99, 87], by decide⟩,
      ⟨![4, 100, 88], by decide⟩,
      ⟨![5, 101, 89], by decide⟩,
      ⟨![4, 102, 90], by decide⟩]
  | 7 => [⟨![-2, 192, 2], by decide⟩,
      ⟨![-1, 191, 1], by decide⟩,
      ⟨![-2, 190, 0], by decide⟩,
      ⟨![-3, 189, 1], by decide⟩,
      ⟨![-4, 190, 2], by decide⟩,
      ⟨![-5, 189, 3], by decide⟩,
      ⟨![-6, 188, 2], by decide⟩,
      ⟨![-5, 187, 1], by decide⟩,
      ⟨![-4, 188, 0], by decide⟩,
      ⟨![-5, 189, -1], by decide⟩,
      ⟨![-4, 190, -2], by decide⟩,
      ⟨![-3, 191, -1], by decide⟩,
      ⟨![-2, 192, -2], by decide⟩,
      ⟨![-1, 193, -1], by decide⟩]
  | 8 => [⟨![1, 191, 3], by decide⟩,
      ⟨![0, 190, 2], by decide⟩,
      ⟨![1, 189, 1], by decide⟩,
      ⟨![2, 190, 0], by decide⟩,
      ⟨![1, 191, -1], by decide⟩,
      ⟨![2, 192, -2], by decide⟩,
      ⟨![3, 191, -3], by decide⟩,
      ⟨![4, 190, -2], by decide⟩,
      ⟨![3, 189, -1], by decide⟩,
      ⟨![4, 188, 0], by decide⟩,
      ⟨![3, 187, 1], by decide⟩,
      ⟨![2, 188, 2], by decide⟩,
      ⟨![3, 189, 3], by decide⟩,
      ⟨![4, 188, 4], by decide⟩,
      ⟨![5, 187, 3], by decide⟩,
      ⟨![4, 186, 2], by decide⟩,
      ⟨![5, 185, 1], by decide⟩,
      ⟨![6, 186, 0], by decide⟩,
      ⟨![5, 187, -1], by decide⟩,
      ⟨![6, 188, -2], by decide⟩,
      ⟨![5, 189, -3], by decide⟩]
  | _ => [⟨![94, 100, 2], by decide⟩,
      ⟨![95, 99, 1], by decide⟩,
      ⟨![94, 98, 0], by decide⟩,
      ⟨![95, 97, -1], by decide⟩,
      ⟨![94, 96, -2], by decide⟩,
      ⟨![93, 97, -3], by decide⟩,
      ⟨![92, 96, -4], by decide⟩]

def bulkNearEscapeVertex (i : Fin 10) : Fin 6 :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 4
  | 8 => 4
  | _ => 5

def bulkNearEscapeHasEnd (i : Fin 10) : Bool :=
  i.val ≠ 1 && i.val ≠ 7

def bulkNearEscapeStart (i : Fin 10) : Site :=
  (bulkNearEscapePath i).headD (octVertexSite 50 0 false)

def bulkNearEscapeFinish (i : Fin 10) : Site :=
  (bulkNearEscapePath i).getLastD (octVertexSite 50 0 false)

theorem bulkNearEscape_nonempty (i : Fin 10) : bulkNearEscapePath i ≠ [] := by
  revert i
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem bulkNearEscape_reference_chain (i : Fin 10) :
    (bulkNearEscapePath i).IsChain (bulkFastCoverBond 50) := by
  revert i
  decide

theorem bulkNearEscape_reference_box (i : Fin 10) :
    ∀ p ∈ bulkNearEscapePath i, InBulkVertexBox 50 (bulkNearEscapeVertex i) 14 p := by
  revert i
  unfold InBulkVertexBox
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bulkNearEscape_reference_end (i : Fin 10) (h : bulkNearEscapeHasEnd i = true) :
    (bulkFastCoverDirections 50 (bulkNearEscapeFinish i)).card ≤ 1 := by
  revert i
  decide

end ProteinFolding.Tetrahedral
