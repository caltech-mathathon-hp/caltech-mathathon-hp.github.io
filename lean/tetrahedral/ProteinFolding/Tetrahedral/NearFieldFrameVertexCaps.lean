import ProteinFolding.Tetrahedral.NearFieldFrameSeparation
import ProteinFolding.Tetrahedral.OctahedralVertices

/-! The free caps at Va and Vc and their complete columns miss every frame P-link. -/

namespace ProteinFolding.Tetrahedral

def frameEndpointVertex (m : ℕ) (atStart : Bool) : Site :=
  if atStart then octVertexSite m 2 false else octVertexSite m 0 true

theorem frameEndpointVertex_inA (m : ℕ) (atStart : Bool) :
    InASublattice (frameEndpointVertex m atStart).val := by
  cases atStart
  · exact octVertexCoordinates_inA m 0 true
  · exact octVertexCoordinates_inA m 2 false

theorem frameEndpointVertex_mem {m : ℕ} (hm : 1 ≤ m) (atStart : Bool) :
    frameEndpointVertex m atStart ∈ octahedron m := by
  cases atStart
  · exact octVertexSite_mem_octahedron hm 0 true
  · exact octVertexSite_mem_octahedron hm 2 false

theorem frameEndpointVertex_face (m : ℕ) (atStart : Bool) :
    tetraCoordinate m (frameEndpointVertex m atStart).val 1 = octRadius m := by
  cases atStart <;> dsimp [frameEndpointVertex, octVertexSite, octVertexCoordinates, octCentre, tetraCoordinate] <;> omega

def frameEndpointColumn {m : ℕ} (hm : 1 ≤ m) (atStart : Bool) : DanglingColumn m where
  owner := frameEndpointVertex m atStart
  dir := 1
  owner_mem := frameEndpointVertex_mem hm atStart
  seed_outside := (step_not_mem_octahedron_A m (frameEndpointVertex_inA m atStart)
    (frameEndpointVertex_mem hm atStart) 1).mpr (frameEndpointVertex_face m atStart)

theorem frameEndpointColumn_sy {m : ℕ} (hm : 1 ≤ m) (atStart : Bool) :
    (frameEndpointColumn hm atStart).sy = -1 := by
  change (if InASublattice (frameEndpointVertex m atStart).val then bigFaceY 1 else -bigFaceY 1) = -1
  rw [if_pos (frameEndpointVertex_inA m atStart)]
  rfl

theorem frameEndpointColumn_negativeY {m : ℕ} (hm : 1 ≤ m) (atStart : Bool) (n : ℕ) :
    bulkY m ((frameEndpointColumn hm atStart).point n) ≤ -1 - (n : ℤ) := by
  have h := (frameEndpointColumn hm atStart).point_signed_y n
  rw [frameEndpointColumn_sy] at h
  omega

theorem nearFrameP_positiveY (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    1 ≤ bulkY m (nearFramePoint m q kind hq r) := by
  have h := (nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 1).1
  change 1 ≤ (nearFramePoint m q kind hq r).val 1 - octRadius m
  fin_cases kind
  · change octRadius m + 1 ≤ (nearFramePoint m q 0 hq r).val 1 at h
    change 1 ≤ (nearFramePoint m q 0 hq r).val 1 - octRadius m
    omega
  · change octRadius m + q + 1 ≤ (nearFramePoint m q 1 hq r).val 1 at h
    change 1 ≤ (nearFramePoint m q 1 hq r).val 1 - octRadius m
    omega
  · change 2 * octRadius m - 1 ≤ (nearFramePoint m q 2 hq r).val 1 at h
    change 1 ≤ (nearFramePoint m q 2 hq r).val 1 - octRadius m
    omega
  · change 2 * octRadius m - 1 ≤ (nearFramePoint m q 3 hq r).val 1 at h
    change 1 ≤ (nearFramePoint m q 3 hq r).val 1 - octRadius m
    omega
  · change octRadius m + q + 1 ≤ (nearFramePoint m q 4 hq r).val 1 at h
    change 1 ≤ (nearFramePoint m q 4 hq r).val 1 - octRadius m
    omega
  · change octRadius m + 1 ≤ (nearFramePoint m q 5 hq r).val 1 at h
    change 1 ≤ (nearFramePoint m q 5 hq r).val 1 - octRadius m
    omega

theorem frameEndpointColumn_ne_frameP {m : ℕ} (hm : 1 ≤ m) (atStart : Bool) (n q : ℕ)
    (kind : Fin 6) (hq : q % 2 = 1) (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (frameEndpointColumn hm atStart).point n ≠ nearFramePoint m q kind hq r := by
  intro heq
  have hn := frameEndpointColumn_negativeY hm atStart n
  have hp := nearFrameP_positiveY m q kind hq hqlo hqhi r hr0 hrlast
  rw [heq] at hn
  omega

theorem frameEndpointColumns_seed_ne {m : ℕ} (hm : 2 ≤ m) :
    (frameEndpointColumn (show 1 ≤ m by omega) true).seed ≠
      (frameEndpointColumn (show 1 ≤ m by omega) false).seed := by
  let C := frameEndpointColumn (show 1 ≤ m by omega) true
  let D := frameEndpointColumn (show 1 ≤ m by omega) false
  intro heq
  have howner : D.owner = C.owner := outside_step_unique_inside m C.owner_mem C.dir C.seed_outside
    (by change tetrahedralLattice.Adj C.seed D.owner; rw [heq]; exact (step_adj D.owner D.dir).symm)
    D.owner_mem
  have hx := congrArg (fun p : Site => p.val 0) howner
  dsimp [C, D, frameEndpointColumn, frameEndpointVertex, octVertexSite, octVertexCoordinates, octCentre] at hx
  dsimp [octRadius] at hx
  omega

theorem frameEndpointColumns_disjoint {m : ℕ} (hm : 2 ≤ m) :
    Disjoint (frameEndpointColumn (show 1 ≤ m by omega) true).sites
      (frameEndpointColumn (show 1 ≤ m by omega) false).sites :=
  DanglingColumn.sites_disjoint_of_seed_ne (frameEndpointColumns_seed_ne hm)

end ProteinFolding.Tetrahedral
