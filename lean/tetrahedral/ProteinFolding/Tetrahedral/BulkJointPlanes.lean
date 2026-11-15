import ProteinFolding.Tetrahedral.BulkFarDamagedDegree

/-! The plane alternatives and coordinate bounds of far damaged-edge sites.
These are local prerequisites for the uniform far-segment classification. -/

namespace ProteinFolding.Tetrahedral

def BulkXEdgeFrame (F : OctEdgeFrame) : Prop :=
  (F.k = 0 ∧ F.j = 1) ∨ (F.k = 1 ∧ F.j = 0) ∨
    (F.k = 2 ∧ F.j = 3) ∨ (F.k = 3 ∧ F.j = 2)

def BulkZEdgeFrame (F : OctEdgeFrame) : Prop :=
  (F.k = 0 ∧ F.j = 3) ∨ (F.k = 3 ∧ F.j = 0) ∨
    (F.k = 1 ∧ F.j = 2) ∨ (F.k = 2 ∧ F.j = 1)

instance (F : OctEdgeFrame) : Decidable (BulkXEdgeFrame F) := by unfold BulkXEdgeFrame; infer_instance
instance (F : OctEdgeFrame) : Decidable (BulkZEdgeFrame F) := by unfold BulkZEdgeFrame; infer_instance

local instance bulkJointPlanesFrameFintype : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bulkFarEdge_reference_plane (F : OctEdgeFrame) (odd : Bool) (d : Fin 4) :
    bulkFastDamaged 21 (bulkEdgeCandidate 21 F 10 odd d (by decide)) →
      BulkXEdgeFrame F ∨ BulkZEdgeFrame F := by
  revert F odd d
  decide

theorem bulkEdgeAnchor_x_of_X {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (hF : BulkXEdgeFrame F) : (bulkEdgeAnchor m F t).val 0 = 0 := by
  have hk := (bulkEdgeAnchor_faces hm F t).1
  have hj := (bulkEdgeAnchor_faces hm F t).2.1
  rcases hF with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  all_goals rw [h0] at hk; rw [h1] at hj
  all_goals dsimp [tetraCoordinate] at hk hj; omega

theorem bulkEdgeAnchor_z_of_Z {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (hF : BulkZEdgeFrame F) : (bulkEdgeAnchor m F t).val 2 = 0 := by
  have hk := (bulkEdgeAnchor_faces hm F t).1
  have hj := (bulkEdgeAnchor_faces hm F t).2.1
  rcases hF with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  all_goals rw [h0] at hk; rw [h1] at hj
  all_goals dsimp [tetraCoordinate] at hk hj; omega

theorem bulkEdgeCandidate_x_bound {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hF : BulkXEdgeFrame F) :
    |(bulkEdgeCandidate m F t odd d hm).val 0| ≤ 2 := by
  have hx := bulkEdgeAnchor_x_of_X hm F t hF
  cases odd
  · have h := adj_coordinate (step_adj (bulkEdgeAnchor m F t) d) 0
    simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq]
    rw [abs_le]
    constructor <;> omega
  · have h1 := adj_coordinate (step_adj (bulkEdgeAnchor m F t) F.a) 0
    have h2 := adj_coordinate (step_adj (step (bulkEdgeAnchor m F t) F.a) d) 0
    simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq]
    rw [abs_le]
    constructor <;> omega

theorem bulkEdgeCandidate_z_bound {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hF : BulkZEdgeFrame F) :
    |bulkZ (bulkEdgeCandidate m F t odd d hm)| ≤ 3 := by
  have hz := bulkEdgeAnchor_z_of_Z hm F t hF
  cases odd
  · have h := adj_coordinate (step_adj (bulkEdgeAnchor m F t) d) 2
    simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq]
    rw [abs_le]
    dsimp [bulkZ]
    constructor <;> omega
  · have h1 := adj_coordinate (step_adj (bulkEdgeAnchor m F t) F.a) 2
    have h2 := adj_coordinate (step_adj (step (bulkEdgeAnchor m F t) F.a) d) 2
    simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq]
    rw [abs_le]
    dsimp [bulkZ]
    constructor <;> omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem bulkFarEdge_damaged_plane (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) (ht : 10 ≤ t) (htm : t + 11 ≤ m)
    (hd : bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m) :
    BulkXEdgeFrame F ∨ BulkZEdgeFrame F := by
  have hbox := bulkEdgeCandidate_in_box m F t odd d hm
  have hDm := (bulkEdgeReanchor_damaged_iff m 21 t 10 F 2 (bulkEdgeCandidate m F t odd d hm)
    (by omega) (by omega) (by decide) (by decide) hbox).mpr hd
  rw [bulkEdgeReanchor_candidate m 21 t 10 F odd d hm (by decide)] at hDm
  exact bulkFarEdge_reference_plane F odd d ((bulkDamaged_fast_iff 21 _).mp hDm)

end ProteinFolding.Tetrahedral
