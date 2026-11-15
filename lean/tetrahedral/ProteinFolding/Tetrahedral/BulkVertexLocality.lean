import ProteinFolding.Tetrahedral.BulkMergedDegree
import ProteinFolding.Tetrahedral.GapGeometry

/-! Uniform translation of bounded vertex neighbourhoods between octahedral sizes. -/

namespace ProteinFolding.Tetrahedral

def bulkVertexDelta (m n : ℕ) (v : Fin 6) : Site :=
  shiftSite (bulkPatchVertex n v) (bulkPatch_vertex_inA n v) (bulkPatchVertex m v)

theorem bulkVertexDelta_inA (m n : ℕ) (v : Fin 6) : InASublattice (bulkVertexDelta m n v).val :=
  sub_A_A (bulkPatch_vertex_inA m v) (bulkPatch_vertex_inA n v)

def bulkReanchorSite (m n : ℕ) (v : Fin 6) (p : Site) : Site :=
  shiftSite (bulkVertexDelta m n v) (bulkVertexDelta_inA m n v) p

theorem bulkReanchorSite_coordinates (m n : ℕ) (v : Fin 6) (p : Site) (k : Fin 3) :
    (bulkReanchorSite m n v p).val k =
      p.val k - (bulkPatchVertex m v).val k + (bulkPatchVertex n v).val k := by
  change p.val k - ((bulkPatchVertex m v).val k - (bulkPatchVertex n v).val k) = _
  omega

theorem bulkReanchorSite_adj_iff (m n : ℕ) (v : Fin 6) (p q : Site) :
    tetrahedralLattice.Adj (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) ↔
      tetrahedralLattice.Adj p q :=
  adj_shift_iff (bulkVertexDelta m n v) (bulkVertexDelta_inA m n v) p q

theorem bulkReanchorSite_injective (m n : ℕ) (v : Fin 6) :
    Function.Injective (bulkReanchorSite m n v) :=
  shiftSite_injective (bulkVertexDelta m n v) (bulkVertexDelta_inA m n v)

def InBulkVertexBox (m : ℕ) (v : Fin 6) (D : ℕ) (p : Site) : Prop :=
  ∀ k : Fin 3, |p.val k - (bulkPatchVertex m v).val k| ≤ (D : ℤ)

theorem bulkReanchorSite_in_box (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hp : InBulkVertexBox m v D p) : InBulkVertexBox n v D (bulkReanchorSite m n v p) := by
  intro k
  rw [bulkReanchorSite_coordinates]
  have heq : p.val k - (bulkPatchVertex m v).val k + (bulkPatchVertex n v).val k -
      (bulkPatchVertex n v).val k = p.val k - (bulkPatchVertex m v).val k := by omega
  rw [heq]
  exact hp k

set_option maxHeartbeats 1200000 in
theorem bulkReanchor_face_le_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p)
    (i : Fin 4) (s c : ℤ) (hs : s = 1 ∨ s = -1) (hc : -2 ≤ c ∧ c ≤ 2) :
    s * tetraCoordinate n (bulkReanchorSite m n v p).val i ≤ octRadius n + c ↔
      s * tetraCoordinate m p.val i ≤ octRadius m + c := by
  have hx := abs_le.mp (hp 0)
  have hy := abs_le.mp (hp 1)
  have hz := abs_le.mp (hp 2)
  have ht0 := bulkReanchorSite_coordinates m n v p 0
  have ht1 := bulkReanchorSite_coordinates m n v p 1
  have ht2 := bulkReanchorSite_coordinates m n v p 2
  rcases hs with rfl | rfl
  all_goals fin_cases v <;> fin_cases i
  all_goals dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre,
    octRadius, tetraCoordinate] at hx hy hz ht0 ht1 ht2 ⊢
  all_goals omega

theorem bulkReanchor_face_eq_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p)
    (i : Fin 4) (s c : ℤ) (hs : s = 1 ∨ s = -1) (hc : -1 ≤ c ∧ c ≤ 2) :
    s * tetraCoordinate n (bulkReanchorSite m n v p).val i = octRadius n + c ↔
      s * tetraCoordinate m p.val i = octRadius m + c := by
  have hle := bulkReanchor_face_le_iff m n v D p hm hn hp i s c hs (by omega)
  have hlt := bulkReanchor_face_le_iff m n v D p hm hn hp i s (c - 1) hs (by omega)
  omega

theorem bulkReanchor_mem_octahedron_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) :
    bulkReanchorSite m n v p ∈ octahedron n ↔ p ∈ octahedron m := by
  rw [mem_octahedron, mem_octahedron]
  unfold InOctahedron
  have hle := fun i => bulkReanchor_face_le_iff m n v D p hm hn hp i 1 0 (Or.inl rfl) (by omega)
  have hge := fun i => bulkReanchor_face_le_iff m n v D p hm hn hp i (-1) 1 (Or.inr rfl) (by omega)
  constructor
  · intro h i
    have hi := h i
    have hlo := hge i
    have hup := hle i
    dsimp [octRadius] at hi hlo hup ⊢
    omega
  · intro h i
    have hi := h i
    have hlo := hge i
    have hup := hle i
    dsimp [octRadius] at hi hlo hup ⊢
    omega

theorem bulkReanchor_inA_iff (m n : ℕ) (v : Fin 6) (p : Site) :
    InASublattice (bulkReanchorSite m n v p).val ↔ InASublattice p.val := by
  rw [inA_iff_x_even, inA_iff_x_even]
  have hd := (bulkVertexDelta_inA m n v).1 0
  change (p.val 0 - (bulkVertexDelta m n v).val 0) % 2 = 0 ↔ p.val 0 % 2 = 0
  omega

theorem bulkReanchor_inB_iff (m n : ℕ) (v : Fin 6) (p : Site) :
    InBSublattice (bulkReanchorSite m n v p).val ↔ InBSublattice p.val := by
  rw [inB_iff_not_inA, inB_iff_not_inA, bulkReanchor_inA_iff]

theorem bulkReanchor_bigFace_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) (i : Fin 4) :
    OctBigFace n i (bulkReanchorSite m n v p) ↔ OctBigFace m i p := by
  have heq := bulkReanchor_face_eq_iff m n v D p hm hn hp i 1 0 (Or.inl rfl) (by omega)
  simp only [one_mul, add_zero] at heq
  unfold OctBigFace
  rw [bulkReanchor_mem_octahedron_iff m n v D p hm hn hp, bulkReanchor_inA_iff, heq]

theorem bulkReanchor_smallFace_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) (i : Fin 4) :
    OctSmallFace n i (bulkReanchorSite m n v p) ↔ OctSmallFace m i p := by
  have heq := bulkReanchor_face_eq_iff m n v D p hm hn hp i (-1) 1 (Or.inr rfl) (by omega)
  have heq' : tetraCoordinate n (bulkReanchorSite m n v p).val i = -(2 * (n : ℤ) - 1) ↔
      tetraCoordinate m p.val i = -(2 * (m : ℤ) - 1) := by
    dsimp [octRadius] at heq
    omega
  unfold OctSmallFace
  rw [bulkReanchor_mem_octahedron_iff m n v D p hm hn hp, bulkReanchor_inB_iff, heq']

theorem bulkReanchor_edgeSite_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) (k j : Fin 4) :
    OctEdgeSite n k j (bulkReanchorSite m n v p) ↔ OctEdgeSite m k j p := by
  have hlow := bulkReanchor_face_eq_iff m n v D p hm hn hp j (-1) 0 (Or.inr rfl) (by omega)
  have hhigh := bulkReanchor_face_eq_iff m n v D p hm hn hp k 1 (-1) (Or.inl rfl) (by omega)
  have hlow' : tetraCoordinate n (bulkReanchorSite m n v p).val j = -octRadius n ↔
      tetraCoordinate m p.val j = -octRadius m := by omega
  have hhigh' : tetraCoordinate n (bulkReanchorSite m n v p).val k = 2 * (n : ℤ) - 3 ↔
      tetraCoordinate m p.val k = 2 * (m : ℤ) - 3 := by dsimp [octRadius] at hhigh; omega
  unfold OctEdgeSite OctAEdgeSite OctBEdgeSite
  rw [bulkReanchor_bigFace_iff m n v D p hm hn hp,
    bulkReanchor_smallFace_iff m n v D p hm hn hp, hlow', hhigh']

theorem bulkReanchor_deleted_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) :
    bulkReanchorSite m n v p ∈ bulkDeletedEdges n ↔ p ∈ bulkDeletedEdges m := by
  have hon : bulkOnDeletedEdge n (bulkReanchorSite m n v p) ↔ bulkOnDeletedEdge m p := by
    unfold bulkOnDeletedEdge
    apply exists_congr
    intro k
    apply exists_congr
    intro j
    exact and_congr_right (fun _ => bulkReanchor_edgeSite_iff m n v D p hm hn hp k j)
  simp only [bulkDeletedEdges, Finset.mem_filter, hon,
    bulkReanchor_mem_octahedron_iff m n v D p hm hn hp]

theorem bulkReanchor_interior_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) :
    bulkReanchorSite m n v p ∈ bulkInterior n ↔ p ∈ bulkInterior m := by
  simp only [bulkInterior, Finset.mem_sdiff,
    bulkReanchor_mem_octahedron_iff m n v D p hm hn hp,
    bulkReanchor_deleted_iff m n v D p hm hn hp]

theorem bulkReanchorSite_step (m n : ℕ) (v : Fin 6) (p : Site) (d : Fin 4) :
    bulkReanchorSite m n v (step p d) = step (bulkReanchorSite m n v p) d := by
  apply Subtype.ext
  funext k
  have hl := bulkReanchorSite_coordinates m n v (step p d) k
  have hr := bulkReanchorSite_coordinates m n v p k
  rcases p.property with hpA | hpB
  · have hqA := (bulkReanchor_inA_iff m n v p).mpr hpA
    rw [step_val_of_A p hpA d] at hl
    rw [step_val_of_A _ hqA d]
    dsimp only at hl ⊢
    omega
  · have hqB := (bulkReanchor_inB_iff m n v p).mpr hpB
    rw [step_val_of_B p hpB d] at hl
    rw [step_val_of_B _ hqB d]
    dsimp only at hl ⊢
    omega

theorem bulk_adjacent_in_vertex_box (m : ℕ) (v : Fin 6) (D : ℕ) {p q : Site}
    (hp : InBulkVertexBox m v D p) (h : tetrahedralLattice.Adj p q) :
    InBulkVertexBox m v (D + 1) q := by
  intro k
  have hb := abs_le.mp (hp k)
  have hd := adj_coordinate h k
  apply abs_le.mpr
  constructor <;> omega

theorem bulkReanchor_danglingDirections_eq (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 3 ≤ m) (hn : D + 3 ≤ n) (hp : InBulkVertexBox m v D p) :
    octDanglingDirections n (bulkReanchorSite m n v p) = octDanglingDirections m p := by
  ext d
  simp only [octDanglingDirections, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← bulkReanchorSite_step]
  exact not_congr (bulkReanchor_mem_octahedron_iff m n v (D + 1) (step p d)
    (by omega) (by omega) (bulk_adjacent_in_vertex_box m v D hp (step_adj p d)))

theorem bulkReanchor_surface_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 3 ≤ m) (hn : D + 3 ≤ n) (hp : InBulkVertexBox m v D p) :
    OctSurfaceSite n (bulkReanchorSite m n v p) ↔ OctSurfaceSite m p := by
  unfold OctSurfaceSite
  rw [bulkReanchor_mem_octahedron_iff m n v D p (by omega) (by omega) hp,
    bulkReanchor_danglingDirections_eq m n v D p hm hn hp]

end ProteinFolding.Tetrahedral
