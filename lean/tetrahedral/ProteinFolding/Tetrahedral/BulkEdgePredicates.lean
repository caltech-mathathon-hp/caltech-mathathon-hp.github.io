import ProteinFolding.Tetrahedral.BulkEdgeLocality

/-! Colours, edges and dangling directions in uniformly translated edge boxes. -/

namespace ProteinFolding.Tetrahedral

theorem bulkEdgeReanchor_adj_iff (m M t T : ℕ) (F : OctEdgeFrame) (p q : Site) :
    tetrahedralLattice.Adj (bulkEdgeReanchor m M t T F p) (bulkEdgeReanchor m M t T F q) ↔
      tetrahedralLattice.Adj p q :=
  adj_shift_iff (bulkEdgeDelta m M t T F) (bulkEdgeDelta_inA m M t T F) p q

theorem bulkEdgeReanchor_injective (m M t T : ℕ) (F : OctEdgeFrame) :
    Function.Injective (bulkEdgeReanchor m M t T F) :=
  shiftSite_injective (bulkEdgeDelta m M t T F) (bulkEdgeDelta_inA m M t T F)

theorem bulkEdgeReanchor_inverse (m M t T : ℕ) (F : OctEdgeFrame) (p : Site) :
    bulkEdgeReanchor M m T t F (bulkEdgeReanchor m M t T F p) = p := by
  apply Subtype.ext
  funext k
  rw [bulkEdgeReanchor_coordinates, bulkEdgeReanchor_coordinates]
  omega

theorem bulkEdgeReanchor_inA_iff (m M t T : ℕ) (F : OctEdgeFrame) (p : Site) :
    InASublattice (bulkEdgeReanchor m M t T F p).val ↔ InASublattice p.val := by
  rw [inA_iff_x_even, inA_iff_x_even]
  have hd := (bulkEdgeDelta_inA m M t T F).1 0
  change (p.val 0 - (bulkEdgeDelta m M t T F).val 0) % 2 = 0 ↔ p.val 0 % 2 = 0
  omega

theorem bulkEdgeReanchor_inB_iff (m M t T : ℕ) (F : OctEdgeFrame) (p : Site) :
    InBSublattice (bulkEdgeReanchor m M t T F p).val ↔ InBSublattice p.val := by
  rw [inB_iff_not_inA, inB_iff_not_inA, bulkEdgeReanchor_inA_iff]

theorem bulkEdgeReanchor_step (m M t T : ℕ) (F : OctEdgeFrame) (p : Site) (d : Fin 4) :
    bulkEdgeReanchor m M t T F (step p d) = step (bulkEdgeReanchor m M t T F p) d := by
  apply Subtype.ext
  funext k
  have hl := bulkEdgeReanchor_coordinates m M t T F (step p d) k
  have hr := bulkEdgeReanchor_coordinates m M t T F p k
  rcases p.property with hpA | hpB
  · have hqA := (bulkEdgeReanchor_inA_iff m M t T F p).mpr hpA
    rw [step_val_of_A p hpA d] at hl
    rw [step_val_of_A _ hqA d]
    dsimp only at hl ⊢
    omega
  · have hqB := (bulkEdgeReanchor_inB_iff m M t T F p).mpr hpB
    rw [step_val_of_B p hpB d] at hl
    rw [step_val_of_B _ hqB d]
    dsimp only at hl ⊢
    omega

theorem bulkEdgeReanchor_bigFace_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) (i : Fin 4) :
    OctBigFace M i (bulkEdgeReanchor m M t T F p) ↔ OctBigFace m i p := by
  have heq := bulkEdgeReanchor_face_eq_iff m M t T F D p ht htm hT hTM hp i 1 0 (Or.inl rfl) (by omega)
  simp only [one_mul, add_zero] at heq
  unfold OctBigFace
  rw [bulkEdgeReanchor_mem_octahedron_iff m M t T F D p ht htm hT hTM hp,
    bulkEdgeReanchor_inA_iff, heq]

theorem bulkEdgeReanchor_smallFace_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) (i : Fin 4) :
    OctSmallFace M i (bulkEdgeReanchor m M t T F p) ↔ OctSmallFace m i p := by
  have heq := bulkEdgeReanchor_face_eq_iff m M t T F D p ht htm hT hTM hp i (-1) 1 (Or.inr rfl) (by omega)
  have heq' : tetraCoordinate M (bulkEdgeReanchor m M t T F p).val i = -(2 * (M : ℤ) - 1) ↔
      tetraCoordinate m p.val i = -(2 * (m : ℤ) - 1) := by dsimp [octRadius] at heq; omega
  unfold OctSmallFace
  rw [bulkEdgeReanchor_mem_octahedron_iff m M t T F D p ht htm hT hTM hp,
    bulkEdgeReanchor_inB_iff, heq']

theorem bulkEdgeReanchor_edgeSite_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) (k j : Fin 4) :
    OctEdgeSite M k j (bulkEdgeReanchor m M t T F p) ↔ OctEdgeSite m k j p := by
  have hlow := bulkEdgeReanchor_face_eq_iff m M t T F D p ht htm hT hTM hp j (-1) 0 (Or.inr rfl) (by omega)
  have hhigh := bulkEdgeReanchor_face_eq_iff m M t T F D p ht htm hT hTM hp k 1 (-1) (Or.inl rfl) (by omega)
  have hlow' : tetraCoordinate M (bulkEdgeReanchor m M t T F p).val j = -octRadius M ↔
      tetraCoordinate m p.val j = -octRadius m := by omega
  have hhigh' : tetraCoordinate M (bulkEdgeReanchor m M t T F p).val k = 2 * (M : ℤ) - 3 ↔
      tetraCoordinate m p.val k = 2 * (m : ℤ) - 3 := by dsimp [octRadius] at hhigh; omega
  unfold OctEdgeSite OctAEdgeSite OctBEdgeSite
  rw [bulkEdgeReanchor_bigFace_iff m M t T F D p ht htm hT hTM hp,
    bulkEdgeReanchor_smallFace_iff m M t T F D p ht htm hT hTM hp, hlow', hhigh']

theorem bulkEdgeReanchor_deleted_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    bulkEdgeReanchor m M t T F p ∈ bulkDeletedEdges M ↔ p ∈ bulkDeletedEdges m := by
  have hon : bulkOnDeletedEdge M (bulkEdgeReanchor m M t T F p) ↔ bulkOnDeletedEdge m p := by
    unfold bulkOnDeletedEdge
    apply exists_congr
    intro k
    apply exists_congr
    intro j
    exact and_congr_right (fun _ => bulkEdgeReanchor_edgeSite_iff m M t T F D p ht htm hT hTM hp k j)
  simp only [bulkDeletedEdges, Finset.mem_filter, hon,
    bulkEdgeReanchor_mem_octahedron_iff m M t T F D p ht htm hT hTM hp]

theorem bulkEdgeReanchor_interior_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    bulkEdgeReanchor m M t T F p ∈ bulkInterior M ↔ p ∈ bulkInterior m := by
  simp only [bulkInterior, Finset.mem_sdiff,
    bulkEdgeReanchor_mem_octahedron_iff m M t T F D p ht htm hT hTM hp,
    bulkEdgeReanchor_deleted_iff m M t T F D p ht htm hT hTM hp]

theorem bulk_adjacent_in_edge_box (m : ℕ) (F : OctEdgeFrame) (t D : ℕ) {p q : Site}
    (hp : InBulkEdgeBox m F t D p) (h : tetrahedralLattice.Adj p q) : InBulkEdgeBox m F t (D + 1) q := by
  intro k
  have hb := abs_le.mp (hp k)
  have hd := adj_coordinate h k
  apply abs_le.mpr
  constructor <;> omega

theorem bulkEdgeReanchor_danglingDirections_eq (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 3 ≤ t) (htm : t + D + 4 ≤ m) (hT : D + 3 ≤ T) (hTM : T + D + 4 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    octDanglingDirections M (bulkEdgeReanchor m M t T F p) = octDanglingDirections m p := by
  ext d
  simp only [octDanglingDirections, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← bulkEdgeReanchor_step]
  exact not_congr (bulkEdgeReanchor_mem_octahedron_iff m M t T F (D + 1) (step p d)
    (by omega) (by omega) (by omega) (by omega) (bulk_adjacent_in_edge_box m F t D hp (step_adj p d)))

end ProteinFolding.Tetrahedral
