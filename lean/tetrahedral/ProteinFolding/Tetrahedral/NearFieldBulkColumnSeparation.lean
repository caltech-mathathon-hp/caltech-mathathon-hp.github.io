import ProteinFolding.Tetrahedral.NearFieldTethersBulkColumns

/-! Endpoint columns cannot coincide with any tether's canonical or borrowed
column. Canonical tether owners are deleted edge sites; borrowed owners
belong to the second row, where the actual bulk graph has degree two. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem column_owner_eq_of_seed_eq {m : ℕ} (C D : DanglingColumn m) (hseed : C.seed = D.seed) :
    C.owner = D.owner := by
  have h := outside_step_unique_inside m C.owner_mem C.dir C.seed_outside
    (r := D.owner) (by change tetrahedralLattice.Adj C.seed D.owner; rw [hseed]; exact (step_adj _ _).symm)
    D.owner_mem
  exact h.symm

theorem faceColumn_zero_a_owner_deleted (m b c : ℕ) (hs : 0 + b + c + 2 = m) :
    (faceDanglingColumn m 0 b c hs).owner ∈ bulkDeletedEdges m := by
  have hp := (faceDanglingColumn m 0 b c hs).owner_mem
  apply Finset.mem_filter.mpr
  refine ⟨hp, 0, 3, by decide, Or.inr ⟨⟨hp, faceSurfaceCoordinates_inB m 0 0 b c hs, ?_⟩, ?_⟩⟩
  · change tetraCoordinate m (faceSurfaceSite m 0 0 b c hs).val 3 = _
    rw [tetraCoordinate_faceSurface]
    rfl
  · change tetraCoordinate m (faceSurfaceSite m 0 0 b c hs).val 0 = _
    rw [tetraCoordinate_faceSurface]
    dsimp [octRadius]
    omega

theorem faceColumn_zero_b_owner_deleted (m a c : ℕ) (hs : a + 0 + c + 2 = m) :
    (faceDanglingColumn m a 0 c hs).owner ∈ bulkDeletedEdges m := by
  have hp := (faceDanglingColumn m a 0 c hs).owner_mem
  apply Finset.mem_filter.mpr
  refine ⟨hp, 1, 3, by decide, Or.inr ⟨⟨hp, faceSurfaceCoordinates_inB m 0 a 0 c hs, ?_⟩, ?_⟩⟩
  · change tetraCoordinate m (faceSurfaceSite m 0 a 0 c hs).val 3 = _
    rw [tetraCoordinate_faceSurface]
    rfl
  · change tetraCoordinate m (faceSurfaceSite m 0 a 0 c hs).val 1 = _
    rw [tetraCoordinate_faceSurface]
    dsimp [octRadius]
    omega

theorem bulkColumn_ne_edgeColumn {m : ℕ} (C D : DanglingColumn m)
    (hC : C.owner ∈ bulkInterior m) (hD : D.owner ∈ bulkDeletedEdges m) (n r : ℕ) :
    C.point n ≠ D.point r := by
  intro heq
  have howners := column_owner_eq_of_seed_eq C D (DanglingColumn.seeds_eq_of_point_eq C D heq)
  exact (Finset.mem_sdiff.mp hC).2 (howners ▸ hD)

theorem bulkEndColumn_ne_secondRowColumn (m : ℕ) (hm : 30 ≤ m) (C : DanglingColumn m)
    (hC : C.owner ∈ bulkInterior m) (hend : (bulkCoverNeighbours m C.owner).card = 1)
    (a b : ℕ) (hs : a + b + 1 + 2 = m) (n r : ℕ) :
    C.point n ≠ (faceDanglingColumn m a b 1 hs).point r := by
  intro heq
  have howners := column_owner_eq_of_seed_eq C _ (DanglingColumn.seeds_eq_of_point_eq C _ heq)
  rw [howners] at hC hend
  have hdegree := bulk_secondRow_degree m hm a b hs hC
  exact (by decide : (2 : ℕ) ≠ 1) (hdegree.symm.trans hend)

theorem entryUp_ne_bulkEndColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1)
    (i : Fin (2 * p.entrySkin k - 1)) (n : ℕ) : (entryUp p k hk).pos i ≠ C.point n := by
  change borrowedPoint p.side (entryAnchorA p k) (3 * (k + 1)) 0
    (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) i.val ≠ C.point n
  cases hidx : i.val with
  | zero =>
    simp only [borrowedPoint]
    exact (bulkColumn_ne_edgeColumn C _ hC
      (faceColumn_zero_c_owner_deleted _ _ _ (entryAnchor_equation p k hk)) n 0).symm
  | succ r =>
    simp only [borrowedPoint]
    exact (bulkEndColumn_ne_secondRowColumn p.side (by have h := p.side_ge; omega) C hC hend
      (entryAnchorA p k - 1) (3 * (k + 1))
      (by have h := entryAnchor_equation p k hk; have ha := entryAnchor_positive p k hk; omega) n (r + 1)).symm

end ProteinFolding.Tetrahedral.NearField
