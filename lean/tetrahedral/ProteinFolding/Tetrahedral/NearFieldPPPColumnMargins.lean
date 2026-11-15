import ProteinFolding.Tetrahedral.NearFieldPPPEdgeColumns
import ProteinFolding.Tetrahedral.NearFieldBulkXRowClassification

/-! Face-value margins exclude the exceptional PPP middle-column owners
at ordinary inner edge sites, vertices, and small-face corners. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgeASecondRow_near_lower (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r < 2 * m - 1) (hA : InASublattice (octEdgeZigzag m F r).val) :
    tetraCoordinate m (edgeASecondRowOwner m F r).val F.j = -octRadius m + 4 := by
  have hbase : tetraCoordinate m (octEdgeZigzag m F r).val F.j = -octRadius m := by
    rcases octEdgeZigzag_mem hm F hr with h | h
    · exact h.2
    · exact (sublattices_disjoint _ hA h.1.2.1).elim
  unfold edgeASecondRowOwner
  rw [tetraCoordinate_step_B m (step_in_B hA F.j), tetraCoordinate_step_A m hA]
  simp only [if_neg F.jb, ite_true]
  omega

theorem edgeBSecondRow_near_upper (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r < 2 * m - 1) (hB : InBSublattice (octEdgeZigzag m F r).val) :
    tetraCoordinate m (edgeBSecondRowOwner m F r).val F.k = octRadius m - 5 := by
  have hbase : tetraCoordinate m (octEdgeZigzag m F r).val F.k = 2 * (m : ℤ) - 3 := by
    rcases octEdgeZigzag_mem hm F hr with h | h
    · exact (sublattices_disjoint _ h.1.2.1 hB).elim
    · exact h.2
  unfold edgeBSecondRowOwner
  rw [tetraCoordinate_step_A m (step_in_A hB F.k), tetraCoordinate_step_B m hB]
  simp only [if_neg F.ka, ite_true]
  dsimp [octRadius]
  omega

theorem inner_edge_A_no_near_lower (m : ℕ) (hm : 3 ≤ m) (G : OctEdgeFrame) (i : ℕ)
    (hilo : 4 ≤ i) (hihi : i + 4 ≤ 2 * m - 2)
    (hA : InASublattice (octEdgeZigzag m G i).val) (d : Fin 4) :
    tetraCoordinate m (octEdgeZigzag m G i).val d ≠ -octRadius m + 4 := by
  have hm1 : 1 ≤ m := by omega
  have hmod := edgeZigzag_A_even hm1 G i hA
  have hi : i = 2 * (i / 2) := by omega
  obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_even hm1 G (i / 2)
  intro heq
  rw [hi] at heq
  rcases G.index_cases d with rfl | rfl | rfl | rfl
  all_goals dsimp [octRadius] at heq hk hj ha hb
  all_goals omega

theorem inner_edge_B_no_near_upper (m : ℕ) (hm : 3 ≤ m) (G : OctEdgeFrame) (i : ℕ)
    (hilo : 4 ≤ i) (hihi : i + 4 ≤ 2 * m - 2)
    (hB : InBSublattice (octEdgeZigzag m G i).val) (d : Fin 4) :
    tetraCoordinate m (octEdgeZigzag m G i).val d ≠ octRadius m - 5 := by
  have hm1 : 1 ≤ m := by omega
  have hmod := edgeZigzag_B_odd hm1 G i hB
  have hi : i = 2 * (i / 2) + 1 := by omega
  obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_odd hm1 G (i / 2)
  intro heq
  rw [hi] at heq
  rcases G.index_cases d with rfl | rfl | rfl | rfl
  all_goals dsimp [octRadius] at heq hk hj ha hb
  all_goals omega

theorem vertex_no_near_lower (m : ℕ) (hm : 3 ≤ m) (a : Fin 3) (positive : Bool) (d : Fin 4) :
    tetraCoordinate m (octVertexSite m a positive).val d ≠ -octRadius m + 4 := by
  fin_cases a <;> cases positive <;> fin_cases d <;>
    dsimp [octVertexSite, octVertexCoordinates, octCentre, tetraCoordinate, octRadius] <;> omega

theorem Bcorner_no_near_upper (m : ℕ) (hm : 4 ≤ m) (G : OctEdgeFrame) (d : Fin 4) :
    tetraCoordinate m (octEdgeZigzag m G 1).val d ≠ octRadius m - 5 := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_odd hm1 G 0
  change tetraCoordinate m (octEdgeZigzag m G 1).val G.k = _ at hk
  change tetraCoordinate m (octEdgeZigzag m G 1).val G.j = _ at hj
  change tetraCoordinate m (octEdgeZigzag m G 1).val G.a = _ at ha
  change tetraCoordinate m (octEdgeZigzag m G 1).val G.b = _ at hb
  intro heq
  rcases G.index_cases d with rfl | rfl | rfl | rfl
  all_goals dsimp [octRadius] at heq hk hj ha hb
  all_goals omega

end ProteinFolding.Tetrahedral.NearField
