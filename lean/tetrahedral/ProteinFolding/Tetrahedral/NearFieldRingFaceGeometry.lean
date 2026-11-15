import ProteinFolding.Tetrahedral.NearFieldRingPPPSeparation

/-! Every retained side H site belongs to just one small face. In particular,
rings on different small faces have disjoint H intervals, including B corners. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem ringEdgePoint_small_coordinate (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (r : ℕ) : tetraCoordinate m (octEdgeZigzag m F r).val F.j ≤ -octRadius m := by
  have hmod : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hmod with h | h
  · have heq : r = 2 * (r / 2) := by omega
    have hx := (octEdgeZigzag_even (by omega : 1 ≤ m) F (r / 2)).2.2.1
    rw [← heq] at hx
    omega
  · have heq : r = 2 * (r / 2) + 1 := by omega
    have hx := (octEdgeZigzag_odd (by omega : 1 ≤ m) F (r / 2)).2.2.1
    rw [← heq] at hx
    omega

theorem ringEdgePoint_other_small_coordinate (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (r : ℕ) (hlo : 1 ≤ r) (hhi : r + 3 ≤ 2 * m - 1) (d : Fin 4) (hd : d ≠ F.j) :
    -octRadius m < tetraCoordinate m (octEdgeZigzag m F r).val d := by
  have hmod : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hmod with h | h
  · have heq : r = 2 * (r / 2) := by omega
    obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_even (by omega : 1 ≤ m) F (r / 2)
    rw [← heq] at hk hj ha hb
    rcases F.index_cases d with rfl | rfl | rfl | rfl
    · dsimp [octRadius] at *; omega
    · exact (hd rfl).elim
    · dsimp [octRadius] at *; omega
    · dsimp [octRadius] at *; omega
  · have heq : r = 2 * (r / 2) + 1 := by omega
    obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_odd (by omega : 1 ≤ m) F (r / 2)
    rw [← heq] at hk hj ha hb
    rcases F.index_cases d with rfl | rfl | rfl | rfl
    · dsimp [octRadius] at *; omega
    · exact (hd rfl).elim
    · dsimp [octRadius] at *; omega
    · dsimp [octRadius] at *; omega

theorem ringEdgePoint_ne_other_small_face (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (r s : ℕ) (hlo : 1 ≤ r) (hhi : r + 3 ≤ 2 * m - 1) (hj : F.j ≠ G.j) :
    octEdgeZigzag m F r ≠ octEdgeZigzag m G s := by
  intro heq
  have hlower := ringEdgePoint_other_small_coordinate m hm F r hlo hhi G.j hj.symm
  have hupper := ringEdgePoint_small_coordinate m hm G s
  rw [heq] at hlower
  omega

theorem ringSideFrame_small (F : OctEdgeFrame) (i : Fin 3) : (ringSideFrame F i).j = F.j := by
  fin_cases i <;> rfl

theorem ringSideHsites_disjoint_small_faces (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hj : F.j ≠ G.j) (i j : Fin 3) :
    Disjoint (edgeDimerHsites m (ringSideFrame F i) 1 (m - 3))
      (edgeDimerHsites m (ringSideFrame G j) 1 (m - 3)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hq
  have hr := r.isLt
  have hpair : (ringSideFrame F i).j ≠ (ringSideFrame G j).j := by
    simpa only [ringSideFrame_small] using hj
  exact ringEdgePoint_ne_other_small_face m hm _ _ _ _ (by omega) (by omega) hpair hs.symm

end ProteinFolding.Tetrahedral.NearField
