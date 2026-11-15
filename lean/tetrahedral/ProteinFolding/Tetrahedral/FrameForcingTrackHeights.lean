import ProteinFolding.Tetrahedral.OctahedralTriangleSteps
import ProteinFolding.Tetrahedral.OctahedralEdgeParametrization

/-! Coordinate-independent versions of the two Section 7 track heights.
They avoid choosing a global orientation of the forced frame. -/

namespace ProteinFolding.Tetrahedral

def frameH2 (m : ℕ) (F : OctEdgeFrame) (p : Site) : ℤ :=
  tetraCoordinate m p.val F.a + tetraCoordinate m p.val F.b

def frameK2 (m : ℕ) (F : OctEdgeFrame) (p : Site) : ℤ :=
  tetraCoordinate m p.val F.a + tetraCoordinate m p.val F.j

theorem entry_edge_height_data (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) :
    0 ≤ frameH2 m F (octEdgeZigzag m F r) ∧ frameH2 m F (octEdgeZigzag m F r) ≤ 2 ∧
      frameK2 m F (octEdgeZigzag m F r) = -2 * octRadius m + 2 * (r : ℤ) := by
  have hmod := Nat.mod_lt r (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div r 2
  by_cases heven : r % 2 = 0
  · have hr : r = 2 * (r / 2) := by omega
    rw [hr]
    obtain ⟨_, _, hj, ha, hb⟩ := octEdgeZigzag_even hm F (r / 2)
    simp only [frameH2, frameK2, hj, ha, hb]
    push_cast
    omega
  · have hr : r = 2 * (r / 2) + 1 := by omega
    rw [hr]
    obtain ⟨_, _, hj, ha, hb⟩ := octEdgeZigzag_odd hm F (r / 2)
    simp only [frameH2, frameK2, hj, ha, hb]
    push_cast
    omega

theorem track_edge_height_data (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) :
    frameH2 m F (octEdgeZigzag m F.smallOtherSide r) = 2 * (r : ℤ) ∧
      frameK2 m F (octEdgeZigzag m F.smallOtherSide r) = -2 * octRadius m + 2 * (r : ℤ) := by
  have hmod := Nat.mod_lt r (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div r 2
  by_cases heven : r % 2 = 0
  · have hr : r = 2 * (r / 2) := by omega
    rw [hr]
    obtain ⟨_, hk, hj, ha, _⟩ := octEdgeZigzag_even hm F.smallOtherSide (r / 2)
    change tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * (r / 2))).val F.b = _ at hk
    change tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * (r / 2))).val F.j = _ at hj
    change tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * (r / 2))).val F.a = _ at ha
    simp only [frameH2, frameK2, hk, hj, ha]
    push_cast
    omega
  · have hr : r = 2 * (r / 2) + 1 := by omega
    rw [hr]
    obtain ⟨_, hk, hj, ha, _⟩ := octEdgeZigzag_odd hm F.smallOtherSide (r / 2)
    change tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * (r / 2) + 1)).val F.b = _ at hk
    change tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * (r / 2) + 1)).val F.j = _ at hj
    change tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * (r / 2) + 1)).val F.a = _ at ha
    simp only [frameH2, frameK2, hk, hj, ha]
    push_cast
    omega

theorem intended_exit_height_data (m : ℕ) (hm : 1 ≤ m) (F G : OctEdgeFrame)
    (hk : G.k = F.a) (hj : G.j = F.j) (ha : G.a = F.b) (r : ℕ) :
    frameH2 m F (octEdgeZigzag m G r) = 2 * (r : ℤ) ∧
      -2 ≤ frameK2 m F (octEdgeZigzag m G r) ∧ frameK2 m F (octEdgeZigzag m G r) ≤ 0 := by
  have hmod := Nat.mod_lt r (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div r 2
  by_cases heven : r % 2 = 0
  · have hr : r = 2 * (r / 2) := by omega
    rw [hr]
    obtain ⟨_, hgk, hgj, hga, _⟩ := octEdgeZigzag_even hm G (r / 2)
    rw [hk] at hgk
    rw [hj] at hgj
    rw [ha] at hga
    simp only [frameH2, frameK2, hgk, hgj, hga]
    push_cast
    omega
  · have hr : r = 2 * (r / 2) + 1 := by omega
    rw [hr]
    obtain ⟨_, hgk, hgj, hga, _⟩ := octEdgeZigzag_odd hm G (r / 2)
    rw [hk] at hgk
    rw [hj] at hgj
    rw [ha] at hga
    simp only [frameH2, frameK2, hgk, hgj, hga]
    push_cast
    omega

theorem two_face_height_adj_bounds (m : ℕ) {a b : Fin 4} (hab : a ≠ b) {p q : Site}
    (hadj : tetrahedralLattice.Adj p q) :
    -2 ≤ (tetraCoordinate m q.val a + tetraCoordinate m q.val b) -
      (tetraCoordinate m p.val a + tetraCoordinate m p.val b) ∧
    (tetraCoordinate m q.val a + tetraCoordinate m q.val b) -
      (tetraCoordinate m p.val a + tetraCoordinate m p.val b) ≤ 2 := by
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp hadj
  rcases p.property with hp | hp
  · rw [tetraCoordinate_step_A m hp, tetraCoordinate_step_A m hp]
    split_ifs <;> omega
  · rw [tetraCoordinate_step_B m hp, tetraCoordinate_step_B m hp]
    split_ifs <;> omega

end ProteinFolding.Tetrahedral
