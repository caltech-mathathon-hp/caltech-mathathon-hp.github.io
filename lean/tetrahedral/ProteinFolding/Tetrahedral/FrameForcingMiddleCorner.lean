import ProteinFolding.Tetrahedral.FrameForcingSeparatorBridge
import Mathlib.Tactic.ClearExcept

/-! The shared small-face corner next to the middle frame vertex has
exactly the three occupied frame sites as neighbours inside Oct. -/

namespace ProteinFolding.Tetrahedral

theorem end_corner_faces (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    InBSublattice (octEdgeZigzag m F (2 * m - 3)).val ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * m - 3)).val F.k = octRadius m - 1 ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * m - 3)).val F.j = -octRadius m - 1 ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * m - 3)).val F.a = octRadius m - 1 ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * m - 3)).val F.b = -octRadius m + 3 := by
  obtain ⟨hpB, hk, hj, ha, hb⟩ := octEdgeZigzag_odd (by omega : 1 ≤ m) F (m - 2)
  have hindex : 2 * (m - 2) + 1 = 2 * m - 3 := by omega
  rw [hindex] at hpB hk hj ha hb
  refine ⟨hpB, hk, hj, ?_, ?_⟩ <;> dsimp [octRadius] at * <;> omega

theorem shared_middle_corner_eq (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hk : G.k = F.a) (hj : G.j = F.j) (ha : G.a = F.b) (hb : G.b = F.k) :
    octEdgeZigzag m F (2 * m - 3) = octEdgeZigzag m G 1 := by
  have hC := end_corner_faces m hm F
  have hG := octEdgeZigzag_odd (by omega : 1 ≤ m) G 0
  have hGk : tetraCoordinate m (octEdgeZigzag m G 1).val F.k = octRadius m - 1 := by
    rw [← hb]; simpa using hG.2.2.2.2
  have hGj : tetraCoordinate m (octEdgeZigzag m G 1).val F.j = -octRadius m - 1 := by
    rw [← hj]; exact hG.2.2.1
  have hGa : tetraCoordinate m (octEdgeZigzag m G 1).val F.a = octRadius m - 1 := by
    rw [← hk]; exact hG.2.1
  have hGb : tetraCoordinate m (octEdgeZigzag m G 1).val F.b = -octRadius m + 3 := by
    rw [← ha]; simpa using hG.2.2.2.1
  apply Subtype.ext
  apply tetraCoordinate_injective m
  funext d
  rcases F.index_cases d with rfl | rfl | rfl | rfl <;> omega

theorem shared_middle_corner_neighbours_of_bound (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hk : G.k = F.a) (hj : G.j = F.j) (ha : G.a = F.b) (hb : G.b = F.k)
    (q : Site) (hlower : -octRadius m - 1 ≤ tetraCoordinate m q.val F.j)
    (hadj : tetrahedralLattice.Adj (octEdgeZigzag m F (2 * m - 3)) q) :
    q = octEdgeZigzag m F (2 * m - 2) ∨
      q = octEdgeZigzag m F (2 * m - 4) ∨ q = octEdgeZigzag m G 2 := by
  have hm1 : 1 ≤ m := by omega
  have hC := end_corner_faces m hm F
  have hCk := hC.2.1
  have hCj := hC.2.2.1
  have hCa := hC.2.2.2.1
  have hCb := hC.2.2.2.2
  have hEnd := octEdgeEnd_faces m hm1 F
  have hIn := octEdgeZigzag_even hm1 F (m - 2)
  have hInIndex : 2 * (m - 2) = 2 * m - 4 := by omega
  rw [hInIndex] at hIn
  have hOut := octEdgeZigzag_even hm1 G 1
  have hOutk : tetraCoordinate m (octEdgeZigzag m G 2).val F.k = octRadius m - 4 := by
    rw [← hb]; simpa using hOut.2.2.2.2
  have hOutj : tetraCoordinate m (octEdgeZigzag m G 2).val F.j = -octRadius m := by
    rw [← hj]; exact hOut.2.2.1
  have hOuta : tetraCoordinate m (octEdgeZigzag m G 2).val F.a = octRadius m := by
    rw [← hk]; exact hOut.2.1
  have hOutb : tetraCoordinate m (octEdgeZigzag m G 2).val F.b = -octRadius m + 4 := by
    rw [← ha]; simpa using hOut.2.2.2.1
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step _ q).mp hadj
  rcases F.index_cases d with rfl | rfl | rfl | rfl
  · right; right
    apply Subtype.ext
    apply tetraCoordinate_injective m
    funext d
    rcases F.index_cases d with rfl | rfl | rfl | rfl
    all_goals rw [tetraCoordinate_step_B m hC.1]
    all_goals simp only [Ne.symm F.kj, Ne.symm F.ka, Ne.symm F.kb, ↓reduceIte]
    all_goals clear * - hCk hCj hCa hCb hOutk hOutj hOuta hOutb
    all_goals omega
  · have hbound := hlower
    rw [tetraCoordinate_step_B m hC.1, if_pos rfl] at hbound
    clear * - hbound hCj
    dsimp [octRadius] at hbound hCj
    omega
  · right; left
    apply Subtype.ext
    apply tetraCoordinate_injective m
    funext d
    rcases F.index_cases d with rfl | rfl | rfl | rfl
    all_goals rw [tetraCoordinate_step_B m hC.1]
    all_goals simp only [F.ka, F.ja, Ne.symm F.ab, ↓reduceIte]
    all_goals clear * - hCk hCj hCa hCb hIn hm
    all_goals dsimp [octRadius] at hCk hCj hCa hCb hIn
    all_goals omega
  · left
    apply Subtype.ext
    apply tetraCoordinate_injective m
    funext d
    rcases F.index_cases d with rfl | rfl | rfl | rfl
    all_goals rw [tetraCoordinate_step_B m hC.1]
    all_goals simp only [F.kb, F.jb, F.ab, ↓reduceIte]
    all_goals clear * - hCk hCj hCa hCb hEnd
    all_goals omega

theorem shared_middle_corner_neighbours (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hk : G.k = F.a) (hj : G.j = F.j) (ha : G.a = F.b) (hb : G.b = F.k)
    (q : Site) (hq : q ∈ octahedron m)
    (hadj : tetrahedralLattice.Adj (octEdgeZigzag m F (2 * m - 3)) q) :
    q = octEdgeZigzag m F (2 * m - 2) ∨
      q = octEdgeZigzag m F (2 * m - 4) ∨ q = octEdgeZigzag m G 2 :=
  shared_middle_corner_neighbours_of_bound m hm F G hk hj ha hb q
    (by
      have h := ((mem_octahedron m q).mp hq F.j).1
      have heq : -octRadius m - 1 = -(2 * (m : ℤ) - 1) := by dsimp [octRadius]; omega
      rw [heq]
      exact h) hadj

end ProteinFolding.Tetrahedral
