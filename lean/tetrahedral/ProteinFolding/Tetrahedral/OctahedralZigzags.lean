import ProteinFolding.Tetrahedral.OctahedralGeodesic
import Mathlib.Algebra.BigOperators.Fin

/-! Exact finite parametrisations of the twelve octahedral edge zigzags. -/

namespace ProteinFolding.Tetrahedral

structure OctEdgeFrame where
  k : Fin 4
  j : Fin 4
  a : Fin 4
  b : Fin 4
  kj : k ≠ j
  ka : k ≠ a
  kb : k ≠ b
  ja : j ≠ a
  jb : j ≠ b
  ab : a ≠ b

theorem OctEdgeFrame.all_indices (F : OctEdgeFrame) :
    ({F.k, F.j, F.a, F.b} : Finset (Fin 4)) = Finset.univ := by
  apply Finset.eq_univ_of_card
  simp [F.kj, F.ka, F.kb, F.ja, F.jb, F.ab]

theorem OctEdgeFrame.index_cases (F : OctEdgeFrame) (i : Fin 4) :
    i = F.k ∨ i = F.j ∨ i = F.a ∨ i = F.b := by
  have h : i ∈ ({F.k, F.j, F.a, F.b} : Finset (Fin 4)) := by
    rw [F.all_indices]
    exact Finset.mem_univ _
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h

theorem tetraCoordinate_sum_frame (m : ℕ) (F : OctEdgeFrame) (p : Coordinates) :
    tetraCoordinate m p F.k + tetraCoordinate m p F.j +
      tetraCoordinate m p F.a + tetraCoordinate m p F.b = 0 := by
  have hsum : (∑ i : Fin 4, tetraCoordinate m p i) = 0 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    have h := tetraCoordinate_sum m p
    change tetraCoordinate m p 0 + (tetraCoordinate m p 1 +
      (tetraCoordinate m p 2 + (tetraCoordinate m p 3 + 0))) = 0
    omega
  rw [← F.all_indices] at hsum
  simpa [F.kj, F.ka, F.kb, F.ja, F.jb, F.ab, add_assoc] using hsum

def octVertexForFaces (m : ℕ) (k b : Fin 4) : Site :=
  if (k = 0 ∧ b = 1) ∨ (k = 1 ∧ b = 0) then octVertexSite m 0 true
  else if (k = 0 ∧ b = 2) ∨ (k = 2 ∧ b = 0) then octVertexSite m 1 true
  else if (k = 0 ∧ b = 3) ∨ (k = 3 ∧ b = 0) then octVertexSite m 2 true
  else if (k = 1 ∧ b = 2) ∨ (k = 2 ∧ b = 1) then octVertexSite m 2 false
  else if (k = 1 ∧ b = 3) ∨ (k = 3 ∧ b = 1) then octVertexSite m 1 false
  else octVertexSite m 0 false

theorem octVertexForFaces_mem (m : ℕ) (k b : Fin 4) :
    octVertexForFaces m k b ∈ octVertices m := by
  unfold octVertexForFaces
  split_ifs <;> exact Finset.mem_image.mpr ⟨(_, _), Finset.mem_univ _, rfl⟩

theorem octVertexForFaces_faces (m : ℕ) {k b : Fin 4} (hkb : k ≠ b) :
    tetraCoordinate m (octVertexForFaces m k b).val k = octRadius m ∧
      tetraCoordinate m (octVertexForFaces m k b).val b = octRadius m := by
  fin_cases k <;> fin_cases b
  all_goals first
    | exact (hkb rfl).elim
    | (dsimp [octVertexForFaces, tetraCoordinate, octVertexSite,
        octVertexCoordinates, octCentre]; constructor <;> omega)

def octEdgeStart (m : ℕ) (F : OctEdgeFrame) : Site := octVertexForFaces m F.k F.b

theorem octEdgeStart_spec {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) :
    InASublattice (octEdgeStart m F).val ∧
      tetraCoordinate m (octEdgeStart m F).val F.k = octRadius m ∧
      tetraCoordinate m (octEdgeStart m F).val F.j = -octRadius m ∧
      tetraCoordinate m (octEdgeStart m F).val F.a = -octRadius m ∧
      tetraCoordinate m (octEdgeStart m F).val F.b = octRadius m := by
  have hv := octVertexForFaces_mem m F.k F.b
  have hpA := octVertices_inA hv
  have hp := octVertices_subset_octahedron hm hv
  have h := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m _).mp hp)
  have hj := h F.j
  have ha := h F.a
  change -octRadius m ≤ tetraCoordinate m (octEdgeStart m F).val F.j ∧
    tetraCoordinate m (octEdgeStart m F).val F.j ≤ octRadius m at hj
  change -octRadius m ≤ tetraCoordinate m (octEdgeStart m F).val F.a ∧
    tetraCoordinate m (octEdgeStart m F).val F.a ≤ octRadius m at ha
  have hfaces := octVertexForFaces_faces m F.kb
  have hs := tetraCoordinate_sum_frame m F (octEdgeStart m F).val
  change tetraCoordinate m (octEdgeStart m F).val F.k = octRadius m ∧
    tetraCoordinate m (octEdgeStart m F).val F.b = octRadius m at hfaces
  exact ⟨hpA, hfaces.1, by omega, by omega, hfaces.2⟩

def edgeZigzag (a b : Fin 4) (p : Site) : ℕ → Site
  | 0 => p
  | n + 1 => edgeForwardStep a b (edgeZigzag a b p n)

def octEdgeZigzag (m : ℕ) (F : OctEdgeFrame) : ℕ → Site :=
  edgeZigzag F.a F.b (octEdgeStart m F)

theorem octEdgeZigzag_succ (m : ℕ) (F : OctEdgeFrame) (n : ℕ) :
    octEdgeZigzag m F (n + 1) = edgeForwardStep F.a F.b (octEdgeZigzag m F n) := rfl

theorem octEdgeZigzag_adj (m : ℕ) (F : OctEdgeFrame) (n : ℕ) :
    tetrahedralLattice.Adj (octEdgeZigzag m F n) (octEdgeZigzag m F (n + 1)) :=
  edgeForwardStep_adj F.a F.b _

theorem octEdgeZigzag_even {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (n : ℕ) :
    InASublattice (octEdgeZigzag m F (2 * n)).val ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * n)).val F.k = octRadius m ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * n)).val F.j = -octRadius m ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * n)).val F.a = -octRadius m + 4 * (n : ℤ) ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * n)).val F.b = octRadius m - 4 * (n : ℤ) := by
  induction n with
  | zero => simpa [octEdgeZigzag, edgeZigzag] using octEdgeStart_spec hm F
  | succ n ih =>
    let p := octEdgeZigzag m F (2 * n)
    have hpA : InASublattice p.val := ih.1
    have hqB := step_in_B hpA F.a
    have hrA := step_in_A hqB F.b
    have hq : octEdgeZigzag m F (2 * n + 1) = step p F.a := by
      rw [octEdgeZigzag_succ, edgeForwardStep, if_pos hpA]
    have hr : octEdgeZigzag m F (2 * (n + 1)) = step (step p F.a) F.b := by
      have hindex : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [hindex, octEdgeZigzag_succ, hq, edgeForwardStep,
        if_neg ((inB_iff_not_inA _).mp hqB)]
    rw [hr]
    have hk1 := tetraCoordinate_step_A m hpA F.a F.k
    have hj1 := tetraCoordinate_step_A m hpA F.a F.j
    have ha1 := tetraCoordinate_step_A m hpA F.a F.a
    have hb1 := tetraCoordinate_step_A m hpA F.a F.b
    have hk2 := tetraCoordinate_step_B m hqB F.b F.k
    have hj2 := tetraCoordinate_step_B m hqB F.b F.j
    have ha2 := tetraCoordinate_step_B m hqB F.b F.a
    have hb2 := tetraCoordinate_step_B m hqB F.b F.b
    simp only [if_neg F.ka, if_neg F.ja, if_neg (Ne.symm F.ab), ite_true] at hk1 hj1 ha1 hb1
    simp only [if_neg F.kb, if_neg F.jb, if_neg F.ab, ite_true] at hk2 hj2 ha2 hb2
    obtain ⟨_, hk, hj, ha, hb⟩ := ih
    change tetraCoordinate m p.val F.k = octRadius m at hk
    change tetraCoordinate m p.val F.j = -octRadius m at hj
    change tetraCoordinate m p.val F.a = -octRadius m + 4 * (n : ℤ) at ha
    change tetraCoordinate m p.val F.b = octRadius m - 4 * (n : ℤ) at hb
    refine ⟨hrA, ?_, ?_, ?_, ?_⟩ <;> push_cast
    all_goals omega

theorem octEdgeZigzag_odd {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (n : ℕ) :
    InBSublattice (octEdgeZigzag m F (2 * n + 1)).val ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * n + 1)).val F.k = octRadius m - 1 ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * n + 1)).val F.j = -octRadius m - 1 ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * n + 1)).val F.a =
        -octRadius m + 3 + 4 * (n : ℤ) ∧
      tetraCoordinate m (octEdgeZigzag m F (2 * n + 1)).val F.b =
        octRadius m - 1 - 4 * (n : ℤ) := by
  obtain ⟨hpA, hk, hj, ha, hb⟩ := octEdgeZigzag_even hm F n
  rw [octEdgeZigzag_succ, edgeForwardStep, if_pos hpA]
  have hk1 := tetraCoordinate_step_A m hpA F.a F.k
  have hj1 := tetraCoordinate_step_A m hpA F.a F.j
  have ha1 := tetraCoordinate_step_A m hpA F.a F.a
  have hb1 := tetraCoordinate_step_A m hpA F.a F.b
  simp only [if_neg F.ka, if_neg F.ja, if_neg (Ne.symm F.ab), ite_true] at hk1 hj1 ha1 hb1
  refine ⟨step_in_B hpA F.a, ?_, ?_, ?_, ?_⟩
  all_goals omega

end ProteinFolding.Tetrahedral
