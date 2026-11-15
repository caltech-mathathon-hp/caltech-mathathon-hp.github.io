import ProteinFolding.Tetrahedral.OctahedralP3Links
import ProteinFolding.Tetrahedral.OctahedralEdgeParametrization

/-! Triangular face steps, used to compare boundary sides in (O5). -/

namespace ProteinFolding.Tetrahedral

theorem twoStep_A_coordinates {p : Site} (hpA : InASublattice p.val) (l i : Fin 4)
    (a : Fin 3) : (step (step p l) i).val a = p.val a + bondVector l a - bondVector i a := by
  rw [step_val_of_B _ (step_in_B hpA l), step_val_of_A p hpA l]

theorem twoStep_B_coordinates {p : Site} (hpB : InBSublattice p.val) (l i : Fin 4)
    (a : Fin 3) : (step (step p l) i).val a = p.val a - bondVector l a + bondVector i a := by
  rw [step_val_of_A _ (step_in_A hpB l), step_val_of_B p hpB l]

theorem tetraCoordinate_twoStep_A (m : ℕ) {p : Site} (hpA : InASublattice p.val)
    (l i r : Fin 4) : tetraCoordinate m (step (step p l) i).val r = tetraCoordinate m p.val r +
      (if r = l then 4 else 0) - (if r = i then 4 else 0) := by
  rw [tetraCoordinate_step_B m (step_in_B hpA l), tetraCoordinate_step_A m hpA]
  split_ifs <;> omega

theorem tetraCoordinate_twoStep_B (m : ℕ) {p : Site} (hpB : InBSublattice p.val)
    (l i r : Fin 4) : tetraCoordinate m (step (step p l) i).val r = tetraCoordinate m p.val r -
      (if r = l then 4 else 0) + (if r = i then 4 else 0) := by
  rw [tetraCoordinate_step_A m (step_in_A hpB l), tetraCoordinate_step_B m hpB]
  split_ifs <;> omega

theorem triangular_neighbours_A_step {m : ℕ} {p q : Site} (hpA : InASublattice p.val)
    (h : OctTriangularNeighbours m p q) :
    ∃ i l : Fin 4, i ≠ l ∧ q = step (step p l) i := by
  obtain ⟨k, i, l, hil, _, _, h⟩ := h
  rcases h with ⟨_, _, hcoords⟩ | ⟨hp, _, _⟩
  · refine ⟨i, l, hil, ?_⟩
    apply Subtype.ext
    funext a
    rw [twoStep_A_coordinates hpA]
    exact hcoords a
  · exact (sublattices_disjoint _ hpA hp.2.1).elim

theorem triangular_neighbours_B_step {m : ℕ} {p q : Site} (hpB : InBSublattice p.val)
    (h : OctTriangularNeighbours m p q) :
    ∃ i l : Fin 4, i ≠ l ∧ q = step (step p l) i := by
  obtain ⟨k, i, l, hil, _, _, h⟩ := h
  rcases h with ⟨hp, _, _⟩ | ⟨_, _, hcoords⟩
  · exact (sublattices_disjoint _ hp.2.1 hpB).elim
  · refine ⟨i, l, hil, ?_⟩
    apply Subtype.ext
    funext a
    rw [twoStep_B_coordinates hpB]
    exact hcoords a

theorem triangular_neighbours_coordinate_bounds {m : ℕ} {p q : Site}
    (h : OctTriangularNeighbours m p q) (r : Fin 4) :
    -4 ≤ tetraCoordinate m q.val r - tetraCoordinate m p.val r ∧
      tetraCoordinate m q.val r - tetraCoordinate m p.val r ≤ 4 := by
  rcases p.property with hpA | hpB
  · obtain ⟨i, l, _, rfl⟩ := triangular_neighbours_A_step hpA h
    rw [tetraCoordinate_twoStep_A m hpA]
    split_ifs <;> omega
  · obtain ⟨i, l, _, rfl⟩ := triangular_neighbours_B_step hpB h
    rw [tetraCoordinate_twoStep_B m hpB]
    split_ifs <;> omega

theorem triangular_neighbours_ne {m : ℕ} {p q : Site} (h : OctTriangularNeighbours m p q) :
    p ≠ q := by
  rcases p.property with hpA | hpB
  · obtain ⟨i, l, hil, rfl⟩ := triangular_neighbours_A_step hpA h
    exact Ne.symm (two_distinct_steps_ne p (Ne.symm hil))
  · obtain ⟨i, l, hil, rfl⟩ := triangular_neighbours_B_step hpB h
    exact Ne.symm (two_distinct_steps_ne p (Ne.symm hil))

theorem triangular_neighbours_symm {m : ℕ} {p q : Site} (h : OctTriangularNeighbours m p q) :
    OctTriangularNeighbours m q p := by
  obtain ⟨k, i, l, hil, hik, hlk, h⟩ := h
  refine ⟨k, l, i, Ne.symm hil, hlk, hik, ?_⟩
  rcases h with ⟨hp, hq, hcoords⟩ | ⟨hp, hq, hcoords⟩
  · left
    refine ⟨hq, hp, fun a => ?_⟩
    have ha := hcoords a
    omega
  · right
    refine ⟨hq, hp, fun a => ?_⟩
    have ha := hcoords a
    omega

theorem big_face_twoStep_triangular {m : ℕ} {p q : Site} {k i l : Fin 4}
    (hp : OctBigFace m k p) (hq : OctBigFace m k q)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k) (heq : q = step (step p l) i) :
    OctTriangularNeighbours m p q := by
  refine ⟨k, i, l, hil, hik, hlk, Or.inl ⟨hp, hq, fun a => ?_⟩⟩
  rw [heq, twoStep_A_coordinates hp.2.1]

theorem small_face_twoStep_triangular {m : ℕ} {p q : Site} {k i l : Fin 4}
    (hp : OctSmallFace m k p) (hq : OctSmallFace m k q)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k) (heq : q = step (step p l) i) :
    OctTriangularNeighbours m p q := by
  refine ⟨k, i, l, hil, hik, hlk, Or.inr ⟨hp, hq, fun a => ?_⟩⟩
  rw [heq, twoStep_B_coordinates hp.2.1]

def OctEdgeFrame.bigOtherSide (F : OctEdgeFrame) : OctEdgeFrame :=
  ⟨F.k, F.a, F.j, F.b, F.ka, F.kj, F.kb, Ne.symm F.ja, F.ab, F.jb⟩

def OctEdgeFrame.smallOtherSide (F : OctEdgeFrame) : OctEdgeFrame :=
  ⟨F.b, F.j, F.a, F.k, Ne.symm F.jb, Ne.symm F.ab, Ne.symm F.kb,
    F.ja, Ne.symm F.kj, Ne.symm F.ka⟩

theorem octEdgeZigzag_even_twoStep {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (i : ℕ) :
    octEdgeZigzag m F (2 * (i + 1)) = step (step (octEdgeZigzag m F (2 * i)) F.a) F.b := by
  have hpA := (octEdgeZigzag_even hm F i).1
  have hqB := step_in_B hpA F.a
  have h1 : octEdgeZigzag m F (2 * i + 1) = step (octEdgeZigzag m F (2 * i)) F.a := by
    rw [octEdgeZigzag_succ, edgeForwardStep, if_pos hpA]
  have hindex : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
  rw [hindex, octEdgeZigzag_succ, h1, edgeForwardStep, if_neg ((inB_iff_not_inA _).mp hqB)]

theorem octEdgeZigzag_odd_twoStep {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (i : ℕ) :
    octEdgeZigzag m F (2 * (i + 1) + 1) =
      step (step (octEdgeZigzag m F (2 * i + 1)) F.b) F.a := by
  have hpB := (octEdgeZigzag_odd hm F i).1
  have hqA := step_in_A hpB F.b
  have h1 : octEdgeZigzag m F ((2 * i + 1) + 1) =
      step (octEdgeZigzag m F (2 * i + 1)) F.b := by
    rw [octEdgeZigzag_succ, edgeForwardStep, if_neg ((inB_iff_not_inA _).mp hpB)]
  have hindex : 2 * (i + 1) + 1 = ((2 * i + 1) + 1) + 1 := by omega
  rw [hindex, octEdgeZigzag_succ, h1, edgeForwardStep, if_pos hqA]

end ProteinFolding.Tetrahedral
