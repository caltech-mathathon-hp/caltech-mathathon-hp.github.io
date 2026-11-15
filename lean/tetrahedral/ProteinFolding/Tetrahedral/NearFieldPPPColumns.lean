import ProteinFolding.Tetrahedral.NearFieldPPPPaths

/-! Exact column-owner alternatives for the middle P-site of an O2 link. -/

namespace ProteinFolding.Tetrahedral

theorem facePPP_middle_A_other_bound (m : ℕ) {p : Site} (k i d : Fin 4)
    (hface : OctBigFace m k p) (hdk : d ≠ k) :
    tetraCoordinate m (step (step p k) i).val d ≤ octRadius m := by
  have hp := ((inOctahedron_iff_A m hface.2.1).mp ((mem_octahedron m p).mp hface.1) d).2
  have h1 := tetraCoordinate_step_A m hface.2.1 k d
  have h2 := tetraCoordinate_step_B m (step_in_B hface.2.1 k) i d
  rw [if_neg hdk] at h1
  split_ifs at h2 <;> omega

theorem facePPP_middle_B_other_bound (m : ℕ) {p : Site} (k i d : Fin 4)
    (hface : OctSmallFace m k p) (hdk : d ≠ k) :
    -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (step (step p k) i).val d := by
  have hp := ((inOctahedron_iff_B m hface.2.1).mp ((mem_octahedron m p).mp hface.1) d).1
  have h1 := tetraCoordinate_step_B m hface.2.1 k d
  have h2 := tetraCoordinate_step_A m (step_in_A hface.2.1 k) i d
  rw [if_neg hdk] at h1
  split_ifs at h2 <;> omega

theorem facePPP_middle_not_dangling (m : ℕ) {p : Site} (k i : Fin 4) (hik : i ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p) :
    ¬ IsDangling m (step (step p k) i) := by
  intro hdang
  have hb := dangling_tetraCoordinate_bounds m hdang k
  rcases hface with hface | hface
  · have h1 := tetraCoordinate_step_A m hface.2.1 k k
    have h2 := tetraCoordinate_step_B m (step_in_B hface.2.1 k) i k
    rw [if_pos rfl] at h1
    rw [if_neg hik.symm] at h2
    have hf := hface.2.2
    omega
  · have h1 := tetraCoordinate_step_B m hface.2.1 k k
    have h2 := tetraCoordinate_step_A m (step_in_A hface.2.1 k) i k
    rw [if_pos rfl] at h1
    rw [if_neg hik.symm] at h2
    have hf := hface.2.2
    omega

theorem facePPP_middle_column_owner (m : ℕ) {p : Site} (k i : Fin 4)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p) (C : DanglingColumn m)
    (heq : C.point 1 = step (step p k) i) :
    C.dir = k ∧ C.owner = step (step p (columnOpposite k)) i := by
  have hdir : C.dir = k := by
    rcases C.owner.property with hpA | hpB
    · have hCA : InASublattice (C.point 1).val := by
        rw [C.point_one_eq]
        exact step_in_A (step_in_B hpA C.dir) (columnOpposite C.dir)
      rcases hface with hface | hface
      · by_contra hne
        have hbound := facePPP_middle_A_other_bound m k i C.dir hface hne
        have hc := C.big_point_coordinate hpA 1
        rw [heq] at hc
        omega
      · rw [heq] at hCA
        exact (sublattices_disjoint _ hCA (step_in_B (step_in_A hface.2.1 k) i)).elim
    · have hCB : InBSublattice (C.point 1).val := by
        rw [C.point_one_eq]
        exact step_in_B (step_in_A hpB C.dir) (columnOpposite C.dir)
      rcases hface with hface | hface
      · rw [heq] at hCB
        exact (sublattices_disjoint _ (step_in_A (step_in_B hface.2.1 k) i) hCB).elim
      · by_contra hne
        have hbound := facePPP_middle_B_other_bound m k i C.dir hface hne
        have hc := C.small_point_coordinate hpB 1
        rw [heq] at hc
        omega
  refine ⟨hdir, ?_⟩
  rw [C.point_one_eq, hdir] at heq
  have howner := congrArg (fun s => step (step s (columnOpposite k)) k) heq
  simp only [step_step] at howner
  change C.owner = faceFourStep p k i (columnOpposite k) at howner
  rw [faceFourStep_eq_twoStep] at howner
  exact howner

theorem facePPP_middle_column_endpoint_alternatives (m : ℕ) {p : Site} (k i l : Fin 4)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p) (C : DanglingColumn m)
    (heq : C.point 1 = step (step p k) i) :
    (columnOpposite k = i ∧ C.owner = p) ∨
    (columnOpposite k = l ∧ C.owner = faceFourStep p k i l) ∨
    (columnOpposite k ≠ i ∧ columnOpposite k ≠ l ∧
      C.dir = k ∧ C.owner = step (step p (columnOpposite k)) i) := by
  obtain ⟨hd, ho⟩ := facePPP_middle_column_owner m k i hface C heq
  by_cases hi : columnOpposite k = i
  · left
    refine ⟨hi, ?_⟩
    simpa only [hi, step_step] using ho
  · right
    by_cases hl : columnOpposite k = l
    · left
      refine ⟨hl, ?_⟩
      rw [hl, ← faceFourStep_eq_twoStep] at ho
      exact ho
    · exact Or.inr ⟨hi, hl, hd, ho⟩

end ProteinFolding.Tetrahedral
