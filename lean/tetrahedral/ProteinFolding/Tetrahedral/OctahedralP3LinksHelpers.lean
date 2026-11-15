import ProteinFolding.Tetrahedral.OctahedralEdgeFacts

namespace ProteinFolding.Tetrahedral

theorem two_distinct_steps_ne (p : Site) {a b : Fin 4} (hab : a ≠ b) :
    step (step p a) b ≠ p := by
  intro h
  have he : step (step p a) b = step (step p a) a := by simpa only [step_step] using h
  exact hab ((step_injective (step p a) he).symm)

theorem four_bond_chain_injective (p a b c q : Site)
    (h0 : tetrahedralLattice.Adj p a) (h1 : tetrahedralLattice.Adj a b)
    (h2 : tetrahedralLattice.Adj b c) (h3 : tetrahedralLattice.Adj c q)
    (hpb : p ≠ b) (hac : a ≠ c) (hbq : b ≠ q) :
    Function.Injective (![p, a, b, c, q] : Fin 5 → Site) := by
  have hpa : p ≠ a := tetrahedralLattice.ne_of_adj h0
  have hab : a ≠ b := tetrahedralLattice.ne_of_adj h1
  have hbc : b ≠ c := tetrahedralLattice.ne_of_adj h2
  have hcq : c ≠ q := tetrahedralLattice.ne_of_adj h3
  have hpc : p ≠ c := by
    intro he
    exact no_triangle p a b ⟨h0, h1, he ▸ h2⟩
  have haq : a ≠ q := by
    intro he
    exact no_triangle a b c ⟨h1, h2, he ▸ h3⟩
  have hpq : p ≠ q := by
    intro he
    exact no_four_cycle hpb hac ⟨h0, h1, h2, he ▸ h3⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

def faceFourStep (p : Site) (k i l : Fin 4) : Site :=
  step (step (step (step p k) i) l) k

theorem faceFourStep_A_coordinates {p : Site} (hp : InASublattice p.val) (k i l : Fin 4)
    (a : Fin 3) :
    (faceFourStep p k i l).val a = p.val a + bondVector l a - bondVector i a := by
  unfold faceFourStep
  rw [step_val_of_B _ (step_in_B (step_in_A (step_in_B hp k) i) l),
    step_val_of_A _ (step_in_A (step_in_B hp k) i),
    step_val_of_B _ (step_in_B hp k), step_val_of_A p hp k]
  dsimp
  omega

theorem faceFourStep_B_coordinates {p : Site} (hp : InBSublattice p.val) (k i l : Fin 4)
    (a : Fin 3) :
    (faceFourStep p k i l).val a = p.val a - bondVector l a + bondVector i a := by
  unfold faceFourStep
  rw [step_val_of_A _ (step_in_A (step_in_B (step_in_A hp k) i) l),
    step_val_of_B _ (step_in_B (step_in_A hp k) i),
    step_val_of_A _ (step_in_A hp k), step_val_of_B p hp k]
  dsimp
  omega

theorem faceFourStep_same_face (m : ℕ) (p : Site) (k i l : Fin 4)
    (hik : i ≠ k) (hlk : l ≠ k) :
    tetraCoordinate m (faceFourStep p k i l).val k = tetraCoordinate m p.val k := by
  rcases p.property with hp | hp
  · have h1 := tetraCoordinate_step_A m hp k k
    have h2 := tetraCoordinate_step_B m (step_in_B hp k) i k
    have h3 := tetraCoordinate_step_A m (step_in_A (step_in_B hp k) i) l k
    have h4 := tetraCoordinate_step_B m (step_in_B (step_in_A (step_in_B hp k) i) l) k k
    simp only [if_true, if_neg (Ne.symm hik), if_neg (Ne.symm hlk)] at h1 h2 h3 h4
    change tetraCoordinate m (step (step (step (step p k) i) l) k).val k = _
    omega
  · have h1 := tetraCoordinate_step_B m hp k k
    have h2 := tetraCoordinate_step_A m (step_in_A hp k) i k
    have h3 := tetraCoordinate_step_B m (step_in_B (step_in_A hp k) i) l k
    have h4 := tetraCoordinate_step_A m (step_in_A (step_in_B (step_in_A hp k) i) l) k k
    simp only [if_true, if_neg (Ne.symm hik), if_neg (Ne.symm hlk)] at h1 h2 h3 h4
    change tetraCoordinate m (step (step (step (step p k) i) l) k).val k = _
    omega

/-- The face first crossed on leaving the solid is also the last one crossed
by a nonbacktracking four-bond return. -/
theorem exterior_four_bond_directions (m : ℕ) (p : Site) (k i l n : Fin 4)
    (hp : p ∈ octahedron m) (hout : step p k ∉ octahedron m)
    (hend : step (step (step (step p k) i) l) n ∈ octahedron m)
    (hback0 : step (step p k) i ≠ p)
    (hback1 : step (step (step p k) i) l ≠ step p k) :
    n = k ∧ i ≠ k ∧ l ≠ k ∧ i ≠ l := by
  have hik : i ≠ k := by intro he; subst i; exact hback0 (step_step p k)
  have hli : l ≠ i := by intro he; subst l; exact hback1 (step_step (step p k) i)
  have hki : k ≠ i := Ne.symm hik
  suffices h : n = k ∧ l ≠ k by exact ⟨h.1, hik, h.2, Ne.symm hli⟩
  rcases p.property with hpA | hpB
  · have hface := (step_not_mem_octahedron_A m hpA hp k).mp hout
    have hendA := step_in_A (step_in_B (step_in_A (step_in_B hpA k) i) l) n
    have hbound := ((inOctahedron_iff_A m hendA).mp ((mem_octahedron m _).mp hend) k).2
    have h1 := tetraCoordinate_step_A m hpA k k
    have h2 := tetraCoordinate_step_B m (step_in_B hpA k) i k
    have h3 := tetraCoordinate_step_A m (step_in_A (step_in_B hpA k) i) l k
    have h4 := tetraCoordinate_step_B m (step_in_B (step_in_A (step_in_B hpA k) i) l) n k
    simp only [if_true, if_neg hki] at h1 h2
    have hkl : k ≠ l := by
      intro he
      rw [if_pos he] at h3
      split_ifs at h4 <;> omega
    rw [if_neg hkl] at h3
    have hkn : k = n := by
      by_contra he
      rw [if_neg he] at h4
      omega
    exact ⟨hkn.symm, Ne.symm hkl⟩
  · have hface := (step_not_mem_octahedron_B m hpB hp k).mp hout
    have hendB := step_in_B (step_in_A (step_in_B (step_in_A hpB k) i) l) n
    have hbound := ((inOctahedron_iff_B m hendB).mp ((mem_octahedron m _).mp hend) k).1
    have h1 := tetraCoordinate_step_B m hpB k k
    have h2 := tetraCoordinate_step_A m (step_in_A hpB k) i k
    have h3 := tetraCoordinate_step_B m (step_in_B (step_in_A hpB k) i) l k
    have h4 := tetraCoordinate_step_A m (step_in_A (step_in_B (step_in_A hpB k) i) l) n k
    simp only [if_true, if_neg hki] at h1 h2
    have hkl : k ≠ l := by
      intro he
      rw [if_pos he] at h3
      split_ifs at h4 <;> omega
    rw [if_neg hkl] at h3
    have hkn : k = n := by
      by_contra he
      rw [if_neg he] at h4
      omega
    exact ⟨hkn.symm, Ne.symm hkl⟩

end ProteinFolding.Tetrahedral
