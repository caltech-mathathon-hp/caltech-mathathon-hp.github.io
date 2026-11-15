import ProteinFolding.Tetrahedral.NearFieldPPPColumns

/-! The three-port geometry that separates all PPPs with disjoint H endpoints. -/

namespace ProteinFolding.Tetrahedral

theorem dangling_caps_ne_of_owner_ne (m : ℕ) (p q : Site) (k l : Fin 4)
    (hp : p ∈ octahedron m) (hq : q ∈ octahedron m) (hout : step p k ∉ octahedron m)
    (hne : p ≠ q) : step p k ≠ step q l := by
  intro heq
  have ho : q = p := outside_step_unique_inside m hp k hout
    (by rw [heq]; exact (step_adj q l).symm) hq
  exact hne ho.symm

theorem facePPP_last_eq_endpoint_cap (p : Site) (k i l : Fin 4) :
    step (step (step p k) i) l = step (faceFourStep p k i l) k :=
  (step_step _ k).symm

theorem facePPP_middle_normal_not_dangling (m : ℕ) {p : Site} (k i : Fin 4) (hik : i ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p) :
    ¬ IsDangling m (step (step (step p k) i) k) := by
  intro hdang
  have hb := dangling_tetraCoordinate_bounds m hdang k
  rcases hface with hface | hface
  · have h1 := tetraCoordinate_step_A m hface.2.1 k k
    have h2 := tetraCoordinate_step_B m (step_in_B hface.2.1 k) i k
    have h3 := tetraCoordinate_step_A m (step_in_A (step_in_B hface.2.1 k) i) k k
    simp only [ite_true, if_neg hik.symm] at h1 h2 h3
    have hf := hface.2.2
    omega
  · have h1 := tetraCoordinate_step_B m hface.2.1 k k
    have h2 := tetraCoordinate_step_A m (step_in_A hface.2.1 k) i k
    have h3 := tetraCoordinate_step_B m (step_in_B (step_in_A hface.2.1 k) i) k k
    simp only [ite_true, if_neg hik.symm] at h1 h2 h3
    have hf := hface.2.2
    omega

theorem no_four_distinct_directions_avoiding (k i l i' l' : Fin 4)
    (hil : i ≠ l) (hii : i ≠ i') (hil' : i ≠ l') (hli : l ≠ i') (hll : l ≠ l') (hi'l' : i' ≠ l')
    (hik : i ≠ k) (hlk : l ≠ k) (hi'k : i' ≠ k) (hl'k : l' ≠ k) : False := by
  have hcard : ({i, l, i', l'} : Finset (Fin 4)).card = 4 := by
    simp [hil, hii, hil', hli, hll, hi'l']
  have hsub : ({i, l, i', l'} : Finset (Fin 4)) ⊆ Finset.univ.erase k := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    all_goals simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    · exact hik
    · exact hlk
    · exact hi'k
    · exact hl'k
  have hle := Finset.card_le_card hsub
  have hsmall : (Finset.univ.erase k : Finset (Fin 4)).card = 3 := by simp
  omega

end ProteinFolding.Tetrahedral
