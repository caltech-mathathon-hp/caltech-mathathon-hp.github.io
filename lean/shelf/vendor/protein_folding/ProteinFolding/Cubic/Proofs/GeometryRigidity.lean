import ProteinFolding.Cubic.Proofs.GeometryEqualityGapless
import ProteinFolding.Cubic.Proofs.GeometryEqualityCardinality

/-! The equality classification in Fact 3.1. Maximal edge count forces
equality in Loomis--Whitney and in each line-counting bound. The support is
therefore Cartesian, its coordinate sets are gapless, and each has n elements.
The resulting shape is exactly a translated n-cube, including the empty case. -/

namespace ProteinFolding.CubicGeometry

theorem eq_cubeFinset_of_maximal_edges (s : Finset Site) (n : ℕ)
    (hc : s.card = n ^ 3) (he : positiveEdgeCount s ≥ 3 * n ^ 2 * (n - 1)) :
    ∃ a : Site, s = cubeFinset a n := by
  classical
  by_cases hn : n = 0
  · subst n
    have hs : s = ∅ := Finset.card_eq_zero.mp (by simpa using hc)
    have hz : cubeFinset (fun _ => 0) 0 = ∅ :=
      Finset.card_eq_zero.mp (by rw [cubeFinset_card]; rfl)
    exact ⟨fun _ => 0, hs.trans hz.symm⟩
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hne : s.Nonempty := Finset.card_pos.mp (by rw [hc]; exact pow_pos hn' _)
    obtain ⟨h0, h1, h2⟩ := lineKey_cards_of_maximal_edges s n hc he
    have hLW : s.card ^ 2 = (s.image (lineKey 0)).card *
        (s.image (lineKey 1)).card * (s.image (lineKey 2)).card := by
      rw [hc, h0, h1, h2]
      ring
    have hcart := mem_iff_coordinate_mem_of_projection_equality s hLW
    have hcards := coordinate_cards_of_cartesian_lines s hne hcart n hn' h0 h1 h2
    have hinter : ∀ k : Fin 3, ∃ a b : ℤ, s.image (fun q => q k) = Finset.Icc a b := by
      intro k
      exact coordinate_eq_interval_of_tight s hne hcart k (axis_tight_of_maximal_edges s n hc he k)
    choose a b hab using hinter
    have hlength : ∀ k : Fin 3, b k + 1 = a k + (n : ℤ) := by
      intro k
      obtain ⟨p, hp⟩ := hne
      have hmem : p k ∈ Finset.Icc (a k) (b k) := by
        rw [← hab k]
        exact Finset.mem_image_of_mem _ hp
      have hord := Finset.mem_Icc.mp hmem
      have hcard := hcards k
      rw [hab k, Int.card_Icc] at hcard
      omega
    refine ⟨a, ?_⟩
    ext p
    rw [hcart p, mem_cubeFinset]
    change (∀ k : Fin 3, p k ∈ s.image (fun q => q k)) ↔
      (∀ k : Fin 3, a k ≤ p k ∧ p k < a k + (n : ℤ))
    constructor
    · intro hp k
      have hk := hp k
      rw [hab k, Finset.mem_Icc] at hk
      have hlen := hlength k
      omega
    · intro hp k
      rw [hab k, Finset.mem_Icc]
      have hk := hp k
      have hlen := hlength k
      omega

theorem positiveEdgeCount_eq_cube_iff (s : Finset Site) (n : ℕ)
    (hc : s.card = n ^ 3) :
    positiveEdgeCount s = 3 * n ^ 2 * (n - 1) ↔ ∃ a : Site, s = cubeFinset a n := by
  constructor
  · intro he
    exact eq_cubeFinset_of_maximal_edges s n hc he.ge
  · rintro ⟨a, rfl⟩
    exact positiveEdgeCount_cubeFinset a n

end ProteinFolding.CubicGeometry
