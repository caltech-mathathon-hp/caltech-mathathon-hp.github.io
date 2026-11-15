import ProteinFolding.Cubic.Proofs.GeometryProjection
import Mathlib.Tactic.Linarith

/-! Coordinate cardinalities of Cartesian equality cases. These finite-set
interfaces do not assume that the coordinate sets are intervals. -/

namespace ProteinFolding.CubicGeometry

theorem pair_image_of_cartesian (s : Finset Site) (hne : s.Nonempty)
    (hcart : ∀ p : Site, p ∈ s ↔ ∀ k : Fin 3, p k ∈ s.image (fun q => q k))
    (i j : Fin 3) (hij : i ≠ j) :
    s.image (fun p => (p i, p j)) =
      (s.image (fun p => p i)) ×ˢ (s.image (fun p => p j)) := by
  classical
  ext xy
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  · intro h
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp h
    obtain ⟨p, hp⟩ := hne
    let q : Site := fun k => if k = i then xy.1 else if k = j then xy.2 else p k
    have hq : q ∈ s := by
      apply (hcart q).mpr
      intro k
      by_cases hki : k = i
      · subst k; simpa [q] using hx
      · by_cases hkj : k = j
        · subst k; simpa [q, hki] using hy
        · simpa [q, hki, hkj] using Finset.mem_image_of_mem (fun r : Site => r k) hp
    exact Finset.mem_image.mpr ⟨q, hq, by simp [q, hij.symm]⟩

theorem pair_card_rigidity (x y z n : ℕ) (hn : 0 < n)
    (hxy : x * y = n ^ 2) (hxz : x * z = n ^ 2) (hyz : y * z = n ^ 2) :
    x = n ∧ y = n ∧ z = n := by
  have hx : 0 < x := by nlinarith
  have hy : 0 < y := by nlinarith
  have hey : y = z := Nat.eq_of_mul_eq_mul_left hx (hxy.trans hxz.symm)
  have hex : x = z := Nat.eq_of_mul_eq_mul_left hy (by
    calc y * x = x * y := Nat.mul_comm _ _
         _ = n ^ 2 := hxy
         _ = y * z := hyz.symm)
  rw [hex, hey] at hxy
  have hz : z = n := by nlinarith
  exact ⟨hex.trans hz, hey.trans hz, hz⟩

theorem coordinate_cards_of_cartesian_lines (s : Finset Site) (hne : s.Nonempty)
    (hcart : ∀ p : Site, p ∈ s ↔ ∀ k : Fin 3, p k ∈ s.image (fun q => q k))
    (n : ℕ) (hn : 0 < n)
    (h0 : (s.image (lineKey 0)).card = n ^ 2)
    (h1 : (s.image (lineKey 1)).card = n ^ 2)
    (h2 : (s.image (lineKey 2)).card = n ^ 2) :
    ∀ k : Fin 3, (s.image (fun q => q k)).card = n := by
  classical
  have hpair (i j : Fin 3) (hij : i ≠ j) :
      (s.image (fun p => (p i, p j))).card =
        (s.image (fun p => p i)).card * (s.image (fun p => p j)).card := by
    rw [pair_image_of_cartesian s hne hcart i j hij, Finset.card_product]
  rw [lineKey_card_eq_projection] at h0 h1 h2
  change (s.image (fun p => (p 1, p 2))).card = n ^ 2 at h0
  change (s.image (fun p => (p 0, p 2))).card = n ^ 2 at h1
  change (s.image (fun p => (p 0, p 1))).card = n ^ 2 at h2
  rw [hpair 1 2 (by decide)] at h0
  rw [hpair 0 2 (by decide)] at h1
  rw [hpair 0 1 (by decide)] at h2
  obtain ⟨hx, hy, hz⟩ := pair_card_rigidity _ _ _ n hn h2 h1 h0
  intro k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl <;> assumption

end ProteinFolding.CubicGeometry
