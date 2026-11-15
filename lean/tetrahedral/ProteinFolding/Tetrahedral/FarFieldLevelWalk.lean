import ProteinFolding.Tetrahedral.FarFieldLevelClassification
import ProteinFolding.Tetrahedral.FarFieldPathTools

/-! A single injective integer curve parametrizes the whole level rho=u.
Euclidean division handles bends explicitly; a finite interval therefore gives
an actual self-avoiding approach path through any number of quadrants. -/

namespace ProteinFolding.Tetrahedral.FarField

def levelWalk (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (t : ℤ) : Site :=
  levelPoint R u x₀ hR hu hx hs (t / u) (t % u)

theorem levelWalk_rho (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (hupos : 0 < u) (t : ℤ) :
    rho R (levelWalk R u x₀ hR hu hx hs t) = u := by
  exact levelPoint_rho R u x₀ hR hu hx hs _ _
    (Int.emod_nonneg t (by omega)) (by have h := Int.emod_lt_of_pos t hupos; omega)

theorem levelWalk_injective (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (hupos : 0 < u) :
    Function.Injective (levelWalk R u x₀ hR hu hx hs) := by
  intro t s h
  have he := levelPoint_injective R u x₀ hR hu hx hs hupos (t / u) (s / u) (t % u) (s % u)
    (Int.emod_nonneg t (by omega)) (Int.emod_lt_of_pos t hupos)
    (Int.emod_nonneg s (by omega)) (Int.emod_lt_of_pos s hupos) h
  have ht := Int.ediv_mul_add_emod t u
  have hs' := Int.ediv_mul_add_emod s u
  rw [he.1, he.2] at ht
  exact ht.symm.trans hs'

theorem divmod_next (u t : ℤ) (hu : 1 < u) :
    ((t + 1) / u = t / u ∧ (t + 1) % u = t % u + 1) ∨
      (t % u = u - 1 ∧ (t + 1) / u = t / u + 1 ∧ (t + 1) % u = 0) := by
  have hu0 : 0 < u := by omega
  have hr0 := Int.emod_nonneg t (by omega : u ≠ 0)
  have hr1 := Int.emod_lt_of_pos t hu0
  have honeDiv : (1 : ℤ) / u = 0 := Int.ediv_eq_zero_of_lt (by omega) hu
  have honeMod : (1 : ℤ) % u = 1 := Int.emod_eq_of_lt (by omega) hu
  have hdiv := Int.add_ediv_of_pos (a := t) (b := 1) hu0
  have hmod := Int.add_emod t 1 u
  rw [honeDiv, honeMod] at hdiv
  rw [honeMod] at hmod
  by_cases hlast : t % u = u - 1
  · right
    have hge : u ≤ t % u + 1 := by omega
    simp only [hge, ite_true, add_zero] at hdiv
    rw [hlast, show u - 1 + 1 = u by omega, Int.emod_self] at hmod
    exact ⟨hlast, hdiv, hmod⟩
  · left
    have hlt : t % u + 1 < u := by omega
    simp only [show ¬u ≤ t % u + 1 by omega, ite_false, add_zero] at hdiv
    rw [Int.emod_eq_of_lt (by omega) hlt] at hmod
    exact ⟨hdiv, hmod⟩

theorem levelWalk_adj (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (humin : 3 ≤ u) (t : ℤ) :
    tetrahedralLattice.Adj (levelWalk R u x₀ hR hu hx hs t)
      (levelWalk R u x₀ hR hu hx hs (t + 1)) := by
  rcases divmod_next u t (by omega) with ⟨hdiv, hmod⟩ | ⟨hr, hdiv, hmod⟩
  · simpa only [levelWalk, hdiv, hmod] using levelPoint_adj_inside R u x₀ hR hu hx hs (t / u) (t % u)
  · simpa only [levelWalk, hr, hdiv, hmod] using levelPoint_adj_bend R u x₀ hR hu hx hs (t / u)

theorem levelWalk_at (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (hupos : 0 < u)
    (j r : ℤ) (hr0 : 0 ≤ r) (hr1 : r < u) :
    levelWalk R u x₀ hR hu hx hs (j * u + r) = levelPoint R u x₀ hR hu hx hs j r := by
  have hdiv : (j * u + r) / u = j := by
    rw [Int.mul_add_ediv_right _ _ (by omega : u ≠ 0), Int.ediv_eq_zero_of_lt hr0 hr1, add_zero]
  have hmod : (j * u + r) % u = r := by
    rw [Int.mul_add_emod_self_right, Int.emod_eq_of_lt hr0 hr1]
  simp only [levelWalk, hdiv, hmod]

theorem levelWalk_exhaustive (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (hupos : 0 < u)
    (p : Site) (hp : rho R p = u) : ∃ t : ℤ, levelWalk R u x₀ hR hu hx hs t = p := by
  obtain ⟨j, r, hr0, hr1, he⟩ := levelPoint_exhaustive R u x₀ hR hu hx hs hupos p hp
  refine ⟨j * u + r, ?_⟩
  rw [levelWalk_at R u x₀ hR hu hx hs hupos j r hr0 hr1, he]

end ProteinFolding.Tetrahedral.FarField
