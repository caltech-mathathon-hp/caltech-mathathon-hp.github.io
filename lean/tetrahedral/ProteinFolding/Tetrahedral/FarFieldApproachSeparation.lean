import ProteinFolding.Tetrahedral.FarFieldApproaches
import ProteinFolding.Tetrahedral.FarFieldWireAvenues
import ProteinFolding.Tetrahedral.FarFieldArms

namespace ProteinFolding.Tetrahedral.FarField

theorem canonical_levelApproach_exists (R u a : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (humin : 3 ≤ u) (ha : a % 2 = 1) (hroom : |a| + 8 < u)
    (T : Site) (hT : rho R T = u) (hα : |alpha R T| + 4 ≤ a) : Nonempty (ApproachData R u a T) := by
  let x₀ := -(R + u + 1)
  have hx : x₀ % 2 = 0 := by dsimp only [x₀]; omega
  have hs : (x₀ + R + u + 1) % 4 = 0 := by dsimp only [x₀]; omega
  exact levelApproach_exists R u x₀ a hR hu hx hs humin ha hroom T hT hα

theorem ApproachData.target_level {R u a : ℤ} {T : Site} (h : ApproachData R u a T) :
    rho R h.target = u := by
  let i : Fin h.sites := ⟨h.sites - 1, by have hp := h.sites_pos; omega⟩
  have hl := h.last i (by dsimp only [i]; have hp := h.sites_pos; omega)
  have hr := h.level i
  rwa [hl] at hr

theorem ApproachData.slab_window {R u a ξ : ℤ} {T : Site} (h : ApproachData R u a T)
    (hT : ξ - 1 ≤ X T ∧ X T ≤ ξ + 4) (i : Fin h.sites) :
    ξ - 5 ≤ X (h.path.pos i) ∧ X (h.path.pos i) ≤ ξ + 5 := by
  have hi := h.window i
  omega

theorem approaches_disjoint_slabs {R u v a ξ η : ℤ} {T S : Site}
    (h : ApproachData R u a T) (k : ApproachData R v a S)
    (hT : ξ - 1 ≤ X T ∧ X T ≤ ξ + 4) (hS : η - 1 ≤ X S ∧ X S ≤ η + 4)
    (hsep : ξ + 60 ≤ η ∨ η + 60 ≤ ξ) :
    Disjoint (Set.range h.path.pos) (Set.range k.path.pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨i, rfl⟩ ⟨j, heq⟩
  have hi := h.slab_window hT i
  have hj := k.slab_window hS j
  rw [heq] at hj
  omega

theorem avenueThrough_hits (R : ℤ) (p v : Site) (hpY : 4 ≤ Y R p) (hpZ : 5 ≤ Z p)
    (hv : PositiveQuadrant R v) (hρ : rho R v = rho R p) (hα : alpha R v = alpha R p) :
    avenueThrough p (X v) = v := by
  have hm := throughAnchor_margins R p hpY hpZ
  have he := throughAnchor_private R p hpY hpZ
  have hρ' : rho R v = privateLevel R (throughAnchor p) (throughUp p) := by rw [he.1, hρ]
  have hα' : alpha R v = privateStrip R (throughAnchor p) := by rw [he.2, hα]
  exact (avenue_exhaustive R (throughAnchor p) (throughAnchor_A p) (throughUp p) v
    hm.1 hm.2 hv (Or.inl hρ') (Or.inl hα')).symm

theorem ApproachData.joining_avenue_intersection {R u a : ℤ} {T : Site}
    (h : ApproachData R u a T) (hroom : |a| + 8 < u) (i : Fin h.sites) (x : ℤ)
    (heq : h.path.pos i = avenueThrough h.target x) : h.path.pos i = h.target := by
  have hlevel : |alpha R h.target| + 8 < rho R h.target := by rw [h.target_alpha, h.target_level]; exact hroom
  have hm := margins_of_level R h.target h.target_positive hlevel
  have hp := avenueThrough_member R h.target x (by omega) hm.2
  rw [← heq] at hp
  have hlim := h.alpha_limit i hp.1
  have hα : alpha R (h.path.pos i) = a := by rw [h.target_alpha] at hp; omega
  exact h.hits_target i hp.1 hα

theorem ApproachData.avoids_higher_strip {R u a : ℤ} {T : Site}
    (h : ApproachData R u a T) (p : Site) (hp : PositiveQuadrant R p) (hα : a < alpha R p) :
    p ∉ Set.range h.path.pos := by
  rintro ⟨i, rfl⟩
  have hi := h.alpha_limit i hp
  omega

theorem ApproachData.radial_intersection {R u a : ℤ} {T : Site}
    (h : ApproachData R u a T) (hR : R % 2 = 0) (q : Quadrant) (p : Site)
    (hp : PositiveQuadrant R p) (stop s : ℤ) (hstop : 0 ≤ stop) (hs : 0 ≤ s)
    (hTop : quadrantArm R hR q p stop = T) (hT : rho R T = u)
    (i : Fin h.sites) (heq : h.path.pos i = quadrantArm R hR q p s) :
    s = stop ∧ h.path.pos i = T := by
  have hρs := (quadrantArm_rho_alpha R hR q p s hp hs).1
  have hρt := (quadrantArm_rho_alpha R hR q p stop hp hstop).1
  rw [hTop, hT] at hρt
  have hρi := h.level i
  rw [heq, hρs] at hρi
  have hsst : s = stop := by omega
  exact ⟨hsst, by rw [heq, hsst, hTop]⟩

end ProteinFolding.Tetrahedral.FarField
