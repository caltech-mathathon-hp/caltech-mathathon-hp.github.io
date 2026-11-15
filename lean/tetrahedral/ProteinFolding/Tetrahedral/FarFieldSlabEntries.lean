import ProteinFolding.Tetrahedral.FarFieldWireAvenues
import ProteinFolding.Tetrahedral.FarFieldRadials
import ProteinFolding.Tetrahedral.FarFieldGluing

namespace ProteinFolding.Tetrahedral.FarField

structure SlabEntry (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (T : Site) (ξ : ℤ) where
  x : ℤ
  lower : ξ ≤ x
  upper : x ≤ ξ + 3
  upper_level : rho R (wireAvenue R hR q T x) = rho R T + 2
  previous_level : rho R (wireAvenue R hR q T (x - 1)) = rho R T
  rung_alpha : alpha R (wireAvenue R hR q T x) = alpha R (wireAvenue R hR q T (x - 1))

theorem slabEntry_exists (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (T : Site) (ξ : ℤ)
    (hq : InQuadrant R q T) (hhigh : |alpha R T| + 8 < rho R T) : Nonempty (SlabEntry R hR q T ξ) := by
  obtain ⟨x, hx0, hx1, hρ, hprev, hα⟩ := wireAvenue_upper_rung R hR q T ξ hq hhigh
  exact ⟨⟨x, hx0, hx1, hρ, hprev, hα⟩⟩

def SlabEntry.point {R ξ : ℤ} {hR : R % 2 = 0} {q : Quadrant} {T : Site}
    (e : SlabEntry R hR q T ξ) : Site := wireAvenue R hR q T e.x

theorem SlabEntry.point_profile {R ξ : ℤ} {hR : R % 2 = 0} {q : Quadrant} {T : Site}
    (e : SlabEntry R hR q T ξ) (hq : InQuadrant R q T) (hhigh : |alpha R T| + 8 < rho R T) :
    InQuadrant R q e.point ∧ rho R e.point = rho R T + 2 ∧
      (alpha R e.point = alpha R T ∨ alpha R e.point = alpha R T + 2) ∧
      (ξ ≤ X e.point ∧ X e.point ≤ ξ + 3) := by
  have hm := wireAvenue_member R hR q T e.x hq hhigh
  exact ⟨hm.1, e.upper_level, hm.2.2, by simpa only [SlabEntry.point, wireAvenue_x] using And.intro e.lower e.upper⟩

def SlabEntry.avenueEdges {R ξ : ℤ} {hR : R % 2 = 0} {q : Quadrant} {T : Site}
    (e : SlabEntry R hR q T ξ) : ℕ := (e.x - X T).toNat

def SlabEntry.avenueFold {R ξ : ℤ} {hR : R % 2 = 0} {q : Quadrant} {T : Site}
    (e : SlabEntry R hR q T ξ) : Fold tetrahedralLattice (e.avenueEdges + 1) :=
  intervalFold (wireAvenue R hR q T) (wireAvenue_injective R hR q T)
    (wireAvenue_adj R hR q T) (X T) e.avenueEdges true

theorem SlabEntry.avenueEdges_exact {R ξ : ℤ} {hR : R % 2 = 0} {q : Quadrant} {T : Site}
    (e : SlabEntry R hR q T ξ) (hstart : X T ≤ ξ) : (e.avenueEdges : ℤ) = e.x - X T := by
  exact Int.toNat_of_nonneg (by have h := e.lower; omega)

theorem SlabEntry.avenueFold_first {R ξ : ℤ} {hR : R % 2 = 0} {q : Quadrant} {T : Site}
    (e : SlabEntry R hR q T ξ) (hq : InQuadrant R q T) (hhigh : |alpha R T| + 8 < rho R T)
    (i : Fin (e.avenueEdges + 1)) (hi : i.val = 0) : e.avenueFold.pos i = T := by
  change wireAvenue R hR q T (X T + i.val) = T
  simp only [hi, Int.natCast_zero, add_zero]
  exact wireAvenue_self R hR q T hq hhigh

theorem SlabEntry.avenueFold_last {R ξ : ℤ} {hR : R % 2 = 0} {q : Quadrant} {T : Site}
    (e : SlabEntry R hR q T ξ) (hstart : X T ≤ ξ)
    (i : Fin (e.avenueEdges + 1)) (hi : i.val = e.avenueEdges) : e.avenueFold.pos i = e.point := by
  have he := e.avenueEdges_exact hstart
  change wireAvenue R hR q T (X T + i.val) = wireAvenue R hR q T e.x
  have hx : X T + (i.val : ℤ) = e.x := by omega
  rw [hx]

theorem SlabEntry.avenueFold_profile {R ξ : ℤ} {hR : R % 2 = 0} {q : Quadrant} {T : Site}
    (e : SlabEntry R hR q T ξ) (hstart : X T ≤ ξ) (hq : InQuadrant R q T)
    (hhigh : |alpha R T| + 8 < rho R T) (i : Fin (e.avenueEdges + 1)) :
    let p := e.avenueFold.pos i
    InQuadrant R q p ∧ (rho R p = rho R T ∨ rho R p = rho R T + 2) ∧
      (alpha R p = alpha R T ∨ alpha R p = alpha R T + 2) ∧
      (X T ≤ X p ∧ X p ≤ ξ + 3) := by
  have he := e.avenueEdges_exact hstart
  have hi := i.isLt
  have hm := wireAvenue_member R hR q T (X T + i.val) hq hhigh
  change InQuadrant R q (wireAvenue R hR q T (X T + i.val)) ∧
    (rho R (wireAvenue R hR q T (X T + i.val)) = rho R T ∨ rho R (wireAvenue R hR q T (X T + i.val)) = rho R T + 2) ∧
    (alpha R (wireAvenue R hR q T (X T + i.val)) = alpha R T ∨ alpha R (wireAvenue R hR q T (X T + i.val)) = alpha R T + 2) ∧
    (X T ≤ X (wireAvenue R hR q T (X T + i.val)) ∧ X (wireAvenue R hR q T (X T + i.val)) ≤ ξ + 3)
  refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
  simp only [wireAvenue_x]
  have hx := e.upper
  omega

theorem SlabEntry.radial_profile {R ξ : ℤ} {hR : R % 2 = 0} {q : Quadrant} {T : Site}
    (e : SlabEntry R hR q T ξ) (hq : InQuadrant R q T) (hhigh : |alpha R T| + 8 < rho R T)
    (u : ℤ) (hu : u % 2 = 1) (hup : rho R T + 2 ≤ u)
    (i : Fin (radialHeight R u e.point + 1)) :
    let p := (radialFold R hR q e.point u).pos i
    InQuadrant R q p ∧ (rho R T + 2 ≤ rho R p ∧ rho R p ≤ u) ∧
      (alpha R p = alpha R T ∨ alpha R p = alpha R T + 2) ∧
      (ξ - 1 ≤ X p ∧ X p ≤ ξ + 4) := by
  have he := e.point_profile hq hhigh
  have hp := radialFold_profile R hR q e.point he.1 u hu (by omega) i
  refine ⟨hp.1, ?_, ?_, ?_⟩
  · rw [he.2.1] at hp
    exact hp.2.1
  · rw [hp.2.2.1]
    exact he.2.2.1
  · have hx := hp.2.2.2
    omega

end ProteinFolding.Tetrahedral.FarField
