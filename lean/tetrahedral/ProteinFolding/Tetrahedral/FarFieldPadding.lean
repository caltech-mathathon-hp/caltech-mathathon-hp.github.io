import ProteinFolding.Tetrahedral.FarFieldPaddingPath
import ProteinFolding.Tetrahedral.FarFieldCoordinates

/-! Every even increase at least six is realized by an actual self-avoiding
diamond-lattice path on the two private avenues, with its endpoints fixed. -/

namespace ProteinFolding.Tetrahedral.FarField

theorem paddingFold_first (c : Site) (hc : InASublattice c.val) (up : Bool)
    (r b : ℕ) (δ η : Bool) (d : ℕ) (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b)
    (i : Fin (routeLength r b δ η d)) (hi : i.val = 0) :
    (paddingFold c hc up r b δ η d hr hb).pos i = avenue c hc up r := by
  change avenueSite c hc up (routeIndex r b δ η d i.val) = _
  rw [hi, routeIndex_first r b δ η d hr]
  rfl

theorem paddingFold_last (c : Site) (hc : InASublattice c.val) (up : Bool)
    (r b : ℕ) (δ η : Bool) (d : ℕ) (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b)
    (i : Fin (routeLength r b δ η d)) (hi : i.val + 1 = routeLength r b δ η d) :
    (paddingFold c hc up r b δ η d hr hb).pos i = avenue c hc up b := by
  change avenueSite c hc up (routeIndex r b δ η d i.val) = _
  have hi' : i.val = routeLength r b δ η d - 1 := by omega
  rw [hi', routeIndex_last r b δ η d hr hb]
  rfl

theorem paddingFold_private (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool)
    (r b : ℕ) (δ η : Bool) (d : ℕ) (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) (i : Fin (routeLength r b δ η d)) :
    let p := (paddingFold c hc up r b δ η d hr hb).pos i
    PositiveQuadrant R p ∧
      (rho R p = privateLevel R c up ∨ rho R p = privateLevel R c up + 2) ∧
      (alpha R p = privateStrip R c ∨ alpha R p = privateStrip R c + 2 ∨
        alpha R p = privateStrip R c + 4 ∨ alpha R p = privateStrip R c + 6) :=
  avenueSite_private R c hc up _ hy hz

/-- Local geometric padding lemma. Length counts sites, including both
endpoints, exactly as required by Lemma F. The Fold witness provides
injectivity and every consecutive lattice edge. -/
theorem exists_even_padding_path (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool)
    (r b Δ : ℕ) (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b)
    (hΔ : 6 ≤ Δ) (heven : Δ % 2 = 0) (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) :
    ∃ (n : ℕ) (f : Fold tetrahedralLattice n),
      n = b - r + 1 + Δ ∧
      (∀ i, i.val = 0 → f.pos i = avenue c hc up r) ∧
      (∀ i, i.val + 1 = n → f.pos i = avenue c hc up b) ∧
      (∀ i, PositiveQuadrant R (f.pos i) ∧
        (rho R (f.pos i) = privateLevel R c up ∨ rho R (f.pos i) = privateLevel R c up + 2) ∧
        (alpha R (f.pos i) = privateStrip R c ∨ alpha R (f.pos i) = privateStrip R c + 2 ∨
          alpha R (f.pos i) = privateStrip R c + 4 ∨ alpha R (f.pos i) = privateStrip R c + 6)) := by
  have hr' : (r : ℤ) = 2 ∨ (r : ℤ) = 3 := by omega
  obtain ⟨δ, η, d, hp⟩ := padding_parameters r Δ hr' (by omega) (by omega)
  refine ⟨routeLength r b δ η d, paddingFold c hc up r b δ η d hr hb, ?_,
    paddingFold_first c hc up r b δ η d hr hb,
    paddingFold_last c hc up r b δ η d hr hb, ?_⟩
  · have hn := routeLength_exact r b δ η d hr hb
    omega
  · intro i
    exact paddingFold_private R c hc up r b δ η d hr hb hy hz i

end ProteinFolding.Tetrahedral.FarField
