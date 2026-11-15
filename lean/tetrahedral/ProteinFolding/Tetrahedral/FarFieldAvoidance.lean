import ProteinFolding.Tetrahedral.FarFieldPadding

/-! The avoidance consequences of private levels/strips. These lemmas state
their needed geometric separation hypotheses explicitly; they do not assume
the unfinished routing construction of Lemma F(A-C). -/

namespace ProteinFolding.Tetrahedral.FarField

theorem paths_disjoint_of_levels {n k : ℕ} (R u v : ℤ)
    (f : Fold tetrahedralLattice n) (g : Fold tetrahedralLattice k)
    (hf : ∀ i, rho R (f.pos i) = u ∨ rho R (f.pos i) = u + 2)
    (hg : ∀ j, rho R (g.pos j) = v ∨ rho R (g.pos j) = v + 2)
    (hgap : u + 4 ≤ v ∨ v + 4 ≤ u) :
    Disjoint (Set.range f.pos) (Set.range g.pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨i, rfl⟩ ⟨j, h⟩
  have hi := hf i
  have hj := hg j
  rw [h] at hj
  omega

theorem paddingFold_avoids_below (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool)
    (r b : ℕ) (δ η : Bool) (d : ℕ) (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) (p : Site) (hp : rho R p < privateLevel R c up) :
    p ∉ Set.range (paddingFold c hc up r b δ η d hr hb).pos := by
  rintro ⟨i, rfl⟩
  have h := paddingFold_private R c hc up r b δ η d hr hb hy hz i
  omega

theorem paddingFold_avoids_lower_strip (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool)
    (r b : ℕ) (δ η : Bool) (d : ℕ) (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) (p : Site) (hp : alpha R p < privateStrip R c) :
    p ∉ Set.range (paddingFold c hc up r b δ η d hr hb).pos := by
  rintro ⟨i, rfl⟩
  have h := paddingFold_private R c hc up r b δ η d hr hb hy hz i
  omega

theorem paddingFold_in_avenues (c : Site) (hc : InASublattice c.val) (up : Bool)
    (r b : ℕ) (δ η : Bool) (d : ℕ) (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b)
    (i : Fin (routeLength r b δ η d)) :
    ∃ x, (paddingFold c hc up r b δ η d hr hb).pos i = avenue c hc up x ∨
      (paddingFold c hc up r b δ η d hr hb).pos i = secondAvenue c hc up x := by
  change ∃ x, avenueSite c hc up (routeIndex r b δ η d i.val) = avenue c hc up x ∨
    avenueSite c hc up (routeIndex r b δ η d i.val) = secondAvenue c hc up x
  obtain ⟨tag, x⟩ := routeIndex r b δ η d i.val
  refine ⟨x, ?_⟩
  cases tag <;> simp [avenueSite]

theorem paddingFold_approach_intersection (c : Site) (hc : InASublattice c.val) (up : Bool)
    (r b : ℕ) (δ η : Bool) (d : ℕ) (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b)
    (approach : Set Site)
    (ha : ∀ x, avenue c hc up x ∈ approach → x = r ∨ x = b)
    (hb' : ∀ x, secondAvenue c hc up x ∉ approach)
    (i : Fin (routeLength r b δ η d))
    (hi : (paddingFold c hc up r b δ η d hr hb).pos i ∈ approach) :
    (paddingFold c hc up r b δ η d hr hb).pos i = avenue c hc up r ∨
      (paddingFold c hc up r b δ η d hr hb).pos i = avenue c hc up b := by
  obtain ⟨x, hx | hx⟩ := paddingFold_in_avenues c hc up r b δ η d hr hb i
  · rw [hx] at hi ⊢
    rcases ha x hi with h | h <;> simp [h]
  · rw [hx] at hi
    exact False.elim (hb' x hi)

end ProteinFolding.Tetrahedral.FarField
