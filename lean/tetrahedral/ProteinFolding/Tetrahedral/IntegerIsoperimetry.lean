import ProteinFolding.Tetrahedral.SiteProfile
import ProteinFolding.Tetrahedral.CompositionBound
import ProteinFolding.Tetrahedral.FoldCounting

/-!
# The sharp bound at octahedral site numbers (Corollary 4)

The exact composition bound suffices for this integer consequence without
using the real integral inequality: if the run mass were smaller than 2m²,
appending a positive part would strictly increase the relaxed value.
-/

namespace ProteinFolding.Tetrahedral

theorem octahedralNumber_pos (m : ℕ) (hm : 0 < m) : 0 < octahedralNumber m := by
  unfold octahedralNumber
  nlinarith

/-- A finite set of N_m sites has run mass at least 2m². -/
theorem totalRuns_ge_octahedral (S : Finset Site) (m : ℕ) (hm : 0 < m)
    (hcard : S.card = octahedralNumber m) : 2 * m ^ 2 ≤ totalRuns S := by
  have hN := octahedralNumber_pos m hm
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hmass, hvalue⟩ := exists_composition_of_site_profile S hne
  by_contra hnot
  let d := 2 * m ^ 2 - c.mass
  have hd : 0 < d := by dsimp [d]; omega
  have hnew : (PositiveComposition.snoc c d hd).mass = 2 * m ^ 2 := by
    change c.mass + d = 2 * m ^ 2
    dsimp [d]
    omega
  have hstrict := twoSidedValue_snoc_strict c d hd
  have hupper := composition_bound m hm (.snoc c d hd) hnew
  omega

/-- Corollary 4's boundary lower bound, uniformly for all finite site sets. -/
theorem boundaryCount_ge_octahedral (S : Finset Site) (m : ℕ) (hm : 0 < m)
    (hcard : S.card = octahedralNumber m) : 4 * m ^ 2 ≤ boundaryCount S := by
  have h := totalRuns_ge_octahedral S m hm hcard
  rw [boundaryCount_eq_twice_totalRuns]
  omega

theorem internalEdgeCount_add_bound (S : Finset Site) (m : ℕ) (hm : 0 < m)
    (hcard : S.card = octahedralNumber m) :
    internalEdgeCount S + 2 * m ^ 2 ≤ 2 * octahedralNumber m := by
  have hb := boundaryCount_ge_octahedral S m hm hcard
  have hd := degree_boundary_identity S
  rw [hcard] at hd
  omega

/-- The contact upper bound used by the NP-hardness reduction. -/
theorem internalEdgeCount_octahedral_bound (S : Finset Site) (m : ℕ) (hm : 0 < m)
    (hcard : S.card = octahedralNumber m) :
    internalEdgeCount S ≤ 2 * octahedralNumber m - 2 * m ^ 2 := by
  have h := internalEdgeCount_add_bound S m hm hcard
  omega

theorem bondCount_octahedral_bound (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hm : 0 < m) (hcount : hydrophobicCount S = octahedralNumber m) :
    bondCount S f ≤ 2 * octahedralNumber m - 2 * m ^ 2 := by
  rw [bondCount_eq_internalEdgeCount]
  apply internalEdgeCount_octahedral_bound _ m hm
  rw [hSupport_card, hcount]

theorem bondCount_octahedral_bound_int (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hm : 0 < m) (hcount : hydrophobicCount S = octahedralNumber m) :
    (bondCount S f : ℤ) ≤ 2 * (octahedralNumber m : ℤ) - 2 * (m ^ 2 : ℕ) := by
  have h := internalEdgeCount_add_bound (hSupport S f) m hm (by rw [hSupport_card, hcount])
  rw [← bondCount_eq_internalEdgeCount] at h
  omega

/-- A contact-maximizing set has exactly the boundary/run mass for Claim U. -/
theorem extremal_boundaryCount (S : Finset Site) (m : ℕ)
    (hcard : S.card = octahedralNumber m)
    (hedges : internalEdgeCount S = 2 * octahedralNumber m - 2 * m ^ 2) :
    boundaryCount S = 4 * m ^ 2 := by
  have hN : m ^ 2 ≤ octahedralNumber m := by unfold octahedralNumber; omega
  have h := degree_boundary_identity S
  rw [hcard, hedges] at h
  omega

theorem extremal_totalRuns (S : Finset Site) (m : ℕ)
    (hcard : S.card = octahedralNumber m)
    (hedges : internalEdgeCount S = 2 * octahedralNumber m - 2 * m ^ 2) :
    totalRuns S = 2 * m ^ 2 := by
  have h := extremal_boundaryCount S m hcard hedges
  rw [boundaryCount_eq_twice_totalRuns] at h
  omega

/-- In the extremal case every inequality in the composition relaxation is
tight, and Claim U supplies its canonical equality profile. -/
theorem extremal_composition (S : Finset Site) (m : ℕ) (hm : 0 < m)
    (hcard : S.card = octahedralNumber m)
    (hedges : internalEdgeCount S = 2 * octahedralNumber m - 2 * m ^ 2) :
    ∃ c : PositiveComposition, c.mass = 2 * m ^ 2 ∧
      twoSidedValue c = octahedralNumber m ∧
      c.parts = (canonicalSquare (m - 1)).parts ++ (canonicalSquare (m - 1)).parts.reverse := by
  have hN := octahedralNumber_pos m hm
  obtain ⟨c, hmass, hvalue⟩ := exists_composition_of_site_profile S
    (Finset.card_pos.mp (by omega))
  have hruns := extremal_totalRuns S m hcard hedges
  have hc : c.mass = 2 * m ^ 2 := by omega
  have hupper := composition_bound m hm c hc
  have heq : twoSidedValue c = octahedralNumber m := by omega
  exact ⟨c, hc, heq, composition_bound_equality m hm c hc heq⟩

end ProteinFolding.Tetrahedral
