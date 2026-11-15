import ProteinFolding.Tetrahedral.FarFieldWires

/-! Separation of the actual finite avenue and radial-arm paths in Stage B.
The descending-level slab order resolves every radial/avenue crossing. -/

namespace ProteinFolding.Tetrahedral.FarField.WireData

variable {w : ℕ} (d : WireData w)

theorem avenue_paths_disjoint (i j : Fin w) (hne : i ≠ j) :
    Disjoint (Set.range (d.entries i).avenueFold.pos) (Set.range (d.entries j).avenueFold.pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨a, rfl⟩ ⟨b, heq⟩
  have h : levelAvenue d.R d.R_even d.H d.quadrants d.bases i (X (d.tops i) + a.val) =
      levelAvenue d.R d.R_even d.H d.quadrants d.bases j (X (d.tops j) + b.val) := by
    simpa only [SlabEntry.avenueFold, intervalFold, ite_true, levelAvenue, tops] using heq.symm
  exact levelAvenues_disjoint d.R d.R_even d.H d.H_odd d.quadrants d.bases
    d.positive d.below d.high d.identities i j hne _ _ h

theorem avenue_column_disjoint (i j : Fin w) (hne : i ≠ j) :
    Disjoint (Set.range (d.entries i).avenueFold.pos) (Set.range (d.columns j).pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨a, rfl⟩ ⟨b, heq⟩
  have h : levelAvenue d.R d.R_even d.H d.quadrants d.bases i (X (d.tops i) + a.val) =
      (columnFold d.R d.R_even d.H d.quadrants d.bases j).pos b := by
    simpa only [SlabEntry.avenueFold, intervalFold, ite_true, levelAvenue, tops, columns] using heq.symm
  exact levelAvenue_other_column d.R d.R_even d.H d.H_odd d.quadrants d.bases
    d.positive d.below d.high d.identities i j hne _
    (by change X (d.tops i) ≤ X (d.tops i) + a.val; omega) b h

theorem radial_column_disjoint (i j : Fin w) (u : ℤ) (hu : u % 2 = 1) (hui : d.levels i + 2 ≤ u) :
    Disjoint (Set.range (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u).pos)
      (Set.range (d.columns j).pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨a, rfl⟩ ⟨b, heq⟩
  have ha := d.radial_paths_profile i u hu hui a
  have hb := columnFold_profile d.R d.R_even d.H d.H_odd d.quadrants d.bases j
    (d.positive j) (d.below j) b
  change _ ∧ _ ∧ _ ∧ (_ ≤ X ((d.columns j).pos b) ∧ X ((d.columns j).pos b) ≤ _) at hb
  rw [heq] at hb
  have hx := d.x_below j
  have hs := (slabValue_bounds d.H d.levels i).1
  change d.H + 60 ≤ d.slabs i at hs
  omega

theorem radial_avenue_disjoint (i j : Fin w) (hne : i ≠ j) (u : ℤ)
    (hu : u % 2 = 1) (hui : d.levels i + 2 ≤ u) :
    Disjoint (Set.range (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u).pos)
      (Set.range (d.entries j).avenueFold.pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨a, rfl⟩ ⟨b, heq⟩
  have ha := d.radial_paths_profile i u hu hui a
  have hb := d.avenue_paths_profile j b
  rw [heq] at hb
  have hq := quadrant_unique d.R (d.quadrants i) (d.quadrants j) _ ha.1 hb.1
  rcases lt_trichotomy (d.levels i) (d.levels j) with hlt | hlev | hgt
  · have horder := slabValue_order d.H d.levels j i hlt
    change d.slabs j < d.slabs i at horder
    have hsep := slabValue_separated d.H d.levels i j hne
    change d.slabs i + 60 ≤ d.slabs j ∨ d.slabs j + 60 ≤ d.slabs i at hsep
    omega
  · have hsep := same_level_strips_separated d.R d.H d.quadrants d.bases d.positive d.identities
      i j hne hq hlev
    omega
  · have hnelev : assignedLevel d.H (wireBaseXs d.quadrants d.bases) i ≠
        assignedLevel d.H (wireBaseXs d.quadrants d.bases) j := by
      change d.levels i ≠ d.levels j
      omega
    have hsep := assignedLevel_separated d.H (wireBaseXs d.quadrants d.bases) i j hnelev
    change d.levels i + 4 ≤ d.levels j ∨ d.levels j + 4 ≤ d.levels i at hsep
    omega

theorem own_avenue_radial_intersection (i : Fin w) (u : ℤ) (hu : u % 2 = 1)
    (hui : d.levels i + 2 ≤ u) (a : Fin ((d.entries i).avenueEdges + 1))
    (b : Fin (radialHeight d.R u (d.entries i).point + 1))
    (heq : (d.entries i).avenueFold.pos a =
      (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u).pos b) :
    a.val + 1 = (d.entries i).avenueEdges + 1 ∧ b.val = 0 := by
  have ha := d.avenue_paths_profile i a
  have hpoint := d.entries_profile i
  have hrad := radialPosition_profile d.R d.R_even (d.quadrants i) (d.entries i).point b.val hpoint.1 (by omega)
  have hρ := congrArg (rho d.R) heq
  change rho d.R ((d.entries i).avenueFold.pos a) =
    rho d.R (radialPosition d.R d.R_even (d.quadrants i) (d.entries i).point (0 + b.val)) at hρ
  simp only [zero_add] at hρ
  have hb : b.val = 0 := by omega
  have hfirst := radialFold_first d.R d.R_even (d.quadrants i) (d.entries i).point u b hb
  rw [hfirst] at heq
  have hx := congrArg X heq
  change X (wireAvenue d.R d.R_even (d.quadrants i) (d.tops i) (X (d.tops i) + a.val)) =
    X (d.entries i).point at hx
  simp only [wireAvenue_x, SlabEntry.point] at hx
  have hedges := (d.entries i).avenueEdges_exact (le_of_lt (d.tops_before_slab i))
  exact ⟨by omega, hb⟩

end ProteinFolding.Tetrahedral.FarField.WireData
