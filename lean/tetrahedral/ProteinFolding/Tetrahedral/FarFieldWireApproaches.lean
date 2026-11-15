import ProteinFolding.Tetrahedral.FarFieldRoutingPlan
import ProteinFolding.Tetrahedral.FarFieldWirePrefixes

namespace ProteinFolding.Tetrahedral.FarField

theorem strip_abs_bound (α β a : ℤ) (hβ : β = α ∨ β = α + 2) (ha : |α| + 6 ≤ a) : |β| + 4 ≤ a := by
  rcases hβ with rfl | rfl
  · omega
  · have h := abs_add_le α 2
    norm_num at h
    omega

namespace RoutingPlan

variable {w : ℕ} {d : WireData w} (p : RoutingPlan d)

theorem own_height (i : Fin w) : d.levels i + 2 ≤ p.heights i := by have h := p.heights_above i i; omega

noncomputable def radialTops (i : Fin w) : Site :=
  radialTop d.R d.R_even (d.quadrants i) (d.entries i).point (p.heights i)

theorem radialTops_profile (i : Fin w) :
    rho d.R (p.radialTops i) = p.heights i ∧
      (alpha d.R (p.radialTops i) = alpha d.R (d.bases i) ∨
        alpha d.R (p.radialTops i) = alpha d.R (d.bases i) + 2) ∧
      (d.slabs i - 1 ≤ X (p.radialTops i) ∧ X (p.radialTops i) ≤ d.slabs i + 4) := by
  let k : Fin (radialHeight d.R (p.heights i) (d.entries i).point + 1) :=
    ⟨radialHeight d.R (p.heights i) (d.entries i).point, by omega⟩
  have hp := d.radial_paths_profile i (p.heights i) (p.heights_odd i) (p.own_height i) k
  have hk := radialFold_last d.R d.R_even (d.quadrants i) (d.entries i).point (p.heights i) k rfl
  rw [hk] at hp
  have he := d.entries_profile i
  have hlev := radialTop_level d.R d.R_even (d.quadrants i) (d.entries i).point he.1
    (p.heights i) (p.heights_odd i) (by have h := p.own_height i; omega)
  exact ⟨hlev, hp.2.2.1, hp.2.2.2⟩

theorem approaches_exists (i : Fin w) : Nonempty (ApproachData d.R (p.heights i) p.a (p.radialTops i)) := by
  have ht := p.radialTops_profile i
  have hroom := p.heights_room i
  have hnon := abs_nonneg p.a
  apply canonical_levelApproach_exists d.R (p.heights i) p.a d.R_even (p.heights_odd i)
    (by omega) p.a_odd hroom (p.radialTops i) ht.1
  exact strip_abs_bound _ _ _ ht.2.1 (p.a_above i)

noncomputable def approaches (i : Fin w) : ApproachData d.R (p.heights i) p.a (p.radialTops i) :=
  Classical.choice (p.approaches_exists i)

theorem approaches_pairwise (i j : Fin w) (hne : i ≠ j) :
    Disjoint (Set.range (p.approaches i).path.pos) (Set.range (p.approaches j).path.pos) := by
  apply approaches_disjoint_slabs (p.approaches i) (p.approaches j)
    (p.radialTops_profile i).2.2 (p.radialTops_profile j).2.2
  exact slabValue_separated d.H d.levels i j hne

theorem approach_column_disjoint (i j : Fin w) :
    Disjoint (Set.range (p.approaches i).path.pos) (Set.range (d.columns j).pos) := by
  apply Set.disjoint_left.mpr
  rintro s ⟨a, rfl⟩ ⟨b, heq⟩
  have ha := (p.approaches i).level a
  have hb := columnFold_profile d.R d.R_even d.H d.H_odd d.quadrants d.bases j (d.positive j) (d.below j) b
  change _ ∧ rho d.R ((d.columns j).pos b) ≤ d.levels j ∧ _ at hb
  rw [heq] at hb
  have hh := p.heights_above i j
  omega

theorem approach_avenue_disjoint (i j : Fin w) :
    Disjoint (Set.range (p.approaches i).path.pos) (Set.range (d.entries j).avenueFold.pos) := by
  apply Set.disjoint_left.mpr
  rintro s ⟨a, rfl⟩ ⟨b, heq⟩
  have ha := (p.approaches i).level a
  have hb := d.avenue_paths_profile j b
  rw [heq] at hb
  have hh := p.heights_above i j
  omega

theorem approach_columnAvenue_disjoint (i j : Fin w) :
    Disjoint (Set.range (p.approaches i).path.pos) (Set.range (d.columnAvenuePath j).pos) := by
  have hu : Disjoint (Set.range (p.approaches i).path.pos)
      (Set.range (d.columns j).pos ∪ Set.range (d.entries j).avenueFold.pos) :=
    Set.disjoint_union_right.mpr ⟨p.approach_column_disjoint i j, p.approach_avenue_disjoint i j⟩
  exact hu.mono (Set.Subset.refl _) (d.columnAvenuePath_range j)

theorem approach_radial_disjoint (i j : Fin w) (hne : i ≠ j) :
    Disjoint (Set.range (p.approaches i).path.pos)
      (Set.range (radialFold d.R d.R_even (d.quadrants j) (d.entries j).point (p.heights j)).pos) := by
  apply Set.disjoint_left.mpr
  rintro s ⟨a, rfl⟩ ⟨b, heq⟩
  have ha := (p.approaches i).slab_window (p.radialTops_profile i).2.2 a
  have hb := d.radial_paths_profile j (p.heights j) (p.heights_odd j) (p.own_height j) b
  rw [heq] at hb
  have hsep := slabValue_separated d.H d.levels i j hne
  change d.slabs i + 60 ≤ d.slabs j ∨ d.slabs j + 60 ≤ d.slabs i at hsep
  omega

theorem approach_prefix_disjoint (i j : Fin w) (hne : i ≠ j) :
    Disjoint (Set.range (p.approaches i).path.pos)
      (Set.range (d.prefixPath j (p.heights j) (p.heights_odd j) (p.own_height j)).pos) := by
  have hu : Disjoint (Set.range (p.approaches i).path.pos)
      (Set.range (d.columnAvenuePath j).pos ∪
        Set.range (radialFold d.R d.R_even (d.quadrants j) (d.entries j).point (p.heights j)).pos) :=
    Set.disjoint_union_right.mpr ⟨p.approach_columnAvenue_disjoint i j, p.approach_radial_disjoint i j hne⟩
  exact hu.mono (Set.Subset.refl _) (d.prefixPath_range j _ _ _)

end RoutingPlan

end ProteinFolding.Tetrahedral.FarField
