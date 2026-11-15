import ProteinFolding.Tetrahedral.FarFieldColumnAvenuePaths

namespace ProteinFolding.Tetrahedral.FarField.WireData

variable {w : ℕ} (d : WireData w)

noncomputable def prefixSites (i : Fin w) (u : ℤ) : ℕ :=
  d.columnAvenueSites i + (radialHeight d.R u (d.entries i).point + 1) - 1

theorem prefix_join (i : Fin w) (u : ℤ) :
    (d.columnAvenuePath i).pos ⟨d.columnAvenueSites i - 1, by have h := d.columnAvenueSites_pos i; omega⟩ =
      (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u).pos ⟨0, by omega⟩ := by
  have ha := d.columnAvenuePath_last i ⟨d.columnAvenueSites i - 1, by have h := d.columnAvenueSites_pos i; omega⟩
    (by change d.columnAvenueSites i - 1 + 1 = d.columnAvenueSites i; have h := d.columnAvenueSites_pos i; omega)
  have hb := radialFold_first d.R d.R_even (d.quadrants i) (d.entries i).point u ⟨0, by omega⟩ rfl
  exact ha.trans hb.symm

theorem prefix_intersection (i : Fin w) (u : ℤ) (hu : u % 2 = 1) (hui : d.levels i + 2 ≤ u)
    (a : Fin (d.columnAvenueSites i)) (b : Fin (radialHeight d.R u (d.entries i).point + 1))
    (heq : (d.columnAvenuePath i).pos a = (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u).pos b) :
    a.val + 1 = d.columnAvenueSites i ∧ b.val = 0 := by
  have hb : b.val = 0 := by
    rcases d.columnAvenuePath_pos_cases i a with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hd := d.radial_column_disjoint i i u hu hui
      exact False.elim (Set.disjoint_left.mp hd ⟨b, rfl⟩ ⟨c, hc.trans heq⟩)
    · exact (d.own_avenue_radial_intersection i u hu hui c b (hc.trans heq)).2
  have hl := d.columnAvenuePath_last i
    ⟨d.columnAvenueSites i - 1, by have h := d.columnAvenueSites_pos i; omega⟩
    (by change d.columnAvenueSites i - 1 + 1 = d.columnAvenueSites i; have h := d.columnAvenueSites_pos i; omega)
  have hr := radialFold_first d.R d.R_even (d.quadrants i) (d.entries i).point u b hb
  have heq' := (d.columnAvenuePath i).injective_pos (heq.trans (hr.trans hl.symm))
  have hav := congrArg (fun x : Fin (d.columnAvenueSites i) => x.val) heq'
  change a.val = d.columnAvenueSites i - 1 at hav
  have hpos := d.columnAvenueSites_pos i
  exact ⟨by omega, hb⟩

noncomputable def prefixPath (i : Fin w) (u : ℤ) (hu : u % 2 = 1) (hui : d.levels i + 2 ≤ u) :
    Fold tetrahedralLattice (d.prefixSites i u) :=
  glue (d.columnAvenuePath i) (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u)
    (d.columnAvenueSites_pos i) (by omega) (d.prefix_join i u)
    (fun a b heq => d.prefix_intersection i u hu hui a b heq)

theorem prefixSites_pos (i : Fin w) (u : ℤ) : 0 < d.prefixSites i u := by
  have h := d.columnAvenueSites_pos i
  unfold prefixSites
  omega

theorem prefixPath_first (i : Fin w) (u : ℤ) (hu : u % 2 = 1) (hui : d.levels i + 2 ≤ u)
    (k : Fin (d.prefixSites i u)) (hk : k.val = 0) :
    (d.prefixPath i u hu hui).pos k = quadrantMap d.R d.R_even (d.quadrants i) (d.bases i) := by
  have h := glue_first (d.columnAvenuePath i) (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u)
    (d.columnAvenueSites_pos i) (by omega) (d.prefix_join i u)
    (fun a b heq => d.prefix_intersection i u hu hui a b heq) k hk
  exact h.trans (d.columnAvenuePath_first i ⟨0, d.columnAvenueSites_pos i⟩ rfl)

theorem prefixPath_last (i : Fin w) (u : ℤ) (hu : u % 2 = 1) (hui : d.levels i + 2 ≤ u)
    (k : Fin (d.prefixSites i u)) (hk : k.val + 1 = d.prefixSites i u) :
    (d.prefixPath i u hu hui).pos k = radialTop d.R d.R_even (d.quadrants i) (d.entries i).point u := by
  have h := glue_last (d.columnAvenuePath i) (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u)
    (d.columnAvenueSites_pos i) (by omega) (d.prefix_join i u)
    (fun a b heq => d.prefix_intersection i u hu hui a b heq) k hk
  exact h.trans (radialFold_last d.R d.R_even (d.quadrants i) (d.entries i).point u _
    (by change radialHeight d.R u (d.entries i).point + 1 - 1 = radialHeight d.R u (d.entries i).point; omega))

theorem prefixPath_range (i : Fin w) (u : ℤ) (hu : u % 2 = 1) (hui : d.levels i + 2 ≤ u) :
    Set.range (d.prefixPath i u hu hui).pos ⊆ Set.range (d.columnAvenuePath i).pos ∪
      Set.range (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u).pos := by
  rintro p ⟨k, rfl⟩
  exact glue_pos_cases (d.columnAvenuePath i) (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u)
    (d.columnAvenueSites_pos i) (by omega) (d.prefix_join i u)
    (fun a b heq => d.prefix_intersection i u hu hui a b heq) k

theorem columnAvenue_radial_disjoint (i j : Fin w) (hne : i ≠ j) (u : ℤ) (hu : u % 2 = 1)
    (huj : d.levels j + 2 ≤ u) :
    Disjoint (Set.range (d.columnAvenuePath i).pos)
      (Set.range (radialFold d.R d.R_even (d.quadrants j) (d.entries j).point u).pos) := by
  have hc := (d.radial_column_disjoint j i u hu huj).symm
  have ha := (d.radial_avenue_disjoint j i hne.symm u hu huj).symm
  have hUnion : Disjoint (Set.range (d.columns i).pos ∪ Set.range (d.entries i).avenueFold.pos)
      (Set.range (radialFold d.R d.R_even (d.quadrants j) (d.entries j).point u).pos) :=
    Set.disjoint_union_left.mpr ⟨hc, ha⟩
  exact hUnion.mono (d.columnAvenuePath_range i) (Set.Subset.refl _)

theorem prefixPaths_disjoint (i j : Fin w) (hne : i ≠ j) (u v : ℤ)
    (hu : u % 2 = 1) (hv : v % 2 = 1) (hui : d.levels i + 2 ≤ u) (hvj : d.levels j + 2 ≤ v) :
    Disjoint (Set.range (d.prefixPath i u hu hui).pos) (Set.range (d.prefixPath j v hv hvj).pos) := by
  have haa := d.columnAvenuePaths_disjoint i j hne
  have har := d.columnAvenue_radial_disjoint i j hne v hv hvj
  have hra := (d.columnAvenue_radial_disjoint j i hne.symm u hu hui).symm
  have hrr := d.radial_paths_disjoint i j hne u v hu hv hui hvj
  have hUnion : Disjoint
      (Set.range (d.columnAvenuePath i).pos ∪ Set.range (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u).pos)
      (Set.range (d.columnAvenuePath j).pos ∪ Set.range (radialFold d.R d.R_even (d.quadrants j) (d.entries j).point v).pos) := by
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    exact ⟨⟨haa, har⟩, ⟨hra, hrr⟩⟩
  exact hUnion.mono (d.prefixPath_range i u hu hui) (d.prefixPath_range j v hv hvj)

end ProteinFolding.Tetrahedral.FarField.WireData
