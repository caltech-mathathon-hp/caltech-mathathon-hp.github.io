import ProteinFolding.Tetrahedral.FarFieldStageA
import ProteinFolding.Tetrahedral.FarFieldSlabEntries

/-! Finite input data for the far-field routing construction. These are
local arm starts and their proved free-column invariants, not a premise that
any linker routes exist. All levels, slabs, column paths and slab entries are
constructed from this data in the definitions below. -/

namespace ProteinFolding.Tetrahedral.FarField

structure WireData (w : ℕ) where
  R : ℤ
  R_even : R % 2 = 0
  H : ℤ
  H_odd : H % 2 = 1
  quadrants : Fin w → Quadrant
  bases : Fin w → Site
  positive : ∀ i, PositiveQuadrant R (bases i)
  below : ∀ i, rho R (bases i) ≤ H
  high : ∀ i, |alpha R (bases i)| + 8 < H
  x_below : ∀ i, wireBaseXs quadrants bases i + 1 < H
  identities : Function.Injective (fun i => armIdentity R (quadrants i) (bases i))

namespace WireData

variable {w : ℕ} (d : WireData w)

def levels : Fin w → ℤ := wireLevels d.H d.quadrants d.bases
def slabs : Fin w → ℤ := slabValue d.H d.levels
def tops (i : Fin w) : Site := columnTop d.R d.R_even d.H d.quadrants d.bases i
def columns (i : Fin w) := columnFold d.R d.R_even d.H d.quadrants d.bases i
def avenues (i : Fin w) : ℤ → Site := levelAvenue d.R d.R_even d.H d.quadrants d.bases i

theorem tops_profile (i : Fin w) :
    InQuadrant d.R (d.quadrants i) (d.tops i) ∧ rho d.R (d.tops i) = d.levels i ∧
      alpha d.R (d.tops i) = alpha d.R (d.bases i) ∧
      (wireBaseXs d.quadrants d.bases i ≤ X (d.tops i) ∧
        X (d.tops i) ≤ wireBaseXs d.quadrants d.bases i + 1) :=
  columnTop_profile d.R d.R_even d.H d.H_odd d.quadrants d.bases i (d.positive i) (d.below i)

theorem tops_high (i : Fin w) : |alpha d.R (d.tops i)| + 8 < rho d.R (d.tops i) := by
  have ht := d.tops_profile i
  have hlev := (assignedLevel_bounds d.H (wireBaseXs d.quadrants d.bases) i).1
  rw [ht.2.1, ht.2.2.1]
  change d.H ≤ d.levels i at hlev
  have hh := d.high i
  omega

theorem tops_before_slab (i : Fin w) : X (d.tops i) < d.slabs i := by
  have ht := d.tops_profile i
  have hx := d.x_below i
  have hs := (slabValue_bounds d.H d.levels i).1
  change d.H + 60 ≤ d.slabs i at hs
  omega

noncomputable def entries (i : Fin w) : SlabEntry d.R d.R_even (d.quadrants i) (d.tops i) (d.slabs i) :=
  Classical.choice (slabEntry_exists d.R d.R_even (d.quadrants i) (d.tops i) (d.slabs i)
    (d.tops_profile i).1 (d.tops_high i))

theorem entries_profile (i : Fin w) :
    InQuadrant d.R (d.quadrants i) (d.entries i).point ∧
      rho d.R (d.entries i).point = d.levels i + 2 ∧
      (alpha d.R (d.entries i).point = alpha d.R (d.bases i) ∨
        alpha d.R (d.entries i).point = alpha d.R (d.bases i) + 2) ∧
      (d.slabs i ≤ X (d.entries i).point ∧ X (d.entries i).point ≤ d.slabs i + 3) := by
  have h := (d.entries i).point_profile (d.tops_profile i).1 (d.tops_high i)
  simpa only [(d.tops_profile i).2.1, (d.tops_profile i).2.2.1] using h

theorem avenue_paths_profile (i : Fin w) (k : Fin ((d.entries i).avenueEdges + 1)) :
    let p := (d.entries i).avenueFold.pos k
    InQuadrant d.R (d.quadrants i) p ∧ (rho d.R p = d.levels i ∨ rho d.R p = d.levels i + 2) ∧
      (alpha d.R p = alpha d.R (d.bases i) ∨ alpha d.R p = alpha d.R (d.bases i) + 2) ∧
      (X (d.tops i) ≤ X p ∧ X p ≤ d.slabs i + 3) := by
  have h := (d.entries i).avenueFold_profile (le_of_lt (d.tops_before_slab i))
    (d.tops_profile i).1 (d.tops_high i) k
  simpa only [(d.tops_profile i).2.1, (d.tops_profile i).2.2.1] using h

theorem radial_paths_profile (i : Fin w) (u : ℤ) (hu : u % 2 = 1) (hup : d.levels i + 2 ≤ u)
    (k : Fin (radialHeight d.R u (d.entries i).point + 1)) :
    let p := (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u).pos k
    InQuadrant d.R (d.quadrants i) p ∧ (d.levels i + 2 ≤ rho d.R p ∧ rho d.R p ≤ u) ∧
      (alpha d.R p = alpha d.R (d.bases i) ∨ alpha d.R p = alpha d.R (d.bases i) + 2) ∧
      (d.slabs i - 1 ≤ X p ∧ X p ≤ d.slabs i + 4) := by
  have ht := d.tops_profile i
  have hp : rho d.R (d.tops i) + 2 ≤ u := by rw [ht.2.1]; exact hup
  have h := (d.entries i).radial_profile ht.1 (d.tops_high i) u hu hp k
  simpa only [ht.2.1, ht.2.2.1] using h

theorem radial_paths_disjoint (i j : Fin w) (hne : i ≠ j) (u v : ℤ)
    (hu : u % 2 = 1) (hv : v % 2 = 1) (hui : d.levels i + 2 ≤ u) (hvj : d.levels j + 2 ≤ v) :
    Disjoint (Set.range (radialFold d.R d.R_even (d.quadrants i) (d.entries i).point u).pos)
      (Set.range (radialFold d.R d.R_even (d.quadrants j) (d.entries j).point v).pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨a, rfl⟩ ⟨b, heq⟩
  have ha := d.radial_paths_profile i u hu hui a
  have hb := d.radial_paths_profile j v hv hvj b
  rw [heq] at hb
  have hsep := slabValue_separated d.H d.levels i j hne
  change d.slabs i + 60 ≤ d.slabs j ∨ d.slabs j + 60 ≤ d.slabs i at hsep
  omega

end WireData

end ProteinFolding.Tetrahedral.FarField
