import ProteinFolding.Tetrahedral.LayerRigidityRectangleGrid
import ProteinFolding.Tetrahedral.OctahedralLayers
import Mathlib.Data.Int.Interval

/-! A nonempty tight square layer is a consecutive rectangle, up to A-translation. -/

namespace ProteinFolding.Tetrahedral

theorem finite_integer_convex_interval (X : Finset ℤ) (hne : X.Nonempty)
    (hconv : ∀ a ∈ X, ∀ b ∈ X, ∀ u : ℤ, a ≤ u → u ≤ b → u ∈ X) :
    ∃ a : ℤ, ∀ u : ℤ, u ∈ X ↔ a ≤ u ∧ u < a + (X.card : ℤ) := by
  let a := X.min' hne
  let b := X.max' hne
  have ha : a ∈ X := Finset.min'_mem X hne
  have hb : b ∈ X := Finset.max'_mem X hne
  have hab : a ≤ b := Finset.min'_le X b hb
  have hX : X = Finset.Icc a b := by
    ext u
    simp only [Finset.mem_Icc]
    constructor
    · intro hu
      exact ⟨Finset.min'_le X u hu, Finset.le_max' X u hu⟩
    · rintro ⟨hau, hub⟩
      exact hconv a ha b hb u hau hub
  have hcard : (X.card : ℤ) = b + 1 - a := by
    rw [hX]
    exact Int.card_Icc_of_le a b (by omega)
  refine ⟨a, ?_⟩
  intro u
  have hmem : u ∈ X ↔ a ≤ u ∧ u ≤ b := by rw [hX, Finset.mem_Icc]
  rw [hmem]
  omega

theorem tight_layer_grid_interval (S : Finset Site) (c : Site) (hc : c ∈ S)
    (heven : c.val 0 % 2 = 0)
    (htight : (finiteLayer S (c.val 0)).card =
      gapRunCount S (c.val 0 - 1) * gapRunCount S (c.val 0)) :
    ∃ a b : ℤ, ∀ u v : ℤ,
      layerGridPoint c u v ∈ finiteLayer S (c.val 0) ↔
        (a ≤ u ∧ u < a + (gapRunCount S (c.val 0 - 1) : ℤ)) ∧
        (b ≤ v ∧ v < b + (gapRunCount S (c.val 0) : ℤ)) := by
  have hne := occupied_grid_nonempty S c hc
  have hconv := occupied_grid_order_convex S c hc heven htight
  have hcard := occupied_grid_card S c hc heven htight
  obtain ⟨a, ha⟩ := finite_integer_convex_interval (occupiedGridU S c) hne.1 hconv.1
  obtain ⟨b, hb⟩ := finite_integer_convex_interval (occupiedGridV S c) hne.2 hconv.2
  refine ⟨a, b, ?_⟩
  intro u v
  rw [occupied_grid_membership S c heven htight, ha, hb, hcard.1, hcard.2]

theorem layerGridPoint_add (c : Site) (a b u v : ℤ) :
    layerGridPoint (layerGridPoint c a b) u v = layerGridPoint c (a + u) (b + v) := by
  apply Subtype.ext
  funext i
  fin_cases i <;> dsimp [layerGridPoint] <;> omega

theorem layerGridPoint_shift (c : Site) (hcA : InASublattice c.val) (u v : ℕ) :
    shiftSite c hcA (layerGridPoint c (u : ℤ) (v : ℤ)) = evenLayerPoint 0 u v := by
  apply Subtype.ext
  funext i
  fin_cases i <;> dsimp [shiftSite, layerGridPoint, evenLayerPoint, evenLayerCoordinates] <;> omega

/-- The complete consecutive rectangle in an A-layer, with its lower corner as anchor. -/
theorem tight_layer_rectangle (S : Finset Site) (k : ℤ)
    (heven : k % 2 = 0) (hne : 0 < (finiteLayer S k).card)
    (htight : (finiteLayer S k).card = gapRunCount S (k - 1) * gapRunCount S k) :
    ∃ c : Site, c ∈ finiteLayer S k ∧
      ∀ u v : ℤ, layerGridPoint c u v ∈ finiteLayer S k ↔
        (0 ≤ u ∧ u < (gapRunCount S (k - 1) : ℤ)) ∧
        (0 ≤ v ∧ v < (gapRunCount S k : ℤ)) := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hne
  have hpS := (Finset.mem_filter.mp hp).1
  have hpx := (Finset.mem_filter.mp hp).2
  obtain ⟨a, b, hrect⟩ := tight_layer_grid_interval S p hpS (by omega) (by simpa [hpx] using htight)
  have hpos := Nat.pos_of_mul_pos_left (by rw [← htight]; exact hne)
  have hpos' := Nat.pos_of_mul_pos_right (by rw [← htight]; exact hne)
  have hc : layerGridPoint p a b ∈ finiteLayer S k := by
    rw [← hpx, hrect]
    simp only [hpx]
    exact ⟨⟨le_refl _, by omega⟩, ⟨le_refl _, by omega⟩⟩
  refine ⟨layerGridPoint p a b, hc, ?_⟩
  intro u v
  rw [layerGridPoint_add, ← hpx, hrect]
  simp only [hpx]
  omega

/-- A tight m-by-m A-layer becomes the canonical central square after translating
its lower corner to the origin. -/
theorem tight_square_layer_normalizes (S : Finset Site) (k : ℤ) (m : ℕ)
    (hm : 0 < m) (heven : k % 2 = 0)
    (hleft : gapRunCount S (k - 1) = m) (hright : gapRunCount S k = m)
    (hcard : (finiteLayer S k).card = m ^ 2) :
    ∃ (c : Site) (hcA : InASublattice c.val), c ∈ finiteLayer S k ∧
      (finiteLayer S k).image (shiftSite c hcA) = finiteLayer (octahedron m) 0 := by
  have hne : 0 < (finiteLayer S k).card := by rw [hcard]; positivity
  have htight : (finiteLayer S k).card = gapRunCount S (k - 1) * gapRunCount S k := by
    rw [hcard, hleft, hright, Nat.pow_two]
  obtain ⟨c, hc, hrect⟩ := tight_layer_rectangle S k heven hne htight
  have hcx := (Finset.mem_filter.mp hc).2
  have hcA : InASublattice c.val := (inA_iff_x_even c).mpr (by omega)
  refine ⟨c, hcA, hc, ?_⟩
  have himage : evenLayerImage m 0 = finiteLayer (octahedron m) 0 := by
    simpa using evenLayerImage_eq_finiteLayer m 0
  rw [← himage]
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hqx := (Finset.mem_filter.mp hq).2
    obtain ⟨u, v, hqgrid⟩ := exists_layerGridPoint c q (by omega)
    have hrange := (hrect u v).mp (hqgrid ▸ hq)
    rw [hleft, hright] at hrange
    let un := u.toNat
    let vn := v.toNat
    have hu : (un : ℤ) = u := by dsimp [un]; omega
    have hv : (vn : ℤ) = v := by dsimp [vn]; omega
    have hum : un < m - 0 := by omega
    have hvm : vn < m - 0 := by omega
    apply Finset.mem_image.mpr
    refine ⟨(⟨un, hum⟩, ⟨vn, hvm⟩), Finset.mem_univ _, ?_⟩
    change evenLayerPoint 0 un vn = shiftSite c hcA q
    rw [← hqgrid, ← hu, ← hv, layerGridPoint_shift]
  · intro p hp
    obtain ⟨⟨u, v⟩, _, rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_image.mpr
    refine ⟨layerGridPoint c (u.val : ℤ) (v.val : ℤ), ?_, layerGridPoint_shift c hcA u.val v.val⟩
    rw [hrect, hleft, hright]
    exact ⟨⟨by omega, by exact_mod_cast u.isLt⟩, ⟨by omega, by exact_mod_cast v.isLt⟩⟩

end ProteinFolding.Tetrahedral
