import ProteinFolding.Tetrahedral.LayerRigidityRectangleHelpers

/-! Tight layer products are Cartesian products of consecutive grid indices. -/

namespace ProteinFolding.Tetrahedral

def layerGridU (c p : Site) : ℤ :=
  (p.val 1 + p.val 2 - c.val 1 - c.val 2) / 4

def layerGridV (c p : Site) : ℤ :=
  (p.val 1 - p.val 2 - c.val 1 + c.val 2) / 4

@[simp] theorem layerGridU_point (c : Site) (u v : ℤ) :
    layerGridU c (layerGridPoint c u v) = u := by
  dsimp [layerGridU, layerGridPoint]
  omega

@[simp] theorem layerGridV_point (c : Site) (u v : ℤ) :
    layerGridV c (layerGridPoint c u v) = v := by
  dsimp [layerGridV, layerGridPoint]
  omega

theorem layerGridPoint_coordinates (c p : Site) (hx : p.val 0 = c.val 0) :
    layerGridPoint c (layerGridU c p) (layerGridV c p) = p := by
  obtain ⟨u, v, rfl⟩ := exists_layerGridPoint c p hx
  simp

def occupiedGridU (S : Finset Site) (c : Site) : Finset ℤ :=
  (finiteLayer S (c.val 0)).image (layerGridU c)

def occupiedGridV (S : Finset Site) (c : Site) : Finset ℤ :=
  (finiteLayer S (c.val 0)).image (layerGridV c)

theorem layer_left_key_grid (c p : Site) (hx : p.val 0 = c.val 0)
    (heven : c.val 0 % 2 = 0) :
    gapChainKey (c.val 0 - 1) p = gapChainKey (c.val 0 - 1) c + 4 * layerGridU c p := by
  rw [← layerGridPoint_coordinates c p hx]
  simp only [layerGridPoint_left_key c _ _ heven, layerGridU_point]

theorem layer_right_key_grid (c p : Site) (hx : p.val 0 = c.val 0)
    (heven : c.val 0 % 2 = 0) :
    gapChainKey (c.val 0) p = gapChainKey (c.val 0) c + 4 * layerGridV c p := by
  rw [← layerGridPoint_coordinates c p hx]
  simp only [layerGridPoint_right_key c _ _ heven, layerGridV_point]

theorem occupied_grid_product (S : Finset Site) (c : Site)
    (heven : c.val 0 % 2 = 0)
    (htight : (finiteLayer S (c.val 0)).card =
      gapRunCount S (c.val 0 - 1) * gapRunCount S (c.val 0))
    (u v : ℤ) (hu : u ∈ occupiedGridU S c) (hv : v ∈ occupiedGridV S c) :
    layerGridPoint c u v ∈ finiteLayer S (c.val 0) := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
  have hpx := (Finset.mem_filter.mp hp).2
  have hqx := (Finset.mem_filter.mp hq).2
  have hpkey : gapChainKey (c.val 0 - 1) p ∈ occupiedGapKeys S (c.val 0 - 1) :=
    Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp).1, Or.inr (by omega)⟩, rfl⟩
  have hqkey : gapChainKey (c.val 0) q ∈ occupiedGapKeys S (c.val 0) :=
    Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hq).1, Or.inl hqx⟩, rfl⟩
  obtain ⟨r, hr, hrleft, hrright⟩ := tight_layer_key_pair_occupied S (c.val 0)
    htight _ _ hpkey hqkey
  have hrx := (Finset.mem_filter.mp hr).2
  have hpu := layer_left_key_grid c p hpx heven
  have hru := layer_left_key_grid c r hrx heven
  have hqv := layer_right_key_grid c q hqx heven
  have hrv := layer_right_key_grid c r hrx heven
  have hu : layerGridU c r = layerGridU c p := by omega
  have hv : layerGridV c r = layerGridV c q := by omega
  have heq := layerGridPoint_coordinates c r hrx
  rw [hu, hv] at heq
  rwa [heq]

theorem occupied_grid_membership (S : Finset Site) (c : Site)
    (heven : c.val 0 % 2 = 0)
    (htight : (finiteLayer S (c.val 0)).card =
      gapRunCount S (c.val 0 - 1) * gapRunCount S (c.val 0)) (u v : ℤ) :
    layerGridPoint c u v ∈ finiteLayer S (c.val 0) ↔
      u ∈ occupiedGridU S c ∧ v ∈ occupiedGridV S c := by
  constructor
  · intro hp
    constructor
    · exact Finset.mem_image.mpr ⟨layerGridPoint c u v, hp, layerGridU_point c u v⟩
    · exact Finset.mem_image.mpr ⟨layerGridPoint c u v, hp, layerGridV_point c u v⟩
  · rintro ⟨hu, hv⟩
    exact occupied_grid_product S c heven htight u v hu hv

theorem occupied_grid_nonempty (S : Finset Site) (c : Site) (hc : c ∈ S) :
    (occupiedGridU S c).Nonempty ∧ (occupiedGridV S c).Nonempty := by
  have hcL : c ∈ finiteLayer S (c.val 0) := Finset.mem_filter.mpr ⟨hc, rfl⟩
  exact ⟨⟨_, Finset.mem_image.mpr ⟨c, hcL, rfl⟩⟩,
    ⟨_, Finset.mem_image.mpr ⟨c, hcL, rfl⟩⟩⟩

theorem occupied_grid_card (S : Finset Site) (c : Site) (hc : c ∈ S)
    (heven : c.val 0 % 2 = 0)
    (htight : (finiteLayer S (c.val 0)).card =
      gapRunCount S (c.val 0 - 1) * gapRunCount S (c.val 0)) :
    (occupiedGridU S c).card = gapRunCount S (c.val 0 - 1) ∧
      (occupiedGridV S c).card = gapRunCount S (c.val 0) := by
  have hcL : c ∈ finiteLayer S (c.val 0) := Finset.mem_filter.mpr ⟨hc, rfl⟩
  have hne : 0 < (finiteLayer S (c.val 0)).card := Finset.card_pos.mpr ⟨c, hcL⟩
  have hcounts := tight_layer_key_counts S (c.val 0) hne htight
  have hleft : (occupiedGridU S c).image
      (fun u => gapChainKey (c.val 0 - 1) c + 4 * u) = occupiedGapKeys S (c.val 0 - 1) := by
    apply Finset.Subset.antisymm
    · intro a ha
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
      have hx := (Finset.mem_filter.mp hp).2
      rw [← layer_left_key_grid c p hx heven]
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hp).1, Or.inr (by omega)⟩, rfl⟩
    · intro a ha
      have hckey : gapChainKey (c.val 0) c ∈ occupiedGapKeys S (c.val 0) :=
        Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, Or.inl rfl⟩, rfl⟩
      obtain ⟨p, hp, hpkey, _⟩ := tight_layer_key_pair_occupied S (c.val 0) htight _ _ ha hckey
      apply Finset.mem_image.mpr
      refine ⟨layerGridU c p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
      rw [← layer_left_key_grid c p (Finset.mem_filter.mp hp).2 heven, hpkey]
  have hright : (occupiedGridV S c).image
      (fun v => gapChainKey (c.val 0) c + 4 * v) = occupiedGapKeys S (c.val 0) := by
    apply Finset.Subset.antisymm
    · intro b hb
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
      have hx := (Finset.mem_filter.mp hp).2
      rw [← layer_right_key_grid c p hx heven]
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hp).1, Or.inl hx⟩, rfl⟩
    · intro b hb
      have hckey : gapChainKey (c.val 0 - 1) c ∈ occupiedGapKeys S (c.val 0 - 1) :=
        Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, Or.inr (by omega)⟩, rfl⟩
      obtain ⟨p, hp, _, hpkey⟩ := tight_layer_key_pair_occupied S (c.val 0) htight _ _ hckey hb
      apply Finset.mem_image.mpr
      refine ⟨layerGridV c p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
      rw [← layer_right_key_grid c p (Finset.mem_filter.mp hp).2 heven, hpkey]
  have hlcard : (occupiedGridU S c).card = (occupiedGapKeys S (c.val 0 - 1)).card := by
    rw [← hleft]
    symm
    have hi : Function.Injective (fun u : ℤ => gapChainKey (c.val 0 - 1) c + 4 * u) := by
      intro u v h
      change gapChainKey (c.val 0 - 1) c + 4 * u = gapChainKey (c.val 0 - 1) c + 4 * v at h
      omega
    exact Finset.card_image_of_injective _ hi
  have hrcard : (occupiedGridV S c).card = (occupiedGapKeys S (c.val 0)).card := by
    rw [← hright]
    symm
    have hi : Function.Injective (fun v : ℤ => gapChainKey (c.val 0) c + 4 * v) := by
      intro u v h
      change gapChainKey (c.val 0) c + 4 * u = gapChainKey (c.val 0) c + 4 * v at h
      omega
    exact Finset.card_image_of_injective _ hi
  exact ⟨hlcard.trans hcounts.1, hrcard.trans hcounts.2⟩

theorem occupied_grid_order_convex (S : Finset Site) (c : Site) (hc : c ∈ S)
    (heven : c.val 0 % 2 = 0)
    (htight : (finiteLayer S (c.val 0)).card =
      gapRunCount S (c.val 0 - 1) * gapRunCount S (c.val 0)) :
    (∀ a ∈ occupiedGridU S c, ∀ b ∈ occupiedGridU S c, ∀ u : ℤ,
      a ≤ u → u ≤ b → u ∈ occupiedGridU S c) ∧
    (∀ a ∈ occupiedGridV S c, ∀ b ∈ occupiedGridV S c, ∀ v : ℤ,
      a ≤ v → v ≤ b → v ∈ occupiedGridV S c) := by
  have hcL : c ∈ finiteLayer S (c.val 0) := Finset.mem_filter.mpr ⟨hc, rfl⟩
  have hne : 0 < (finiteLayer S (c.val 0)).card := Finset.card_pos.mpr ⟨c, hcL⟩
  have hinj := tight_layer_one_start_per_chain S (c.val 0) hne htight
  have hU0 : 0 ∈ occupiedGridU S c := by
    have h : layerGridPoint c 0 0 ∈ finiteLayer S (c.val 0) := by simpa using hcL
    exact ((occupied_grid_membership S c heven htight 0 0).mp h).1
  have hV0 : 0 ∈ occupiedGridV S c := by
    have h : layerGridPoint c 0 0 ∈ finiteLayer S (c.val 0) := by simpa using hcL
    exact ((occupied_grid_membership S c heven htight 0 0).mp h).2
  constructor
  · intro a ha b hb u hau hub
    have hlo := occupied_grid_product S c heven htight a 0 ha hV0
    have hhi := occupied_grid_product S c heven htight b 0 hb hV0
    have hocc : layerGridPoint c u 0 ∈ S := by
      apply one_start_per_chain_order_convex S (c.val 0) hinj.2
        (layerGridPoint c a 0) (layerGridPoint c u 0) (layerGridPoint c b 0)
        (Finset.mem_filter.mp hlo).1 (Finset.mem_filter.mp hhi).1
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · rw [layerGridPoint_right_key c _ _ heven, layerGridPoint_right_key c _ _ heven]
      · rw [layerGridPoint_right_key c _ _ heven, layerGridPoint_right_key c _ _ heven]
      · simp only [layerGridPoint_y]
        omega
      · simp only [layerGridPoint_y]
        omega
    exact ((occupied_grid_membership S c heven htight u 0).mp
      (Finset.mem_filter.mpr ⟨hocc, rfl⟩)).1
  · intro a ha b hb v hav hvb
    have hlo := occupied_grid_product S c heven htight 0 a hU0 ha
    have hhi := occupied_grid_product S c heven htight 0 b hU0 hb
    have hocc : layerGridPoint c 0 v ∈ S := by
      apply one_start_per_chain_order_convex S (c.val 0 - 1) hinj.1
        (layerGridPoint c 0 a) (layerGridPoint c 0 v) (layerGridPoint c 0 b)
        (Finset.mem_filter.mp hlo).1 (Finset.mem_filter.mp hhi).1
      · exact Or.inr (by simp)
      · exact Or.inr (by simp)
      · exact Or.inr (by simp)
      · rw [layerGridPoint_left_key c _ _ heven, layerGridPoint_left_key c _ _ heven]
      · rw [layerGridPoint_left_key c _ _ heven, layerGridPoint_left_key c _ _ heven]
      · simp only [layerGridPoint_y]
        omega
      · simp only [layerGridPoint_y]
        omega
    exact ((occupied_grid_membership S c heven htight 0 v).mp
      (Finset.mem_filter.mpr ⟨hocc, rfl⟩)).2

end ProteinFolding.Tetrahedral
