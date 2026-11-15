import ProteinFolding.Tetrahedral.LayerRigidityRectangleHelpers

/-! Reflection carries finite gap runs to reversed gap runs. -/

namespace ProteinFolding.Tetrahedral

@[simp] theorem mem_reflected_finset (S : Finset Site) (a : Site)
    (ha : InBSublattice a.val) (p : Site) :
    reflectSite a ha p ∈ S.image (reflectSite a ha) ↔ p ∈ S := by
  constructor
  · intro hp
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hp
    have hqp := reflectSite_injective a ha heq
    rwa [← hqp]
  · intro hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem reflected_in_gap (a : Site) (ha : InBSublattice a.val) (k : ℤ) (p : Site) :
    InGap (a.val 0 - k - 1) (reflectSite a ha p) ↔ InGap k p := by
  change (a.val 0 - p.val 0 = a.val 0 - k - 1 ∨
      a.val 0 - p.val 0 = a.val 0 - k - 1 + 1) ↔
    (p.val 0 = k ∨ p.val 0 = k + 1)
  omega

theorem reflected_gap_key (a : Site) (ha : InBSublattice a.val) (k : ℤ) (p : Site) :
    gapChainKey (a.val 0 - k - 1) (reflectSite a ha p) =
      gapChainKey k a - gapChainKey k p := by
  have hax := ha.1 0
  have hpar : (a.val 0 - k - 1) % 2 = k % 2 := by omega
  by_cases hk : k % 2 = 0
  · simp only [gapChainKey, hpar, hk, if_true]
    change (a.val 1 - p.val 1) - (a.val 2 - p.val 2) =
      (a.val 1 - a.val 2) - (p.val 1 - p.val 2)
    omega
  · simp only [gapChainKey, hpar, hk, if_false]
    change (a.val 1 - p.val 1) + (a.val 2 - p.val 2) =
      (a.val 1 + a.val 2) - (p.val 1 + p.val 2)
    omega

theorem reflected_gapNext (a : Site) (ha : InBSublattice a.val) (k : ℤ) (p : Site)
    (hp : InGap k p) :
    reflectSite a ha (gapNext k p) = gapPrev (a.val 0 - k - 1) (reflectSite a ha p) := by
  apply gap_key_y_ext
    ((reflected_in_gap a ha k (gapNext k p)).mpr (gapNext_in_gap hp))
    (gapPrev_in_gap ((reflected_in_gap a ha k p).mpr hp))
  · rw [reflected_gap_key, gapNext_key, gapPrev_key, reflected_gap_key]
  · rw [gapPrev_y]
    change a.val 1 - (gapNext k p).val 1 = a.val 1 - p.val 1 - 1
    rw [gapNext_y]
    omega

theorem reflected_run_starts (S : Finset Site) (a : Site)
    (ha : InBSublattice a.val) (k : ℤ) :
    gapRunStarts (S.image (reflectSite a ha)) (a.val 0 - k - 1) =
      (gapRunEnds S k).image (reflectSite a ha) := by
  apply Finset.Subset.antisymm
  · intro q hq
    have hqf := Finset.mem_filter.mp hq
    have hqs := Finset.mem_filter.mp hqf.1
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hqs.1
    have hpgap := (reflected_in_gap a ha k p).mp hqs.2
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp, hpgap⟩, ?_⟩, rfl⟩
    intro hnext
    apply hqf.2
    rw [← reflected_gapNext a ha k p hpgap]
    exact (mem_reflected_finset S a ha (gapNext k p)).mpr hnext
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hpf := Finset.mem_filter.mp hp
    have hps := Finset.mem_filter.mp hpf.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨(mem_reflected_finset S a ha p).mpr hps.1,
        (reflected_in_gap a ha k p).mpr hps.2⟩, ?_⟩
    rw [← reflected_gapNext a ha k p hps.2, mem_reflected_finset]
    exact hpf.2

theorem gapRunCount_reflected (S : Finset Site) (a : Site)
    (ha : InBSublattice a.val) (k : ℤ) :
    gapRunCount (S.image (reflectSite a ha)) (a.val 0 - k - 1) = gapRunCount S k := by
  unfold gapRunCount
  rw [reflected_run_starts, Finset.card_image_of_injective _ (reflectSite_injective a ha),
    gapRunStarts_card_eq_ends]

theorem finiteLayer_reflected (S : Finset Site) (a : Site)
    (ha : InBSublattice a.val) (k : ℤ) :
    finiteLayer (S.image (reflectSite a ha)) (a.val 0 - k) =
      (finiteLayer S k).image (reflectSite a ha) := by
  apply Finset.Subset.antisymm
  · intro q hq
    have h := Finset.mem_filter.mp hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h.1
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
    have hx := h.2
    change a.val 0 - p.val 0 = a.val 0 - k at hx
    omega
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have h := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨p, h.1, rfl⟩, ?_⟩
    change a.val 0 - p.val 0 = a.val 0 - k
    omega

theorem card_finiteLayer_reflected (S : Finset Site) (a : Site)
    (ha : InBSublattice a.val) (k : ℤ) :
    (finiteLayer (S.image (reflectSite a ha)) (a.val 0 - k)).card =
      (finiteLayer S k).card := by
  rw [finiteLayer_reflected, Finset.card_image_of_injective _ (reflectSite_injective a ha)]

end ProteinFolding.Tetrahedral
