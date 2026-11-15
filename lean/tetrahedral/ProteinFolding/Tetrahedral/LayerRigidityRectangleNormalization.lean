import ProteinFolding.Tetrahedral.LayerRigidityRectangle
import ProteinFolding.Tetrahedral.LayerRigidityRectangleTransport

/-! Both sublattices admit the same central-square normalization. -/

namespace ProteinFolding.Tetrahedral

theorem tight_square_B_layer_normalizes (S : Finset Site) (k : ℤ) (m : ℕ)
    (hm : 0 < m) (hodd : k % 2 ≠ 0)
    (hleft : gapRunCount S (k - 1) = m) (hright : gapRunCount S k = m)
    (hcard : (finiteLayer S k).card = m ^ 2) :
    ∃ (c : Site) (hcB : InBSublattice c.val), c ∈ finiteLayer S k ∧
      (finiteLayer S k).image (reflectSite c hcB) = finiteLayer (octahedron m) 0 := by
  have hne : 0 < (finiteLayer S k).card := by rw [hcard]; positivity
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hne
  have hax := (Finset.mem_filter.mp ha).2
  have haB : InBSublattice a.val := by
    rcases a.property with h | h
    · have heven := h.1 0
      exact False.elim (hodd (by omega))
    · exact h
  let T := S.image (reflectSite a haB)
  have hTleft : gapRunCount T (-1) = m := by
    have h := gapRunCount_reflected S a haB k
    simpa [T, hax, hright] using h
  have hTright : gapRunCount T 0 = m := by
    have h := gapRunCount_reflected S a haB (k - 1)
    simpa [T, hax, hleft] using h
  have hTlayer : finiteLayer T 0 = (finiteLayer S k).image (reflectSite a haB) := by
    simpa [T, hax] using finiteLayer_reflected S a haB k
  have hTcard : (finiteLayer T 0).card = m ^ 2 := by
    rw [hTlayer, Finset.card_image_of_injective _ (reflectSite_injective a haB), hcard]
  obtain ⟨q, hqA, hq, heq⟩ := tight_square_layer_normalizes T 0 m hm (by decide)
    (by simpa using hTleft) hTright hTcard
  rw [hTlayer] at hq
  obtain ⟨c, hc, hqc⟩ := Finset.mem_image.mp hq
  have hcB : InBSublattice c.val := by
    have hcx := (Finset.mem_filter.mp hc).2
    rcases c.property with h | h
    · have heven := h.1 0
      exact False.elim (hodd (by omega))
    · exact h
  refine ⟨c, hcB, hc, ?_⟩
  rw [hTlayer, Finset.image_image] at heq
  have hfun : (shiftSite q hqA ∘ reflectSite a haB) = reflectSite c hcB := by
    funext p
    apply Subtype.ext
    funext i
    have hi := congrArg (fun r : Site => r.val i) hqc
    change a.val i - c.val i = q.val i at hi
    change a.val i - p.val i - q.val i = c.val i - p.val i
    omega
  rwa [hfun] at heq

/-- No parity assumption is needed for normalizing a tight square layer. -/
theorem tight_square_layer_normalizes_all (S : Finset Site) (k : ℤ) (m : ℕ)
    (hm : 0 < m) (hleft : gapRunCount S (k - 1) = m) (hright : gapRunCount S k = m)
    (hcard : (finiteLayer S k).card = m ^ 2) :
    ∃ c : Site, c ∈ finiteLayer S k ∧
      (finiteLayer S k).image (normalizeSite c) = finiteLayer (octahedron m) 0 := by
  by_cases heven : k % 2 = 0
  · obtain ⟨c, hcA, hc, heq⟩ := tight_square_layer_normalizes S k m hm heven hleft hright hcard
    refine ⟨c, hc, ?_⟩
    have hfun : normalizeSite c = shiftSite c hcA := by
      funext p
      simp only [normalizeSite, dif_pos hcA]
    rwa [hfun]
  · obtain ⟨c, hcB, hc, heq⟩ := tight_square_B_layer_normalizes S k m hm heven hleft hright hcard
    have hcnotA : ¬ InASublattice c.val := fun hcA => sublattices_disjoint c.val hcA hcB
    refine ⟨c, hc, ?_⟩
    have hfun : normalizeSite c = reflectSite c hcB := by
      funext p
      simp only [normalizeSite, dif_neg hcnotA]
    rwa [hfun]

end ProteinFolding.Tetrahedral
