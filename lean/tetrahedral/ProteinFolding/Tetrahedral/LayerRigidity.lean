import ProteinFolding.Tetrahedral.GapRuns

/-! Equality consequences of the intersecting-chain product bound, Section 5.5. -/

namespace ProteinFolding.Tetrahedral

def occupiedGapKeys (S : Finset Site) (k : ℤ) : Finset ℤ :=
  (gapSupport S k).image (gapChainKey k)

def occupiedLayerKeyPairs (S : Finset Site) (k : ℤ) : Finset (ℤ × ℤ) :=
  (finiteLayer S k).image (fun p => (gapChainKey (k - 1) p, gapChainKey k p))

theorem occupiedLayerKeyPairs_card (S : Finset Site) (k : ℤ) :
    (occupiedLayerKeyPairs S k).card = (finiteLayer S k).card := by
  apply Finset.card_image_of_injOn
  intro p hp q hq heq
  exact layer_pair_keys_injective k (Finset.mem_filter.mp hp).2
    (Finset.mem_filter.mp hq).2 heq

theorem occupiedLayerKeyPairs_subset (S : Finset Site) (k : ℤ) :
    occupiedLayerKeyPairs S k ⊆ occupiedGapKeys S (k - 1) ×ˢ occupiedGapKeys S k := by
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  have h := Finset.mem_filter.mp hp
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨h.1, Or.inr (by omega)⟩, rfl⟩
  · exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨h.1, Or.inl h.2⟩, rfl⟩

theorem layer_card_le_occupied_key_product (S : Finset Site) (k : ℤ) :
    (finiteLayer S k).card ≤ (occupiedGapKeys S (k - 1)).card * (occupiedGapKeys S k).card := by
  have h := Finset.card_le_card (occupiedLayerKeyPairs_subset S k)
  rwa [occupiedLayerKeyPairs_card, Finset.card_product] at h

/-- Tightness forces the entire product of occupied row and column keys. -/
theorem tight_layer_key_product (S : Finset Site) (k : ℤ)
    (htight : (finiteLayer S k).card = gapRunCount S (k - 1) * gapRunCount S k) :
    occupiedLayerKeyPairs S k = occupiedGapKeys S (k - 1) ×ˢ occupiedGapKeys S k := by
  apply Finset.eq_of_subset_of_card_le (occupiedLayerKeyPairs_subset S k)
  rw [Finset.card_product, occupiedLayerKeyPairs_card, htight]
  exact Nat.mul_le_mul (gapChainKeys_card_le_runs S (k - 1)) (gapChainKeys_card_le_runs S k)

/-- Every pair of occupied adjacent-gap keys is realised by an occupied site
in the layer, not merely bounded in number. -/
theorem tight_layer_key_pair_occupied (S : Finset Site) (k : ℤ)
    (htight : (finiteLayer S k).card = gapRunCount S (k - 1) * gapRunCount S k)
    (a b : ℤ) (ha : a ∈ occupiedGapKeys S (k - 1)) (hb : b ∈ occupiedGapKeys S k) :
    ∃ p ∈ finiteLayer S k, gapChainKey (k - 1) p = a ∧ gapChainKey k p = b := by
  have hz : (a, b) ∈ occupiedLayerKeyPairs S k := by
    rw [tight_layer_key_product S k htight]
    exact Finset.mem_product.mpr ⟨ha, hb⟩
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hz
  exact ⟨p, hp, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

/-- For a nonempty tight layer, each occupied chain contains exactly one run.
The nonempty hypothesis is necessary to cancel the product bound. -/
theorem tight_layer_key_counts (S : Finset Site) (k : ℤ)
    (hne : 0 < (finiteLayer S k).card)
    (htight : (finiteLayer S k).card = gapRunCount S (k - 1) * gapRunCount S k) :
    (occupiedGapKeys S (k - 1)).card = gapRunCount S (k - 1) ∧
      (occupiedGapKeys S k).card = gapRunCount S k := by
  have hA := gapChainKeys_card_le_runs S (k - 1)
  have hB := gapChainKeys_card_le_runs S k
  change (occupiedGapKeys S (k - 1)).card ≤ gapRunCount S (k - 1) at hA
  change (occupiedGapKeys S k).card ≤ gapRunCount S k at hB
  have hprod := layer_card_le_occupied_key_product S k
  have hApos : 0 < (occupiedGapKeys S (k - 1)).card := by
    by_contra hnot
    have heq : (occupiedGapKeys S (k - 1)).card = 0 := by omega
    rw [heq, Nat.zero_mul] at hprod
    omega
  have hBpos : 0 < (occupiedGapKeys S k).card := by
    by_contra hnot
    have heq : (occupiedGapKeys S k).card = 0 := by omega
    rw [heq, Nat.mul_zero] at hprod
    omega
  constructor
  · by_contra hnot
    have hlt : (occupiedGapKeys S (k - 1)).card < gapRunCount S (k - 1) := by
      change (occupiedGapKeys S (k - 1)).card ≤ gapRunCount S (k - 1) at hA
      omega
    have hp₁ := Nat.mul_lt_mul_of_pos_right hlt hBpos
    have hp₂ := Nat.mul_le_mul_left (gapRunCount S (k - 1)) hB
    omega
  · by_contra hnot
    have hlt : (occupiedGapKeys S k).card < gapRunCount S k := by
      change (occupiedGapKeys S k).card ≤ gapRunCount S k at hB
      omega
    have hp₁ := Nat.mul_lt_mul_of_pos_left hlt hApos
    have hp₂ := Nat.mul_le_mul_right (gapRunCount S k) hA
    omega

theorem one_start_per_chain_of_key_count (S : Finset Site) (k : ℤ)
    (hcount : (occupiedGapKeys S k).card = gapRunCount S k) :
    Set.InjOn (gapChainKey k) (gapRunStarts S k) := by
  apply Finset.card_image_iff.mp
  rw [← gapChainKeys_eq_startKeys]
  exact hcount

theorem tight_layer_one_start_per_chain (S : Finset Site) (k : ℤ)
    (hne : 0 < (finiteLayer S k).card)
    (htight : (finiteLayer S k).card = gapRunCount S (k - 1) * gapRunCount S k) :
    Set.InjOn (gapChainKey (k - 1)) (gapRunStarts S (k - 1)) ∧
      Set.InjOn (gapChainKey k) (gapRunStarts S k) := by
  have hcounts := tight_layer_key_counts S k hne htight
  exact ⟨one_start_per_chain_of_key_count S (k - 1) hcounts.1,
    one_start_per_chain_of_key_count S k hcounts.2⟩

end ProteinFolding.Tetrahedral
