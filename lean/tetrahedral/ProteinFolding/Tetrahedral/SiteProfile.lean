import ProteinFolding.Tetrahedral.RawProfile
import ProteinFolding.Tetrahedral.LayerBounds

/-! From a nonempty finite occupied site set to a positive composition.
Every active gap has a positive run count. Compressing the inactive integer
gaps preserves total mass and can only increase the capped profile sum. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

theorem activeGaps_nonempty_of_site_nonempty (S : Finset Site) (hne : S.Nonempty) :
    (activeGaps S).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  refine ⟨p.val 0, Finset.mem_union_left _ ?_⟩
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem gapRunCount_pos_of_mem_active (S : Finset Site) (k : ℤ) (hk : k ∈ activeGaps S) :
    0 < gapRunCount S k := by
  have hgap : (gapSupport S k).Nonempty := by
    rcases Finset.mem_union.mp hk with hleft | hright
    · obtain ⟨p, hp, hx⟩ := Finset.mem_image.mp hleft
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, Or.inl hx⟩⟩
    · obtain ⟨p, hp, hx⟩ := Finset.mem_image.mp hright
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, Or.inr (by change p.val 0 - 1 = k at hx; omega)⟩⟩
  have hpos := Finset.card_pos.mpr (hgap.image (gapChainKey k))
  have hle := gapChainKeys_card_le_runs S k
  omega

theorem activeLayers_subset_activeGaps (S : Finset Site) : activeLayers S ⊆ activeGaps S := by
  intro k hk
  exact Finset.mem_union_left _ hk

theorem predecessor_mem_activeGaps_of_layer (S : Finset Site) (k : ℤ)
    (hk : k ∈ activeLayers S) : k - 1 ∈ activeGaps S := by
  obtain ⟨p, hp, hx⟩ := Finset.mem_image.mp hk
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨p, hp, ?_⟩
  change p.val 0 - 1 = k - 1
  change p.val 0 = k at hx
  omega

/-- The finite-site layer relaxation is bounded by the raw active-gap profile. -/
theorem site_card_le_rawProfile (S : Finset Site) :
    S.card ≤ rawProfileValue (totalRuns S) (activeGaps S) (gapRunCount S) := by
  let f : ℤ → ℕ := fun k => if k - 1 ∈ activeGaps S then
    min (min (rawPrefix (activeGaps S) (gapRunCount S) k)
      (totalRuns S - rawPrefix (activeGaps S) (gapRunCount S) k))
        (gapRunCount S (k - 1) * gapRunCount S k) else 0
  have heq : (∑ k ∈ activeLayers S, min (runsBefore S k)
      (min (totalRuns S - runsBefore S k) (gapRunCount S (k - 1) * gapRunCount S k))) =
      ∑ k ∈ activeLayers S, f k := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f]
    rw [if_pos (predecessor_mem_activeGaps_of_layer S k hk)]
    exact (min_assoc _ _ _).symm
  calc
    S.card ≤ ∑ k ∈ activeLayers S, min (runsBefore S k)
        (min (totalRuns S - runsBefore S k) (gapRunCount S (k - 1) * gapRunCount S k)) :=
      card_le_sum_layer_relaxation S
    _ = ∑ k ∈ activeLayers S, f k := heq
    _ ≤ ∑ k ∈ activeGaps S, f k :=
      Finset.sum_le_sum_of_subset (activeLayers_subset_activeGaps S)
    _ = rawProfileValue (totalRuns S) (activeGaps S) (gapRunCount S) := rfl

/-- Section 5.2's composition relaxation for an arbitrary nonempty finite set
of diamond-lattice sites. The composition mass is exactly half the boundary. -/
theorem exists_composition_of_site_profile (S : Finset Site) (hne : S.Nonempty) :
    ∃ c : PositiveComposition, c.mass = totalRuns S ∧ S.card ≤ twoSidedValue c := by
  obtain ⟨c, k, hk, hmax, hmass, hlast, hvalue⟩ :=
    rawProfile_composition_exists (totalRuns S) (gapRunCount S) (activeGaps S)
      (activeGaps_nonempty_of_site_nonempty S hne) (gapRunCount_pos_of_mem_active S)
  refine ⟨c, hmass, ?_⟩
  unfold twoSidedValue
  rw [hmass]
  exact (site_card_le_rawProfile S).trans hvalue

theorem totalRuns_pos_of_site_nonempty (S : Finset Site) (hne : S.Nonempty) : 0 < totalRuns S := by
  obtain ⟨c, hmass, _⟩ := exists_composition_of_site_profile S hne
  have h := c.mass_pos
  omega

end ProteinFolding.Tetrahedral
