import ProteinFolding.Tetrahedral.SiteProfile
import ProteinFolding.Tetrahedral.RawProfileWitness
import ProteinFolding.Tetrahedral.CompositionBound

/-! Equality information retained by the finite-site composition bridge.
At octahedral equality there are no omitted internal integer gaps, and the
ascending list of their run counts is exactly the canonical composition. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

theorem exists_ordered_site_profile_witness (S : Finset Site) (hne : S.Nonempty) :
    Nonempty (RawProfileWitness (totalRuns S) (gapRunCount S) (activeGaps S)) :=
  rawProfile_witness_exists (totalRuns S) (gapRunCount S) (activeGaps S)
    (activeGaps_nonempty_of_site_nonempty S hne) (gapRunCount_pos_of_mem_active S)

theorem site_profile_equality_data (S : Finset Site) (hne : S.Nonempty) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m) (hRuns : totalRuns S = 2 * m ^ 2) :
    ∃ w : RawProfileWitness (totalRuns S) (gapRunCount S) (activeGaps S),
      w.composition.parts = (canonicalSquare (m - 1)).parts ++
        (canonicalSquare (m - 1)).parts.reverse ∧
      RawKeysConvex (activeGaps S) ∧
      rawProfileValue (totalRuns S) (activeGaps S) (gapRunCount S) = S.card ∧
      profileValue (totalRuns S) 0 w.composition = S.card := by
  obtain ⟨w⟩ := exists_ordered_site_profile_witness S hne
  have hmass : w.composition.mass = 2 * m ^ 2 := by rw [w.mass_eq]; exact hRuns
  have hupper := composition_bound m hm w.composition hmass
  have hlower := site_card_le_rawProfile S
  have hprof : profileValue (totalRuns S) 0 w.composition = twoSidedValue w.composition := by
    unfold twoSidedValue
    rw [w.mass_eq]
    rfl
  have hval := w.value_le
  have hveq : twoSidedValue w.composition = octahedralNumber m := by omega
  have hraw : rawProfileValue (totalRuns S) (activeGaps S) (gapRunCount S) = S.card := by omega
  have hpeq : profileValue (totalRuns S) 0 w.composition = S.card := by omega
  refine ⟨w, composition_bound_equality m hm w.composition hmass hveq, ?_, hraw, hpeq⟩
  exact w.equality_convex (by exact le_rfl) (by omega)

theorem site_profile_canonical_run_list (S : Finset Site) (hne : S.Nonempty) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m) (hRuns : totalRuns S = 2 * m ^ 2) :
    ∃ keys : List ℤ, keys.toFinset = activeGaps S ∧ keys.Pairwise (fun i j => i < j) ∧
      keys.map (gapRunCount S) = (canonicalSquare (m - 1)).parts ++
        (canonicalSquare (m - 1)).parts.reverse ∧ RawKeysConvex (activeGaps S) := by
  obtain ⟨w, hparts, hconv, _, _⟩ := site_profile_equality_data S hne m hm hcard hRuns
  exact ⟨w.keys, w.keys_set, w.keys_sorted, w.parts_eq.symm.trans hparts, hconv⟩

/-- Any integer between two active gaps is active at octahedral equality. -/
theorem site_profile_no_missing_gaps (S : Finset Site) (hne : S.Nonempty) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m) (hRuns : totalRuns S = 2 * m ^ 2) :
    RawKeysConvex (activeGaps S) := by
  obtain ⟨_, _, hconv, _, _⟩ := site_profile_equality_data S hne m hm hcard hRuns
  exact hconv

def siteLayerTerm (S : Finset Site) (k : ℤ) : ℕ :=
  if k - 1 ∈ activeGaps S then
    min (min (rawPrefix (activeGaps S) (gapRunCount S) k)
      (totalRuns S - rawPrefix (activeGaps S) (gapRunCount S) k))
      (gapRunCount S (k - 1) * gapRunCount S k) else 0

theorem layer_card_zero_of_not_active (S : Finset Site) (k : ℤ) (hk : k ∉ activeLayers S) :
    (finiteLayer S k).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := Finset.mem_filter.mp hp
  apply hk
  exact Finset.mem_image.mpr ⟨p, h.1, h.2⟩

theorem site_layer_card_le_term (S : Finset Site) (k : ℤ) :
    (finiteLayer S k).card ≤ siteLayerTerm S k := by
  by_cases hk : k ∈ activeLayers S
  · unfold siteLayerTerm
    rw [if_pos (predecessor_mem_activeGaps_of_layer S k hk)]
    simpa only [rawPrefix, runsBefore, min_assoc] using layer_card_le_relaxation S k
  · rw [layer_card_zero_of_not_active S k hk]
    exact Nat.zero_le _

theorem site_card_eq_sum_activeGap_layers (S : Finset Site) :
    S.card = ∑ k ∈ activeGaps S, (finiteLayer S k).card := by
  rw [card_eq_sum_layer_card]
  exact Finset.sum_subset (activeLayers_subset_activeGaps S)
    (fun k _ hk => layer_card_zero_of_not_active S k hk)

theorem site_layer_tight_of_rawProfile (S : Finset Site)
    (heq : rawProfileValue (totalRuns S) (activeGaps S) (gapRunCount S) = S.card) :
    ∀ k ∈ activeGaps S, (finiteLayer S k).card = siteLayerTerm S k := by
  have hsum : (∑ k ∈ activeGaps S, (finiteLayer S k).card) =
      ∑ k ∈ activeGaps S, siteLayerTerm S k := by
    rw [← site_card_eq_sum_activeGap_layers S, ← heq]
    rfl
  intro k hk
  have hle := site_layer_card_le_term S k
  by_contra hnot
  have hlt : (finiteLayer S k).card < siteLayerTerm S k := by omega
  have hs := Finset.sum_lt_sum (fun j _ => site_layer_card_le_term S j) ⟨k, hk, hlt⟩
  omega

/-- Every occupied layer attains its capped relaxation at global equality. -/
theorem site_layer_relaxation_tight (S : Finset Site) (hne : S.Nonempty) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m) (hRuns : totalRuns S = 2 * m ^ 2)
    (k : ℤ) (hk : k ∈ activeLayers S) :
    (finiteLayer S k).card = min (runsBefore S k)
      (min (totalRuns S - runsBefore S k) (gapRunCount S (k - 1) * gapRunCount S k)) := by
  obtain ⟨_, _, _, hraw, _⟩ := site_profile_equality_data S hne m hm hcard hRuns
  have h := site_layer_tight_of_rawProfile S hraw k (activeLayers_subset_activeGaps S hk)
  unfold siteLayerTerm at h
  rw [if_pos (predecessor_mem_activeGaps_of_layer S k hk)] at h
  simpa only [rawPrefix, runsBefore, min_assoc] using h

theorem siteLayerTerm_pos_of_adjacent_active (S : Finset Site) (k : ℤ)
    (hk : k ∈ activeGaps S) (hprev : k - 1 ∈ activeGaps S) : 0 < siteLayerTerm S k := by
  have hβk := gapRunCount_pos_of_mem_active S k hk
  have hβprev := gapRunCount_pos_of_mem_active S (k - 1) hprev
  have hbefore : gapRunCount S (k - 1) ≤ runsBefore S k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨hprev, by omega⟩)
  have hfrom : gapRunCount S k ≤ runsFrom S k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨hk, le_rfl⟩)
  have hsum := runsBefore_add_runsFrom S k
  have hprefix : 0 < rawPrefix (activeGaps S) (gapRunCount S) k := by
    change 0 < runsBefore S k
    omega
  have hroom : 0 < totalRuns S - rawPrefix (activeGaps S) (gapRunCount S) k := by
    change 0 < totalRuns S - runsBefore S k
    omega
  unfold siteLayerTerm
  rw [if_pos hprev]
  exact lt_min (lt_min hprefix hroom) (Nat.mul_pos hβprev hβk)

theorem site_internal_layer_nonempty (S : Finset Site) (hne : S.Nonempty) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m) (hRuns : totalRuns S = 2 * m ^ 2)
    (k : ℤ) (hk : k ∈ activeGaps S) (hprev : k - 1 ∈ activeGaps S) :
    (finiteLayer S k).Nonempty := by
  obtain ⟨_, _, _, hraw, _⟩ := site_profile_equality_data S hne m hm hcard hRuns
  have htight := site_layer_tight_of_rawProfile S hraw k hk
  have hpos := siteLayerTerm_pos_of_adjacent_active S k hk hprev
  apply Finset.card_pos.mp
  omega

/-- At equality the occupied layers are exactly the intervals between active gaps. -/
theorem site_activeLayers_eq_adjacent_gaps (S : Finset Site) (hne : S.Nonempty) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m) (hRuns : totalRuns S = 2 * m ^ 2) :
    activeLayers S = (activeGaps S).filter (fun k => k - 1 ∈ activeGaps S) := by
  ext k
  simp only [Finset.mem_filter]
  constructor
  · intro hk
    exact ⟨activeLayers_subset_activeGaps S hk, predecessor_mem_activeGaps_of_layer S k hk⟩
  · rintro ⟨hk, hprev⟩
    obtain ⟨p, hp⟩ := site_internal_layer_nonempty S hne m hm hcard hRuns k hk hprev
    have h := Finset.mem_filter.mp hp
    exact Finset.mem_image.mpr ⟨p, h.1, h.2⟩

theorem site_occupied_layers_convex (S : Finset Site) (hne : S.Nonempty) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m) (hRuns : totalRuns S = 2 * m ^ 2) :
    RawKeysConvex (activeLayers S) := by
  have hconv := site_profile_no_missing_gaps S hne m hm hcard hRuns
  have hset := site_activeLayers_eq_adjacent_gaps S hne m hm hcard hRuns
  intro i hi j hj k hik hkj
  rw [hset] at hi hj ⊢
  have hi' := Finset.mem_filter.mp hi
  have hj' := Finset.mem_filter.mp hj
  apply Finset.mem_filter.mpr
  exact ⟨hconv i hi'.1 j hj'.1 k hik hkj,
    hconv (i - 1) hi'.2 (j - 1) hj'.2 (k - 1) (by omega) (by omega)⟩

end ProteinFolding.Tetrahedral
