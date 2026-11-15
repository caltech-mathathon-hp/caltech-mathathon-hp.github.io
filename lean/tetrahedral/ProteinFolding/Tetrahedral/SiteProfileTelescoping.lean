import ProteinFolding.Tetrahedral.SiteProfileCentral

/-! Tightness of the prefix and suffix bounds propagates from the central layer. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

theorem runsBefore_succ (S : Finset Site) (k : ℤ) :
    runsBefore S (k + 1) = runsBefore S k + gapRunCount S k := by
  have hsum : runsBefore S (k + 1) = runsBefore S k +
      ∑ j ∈ activeGaps S, if j = k then gapRunCount S j else 0 := by
    unfold runsBefore
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjk : j < k
    · have hnext : j < k + 1 := by omega
      have hne : j ≠ k := by omega
      simp [hjk, hnext, hne]
    · by_cases heq : j = k
      · subst j
        simp
      · have hnext : ¬ j < k + 1 := by omega
        simp [hjk, heq, hnext]
  rw [hsum]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [hjk]
  · intro hk
    simp [gapRunCount_zero_of_not_active hk]

theorem runsFrom_succ (S : Finset Site) (k : ℤ) :
    runsFrom S k = runsFrom S (k + 1) + gapRunCount S k := by
  have h₁ := runsBefore_add_runsFrom S k
  have h₂ := runsBefore_add_runsFrom S (k + 1)
  have h₃ := runsBefore_succ S k
  omega

theorem layer_prefix_tight_propagates_left (S : Finset Site) (k : ℤ)
    (htight : (finiteLayer S (k + 1)).card = runsBefore S (k + 1)) :
    (finiteLayer S k).card = runsBefore S k := by
  have hle := layer_card_le_runsBefore S k
  have hstep := (layer_imbalance_bound S k).2
  have hsum := runsBefore_succ S k
  omega

theorem layer_suffix_tight_propagates_right (S : Finset Site) (k : ℤ)
    (htight : (finiteLayer S k).card = runsFrom S k) :
    (finiteLayer S (k + 1)).card = runsFrom S (k + 1) := by
  have hle := layer_card_le_runsFrom S (k + 1)
  have hstep := (layer_imbalance_bound S k).1
  have hsum := runsFrom_succ S k
  omega

theorem layer_prefix_tight_left (S : Finset Site) (center : ℤ)
    (htight : (finiteLayer S center).card = runsBefore S center) :
    ∀ k ≤ center, (finiteLayer S k).card = runsBefore S k := by
  have hdown : ∀ n : ℕ, (finiteLayer S (center - n)).card = runsBefore S (center - n) := by
    intro n
    induction n with
    | zero => simpa using htight
    | succ n ih =>
      have heq : center - ((n + 1 : ℕ) : ℤ) + 1 = center - n := by omega
      apply layer_prefix_tight_propagates_left
      simpa only [heq] using ih
  intro k hk
  have heq : center - ((center - k).toNat : ℤ) = k := by omega
  simpa only [heq] using hdown (center - k).toNat

theorem layer_suffix_tight_right (S : Finset Site) (center : ℤ)
    (htight : (finiteLayer S center).card = runsFrom S center) :
    ∀ k, center ≤ k → (finiteLayer S k).card = runsFrom S k := by
  have hup : ∀ n : ℕ, (finiteLayer S (center + n)).card = runsFrom S (center + n) := by
    intro n
    induction n with
    | zero => simpa using htight
    | succ n ih =>
      have heq : center + ((n + 1 : ℕ) : ℤ) = center + n + 1 := by omega
      rw [heq]
      exact layer_suffix_tight_propagates_right S _ ih
  intro k hk
  have heq : center + ((k - center).toNat : ℤ) = k := by omega
  simpa only [heq] using hup (k - center).toNat

/-- Every gap below the central layer has its upper layer larger by its run count;
above the central layer the lower layer is larger by its run count. -/
theorem site_extremal_signed_imbalances (S : Finset Site) (hne : S.Nonempty) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m)
    (hRuns : totalRuns S = 2 * m ^ 2) :
    ∃ center : ℤ, center ∈ activeLayers S ∧ gapRunCount S (center - 1) = m ∧
      gapRunCount S center = m ∧ (finiteLayer S center).card = m ^ 2 ∧
      (∀ k < center, (finiteLayer S (k + 1)).card =
        (finiteLayer S k).card + gapRunCount S k) ∧
      (∀ k, center ≤ k → (finiteLayer S k).card =
        (finiteLayer S (k + 1)).card + gapRunCount S k) := by
  obtain ⟨center, hactive, hβprev, hβ, hprefix, hlayer⟩ :=
    site_extremal_central_layer S hne m hm hcard hRuns
  have hpref : (finiteLayer S center).card = runsBefore S center := by omega
  have hsum := runsBefore_add_runsFrom S center
  have hsuf : (finiteLayer S center).card = runsFrom S center := by omega
  refine ⟨center, hactive, hβprev, hβ, hlayer, ?_, ?_⟩
  · intro k hk
    rw [layer_prefix_tight_left S center hpref k (by omega),
      layer_prefix_tight_left S center hpref (k + 1) (by omega)]
    exact runsBefore_succ S k
  · intro k hk
    rw [layer_suffix_tight_right S center hsuf k hk,
      layer_suffix_tight_right S center hsuf (k + 1) (by omega)]
    exact runsFrom_succ S k

end ProteinFolding.Tetrahedral
