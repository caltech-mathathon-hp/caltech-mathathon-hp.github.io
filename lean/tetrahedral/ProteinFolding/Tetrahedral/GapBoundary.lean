import ProteinFolding.Tetrahedral.GapRuns
import ProteinFolding.Tetrahedral.FiniteSets

/-! Counting actual boundary bonds in each layer gap by the two ends of runs. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

def gapNeighbours (k : ℤ) (p : Site) : Finset Site :=
  (neighbours p).filter (InGap k)

theorem gapNeighbours_of_lower {k : ℤ} {p : Site} (hp : p.val 0 = k) :
    gapNeighbours k p = neighboursAbove p := by
  ext q
  simp only [gapNeighbours, neighboursAbove, Finset.mem_filter, mem_neighbours]
  constructor
  · rintro ⟨hadj, hgap⟩
    have hx := adj_coordinate hadj 0
    exact ⟨hadj, by unfold InGap at hgap; omega⟩
  · rintro ⟨hadj, hx⟩
    exact ⟨hadj, Or.inr (by omega)⟩

theorem gapNeighbours_of_upper {k : ℤ} {p : Site} (hp : p.val 0 = k + 1) :
    gapNeighbours k p = neighboursBelow p := by
  ext q
  simp only [gapNeighbours, neighboursBelow, Finset.mem_filter, mem_neighbours]
  constructor
  · rintro ⟨hadj, hgap⟩
    have hx := adj_coordinate hadj 0
    exact ⟨hadj, by unfold InGap at hgap; omega⟩
  · rintro ⟨hadj, hx⟩
    exact ⟨hadj, Or.inl (by omega)⟩

theorem card_gapNeighbours {k : ℤ} {p : Site} (hp : InGap k p) :
    (gapNeighbours k p).card = 2 := by
  rcases hp with hp | hp
  · rw [gapNeighbours_of_lower hp, card_neighboursAbove]
  · rw [gapNeighbours_of_upper hp, card_neighboursBelow]

theorem gapPrev_ne_next (k : ℤ) (p : Site) : gapPrev k p ≠ gapNext k p := by
  intro h
  have hy := congrArg (fun q : Site => q.val 1) h
  simp only [gapPrev_y, gapNext_y] at hy
  omega

theorem gapNeighbours_eq_pair {k : ℤ} {p : Site} (hp : InGap k p) :
    gapNeighbours k p = {gapPrev k p, gapNext k p} := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hq :
      q = gapPrev k p ∨ q = gapNext k p) with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨(mem_neighbours _ _).mpr (gapPrev_adj k p),
        gapPrev_in_gap hp⟩
    · exact Finset.mem_filter.mpr ⟨(mem_neighbours _ _).mpr (gapNext_adj k p),
        gapNext_in_gap hp⟩
  · rw [card_gapNeighbours hp, Finset.card_pair (gapPrev_ne_next k p)]

/-- Number of outgoing boundary bonds that cross gap k. -/
def gapBoundaryCount (S : Finset Site) (k : ℤ) : ℕ :=
  ∑ p ∈ gapSupport S k, ((gapNeighbours k p).filter (fun q => q ∉ S)).card

theorem gapBoundaryCount_eq_ends (S : Finset Site) (k : ℤ) :
    gapBoundaryCount S k = (gapRunStarts S k).card + (gapRunEnds S k).card := by
  unfold gapBoundaryCount
  have hcount : ∀ p ∈ gapSupport S k,
      ((gapNeighbours k p).filter (fun q => q ∉ S)).card =
        (if gapPrev k p ∉ S then 1 else 0) + (if gapNext k p ∉ S then 1 else 0) := by
    intro p hp
    rw [gapNeighbours_eq_pair (Finset.mem_filter.mp hp).2]
    by_cases hprev : gapPrev k p ∈ S <;> by_cases hnext : gapNext k p ∈ S <;>
      simp [Finset.filter_insert, Finset.filter_singleton, hprev, hnext, gapPrev_ne_next]
  rw [Finset.sum_congr rfl hcount, Finset.sum_add_distrib]
  simp only [gapRunStarts, gapRunEnds, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Each occupied run has exactly two boundary bonds, at its two ends. -/
theorem gapBoundaryCount_eq_twice_runs (S : Finset Site) (k : ℤ) :
    gapBoundaryCount S k = 2 * gapRunCount S k := by
  rw [gapBoundaryCount_eq_ends, ← gapRunStarts_card_eq_ends]
  unfold gapRunCount
  omega

/-- Only these finitely many gaps can meet an occupied site or boundary bond. -/
def activeGaps (S : Finset Site) : Finset ℤ :=
  S.image (fun p => p.val 0) ∪ S.image (fun p => p.val 0 - 1)

theorem gapSupport_empty_of_not_active {S : Finset Site} {k : ℤ}
    (hk : k ∉ activeGaps S) : gapSupport S k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := Finset.mem_filter.mp hp
  apply hk
  rcases h.2 with hx | hx
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, h.1, hx⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, h.1, by omega⟩)

theorem gapRunCount_zero_of_not_active {S : Finset Site} {k : ℤ}
    (hk : k ∉ activeGaps S) : gapRunCount S k = 0 := by
  simp [gapRunCount, gapRunStarts, gapSupport_empty_of_not_active hk]

theorem externalNeighbours_split (S : Finset Site) (p : Site) :
    (externalNeighbours S p).card =
      ((gapNeighbours (p.val 0) p).filter (fun q => q ∉ S)).card +
      ((gapNeighbours (p.val 0 - 1) p).filter (fun q => q ∉ S)).card := by
  have habove : (externalNeighbours S p).filter (fun q => q.val 0 = p.val 0 + 1) =
      (gapNeighbours (p.val 0) p).filter (fun q => q ∉ S) := by
    rw [gapNeighbours_of_lower rfl]
    ext q
    simp [externalNeighbours, neighboursAbove, and_comm, and_assoc]
  have hbelow : (externalNeighbours S p).filter (fun q => ¬ q.val 0 = p.val 0 + 1) =
      (gapNeighbours (p.val 0 - 1) p).filter (fun q => q ∉ S) := by
    rw [gapNeighbours_of_upper (by omega)]
    ext q
    simp only [externalNeighbours, neighboursBelow, Finset.mem_filter, mem_neighbours]
    constructor
    · rintro ⟨⟨hadj, hout⟩, hx⟩
      have hd := adj_coordinate hadj 0
      exact ⟨⟨hadj, by omega⟩, hout⟩
    · rintro ⟨⟨hadj, hx⟩, hout⟩
      exact ⟨⟨hadj, hout⟩, by omega⟩
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := externalNeighbours S p) (p := fun q => q.val 0 = p.val 0 + 1)
  rw [habove, hbelow] at h
  exact h.symm

/-- Every boundary bond occurs in exactly one layer gap. -/
theorem boundaryCount_eq_sum_gapBoundary (S : Finset Site) :
    boundaryCount S = ∑ k ∈ activeGaps S, gapBoundaryCount S k := by
  unfold gapBoundaryCount gapSupport
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold boundaryCount
  apply Finset.sum_congr rfl
  intro p hp
  have h₁ : p.val 0 ∈ activeGaps S :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have h₂ : p.val 0 - 1 ∈ activeGaps S :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have hs := Finset.sum_eq_add_of_mem (f := fun k => if InGap k p then
      ((gapNeighbours k p).filter (fun q => q ∉ S)).card else 0)
    (p.val 0) (p.val 0 - 1) h₁ h₂ (by omega)
    (by
      intro k _ hne
      have hn : ¬ InGap k p := by unfold InGap; omega
      exact if_neg hn)
  rw [hs]
  have hgap₁ : InGap (p.val 0) p := Or.inl rfl
  have hgap₂ : InGap (p.val 0 - 1) p := Or.inr (by omega)
  simp only [hgap₁, hgap₂, if_true]
  exact externalNeighbours_split S p

/-- Section 4's boundary/run identity: |∂S| = 2 Σ_k β_k. -/
theorem boundaryCount_eq_twice_sum_runs (S : Finset Site) :
    boundaryCount S = 2 * ∑ k ∈ activeGaps S, gapRunCount S k := by
  rw [boundaryCount_eq_sum_gapBoundary]
  simp_rw [gapBoundaryCount_eq_twice_runs, Nat.two_mul]
  rw [Finset.sum_add_distrib]

end ProteinFolding.Tetrahedral
