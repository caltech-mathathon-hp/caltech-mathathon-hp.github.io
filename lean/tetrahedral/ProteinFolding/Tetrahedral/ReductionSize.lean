import ProteinFolding.Tetrahedral.ReductionWordLinkers
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Output-size bounds for the actual literal reduction word. These are
separate from the still-required machine computation of its canonical data. -/

namespace ProteinFolding.Tetrahedral

theorem dimerChain_length_le (q : ℕ) : (dimerChain q).length ≤ 5 * q := by
  cases q with
  | zero => simp [dimerChain]
  | succ q => have h := dimerChain_length (q + 1) (by omega); omega

theorem list_length_le_sum_of_pos (xs : List ℕ) (h : ∀ x ∈ xs, 0 < x) : xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons, List.sum_cons]
    omega

theorem sum_word_lengths_le (us : List Sequence) (Q : ℕ)
    (h : ∀ u ∈ us, u.length ≤ Q) : (us.map List.length).sum ≤ us.length * Q := by
  induction us with
  | nil => simp
  | cons u us ih =>
    have hu := h u (by simp)
    have ht := ih (fun v hv => h v (by simp [hv]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem assembleCappedBodies_length_bound (gaps : ℕ → ℕ) (L : ℕ)
    (hgap : ∀ i, gaps i + 2 ≤ L) (us : List Sequence) (i : ℕ) :
    (assembleCappedBodies gaps i us).length ≤ (us.map List.length).sum + us.length * L := by
  induction us generalizing i with
  | nil => simp [assembleCappedBodies]
  | cons u us ih =>
    have ht := ih (i + 1)
    have hg := hgap i
    simp only [assembleCappedBodies, capWord, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil, List.map_cons, List.sum_cons,
      Nat.add_mul, Nat.one_mul] at ⊢
    omega

theorem assembleReductionWord_length_bound (gaps : ℕ → ℕ) (L : ℕ)
    (hgap : ∀ i, gaps i + 2 ≤ L) (us : List Sequence) :
    (assembleReductionWord gaps us).length ≤ 2 + (us.map List.length).sum + us.length * L := by
  have h := assembleCappedBodies_length_bound gaps L hgap us 0
  simp only [assembleReductionWord, List.length_append, List.length_cons, List.length_nil]
  omega

namespace ConstructionParameters

theorem total_capacity_le_side (p : ConstructionParameters) : p.bins * p.capacity ≤ p.side := by
  have hs := p.scale_ge
  have hc : p.capacity ≤ p.binDimers := by
    have h := Nat.mul_le_mul_right p.capacity (show 1 ≤ p.scale by omega)
    simpa only [Nat.one_mul, binDimers] using h
  have hmul := Nat.mul_le_mul_left p.bins hc
  have ht := p.track_total_dimer_count
  omega

theorem unit_dimer_lengths_bound (p : ConstructionParameters) (items : List ℕ)
    (htotal : items.sum = p.bins * p.capacity) :
    (dimerChain p.leftFiller).length ≤ 15 * p.side ∧
      (dimerChain p.rightFiller).length ≤ 15 * p.side ∧
      (∀ s ∈ items, (dimerChain (p.itemDimers s)).length ≤ 15 * p.side) ∧
      (dimerChain (3 * (p.side - 2))).length ≤ 15 * p.side := by
  have ht := p.track_total_dimer_count
  have hleft := dimerChain_length_le p.leftFiller
  have hright := dimerChain_length_le p.rightFiller
  have hring := dimerChain_length_le (3 * (p.side - 2))
  refine ⟨by omega, by omega, ?_, by omega⟩
  intro s hs
  have hmem := List.le_sum_of_mem hs
  have hmul := Nat.mul_le_mul_left p.scale hmem
  have heq : p.scale * items.sum = p.bins * p.binDimers := by
    rw [htotal]
    unfold binDimers
    ring
  rw [heq] at hmul
  have hd := dimerChain_length_le (p.itemDimers s)
  unfold itemDimers at hd ⊢
  omega

theorem reductionUnitBodies_length_bound (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (htotal : items.sum = p.bins * p.capacity) :
    ∀ u ∈ p.reductionUnitBodies items bulkLengths,
      u.length ≤ bulkLengths.sum + 200 * (p.side + 1) := by
  have hK : p.bins ≤ p.side := by have h := p.family_side_bound; omega
  have hd := p.unit_dimer_lengths_bound items htotal
  have hframe : (p.framePart1 ++ p.framePart2).length ≤ 27 * (p.side + 1) := by
    have h := p.frameWord_length
    simp only [frameWord, List.length_append, List.length_singleton] at h
    rw [List.length_append]
    omega
  have hsep : ∀ u ∈ (List.range (p.bins + 1)).map p.separatorWord,
      u.length ≤ 141 * (p.side + 1) := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu
    have hk' : k ≤ p.bins := by have h := List.mem_range.mp hk; omega
    rw [p.separatorWord_length k hk']
    have hslack := p.tether_slack_bounds k hk'
    unfold sigma at hslack
    omega
  have hitem : ∀ u ∈ items.map (fun s => dimerChain (p.itemDimers s)),
      u.length ≤ 15 * p.side := by
    intro u hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
    exact hd.2.2.1 s hs
  have hbulk : ∀ u ∈ bulkLengths.map (fun n => List.replicate n Residue.H),
      u.length ≤ bulkLengths.sum := by
    intro u hu
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hu
    simpa only [List.length_replicate] using List.le_sum_of_mem hn
  intro u hu
  simp only [reductionUnitBodies, List.mem_append] at hu
  rcases hu with ((((((h | h) | h) | h) | h) | h) | h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · simp only [List.length_singleton]; omega
    · simp only [List.length_singleton]; omega
    · simp only [List.length_singleton]; omega
    · omega
  · have h := hsep u h
    omega
  · simp only [List.mem_singleton] at h
    subst u
    omega
  · have h := hitem u h
    omega
  · simp only [List.mem_singleton] at h
    subst u
    omega
  · have hmem := List.mem_replicate.mp h
    rcases hmem with ⟨_, rfl⟩
    omega
  · have h := hbulk u h
    omega

theorem reduction_units_count_bound (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (hitems : ∀ s ∈ items, 0 < s) (htotal : items.sum = p.bins * p.capacity)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) :
    (p.reductionUnitBodies items bulkLengths).length ≤ 2 * p.side + bulkLengths.sum + 10 := by
  have hi := list_length_le_sum_of_pos items hitems
  have hb := list_length_le_sum_of_pos bulkLengths (fun n hn => by have h := hbulk n hn; omega)
  have hcap := p.total_capacity_le_side
  have hK : p.bins ≤ p.side := by have h := p.family_side_bound; omega
  rw [p.reductionUnitBodies_length]
  omega

theorem prescribedReductionWord_length_bound (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (sameSublattice : List Bool)
    (htotal : items.sum = p.bins * p.capacity) :
    (p.prescribedReductionWord items bulkLengths sameSublattice).length ≤
      2 + (p.reductionUnitBodies items bulkLengths).length *
        (bulkLengths.sum + 200 * (p.side + 1) +
          p.baseLinkerLength (p.reductionWireCount items bulkLengths) + 1) := by
  let N := (p.reductionUnitBodies items bulkLengths).length
  let L := p.baseLinkerLength (p.reductionWireCount items bulkLengths) + 1
  have hgap : ∀ i, p.prescribedLinkerGap items bulkLengths sameSublattice i + 2 ≤ L := by
    intro i
    rw [p.prescribedLinkerGap_add_two]
    unfold longLinkerLength
    split_ifs <;> dsimp [L] <;> omega
  have hw := assembleReductionWord_length_bound _ L hgap (p.reductionUnitBodies items bulkLengths)
  have hs := sum_word_lengths_le _ _ (p.reductionUnitBodies_length_bound items bulkLengths htotal)
  change (p.prescribedReductionWord items bulkLengths sameSublattice).length ≤ _ at hw
  dsimp [L] at hw
  nlinarith

end ConstructionParameters

end ProteinFolding.Tetrahedral
