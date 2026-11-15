import ProteinFolding.Tetrahedral.ReductionDimerProvenanceCounts

/-! Exactly one declared central chain carries each separator tag.
The tags distinguish occurrences even when item sizes repeat. -/

namespace ProteinFolding.Tetrahedral

theorem ReductionDimerProvenance.separator_tag_weight (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (k : ℕ) (hk : k ≤ p.bins) :
    (catalogue p items bulkLengths gaps hbulk).val.weightSum
      (fun tag _ => if tag = .separator k then 1 else 0) = 1 := by
  classical
  let F : ReductionChainTag → ℕ → ℕ := fun tag _ => match tag with
    | .separator l => if l = k then 1 else 0
    | _ => 0
  have hF : F = (fun tag _ => if tag = .separator k then 1 else 0) := by
    funext tag q
    cases tag <;> simp [F]
  rw [← hF]
  calc
    (catalogue p items bulkLengths gaps hbulk).val.weightSum F =
        ((List.range (p.bins + 1)).map (fun l => if l = k then 1 else 0)).sum := by
      rw [catalogue_weightSum_formula]
      simp [F]
    _ = 1 := by
      rw [← List.sum_toFinset _ List.nodup_range]
      simp [show k < p.bins + 1 by omega]

theorem DimerCatalogue.tag_unique_of_weight_one {α : Type} [DecidableEq α] {S : Sequence}
    (c : DimerCatalogue α S) (tag : α)
    (hc : c.weightSum (fun t _ => if t = tag then 1 else 0) = 1)
    (i j : c.Index) (hi : c.tag i = tag) (hj : c.tag j = tag) : i = j := by
  classical
  letI := c.finiteIndex
  let I := Finset.univ.filter (fun t => c.tag t = tag)
  have hcard : I.card = 1 := by
    change (Finset.univ.filter (fun t => c.tag t = tag)).card = 1
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact hc
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hia : i = a := by
    have hm : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    simpa only [ha, Finset.mem_singleton] using hm
  have hja : j = a := by
    have hm : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    simpa only [ha, Finset.mem_singleton] using hm
  exact hia.trans hja.symm

end ProteinFolding.Tetrahedral
