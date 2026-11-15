import ProteinFolding.Tetrahedral.ReductionDimerProvenanceConcrete
import ProteinFolding.Tetrahedral.ReductionDimerProvenanceWeights

namespace ProteinFolding.Tetrahedral.ReductionDimerProvenance

open ReductionChainTag

theorem separator_weightSum (p : ConstructionParameters) (items : List ℕ) (k : ℕ) (hk : k ≤ p.bins)
    (F : ReductionChainTag → ℕ → ℕ) :
    (separatorBody p items k hk).catalogue.weightSum F = F (.entry k) 1 + F (.separator k) 2 + F (.exit k) 3 := by
  dsimp only [separatorBody]
  rw [DimerCatalogue.weightSum_cast, DimerCatalogue.weightSum_append,
    DimerCatalogue.weightSum_append, DimerCatalogue.weightSum_prependP,
    DimerCatalogue.weightSum_prependP, DimerCatalogue.weightSum_chain,
    DimerCatalogue.weightSum_chain, DimerCatalogue.weightSum_chain]

theorem catalogue_weightSum (p : ConstructionParameters) (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) (F : ReductionChainTag → ℕ → ℕ) :
    (catalogue p items bulkLengths gaps hbulk).val.weightSum F =
      ((bodies p items bulkLengths hbulk).map (fun u => u.catalogue.weightSum F)).sum := by
  dsimp only [catalogue]
  rw [DimerCatalogue.weightSum_cast, CataloguedBody.reduction_weightSum]

theorem catalogue_weightSum_formula (p : ConstructionParameters) (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) (F : ReductionChainTag → ℕ → ℕ) :
    (catalogue p items bulkLengths gaps hbulk).val.weightSum F =
      ((List.range (p.bins + 1)).map (fun k => F (.entry k) 1 + F (.separator k) 2 + F (.exit k) 3)).sum +
      F .leftFiller p.leftFiller + (items.map (fun s => F (.item s) (p.itemDimers s))).sum +
      F .rightFiller p.rightFiller + ((List.range 3).map (fun r => F (.ring r) (3 * (p.side - 2)))).sum := by
  rw [catalogue_weightSum]
  simp only [bodies, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.map_map, Function.comp_def, CataloguedBody.silent,
    CataloguedBody.chain, DimerCatalogue.weightSum_silent, DimerCatalogue.weightSum_chain,
    separator_weightSum, Nat.zero_add, Nat.add_zero]
  rw [map_attach_val (List.range (p.bins + 1))
    (fun k => F (.entry k) 1 + F (.separator k) 2 + F (.exit k) 3),
    map_attach_val items (fun s => F (.item s) (p.itemDimers s)),
    map_attach_val (List.range 3) (fun r => F (.ring r) (3 * (p.side - 2)))]
  simp

theorem small_weightSum (p : ConstructionParameters) (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) (hpos : ∀ s ∈ items, 0 < s)
    (v : ℕ) (hv : v = 1 ∨ v = 2 ∨ v = 3) :
    (catalogue p items bulkLengths gaps hbulk).val.weightSum (fun _ q => if q = v then 1 else 0) = p.bins + 1 := by
  rw [catalogue_weightSum_formula]
  have hlf := p.leftFiller_ge
  have hrf := p.rightFiller_ge
  have hm := p.side_ge
  have hi : (items.map (fun s => if p.itemDimers s = v then 1 else 0)).sum = 0 := by
    apply word_sum_map_zero
    intro s hs
    have h := p.itemDimers_ge s (hpos s hs)
    have hne : p.itemDimers s ≠ v := by omega
    exact if_neg hne
  have hleft : p.leftFiller ≠ v := by omega
  have hright : p.rightFiller ≠ v := by omega
  have hring : 3 * (p.side - 2) ≠ v := by omega
  simp only [if_neg hleft, if_neg hright, if_neg hring, hi, Nat.add_zero]
  rcases hv with rfl | rfl | rfl <;> simp

theorem small_chain_card (p : ConstructionParameters) (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) (hpos : ∀ s ∈ items, 0 < s)
    (v : ℕ) (hv : v = 1 ∨ v = 2 ∨ v = 3) :
    let c := (catalogue p items bulkLengths gaps hbulk).val
    letI := c.finiteIndex
    (Finset.univ.filter (fun i => c.q i = v)).card = p.bins + 1 := by
  dsimp only
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact small_weightSum p items bulkLengths gaps hbulk hpos v hv

theorem chain_positive (p : ConstructionParameters) (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) (hpos : ∀ s ∈ items, 0 < s)
    (i : (catalogue p items bulkLengths gaps hbulk).val.Index) :
    0 < (catalogue p items bulkLengths gaps hbulk).val.q i := by
  have h := (catalogue p items bulkLengths gaps hbulk).property i
  rcases h with ⟨hq, ht⟩
  cases htag : (catalogue p items bulkLengths gaps hbulk).val.tag i with
  | entry k => simp only [htag, size] at hq; omega
  | separator k => simp only [htag, size] at hq; omega
  | exit k => simp only [htag, size] at hq; omega
  | leftFiller => have hge := p.leftFiller_ge; simp only [htag, size] at hq; omega
  | rightFiller => have hge := p.rightFiller_ge; simp only [htag, size] at hq; omega
  | item s =>
    have hs : s ∈ items := by simpa only [htag, Valid] using ht
    have hge := p.itemDimers_ge s (hpos s hs)
    simp only [htag, size] at hq
    omega
  | ring r => have hge := p.side_ge; simp only [htag, size] at hq; omega

end ProteinFolding.Tetrahedral.ReductionDimerProvenance
