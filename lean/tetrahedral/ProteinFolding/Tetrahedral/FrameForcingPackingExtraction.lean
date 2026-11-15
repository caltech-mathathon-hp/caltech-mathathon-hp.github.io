import ProteinFolding.Tetrahedral.FrameForcingBinRegions
import ProteinFolding.Tetrahedral.FrameForcingBinLoad
import ProteinFolding.Tetrahedral.FrameForcingCatalogueGeometry
import ProteinFolding.Tetrahedral.PackingFromFiniteBins

/-! Whole-item classification and actual track coverage give exact full
source bins and an occurrence-preserving list packing. -/

namespace ProteinFolding.Tetrahedral.DimerCatalogue

open scoped BigOperators

theorem packing_of_bin_classification {α : Type} {S : Sequence}
    (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length)
    (p : ConstructionParameters) (F : OctEdgeFrame) (starts : Fin (p.bins + 1) → ℕ)
    (hwindow : ∀ k, |(starts k : ℤ) - (p.separatorIndex k.val : ℤ)| ≤ (p.separatorRadius : ℤ))
    (htrack : frameTrackSites p.side F ⊆ (foldDimerPairs S f).covered)
    (items : List ℕ) (eligible : Finset c.Index) (value : c.Index → ℕ)
    (hperm : items.Perm (eligible.toList.map value))
    (hpos : ∀ i ∈ eligible, 0 < value i)
    (hsize : ∀ i ∈ eligible, c.q i = p.itemDimers (value i))
    (htotal : items.sum = p.capacity * p.bins)
    (hclass : ∀ k t, (c.chainSites f t ∩ p.binTrackRegion F starts k).Nonempty →
      t ∈ eligible ∧ c.chainSites f t ⊆ p.binTrackRegion F starts k) :
    ∃ parts : List (List ℕ), parts.length = p.bins ∧ items.Perm parts.flatten ∧
      ∀ part ∈ parts, part.sum = p.capacity := by
  classical
  let bucket (k : Fin p.bins) := eligible.filter
    (fun t => (c.chainSites f t ∩ p.binTrackRegion F starts k).Nonempty)
  have hsub (k : Fin p.bins) : bucket k ⊆ eligible := Finset.filter_subset _ _
  have hwhole (k : Fin p.bins) (t : c.Index) (ht : t ∈ bucket k) :
      c.chainSites f t ⊆ p.binTrackRegion F starts k :=
    (hclass k t (Finset.mem_filter.mp ht).2).2
  have hdisjoint (k l : Fin p.bins) (hne : k ≠ l) : Disjoint (bucket k) (bucket l) := by
    apply Finset.disjoint_left.mpr
    intro t ht hl
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp ht).2
    obtain ⟨hxC, hxW⟩ := Finset.mem_inter.mp hx
    exact Finset.disjoint_left.mp (p.binTrackRegion_pairwise_disjoint F starts hwindow k l hne)
      hxW (hwhole l t hl hxC)
  have hcover (k : Fin p.bins) :
      (bucket k).biUnion (c.chainSites f) = p.binTrackRegion F starts k := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
      exact hwhole k t ht hxt
    · intro x hx
      have hxTrack := (p.binTrackRegion_margins F starts hwindow k).2.2 hx
      obtain ⟨t, hxt⟩ := c.chainSites_cover f x (htrack hxTrack)
      have hmeet : (c.chainSites f t ∩ p.binTrackRegion F starts k).Nonempty :=
        ⟨x, Finset.mem_inter.mpr ⟨hxt, hx⟩⟩
      exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_filter.mpr ⟨(hclass k t hmeet).1, hmeet⟩, hxt⟩
  have hload (k : Fin p.bins) : (∑ t ∈ bucket k, value t) = p.capacity := by
    have hwindowL : |(starts (p.binLeftIndex k) : ℤ) - (p.separatorIndex k.val : ℤ)| ≤
        (p.separatorRadius : ℤ) := hwindow _
    have hwindowR : |(starts (p.binRightIndex k) : ℤ) - (p.separatorIndex (k.val + 1) : ℤ)| ≤
        (p.separatorRadius : ℤ) := hwindow _
    apply p.bin_load_of_item_chain_cover (bucket k) value (c.chainSites f) _ _ F k.val
      (starts (p.binLeftIndex k)) (starts (p.binRightIndex k)) hwindowL hwindowR (hcover k)
    · intro t ht
      exact (c.chainSites_card f t).trans (congrArg (2 * ·) (hsize t (hsub k ht)))
    · intro t _ u _ hne
      exact c.chainSites_disjoint f t u hne
  exact packing_of_finite_full_buckets items p.capacity p.bins eligible value hperm hpos htotal
    bucket hsub hdisjoint hload

end ProteinFolding.Tetrahedral.DimerCatalogue
