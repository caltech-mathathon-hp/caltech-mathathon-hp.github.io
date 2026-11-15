import ProteinFolding.Tetrahedral.FrameForcingCatalogueGeometry
import ProteinFolding.Tetrahedral.FrameForcingSlotDisjoint

/-! The actual HH catalogue and slot parity force every singleton chain
into an entry slot and every exit slot to be exactly one three-dimer chain. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

theorem actual_catalogue_singleton_sites (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (pre post : Sequence) (heq : p.reductionWord items bulkLengths gaps = pre ++ p.frameWord ++ post)
    (F : ForcedFrameFamily p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq).toFold)
      p.frameGaps1 p.frameGaps2)
    {α : Type} (c : DimerCatalogue α (p.reductionWord items bulkLengths gaps))
    (hpositive : ∀ i, 0 < c.q i)
    (hcount : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 1)).card = p.bins + 1) :
    ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 1)).biUnion (c.chainSites f) =
      Finset.univ.biUnion (fun k : Fin (p.bins + 1) => edgeBlock p.side F.first (6 * (k.val + 1)) 2) := by
  letI := c.finiteIndex
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq
  have hsub := p.actual_dimers_subset_remaining _ f hsupport hvertices pre post heq
  have hcovered := (p.actual_frame_family_slots_covered items bulkLengths gaps htotal hbulk f hsupport hvertices pre post heq F).1
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply two_slot_family_exhausts_singletons (c.chainSites f) c.q
    (fun k : Fin (p.bins + 1) => edgeBlock p.side F.first (6 * (k.val + 1)) 2)
    hpositive (c.chainSites_card f) (c.chainSites_disjoint f)
  · intro k
    exact edgeBlock_card p.side hm F.first _ _
  · intro k l hkl
    apply p.entry_slot_disjoint F.first (k.val + 1) (l.val + 1)
    intro he
    apply hkl
    apply Fin.ext
    omega
  · intro k x hx
    exact c.chainSites_cover f x (hcovered (k.val + 1) (by omega) (by omega) hx)
  · intro k i hmeet
    exact c.chainSites_component f p.side hsupport (p.frameRemainingEdges P) _ hsub
      (p.forced_family_entry_slot _ F (k.val + 1) (by omega) (by omega)).2
      (p.forced_family_entry_slot_P3_closed _ F (k.val + 1) (by omega) (by omega)) i hmeet
  · simpa only [Fintype.card_fin] using hcount

theorem actual_catalogue_exit_slot_chain (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (pre post : Sequence) (heq : p.reductionWord items bulkLengths gaps = pre ++ p.frameWord ++ post)
    (F : ForcedFrameFamily p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq).toFold)
      p.frameGaps1 p.frameGaps2)
    {α : Type} (c : DimerCatalogue α (p.reductionWord items bulkLengths gaps))
    (hpositive : ∀ i, 0 < c.q i)
    (hcount : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 1)).card = p.bins + 1)
    (k : ℕ) (hk : k ≤ p.bins) :
    ∃ i : c.Index, c.q i = 3 ∧ c.chainSites f i =
      edgeBlock p.side F.second (2 * p.side - (10 * k + 13)) 6 := by
  letI := c.finiteIndex
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq
  have hsub := p.actual_dimers_subset_remaining _ f hsupport hvertices pre post heq
  have hcovered := (p.actual_frame_family_slots_covered items bulkLengths gaps htotal hbulk f hsupport hvertices pre post heq F).2
  have hsingles := p.actual_catalogue_singleton_sites items bulkLengths gaps htotal hbulk f hsupport hvertices
    pre post heq F c hpositive hcount
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply six_component_one_three_chain (c.chainSites f) c.q _
    (edgeBlock_card p.side hm F.second _ _) hpositive (c.chainSites_card f) (c.chainSites_disjoint f)
  · intro x hx
    exact c.chainSites_cover f x (hcovered k hk hx)
  · intro i hmeet
    exact c.chainSites_component f p.side hsupport (p.frameRemainingEdges P) _ hsub
      (p.forced_family_exit_slot _ F k hk).2 (p.forced_family_exit_slot_P3_closed _ F k hk) i hmeet
  · intro i hqi
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxSingles : x ∈ (Finset.univ.filter (fun i => c.q i = 1)).biUnion (c.chainSites f) :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqi⟩, hx⟩
    rw [hsingles] at hxSingles
    obtain ⟨j, _, hxEntry⟩ := Finset.mem_biUnion.mp hxSingles
    exact Finset.disjoint_left.mp (p.forced_family_entry_exit_disjoint _ F (j.val + 1) k
      (by omega) (by omega) hk) hxEntry hy

end ProteinFolding.Tetrahedral.ConstructionParameters
