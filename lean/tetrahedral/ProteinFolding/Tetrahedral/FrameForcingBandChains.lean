import ProteinFolding.Tetrahedral.FrameForcingTrackBands
import ProteinFolding.Tetrahedral.FrameForcingActualChains

/-! Literal whole dimer chains that meet a sealed track band remain in
that band.  Their actual HH sites give the corresponding capacity bound. -/

namespace ProteinFolding.Tetrahedral

theorem factorDimerPairs_band_all (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hm : 3 ≤ m) (hsupport : hSupport S f = octahedron m)
    (pre post : Sequence) (q : ℕ) (heq : S = pre ++ capWord (dimerChain q) ++ post)
    (F : OctEdgeFrame) (lo hi : ℕ) (hlo : 5 ≤ lo) (hhi : hi + 6 ≤ 2 * m)
    (V : Finset Site) (hV : V ⊆ bulkDeletedEdges m)
    (hsub : (factorDimerPairs S f pre post q heq).covered ⊆ V)
    (hguard : ∀ s ∈ Finset.Ico (lo - 2) lo ∪ Finset.Ico hi (hi + 2), frameTrackPoint m F s ∉ V)
    (hmeet : ∃ i b, (factorDimerPairs S f pre post q heq).point (i, b) ∈ frameTrackBand m F lo hi) :
    (factorDimerPairs S f pre post q heq).covered ⊆ frameTrackBand m F lo hi := by
  have hclosed := frameTrackBand_closed m hm F lo hi hlo hhi V hV hguard
  exact (factorDimerPairs S f pre post q heq).chain_component_all q V (frameTrackBand m F lo hi)
    hsub (fun i => foldDimerPairs_adjacent S f (factorDimerOccurrence S pre post q heq i))
    (factorDimerPairs_link S f m hsupport pre post q heq)
    (fun x hx y hy h => hclosed x hx y hy (Or.inl h))
    (fun x hx y hy h => hclosed x hx y hy (Or.inr h)) hmeet

theorem factorDimerPairs_band_size (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hm : 3 ≤ m) (hsupport : hSupport S f = octahedron m)
    (pre post : Sequence) (q : ℕ) (heq : S = pre ++ capWord (dimerChain q) ++ post)
    (F : OctEdgeFrame) (lo hi : ℕ) (hlo : 5 ≤ lo) (hhi : hi + 6 ≤ 2 * m)
    (V : Finset Site) (hV : V ⊆ bulkDeletedEdges m)
    (hsub : (factorDimerPairs S f pre post q heq).covered ⊆ V)
    (hguard : ∀ s ∈ Finset.Ico (lo - 2) lo ∪ Finset.Ico hi (hi + 2), frameTrackPoint m F s ∉ V)
    (hmeet : ∃ i b, (factorDimerPairs S f pre post q heq).point (i, b) ∈ frameTrackBand m F lo hi) :
    2 * q ≤ hi - lo := by
  have hc := Finset.card_le_card (factorDimerPairs_band_all S f m hm hsupport
    pre post q heq F lo hi hlo hhi V hV hsub hguard hmeet)
  rw [FinitePairFamily.covered_card, Fintype.card_fin, frameTrackBand_card m (by omega) F lo hi] at hc
  exact hc

end ProteinFolding.Tetrahedral
