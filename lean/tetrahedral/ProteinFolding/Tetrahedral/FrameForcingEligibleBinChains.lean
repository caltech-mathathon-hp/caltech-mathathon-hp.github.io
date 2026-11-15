import ProteinFolding.Tetrahedral.FrameForcingExhaustedBinChains
import ProteinFolding.Tetrahedral.FrameForcingBinChainHeights
import ProteinFolding.Tetrahedral.FrameForcingBinLoad

/-! The anchor height bounds and exact physical bin capacity classify
every chain meeting a bin as an eligible whole item chain. -/

namespace ProteinFolding.Tetrahedral.DimerCatalogue

theorem bin_chain_eligible {α : Type} {S : Sequence}
    (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length)
    (p : ConstructionParameters) (hsupport : hSupport S f = octahedron p.side)
    (F G : OctEdgeFrame) (hGk : G.k = F.a) (hGj : G.j = F.j) (hGa : G.a = F.b)
    (starts : Fin (p.bins + 1) → ℕ)
    (hwindow : ∀ k, |(starts k : ℤ) - (p.separatorIndex k.val : ℤ)| ≤ (p.separatorRadius : ℤ))
    (hexhaust : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 2)).biUnion (c.chainSites f) =
      Finset.univ.biUnion (fun k => frameTrackBand p.side F (2 * starts k) (2 * starts k + 4)))
    (hsingle : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 1)).biUnion (c.chainSites f) =
      Finset.univ.biUnion (fun k : Fin (p.bins + 1) => edgeBlock p.side F (6 * (k.val + 1)) 2))
    (hexit : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 3)).biUnion (c.chainSites f) =
      Finset.univ.biUnion (fun k : Fin (p.bins + 1) => edgeBlock p.side G (2 * p.side - (10 * k.val + 13)) 6))
    (eligible : Finset c.Index)
    (hclass : ∀ t, c.q t ≠ 1 → c.q t ≠ 2 → c.q t ≠ 3 →
      c.q t ≤ p.binDimers + p.sigma + 6 → t ∈ eligible)
    (k : Fin p.bins) (t : c.Index)
    (hmeet : (c.chainSites f t ∩ p.binTrackRegion F starts k).Nonempty) :
    t ∈ eligible ∧ c.chainSites f t ⊆ p.binTrackRegion F starts k := by
  have hm := p.side_ge
  obtain ⟨hne₂, hwhole⟩ := c.bin_chain_of_double_exhaustion f p hsupport F starts hwindow hexhaust k t hmeet
  have hmarg := p.binTrackRegion_margins F starts hwindow k
  obtain ⟨x, hx⟩ := hmeet
  obtain ⟨hxC, hxW⟩ := Finset.mem_inter.mp hx
  have hheights := frameTrackBand_interior_heights p.side (by omega) F _ _ hmarg.1 hmarg.2.1 x hxW
  have hne₁ : c.q t ≠ 1 := by
    intro ht
    have h := c.singleton_height_bound f p.side (by omega) F p.bins hsingle t ht x hxC
    omega
  have hne₃ : c.q t ≠ 3 := by
    intro ht
    have h := c.exit_height_bound f p.side (by omega) F G p.bins hGk hGj hGa hexit t ht x hxC
    omega
  have hwindowL : |(starts (p.binLeftIndex k) : ℤ) - (p.separatorIndex k.val : ℤ)| ≤
      (p.separatorRadius : ℤ) := hwindow _
  have hwindowR : |(starts (p.binRightIndex k) : ℤ) - (p.separatorIndex (k.val + 1) : ℤ)| ≤
      (p.separatorRadius : ℤ) := hwindow _
  have hcardW : (p.binTrackRegion F starts k).card =
      2 * (starts (p.binRightIndex k) - starts (p.binLeftIndex k) - 2) :=
    p.separator_bin_band_card F k.val (starts (p.binLeftIndex k)) (starts (p.binRightIndex k)) hwindowL hwindowR
  have hc := Finset.card_le_card hwhole
  rw [c.chainSites_card f t, hcardW] at hc
  have herror := p.separator_bin_capacity_error k.val (starts (p.binLeftIndex k))
    (starts (p.binRightIndex k)) hwindowL hwindowR
  have herr := abs_le.mp herror
  have hbound : c.q t ≤ p.binDimers + p.sigma + 6 := by omega
  exact ⟨hclass t hne₁ hne₂ hne₃ hbound, hwhole⟩

end ProteinFolding.Tetrahedral.DimerCatalogue
