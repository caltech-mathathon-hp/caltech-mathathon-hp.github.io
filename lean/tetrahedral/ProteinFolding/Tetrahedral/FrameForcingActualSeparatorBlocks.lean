import ProteinFolding.Tetrahedral.FrameForcingActualSeparator
import ProteinFolding.Tetrahedral.FrameForcingSeparatorBlocks

/-! All size-two chains are precisely the K+1 forced separator blocks.
Their physical starts satisfy the sharp ordered windows. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem actual_separator_blocks (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hpos : ∀ s ∈ items, 0 < s)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (framePre framePost : Sequence)
    (hframe : p.reductionWord items bulkLengths gaps = framePre ++ p.frameWord ++ framePost)
    (F : ActualFrameConfiguration p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport framePre p.frameWord framePost hframe).toFold)
      p.frameGaps1 p.frameGaps2
      (OctWordPath.ofFoldOccurrence f p.side hsupport framePre p.frameWord framePost hframe).site p.framePart1.length)
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b) :
    let c := (ReductionDimerProvenance.catalogue p items bulkLengths gaps hbulk).val
    letI := c.finiteIndex
    ∃ starts : Fin (p.bins + 1) → ℕ,
      (∀ k, |(starts k : ℤ) - (p.separatorIndex k.val : ℤ)| ≤ (p.separatorRadius : ℤ)) ∧
      (Finset.univ.filter (fun i => c.q i = 2)).biUnion (c.chainSites f) =
        Finset.univ.biUnion (fun k => frameTrackBand p.side F.first (2 * starts k) (2 * starts k + 4)) := by
  classical
  let c := (ReductionDimerProvenance.catalogue p items bulkLengths gaps hbulk).val
  letI := c.finiteIndex
  have hm := p.side_ge
  have hseparators (k : Fin (p.bins + 1)) := p.actual_separator_window items bulkLengths gaps htotal hpos
    hbulk f hsupport hvertices framePre framePost hframe F hsmall ha k.val (by have h := k.isLt; omega)
  choose pre post hsep u v hconsecutive hwindow hsites havoid centre hqcentre hsubcentre using hseparators
  let W (k : Fin (p.bins + 1)) := twoTrackPairs p.side F.first (u k) (v k)
  have hWcard (k : Fin (p.bins + 1)) : (W k).card = 4 :=
    twoTrackPairs_card p.side (by omega) F.first (u k) (v k) (hconsecutive k)
  have hWdisjoint (k l : Fin (p.bins + 1)) (hne : k ≠ l) : Disjoint (W k) (W l) := by
    have hval : k.val ≠ l.val := by intro h; exact hne (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hkl | hlk
    · apply twoTrackPairs_disjoint p.side (by omega) F.first (u k) (v k) (u l) (v l)
        (hconsecutive k) (hconsecutive l)
      have horder := p.separator_window_order_of_lt k.val l.val (min (u k) (v k)) (min (u l) (v l))
        hkl (hwindow k) (hwindow l)
      omega
    · apply Disjoint.symm
      apply twoTrackPairs_disjoint p.side (by omega) F.first (u l) (v l) (u k) (v k)
        (hconsecutive l) (hconsecutive k)
      have horder := p.separator_window_order_of_lt l.val k.val (min (u l) (v l)) (min (u k) (v k))
        hlk (hwindow l) (hwindow k)
      omega
  have hsubset (k : Fin (p.bins + 1)) :
      W k ⊆ (Finset.univ.filter (fun i => c.q i = 2)).biUnion (c.chainSites f) := by
    intro x hx
    have hxCentre : x ∈ p.separatorCentreSites k.val (OctWordPath.ofFoldOccurrence f p.side hsupport
        (pre k) (capWord (p.separatorWord k.val)) (post k) (hsep k)) := by
      rw [hsites k]
      exact hx
    exact Finset.mem_biUnion.mpr ⟨centre k, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hqcentre k⟩, hsubcentre k hxCentre⟩
  have hcount : (Finset.univ.filter (fun i => c.q i = 2)).card = Fintype.card (Fin (p.bins + 1)) := by
    simpa only [Fintype.card_fin] using
      ReductionDimerProvenance.small_chain_card p items bulkLengths gaps hbulk hpos 2 (Or.inr (Or.inl rfl))
  have hexhaust := four_blocks_exhaust_double_chains (c.chainSites f) c.q W
    (c.chainSites_card f) (c.chainSites_disjoint f) hWcard hWdisjoint hsubset hcount
  refine ⟨fun k => min (u k) (v k), hwindow, ?_⟩
  rw [hexhaust]
  congr 1
  funext k
  exact twoTrackPairs_eq_band p.side F.first (u k) (v k) (hconsecutive k)

end ProteinFolding.Tetrahedral.ConstructionParameters
