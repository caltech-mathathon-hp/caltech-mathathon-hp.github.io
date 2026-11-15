import ProteinFolding.Tetrahedral.FrameForcingActualTrack
import ProteinFolding.Tetrahedral.FrameForcingSeparatorAnchors
import ProteinFolding.Tetrahedral.FrameForcingSeparatorLocation
import ProteinFolding.Tetrahedral.FrameForcingTrackPairHeights
import ProteinFolding.Tetrahedral.FrameForcingSeparatorActualPoints
import ProteinFolding.Tetrahedral.FrameForcingTrackPairSets

/-! Each actual separator occupies two consecutive physical track pairs,
with its first pair in the exact scale-preserving window. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

theorem catalogue_separator_window (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity)
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
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b)
    (k : ℕ) (hk : k ≤ p.bins)
    {α : Type} (c : DimerCatalogue α (p.reductionWord items bulkLengths gaps))
    (pre post : Sequence) (hsep : p.reductionWord items bulkLengths gaps =
      pre ++ capWord (p.separatorWord k) ++ post)
    (iC : c.Index) (hC : c.q iC = 2)
    (hpreC : (c.pre iC).length = pre.length + p.entryTether k + 2)
    (r s : ℕ) (hr : r ≤ 6 * p.bins + 7) (hs : s ≤ 2 * p.side - 2)
    (hdef : 2 * p.side - 2 - s ≤ 10 * p.bins + 11)
    (hentry : (OctWordPath.ofFoldOccurrence f p.side hsupport pre
      (capWord (p.separatorWord k)) post hsep).site 2 = octEdgeZigzag p.side F.first r)
    (hexit : (OctWordPath.ofFoldOccurrence f p.side hsupport pre
      (capWord (p.separatorWord k)) post hsep).site
      (p.entryTether k + p.exitTether k + 10) = octEdgeZigzag p.side F.second s) :
    ∃ u v : ℕ,
      (u + 1 = v ∨ v + 1 = u) ∧
      |(min u v : ℕ) - (p.separatorIndex k : ℤ)| ≤ (p.separatorRadius : ℤ) ∧
      p.separatorCentreSites k (OctWordPath.ofFoldOccurrence f p.side hsupport
        pre (capWord (p.separatorWord k)) post hsep) =
        {frameTrackPoint p.side F.first (2 * u), frameTrackPoint p.side F.first (2 * u + 1),
          frameTrackPoint p.side F.first (2 * v), frameTrackPoint p.side F.first (2 * v + 1)} ∧
      (∀ t, c.q t ≠ 2 → Disjoint (c.chainSites f t)
        (p.separatorCentreSites k (OctWordPath.ofFoldOccurrence f p.side hsupport
          pre (capWord (p.separatorWord k)) post hsep))) ∧
      ∃ t, c.q t = 2 ∧ p.separatorCentreSites k (OctWordPath.ofFoldOccurrence f p.side hsupport
        pre (capWord (p.separatorWord k)) post hsep) ⊆ c.chainSites f t := by
  let S := p.reductionWord items bulkLengths gaps
  let D := foldDimerPairs S f
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre (capWord (p.separatorWord k)) post hsep
  obtain ⟨i, j, hne, hA, hB, hC', hD, hlink, hcentreSub, hcentreAvoid⟩ :=
    catalogue_separator_centre_data p k f hsupport c pre post hsep iC hC hpreC
  have hstrict := p.separator_centre_strict_heights k hk P F.first F.second F.next_big hsmall ha
    r s hr hs hdef hentry hexit
  have hon := p.separator_centre_on_track k hk P F.first F.second F.next_big hsmall ha
    r s hr hs hdef hentry hexit
  have hAset : P.site (p.entryTether k + 3) ∈ p.separatorCentreSites k P :=
    Finset.mem_insert_self _ _
  have hCset : P.site (p.entryTether k + 8) ∈ p.separatorCentreSites k P :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have htrack (x : Site) (hx : x ∈ p.separatorCentreSites k P) : x ∈ frameTrackSites p.side F.first := by
    obtain ⟨t, htlo, hthi, heq⟩ := hon x hx
    apply Finset.mem_image.mpr
    refine ⟨t, Finset.mem_range.mpr (by have hm := p.side_ge; omega), ?_⟩
    rw [frameTrackPoint, if_neg (by omega : t ≠ 0)]
    exact heq.symm
  have hi : D.point (i, false) ∈ frameTrackSites p.side F.first := by rw [hA]; exact htrack _ hAset
  have hj : D.point (j, false) ∈ frameTrackSites p.side F.first := by rw [hC']; exact htrack _ hCset
  have hHi : 6 ≤ frameH2 p.side F.first (D.point (i, false)) := by rw [hA]; exact (hstrict _ hAset).2.1
  have hHj : 6 ≤ frameH2 p.side F.first (D.point (j, false)) := by rw [hC']; exact (hstrict _ hCset).2.1
  obtain ⟨u, v, hu, hv, huv, hwindow⟩ := p.two_pair_separator_window D F.first F.second
    (p.actual_track_subset_dimers items bulkLengths gaps htotal hbulk f hsupport hvertices
      framePre framePost hframe F hsmall ha)
    (p.actual_track_pairs_closed items bulkLengths gaps htotal hbulk f hsupport hvertices
      framePre framePost hframe F hsmall ha)
    (foldDimerPairs_adjacent S f) k hk P F.next_big hsmall ha r s hentry hexit
    i j hne hi hj hHi hHj hlink hA hD
  refine ⟨u, v, huv, hwindow, ?_, hcentreAvoid, iC, hC, hcentreSub⟩
  change p.separatorCentreSites k P = _
  rw [separatorCentreSites, ← hA, ← hB, ← hC', ← hD]
  exact FinitePairFamily.OnTrackPair.two_pairs_sites D p.side F.first hu hv

theorem actual_separator_window (p : ConstructionParameters)
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
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b)
    (k : ℕ) (hk : k ≤ p.bins) :
    let c := (ReductionDimerProvenance.catalogue p items bulkLengths gaps hbulk).val
    ∃ (pre post : Sequence) (hsep : p.reductionWord items bulkLengths gaps =
        pre ++ capWord (p.separatorWord k) ++ post) (u v : ℕ),
      (u + 1 = v ∨ v + 1 = u) ∧
      |(min u v : ℕ) - (p.separatorIndex k : ℤ)| ≤ (p.separatorRadius : ℤ) ∧
      p.separatorCentreSites k (OctWordPath.ofFoldOccurrence f p.side hsupport
        pre (capWord (p.separatorWord k)) post hsep) =
        {frameTrackPoint p.side F.first (2 * u), frameTrackPoint p.side F.first (2 * u + 1),
          frameTrackPoint p.side F.first (2 * v), frameTrackPoint p.side F.first (2 * v + 1)} ∧
      (∀ t, c.q t ≠ 2 → Disjoint (c.chainSites f t)
        (p.separatorCentreSites k (OctWordPath.ofFoldOccurrence f p.side hsupport
          pre (capWord (p.separatorWord k)) post hsep))) ∧
      ∃ t, c.q t = 2 ∧ p.separatorCentreSites k (OctWordPath.ofFoldOccurrence f p.side hsupport
        pre (capWord (p.separatorWord k)) post hsep) ⊆ c.chainSites f t := by
  let c := (ReductionDimerProvenance.catalogue p items bulkLengths gaps hbulk).val
  obtain ⟨pre, post, hsep, iC, hC, hpreC, r, s, hr, hs, hdef, hentry, hexit⟩ :=
    p.actual_separator_anchors items bulkLengths gaps htotal hpos hbulk f hsupport hvertices
      framePre framePost hframe F k hk
  obtain ⟨u, v, hresult⟩ := p.catalogue_separator_window items bulkLengths gaps htotal hbulk f hsupport hvertices
    framePre framePost hframe F hsmall ha k hk c pre post hsep iC hC hpreC r s hr hs hdef hentry hexit
  exact ⟨pre, post, hsep, u, v, hresult⟩

end ProteinFolding.Tetrahedral.ConstructionParameters
