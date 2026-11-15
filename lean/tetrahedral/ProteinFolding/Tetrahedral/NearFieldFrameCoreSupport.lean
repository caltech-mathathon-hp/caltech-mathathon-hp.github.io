import ProteinFolding.Tetrahedral.NearFieldFrameCoreFold
import ProteinFolding.Tetrahedral.NearFieldFrameRawLocality

/-! Hydrophobic support and scalar locality of the actual assembled frame core. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

private theorem subset_of_support_eq {A B T : Finset Site} (h : A = B) (hB : B ⊆ T) : A ⊆ T := by
  rw [h]
  exact hB

private theorem edgeBlock_subset_oct {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ)
    (hroom : a + n ≤ 2 * m - 1) : edgeBlock m F a n ⊆ octahedron m := by
  intro x hx
  obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hx
  have ht' := Finset.mem_range.mp ht
  rw [← heq]
  rcases octEdgeZigzag_mem hm F (show a + t < 2 * m - 1 by omega) with h | h <;> exact h.1.1

theorem frameCorePiece_hSupport_subset_oct (p : ConstructionParameters) (i : FrameCoreIndex p) :
    hSupport (frameCorePiece p i).word (frameCorePiece p i).fold ⊆ octahedron p.side := by
  rcases i with i | i
  · change hSupport (frameHRunWord p i) (frameHRunFold p i) ⊆ _
    exact subset_of_support_eq
      ((hSupport_allH_eq_foldSites (frameHRunData p i).count (frameHRunFold p i)).trans
        (frameHRunFold_sites p i))
      (edgeBlock_subset_oct (m := p.side) (by have h := p.side_ge; omega) _ _ _ (frameHRun_room p i))
  · change hSupport (List.replicate (nearFrameLength (frameLinkKind i) - 2) .P)
      (frameLinkWordFold p i) ⊆ _
    rw [hSupport_allP_empty]
    exact Finset.empty_subset _

theorem frameCoreFold_hSupport_subset_oct (p : ConstructionParameters) :
    hSupport (p.framePart1 ++ p.framePart2) (frameCoreFold p) ⊆ octahedron p.side := by
  rw [frameCoreFold, transportWordFold_hSupport]
  apply (frameCoreAssembly p).hSupport_subset
  intro q hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  exact frameCorePiece_hSupport_subset_oct p i

theorem octSite_mem_solid_one {m : ℕ} (x : Site) (hx : x ∈ octahedron m) : x ∈ skinSolid m 1 := by
  have hzero : x ∈ skinSolid m 0 := by rwa [skinSolid_zero]
  exact (skinSolid_mono m (by omega : 0 ≤ 1)) hzero

theorem skinSite_mem_solid_one {m : ℕ} (x : Site) (hx : x ∈ skin m 1) : x ∈ skinSolid m 1 :=
  skin_subset_solid m 1 hx

theorem octSite_inSkinSolid_one {m : ℕ} (x : Site) (hx : x ∈ octahedron m) : InSkinSolid m 1 x :=
  (mem_skinSolid m 1 x).mp (octSite_mem_solid_one x hx)

theorem skinSite_inSkinSolid_one {m : ℕ} (x : Site) (hx : x ∈ skin m 1) : InSkinSolid m 1 x :=
  (mem_skinSolid m 1 x).mp (skinSite_mem_solid_one x hx)

private theorem rawFold_inSkinSolid_one {m n : ℕ} (f : Fold tetrahedralLattice n)
    (hf : ∀ s, f.pos s ∈ skin m 1) : ∀ s, InSkinSolid m 1 (f.pos s) := by
  intro s
  exact (mem_skinSolid m 1 (f.pos s)).mp (skin_subset_solid m 1 (hf s))

theorem frameCorePiece_inSkinSolid_one (p : ConstructionParameters) (i : FrameCoreIndex p)
    (r : Fin (frameCorePiece p i).word.length) :
    InSkinSolid p.side 1 ((frameCorePiece p i).fold.pos r) := by
  intro d
  rcases i with i | i
  · dsimp only [frameCorePiece, frameHRunPiece] at r ⊢
    exact fold_inOct_to_inSkinSolid_one (S := frameHRunWord p i) (m := p.side)
      (frameHRunFold p i) (frameHRunFold_mem_oct p i) r d
  · dsimp only [frameCorePiece, frameLinkPiece] at r ⊢
    change _ ≤ tetraCoordinate p.side ((frameLinkWordFold p i).pos r).val d ∧
      tetraCoordinate p.side ((frameLinkWordFold p i).pos r).val d ≤ _
    rw [frameLinkWordFold_pos]
    let j : Fin (nearFrameLength (frameLinkKind (p := p) i) - 2) :=
      ⟨r.val, by simpa only [frameLinkWord, List.length_replicate] using r.isLt⟩
    dsimp only [frameLinkFold]
    exact framePFold_inSkinSolid_one p.side (frameLinkParameter (p := p) i) (frameLinkKind (p := p) i)
      (frameLinkParameter_odd p i) (frameLinkParameter_ge p i) (frameLinkParameter_room p i) j d

theorem frameCorePiece_mem_solid_one (p : ConstructionParameters) (i : FrameCoreIndex p)
    (r : Fin (frameCorePiece p i).word.length) :
    (frameCorePiece p i).fold.pos r ∈ skinSolid p.side 1 := by
  rw [mem_skinSolid]
  exact frameCorePiece_inSkinSolid_one p i r

theorem frameCoreFold_mem_solid_one (p : ConstructionParameters)
    (r : Fin (p.framePart1 ++ p.framePart2).length) :
    (frameCoreFold p).pos r ∈ skinSolid p.side 1 := by
  rw [mem_skinSolid]
  unfold frameCoreFold
  refine transportWordFold_property
    ((frameCoreAssembly p).word_eq.trans (frameCorePieces_words p))
    (frameCoreAssembly p).piece.fold (InSkinSolid p.side 1) ?_ r
  intro j
  apply (frameCoreAssembly p).position_property (InSkinSolid p.side 1) _ j
  intro q hq s
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  exact frameCorePiece_inSkinSolid_one p i s

end ProteinFolding.Tetrahedral.NearField
