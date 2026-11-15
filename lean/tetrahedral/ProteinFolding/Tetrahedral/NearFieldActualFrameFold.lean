import ProteinFolding.Tetrahedral.NearFieldFrameCoreEndpoints
import ProteinFolding.Tetrahedral.NearFieldFrameCoreSupport
import ProteinFolding.Tetrahedral.NearFieldCapFoldSites
import ProteinFolding.Tetrahedral.NearFieldFrameTrackCoreSeparation

/-! The complete capped frame, folding its exact source word with no auxiliary
geometry certificate as an input. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096

def frameFirstColumn (p : ConstructionParameters) : DanglingColumn p.side :=
  frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) true

def frameLastColumn (p : ConstructionParameters) : DanglingColumn p.side :=
  frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) false

theorem frameCore_word_pos (p : ConstructionParameters) : 0 < (p.framePart1 ++ p.framePart2).length := by
  simp only [List.length_append, ConstructionParameters.framePart1, List.length_append,
    List.length_singleton, List.length_replicate]
  omega

noncomputable def frameCappedFold (p : ConstructionParameters) :
    Fold tetrahedralLattice (capWord (p.framePart1 ++ p.framePart2)).length :=
  cappedWordFold (frameCoreFold p) (frameFirstColumn p).seed (frameLastColumn p).seed
    (frameCore_word_pos p)
    (fun i => (frameCoreFold_ne_endpointColumn p true 0 i).symm)
    (frameCoreFold_ne_endpointColumn p false 0)
    (frameEndpointColumns_seed_ne (by have h := p.side_ge; omega : 2 ≤ p.side))
    (by
      intro i hi
      rw [frameCoreFold_first p i hi]
      have he := frameEndpointVertex_eq_edge p true
      change (frameFirstColumn p).owner = octEdgeZigzag p.side entryEdgeFrame 0 at he
      rw [← he]
      exact (step_adj (frameFirstColumn p).owner (frameFirstColumn p).dir).symm)
    (by
      intro i hi
      rw [frameCoreFold_last p i hi]
      have he := frameEndpointVertex_eq_edge p false
      change (frameLastColumn p).owner = octEdgeZigzag p.side exitEdgeFrame 0 at he
      rw [← he]
      exact step_adj (frameLastColumn p).owner (frameLastColumn p).dir)

theorem frame_capWord_eq (p : ConstructionParameters) :
    capWord (p.framePart1 ++ p.framePart2) = p.frameWord := by
  simp only [capWord, ConstructionParameters.frameWord, List.append_assoc]
  rfl

noncomputable def frameFold (p : ConstructionParameters) : Fold tetrahedralLattice p.frameWord.length :=
  transportWordFold (frame_capWord_eq p) (frameCappedFold p)

theorem frameFold_first (p : ConstructionParameters) (i : Fin p.frameWord.length) (hi : i.val = 0) :
    (frameFold p).pos i = (frameFirstColumn p).seed := by
  apply transportWordFold_first
  · exact cappedWordFold_first _ _ _ _ _ _ _ _ _
  · exact hi

theorem frameFold_last (p : ConstructionParameters) (i : Fin p.frameWord.length)
    (hi : i.val + 1 = p.frameWord.length) : (frameFold p).pos i = (frameLastColumn p).seed := by
  apply transportWordFold_last
  · exact cappedWordFold_last _ _ _ _ _ _ _ _ _
  · exact hi

theorem frameFold_hSupport_subset_oct (p : ConstructionParameters) :
    hSupport p.frameWord (frameFold p) ⊆ octahedron p.side := by
  rw [frameFold, transportWordFold_hSupport, frameCappedFold, cappedWordFold_hSupport]
  exact frameCoreFold_hSupport_subset_oct p

theorem frameFold_sites (p : ConstructionParameters) :
    foldSites (frameFold p) =
      ({(frameFirstColumn p).seed} ∪ foldSites (frameCoreFold p)) ∪ {(frameLastColumn p).seed} := by
  rw [frameFold, transportWordFold_sites, frameCappedFold, cappedWordFold_sites]

private theorem column_seed_scalar {m : ℕ} (C : DanglingColumn m) : InSkinSolid m 1 C.seed :=
  (mem_skinSolid m 1 C.seed).mp C.point_zero_mem_solid_one

private theorem rawFold_solid_scalar {m n : ℕ} (f : Fold tetrahedralLattice n)
    (hf : ∀ i, f.pos i ∈ skinSolid m 1) : ∀ i, InSkinSolid m 1 (f.pos i) :=
  fun i => (mem_skinSolid m 1 (f.pos i)).mp (hf i)

theorem frameFold_mem_solid_one (p : ConstructionParameters) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ∈ skinSolid p.side 1 := by
  rw [mem_skinSolid]
  exact frameTrack_property_of_capped_sites (frameFold p) (frameCoreFold p)
    (frameFirstColumn p).seed (frameLastColumn p).seed (frameFold_sites p) (InSkinSolid p.side 1)
    (column_seed_scalar (frameFirstColumn p))
    (rawFold_solid_scalar (m := p.side) (frameCoreFold p) (frameCoreFold_mem_solid_one p))
    (column_seed_scalar (frameLastColumn p)) i

theorem frameEndpointCaps_ne_positive_column (p : ConstructionParameters) (b c : Bool)
    (n : ℕ) (hn : 1 ≤ n) :
    (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).seed ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) c).point n := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  by_cases hbc : b = c
  · subst c
    intro heq
    have h := (frameEndpointColumn hm b).point_injective (show
      (frameEndpointColumn hm b).point 0 = (frameEndpointColumn hm b).point n from heq)
    omega
  · have hseed : (frameEndpointColumn hm b).seed ≠ (frameEndpointColumn hm c).seed := by
      cases b <;> cases c
      · exact False.elim (hbc rfl)
      · exact (frameEndpointColumns_seed_ne (by have h := p.side_ge; omega : 2 ≤ p.side)).symm
      · exact frameEndpointColumns_seed_ne (by have h := p.side_ge; omega : 2 ≤ p.side)
      · exact False.elim (hbc rfl)
    exact DanglingColumn.points_ne_of_seed_ne hseed 0 n

theorem frameFold_ne_endpointColumn (p : ConstructionParameters) (atStart : Bool)
    (n : ℕ) (hn : 1 ≤ n) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n := by
  intro heq
  have h := (mem_foldSites (frameFold p) _).mpr ⟨i, heq⟩
  rw [frameFold_sites] at h
  simp only [Finset.mem_union, Finset.mem_singleton] at h
  rcases h with (h | h) | h
  · exact frameEndpointCaps_ne_positive_column p true atStart n hn h.symm
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    exact frameCoreFold_ne_endpointColumn p atStart n j hj
  · exact frameEndpointCaps_ne_positive_column p false atStart n hn h.symm

noncomputable def frameWordPiece (p : ConstructionParameters) : PositionedWord where
  word := p.frameWord
  fold := frameFold p
  length_pos := by rw [p.frameWord_length]; omega
  first := (frameFirstColumn p).seed
  last := (frameLastColumn p).seed
  first_eq := frameFold_first p
  last_eq := frameFold_last p

end ProteinFolding.Tetrahedral.NearField
