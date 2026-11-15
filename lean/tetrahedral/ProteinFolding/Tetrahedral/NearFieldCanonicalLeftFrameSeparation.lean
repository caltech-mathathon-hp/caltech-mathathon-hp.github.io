import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import ProteinFolding.Tetrahedral.NearFieldLeftFillerFrameClearance
import ProteinFolding.Tetrahedral.NearFieldFrameLeftHSupport
import ProteinFolding.Tetrahedral.NearFieldDimerResidues
import ProteinFolding.Tetrahedral.NearFieldFrameTrackCoreSeparation
import ProteinFolding.Tetrahedral.NearFieldActualFrameFold
import ProteinFolding.Tetrahedral.NearFieldCanonicalTrackPieces

/-! Both actual left caps and the corner-starting body avoid the full frame. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

private theorem mem_ne_not_mem {α : Type*} [DecidableEq α] {A : Finset α}
    {x y : α} (hx : x ∈ A) (hy : y ∉ A) : x ≠ y := by
  intro heq
  exact hy (heq ▸ hx)

private theorem column_seeds_ne_of_owner_ne {m : ℕ} (C D : DanglingColumn m)
    (howner : C.owner ≠ D.owner) : C.seed ≠ D.seed :=
  dangling_caps_ne_of_owner_ne m C.owner D.owner C.dir D.dir
    C.owner_mem D.owner_mem C.seed_outside howner

private theorem column_seed_outside {m : ℕ} (C : DanglingColumn m) :
    C.seed ∉ octahedron m := C.seed_outside

private theorem edgePPP_ne_column_seed {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (r : ℕ) (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m)
    (hstart : C.owner ≠ octEdgeZigzag m F r)
    (hend : C.owner ≠ octEdgeZigzag m F (r + 2)) (s : Fin 3) :
    (edgePPPFold m F r).pos s ≠ C.seed := by
  have hmem : faceFourStep (octEdgeZigzag m F r) (edgePPPNormal F (octEdgeZigzag m F r))
      (edgePPPBack F (octEdgeZigzag m F r)) (edgePPPForward F (octEdgeZigzag m F r)) ∈ octahedron m := by
    rw [edgePPP_endpoint]
    rcases octEdgeZigzag_mem hm F hr with h | h
    · exact h.1.1
    · exact h.1.1
  exact facePPPFold_ne_cap_of_owner_ne m _ _ _ _ (edgePPPLateral_ne F _)
    (edgePPP_back_ne_normal F _) (edgePPP_normal_face hm F r (by omega)) hmem C
    hstart (by simpa only [edgePPP_endpoint] using hend) s

private theorem fold_ne_inside_of_Hdis {m : ℕ} {S T : Sequence}
    (f : Fold tetrahedralLattice S.length) (g : Fold tetrahedralLattice T.length)
    (hP : ∀ i, S.get i = .P → f.pos i ∉ octahedron m)
    (hg : ∀ j, g.pos j ∈ octahedron m)
    (hdis : Disjoint (foldSites g) (hSupport S f)) (i : Fin S.length) (j : Fin T.length) :
    f.pos i ≠ g.pos j := by
  intro heq
  have hin : f.pos i ∈ octahedron m := heq.symm ▸ hg j
  have hH := site_mem_hSupport_of_mem_oct (S := S) f m hP (f.pos i)
    ((mem_foldSites f _).mpr ⟨i, rfl⟩) hin
  exact Finset.disjoint_left.mp hdis ((mem_foldSites g _).mpr ⟨j, heq.symm⟩) hH

private theorem column_seed_ne_inside_fold {m : ℕ} {S : Sequence}
    (C : DanglingColumn m) (g : Fold tetrahedralLattice S.length)
    (hg : ∀ j, g.pos j ∈ octahedron m) (j : Fin S.length) : C.seed ≠ g.pos j :=
  (fold_ne_column_of_inside (S := S) g C hg j 0).symm

private theorem capped_sites_ne_inside_of_Hdis {m a : ℕ} {S T : Sequence}
    (f : Fold tetrahedralLattice a) (body : Fold tetrahedralLattice S.length)
    (g : Fold tetrahedralLattice T.length) (C D : DanglingColumn m)
    (hsites : foldSites f = ({C.seed} ∪ foldSites body) ∪ {D.seed})
    (hP : ∀ i, S.get i = .P → body.pos i ∉ octahedron m)
    (hg : ∀ j, g.pos j ∈ octahedron m)
    (hdis : Disjoint (foldSites g) (hSupport S body)) (i : Fin a) (j : Fin T.length) :
    f.pos i ≠ g.pos j :=
  frameTrack_property_of_capped_sites f body C.seed D.seed hsites (fun x => x ≠ g.pos j)
    (column_seed_ne_inside_fold C g hg j)
    (fun r => fold_ne_inside_of_Hdis body g hP hg hdis r j)
    (column_seed_ne_inside_fold D g hg j) i

theorem leftFillerFold_ne_cap_of_owner_not_mem (p : ConstructionParameters) (C : DanglingColumn p.side)
    (hnot : C.owner ∉ leftFillerHsites p) (i : Fin (dimerChain p.leftFiller).length) :
    (leftFillerFold p).pos i ≠ C.seed := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hi : i.val < 5 * (p.leftFiller - 1) + 2 := by rw [← leftFiller_word_length p]; exact i.isLt
  by_cases hi0 : i.val = 0
  · rw [leftFillerFold_first p i hi0]
    with_reducible
      exact mem_ne_not_mem (leftFillerStart_mem_oct p) (column_seed_outside C)
  · rw [leftFillerFold_pos, leftFillerCurve, if_neg hi0]
    by_cases hH : i.val % 5 < 2
    · with_reducible
        exact mem_ne_not_mem
          (edgeDimerCurve_H_mem hm trackEdgeFrame 0 (p.leftFiller - 1) false
            (leftFiller_room p) i.val hi hH) (column_seed_outside C)
    · simp only [edgeDimerCurve, dif_neg hH]
      have hj := dimerCurve_Pblock_lt (p.leftFiller - 1) i.val hi hH
      have hr := dimerCurve_Prange p.side 0 (p.leftFiller - 1) false (leftFiller_room p) i.val hi hH
      have hs := leftFillerLink_endpoint_mem p (i.val / 5) hj 0
      have he := leftFillerLink_endpoint_mem p (i.val / 5) hj 1
      simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at hs
      simp only [Fin.val_one, Nat.mul_one] at he
      with_reducible
        exact edgePPP_ne_column_seed hm trackEdgeFrame _ hr C
          (mem_ne_not_mem hs hnot).symm (mem_ne_not_mem he hnot).symm _

theorem cappedLeftFillerFold_ne_cap_of_owner_not_mem (p : ConstructionParameters)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2))
    (E : DanglingColumn p.side) (hnot : E.owner ∉ leftFillerHsites p)
    (i : Fin (capWord (dimerChain p.leftFiller)).length) :
    (cappedLeftFillerFold p C D hC hD).pos i ≠ E.seed := by
  have hcap (X : DanglingColumn p.side) (hX : X.owner ∈ leftFillerHsites p) : X.seed ≠ E.seed := by
    with_reducible
      exact column_seeds_ne_of_owner_ne X E (mem_ne_not_mem hX hnot)
  exact frameTrack_property_of_capped_sites (cappedLeftFillerFold p C D hC hD) (leftFillerFold p)
    C.seed D.seed (cappedLeftFillerFold_sites p C D hC hD) (fun x => x ≠ E.seed)
    (hcap C (by rw [hC]; exact Finset.mem_insert_self _ _))
    (leftFillerFold_ne_cap_of_owner_not_mem p E hnot)
    (hcap D (by rw [hD]; exact leftFillerLast_mem_Hsites p)) i

theorem frameEndpointColumn_not_leftFillerHsites (p : ConstructionParameters) (b : Bool) :
    (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).owner ∉ leftFillerHsites p := by
  change frameEndpointVertex p.side b ∉ leftFillerHsites p
  rw [frameEndpointVertex_eq_edge p b]
  cases b
  · change octEdgeZigzag p.side exitEdgeFrame 0 ∉ _
    exact exitPoint_not_leftFillerHsites p 0 (by have h := p.side_ge; omega)
  · change octEdgeZigzag p.side entryEdgeFrame 0 ∉ _
    exact entryPoint_not_leftFillerHsites p 0 (by have h := p.side_ge; omega) (by decide) (by decide)

theorem cappedLeftFillerFold_ne_frameHRun (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2))
    (i : Fin (capWord (dimerChain p.leftFiller)).length) (j : FrameHRunIndex p)
    (s : Fin (frameHRunWord p j).length) :
    (cappedLeftFillerFold p C D hC hD).pos i ≠ (frameHRunFold p j).pos s := by
  with_reducible
    exact capped_sites_ne_inside_of_Hdis (m := p.side) (S := dimerChain p.leftFiller)
      (T := frameHRunWord p j) (cappedLeftFillerFold p C D hC hD) (leftFillerFold p)
      (frameHRunFold p j) C D (cappedLeftFillerFold_sites p C D hC hD)
      (leftFillerFold_P_outside p) (frameHRunFold_mem_oct p j)
      (frameHRunFold_disjoint_left_hSupport p j) i s

theorem canonicalLeftPiece_ne_frameFold (p : ConstructionParameters)
    (i : Fin (canonicalLeftPiece p).word.length) (t : Fin p.frameWord.length) :
    (canonicalLeftPiece p).fold.pos i ≠ (frameFold p).pos t := by
  let C := entryLocalColumn p none
  let D := leftLastColumn p
  have hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2 := rfl
  have hD := leftLastColumn_owner p
  have hcaps (b : Bool) : (canonicalLeftPiece p).fold.pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).seed :=
    cappedLeftFillerFold_ne_cap_of_owner_not_mem p C D hC hD _
      (frameEndpointColumn_not_leftFillerHsites p b) i
  have hcore : ∀ r, (canonicalLeftPiece p).fold.pos i ≠ (frameCoreFold p).pos r := by
    intro r
    apply frameCoreFold_property p (fun x => (canonicalLeftPiece p).fold.pos i ≠ x) _ r
    intro j s
    rcases j with j | j
    · dsimp only [frameCorePiece, frameHRunPiece] at s ⊢
      exact cappedLeftFillerFold_ne_frameHRun p C D hC hD i j s
    · dsimp only [frameCorePiece, frameLinkPiece] at s ⊢
      rw [frameLinkWordFold_pos]
      exact cappedLeftFillerFold_ne_framePFold p C D hC hD (frameLinkParameter j) (frameLinkKind j)
        (frameLinkParameter_odd p j) (frameLinkParameter_ge p j) (frameLinkParameter_room p j) i _
  exact frameTrack_property_of_capped_sites (frameFold p) (frameCoreFold p)
    (frameFirstColumn p).seed (frameLastColumn p).seed (frameFold_sites p)
    (fun x => (canonicalLeftPiece p).fold.pos i ≠ x) (hcaps true) hcore (hcaps false) t

theorem canonicalLeftPiece_frameWordPiece_disjoint (p : ConstructionParameters) :
    WordsDisjoint (canonicalLeftPiece p) (frameWordPiece p) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalLeftPiece_ne_frameFold p)

end ProteinFolding.Tetrahedral.NearField
