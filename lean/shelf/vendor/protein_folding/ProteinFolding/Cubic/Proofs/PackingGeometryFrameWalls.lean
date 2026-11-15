import ProteinFolding.Cubic.Proofs.PackingGeometryFrameAnchorFamily
import ProteinFolding.Cubic.Proofs.PackingGeometryWordJoins
import ProteinFolding.Cubic.Proofs.PackingFaceOccurrences

/-! The two literal F_d walls in every repeated unit. Their E/F/E joins are
transported back to the complete fold using exact source offsets. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

abbrev FrameWall (q : ℕ) := Fin q × Fin 2

def wallLeftSize {q : ℕ} (Q : ℕ) (w : FrameWall q) : ℕ := if w.2 = 0 then alpha Q else beta Q
def wallRightSize {q : ℕ} (Q : ℕ) (w : FrameWall q) : ℕ := if w.2 = 0 then beta Q else alpha Q

def wallLeftBlock {q : ℕ} (w : FrameWall q) : FrameBlock q := (w.1, if w.2 = 0 then 0 else 1)
def wallRightBlock {q : ℕ} (w : FrameWall q) : FrameBlock q := (w.1, if w.2 = 0 then 1 else 2)

theorem wallLeftSize_eq {q : ℕ} (Q : ℕ) (w : FrameWall q) :
    wallLeftSize Q w = anchorLength Q (frameBlockKind (wallLeftBlock w)) := by
  rcases w with ⟨j, k⟩
  fin_cases k <;> simp [wallLeftSize, wallLeftBlock, frameBlockKind, anchorLength]

theorem wallRightSize_eq {q : ℕ} (Q : ℕ) (w : FrameWall q) :
    wallRightSize Q w = anchorLength Q (frameBlockKind (wallRightBlock w)) := by
  rcases w with ⟨j, k⟩
  fin_cases k <;> simp [wallRightSize, wallRightBlock, frameBlockKind, anchorLength]

def frameWallOffset (q Q : ℕ) (w : FrameWall q) : ℕ :=
  (prefixWord q Q).length + w.1.val * wallStride q Q +
    if w.2 = 0 then 0 else 3 * alpha Q + 2 * depth q Q

structure FrameWallOccurrence (q Q : ℕ) (items : List ℕ) (w : FrameWall q) where
  pre : Sequence
  post : Sequence
  word_eq : frameWord q Q items = wallSegment pre post (wallLeftSize Q w) (depth q Q) (wallRightSize Q w)
  offset_eq : pre.length = frameWallOffset q Q w

theorem frame_wall_occurrence_exists (q Q : ℕ) (items : List ℕ) (w : FrameWall q) :
    Nonempty (FrameWallOccurrence q Q items w) := by
  obtain ⟨u, v, huv, hul⟩ := separatedCopies_occurrence (wallUnit q Q)
    (List.replicate (2 * alpha Q) .P) q w.1.val w.1.isLt
  have hframe : frameWord q Q items = prefixWord q Q ++ u ++ wallUnit q Q ++ v ++
      gapWord q Q ++ itemWords q Q items := by
    change prefixWord q Q ++ walls q Q ++ itemWords q Q items = _
    have hunit : walls q Q = separatedCopies (wallUnit q Q) (List.replicate (2 * alpha Q) .P) q ++ gapWord q Q := rfl
    rw [hunit, huv]
    simp only [List.append_assoc]
  rcases w with ⟨j, k⟩
  fin_cases k
  · refine ⟨⟨prefixWord q Q ++ u,
      faceWord (depth q Q) ++ edgeWord (alpha Q) ++ v ++ gapWord q Q ++ itemWords q Q items,
      ?_, ?_⟩⟩
    · simpa [wallSegment, wallLeftSize, wallRightSize, wallUnit, List.append_assoc] using hframe
    · simp only [List.length_append, hul, List.length_replicate, wallUnit_length]
      simp [frameWallOffset, wallStride]
      ring_nf
      simp
  · refine ⟨⟨prefixWord q Q ++ u ++ edgeWord (alpha Q) ++ faceWord (depth q Q),
      v ++ gapWord q Q ++ itemWords q Q items, ?_, ?_⟩⟩
    · simpa [wallSegment, wallLeftSize, wallRightSize, wallUnit, List.append_assoc] using hframe
    · simp only [List.length_append, hul, List.length_replicate, wallUnit_length,
        edgeWord_length, faceWord_length _ (depth_even q Q)]
      simp [frameWallOffset, wallStride]
      ring_nf

noncomputable def frameWallOccurrence (q Q : ℕ) (items : List ℕ) (w : FrameWall q) :
    FrameWallOccurrence q Q items w := Classical.choice (frame_wall_occurrence_exists q Q items w)

noncomputable def frameWallFace (q Q : ℕ) (items : List ℕ) (w : FrameWall q) :
    FaceOccurrence (frameWord q Q items) (depth q Q) where
  pre := (frameWallOccurrence q Q items w).pre ++ edgeWord (wallLeftSize Q w)
  post := edgeWord (wallRightSize Q w) ++ (frameWallOccurrence q Q items w).post
  word_eq := (frameWallOccurrence q Q items w).word_eq.trans
    (wallSegment_middle _ _ _ _ _)

theorem frameWallFace_offset (q Q : ℕ) (items : List ℕ) (w : FrameWall q) :
    (frameWallFace q Q items w).pre.length = frameWallOffset q Q w + 3 * wallLeftSize Q w := by
  simp only [frameWallFace, List.length_append, edgeWord_length]
  rw [(frameWallOccurrence q Q items w).offset_eq]

noncomputable def frameWallPath (q Q : ℕ) (items : List ℕ) (w : FrameWall q)
    (f : Fold cubicLattice (frameWord q Q items).length) (i : Fin (depth q Q)) : Site :=
  (frameWallFace q Q items w).path f (Fin.cast (Nat.mul_div_cancel' (depth_even q Q)).symm i)

theorem frameWallPath_eq (q Q : ℕ) (items : List ℕ) (w : FrameWall q)
    (f : Fold cubicLattice (frameWord q Q items).length) :
    frameWallPath q Q items w f =
      wallMiddlePath (frameWallOccurrence q Q items w).pre (frameWallOccurrence q Q items w).post
        (wallLeftSize Q w) (depth q Q) (wallRightSize Q w) (depth_even q Q)
        (foldOnWord (frameWallOccurrence q Q items w).word_eq f) := by
  funext i
  unfold frameWallPath wallMiddlePath faceWallPath faceHPath FaceOccurrence.path
  rw [foldOnWord_pos, foldOnWord_pos]
  congr 1

theorem frameWall_left_anchor_eq (q Q : ℕ) (items : List ℕ) (w : FrameWall q)
    (hQ : 0 < Q) (f : Fold cubicLattice (frameWord q Q items).length) :
    wallLeftAnchor (frameWallOccurrence q Q items w).pre (frameWallOccurrence q Q items w).post
      (wallLeftSize Q w) (depth q Q) (wallRightSize Q w)
      (by rw [wallLeftSize_eq]; exact frameBlock_length_pos q Q hQ _)
      (foldOnWord (frameWallOccurrence q Q items w).word_eq f) =
      (frameBlockOccurrence q Q items (wallLeftBlock w)).path f
        ⟨wallLeftSize Q w - 1, by rw [← wallLeftSize_eq]; have := frameBlock_length_pos q Q hQ (wallLeftBlock w); rw [← wallLeftSize_eq] at this; omega⟩ := by
  unfold wallLeftAnchor edgeHPath EdgeOccurrence.path
  rw [foldOnWord_pos, foldOnWord_pos]
  congr 1
  apply Fin.ext
  change (frameWallOccurrence q Q items w).pre.length + 3 * (wallLeftSize Q w - 1) + 1 =
    (frameBlockOccurrence q Q items (wallLeftBlock w)).pre.length + 3 * (wallLeftSize Q w - 1) + 1
  rw [(frameWallOccurrence q Q items w).offset_eq, frameBlockOccurrence_offset]
  rcases w with ⟨j, k⟩
  fin_cases k <;> simp [frameWallOffset, frameBlockOffset, wallLeftBlock, wallInnerOffset, Nat.add_assoc]

theorem frameWall_right_anchor_eq (q Q : ℕ) (items : List ℕ) (w : FrameWall q)
    (hQ : 0 < Q) (f : Fold cubicLattice (frameWord q Q items).length) :
    wallRightAnchor (frameWallOccurrence q Q items w).pre (frameWallOccurrence q Q items w).post
      (wallLeftSize Q w) (depth q Q) (wallRightSize Q w)
      (by rw [wallRightSize_eq]; exact frameBlock_length_pos q Q hQ _)
      (foldOnWord (frameWallOccurrence q Q items w).word_eq f) =
      (frameBlockOccurrence q Q items (wallRightBlock w)).path f
        ⟨0, frameBlock_length_pos q Q hQ _⟩ := by
  unfold wallRightAnchor edgeHPath EdgeOccurrence.path
  rw [foldOnWord_pos, foldOnWord_pos]
  congr 1
  apply Fin.ext
  change ((frameWallOccurrence q Q items w).pre ++ edgeWord (wallLeftSize Q w) ++
    faceWord (depth q Q)).length + 3 * 0 + 1 =
      (frameBlockOccurrence q Q items (wallRightBlock w)).pre.length + 3 * 0 + 1
  simp only [List.length_append, edgeWord_length, faceWord_length _ (depth_even q Q), Nat.mul_zero, Nat.add_zero]
  rw [(frameWallOccurrence q Q items w).offset_eq, frameBlockOccurrence_offset]
  rcases w with ⟨j, k⟩
  fin_cases k
  all_goals simp [frameWallOffset, frameBlockOffset, wallRightBlock, wallInnerOffset,
    wallLeftSize, Nat.add_assoc]
  all_goals omega

theorem FrameAnchorFamily.wall_rails_distinct {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hQ : 0 < Q) (hq : q < Q) (w : FrameWall q) :
    F.rail (wallLeftBlock w) ≠ F.rail (wallRightBlock w) := by
  have hleft := F.long_rail hQ hq (wallLeftBlock w)
  have hright := F.long_rail hQ hq (wallRightBlock w)
  rcases w with ⟨j, k⟩
  fin_cases k
  · simp [wallLeftBlock, wallRightBlock, frameBlockKind] at hleft hright
    change F.rail (j, 0) ≠ F.rail (j, 1)
    simpa only [hright] using hleft
  · simp [wallLeftBlock, wallRightBlock, frameBlockKind] at hleft hright
    change F.rail (j, 1) ≠ F.rail (j, 2)
    intro he
    have he' : (1 : Fin 2) = F.rail (j, 2) := by simpa only [hleft] using he
    exact hright he'.symm

theorem FrameAnchorFamily.wall_no_common_corner {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hQ : 0 < Q) (hq : q < Q) (w : FrameWall q) :
    NoCommonCorner (F.railEdge (F.rail (wallLeftBlock w))) (F.railEdge (F.rail (wallRightBlock w))) := by
  apply noCommonCorner_of_matching (Finset.univ.image F.railEdge) F.matching _ _
    (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
    (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
  intro he
  exact F.wall_rails_distinct hQ hq w (F.railEdge_injective he)

/-- Both literal F_d walls in every actual frame unit are straight crossings
between the two forced rails. Their P/H seams are discharged by the word. -/
theorem FrameAnchorFamily.wall_straight {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hq0 : 0 < q) (hQ : 0 < Q) (hq : q < Q)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) (w : FrameWall q) :
    ∃ (r : Fin (depth q Q)) (axis : Fin 3),
      axis ≠ (F.railEdge (F.rail (wallLeftBlock w))).axis ∧
      axis ≠ (F.railEdge (F.rail (wallRightBlock w))).axis ∧
      ((∀ i, frameWallPath q Q items w f i =
        Function.update (openEdgePoint a (depth q Q) (F.railEdge (F.rail (wallLeftBlock w))) r) axis
          (openEdgePoint a (depth q Q) (F.railEdge (F.rail (wallLeftBlock w))) r axis + ((i.val + 1 : ℕ) : ℤ))) ∨
       (∀ i, frameWallPath q Q items w f i =
        Function.update (openEdgePoint a (depth q Q) (F.railEdge (F.rail (wallLeftBlock w))) r) axis
          (openEdgePoint a (depth q Q) (F.railEdge (F.rail (wallLeftBlock w))) r axis - ((i.val + 1 : ℕ) : ℤ)))) := by
  have hs : 0 < wallLeftSize Q w := by rw [wallLeftSize_eq]; exact frameBlock_length_pos q Q hQ _
  have ht : 0 < wallRightSize Q w := by rw [wallRightSize_eq]; exact frameBlock_length_pos q Q hQ _
  have hd : 0 < depth q Q := by have := depth_two_le q Q hq0; omega
  have hl := F.on_edge (wallLeftBlock w) ⟨wallLeftSize Q w - 1, by rw [← wallLeftSize_eq]; omega⟩
  have hr := F.on_edge (wallRightBlock w) ⟨0, frameBlock_length_pos q Q hQ _⟩
  obtain ⟨r, _, hleft⟩ := Finset.mem_image.mp hl
  obtain ⟨u, _, hright⟩ := Finset.mem_image.mp hr
  have hpack' : hydrophobicSites
      (wallSegment (frameWallOccurrence q Q items w).pre (frameWallOccurrence q Q items w).post
        (wallLeftSize Q w) (depth q Q) (wallRightSize Q w))
      (foldOnWord (frameWallOccurrence q Q items w).word_eq f) = cube a (depth q Q + 2) := by
    rw [foldOnWord_hydrophobicSites]
    exact hpack
  obtain ⟨axis, haxisL, haxisR, hstraight⟩ := wallSegment_straight
    (frameWallOccurrence q Q items w).pre (frameWallOccurrence q Q items w).post
    (wallLeftSize Q w) (depth q Q) (wallRightSize Q w) hs hd ht (depth_even q Q)
    (foldOnWord (frameWallOccurrence q Q items w).word_eq f) a hpack'
    (F.railEdge (F.rail (wallLeftBlock w))) (F.railEdge (F.rail (wallRightBlock w))) r u
    (F.wall_no_common_corner hQ hq w)
    (by rw [frameWall_left_anchor_eq q Q items w hQ f]; exact hleft.symm)
    (by rw [frameWall_right_anchor_eq q Q items w hQ f]; exact hright.symm)
  exact ⟨r, axis, haxisL, haxisR, by simpa only [frameWallPath_eq] using hstraight⟩

end ProteinFolding.CubicPackingGeometry
