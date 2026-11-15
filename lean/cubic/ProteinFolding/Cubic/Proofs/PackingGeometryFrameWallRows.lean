import ProteinFolding.Cubic.Proofs.PackingGeometryFrameWalls
import ProteinFolding.Cubic.Proofs.PackingFrameFaceConfinement

/-! Full wall rows on the unique packing face. The source indices, face
assignment and parallel rails are consequences of the actual perfect fold. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

theorem frameWallFace_after_prefix (q Q : ℕ) (items : List ℕ) (w : FrameWall q) :
    (prefixWord q Q).length ≤ (frameWallFace q Q items w).pre.length := by
  rw [frameWallFace_offset]
  unfold frameWallOffset
  omega

theorem frame_walls_one_face (q Q : ℕ) (items : List ℕ) (hq : 2 ≤ q)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    ∃ face : CubeFace, ∀ (w : FrameWall q) (i : Fin (depth q Q)),
      FaceInterior a (side q Q) face.1 face.2 (frameWallPath q Q items w f i) := by
  have hd := depth_two_le q Q (by omega : 0 < q)
  have hβ : 2 ≤ beta Q := by dsimp [beta]; omega
  have hd4 : 4 ≤ depth q Q := by
    have hm := Nat.mul_le_mul_right (beta Q) hq
    dsimp [depth]
    omega
  obtain ⟨face, hface⟩ := frame_remaining_face_confines q Q items (by omega)
    (by nlinarith) f a hpack
  refine ⟨face, ?_⟩
  intro w i
  apply hface (depth q Q) (frameWallFace q Q items w) (frameWallFace_after_prefix q Q items w)
    (by have he := Nat.mul_div_cancel' (depth_even q Q); omega)
  exact Finset.mem_image.mpr ⟨Fin.cast (Nat.mul_div_cancel' (depth_even q Q)).symm i,
    Finset.mem_univ _, rfl⟩

theorem FrameAnchorFamily.wall_rails_parallel {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hq0 : 0 < q) (hQ : 0 < Q) (hq : q < Q)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) (w : FrameWall q) :
    (F.railEdge (F.rail (wallLeftBlock w))).axis = (F.railEdge (F.rail (wallRightBlock w))).axis := by
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
  apply wallSegment_rails_parallel
    (frameWallOccurrence q Q items w).pre (frameWallOccurrence q Q items w).post
    (wallLeftSize Q w) (depth q Q) (wallRightSize Q w) hs hd ht (depth_even q Q)
    (foldOnWord (frameWallOccurrence q Q items w).word_eq f) a hpack' _ _ r u
    (F.wall_no_common_corner hQ hq w)
    (by rw [frameWall_left_anchor_eq q Q items w hQ f]; exact hleft.symm)
    (by rw [frameWall_right_anchor_eq q Q items w hQ f]; exact hright.symm)
  intro i
  rw [← frameWallPath_eq]
  exact frameFaceOccurrence_noedge q Q items hq0 f a hpack (frameWallFace q Q items w) _

theorem FrameAnchorFamily.rails_parallel {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hq0 : 0 < q) (hQ : 0 < Q) (hq : q < Q)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    (F.railEdge 0).axis = (F.railEdge 1).axis := by
  let j : Fin q := ⟨0, hq0⟩
  have hleft : F.rail (j, 0) = 0 := by
    have h := F.long_rail hQ hq (j, 0)
    simp [frameBlockKind] at h
    apply Fin.ext
    have := (F.rail (j, 0)).isLt
    have hval : (F.rail (j, 0)).val ≠ 1 := by intro he; exact h (Fin.ext he)
    omega
  have hright : F.rail (j, 1) = 1 := (F.long_rail hQ hq (j, 1)).mpr (by simp [frameBlockKind])
  simpa only [wallLeftBlock, wallRightBlock, ↓reduceIte, hleft, hright] using
    F.wall_rails_parallel hq0 hQ hq hpack (j, 0)

noncomputable def faceRowFinset (a : Site) (d : ℕ) (face : CubeFace) (axis : Fin 3) (level : ℕ) : Finset Site :=
  (faceInteriorFinset a d face).filter fun p => railCoordinate a axis p = level

theorem third_axis_exists : ∀ x y : Fin 3, x ≠ y → ∃ z : Fin 3, z ≠ x ∧ z ≠ y := by decide

theorem faceRowFinset_card_le (a : Site) (d : ℕ) (face : CubeFace) (axis : Fin 3)
    (haxis : axis ≠ face.1) (level : ℕ) : (faceRowFinset a d face axis level).card ≤ d := by
  obtain ⟨x, hxa, hxn⟩ := third_axis_exists axis face.1 haxis
  have h := faceStrip_occupancy_bound a d face.1 face.2 x axis hxa hxn haxis
    (a axis + (level : ℤ) - 1) (a axis + (level : ℤ) + 1)
    (faceRowFinset a d face axis level) id (fun _ _ he => he)
    (fun p hp => (mem_faceInteriorFinset a d face p).mp (Finset.mem_filter.mp hp).1)
    (by
      intro p hp
      have hf := (mem_faceInteriorFinset a d face p).mp (Finset.mem_filter.mp hp).1
      have he := (Finset.mem_filter.mp hp).2
      have hs := hf.2.2 axis haxis
      dsimp [railCoordinate] at he
      change a axis + (level : ℤ) - 1 < p axis ∧ p axis < a axis + (level : ℤ) + 1
      omega)
  have he : (a axis + (level : ℤ) + 1 - (a axis + (level : ℤ) - 1) - 1).toNat = 1 := by omega
  simpa only [he, Nat.mul_one] using h

/-- Any d distinct wall H sites in one face at one rail coordinate fill the
entire corresponding row. This is a capacity argument, with no orientation
choice or assumption that a row is already occupied. -/
theorem face_row_filled (a : Site) (d : ℕ) (face : CubeFace) (axis : Fin 3)
    (haxis : axis ≠ face.1) (level : ℕ) (sites : Finset Site) (hcard : sites.card = d)
    (hface : ∀ p ∈ sites, FaceInterior a (d + 2) face.1 face.2 p)
    (hcoord : ∀ p ∈ sites, railCoordinate a axis p = level) :
    sites = faceRowFinset a d face axis level := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    exact Finset.mem_filter.mpr ⟨(mem_faceInteriorFinset a d face p).mpr (hface p hp), hcoord p hp⟩
  · rw [hcard]
    exact faceRowFinset_card_le a d face axis haxis level

theorem wallSegment_axis_constant (pre post : Sequence) (s d t : ℕ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 < t) (heven : 2 ∣ d)
    (f : Fold cubicLattice (wallSegment pre post s d t).length) (a : Site)
    (hpack : hydrophobicSites (wallSegment pre post s d t) f = cube a (d + 2))
    (e g : CubeEdge) (r u : Fin d) (hnc : NoCommonCorner e g)
    (hleft : wallLeftAnchor pre post s d t hs f = openEdgePoint a d e r)
    (hright : wallRightAnchor pre post s d t ht f = openEdgePoint a d g u) :
    (∀ i, wallMiddlePath pre post s d t heven f i e.axis = openEdgePoint a d e r e.axis) ∧
      openEdgePoint a d g u e.axis = openEdgePoint a d e r e.axis := by
  let middle := wallMiddlePath pre post s d t heven f
  let p := anchoredPath (openEdgePoint a d e r) (openEdgePoint a d g u) middle
  have hfirst := wallLeftJoin_adjacent pre post s d t hs hd heven f a (d + 2) hpack
  have hlast := wallRightJoin_adjacent pre post s d t ht hd heven f a (d + 2) hpack
  rw [hleft] at hfirst
  rw [hright] at hlast
  have hpack' : hydrophobicSites (wallMiddlePre pre s ++ faceWord d ++ wallMiddlePost post t)
      (foldOnWord (wallSegment_middle pre post s d t) f) = cube a (d + 2) := by
    rw [foldOnWord_hydrophobicSites]
    exact hpack
  have hstep := faceWallPath_adjacent (wallMiddlePre pre s) (wallMiddlePost post t) d heven
    (foldOnWord (wallSegment_middle pre post s d t) f) a (d + 2) hpack'
  have hsteps := anchoredPath_steps hd (openEdgePoint a d e r) (openEdgePoint a d g u) middle
    hfirst hlast hstep
  obtain ⟨axis, haxis, _, hstraight⟩ := nonincident_crossing_straight a d e g r u hnc p
    (anchoredPath_start _ _ middle) (anchoredPath_end _ _ middle) hsteps
  have hconstant : ∀ j, j ≤ d + 1 → p j e.axis = openEdgePoint a d e r e.axis := by
    intro j hj
    rcases hstraight with hp | hp
    all_goals
      have h := congrFun (hp j hj) e.axis
      simpa only [Function.update_of_ne haxis.symm, p, anchoredPath_start] using h
  constructor
  · intro i
    have h := hconstant (i.val + 1) (by have := i.isLt; omega)
    simpa only [p, anchoredPath_middle, middle] using h
  · simpa only [p, anchoredPath_end] using hconstant (d + 1) le_rfl

theorem FrameAnchorFamily.rail_axis_eq {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hq0 : 0 < q) (hQ : 0 < Q) (hq : q < Q)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) (r : Fin 2) :
    (F.railEdge r).axis = (F.railEdge 1).axis := by
  fin_cases r
  · exact F.rails_parallel hq0 hQ hq hpack
  · rfl

def frameWallLongIndex {q : ℕ} (Q : ℕ) (hQ : 0 < Q) (w : FrameWall q) :
    Fin (anchorLength Q (frameBlockKind (w.1, 1))) :=
  ⟨if w.2 = 0 then 0 else beta Q - 1, by
    simp only [frameBlockKind, ↓reduceIte, anchorLength]
    dsimp [beta]
    split_ifs <;> omega⟩

noncomputable def frameWallLongEndpoint (q Q : ℕ) (items : List ℕ) (hQ : 0 < Q)
    (w : FrameWall q) (f : Fold cubicLattice (frameWord q Q items).length) : Site :=
  (frameBlockOccurrence q Q items (w.1, 1)).path f (frameWallLongIndex Q hQ w)

theorem FrameAnchorFamily.wall_coordinate_eq_long_endpoint {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hq0 : 0 < q) (hQ : 0 < Q) (hq : q < Q)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) (w : FrameWall q) :
    ∀ i, frameWallPath q Q items w f i (F.railEdge 1).axis =
      frameWallLongEndpoint q Q items hQ w f (F.railEdge 1).axis := by
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
  obtain ⟨hpath, hend⟩ := wallSegment_axis_constant
    (frameWallOccurrence q Q items w).pre (frameWallOccurrence q Q items w).post
    (wallLeftSize Q w) (depth q Q) (wallRightSize Q w) hs hd ht (depth_even q Q)
    (foldOnWord (frameWallOccurrence q Q items w).word_eq f) a hpack'
    (F.railEdge (F.rail (wallLeftBlock w))) (F.railEdge (F.rail (wallRightBlock w))) r u
    (F.wall_no_common_corner hQ hq w)
    (by rw [frameWall_left_anchor_eq q Q items w hQ f]; exact hleft.symm)
    (by rw [frameWall_right_anchor_eq q Q items w hQ f]; exact hright.symm)
  have haxis := F.rail_axis_eq hq0 hQ hq hpack (F.rail (wallLeftBlock w))
  rw [haxis] at hend
  have hlong : frameWallLongEndpoint q Q items hQ w f (F.railEdge 1).axis =
      openEdgePoint a (depth q Q) (F.railEdge (F.rail (wallLeftBlock w))) r (F.railEdge 1).axis := by
    rcases w with ⟨j, k⟩
    fin_cases k
    · have hr' := congrFun hright (F.railEdge 1).axis
      simpa only [frameWallLongEndpoint, frameWallLongIndex, wallRightBlock, ↓reduceIte] using hr'.symm.trans hend
    · have hl' := congrFun hleft (F.railEdge 1).axis
      simpa only [frameWallLongEndpoint, frameWallLongIndex, wallLeftBlock, wallLeftSize, ↓reduceIte] using hl'.symm
  intro i
  rw [hlong]
  have hi := hpath i
  rw [haxis] at hi
  simpa only [← frameWallPath_eq] using hi

theorem frameWallFace_sites_eq_path (q Q : ℕ) (items : List ℕ) (w : FrameWall q)
    (f : Fold cubicLattice (frameWord q Q items).length) :
    (frameWallFace q Q items w).sites f = Finset.univ.image (frameWallPath q Q items w f) := by
  ext p
  simp only [FaceOccurrence.sites, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.cast (Nat.mul_div_cancel' (depth_even q Q)) i, ?_⟩
    rfl
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast (Nat.mul_div_cancel' (depth_even q Q)).symm i, rfl⟩

theorem FrameAnchorFamily.wall_axis_ne_face {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hq0 : 0 < q) (hQ : 0 < Q) (hq : q < Q)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q))
    (face : CubeFace) (hface : ∀ (w : FrameWall q) i,
      FaceInterior a (side q Q) face.1 face.2 (frameWallPath q Q items w f i)) :
    (F.railEdge 1).axis ≠ face.1 := by
  have hd : 0 < depth q Q := by have := depth_two_le q Q hq0; omega
  let j : Fin q := ⟨0, hq0⟩
  let w : FrameWall q := (j, 0)
  let i : Fin (depth q Q) := ⟨0, hd⟩
  have hr : F.rail (j, 1) = 1 := (F.long_rail hQ hq (j, 1)).mpr (by simp [frameBlockKind])
  have hp : frameWallLongEndpoint q Q items hQ w f ∈ openEdgeFinset a (depth q Q) (F.railEdge 1) := by
    simpa only [frameWallLongEndpoint, w, hr] using F.on_edge (j, 1) (frameWallLongIndex Q hQ w)
  obtain ⟨r, _, he⟩ := Finset.mem_image.mp hp
  have hc := F.wall_coordinate_eq_long_endpoint hq0 hQ hq hpack w i
  have hs := openEdgePoint_axis_strict a (depth q Q) (F.railEdge 1) r
  rw [he] at hs
  intro ha
  have hb := faceInterior_boundary (hface w i)
  rw [← ha] at hb
  apply boundary_not_strict hb
  rw [hc]
  exact hs

theorem FrameAnchorFamily.wall_full_row {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hq0 : 0 < q) (hQ : 0 < Q) (hq : q < Q)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q))
    (face : CubeFace) (hface : ∀ (w : FrameWall q) i,
      FaceInterior a (side q Q) face.1 face.2 (frameWallPath q Q items w f i)) (w : FrameWall q) :
    (frameWallFace q Q items w).sites f =
      faceRowFinset a (depth q Q) face (F.railEdge 1).axis
        (railCoordinate a (F.railEdge 1).axis (frameWallLongEndpoint q Q items hQ w f)) := by
  apply face_row_filled a (depth q Q) face (F.railEdge 1).axis
    (F.wall_axis_ne_face hq0 hQ hq hpack face hface)
  · rw [FaceOccurrence.sites_card]
    exact Nat.mul_div_cancel' (depth_even q Q)
  · intro p hp
    rw [frameWallFace_sites_eq_path] at hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hface w i
  · intro p hp
    rw [frameWallFace_sites_eq_path] at hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    unfold railCoordinate
    rw [F.wall_coordinate_eq_long_endpoint hq0 hQ hq hpack w i]

/-- Every wall block fills one complete row on the common packing face,
located at the first or last site of its adjacent long anchor. -/
theorem frame_walls_full_rows (q Q : ℕ) (items : List ℕ) (hq : 2 ≤ q) (hQ : q < Q)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    ∃ (F : FrameAnchorFamily q Q items f a) (face : CubeFace),
      (F.railEdge 1).axis ≠ face.1 ∧
      ∀ w : FrameWall q, (frameWallFace q Q items w).sites f =
        faceRowFinset a (depth q Q) face (F.railEdge 1).axis
          (railCoordinate a (F.railEdge 1).axis (frameWallLongEndpoint q Q items (by omega) w f)) := by
  obtain ⟨F⟩ := frame_anchor_family_exists q Q items hq hQ f a hpack
  obtain ⟨face, hface⟩ := frame_walls_one_face q Q items hq f a hpack
  refine ⟨F, face, F.wall_axis_ne_face (by omega) (by omega) hQ hpack face hface, ?_⟩
  exact F.wall_full_row (by omega) (by omega) hQ hpack face hface

end ProteinFolding.CubicPackingGeometry
