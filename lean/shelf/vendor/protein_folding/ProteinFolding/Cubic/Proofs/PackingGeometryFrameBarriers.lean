import ProteinFolding.Cubic.Proofs.PackingGeometryFrameWallRows

/-! Canonical barrier rows forced by the literal long anchors. A long E_β
block may run in either direction; its two adjacent walls occupy its two
endpoint rows, so their unordered set of levels is fixed. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

theorem edge_coordinate_adjacent {a : Site} {d : ℕ} {e : CubeEdge} {p r : Site}
    (hp : p ∈ openEdgeFinset a d e) (hr : r ∈ openEdgeFinset a d e)
    (hadj : cubicLattice.Adj p r) :
    ((railCoordinate a e.axis r : ℤ) - (railCoordinate a e.axis p : ℤ)).natAbs = 1 := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr
  have h : latticeDistance r p = 1 := hadj.symm
  rw [← hi, ← hj, openEdgePoint_distance] at h
  rw [← hi, ← hj, railCoordinate_openEdgePoint, railCoordinate_openEdgePoint]
  omega

theorem nat_interval_path_endpoints {t : ℕ} (ht : 0 < t) (x : Fin t → ℕ)
    (hinj : Function.Injective x)
    (hstep : ∀ i j : Fin t, i.val + 1 = j.val → ((x j : ℤ) - (x i : ℤ)).natAbs = 1)
    (start : ℕ) (himage : Finset.univ.image x = Finset.Ico start (start + t)) :
    (x ⟨0, ht⟩ = start ∧ x ⟨t - 1, by omega⟩ + 1 = start + t) ∨
      (x ⟨t - 1, by omega⟩ = start ∧ x ⟨0, ht⟩ + 1 = start + t) := by
  let first : Fin t := ⟨0, ht⟩
  let last : Fin t := ⟨t - 1, by omega⟩
  have hf : x first ∈ Finset.Ico start (start + t) := by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨first, Finset.mem_univ _, rfl⟩
  have hl : x last ∈ Finset.Ico start (start + t) := by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨last, Finset.mem_univ _, rfl⟩
  obtain ⟨hf0, hf1⟩ := Finset.mem_Ico.mp hf
  obtain ⟨hl0, hl1⟩ := Finset.mem_Ico.mp hl
  have hz : Function.Injective (fun i => (x i : ℤ)) := by
    intro i j he
    apply hinj
    change (x i : ℤ) = (x j : ℤ) at he
    omega
  change (x first = start ∧ x last + 1 = start + t) ∨
    (x last = start ∧ x first + 1 = start + t)
  rcases line_path_interval ht (fun i => (x i : ℤ)) hz hstep with h | h
  · have he := h last
    change (x last : ℤ) = (x first : ℤ) + ((t - 1 : ℕ) : ℤ) at he
    exact Or.inl ⟨by omega, by omega⟩
  · have he := h last
    change (x last : ℤ) = (x first : ℤ) - ((t - 1 : ℕ) : ℤ) at he
    exact Or.inr ⟨by omega, by omega⟩

noncomputable def frameWallLevel {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hQ : 0 < Q) (w : FrameWall q) : ℕ :=
  railCoordinate a (F.railEdge 1).axis (frameWallLongEndpoint q Q items hQ w f)

theorem FrameAnchorFamily.wall_level_pair {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (_hq0 : 0 < q) (hQ : 0 < Q) (hq : q < Q)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) (j : Fin q) :
    ({frameWallLevel F hQ (j, 0), frameWallLevel F hQ (j, 1)} : Finset ℕ) =
      {F.start (j, 1), F.start (j, 1) + beta Q - 1} := by
  let p : Fin (beta Q) → Site := (frameBlockOccurrence q Q items (j, 1)).path f
  let x : Fin (beta Q) → ℕ := fun i => railCoordinate a (F.railEdge 1).axis (p i)
  have ht : 0 < beta Q := by dsimp [beta]; omega
  have hr : F.rail (j, 1) = 1 := (F.long_rail hQ hq (j, 1)).mpr (by simp [frameBlockKind])
  have hedge : ∀ i, p i ∈ openEdgeFinset a (depth q Q) (F.railEdge 1) := by
    intro i
    simpa only [p, hr] using F.on_edge (j, 1) i
  have hxinj : Function.Injective x := by
    intro i k hik
    apply (frameBlockOccurrence q Q items (j, 1)).path_injective f
    exact railCoordinate_injective_on_edge a (depth q Q) (F.railEdge 1) (p i) (p k) (hedge i) (hedge k) hik
  have hxstep : ∀ i k : Fin (beta Q), i.val + 1 = k.val → ((x k : ℤ) - (x i : ℤ)).natAbs = 1 := by
    intro i k hik
    exact edge_coordinate_adjacent (hedge i) (hedge k)
      ((frameBlockOccurrence q Q items (j, 1)).path_adjacent f a (side q Q) hpack i k hik)
  have himage : Finset.univ.image x = Finset.Ico (F.start (j, 1)) (F.start (j, 1) + beta Q) := by
    simpa [x, p, hr, anchorSites, frameBlockKind, anchorLength] using F.coordinate_image (j, 1)
  have hend := nat_interval_path_endpoints ht x hxinj hxstep (F.start (j, 1)) himage
  change ({x ⟨0, ht⟩, x ⟨beta Q - 1, by omega⟩} : Finset ℕ) = _
  rcases hend with ⟨hfirst, hlast⟩ | ⟨hlast, hfirst⟩
  · have hl : x ⟨beta Q - 1, by omega⟩ = F.start (j, 1) + beta Q - 1 := by omega
    rw [hfirst, hl]
  · have hf : x ⟨0, ht⟩ = F.start (j, 1) + beta Q - 1 := by omega
    rw [hf, hlast, Finset.pair_comm]

theorem FrameAnchorFamily.wall_levels_canonical {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hq0 : 0 < q) (hQ : 0 < Q) (hq : q < Q)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    Finset.univ.image (frameWallLevel F hQ) =
      (Finset.range q).biUnion (fun j => {j * beta Q + 1, (j + 1) * beta Q}) := by
  have hpairs : Finset.univ.image (frameWallLevel F hQ) =
      Finset.univ.biUnion (fun j : Fin q => {frameWallLevel F hQ (j, 0), frameWallLevel F hQ (j, 1)}) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨j, k⟩, hy⟩
      refine ⟨j, ?_⟩
      fin_cases k
      · exact Or.inl hy.symm
      · exact Or.inr hy.symm
    · rintro ⟨j, hy | hy⟩
      · exact ⟨(j, 0), hy.symm⟩
      · exact ⟨(j, 1), hy.symm⟩
  rw [hpairs]
  simp_rw [F.wall_level_pair hq0 hQ hq hpack]
  have himage : (Finset.univ.image (fun j : Fin q => F.start (j, 1))).biUnion
      (fun s => {s, s + beta Q - 1}) =
      Finset.univ.biUnion (fun j : Fin q => {F.start (j, 1), F.start (j, 1) + beta Q - 1}) :=
    Finset.image_biUnion
  rw [← himage, F.long_starts_by_wall hQ hq, Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro j _
  have he : j * beta Q + 1 + beta Q - 1 = (j + 1) * beta Q := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [he]

/-- Exact occupied wall set, for any supplied common face containing all
actual wall paths. Consequently callers may use the same face witness as for
the items, without any independent orientation choice. -/
theorem FrameAnchorFamily.wall_union_canonical {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hq0 : 0 < q) (hQ : 0 < Q) (hq : q < Q)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q))
    (face : CubeFace) (hface : ∀ (w : FrameWall q) i,
      FaceInterior a (side q Q) face.1 face.2 (frameWallPath q Q items w f i)) :
    (Finset.univ.biUnion fun w : FrameWall q => (frameWallFace q Q items w).sites f) =
      (Finset.range q).biUnion (fun j =>
        faceRowFinset a (depth q Q) face (F.railEdge 1).axis (j * beta Q + 1) ∪
        faceRowFinset a (depth q Q) face (F.railEdge 1).axis ((j + 1) * beta Q)) := by
  have hrows : ∀ w, (frameWallFace q Q items w).sites f =
      faceRowFinset a (depth q Q) face (F.railEdge 1).axis (frameWallLevel F hQ w) :=
    F.wall_full_row hq0 hQ hq hpack face hface
  simp_rw [hrows]
  have himage : (Finset.univ.image (frameWallLevel F hQ)).biUnion
      (faceRowFinset a (depth q Q) face (F.railEdge 1).axis) =
      Finset.univ.biUnion (fun w : FrameWall q =>
        faceRowFinset a (depth q Q) face (F.railEdge 1).axis (frameWallLevel F hQ w)) :=
    Finset.image_biUnion
  rw [← himage, F.wall_levels_canonical hq0 hQ hq hpack]
  simp only [Finset.biUnion_biUnion, Finset.biUnion_insert, Finset.singleton_biUnion]

theorem frameWallFace_end_at_right_block (q Q : ℕ) (items : List ℕ) (w : FrameWall q) :
    (frameWallFace q Q items w).pre.length + (faceWord (depth q Q)).length =
      frameBlockOffset q Q (wallRightBlock w) := by
  rw [frameWallFace_offset, faceWord_length _ (depth_even q Q)]
  rcases w with ⟨j, k⟩
  fin_cases k
  all_goals simp [frameWallOffset, frameBlockOffset, wallRightBlock, wallLeftSize,
    wallInnerOffset, Nat.add_assoc]
  all_goals omega

/-- Every wall F block ends before the item-word tail starts. This source
index bound gives spatial disjointness from all actual item fragments. -/
theorem frameWallFace_end_le_items (q Q : ℕ) (items : List ℕ) (w : FrameWall q) :
    (frameWallFace q Q items w).pre.length + (faceWord (depth q Q)).length ≤
      (prefixWord q Q).length + (walls q Q).length := by
  rw [frameWallFace_end_at_right_block]
  have hunit : (wallUnits q Q).length ≤ (walls q Q).length := by
    change (wallUnits q Q).length ≤ (wallUnits q Q ++ gapWord q Q).length
    simp only [List.length_append]
    omega
  have hb : frameBlockOffset q Q (wallRightBlock w) ≤ (prefixWord q Q).length + (wallUnits q Q).length := by
    rcases w with ⟨j, k⟩
    fin_cases k
    · have h := wall_block_end_le_units q Q j 1
      simpa [frameBlockOffset, wallRightBlock, wallInnerOffset, Nat.add_assoc] using
        (Nat.add_le_add_left (Nat.le_trans (by omega : j.val * wallStride q Q + wallInnerOffset q Q 1 ≤
          j.val * wallStride q Q + wallInnerOffset q Q 1 + 3 * beta Q) h) (prefixWord q Q).length)
    · have h := wall_block_end_le_units q Q j 2
      simpa [frameBlockOffset, wallRightBlock, wallInnerOffset, Nat.add_assoc] using
        (Nat.add_le_add_left (Nat.le_trans (by omega : j.val * wallStride q Q + wallInnerOffset q Q 2 ≤
          j.val * wallStride q Q + wallInnerOffset q Q 2 + 3 * alpha Q) h) (prefixWord q Q).length)
  exact hb.trans (Nat.add_le_add_left hunit _)

end ProteinFolding.CubicPackingGeometry
