import ProteinFolding.Cubic.Proofs.PackingFaceOccurrences
import ProteinFolding.Cubic.Proofs.PackingAnchors

/-! Extracting the five large literal F blocks of the actual frame prefix.
Their source intervals avoid every marked E anchor. Full skeleton saturation
therefore confines each block to a face interior, without a chosen orientation. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking
open scoped BigOperators

theorem prefixMarked_anchors (q Q : ℕ) :
    (prefixMarked q Q).anchors =
      (MarkedWord.edge (9 * depth q Q + 8)).anchors ∪
        (MarkedWord.edge (depth q Q)).anchors.image
          (fun i => (edgeWord (9 * depth q Q + 8)).length + (faceWord (depth q Q ^ 2)).length + i) := by
  simp [prefixMarked, MarkedWord.join, MarkedWord.append, MarkedWord.plain,
    MarkedWord.repeat, List.length_append, Finset.image_image, Function.comp_def, Nat.add_assoc,
    MarkedWord.edge]

theorem frameAnchor_location (q Q : ℕ) (items : List ℕ)
    (i : Fin (frameWord q Q items).length) (hi : i ∈ frameAnchors q Q items) :
    i.val < (edgeWord (9 * depth q Q + 8)).length ∨
    ((edgeWord (9 * depth q Q + 8)).length + (faceWord (depth q Q ^ 2)).length ≤ i.val ∧
      i.val < (edgeWord (9 * depth q Q + 8)).length +
        (faceWord (depth q Q ^ 2)).length + (edgeWord (depth q Q)).length) ∨
    (prefixWord q Q).length ≤ i.val := by
  have hm : i.val ∈ (frameMarked q Q items).anchors :=
    (MarkedWord.mem_indices (markedFrame q Q items) i).mp hi
  simp only [frameMarked, MarkedWord.join, MarkedWord.append, MarkedWord.plain,
    Finset.union_empty, Finset.image_empty,
    Finset.mem_union, Finset.mem_image] at hm
  rcases hm with hp | ⟨j, hj, he⟩
  · rw [prefixMarked_anchors] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have h := ((MarkedWord.edge (9 * depth q Q + 8)).valid i.val hp).2.1
      change i.val + 1 < (edgeWord (9 * depth q Q + 8)).length at h
      exact Or.inl (by omega)
    · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hp
      have h := ((MarkedWord.edge (depth q Q)).valid j hj).2.1
      change j + 1 < (edgeWord (depth q Q)).length at h
      right
      left
      omega
  · right
    right
    rw [prefixMarked_word] at he
    omega

def largeFaceTail (q Q : ℕ) (items : List ℕ) : Sequence :=
  [.P] ++ List.replicate (depth q Q ^ 3 + 2) .H ++
    List.replicate (alpha Q + 8) .P ++ walls q Q ++ itemWords q Q items

def sideFaceBlock (q Q : ℕ) : Sequence :=
  faceWord (depth q Q ^ 2) ++ List.replicate (depth q Q + 9) .P

def beforeSideFaces (q Q : ℕ) : Sequence :=
  edgeWord (9 * depth q Q + 8) ++ faceWord (depth q Q ^ 2) ++
    edgeWord (depth q Q) ++ List.replicate 4 .P

def initialLargeFace (q Q : ℕ) (items : List ℕ) :
    FaceOccurrence (frameWord q Q items) (depth q Q ^ 2) where
  pre := edgeWord (9 * depth q Q + 8)
  post := edgeWord (depth q Q) ++ List.replicate 4 .P ++ repeatWord (sideFaceBlock q Q) 3 ++
    faceWord (depth q Q ^ 2 - 2) ++ largeFaceTail q Q items
  word_eq := by
    simp [frameWord, prefixWord, sideFaceBlock, largeFaceTail, List.append_assoc]

def sideLargeFace (q Q : ℕ) (items : List ℕ) (j : Fin 3) :
    FaceOccurrence (frameWord q Q items) (depth q Q ^ 2) where
  pre := beforeSideFaces q Q ++ repeatWord (sideFaceBlock q Q) j.val
  post := List.replicate (depth q Q + 9) .P ++
    repeatWord (sideFaceBlock q Q) (3 - j.val - 1) ++
    faceWord (depth q Q ^ 2 - 2) ++ largeFaceTail q Q items
  word_eq := by
    simp only [frameWord, prefixWord, sideFaceBlock]
    have hsplit := repeatWord_split (sideFaceBlock q Q) 3 j.val j.isLt
    dsimp only [sideFaceBlock] at hsplit
    rw [hsplit]
    simp [beforeSideFaces, largeFaceTail, List.append_assoc]

def finalLargeFace (q Q : ℕ) (items : List ℕ) :
    FaceOccurrence (frameWord q Q items) (depth q Q ^ 2 - 2) where
  pre := beforeSideFaces q Q ++ repeatWord (sideFaceBlock q Q) 3
  post := largeFaceTail q Q items
  word_eq := by
    simp [frameWord, prefixWord, beforeSideFaces, sideFaceBlock, largeFaceTail, List.append_assoc]

def largeFaceSize (q Q : ℕ) (i : Fin 5) : ℕ :=
  if i = 4 then depth q Q ^ 2 - 2 else depth q Q ^ 2

def frameLargeFace (q Q : ℕ) (items : List ℕ) :
    (i : Fin 5) → FaceOccurrence (frameWord q Q items) (largeFaceSize q Q i)
  | 0 => initialLargeFace q Q items
  | 1 => sideLargeFace q Q items 0
  | 2 => sideLargeFace q Q items 1
  | 3 => sideLargeFace q Q items 2
  | 4 => finalLargeFace q Q items

theorem frameLargeFace_interval (q Q : ℕ) (items : List ℕ) (i : Fin 5) :
    ((edgeWord (9 * depth q Q + 8)).length ≤ (frameLargeFace q Q items i).pre.length ∧
      (frameLargeFace q Q items i).pre.length + (faceWord (largeFaceSize q Q i)).length ≤
        (edgeWord (9 * depth q Q + 8)).length + (faceWord (depth q Q ^ 2)).length) ∨
    ((edgeWord (9 * depth q Q + 8)).length + (faceWord (depth q Q ^ 2)).length +
        (edgeWord (depth q Q)).length ≤ (frameLargeFace q Q items i).pre.length ∧
      (frameLargeFace q Q items i).pre.length + (faceWord (largeFaceSize q Q i)).length ≤
        (prefixWord q Q).length) := by
  fin_cases i <;>
    simp [frameLargeFace, initialLargeFace, sideLargeFace, finalLargeFace, largeFaceSize,
      beforeSideFaces, prefixWord, sideFaceBlock, repeatWord_length] <;> omega

theorem frameLargeFace_before (q Q : ℕ) (items : List ℕ) (i j : Fin 5) (hij : i < j) :
    (frameLargeFace q Q items i).pre.length + (faceWord (largeFaceSize q Q i)).length ≤
      (frameLargeFace q Q items j).pre.length := by
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals simp [frameLargeFace, initialLargeFace, sideLargeFace, finalLargeFace, largeFaceSize,
    beforeSideFaces, sideFaceBlock, repeatWord_length]
  all_goals omega

theorem frameLargeFace_not_anchor (q Q : ℕ) (items : List ℕ) (i : Fin 5)
    (j : Fin (2 * (largeFaceSize q Q i / 2))) :
    (frameLargeFace q Q items i).index j ∉ frameAnchors q Q items := by
  intro ha
  have hl := frameAnchor_location q Q items _ ha
  have hf := (frameLargeFace q Q items i).index_in_fragment j
  have hb := frameLargeFace_interval q Q items i
  have hp : (edgeWord (9 * depth q Q + 8)).length + (faceWord (depth q Q ^ 2)).length ≤
      (prefixWord q Q).length := by
    simp only [prefixWord, List.length_append, List.length_replicate]
    omega
  rcases hb with hb | hb <;> rcases hl with hl | hl | hl <;> omega

theorem frameLargeFace_noedge (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q))
    (i : Fin 5) (j : Fin (2 * (largeFaceSize q Q i / 2))) :
    ¬ EdgeSkeleton a (side q Q) ((frameLargeFace q Q items i).path f j) :=
  nonanchor_not_edge f a (side q Q) (frameAnchors q Q items)
    (frame_skeleton_saturated q Q items hq f a hpack) _ (frameLargeFace_not_anchor q Q items i j)

theorem largeFaceSize_even (q Q : ℕ) (i : Fin 5) : 2 ∣ largeFaceSize q Q i := by
  unfold largeFaceSize
  split_ifs
  · exact depth_square_sub_two_even q Q
  · exact depth_square_even q Q

theorem frameLargeFace_sites_card (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) (i : Fin 5) :
    ((frameLargeFace q Q items i).sites f).card = largeFaceSize q Q i := by
  rw [FaceOccurrence.sites_card]
  exact Nat.mul_div_cancel' (largeFaceSize_even q Q i)

theorem frameLargeFace_sites_disjoint (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) (i j : Fin 5) (hij : i ≠ j) :
    Disjoint ((frameLargeFace q Q items i).sites f) ((frameLargeFace q Q items j).sites f) := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact FaceOccurrence.sites_disjoint_of_before _ _ f (frameLargeFace_before q Q items i j hij)
  · exact (FaceOccurrence.sites_disjoint_of_before _ _ f (frameLargeFace_before q Q items j i hij)).symm

/-- In any perfect fold, the five actual large F blocks occupy five different
face interiors and leave exactly two sites in those faces. No face labels or
placements are assumptions. -/
theorem frame_five_large_faces (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (hd : 4 < depth q Q ^ 2)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    ∃ face : Fin 5 → CubeFace,
      (∀ i p, p ∈ (frameLargeFace q Q items i).sites f →
        FaceInterior a (side q Q) (face i).1 (face i).2 p) ∧
      Function.Injective face ∧
      ((Finset.univ.image face).biUnion (faceInteriorFinset a (depth q Q)) \
        Finset.univ.biUnion (fun i => (frameLargeFace q Q items i).sites f)).card = 2 := by
  classical
  have heach : ∀ i : Fin 5, ∃ face : CubeFace,
      ∀ p ∈ (frameLargeFace q Q items i).sites f,
        FaceInterior a (side q Q) face.1 face.2 p := by
    intro i
    apply (frameLargeFace q Q items i).in_one_face f a (side q Q) hpack
    · have heven := Nat.mul_div_cancel' (largeFaceSize_even q Q i)
      have hpos : 0 < largeFaceSize q Q i := by
        unfold largeFaceSize
        split_ifs <;> omega
      omega
    · exact frameLargeFace_noedge q Q items hq f a hpack i
  choose face hface using heach
  refine ⟨face, hface, ?_⟩
  apply five_large_faces_left_two a (depth q Q) hd
    (fun i => (frameLargeFace q Q items i).sites f) face
  · intro i
    rw [frameLargeFace_sites_card]
    unfold largeFaceSize
    split_ifs <;> omega
  · have hu : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
    rw [hu]
    simp [frameLargeFace_sites_card, largeFaceSize]
    omega
  · exact hface
  · exact frameLargeFace_sites_disjoint q Q items f

/-- The remaining sixth face is unique; all other face interiors together
have exactly two sites not occupied by the large prefix blocks. -/
theorem frame_remaining_face (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (hd : 4 < depth q Q ^ 2)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    ∃ packingFace : CubeFace,
      (((Finset.univ : Finset CubeFace) \ {packingFace}).biUnion
          (faceInteriorFinset a (depth q Q)) \
        Finset.univ.biUnion (fun i => (frameLargeFace q Q items i).sites f)).card = 2 := by
  classical
  obtain ⟨face, _, hinj, htwo⟩ := frame_five_large_faces q Q items hq hd f a hpack
  have hlt : (Finset.univ.image face).card < (Finset.univ : Finset CubeFace).card := by
    rw [five_face_labels_card face hinj, Finset.card_univ, cubeFace_card]
    decide
  obtain ⟨packingFace, _, hav⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have havoid : ∀ i, face i ≠ packingFace := by
    intro i he
    exact hav (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
  refine ⟨packingFace, ?_⟩
  rwa [five_faces_exhaust_other_faces face hinj packingFace havoid] at htwo

end ProteinFolding.CubicPackingGeometry
