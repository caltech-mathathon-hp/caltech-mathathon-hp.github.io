import ProteinFolding.Cubic.Proofs.PackingGeometryFrameBarriers
import ProteinFolding.Cubic.Proofs.PackingFrameItems
import ProteinFolding.Cubic.Proofs.PackingCanonicalBins

/-! Soundness of the actual alternative cubic frame: recover an exact packing
from every perfect fold. Item occurrences retain distinct indices even when
their numerical sizes agree. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

theorem itemFaceOccurrence_after_walls (q Q : ℕ) (items : List ℕ) (i : Fin items.length) :
    (prefixWord q Q).length + (walls q Q).length ≤ (itemFaceOccurrence q Q items i).pre.length := by
  simp only [itemFaceOccurrence, List.length_append, List.length_replicate]
  omega

theorem itemFaceOccurrence_disjoint_wall (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) (i : Fin items.length) (w : FrameWall q) :
    Disjoint ((itemFaceOccurrence q Q items i).sites f) ((frameWallFace q Q items w).sites f) := by
  exact (FaceOccurrence.sites_disjoint_of_before _ _ f
    ((frameWallFace_end_le_items q Q items w).trans (itemFaceOccurrence_after_walls q Q items i))).symm

theorem FrameAnchorFamily.item_avoids_rows {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hq0 : 0 < q) (hQ : 0 < Q) (hq : q < Q)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q))
    (face : CubeFace) (hwallface : ∀ (w : FrameWall q) i,
      FaceInterior a (side q Q) face.1 face.2 (frameWallPath q Q items w f i))
    (hitemface : ∀ (i : Fin items.length) p, p ∈ (itemFaceOccurrence q Q items i).sites f →
      FaceInterior a (side q Q) face.1 face.2 p) :
    ∀ (i : Fin items.length) p, p ∈ (itemFaceOccurrence q Q items i).sites f → ∀ j : Fin q,
      railCoordinate a (F.railEdge 1).axis p ≠ j.val * beta Q + 1 ∧
      railCoordinate a (F.railEdge 1).axis p ≠ (j.val + 1) * beta Q := by
  have hrows := F.wall_union_canonical hq0 hQ hq hpack face hwallface
  intro i p hp j
  have hnot : p ∉ (Finset.univ.biUnion fun w : FrameWall q => (frameWallFace q Q items w).sites f) := by
    intro hm
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hm
    exact Finset.disjoint_left.mp (itemFaceOccurrence_disjoint_wall q Q items f i w) hp hw
  have hbase : p ∈ faceInteriorFinset a (depth q Q) face :=
    (mem_faceInteriorFinset a (depth q Q) face p).mpr (hitemface i p hp)
  constructor
  · intro he
    apply hnot
    rw [hrows]
    exact Finset.mem_biUnion.mpr ⟨j.val, Finset.mem_range.mpr j.isLt,
      Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hbase, he⟩)⟩
  · intro he
    apply hnot
    rw [hrows]
    exact Finset.mem_biUnion.mpr ⟨j.val, Finset.mem_range.mpr j.isLt,
      Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbase, he⟩)⟩

theorem FaceOccurrence.path_adjacent {S : Sequence} {t : ℕ} (o : FaceOccurrence S t)
    (f : Fold cubicLattice S.length) (a : Site) (n : ℕ)
    (hpack : hydrophobicSites S f = cube a n) (i j : Fin (2 * (t / 2))) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (o.path f i) (o.path f j) := by
  rw [o.path_eq]
  apply faceHPath_adjacent o.pre o.post t (foldOnWord o.word_eq f) a n
    (by rw [foldOnWord_hydrophobicSites]; exact hpack) i j hij

theorem frame_common_item_wall_face (q Q : ℕ) (items : List ℕ) (hq : 2 ≤ q) (hQ : q < Q)
    (hpos : ∀ s ∈ items, 0 < s)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    ∃ face : CubeFace,
      (∀ (w : FrameWall q) i, FaceInterior a (side q Q) face.1 face.2 (frameWallPath q Q items w f i)) ∧
      ∀ (i : Fin items.length) p, p ∈ (itemFaceOccurrence q Q items i).sites f →
        FaceInterior a (side q Q) face.1 face.2 p := by
  have hd : 2 < depth q Q := by
    have hQ0 : 0 < Q := by omega
    have hm := Nat.mul_le_mul_right (beta Q) hq
    dsimp [depth, beta] at *
    omega
  obtain ⟨face, hface⟩ := frame_remaining_face_confines q Q items (by omega)
    (by nlinarith : 4 < depth q Q ^ 2) f a hpack
  refine ⟨face, ?_, ?_⟩
  · intro w i
    apply hface (depth q Q) (frameWallFace q Q items w) (frameWallFace_after_prefix q Q items w)
      (by have he := Nat.mul_div_cancel' (depth_even q Q); omega)
    exact Finset.mem_image.mpr ⟨Fin.cast (Nat.mul_div_cancel' (depth_even q Q)).symm i,
      Finset.mem_univ _, rfl⟩
  · intro i
    apply hface (depth q Q * items.get i) (itemFaceOccurrence q Q items i)
      (itemFaceOccurrence_after_prefix q Q items i)
    have hp := hpos _ (List.get_mem items i)
    rw [Nat.mul_div_cancel' (Nat.dvd_mul_right_of_dvd (depth_even q Q) _)]
    nlinarith

/-- Soundness of the unchanged literal cubic frame. Every successful perfect
fold gives an exact q-bin packing of the original item occurrences. The proof
allows arbitrary connected item shapes inside the forced strips. -/
theorem frameWord_sound (q Q : ℕ) (items : List ℕ) (hq : 2 ≤ q) (hQ : q < Q)
    (hpos : ∀ s ∈ items, 0 < s) (hsum : items.sum = q * (4 * Q)) :
    PerfectHPStringFold (frameWord q Q items) (side q Q) →
      ∃ parts, Packing.Exact ⟨items, 4 * Q, q⟩ parts := by
  intro hfold
  obtain ⟨f, a, hpack⟩ := hfold.2
  have hq0 : 0 < q := by omega
  have hQ0 : 0 < Q := by omega
  have hd : 0 < depth q Q := by have := depth_two_le q Q hq0; omega
  have hβ : 2 < beta Q := by dsimp [beta]; omega
  obtain ⟨F⟩ := frame_anchor_family_exists q Q items hq hQ f a hpack
  obtain ⟨face, hwallface, hitemface⟩ := frame_common_item_wall_face q Q items hq hQ hpos f a hpack
  let axis := (F.railEdge 1).axis
  have haxis : axis ≠ face.1 := F.wall_axis_ne_face hq0 hQ0 hQ hpack face hwallface
  have havoid := F.item_avoids_rows hq0 hQ0 hQ hpack face hwallface hitemface
  have hbins : ∀ i : Fin items.length, ∃ j : Fin q,
      ∀ k : Fin (2 * (depth q Q * items.get i / 2)),
        a axis + ((j.val * beta Q + 1 : ℕ) : ℤ) < (itemFaceOccurrence q Q items i).path f k axis ∧
        (itemFaceOccurrence q Q items i).path f k axis < a axis + (((j.val + 1) * beta Q : ℕ) : ℤ) := by
    intro i
    have hsize := hpos _ (List.get_mem items i)
    have heven : 2 * (depth q Q * items.get i / 2) = depth q Q * items.get i :=
      Nat.mul_div_cancel' (Nat.dvd_mul_right_of_dvd (depth_even q Q) _)
    apply exists_bin_for_face_path q (beta Q) (depth q Q) hq0 hβ rfl a face axis haxis
      ((itemFaceOccurrence q Q items i).path f) (by rw [heven]; exact Nat.mul_pos hd hsize)
    · intro k
      exact hitemface i _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    · intro k l hkl
      exact (itemFaceOccurrence q Q items i).path_adjacent f a (side q Q) hpack k l hkl
    · intro k j
      exact havoid i _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩) j
  let label : Fin items.length → Fin q := fun i => Classical.choose (hbins i)
  obtain ⟨cross, hcrossaxis, hcrossnormal⟩ := third_axis_exists axis face.1 haxis
  let regions : Fin q → Finset Site := canonicalBinRegion a (depth q Q) (beta Q) face cross axis
  have hinside : ∀ i, (itemFaceOccurrence q Q items i).sites f ⊆ regions (label i) := by
    intro i p hp
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
    apply mem_faceStrip_of_faceInterior cross axis hcrossaxis hcrossnormal haxis
    · exact hitemface i _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    · exact Classical.choose_spec (hbins i) k
  have hcapacity : ∀ j, (regions j).card ≤ depth q Q * (4 * Q) := by
    intro j
    change (canonicalBinRegion a (depth q Q) (beta Q) face cross axis j).card ≤ depth q Q * (4 * Q)
    rw [canonicalBinRegion_card a (depth q Q) (beta Q) face cross axis hcrossaxis]
    have he : beta Q - 2 = 4 * Q := by dsimp [beta]; omega
    rw [he]
  have hloads := Packing.label_sums_le_of_disjoint_sites items hd label
    (fun i => (itemFaceOccurrence q Q items i).sites f) regions
    (itemFaceOccurrence_sites_card q Q items f)
    (itemFaceOccurrence_sites_disjoint q Q items f) hinside hcapacity
  refine ⟨Packing.labelledParts items label, ?_⟩
  apply Packing.exact_of_label_sums ⟨items, 4 * Q, q⟩ label
  · simpa only [Nat.mul_comm q (4 * Q)] using hsum
  · exact hloads

end ProteinFolding.CubicPackingGeometry
