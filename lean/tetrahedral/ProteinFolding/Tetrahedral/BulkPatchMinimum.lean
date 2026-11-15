import ProteinFolding.Tetrahedral.BulkPatchReferenceMinimum
import ProteinFolding.Tetrahedral.BulkDegree
import ProteinFolding.Tetrahedral.BulkSurfaceDegree

/-! Uniform minimum-degree consequences of the fixed patch certificate. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem bulkPatch_minimum (m : ℕ) (hm : 15 ≤ m) (v : Fin 6)
    (r : {r : Coordinates // r ∈ bulkPatchOffsets v})
    (hp : bulkPatchOffsetSite m v r ∈ bulkInterior m) :
    (if 0 < (octDanglingDirections m (bulkPatchOffsetSite m v r)).card then 1 else 2) ≤
      (bulkCoverNeighbours m (bulkPatchOffsetSite m v r)).card := by
  have hbox := bulkPatchOffsetSite_in_box m v r
  have hI := (bulkReanchor_interior_iff m 15 v 8 (bulkPatchOffsetSite m v r)
    (by omega) (by decide) hbox).mpr hp
  rw [bulkReanchor_patchOffsetSite] at hI
  have hc := bulkPatch_reference_minimum v r
  dsimp only at hc
  have hmin := hc ((bulkInterior_fast_iff 15 _).mp hI)
  rw [← bulkDanglingDirections_fast_eq, ← bulkCoverNeighbours_fast_card] at hmin
  have hcard := bulkReanchor_coverNeighbours_card m 15 v 8 (bulkPatchOffsetSite m v r)
    (by omega) (by decide) hbox
  have hdang := bulkReanchor_danglingDirections_eq m 15 v 8 (bulkPatchOffsetSite m v r)
    (by omega) (by decide) hbox
  rw [bulkReanchor_patchOffsetSite] at hcard hdang
  rwa [hdang, hcard] at hmin

theorem bulkCover_minimum_on_patch_support (m : ℕ) (hm : 15 ≤ m) (p : Site)
    (hp : p ∈ bulkInterior m) (hs : p ∈ bulkPatchSupport m) :
    (if 0 < (octDanglingDirections m p).card then 1 else 2) ≤ (bulkCoverNeighbours m p).card := by
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hs
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
  exact bulkPatch_minimum m hm v r hp

theorem bulkCover_surface_positive (m : ℕ) (hm : 15 ≤ m) (p : Site)
    (hp : p ∈ bulkInterior m) (hs : OctSurfaceSite m p) : 1 ≤ (bulkCoverNeighbours m p).card := by
  by_cases hpatch : p ∈ bulkPatchSupport m
  · have hmin := bulkCover_minimum_on_patch_support m hm p hp hpatch
    rwa [if_pos hs.2] at hmin
  · exact bulkCover_surface_positive_of_not_support (by omega) p hp hs hpatch

theorem bulkCover_nondamaged_nonsurface_degree_all (m : ℕ) (hm : 15 ≤ m) (p : Site)
    (hp : p ∈ bulkInterior m) (hn : ¬OctSurfaceSite m p) (hd : p ∉ bulkDamaged m) :
    (bulkCoverNeighbours m p).card = 2 := by
  by_cases hpatch : p ∈ bulkPatchSupport m
  · have hmin := bulkCover_minimum_on_patch_support m hm p hp hpatch
    have hDang : ¬0 < (octDanglingDirections m p).card := by
      intro h
      exact hn ⟨(Finset.mem_sdiff.mp hp).1, h⟩
    rw [if_neg hDang] at hmin
    have hmax := bulkCoverNeighbours_card_le_two m hm p
    omega
  · exact bulkCover_nondamaged_nonsurface_degree m p hp hn hd hpatch

theorem bulkCover_good_degree_of_nondamaged (m : ℕ) (hm : 15 ≤ m) (p : Site)
    (hp : p ∈ bulkInterior m) (hd : p ∉ bulkDamaged m) :
    1 ≤ (bulkCoverNeighbours m p).card ∧
      (¬OctSurfaceSite m p → (bulkCoverNeighbours m p).card = 2) := by
  by_cases hs : OctSurfaceSite m p
  · exact ⟨bulkCover_surface_positive m hm p hp hs, fun hn => (hn hs).elim⟩
  · have heq := bulkCover_nondamaged_nonsurface_degree_all m hm p hp hs hd
    exact ⟨by omega, fun _ => heq⟩

end ProteinFolding.Tetrahedral
