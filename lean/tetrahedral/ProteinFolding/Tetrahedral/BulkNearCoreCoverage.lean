import ProteinFolding.Tetrahedral.BulkNearCoreEscape
import ProteinFolding.Tetrahedral.BulkNearPatchReference

/-! Coverage of the near-core table is stated for the actual near-edge
candidates and the actual frozen patch support. No general box-exhaustion
claim is made or needed by these interfaces. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkReanchor_fastDamaged_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 3 ≤ m) (hn : D + 3 ≤ n) (hp : InBulkVertexBox m v D p) :
    bulkFastDamaged n (bulkReanchorSite m n v p) ↔ bulkFastDamaged m p :=
  (bulkDamaged_fast_iff n (bulkReanchorSite m n v p)).symm.trans
    ((bulkReanchor_damaged_iff m n v D p hm hn hp).trans (bulkDamaged_fast_iff m p))

theorem bulkNearEdgeCandidate_core_image (m : ℕ) (hm : 50 ≤ m)
    (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d : Fin 4)
    (hd : bulkEdgeCandidate m F t.val odd d (by omega) ∈ bulkDamaged m) :
    bulkEdgeCandidate m F t.val odd d (by omega) ∈
        (bulkNearSegmentSupport (bulkNearSegmentCandidateIndex F t odd d)).image
          (bulkReanchorSite 50 m
            (bulkNearSegmentVertex (bulkNearSegmentCandidateIndex F t odd d))) ∧
      bulkNearSegmentCore (bulkNearSegmentCandidateIndex F t odd d) = true := by
  have hOne : 1 ≤ m := Nat.le_trans (by decide : 1 ≤ 50) hm
  have hLarge : 20 + 3 ≤ m := Nat.le_trans (by decide : 23 ≤ 50) hm
  have ht : t.val ≤ 9 := Nat.le_of_lt_succ t.isLt
  let c := bulkEdgeCandidate 50 F t.val odd d (by decide)
  let q := bulkEdgeCandidate m F t.val odd d hOne
  let i := bulkNearSegmentCandidateIndex F t odd d
  change q ∈ bulkDamaged m at hd
  change q ∈ (bulkNearSegmentSupport i).image
    (bulkReanchorSite 50 m (bulkNearSegmentVertex i)) ∧ bulkNearSegmentCore i = true
  have hbox : InBulkVertexBox 50 (bulkEdgeStartIndex F) 20 c :=
    bulkNearEdgeCandidate_in_start_box 50 F t.val odd d (by decide) ht
  have hs : bulkReanchorSite 50 m (bulkEdgeStartIndex F) c = q :=
    bulkVertexReanchor_candidate 50 m F t.val odd d (by decide) hOne
  have hdmapped : bulkReanchorSite 50 m (bulkEdgeStartIndex F) c ∈ bulkDamaged m :=
    Eq.mp (congrArg (fun p : Site => p ∈ bulkDamaged m) hs.symm) hd
  have hfastmapped := (bulkDamaged_fast_iff m (bulkReanchorSite 50 m (bulkEdgeStartIndex F) c)).mp hdmapped
  have hdref := (bulkReanchor_fastDamaged_iff 50 m (bulkEdgeStartIndex F) 20 c
    (by decide) hLarge hbox).mp hfastmapped
  have href := bulkNearSegment_candidate_reference F t odd d
    hdref
  have hmem : c ∈ bulkNearSegmentSupport i := href.1
  have hv : bulkNearSegmentVertex i = bulkEdgeStartIndex F := href.2.1
  have hcore : bulkNearSegmentCore i = true := href.2.2
  have himg : bulkReanchorSite 50 m (bulkNearSegmentVertex i) c = q :=
    (congrArg (fun v : Fin 6 => bulkReanchorSite 50 m v c) hv).trans hs
  have hq : q ∈ (bulkNearSegmentSupport i).image
      (bulkReanchorSite 50 m (bulkNearSegmentVertex i)) :=
    (Finset.mem_image (f := bulkReanchorSite 50 m (bulkNearSegmentVertex i))
      (s := bulkNearSegmentSupport i) (b := q)).mpr ⟨c, hmem, himg⟩
  exact ⟨hq, hcore⟩

theorem bulkNearEdgeCandidate_escape (m : ℕ) (hm : 50 ≤ m)
    (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d : Fin 4) (p : BulkVertex m)
    (hp : p.val = bulkEdgeCandidate m F t.val odd d (by omega))
    (hd : p.val ∈ bulkDamaged m) :
    ∃ q : BulkVertex m, (bulkFiniteGraph m).Reachable p q ∧
      ((bulkFiniteGraph m).degree q ≤ 1 ∨ bulkSegmentPotential m p < bulkSegmentPotential m q) := by
  have hc := bulkNearEdgeCandidate_core_image m hm F t odd d (by simpa only [← hp] using hd)
  exact bulkNearCore_point_escape m hm (bulkNearSegmentCandidateIndex F t odd d)
    hc.2 p (by simpa only [hp] using hc.1)

theorem bulkNearPatch_core_image (m : ℕ) (v : Fin 6)
    (r : {r : Coordinates // r ∈ bulkPatchOffsets v}) :
    bulkPatchOffsetSite m v r ∈
        (bulkNearSegmentSupport (bulkNearPatchSegmentIndex v r.val)).image
          (bulkReanchorSite 50 m (bulkNearSegmentVertex (bulkNearPatchSegmentIndex v r.val))) ∧
      bulkNearSegmentCore (bulkNearPatchSegmentIndex v r.val) = true := by
  obtain ⟨hmem, hv, hcore⟩ := bulkNearPatch_reference v r.val r.property
  refine ⟨?_, hcore⟩
  rw [hv]
  exact Finset.mem_image.mpr ⟨bulkPatchOffsetSite 50 v r, hmem,
    bulkReanchor_patchOffsetSite 50 m v r⟩

theorem bulkPatchSupport_escape (m : ℕ) (hm : 50 ≤ m) (p : BulkVertex m)
    (hp : p.val ∈ bulkPatchSupport m) :
    ∃ q : BulkVertex m, (bulkFiniteGraph m).Reachable p q ∧
      ((bulkFiniteGraph m).degree q ≤ 1 ∨ bulkSegmentPotential m p < bulkSegmentPotential m q) := by
  obtain ⟨v, _, h⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp h
  have hc := bulkNearPatch_core_image m v r
  exact bulkNearCore_point_escape m hm (bulkNearPatchSegmentIndex v r.val) hc.2 p
    (by simpa only [hr] using hc.1)

end ProteinFolding.Tetrahedral
