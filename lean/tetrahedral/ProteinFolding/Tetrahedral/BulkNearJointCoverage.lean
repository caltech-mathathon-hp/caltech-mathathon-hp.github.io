import ProteinFolding.Tetrahedral.BulkNearCoreCoverage
import ProteinFolding.Tetrahedral.BulkNearJointReference

/-! Uniform coverage of merge targets adjacent to near damaged candidates.
Both the actual cover edge and its non-rung status are retained explicitly. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkReanchor_fastCoverBond_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p q : Site)
    (hm : D + 6 ≤ m) (hn : D + 6 ≤ n)
    (hp : InBulkVertexBox m v D p) (hq : InBulkVertexBox m v D q) :
    bulkFastCoverBond n (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) ↔
      bulkFastCoverBond m p q :=
  (bulkCoverBond_fast_iff n (bulkReanchorSite m n v p) (bulkReanchorSite m n v q)).symm.trans
    ((bulkReanchor_coverBond_iff m n v D p q hm hn hp hq).trans
      (bulkCoverBond_fast_iff m p q))

theorem bulkNearJoint_core_image (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame)
    (t : Fin 10) (odd : Bool) (d e : Fin 4)
    (hd : bulkEdgeCandidate m F t.val odd d (by omega) ∈ bulkDamaged m)
    (hrho : bulkRho m (bulkEdgeCandidate m F t.val odd d (by omega)) =
      bulkRho m (step (bulkEdgeCandidate m F t.val odd d (by omega)) e))
    (hbond : bulkCoverBond m (bulkEdgeCandidate m F t.val odd d (by omega))
      (step (bulkEdgeCandidate m F t.val odd d (by omega)) e)) :
    step (bulkEdgeCandidate m F t.val odd d (by omega)) e ∈
        (bulkNearSegmentSupport (bulkNearSegmentJointIndex F t odd d e)).image
          (bulkReanchorSite 50 m
            (bulkNearSegmentVertex (bulkNearSegmentJointIndex F t odd d e))) ∧
      bulkNearSegmentCore (bulkNearSegmentJointIndex F t odd d e) = true := by
  have hOne : 1 ≤ m := Nat.le_trans (by decide : 1 ≤ 50) hm
  have hLarge : 21 + 6 ≤ m := Nat.le_trans (by decide : 27 ≤ 50) hm
  have hDamage : 21 + 3 ≤ m := Nat.le_trans (by decide : 24 ≤ 27) hLarge
  have hRho : 21 + 2 ≤ m := Nat.le_trans (by decide : 23 ≤ 27) hLarge
  have hNear : t.val ≤ 9 := Nat.le_of_lt_succ t.isLt
  let c := bulkEdgeCandidate 50 F t.val odd d (by decide)
  let q := step c e
  have hs : bulkReanchorSite 50 m (bulkEdgeStartIndex F) c =
      bulkEdgeCandidate m F t.val odd d (by omega) :=
    bulkVertexReanchor_candidate 50 m F t.val odd d (by decide) hOne
  have ht : bulkReanchorSite 50 m (bulkEdgeStartIndex F) q =
      step (bulkEdgeCandidate m F t.val odd d (by omega)) e := by
    change bulkReanchorSite 50 m (bulkEdgeStartIndex F) (step c e) = _
    rw [bulkReanchorSite_step, hs]
  have hbox := bulkNearEdgeCandidate_in_start_box 50 F t.val odd d (by decide) hNear
  have hboxc : InBulkVertexBox 50 (bulkEdgeStartIndex F) 21 c :=
    bulkVertexBox_mono 50 _ (by decide) hbox
  have hboxq : InBulkVertexBox 50 (bulkEdgeStartIndex F) 21 q :=
    bulk_adjacent_in_vertex_box 50 _ 20 hbox (step_adj c e)
  have hdmapped : bulkReanchorSite 50 m (bulkEdgeStartIndex F) c ∈ bulkDamaged m :=
    Eq.mp (congrArg (fun p : Site => p ∈ bulkDamaged m) hs.symm) hd
  have hfastmapped := (bulkDamaged_fast_iff m (bulkReanchorSite 50 m (bulkEdgeStartIndex F) c)).mp hdmapped
  have hdref := (bulkReanchor_fastDamaged_iff 50 m (bulkEdgeStartIndex F) 21 c
    (by decide) hDamage hboxc).mp hfastmapped
  have hrhoref : bulkRho 50 c = bulkRho 50 q := by
    have hcs := (bulkReanchor_rho_alpha 50 m (bulkEdgeStartIndex F) 21 c
      (by decide) hRho hboxc).1
    have hqs := (bulkReanchor_rho_alpha 50 m (bulkEdgeStartIndex F) 21 q
      (by decide) hRho hboxq).1
    rw [hs] at hcs
    rw [ht] at hqs
    omega
  have hbondmapped : bulkCoverBond m (bulkReanchorSite 50 m (bulkEdgeStartIndex F) c)
      (bulkReanchorSite 50 m (bulkEdgeStartIndex F) q) := by
    simpa only [hs, ht] using hbond
  have hfastbond := (bulkCoverBond_fast_iff m (bulkReanchorSite 50 m (bulkEdgeStartIndex F) c)
    (bulkReanchorSite 50 m (bulkEdgeStartIndex F) q)).mp hbondmapped
  have hbondref := (bulkReanchor_fastCoverBond_iff 50 m (bulkEdgeStartIndex F) 21 c q
    (by decide) hLarge hboxc hboxq).mp hfastbond
  obtain ⟨hmem, hv, hcore⟩ := bulkNearJoint_reference F t odd d e hdref hrhoref hbondref
  refine ⟨?_, hcore⟩
  rw [hv]
  exact Finset.mem_image.mpr ⟨q, hmem, ht⟩

theorem bulkNearJoint_escape (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame)
    (t : Fin 10) (odd : Bool) (d e : Fin 4) (p : BulkVertex m)
    (hp : p.val = step (bulkEdgeCandidate m F t.val odd d (by omega)) e)
    (hd : bulkEdgeCandidate m F t.val odd d (by omega) ∈ bulkDamaged m)
    (hrho : bulkRho m (bulkEdgeCandidate m F t.val odd d (by omega)) = bulkRho m p.val)
    (hbond : bulkCoverBond m (bulkEdgeCandidate m F t.val odd d (by omega)) p.val) :
    ∃ q : BulkVertex m, (bulkFiniteGraph m).Reachable p q ∧
      ((bulkFiniteGraph m).degree q ≤ 1 ∨ bulkSegmentPotential m p < bulkSegmentPotential m q) := by
  have hc := bulkNearJoint_core_image m hm F t odd d e hd
    (by simpa only [← hp] using hrho) (by simpa only [← hp] using hbond)
  exact bulkNearCore_point_escape m hm (bulkNearSegmentJointIndex F t odd d e) hc.2 p
    (by simpa only [hp] using hc.1)

end ProteinFolding.Tetrahedral
