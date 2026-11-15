import ProteinFolding.Tetrahedral.BulkNearCoreCheck0
import ProteinFolding.Tetrahedral.BulkNearCoreCheck1
import ProteinFolding.Tetrahedral.BulkNearCoreCheck2
import ProteinFolding.Tetrahedral.BulkNearCoreCheck3
import ProteinFolding.Tetrahedral.BulkNearCoreCheck4
import ProteinFolding.Tetrahedral.BulkNearCoreCheck5
import ProteinFolding.Tetrahedral.BulkNearSegmentsUniform
import ProteinFolding.Tetrahedral.BulkNearExceptionalEscape

/-! Every listed core component reaches an end or a component of strictly
larger potential. The statement concerns the actual finite bulk cover at m. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkNearCore_reference (i : Fin 234) : BulkNearCoreEscapeCheck i := by
  have h : ∀ v : Fin 6, bulkNearSegmentVertex i = v → BulkNearCoreEscapeCheck i := by
    intro v
    fin_cases v
    · exact bulkNearCore_reference_0 i
    · exact bulkNearCore_reference_1 i
    · exact bulkNearCore_reference_2 i
    · exact bulkNearCore_reference_3 i
    · exact bulkNearCore_reference_4 i
    · exact bulkNearCore_reference_5 i
  exact h _ rfl

theorem bulkNearSegment_root_cover_reachable (m : ℕ) (hm : 50 ≤ m) (i : Fin 234)
    (p : Site) (hp : p ∈ bulkNearSegmentSupport i) :
    (bulkFiniteGraph m).Reachable (bulkNearSegmentRootView m hm i)
      (bulkNearSegmentPointView m hm i p hp) :=
  bulkSegment_reachable_cover m (bulkNearSegment_point_reachable m hm i p hp)

theorem bulkNearCore_root_escape (m : ℕ) (hm : 50 ≤ m) (i : Fin 234)
    (hcore : bulkNearSegmentCore i = true) :
    ∃ q : BulkVertex m,
      (bulkFiniteGraph m).Reachable (bulkNearSegmentRootView m hm i) q ∧
      ((bulkFiniteGraph m).degree q ≤ 1 ∨
        bulkSegmentPotential m (bulkNearSegmentRootView m hm i) < bulkSegmentPotential m q) := by
  have hc := (bulkNearCore_reference i) hcore
  by_cases h0 : (bulkNearCoreCase i).val = 0
  · rw [if_pos h0] at hc
    obtain ⟨hp, hdeg⟩ := hc
    refine ⟨bulkNearSegmentPointView m hm i (bulkNearCoreSource i) hp,
      bulkNearSegment_root_cover_reachable m hm i _ hp, Or.inl ?_⟩
    rw [bulkFinite_degree]
    change (bulkCoverNeighbours m
      (bulkReanchorSite 50 m (bulkNearSegmentVertex i) (bulkNearCoreSource i))).card ≤ 1
    rw [bulkReanchor_coverNeighbours_card 50 m (bulkNearSegmentVertex i) 43 _
      (by decide) hm (bulkNearSegment_reference_box i _ hp), bulkCoverNeighbours_fast_card]
    exact hdeg
  · rw [if_neg h0] at hc
    by_cases h1 : (bulkNearCoreCase i).val = 1
    · rw [if_pos h1] at hc
      obtain ⟨hp, hq, hbond, hv, hlt⟩ := hc
      let j := bulkNearCoreNext i
      have hqbox : InBulkVertexBox 50 (bulkNearSegmentVertex i) 43 (bulkNearCoreTarget i) := by
        rw [← hv]
        exact bulkNearSegment_reference_box j _ hq
      have hbond' := (bulkReanchor_coverBond_iff 50 m (bulkNearSegmentVertex i) 43
        (bulkNearCoreSource i) (bulkNearCoreTarget i) (by decide) (by omega)
        (bulkNearSegment_reference_box i _ hp) hqbox).mpr
          ((bulkCoverBond_fast_iff 50 _ _).mpr hbond)
      have hadj : (bulkFiniteGraph m).Adj
          (bulkNearSegmentPointView m hm i (bulkNearCoreSource i) hp)
          (bulkNearSegmentPointView m hm j (bulkNearCoreTarget i) hq) := by
        change bulkCoverBond m (bulkReanchorSite 50 m (bulkNearSegmentVertex i) _)
          (bulkReanchorSite 50 m (bulkNearSegmentVertex j) _)
        change bulkNearSegmentVertex (bulkNearCoreNext i) = bulkNearSegmentVertex i at hv
        rw [show bulkNearSegmentVertex j = bulkNearSegmentVertex i from hv]
        exact hbond'
      refine ⟨bulkNearSegmentRootView m hm j,
        ((bulkNearSegment_root_cover_reachable m hm i _ hp).trans hadj.reachable).trans
          (bulkNearSegment_root_cover_reachable m hm j _ hq).symm, Or.inr ?_⟩
      exact bulkNearSegment_uniform_potential_lt m hm i j hv hlt
    · rw [if_neg h1] at hc
      obtain ⟨hp, hv⟩ := hc
      let e := bulkNearCoreException i
      have he : bulkNearSegmentPointView m hm i (bulkNearEscapeStart e) hp =
          bulkNearEscapeStartView m (by omega) e := by
        apply Subtype.ext
        change bulkReanchorSite 50 m (bulkNearSegmentVertex i) _ =
          bulkReanchorSite 50 m (bulkNearEscapeVertex e) _
        rw [show bulkNearEscapeVertex e = bulkNearSegmentVertex i from hv]
      obtain ⟨q, hreach, hcase⟩ := bulkNearExceptional_escape m (by omega) e
      have hr := bulkNearSegment_root_cover_reachable m hm i (bulkNearEscapeStart e) hp
      rw [he] at hr
      refine ⟨q, hr.trans hreach, ?_⟩
      rcases hcase with hdeg | hlt
      · exact Or.inl hdeg
      · right
        have hphi := bulkNearSegment_point_potential m hm i (bulkNearEscapeStart e) hp
        rw [he] at hphi
        rw [hphi]
        exact hlt

theorem bulkNearCore_point_escape (m : ℕ) (hm : 50 ≤ m) (i : Fin 234)
    (hcore : bulkNearSegmentCore i = true) (p : BulkVertex m)
    (hp : p.val ∈ (bulkNearSegmentSupport i).image
      (bulkReanchorSite 50 m (bulkNearSegmentVertex i))) :
    ∃ q : BulkVertex m, (bulkFiniteGraph m).Reachable p q ∧
      ((bulkFiniteGraph m).degree q ≤ 1 ∨ bulkSegmentPotential m p < bulkSegmentPotential m q) := by
  have hseg : (bulkSegmentGraph m).Reachable (bulkNearSegmentRootView m hm i) p :=
    (bulkSegment_reachable_iff_site m (bulkNearSegmentRootView m hm i) p).mpr
      ((bulkNearSegment_uniform_component m hm i p.val).mp hp)
  obtain ⟨q, hreach, hcase⟩ := bulkNearCore_root_escape m hm i hcore
  refine ⟨q, (bulkSegment_reachable_cover m hseg).symm.trans hreach, ?_⟩
  rcases hcase with hdeg | hlt
  · exact Or.inl hdeg
  · right
    rwa [← bulkSegmentPotential_eq m hseg]

end ProteinFolding.Tetrahedral
