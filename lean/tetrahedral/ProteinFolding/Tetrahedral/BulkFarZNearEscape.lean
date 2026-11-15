import ProteinFolding.Tetrahedral.BulkFarZNearUniform

/-! Actual merge endpoints in the three Z-edge transition positions
inherit the complete row certificates and strict escapes. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkFarZNear_endpoint_view (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (j : Fin 3)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (hZ : BulkZEdgeFrame F)
    (hd : bulkEdgeCandidate m F (bulkFarZNearT j) odd d hOne ∈ bulkDamaged m) (p : BulkVertex m)
    (hp : p.val = bulkEdgeCandidate m F (bulkFarZNearT j) odd d hOne ∨
      bulkMerge m (bulkEdgeCandidate m F (bulkFarZNearT j) odd d hOne) p.val) :
    ∃ (i : Fin 4) (hf : BulkFarZAscendingFrame F i),
      p = bulkFarZNearView m hm F j (bulkFarZFrom i) (bulkFarZ_from_family F i hf) := by
  have hbox := bulkFarZNear_candidate_box m F j odd d hOne
  have hDm := (bulkReanchor_damaged_iff m 50 (bulkEdgeStartIndex F) 26
    (bulkEdgeCandidate m F (bulkFarZNearT j) odd d hOne) (by omega) (by decide) hbox).mpr hd
  rw [bulkVertexReanchor_candidate m 50 F (bulkFarZNearT j) odd d hOne (by decide)] at hDm
  have href := bulkFarZNear_reference_source F j odd d hZ ((bulkDamaged_fast_iff 50 _).mp hDm)
  rcases href with ⟨hPos, hroot⟩ | ⟨hNeg, hroot⟩
  · rcases hp with hp | hp
    · have hsrc := congrArg (bulkReanchorSite 50 m (bulkEdgeStartIndex F)) hroot
      rw [bulkVertexReanchor_candidate 50 m F (bulkFarZNearT j) odd d (by decide) hOne] at hsrc
      let hf : BulkFarZAscendingFrame F 0 := Or.inl ⟨hPos, by decide⟩
      refine ⟨0, hf, Subtype.ext ?_⟩
      exact hp.trans hsrc
    · have hRule := (bulkReanchor_rule_iff m 50 (bulkEdgeStartIndex F) 26 _ p.val
        (by omega) (by decide) hbox).mpr hp.2.1.2.1
      rw [bulkVertexReanchor_candidate m 50 F (bulkFarZNearT j) odd d hOne (by decide), hroot] at hRule
      have htgt := congrArg (bulkReanchorSite 50 m (bulkEdgeStartIndex F))
        (bulkFarZNear_positive_target F j hPos _ hRule)
      rw [bulkReanchorSite_inverse] at htgt
      let hf : BulkFarZAscendingFrame F 1 := Or.inl ⟨hPos, by decide⟩
      refine ⟨1, hf, Subtype.ext ?_⟩
      exact htgt
  · rcases hp with hp | hp
    · have hsrc := congrArg (bulkReanchorSite 50 m (bulkEdgeStartIndex F)) hroot
      rw [bulkVertexReanchor_candidate 50 m F (bulkFarZNearT j) odd d (by decide) hOne] at hsrc
      let hf : BulkFarZAscendingFrame F 2 := Or.inr ⟨hNeg, by decide⟩
      refine ⟨2, hf, Subtype.ext ?_⟩
      exact hp.trans hsrc
    · have hRule := (bulkReanchor_rule_iff m 50 (bulkEdgeStartIndex F) 26 _ p.val
        (by omega) (by decide) hbox).mpr hp.2.1.2.1
      rw [bulkVertexReanchor_candidate m 50 F (bulkFarZNearT j) odd d hOne (by decide), hroot] at hRule
      have htgt := congrArg (bulkReanchorSite 50 m (bulkEdgeStartIndex F))
        (bulkFarZNear_negative_target F j hNeg _ hRule)
      rw [bulkReanchorSite_inverse] at htgt
      let hf : BulkFarZAscendingFrame F 3 := Or.inr ⟨hNeg, by decide⟩
      refine ⟨3, hf, Subtype.ext ?_⟩
      exact htgt

theorem bulkFarZNear_endpoint_escape (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (j : Fin 3)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (hZ : BulkZEdgeFrame F)
    (hd : bulkEdgeCandidate m F (bulkFarZNearT j) odd d hOne ∈ bulkDamaged m) (p : BulkVertex m)
    (hp : p.val = bulkEdgeCandidate m F (bulkFarZNearT j) odd d hOne ∨
      bulkMerge m (bulkEdgeCandidate m F (bulkFarZNearT j) odd d hOne) p.val) :
    ∃ q : BulkVertex m, (bulkFiniteGraph m).Reachable p q ∧
      bulkSegmentPotential m p < bulkSegmentPotential m q := by
  obtain ⟨i, hf, rfl⟩ := bulkFarZNear_endpoint_view m hm F j odd d hOne hZ hd p hp
  exact ⟨bulkFarZNearView m hm F j (bulkFarZTo i) (bulkFarZ_to_family F i hf),
    bulkFarZNear_ascent_reachable m hm F j i hf, bulkFarZNear_ascent_potential m hm F j i hf⟩

end ProteinFolding.Tetrahedral
