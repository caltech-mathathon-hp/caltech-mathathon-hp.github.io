import ProteinFolding.Tetrahedral.BulkFarZAscent
import ProteinFolding.Tetrahedral.BulkFarZRecognition

/-! Uniform strict escape for actual class-Z merge endpoints away from
the bounded transition range. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkFarZ_endpoint_view (m t : ℕ) (F : OctEdgeFrame) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) (ht : 13 ≤ t) (htm : t + 14 ≤ m) (hZ : BulkZEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m) (p : BulkVertex m)
    (hp : p.val = bulkEdgeCandidate m F t odd d hm ∨ bulkMerge m (bulkEdgeCandidate m F t odd d hm) p.val) :
    ∃ (i : Fin 4) (hf : BulkFarZAscendingFrame F i),
      p = bulkFarZView m t F (bulkFarZFrom i) ht htm (bulkFarZ_from_family F i hf) := by
  have hbox := bulkEdgeCandidate_in_box m F t odd d hm
  have hDm := (bulkEdgeReanchor_damaged_iff m 27 t 13 F 2 (bulkEdgeCandidate m F t odd d hm)
    (by omega) (by omega) (by decide) (by decide) hbox).mpr hd
  rw [bulkEdgeReanchor_candidate m 27 t 13 F odd d hm (by decide)] at hDm
  have href := bulkFarZ_reference_source F odd d hZ ((bulkDamaged_fast_iff 27 _).mp hDm)
  rcases href with ⟨hPos, hroot⟩ | ⟨hNeg, hroot⟩
  · rcases hp with hp | hp
    · have hsrc := congrArg (bulkEdgeReanchor 27 m 13 t F) hroot
      rw [bulkEdgeReanchor_candidate 27 m 13 t F odd d (by decide) hm] at hsrc
      let hf : BulkFarZAscendingFrame F 0 := Or.inl ⟨hPos, by decide⟩
      refine ⟨0, hf, Subtype.ext ?_⟩
      change p.val = bulkEdgeReanchor 27 m 13 t F (bulkFarZRoot 0)
      exact hp.trans hsrc
    · have hRule := (bulkEdgeReanchor_rule_iff m 27 t 13 F 2 _ p.val
        (by omega) (by omega) (by decide) (by decide) hbox).mpr hp.2.1.2.1
      rw [bulkEdgeReanchor_candidate m 27 t 13 F odd d hm (by decide), hroot] at hRule
      have htgt := congrArg (bulkEdgeReanchor 27 m 13 t F)
        (bulkFarZ_rule_positive_target _ hRule)
      rw [bulkEdgeReanchor_inverse] at htgt
      let hf : BulkFarZAscendingFrame F 1 := Or.inl ⟨hPos, by decide⟩
      refine ⟨1, hf, Subtype.ext ?_⟩
      exact htgt
  · rcases hp with hp | hp
    · have hsrc := congrArg (bulkEdgeReanchor 27 m 13 t F) hroot
      rw [bulkEdgeReanchor_candidate 27 m 13 t F odd d (by decide) hm] at hsrc
      let hf : BulkFarZAscendingFrame F 2 := Or.inr ⟨hNeg, by decide⟩
      refine ⟨2, hf, Subtype.ext ?_⟩
      change p.val = bulkEdgeReanchor 27 m 13 t F (bulkFarZRoot 3)
      exact hp.trans hsrc
    · have hRule := (bulkEdgeReanchor_rule_iff m 27 t 13 F 2 _ p.val
        (by omega) (by omega) (by decide) (by decide) hbox).mpr hp.2.1.2.1
      rw [bulkEdgeReanchor_candidate m 27 t 13 F odd d hm (by decide), hroot] at hRule
      have htgt := congrArg (bulkEdgeReanchor 27 m 13 t F)
        (bulkFarZ_rule_negative_target _ hRule)
      rw [bulkEdgeReanchor_inverse] at htgt
      let hf : BulkFarZAscendingFrame F 3 := Or.inr ⟨hNeg, by decide⟩
      refine ⟨3, hf, Subtype.ext ?_⟩
      exact htgt

theorem bulkFarZ_endpoint_escape (m t : ℕ) (F : OctEdgeFrame) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) (ht : 13 ≤ t) (htm : t + 14 ≤ m) (hZ : BulkZEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m) (p : BulkVertex m)
    (hp : p.val = bulkEdgeCandidate m F t odd d hm ∨ bulkMerge m (bulkEdgeCandidate m F t odd d hm) p.val) :
    ∃ q : BulkVertex m, (bulkFiniteGraph m).Reachable p q ∧
      bulkSegmentPotential m p < bulkSegmentPotential m q := by
  obtain ⟨i, hf, rfl⟩ := bulkFarZ_endpoint_view m t F odd d hm ht htm hZ hd p hp
  exact ⟨bulkFarZView m t F (bulkFarZTo i) ht htm (bulkFarZ_to_family F i hf),
    bulkFarZ_ascent_reachable m t F i ht htm hf, bulkFarZ_ascent_potential m t F i ht htm hf⟩

end ProteinFolding.Tetrahedral
