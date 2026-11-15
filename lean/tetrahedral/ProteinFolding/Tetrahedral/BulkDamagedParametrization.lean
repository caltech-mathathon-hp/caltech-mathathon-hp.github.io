import ProteinFolding.Tetrahedral.BulkEdgeReversal
import ProteinFolding.Tetrahedral.BulkLocality

/-! Every damaged end is one of the finitely parametrised edge-neighbour families. -/

namespace ProteinFolding.Tetrahedral

theorem bulkEdge_complement_exists : ∀ k j : Fin 4, k ≠ j →
    ∃ a b : Fin 4, k ≠ a ∧ k ≠ b ∧ j ≠ a ∧ j ≠ b ∧ a ≠ b := by decide

theorem bulkDamaged_candidate_exists {m : ℕ} (hm : 1 ≤ m) (p : Site) (hd : p ∈ bulkDamaged m) :
    ∃ (F : OctEdgeFrame) (t : ℕ) (d : Fin 4),
      (t < m ∧ p = bulkEdgeCandidate m F t false d hm) ∨
      (t + 2 ≤ m ∧ p = bulkEdgeCandidate m F t true d hm) := by
  obtain ⟨e, he, hpe⟩ := bulkDamaged_has_deleted_neighbour m hd
  obtain ⟨k, j, hkj, hEdge⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨a, b, hka, hkb, hja, hjb, hab⟩ := bulkEdge_complement_exists k j hkj
  let F : OctEdgeFrame := ⟨k, j, a, b, hkj, hka, hkb, hja, hjb, hab⟩
  have hEdge' : OctEdgeSite m F.k F.j e := hEdge
  obtain ⟨r, hr, her⟩ := (octEdgeSite_iff_param hm F e).mp hEdge'
  obtain ⟨d, hstep⟩ := (adj_iff_exists_step e p).mp hpe.symm
  have hpr : p = step (octEdgeZigzag m F r) d := by rw [← her]; exact hstep.symm
  let t := r / 2
  by_cases hmod : r % 2 = 0
  · have heven : r = 2 * t := by dsimp [t]; omega
    refine ⟨F, t, d, Or.inl ⟨by omega, ?_⟩⟩
    rw [hpr, heven]
    simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor]
  · have hodd : r = 2 * t + 1 := by dsimp [t]; omega
    refine ⟨F, t, d, Or.inr ⟨by omega, ?_⟩⟩
    rw [hpr, hodd]
    simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor_next]

end ProteinFolding.Tetrahedral
