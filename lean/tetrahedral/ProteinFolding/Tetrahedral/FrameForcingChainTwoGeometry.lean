import ProteinFolding.Tetrahedral.FrameForcingLocalDimer
import ProteinFolding.Tetrahedral.FrameForcingHeightBounds

/-! Opaque local geometry facts for a two-dimer chain, avoiding repeated
unfolding of the enclosing separator's dependent factor path. -/

namespace ProteinFolding.Tetrahedral.OctWordPath

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem chain2_deleted {m : ℕ} (Q : OctWordPath m (capWord (dimerChain 2))) :
    ∀ x ∈ ({Q.site 1, Q.site 2, Q.site 6, Q.site 7} : Finset Site), bulkOnDeletedEdge m x := by
  obtain ⟨k, t, hkt, hleft, hright⟩ := Q.dimer_on_edge 0 (capped_dimer_start 2 0 (by decide))
  obtain ⟨k', t', hkt', hleft', hright'⟩ := Q.dimer_on_edge 5 (capped_dimer_start 2 1 (by decide))
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨k, t, hkt, hleft⟩
  · exact ⟨k, t, hkt, hright⟩
  · exact ⟨k', t', hkt', hleft'⟩
  · exact ⟨k', t', hkt', hright'⟩

theorem chain2_height_bounds {m : ℕ} (Q : OctWordPath m (capWord (dimerChain 2))) (F : OctEdgeFrame) :
    (∀ x ∈ ({Q.site 1, Q.site 2, Q.site 6, Q.site 7} : Finset Site),
      -8 ≤ frameH2 m F x - frameH2 m F (Q.site 1) ∧
      frameH2 m F x - frameH2 m F (Q.site 1) ≤ 8 ∧
      -8 ≤ frameH2 m F x - frameH2 m F (Q.site 7) ∧
      frameH2 m F x - frameH2 m F (Q.site 7) ≤ 8) ∧
    (∀ x ∈ ({Q.site 1, Q.site 2, Q.site 6, Q.site 7} : Finset Site),
      -8 ≤ frameK2 m F x - frameK2 m F (Q.site 1) ∧
      frameK2 m F x - frameK2 m F (Q.site 1) ≤ 8 ∧
      -8 ≤ frameK2 m F x - frameK2 m F (Q.site 7) ∧
      frameK2 m F x - frameK2 m F (Q.site 7) ≤ 8) := by
  have hadj₁ := Q.adjacent 1 (by decide)
  have hadj₂ := Q.adjacent 6 (by decide)
  have hlink : OctTriangularNeighbours m (Q.site 2) (Q.site 6) := by
    obtain ⟨hH₀, hH₄, hP⟩ := capped_dimer_P3 2 0 (by decide)
    exact exterior_P3_link_triangular m (Q.P3_link 2 (by decide) hH₀ hH₄ hP)
  exact ⟨quartet_height_bounds (frameH2 m F) _ _ _ _
      (frameH2_adj_bounds m F hadj₁) (frameH2_triangular_bounds m F hlink) (frameH2_adj_bounds m F hadj₂),
    quartet_height_bounds (frameK2 m F) _ _ _ _
      (frameK2_adj_bounds m F hadj₁) (frameK2_triangular_bounds m F hlink) (frameK2_adj_bounds m F hadj₂)⟩

end ProteinFolding.Tetrahedral.OctWordPath
