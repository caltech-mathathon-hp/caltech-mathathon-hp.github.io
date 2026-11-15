import ProteinFolding.Tetrahedral.NearFieldInnerEdgeSeparation

/-! Small opaque index-level interfaces for exclusion from complete dimer
H intervals. Their callers never compare expanded geometric walks. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgeDimerHsites_not_mem_of_indices {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (base q r : ℕ) (hindices : ∀ t, t < 2 * (q + 1) → base + t ≠ r) :
    octEdgeZigzag m F r ∉ edgeDimerHsites m F base q := by
  intro hp
  obtain ⟨t, _, heq⟩ := Finset.mem_image.mp hp
  exact hindices t.val t.isLt (octEdgeZigzag_injective hm F heq)

theorem edgeDimerHsites_not_mem_other_pair {m : ℕ} (hm : 3 ≤ m) (F : OctEdgeFrame)
    (base q : ℕ) (hlo : 2 ≤ base) (hhi : base + 2 * (q + 1) + 1 ≤ 2 * m - 2)
    (G : OctEdgeFrame) (r : ℕ) (hr : r < 2 * m - 1)
    (hpair : G.k ≠ F.k ∨ G.j ≠ F.j) :
    octEdgeZigzag m G r ∉ edgeDimerHsites m F base q := by
  intro hp
  obtain ⟨t, _, heq⟩ := Finset.mem_image.mp hp
  have ht := t.isLt
  exact innerEdgePoint_ne_other_pair hm F (base + t.val) (by omega) (by omega) G r hr hpair heq

end ProteinFolding.Tetrahedral.NearField
