import ProteinFolding.Tetrahedral.NearFieldDimerChainDisjoint
import ProteinFolding.Tetrahedral.FrameForcingSlotGeometry

/-! Inner edge sites determine their normal pair, uniformly in both endpoints. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem innerEdgePoint_ne_other_pair {m : ℕ} (hm : 3 ≤ m) (F : OctEdgeFrame)
    (i : ℕ) (hilo : 2 ≤ i) (hihi : i + 2 ≤ 2 * m - 2)
    (G : OctEdgeFrame) (r : ℕ) (hr : r < 2 * m - 1)
    (hpair : G.k ≠ F.k ∨ G.j ≠ F.j) : octEdgeZigzag m F i ≠ octEdgeZigzag m G r := by
  intro heq
  have he := octEdgeZigzag_mem (by omega : 1 ≤ m) G hr
  rw [← heq] at he
  have hfaces := inner_edge_unique_faces m hm F i hilo hihi he
  rcases hpair with h | h
  · exact h hfaces.1
  · exact h hfaces.2

theorem edgeDimerHsites_disjoint_other_pair {m : ℕ} (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (base q base' q' : ℕ) (hlo : 2 ≤ base)
    (hhi : base + 2 * (q + 1) + 1 ≤ 2 * m - 2)
    (hroom' : base' + 2 * (q' + 1) ≤ 2 * m - 1)
    (hpair : G.k ≠ F.k ∨ G.j ≠ F.j) :
    Disjoint (edgeDimerHsites m F base q) (edgeDimerHsites m G base' q') := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp'
  have hi := i.isLt
  have hjb := j.isLt
  exact innerEdgePoint_ne_other_pair hm F (base + i.val) (by omega) (by omega)
    G (base' + j.val) (by omega) hpair hj.symm

end ProteinFolding.Tetrahedral.NearField
