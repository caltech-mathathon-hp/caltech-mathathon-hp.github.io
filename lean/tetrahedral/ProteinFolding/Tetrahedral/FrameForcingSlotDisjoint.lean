import ProteinFolding.Tetrahedral.FrameForcingConfiguration

/-! Entry slots, exit slots, and the two slot families are pairwise disjoint. -/

namespace ProteinFolding.Tetrahedral

theorem interior_edgeBlock_disjoint_other_edge (m : ℕ) (hm : 3 ≤ m)
    (F G : OctEdgeFrame) (hdistinct : F.k ≠ G.k) (a n b t : ℕ)
    (hlo : 2 ≤ a) (hhi : a + n + 1 ≤ 2 * m - 2) (hother : b + t ≤ 2 * m - 1) :
    Disjoint (edgeBlock m F a n) (edgeBlock m G b t) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hy
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have hG := octEdgeZigzag_mem (by omega : 1 ≤ m) G (by omega : b + j < 2 * m - 1)
  rw [heq] at hG
  have hid := inner_edge_unique_faces m hm F (a + i) (by omega) (by omega) hG
  exact hdistinct hid.1.symm

namespace ConstructionParameters

theorem entry_slot_disjoint (p : ConstructionParameters) (F : OctEdgeFrame) (k l : ℕ) (hkl : k ≠ l) :
    Disjoint (edgeBlock p.side F (6 * k) 2) (edgeBlock p.side F (6 * l) 2) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hy
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hindex := octEdgeZigzag_injective hm F heq
  exact hkl (by omega)

theorem exit_slot_disjoint (p : ConstructionParameters) (F : OctEdgeFrame) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hkl : k ≠ l) :
    Disjoint (edgeBlock p.side F (2 * p.side - (10 * k + 13)) 6)
      (edgeBlock p.side F (2 * p.side - (10 * l + 13)) 6) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hy
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have hfamily := p.family_side_bound
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hindex := octEdgeZigzag_injective hm F heq
  exact hkl (by omega)

theorem forced_family_entry_exit_disjoint (p : ConstructionParameters) (H : Finset Site)
    (F : ForcedFrameFamily p.side H p.frameGaps1 p.frameGaps2)
    (k l : ℕ) (hklo : 1 ≤ k) (hkhi : k ≤ p.bins + 1) (hl : l ≤ p.bins) :
    Disjoint (edgeBlock p.side F.first (6 * k) 2)
      (edgeBlock p.side F.second (2 * p.side - (10 * l + 13)) 6) := by
  have hm := p.side_ge
  have hfamily := p.family_side_bound
  exact interior_edgeBlock_disjoint_other_edge p.side (by omega) F.first F.second F.distinct
    (6 * k) 2 (2 * p.side - (10 * l + 13)) 6 (by omega) (by omega) (by omega)

end ConstructionParameters

end ProteinFolding.Tetrahedral
