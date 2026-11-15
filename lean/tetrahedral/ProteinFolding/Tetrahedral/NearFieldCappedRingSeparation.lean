import ProteinFolding.Tetrahedral.NearFieldRingCaps
import ProteinFolding.Tetrahedral.NearFieldRingForeignColumns

/-! Whole capped rings on different small faces are pairwise disjoint.
The proof includes body/body, cap/body and cap/cap separation. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem cappedRingFolds_disjoint_small_faces (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j) (C D C' D' : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (hC' : C'.owner = ringTerminalSite m G 0 0) (hD' : D'.owner = ringTerminalSite m G 2 1) :
    Disjoint (foldSites (cappedRingFold m hm heven F C D hC hD))
      (foldSites (cappedRingFold m hm heven G C' D' hC' hD')) := by
  have hcap (X Y : DanglingColumn m)
      (hX : X.owner = ringTerminalSite m F 0 0 ∨ X.owner = ringTerminalSite m F 2 1)
      (hY : Y.owner = ringTerminalSite m G 0 0 ∨ Y.owner = ringTerminalSite m G 2 1) :
      X.seed ≠ Y.seed := ringTerminalColumns_seeds_ne m hm F G hj X Y hX hY
  rw [cappedRingFold_sites, cappedRingFold_sites]
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  simp only [Finset.mem_union, Finset.mem_singleton] at hp hp'
  rcases hp with (rfl | hp) | rfl
  · rcases hp' with (h | hp') | h
    · exact hcap C C' (Or.inl hC) (Or.inl hC') h
    · obtain ⟨i, hi⟩ := (mem_foldSites _ _).mp hp'
      exact ringFold_ne_foreign_terminal_column m hm heven G F hj.symm C (Or.inl hC) i 0 hi
    · exact hcap C D' (Or.inl hC) (Or.inr hD') h
  · obtain ⟨i, rfl⟩ := (mem_foldSites _ _).mp hp
    rcases hp' with (h | hp') | h
    · exact ringFold_ne_foreign_terminal_column m hm heven F G hj C' (Or.inl hC') i 0 h
    · obtain ⟨j, hj'⟩ := (mem_foldSites _ _).mp hp'
      exact ringFolds_disjoint_small_faces m (by omega) heven F G hj i j hj'.symm
    · exact ringFold_ne_foreign_terminal_column m hm heven F G hj D' (Or.inr hD') i 0 h
  · rcases hp' with (h | hp') | h
    · exact hcap D C' (Or.inr hD) (Or.inl hC') h
    · obtain ⟨i, hi⟩ := (mem_foldSites _ _).mp hp'
      exact ringFold_ne_foreign_terminal_column m hm heven G F hj.symm D (Or.inr hD) i 0 hi
    · exact hcap D D' (Or.inr hD) (Or.inr hD') h

end ProteinFolding.Tetrahedral.NearField
