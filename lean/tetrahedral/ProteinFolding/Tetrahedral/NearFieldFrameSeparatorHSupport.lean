import ProteinFolding.Tetrahedral.NearFieldFrameHRunHoles
import ProteinFolding.Tetrahedral.NearFieldDimerHsiteIndices
import ProteinFolding.Tetrahedral.NearFieldSeparatorSupport

/-! Every retained frame H run avoids each separator's three H intervals. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

theorem frameHRunSite_ne_separatorEntry (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : FrameHRunIndex p) (r : ℕ) (hr : r < (frameHRunData p i).count) :
    octEdgeZigzag p.side (frameHRunData p i).frame ((frameHRunData p i).base + r) ∉
      edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0 := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have ht := p.entry_column_triangle_room k hk
  have hroom := frameHRun_room p i
  rw [frameHRun_frame]
  cases hb : frameHRunOnExit i
  · simp only [hb, Bool.false_eq_true, if_false]
    exact edgeDimerHsites_not_mem_of_indices (by omega) entryEdgeFrame _ _ _
      (fun t ht => (frameHRun_entry_separator_gap p k hk i r hr hb t (by simpa using ht)).symm)
  · simp only [hb, ite_true]
    exact edgeDimerHsites_not_mem_other_pair hm entryEdgeFrame _ _ (by omega) (by omega)
      exitEdgeFrame _ (by omega) (Or.inl (by decide))

theorem frameHRunSite_ne_separatorCenter (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : FrameHRunIndex p) (r : ℕ) (hr : r < (frameHRunData p i).count) :
    octEdgeZigzag p.side (frameHRunData p i).frame ((frameHRunData p i).base + r) ∉
      edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k) 1 := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have hlo := separatorIndex_ge_two p k
  have hspace := p.separator_room k hk
  have hfill := p.rightFiller_ge
  have hroom := frameHRun_room p i
  have hpair : (frameHRunData p i).frame.k ≠ trackEdgeFrame.k := by
    rw [frameHRun_frame]
    cases hb : frameHRunOnExit i <;> simp [hb, entryEdgeFrame, exitEdgeFrame, trackEdgeFrame]
  exact edgeDimerHsites_not_mem_other_pair hm trackEdgeFrame _ _ (by omega) (by omega)
    _ _ (by omega) (Or.inl hpair)

theorem frameHRunSite_ne_separatorExit (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : FrameHRunIndex p) (r : ℕ) (hr : r < (frameHRunData p i).count) :
    octEdgeZigzag p.side (frameHRunData p i).frame ((frameHRunData p i).base + r) ∉
      edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have ht := p.exit_column_triangle_room k
  have hroom := frameHRun_room p i
  rw [frameHRun_frame]
  cases hb : frameHRunOnExit i
  · simp only [hb, Bool.false_eq_true, if_false]
    exact edgeDimerHsites_not_mem_other_pair hm exitEdgeFrame _ _ (by omega) (by omega)
      entryEdgeFrame _ (by omega) (Or.inl (by decide))
  · simp only [hb, ite_true]
    exact edgeDimerHsites_not_mem_of_indices (by omega) exitEdgeFrame _ _ _
      (fun t ht => (frameHRun_exit_separator_gap p k hk i r hr hb t (by simpa using ht)).symm)

theorem frameHRunFold_disjoint_separator_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : FrameHRunIndex p) :
    Disjoint (foldSites (frameHRunFold p i)) (hSupport (p.separatorWord k) (separatorFold p k hk)) := by
  rw [frameHRunFold_sites, separatorFold_hSupport]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hx
  have hrt := Finset.mem_range.mp hr
  rw [← heq] at hy
  rcases Finset.mem_union.mp hy with hy | hy
  · rcases Finset.mem_union.mp hy with hy | hy
    · exact frameHRunSite_ne_separatorEntry p k hk i r hrt hy
    · exact frameHRunSite_ne_separatorCenter p k hk i r hrt hy
  · exact frameHRunSite_ne_separatorExit p k hk i r hrt hy

end ProteinFolding.Tetrahedral.NearField
