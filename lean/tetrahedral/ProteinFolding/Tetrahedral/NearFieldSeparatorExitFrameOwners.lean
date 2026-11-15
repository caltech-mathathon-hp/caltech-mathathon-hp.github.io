import ProteinFolding.Tetrahedral.NearFieldFramePortMetadata
import ProteinFolding.Tetrahedral.NearFieldDimerHsiteIndices

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 100000

theorem separatorExit_excludes_frameH (p : ConstructionParameters) (k : ℕ)
    (f : ℕ) (kind : Fin 6) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side)
    (hslot : kind = 4 → f % 10 = 5) (last : Bool) :
    (if last then frameEndH p.side f kind else frameStartH p.side f kind) ∉
      edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have ht := p.exit_column_triangle_room k
  have ha := framePortMetadata_exit_allowed p k f kind last hfhi hslot
  rw [frameEndpoint_eq_metadata]
  apply interpretFramePort_not_mem
    (octEdgeZigzag p.side entryEdgeFrame) (octEdgeZigzag p.side exitEdgeFrame)
    (framePortMetadata p.side f kind last)
  · intro hb
    have hr : (framePortMetadata p.side f kind last).2 < 2 * p.side - 1 := by
      simpa only [hb, Bool.false_eq_true, if_false] using ha
    exact edgeDimerHsites_not_mem_other_pair hm exitEdgeFrame (10 * p.exitSlot k + 6) 2
      (by omega) (by omega) entryEdgeFrame _ hr (Or.inl (by decide))
  · intro hb
    have hi : ∀ t, t < 6 → 10 * p.exitSlot k + 6 + t ≠ (framePortMetadata p.side f kind last).2 := by
      simpa only [hb, ite_true] using ha
    exact edgeDimerHsites_not_mem_of_indices (by omega : 1 ≤ p.side) exitEdgeFrame (10 * p.exitSlot k + 6) 2 _ hi

end ProteinFolding.Tetrahedral.NearField

