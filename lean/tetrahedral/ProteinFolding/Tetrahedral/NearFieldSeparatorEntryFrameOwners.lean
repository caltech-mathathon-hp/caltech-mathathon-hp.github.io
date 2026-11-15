import ProteinFolding.Tetrahedral.NearFieldFramePortMetadata
import ProteinFolding.Tetrahedral.NearFieldDimerHsiteIndices

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 100000

theorem separatorEntry_excludes_frameH (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (f : ℕ) (kind : Fin 6) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side)
    (hslot : kind = 1 → f % 6 = 5) (last : Bool) :
    (if last then frameEndH p.side f kind else frameStartH p.side f kind) ∉
      edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0 := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have ht := p.entry_column_triangle_room k hk
  have ha := framePortMetadata_entry_allowed p k hk f kind last hfhi hslot
  rw [frameEndpoint_eq_metadata]
  apply interpretFramePort_not_mem
    (octEdgeZigzag p.side entryEdgeFrame) (octEdgeZigzag p.side exitEdgeFrame)
    (framePortMetadata p.side f kind last)
  · intro hb
    have hi : ∀ t, t < 2 → 6 * (k + 1) + t ≠ (framePortMetadata p.side f kind last).2 := by
      simpa only [hb, Bool.false_eq_true, if_false] using ha
    exact edgeDimerHsites_not_mem_of_indices (by omega : 1 ≤ p.side) entryEdgeFrame (6 * (k + 1)) 0 _ hi
  · intro hb
    have hr : (framePortMetadata p.side f kind last).2 < 2 * p.side - 1 := by
      simpa only [hb, ite_true] using ha
    exact edgeDimerHsites_not_mem_other_pair hm entryEdgeFrame (6 * (k + 1)) 0
      (by omega) (by omega) exitEdgeFrame _ hr (Or.inl (by decide))

end ProteinFolding.Tetrahedral.NearField

