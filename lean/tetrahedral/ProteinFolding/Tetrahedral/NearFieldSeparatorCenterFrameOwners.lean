import ProteinFolding.Tetrahedral.NearFieldFramePortMetadata
import ProteinFolding.Tetrahedral.NearFieldDimerHsiteIndices

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 100000

theorem separatorCenter_excludes_frameH (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (f : ℕ) (kind : Fin 6) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side) (last : Bool) :
    (if last then frameEndH p.side f kind else frameStartH p.side f kind) ∉
      edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k) 1 := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have hlo := separatorIndex_ge_two p k
  have hroom := p.separator_room k hk
  have hfill := p.rightFiller_ge
  have hr := framePortMetadata_index_lt p.side f hm kind last hfhi
  rw [frameEndpoint_eq_metadata]
  apply interpretFramePort_not_mem
    (octEdgeZigzag p.side entryEdgeFrame) (octEdgeZigzag p.side exitEdgeFrame)
    (framePortMetadata p.side f kind last)
  · intro _
    exact edgeDimerHsites_not_mem_other_pair hm trackEdgeFrame (2 * p.separatorIndex k) 1
      (by omega) (by omega) entryEdgeFrame _ hr (Or.inl (by decide))
  · intro _
    exact edgeDimerHsites_not_mem_other_pair hm trackEdgeFrame (2 * p.separatorIndex k) 1
      (by omega) (by omega) exitEdgeFrame _ hr (Or.inl (by decide))

end ProteinFolding.Tetrahedral.NearField

