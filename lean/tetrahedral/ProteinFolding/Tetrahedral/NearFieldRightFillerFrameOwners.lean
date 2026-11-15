import ProteinFolding.Tetrahedral.NearFieldCanonicalRightPiece
import ProteinFolding.Tetrahedral.NearFieldFramePortMetadata
import ProteinFolding.Tetrahedral.NearFieldInnerEdgeSeparation
import ProteinFolding.Tetrahedral.NearFieldFrameHRunHoles
import ProteinFolding.Tetrahedral.NearFieldFrameCoreEndpoints

/-! The right filler ends at exit[1], the omitted B site of the last corner. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

def rightFillerHsites (p : ConstructionParameters) : Finset Site :=
  edgeDimerHsites p.side trackEdgeFrame (rightFillerTrackBase p) (p.rightFiller - 1)

theorem rightFillerTrackBase_end (p : ConstructionParameters) :
    rightFillerTrackBase p + 2 * p.rightFiller = 2 * p.side - 2 := by
  have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
  dsimp [rightFillerTrackBase]
  omega

private theorem framePortMetadata_exit_one_gap (m f : ℕ) (hm : 3 ≤ m) (hf : 5 ≤ f)
    (kind : Fin 6) (last : Bool) :
    if (framePortMetadata m f kind last).1 then (framePortMetadata m f kind last).2 ≠ 1 else True := by
  fin_cases kind <;> cases last <;> norm_num [framePortMetadata, Fin.ext_iff] <;> omega

private theorem exit_one_ne_entry {m : ℕ} (hm : 3 ≤ m) (r : ℕ) :
    octEdgeZigzag m exitEdgeFrame 1 ≠ octEdgeZigzag m entryEdgeFrame r := by
  intro heq
  have hx := congrArg (fun x : Site => x.val 0) heq
  have hy := congrArg (fun x : Site => x.val 1) heq
  change (octEdgeZigzag m exitEdgeFrame 1).val 0 = (octEdgeZigzag m entryEdgeFrame r).val 0 at hx
  change (octEdgeZigzag m exitEdgeFrame 1).val 1 = (octEdgeZigzag m entryEdgeFrame r).val 1 at hy
  rw [exitEdgeZigzag_coordinates (by omega : 1 ≤ m), entryEdgeZigzag_coordinates (by omega : 1 ≤ m)] at hx hy
  dsimp [exitEdgeCoordinates, entryEdgeCoordinates, octRadius] at hx hy
  omega

theorem rightFiller_last_shared (p : ConstructionParameters) :
    octEdgeZigzag p.side trackEdgeFrame (2 * p.side - 3) = octEdgeZigzag p.side exitEdgeFrame 1 :=
  (rightFinalColumn_track_owner p).symm.trans (rightFinalColumn_exit_owner p)

theorem entryPoint_not_rightFillerHsites (p : ConstructionParameters) (r : ℕ) (hr : r < 2 * p.side - 1) :
    octEdgeZigzag p.side entryEdgeFrame r ∉ rightFillerHsites p := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  intro hx
  obtain ⟨t, _, heq⟩ := Finset.mem_image.mp hx
  have ht := t.isLt
  have hend := rightFillerTrackBase_end p
  have hn := p.rightFiller_ge
  have hlo : 2 ≤ rightFillerTrackBase p + t.val := by dsimp [rightFillerTrackBase]; omega
  have hhi : rightFillerTrackBase p + t.val ≤ 2 * p.side - 3 := by omega
  by_cases hlast : rightFillerTrackBase p + t.val = 2 * p.side - 3
  · rw [hlast, rightFiller_last_shared] at heq
    exact exit_one_ne_entry hm r heq
  · exact innerEdgePoint_ne_other_pair hm trackEdgeFrame _ hlo (by omega)
      entryEdgeFrame r hr (Or.inl (by decide)) heq

theorem exitPoint_not_rightFillerHsites (p : ConstructionParameters) (r : ℕ)
    (hr : r < 2 * p.side - 1) (hr1 : r ≠ 1) :
    octEdgeZigzag p.side exitEdgeFrame r ∉ rightFillerHsites p := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  intro hx
  obtain ⟨t, _, heq⟩ := Finset.mem_image.mp hx
  have ht := t.isLt
  have hend := rightFillerTrackBase_end p
  have hn := p.rightFiller_ge
  have hlo : 2 ≤ rightFillerTrackBase p + t.val := by dsimp [rightFillerTrackBase]; omega
  have hhi : rightFillerTrackBase p + t.val ≤ 2 * p.side - 3 := by omega
  by_cases hlast : rightFillerTrackBase p + t.val = 2 * p.side - 3
  · rw [hlast, rightFiller_last_shared] at heq
    exact hr1 (octEdgeZigzag_injective (by omega) exitEdgeFrame heq).symm
  · exact innerEdgePoint_ne_other_pair hm trackEdgeFrame _ hlo (by omega)
      exitEdgeFrame r hr (Or.inl (by decide)) heq

theorem rightFiller_excludes_frameH (p : ConstructionParameters) (f : ℕ) (kind : Fin 6)
    (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side) (last : Bool) :
    (if last then frameEndH p.side f kind else frameStartH p.side f kind) ∉ rightFillerHsites p := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have hi := framePortMetadata_index_lt p.side f hm kind last hfhi
  have hgap := framePortMetadata_exit_one_gap p.side f hm hflo kind last
  rw [frameEndpoint_eq_metadata]
  apply interpretFramePort_not_mem (octEdgeZigzag p.side entryEdgeFrame)
    (octEdgeZigzag p.side exitEdgeFrame) (framePortMetadata p.side f kind last)
  · intro _
    exact entryPoint_not_rightFillerHsites p _ hi
  · intro hb
    have hg : (framePortMetadata p.side f kind last).2 ≠ 1 := by simpa only [hb, ite_true] using hgap
    exact exitPoint_not_rightFillerHsites p _ hi hg

private theorem frameHRun_exit_one_gap (p : ConstructionParameters) (i : FrameHRunIndex p)
    (r : ℕ) (hr : r < (frameHRunData p i).count) (hexit : frameHRunOnExit i = true) :
    (frameHRunData p i).base + r ≠ 1 := by
  rcases i with c | ⟨b, u⟩
  · fin_cases c <;> dsimp [frameHRunData, frameHRunOnExit] at hr hexit ⊢
    all_goals first | contradiction | omega
  · cases b <;> dsimp [frameHRunData, frameHRunOnExit] at hr hexit ⊢
    · contradiction
    · omega

theorem frameHRunSite_not_rightFillerHsites (p : ConstructionParameters) (i : FrameHRunIndex p)
    (r : ℕ) (hr : r < (frameHRunData p i).count) :
    octEdgeZigzag p.side (frameHRunData p i).frame ((frameHRunData p i).base + r) ∉ rightFillerHsites p := by
  have hroom := frameHRun_room p i
  have hidx : (frameHRunData p i).base + r < 2 * p.side - 1 := by omega
  rw [frameHRun_frame]
  cases hb : frameHRunOnExit i
  · simp only [hb, Bool.false_eq_true, if_false]
    exact entryPoint_not_rightFillerHsites p _ hidx
  · simp only [hb, ite_true]
    exact exitPoint_not_rightFillerHsites p _ hidx (frameHRun_exit_one_gap p i r hr hb)

theorem frameHRunFold_not_rightFillerHsites (p : ConstructionParameters) (i : FrameHRunIndex p)
    (s : Fin (frameHRunWord p i).length) : (frameHRunFold p i).pos s ∉ rightFillerHsites p := by
  have hpos := (mem_foldSites (frameHRunFold p i) _).mpr ⟨s, rfl⟩
  rw [frameHRunFold_sites] at hpos
  obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hpos
  intro hx
  rw [← heq] at hx
  exact frameHRunSite_not_rightFillerHsites p i r (Finset.mem_range.mp hr) hx

theorem frameEndpointColumn_not_rightFillerHsites (p : ConstructionParameters) (b : Bool) :
    (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).owner ∉ rightFillerHsites p := by
  change frameEndpointVertex p.side b ∉ rightFillerHsites p
  rw [frameEndpointVertex_eq_edge p b]
  cases b
  · change octEdgeZigzag p.side exitEdgeFrame 0 ∉ _
    exact exitPoint_not_rightFillerHsites p 0 (by have h := p.side_ge; omega) (by decide)
  · change octEdgeZigzag p.side entryEdgeFrame 0 ∉ _
    exact entryPoint_not_rightFillerHsites p 0 (by have h := p.side_ge; omega)

end ProteinFolding.Tetrahedral.NearField
