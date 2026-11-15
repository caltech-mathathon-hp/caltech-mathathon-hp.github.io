import ProteinFolding.Tetrahedral.NearFieldLeftFillerSupport
import ProteinFolding.Tetrahedral.NearFieldFramePortMetadata
import ProteinFolding.Tetrahedral.NearFieldInnerEdgeSeparation

/-! The first two entry H sites and the initial track interval are precisely
the frame holes occupied by the special left filler. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

private theorem framePortMetadata_initial_gap (m f : ℕ) (hm : 4 ≤ m) (hf : 5 ≤ f)
    (kind : Fin 6) (last : Bool) :
    if (framePortMetadata m f kind last).1 then True
    else (framePortMetadata m f kind last).2 ≠ 1 ∧ (framePortMetadata m f kind last).2 ≠ 2 := by
  fin_cases kind <;> cases last <;> norm_num [framePortMetadata, Fin.ext_iff] <;> omega

private theorem track_one_ne_exit {m : ℕ} (hm : 3 ≤ m) (r : ℕ) :
    octEdgeZigzag m trackEdgeFrame 1 ≠ octEdgeZigzag m exitEdgeFrame r := by
  intro heq
  have hx := congrArg (fun x : Site => x.val 0) heq
  have hy := congrArg (fun x : Site => x.val 1) heq
  change (octEdgeZigzag m trackEdgeFrame 1).val 0 = (octEdgeZigzag m exitEdgeFrame r).val 0 at hx
  change (octEdgeZigzag m trackEdgeFrame 1).val 1 = (octEdgeZigzag m exitEdgeFrame r).val 1 at hy
  rw [trackEdgeZigzag_coordinates (by omega : 1 ≤ m), exitEdgeZigzag_coordinates (by omega : 1 ≤ m)] at hx hy
  dsimp [trackEdgeCoordinates, exitEdgeCoordinates, octRadius] at hx hy
  omega

theorem entryPoint_not_leftFillerHsites (p : ConstructionParameters) (r : ℕ)
    (hr : r < 2 * p.side - 1) (hr1 : r ≠ 1) (hr2 : r ≠ 2) :
    octEdgeZigzag p.side entryEdgeFrame r ∉ leftFillerHsites p := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  intro hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · exact hr2 (octEdgeZigzag_injective (by omega) entryEdgeFrame hx)
  · have hne := (Finset.mem_erase.mp hx).1
    obtain ⟨t, _, heq⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hx).2
    have ht := t.isLt
    have htpos : 0 < t.val := by
      by_contra hn
      have ht0 : t.val = 0 := by omega
      exact hne (by simpa only [Nat.zero_add, ht0] using heq.symm)
    by_cases ht1 : t.val = 1
    · have hs := start_corner_shared p.side (by omega : 1 ≤ p.side) entryEdgeFrame
      change octEdgeZigzag p.side entryEdgeFrame 1 = octEdgeZigzag p.side trackEdgeFrame 1 at hs
      have he : octEdgeZigzag p.side trackEdgeFrame 1 = octEdgeZigzag p.side entryEdgeFrame r := by
        simpa only [Nat.zero_add, ht1] using heq
      exact hr1 (octEdgeZigzag_injective (by omega) entryEdgeFrame (hs.trans he)).symm
    · have hside := p.side_eq_track
      exact innerEdgePoint_ne_other_pair hm trackEdgeFrame t.val (by omega) (by omega)
        entryEdgeFrame r hr (Or.inl (by decide)) (by simpa only [Nat.zero_add] using heq)

theorem exitPoint_not_leftFillerHsites (p : ConstructionParameters) (r : ℕ)
    (hr : r < 2 * p.side - 1) : octEdgeZigzag p.side exitEdgeFrame r ∉ leftFillerHsites p := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  intro hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · exact innerEdgePoint_ne_other_pair hm entryEdgeFrame 2 (by omega) (by have h := p.side_ge; omega)
      exitEdgeFrame r hr (Or.inl (by decide)) hx.symm
  · have hne := (Finset.mem_erase.mp hx).1
    obtain ⟨t, _, heq⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hx).2
    have ht := t.isLt
    have htpos : 0 < t.val := by
      by_contra hn
      have ht0 : t.val = 0 := by omega
      exact hne (by simpa only [Nat.zero_add, ht0] using heq.symm)
    by_cases ht1 : t.val = 1
    · exact track_one_ne_exit hm r (by simpa only [Nat.zero_add, ht1] using heq)
    · have hside := p.side_eq_track
      exact innerEdgePoint_ne_other_pair hm trackEdgeFrame t.val (by omega) (by omega)
        exitEdgeFrame r hr (Or.inl (by decide)) (by simpa only [Nat.zero_add] using heq)

theorem leftFiller_excludes_frameH (p : ConstructionParameters) (f : ℕ) (kind : Fin 6)
    (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side) (last : Bool) :
    (if last then frameEndH p.side f kind else frameStartH p.side f kind) ∉ leftFillerHsites p := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have hi := framePortMetadata_index_lt p.side f hm kind last hfhi
  have hgap := framePortMetadata_initial_gap p.side f (by have h := p.side_ge; omega) hflo kind last
  rw [frameEndpoint_eq_metadata]
  apply interpretFramePort_not_mem (octEdgeZigzag p.side entryEdgeFrame)
    (octEdgeZigzag p.side exitEdgeFrame) (framePortMetadata p.side f kind last)
  · intro hb
    have hg : (framePortMetadata p.side f kind last).2 ≠ 1 ∧
        (framePortMetadata p.side f kind last).2 ≠ 2 := by
      simpa only [hb, Bool.false_eq_true, if_false] using hgap
    exact entryPoint_not_leftFillerHsites p _ hi hg.1 hg.2
  · intro _
    exact exitPoint_not_leftFillerHsites p _ hi

end ProteinFolding.Tetrahedral.NearField
