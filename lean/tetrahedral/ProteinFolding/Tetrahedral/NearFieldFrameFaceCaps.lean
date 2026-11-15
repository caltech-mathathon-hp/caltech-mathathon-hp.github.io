import ProteinFolding.Tetrahedral.NearFieldFrameSeparation
import ProteinFolding.Tetrahedral.FaceRowsColumns

/-! The only F' dangling caps used by the literal frame P-links. -/

namespace ProteinFolding.Tetrahedral

theorem entryEdgeZigzag_inB {m : ℕ} (hm : 1 ≤ m) (q : ℕ) (hq : q % 2 = 1) :
    InBSublattice (octEdgeZigzag m entryEdgeFrame q).val := by
  have he : q = 2 * (q / 2) + 1 := by omega
  rw [he]
  exact (octEdgeZigzag_odd hm entryEdgeFrame (q / 2)).1

theorem exitEdgeZigzag_inB {m : ℕ} (hm : 1 ≤ m) (q : ℕ) (hq : q % 2 = 1) :
    InBSublattice (octEdgeZigzag m exitEdgeFrame q).val := by
  have he : q = 2 * (q / 2) + 1 := by omega
  rw [he]
  exact (octEdgeZigzag_odd hm exitEdgeFrame (q / 2)).1

theorem nearFrame_initial_faceCap {m : ℕ} (hm : 1 ≤ m) (q : ℕ) (hq : q % 2 = 1) :
    nearFramePoint m q 0 hq ⟨6, by decide⟩ = step (octEdgeZigzag m entryEdgeFrame 3) 3 := by
  apply Subtype.ext
  rw [step_val_of_B _ (entryEdgeZigzag_inB hm 3 (by decide)), entryEdgeZigzag_coordinates hm]
  funext k
  rw [bondVector_eq_bondComponent]
  fin_cases k <;> dsimp [nearFramePoint, nearFrameCoordinates, nearFrameReference,
    nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, entryEdgeCoordinates, bondComponent] <;> omega

theorem nearFrame_twoSlot_faceCap {m : ℕ} (hm : 1 ≤ m) (q : ℕ) (hq : q % 2 = 1) :
    nearFramePoint m q 1 hq ⟨1, by decide⟩ = step (octEdgeZigzag m entryEdgeFrame q) 3 := by
  apply Subtype.ext
  rw [step_val_of_B _ (entryEdgeZigzag_inB hm q hq), entryEdgeZigzag_coordinates hm]
  funext k
  rw [bondVector_eq_bondComponent]
  fin_cases k <;> dsimp [nearFramePoint, nearFrameCoordinates, nearFrameReference,
    nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, entryEdgeCoordinates, bondComponent] <;> omega

theorem nearFrame_sixSlot_faceCap {m : ℕ} (hm : 1 ≤ m) (q : ℕ) (hq : q % 2 = 1) :
    nearFramePoint m q 4 hq ⟨10, by decide⟩ = step (octEdgeZigzag m exitEdgeFrame q) 3 := by
  apply Subtype.ext
  rw [step_val_of_B _ (exitEdgeZigzag_inB hm q hq), exitEdgeZigzag_coordinates hm]
  funext k
  rw [bondVector_eq_bondComponent]
  fin_cases k <;> dsimp [nearFramePoint, nearFrameCoordinates, nearFrameReference,
    nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, exitEdgeCoordinates, bondComponent] <;> omega

theorem nearFrame_initial_only_maxX (r : Fin (nearFrameLength 0))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 0)
    (hx : nearFrameOffset 0 r.val 0 = 2) : r.val = 6 := by
  revert r hr0 hrlast hx
  decide

theorem nearFrame_twoSlot_only_maxX (r : Fin (nearFrameLength 1))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 1)
    (hx : nearFrameOffset 1 r.val 0 = 1) : r.val = 1 := by
  revert r hr0 hrlast hx
  decide

theorem nearFrame_sixSlot_only_minZ (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hz : nearFrameOffset 4 r.val 2 = -1) : r.val = 10 := by
  revert r hr0 hrlast hz
  decide

end ProteinFolding.Tetrahedral
