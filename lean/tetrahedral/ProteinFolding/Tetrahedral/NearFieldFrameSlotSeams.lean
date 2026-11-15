import ProteinFolding.Tetrahedral.NearFieldFramePieces
import Mathlib.Data.List.Chain

/-! Every adjacent retained run and literal P-link has its actual lattice seam. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem frameSlot_internal_seam (p : ConstructionParameters) (b : Bool) (t : Fin (p.bins + 1)) :
    tetrahedralLattice.Adj (frameLinkPiece p (.inr (b, t))).last
      (frameHRunPiece p (.inr (b, t))).first := by
  have h := frameLinkPiece_last_seam p (.inr (b, t))
  suffices he :
      octEdgeZigzag p.side (nearFrameRouteFrame (frameLinkKind (p := p) (.inr (b, t))))
        (nearFrameEndIndex p.side (frameLinkParameter (p := p) (.inr (b, t))) (frameLinkKind (p := p) (.inr (b, t)))) =
      (frameHRunPiece p (.inr (b, t))).first by
    rw [he] at h
    exact h
  cases b
  · rfl
  · change octEdgeZigzag p.side exitEdgeFrame (10 * t.val + 5) =
      octEdgeZigzag p.side exitEdgeFrame (10 * t.val + 2 + (4 - 1))
    congr 1

theorem frameEntrySlots_seam (p : ConstructionParameters) (t u : Fin (p.bins + 1))
    (htu : t.val + 1 = u.val) :
    tetrahedralLattice.Adj (frameHRunPiece p (.inr (false, t))).last
      (frameLinkPiece p (.inr (false, u))).first := by
  have ht : t.val ≠ p.bins := by have hu := u.isLt; omega
  have h := frameLinkPiece_first_seam p (.inr (false, u))
  convert h using 1
  change octEdgeZigzag p.side entryEdgeFrame
      (6 * t.val + 8 + ((if t.val = p.bins then p.frameTail1 else 4) - 1)) =
    octEdgeZigzag p.side entryEdgeFrame (6 * u.val + 5)
  rw [if_neg ht]
  congr 1
  omega

theorem frameExitSlots_seam (p : ConstructionParameters) (t u : Fin (p.bins + 1))
    (htu : u.val + 1 = t.val) :
    tetrahedralLattice.Adj (frameHRunPiece p (.inr (true, t))).last
      (frameLinkPiece p (.inr (true, u))).first := by
  have h := frameLinkPiece_first_seam p (.inr (true, u))
  convert h using 1
  change octEdgeZigzag p.side exitEdgeFrame (10 * t.val + 2) =
    octEdgeZigzag p.side exitEdgeFrame (10 * u.val + 5 + 7)
  congr 1
  omega

theorem piecesSeams_iff_isChain (ps : List PositionedWord) :
    piecesSeams ps ↔ ps.IsChain (fun a b => tetrahedralLattice.Adj a.last b.first) := by
  induction ps using List.twoStepInduction with
  | nil => simp [piecesSeams]
  | singleton a => simp [piecesSeams]
  | cons_cons a b ps _ ih => simp only [piecesSeams, List.isChain_cons_cons, ih b]

theorem pairedPieces_seams {α : Type*} (xs : List α) (a b : α → PositionedWord)
    (hab : ∀ x, tetrahedralLattice.Adj (a x).last (b x).first)
    (hnext : xs.IsChain (fun x y => tetrahedralLattice.Adj (b x).last (a y).first)) :
    piecesSeams (xs.flatMap (fun x => [a x, b x])) := by
  revert hnext
  induction xs using List.twoStepInduction with
  | nil => intro _; trivial
  | singleton x => intro _; exact ⟨hab x, trivial⟩
  | cons_cons x y xs _ ih =>
    intro hnext
    have hh := List.isChain_cons_cons.mp hnext
    exact ⟨hab x, hh.1, ih y hh.2⟩

end ProteinFolding.Tetrahedral.NearField
