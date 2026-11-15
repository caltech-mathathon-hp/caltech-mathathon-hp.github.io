import ProteinFolding.Tetrahedral.NearFieldHRunReverse
import ProteinFolding.Tetrahedral.NearFieldWordPieceAssembly
import ProteinFolding.Tetrahedral.FrameWord
import ProteinFolding.Tetrahedral.OctahedralTrackGeometry

/-! Every retained H-run of the literal frame, with its exact direction and endpoints. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

abbrev FrameHRunIndex (p : ConstructionParameters) := Fin 5 ⊕ (Bool × Fin (p.bins + 1))

structure FrameHRunDescription where
  frame : OctEdgeFrame
  base : ℕ
  count : ℕ
  reversed : Bool

def frameHRunData (p : ConstructionParameters) : FrameHRunIndex p → FrameHRunDescription
  | .inl c =>
      if c = 0 then ⟨entryEdgeFrame, 0, 1, false⟩
      else if c = 1 then ⟨entryEdgeFrame, 3, 3, false⟩
      else if c = 2 then ⟨entryEdgeFrame, 2 * p.side - 2, 1, false⟩
      else if c = 3 then ⟨exitEdgeFrame, 10 * p.bins + 12, p.frameTail2, true⟩
      else ⟨exitEdgeFrame, 0, 1, false⟩
  | .inr (false, t) => ⟨entryEdgeFrame, 6 * t.val + 8, if t.val = p.bins then p.frameTail1 else 4, false⟩
  | .inr (true, t) => ⟨exitEdgeFrame, 10 * t.val + 2, 4, true⟩

theorem frameHRun_count_pos (p : ConstructionParameters) (i : FrameHRunIndex p) :
    0 < (frameHRunData p i).count := by
  have h1 := p.frameTail1_ge_three
  have h2 := p.frameTail2_ge_three
  rcases i with c | ⟨b, t⟩
  · fin_cases c <;> dsimp [frameHRunData] <;> omega
  · cases b <;> dsimp only [frameHRunData]
    · split_ifs <;> omega
    · omega

theorem frameHRun_room (p : ConstructionParameters) (i : FrameHRunIndex p) :
    (frameHRunData p i).base + (frameHRunData p i).count ≤ 2 * p.side - 1 := by
  have h1 := p.frameTail1_add
  have h2 := p.frameTail2_add
  have hm := p.side_ge
  have hf := p.family_side_bound
  rcases i with c | ⟨b, t⟩
  · fin_cases c <;> dsimp [frameHRunData] <;> omega
  · have ht := t.isLt
    cases b <;> dsimp only [frameHRunData]
    · split_ifs <;> omega
    · omega

def frameHRunWord (p : ConstructionParameters) (i : FrameHRunIndex p) : Sequence :=
  List.replicate (frameHRunData p i).count .H

def frameHRunFold (p : ConstructionParameters) (i : FrameHRunIndex p) :
    Fold tetrahedralLattice (frameHRunWord p i).length :=
  if (frameHRunData p i).reversed then
    (edgeHRunFold (m := p.side) (by have h := p.side_ge; omega) (frameHRunData p i).frame
      (frameHRunData p i).base (frameHRunData p i).count).reverse
  else edgeHRunFold (m := p.side) (by have h := p.side_ge; omega) (frameHRunData p i).frame
    (frameHRunData p i).base (frameHRunData p i).count

def frameHRunFirst (p : ConstructionParameters) (i : FrameHRunIndex p) : Site :=
  octEdgeZigzag p.side (frameHRunData p i).frame
    (if (frameHRunData p i).reversed then (frameHRunData p i).base + ((frameHRunData p i).count - 1)
     else (frameHRunData p i).base)

def frameHRunLast (p : ConstructionParameters) (i : FrameHRunIndex p) : Site :=
  octEdgeZigzag p.side (frameHRunData p i).frame
    (if (frameHRunData p i).reversed then (frameHRunData p i).base
     else (frameHRunData p i).base + ((frameHRunData p i).count - 1))

def frameHRunPiece (p : ConstructionParameters) (i : FrameHRunIndex p) : PositionedWord where
  word := frameHRunWord p i
  fold := frameHRunFold p i
  length_pos := by simpa only [frameHRunWord, List.length_replicate] using frameHRun_count_pos p i
  first := frameHRunFirst p i
  last := frameHRunLast p i
  first_eq r hr := by
    cases hb : (frameHRunData p i).reversed
    · simpa only [frameHRunFold, frameHRunFirst, hb, Bool.false_eq_true, if_false] using
        edgeHRunFold_first (m := p.side) (by have h := p.side_ge; omega) _ _ _ r hr
    · simpa only [frameHRunFold, frameHRunFirst, hb, ite_true] using
        edgeHRunFold_reverse_first (m := p.side) (by have h := p.side_ge; omega) _ _ _ r hr
  last_eq r hr := by
    cases hb : (frameHRunData p i).reversed
    · simpa only [frameHRunFold, frameHRunLast, hb, Bool.false_eq_true, if_false] using
        edgeHRunFold_last (m := p.side) (by have h := p.side_ge; omega) _ _ _ r hr
    · simpa only [frameHRunFold, frameHRunLast, hb, ite_true] using
        edgeHRunFold_reverse_last (m := p.side) (by have h := p.side_ge; omega) _ _ _ r hr

theorem frameHRunFold_sites (p : ConstructionParameters) (i : FrameHRunIndex p) :
    foldSites (frameHRunFold p i) =
      edgeBlock p.side (frameHRunData p i).frame (frameHRunData p i).base (frameHRunData p i).count := by
  cases hb : (frameHRunData p i).reversed <;> simp only [frameHRunFold, hb, Bool.false_eq_true, if_false, ite_true]
  · exact edgeHRunFold_sites _ _ _ _
  · rw [foldSites_reverse]
    exact edgeHRunFold_sites _ _ _ _

end ProteinFolding.Tetrahedral.NearField
