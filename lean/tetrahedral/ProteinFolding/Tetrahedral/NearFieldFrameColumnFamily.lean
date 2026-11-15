import ProteinFolding.Tetrahedral.NearFieldActualFrameFold
import ProteinFolding.Tetrahedral.NearFieldEntryCapFamily
import ProteinFolding.Tetrahedral.NearFieldExitCapFamily
import ProteinFolding.Tetrahedral.NearFieldCanonicalRings
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonColumns
import ProteinFolding.Tetrahedral.NearFieldRightFinalColumn
import ProteinFolding.Tetrahedral.FarFieldMixedCaps

/-! Whole-frame clearance from the actual selected routing columns. The
existing P-link interfaces suffice: frame H sites are inside Oct and all
complete-frame cap sites are dangling. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def frameLinkInteriorIndex (p : ConstructionParameters) (j : FrameLinkIndex p)
    (s : Fin (nearFrameLength (frameLinkKind j) - 2)) : Fin (nearFrameLength (frameLinkKind j)) :=
  ⟨s.val + 1, by have h := s.isLt; omega⟩

theorem frameLinkInteriorIndex_pos (p : ConstructionParameters) (j : FrameLinkIndex p)
    (s : Fin (nearFrameLength (frameLinkKind j) - 2)) : 0 < (frameLinkInteriorIndex p j s).val := by
  change 0 < s.val + 1
  omega

theorem frameLinkInteriorIndex_before_last (p : ConstructionParameters) (j : FrameLinkIndex p)
    (s : Fin (nearFrameLength (frameLinkKind j) - 2)) :
    (frameLinkInteriorIndex p j s).val + 1 < nearFrameLength (frameLinkKind j) := by
  change s.val + 1 + 1 < _
  have h := s.isLt
  omega

theorem frameLinkFold_pos_eq_framePoint (p : ConstructionParameters) (j : FrameLinkIndex p)
    (s : Fin (nearFrameLength (frameLinkKind j) - 2)) :
    (frameLinkFold p j).pos s = nearFramePoint p.side (frameLinkParameter j) (frameLinkKind j)
      (frameLinkParameter_odd p j) (frameLinkInteriorIndex p j s) := rfl

theorem frameCoreFold_ne_column_of_links (p : ConstructionParameters) (C : DanglingColumn p.side)
    (n : ℕ) (hclear : ∀ j : FrameLinkIndex p, ∀ s : Fin (nearFrameLength (frameLinkKind j) - 2),
      C.point n ≠ (frameLinkFold p j).pos s)
    (i : Fin (p.framePart1 ++ p.framePart2).length) : (frameCoreFold p).pos i ≠ C.point n := by
  apply frameCoreFold_property p (fun x => x ≠ C.point n) _ i
  intro j s
  rcases j with j | j
  · dsimp only [frameCorePiece, frameHRunPiece] at s ⊢
    exact fold_ne_column_of_inside (S := frameHRunWord p j) (m := p.side)
      (frameHRunFold p j) C (frameHRunFold_mem_oct p j) s n
  · dsimp only [frameCorePiece, frameLinkPiece] at s ⊢
    rw [frameLinkWordFold_pos]
    exact (hclear j _).symm

theorem frameFold_ne_positiveColumn_of_links (p : ConstructionParameters) (C : DanglingColumn p.side)
    (n : ℕ) (hn : 1 ≤ n)
    (hclear : ∀ j : FrameLinkIndex p, ∀ s : Fin (nearFrameLength (frameLinkKind j) - 2),
      C.point n ≠ (frameLinkFold p j).pos s)
    (i : Fin p.frameWord.length) : (frameFold p).pos i ≠ C.point n := by
  intro heq
  have hmem := (mem_foldSites (frameFold p) _).mpr ⟨i, heq⟩
  rw [frameFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact FarField.dangling_ne_positive_column (frameFirstColumn p).seed_dangling C n hn h.symm
  · obtain ⟨j, hj⟩ := (mem_foldSites (frameCoreFold p) _).mp h
    exact frameCoreFold_ne_column_of_links p C n hclear j hj
  · exact FarField.dangling_ne_positive_column (frameLastColumn p).seed_dangling C n hn h.symm

theorem frameFold_ne_bulkColumn (p : ConstructionParameters) (C : DanglingColumn p.side)
    (hC : C.owner ∈ bulkInterior p.side) (n : ℕ) (hn : 1 ≤ n) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠ C.point n := by
  apply frameFold_ne_positiveColumn_of_links p C n hn _ i
  intro j s
  rw [frameLinkFold_pos_eq_framePoint]
  exact bulkColumn_ne_frameP C hC (frameLinkKind j) (frameLinkParameter_odd p j)
    (frameLinkParameter_ge p j) (frameLinkParameter_room p j) n (frameLinkInteriorIndex p j s)
    (frameLinkInteriorIndex_pos p j s) (frameLinkInteriorIndex_before_last p j s)

theorem frameFold_ne_trackAColumn (p : ConstructionParameters) (a : ℕ) (ha : a < p.side)
    (n : ℕ) (hn : 1 ≤ n) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠
      (trackAColumn (m := p.side) (by have h := p.side_ge; omega) a ha).point n := by
  apply frameFold_ne_positiveColumn_of_links p _ n hn _ i
  intro j s
  rw [frameLinkFold_pos_eq_framePoint]
  exact trackAColumn_ne_frameP (m := p.side) (by have h := p.side_ge; omega) a ha n
    (frameLinkParameter j) (frameLinkKind j) (frameLinkParameter_odd p j)
    (frameLinkParameter_ge p j) (frameLinkParameter_room p j) (frameLinkInteriorIndex p j s)
    (frameLinkInteriorIndex_pos p j s) (frameLinkInteriorIndex_before_last p j s)

theorem frameFold_ne_exitCapColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (n : ℕ) (hn : 1 ≤ n) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠ (exitCapColumn p k hk).point n :=
  frameFold_ne_positiveColumn_of_links p (exitCapColumn p k hk) n hn
    (fun j s => exitCapColumn_ne_frameLinkFold p k hk j n s) i

theorem frameFold_ne_canonicalRingColumn (p : ConstructionParameters) (r : Fin 3) (e : Fin 2)
    (n : ℕ) (hn : 1 ≤ n) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠ (canonicalRingColumn p r e).point n :=
  frameFold_ne_positiveColumn_of_links p (canonicalRingColumn p r e) n hn
    (fun j s => canonicalRingColumn_ne_frameLink p r e j n s) i

theorem frameFold_ne_singletonColumn (p : ConstructionParameters) (r : Fin 3) (last : Bool)
    (n : ℕ) (hn : 1 ≤ n) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n :=
  frameFold_ne_positiveColumn_of_links p _ n hn
    (fun j s => canonicalSingletonColumn_ne_framePFold p.side (by have h := p.side_ge; omega)
      r last n (frameLinkParameter j) (frameLinkKind j) (frameLinkParameter_odd p j)
      (frameLinkParameter_ge p j) (frameLinkParameter_room p j) s) i

theorem frameFold_ne_rightFinalColumn (p : ConstructionParameters)
    (n : ℕ) (hn : 1 ≤ n) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠ (rightFinalColumn p).point n :=
  frameFold_ne_positiveColumn_of_links p (rightFinalColumn p) n hn
    (fun j s => rightFinalColumn_ne_framePFold p (frameLinkParameter j) (frameLinkKind j)
      (frameLinkParameter_odd p j) (frameLinkParameter_ge p j) n s) i

theorem frameFold_ne_terminalColumn (p : ConstructionParameters)
    (n : ℕ) (hn : 1 ≤ n) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠ (terminalColumn p).point n := by
  apply frameFold_ne_positiveColumn_of_links p (terminalColumn p) n hn _ i
  intro j s
  rw [frameLinkFold_pos_eq_framePoint]
  exact terminalColumn_ne_frameP p (frameLinkParameter j) (frameLinkKind j)
    (frameLinkParameter_odd p j) (frameLinkParameter_room p j) n (frameLinkInteriorIndex p j s)
    (frameLinkInteriorIndex_pos p j s) (frameLinkInteriorIndex_before_last p j s)

theorem frameFold_ne_selectedEntryColumn (p : ConstructionParameters) (r : EntryCapIndex p)
    (n : ℕ) (hn : 1 ≤ n) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠ (selectedEntryColumn p r).point n :=
  frameFold_ne_positiveColumn_of_links p (selectedEntryColumn p r) n hn
    (fun j s => selectedEntryColumn_ne_frameP p r j n hn s) i

end ProteinFolding.Tetrahedral.NearField
