import ProteinFolding.Tetrahedral.NearFieldFrameCoreFold
import ProteinFolding.Tetrahedral.NearFieldFrameVertexCaps

/-! Exact first and last H sites and the free vertex-column clearance of the
same assembled frame fold. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096

theorem piecesFirst_eq_head (ps : List PositionedWord) :
    piecesFirst ps = ps.head?.map PositionedWord.first := by cases ps <;> rfl

theorem piecesLast_eq_getLast (ps : List PositionedWord) :
    piecesLast ps = ps.getLast?.map PositionedWord.last := by
  induction ps using List.twoStepInduction with
  | nil => rfl
  | singleton p => rfl
  | cons_cons p q ps _ ih => simpa only [piecesLast, List.getLast?_cons_cons] using ih q

theorem frameCoreAssembly_first (p : ConstructionParameters) :
    (frameCoreAssembly p).piece.first = octEdgeZigzag p.side entryEdgeFrame 0 := by
  have hh : (frameCorePieces p).head? = some (frameHRunPiece p (.inl 0)) := by
    rw [frameCorePieces_slot_blocks]
    rfl
  have h := (frameCoreAssembly p).first_eq
  rw [piecesFirst_eq_head, hh] at h
  have he := Option.some.inj h
  simpa only [frameHRunPiece, frameHRunFirst, frameHRunData, ite_true, Bool.false_eq_true, if_false] using he

theorem frameCoreAssembly_last (p : ConstructionParameters) :
    (frameCoreAssembly p).piece.last = octEdgeZigzag p.side exitEdgeFrame 0 := by
  have hh : (frameCorePieces p).getLast? = some (frameHRunPiece p (.inl 4)) := by
    rw [frameCorePieces_slot_blocks]
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    rfl
  have h := (frameCoreAssembly p).last_eq
  rw [piecesLast_eq_getLast, hh] at h
  have he := Option.some.inj h
  simpa [frameHRunPiece, frameHRunLast, frameHRunData] using he

theorem frameCoreFold_first (p : ConstructionParameters) (r : Fin (p.framePart1 ++ p.framePart2).length)
    (hr : r.val = 0) : (frameCoreFold p).pos r = octEdgeZigzag p.side entryEdgeFrame 0 := by
  apply transportWordFold_first
  · intro i hi
    rw [(frameCoreAssembly p).piece.first_eq i hi]
    exact frameCoreAssembly_first p
  · exact hr

theorem frameCoreFold_last (p : ConstructionParameters) (r : Fin (p.framePart1 ++ p.framePart2).length)
    (hr : r.val + 1 = (p.framePart1 ++ p.framePart2).length) :
    (frameCoreFold p).pos r = octEdgeZigzag p.side exitEdgeFrame 0 := by
  apply transportWordFold_last
  · intro i hi
    rw [(frameCoreAssembly p).piece.last_eq i hi]
    exact frameCoreAssembly_last p
  · exact hr

theorem frameCoreFold_property (p : ConstructionParameters) (P : Site → Prop)
    (hpieces : ∀ i : FrameCoreIndex p, ∀ r, P ((frameCorePiece p i).fold.pos r))
    (r : Fin (p.framePart1 ++ p.framePart2).length) : P ((frameCoreFold p).pos r) := by
  unfold frameCoreFold
  refine transportWordFold_property
    ((frameCoreAssembly p).word_eq.trans (frameCorePieces_words p))
    (frameCoreAssembly p).piece.fold P ?_ r
  intro j
  apply (frameCoreAssembly p).position_property P _ j
  intro q hq s
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  exact hpieces i s

theorem frameCoreFold_ne_endpointColumn (p : ConstructionParameters) (atStart : Bool) (n : ℕ)
    (r : Fin (p.framePart1 ++ p.framePart2).length) :
    (frameCoreFold p).pos r ≠ (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply frameCoreFold_property p (fun x => x ≠ (frameEndpointColumn hm atStart).point n) _ r
  intro i s
  rcases i with i | i
  · dsimp only [frameCorePiece, frameHRunPiece] at s ⊢
    exact fold_ne_column_of_inside (S := frameHRunWord p i) (m := p.side)
      (frameHRunFold p i) (frameEndpointColumn hm atStart) (frameHRunFold_mem_oct p i) s n
  · dsimp only [frameCorePiece, frameLinkPiece] at s ⊢
    have hs : s.val < nearFrameLength (frameLinkKind i) - 2 := by
      simpa only [frameLinkWord, List.length_replicate] using s.isLt
    have hlen := nearFrameLength_ge_five (frameLinkKind i)
    change (frameLinkWordFold p i).pos s ≠ _
    rw [frameLinkWordFold_pos]
    exact (frameEndpointColumn_ne_frameP hm atStart n (frameLinkParameter i) (frameLinkKind i)
      (frameLinkParameter_odd p i) (frameLinkParameter_ge p i) (frameLinkParameter_room p i)
      ⟨s.val + 1, by omega⟩
      (by change 0 < s.val + 1; omega)
      (by change s.val + 1 + 1 < nearFrameLength (frameLinkKind i); omega)).symm

theorem frameEndpointVertex_eq_edge (p : ConstructionParameters) (atStart : Bool) :
    frameEndpointVertex p.side atStart =
      if atStart then octEdgeZigzag p.side entryEdgeFrame 0 else octEdgeZigzag p.side exitEdgeFrame 0 := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply Subtype.ext
  cases atStart
  · change (frameEndpointVertex p.side false).val = (octEdgeZigzag p.side exitEdgeFrame 0).val
    rw [exitEdgeZigzag_coordinates hm]
    funext c
    fin_cases c <;> dsimp [frameEndpointVertex, octVertexSite, octVertexCoordinates,
      octCentre, exitEdgeCoordinates, octRadius] <;> omega
  · change (frameEndpointVertex p.side true).val = (octEdgeZigzag p.side entryEdgeFrame 0).val
    rw [entryEdgeZigzag_coordinates hm]
    funext c
    fin_cases c <;> dsimp [frameEndpointVertex, octVertexSite, octVertexCoordinates,
      octCentre, entryEdgeCoordinates, octRadius] <;> omega

end ProteinFolding.Tetrahedral.NearField
