import ProteinFolding.Tetrahedral.NearFieldLinkerPieces

/-! A single actual fold of units interleaved with the interiors of their
simultaneously routed cap-to-cap linkers. -/

namespace ProteinFolding.Tetrahedral.NearField

def weavePieces : List PositionedWord → List PositionedWord → List PositionedWord
  | [], _ => []
  | us, [] => us
  | u :: us, l :: ls => u :: l :: weavePieces us ls

theorem mem_weavePieces (us ls : List PositionedWord) (x : PositionedWord) :
    x ∈ weavePieces us ls → x ∈ us ∨ x ∈ ls := by
  induction us generalizing ls with
  | nil => simp [weavePieces]
  | cons u us ih =>
    cases ls with
    | nil => simp [weavePieces]
    | cons l ls =>
      intro hx
      simp only [weavePieces, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_self ..)
      · exact (ih ls hx).elim (fun h => Or.inl (List.mem_cons_of_mem _ h))
          (fun h => Or.inr (List.mem_cons_of_mem _ h))

def WordsDisjoint (a b : PositionedWord) : Prop := Disjoint (foldSites a.fold) (foldSites b.fold)

theorem weavePieces_pairwise (us ls : List PositionedWord)
    (hu : us.Pairwise WordsDisjoint) (hl : ls.Pairwise WordsDisjoint)
    (hcross : ∀ u ∈ us, ∀ l ∈ ls, WordsDisjoint u l) :
    (weavePieces us ls).Pairwise WordsDisjoint := by
  induction us generalizing ls with
  | nil => simp [weavePieces]
  | cons u us ih =>
    cases ls with
    | nil => exact hu
    | cons l ls =>
      have huu := List.pairwise_cons.mp hu
      have hll := List.pairwise_cons.mp hl
      apply List.pairwise_cons.mpr
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hxl | hx
        · subst x
          exact hcross u (List.mem_cons_self ..) l (List.mem_cons_self ..)
        · rcases mem_weavePieces us ls x hx with hx | hx
          · exact huu.1 x hx
          · exact hcross u (List.mem_cons_self ..) x (List.mem_cons_of_mem _ hx)
      · apply List.pairwise_cons.mpr
        refine ⟨?_, ih ls huu.2 hll.2 ?_⟩
        · intro x hx
          rcases mem_weavePieces us ls x hx with hx | hx
          · exact (hcross x (List.mem_cons_of_mem _ hx) l (List.mem_cons_self ..)).symm
          · exact hll.1 x hx
        · intro v hv q hq
          exact hcross v (List.mem_cons_of_mem _ hv) q (List.mem_cons_of_mem _ hq)

def weaveSeams : List PositionedWord → List PositionedWord → Prop
  | [], [] => True
  | [_], [] => True
  | u :: v :: us, l :: ls => tetrahedralLattice.Adj u.last l.first ∧
      tetrahedralLattice.Adj l.last v.first ∧ weaveSeams (v :: us) ls
  | _, _ => False

theorem weavePieces_seams (us ls : List PositionedWord) (h : weaveSeams us ls) :
    piecesSeams (weavePieces us ls) := by
  induction us generalizing ls with
  | nil =>
    cases ls with
    | nil => trivial
    | cons l ls => exact False.elim h
  | cons u us ih =>
    cases us with
    | nil =>
      cases ls with
      | nil => trivial
      | cons l ls => exact False.elim h
    | cons v us =>
      cases ls with
      | nil => exact False.elim h
      | cons l ls =>
        have hh : tetrahedralLattice.Adj u.last l.first ∧ tetrahedralLattice.Adj l.last v.first ∧
            weaveSeams (v :: us) ls := h
        have ht := ih ls hh.2.2
        cases ls <;> exact ⟨hh.1, hh.2.1, ht⟩

noncomputable def assembleWeave (us ls : List PositionedWord) (hne : us ≠ [])
    (hu : us.Pairwise WordsDisjoint) (hl : ls.Pairwise WordsDisjoint)
    (hcross : ∀ u ∈ us, ∀ l ∈ ls, WordsDisjoint u l) (hseams : weaveSeams us ls) :
    PieceAssembly (weavePieces us ls) :=
  assemblePieces (weavePieces us ls)
    (by cases us with
        | nil => exact False.elim (hne rfl)
        | cons u us => cases ls <;> simp [weavePieces])
    (weavePieces_pairwise us ls hu hl hcross) (weavePieces_seams us ls hseams)

end ProteinFolding.Tetrahedral.NearField
