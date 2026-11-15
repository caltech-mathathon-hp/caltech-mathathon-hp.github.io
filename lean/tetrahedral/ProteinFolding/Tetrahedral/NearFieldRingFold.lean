import ProteinFolding.Tetrahedral.NearFieldRingCornerSeparation
import ProteinFolding.Tetrahedral.NearFieldRingWords
import ProteinFolding.Tetrahedral.NearFieldWordPieceAssembly
import ProteinFolding.Tetrahedral.NearFieldWordTransport

/-! The complete literal ring body: three side chains and exactly two corner
PPPs, assembled into one injective fold with its actual endpoint H sites. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def ringSidePiece (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame)
    (i : Fin 3) : PositionedWord where
  word := dimerChain (m - 2)
  fold := ringSideFold m hm (ringSideFrame F i)
  length_pos := by have h := dimerChain_length (m - 2) (by omega); omega
  first := ringTerminalSite m F i 0
  last := ringTerminalSite m F i 1
  first_eq := by
    intro r hr
    change (ringSideFold m hm (ringSideFrame F i)).pos r = octEdgeZigzag m (ringSideFrame F i) 1
    exact ringSideFold_first m hm (ringSideFrame F i) r hr
  last_eq := by
    intro r hr
    change (ringSideFold m hm (ringSideFrame F i)).pos r =
      octEdgeZigzag m (ringSideFrame F i) (2 * m - 5)
    exact ringSideFold_last m hm heven (ringSideFrame F i) r hr

def ringCornerPiece (m : ℕ) (F : OctEdgeFrame) (c : Fin 2) : PositionedWord where
  word := List.replicate 3 .P
  fold := ringCornerFold m (ringSideFrame F c.castSucc)
  length_pos := by decide
  first := (ringCornerFold m (ringSideFrame F c.castSucc)).pos 0
  last := (ringCornerFold m (ringSideFrame F c.castSucc)).pos 2
  first_eq := by
    intro i hi
    exact congrArg (ringCornerFold m (ringSideFrame F c.castSucc)).pos (Fin.ext hi)
  last_eq := by
    intro i hi
    have hil := i.isLt
    have heq : i = (2 : Fin 3) := Fin.ext (by change i.val = 2; change i.val + 1 = 3 at hi; omega)
    exact congrArg (ringCornerFold m (ringSideFrame F c.castSucc)).pos heq

def ringPieces (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame) : List PositionedWord :=
  [ringSidePiece m hm heven F 0, ringCornerPiece m F 0,
   ringSidePiece m hm heven F 1, ringCornerPiece m F 1,
   ringSidePiece m hm heven F 2]

private theorem pairwise_five {α : Type} (R : α → α → Prop) (a b c d e : α)
    (hab : R a b) (hac : R a c) (had : R a d) (hae : R a e)
    (hbc : R b c) (hbd : R b d) (hbe : R b e)
    (hcd : R c d) (hce : R c e) (hde : R d e) : [a, b, c, d, e].Pairwise R := by
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals assumption
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    all_goals assumption
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    all_goals assumption
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact hde
  · intro x hx
    cases hx

theorem ringPieces_pairwise (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame) :
    (ringPieces m hm heven F).Pairwise
      (fun a b => Disjoint (foldSites a.fold) (foldSites b.fold)) := by
  have hside (i j : Fin 3) (hij : i ≠ j) :
      Disjoint (foldSites (ringSidePiece m hm heven F i).fold)
        (foldSites (ringSidePiece m hm heven F j).fold) :=
    (foldSites_disjoint_iff _ _).mpr (ringSideFolds_pairwise m hm F i j hij)
  have hcorner (i : Fin 3) (c : Fin 2) :
      Disjoint (foldSites (ringSidePiece m hm heven F i).fold)
        (foldSites (ringCornerPiece m F c).fold) :=
    (foldSites_disjoint_iff _ _).mpr (ringSide_ne_corner m hm heven F i c)
  have hcorners : Disjoint (foldSites (ringCornerPiece m F 0).fold)
      (foldSites (ringCornerPiece m F 1).fold) :=
    (foldSites_disjoint_iff _ _).mpr (ringCorners_disjoint m hm heven F)
  exact pairwise_five _ _ _ _ _ _
    (hcorner 0 0) (hside 0 1 (by decide)) (hcorner 0 1) (hside 0 2 (by decide))
    (hcorner 1 0).symm hcorners (hcorner 2 0).symm
    (hcorner 1 1) (hside 1 2 (by decide)) (hcorner 2 1).symm

theorem ringPieces_seams (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame) :
    piecesSeams (ringPieces m hm heven F) := by
  have hsc (c : Fin 2) : tetrahedralLattice.Adj
      (ringSidePiece m hm heven F c.castSucc).last (ringCornerPiece m F c).first :=
    ringCornerFold_first_seam m hm (ringSideFrame F c.castSucc)
  have hcs (c : Fin 2) : tetrahedralLattice.Adj
      (ringCornerPiece m F c).last (ringSidePiece m hm heven F c.succ).first := by
    change tetrahedralLattice.Adj ((ringCornerFold m (ringSideFrame F c.castSucc)).pos 2)
      (octEdgeZigzag m (ringSideFrame F c.succ) 1)
    rw [← ringSideFrame_succ F c]
    exact ringCornerFold_last_seam m hm (ringSideFrame F c.castSucc)
  exact ⟨hsc 0, hcs 0, hsc 1, hcs 1, True.intro⟩

theorem ringPieces_word (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame) :
    pieceWords (ringPieces m hm heven F) = dimerChain (3 * (m - 2)) := by
  simpa only [pieceWords, ringPieces, ringSidePiece, ringCornerPiece,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] using
    dimerChain_three_sides (m - 2) (by omega)

noncomputable def ringAssembly (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame) :
    PieceAssembly (ringPieces m hm heven F) :=
  assemblePieces _ (by intro h; cases h)
    (ringPieces_pairwise m hm heven F) (ringPieces_seams m hm heven F)

noncomputable def ringFold (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame) :
    Fold tetrahedralLattice (dimerChain (3 * (m - 2))).length :=
  transportWordFold ((ringAssembly m hm heven F).word_eq.trans (ringPieces_word m hm heven F))
    (ringAssembly m hm heven F).piece.fold

theorem ringFold_first (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame)
    (i : Fin (dimerChain (3 * (m - 2))).length) (hi : i.val = 0) :
    (ringFold m hm heven F).pos i = ringTerminalSite m F 0 0 := by
  have hfirst : (ringAssembly m hm heven F).piece.first = ringTerminalSite m F 0 0 :=
    Option.some.inj (ringAssembly m hm heven F).first_eq
  apply transportWordFold_first
  intro j hj
  rw [(ringAssembly m hm heven F).piece.first_eq j hj, hfirst]
  exact hi

theorem ringFold_last (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame)
    (i : Fin (dimerChain (3 * (m - 2))).length)
    (hi : i.val + 1 = (dimerChain (3 * (m - 2))).length) :
    (ringFold m hm heven F).pos i = ringTerminalSite m F 2 1 := by
  have hlast : (ringAssembly m hm heven F).piece.last = ringTerminalSite m F 2 1 :=
    Option.some.inj (ringAssembly m hm heven F).last_eq
  apply transportWordFold_last
  intro j hj
  rw [(ringAssembly m hm heven F).piece.last_eq j hj, hlast]
  exact hi

end ProteinFolding.Tetrahedral.NearField
