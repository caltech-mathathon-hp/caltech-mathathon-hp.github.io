import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import ProteinFolding.Tetrahedral.ReductionWord

/-! Interleaving the interiors of cap-to-cap routes yields exactly the
literal reduction word, with each unit cap occurring once. -/

namespace ProteinFolding.Tetrahedral.NearField

def weaveWords : List Sequence → List Sequence → Sequence
  | [], _ => []
  | us, [] => us.flatten
  | u :: us, l :: ls => u ++ l ++ weaveWords us ls

theorem pieceWords_weave (us ls : List PositionedWord) :
    pieceWords (weavePieces us ls) = weaveWords (us.map PositionedWord.word) (ls.map PositionedWord.word) := by
  induction us generalizing ls with
  | nil => cases ls <;> rfl
  | cons u us ih =>
    cases ls with
    | nil => rfl
    | cons l ls =>
      change u.word ++ (l.word ++ pieceWords (weavePieces us ls)) =
        u.word ++ l.word ++ weaveWords (us.map PositionedWord.word) (ls.map PositionedWord.word)
      rw [ih ls, List.append_assoc]

theorem weaveWords_capped (gaps : ℕ → ℕ) (bodies : List Sequence) (i : ℕ) (initial : Sequence) :
    weaveWords (initial :: bodies.map capWord)
      ((List.range' i bodies.length).map (fun j => List.replicate (gaps j) .P)) =
        initial ++ assembleCappedBodies gaps i bodies := by
  induction bodies generalizing i initial with
  | nil => simp [weaveWords, assembleCappedBodies]
  | cons u us ih =>
    simp only [List.length_cons, List.range'_succ, List.map_cons, weaveWords]
    rw [ih (i + 1) (capWord u)]
    simp only [assembleCappedBodies, List.append_assoc]

theorem pieceWords_weave_reduction (us ls : List PositionedWord) (gaps : ℕ → ℕ)
    (bodies : List Sequence)
    (hu : us.map PositionedWord.word = [.H, .P] :: bodies.map capWord)
    (hl : ls.map PositionedWord.word =
      (List.range bodies.length).map (fun j => List.replicate (gaps j) .P)) :
    pieceWords (weavePieces us ls) = assembleReductionWord gaps bodies := by
  rw [pieceWords_weave, hu, hl, List.range_eq_range', weaveWords_capped]
  rfl

end ProteinFolding.Tetrahedral.NearField
