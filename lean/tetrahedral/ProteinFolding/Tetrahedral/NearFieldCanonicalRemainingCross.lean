import ProteinFolding.Tetrahedral.NearFieldCanonicalBasePieces

/-! The seven remaining local cross-family relations. This interface does
not assert them: an unconditional geometric constructor is still required. -/

namespace ProteinFolding.Tetrahedral.NearField

structure CanonicalRemainingCross (p : ConstructionParameters) : Prop where
  frame_separator : ∀ k : Fin (p.bins + 1),
    WordsDisjoint (frameWordPiece p) (canonicalSeparatorPiece p k)
  separator_left : ∀ k : Fin (p.bins + 1),
    WordsDisjoint (canonicalSeparatorPiece p k) (canonicalLeftPiece p)
  separator_item : ∀ k : Fin (p.bins + 1), ∀ b before s : ℕ, ∀ hb : b < p.bins,
    ∀ hs : 0 < s, ∀ hload : before + s ≤ p.capacity,
    WordsDisjoint (canonicalSeparatorPiece p k) (canonicalItemPiece p b before s hb hs hload)
  separator_right : ∀ k : Fin (p.bins + 1),
    WordsDisjoint (canonicalSeparatorPiece p k) (canonicalRightPiece p)
  left_item : ∀ b before s : ℕ, ∀ hb : b < p.bins, ∀ hs : 0 < s,
    ∀ hload : before + s ≤ p.capacity,
    WordsDisjoint (canonicalLeftPiece p) (canonicalItemPiece p b before s hb hs hload)
  left_right : WordsDisjoint (canonicalLeftPiece p) (canonicalRightPiece p)
  item_right : ∀ b before s : ℕ, ∀ hb : b < p.bins, ∀ hs : 0 < s,
    ∀ hload : before + s ≤ p.capacity,
    WordsDisjoint (canonicalItemPiece p b before s hb hs hload) (canonicalRightPiece p)

end ProteinFolding.Tetrahedral.NearField
