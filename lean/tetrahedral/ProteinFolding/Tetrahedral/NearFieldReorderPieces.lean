import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import Mathlib.Data.List.Perm.Basic

/-! A packing permutation reorders the actual positioned item occurrences,
including repeated equal sizes, while retaining every geometric certificate. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem reorderPieces_exists (ps : List PositionedWord) (words : List Sequence)
    (hwords : words.Perm (ps.map PositionedWord.word)) :
    ∃ qs : List PositionedWord, qs.Perm ps ∧ qs.map PositionedWord.word = words := by
  have hr : Relation.Comp (fun a b => a = b.map PositionedWord.word) List.Perm words ps := by
    rw [List.eq_map_comp_perm]
    exact hwords
  obtain ⟨qs, hmap, hperm⟩ := hr
  exact ⟨qs, hperm, hmap.symm⟩

structure ReorderedPieces (ps : List PositionedWord) (words : List Sequence) where
  pieces : List PositionedWord
  perm : pieces.Perm ps
  words_eq : pieces.map PositionedWord.word = words

noncomputable def reorderPieces (ps : List PositionedWord) (words : List Sequence)
    (hwords : words.Perm (ps.map PositionedWord.word)) : ReorderedPieces ps words := by
  let qs := Classical.choose (reorderPieces_exists ps words hwords)
  have hq := Classical.choose_spec (reorderPieces_exists ps words hwords)
  exact ⟨qs, hq.1, hq.2⟩

theorem ReorderedPieces.pairwise {ps : List PositionedWord} {words : List Sequence}
    (r : ReorderedPieces ps words) (h : ps.Pairwise WordsDisjoint) : r.pieces.Pairwise WordsDisjoint :=
  r.perm.symm.pairwise h (fun hxy => hxy.symm)

theorem ReorderedPieces.property {ps : List PositionedWord} {words : List Sequence}
    (r : ReorderedPieces ps words) (P : PositionedWord → Prop) (h : ∀ p ∈ ps, P p) :
    ∀ p ∈ r.pieces, P p := by
  intro p hp
  exact h p (r.perm.subset hp)

end ProteinFolding.Tetrahedral.NearField
