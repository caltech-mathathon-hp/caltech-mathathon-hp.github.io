import ProteinFolding.Tetrahedral.NearFieldUnitCapFamily
import ProteinFolding.Tetrahedral.Columns
import ProteinFolding.Tetrahedral.FrameWordPHP
import Mathlib.Data.List.Perm.Basic

/-! Selected columns remain attached to their actual capped local words,
including during an occurrence-preserving item permutation. -/

namespace ProteinFolding.Tetrahedral.NearField

structure CappedUnit (m : ℕ) where
  body : Sequence
  piece : PositionedWord
  word_eq : piece.word = capWord body
  entry : DanglingColumn m
  exit : DanglingColumn m
  first_dangling : IsDangling m piece.first
  last_dangling : IsDangling m piece.last
  first_adjacent : tetrahedralLattice.Adj piece.first (entry.point 1)
  last_adjacent : tetrahedralLattice.Adj piece.last (exit.point 1)

def CappedUnit.ofColumns {m : ℕ} (body : Sequence) (piece : PositionedWord)
    (hword : piece.word = capWord body) (C D : DanglingColumn m)
    (hfirst : piece.first = C.seed) (hlast : piece.last = D.seed) : CappedUnit m where
  body := body
  piece := piece
  word_eq := hword
  entry := C
  exit := D
  first_dangling := by rw [hfirst]; exact C.seed_dangling
  last_dangling := by rw [hlast]; exact D.seed_dangling
  first_adjacent := by rw [hfirst]; exact C.point_adj 0
  last_adjacent := by rw [hlast]; exact D.point_adj 0

theorem CappedUnit.length_ge_two {m : ℕ} (u : CappedUnit m) : 2 ≤ u.piece.word.length := by
  rw [u.word_eq]
  simp only [capWord, List.length_cons, List.length_append, List.length_singleton]
  omega

def CappedUnit.column {m : ℕ} (u : CappedUnit m) (first : Bool) : DanglingColumn m :=
  if first then u.entry else u.exit

theorem CappedUnit.column_adjacent {m : ℕ} (u : CappedUnit m) (first : Bool) :
    tetrahedralLattice.Adj (wordEndpoint u.piece first) ((u.column first).point 1) := by
  cases first
  · exact u.last_adjacent
  · exact u.first_adjacent

theorem reorderCappedUnits_exists {m : ℕ} (us : List (CappedUnit m)) (words : List Sequence)
    (hwords : words.Perm (us.map (fun u => u.piece.word))) :
    ∃ vs : List (CappedUnit m), vs.Perm us ∧ vs.map (fun u => u.piece.word) = words := by
  have hr : Relation.Comp (fun a b => a = b.map (fun u : CappedUnit m => u.piece.word)) List.Perm words us := by
    rw [List.eq_map_comp_perm]
    exact hwords
  obtain ⟨vs, hv, hp⟩ := hr
  exact ⟨vs, hp, hv.symm⟩

structure ReorderedCappedUnits {m : ℕ} (us : List (CappedUnit m)) (words : List Sequence) where
  units : List (CappedUnit m)
  perm : units.Perm us
  words_eq : units.map (fun u => u.piece.word) = words

noncomputable def reorderCappedUnits {m : ℕ} (us : List (CappedUnit m)) (words : List Sequence)
    (hwords : words.Perm (us.map (fun u => u.piece.word))) : ReorderedCappedUnits us words := by
  let vs := Classical.choose (reorderCappedUnits_exists us words hwords)
  have hv := Classical.choose_spec (reorderCappedUnits_exists us words hwords)
  exact ⟨vs, hv.1, hv.2⟩

theorem ReorderedCappedUnits.property {m : ℕ} {us : List (CappedUnit m)} {words : List Sequence}
    (r : ReorderedCappedUnits us words) (P : CappedUnit m → Prop) (h : ∀ u ∈ us, P u) :
    ∀ u ∈ r.units, P u := by
  intro u hu
  exact h u (r.perm.subset hu)

theorem ReorderedCappedUnits.pairwise {m : ℕ} {us : List (CappedUnit m)} {words : List Sequence}
    (r : ReorderedCappedUnits us words)
    (h : us.Pairwise (fun u v => WordsDisjoint u.piece v.piece)) :
    r.units.Pairwise (fun u v => WordsDisjoint u.piece v.piece) :=
  r.perm.symm.pairwise h (fun hxy => hxy.symm)

theorem reorderCappedBodies_exists {m : ℕ} (us : List (CappedUnit m)) (bodies : List Sequence)
    (hwords : bodies.Perm (us.map CappedUnit.body)) :
    ∃ vs : List (CappedUnit m), vs.Perm us ∧ vs.map CappedUnit.body = bodies := by
  have hr : Relation.Comp (fun a b => a = b.map (CappedUnit.body (m := m))) List.Perm bodies us := by
    rw [List.eq_map_comp_perm]
    exact hwords
  obtain ⟨vs, hv, hp⟩ := hr
  exact ⟨vs, hp, hv.symm⟩

structure ReorderedCappedBodies {m : ℕ} (us : List (CappedUnit m)) (bodies : List Sequence) where
  units : List (CappedUnit m)
  perm : units.Perm us
  bodies_eq : units.map CappedUnit.body = bodies

noncomputable def reorderCappedBodies {m : ℕ} (us : List (CappedUnit m)) (bodies : List Sequence)
    (hwords : bodies.Perm (us.map CappedUnit.body)) : ReorderedCappedBodies us bodies := by
  let vs := Classical.choose (reorderCappedBodies_exists us bodies hwords)
  have hv := Classical.choose_spec (reorderCappedBodies_exists us bodies hwords)
  exact ⟨vs, hv.1, hv.2⟩

theorem CappedUnit.pieces_words {m : ℕ} (us : List (CappedUnit m)) :
    (us.map CappedUnit.piece).map PositionedWord.word = (us.map CappedUnit.body).map capWord := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro u _
  exact u.word_eq

theorem ReorderedCappedBodies.words {m : ℕ} {us : List (CappedUnit m)} {bodies : List Sequence}
    (r : ReorderedCappedBodies us bodies) :
    (r.units.map CappedUnit.piece).map PositionedWord.word = bodies.map capWord := by
  rw [CappedUnit.pieces_words, r.bodies_eq]

theorem ReorderedCappedBodies.property {m : ℕ} {us : List (CappedUnit m)} {bodies : List Sequence}
    (r : ReorderedCappedBodies us bodies) (P : CappedUnit m → Prop) (h : ∀ u ∈ us, P u) :
    ∀ u ∈ r.units, P u := by
  intro u hu
  exact h u (r.perm.subset hu)

theorem ReorderedCappedBodies.pairwise {m : ℕ} {us : List (CappedUnit m)} {bodies : List Sequence}
    (r : ReorderedCappedBodies us bodies)
    (h : us.Pairwise (fun u v => WordsDisjoint u.piece v.piece)) :
    r.units.Pairwise (fun u v => WordsDisjoint u.piece v.piece) :=
  r.perm.symm.pairwise h (fun hxy => hxy.symm)

end ProteinFolding.Tetrahedral.NearField
