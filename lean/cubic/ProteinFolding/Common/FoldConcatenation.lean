import ProteinFolding.Common.Statement
import Mathlib.Data.Fin.Tuple.Basic
import Lean.Elab.Tactic.Omega

/-! Concatenating disjoint self-avoiding walks across one backbone edge.
The graph and the lengths are arbitrary, including empty components. These
helpers assemble explicit folds without imposing any geometric assumptions. -/

namespace ProteinFolding.Fold

variable {V : Type*} {G : SimpleGraph V} {N M : ℕ}

/-- Append two folds with disjoint images and an edge across the seam.
The quantified seam condition also covers an empty component. -/
def append (f : Fold G N) (g : Fold G M)
    (hdisjoint : ∀ i j, f.pos i ≠ g.pos j)
    (hseam : ∀ i : Fin N, ∀ j : Fin M,
      i.val + 1 = N → j.val = 0 → G.Adj (f.pos i) (g.pos j)) :
    Fold G (N + M) where
  pos := Fin.append f.pos g.pos
  injective_pos := Fin.append_injective_iff.mpr
    ⟨f.injective_pos, g.injective_pos, hdisjoint⟩
  consecutive := by
    intro i j hij
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j =>
        simpa only [Fin.append_left] using f.consecutive i j hij
      | right j =>
        have hi := i.isLt
        have hcross : i.val + 1 = N + j.val := hij
        have hn : i.val + 1 = N := by omega
        have hj : j.val = 0 := by omega
        simpa only [Fin.append_left, Fin.append_right] using hseam i j hn hj
    | right i =>
      cases j using Fin.addCases with
      | left j =>
        have hj := j.isLt
        change N + i.val + 1 = j.val at hij
        omega
      | right j =>
        have hstep : i.val + 1 = j.val := by
          change N + i.val + 1 = N + j.val at hij
          omega
        simpa only [Fin.append_right] using g.consecutive i j hstep

@[simp] theorem append_pos_left (f : Fold G N) (g : Fold G M) hdisjoint hseam (i : Fin N) :
    (append f g hdisjoint hseam).pos (Fin.castAdd M i) = f.pos i :=
  Fin.append_left _ _ _

@[simp] theorem append_pos_right (f : Fold G N) (g : Fold G M) hdisjoint hseam (i : Fin M) :
    (append f g hdisjoint hseam).pos (Fin.natAdd N i) = g.pos i :=
  Fin.append_right _ _ _

/-- The concatenation visits precisely the sites visited by its components. -/
theorem append_exists_pos (f : Fold G N) (g : Fold G M) hdisjoint hseam (v : V) :
    (∃ i, (append f g hdisjoint hseam).pos i = v) ↔
      (∃ i, f.pos i = v) ∨ ∃ j, g.pos j = v := by
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.addCases with
    | left i => exact Or.inl ⟨i, by simpa only [append_pos_left] using hi⟩
    | right i => exact Or.inr ⟨i, by simpa only [append_pos_right] using hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨Fin.castAdd M i, by simpa only [append_pos_left] using hi⟩
    · exact ⟨Fin.natAdd N i, by simpa only [append_pos_right] using hi⟩

/-- Transport the length of a fold along an equality. -/
def onLength (f : Fold G N) {M : ℕ} (h : M = N) : Fold G M where
  pos i := f.pos (Fin.cast h i)
  injective_pos := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin N => x.val) (f.injective_pos hij))
  consecutive i j hij := f.consecutive (Fin.cast h i) (Fin.cast h j) hij

/-- Reverse a walk, preserving its sites and its length. -/
def reverse (f : Fold G N) : Fold G N where
  pos i := f.pos i.rev
  injective_pos := by
    intro i j hij
    have he := congrArg (fun x : Fin N => x.val) (f.injective_pos hij)
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    simp only [Fin.val_rev] at he
    omega
  consecutive := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    apply G.symm
    apply f.consecutive j.rev i.rev
    simp only [Fin.val_rev]
    omega

def leftWordIndex (S T : Sequence) (i : Fin S.length) : Fin (S ++ T).length :=
  ⟨i.val, by simp only [List.length_append]; omega⟩

def rightWordIndex (S T : Sequence) (j : Fin T.length) : Fin (S ++ T).length :=
  ⟨S.length + j.val, by simp only [List.length_append]; omega⟩

/-- The same concatenation, with the exact length of the concatenated word. -/
def appendWord {S T : Sequence} (f : Fold G S.length) (g : Fold G T.length)
    (hdisjoint : ∀ i j, f.pos i ≠ g.pos j)
    (hseam : ∀ i : Fin S.length, ∀ j : Fin T.length,
      i.val + 1 = S.length → j.val = 0 → G.Adj (f.pos i) (g.pos j)) :
    Fold G (S ++ T).length :=
  (append f g hdisjoint hseam).onLength List.length_append

@[simp] theorem appendWord_pos_left {S T : Sequence} (f : Fold G S.length)
    (g : Fold G T.length) hdisjoint hseam (i : Fin S.length) :
    (appendWord f g hdisjoint hseam).pos (leftWordIndex S T i) = f.pos i := by
  change Fin.append f.pos g.pos (Fin.castAdd T.length i) = f.pos i
  exact Fin.append_left _ _ _

@[simp] theorem appendWord_pos_right {S T : Sequence} (f : Fold G S.length)
    (g : Fold G T.length) hdisjoint hseam (j : Fin T.length) :
    (appendWord f g hdisjoint hseam).pos (rightWordIndex S T j) = g.pos j := by
  change Fin.append f.pos g.pos (Fin.natAdd S.length j) = g.pos j
  exact Fin.append_right _ _ _

@[simp] theorem get_leftWordIndex (S T : Sequence) (i : Fin S.length) :
    (S ++ T).get (leftWordIndex S T i) = S.get i := by
  simp only [List.get_eq_getElem, leftWordIndex, List.getElem_append_left i.isLt]

@[simp] theorem get_rightWordIndex (S T : Sequence) (j : Fin T.length) :
    (S ++ T).get (rightWordIndex S T j) = T.get j := by
  simp only [List.get_eq_getElem, rightWordIndex,
    List.getElem_append_right (Nat.le_add_right S.length j.val), Nat.add_sub_cancel_left]

/-- A residue's sites in the full word are exactly those in either component. -/
theorem appendWord_exists_residue {S T : Sequence} (f : Fold G S.length)
    (g : Fold G T.length) hdisjoint hseam (r : Residue) (v : V) :
    (∃ i, (S ++ T).get i = r ∧ (appendWord f g hdisjoint hseam).pos i = v) ↔
      (∃ i, S.get i = r ∧ f.pos i = v) ∨ ∃ j, T.get j = r ∧ g.pos j = v := by
  constructor
  · rintro ⟨i, hr, hv⟩
    by_cases hi : i.val < S.length
    · let j : Fin S.length := ⟨i.val, hi⟩
      have he : i = leftWordIndex S T j := Fin.ext rfl
      rw [he, get_leftWordIndex] at hr
      rw [he, appendWord_pos_left] at hv
      exact Or.inl ⟨j, hr, hv⟩
    · have hil := i.isLt
      simp only [List.length_append] at hil
      let j : Fin T.length := ⟨i.val - S.length, by omega⟩
      have he : i = rightWordIndex S T j := by apply Fin.ext; dsimp [rightWordIndex, j]; omega
      rw [he, get_rightWordIndex] at hr
      rw [he, appendWord_pos_right] at hv
      exact Or.inr ⟨j, hr, hv⟩
  · rintro (⟨i, hr, hv⟩ | ⟨j, hr, hv⟩)
    · exact ⟨leftWordIndex S T i, by simpa only [get_leftWordIndex, appendWord_pos_left] using And.intro hr hv⟩
    · exact ⟨rightWordIndex S T j, by simpa only [get_rightWordIndex, appendWord_pos_right] using And.intro hr hv⟩

end ProteinFolding.Fold
