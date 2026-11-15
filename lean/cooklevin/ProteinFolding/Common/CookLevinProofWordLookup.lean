import ProteinFolding.Common.TM2WordDrop
import ProteinFolding.Common.TM2WordFold
import ProteinFolding.Common.TM2EncodingWords
import ProteinFolding.Common.TM2ProductMap
import ProteinFolding.Common.TM2Constants

/-! Actual polynomial-time observations of a word at a unary index. The
finite-state observer remembers its first letter, after the checked suffix
machine has discarded the prefix. Empty alphabets and out-of-range indices
are included. The typed adapter inspects the original encoding itself. -/

namespace ProteinFolding.SAT.CookLevinWordLookup

open Computability Turing

def keepFirst {A : Type} (s : Option A) (a : A) : Option A := s.or (some a)

theorem fold_keepFirst {A : Type} (w : List A) (s : Option A) :
    w.foldl keepFirst s = s.or w.head? := by
  induction w generalizing s with
  | nil => cases s <;> rfl
  | cons a w ih =>
    rw [List.foldl_cons, ih]
    cases s <;> rfl

def headTest {A : Type} [DecidableEq A] (v : Option A) (w : List A) : Bool :=
  decide (w.head? = v)

noncomputable def headTestComputable (A : Type) [Fintype A] [DecidableEq A]
    (v : Option A) :
    TM2ComputableInPolyTime (wordEncoding A) finEncodingBoolBool (headTest v) := by
  simpa only [fold_keepFirst, Option.or_none, headTest] using
    TM2WordFold.computable A (Option A) keepFirst (fun s => decide (s = v)) none

def lookupTest {A : Type} [DecidableEq A] (v : Option A) (p : List A × ℕ) : Bool :=
  decide (p.1[p.2]? = v)

theorem lookupTest_eq_head_drop {A : Type} [DecidableEq A] (v : Option A)
    (p : List A × ℕ) : lookupTest v p = headTest v (p.1.drop p.2) := by
  simp [lookupTest, headTest]

noncomputable def lookupTestComputable (A : Type) [Fintype A] [DecidableEq A]
    (v : Option A) :
    TM2ComputableInPolyTime (pairEncoding (wordEncoding A) unaryFinEncodingNat)
      finEncodingBoolBool (lookupTest v) := by
  classical
  by_cases hA : Nonempty A
  · letI : Inhabited A := ⟨Classical.choice hA⟩
    have same : lookupTest v = (fun p : List A × ℕ => headTest v (p.1.drop p.2)) :=
      funext (lookupTest_eq_head_drop v)
    rw [same]
    exact TM2CompositionPoly.compose (TM2WordDrop.dropComputable A) (headTestComputable A v)
  · have empty_word (w : List A) : w = [] := by
      cases w with
      | nil => rfl
      | cons a _ => exact (hA ⟨a⟩).elim
    have same : lookupTest v = (fun _ : List A × ℕ => decide ((none : Option A) = v)) := by
      funext p
      simp [lookupTest, empty_word p.1]
    rw [same]
    exact TM2Constants.constantComputable _ _ _

def encodedLookupTest {X : Type} (ex : FinEncoding X) [DecidableEq ex.Γ]
    (v : Option ex.Γ) (p : X × ℕ) : Bool := decide ((ex.encode p.1)[p.2]? = v)

noncomputable def encodedLookupTestComputable {X : Type} (ex : FinEncoding X)
    [DecidableEq ex.Γ] (v : Option ex.Γ) :
    TM2ComputableInPolyTime (pairEncoding ex unaryFinEncodingNat) finEncodingBoolBool
      (encodedLookupTest ex v) := by
  letI : Fintype ex.Γ := ex.ΓFin
  simpa only [Function.comp_def, lookupTest, encodedLookupTest] using
    TM2CompositionPoly.compose
      (TM2ProductMap.leftMapComputable (TM2EncodingWords.encodeComputable ex)
        unaryFinEncodingNat)
      (lookupTestComputable ex.Γ v)

end ProteinFolding.SAT.CookLevinWordLookup
