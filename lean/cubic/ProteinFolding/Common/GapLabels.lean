import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card

/-! Counting distinct path components separated by marked vertices. For the
cubic frame, a label is an open cube edge and a gap is a cube corner. Adjacent
noncorner vertices cannot change their edge label. This combinatorial lemma
does not assume the geometric classification it will be used to prove. -/

namespace ProteinFolding.GapLabels

variable {E : Type} [DecidableEq E]

def SameOrGap (a b : Option E) : Prop := ∀ e f, a = some e → b = some f → e = f

def labels (xs : List (Option E)) : Finset E := (xs.filterMap id).toFinset

def gaps (xs : List (Option E)) : ℕ := (xs.filter Option.isNone).length

def start : List (Option E) → ℕ
  | some _ :: _ => 1
  | _ => 0

omit [DecidableEq E] in
theorem start_le_one (xs : List (Option E)) : start xs ≤ 1 := by
  cases xs with
  | nil => simp [start]
  | cons a xs => cases a <;> simp [start]

/-- Each new nonempty run needs a preceding gap, except for the first run
when the path starts inside a labelled component. Repeated labels only lower
the number of distinct components. -/
theorem card_labels_le (xs : List (Option E)) (h : xs.IsChain SameOrGap) :
    (labels xs).card ≤ gaps xs + start xs := by
  induction xs with
  | nil => simp [labels, gaps, start]
  | cons a xs ih =>
    cases xs with
    | nil => cases a <;> simp [labels, gaps, start]
    | cons b xs =>
      obtain ⟨hab, htail⟩ := List.isChain_cons_cons.mp h
      have hi := ih htail
      cases a with
      | none =>
        cases b <;> simp [labels, gaps, start] at * <;> omega
      | some e =>
        cases b with
        | none =>
          have hc := Finset.card_insert_le e (labels (none :: xs))
          simp [labels, gaps, start] at *
          omega
        | some f =>
          have he : e = f := hab e f rfl rfl
          subst f
          simpa [labels, gaps, start] using hi

theorem card_labels_le_gaps_add_one (xs : List (Option E)) (h : xs.IsChain SameOrGap) :
    (labels xs).card ≤ gaps xs + 1 := by
  have hc := card_labels_le xs h
  have hs := start_le_one xs
  omega

theorem card_labels_le_of_start_gap (xs : List (Option E))
    (h : (none :: xs).IsChain SameOrGap) :
    (labels (none :: xs)).card ≤ gaps (none :: xs) := by
  simpa only [start, Nat.add_zero] using card_labels_le (none :: xs) h

end ProteinFolding.GapLabels
