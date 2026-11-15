import ProteinFolding.Tetrahedral.ReductionTM2Arithmetic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Fin

namespace ProteinFolding.Tetrahedral.ReductionTM2.Arithmetic

variable {n : ℕ}

def allList : List (Expr n .boolean) → Expr n .boolean
  | [] => .bool true
  | e :: es => .and e (allList es)

def anyList : List (Expr n .boolean) → Expr n .boolean
  | [] => .bool false
  | e :: es => .or e (anyList es)

def countList : List (Expr n .boolean) → Expr n .natural
  | [] => .nat 0
  | e :: es => .add (.ite e (.nat 1) (.nat 0)) (countList es)

def all (k : ℕ) (f : Fin k → Expr n .boolean) : Expr n .boolean := allList (List.ofFn f)
def any (k : ℕ) (f : Fin k → Expr n .boolean) : Expr n .boolean := anyList (List.ofFn f)
def count (k : ℕ) (f : Fin k → Expr n .boolean) : Expr n .natural := countList (List.ofFn f)

theorem eval_allList (ν : Fin n → ℕ) (es : List (Expr n .boolean)) :
    eval ν (allList es) = true ↔ ∀ e ∈ es, eval ν e = true := by
  induction es with
  | nil => simp [allList, eval]
  | cons e es ih => simp [allList, eval, ih]

theorem eval_anyList (ν : Fin n → ℕ) (es : List (Expr n .boolean)) :
    eval ν (anyList es) = true ↔ ∃ e ∈ es, eval ν e = true := by
  induction es with
  | nil => simp [anyList, eval]
  | cons e es ih => simp [anyList, eval, ih]

theorem eval_countList (ν : Fin n → ℕ) (es : List (Expr n .boolean)) :
    eval ν (countList es) = (es.filter (fun e => eval ν e)).length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases he : eval ν e <;> simp [countList, eval, he, ih, Nat.add_comm]

theorem eval_countList_sum (ν : Fin n → ℕ) (es : List (Expr n .boolean)) :
    eval ν (countList es) = (es.map (fun e => if eval ν e then 1 else 0)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [countList, eval, List.map_cons, List.sum_cons, ih]

theorem eval_all (ν : Fin n → ℕ) (k : ℕ) (f : Fin k → Expr n .boolean) :
    eval ν (all k f) = true ↔ ∀ i, eval ν (f i) = true := by
  rw [all, eval_allList]
  constructor
  · intro h i
    exact h (f i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact h i

theorem eval_any (ν : Fin n → ℕ) (k : ℕ) (f : Fin k → Expr n .boolean) :
    eval ν (any k f) = true ↔ ∃ i, eval ν (f i) = true := by
  rw [any, eval_anyList]
  constructor
  · rintro ⟨e, he, ht⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact ⟨i, ht⟩
  · rintro ⟨i, hi⟩
    exact ⟨f i, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩

theorem eval_count (ν : Fin n → ℕ) (k : ℕ) (f : Fin k → Expr n .boolean) :
    eval ν (count k f) = (Finset.univ.filter (fun i : Fin k => eval ν (f i) = true)).card := by
  rw [count, eval_countList_sum, List.map_ofFn, List.sum_ofFn]
  simpa using (Finset.card_filter (fun i : Fin k => eval ν (f i) = true) Finset.univ).symm

end ProteinFolding.Tetrahedral.ReductionTM2.Arithmetic
