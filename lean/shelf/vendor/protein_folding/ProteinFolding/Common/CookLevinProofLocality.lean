import ProteinFolding.Common.TM2Bounds

/-! A locality theorem for the actual mathlib TM2 operational semantics.
A finite statement inspects only a bounded stack prefix. Arbitrary untouched
suffixes commute with execution, including when a short prefix is already the
whole stack. This provides the model-specific finite-window fact needed by a
Cook--Levin tableau compiler; it does not itself assert that compiler.
-/

namespace ProteinFolding.SAT.CookLevinLocality

open Turing TM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

def readBound : Stmt Γ Λ σ → ℕ
  | .push _ _ q => readBound q
  | .peek _ _ q => readBound q + 1
  | .pop _ _ q => readBound q + 1
  | .load _ q => readBound q
  | .branch _ q r => max (readBound q) (readBound r)
  | .goto _ | .halt => 0

def appendStacks (S T : ∀ k, List (Γ k)) : ∀ k, List (Γ k) := fun k => S k ++ T k

def appendConfig (c : Cfg Γ Λ σ) (T : ∀ k, List (Γ k)) : Cfg Γ Λ σ :=
  ⟨c.l, c.var, appendStacks c.stk T⟩

theorem head_append_guard {A : Type*} (xs ys : List A)
    (h : 0 < xs.length ∨ ys = []) : (xs ++ ys).head? = xs.head? := by
  cases xs with
  | nil =>
    rcases h with h | h
    · simp at h
    · simp [h]
  | cons x xs => rfl

theorem tail_append_guard {A : Type*} (xs ys : List A)
    (h : 0 < xs.length ∨ ys = []) : (xs ++ ys).tail = xs.tail ++ ys := by
  cases xs with
  | nil =>
    rcases h with h | h
    · simp at h
    · simp [h]
  | cons x xs => rfl

variable [DecidableEq K]

theorem appendStacks_update (S T : ∀ k, List (Γ k)) (j : K) (xs : List (Γ j)) :
    Function.update (appendStacks S T) j (xs ++ T j) = appendStacks (Function.update S j xs) T := by
  funext k
  by_cases h : k = j
  · subst k; simp [appendStacks]
  · simp [appendStacks, Function.update, h]

theorem stepAux_append (q : Stmt Γ Λ σ) (v : σ) (S T : ∀ k, List (Γ k))
    (h : ∀ k, readBound q ≤ (S k).length ∨ T k = []) :
    stepAux q v (appendStacks S T) = appendConfig (stepAux q v S) T := by
  induction q generalizing v S with
  | push j f q ih =>
    simp only [stepAux]
    change stepAux q v (Function.update (appendStacks S T) j ((f v :: S j) ++ T j)) = _
    rw [appendStacks_update]
    apply ih
    intro k
    by_cases hk : k = j
    · subst k
      rcases h j with hj | hj
      · left; simpa using Nat.le_trans hj (Nat.le_succ _)
      · exact Or.inr hj
    · simpa [Function.update, hk] using h k
  | peek j f q ih =>
    have hj : 0 < (S j).length ∨ T j = [] := by
      rcases h j with hj | hj
      · left; simp only [readBound] at hj; omega
      · exact Or.inr hj
    simp only [stepAux]
    change stepAux q (f v ((S j ++ T j).head?)) (appendStacks S T) = _
    rw [head_append_guard _ _ hj]
    apply ih
    intro k
    rcases h k with hk | hk
    · left; simp only [readBound] at hk; omega
    · exact Or.inr hk
  | pop j f q ih =>
    have hj : 0 < (S j).length ∨ T j = [] := by
      rcases h j with hj | hj
      · left; simp only [readBound] at hj; omega
      · exact Or.inr hj
    simp only [stepAux]
    change stepAux q (f v ((S j ++ T j).head?))
      (Function.update (appendStacks S T) j (S j ++ T j).tail) = _
    rw [head_append_guard _ _ hj, tail_append_guard _ _ hj, appendStacks_update]
    apply ih
    intro k
    by_cases hk : k = j
    · subst k
      rcases h j with hj | hj
      · left
        simp only [Function.update_self, List.length_tail]
        simp only [readBound] at hj
        omega
      · exact Or.inr hj
    · rcases h k with hn | hn
      · left
        simp only [Function.update_of_ne hk]
        simp only [readBound] at hn
        omega
      · exact Or.inr hn
  | load f q ih => exact ih (f v) S h
  | branch f q r ihq ihr =>
    have hq : ∀ k, readBound q ≤ (S k).length ∨ T k = [] := by
      intro k
      rcases h k with hk | hk
      · left; exact le_trans (Nat.le_max_left _ _) hk
      · exact Or.inr hk
    have hr : ∀ k, readBound r ≤ (S k).length ∨ T k = [] := by
      intro k
      rcases h k with hk | hk
      · left; exact le_trans (Nat.le_max_right _ _) hk
      · exact Or.inr hk
    simp only [stepAux]
    cases hf : f v
    · simpa only [hf, cond_false] using ihr v S hr
    · simpa only [hf, cond_true] using ihq v S hq
  | goto f => rfl
  | halt => rfl

theorem stepAux_take_decomposition (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    stepAux q v S =
      appendConfig (stepAux q v (fun k => (S k).take (readBound q)))
        (fun k => (S k).drop (readBound q)) := by
  have h : ∀ k, readBound q ≤ ((S k).take (readBound q)).length ∨
      (S k).drop (readBound q) = [] := by
    intro k
    by_cases hk : readBound q ≤ (S k).length
    · left; simp only [List.length_take]; omega
    · right; apply List.drop_eq_nil_of_le; omega
  have he : appendStacks (fun k => (S k).take (readBound q))
      (fun k => (S k).drop (readBound q)) = S := by
    funext k
    exact List.take_append_drop _ _
  have hs := stepAux_append q v (fun k => (S k).take (readBound q))
    (fun k => (S k).drop (readBound q)) h
  rw [he] at hs
  exact hs

/-- Control changes are determined completely by the bounded prefix. -/
theorem stepAux_control_prefix (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    (stepAux q v S).l = (stepAux q v (fun k => (S k).take (readBound q))).l ∧
    (stepAux q v S).var = (stepAux q v (fun k => (S k).take (readBound q))).var := by
  rw [stepAux_take_decomposition q v S]
  exact ⟨rfl, rfl⟩

theorem stepAux_control_congr (q : Stmt Γ Λ σ) (v : σ) (S T : ∀ k, List (Γ k))
    (h : ∀ k, (S k).take (readBound q) = (T k).take (readBound q)) :
    (stepAux q v S).l = (stepAux q v T).l ∧ (stepAux q v S).var = (stepAux q v T).var := by
  have he : (fun k => (S k).take (readBound q)) = fun k => (T k).take (readBound q) := funext h
  have hs := stepAux_control_prefix q v S
  have ht := stepAux_control_prefix q v T
  rw [he] at hs
  exact ⟨hs.1.trans ht.1.symm, hs.2.trans ht.2.symm⟩

/-- The replacement prefix is bounded too: a statement's complete local
transition fits in fixed input/output windows before untouched tails rejoin. -/
theorem stepAux_output_prefix_length (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((stepAux q v (fun j => (S j).take (readBound q))).stk k).length ≤
      readBound q + TM2Bounds.pushBound q := by
  have h := TM2Bounds.stepAux_stack_length q v (fun j => (S j).take (readBound q)) k
  have ht : ((S k).take (readBound q)).length ≤ readBound q := by
    simp only [List.length_take]
    exact Nat.min_le_left _ _
  exact h.trans (Nat.add_le_add_right ht _)

end ProteinFolding.SAT.CookLevinLocality
