import ProteinFolding.Common.CookLevin
import Mathlib.Data.Nat.Pairing

/-! A linear-clause-size transformation from CNF to clauses of width at most
three. Original variable v is renamed to 2v. Odd variables encode pairs of
clause and suffix indices; their values are bounded polynomially by the number
of occurrences, independently of the values of the original binary indices.
Every suffix flag is constrained only in the direction needed for soundness.
This file establishes semantics; it does not assume any complexity theorem. -/

namespace ProteinFolding.SAT.ThreeCNF

def fresh (j k : ℕ) : ℕ := 2 * Nat.pair j k + 1

def positive (v : ℕ) : Literal := ⟨v, true⟩
def negative (v : ℕ) : Literal := ⟨v, false⟩
def liftLiteral (l : Literal) : Literal := ⟨2 * l.var, l.pos⟩

def chain (j : ℕ) : ℕ → Clause → CNF
  | k, [] => [[negative (fresh j k)]]
  | k, l :: ls =>
    [negative (fresh j k), liftLiteral l, positive (fresh j (k + 1))] :: chain j (k + 1) ls

def gadget (j : ℕ) (c : Clause) : CNF := [positive (fresh j 0)] :: chain j 0 c

def transform (φ : CNF) : CNF :=
  (List.ofFn (fun j : Fin φ.length => gadget j.val (φ.get j))).flatten

def WidthAtMostThree (φ : CNF) : Prop := ∀ c ∈ φ, c.length ≤ 3

def SatisfiedBy (a : ℕ → Bool) (φ : CNF) : Prop :=
  ∀ c ∈ φ, ∃ l ∈ c, l.eval a = true

def clauseValue (a : ℕ → Bool) (c : Clause) : Bool := c.any (Literal.eval a)

def extend (φ : CNF) (a : ℕ → Bool) (v : ℕ) : Bool :=
  if v % 2 = 0 then a (v / 2)
  else match φ[(Nat.unpair (v / 2)).1]? with
    | none => false
    | some c => clauseValue a (c.drop (Nat.unpair (v / 2)).2)

theorem extend_old (φ : CNF) (a : ℕ → Bool) (v : ℕ) : extend φ a (2 * v) = a v := by
  simp [extend, Nat.mul_comm]

theorem extend_fresh (φ : CNF) (a : ℕ → Bool) (j : Fin φ.length) (k : ℕ) :
    extend φ a (fresh j.val k) = clauseValue a ((φ.get j).drop k) := by
  have hmod : (2 * Nat.pair j.val k + 1) % 2 = 1 := by omega
  have hdiv : (2 * Nat.pair j.val k + 1) / 2 = Nat.pair j.val k := by omega
  simp [extend, fresh, hmod, hdiv, Nat.unpair_pair, j.isLt]

theorem lift_eval (b : ℕ → Bool) (l : Literal) :
    (liftLiteral l).eval b = l.eval (fun v => b (2 * v)) := by
  rfl

theorem extend_lift_eval (φ : CNF) (a : ℕ → Bool) (l : Literal) :
    (liftLiteral l).eval (extend φ a) = l.eval a := by
  simp [Literal.eval, liftLiteral, extend_old]

theorem chain_width (j k : ℕ) (c : Clause) : WidthAtMostThree (chain j k c) := by
  induction c generalizing k with
  | nil => simp [chain, WidthAtMostThree]
  | cons l ls ih => simpa [chain, WidthAtMostThree] using ih (k + 1)

theorem gadget_width (j : ℕ) (c : Clause) : WidthAtMostThree (gadget j c) := by
  simpa [gadget, WidthAtMostThree] using chain_width j 0 c

theorem transform_width (φ : CNF) : WidthAtMostThree (transform φ) := by
  intro c hc
  obtain ⟨g, hg, hc⟩ := List.mem_flatten.mp hc
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  exact gadget_width j.val (φ.get j) c hc

theorem chain_sound (b : ℕ → Bool) (j k : ℕ) (c : Clause)
    (h : SatisfiedBy b (chain j k c)) (hflag : b (fresh j k) = true) :
    ∃ l ∈ c, l.eval (fun v => b (2 * v)) = true := by
  induction c generalizing k with
  | nil =>
    obtain ⟨l, hl, he⟩ := h [negative (fresh j k)] (by simp [chain])
    simp only [List.mem_singleton] at hl
    subst l
    simp [negative, Literal.eval, hflag] at he
  | cons l ls ih =>
    have hhead := h [negative (fresh j k), liftLiteral l, positive (fresh j (k + 1))]
      (by simp [chain])
    have htail : SatisfiedBy b (chain j (k + 1) ls) := by
      intro d hd
      exact h d (by simp [chain, hd])
    obtain ⟨v, hv, he⟩ := hhead
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · simp [negative, Literal.eval, hflag] at he
    · exact ⟨l, List.mem_cons_self .., by simpa only [lift_eval] using he⟩
    · obtain ⟨v, hv, heval⟩ := ih (k + 1) htail (by simpa [positive, Literal.eval] using he)
      exact ⟨v, List.mem_cons_of_mem _ hv, heval⟩

theorem gadget_sound (b : ℕ → Bool) (j : ℕ) (c : Clause)
    (h : SatisfiedBy b (gadget j c)) :
    ∃ l ∈ c, l.eval (fun v => b (2 * v)) = true := by
  have hfirst := h [positive (fresh j 0)] (by simp [gadget])
  have hflag : b (fresh j 0) = true := by simpa [positive, Literal.eval] using hfirst
  apply chain_sound b j 0 c (fun d hd => h d (by simp [gadget, hd])) hflag

theorem chain_complete (φ : CNF) (a : ℕ → Bool) (j : Fin φ.length)
    (k : ℕ) (c : Clause) (hc : (φ.get j).drop k = c) :
    SatisfiedBy (extend φ a) (chain j.val k c) := by
  induction c generalizing k with
  | nil =>
    intro d hd
    simp only [chain, List.mem_singleton] at hd
    subst d
    refine ⟨negative (fresh j.val k), by simp, ?_⟩
    change Bool.not (extend φ a (fresh j.val k)) = true
    rw [extend_fresh, hc]
    rfl
  | cons l ls ih =>
    have hnext : (φ.get j).drop (k + 1) = ls := by
      have hh := congrArg (List.drop 1) hc
      simpa [List.drop_drop, Nat.add_comm] using hh
    intro d hd
    simp only [chain, List.mem_cons] at hd
    rcases hd with rfl | hd
    · by_cases hl : l.eval a = true
      · exact ⟨liftLiteral l, by simp, by simpa only [extend_lift_eval] using hl⟩
      · by_cases ht : clauseValue a ls = true
        · refine ⟨positive (fresh j.val (k + 1)), by simp, ?_⟩
          change extend φ a (fresh j.val (k + 1)) = true
          rw [extend_fresh, hnext]
          exact ht
        · refine ⟨negative (fresh j.val k), by simp, ?_⟩
          have hlf : l.eval a = false := Bool.eq_false_iff.mpr hl
          have htf : clauseValue a ls = false := Bool.eq_false_iff.mpr ht
          change Bool.not (extend φ a (fresh j.val k)) = true
          rw [extend_fresh, hc]
          change Bool.not (l.eval a || clauseValue a ls) = true
          rw [hlf, htf]
          rfl
    · exact ih (k + 1) hnext d hd

theorem gadget_complete (φ : CNF) (a : ℕ → Bool) (j : Fin φ.length)
    (h : ∃ l ∈ φ.get j, l.eval a = true) :
    SatisfiedBy (extend φ a) (gadget j.val (φ.get j)) := by
  intro d hd
  simp only [gadget, List.mem_cons] at hd
  rcases hd with rfl | hd
  · refine ⟨positive (fresh j.val 0), by simp, ?_⟩
    change extend φ a (fresh j.val 0) = true
    rw [extend_fresh, List.drop_zero]
    exact List.any_eq_true.mpr h
  · exact chain_complete φ a j 0 (φ.get j) (by simp) d hd

theorem transform_equisatisfiable (φ : CNF) : Satisfiable (transform φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨fun v => b (2 * v), ?_⟩
    intro c hc
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hc
    apply gadget_sound b j.val (φ.get j)
    intro d hd
    exact hb d (List.mem_flatten.mpr ⟨gadget j.val (φ.get j), List.mem_ofFn.mpr ⟨j, rfl⟩, hd⟩)
  · rintro ⟨a, ha⟩
    refine ⟨extend φ a, ?_⟩
    intro d hd
    obtain ⟨g, hg, hd⟩ := List.mem_flatten.mp hd
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    exact gadget_complete φ a j (ha _ (List.get_mem ..)) d hd

end ProteinFolding.SAT.ThreeCNF
