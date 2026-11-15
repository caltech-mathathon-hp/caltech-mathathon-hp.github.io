import ProteinFolding.Tetrahedral.ReductionTM2Arithmetic
import Mathlib.Tactic.Ring

/-! Signed local-coordinate expressions represented by two unary natural
terms. Arithmetic and comparisons expand into the finite expression compiler;
the representation requires no binary integer-arithmetic machine. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Arithmetic

variable {n : ℕ}

structure SignedExpr (n : ℕ) where
  positive : Expr n .natural
  negative : Expr n .natural

namespace SignedExpr

def eval (ν : Fin n → ℕ) (e : SignedExpr n) : ℤ :=
  (Arithmetic.eval ν e.positive : ℤ) - (Arithmetic.eval ν e.negative : ℤ)

def ofNat (a : Expr n .natural) : SignedExpr n := ⟨a, .nat 0⟩
def constant : ℤ → SignedExpr n
  | .ofNat c => ⟨.nat c, .nat 0⟩
  | .negSucc c => ⟨.nat 0, .nat (c + 1)⟩

def add (a b : SignedExpr n) : SignedExpr n :=
  ⟨.add a.positive b.positive, .add a.negative b.negative⟩
def neg (a : SignedExpr n) : SignedExpr n := ⟨a.negative, a.positive⟩
def sub (a b : SignedExpr n) : SignedExpr n := add a (neg b)
def mul (a b : SignedExpr n) : SignedExpr n :=
  ⟨.add (.mul a.positive b.positive) (.mul a.negative b.negative),
    .add (.mul a.positive b.negative) (.mul a.negative b.positive)⟩

def absNat (a : SignedExpr n) : Expr n .natural :=
  .add (.sub a.positive a.negative) (.sub a.negative a.positive)

def eq (a b : SignedExpr n) : Expr n .boolean :=
  .eq (.add a.positive b.negative) (.add b.positive a.negative)
def lt (a b : SignedExpr n) : Expr n .boolean :=
  .lt (.add a.positive b.negative) (.add b.positive a.negative)
def le (a b : SignedExpr n) : Expr n .boolean :=
  .le (.add a.positive b.negative) (.add b.positive a.negative)

def sign (a : SignedExpr n) : SignedExpr n :=
  ⟨.ite (.lt a.negative a.positive) (.nat 1) (.nat 0),
    .ite (.lt a.positive a.negative) (.nat 1) (.nat 0)⟩

@[simp] theorem eval_ofNat (ν : Fin n → ℕ) (a : Expr n .natural) :
    eval ν (ofNat a) = (Arithmetic.eval ν a : ℤ) := by simp [eval, ofNat, Arithmetic.eval]

@[simp] theorem eval_constant (ν : Fin n → ℕ) (c : ℤ) : eval ν (constant c) = c := by
  cases c <;> simp [eval, constant, Arithmetic.eval, Int.negSucc_eq]

@[simp] theorem eval_add (ν : Fin n → ℕ) (a b : SignedExpr n) :
    eval ν (add a b) = eval ν a + eval ν b := by
  simp only [eval, add, Arithmetic.eval, Nat.cast_add]
  ring

@[simp] theorem eval_neg (ν : Fin n → ℕ) (a : SignedExpr n) :
    eval ν (neg a) = -eval ν a := by simp only [eval, neg]; ring

@[simp] theorem eval_sub (ν : Fin n → ℕ) (a b : SignedExpr n) :
    eval ν (sub a b) = eval ν a - eval ν b := by simp [sub, sub_eq_add_neg]

@[simp] theorem eval_mul (ν : Fin n → ℕ) (a b : SignedExpr n) :
    eval ν (mul a b) = eval ν a * eval ν b := by
  simp only [eval, mul, Arithmetic.eval, Nat.cast_add, Nat.cast_mul]
  ring

theorem natural_difference_abs (a b : ℕ) :
    (((a - b) + (b - a) : ℕ) : ℤ) = |(a : ℤ) - b| := by
  by_cases h : a ≤ b
  · have hn : (a : ℤ) - b ≤ 0 := by omega
    rw [Nat.sub_eq_zero_of_le h, Nat.zero_add, Nat.cast_sub h, abs_of_nonpos hn]
    ring
  · have hr : b ≤ a := by omega
    have hn : 0 ≤ (a : ℤ) - b := by omega
    rw [Nat.sub_eq_zero_of_le hr, Nat.add_zero, Nat.cast_sub hr, abs_of_nonneg hn]

theorem natural_difference_eq (a b c d : ℕ) :
    a + d = c + b ↔ (a : ℤ) - b = (c : ℤ) - d := by omega

theorem natural_difference_lt (a b c d : ℕ) :
    a + d < c + b ↔ (a : ℤ) - b < (c : ℤ) - d := by omega

theorem natural_difference_le (a b c d : ℕ) :
    a + d ≤ c + b ↔ (a : ℤ) - b ≤ (c : ℤ) - d := by omega

theorem natural_difference_sign (a b : ℕ) :
    ((if b < a then 1 else 0 : ℕ) : ℤ) - ((if a < b then 1 else 0 : ℕ) : ℤ) =
      if 0 < (a : ℤ) - b then 1 else if (a : ℤ) - b < 0 then -1 else 0 := by
  split_ifs <;> norm_num <;> omega

theorem eval_absNat (ν : Fin n → ℕ) (a : SignedExpr n) :
    (Arithmetic.eval ν (absNat a) : ℤ) = |eval ν a| :=
  natural_difference_abs (Arithmetic.eval ν a.positive) (Arithmetic.eval ν a.negative)

@[simp] theorem eval_eq (ν : Fin n → ℕ) (a b : SignedExpr n) :
    Arithmetic.eval ν (eq a b) = decide (eval ν a = eval ν b) := by
  simp only [eval, eq, Arithmetic.eval]
  congr 1
  apply propext
  exact natural_difference_eq _ _ _ _

@[simp] theorem eval_lt (ν : Fin n → ℕ) (a b : SignedExpr n) :
    Arithmetic.eval ν (lt a b) = decide (eval ν a < eval ν b) := by
  simp only [eval, lt, Arithmetic.eval]
  congr 1
  apply propext
  exact natural_difference_lt _ _ _ _

@[simp] theorem eval_le (ν : Fin n → ℕ) (a b : SignedExpr n) :
    Arithmetic.eval ν (le a b) = decide (eval ν a ≤ eval ν b) := by
  simp only [eval, le, Arithmetic.eval]
  congr 1
  apply propext
  exact natural_difference_le _ _ _ _

theorem eval_sign (ν : Fin n → ℕ) (a : SignedExpr n) :
    eval ν (sign a) = if 0 < eval ν a then 1 else if eval ν a < 0 then -1 else 0 := by
  simpa only [eval, sign, Arithmetic.eval, decide_eq_true_eq] using
    natural_difference_sign (Arithmetic.eval ν a.positive) (Arithmetic.eval ν a.negative)

end SignedExpr
end ProteinFolding.Tetrahedral.ReductionTM2.Arithmetic
