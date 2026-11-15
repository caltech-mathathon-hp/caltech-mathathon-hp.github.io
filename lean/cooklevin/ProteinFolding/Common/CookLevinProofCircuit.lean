import ProteinFolding.Common.CookLevin

/-!
The propositional part of Cook--Levin: a linear-size Tseitin encoding of
straight-line Boolean programs, with pinned input variables and a designated
true output. This file proves the encoding and its size bounds. Compiling
bounded TM2 executions into these programs and proving the emitting machine's
polynomial runtime remain separate obligations; no Cook--Levin theorem is
asserted merely from this circuit compiler.
-/

namespace ProteinFolding.SAT

namespace CookLevinCircuit

open Computability

def Satisfied (a : ℕ → Bool) (φ : CNF) : Prop :=
  ∀ c ∈ φ, ∃ l ∈ c, l.eval a = true

theorem satisfied_append (a : ℕ → Bool) (φ ψ : CNF) :
    Satisfied a (φ ++ ψ) ↔ Satisfied a φ ∧ Satisfied a ψ := by
  simp only [Satisfied, List.mem_append, or_imp, forall_and]

def positive (i : ℕ) : Literal := ⟨i, true⟩
def negative (i : ℕ) : Literal := ⟨i, false⟩

theorem positive_eval (a : ℕ → Bool) (i : ℕ) : (positive i).eval a = a i := rfl
theorem negative_eval (a : ℕ → Bool) (i : ℕ) : (negative i).eval a = !(a i) := rfl

inductive Gate where
  | constant : Bool → Gate
  | copy : ℕ → Gate
  | not : ℕ → Gate
  | and : ℕ → ℕ → Gate
  | or : ℕ → ℕ → Gate
  deriving DecidableEq, Repr

def Gate.eval (a : ℕ → Bool) : Gate → Bool
  | .constant b => b
  | .copy i => a i
  | .not i => !(a i)
  | .and i j => a i && a j
  | .or i j => a i || a j

def Gate.Below (n : ℕ) : Gate → Prop
  | .constant _ => True
  | .copy i | .not i => i < n
  | .and i j | .or i j => i < n ∧ j < n

def Gate.clauses (out : ℕ) : Gate → CNF
  | .constant true => [[positive out]]
  | .constant false => [[negative out]]
  | .copy i => [[negative out, positive i], [positive out, negative i]]
  | .not i => [[negative out, negative i], [positive out, positive i]]
  | .and i j =>
    [[negative out, positive i], [negative out, positive j],
      [positive out, negative i, negative j]]
  | .or i j =>
    [[positive out, negative i], [positive out, negative j],
      [negative out, positive i, positive j]]

theorem gate_clauses_iff (a : ℕ → Bool) (out : ℕ) (g : Gate) :
    Satisfied a (g.clauses out) ↔ a out = g.eval a := by
  cases g with
  | constant b => cases b <;> cases ho : a out <;> simp [Gate.clauses, Gate.eval, Satisfied,
      positive, negative, Literal.eval, ho]
  | copy i | not i => cases ho : a out <;> cases hi : a i <;>
      simp [Gate.clauses, Gate.eval, Satisfied, positive, negative, Literal.eval, ho, hi]
  | and i j | or i j => cases ho : a out <;> cases hi : a i <;> cases hj : a j <;>
      simp [Gate.clauses, Gate.eval, Satisfied, positive, negative, Literal.eval, ho, hi, hj]

theorem gate_eval_congr {n : ℕ} {a b : ℕ → Bool} (hab : ∀ i < n, a i = b i)
    {g : Gate} (hg : g.Below n) : g.eval a = g.eval b := by
  cases g with
  | constant b => rfl
  | copy i => exact hab i hg
  | not i => exact congrArg Bool.not (hab i hg)
  | and i j => simp only [Gate.eval, hab i hg.1, hab j hg.2]
  | or i j => simp only [Gate.eval, hab i hg.1, hab j hg.2]

def WellFormed : ℕ → List Gate → Prop
  | _, [] => True
  | n, g :: gs => g.Below n ∧ WellFormed (n + 1) gs

def compile : ℕ → List Gate → CNF
  | _, [] => []
  | n, g :: gs => g.clauses n ++ compile (n + 1) gs

def execute : ℕ → List Gate → (ℕ → Bool) → (ℕ → Bool)
  | _, [], a => a
  | n, g :: gs, a => execute (n + 1) gs (Function.update a n (g.eval a))

theorem execute_preserves (n : ℕ) (gs : List Gate) (a : ℕ → Bool) :
    ∀ i < n, execute n gs a i = a i := by
  induction gs generalizing n a with
  | nil => intro i _; rfl
  | cons g gs ih =>
    intro i hi
    rw [execute, ih (n + 1) _ i (by omega), Function.update_of_ne (by omega)]

theorem execute_satisfies {n : ℕ} {gs : List Gate} (hw : WellFormed n gs)
    (a : ℕ → Bool) : Satisfied (execute n gs a) (compile n gs) := by
  induction gs generalizing n a with
  | nil => simp [compile, Satisfied]
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := hw
    rw [compile, satisfied_append]
    refine ⟨?_, ih hgs _⟩
    apply (gate_clauses_iff _ n g).2
    have hout := execute_preserves (n + 1) gs (Function.update a n (g.eval a)) n (by omega)
    have hin : ∀ i < n, execute (n + 1) gs (Function.update a n (g.eval a)) i = a i := by
      intro i hi
      rw [execute_preserves _ _ _ i (by omega), Function.update_of_ne (by omega)]
    change execute (n + 1) gs (Function.update a n (g.eval a)) n = _
    rw [hout, Function.update_self]
    exact (gate_eval_congr hin hg).symm

theorem execute_fixed {n : ℕ} {gs : List Gate} {a : ℕ → Bool}
    (ha : Satisfied a (compile n gs)) : execute n gs a = a := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := (satisfied_append a _ _).1 ha
    have hg' := (gate_clauses_iff a n g).1 hg
    have hu : Function.update a n (g.eval a) = a := by
      rw [← hg', Function.update_eq_self]
    rw [execute, hu]
    exact ih hgs

def pins (bindings : List (ℕ × Bool)) : CNF :=
  bindings.map (fun b => [⟨b.1, b.2⟩])

def Matches (a : ℕ → Bool) (bindings : List (ℕ × Bool)) : Prop :=
  ∀ b ∈ bindings, a b.1 = b.2

theorem pins_iff (a : ℕ → Bool) (bindings : List (ℕ × Bool)) :
    Satisfied a (pins bindings) ↔ Matches a bindings := by
  simp only [Satisfied, pins, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    List.mem_singleton, exists_eq_left, Literal.eval]
  constructor
  · intro h b hb
    have hi := h b hb
    cases hbit : b.2 <;> simp_all
  · intro h b hb
    have hi := h b hb
    cases hbit : b.2 <;> simp_all

def outputFormula (n : ℕ) (gs : List Gate) (bindings : List (ℕ × Bool)) (out : ℕ) : CNF :=
  pins bindings ++ compile n gs ++ [[positive out]]

theorem outputFormula_satisfiable_iff {n : ℕ} {gs : List Gate}
    (hw : WellFormed n gs) (bindings : List (ℕ × Bool))
    (hb : ∀ b ∈ bindings, b.1 < n) (out : ℕ) :
    Satisfiable (outputFormula n gs bindings out) ↔
      ∃ a : ℕ → Bool, Matches a bindings ∧ execute n gs a out = true := by
  constructor
  · rintro ⟨a, ha⟩
    have h₁ := (satisfied_append a _ _).mp ha
    have h₂ := (satisfied_append a _ _).mp h₁.1
    have hsplit : Satisfied a (pins bindings) ∧ Satisfied a (compile n gs) ∧ a out = true := by
      refine ⟨h₂.1, h₂.2, ?_⟩
      simpa [Satisfied, positive_eval] using h₁.2
    refine ⟨a, (pins_iff a bindings).1 hsplit.1, ?_⟩
    rw [execute_fixed hsplit.2.1]
    exact hsplit.2.2
  · rintro ⟨a, ha, hout⟩
    refine ⟨execute n gs a, ?_⟩
    have hp : Satisfied (execute n gs a) (pins bindings) := by
      apply (pins_iff _ _).2
      intro b hmem
      rw [execute_preserves n gs a b.1 (hb b hmem)]
      exact ha b hmem
    have hg := execute_satisfies hw a
    change Satisfied (execute n gs a) (outputFormula n gs bindings out)
    apply (satisfied_append _ _ _).mpr
    refine ⟨(satisfied_append _ _ _).mpr ⟨hp, hg⟩, ?_⟩
    simpa [Satisfied, positive_eval] using hout

theorem gate_clause_count (g : Gate) (out : ℕ) : (g.clauses out).length ≤ 3 := by
  cases g with
  | constant b => cases b <;> simp [Gate.clauses]
  | copy i | not i | and i j | or i j => simp [Gate.clauses]

theorem gate_literal_count (g : Gate) (out : ℕ) : (g.clauses out).flatten.length ≤ 7 := by
  cases g with
  | constant b => cases b <;> simp [Gate.clauses]
  | copy i | not i | and i j | or i j => simp [Gate.clauses]

theorem gate_clause_width (g : Gate) (out : ℕ) : ∀ c ∈ g.clauses out, c.length ≤ 3 := by
  cases g with
  | constant b => cases b <;> simp [Gate.clauses]
  | copy i | not i | and i j | or i j => simp [Gate.clauses]

theorem compile_clause_count (n : ℕ) (gs : List Gate) : (compile n gs).length ≤ 3 * gs.length := by
  induction gs generalizing n with
  | nil => simp [compile]
  | cons g gs ih =>
    have h := gate_clause_count g n
    have ht := ih (n + 1)
    simp only [compile, List.length_append, List.length_cons]
    omega

theorem compile_literal_count (n : ℕ) (gs : List Gate) : (compile n gs).flatten.length ≤ 7 * gs.length := by
  induction gs generalizing n with
  | nil => simp [compile]
  | cons g gs ih =>
    have h := gate_literal_count g n
    have ht := ih (n + 1)
    simp only [compile, List.flatten_append, List.length_append, List.length_cons]
    omega

theorem compile_clause_width (n : ℕ) (gs : List Gate) : ∀ c ∈ compile n gs, c.length ≤ 3 := by
  induction gs generalizing n with
  | nil => simp [compile]
  | cons g gs ih =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact gate_clause_width g n c hc
    · exact ih (n + 1) c hc

theorem outputFormula_clause_count (n : ℕ) (gs : List Gate) (bindings : List (ℕ × Bool)) (out : ℕ) :
    (outputFormula n gs bindings out).length ≤ bindings.length + 3 * gs.length + 1 := by
  have h := compile_clause_count n gs
  simp only [outputFormula, List.length_append, pins, List.length_map, List.length_cons, List.length_nil]
  omega

theorem pins_literal_count (bindings : List (ℕ × Bool)) : (pins bindings).flatten.length = bindings.length := by
  induction bindings with
  | nil => rfl
  | cons b bindings ih =>
    change (List.flatten ([⟨b.1, b.2⟩] :: pins bindings)).length = _
    simpa using congrArg Nat.succ ih

theorem outputFormula_literal_count (n : ℕ) (gs : List Gate) (bindings : List (ℕ × Bool)) (out : ℕ) :
    (outputFormula n gs bindings out).flatten.length ≤ bindings.length + 7 * gs.length + 1 := by
  have h := compile_literal_count n gs
  simp only [outputFormula, List.flatten_append, List.length_append, pins_literal_count,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.length_cons, List.length_nil]
  omega

theorem gate_vars_lt {n : ℕ} {g : Gate} (hg : g.Below n) (out : ℕ) :
    ∀ c ∈ g.clauses out, ∀ l ∈ c, l.var = out ∨ l.var < n := by
  cases g with
  | constant b => cases b <;> simp [Gate.clauses, positive, negative]
  | copy i | not i => simp_all [Gate.Below, Gate.clauses, positive, negative]
  | and i j | or i j => simp_all [Gate.Below, Gate.clauses, positive, negative]

theorem compile_vars_lt {n : ℕ} {gs : List Gate} (hw : WellFormed n gs) :
    ∀ c ∈ compile n gs, ∀ l ∈ c, l.var < n + gs.length := by
  induction gs generalizing n with
  | nil => simp [compile]
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := hw
    intro c hc l hl
    rcases List.mem_append.mp hc with hc | hc
    · have h := gate_vars_lt hg n c hc l hl
      simp only [List.length_cons]
      omega
    · have h := ih hgs c hc l hl
      simp only [List.length_cons]
      omega

theorem encodePosNum_length_le (n : PosNum) : (encodePosNum n).length ≤ (n : ℕ) := by
  induction n with
  | one => decide
  | bit0 n ih =>
    have hp := PosNum.to_nat_pos n
    simp only [encodePosNum, List.length_cons, PosNum.cast_bit0]
    omega
  | bit1 n ih =>
    simp only [encodePosNum, List.length_cons, PosNum.cast_bit1]
    omega

theorem encodeNum_length_le (n : Num) : (encodeNum n).length ≤ (n : ℕ) := by
  cases n with
  | zero => decide
  | pos n => exact encodePosNum_length_le n

theorem encodeNat_length_le (n : ℕ) : (encodeNat n).length ≤ n := by
  simpa [encodeNat] using encodeNum_length_le (n : Num)

theorem encodeLit_length_le (l : Literal) : (encodeLit l).length ≤ l.var + 1 := by
  obtain ⟨v, b⟩ := l
  have h := encodeNat_length_le v
  cases b <;> simp [encodeLit] <;> omega

theorem encTerminated_length_bound {A B : Type} (terminator : B) (enc : A → List B)
    (xs : List A) (L : ℕ) (h : ∀ x ∈ xs, (enc x).length ≤ L) :
    (encTerminated terminator enc xs).length ≤ xs.length * (L + 1) := by
  induction xs with
  | nil => simp [encTerminated]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [encTerminated, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil, Nat.add_mul]
    change (enc x).length + 1 + (encTerminated terminator enc xs).length ≤ _
    omega

theorem encodeClause_length_bound (c : Clause) (V : ℕ) (h : ∀ l ∈ c, l.var ≤ V) :
    (encodeClause c).length ≤ c.length * (V + 2) := by
  have hb : ∀ l ∈ c, (encodeLit l).length ≤ V + 1 := by
    intro l hl
    exact (encodeLit_length_le l).trans (Nat.add_le_add_right (h l hl) 1)
  exact encTerminated_length_bound Sym.endLit encodeLit c (V + 1) hb

theorem cnfEncoding_length_bound (φ : CNF) (V : ℕ)
    (h : ∀ c ∈ φ, ∀ l ∈ c, l.var ≤ V) :
    (cnfEncoding.encode φ).length ≤ φ.flatten.length * (V + 2) + φ.length := by
  induction φ with
  | nil => simp [cnfEncoding, encTerminated]
  | cons c φ ih =>
    have hc := encodeClause_length_bound c V (h c (List.mem_cons_self ..))
    have ht := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    change (encTerminated Sym.endClause encodeClause φ).length ≤ _ at ht
    change ((encodeClause c ++ [Sym.endClause]) ++
      encTerminated Sym.endClause encodeClause φ).length ≤ _
    simp only [List.length_append, List.flatten_cons,
      List.length_cons, List.length_nil, Nat.add_mul]
    omega

theorem outputFormula_vars_lt {n : ℕ} {gs : List Gate} (hw : WellFormed n gs)
    (bindings : List (ℕ × Bool)) (hb : ∀ b ∈ bindings, b.1 < n)
    (out : ℕ) (hout : out < n + gs.length) :
    ∀ c ∈ outputFormula n gs bindings out, ∀ l ∈ c, l.var < n + gs.length := by
  intro c hc l hl
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hc
      have he := List.mem_singleton.mp hl
      subst l
      have hv := hb b hb'
      change b.1 < _
      omega
    · exact compile_vars_lt hw c hc l hl
  · have he := List.mem_singleton.mp hc
    subst c
    have he := List.mem_singleton.mp hl
    subst l
    exact hout

/-- A polynomial bound for the actual frozen binary CNF representation,
not just for the number of gates or abstract literals. -/
theorem outputFormula_encoded_length_bound {n : ℕ} {gs : List Gate} (hw : WellFormed n gs)
    (bindings : List (ℕ × Bool)) (hb : ∀ b ∈ bindings, b.1 < n)
    (out : ℕ) (hout : out < n + gs.length) :
    (cnfEncoding.encode (outputFormula n gs bindings out)).length ≤
      (bindings.length + 7 * gs.length + 1) * (n + gs.length + 2) +
        (bindings.length + 3 * gs.length + 1) := by
  have hv := outputFormula_vars_lt hw bindings hb out hout
  have he := cnfEncoding_length_bound (outputFormula n gs bindings out) (n + gs.length)
    (fun c hc l hl => Nat.le_of_lt (hv c hc l hl))
  have hclauses := outputFormula_clause_count n gs bindings out
  have hliterals := outputFormula_literal_count n gs bindings out
  exact he.trans (Nat.add_le_add (Nat.mul_le_mul_right (n + gs.length + 2) hliterals) hclauses)

-- Shared wires and input pinning exercise the straight-line semantics.
example : ¬ Satisfiable (outputFormula 1 [.not 0, .and 0 1] [] 2) := by
  rw [outputFormula_satisfiable_iff (by simp [WellFormed, Gate.Below]) [] (by simp) 2]
  rintro ⟨a, _, ha⟩
  cases h : a 0 <;> simp [execute, Gate.eval, Function.update, h] at ha

example : Satisfiable (outputFormula 1 [.not 0] [(0, false)] 1) := by
  apply (outputFormula_satisfiable_iff (by simp [WellFormed, Gate.Below]) [(0, false)] (by simp) 1).mpr
  refine ⟨fun _ => false, ?_, ?_⟩
  · simp [Matches]
  · simp [execute, Gate.eval, Function.update]

-- Output variable zero is valid when the first instruction is constant.
example : ¬ Satisfiable (outputFormula 0 [.constant false] [] 0) := by
  rw [outputFormula_satisfiable_iff (by simp [WellFormed, Gate.Below]) [] (by simp) 0]
  simp [execute, Gate.eval, Function.update]

end CookLevinCircuit

end ProteinFolding.SAT
