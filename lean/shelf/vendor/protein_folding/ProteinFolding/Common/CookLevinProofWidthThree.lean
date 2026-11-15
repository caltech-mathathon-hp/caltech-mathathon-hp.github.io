import ProteinFolding.Common.CookLevinProofCircuit
import ProteinFolding.Common.SAT.ThreeCNF
import Mathlib.Data.List.OfFn

/-! Width-three chains with affine auxiliary identifiers. Original indices
are retained. For clauses of fixed maximum width Q, clause j receives Q+1
private flags beginning at V+j*(Q+1), above all original variables <V.
The later fixed-template compiler emits these chains directly. -/

namespace ProteinFolding.SAT.CookLevinWidthThree

open CookLevinCircuit

def flag (Q V j k : ℕ) : ℕ := V + j * (Q + 1) + k

def chain (base : ℕ) : ℕ → Clause → CNF
  | k, [] => [[negative (base + k)]]
  | k, l :: ls => [negative (base + k), l, positive (base + (k + 1))] :: chain base (k + 1) ls

def gadget (base : ℕ) (c : Clause) : CNF := [positive base] :: chain base 0 c

def clauseValue (a : ℕ → Bool) (c : Clause) : Bool := c.any (Literal.eval a)

theorem chain_width (base k : ℕ) (c : Clause) : ThreeCNF.WidthAtMostThree (chain base k c) := by
  induction c generalizing k with
  | nil => simp [chain, ThreeCNF.WidthAtMostThree]
  | cons l ls ih => simpa [chain, ThreeCNF.WidthAtMostThree] using ih (k + 1)

theorem gadget_width (base : ℕ) (c : Clause) : ThreeCNF.WidthAtMostThree (gadget base c) := by
  simpa [gadget, ThreeCNF.WidthAtMostThree] using chain_width base 0 c

theorem chain_sound (a : ℕ → Bool) (base k : ℕ) (c : Clause)
    (h : Satisfied a (chain base k c)) (hf : a (base + k) = true) :
    ∃ l ∈ c, l.eval a = true := by
  induction c generalizing k with
  | nil =>
    obtain ⟨l, hl, he⟩ := h [negative (base + k)] (by simp [chain])
    simp only [List.mem_singleton] at hl
    subst l
    simp [negative, Literal.eval, hf] at he
  | cons l ls ih =>
    obtain ⟨v, hv, he⟩ := h [negative (base + k), l, positive (base + (k + 1))] (by simp [chain])
    have ht : Satisfied a (chain base (k + 1) ls) := fun d hd => h d (by simp [chain, hd])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with hv | hv | hv
    · rw [hv] at he
      simp [negative, Literal.eval, hf] at he
    · exact ⟨l, List.mem_cons_self .., by simpa only [hv] using he⟩
    · rw [hv] at he
      obtain ⟨v, hv, he⟩ := ih (k + 1) ht (by simpa [positive, Literal.eval] using he)
      exact ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem gadget_sound (a : ℕ → Bool) (base : ℕ) (c : Clause) (h : Satisfied a (gadget base c)) :
    ∃ l ∈ c, l.eval a = true := by
  have hf := h [positive base] (by simp [gadget])
  apply chain_sound a base 0 c (fun d hd => h d (by simp [gadget, hd]))
  simpa [positive, Literal.eval] using hf

theorem chain_complete (a b : ℕ → Bool) (base : ℕ) (C : Clause)
    (hOld : ∀ l ∈ C, l.eval b = l.eval a)
    (hFlags : ∀ s ≤ C.length, b (base + s) = clauseValue a (C.drop s))
    (k : ℕ) (c : Clause) (hk : k ≤ C.length) (hc : C.drop k = c) :
    Satisfied b (chain base k c) := by
  induction c generalizing k with
  | nil =>
    intro d hd
    simp only [chain, List.mem_singleton] at hd
    subst d
    refine ⟨negative (base + k), by simp, ?_⟩
    change Bool.not (b (base + k)) = true
    rw [hFlags k hk, hc]
    rfl
  | cons l ls ih =>
    have hnext : C.drop (k + 1) = ls := by
      have hh := congrArg (List.drop 1) hc
      simpa [List.drop_drop, Nat.add_comm] using hh
    have hk' : k + 1 ≤ C.length := by
      have hl := congrArg List.length hc
      simp only [List.length_drop, List.length_cons] at hl
      omega
    have hlC : l ∈ C := List.mem_of_mem_drop (by rw [hc]; simp)
    intro d hd
    simp only [chain, List.mem_cons] at hd
    rcases hd with rfl | hd
    · by_cases hl : l.eval a = true
      · exact ⟨l, by simp, by rw [hOld l hlC]; exact hl⟩
      · by_cases ht : clauseValue a ls = true
        · refine ⟨positive (base + (k + 1)), by simp, ?_⟩
          change b (base + (k + 1)) = true
          rw [hFlags (k + 1) hk', hnext]
          exact ht
        · refine ⟨negative (base + k), by simp, ?_⟩
          have hlf : l.eval a = false := Bool.eq_false_iff.mpr hl
          have htf : clauseValue a ls = false := Bool.eq_false_iff.mpr ht
          change Bool.not (b (base + k)) = true
          rw [hFlags k hk, hc]
          change Bool.not (l.eval a || clauseValue a ls) = true
          rw [hlf, htf]
          rfl
    · exact ih (k + 1) hk' hnext d hd

theorem gadget_complete (a b : ℕ → Bool) (base : ℕ) (c : Clause)
    (hOld : ∀ l ∈ c, l.eval b = l.eval a)
    (hFlags : ∀ s ≤ c.length, b (base + s) = clauseValue a (c.drop s))
    (hc : ∃ l ∈ c, l.eval a = true) : Satisfied b (gadget base c) := by
  intro d hd
  simp only [gadget, List.mem_cons] at hd
  rcases hd with rfl | hd
  · refine ⟨positive base, by simp, ?_⟩
    change b base = true
    simpa only [Nat.add_zero, List.drop_zero] using
      (hFlags 0 (Nat.zero_le _)).trans (List.any_eq_true.mpr hc)
  · exact chain_complete a b base c hOld hFlags 0 c (Nat.zero_le _) (by simp) d hd

def transform (Q V : ℕ) (φ : CNF) : CNF :=
  (List.ofFn (fun j : Fin φ.length => gadget (flag Q V j.val 0) (φ.get j))).flatten

def extend (Q V : ℕ) (φ : CNF) (a : ℕ → Bool) (v : ℕ) : Bool :=
  if v < V then a v else match φ[(v - V) / (Q + 1)]? with
    | none => false
    | some c => clauseValue a (c.drop ((v - V) % (Q + 1)))

theorem extend_old (Q V : ℕ) (φ : CNF) (a : ℕ → Bool) (v : ℕ) (hv : v < V) :
    extend Q V φ a v = a v := by simp [extend, hv]

theorem flag_div (Q V j k : ℕ) (hk : k ≤ Q) : (flag Q V j k - V) / (Q + 1) = j := by
  have hs : flag Q V j k - V = j * (Q + 1) + k := by unfold flag; omega
  rw [hs, Nat.add_comm (j * (Q + 1)), Nat.add_mul_div_right _ _ (by omega),
    Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem flag_mod (Q V j k : ℕ) (hk : k ≤ Q) : (flag Q V j k - V) % (Q + 1) = k := by
  have hs : flag Q V j k - V = j * (Q + 1) + k := by unfold flag; omega
  rw [hs]
  simp [Nat.mod_eq_of_lt (show k < Q + 1 by omega)]

theorem flag_injective (Q V j j' k k' : ℕ) (hk : k ≤ Q) (hk' : k' ≤ Q)
    (h : flag Q V j k = flag Q V j' k') : j = j' ∧ k = k' := by
  have hd := congrArg (fun v => (v - V) / (Q + 1)) h
  have hm := congrArg (fun v => (v - V) % (Q + 1)) h
  dsimp only at hd hm
  rw [flag_div Q V j k hk, flag_div Q V j' k' hk'] at hd
  rw [flag_mod Q V j k hk, flag_mod Q V j' k' hk'] at hm
  exact ⟨hd, hm⟩

theorem flag_ge (Q V j k : ℕ) : V ≤ flag Q V j k := by unfold flag; omega

theorem flag_lt (Q V N j k : ℕ) (hj : j < N) (hk : k ≤ Q) :
    flag Q V j k < V + N * (Q + 1) := by
  have hm := Nat.mul_le_mul_right (Q + 1) (show j + 1 ≤ N by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hm
  unfold flag
  omega

theorem extend_flag (Q V : ℕ) (φ : CNF) (a : ℕ → Bool) (j : Fin φ.length)
    (k : ℕ) (hk : k ≤ Q) : extend Q V φ a (flag Q V j.val k) = clauseValue a ((φ.get j).drop k) := by
  have hn : ¬ flag Q V j.val k < V := by have := flag_ge Q V j.val k; omega
  simp [extend, hn, flag_div Q V j.val k hk, flag_mod Q V j.val k hk, j.isLt]

theorem transform_width (Q V : ℕ) (φ : CNF) : ThreeCNF.WidthAtMostThree (transform Q V φ) := by
  intro c hc
  obtain ⟨g, hg, hc⟩ := List.mem_flatten.mp hc
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  exact gadget_width (flag Q V j.val 0) (φ.get j) c hc

theorem transform_sound (Q V : ℕ) (φ : CNF) (a : ℕ → Bool)
    (h : Satisfied a (transform Q V φ)) : Satisfied a φ := by
  intro c hc
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hc
  apply gadget_sound a (flag Q V j.val 0) (φ.get j)
  intro d hd
  exact h d (List.mem_flatten.mpr ⟨gadget (flag Q V j.val 0) (φ.get j),
    List.mem_ofFn.mpr ⟨j, rfl⟩, hd⟩)

theorem transform_complete (Q V : ℕ) (φ : CNF)
    (hWidth : ∀ c ∈ φ, c.length ≤ Q) (hVars : ∀ c ∈ φ, ∀ l ∈ c, l.var < V)
    (a : ℕ → Bool) (ha : Satisfied a φ) : Satisfied (extend Q V φ a) (transform Q V φ) := by
  intro d hd
  obtain ⟨g, hg, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  apply gadget_complete a (extend Q V φ a) (flag Q V j.val 0) (φ.get j) ?_ ?_ (ha _ (List.get_mem ..)) d hd
  · intro l hl
    have hv := hVars (φ.get j) (List.get_mem ..) l hl
    simp only [Literal.eval, extend_old Q V φ a l.var hv]
  · intro s hs
    have hsq : s ≤ Q := hs.trans (hWidth (φ.get j) (List.get_mem ..))
    simpa only [flag, Nat.add_zero] using extend_flag Q V φ a j s hsq

theorem transform_equisatisfiable (Q V : ℕ) (φ : CNF)
    (hWidth : ∀ c ∈ φ, c.length ≤ Q) (hVars : ∀ c ∈ φ, ∀ l ∈ c, l.var < V) :
    Satisfiable (transform Q V φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, transform_sound Q V φ a ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨extend Q V φ a, transform_complete Q V φ hWidth hVars a ha⟩

end ProteinFolding.SAT.CookLevinWidthThree
