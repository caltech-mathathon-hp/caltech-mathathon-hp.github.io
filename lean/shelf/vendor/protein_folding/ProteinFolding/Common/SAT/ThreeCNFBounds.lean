import ProteinFolding.Common.SAT.ThreeCNF
import Mathlib.Tactic.Linarith

/-! Size bounds for the width-three transformation under the frozen binary
CNF encoding. Renaming an original index doubles its value and adds at most
one binary digit; fresh indices depend only on clause and occurrence counts.
An output-length bound is not asserted to be a TM2 time bound. -/

namespace ProteinFolding.SAT.ThreeCNF

open Computability

theorem encodeNat_double_length (v : ℕ) :
    (encodeNat (2 * v)).length ≤ (encodeNat v).length + 1 := by
  let n : Num := v
  have hn : (n : ℕ) = v := Num.to_of_nat v
  rw [← hn, ← Num.cast_bit0]
  simp only [encodeNat, Num.of_to_nat]
  cases n with
  | zero => simp [Num.bit0, encodeNum]
  | pos n => simp [Num.bit0, encodeNum, encodePosNum]

theorem encodePosNum_length_le (n : PosNum) : (encodePosNum n).length ≤ (n : ℕ) := by
  induction n with
  | one => simp [encodePosNum]
  | bit0 n ih =>
    have hn := PosNum.to_nat_pos n
    simp only [encodePosNum, List.length_cons, PosNum.cast_bit0]
    omega
  | bit1 n ih =>
    simp only [encodePosNum, List.length_cons, PosNum.cast_bit1]
    omega

theorem encodeNat_length_le (v : ℕ) : (encodeNat v).length ≤ v := by
  let n : Num := v
  have hn : (n : ℕ) = v := Num.to_of_nat v
  rw [← hn]
  simp only [encodeNat, Num.of_to_nat]
  cases n with
  | zero => rfl
  | pos n => exact encodePosNum_length_le n

theorem liftLiteral_length (l : Literal) :
    (encodeLit (liftLiteral l)).length ≤ (encodeLit l).length + 1 := by
  have h := encodeNat_double_length l.var
  cases hp : l.pos <;> simp [encodeLit, liftLiteral, hp] <;> omega

theorem encodeClause_cons_length (l : Literal) (ls : Clause) :
    (encodeClause (l :: ls)).length = (encodeLit l).length + 1 + (encodeClause ls).length := by
  simp [encodeClause, encTerminated]
  omega

theorem cnfEncoding_cons_length (c : Clause) (φ : CNF) :
    (cnfEncoding.encode (c :: φ)).length =
      (encodeClause c).length + 1 + (cnfEncoding.encode φ).length := by
  simp [cnfEncoding, encTerminated]
  omega

theorem literal_length_le_clause (l : Literal) (c : Clause) (h : l ∈ c) :
    (encodeLit l).length ≤ (encodeClause c).length := by
  induction c with
  | nil => simp at h
  | cons v c ih =>
    rw [encodeClause_cons_length]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem clause_length_le_encoding (c : Clause) : c.length ≤ (encodeClause c).length := by
  induction c with
  | nil => simp [encodeClause, encTerminated]
  | cons l c ih => rw [List.length_cons, encodeClause_cons_length]; omega

theorem clause_encoding_le_formula (c : Clause) (φ : CNF) (h : c ∈ φ) :
    (encodeClause c).length ≤ (cnfEncoding.encode φ).length := by
  induction φ with
  | nil => simp at h
  | cons d φ ih =>
    rw [cnfEncoding_cons_length]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem formula_length_le_encoding (φ : CNF) : φ.length ≤ (cnfEncoding.encode φ).length := by
  induction φ with
  | nil => simp [cnfEncoding, encTerminated]
  | cons c φ ih => rw [List.length_cons, cnfEncoding_cons_length]; omega

theorem fresh_binary_length_le (j k N : ℕ) (hj : j ≤ N) (hk : k ≤ N) :
    (encodeNat (fresh j k)).length ≤ 2 * (N + 1) ^ 2 + 1 := by
  have hp := Nat.pair_lt_max_add_one_sq j k
  have hm : max j k + 1 ≤ N + 1 := by omega
  have hmul := Nat.mul_le_mul hm hm
  have he := encodeNat_length_le (fresh j k)
  dsimp [fresh] at he
  change (encodeNat (2 * Nat.pair j k + 1)).length ≤ _
  nlinarith

theorem chain_length (j k : ℕ) (c : Clause) : (chain j k c).length = c.length + 1 := by
  induction c generalizing k with
  | nil => rfl
  | cons l c ih => simp [chain, ih]

theorem gadget_length (j : ℕ) (c : Clause) : (gadget j c).length = c.length + 2 := by
  simp [gadget, chain_length]

theorem chain_literal (j k : ℕ) (c d : Clause) (l : Literal)
    (hd : d ∈ chain j k c) (hl : l ∈ d) :
    (∃ v ∈ c, l = liftLiteral v) ∨
      ∃ t, k ≤ t ∧ t ≤ k + c.length ∧
        (l = positive (fresh j t) ∨ l = negative (fresh j t)) := by
  induction c generalizing k with
  | nil =>
    simp only [chain, List.mem_singleton] at hd
    subst d
    simp only [List.mem_singleton] at hl
    exact Or.inr ⟨k, le_rfl, by simp, Or.inr hl⟩
  | cons v c ih =>
    simp only [chain, List.mem_cons] at hd
    rcases hd with rfl | hd
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact Or.inr ⟨k, le_rfl, by simp, Or.inr rfl⟩
      · exact Or.inl ⟨v, by simp, rfl⟩
      · exact Or.inr ⟨k + 1, by omega, by simp only [List.length_cons]; omega, Or.inl rfl⟩
    · rcases ih (k + 1) hd with h | ⟨t, ht, ht', he⟩
      · obtain ⟨v, hv, he⟩ := h
        exact Or.inl ⟨v, List.mem_cons_of_mem _ hv, he⟩
      · exact Or.inr ⟨t, by omega, by simp only [List.length_cons]; omega, he⟩

theorem formula_occurrences_length_le_encoding (φ : CNF) :
    φ.flatten.length + φ.length ≤ (cnfEncoding.encode φ).length := by
  induction φ with
  | nil => simp [cnfEncoding, encTerminated]
  | cons c φ ih =>
    have hc := clause_length_le_encoding c
    rw [cnfEncoding_cons_length]
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem sum_lengths_add (φ : CNF) (n : ℕ) :
    (φ.map (fun c => c.length + n)).sum = φ.flatten.length + n * φ.length := by
  induction φ with
  | nil => simp
  | cons c φ ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append,
      List.length_cons, Nat.mul_succ, ih]
    omega

theorem transform_length (φ : CNF) :
    (transform φ).length = φ.flatten.length + 2 * φ.length := by
  simp only [transform, List.length_flatten, List.map_ofFn, Function.comp_def, gadget_length]
  have he : (List.ofFn fun j : Fin φ.length => (φ.get j).length + 2) =
      φ.map (fun c => c.length + 2) := by
    calc
      _ = (List.ofFn φ.get).map (fun c : Clause => c.length + 2) :=
        List.ofFn_comp' φ.get (fun c : Clause => c.length + 2)
      _ = _ := by rw [List.ofFn_get]
  rw [he]
  simpa only [List.length_flatten] using sum_lengths_add φ 2

theorem transform_length_le (φ : CNF) :
    (transform φ).length ≤ 2 * (cnfEncoding.encode φ).length := by
  rw [transform_length]
  have h := formula_occurrences_length_le_encoding φ
  omega

theorem gadget_literal_encoding_bound (φ : CNF) (j : Fin φ.length)
    (d : Clause) (l : Literal) (hd : d ∈ gadget j.val (φ.get j)) (hl : l ∈ d) :
    (encodeLit l).length ≤ 2 * ((cnfEncoding.encode φ).length + 1) ^ 2 + 2 := by
  let N := (cnfEncoding.encode φ).length
  have hj : j.val ≤ N := by
    have hj' := j.isLt
    have hf := formula_length_le_encoding φ
    omega
  have hc : (φ.get j).length ≤ N :=
    (clause_length_le_encoding _).trans (clause_encoding_le_formula _ _ (List.get_mem ..))
  simp only [gadget, List.mem_cons] at hd
  rcases hd with rfl | hd
  · simp only [List.mem_singleton] at hl
    subst l
    have hf := fresh_binary_length_le j.val 0 N hj (by omega)
    have hh : (encodeNat (fresh j.val 0)).length ≤
        2 * ((cnfEncoding.encode φ).length + 1) ^ 2 + 2 := by
      dsimp [N] at hf
      omega
    simpa [positive, encodeLit] using hh
  · rcases chain_literal j.val 0 (φ.get j) d l hd hl with ⟨v, hv, rfl⟩ | ⟨t, _, ht, he⟩
    · have hv' := literal_length_le_clause v (φ.get j) hv
      have hform := clause_encoding_le_formula (φ.get j) φ (List.get_mem ..)
      have h := liftLiteral_length v
      dsimp [N] at *
      nlinarith
    · have ht' : t ≤ N := by omega
      have hf := fresh_binary_length_le j.val t N hj ht'
      rcases he with rfl | rfl <;> simp [positive, negative, encodeLit] <;> dsimp [N] at * <;> omega

theorem clause_encoding_bound (c : Clause) (B : ℕ)
    (h : ∀ l ∈ c, (encodeLit l).length ≤ B) :
    (encodeClause c).length ≤ c.length * (B + 1) := by
  induction c with
  | nil => simp [encodeClause, encTerminated]
  | cons l c ih =>
    have hl := h l (by simp)
    have hc := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    rw [encodeClause_cons_length]
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem formula_encoding_bound (φ : CNF) (B : ℕ) (hw : WidthAtMostThree φ)
    (h : ∀ c ∈ φ, ∀ l ∈ c, (encodeLit l).length ≤ B) :
    (cnfEncoding.encode φ).length ≤ φ.length * (3 * (B + 1) + 1) := by
  induction φ with
  | nil => simp [cnfEncoding, encTerminated]
  | cons c φ ih =>
    have hc := (clause_encoding_bound c B (h c (by simp))).trans
      (Nat.mul_le_mul_right (B + 1) (hw c (by simp)))
    have hφ := ih (fun d hd => hw d (List.mem_cons_of_mem _ hd))
      (fun d hd => h d (List.mem_cons_of_mem _ hd))
    rw [cnfEncoding_cons_length]
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A cubic bound in the actual binary input encoding length. In particular,
large original variable indices do not lead to unary-size output fields. -/
theorem transform_encoding_length_bound (φ : CNF) :
    (cnfEncoding.encode (transform φ)).length ≤
      100 * ((cnfEncoding.encode φ).length + 1) ^ 3 := by
  let N := (cnfEncoding.encode φ).length
  let B := 2 * (N + 1) ^ 2 + 2
  have hl : ∀ c ∈ transform φ, ∀ l ∈ c, (encodeLit l).length ≤ B := by
    intro c hc l hl
    obtain ⟨g, hg, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    exact gadget_literal_encoding_bound φ j c l hc hl
  have hbound := formula_encoding_bound (transform φ) B (transform_width φ) hl
  have hlen := transform_length_le φ
  have hmul := Nat.mul_le_mul_right (3 * (B + 1) + 1) hlen
  have ht := hbound.trans hmul
  dsimp [N, B] at *
  nlinarith

end ProteinFolding.SAT.ThreeCNF
