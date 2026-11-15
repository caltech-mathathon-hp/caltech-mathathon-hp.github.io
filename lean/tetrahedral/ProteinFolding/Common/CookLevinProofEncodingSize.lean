import ProteinFolding.Common.CookLevinProofSize

/-! Bounds for the actual frozen binary CNF encoding of concrete TM2 runs,
including every variable index and both complete configuration boundaries.
-/

namespace ProteinFolding.SAT.CookLevinEncodingSize

open Turing TM2 CookLevinAlphabet CookLevinWindow CookLevinWindowCNF CookLevinCells
open CookLevinPaddedWindow CookLevinRows CookLevinStepCNF CookLevinGlobalCNF CookLevinSize
open CookLevinLocal CookLevinCircuit

theorem reference_lt (tm : FinTM2) (M t T : ℕ) (ht : t ≤ T) (b : Bit tm M) :
    reference tm M t b < (T + 1) * width tm M := by
  have hm := Nat.mul_le_mul_right (width tm M) ht
  have hb := (bitIndex tm M b).isLt
  simp only [reference, Nat.add_mul, Nat.one_mul]
  omega

theorem codeRefs_vars_lt {A : Type*} [Fintype A] (tm : FinTM2) (M t T : ℕ)
    (ht : t ≤ T) (tag : A → Bit tm M) :
    ∀ i ∈ codeRefs tm M t tag, i < (T + 1) * width tm M := by
  intro i hi
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hi
  exact reference_lt tm M t T ht b

theorem functionFactor_vars_lt {A B : Type*} [Fintype A] [Fintype B]
    (tm : FinTM2) (M t u T : ℕ) (ht : t ≤ T) (hu : u ≤ T)
    (tagA : A → Bit tm M) (tagB : B → Bit tm M) (f : A → B) :
    ∀ i ∈ (functionFactor tm M t u tagA tagB f).vars, i < (T + 1) * width tm M := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact codeRefs_vars_lt tm M t T ht tagA i hi
  · exact codeRefs_vars_lt tm M u T hu tagB i hi

theorem toCellFactor_vars_lt {A : Type*} [Fintype A]
    (tm : FinTM2) (M t T : ℕ) (ht : t ≤ T) (tag : A → Bit tm M)
    (k : tm.K) (n : ℕ) (f : A → Option (Symbol tm k)) :
    ∀ i ∈ (toCellFactor tm M t tag k n f).vars, i < (T + 1) * width tm M := by
  unfold toCellFactor
  split
  · exact functionFactor_vars_lt tm M t t T ht ht tag _ f
  · exact codeRefs_vars_lt tm M t T ht tag

theorem componentConstraint_vars_lt {A : Type*} [Fintype A]
    (tm : FinTM2) (M : ℕ) (tag : A → Bit tm M) :
    ∀ i ∈ (componentConstraint tm M tag).vars, i < width tm M := by
  intro i hi
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hi
  exact (bitIndex tm M b).isLt

theorem validityConstraints_vars_lt (tm : FinTM2) (M : ℕ) :
    ∀ c ∈ validityConstraints tm M, ∀ i ∈ c.vars, i < width tm M := by
  letI := tm.kFin
  intro c hc
  unfold validityConstraints at hc
  rcases List.mem_append.mp hc with hc | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact componentConstraint_vars_lt tm M _
  · obtain ⟨k, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨n, _, hc⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact componentConstraint_vars_lt tm M _

theorem rowConstraints_vars_lt (tm : FinTM2) (M t T : ℕ) (ht : t ≤ T) :
    ∀ c ∈ rowConstraints tm M t, ∀ i ∈ c.vars, i < (T + 1) * width tm M := by
  intro c hc i hi
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  have hv := validityConstraints_vars_lt tm M d hd j hj
  have hm := Nat.mul_le_mul_right (width tm M) ht
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem stepConstraints_vars_lt (tm : FinTM2) (M t T : ℕ) (ht : t < T) :
    ∀ c ∈ stepConstraints tm M t, ∀ i ∈ c.vars, i < (T + 1) * width tm M := by
  letI := tm.kFin
  have hle : t ≤ T := by omega
  have hnext : t + 1 ≤ T := by omega
  intro c hc i hi
  unfold stepConstraints at hc
  rcases List.mem_append.mp hc with hc | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact functionFactor_vars_lt tm M t t T hle hle _ _ _ i hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact codeRefs_vars_lt tm M t T hle _ i hi
      · exact codeRefs_vars_lt tm M t T hle _ i hi
    · exact functionFactor_vars_lt tm M t (t + 1) T hle hnext _ _ _ i hi
  · obtain ⟨k, _, hc⟩ := List.mem_flatMap.mp hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hc
      exact toCellFactor_vars_lt tm M t T hle _ _ _ _ i hi
    · obtain ⟨n, _, hc⟩ := List.mem_flatMap.mp hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
        exact toCellFactor_vars_lt tm M t T hle _ _ _ _ i hi
      · have he := List.mem_singleton.mp hc
        subst c
        rcases List.mem_append.mp hi with hi | hi
        · rcases List.mem_append.mp hi with hi | hi
          · exact codeRefs_vars_lt tm M t T hle _ i hi
          · exact codeRefs_vars_lt tm M t T hle _ i hi
        · exact codeRefs_vars_lt tm M (t + 1) T hnext _ i hi

theorem globalConstraints_vars_lt (tm : FinTM2) (M T : ℕ) :
    ∀ c ∈ globalConstraints tm M T, ∀ i ∈ c.vars, i < (T + 1) * width tm M := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
    exact rowConstraints_vars_lt tm M t T (by have h := List.mem_range.mp ht; omega) c hc
  · obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
    exact stepConstraints_vars_lt tm M t T (List.mem_range.mp ht) c hc

theorem globalCNF_vars_lt (tm : FinTM2) (M T : ℕ) :
    ∀ c ∈ globalCNF tm M T, ∀ l ∈ c, l.var < (T + 1) * width tm M := by
  intro c hc l hl
  obtain ⟨d, hd, hi⟩ := compileConstraints_vars (globalConstraints tm M T) c hc l hl
  exact globalConstraints_vars_lt tm M T d hd l.var hi

theorem componentPins_length {A : Type*} [Fintype A] (tm : FinTM2) (M t : ℕ)
    (tag : A → Bit tm M) (v : A) : (componentPins tm M t tag v).length = Fintype.card A := by
  simp [componentPins, codeRefs_length, finiteCode_length]

theorem flatMap_length_le {A B : Type*} (xs : List A) (f : A → List B) (N : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ N) : (xs.flatMap f).length ≤ xs.length * N := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    have hx := h x (List.mem_cons_self ..)
    have hs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

noncomputable def boundaryBound (tm : FinTM2) (M : ℕ) : ℕ :=
  letI := tm.kFin
  Fintype.card (Control tm) + Fintype.card tm.K * (M * domainBound tm)

theorem boundaryBindings_length (tm : FinTM2) (M t : ℕ) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) :
    (boundaryBindings tm M t c h).length ≤ boundaryBound tm M := by
  letI := tm.kFin
  have hi : ∀ k : tm.K,
      ((List.finRange M).flatMap (fun n => componentPins tm M t (cellTag tm M k n)
        ((CookLevinLinks.encodedStack tm c h k)[n.val]?))).length ≤ M * domainBound tm := by
    intro k
    have hp := flatMap_length_le (List.finRange M) (fun n => componentPins tm M t (cellTag tm M k n)
      ((CookLevinLinks.encodedStack tm c h k)[n.val]?)) (domainBound tm)
      (fun n _ => by simpa only [componentPins_length] using (domain_bounds tm).2.2.2 k |>.1)
    simpa only [List.length_finRange] using hp
  have ho := flatMap_length_le Finset.univ.toList
    (fun k => (List.finRange M).flatMap (fun n => componentPins tm M t (cellTag tm M k n)
      ((CookLevinLinks.encodedStack tm c h k)[n.val]?))) (M * domainBound tm) (fun k _ => hi k)
  unfold boundaryBindings boundaryBound
  rw [List.length_append, componentPins_length]
  exact Nat.add_le_add_left (by simpa using ho) _

theorem componentPins_vars_lt {A : Type*} [Fintype A] (tm : FinTM2) (M t T : ℕ)
    (ht : t ≤ T) (tag : A → Bit tm M) (v : A) :
    ∀ b ∈ componentPins tm M t tag v, b.1 < (T + 1) * width tm M := by
  intro b hb
  exact codeRefs_vars_lt tm M t T ht tag b.1 (List.of_mem_zip hb).1

theorem boundaryBindings_vars_lt (tm : FinTM2) (M t T : ℕ) (ht : t ≤ T) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) :
    ∀ b ∈ boundaryBindings tm M t c h, b.1 < (T + 1) * width tm M := by
  letI := tm.kFin
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact componentPins_vars_lt tm M t T ht _ _ b hb
  · obtain ⟨k, _, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨n, _, hb⟩ := List.mem_flatMap.mp hb
    exact componentPins_vars_lt tm M t T ht _ _ b hb

theorem pins_vars_lt (bindings : List (ℕ × Bool)) (N : ℕ)
    (h : ∀ b ∈ bindings, b.1 < N) : ∀ c ∈ pins bindings, ∀ l ∈ c, l.var < N := by
  intro c hc l hl
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  have he := List.mem_singleton.mp hl
  subst l
  exact h b hb

theorem runCNF_vars_lt (tm : FinTM2) (M T : ℕ) (input : List (tm.Γ tm.k₀))
    (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk) :
    ∀ c ∈ runCNF tm M T input final hf, ∀ l ∈ c, l.var < (T + 1) * width tm M := by
  intro c hc l hl
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · exact pins_vars_lt _ _ (boundaryBindings_vars_lt tm M 0 T (Nat.zero_le T) _ _) c hc l hl
    · exact globalCNF_vars_lt tm M T c hc l hl
  · exact pins_vars_lt _ _ (boundaryBindings_vars_lt tm M T T le_rfl _ _) c hc l hl

noncomputable def runClauseBound (tm : FinTM2) (M T : ℕ) : ℕ :=
  2 * boundaryBound tm M + constraintCount tm M T * 2 ^ (3 * domainBound tm)

noncomputable def runLiteralBound (tm : FinTM2) (M T : ℕ) : ℕ :=
  2 * boundaryBound tm M + (constraintCount tm M T * 2 ^ (3 * domainBound tm)) * (3 * domainBound tm)

theorem runCNF_clause_bound (tm : FinTM2) (M T : ℕ) (input : List (tm.Γ tm.k₀))
    (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk) :
    (runCNF tm M T input final hf).length ≤ runClauseBound tm M T := by
  have hi := boundaryBindings_length tm M 0 (initList tm input) (initList_stacksIn tm input)
  have hf' := boundaryBindings_length tm M T final hf
  have hg := globalCNF_clause_bound tm M T
  simp only [runCNF, List.length_append, pins, List.length_map, runClauseBound]
  omega

theorem runCNF_literal_bound (tm : FinTM2) (M T : ℕ) (input : List (tm.Γ tm.k₀))
    (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk) :
    (runCNF tm M T input final hf).flatten.length ≤ runLiteralBound tm M T := by
  have hi := boundaryBindings_length tm M 0 (initList tm input) (initList_stacksIn tm input)
  have hf' := boundaryBindings_length tm M T final hf
  have hg := globalCNF_literal_bound tm M T
  simp only [runCNF, List.flatten_append, List.length_append, pins_literal_count, runLiteralBound]
  omega

noncomputable def runEncodedBound (tm : FinTM2) (M T : ℕ) : ℕ :=
  runLiteralBound tm M T * ((T + 1) * width tm M + 2) + runClauseBound tm M T

/-- Bound for the frozen binary CNF encoding, including every index and pin. -/
theorem runCNF_encoded_bound (tm : FinTM2) (M T : ℕ) (input : List (tm.Γ tm.k₀))
    (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk) :
    (cnfEncoding.encode (runCNF tm M T input final hf)).length ≤ runEncodedBound tm M T := by
  have he := cnfEncoding_length_bound (runCNF tm M T input final hf) ((T + 1) * width tm M)
    (fun c hc l hl => (runCNF_vars_lt tm M T input final hf c hc l hl).le)
  exact he.trans (Nat.add_le_add
    (Nat.mul_le_mul_right _ (runCNF_literal_bound tm M T input final hf))
    (runCNF_clause_bound tm M T input final hf))

noncomputable def runBoundPolynomial (tm : FinTM2) (stack time : Polynomial ℕ) : Polynomial ℕ := by
  letI := tm.kFin
  let boundary := Polynomial.C (Fintype.card (Control tm)) +
    Polynomial.C (Fintype.card tm.K) * (stack * Polynomial.C (domainBound tm))
  let validity := Polynomial.C 3 + Polynomial.C (Fintype.card tm.K) * (stack * Polynomial.C 2)
  let transition := Polynomial.C 3 + Polynomial.C (Fintype.card tm.K) *
    (Polynomial.C (machineReadBound tm) + stack * (Polynomial.C (cellWindowWidth tm) + Polynomial.C 1))
  let count := (time + Polynomial.C 1) * validity + time * transition
  let clauses := Polynomial.C 2 * boundary + count * Polynomial.C (2 ^ (3 * domainBound tm))
  let literals := Polynomial.C 2 * boundary +
    (count * Polynomial.C (2 ^ (3 * domainBound tm))) * Polynomial.C (3 * domainBound tm)
  let varCount := (time + Polynomial.C 1) *
    (Polynomial.C (widthBase tm) + stack * Polynomial.C (widthSlope tm))
  exact literals * (varCount + Polynomial.C 2) + clauses

theorem runBoundPolynomial_eval (tm : FinTM2) (stack time : Polynomial ℕ) (n : ℕ) :
    (runBoundPolynomial tm stack time).eval n = runEncodedBound tm (stack.eval n) (time.eval n) := by
  letI := tm.kFin
  simp only [runBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    runEncodedBound, runLiteralBound, runClauseBound, boundaryBound, constraintCount,
    validityCount, stepCount, width_linear]

/-- A polynomial stack bound and horizon give a proved polynomial bound for
the actual binary encoding of the complete concrete machine-run CNF. -/
theorem runCNF_encoded_polynomial (tm : FinTM2) (stack time : Polynomial ℕ) :
    ∃ p : Polynomial ℕ, ∀ n (input : List (tm.Γ tm.k₀)) (final : tm.Cfg)
      (hf : StacksIn (machineSymbols tm) final.stk),
      (cnfEncoding.encode (runCNF tm (stack.eval n) (time.eval n) input final hf)).length ≤ p.eval n := by
  refine ⟨runBoundPolynomial tm stack time, ?_⟩
  intro n input final hf
  rw [runBoundPolynomial_eval]
  exact runCNF_encoded_bound tm _ _ input final hf

end ProteinFolding.SAT.CookLevinEncodingSize
