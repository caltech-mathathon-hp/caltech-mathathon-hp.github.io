import ProteinFolding.Common.CookLevinProofCertificateCNF
import ProteinFolding.Common.CookLevinProofBoundedRunCNF
import ProteinFolding.Common.CookLevinProofEncodingSize

/-! Complete size bounds for the concrete variable-certificate boundary.
The quadratic no-hole check count and every original binary variable index
are included. All exponential factors depend only on the fixed machine. -/

namespace ProteinFolding.SAT.CookLevinCertificateSize

open Turing TM2 CookLevinAlphabet CookLevinRows CookLevinStepCNF CookLevinGlobalCNF
open CookLevinWindowCNF CookLevinLocal CookLevinCircuit CookLevinSize CookLevinEncodingSize
open CookLevinCertificateCNF
open CookLevinPaddedWindow
open CookLevinBoundedRunCNF

theorem certificateFactors_length {C : Type*} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (H B : ℕ) (hM : H + B ≤ M) :
    (certificateFactors tm M e H B hM).length ≤ B + B * B := by
  have h := flatMap_length_le (List.finRange B)
    (fun i => ((List.finRange B).filter (fun j => i < j)).map (noHoleFactor tm M H B hM i))
    B (fun i _ => by simpa only [List.length_map, List.length_finRange] using
      List.length_filter_le (fun j : Fin B => decide (i < j)) (List.finRange B))
  simp only [certificateFactors, List.length_append, List.length_map, List.length_finRange]
  simpa only [List.length_finRange] using Nat.add_le_add_left h B

theorem certificateFactors_arity {C : Type*} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (H B : ℕ) (hM : H + B ≤ M) :
    ∀ c ∈ certificateFactors tm M e H B hM, c.vars.length ≤ 2 * domainBound tm := by
  intro c hc
  have hd := (domain_bounds tm).2.2.2 tm.k₀ |>.1
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    simpa only [alphabetFactor, codeRefs_length] using hd.trans (by omega)
  · obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
    simp only [noHoleFactor, List.length_append, codeRefs_length]
    omega

theorem certificateFactors_vars_lt {C : Type*} (tm : FinTM2) (M T : ℕ)
    (e : C → Symbol tm tm.k₀) (H B : ℕ) (hM : H + B ≤ M) :
    ∀ c ∈ certificateFactors tm M e H B hM, ∀ i ∈ c.vars,
      i < (T + 1) * width tm M := by
  intro c hc i hi
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
    exact codeRefs_vars_lt tm M 0 T (Nat.zero_le T) _ i hi
  · obtain ⟨j, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
    rcases List.mem_append.mp hi with hi | hi <;>
      exact codeRefs_vars_lt tm M 0 T (Nat.zero_le T) _ i hi

noncomputable def certificatePinBound (tm : FinTM2) (M : ℕ) : ℕ :=
  letI := tm.kFin
  Fintype.card (Control tm) + (2 + Fintype.card tm.K) * (M * domainBound tm)

theorem certificateBindings_length {C : Type*} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) :
    (certificateBindings tm M e header B hM).length ≤ certificatePinBound tm M := by
  classical
  letI := tm.kFin
  have hd := (domain_bounds tm).2.2.2 tm.k₀ |>.1
  have hh := flatMap_length_le (List.finRange header.length)
    (fun i => componentPins tm M 0 (cellTag tm M tm.k₀ (CookLevinCertificatePoints.headerIndex header.length hM i))
      (some header[i.val])) (domainBound tm) (fun _ _ => by simpa only [componentPins_length] using hd)
  simp only [List.length_finRange] at hh
  have hs := flatMap_length_le
    ((List.finRange M).filter (fun i => decide (header.length + B ≤ i.val)))
    (fun i => componentPins tm M 0 (cellTag tm M tm.k₀ i) none) (domainBound tm)
    (fun _ _ => by simpa only [componentPins_length] using hd)
  have hfilter := List.length_filter_le (fun i : Fin M => decide (header.length + B ≤ i.val)) (List.finRange M)
  simp only [List.length_finRange] at hfilter
  have hsb : (((List.finRange M).filter (fun i => decide (header.length + B ≤ i.val))).flatMap
      (fun i => componentPins tm M 0 (cellTag tm M tm.k₀ i) none)).length ≤ M * domainBound tm :=
    hs.trans (Nat.mul_le_mul_right _ hfilter)
  have hk : ∀ k : tm.K, ((List.finRange M).flatMap
      (fun n => componentPins tm M 0 (cellTag tm M k n) none)).length ≤ M * domainBound tm := by
    intro k
    simpa only [List.length_finRange] using flatMap_length_le (List.finRange M)
      (fun n => componentPins tm M 0 (cellTag tm M k n) none) (domainBound tm)
      (fun _ _ => by simpa only [componentPins_length] using (domain_bounds tm).2.2.2 k |>.1)
  have ho := flatMap_length_le (Finset.univ.toList.filter (fun k => decide (k ≠ tm.k₀)))
    (fun k => (List.finRange M).flatMap (fun n => componentPins tm M 0 (cellTag tm M k n) none))
    (M * domainBound tm) (fun k _ => hk k)
  have hof := List.length_filter_le (fun k : tm.K => decide (k ≠ tm.k₀)) Finset.univ.toList
  simp only [Finset.length_toList, Finset.card_univ] at hof
  have hob := ho.trans (Nat.mul_le_mul_right _ hof)
  have hhb : header.length * domainBound tm ≤ M * domainBound tm :=
    Nat.mul_le_mul_right _ (by omega)
  unfold certificateBindings certificatePinBound
  simp only [List.length_append, componentPins_length]
  rw [Nat.add_mul]
  omega

theorem certificateBindings_vars_lt {C : Type*} (tm : FinTM2) (M T : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) :
    ∀ b ∈ certificateBindings tm M e header B hM, b.1 < (T + 1) * width tm M := by
  classical
  letI := tm.kFin
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact componentPins_vars_lt tm M 0 T (Nat.zero_le T) _ _ b hb
      · obtain ⟨i, _, hb⟩ := List.mem_flatMap.mp hb
        exact componentPins_vars_lt tm M 0 T (Nat.zero_le T) _ _ b hb
    · obtain ⟨i, _, hb⟩ := List.mem_flatMap.mp hb
      exact componentPins_vars_lt tm M 0 T (Nat.zero_le T) _ _ b hb
  · obtain ⟨k, _, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨n, _, hb⟩ := List.mem_flatMap.mp hb
    exact componentPins_vars_lt tm M 0 T (Nat.zero_le T) _ _ b hb

noncomputable def certificateClauseBound (tm : FinTM2) (M : ℕ) : ℕ :=
  certificatePinBound tm M + (M + M * M) * 2 ^ (2 * domainBound tm)

noncomputable def certificateLiteralBound (tm : FinTM2) (M : ℕ) : ℕ :=
  certificatePinBound tm M + ((M + M * M) * 2 ^ (2 * domainBound tm)) * (2 * domainBound tm)

theorem certificateCNF_clause_bound {C : Type*} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) :
    (certificateCNF tm M e header B hM).length ≤ certificateClauseBound tm M := by
  have hp := certificateBindings_length tm M e header B hM
  have hc := compileConstraints_clause_bound (certificateFactors tm M e header.length B hM)
    _ (certificateFactors_arity tm M e header.length B hM)
  have hn := certificateFactors_length tm M e header.length B hM
  have hb : B + B * B ≤ M + M * M := Nat.add_le_add (by omega)
    (Nat.mul_le_mul (by omega) (by omega))
  have hcb := hc.trans (Nat.mul_le_mul_right _ (hn.trans hb))
  simp only [certificateCNF, certificateClauseBound, List.length_append, pins, List.length_map]
  omega

theorem certificateCNF_literal_bound {C : Type*} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) :
    (certificateCNF tm M e header B hM).flatten.length ≤ certificateLiteralBound tm M := by
  have hp := certificateBindings_length tm M e header B hM
  have hc := compileConstraints_literal_bound (certificateFactors tm M e header.length B hM)
    _ (certificateFactors_arity tm M e header.length B hM)
  have hn := certificateFactors_length tm M e header.length B hM
  have hb : B + B * B ≤ M + M * M := Nat.add_le_add (by omega)
    (Nat.mul_le_mul (by omega) (by omega))
  have hcb := hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hn.trans hb)))
  simp only [certificateCNF, certificateLiteralBound, List.flatten_append, List.length_append,
    pins_literal_count]
  omega

theorem certificateCNF_vars_lt {C : Type*} (tm : FinTM2) (M T : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) :
    ∀ c ∈ certificateCNF tm M e header B hM, ∀ l ∈ c, l.var < (T + 1) * width tm M := by
  intro c hc l hl
  rcases List.mem_append.mp hc with hc | hc
  · exact pins_vars_lt _ _ (certificateBindings_vars_lt tm M T e header B hM) c hc l hl
  · obtain ⟨d, hd, hi⟩ := compileConstraints_vars _ c hc l hl
    exact certificateFactors_vars_lt tm M T e header.length B hM d hd l.var hi

theorem certificateCNF_width {C : Type*} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) :
    ∀ c ∈ certificateCNF tm M e header B hM, c.length ≤ 2 * domainBound tm + 1 := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
    simp
  · exact (compileConstraints_clause_width _ _ (certificateFactors_arity tm M e header.length B hM) c hc).trans (by omega)

noncomputable def boundedRunClauseBound (tm : FinTM2) (M T : ℕ) : ℕ :=
  certificateClauseBound tm M + constraintCount tm M T * 2 ^ (3 * domainBound tm) + boundaryBound tm M

noncomputable def boundedRunLiteralBound (tm : FinTM2) (M T : ℕ) : ℕ :=
  certificateLiteralBound tm M +
    (constraintCount tm M T * 2 ^ (3 * domainBound tm)) * (3 * domainBound tm) + boundaryBound tm M

noncomputable def boundedRunEncodedBound (tm : FinTM2) (M T : ℕ) : ℕ :=
  boundedRunLiteralBound tm M T * ((T + 1) * width tm M + 2) + boundedRunClauseBound tm M T

theorem boundedRunCNF_clause_bound {C : Type*} (tm : FinTM2) (M T : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk) :
    (boundedRunCNF tm M T e header B hM final hf).length ≤ boundedRunClauseBound tm M T := by
  have hc := certificateCNF_clause_bound tm M e header B hM
  have hg := globalCNF_clause_bound tm M T
  have hf' := boundaryBindings_length tm M T final hf
  simp only [boundedRunCNF, List.length_append, pins, List.length_map, boundedRunClauseBound]
  omega

theorem boundedRunCNF_literal_bound {C : Type*} (tm : FinTM2) (M T : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk) :
    (boundedRunCNF tm M T e header B hM final hf).flatten.length ≤ boundedRunLiteralBound tm M T := by
  have hc := certificateCNF_literal_bound tm M e header B hM
  have hg := globalCNF_literal_bound tm M T
  have hf' := boundaryBindings_length tm M T final hf
  simp only [boundedRunCNF, List.flatten_append, List.length_append, pins_literal_count,
    boundedRunLiteralBound]
  omega

theorem boundedRunCNF_vars_lt {C : Type*} (tm : FinTM2) (M T : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk) :
    ∀ c ∈ boundedRunCNF tm M T e header B hM final hf, ∀ l ∈ c, l.var < (T + 1) * width tm M := by
  intro c hc l hl
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · exact certificateCNF_vars_lt tm M T e header B hM c hc l hl
    · exact globalCNF_vars_lt tm M T c hc l hl
  · exact pins_vars_lt _ _ (boundaryBindings_vars_lt tm M T T le_rfl final hf) c hc l hl

theorem boundedRunCNF_width {C : Type*} (tm : FinTM2) (M T : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk) :
    ∀ c ∈ boundedRunCNF tm M T e header B hM final hf, c.length ≤ 3 * domainBound tm + 1 := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · exact (certificateCNF_width tm M e header B hM c hc).trans (by omega)
    · exact (compileConstraints_clause_width _ _ (globalConstraints_arity tm M T) c hc).trans (by omega)
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
    simp

theorem boundedRunCNF_encoded_bound {C : Type*} (tm : FinTM2) (M T : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk) :
    (cnfEncoding.encode (boundedRunCNF tm M T e header B hM final hf)).length ≤ boundedRunEncodedBound tm M T := by
  exact (cnfEncoding_length_bound _ _
    (fun c hc l hl => (boundedRunCNF_vars_lt tm M T e header B hM final hf c hc l hl).le)).trans
      (Nat.add_le_add (Nat.mul_le_mul_right _ (boundedRunCNF_literal_bound tm M T e header B hM final hf))
        (boundedRunCNF_clause_bound tm M T e header B hM final hf))

noncomputable def boundedRunBoundPolynomial (tm : FinTM2) (stack time : Polynomial ℕ) : Polynomial ℕ := by
  letI := tm.kFin
  let boundary := Polynomial.C (Fintype.card (Control tm)) +
    Polynomial.C (Fintype.card tm.K) * (stack * Polynomial.C (domainBound tm))
  let certPins := Polynomial.C (Fintype.card (Control tm)) +
    Polynomial.C (2 + Fintype.card tm.K) * (stack * Polynomial.C (domainBound tm))
  let certCount := stack + stack * stack
  let validity := Polynomial.C 3 + Polynomial.C (Fintype.card tm.K) * (stack * Polynomial.C 2)
  let transition := Polynomial.C 3 + Polynomial.C (Fintype.card tm.K) *
    (Polynomial.C (CookLevinWindow.machineReadBound tm) +
      stack * (Polynomial.C (CookLevinCells.cellWindowWidth tm) + Polynomial.C 1))
  let count := (time + Polynomial.C 1) * validity + time * transition
  let clauses := certPins + certCount * Polynomial.C (2 ^ (2 * domainBound tm)) +
    count * Polynomial.C (2 ^ (3 * domainBound tm)) + boundary
  let literals := certPins + (certCount * Polynomial.C (2 ^ (2 * domainBound tm))) *
      Polynomial.C (2 * domainBound tm) +
    (count * Polynomial.C (2 ^ (3 * domainBound tm))) * Polynomial.C (3 * domainBound tm) + boundary
  let varCount := (time + Polynomial.C 1) *
    (Polynomial.C (widthBase tm) + stack * Polynomial.C (widthSlope tm))
  exact literals * (varCount + Polynomial.C 2) + clauses

theorem boundedRunBoundPolynomial_eval (tm : FinTM2) (stack time : Polynomial ℕ) (n : ℕ) :
    (boundedRunBoundPolynomial tm stack time).eval n =
      boundedRunEncodedBound tm (stack.eval n) (time.eval n) := by
  letI := tm.kFin
  simp only [boundedRunBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    boundedRunEncodedBound, boundedRunLiteralBound, boundedRunClauseBound,
    certificateClauseBound, certificateLiteralBound, certificatePinBound,
    boundaryBound, constraintCount, validityCount, stepCount, width_linear]

theorem boundedRunCNF_encoded_polynomial {C : Type*} (tm : FinTM2) (stack time : Polynomial ℕ)
    (e : C → Symbol tm tm.k₀) :
    ∃ p : Polynomial ℕ, ∀ n (header : List (Symbol tm tm.k₀)) (B : ℕ)
      (hM : header.length + B ≤ stack.eval n) (final : tm.Cfg)
      (hf : StacksIn (machineSymbols tm) final.stk),
      (cnfEncoding.encode (boundedRunCNF tm (stack.eval n) (time.eval n) e header B hM final hf)).length ≤ p.eval n := by
  refine ⟨boundedRunBoundPolynomial tm stack time, ?_⟩
  intro n header B hM final hf
  rw [boundedRunBoundPolynomial_eval]
  exact boundedRunCNF_encoded_bound tm _ _ e header B hM final hf

end ProteinFolding.SAT.CookLevinCertificateSize
