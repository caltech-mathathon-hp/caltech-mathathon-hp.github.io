import ProteinFolding.Common.CookLevinProofGlobalCNF

/-! Machine-fixed arities and exact constraint counts for the concrete global
TM2 tableau. The finite domains may be large constants, but none depends on
the input length, stack bound, or computation horizon.
-/

namespace ProteinFolding.SAT.CookLevinSize

open Turing TM2 CookLevinAlphabet CookLevinWindow CookLevinWindowCNF CookLevinCells
open CookLevinPaddedWindow CookLevinRows CookLevinStepCNF CookLevinGlobalCNF
open CookLevinLocal CookLevinCircuit

noncomputable def cellDomainBound (tm : FinTM2) : ℕ :=
  letI := tm.kFin
  Finset.univ.sup (fun k => Fintype.card (Option (Symbol tm k)) + Fintype.card (CellWindow tm k))

noncomputable def domainBound (tm : FinTM2) : ℕ :=
  Fintype.card (Control tm) + Fintype.card (PaddedWindow tm) + Fintype.card (Replacement tm) + cellDomainBound tm

theorem domain_bounds (tm : FinTM2) :
    Fintype.card (Control tm) ≤ domainBound tm ∧
    Fintype.card (PaddedWindow tm) ≤ domainBound tm ∧
    Fintype.card (Replacement tm) ≤ domainBound tm ∧
    ∀ k, Fintype.card (Option (Symbol tm k)) ≤ domainBound tm ∧
      Fintype.card (CellWindow tm k) ≤ domainBound tm := by
  have hk : ∀ k, Fintype.card (Option (Symbol tm k)) + Fintype.card (CellWindow tm k) ≤ cellDomainBound tm := by
    intro k
    letI := tm.kFin
    exact Finset.le_sup (f := fun k => Fintype.card (Option (Symbol tm k)) +
      Fintype.card (CellWindow tm k)) (Finset.mem_univ k)
  unfold domainBound
  exact ⟨by omega, by omega, by omega, fun k => ⟨by have h := hk k; omega, by have h := hk k; omega⟩⟩

theorem codeRefs_length {A : Type*} [Fintype A] (tm : FinTM2) (M t : ℕ) (tag : A → Bit tm M) :
    (codeRefs tm M t tag).length = Fintype.card A := by simp [codeRefs, codeSlots_length]

theorem componentConstraint_length {A : Type*} [Fintype A] (tm : FinTM2) (M : ℕ) (tag : A → Bit tm M) :
    (componentConstraint tm M tag).vars.length = Fintype.card A := by simp [componentConstraint, codeSlots_length]

theorem functionFactor_length {A B : Type*} [Fintype A] [Fintype B]
    (tm : FinTM2) (M t u : ℕ) (tagA : A → Bit tm M) (tagB : B → Bit tm M) (f : A → B) :
    (functionFactor tm M t u tagA tagB f).vars.length = Fintype.card A + Fintype.card B := by
  simp [functionFactor, codeRefs_length]

theorem toCellFactor_length {A : Type*} [Fintype A]
    (tm : FinTM2) (M t : ℕ) (tag : A → Bit tm M)
    (k : tm.K) (n : ℕ) (f : A → Option (Symbol tm k)) :
    (toCellFactor tm M t tag k n f).vars.length ≤ Fintype.card A + Fintype.card (Option (Symbol tm k)) := by
  unfold toCellFactor
  split
  · exact (functionFactor_length tm M t t tag _ f).le
  · simp only [codeRefs_length]; omega

theorem validityConstraints_arity (tm : FinTM2) (M : ℕ) :
    ∀ c ∈ validityConstraints tm M, c.vars.length ≤ domainBound tm := by
  letI := tm.kFin
  obtain ⟨hc, hw, hr, hk⟩ := domain_bounds tm
  intro c h
  unfold validityConstraints at h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · simpa only [componentConstraint_length] using hc
    · simpa only [componentConstraint_length] using hw
    · simpa only [componentConstraint_length] using hr
  · obtain ⟨k, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨n, _, h⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · simpa only [componentConstraint_length] using (hk k).1
    · simpa only [componentConstraint_length] using (hk k).2

theorem stepConstraints_arity (tm : FinTM2) (M t : ℕ) :
    ∀ c ∈ stepConstraints tm M t, c.vars.length ≤ 3 * domainBound tm := by
  letI := tm.kFin
  obtain ⟨hc, hw, hr, hk⟩ := domain_bounds tm
  intro c h
  unfold stepConstraints at h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · simp only [controlLink, functionFactor_length]; omega
    · simp only [executionLink, List.length_append, codeRefs_length]; omega
    · simp only [nextControlLink, functionFactor_length]; omega
  · obtain ⟨k, _, h⟩ := List.mem_flatMap.mp h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
      have hp := toCellFactor_length tm M t (windowTag tm M) k i.val (fun w => ((w.2 k).val)[i.val]?)
      have hb := (hk k).1
      exact hp.trans (by omega)
    · obtain ⟨n, _, h⟩ := List.mem_flatMap.mp h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
        have hp := toCellFactor_length tm M t (queryTag tm M k n) k (cellBase tm n.val + i.val) (fun q => q i)
        have hb := hk k
        exact hp.trans (by omega)
      · have he := List.mem_singleton.mp h
        subst c
        have hb := hk k
        simp only [selectedCellLink, List.length_append, codeRefs_length]
        omega

theorem rowConstraints_arity (tm : FinTM2) (M t : ℕ) :
    ∀ c ∈ rowConstraints tm M t, c.vars.length ≤ domainBound tm := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa only [shiftConstraint, List.length_map] using validityConstraints_arity tm M d hd

theorem globalConstraints_arity (tm : FinTM2) (M T : ℕ) :
    ∀ c ∈ globalConstraints tm M T, c.vars.length ≤ 3 * domainBound tm := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨t, _, hc⟩ := List.mem_flatMap.mp hc
    exact (rowConstraints_arity tm M t c hc).trans (by omega)
  · obtain ⟨t, _, hc⟩ := List.mem_flatMap.mp hc
    exact stepConstraints_arity tm M t c hc

theorem flatMap_uniform_length {A B : Type*} (xs : List A) (f : A → List B) (N : ℕ)
    (h : ∀ x ∈ xs, (f x).length = N) : (xs.flatMap f).length = xs.length * N := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]
    omega

noncomputable def validityCount (tm : FinTM2) (M : ℕ) : ℕ :=
  letI := tm.kFin
  3 + Fintype.card tm.K * (M * 2)

theorem validityConstraints_length (tm : FinTM2) (M : ℕ) :
    (validityConstraints tm M).length = validityCount tm M := by
  letI := tm.kFin
  have hi : ∀ k : tm.K,
      ((List.finRange M).flatMap (fun n => [componentConstraint tm M (cellTag tm M k n),
        componentConstraint tm M (queryTag tm M k n)])).length = M * 2 := by
    intro k
    rw [flatMap_uniform_length _ _ 2 (by intros; rfl), List.length_finRange]
  unfold validityConstraints validityCount
  rw [List.length_append, flatMap_uniform_length _ _ (M * 2) (fun k _ => hi k)]
  simp

noncomputable def stepCount (tm : FinTM2) (M : ℕ) : ℕ :=
  letI := tm.kFin
  3 + Fintype.card tm.K * (machineReadBound tm + M * (cellWindowWidth tm + 1))

theorem stepConstraints_length (tm : FinTM2) (M t : ℕ) :
    (stepConstraints tm M t).length = stepCount tm M := by
  letI := tm.kFin
  have hi : ∀ k : tm.K, ∀ n : Fin M,
      ((List.finRange (cellWindowWidth tm)).map (queryLink tm M t k n) ++ [selectedCellLink tm M t k n]).length =
        cellWindowWidth tm + 1 := by intros; simp
  have hk : ∀ k : tm.K,
      ((List.finRange (machineReadBound tm)).map (prefixLink tm M t k) ++
        (List.finRange M).flatMap (fun n => (List.finRange (cellWindowWidth tm)).map (queryLink tm M t k n) ++
          [selectedCellLink tm M t k n])).length = machineReadBound tm + M * (cellWindowWidth tm + 1) := by
    intro k
    rw [List.length_append, List.length_map, List.length_finRange,
      flatMap_uniform_length _ _ _ (fun n _ => hi k n), List.length_finRange]
  unfold stepConstraints stepCount
  rw [List.length_append, flatMap_uniform_length _ _ _ (fun k _ => hk k)]
  simp

noncomputable def constraintCount (tm : FinTM2) (M T : ℕ) : ℕ :=
  (T + 1) * validityCount tm M + T * stepCount tm M

theorem globalConstraints_length (tm : FinTM2) (M T : ℕ) :
    (globalConstraints tm M T).length = constraintCount tm M T := by
  unfold globalConstraints constraintCount
  rw [List.length_append, flatMap_uniform_length _ _ (validityCount tm M)
    (fun t _ => by simp only [rowConstraints, List.length_map, validityConstraints_length]),
    flatMap_uniform_length _ _ (stepCount tm M) (fun t _ => stepConstraints_length tm M t)]
  simp only [List.length_range]

theorem globalCNF_clause_bound (tm : FinTM2) (M T : ℕ) :
    (globalCNF tm M T).length ≤ constraintCount tm M T * 2 ^ (3 * domainBound tm) := by
  simpa only [globalCNF, globalConstraints_length] using
    compileConstraints_clause_bound (globalConstraints tm M T) _ (globalConstraints_arity tm M T)

theorem globalCNF_literal_bound (tm : FinTM2) (M T : ℕ) :
    (globalCNF tm M T).flatten.length ≤
      (constraintCount tm M T * 2 ^ (3 * domainBound tm)) * (3 * domainBound tm) := by
  simpa only [globalCNF, globalConstraints_length] using
    compileConstraints_literal_bound (globalConstraints tm M T) _ (globalConstraints_arity tm M T)

end ProteinFolding.SAT.CookLevinSize
