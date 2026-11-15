import ProteinFolding.Common.CookLevinProofStepCNF

/-! A concrete global CNF for finite padded TM2 runs, with initial and final
configuration pins. Satisfiability is proved equivalent to the actual fixed-
horizon machine run. The emitting-machine runtime and variable certificate
boundary construction are separate obligations.
-/

namespace ProteinFolding.SAT.CookLevinGlobalCNF

open Turing TM2 CookLevinAlphabet CookLevinWindowCNF CookLevinPadded CookLevinRows
open CookLevinLinks CookLevinRuns CookLevinStepCNF CookLevinLocal CookLevinCircuit

def shiftConstraint (offset : ℕ) (c : Constraint) : Constraint :=
  ⟨c.vars.map (offset + ·), c.allowed⟩

theorem shiftConstraint_iff (offset : ℕ) (c : Constraint) (a : ℕ → Bool) :
    (shiftConstraint offset c).Holds a ↔ c.Holds (fun i => a (offset + i)) := by
  simp only [shiftConstraint, Constraint.Holds, List.map_map, Function.comp_def]

noncomputable def rowConstraints (tm : FinTM2) (M t : ℕ) : List Constraint :=
  (validityConstraints tm M).map (shiftConstraint (t * width tm M))

theorem rowConstraints_iff (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) :
    Satisfied a (compileConstraints (rowConstraints tm M t)) ↔ ∃ r : Row tm M, Reads tm M t a r := by
  rw [compileConstraints_iff]
  unfold rowConstraints
  simp only [List.forall_mem_map, shiftConstraint_iff]
  rw [← compileConstraints_iff, validityConstraints_iff]
  simp only [Reads, reference, funext_iff]

noncomputable def globalConstraints (tm : FinTM2) (M T : ℕ) : List Constraint :=
  (List.range (T + 1)).flatMap (rowConstraints tm M) ++
    (List.range T).flatMap (stepConstraints tm M)

noncomputable def globalCNF (tm : FinTM2) (M T : ℕ) : CNF :=
  compileConstraints (globalConstraints tm M T)

theorem globalCNF_components_iff (tm : FinTM2) (M T : ℕ) (a : ℕ → Bool) :
    Satisfied a (globalCNF tm M T) ↔
      (∀ t ≤ T, ∃ r : Row tm M, Reads tm M t a r) ∧
      (∀ t < T, Satisfied a (compileConstraints (stepConstraints tm M t))) := by
  unfold globalCNF globalConstraints
  rw [compileConstraints_iff]
  simp only [List.forall_mem_append, List.forall_mem_flatMap, List.mem_range]
  simp only [← compileConstraints_iff, rowConstraints_iff, Nat.lt_add_one_iff]

theorem globalCNF_iff (tm : FinTM2) (M T : ℕ) (a : ℕ → Bool) :
    Satisfied a (globalCNF tm M T) ↔ ∃ rows : ℕ → Row tm M,
      (∀ t ≤ T, Reads tm M t a (rows t)) ∧ (∀ t < T, Links (rows t) (rows (t + 1))) := by
  classical
  rw [globalCNF_components_iff]
  constructor
  · rintro ⟨hv, hs⟩
    have hall : ∀ t, ∃ r : Row tm M, t ≤ T → Reads tm M t a r := by
      intro t
      by_cases ht : t ≤ T
      · obtain ⟨r, hr⟩ := hv t ht
        exact ⟨r, fun _ => hr⟩
      · exact ⟨canonicalRow tm M (initList tm []) (initList_stacksIn tm []), fun h => (ht h).elim⟩
    choose rows hrows using hall
    refine ⟨rows, hrows, ?_⟩
    intro t ht
    exact (stepConstraints_iff tm M t a _ _ (hrows t (by omega))
      (hrows (t + 1) (by omega))).mp (hs t ht)
  · rintro ⟨rows, hr, hl⟩
    exact ⟨fun t ht => ⟨rows t, hr t ht⟩, fun t ht =>
      (stepConstraints_iff tm M t a _ _ (hr t (by omega)) (hr (t + 1) (by omega))).mpr (hl t ht)⟩

noncomputable def rowAssignment (tm : FinTM2) (M : ℕ) (rows : ℕ → Row tm M) (i : ℕ) : Bool :=
  encodeRow (rows (i / width tm M))
    ((bitIndex tm M).symm ⟨i % width tm M, Nat.mod_lt _ (width_pos tm M)⟩)

theorem rowAssignment_reads (tm : FinTM2) (M : ℕ) (rows : ℕ → Row tm M) (t : ℕ) :
    Reads tm M t (rowAssignment tm M rows) (rows t) := by
  intro b
  have hd : (t * width tm M + (bitIndex tm M b).val) / width tm M = t := by
    rw [Nat.add_comm (t * width tm M), Nat.add_mul_div_right _ _ (width_pos tm M),
      Nat.div_eq_of_lt (bitIndex tm M b).isLt, Nat.zero_add]
  have hm : (t * width tm M + (bitIndex tm M b).val) % width tm M = (bitIndex tm M b).val := by
    simp [Nat.mod_eq_of_lt (bitIndex tm M b).isLt]
  unfold rowAssignment reference
  rw [hd]
  have hfin : (⟨(t * width tm M + (bitIndex tm M b).val) % width tm M,
      Nat.mod_lt _ (width_pos tm M)⟩ : Fin (width tm M)) =
      bitIndex tm M b := Fin.ext hm
  rw [hfin, Equiv.symm_apply_apply]

theorem matches_zip_iff (a : ℕ → Bool) (vars : List ℕ) (bs : List Bool)
    (h : vars.length = bs.length) : Matches a (vars.zip bs) ↔ vars.map a = bs := by
  induction vars generalizing bs with
  | nil =>
    have hb : bs = [] := List.length_eq_zero_iff.mp h.symm
    subst bs
    simp [Matches]
  | cons v vars ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.zip_cons_cons, Matches, List.forall_mem_cons, List.map_cons, List.cons.injEq]
      exact and_congr Iff.rfl (ih bs (by simpa using h))

noncomputable def componentPins {A : Type*} [Fintype A] (tm : FinTM2) (M t : ℕ)
    (tag : A → Bit tm M) (v : A) : List (ℕ × Bool) := (codeRefs tm M t tag).zip (finiteCode v)

theorem componentPins_matches_iff {A : Type*} [Fintype A] (tm : FinTM2) (M t : ℕ)
    (tag : A → Bit tm M) (x y : A) (a : ℕ → Bool)
    (h : (codeRefs tm M t tag).map a = finiteCode x) :
    Matches a (componentPins tm M t tag y) ↔ x = y := by
  unfold componentPins
  rw [matches_zip_iff a _ _ (by simp [codeRefs, codeSlots_length, finiteCode_length]), h]
  exact finiteCode_injective.eq_iff

theorem matches_append_iff (a : ℕ → Bool) (xs ys : List (ℕ × Bool)) :
    Matches a (xs ++ ys) ↔ Matches a xs ∧ Matches a ys := by
  simp only [Matches, List.forall_mem_append]

theorem matches_flatMap_iff {A : Type*} (a : ℕ → Bool) (xs : List A) (f : A → List (ℕ × Bool)) :
    Matches a (xs.flatMap f) ↔ ∀ x ∈ xs, Matches a (f x) := by
  simp only [Matches, List.forall_mem_flatMap]

noncomputable def boundaryBindings (tm : FinTM2) (M t : ℕ) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) : List (ℕ × Bool) := by
  letI := tm.kFin
  exact componentPins tm M t (controlTag tm M) (c.l, c.var) ++
    Finset.univ.toList.flatMap (fun k => (List.finRange M).flatMap (fun n =>
      componentPins tm M t (cellTag tm M k n) ((encodedStack tm c h k)[n.val]?)))

theorem boundaryPins_iff (tm : FinTM2) (M t : ℕ) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (a : ℕ → Bool) (r : Row tm M)
    (hr : Reads tm M t a r) :
    Satisfied a (pins (boundaryBindings tm M t c h)) ↔ Represents r c h := by
  letI := tm.kFin
  rw [pins_iff]
  unfold boundaryBindings Represents
  rw [matches_append_iff]
  simp only [matches_flatMap_iff, Finset.mem_toList, Finset.mem_univ, List.mem_finRange, forall_const,
    componentPins_matches_iff tm M t _ _ _ a (controlCode tm M t a r hr)]
  simp only [componentPins_matches_iff tm M t _ _ _ a (cellCode tm M t a r hr _ _)]

noncomputable def runCNF (tm : FinTM2) (M T : ℕ) (input : List (tm.Γ tm.k₀))
    (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk) : CNF :=
  pins (boundaryBindings tm M 0 (initList tm input) (initList_stacksIn tm input)) ++
    globalCNF tm M T ++ pins (boundaryBindings tm M T final hf)

/-- Concrete global CNF correctness for the actual mathlib machine, with full
initial and final configuration pins and a proved sufficient stack bound. -/
theorem runCNF_satisfiable_iff (tm : FinTM2) (M T : ℕ) (input : List (tm.Γ tm.k₀))
    (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk)
    (hM : input.length + T * TM2Bounds.machinePushBound tm ≤ M)
    (hfM : ∀ k, (final.stk k).length ≤ M) :
    Satisfiable (runCNF tm M T input final hf) ↔
      (paddedStep tm)^[T] (initList tm input) = final := by
  rw [← linked_trace_iff tm input M T final hf hM hfM]
  constructor
  · rintro ⟨a, ha⟩
    change Satisfied a (_ ++ _ ++ _) at ha
    rw [satisfied_append, satisfied_append] at ha
    obtain ⟨rows, hr, hl⟩ := (globalCNF_iff tm M T a).mp ha.1.2
    exact ⟨rows, (boundaryPins_iff tm M 0 _ _ a _ (hr 0 (by omega))).mp ha.1.1,
      hl, (boundaryPins_iff tm M T final hf a _ (hr T le_rfl)).mp ha.2⟩
  · rintro ⟨rows, h0, hl, hfrow⟩
    let a := rowAssignment tm M rows
    refine ⟨a, ?_⟩
    change Satisfied a (_ ++ _ ++ _)
    rw [satisfied_append, satisfied_append]
    exact ⟨⟨(boundaryPins_iff tm M 0 _ _ a _ (rowAssignment_reads tm M rows 0)).mpr h0,
      (globalCNF_iff tm M T a).mpr ⟨rows, fun t _ => rowAssignment_reads tm M rows t, hl⟩⟩,
      (boundaryPins_iff tm M T final hf a _ (rowAssignment_reads tm M rows T)).mpr hfrow⟩

end ProteinFolding.SAT.CookLevinGlobalCNF
