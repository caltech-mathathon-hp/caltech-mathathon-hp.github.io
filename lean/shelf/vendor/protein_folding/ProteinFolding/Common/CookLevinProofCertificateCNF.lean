import ProteinFolding.Common.CookLevinProofCertificatePoints

/-! Concrete bounded-certificate boundary CNF. Its variable alphabet checks
and empty-cell propagation use one or two cell codes per factor. Header,
control, unused stacks and the suffix are pinned explicitly.
-/

namespace ProteinFolding.SAT.CookLevinCertificateCNF

open Turing TM2 CookLevinAlphabet CookLevinRows CookLevinLinks CookLevinStepCNF
open CookLevinWindowCNF CookLevinLocal CookLevinCircuit CookLevinGlobalCNF
open CookLevinCertificateCells CookLevinCertificateBoundary CookLevinCertificatePoints

noncomputable def unaryAllowed {D : Type*} [Fintype D] (P : D → Prop) (bs : List Bool) : Bool := by
  classical
  exact decide (∃ v : D, bs = finiteCode v ∧ P v)

theorem unaryAllowed_code_iff {D : Type*} [Fintype D] (P : D → Prop) (v : D) :
    unaryAllowed P (finiteCode v) = true ↔ P v := by
  classical
  unfold unaryAllowed
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨u, he, hp⟩
    exact (finiteCode_injective he) ▸ hp
  · intro hp
    exact ⟨v, rfl, hp⟩

noncomputable def binaryAllowed {D : Type*} [Fintype D] (P : D → D → Prop) (bs : List Bool) : Bool := by
  classical
  exact decide (∃ u v : D, bs = finiteCode u ++ finiteCode v ∧ P u v)

theorem binaryAllowed_code_iff {D : Type*} [Fintype D] (P : D → D → Prop) (u v : D) :
    binaryAllowed P (finiteCode u ++ finiteCode v) = true ↔ P u v := by
  classical
  unfold binaryAllowed
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨u', v', he, hp⟩
    have hparts := List.append_inj he (by simp only [finiteCode_length])
    have hu := finiteCode_injective hparts.1
    have hv := finiteCode_injective hparts.2
    exact hu.symm ▸ hv.symm ▸ hp
  · intro hp
    exact ⟨u, v, rfl, hp⟩

noncomputable def alphabetFactor {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (H B : ℕ) (hM : H + B ≤ M) (i : Fin B) : Constraint :=
  ⟨codeRefs tm M 0 (cellTag tm M tm.k₀ (certificateIndex H hM i)),
    unaryAllowed (fun v => v = none ∨ ∃ c, v = some (e c))⟩

noncomputable def noHoleFactor (tm : FinTM2) (M H B : ℕ) (hM : H + B ≤ M) (i j : Fin B) : Constraint :=
  ⟨codeRefs tm M 0 (cellTag tm M tm.k₀ (certificateIndex H hM i)) ++
    codeRefs tm M 0 (cellTag tm M tm.k₀ (certificateIndex H hM j)),
    binaryAllowed (fun u v : Option (Symbol tm tm.k₀) => u = none → v = none)⟩

theorem alphabetFactor_iff {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (H B : ℕ) (hM : H + B ≤ M) (i : Fin B) (a : ℕ → Bool) (r : Row tm M) (hr : Reads tm M 0 a r) :
    (alphabetFactor tm M e H B hM i).Holds a ↔
      r.cells tm.k₀ (certificateIndex H hM i) = none ∨
        ∃ c, r.cells tm.k₀ (certificateIndex H hM i) = some (e c) := by
  simp only [alphabetFactor, Constraint.Holds, cellCode tm M 0 a r hr, unaryAllowed_code_iff]

theorem noHoleFactor_iff (tm : FinTM2) (M H B : ℕ) (hM : H + B ≤ M) (i j : Fin B)
    (a : ℕ → Bool) (r : Row tm M) (hr : Reads tm M 0 a r) :
    (noHoleFactor tm M H B hM i j).Holds a ↔
      (r.cells tm.k₀ (certificateIndex H hM i) = none →
        r.cells tm.k₀ (certificateIndex H hM j) = none) := by
  simp only [noHoleFactor, Constraint.Holds, List.map_append,
    cellCode tm M 0 a r hr, binaryAllowed_code_iff]

noncomputable def certificateFactors {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (H B : ℕ) (hM : H + B ≤ M) : List Constraint :=
  (List.finRange B).map (alphabetFactor tm M e H B hM) ++
    (List.finRange B).flatMap (fun i => ((List.finRange B).filter (fun j => i < j)).map (noHoleFactor tm M H B hM i))

theorem certificateFactors_iff {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (H B : ℕ) (hM : H + B ≤ M) (a : ℕ → Bool) (r : Row tm M) (hr : Reads tm M 0 a r) :
    Satisfied a (compileConstraints (certificateFactors tm M e H B hM)) ↔
      (∀ i : Fin B, r.cells tm.k₀ (certificateIndex H hM i) = none ∨
        ∃ c, r.cells tm.k₀ (certificateIndex H hM i) = some (e c)) ∧
      (∀ i j : Fin B, i < j → r.cells tm.k₀ (certificateIndex H hM i) = none →
        r.cells tm.k₀ (certificateIndex H hM j) = none) := by
  rw [compileConstraints_iff]
  unfold certificateFactors
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_flatMap,
    List.mem_finRange, forall_const, List.mem_filter, true_and, decide_eq_true_eq,
    alphabetFactor_iff tm M e H B hM _ a r hr, noHoleFactor_iff tm M H B hM _ _ a r hr]

noncomputable def certificateBindings {C : Type*} (tm : FinTM2) (M : ℕ) (_e : C → Symbol tm tm.k₀)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) (hM : header.length + B ≤ M) : List (ℕ × Bool) := by
  classical
  letI := tm.kFin
  exact componentPins tm M 0 (controlTag tm M) (some tm.main, tm.initialState) ++
    (List.finRange header.length).flatMap (fun i => componentPins tm M 0
      (cellTag tm M tm.k₀ (headerIndex header.length hM i)) (some header[i.val])) ++
    ((List.finRange M).filter (fun i => header.length + B ≤ i.val)).flatMap (fun i =>
      componentPins tm M 0 (cellTag tm M tm.k₀ i) none) ++
    (Finset.univ.toList.filter (fun k => k ≠ tm.k₀)).flatMap (fun k =>
      (List.finRange M).flatMap (fun n => componentPins tm M 0 (cellTag tm M k n) none))

theorem certificatePins_iff {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) (hM : header.length + B ≤ M)
    (a : ℕ → Bool) (r : Row tm M) (hr : Reads tm M 0 a r) :
    Satisfied a (pins (certificateBindings tm M e header B hM)) ↔
      r.control = (some tm.main, tm.initialState) ∧
      (∀ i : Fin header.length, r.cells tm.k₀ (headerIndex header.length hM i) = some header[i.val]) ∧
      (∀ i : Fin M, header.length + B ≤ i.val → r.cells tm.k₀ i = none) ∧
      ∀ k, k ≠ tm.k₀ → ∀ n, r.cells k n = none := by
  classical
  letI := tm.kFin
  rw [pins_iff]
  unfold certificateBindings
  simp only [matches_append_iff, matches_flatMap_iff, List.mem_filter, List.mem_finRange,
    Finset.mem_toList, Finset.mem_univ, true_and, decide_eq_true_eq, forall_const,
    componentPins_matches_iff tm M 0 _ _ _ a (controlCode tm M 0 a r hr),
    componentPins_matches_iff tm M 0 _ _ _ a (cellCode tm M 0 a r hr _ _), and_assoc]

noncomputable def certificateCNF {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) (hM : header.length + B ≤ M) : CNF :=
  pins (certificateBindings tm M e header B hM) ++
    compileConstraints (certificateFactors tm M e header.length B hM)

theorem certificateCNF_iff {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) (hM : header.length + B ≤ M)
    (a : ℕ → Bool) (r : Row tm M) (hr : Reads tm M 0 a r) :
    Satisfied a (certificateCNF tm M e header B hM) ↔ PointBoundary tm M e header B hM r := by
  rw [certificateCNF, satisfied_append, certificatePins_iff tm M e header B hM a r hr,
    certificateFactors_iff tm M e header.length B hM a r hr]
  constructor
  · rintro ⟨⟨hc, hh, hs, ho⟩, ha, hn⟩
    exact ⟨hc, hh, ha, hn, hs, ho⟩
  · rintro ⟨hc, hh, ha, hn, hs, ho⟩
    exact ⟨⟨hc, hh, hs, ho⟩, ha, hn⟩

theorem certificateCNF_words_iff {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) (hM : header.length + B ≤ M)
    (a : ℕ → Bool) (r : Row tm M) (hr : Reads tm M 0 a r) :
    Satisfied a (certificateCNF tm M e header B hM) ↔ ∃ cs : List C, cs.length ≤ B ∧
      Represents r (initList tm ((header ++ cs.map e).map Subtype.val)) (initList_stacksIn tm _) := by
  rw [certificateCNF_iff tm M e header B hM a r hr, pointBoundary_words_iff]

end ProteinFolding.SAT.CookLevinCertificateCNF
