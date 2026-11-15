import ProteinFolding.Common.CookLevinProofCertificateCNF

/-! Concrete global CNF with a variable bounded certificate boundary. Its
models are exactly accepting runs from the fixed header and some certificate
word, rather than runs from a completely pinned chosen certificate.
-/

namespace ProteinFolding.SAT.CookLevinBoundedRunCNF

open Turing TM2 CookLevinAlphabet CookLevinRows CookLevinLinks CookLevinRuns
open CookLevinStepCNF CookLevinGlobalCNF CookLevinCircuit CookLevinPadded
open CookLevinCertificateCNF

noncomputable def boundedRunCNF {C : Type*} (tm : FinTM2) (M T : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk) : CNF :=
  certificateCNF tm M e header B hM ++ globalCNF tm M T ++ pins (boundaryBindings tm M T final hf)

/-- Global correctness with an arbitrary bounded finite-alphabet certificate. -/
theorem boundedRunCNF_satisfiable_iff {C : Type*} (tm : FinTM2) (M T : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk)
    (hstack : header.length + B + T * TM2Bounds.machinePushBound tm ≤ M)
    (hfM : ∀ k, (final.stk k).length ≤ M) :
    Satisfiable (boundedRunCNF tm M T e header B hM final hf) ↔
      ∃ cs : List C, cs.length ≤ B ∧
        (paddedStep tm)^[T] (initList tm ((header ++ cs.map e).map Subtype.val)) = final := by
  constructor
  · rintro ⟨a, ha⟩
    change Satisfied a (_ ++ _ ++ _) at ha
    rw [satisfied_append, satisfied_append] at ha
    obtain ⟨rows, hr, hl⟩ := (globalCNF_iff tm M T a).mp ha.1.2
    obtain ⟨cs, hcs, h0⟩ := (certificateCNF_words_iff tm M e header B hM a _ (hr 0 (by omega))).mp ha.1.1
    have hfrow := (boundaryPins_iff tm M T final hf a _ (hr T le_rfl)).mp ha.2
    have hlen : ((header ++ cs.map e).map Subtype.val).length + T * TM2Bounds.machinePushBound tm ≤ M := by
      simp only [List.length_map, List.length_append]
      omega
    exact ⟨cs, hcs, (linked_trace_iff tm _ M T final hf hlen hfM).mp ⟨rows, h0, hl, hfrow⟩⟩
  · rintro ⟨cs, hcs, hrun⟩
    have hlen : ((header ++ cs.map e).map Subtype.val).length + T * TM2Bounds.machinePushBound tm ≤ M := by
      simp only [List.length_map, List.length_append]
      omega
    obtain ⟨rows, h0, hl, hfrow⟩ := (linked_trace_iff tm _ M T final hf hlen hfM).mpr hrun
    let a := rowAssignment tm M rows
    refine ⟨a, ?_⟩
    change Satisfied a (_ ++ _ ++ _)
    rw [satisfied_append, satisfied_append]
    exact ⟨⟨(certificateCNF_words_iff tm M e header B hM a _ (rowAssignment_reads tm M rows 0)).mpr
      ⟨cs, hcs, h0⟩, (globalCNF_iff tm M T a).mpr
        ⟨rows, fun t _ => rowAssignment_reads tm M rows t, hl⟩⟩,
      (boundaryPins_iff tm M T final hf a _ (rowAssignment_reads tm M rows T)).mpr hfrow⟩

end ProteinFolding.SAT.CookLevinBoundedRunCNF
