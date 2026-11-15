import ProteinFolding.Common.CookLevinProofLinks

/-! Complete finite-horizon row semantics for an arbitrary concrete FinTM2.
Linked rows characterize its actual padded run; row validity alone is never
used as a substitute for transition correctness. Stack bounds are the proved
input-length plus runtime times the fixed push bound.
-/

namespace ProteinFolding.SAT.CookLevinRuns

open Turing TM2 CookLevinAlphabet CookLevinCells CookLevinPadded CookLevinRows CookLevinLinks

theorem represents_unique {tm : FinTM2} {M : ℕ} (r : Row tm M) (c d : tm.Cfg)
    (hc : StacksIn (machineSymbols tm) c.stk) (hd : StacksIn (machineSymbols tm) d.stk)
    (hcr : Represents r c hc) (hdr : Represents r d hd)
    (hcM : ∀ k, (c.stk k).length ≤ M) (hdM : ∀ k, (d.stk k).length ≤ M) : c = d := by
  have hctrl := hcr.1.symm.trans hdr.1
  apply config_ext tm c d (congrArg Prod.fst hctrl) (congrArg Prod.snd hctrl)
  funext k
  apply boundedList_ext M (hcM k) (hdM k)
  intro n hn
  have he := (hcr.2 k ⟨n, hn⟩).symm.trans (hdr.2 k ⟨n, hn⟩)
  have hm := congrArg (Option.map Subtype.val) he
  simpa only [encodedStack_get_map] using hm

theorem run_stack_bound (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (M T t : ℕ)
    (hM : input.length + T * TM2Bounds.machinePushBound tm ≤ M) (ht : t ≤ T) (k : tm.K) :
    (((paddedStep tm)^[t] (initList tm input)).stk k).length ≤ M := by
  exact (paddedRun_stack_length tm input t k).trans
    ((Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _).trans hM)

theorem linked_trace_represents (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (M T : ℕ)
    (rows : ℕ → Row tm M) (hM : input.length + T * TM2Bounds.machinePushBound tm ≤ M)
    (h0 : Represents (rows 0) (initList tm input) (initList_stacksIn tm input))
    (hlinks : ∀ t < T, Links (rows t) (rows (t + 1))) :
    ∀ t ≤ T, Represents (rows t) ((paddedStep tm)^[t] (initList tm input))
      (paddedRun_stacksIn tm input t) := by
  intro t
  induction t with
  | zero => intro _; exact h0
  | succ t ih =>
    intro ht
    have htT : t ≤ T := by omega
    have hr := links_sound (rows t) (rows (t + 1))
      ((paddedStep tm)^[t] (initList tm input)) (paddedRun_stacksIn tm input t)
      (ih htT) (run_stack_bound tm input M T t hM htT) (hlinks t (by omega))
    simpa only [Function.iterate_succ_apply'] using hr

/-- A complete linked-row witness exists exactly when the original concrete
machine's fixed-horizon padded run has the required final configuration. -/
theorem linked_trace_iff (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (M T : ℕ)
    (final : tm.Cfg) (hf : StacksIn (machineSymbols tm) final.stk)
    (hM : input.length + T * TM2Bounds.machinePushBound tm ≤ M)
    (hfM : ∀ k, (final.stk k).length ≤ M) :
    (∃ rows : ℕ → Row tm M,
      Represents (rows 0) (initList tm input) (initList_stacksIn tm input) ∧
      (∀ t < T, Links (rows t) (rows (t + 1))) ∧ Represents (rows T) final hf) ↔
        (paddedStep tm)^[T] (initList tm input) = final := by
  constructor
  · rintro ⟨rows, h0, hl, hfrow⟩
    exact represents_unique (rows T) _ final (paddedRun_stacksIn tm input T) hf
      (linked_trace_represents tm input M T rows hM h0 hl T le_rfl) hfrow
      (run_stack_bound tm input M T T hM le_rfl) hfM
  · intro hrun
    let rows : ℕ → Row tm M := fun t => canonicalRow tm M
      ((paddedStep tm)^[t] (initList tm input)) (paddedRun_stacksIn tm input t)
    refine ⟨rows, canonicalRow_represents tm M _ _, ?_, ?_⟩
    · intro t ht
      have hl := canonicalRows_linked tm M ((paddedStep tm)^[t] (initList tm input))
        (paddedRun_stacksIn tm input t) (run_stack_bound tm input M T t hM (by omega))
      simpa only [rows, Function.iterate_succ_apply'] using hl
    · have hr := canonicalRow_represents tm M
        ((paddedStep tm)^[T] (initList tm input)) (paddedRun_stacksIn tm input T)
      simpa only [rows, hrun] using hr

end ProteinFolding.SAT.CookLevinRuns
