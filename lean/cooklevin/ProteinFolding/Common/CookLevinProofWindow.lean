import ProteinFolding.Common.CookLevinProofAlphabet

/-! Finite transition windows for a concrete mathlib FinTM2. Executing the
window and reattaching the untouched stack suffixes gives exactly TM2.stepAux.
Both the input window and its replacement have finite types of machine-fixed
size; no bound or finiteness assumption is imposed on the complete stacks.
-/

namespace ProteinFolding.SAT.CookLevinWindow

open Turing TM2 CookLevinAlphabet CookLevinLocality

def BoundedStack (tm : FinTM2) (k : tm.K) (N : ℕ) :=
  {xs : List (Symbol tm k) // xs.length ≤ N}

noncomputable instance boundedStackFintype (tm : FinTM2) (k : tm.K) (N : ℕ) :
    Fintype (BoundedStack tm k N) := (List.finite_length_le (Symbol tm k) N).fintype

def decodeStack {tm : FinTM2} {k : tm.K} {N : ℕ} (xs : BoundedStack tm k N) :
    List (tm.Γ k) := xs.val.map Subtype.val

theorem decodeStack_length {tm : FinTM2} {k : tm.K} {N : ℕ}
    (xs : BoundedStack tm k N) : (decodeStack xs).length ≤ N := by
  simpa [decodeStack] using xs.property

theorem decodeStack_stacksIn {tm : FinTM2} {N : ℕ}
    (S : ∀ k, BoundedStack tm k N) :
    StacksIn (machineSymbols tm) (fun k => decodeStack (S k)) := by
  intro k x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact y.property

def machineReadBound (tm : FinTM2) : ℕ :=
  letI := tm.ΛFin
  Finset.univ.sup (fun l => readBound (tm.m l))

theorem readBound_le_machineReadBound (tm : FinTM2) (l : tm.Λ) :
    readBound (tm.m l) ≤ machineReadBound tm := by
  letI := tm.ΛFin
  exact Finset.le_sup (f := fun l => readBound (tm.m l)) (Finset.mem_univ l)

def replacementBound (tm : FinTM2) : ℕ := machineReadBound tm + TM2Bounds.machinePushBound tm

def Window (tm : FinTM2) :=
  tm.Λ × tm.σ × (∀ k, BoundedStack tm k (machineReadBound tm))

def Replacement (tm : FinTM2) :=
  Option tm.Λ × tm.σ × (∀ k, BoundedStack tm k (replacementBound tm))

noncomputable instance windowFintype (tm : FinTM2) : Fintype (Window tm) := by
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  unfold Window
  infer_instance

noncomputable instance replacementFintype (tm : FinTM2) : Fintype (Replacement tm) := by
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  unfold Replacement
  infer_instance

def windowExecution (tm : FinTM2) (w : Window tm) : tm.Cfg :=
  stepAux (tm.m w.1) w.2.1 (fun k => decodeStack (w.2.2 k))

theorem windowExecution_stacksIn (tm : FinTM2) (w : Window tm) :
    StacksIn (machineSymbols tm) (windowExecution tm w).stk := by
  letI := tm.σFin
  exact stepAux_stacksIn _ _ _ _ (decodeStack_stacksIn w.2.2)
    (pushedSymbols_subset_machineSymbols tm w.1)

theorem windowExecution_length (tm : FinTM2) (w : Window tm) (k : tm.K) :
    ((windowExecution tm w).stk k).length ≤ replacementBound tm := by
  have hs := TM2Bounds.stepAux_stack_length (tm.m w.1) w.2.1
    (fun j => decodeStack (w.2.2 j)) k
  have hi := decodeStack_length (w.2.2 k)
  have hp : TM2Bounds.pushBound (tm.m w.1) ≤ TM2Bounds.machinePushBound tm := by
    letI := tm.ΛFin
    exact Finset.le_sup (f := fun l => TM2Bounds.pushBound (tm.m l)) (Finset.mem_univ w.1)
  exact hs.trans (Nat.add_le_add hi hp)

noncomputable def executeWindow (tm : FinTM2) (w : Window tm) : Replacement tm :=
  ((windowExecution tm w).l, (windowExecution tm w).var, fun k =>
    ⟨encodeStack tm k ((windowExecution tm w).stk k) (windowExecution_stacksIn tm w k),
      by rw [encodeStack_length]; exact windowExecution_length tm w k⟩)

def decodeReplacement (tm : FinTM2) (r : Replacement tm) : tm.Cfg :=
  ⟨r.1, r.2.1, fun k => decodeStack (r.2.2 k)⟩

theorem decode_executeWindow (tm : FinTM2) (w : Window tm) :
    decodeReplacement tm (executeWindow tm w) = windowExecution tm w := by
  have hs : (fun k => decodeStack ((executeWindow tm w).2.2 k)) =
      (windowExecution tm w).stk := by
    funext k
    exact encodeStack_decode _ _ _ _
  change (⟨(windowExecution tm w).l, (windowExecution tm w).var, _⟩ : tm.Cfg) = _
  rw [hs]
  cases windowExecution tm w
  rfl

noncomputable def captureWindow (tm : FinTM2) (l : tm.Λ) (v : tm.σ)
    (S : ∀ k, List (tm.Γ k)) (hS : StacksIn (machineSymbols tm) S) : Window tm :=
  (l, v, fun k =>
    ⟨encodeStack tm k ((S k).take (machineReadBound tm))
      (fun x hx => hS k x (List.mem_of_mem_take hx)),
      by rw [encodeStack_length, List.length_take]; exact Nat.min_le_left _ _⟩)

theorem captureWindow_decode (tm : FinTM2) (l : tm.Λ) (v : tm.σ)
    (S : ∀ k, List (tm.Γ k)) (hS : StacksIn (machineSymbols tm) S) (k : tm.K) :
    decodeStack ((captureWindow tm l v S hS).2.2 k) =
      (S k).take (machineReadBound tm) := encodeStack_decode _ _ _ _

theorem stepAux_take_decomposition_of_le {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    [DecidableEq K] (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (B : ℕ)
    (hB : readBound q ≤ B) :
    stepAux q v S =
      appendConfig (stepAux q v (fun k => (S k).take B)) (fun k => (S k).drop B) := by
  have h : ∀ k, readBound q ≤ ((S k).take B).length ∨ (S k).drop B = [] := by
    intro k
    by_cases hk : B ≤ (S k).length
    · left; simpa only [List.length_take, Nat.min_eq_left hk] using hB
    · right; exact List.drop_eq_nil_of_le (by omega)
  have he : appendStacks (fun k => (S k).take B) (fun k => (S k).drop B) = S := by
    funext k
    exact List.take_append_drop _ _
  have hs := stepAux_append q v (fun k => (S k).take B) (fun k => (S k).drop B) h
  rw [he] at hs
  exact hs

/-- Concrete window execution, followed by untouched suffixes, is the exact
mathlib transition. This is an equality of complete configurations. -/
theorem capture_execute_exact (tm : FinTM2) (l : tm.Λ) (v : tm.σ)
    (S : ∀ k, List (tm.Γ k)) (hS : StacksIn (machineSymbols tm) S) :
    stepAux (tm.m l) v S =
      appendConfig (decodeReplacement tm (executeWindow tm (captureWindow tm l v S hS)))
        (fun k => (S k).drop (machineReadBound tm)) := by
  rw [decode_executeWindow]
  have he : (fun k => decodeStack ((captureWindow tm l v S hS).2.2 k)) =
      fun k => (S k).take (machineReadBound tm) := funext (captureWindow_decode tm l v S hS)
  unfold windowExecution
  change stepAux (tm.m l) v S =
    appendConfig (stepAux (tm.m l) v (fun k => decodeStack ((captureWindow tm l v S hS).2.2 k))) _
  rw [he]
  exact stepAux_take_decomposition_of_le _ _ _ _ (readBound_le_machineReadBound tm l)

end ProteinFolding.SAT.CookLevinWindow
