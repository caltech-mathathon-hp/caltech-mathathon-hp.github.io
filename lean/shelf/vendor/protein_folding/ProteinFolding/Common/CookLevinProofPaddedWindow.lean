import ProteinFolding.Common.CookLevinProofCells
import ProteinFolding.Common.CookLevinProofPadded

/-! The concrete finite transition window including the halted copying case.
Its total transition reconstructs paddedStep on complete configurations.
-/

namespace ProteinFolding.SAT.CookLevinPaddedWindow

open Turing TM2 CookLevinAlphabet CookLevinLocality CookLevinWindow
open CookLevinWindowCNF CookLevinCells CookLevinPadded CookLevinLocal CookLevinCircuit

def Control (tm : FinTM2) := Option tm.Λ × tm.σ

noncomputable instance controlFintype (tm : FinTM2) : Fintype (Control tm) := by
  letI := tm.ΛFin
  letI := tm.σFin
  unfold Control
  infer_instance

def PaddedWindow (tm : FinTM2) :=
  Control tm × (∀ k, BoundedStack tm k (machineReadBound tm))

noncomputable instance paddedWindowFintype (tm : FinTM2) : Fintype (PaddedWindow tm) := by
  letI := tm.kFin
  unfold PaddedWindow
  infer_instance

def windowConfig (tm : FinTM2) (w : PaddedWindow tm) : tm.Cfg :=
  ⟨w.1.1, w.1.2, fun k => decodeStack (w.2 k)⟩

def localExecution (tm : FinTM2) (w : PaddedWindow tm) : tm.Cfg :=
  paddedStep tm (windowConfig tm w)

theorem localExecution_stacksIn (tm : FinTM2) (w : PaddedWindow tm) :
    StacksIn (machineSymbols tm) (localExecution tm w).stk :=
  paddedStep_stacksIn tm _ (decodeStack_stacksIn w.2)

theorem localExecution_length (tm : FinTM2) (w : PaddedWindow tm) (k : tm.K) :
    ((localExecution tm w).stk k).length ≤ replacementBound tm := by
  exact (paddedStep_stack_length tm (windowConfig tm w) k).trans
    (Nat.add_le_add_right (decodeStack_length (w.2 k)) _)

noncomputable def executePaddedWindow (tm : FinTM2) (w : PaddedWindow tm) : Replacement tm :=
  ((localExecution tm w).l, (localExecution tm w).var, fun k =>
    ⟨encodeStack tm k ((localExecution tm w).stk k) (localExecution_stacksIn tm w k),
      by rw [encodeStack_length]; exact localExecution_length tm w k⟩)

theorem decode_executePaddedWindow (tm : FinTM2) (w : PaddedWindow tm) :
    decodeReplacement tm (executePaddedWindow tm w) = localExecution tm w := by
  apply config_ext tm (decodeReplacement tm (executePaddedWindow tm w)) (localExecution tm w)
  · rfl
  · rfl
  · funext k
    exact encodeStack_decode _ _ _ _

noncomputable def capturePaddedWindow (tm : FinTM2) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) : PaddedWindow tm :=
  ((c.l, c.var), fun k =>
    ⟨encodeStack tm k ((c.stk k).take (machineReadBound tm))
      (fun x hx => h k x (List.mem_of_mem_take hx)),
      by rw [encodeStack_length, List.length_take]; exact Nat.min_le_left _ _⟩)

theorem capturePaddedWindow_decode (tm : FinTM2) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (k : tm.K) :
    decodeStack ((capturePaddedWindow tm c h).2 k) = (c.stk k).take (machineReadBound tm) :=
  encodeStack_decode _ _ _ _

/-- Includes halted rows: the finite window is executed, then exactly the old
suffixes are reattached. The equality is for full mathlib configurations. -/
theorem capturePadded_execute_exact (tm : FinTM2) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) :
    paddedStep tm c =
      appendConfig (decodeReplacement tm (executePaddedWindow tm (capturePaddedWindow tm c h)))
        (fun k => (c.stk k).drop (machineReadBound tm)) := by
  rw [decode_executePaddedWindow]
  have hs : (fun k => decodeStack ((capturePaddedWindow tm c h).2 k)) =
      fun k => (c.stk k).take (machineReadBound tm) :=
    funext (capturePaddedWindow_decode tm c h)
  unfold localExecution windowConfig
  change paddedStep tm c =
    appendConfig (paddedStep tm ⟨c.l, c.var, fun k => decodeStack ((capturePaddedWindow tm c h).2 k)⟩) _
  rw [hs]
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none =>
    apply config_ext tm _ _
    · rfl
    · rfl
    · funext k
      exact (List.take_append_drop _ _).symm
  | some l =>
    change stepAux (tm.m l) v S =
      appendConfig (stepAux (tm.m l) v (fun k => (S k).take (machineReadBound tm))) _
    exact stepAux_take_decomposition_of_le _ _ _ _ (readBound_le_machineReadBound tm l)

theorem padded_transition_cell_exact (tm : FinTM2) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (k : tm.K) (n : ℕ) :
    ((paddedStep tm c).stk k)[n]? =
      (selectCell tm k n (executePaddedWindow tm (capturePaddedWindow tm c h))
        (cellSnapshot tm k n (encodeStack tm k (c.stk k) (h k)))).map Subtype.val := by
  rw [selectCell_exact]
  rw [← List.getElem?_map (f := fun x : Symbol tm k => x.val)]
  simp only [List.map_append, List.map_drop]
  change ((paddedStep tm c).stk k)[n]? =
    (decodeStack ((executePaddedWindow tm (capturePaddedWindow tm c h)).2.2 k) ++
      ((encodeStack tm k (c.stk k) (h k)).map Subtype.val).drop (machineReadBound tm))[n]?
  rw [encodeStack_decode]
  exact congrArg (fun d : tm.Cfg => (d.stk k)[n]?) (capturePadded_execute_exact tm c h)

noncomputable def paddedWindowAllowed (tm : FinTM2) (bs : List Bool) : Bool := by
  classical
  exact decide (∃ w : PaddedWindow tm,
    bs = finiteCode w ++ finiteCode (executePaddedWindow tm w))

theorem paddedWindowAllowed_iff (tm : FinTM2) (bs : List Bool) :
    paddedWindowAllowed tm bs = true ↔ ∃ w : PaddedWindow tm,
      bs = finiteCode w ++ finiteCode (executePaddedWindow tm w) := by
  classical
  simp only [paddedWindowAllowed, decide_eq_true_eq]

theorem paddedWindowAllowed_code_iff (tm : FinTM2) (w : PaddedWindow tm) (r : Replacement tm) :
    paddedWindowAllowed tm (finiteCode w ++ finiteCode r) = true ↔ r = executePaddedWindow tm w := by
  rw [paddedWindowAllowed_iff]
  constructor
  · rintro ⟨u, he⟩
    have hp := List.append_inj he (by simp only [finiteCode_length])
    have hu : w = u := finiteCode_injective hp.1
    subst u
    exact finiteCode_injective hp.2
  · rintro rfl
    exact ⟨w, rfl⟩

noncomputable def paddedWindowCNF (tm : FinTM2) (vars : List ℕ) : CNF :=
  relationCNF vars (paddedWindowAllowed tm)

theorem paddedWindowCNF_codes_iff (tm : FinTM2) (vars : List ℕ) (a : ℕ → Bool)
    (w : PaddedWindow tm) (r : Replacement tm)
    (h : vars.map a = finiteCode w ++ finiteCode r) :
    Satisfied a (paddedWindowCNF tm vars) ↔ r = executePaddedWindow tm w := by
  rw [paddedWindowCNF, relationCNF_iff, h, paddedWindowAllowed_code_iff]

end ProteinFolding.SAT.CookLevinPaddedWindow
