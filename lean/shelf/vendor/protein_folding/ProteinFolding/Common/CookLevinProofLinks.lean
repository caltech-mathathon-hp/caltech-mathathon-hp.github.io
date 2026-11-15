import ProteinFolding.Common.CookLevinProofRows

/-! Projection links between concrete row components. Their soundness and
completeness are proved against the actual padded mathlib TM2 transition.
Every link inspects machine-fixed finite domains; the number of links grows
linearly with the stack bound.
-/

namespace ProteinFolding.SAT.CookLevinLinks

open Turing TM2 CookLevinAlphabet CookLevinWindow CookLevinWindowCNF
open CookLevinCells CookLevinPadded CookLevinPaddedWindow CookLevinRows

def rowCell {tm : FinTM2} {M : ℕ} (r : Row tm M) (k : tm.K) (n : ℕ) : Option (Symbol tm k) :=
  if h : n < M then r.cells k ⟨n, h⟩ else none

def Links {tm : FinTM2} {M : ℕ} (r s : Row tm M) : Prop :=
  r.window.1 = r.control ∧
  (∀ k (i : Fin (machineReadBound tm)), ((r.window.2 k).val)[i.val]? = rowCell r k i.val) ∧
  r.replacement = executePaddedWindow tm r.window ∧
  s.control = (r.replacement.1, r.replacement.2.1) ∧
  (∀ k (n : Fin M) (i : Fin (cellWindowWidth tm)),
    r.queries k n i = rowCell r k (cellBase tm n.val + i.val)) ∧
  (∀ k (n : Fin M), s.cells k n = selectCell tm k n.val r.replacement (r.queries k n))

noncomputable def encodedStack (tm : FinTM2) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (k : tm.K) : List (Symbol tm k) :=
  encodeStack tm k (c.stk k) (h k)

theorem encodedStack_length (tm : FinTM2) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (k : tm.K) :
    (encodedStack tm c h k).length = (c.stk k).length := encodeStack_length _ _ _ _

theorem encodedStack_get_map (tm : FinTM2) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (k : tm.K) (n : ℕ) :
    ((encodedStack tm c h k)[n]?).map Subtype.val = (c.stk k)[n]? := by
  rw [← List.getElem?_map (f := fun x : Symbol tm k => x.val)]
  change ((encodeStack tm k (c.stk k) (h k)).map Subtype.val)[n]? = _
  rw [encodeStack_decode]

theorem encodedStack_take (tm : FinTM2) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (k : tm.K) (N : ℕ) :
    encodeStack tm k ((c.stk k).take N) (fun x hx => h k x (List.mem_of_mem_take hx)) =
      (encodedStack tm c h k).take N := by
  apply List.map_injective_iff.mpr Subtype.coe_injective
  rw [encodeStack_decode, List.map_take]
  change (c.stk k).take N = ((encodeStack tm k (c.stk k) (h k)).map Subtype.val).take N
  rw [encodeStack_decode]

def Represents {tm : FinTM2} {M : ℕ} (r : Row tm M) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) : Prop :=
  r.control = (c.l, c.var) ∧ ∀ k (n : Fin M), r.cells k n = (encodedStack tm c h k)[n.val]?

theorem rowCell_represents {tm : FinTM2} {M : ℕ} (r : Row tm M) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (hr : Represents r c h)
    (hM : ∀ k, (c.stk k).length ≤ M) (k : tm.K) (n : ℕ) :
    rowCell r k n = (encodedStack tm c h k)[n]? := by
  unfold rowCell
  split
  · exact hr.2 k _
  · rename_i hn
    symm
    apply List.getElem?_eq_none_iff.mpr
    rw [encodedStack_length]
    exact (hM k).trans (Nat.le_of_not_gt hn)

noncomputable def canonicalRow (tm : FinTM2) (M : ℕ) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) : Row tm M where
  control := (c.l, c.var)
  cells k n := (encodedStack tm c h k)[n.val]?
  window := capturePaddedWindow tm c h
  replacement := executePaddedWindow tm (capturePaddedWindow tm c h)
  queries k n := cellSnapshot tm k n.val (encodedStack tm c h k)

theorem canonicalRow_represents (tm : FinTM2) (M : ℕ) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) : Represents (canonicalRow tm M c h) c h :=
  ⟨rfl, fun _ _ => rfl⟩

theorem window_unique {tm : FinTM2} {M : ℕ} (r s : Row tm M) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (hr : Represents r c h)
    (hM : ∀ k, (c.stk k).length ≤ M) (hlinks : Links r s) :
    r.window = capturePaddedWindow tm c h := by
  apply Prod.ext
  · exact hlinks.1.trans hr.1
  · funext k
    apply Subtype.ext
    apply boundedList_ext (machineReadBound tm) (r.window.2 k).property
      ((capturePaddedWindow tm c h).2 k).property
    intro n hn
    rw [hlinks.2.1 k ⟨n, hn⟩, rowCell_represents r c h hr hM]
    change (encodedStack tm c h k)[n]? =
      (encodeStack tm k ((c.stk k).take (machineReadBound tm)) _)[n]?
    rw [encodedStack_take, List.getElem?_take_of_lt hn]

theorem query_unique {tm : FinTM2} {M : ℕ} (r s : Row tm M) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (hr : Represents r c h)
    (hM : ∀ k, (c.stk k).length ≤ M) (hlinks : Links r s) (k : tm.K) (n : Fin M) :
    r.queries k n = cellSnapshot tm k n.val (encodedStack tm c h k) := by
  funext i
  exact (hlinks.2.2.2.2.1 k n i).trans (rowCell_represents r c h hr hM k _)

/-- All projection links force the actual complete machine successor on the
next row's control and represented cells, including copying after halt. -/
theorem links_sound {tm : FinTM2} {M : ℕ} (r s : Row tm M) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (hr : Represents r c h)
    (hM : ∀ k, (c.stk k).length ≤ M) (hlinks : Links r s) :
    Represents s (paddedStep tm c) (paddedStep_stacksIn tm c h) := by
  have hw := window_unique r s c h hr hM hlinks
  have hrep : r.replacement = executePaddedWindow tm (capturePaddedWindow tm c h) := by
    rw [hlinks.2.2.1, hw]
  constructor
  · have he := capturePadded_execute_exact tm c h
    have hl := congrArg (fun d : tm.Cfg => d.l) he
    have hv := congrArg (fun d : tm.Cfg => d.var) he
    exact (hlinks.2.2.2.1.trans (by rw [hrep])).trans (Prod.ext hl.symm hv.symm)
  · intro k n
    apply Option.map_injective Subtype.coe_injective
    rw [hlinks.2.2.2.2.2 k n, hrep, query_unique r s c h hr hM hlinks k n,
      encodedStack_get_map]
    exact (padded_transition_cell_exact tm c h k n.val).symm

theorem canonicalRows_linked (tm : FinTM2) (M : ℕ) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) (hM : ∀ k, (c.stk k).length ≤ M) :
    Links (canonicalRow tm M c h)
      (canonicalRow tm M (paddedStep tm c) (paddedStep_stacksIn tm c h)) := by
  refine ⟨rfl, ?_, rfl, ?_, ?_, ?_⟩
  · intro k n
    change (encodeStack tm k ((c.stk k).take (machineReadBound tm)) _)[n.val]? = _
    rw [encodedStack_take, List.getElem?_take_of_lt n.isLt]
    exact (rowCell_represents _ c h (canonicalRow_represents tm M c h) hM k _).symm
  · have he := capturePadded_execute_exact tm c h
    have hl := congrArg (fun d : tm.Cfg => d.l) he
    have hv := congrArg (fun d : tm.Cfg => d.var) he
    exact Prod.ext hl hv
  · intro k n i
    exact (rowCell_represents _ c h (canonicalRow_represents tm M c h) hM k _).symm
  · intro k n
    apply Option.map_injective Subtype.coe_injective
    change ((encodedStack tm (paddedStep tm c) (paddedStep_stacksIn tm c h) k)[n.val]?).map Subtype.val =
      (selectCell tm k n.val (executePaddedWindow tm (capturePaddedWindow tm c h))
        (cellSnapshot tm k n.val (encodedStack tm c h k))).map Subtype.val
    rw [encodedStack_get_map]
    exact padded_transition_cell_exact tm c h k n.val

end ProteinFolding.SAT.CookLevinLinks
