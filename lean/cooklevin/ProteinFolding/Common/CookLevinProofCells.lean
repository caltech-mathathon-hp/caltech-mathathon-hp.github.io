import ProteinFolding.Common.CookLevinProofWindowCNF

/-! Constant-width rules for every cell of a complete FinTM2 stack transition.
A replacement window is short; the untouched suffix shifts by a bounded
amount. Thus a next-row cell reads only the replacement and a fixed-width
current-row cell window, even when the complete stack is arbitrarily long.
-/

namespace ProteinFolding.SAT.CookLevinCells

open Turing TM2 CookLevinAlphabet CookLevinWindow CookLevinWindowCNF
open CookLevinCircuit CookLevinLocal

def cellWindowWidth (tm : FinTM2) : ℕ := replacementBound tm + machineReadBound tm + 1

def cellBase (tm : FinTM2) (n : ℕ) : ℕ := n - replacementBound tm

def CellWindow (tm : FinTM2) (k : tm.K) :=
  Fin (cellWindowWidth tm) → Option (Symbol tm k)

noncomputable instance cellWindowFintype (tm : FinTM2) (k : tm.K) :
    Fintype (CellWindow tm k) := by
  unfold CellWindow
  infer_instance

def cellSnapshot (tm : FinTM2) (k : tm.K) (n : ℕ) (xs : List (Symbol tm k)) :
    CellWindow tm k := fun i => xs[cellBase tm n + i.val]?

theorem sourceOffset_bound (tm : FinTM2) (k : tm.K) (n : ℕ) (r : Replacement tm)
    (_h : ((r.2.2 k).val).length ≤ n) :
    n + machineReadBound tm - ((r.2.2 k).val).length - cellBase tm n < cellWindowWidth tm := by
  have hr := (r.2.2 k).property
  unfold cellBase cellWindowWidth
  omega

def selectCell (tm : FinTM2) (k : tm.K) (n : ℕ) (r : Replacement tm)
    (q : CellWindow tm k) : Option (Symbol tm k) :=
  if h : n < ((r.2.2 k).val).length then ((r.2.2 k).val)[n]?
  else q ⟨n + machineReadBound tm - ((r.2.2 k).val).length - cellBase tm n,
    sourceOffset_bound tm k n r (Nat.le_of_not_gt h)⟩

theorem selectCell_exact (tm : FinTM2) (k : tm.K) (n : ℕ) (r : Replacement tm)
    (xs : List (Symbol tm k)) :
    selectCell tm k n r (cellSnapshot tm k n xs) =
      (((r.2.2 k).val) ++ xs.drop (machineReadBound tm))[n]? := by
  unfold selectCell
  split
  · exact (List.getElem?_append_left ‹_›).symm
  · rename_i hn
    rw [List.getElem?_append_right (Nat.le_of_not_gt hn), List.getElem?_drop]
    change xs[cellBase tm n + (n + machineReadBound tm - ((r.2.2 k).val).length -
      cellBase tm n)]? = xs[machineReadBound tm + (n - ((r.2.2 k).val).length)]?
    have hr := (r.2.2 k).property
    have he : cellBase tm n + (n + machineReadBound tm - ((r.2.2 k).val).length -
        cellBase tm n) = machineReadBound tm + (n - ((r.2.2 k).val).length) := by
      unfold cellBase
      omega
    rw [he]

/-- This cell selector describes the actual, complete TM2 successor stack. -/
theorem transition_cell_exact (tm : FinTM2) (l : tm.Λ) (v : tm.σ)
    (S : ∀ k, List (tm.Γ k)) (hS : StacksIn (machineSymbols tm) S) (k : tm.K) (n : ℕ) :
    ((stepAux (tm.m l) v S).stk k)[n]? =
      (selectCell tm k n (executeWindow tm (captureWindow tm l v S hS))
        (cellSnapshot tm k n (encodeStack tm k (S k) (hS k)))).map Subtype.val := by
  rw [selectCell_exact]
  rw [← List.getElem?_map (f := fun x : Symbol tm k => x.val)]
  simp only [List.map_append, List.map_drop]
  change ((stepAux (tm.m l) v S).stk k)[n]? =
    (decodeStack ((executeWindow tm (captureWindow tm l v S hS)).2.2 k) ++
      ((encodeStack tm k (S k) (hS k)).map Subtype.val).drop (machineReadBound tm))[n]?
  rw [encodeStack_decode]
  have he := congrArg (fun c : tm.Cfg => (c.stk k)[n]?) (capture_execute_exact tm l v S hS)
  exact he

noncomputable def cellAllowed (tm : FinTM2) (k : tm.K) (n : ℕ) (bs : List Bool) : Bool := by
  classical
  exact decide (∃ r : Replacement tm, ∃ q : CellWindow tm k,
    bs = finiteCode r ++ finiteCode q ++ finiteCode (selectCell tm k n r q))

theorem cellAllowed_iff (tm : FinTM2) (k : tm.K) (n : ℕ) (bs : List Bool) :
    cellAllowed tm k n bs = true ↔ ∃ r : Replacement tm, ∃ q : CellWindow tm k,
      bs = finiteCode r ++ finiteCode q ++ finiteCode (selectCell tm k n r q) := by
  classical
  simp only [cellAllowed, decide_eq_true_eq]

theorem cellAllowed_code_iff (tm : FinTM2) (k : tm.K) (n : ℕ)
    (r : Replacement tm) (q : CellWindow tm k) (b : Option (Symbol tm k)) :
    cellAllowed tm k n (finiteCode r ++ finiteCode q ++ finiteCode b) = true ↔
      b = selectCell tm k n r q := by
  rw [cellAllowed_iff]
  constructor
  · rintro ⟨r', q', h⟩
    have hparts := List.append_inj h (by simp only [List.length_append, finiteCode_length])
    have hinputs := List.append_inj hparts.1 (by simp only [finiteCode_length])
    have hr : r = r' := finiteCode_injective hinputs.1
    have hq : q = q' := finiteCode_injective hinputs.2
    subst r'
    subst q'
    exact finiteCode_injective hparts.2
  · rintro rfl
    exact ⟨r, q, rfl⟩

noncomputable def cellCNF (tm : FinTM2) (k : tm.K) (n : ℕ) (vars : List ℕ) : CNF :=
  relationCNF vars (cellAllowed tm k n)

theorem cellCNF_iff (tm : FinTM2) (k : tm.K) (n : ℕ) (vars : List ℕ) (a : ℕ → Bool) :
    Satisfied a (cellCNF tm k n vars) ↔ ∃ r : Replacement tm, ∃ q : CellWindow tm k,
      vars.map a = finiteCode r ++ finiteCode q ++ finiteCode (selectCell tm k n r q) := by
  rw [cellCNF, relationCNF_iff, cellAllowed_iff]

theorem cellCNF_codes_iff (tm : FinTM2) (k : tm.K) (n : ℕ) (vars : List ℕ) (a : ℕ → Bool)
    (r : Replacement tm) (q : CellWindow tm k) (b : Option (Symbol tm k))
    (h : vars.map a = finiteCode r ++ finiteCode q ++ finiteCode b) :
    Satisfied a (cellCNF tm k n vars) ↔ b = selectCell tm k n r q := by
  rw [cellCNF, relationCNF_iff, h, cellAllowed_code_iff]

noncomputable def cellArity (tm : FinTM2) (k : tm.K) : ℕ :=
  Fintype.card (Replacement tm) + Fintype.card (CellWindow tm k) + Fintype.card (Option (Symbol tm k))

theorem cellAllowed_length (tm : FinTM2) (k : tm.K) (n : ℕ) (bs : List Bool)
    (h : cellAllowed tm k n bs = true) : bs.length = cellArity tm k := by
  obtain ⟨r, q, rfl⟩ := (cellAllowed_iff tm k n bs).mp h
  simp only [List.length_append, finiteCode_length, cellArity]

theorem cellCNF_clause_count (tm : FinTM2) (k : tm.K) (n : ℕ) (vars : List ℕ)
    (h : vars.length = cellArity tm k) :
    (cellCNF tm k n vars).length ≤ 2 ^ cellArity tm k := by
  simpa only [cellCNF, h] using relationCNF_clause_count vars (cellAllowed tm k n)

theorem cellCNF_encoded_length (tm : FinTM2) (k : tm.K) (n : ℕ) (vars : List ℕ)
    (h : vars.length = cellArity tm k) (V : ℕ) (hv : ∀ i ∈ vars, i ≤ V) :
    (cnfEncoding.encode (cellCNF tm k n vars)).length ≤
      (2 ^ cellArity tm k * cellArity tm k) * (V + 2) + 2 ^ cellArity tm k := by
  simpa only [cellCNF, h] using relationCNF_encoded_length_bound vars (cellAllowed tm k n) V hv

theorem boundedList_ext {A : Type*} {xs ys : List A} (N : ℕ)
    (hx : xs.length ≤ N) (hy : ys.length ≤ N)
    (h : ∀ n < N, xs[n]? = ys[n]?) : xs = ys := by
  apply List.ext_getElem?
  intro n
  by_cases hn : n < N
  · exact h n hn
  · have hxn : xs[n]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    have hyn : ys[n]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [hxn, hyn]

theorem config_ext (tm : FinTM2) (a b : tm.Cfg)
    (hl : a.l = b.l) (hv : a.var = b.var) (hS : a.stk = b.stk) : a = b := by
  cases a
  cases b
  cases hl
  cases hv
  cases hS
  rfl

/-- Finitely many fixed-width cell rules determine the complete successor.
For stacks of length at most L only L + P successor cells need be checked,
where P is the machine's fixed per-step push bound. -/
theorem bounded_transition_iff (tm : FinTM2) (l : tm.Λ) (v : tm.σ)
    (S : ∀ k, List (tm.Γ k)) (hS : StacksIn (machineSymbols tm) S)
    (L : ℕ) (hL : ∀ k, (S k).length ≤ L) (c : tm.Cfg)
    (hc : ∀ k, (c.stk k).length ≤ L + TM2Bounds.machinePushBound tm) :
    c = stepAux (tm.m l) v S ↔
      c.l = (executeWindow tm (captureWindow tm l v S hS)).1 ∧
      c.var = (executeWindow tm (captureWindow tm l v S hS)).2.1 ∧
      ∀ k, ∀ n < L + TM2Bounds.machinePushBound tm,
        (c.stk k)[n]? =
          (selectCell tm k n (executeWindow tm (captureWindow tm l v S hS))
            (cellSnapshot tm k n (encodeStack tm k (S k) (hS k)))).map Subtype.val := by
  have he := capture_execute_exact tm l v S hS
  have hl := congrArg (fun d : tm.Cfg => d.l) he
  have hv := congrArg (fun d : tm.Cfg => d.var) he
  constructor
  · rintro rfl
    exact ⟨hl, hv, fun k n _ => transition_cell_exact tm l v S hS k n⟩
  · rintro ⟨hcl, hcv, hcells⟩
    apply config_ext tm c (stepAux (tm.m l) v S) (hcl.trans hl.symm) (hcv.trans hv.symm)
    funext k
    apply boundedList_ext (L + TM2Bounds.machinePushBound tm) (hc k)
    · have hs := TM2Bounds.stepAux_stack_length (tm.m l) v S k
      have hp : TM2Bounds.pushBound (tm.m l) ≤ TM2Bounds.machinePushBound tm := by
        letI := tm.ΛFin
        exact Finset.le_sup (f := fun j => TM2Bounds.pushBound (tm.m j)) (Finset.mem_univ l)
      exact hs.trans (Nat.add_le_add (hL k) hp)
    · intro n hn
      exact (hcells k n hn).trans (transition_cell_exact tm l v S hS k n).symm

end ProteinFolding.SAT.CookLevinCells
