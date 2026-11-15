import ProteinFolding.Common.TM2WalkCounters

/-! A fixed finite TM2 statement inspects the six signed-unary counters,
classifies their total size as zero, one, or at least two, and restores every
stack. It looks at at most two tokens per counter. This can be inlined after
each walk update without adding a loop over coordinate magnitude. -/

namespace ProteinFolding.TM2WalkInspector

open Turing TM2 TM2WalkCounters

def cap (n : ℕ) : Fin 3 := ⟨min n 2, by omega⟩

theorem cap_val (a : Fin 3) : cap a.val = a := by
  apply Fin.ext
  simp only [cap]
  omega

theorem cap_of_two_le (n : ℕ) (h : 2 ≤ n) : cap n = 2 := by
  apply Fin.ext
  simp only [cap]
  omega

theorem cap_add (a b : ℕ) : cap ((cap a).val + b) = cap (a + b) := by
  apply Fin.ext
  simp only [cap]
  omega

theorem cap_eq_zero (n : ℕ) : cap n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    change min n 2 = 0 at hv
    omega
  · intro h; subst n; rfl

theorem cap_eq_one (n : ℕ) : cap n = 1 ↔ n = 1 := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    change min n 2 = 1 at hv
    omega
  · intro h; subst n; rfl

variable {I L : Type}

def reset (q : Stmt (Alphabet I) L (Bool × Fin 3)) : Stmt (Alphabet I) L (Bool × Fin 3) :=
  .load (fun st => (false, st.2)) q

def probe (d : Fin 6) (q : Stmt (Alphabet I) L (Bool × Fin 3)) :
    Stmt (Alphabet I) L (Bool × Fin 3) :=
  .pop (.counter d) (fun st o => (o.isSome, st.2))
    (.branch Prod.fst
      (.peek (.counter d) (fun st o => (st.1, if o.isSome then 2 else cap (st.2.val + 1)))
        (.push (.counter d) (fun _ => ()) (reset q)))
      (reset q))

theorem probe_stepAux (d : Fin 6) (q : Stmt (Alphabet I) L (Bool × Fin 3))
    (flag : Bool) (acc : Fin 3) (input : List I) (c : Counts) :
    stepAux (probe d q) (flag, acc) (stackContents input c) =
      stepAux q (false, cap (acc.val + c d)) (stackContents input c) := by
  cases hc : c d with
  | zero =>
    have hpop : Function.update (stackContents input c) (.counter d) [] =
        stackContents input c := by
      change Function.update (stackContents input c) (.counter d) (List.replicate 0 ()) = _
      rw [update_counter, ← hc, Function.update_eq_self]
    simp [probe, stepAux, stackContents, hc, hpop, reset, cap_val]
  | succ m =>
    have hrestore : Function.update (stackContents input c)
        (.counter d) (() :: List.replicate m ()) = stackContents input c := by
      change Function.update (stackContents input c) (.counter d) (List.replicate (m + 1) ()) = _
      rw [update_counter, ← hc, Function.update_eq_self]
    cases m with
    | zero =>
      simp only [List.replicate_zero] at hrestore
      simp [probe, stepAux, stackContents, hc, hrestore, reset, List.replicate_succ]
    | succ m =>
      simp only [List.replicate_succ] at hrestore
      have hcap : cap (acc.val + (m + 1 + 1)) = 2 := cap_of_two_le _ (by omega)
      simp [probe, stepAux, stackContents, hc, hrestore, reset, List.replicate_succ, hcap]

def inspect (q : Stmt (Alphabet I) L (Bool × Fin 3)) : Stmt (Alphabet I) L (Bool × Fin 3) :=
  probe 0 (probe 1 (probe 2 (probe 3 (probe 4 (probe 5 q)))))

theorem inspect_stepAux (q : Stmt (Alphabet I) L (Bool × Fin 3))
    (flag : Bool) (acc : Fin 3) (input : List I) (c : Counts) :
    stepAux (inspect q) (flag, acc) (stackContents input c) =
      stepAux q (false, cap (acc.val + totalCounts c)) (stackContents input c) := by
  simp only [inspect, probe_stepAux, cap_add]
  simp [totalCounts, Nat.add_assoc]

theorem inspect_reduced_stepAux (q : Stmt (Alphabet I) L (Bool × Fin 3))
    (input : List I) (c : Counts) (h : Reduced c) :
    stepAux (inspect q) (false, 0) (stackContents input c) =
      stepAux q (false, cap ((coordinate c 0).natAbs + (coordinate c 1).natAbs +
        (coordinate c 2).natAbs)) (stackContents input c) := by
  rw [inspect_stepAux, totalCounts_eq_manhattan c h]
  simp

end ProteinFolding.TM2WalkInspector
