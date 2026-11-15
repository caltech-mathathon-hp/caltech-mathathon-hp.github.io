import ProteinFolding.Common.TM2WalkCounters

/-!
# A concrete bounded TM2 inspector for tetrahedral displacement

Six signed-unary counters represent three coordinates. This finite TM2 body
classifies their total mass as 0,1,2,3,or at least 4 while restoring every
counter. Diamond adjacency will use the class 3; collision detection uses 0.
-/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Inspector

open Turing TM2 ProteinFolding.TM2WalkCounters

def cap (n : ℕ) : Fin 5 := ⟨min n 4, by omega⟩

theorem cap_val (a : Fin 5) : cap a.val = a := by
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
    change min n 4 = 0 at hv
    omega
  · intro h; subst n; rfl

theorem cap_eq_three (n : ℕ) : cap n = 3 ↔ n = 3 := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    change min n 4 = 3 at hv
    omega
  · intro h; subst n; rfl

variable {I L : Type}

def reset (q : Stmt (Alphabet I) L (Bool × Fin 5)) : Stmt (Alphabet I) L (Bool × Fin 5) :=
  .load (fun st => (false, st.2)) q

/-- Pop at most `fuel` tokens, recording their capped count, and restore them.
Only the instance `fuel=4` is used in the finite inspector. -/
def probeFuel : ℕ → Fin 6 → Stmt (Alphabet I) L (Bool × Fin 5) →
    Stmt (Alphabet I) L (Bool × Fin 5)
  | 0, _, q => reset q
  | n + 1, d, q =>
    .pop (.counter d) (fun st o => (o.isSome, if o.isSome then cap (st.2.val + 1) else st.2))
      (.branch Prod.fst
        (probeFuel n d (.push (.counter d) (fun _ => ()) (reset q)))
        (reset q))

theorem probeFuel_stepAux (fuel : ℕ) (d : Fin 6)
    (q : Stmt (Alphabet I) L (Bool × Fin 5)) (flag : Bool) (acc : Fin 5)
    (input : List I) (c : Counts) :
    stepAux (probeFuel fuel d q) (flag, acc) (stackContents input c) =
      stepAux q (false, cap (acc.val + min fuel (c d))) (stackContents input c) := by
  induction fuel generalizing q flag acc c with
  | zero => simp [probeFuel, reset, stepAux, cap_val]
  | succ fuel ih =>
    cases hc : c d with
    | zero =>
      have hpop : Function.update (stackContents input c) (.counter d) [] =
          stackContents input c := by
        change Function.update (stackContents input c) (.counter d) (List.replicate 0 ()) = _
        rw [update_counter, ← hc, Function.update_eq_self]
      simp [probeFuel, stepAux, stackContents, hc, hpop, reset, cap_val]
    | succ m =>
      let c' := Function.update c d m
      have hrestore : Function.update (stackContents input c') (.counter d) (() :: List.replicate m ()) =
          stackContents input c := by
        change Function.update (stackContents input c') (.counter d) (List.replicate (m + 1) ()) = _
        rw [update_counter]
        congr 1
        funext e
        by_cases he : e = d
        · subst e; simp [hc]
        · simp [c', he]
      have hrec := ih (.push (.counter d) (fun _ => ()) (reset q)) true
        (cap (acc.val + 1)) c'
      simp only [c', Function.update_self] at hrec
      have hrestore' : Function.update (stackContents input c') (.counter d)
          (() :: stackContents input c' (.counter d)) = stackContents input c := by
        simpa only [stackContents, c', Function.update_self] using hrestore
      simp only [probeFuel, stepAux, stackContents, hc, List.head?_replicate,
        List.tail_replicate, Option.isSome_some, cond_true]
      rw [update_counter]
      change stepAux (probeFuel fuel d (.push (.counter d) (fun _ => ()) (reset q)))
        (true, cap (acc.val + 1)) (stackContents input c') = _
      rw [hrec]
      simp only [stepAux, reset, cap_add]
      rw [hrestore']
      apply congrArg (fun r : Bool × Fin 5 => stepAux q r (stackContents input c))
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp only [cap]
        omega

def probe (d : Fin 6) (q : Stmt (Alphabet I) L (Bool × Fin 5)) :
    Stmt (Alphabet I) L (Bool × Fin 5) := probeFuel 4 d q

theorem probe_stepAux (d : Fin 6) (q : Stmt (Alphabet I) L (Bool × Fin 5))
    (flag : Bool) (acc : Fin 5) (input : List I) (c : Counts) :
    stepAux (probe d q) (flag, acc) (stackContents input c) =
      stepAux q (false, cap (acc.val + c d)) (stackContents input c) := by
  rw [probe, probeFuel_stepAux]
  congr 2
  apply Fin.ext
  simp only [cap]
  omega

def inspect (q : Stmt (Alphabet I) L (Bool × Fin 5)) :
    Stmt (Alphabet I) L (Bool × Fin 5) :=
  probe 0 (probe 1 (probe 2 (probe 3 (probe 4 (probe 5 q)))))

theorem inspect_stepAux (q : Stmt (Alphabet I) L (Bool × Fin 5))
    (flag : Bool) (acc : Fin 5) (input : List I) (c : Counts) :
    stepAux (inspect q) (flag, acc) (stackContents input c) =
      stepAux q (false, cap (acc.val + totalCounts c)) (stackContents input c) := by
  simp only [inspect, probe_stepAux, cap_add]
  simp [totalCounts, Nat.add_assoc]

theorem inspect_reduced_stepAux (q : Stmt (Alphabet I) L (Bool × Fin 5))
    (input : List I) (c : Counts) (hc : Reduced c) :
    stepAux (inspect q) (false, 0) (stackContents input c) =
      stepAux q (false, cap ((coordinate c 0).natAbs + (coordinate c 1).natAbs +
        (coordinate c 2).natAbs)) (stackContents input c) := by
  rw [inspect_stepAux, totalCounts_eq_manhattan c hc]
  simp

end ProteinFolding.Tetrahedral.CertificatesTM2Inspector
