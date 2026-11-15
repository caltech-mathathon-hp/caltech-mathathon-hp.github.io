import ProteinFolding.Tetrahedral.CertificatesTM2Directions

/-!
# Inlining a diamond step into a concrete TM2 statement

Three signed-unary updates can be executed in the same TM2 statement before
the next geometric inspection. Thus a suffix-row verifier need not introduce
or inspect artificial intermediate vertices of the unit-step expansion.
-/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Updates

open Turing TM2
open ProteinFolding.TM2WalkCounters CertificatesTM2Directions

variable {I L S : Type}

def reset (q : Stmt (Alphabet I) L (Bool × S)) : Stmt (Alphabet I) L (Bool × S) :=
  .load (fun st => (false, st.2)) q

def unitUpdate (d : Fin 6) (q : Stmt (Alphabet I) L (Bool × S)) :
    Stmt (Alphabet I) L (Bool × S) :=
  .pop (.counter (opposite d)) (fun st o => (o.isSome, st.2))
    (.branch Prod.fst (reset q) (.push (.counter d) (fun _ => ()) (reset q)))

theorem unitUpdate_stepAux (d : Fin 6) (q : Stmt (Alphabet I) L (Bool × S))
    (flag : Bool) (s : S) (input : List I) (c : Counts) :
    stepAux (unitUpdate d q) (flag, s) (stackContents input c) =
      stepAux q (false, s) (stackContents input (updateCounts c d)) := by
  cases hc : c (opposite d) with
  | zero =>
    have hpop : Function.update (stackContents input c) (.counter (opposite d)) [] =
        stackContents input c := by
      change Function.update (stackContents input c) (.counter (opposite d)) (List.replicate 0 ()) = _
      rw [update_counter, ← hc, Function.update_eq_self]
    simp [unitUpdate, stepAux, stackContents, hc, hpop, reset, updateCounts,
      update_counter, List.replicate_succ]
    apply congrArg (fun st => stepAux q (false, s) st)
    simpa only [List.replicate_succ] using update_counter input c d (c d + 1)
  | succ m =>
    simp [unitUpdate, stepAux, stackContents, hc, reset, updateCounts, update_counter,
      List.replicate_succ]

def updateWord : List (Fin 6) → Stmt (Alphabet I) L (Bool × S) →
    Stmt (Alphabet I) L (Bool × S)
  | [], q => reset q
  | d :: ds, q => unitUpdate d (updateWord ds q)

theorem updateWord_stepAux (ds : List (Fin 6)) (q : Stmt (Alphabet I) L (Bool × S))
    (flag : Bool) (s : S) (input : List I) (c : Counts) :
    stepAux (updateWord ds q) (flag, s) (stackContents input c) =
      stepAux q (false, s) (stackContents input (runCounts c ds)) := by
  induction ds generalizing flag c with
  | nil => simp [updateWord, reset, stepAux, runCounts]
  | cons d ds ih => rw [updateWord, unitUpdate_stepAux, ih, runCounts]

def diamondUpdate (isA : Bool) (d : Fin 4) (q : Stmt (Alphabet I) L (Bool × S)) :
    Stmt (Alphabet I) L (Bool × S) := updateWord (unitDirections isA d) q

theorem diamondUpdate_stepAux (isA : Bool) (d : Fin 4) (q : Stmt (Alphabet I) L (Bool × S))
    (flag : Bool) (s : S) (input : List I) (c : Counts) :
    stepAux (diamondUpdate isA d q) (flag, s) (stackContents input c) =
      stepAux q (false, s) (stackContents input (runCounts c (unitDirections isA d))) :=
  updateWord_stepAux _ _ _ _ _ _

theorem diamondUpdate_coordinate (c : Counts) (isA : Bool) (d : Fin 4) (k : Fin 3) :
    coordinate (runCounts c (unitDirections isA d)) k = coordinate c k +
      (if isA then bondVector d k else -bondVector d k) := by
  rw [runCounts_coordinate, unitDirections_displacement]

def dispatch (decode : S → Bool × Fin 4) (symbols : List (Bool × Fin 4))
    (q : Stmt (Alphabet I) L (Bool × S)) : Stmt (Alphabet I) L (Bool × S) :=
  match symbols with
  | [] => reset q
  | a :: symbols => .branch (fun st => decide (decode st.2 = a))
      (diamondUpdate a.1 a.2 q) (dispatch decode symbols q)

theorem dispatch_stepAux (decode : S → Bool × Fin 4) (symbols : List (Bool × Fin 4))
    (q : Stmt (Alphabet I) L (Bool × S)) (flag : Bool) (s : S)
    (input : List I) (c : Counts) (h : decode s ∈ symbols) :
    stepAux (dispatch decode symbols q) (flag, s) (stackContents input c) =
      stepAux q (false, s)
        (stackContents input (runCounts c (unitDirections (decode s).1 (decode s).2))) := by
  induction symbols with
  | nil => simp at h
  | cons a symbols ih =>
    by_cases ha : decode s = a
    · simp [dispatch, stepAux, ha, diamondUpdate_stepAux]
    · have ht := (List.mem_cons.mp h).resolve_left ha
      simpa [dispatch, stepAux, ha] using ih ht

def allSymbols : List (Bool × Fin 4) :=
  [(true, 0), (true, 1), (true, 2), (true, 3),
    (false, 0), (false, 1), (false, 2), (false, 3)]

theorem mem_allSymbols (a : Bool × Fin 4) : a ∈ allSymbols := by revert a; decide

def dispatchAll (decode : S → Bool × Fin 4) (q : Stmt (Alphabet I) L (Bool × S)) :
    Stmt (Alphabet I) L (Bool × S) := dispatch decode allSymbols q

theorem dispatchAll_stepAux (decode : S → Bool × Fin 4)
    (q : Stmt (Alphabet I) L (Bool × S)) (flag : Bool) (s : S)
    (input : List I) (c : Counts) :
    stepAux (dispatchAll decode q) (flag, s) (stackContents input c) =
      stepAux q (false, s)
        (stackContents input (runCounts c (unitDirections (decode s).1 (decode s).2))) :=
  dispatch_stepAux _ _ _ _ _ _ _ (mem_allSymbols _)

end ProteinFolding.Tetrahedral.CertificatesTM2Updates
