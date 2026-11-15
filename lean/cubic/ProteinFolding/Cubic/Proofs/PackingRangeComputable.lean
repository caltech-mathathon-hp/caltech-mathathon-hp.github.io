import ProteinFolding.Cubic.Proofs.PackingSources
import ProteinFolding.Common.TM2CompositionPoly
import Mathlib.Tactic.Ring

/-! An actual TM2 generating the unary list `0,...,n-1` from unary n.
The current index is a unary stack, copied and restored for every item. The
output is accumulated in reverse and reversed once, with all counters cleared.
-/

namespace ProteinFolding.PackingRange

open Computability Turing TM2

inductive Slot where
  | input | index | cache | buffer | output
  deriving DecidableEq, Fintype

inductive Phase where
  | outer | copy | restore | drain | emit
  deriving DecidableEq, Fintype

def Alphabet : Slot → Type
  | .input | .buffer | .output => Bool
  | .index | .cache => Unit

abbrev State := Bool × Option Bool

def contents (w : List Bool) (i c : ℕ) (b o : List Bool) : ∀ k, List (Alphabet k)
  | .input => w | .index => List.replicate i () | .cache => List.replicate c ()
  | .buffer => b | .output => o

def cfg (p : Phase) (w : List Bool) (i c : ℕ) (b o : List Bool) : Cfg Alphabet Phase State :=
  ⟨some p, (false, none), contents w i c b o⟩

def halted (o : List Bool) : Cfg Alphabet Phase State :=
  ⟨none, (false, none), contents [] 0 0 [] o⟩

def again (p : Phase) : Stmt Alphabet Phase State :=
  .load (fun _ => (false, none)) (.goto (fun _ => p))

def program : Phase → Stmt Alphabet Phase State
  | .outer => .pop .input (fun _ head => (head.isSome, none))
      (.branch Prod.fst (again .copy) (again .drain))
  | .copy => .pop .index (fun _ head => (head.isSome, none))
      (.branch Prod.fst
        (.push .cache (fun _ => ()) (.push .buffer (fun _ => true) (again .copy)))
        (again .restore))
  | .restore => .pop .cache (fun _ head => (head.isSome, none))
      (.branch Prod.fst
        (.push .index (fun _ => ()) (again .restore))
        (.push .index (fun _ => ()) (.push .buffer (fun _ => false) (again .outer))))
  | .drain => .pop .index (fun _ head => (head.isSome, none))
      (.branch Prod.fst (again .drain) (again .emit))
  | .emit => .pop .buffer (fun _ head => (false, head))
      (.branch (fun st => st.2.isSome)
        (.push .output (fun st => st.2.getD false) (again .emit))
        (.load (fun _ => (false, none)) .halt))

theorem update_input (w w' : List Bool) (i c : ℕ) (b o : List Bool) :
    Function.update (contents w i c b o) .input w' = contents w' i c b o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_index (w : List Bool) (i i' c : ℕ) (b o : List Bool) :
    Function.update (contents w i c b o) .index (List.replicate i' ()) = contents w i' c b o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_cache (w : List Bool) (i c c' : ℕ) (b o : List Bool) :
    Function.update (contents w i c b o) .cache (List.replicate c' ()) = contents w i c' b o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_buffer (w : List Bool) (i c : ℕ) (b b' o : List Bool) :
    Function.update (contents w i c b o) .buffer b' = contents w i c b' o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_output (w : List Bool) (i c : ℕ) (b o o' : List Bool) :
    Function.update (contents w i c b o) .output o' = contents w i c b o' := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem outer_cons (a : Bool) (w : List Bool) (i c : ℕ) (b o : List Bool) :
    step program (cfg .outer (a :: w) i c b o) = some (cfg .copy w i c b o) := by
  simp [program, again, cfg, step, stepAux, contents, update_input]

theorem outer_nil (i c : ℕ) (b o : List Bool) :
    step program (cfg .outer [] i c b o) = some (cfg .drain [] i c b o) := by
  simp [program, again, cfg, step, stepAux, contents, update_input]

theorem copy_succ (w : List Bool) (i c : ℕ) (b o : List Bool) :
    step program (cfg .copy w (i + 1) c b o) = some (cfg .copy w i (c + 1) (true :: b) o) := by
  simp [program, again, cfg, step, stepAux, contents, List.replicate_succ]
  change Function.update
    (Function.update (Function.update (contents w (i + 1) c b o) .index (List.replicate i ()))
      .cache (List.replicate (c + 1) ())) .buffer (true :: b) = _
  rw [update_index, update_cache, update_buffer]

theorem copy_zero (w : List Bool) (c : ℕ) (b o : List Bool) :
    step program (cfg .copy w 0 c b o) = some (cfg .restore w 0 c b o) := by
  simp [program, again, cfg, step, stepAux, contents]

theorem restore_succ (w : List Bool) (i c : ℕ) (b o : List Bool) :
    step program (cfg .restore w i (c + 1) b o) = some (cfg .restore w (i + 1) c b o) := by
  simp [program, again, cfg, step, stepAux, contents, List.replicate_succ]
  change Function.update (Function.update (contents w i (c + 1) b o) .cache (List.replicate c ()))
    .index (List.replicate (i + 1) ()) = _
  rw [update_cache, update_index]

theorem restore_zero (w : List Bool) (i : ℕ) (b o : List Bool) :
    step program (cfg .restore w i 0 b o) = some (cfg .outer w (i + 1) 0 (false :: b) o) := by
  simp [program, again, cfg, step, stepAux, contents]
  change Function.update
    (Function.update (Function.update (contents w i 0 b o) .cache (List.replicate 0 ()))
      .index (List.replicate (i + 1) ())) .buffer (false :: b) = _
  rw [update_cache, update_index, update_buffer]

theorem drain_succ (w : List Bool) (i c : ℕ) (b o : List Bool) :
    step program (cfg .drain w (i + 1) c b o) = some (cfg .drain w i c b o) := by
  simp [program, again, cfg, step, stepAux, contents, List.replicate_succ]
  exact update_index w (i + 1) i c b o

theorem drain_zero (w : List Bool) (c : ℕ) (b o : List Bool) :
    step program (cfg .drain w 0 c b o) = some (cfg .emit w 0 c b o) := by
  simp [program, again, cfg, step, stepAux, contents]

theorem emit_cons (a : Bool) (b o : List Bool) :
    step program (cfg .emit [] 0 0 (a :: b) o) = some (cfg .emit [] 0 0 b (a :: o)) := by
  simp [program, again, cfg, step, stepAux, contents]
  change Function.update (Function.update (contents [] 0 0 (a :: b) o) .buffer b) .output (a :: o) = _
  rw [update_buffer, update_output]

theorem emit_nil (o : List Bool) :
    step program (cfg .emit [] 0 0 [] o) = some (halted o) := by
  simp [program, again, cfg, halted, step, stepAux, contents]

def run (k : ℕ) (q : Cfg Alphabet Phase State) : Option (Cfg Alphabet Phase State) :=
  (fun x : Option (Cfg Alphabet Phase State) => x.bind (step program))^[k] (some q)

theorem run_step {q q' : Cfg Alphabet Phase State} (h : step program q = some q') (k : ℕ) :
    run (k + 1) q = run k q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add {q q' : Cfg Alphabet Phase State} {k : ℕ} (h : run k q = some q') (m : ℕ) :
    run (k + m) q = run m q' := by
  rw [Nat.add_comm k m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg Alphabet Phase State) => x.bind (step program))^[k] (some q) = some q' from h]

theorem copy_run (w : List Bool) (i c : ℕ) (b o : List Bool) :
    run (i + 1) (cfg .copy w i c b o) =
      some (cfg .restore w 0 (c + i) (List.replicate i true ++ b) o) := by
  induction i generalizing c b with
  | zero => simpa only [run, Function.iterate_one, Option.bind_some, Nat.add_zero,
      List.replicate_zero, List.nil_append] using copy_zero w c b o
  | succ i ih =>
    rw [run_step (copy_succ w i c b o), ih]
    simp only [Nat.add_left_comm, Nat.add_comm]
    have he : List.replicate i true ++ true :: b = List.replicate (i + 1) true ++ b := by
      rw [List.replicate_succ', List.append_assoc]
      rfl
    rw [he]

theorem restore_run (w : List Bool) (i c : ℕ) (b o : List Bool) :
    run (c + 1) (cfg .restore w i c b o) = some (cfg .outer w (i + c + 1) 0 (false :: b) o) := by
  induction c generalizing i with
  | zero => simpa only [run, Function.iterate_one, Option.bind_some, Nat.add_zero] using restore_zero w i b o
  | succ c ih => rw [run_step (restore_succ w i c b o), ih]; congr 2; omega

theorem iteration (a : Bool) (w : List Bool) (i : ℕ) (b o : List Bool) :
    run (2 * i + 3) (cfg .outer (a :: w) i 0 b o) =
      some (cfg .outer w (i + 1) 0 (false :: (List.replicate i true ++ b)) o) := by
  rw [show 2 * i + 3 = ((i + 1) + (i + 1)) + 1 by omega,
    run_step (outer_cons a w i 0 b o), run_add (copy_run w i 0 b o)]
  simpa only [Nat.zero_add] using restore_run w 0 i (List.replicate i true ++ b) o

def codeFrom (i n : ℕ) : List Bool := Packing.itemEncoding.encode (List.range' i n)

theorem unary_replicate (n : ℕ) : unaryEncodeNat n = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [unaryEncodeNat, List.replicate_succ, ih]

theorem codeFrom_zero (i : ℕ) : codeFrom i 0 = [] := rfl

theorem codeFrom_succ (i n : ℕ) :
    codeFrom i (n + 1) = unaryEncodeNat i ++ false :: codeFrom (i + 1) n := by
  simp [codeFrom, List.range'_succ, Packing.itemEncoding, SAT.encTerminated, List.append_assoc]

theorem core_run (n i : ℕ) (b : List Bool) :
    run (n * (2 * i + n + 2)) (cfg .outer (unaryEncodeNat n) i 0 b []) =
      some (cfg .outer [] (i + n) 0 ((codeFrom i n).reverse ++ b) []) := by
  induction n generalizing i b with
  | zero => simp [run, unaryEncodeNat, codeFrom_zero]
  | succ n ih =>
    rw [show (n + 1) * (2 * i + (n + 1) + 2) =
      (2 * i + 3) + n * (2 * (i + 1) + n + 2) by ring]
    rw [unaryEncodeNat, run_add (iteration true (unaryEncodeNat n) i b [])]
    rw [ih]
    have hi : i + 1 + n = i + (n + 1) := by omega
    simp [hi, codeFrom_succ, List.reverse_append, unary_replicate, List.append_assoc]

theorem drain_run (i : ℕ) (b : List Bool) :
    run (i + 1) (cfg .drain [] i 0 b []) = some (cfg .emit [] 0 0 b []) := by
  induction i with
  | zero => simpa only [run, Function.iterate_one, Option.bind_some] using drain_zero [] 0 b []
  | succ i ih => rw [run_step (drain_succ [] i 0 b []), ih]

theorem emit_run (b o : List Bool) :
    run (b.length + 1) (cfg .emit [] 0 0 b o) = some (halted (b.reverse ++ o)) := by
  induction b generalizing o with
  | nil => simpa only [run, Function.iterate_one, Option.bind_some, List.reverse_nil,
      List.nil_append] using emit_nil o
  | cons a b ih =>
    rw [List.length_cons, run_step (emit_cons a b o), ih]
    simp [List.reverse_cons, List.append_assoc]

theorem program_run (n : ℕ) :
    run (n * (n + 2) + n + (codeFrom 0 n).length + 3)
      (cfg .outer (unaryEncodeNat n) 0 0 [] []) = some (halted (codeFrom 0 n)) := by
  have hc := core_run n 0 []
  simp only [Nat.mul_zero, Nat.zero_add, List.append_nil] at hc
  rw [show n * (n + 2) + n + (codeFrom 0 n).length + 3 =
      n * (n + 2) + ((n + (codeFrom 0 n).length + 2) + 1) by omega,
    run_add hc, run_step (outer_nil n 0 (codeFrom 0 n).reverse [])]
  rw [show n + (codeFrom 0 n).length + 2 =
      (n + 1) + ((codeFrom 0 n).reverse.length + 1) by simp; omega,
    run_add (drain_run n (codeFrom 0 n).reverse), emit_run]
  simp only [List.reverse_reverse, List.append_nil]

theorem codeFrom_length_bound (i n : ℕ) : (codeFrom i n).length ≤ n * (i + n + 1) := by
  induction n generalizing i with
  | zero => simp [codeFrom_zero]
  | succ n ih =>
    have ht := ih (i + 1)
    rw [codeFrom_succ, List.length_append, Packing.unary_length, List.length_cons]
    nlinarith

def machine : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Phase
  main := .outer
  σ := State
  initialState := (false, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

def machine_outputs (n : ℕ) : TM2OutputsInTime machine (unaryEncodeNat n)
    (some (Packing.itemEncoding.encode (List.range n))) (3 * n ^ 2 + 6 * n + 5) := by
  have hi : initList machine (unaryEncodeNat n) = cfg .outer (unaryEncodeNat n) 0 0 [] [] := by
    apply congrArg (fun A => (⟨some .outer, (false, none), A⟩ : Cfg Alphabet Phase State))
    funext k; cases k <;> rfl
  have ho : haltList machine (codeFrom 0 n) = halted (codeFrom 0 n) := by
    apply congrArg (fun A => (⟨none, (false, none), A⟩ : Cfg Alphabet Phase State))
    funext k; cases k <;> rfl
  have he : codeFrom 0 n = Packing.itemEncoding.encode (List.range n) := by
    simp [codeFrom, List.range'_eq_map_range]
  rw [← he]
  refine ⟨⟨n * (n + 2) + n + (codeFrom 0 n).length + 3, ?_⟩, ?_⟩
  · change run _ (initList machine _) = some (haltList machine _)
    rw [hi, ho]
    exact program_run n
  · have hl := codeFrom_length_bound 0 n
    nlinarith

/-- Actual polynomial-time generation of a unary-encoded finite index range. -/
noncomputable def rangeComputable : TM2ComputableInPolyTime unaryFinEncodingNat Packing.itemEncoding List.range where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 6 * Polynomial.X + Polynomial.C 5
  outputsFun n := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime machine (List.map id (unaryEncodeNat n))
      (some (List.map id (Packing.itemEncoding.encode (List.range n))))
      (3 * (unaryEncodeNat n).length ^ 2 + 6 * (unaryEncodeNat n).length + 5)
    simpa only [List.map_id, Packing.unary_length] using machine_outputs n

end ProteinFolding.PackingRange
