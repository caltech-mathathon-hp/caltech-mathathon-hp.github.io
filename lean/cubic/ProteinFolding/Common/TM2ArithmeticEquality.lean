import ProteinFolding.Common.TM2ArithmeticSignedUnary

/-! A finite TM2 comparing a binary natural with a unary natural for equality.
The comparator's decrement loop is reused. During cleanup, any unconsumed unary
symbol changes the answer to false, distinguishing equality from inequality. -/

namespace ProteinFolding.TM2Arithmetic.Equality

open Computability Turing TM2 Polynomial Comparator

def program : Phase → Stmt Alphabet Phase Reg
  | .clearUnary => .pop .unary (fun st x => {st with bit := x})
      (.branch (fun st => st.bit.isSome)
        (.load (fun st => {st with bit := none, result := false}) (.goto (fun _ => .clearUnary)))
        (.goto (fun _ => .finish)))
  | label => Comparator.program label

abbrev tick : Option (Cfg Alphabet Phase Reg) → Option (Cfg Alphabet Phase Reg) :=
  fun x => x.bind (step program)

theorem dec_step_cons (borrow neg res a : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .dec (regs borrow neg res) i b (a :: w) u o)) =
      some (cfg .dec (regs (borrow && !a) neg res) i
        ((if borrow then !a else a) :: b) w u o) := by
  simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_bits, update_buffer]

def afterDec (borrow neg res : Bool) (i : List Sym) (b u o : List Bool) :
    Cfg Alphabet Phase Reg :=
  if borrow then cfg .clearBits (regs true neg true) i b [] u o
  else cfg .consume (regs false neg res) i b [] u o

theorem dec_step_nil (borrow neg res : Bool) (i : List Sym) (b u o : List Bool) :
    tick (some (cfg .dec (regs borrow neg res) i b [] u o)) =
      some (afterDec borrow neg res i b u o) := by
  cases borrow <;> simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents,
    update_bits, afterDec]

theorem dec_run (w : List Bool) (borrow neg res : Bool) (i : List Sym) (b u o : List Bool) :
    tick^[w.length + 1] (some (cfg .dec (regs borrow neg res) i b w u o)) =
      some (afterDec (decrement borrow w).2 neg res i
        ((decrement borrow w).1.reverse ++ b) u o) := by
  induction w generalizing borrow b with
  | nil => simpa [decrement] using dec_step_nil borrow neg res i b u o
  | cons a w ih =>
    rw [List.length_cons, Nat.add_right_comm w.length 1 1, Function.iterate_succ_apply,
      dec_step_cons]
    simpa [decrement, List.reverse_cons, List.append_assoc] using
      ih (borrow && !a) ((if borrow then !a else a) :: b)

theorem restore_step_cons (borrow neg res a : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .restore (regs borrow neg res) i (a :: b) w u o)) =
      some (cfg .restore (regs borrow neg res) i b (a :: w) u o) := by
  simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_bits, update_buffer]

theorem restore_step_nil (borrow neg res : Bool) (i : List Sym) (w u o : List Bool) :
    tick (some (cfg .restore (regs borrow neg res) i [] w u o)) =
      some (cfg .dec (regs true neg res) i [] w u o) := by
  simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_buffer]

theorem restore_run (b : List Bool) (borrow neg res : Bool) (i : List Sym) (w u o : List Bool) :
    tick^[b.length + 1] (some (cfg .restore (regs borrow neg res) i b w u o)) =
      some (cfg .dec (regs true neg res) i [] (b.reverse ++ w) u o) := by
  induction b generalizing w with
  | nil => simpa using restore_step_nil borrow neg res i w u o
  | cons a b ih =>
    rw [List.length_cons, Nat.add_right_comm b.length 1 1, Function.iterate_succ_apply,
      restore_step_cons]
    simpa [List.reverse_cons, List.append_assoc] using ih (a :: w)

theorem consume_step_cons (borrow neg res a : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .consume (regs borrow neg res) i b w (a :: u) o)) =
      some (cfg .restore (regs borrow neg res) i b w u o) := by
  simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_unary]

theorem consume_step_nil (borrow neg res : Bool) (i : List Sym) (b w o : List Bool) :
    tick (some (cfg .consume (regs borrow neg res) i b w [] o)) =
      some (cfg .clearBits (regs borrow neg false) i b w [] o) := by
  simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_unary]

theorem clearBits_run (w : List Bool) (borrow neg res : Bool) (i : List Sym) (b u o : List Bool) :
    tick^[w.length + 1] (some (cfg .clearBits (regs borrow neg res) i b w u o)) =
      some (cfg .clearBuffer (regs borrow neg res) i b [] u o) := by
  induction w with
  | nil => simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_bits]
  | cons a w ih =>
    rw [List.length_cons, Nat.add_right_comm w.length 1 1, Function.iterate_succ_apply]
    simpa only [tick, Option.bind_some, cfg, regs, program, Comparator.program, step, stepAux, contents, update_bits, List.head?_cons,
      List.tail_cons, Option.isSome_some, cond_true] using ih

theorem clearBuffer_run (b : List Bool) (borrow neg res : Bool) (i : List Sym) (w u o : List Bool) :
    tick^[b.length + 1] (some (cfg .clearBuffer (regs borrow neg res) i b w u o)) =
      some (cfg .clearUnary (regs borrow neg res) i [] w u o) := by
  induction b with
  | nil => simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_buffer]
  | cons a b ih =>
    rw [List.length_cons, Nat.add_right_comm b.length 1 1, Function.iterate_succ_apply]
    simpa only [tick, Option.bind_some, cfg, regs, program, Comparator.program, step, stepAux, contents, update_buffer, List.head?_cons,
      List.tail_cons, Option.isSome_some, cond_true] using ih

theorem clearUnary_run (u : List Bool) (borrow neg res : Bool) (i : List Sym) (b w o : List Bool) :
    tick^[u.length + 1] (some (cfg .clearUnary (regs borrow neg res) i b w u o)) =
      some (cfg .finish (regs borrow neg (if u.isEmpty then res else false)) i b w [] o) := by
  induction u generalizing res with
  | nil => simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_unary]
  | cons a u ih =>
    rw [List.length_cons, Nat.add_right_comm u.length 1 1, Function.iterate_succ_apply]
    simpa [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_unary] using ih false

theorem finish_step (borrow neg res : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .finish (regs borrow neg res) i b w u o)) =
      some (⟨none, initial, contents i b w u (res :: o)⟩ : Cfg Alphabet Phase Reg) := by
  simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_output]

theorem run_join {a b c : Option (Cfg Alphabet Phase Reg)} (m n : ℕ)
    (hm : tick^[m] a = b) (hn : tick^[n] b = c) : tick^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, hm, hn]

theorem cleanup_run (w b u : List Bool) (borrow neg res : Bool) (o : List Bool) :
    tick^[w.length + b.length + u.length + 4]
      (some (cfg .clearBits (regs borrow neg res) [] b w u o)) =
        some (⟨none, initial, contents [] [] [] [] ((if u.isEmpty then res else false) :: o)⟩ : Cfg Alphabet Phase Reg) := by
  have h1 := clearBits_run w borrow neg res [] b u o
  have h2 := clearBuffer_run b borrow neg res [] [] u o
  have h3 := clearUnary_run u borrow neg res [] [] [] o
  have h4 : tick^[1] (some (cfg .finish (regs borrow neg (if u.isEmpty then res else false)) [] [] [] [] o)) =
      some (⟨none, initial, contents [] [] [] [] ((if u.isEmpty then res else false) :: o)⟩ : Cfg Alphabet Phase Reg) :=
    finish_step borrow neg (if u.isEmpty then res else false) [] [] [] [] o
  have h := run_join _ _ (run_join _ _ (run_join _ _ h1 h2) h3) h4
  have hexp : w.length + 1 + (b.length + 1) + (u.length + 1) + 1 =
      w.length + b.length + u.length + 4 := by omega
  simpa only [hexp] using h


theorem comparison_run (u : List Bool) (w : List Bool) :
    ∃ steps, steps ≤ (u.length + 1) * (2 * w.length + 7) + u.length + 5 ∧
      tick^[steps] (some (cfg .dec (regs true false false) [] [] w u [])) =
        some (doneCfg (decide (bitValue w = u.length))) := by
  induction u generalizing w with
  | nil =>
    have hdec := dec_run w true false false [] [] [] []
    cases hc : (decrement true w).2 with
    | true =>
      have hz := (decrement_underflow_iff w).mp hc
      have hd : tick^[w.length + 1]
          (some (cfg .dec (regs true false false) [] [] w [] [])) =
          some (cfg .clearBits (regs true false true) [] (decrement true w).1.reverse [] [] []) := by
        simpa [afterDec, hc] using hdec
      have hcl := cleanup_run [] (decrement true w).1.reverse [] true false true []
      have ht := run_join _ _ hd hcl
      refine ⟨(w.length + 1) + ((decrement true w).1.reverse.length + 4), ?_, ?_⟩
      · simp only [List.length_nil, List.length_reverse, decrement_length]
        omega
      · simpa [doneCfg, hz] using ht
    | false =>
      have hv := decrement_success w hc
      have hn : ¬ bitValue w = 0 := by omega
      have hd : tick^[w.length + 1]
          (some (cfg .dec (regs true false false) [] [] w [] [])) =
          some (cfg .consume (regs false false false) [] (decrement true w).1.reverse [] [] []) := by
        simpa [afterDec, hc] using hdec
      have hconsume := consume_step_nil false false false [] (decrement true w).1.reverse [] []
      have hcl := cleanup_run [] (decrement true w).1.reverse [] false false false []
      have ht := run_join _ _ (run_join _ 1 hd hconsume) hcl
      refine ⟨(w.length + 1) + 1 + ((decrement true w).1.reverse.length + 4), ?_, ?_⟩
      · simp only [List.length_nil, List.length_reverse, decrement_length]
        omega
      · simpa [doneCfg, hn] using ht
  | cons a u ih =>
    have hdec := dec_run w true false false [] [] (a :: u) []
    cases hc : (decrement true w).2 with
    | true =>
      have hz := (decrement_underflow_iff w).mp hc
      have hd : tick^[w.length + 1]
          (some (cfg .dec (regs true false false) [] [] w (a :: u) [])) =
          some (cfg .clearBits (regs true false true) [] (decrement true w).1.reverse [] (a :: u) []) := by
        simpa [afterDec, hc] using hdec
      have hcl := cleanup_run [] (decrement true w).1.reverse (a :: u) true false true []
      have ht := run_join _ _ hd hcl
      refine ⟨(w.length + 1) + ((decrement true w).1.reverse.length + (a :: u).length + 4), ?_, ?_⟩
      · simp only [List.length_cons, List.length_reverse, decrement_length]
        nlinarith [Nat.zero_le (u.length * w.length)]
      · simpa [doneCfg, hz] using ht
    | false =>
      have hv := decrement_success w hc
      have hd : tick^[w.length + 1]
          (some (cfg .dec (regs true false false) [] [] w (a :: u) [])) =
          some (cfg .consume (regs false false false) [] (decrement true w).1.reverse [] (a :: u) []) := by
        simpa [afterDec, hc] using hdec
      have hconsume := consume_step_cons false false false a [] (decrement true w).1.reverse [] u []
      have hrestore := restore_run (decrement true w).1.reverse false false false [] [] u []
      simp only [List.reverse_reverse, List.append_nil] at hrestore
      obtain ⟨t, hbound, hrun⟩ := ih (decrement true w).1
      have ht := run_join _ _ (run_join _ _ (run_join _ 1 hd hconsume) hrestore) hrun
      refine ⟨(w.length + 1) + 1 + ((decrement true w).1.reverse.length + 1) + t, ?_, ?_⟩
      · simp only [List.length_cons, List.length_reverse, decrement_length] at hbound ⊢
        nlinarith
      · have hiff : bitValue (decrement true w).1 = u.length ↔
            bitValue w = (a :: u).length := by simp only [List.length_cons]; omega
        simpa only [hiff] using ht



def inputWord (w : List Bool) (c : ℕ) : List Sym :=
  w.map PairSymbol.left ++ .sep :: (unaryEncodeNat c).map PairSymbol.right

theorem inputWord_length (w : List Bool) (c : ℕ) :
    (inputWord w c).length = w.length + c + 1 := by
  simp [inputWord, unaryEncodeNat_length]; omega

theorem scan_left_step (borrow neg res a : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .scan (regs borrow neg res) (.left a :: i) b w u o)) =
      some (cfg .scan (regs borrow neg res) i (a :: b) w u o) := by
  simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_input, update_buffer, leftBit]

theorem scan_right_step (borrow neg res a : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .scan (regs borrow neg res) (.right a :: i) b w u o)) =
      some (cfg .scan (regs borrow neg res) i b w (true :: u) o) := by
  simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_input, update_unary,
    leftBit, rightToken]

theorem scan_sep_step (borrow neg res : Bool) (i : List Sym) (b w u o : List Bool) :
    tick (some (cfg .scan (regs borrow neg res) (.sep :: i) b w u o)) =
      some (cfg .scan (regs borrow neg res) i b w u o) := by
  simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_input, leftBit, rightToken]

def afterScan (negative : Bool) (b u : List Bool) : Cfg Alphabet Phase Reg :=
  if negative then cfg .clearBits (regs true true true) [] b [] u []
  else cfg .restore (regs true false false) [] b [] u []

theorem scan_nil_step (negative : Bool) (b u : List Bool) :
    tick (some (cfg .scan (regs true negative false) [] b [] u [])) =
      some (afterScan negative b u) := by
  cases negative <;>
    simp [tick, cfg, regs, program, Comparator.program, step, stepAux, contents, update_input, afterScan]

theorem scan_left_run (bs : List Bool) (borrow neg res : Bool) (i : List Sym)
    (b w u o : List Bool) :
    tick^[bs.length] (some (cfg .scan (regs borrow neg res)
      (bs.map PairSymbol.left ++ i) b w u o)) =
        some (cfg .scan (regs borrow neg res) i (bs.reverse ++ b) w u o) := by
  induction bs generalizing b with
  | nil => rfl
  | cons a bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.map_cons, List.cons_append, scan_left_step]
    simpa [List.reverse_cons, List.append_assoc] using ih (a :: b)

theorem scan_unary_run (c : ℕ) (borrow neg res : Bool) (i : List Sym)
    (b w u o : List Bool) :
    tick^[c] (some (cfg .scan (regs borrow neg res)
      ((unaryEncodeNat c).map PairSymbol.right ++ i) b w u o)) =
        some (cfg .scan (regs borrow neg res) i b w (List.replicate c true ++ u) o) := by
  induction c generalizing u with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply]
    simp only [unaryEncodeNat, List.map_cons, List.cons_append, scan_right_step]
    have hrep (c : ℕ) : List.replicate c true ++ true :: u =
        true :: (List.replicate c true ++ u) := by
      induction c with
      | zero => rfl
      | succ c hc =>
        have he := congrArg (List.cons true) hc
        simpa only [List.replicate_succ, List.cons_append] using he
    simpa only [List.replicate_succ, List.cons_append, hrep] using ih (true :: u)

theorem run_one {a b : Option (Cfg Alphabet Phase Reg)} (h : tick a = b) : tick^[1] a = b := by
  simpa only [Function.iterate_one] using h


theorem parse_run (w : List Bool) (c : ℕ) :
    tick^[w.length + c + 2]
      (some (cfg .scan initial (inputWord w c) [] [] [] [])) =
        some (afterScan false w.reverse (List.replicate c true)) := by
  have h1 := scan_left_run w true false false
    (.sep :: (unaryEncodeNat c).map PairSymbol.right) [] [] [] []
  simp only [List.append_nil] at h1
  have h2 := scan_sep_step true false false
    ((unaryEncodeNat c).map PairSymbol.right) w.reverse [] [] []
  have h3 := scan_unary_run c true false false [] w.reverse [] [] []
  simp only [List.append_nil] at h3
  have h4 := scan_nil_step false w.reverse (List.replicate c true)
  have ht := run_join _ 1 (run_join _ _ (run_join _ 1 h1 (run_one h2)) h3) (run_one h4)
  have he : w.length + 1 + c + 1 = w.length + c + 2 := by omega
  simpa only [he, inputWord, initial] using ht

theorem program_run (w : List Bool) (c : ℕ) :
    ∃ steps, steps ≤ 10 * (w.length + c + 2) ^ 2 + 10 ∧
      tick^[steps] (some (cfg .scan initial (inputWord w c) [] [] [] [])) =
        some (doneCfg (decide (bitValue w = c))) := by
  have hp := parse_run w c
  have hrestore := restore_run w.reverse true false false [] [] (List.replicate c true) []
  simp only [List.reverse_reverse, List.append_nil] at hrestore
  obtain ⟨t, hbound, hrun⟩ := comparison_run (List.replicate c true) w
  simp only [List.length_replicate] at hbound hrun
  have ht := run_join _ _ (run_join _ _ hp hrestore) hrun
  refine ⟨(w.length + c + 2) + (w.reverse.length + 1) + t, ?_, ?_⟩
  · simp only [List.length_reverse]
    nlinarith [Nat.zero_le (w.length * c), Nat.zero_le (w.length ^ 2), Nat.zero_le (c ^ 2)]
  · simpa [afterScan] using ht

def machine : FinTM2 := { Comparator.machine with main := .scan, m := program }

def natUnaryEncoding : FinEncoding (ℕ × ℕ) :=
  pairEncoding finEncodingNatBool unaryFinEncodingNat

def answer (x : ℕ × ℕ) : Bool := decide (x.1 = x.2)

noncomputable def equalityTime : Polynomial ℕ := C 10 * (X + C 1) ^ 2 + C 10

theorem machine_init (i : List Sym) : initList machine i = cfg .scan initial i [] [] [] [] := by
  apply congrArg (fun S : ∀ k, List (Alphabet k) =>
    (⟨some Phase.scan, initial, S⟩ : Cfg Alphabet Phase Reg))
  funext k
  cases k <;> rfl

theorem machine_halt (b : Bool) : haltList machine [b] = doneCfg b := by
  apply congrArg (fun S : ∀ k, List (Alphabet k) =>
    (⟨none, initial, S⟩ : Cfg Alphabet Phase Reg))
  funext k
  cases k <;> rfl

theorem machine_outputs_raw (w : List Bool) (c : ℕ) :
    Nonempty (TM2OutputsInTime machine (inputWord w c)
      (some [decide (bitValue w = c)])
      (10 * ((inputWord w c).length + 1) ^ 2 + 10)) := by
  obtain ⟨t, ht, hrun⟩ := program_run w c
  refine ⟨{ steps := t, evals_in_steps := ?_, steps_le_m := ?_ }⟩
  · change tick^[t] (some (initList machine (inputWord w c))) =
      some (haltList machine [decide (bitValue w = c)])
    rw [machine_init, machine_halt]
    exact hrun
  · simpa only [inputWord_length, Nat.add_assoc] using ht

theorem machine_outputs (n c : ℕ) :
    Nonempty (TM2OutputsInTime machine (natUnaryEncoding.encode (n, c))
      (some [answer (n, c)]) (equalityTime.eval (natUnaryEncoding.encode (n, c)).length)) := by
  have henc : natUnaryEncoding.encode (n, c) = inputWord (encodeNat n) c := rfl
  simpa only [henc, bitValue_encodeNat, answer, equalityTime,
    eval_add, eval_mul, eval_C, eval_pow, eval_X] using machine_outputs_raw (encodeNat n) c

noncomputable def natUnaryComputable :
    TM2ComputableInPolyTime natUnaryEncoding finEncodingBoolBool answer where
  tm := machine
  inputAlphabet := Equiv.refl Sym
  outputAlphabet := Equiv.refl Bool
  time := equalityTime
  outputsFun x := by
    rcases x with ⟨n, c⟩
    have h := Classical.choice (machine_outputs n c)
    simpa [Equiv.refl, finEncodingBoolBool, encodeBool] using h

theorem natUnary_polyTimeDecidable :
    PolyTimeDecidable natUnaryEncoding (fun x => x.1 = x.2) :=
  ⟨answer, ⟨natUnaryComputable⟩, fun x => by simp [answer]⟩

end ProteinFolding.TM2Arithmetic.Equality
