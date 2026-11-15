import ProteinFolding.Common.TM2ArithmeticRuns
import Mathlib.Tactic.Linarith

/-! The finite comparison loop terminates in polynomially many steps,
inducting on the unary counter rather than on the binary value. -/

namespace ProteinFolding.TM2Arithmetic.Comparator

open Computability Turing TM2

def doneCfg (answer : Bool) : Cfg Alphabet Phase Reg :=
  ⟨none, initial, contents [] [] [] [] [answer]⟩

theorem comparison_run (u : List Bool) (w : List Bool) :
    ∃ steps, steps ≤ (u.length + 1) * (2 * w.length + 7) + u.length + 5 ∧
      tick^[steps] (some (cfg .dec (regs true false false) [] [] w u [])) =
        some (doneCfg (decide (bitValue w ≤ u.length))) := by
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
      have hn : ¬ bitValue w ≤ 0 := by omega
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
      · have hiff : bitValue (decrement true w).1 ≤ u.length ↔
            bitValue w ≤ (a :: u).length := by simp only [List.length_cons]; omega
        simpa only [hiff] using ht

end ProteinFolding.TM2Arithmetic.Comparator
