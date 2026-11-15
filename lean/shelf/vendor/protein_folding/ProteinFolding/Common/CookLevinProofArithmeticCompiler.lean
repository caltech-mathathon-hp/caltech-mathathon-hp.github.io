import ProteinFolding.Common.CookLevinProofCNFCompiler
import ProteinFolding.Common.TM2WordRepeat

/-! Actual polynomial TM2 arithmetic for tableau loop bounds and indices.
Unary addition and multiplication use checked word concatenation/repetition;
every fixed natural-coefficient polynomial is then compiled compositionally.
The source length is read by an actual finite-alphabet scan.
-/

namespace ProteinFolding.SAT.CookLevinArithmeticCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap

theorem unary_append (a b : ℕ) : unaryEncodeNat (a + b) = unaryEncodeNat a ++ unaryEncodeNat b := by
  induction a with
  | zero => simp [unaryEncodeNat]
  | succ a ih => simpa only [Nat.succ_add, unaryEncodeNat, List.cons_append] using congrArg (true :: ·) ih

theorem wordRepeat_unary (a b : ℕ) : TM2WordRepeat.wordRepeat (unaryEncodeNat a) b = unaryEncodeNat (a * b) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [TM2WordRepeat.wordRepeat, ih, ← unary_append, Nat.mul_succ]

noncomputable def additionComputable :
    TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)
      unaryFinEncodingNat (fun p : ℕ × ℕ => p.1 + p.2) := by
  let hm := TM2PairProjections.concatComputable Bool
  exact
    { toTM2ComputableAux := hm.toTM2ComputableAux
      time := hm.time
      outputsFun p := by
        have hp := hm.outputsFun (unaryEncodeNat p.1, unaryEncodeNat p.2)
        simpa only [unaryFinEncodingNat, wordEncoding, unary_append] using hp }

noncomputable def multiplicationComputable :
    TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)
      unaryFinEncodingNat (fun p : ℕ × ℕ => p.1 * p.2) := by
  let hm := TM2WordRepeat.computable Bool
  exact
    { toTM2ComputableAux := hm.toTM2ComputableAux
      time := hm.time
      outputsFun p := by
        have hp := hm.outputsFun (unaryEncodeNat p.1, p.2)
        simpa only [wordRepeat_unary] using hp }

theorem polynomialMachine_nonempty (p : Polynomial ℕ) :
    Nonempty (TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat (fun n => p.eval n)) := by
  refine Polynomial.induction_on p (fun a => ?_) (fun p q hp hq => ?_) (fun n a hp => ?_)
  · simpa only [Polynomial.eval_C] using
      (Nonempty.intro (TM2Constants.constantComputable unaryFinEncodingNat unaryFinEncodingNat a))
  · obtain ⟨hp⟩ := hp
    obtain ⟨hq⟩ := hq
    have he : (fun n => (p + q).eval n) = (fun n => p.eval n + q.eval n) := by
      funext n
      exact Polynomial.eval_add
    rw [he]
    exact ⟨compose (pairComputable hp hq) additionComputable⟩
  · obtain ⟨hp⟩ := hp
    have he : (fun x => (Polynomial.C a * Polynomial.X ^ (n + 1)).eval x) =
        (fun x => (Polynomial.C a * Polynomial.X ^ n).eval x * x) := by
      funext x
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, pow_succ]
      exact (Nat.mul_assoc _ _ _).symm
    rw [he]
    exact ⟨compose (pairComputable hp (idComputableInPolyTime unaryFinEncodingNat)) multiplicationComputable⟩

noncomputable def polynomialComputable (p : Polynomial ℕ) :
    TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat (fun n => p.eval n) :=
  Classical.choice (polynomialMachine_nonempty p)

theorem map_true_unary {D : Type*} (xs : List D) : xs.map (fun _ => true) = unaryEncodeNat xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.length_cons, List.map_cons, unaryEncodeNat] using congrArg (true :: ·) ih

noncomputable def lengthComputable {D : Type} (ed : FinEncoding D) :
    TM2ComputableInPolyTime ed unaryFinEncodingNat (fun d => (ed.encode d).length) := by
  letI := ed.ΓFin
  let hm := TM2WordMap.mapComputable (fun _ : ed.Γ => true)
  exact
    { toTM2ComputableAux := hm.toTM2ComputableAux
      time := hm.time
      outputsFun d := by simpa only [map_true_unary] using hm.outputsFun (ed.encode d) }

/-- Compute any fixed polynomial of the actual input encoding length by an
actual finite TM2 with a proved polynomial bound. -/
noncomputable def encodedPolynomialComputable {D : Type} (ed : FinEncoding D) (p : Polynomial ℕ) :
    TM2ComputableInPolyTime ed unaryFinEncodingNat (fun d => p.eval (ed.encode d).length) :=
  compose (lengthComputable ed) (polynomialComputable p)

end ProteinFolding.SAT.CookLevinArithmeticCompiler
