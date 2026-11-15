import ProteinFolding.Common.CookLevinProofWidthThree
import ProteinFolding.Common.CookLevinProofBoundaryCompiler
import ProteinFolding.Common.CookLevinProofBoundedVariableCompiler
import ProteinFolding.Common.CookLevinProofWidthThreeCompiler

namespace ProteinFolding.SAT.CookLevinWidthThreeCompilerCorrectness

open CookLevinWidthThree CookLevinCircuit CookLevinBoundaryCompiler
open CookLevinSourceQueryCompiler CookLevinBoundedVariableCompiler CookLevinWidthThreeCompiler

def triples (base k Q : ℕ) (c : Clause) : CNF :=
  (List.range Q).flatMap (fun j => if h : j < c.length then
    [[negative (base + (k + j)), c[j], positive (base + (k + j + 1))]] else [])

theorem triples_nil (base k Q : ℕ) : triples base k Q [] = [] := by
  simp [triples]

theorem chain_eq_triples (base k Q : ℕ) (c : Clause) (hQ : c.length ≤ Q) :
    chain base k c = triples base k Q c ++ [[negative (base + (k + c.length))]] := by
  induction c generalizing k Q with
  | nil => simp only [chain, triples_nil, List.length_nil, Nat.add_zero, List.nil_append]
  | cons l c ih =>
    cases Q with
    | zero => simp only [List.length_cons] at hQ; omega
    | succ Q =>
      have hc : c.length ≤ Q := by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hQ
      have ht : triples base k (Q + 1) (l :: c) =
          [negative (base + k), l, positive (base + (k + 1))] :: triples base (k + 1) Q c := by
        simp only [triples, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
          List.length_cons, Nat.zero_lt_succ, ↓reduceDIte, List.getElem_cons_zero,
          Nat.add_zero, List.singleton_append]
        congr 1
        apply List.flatMap_congr
        intro j _
        by_cases hj : j < c.length
        · simp [Nat.succ_lt_succ_iff, hj, List.getElem_cons_succ, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm]
        · simp [Nat.succ_lt_succ_iff, hj]
      rw [ht, chain, ih (k + 1) Q hc]
      simp only [List.cons_append, List.length_cons]
      congr 2
      congr 2
      congr 1
      omega

theorem clauseFormula_eq (Q V : ℕ) (φ : CNF) (i : ℕ) (hi : i < φ.length)
    (hQ : φ[i].length ≤ Q) (hV : ∀ l ∈ φ[i], l.var < V) :
    clauseFormula Q ((φ, V), i) = gadget (flag Q V i 0) φ[i] := by
  have hlen : clauseLength ((φ, V), i) = φ[i].length := clauseLengthAt_correct φ i hi
  have hb : auxBase Q ((φ, V), i) = flag Q V i 0 := by simp only [auxBase, flag, Nat.add_zero]
  have ht : (List.finRange Q).flatMap (fun j => guardedTriple Q j.val ((φ, V), i)) =
      triples (flag Q V i 0) 0 Q φ[i] := by
    rw [triples, range_flatMap_finRange]
    apply List.flatMap_congr
    intro j _
    simp only [guardedTriple, hlen]
    by_cases hj : j.val < φ[i].length
    · simp only [hj, ↓reduceIte, ↓reduceDIte]
      have hv := boundedVariable_correct φ i j.val V hi hj (hV _ (List.getElem_mem hj))
      have hp := positiveAt_correct φ i j.val hi hj
      simp only [triple, literalVariable, polarity, sourceClause, hv, hp, hb, Nat.zero_add]
    · simp only [hj, ↓reduceIte, ↓reduceDIte]
  rw [clauseFormula, ht, hlen, Nat.min_eq_left hQ, hb, gadget,
    chain_eq_triples (flag Q V i 0) 0 Q φ[i] hQ]
  simp only [Nat.zero_add, List.cons_append, List.nil_append]

theorem formula_eq_transform (Q V : ℕ) (φ : CNF)
    (hQ : ∀ c ∈ φ, c.length ≤ Q) (hV : ∀ c ∈ φ, ∀ l ∈ c, l.var < V) :
    formula Q (φ, V) = transform Q V φ := by
  simp only [formula, transform, List.ofFn_eq_map, range_flatMap_finRange]
  exact List.flatMap_congr (fun i _ => clauseFormula_eq Q V φ i.val i.isLt
    (hQ _ (List.getElem_mem i.isLt)) (hV _ (List.getElem_mem i.isLt)))

theorem formula_equisatisfiable (Q : ℕ) (φ : CNF) (V : ℕ)
    (hQ : ∀ c ∈ φ, c.length ≤ Q) (hV : ∀ c ∈ φ, ∀ l ∈ c, l.var < V) :
    Satisfiable (formula Q (φ, V)) ↔ Satisfiable φ := by
  rw [formula_eq_transform Q V φ hQ hV]
  exact transform_equisatisfiable Q V φ hQ hV

end ProteinFolding.SAT.CookLevinWidthThreeCompilerCorrectness
