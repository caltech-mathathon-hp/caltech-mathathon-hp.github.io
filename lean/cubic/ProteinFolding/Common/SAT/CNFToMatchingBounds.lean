import ProteinFolding.Common.SAT.CNFToMatching

/-! Polynomial magnitude and unary output-length bounds for the explicit
CNF-to-matching transformation. These bounds are on actual frozen CNF input
encoding lengths, and do not constitute an unproved TM2 runtime assertion. -/

namespace ProteinFolding.ThreeDimensionalMatching

open Computability SAT

theorem indexedOccurrences_length (φ : CNF) :
    (indexedOccurrences φ).length = φ.flatten.length := by
  simp only [indexedOccurrences, List.length_flatten, List.map_ofFn, Function.comp_def,
    List.length_map]
  have he : (List.ofFn fun j : Fin φ.length => (φ.get j).length) = φ.map List.length := by
    calc
      _ = (List.ofFn φ.get).map List.length := List.ofFn_comp' φ.get List.length
      _ = _ := by rw [List.ofFn_get]
  rw [he]

theorem indexedOccurrences_length_le_input (φ : CNF) :
    (indexedOccurrences φ).length ≤ (cnfEncoding.encode φ).length := by
  rw [indexedOccurrences_length]
  have h := ThreeCNF.formula_occurrences_length_le_encoding φ
  omega

theorem unary_length (n : ℕ) : (unaryEncodeNat n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, ih]

theorem encodeTriple_length (t : Triple) :
    (encodeTriple t).length = t.1 + t.2.1 + t.2.2 + 2 := by
  simp [encodeTriple, tripleFieldsEncoding, pairEncoding, unaryFinEncodingNat, unary_length]
  omega

theorem triplesEncoding_cons_length (t : Triple) (ts : List Triple) :
    (triplesEncoding.encode (t :: ts)).length =
      t.1 + t.2.1 + t.2.2 + 3 + (triplesEncoding.encode ts).length := by
  simp [triplesEncoding, SAT.encTerminated, encodeTriple_length]
  omega

theorem triplesEncoding_length_bound (n : ℕ) (ts : List Triple)
    (h : ∀ t ∈ ts, t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n) :
    (triplesEncoding.encode ts).length ≤ ts.length * (3 * n + 3) := by
  induction ts with
  | nil => simp [triplesEncoding, SAT.encTerminated]
  | cons t ts ih =>
    have ht := h t (by simp)
    have hs := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
    rw [triplesEncoding_cons_length]
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem instanceEncoding_length_bound (I : Instance) (h : WellFormed I) :
    (instanceEncoding.encode I).length ≤ I.size + 1 + I.triples.length * (3 * I.size + 3) := by
  have ht := triplesEncoding_length_bound I.size I.triples h
  simp only [instanceEncoding, fieldsEncoding, pairEncoding, List.length_append,
    List.length_map, List.length_cons, unaryFinEncodingNat, unary_length]
  omega

theorem flatMap_length_bound {α β : Type} (xs : List α) (f : α → List β) (n : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ n) : (xs.flatMap f).length ≤ xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem graphTriples_length_bound (n : ℕ) (p : Fin n → Fin n → Fin n → Bool) :
    (graphTriples n p).length ≤ n ^ 3 := by
  unfold graphTriples
  have h := flatMap_length_bound (List.finRange n)
    (fun x => (List.finRange n).flatMap fun y =>
      ((List.finRange n).filter (fun z => p x y z)).map (fun z => (x.val, y.val, z.val)))
    (n * n) (by
      intro x hx
      have hh := flatMap_length_bound (List.finRange n)
        (fun y => ((List.finRange n).filter (fun z => p x y z)).map
          (fun z => (x.val, y.val, z.val))) n (by
          intro y hy
          simpa only [List.length_map, List.length_finRange] using
            List.length_filter_le (fun z => p x y z) (List.finRange n))
      simpa only [List.length_finRange] using hh)
  simpa only [List.length_finRange, Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc] using h

theorem cnfToMatching_size_bound (φ : CNF) :
    (cnfToMatching φ).size ≤ 2 * (cnfEncoding.encode φ).length + 1 := by
  have hq := indexedOccurrences_length_le_input φ
  unfold cnfToMatching
  split
  · change 2 * (indexedOccurrences φ).length ≤ _
    omega
  · change 1 ≤ _
    omega

/-- Unary output is polynomially bounded by the original binary CNF input.
The canonical graph enumeration may contain O(L³) triples, each of unary size
O(L), so the simple bound has degree four. -/
theorem cnfToMatching_encoding_length_bound (φ : CNF) :
    (instanceEncoding.encode (cnfToMatching φ)).length ≤
      100 * ((cnfEncoding.encode φ).length + 1) ^ 4 := by
  let q := (indexedOccurrences φ).length
  let N := (cnfEncoding.encode φ).length
  have hq : q ≤ N := indexedOccurrences_length_le_input φ
  unfold cnfToMatching
  split
  · rename_i hm
    have hlen := graphTriples_length_bound (2 * q) (gadgetRelation (formulaLayout φ) hm)
    have he := instanceEncoding_length_bound (gadgetInstance (formulaLayout φ) hm)
      (gadgetInstance_wellFormed _ _)
    change (instanceEncoding.encode (gadgetInstance (formulaLayout φ) hm)).length ≤ _
    change (instanceEncoding.encode (gadgetInstance (formulaLayout φ) hm)).length ≤
      2 * q + 1 + (graphTriples (2 * q) (gadgetRelation (formulaLayout φ) hm)).length *
        (3 * (2 * q) + 3) at he
    have hmul := Nat.mul_le_mul_right (3 * (2 * q) + 3) hlen
    have hout := he.trans (Nat.add_le_add_left hmul (2 * q + 1))
    have hp := Nat.pow_le_pow_left hq 4
    have hp3 := Nat.pow_le_pow_left hq 3
    dsimp [N, q] at *
    nlinarith
  · change (instanceEncoding.encode noInstance).length ≤ _
    have he : (instanceEncoding.encode noInstance).length = 2 := by
      rfl
    rw [he]
    have hp : 0 < ((cnfEncoding.encode φ).length + 1) ^ 4 := Nat.pow_pos (by omega)
    omega

end ProteinFolding.ThreeDimensionalMatching
