import ProteinFolding.Common.CookLevinProofCertificateCells

/-! The finite-cell certificate boundary is exactly an initial mathlib TM2
configuration with a fixed header and an arbitrary bounded certificate word.
No enumeration of certificate words or restriction to Boolean alphabets occurs.
-/

namespace ProteinFolding.SAT.CookLevinCertificateBoundary

open Turing TM2 CookLevinAlphabet CookLevinRows CookLevinLinks CookLevinCertificateCells

theorem initial_encoded_input (tm : FinTM2) (xs : List (Symbol tm tm.k₀)) :
    encodedStack tm (initList tm (xs.map Subtype.val)) (initList_stacksIn tm _) tm.k₀ = xs := by
  apply List.map_injective_iff.mpr Subtype.coe_injective
  rw [encodedStack, encodeStack_decode]
  simp [initList]

theorem initial_encoded_other (tm : FinTM2) (xs : List (Symbol tm tm.k₀))
    (k : tm.K) (hk : k ≠ tm.k₀) :
    encodedStack tm (initList tm (xs.map Subtype.val)) (initList_stacksIn tm _) k = [] := by
  apply List.length_eq_zero_iff.mp
  rw [encodedStack_length]
  simp [initList, hk]

theorem represents_input_iff (tm : FinTM2) (M : ℕ) (xs : List (Symbol tm tm.k₀))
    (hM : xs.length ≤ M) (r : Row tm M) :
    Represents r (initList tm (xs.map Subtype.val)) (initList_stacksIn tm _) ↔
      r.control = (some tm.main, tm.initialState) ∧ inputCells tm M r = padded xs M ∧
      ∀ k, k ≠ tm.k₀ → ∀ n, r.cells k n = none := by
  constructor
  · intro hr
    refine ⟨hr.1, ?_, ?_⟩
    · have hf : r.cells tm.k₀ = fun n : Fin M => xs[n.val]? := by
        funext n
        rw [hr.2 tm.k₀ n, initial_encoded_input]
      rw [inputCells, hf, padded_ofFn xs M hM]
    · intro k hk n
      rw [hr.2 k n, initial_encoded_other tm xs k hk]
      rfl
  · rintro ⟨hc, hi, ho⟩
    refine ⟨hc, ?_⟩
    intro k n
    by_cases hk : k = tm.k₀
    · subst k
      have he : List.ofFn (r.cells tm.k₀) = List.ofFn (fun n : Fin M => xs[n.val]?) :=
        hi.trans (padded_ofFn xs M hM).symm
      rw [initial_encoded_input]
      exact congrFun (List.ofFn_injective he) n
    · rw [ho k hk n, initial_encoded_other tm xs k hk]
      rfl

/-- The local finite-cell boundary permits precisely every certificate word
over the specified alphabet whose length is at most B. -/
theorem certificateBoundary_iff {C : Type*} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (header : List (Symbol tm tm.k₀)) (B : ℕ)
    (hM : header.length + B ≤ M) (r : Row tm M) :
    CertificateBoundary tm M e header B r ↔
      ∃ cs : List C, cs.length ≤ B ∧
        Represents r (initList tm ((header ++ cs.map e).map Subtype.val)) (initList_stacksIn tm _) := by
  constructor
  · rintro ⟨hc, hb, ho⟩
    obtain ⟨cs, hcs, hi⟩ := (hasCertificate_iff e header B M (inputCells tm M r)
      (by simp only [inputCells, List.length_ofFn]) hM).mp hb
    have hword : (header ++ cs.map e).length ≤ M := by
      simp only [List.length_append, List.length_map]
      omega
    exact ⟨cs, hcs, (represents_input_iff tm M (header ++ cs.map e) hword r).mpr ⟨hc, hi, ho⟩⟩
  · rintro ⟨cs, hcs, hr⟩
    have hword : (header ++ cs.map e).length ≤ M := by
      simp only [List.length_append, List.length_map]
      omega
    obtain ⟨hc, hi, ho⟩ := (represents_input_iff tm M (header ++ cs.map e) hword r).mp hr
    refine ⟨hc, ?_, ho⟩
    exact (hasCertificate_iff e header B M (inputCells tm M r)
      (by simp only [inputCells, List.length_ofFn]) hM).mpr ⟨cs, hcs, hi⟩

theorem surjective_certificate_words {C : Type} (ec : Computability.FinEncoding C)
    (hs : Function.Surjective ec.encode) (B : ℕ) (P : List ec.Γ → Prop) :
    (∃ w : List ec.Γ, w.length ≤ B ∧ P w) ↔
      ∃ c : C, (ec.encode c).length ≤ B ∧ P (ec.encode c) := by
  constructor
  · rintro ⟨w, hw, hp⟩
    obtain ⟨c, rfl⟩ := hs w
    exact ⟨c, hw, hp⟩
  · rintro ⟨c, hc, hp⟩
    exact ⟨ec.encode c, hc, hp⟩

end ProteinFolding.SAT.CookLevinCertificateBoundary
