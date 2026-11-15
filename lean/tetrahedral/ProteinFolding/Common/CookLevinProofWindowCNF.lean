import ProteinFolding.Common.CookLevinProofWindow
import ProteinFolding.Common.CookLevinProofLocal

/-! Boolean clauses for the finite local transition table of an actual FinTM2.
One-hot window and replacement codes have machine-fixed length. The clauses
reject malformed codes as well as incorrect transitions. Their interpretation
is connected to the complete TM2 configuration by capture_execute_exact.
The transition table is a finite object; this module does not yet construct
the TM2 machine which emits an entire finite-horizon tableau.
-/

namespace ProteinFolding.SAT.CookLevinWindowCNF

open Turing TM2 CookLevinAlphabet CookLevinWindow CookLevinLocal CookLevinCircuit

open scoped Classical in
noncomputable def finiteCode {A : Type*} [Fintype A] (a : A) : List Bool :=
  Finset.univ.toList.map (fun x => decide (x = a))

theorem finiteCode_length {A : Type*} [Fintype A] (a : A) :
    (finiteCode a).length = Fintype.card A := by
  classical
  simp [finiteCode]

theorem finiteCode_injective {A : Type*} [Fintype A] :
    Function.Injective (@finiteCode A _) := by
  classical
  intro a b h
  have he := List.map_inj_left.mp h a (by simp)
  simpa only [decide_true, decide_eq_true_eq] using he.symm

noncomputable def windowAllowed (tm : FinTM2) (bs : List Bool) : Bool := by
  classical
  exact decide (∃ w : Window tm, bs = finiteCode w ++ finiteCode (executeWindow tm w))

theorem windowAllowed_iff (tm : FinTM2) (bs : List Bool) :
    windowAllowed tm bs = true ↔
      ∃ w : Window tm, bs = finiteCode w ++ finiteCode (executeWindow tm w) := by
  classical
  simp only [windowAllowed, decide_eq_true_eq]

theorem windowAllowed_code_iff (tm : FinTM2) (w : Window tm) (r : Replacement tm) :
    windowAllowed tm (finiteCode w ++ finiteCode r) = true ↔ r = executeWindow tm w := by
  rw [windowAllowed_iff]
  constructor
  · rintro ⟨u, h⟩
    have hparts := List.append_inj h (by simp only [finiteCode_length])
    have hu : w = u := finiteCode_injective hparts.1
    subst u
    exact finiteCode_injective hparts.2
  · rintro rfl
    exact ⟨w, rfl⟩

noncomputable def windowCNF (tm : FinTM2) (vars : List ℕ) : CNF :=
  relationCNF vars (windowAllowed tm)

theorem windowCNF_iff (tm : FinTM2) (vars : List ℕ) (a : ℕ → Bool) :
    Satisfied a (windowCNF tm vars) ↔
      ∃ w : Window tm, vars.map a = finiteCode w ++ finiteCode (executeWindow tm w) := by
  rw [windowCNF, relationCNF_iff, windowAllowed_iff]

theorem windowCNF_codes_iff (tm : FinTM2) (vars : List ℕ) (a : ℕ → Bool)
    (w : Window tm) (r : Replacement tm)
    (h : vars.map a = finiteCode w ++ finiteCode r) :
    Satisfied a (windowCNF tm vars) ↔ r = executeWindow tm w := by
  rw [windowCNF, relationCNF_iff, h, windowAllowed_code_iff]

noncomputable def windowArity (tm : FinTM2) : ℕ := Fintype.card (Window tm) + Fintype.card (Replacement tm)

theorem windowAllowed_length (tm : FinTM2) (bs : List Bool)
    (h : windowAllowed tm bs = true) : bs.length = windowArity tm := by
  obtain ⟨w, rfl⟩ := (windowAllowed_iff tm bs).mp h
  simp only [List.length_append, finiteCode_length, windowArity]

theorem windowCNF_clause_count (tm : FinTM2) (vars : List ℕ)
    (h : vars.length = windowArity tm) :
    (windowCNF tm vars).length ≤ 2 ^ windowArity tm := by
  simpa only [windowCNF, h] using relationCNF_clause_count vars (windowAllowed tm)

theorem windowCNF_clause_width (tm : FinTM2) (vars : List ℕ)
    (h : vars.length = windowArity tm) :
    ∀ c ∈ windowCNF tm vars, c.length = windowArity tm := by
  intro c hc
  exact (relationCNF_clause_width vars (windowAllowed tm) c hc).trans h

theorem windowCNF_encoded_length (tm : FinTM2) (vars : List ℕ)
    (h : vars.length = windowArity tm) (V : ℕ) (hv : ∀ i ∈ vars, i ≤ V) :
    (cnfEncoding.encode (windowCNF tm vars)).length ≤
      (2 ^ windowArity tm * windowArity tm) * (V + 2) + 2 ^ windowArity tm := by
  simpa only [windowCNF, h] using relationCNF_encoded_length_bound vars (windowAllowed tm) V hv

/-- A satisfying local transition on captured stack prefixes reconstructs the
exact complete mathlib transition, including the unbounded untouched suffixes. -/
theorem windowCNF_transition_exact (tm : FinTM2) (vars : List ℕ) (a : ℕ → Bool)
    (l : tm.Λ) (v : tm.σ) (S : ∀ k, List (tm.Γ k))
    (hS : StacksIn (machineSymbols tm) S) (r : Replacement tm)
    (hc : vars.map a = finiteCode (captureWindow tm l v S hS) ++ finiteCode r)
    (hs : Satisfied a (windowCNF tm vars)) :
    stepAux (tm.m l) v S =
      CookLevinLocality.appendConfig (decodeReplacement tm r)
        (fun k => (S k).drop (machineReadBound tm)) := by
  have hr := (windowCNF_codes_iff tm vars a _ r hc).mp hs
  rw [hr]
  exact capture_execute_exact tm l v S hS

end ProteinFolding.SAT.CookLevinWindowCNF
