import ProteinFolding.Common.SAT.MatchingCycle

/-! Soundness of the standard variable-cycle, clause, and garbage 3DM gadget.
The occurrence layout is finite: vertices depend on occurrence counts, never
on the largest binary variable index. This generic lemma exposes its layout
conditions explicitly; construction of a layout from a formula and the raw
unary instance conversion are separate obligations. -/

namespace ProteinFolding.ThreeDimensionalMatching

structure OccurrenceLayout (q m : ℕ) where
  variableId : Fin q → ℕ
  polarity : Fin q → Bool
  clause : Fin q → Fin m
  next : Equiv.Perm (Fin q)
  next_variable : ∀ i, variableId (next i) = variableId i
  connected : ∀ i j, variableId i = variableId j → ∃ k : ℕ, next^[k] i = j

abbrev GadgetVertex (q m : ℕ) := Fin q ⊕ (Fin m ⊕ Fin (q - m))
abbrev GadgetZ (q : ℕ) := Fin q × Bool

def GadgetAllowed {q m : ℕ} (L : OccurrenceLayout q m)
    (y x : GadgetVertex q m) (z : GadgetZ q) : Prop :=
  match y with
  | .inl i =>
    (x = .inl i ∧ z = (i, false)) ∨ (x = .inl (L.next i) ∧ z = (i, true))
  | .inr (.inl j) =>
    ∃ i, L.clause i = j ∧ x = .inr (.inl j) ∧ z = (i, L.polarity i)
  | .inr (.inr t) => x = .inr (.inr t)

def LayoutSatisfiable {q m : ℕ} (L : OccurrenceLayout q m) : Prop :=
  ∃ a : ℕ → Bool, ∀ j : Fin m, ∃ i : Fin q,
    L.clause i = j ∧ a (L.variableId i) = L.polarity i

theorem gadget_variable_values {q m : ℕ} (L : OccurrenceLayout q m)
    (mx : GadgetVertex q m ≃ GadgetVertex q m) (mz : GadgetVertex q m ≃ GadgetZ q)
    (h : ∀ y, GadgetAllowed L y (mx y) (mz y)) (i : Fin q) :
    mx (.inl i) = .inl (cycleSelector L.next (fun k => !(mz (.inl k)).2) i) ∧
      mz (.inl i) = (i, (mz (.inl i)).2) := by
  rcases h (.inl i) with ⟨hx, hz⟩ | ⟨hx, hz⟩
  · simp [hz, cycleSelector, hx]
  · simp [hz, cycleSelector, hx]

theorem gadget_choices_injective {q m : ℕ} (L : OccurrenceLayout q m)
    (mx : GadgetVertex q m ≃ GadgetVertex q m) (mz : GadgetVertex q m ≃ GadgetZ q)
    (h : ∀ y, GadgetAllowed L y (mx y) (mz y)) :
    Function.Injective (cycleSelector L.next (fun k => !(mz (.inl k)).2)) := by
  intro i j hij
  have hi := (gadget_variable_values L mx mz h i).1
  have hj := (gadget_variable_values L mx mz h j).1
  have he : mx (.inl i) = mx (.inl j) := by rw [hi, hj, hij]
  exact Sum.inl.inj (mx.injective he)

theorem gadget_choices_consistent {q m : ℕ} (L : OccurrenceLayout q m)
    (mx : GadgetVertex q m ≃ GadgetVertex q m) (mz : GadgetVertex q m ≃ GadgetZ q)
    (h : ∀ y, GadgetAllowed L y (mx y) (mz y)) (i j : Fin q)
    (hvar : L.variableId i = L.variableId j) : (mz (.inl i)).2 = (mz (.inl j)).2 := by
  let b : Fin q → Bool := fun k => !(mz (.inl k)).2
  have hb := selector_injective_forces_invariance L.next b (gadget_choices_injective L mx mz h)
  obtain ⟨n, hn⟩ := L.connected i j hvar
  have hiter : ∀ k : ℕ, b (L.next^[k] i) = b i := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hb, ih]
  have he := hiter n
  rw [hn] at he
  dsimp [b] at he
  simpa using congrArg Bool.not he.symm

/-- Every perfect matching of the variable/clause/garbage gadget supplies a
single consistent Boolean assignment satisfying each original clause. -/
theorem gadget_matching_sound {q m : ℕ} (L : OccurrenceLayout q m)
    (mx : GadgetVertex q m ≃ GadgetVertex q m) (mz : GadgetVertex q m ≃ GadgetZ q)
    (h : ∀ y, GadgetAllowed L y (mx y) (mz y)) : LayoutSatisfiable L := by
  classical
  let b : Fin q → Bool := fun i => !(mz (.inl i)).2
  let a : ℕ → Bool := fun v =>
    if hv : ∃ i : Fin q, L.variableId i = v then b (Classical.choose hv) else false
  have ha : ∀ i : Fin q, a (L.variableId i) = b i := by
    intro i
    have hv : ∃ j : Fin q, L.variableId j = L.variableId i := ⟨i, rfl⟩
    dsimp [a]
    rw [dif_pos hv]
    have he := gadget_choices_consistent L mx mz h (Classical.choose hv) i (Classical.choose_spec hv)
    dsimp [b]
    rw [he]
  refine ⟨a, ?_⟩
  intro j
  obtain ⟨i, hclause, _, hz⟩ := h (.inr (.inl j))
  refine ⟨i, hclause, ?_⟩
  rw [ha]
  have hvar := (gadget_variable_values L mx mz h i).2
  have hdiff : mz (.inl i) ≠ mz (.inr (.inl j)) := by
    intro he
    have he' := mz.injective he
    cases he'
  rw [hz, hvar] at hdiff
  have hpol : (mz (.inl i)).2 ≠ L.polarity i := by
    intro he
    exact hdiff (Prod.ext rfl he)
  dsimp [b]
  cases hbi : (mz (.inl i)).2 <;> cases hpi : L.polarity i <;> simp_all

end ProteinFolding.ThreeDimensionalMatching
