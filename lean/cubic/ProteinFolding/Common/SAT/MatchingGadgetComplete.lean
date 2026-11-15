import ProteinFolding.Common.SAT.MatchingGadget
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set

/-! Completing a satisfying assignment to a perfect matching of the typed
3DM gadget. Clause witnesses occupy distinct free occurrence slots, and an
explicit finite-complement equivalence assigns the remaining slots to garbage
vertices. These are semantic existence proofs, not claims of reduction runtime.
-/

namespace ProteinFolding.ThreeDimensionalMatching

theorem extend_injection_to_sum {q m : ℕ} (f : Fin m → Fin q) (hf : Function.Injective f) :
    ∃ e : (Fin m ⊕ Fin (q - m)) ≃ Fin q, ∀ i, e (.inl i) = f i := by
  classical
  let e0 : Fin m ≃ Set.range f := Equiv.ofInjective f hf
  have hc : Fintype.card {i : Fin q // i ∉ Set.range f} = q - m := by
    rw [Fintype.card_subtype_compl]
    rw [← Fintype.card_congr e0]
    simp
  let e1 : Fin (q - m) ≃ {i : Fin q // i ∉ Set.range f} :=
    Fintype.equivOfCardEq (by simpa using hc.symm)
  let e : (Fin m ⊕ Fin (q - m)) ≃ Fin q :=
    (Equiv.sumCongr e0 e1).trans (Equiv.Set.sumCompl (Set.range f))
  refine ⟨e, ?_⟩
  intro i
  rfl

def choiceSplitEquiv {q : ℕ} (b : Fin q → Bool) : (Fin q ⊕ Fin q) ≃ GadgetZ q where
  toFun
    | .inl i => (i, !b i)
    | .inr i => (i, b i)
  invFun z := if z.2 = b z.1 then .inr z.1 else .inl z.1
  left_inv z := by
    cases z with
    | inl i => cases hb : b i <;> simp [hb]
    | inr i => simp
  right_inv z := by
    obtain ⟨i, t⟩ := z
    cases hb : b i <;> cases t <;> simp [hb]

theorem gadget_matching_complete {q m : ℕ} (L : OccurrenceLayout q m)
    (h : LayoutSatisfiable L) :
    ∃ (mx : GadgetVertex q m ≃ GadgetVertex q m) (mz : GadgetVertex q m ≃ GadgetZ q),
      ∀ y, GadgetAllowed L y (mx y) (mz y) := by
  classical
  obtain ⟨a, ha⟩ := h
  let f : Fin m → Fin q := fun j => Classical.choose (ha j)
  have hfclause : ∀ j, L.clause (f j) = j := fun j => (Classical.choose_spec (ha j)).1
  have hfpolarity : ∀ j, a (L.variableId (f j)) = L.polarity (f j) :=
    fun j => (Classical.choose_spec (ha j)).2
  have hfinj : Function.Injective f := by
    intro i j he
    have he' := congrArg L.clause he
    simpa only [hfclause] using he'
  obtain ⟨e, he⟩ := extend_injection_to_sum f hfinj
  let b : Fin q → Bool := fun i => a (L.variableId i)
  have hb : ∀ i, b (L.next i) = b i := by intro i; dsimp [b]; rw [L.next_variable]
  let mx : GadgetVertex q m ≃ GadgetVertex q m :=
    Equiv.sumCongr (selectorPerm L.next b hb) (Equiv.refl _)
  let mz : GadgetVertex q m ≃ GadgetZ q :=
    (Equiv.sumCongr (Equiv.refl _) e).trans (choiceSplitEquiv b)
  refine ⟨mx, mz, ?_⟩
  intro y
  rcases y with i | (j | t)
  · change (mx (.inl i) = .inl i ∧ mz (.inl i) = (i, false)) ∨
      (mx (.inl i) = .inl (L.next i) ∧ mz (.inl i) = (i, true))
    cases hi : b i
    · right
      simp [mx, mz, selectorPerm, cycleSelector, choiceSplitEquiv, hi]
    · left
      simp [mx, mz, selectorPerm, cycleSelector, choiceSplitEquiv, hi]
  · refine ⟨f j, hfclause j, ?_, ?_⟩
    · rfl
    · change (e (.inl j), b (e (.inl j))) = (f j, L.polarity (f j))
      rw [he]
      exact Prod.ext rfl (hfpolarity j)
  · rfl

theorem gadget_matching_iff {q m : ℕ} (L : OccurrenceLayout q m) :
    (∃ (mx : GadgetVertex q m ≃ GadgetVertex q m) (mz : GadgetVertex q m ≃ GadgetZ q),
      ∀ y, GadgetAllowed L y (mx y) (mz y)) ↔ LayoutSatisfiable L := by
  constructor
  · rintro ⟨mx, mz, h⟩
    exact gadget_matching_sound L mx mz h
  · exact gadget_matching_complete L

end ProteinFolding.ThreeDimensionalMatching
