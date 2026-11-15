import ProteinFolding.Common.SAT.OccurrenceCycles
import ProteinFolding.Common.SAT.ThreeCNFBounds

/-! An explicit occurrence layout for an arbitrary CNF formula. Clause tags
are finite indices, and repeated literals are retained as separate occurrences.
Sorting a variable's occurrence indices supplies its cycle. Large binary
variable identifiers are compared but never used as universe sizes. -/

namespace ProteinFolding.ThreeDimensionalMatching

open SAT

def indexedOccurrences (φ : CNF) : List (Fin φ.length × Literal) :=
  (List.ofFn (fun j : Fin φ.length => (φ.get j).map (fun l => (j, l)))).flatten

theorem mem_indexedOccurrences (φ : CNF) (j : Fin φ.length) (l : Literal) :
    (j, l) ∈ indexedOccurrences φ ↔ l ∈ φ.get j := by
  constructor
  · intro h
    obtain ⟨c, hc, hl⟩ := List.mem_flatten.mp h
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hl
    have hk : k = j := congrArg Prod.fst he
    have hv' : v = l := congrArg Prod.snd he
    simpa only [hk, hv'] using hv
  · intro h
    apply List.mem_flatten.mpr
    refine ⟨(φ.get j).map (fun v => (j, v)), List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
    exact List.mem_map.mpr ⟨l, h, rfl⟩

def occurrenceVariable (φ : CNF) (i : Fin (indexedOccurrences φ).length) : ℕ :=
  ((indexedOccurrences φ).get i).2.var

def formulaLayout (φ : CNF) : OccurrenceLayout (indexedOccurrences φ).length φ.length where
  variableId := occurrenceVariable φ
  polarity i := ((indexedOccurrences φ).get i).2.pos
  clause i := ((indexedOccurrences φ).get i).1
  next := occurrenceCycle (occurrenceVariable φ)
  next_variable := occurrenceCycle_variable (occurrenceVariable φ)
  connected := occurrenceCycle_connected (occurrenceVariable φ)

theorem literal_eval_true_iff (a : ℕ → Bool) (l : Literal) :
    l.eval a = true ↔ a l.var = l.pos := by
  cases hp : l.pos <;> cases hv : a l.var <;> simp [Literal.eval, hp, hv]

theorem formulaLayout_satisfiable_iff (φ : CNF) :
    LayoutSatisfiable (formulaLayout φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro c hc
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hc
    obtain ⟨i, hi, hp⟩ := ha j
    let l := ((indexedOccurrences φ).get i).2
    have hpair : (j, l) ∈ indexedOccurrences φ := by
      have hm := List.get_mem (indexedOccurrences φ) i
      have he : ((indexedOccurrences φ).get i) = (j, l) := by
        apply Prod.ext
        · exact hi
        · rfl
      rwa [he] at hm
    refine ⟨l, (mem_indexedOccurrences φ j l).mp hpair, ?_⟩
    exact (literal_eval_true_iff a l).mpr hp
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro j
    obtain ⟨l, hl, he⟩ := ha (φ.get j) (List.get_mem ..)
    have hm := (mem_indexedOccurrences φ j l).mpr hl
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    refine ⟨i, ?_, ?_⟩
    · exact congrArg Prod.fst hi
    · have hlit : ((indexedOccurrences φ).get i).2 = l := congrArg Prod.snd hi
      change a (((indexedOccurrences φ).get i).2.var) = ((indexedOccurrences φ).get i).2.pos
      rw [hlit]
      exact (literal_eval_true_iff a l).mp he

/-- The actual finite variable/clause/garbage gadget constructed from φ has a
perfect matching exactly when φ is satisfiable. This is the semantic reduction;
raw vertex renumbering and TM2 runtime are separate statements. -/
theorem formula_gadget_equisatisfiable (φ : CNF) :
    (∃ (mx : GadgetVertex (indexedOccurrences φ).length φ.length ≃
        GadgetVertex (indexedOccurrences φ).length φ.length)
      (mz : GadgetVertex (indexedOccurrences φ).length φ.length ≃
        GadgetZ (indexedOccurrences φ).length),
      ∀ y, GadgetAllowed (formulaLayout φ) y (mx y) (mz y)) ↔ Satisfiable φ := by
  rw [gadget_matching_iff, formulaLayout_satisfiable_iff]

end ProteinFolding.ThreeDimensionalMatching
