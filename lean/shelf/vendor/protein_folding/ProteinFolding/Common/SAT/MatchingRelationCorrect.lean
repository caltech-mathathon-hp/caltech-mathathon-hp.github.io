import ProteinFolding.Common.SAT.MatchingRelation
import ProteinFolding.Common.SAT.MatchingGadgetRaw

/-! Arithmetic correctness of the occurrence-gadget relation. The existing
`gadgetZEquiv` interleaves the two Boolean copies. The actual relation uses two
contiguous blocks instead; the additional equivalence below establishes that
this alternative labelling has exactly the same matching semantics. No
previous gadget definition is changed. -/

namespace ProteinFolding.ThreeDimensionalMatching

open SAT SourceQueries

def blockGadgetZEquiv (q : ℕ) : GadgetZ q ≃ Fin (2 * q) :=
  ((Equiv.prodComm (Fin q) Bool).trans
    (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl (Fin q)))).trans finProdFinEquiv

theorem vertex_inl_val (q m : ℕ) (h : m ≤ q) (i : Fin q) :
    (gadgetVertexEquiv q m h (.inl i)).val = i.val := rfl

theorem vertex_clause_val (q m : ℕ) (h : m ≤ q) (j : Fin m) :
    (gadgetVertexEquiv q m h (.inr (.inl j))).val = q + j.val := rfl

theorem vertex_garbage_val (q m : ℕ) (h : m ≤ q) (t : Fin (q - m)) :
    (gadgetVertexEquiv q m h (.inr (.inr t))).val = q + (m + t.val) := rfl

theorem blockZ_false_val (q : ℕ) (i : Fin q) :
    (blockGadgetZEquiv q (i, false)).val = i.val := by
  change i.val + q * 0 = i.val
  omega

theorem blockZ_true_val (q : ℕ) (i : Fin q) :
    (blockGadgetZEquiv q (i, true)).val = q + i.val := by
  change i.val + q * 1 = q + i.val
  omega

theorem vertex_value_eq_iff {q m : ℕ} (h : m ≤ q) (x y : GadgetVertex q m) :
    (gadgetVertexEquiv q m h x).val = (gadgetVertexEquiv q m h y).val ↔ x = y := by
  constructor
  · intro he
    exact (gadgetVertexEquiv q m h).injective (Fin.ext he)
  · rintro rfl
    rfl

theorem block_slot_false (φ : CNF) (i : Fin (indexedOccurrences φ).length) :
    occurrenceSlot φ (blockGadgetZEquiv _ (i, false)).val = i.val := by
  rw [blockZ_false_val]
  simp only [occurrenceSlot, i.isLt, if_pos]

theorem block_slot_true (φ : CNF) (i : Fin (indexedOccurrences φ).length) :
    occurrenceSlot φ (blockGadgetZEquiv _ (i, true)).val = i.val := by
  rw [blockZ_true_val]
  have hi := i.isLt
  simp [occurrenceSlot, show ¬ (indexedOccurrences φ).length + i.val < (indexedOccurrences φ).length by omega]

theorem positiveAt_indexed (φ : CNF) (i : Fin (indexedOccurrences φ).length) :
    positiveAt (φ, i.val) = (formulaLayout φ).polarity i := by
  rw [positiveAt_correct φ i.val (by simpa only [indexedOccurrences_length] using i.isLt)]
  exact congrArg (fun l : Literal => l.pos) (indexedOccurrence_literal φ i).symm

theorem vertex_inl_eq_iff {q m : ℕ} (h : m ≤ q) (x : GadgetVertex q m) (i : Fin q) :
    (gadgetVertexEquiv q m h x).val = i.val ↔ x = .inl i := by
  rw [← vertex_inl_val q m h i]
  exact vertex_value_eq_iff h x (.inl i)

theorem vertex_clause_eq_iff {q m : ℕ} (h : m ≤ q) (x : GadgetVertex q m) (j : Fin m) :
    (gadgetVertexEquiv q m h x).val = q + j.val ↔ x = .inr (.inl j) := by
  rw [← vertex_clause_val q m h j]
  exact vertex_value_eq_iff h x (.inr (.inl j))

theorem vertex_garbage_eq_iff {q m : ℕ} (h : m ≤ q) (x : GadgetVertex q m) (t : Fin (q-m)) :
    (gadgetVertexEquiv q m h x).val = q + (m + t.val) ↔ x = .inr (.inr t) := by
  rw [← vertex_garbage_val q m h t]
  exact vertex_value_eq_iff h x (.inr (.inr t))

theorem clause_allowed_iff {q m : ℕ} (L : OccurrenceLayout q m) (x : GadgetVertex q m)
    (j : Fin m) (i : Fin q) (b : Bool) :
    GadgetAllowed L (.inr (.inl j)) x (i, b) ↔
      x = .inr (.inl j) ∧ L.clause i = j ∧ L.polarity i = b := by
  change (∃ k, L.clause k = j ∧ x = .inr (.inl j) ∧ (i, b) = (k, L.polarity k)) ↔ _
  constructor
  · rintro ⟨k, hc, hx, hz⟩
    have hik : i = k := congrArg Prod.fst hz
    have hbp : b = L.polarity k := congrArg Prod.snd hz
    subst k
    exact ⟨hx, hc, hbp.symm⟩
  · rintro ⟨hx, hc, hp⟩
    exact ⟨i, hc, hx, Prod.ext rfl hp.symm⟩

theorem rawRelation_vertices (φ : CNF) (h : φ.length ≤ (indexedOccurrences φ).length)
    (x y : GadgetVertex (indexedOccurrences φ).length φ.length)
    (z : GadgetZ (indexedOccurrences φ).length) :
    rawRelation φ (gadgetVertexEquiv _ _ h x).val (gadgetVertexEquiv _ _ h y).val
      (blockGadgetZEquiv _ z).val = decide (GadgetAllowed (formulaLayout φ) y x z) := by
  obtain ⟨i, b⟩ := z
  rcases y with j | (j | t)
  · cases b
    · have hij : ¬ i.val = (indexedOccurrences φ).length + j.val := by have := i.isLt; omega
      simp [rawRelation, vertex_inl_val, blockZ_false_val, j.isLt, hij,
        nextVariableIndex_correct, formulaLayout, GadgetAllowed, vertex_inl_eq_iff, Fin.ext_iff]
    · have hij : ¬ (indexedOccurrences φ).length + i.val = j.val := by have := j.isLt; omega
      simp [rawRelation, vertex_inl_val, blockZ_true_val, j.isLt, hij,
        nextVariableIndex_correct, formulaLayout, GadgetAllowed, vertex_inl_eq_iff, Fin.ext_iff]
  · have hjq : ¬ (indexedOccurrences φ).length + j.val < (indexedOccurrences φ).length := by omega
    have hjm : (indexedOccurrences φ).length + j.val < (indexedOccurrences φ).length + φ.length := by have := j.isLt; omega
    cases b
    · have hiz : ¬ (indexedOccurrences φ).length ≤ i.val := by have := i.isLt; omega
      simp [rawRelation, vertex_clause_val, blockZ_false_val, hjq, hjm, occurrenceSlot,
        i.isLt, hiz, clauseIndexAt_correct φ i, positiveAt_indexed φ i, vertex_clause_eq_iff,
        clause_allowed_iff, formulaLayout, Fin.ext_iff, Bool.and_assoc]
    · have hiz : (indexedOccurrences φ).length ≤ (indexedOccurrences φ).length + i.val := by omega
      have hiq : ¬ (indexedOccurrences φ).length + i.val < (indexedOccurrences φ).length := by omega
      simp [rawRelation, vertex_clause_val, blockZ_true_val, hjq, hjm, occurrenceSlot,
        hiq, hiz, clauseIndexAt_correct φ i, positiveAt_indexed φ i, vertex_clause_eq_iff,
        clause_allowed_iff, formulaLayout, Fin.ext_iff, Bool.and_assoc]
  · have htq : ¬ (indexedOccurrences φ).length + (φ.length + t.val) < (indexedOccurrences φ).length := by omega
    have htm : ¬ (indexedOccurrences φ).length + (φ.length + t.val) < (indexedOccurrences φ).length + φ.length := by omega
    simp only [rawRelation, vertex_garbage_val, htq, htm, if_false, vertex_garbage_eq_iff, GadgetAllowed]

def blockGadgetRelation {q m : ℕ} (L : OccurrenceLayout q m) (h : m ≤ q)
    (x y z : Fin (2 * q)) : Bool :=
  decide (GadgetAllowed L ((gadgetVertexEquiv q m h).symm y)
    ((gadgetVertexEquiv q m h).symm x) ((blockGadgetZEquiv q).symm z))

def blockGadgetInstance {q m : ℕ} (L : OccurrenceLayout q m) (h : m ≤ q) : Instance :=
  graphInstance (2 * q) (blockGadgetRelation L h)

theorem rawRelation_correct (φ : CNF) (h : φ.length ≤ (indexedOccurrences φ).length)
    (x y z : Fin (2 * (indexedOccurrences φ).length)) :
    rawRelation φ x.val y.val z.val = blockGadgetRelation (formulaLayout φ) h x y z := by
  have he := rawRelation_vertices φ h ((gadgetVertexEquiv _ _ h).symm x)
    ((gadgetVertexEquiv _ _ h).symm y) ((blockGadgetZEquiv _).symm z)
  simpa only [blockGadgetRelation, Equiv.apply_symm_apply] using he

theorem blockGadgetInstance_accepts_iff {q m : ℕ} (L : OccurrenceLayout q m) (h : m ≤ q) :
    Accepts (blockGadgetInstance L h) ↔ LayoutSatisfiable L := by
  rw [blockGadgetInstance, graphInstance_accepts_iff, ← gadget_matching_iff]
  let ex := gadgetVertexEquiv q m h
  let ez := blockGadgetZEquiv q
  constructor
  · rintro ⟨mx, mz, hm⟩
    refine ⟨ex.trans (mx.trans ex.symm), ex.trans (mz.trans ez.symm), ?_⟩
    intro y
    have hy := hm (ex y)
    simpa only [ex, ez, blockGadgetRelation, decide_eq_true_eq, Equiv.trans_apply,
      Equiv.symm_apply_apply] using hy
  · rintro ⟨mx, mz, hm⟩
    refine ⟨ex.symm.trans (mx.trans ex), ex.symm.trans (mz.trans ez), ?_⟩
    intro y
    have hy := hm (ex.symm y)
    simpa only [ex, ez, blockGadgetRelation, decide_eq_true_eq, Equiv.trans_apply,
      Equiv.symm_apply_apply] using hy

/-- The block-labelled arithmetic graph is satisfiable exactly when the source
CNF is satisfiable. The proof uses an explicit equivalence of vertex labels. -/
theorem blockGraph_accepts_iff (φ : CNF) (h : φ.length ≤ (indexedOccurrences φ).length) :
    Accepts (graphInstance (2 * (indexedOccurrences φ).length)
      (fun x y z => rawRelation φ x.val y.val z.val)) ↔ Satisfiable φ := by
  have hr : (fun x y z : Fin (2 * (indexedOccurrences φ).length) => rawRelation φ x.val y.val z.val) =
      blockGadgetRelation (formulaLayout φ) h := by
    funext x y z
    exact rawRelation_correct φ h x y z
  rw [hr]
  exact (blockGadgetInstance_accepts_iff (formulaLayout φ) h).trans (formulaLayout_satisfiable_iff φ)

end ProteinFolding.ThreeDimensionalMatching
