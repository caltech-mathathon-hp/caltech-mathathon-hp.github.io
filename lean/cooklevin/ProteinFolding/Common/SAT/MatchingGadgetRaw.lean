import ProteinFolding.Common.SAT.FormulaOccurrences
import ProteinFolding.Common.SAT.MatchingGraph

/-! Canonical renumbering of typed gadget vertices into the explicit raw
three-dimensional matching problem. The three universes have size 2q when
m≤q, where q is the number of literal occurrences and m the clause count.
Enumeration uses only bounded finite indices. -/

namespace ProteinFolding.ThreeDimensionalMatching

instance {q m : ℕ} (L : OccurrenceLayout q m) (y x : GadgetVertex q m) (z : GadgetZ q) :
    Decidable (GadgetAllowed L y x z) := by
  rcases y with i | (j | t) <;> unfold GadgetAllowed <;> infer_instance

def gadgetVertexEquiv (q m : ℕ) (h : m ≤ q) : GadgetVertex q m ≃ Fin (2 * q) :=
  ((Equiv.sumCongr (Equiv.refl (Fin q)) finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by omega))

def gadgetZEquiv (q : ℕ) : GadgetZ q ≃ Fin (2 * q) :=
  ((Equiv.prodCongr (Equiv.refl (Fin q)) finTwoEquiv.symm).trans finProdFinEquiv).trans
    (finCongr (Nat.mul_comm q 2))

def gadgetRelation {q m : ℕ} (L : OccurrenceLayout q m) (h : m ≤ q)
    (x y z : Fin (2 * q)) : Bool :=
  decide (GadgetAllowed L ((gadgetVertexEquiv q m h).symm y)
    ((gadgetVertexEquiv q m h).symm x) ((gadgetZEquiv q).symm z))

def gadgetInstance {q m : ℕ} (L : OccurrenceLayout q m) (h : m ≤ q) : Instance :=
  graphInstance (2 * q) (gadgetRelation L h)

theorem gadgetInstance_wellFormed {q m : ℕ} (L : OccurrenceLayout q m) (h : m ≤ q) :
    WellFormed (gadgetInstance L h) := graphInstance_wellFormed _ _

theorem gadgetInstance_accepts_iff {q m : ℕ} (L : OccurrenceLayout q m) (h : m ≤ q) :
    Accepts (gadgetInstance L h) ↔ LayoutSatisfiable L := by
  rw [gadgetInstance, graphInstance_accepts_iff, ← gadget_matching_iff]
  let ex := gadgetVertexEquiv q m h
  let ez := gadgetZEquiv q
  constructor
  · rintro ⟨mx, mz, hm⟩
    refine ⟨ex.trans (mx.trans ex.symm), ex.trans (mz.trans ez.symm), ?_⟩
    intro y
    have hy := hm (ex y)
    simpa only [ex, ez, gadgetRelation, decide_eq_true_eq, Equiv.trans_apply,
      Equiv.symm_apply_apply] using hy
  · rintro ⟨mx, mz, hm⟩
    refine ⟨ex.symm.trans (mx.trans ex), ex.symm.trans (mz.trans ez), ?_⟩
    intro y
    have hy := hm (ex.symm y)
    simpa only [ex, ez, gadgetRelation, decide_eq_true_eq, Equiv.trans_apply,
      Equiv.symm_apply_apply] using hy

end ProteinFolding.ThreeDimensionalMatching
