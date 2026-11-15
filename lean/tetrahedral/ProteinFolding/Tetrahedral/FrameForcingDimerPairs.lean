import ProteinFolding.Tetrahedral.FrameForcingDimerCounts
import ProteinFolding.Tetrahedral.FrameForcingMatching
import ProteinFolding.Tetrahedral.SoundnessDimers

/-! Actual disjoint dimer pairs of a fold, indexed by P-H-H-P occurrences. -/

namespace ProteinFolding.Tetrahedral

abbrev DimerOccurrence (S : Sequence) := {i : ℕ // i ∈ dimerStartIndices S}

theorem dimerOccurrence_data {S : Sequence} (a : DimerOccurrence S) : IsDimerStart S a.val :=
  (Finset.mem_filter.mp a.property).2

def dimerResidueIndex (S : Sequence) : DimerOccurrence S × Bool → Fin S.length
  | (a, false) => ⟨a.val + 1, by
      have h := (List.getElem?_eq_some_iff.mp (dimerOccurrence_data a).2.2.2).choose
      omega⟩
  | (a, true) => ⟨a.val + 2, by
      have h := (List.getElem?_eq_some_iff.mp (dimerOccurrence_data a).2.2.2).choose
      omega⟩

theorem dimerResidueIndex_injective (S : Sequence) : Function.Injective (dimerResidueIndex S) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ heq
  have h := congrArg Fin.val heq
  cases b <;> cases d
  · have hac : a = c := by apply Subtype.ext; change a.val + 1 = c.val + 1 at h; omega
    subst c
    rfl
  · change a.val + 1 = c.val + 2 at h
    have hac : a.val = c.val + 1 := by omega
    have hP := (dimerOccurrence_data a).1
    have hH := (dimerOccurrence_data c).2.1
    rw [hac] at hP
    have hbad := hP.symm.trans hH
    cases hbad
  · change a.val + 2 = c.val + 1 at h
    have hca : c.val = a.val + 1 := by omega
    have hP := (dimerOccurrence_data c).1
    have hH := (dimerOccurrence_data a).2.1
    rw [hca] at hP
    have hbad := hP.symm.trans hH
    cases hbad
  · have hac : a = c := by apply Subtype.ext; change a.val + 2 = c.val + 2 at h; omega
    subst c
    rfl

def foldDimerPairs (S : Sequence) (f : Fold tetrahedralLattice S.length) :
    FinitePairFamily (DimerOccurrence S) Site where
  point a := f.pos (dimerResidueIndex S a)
  injective := f.injective_pos.comp (dimerResidueIndex_injective S)

theorem foldDimerPairs_card (S : Sequence) (f : Fold tetrahedralLattice S.length) :
    (foldDimerPairs S f).covered.card = 2 * dimerStartCount S := by
  rw [FinitePairFamily.covered_card, Fintype.card_coe, dimerStartIndices_card]

theorem foldDimerPairs_adjacent (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (a : DimerOccurrence S) :
    tetrahedralLattice.Adj ((foldDimerPairs S f).point (a, false))
      ((foldDimerPairs S f).point (a, true)) := by
  exact f.consecutive _ _ rfl

theorem foldDimerPairs_on_edge (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m) (a : DimerOccurrence S) :
    ∃ k t, k ≠ t ∧ OctEdgeSite m k t ((foldDimerPairs S f).point (a, false)) ∧
      OctEdgeSite m k t ((foldDimerPairs S f).point (a, true)) := by
  obtain ⟨hlb, hl⟩ := List.getElem?_eq_some_iff.mp (dimerOccurrence_data a).1
  obtain ⟨hib, hi⟩ := List.getElem?_eq_some_iff.mp (dimerOccurrence_data a).2.1
  obtain ⟨hjb, hj⟩ := List.getElem?_eq_some_iff.mp (dimerOccurrence_data a).2.2.1
  obtain ⟨hrb, hr⟩ := List.getElem?_eq_some_iff.mp (dimerOccurrence_data a).2.2.2
  exact flanked_dimer_on_edge S f m hsupport ⟨a.val, hlb⟩ ⟨a.val + 1, hib⟩
    ⟨a.val + 2, hjb⟩ ⟨a.val + 3, hrb⟩ hl hi hj hr rfl rfl rfl

theorem dimerResidueIndex_not_php {S : Sequence} (a : DimerOccurrence S) (b : Bool) :
    ¬ IsPHPMonomer S (dimerResidueIndex S (a, b)) := by
  rintro ⟨_, l, r, hli, hir, hl, hr⟩
  cases b with
  | false =>
    have hrval : r.val = a.val + 2 := by change (a.val + 1) + 1 = r.val at hir; omega
    have hP : S[r.val]? = some .P := List.getElem?_eq_some_iff.mpr ⟨r.isLt, hr⟩
    rw [hrval] at hP
    have hbad := hP.symm.trans (dimerOccurrence_data a).2.2.1
    cases hbad
  | true =>
    have hlval : l.val = a.val + 1 := by change l.val + 1 = a.val + 2 at hli; omega
    have hP : S[l.val]? = some .P := List.getElem?_eq_some_iff.mpr ⟨l.isLt, hl⟩
    rw [hlval] at hP
    have hbad := hP.symm.trans (dimerOccurrence_data a).2.1
    cases hbad

theorem foldDimerPairs_avoid_vertices (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hvertices : (phpIndices S).image f.pos = octVertices m) :
    Disjoint (foldDimerPairs S f).covered (octVertices m) := by
  apply Finset.disjoint_left.mpr
  intro x hx hv
  obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.mp hx
  rw [← hvertices] at hv
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hv
  have hidx : i = dimerResidueIndex S (a, b) := f.injective_pos heq
  have hphp := (Finset.mem_filter.mp hi).2
  rw [hidx] at hphp
  exact dimerResidueIndex_not_php a b hphp

namespace ConstructionParameters

theorem reductionWord_foldDimerPairs_card (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length) :
    (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).covered.card = 2 * p.reductionDimerCount := by
  rw [foldDimerPairs_card, p.reductionWord_dimerStartCount items bulkLengths gaps htotal hbulk]

end ConstructionParameters

end ProteinFolding.Tetrahedral
