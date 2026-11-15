import ProteinFolding.Tetrahedral.FrameForcingDimerPairs
import ProteinFolding.Tetrahedral.FrameForcingActual

/-! Actual dimer pairs avoid every P-capped unit with no maximal HH run. -/

namespace ProteinFolding.Tetrahedral

theorem dimer_index_avoids_capped_factor (S pre body post : Sequence)
    (heq : S = pre ++ capWord body ++ post) (hzero : dimerStartCount (capWord body) = 0)
    (a : DimerOccurrence S) (b : Bool) :
    ¬ (pre.length ≤ (dimerResidueIndex S (a, b)).val ∧
      (dimerResidueIndex S (a, b)).val < pre.length + (capWord body).length) := by
  rintro ⟨hlo, hhi⟩
  rw [capWord_length] at hhi
  have hidx : a.val + 1 ≤ (dimerResidueIndex S (a, b)).val ∧
      (dimerResidueIndex S (a, b)).val ≤ a.val + 2 := by
    cases b <;> simp [dimerResidueIndex]
  have hfirst : S[pre.length]? = some .P := by
    have h := word_factor_getElem S pre (capWord body) post heq 0 (by rw [capWord_length]; omega)
    simpa only [Nat.add_zero, capWord, List.getElem?_cons_zero] using h
  have hlast : S[pre.length + body.length + 1]? = some .P := by
    have h := word_factor_getElem S pre (capWord body) post heq (body.length + 1)
      (by rw [capWord_length]; omega)
    have h' := h.trans (capWord_get_final_P body)
    simpa only [Nat.add_assoc] using h'
  have ha : pre.length ≤ a.val := by
    by_contra hbad
    have hcases : pre.length = a.val + 1 ∨ pre.length = a.val + 2 := by omega
    rcases hcases with h | h
    · rw [h] at hfirst
      have hbad := hfirst.symm.trans (dimerOccurrence_data a).2.1
      cases hbad
    · rw [h] at hfirst
      have hbad := hfirst.symm.trans (dimerOccurrence_data a).2.2.1
      cases hbad
  have hb : a.val + 3 < pre.length + (body.length + 2) := by
    by_contra hbad
    have hcases : pre.length + body.length + 1 = a.val + 1 ∨
        pre.length + body.length + 1 = a.val + 2 := by omega
    rcases hcases with h | h
    · rw [h] at hlast
      have hbad := hlast.symm.trans (dimerOccurrence_data a).2.1
      cases hbad
    · rw [h] at hlast
      have hbad := hlast.symm.trans (dimerOccurrence_data a).2.2.1
      cases hbad
  have hlocal (r : ℕ) (hr : r ≤ 3) :
      (capWord body)[a.val - pre.length + r]? = S[a.val + r]? := by
    have h := word_factor_getElem S pre (capWord body) post heq (a.val - pre.length + r)
      (by rw [capWord_length]; omega)
    have hind : pre.length + (a.val - pre.length + r) = a.val + r := by omega
    rw [hind] at h
    exact h.symm
  have hstart : IsDimerStart (capWord body) (a.val - pre.length) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Nat.add_zero] using (hlocal 0 (by decide)).trans (dimerOccurrence_data a).1
    · exact (hlocal 1 (by decide)).trans (dimerOccurrence_data a).2.1
    · exact (hlocal 2 (by decide)).trans (dimerOccurrence_data a).2.2.1
    · exact (hlocal 3 le_rfl).trans (dimerOccurrence_data a).2.2.2
  have hmem : a.val - pre.length ∈ dimerStartIndices (capWord body) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rw [capWord_length]; omega), hstart⟩
  have hcard : (dimerStartIndices (capWord body)).card = 0 := by rw [dimerStartIndices_card, hzero]
  have hempty := Finset.card_eq_zero.mp hcard
  rw [hempty] at hmem
  exact Finset.notMem_empty _ hmem

theorem foldDimerPairs_avoid_capped_occurrence (S : Sequence)
    (f : Fold tetrahedralLattice S.length) (pre body post : Sequence)
    (heq : S = pre ++ capWord body ++ post) (hzero : dimerStartCount (capWord body) = 0) :
    Disjoint (foldDimerPairs S f).covered
      ((Finset.range (capWord body).length).image (fun i => foldSiteAt f (pre.length + i))) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i, hi, heqSite⟩ := Finset.mem_image.mp hy
  have hi' := Finset.mem_range.mp hi
  have hlen : pre.length + (capWord body).length ≤ S.length := by
    rw [heq, List.length_append, List.length_append]
    omega
  rw [foldSiteAt_eq f _ (by omega)] at heqSite
  have hindex := congrArg Fin.val (f.injective_pos heqSite)
  change pre.length + i = (dimerResidueIndex S (a, b)).val at hindex
  exact dimer_index_avoids_capped_factor S pre body post heq hzero a b ⟨by omega, by omega⟩

end ProteinFolding.Tetrahedral
