import ProteinFolding.Tetrahedral.FrameForcingActual

/-! A non-PHP H without an H chain-neighbour is the first monomer of the
actual reduction word, whose final residue is P. -/

namespace ProteinFolding.Tetrahedral

theorem H_first_of_no_H_neighbours (S pre : Sequence) (heq : S = pre ++ [.P])
    (i : Fin S.length) (hH : S.get i = .H) (hnotPHP : ¬ IsPHPMonomer S i)
    (hnoH : ∀ j : Fin S.length, S.get j = .H → i.val + 1 ≠ j.val ∧ j.val + 1 ≠ i.val) :
    i.val = 0 := by
  by_contra hzero
  have hlen : S.length = pre.length + 1 := by rw [heq, List.length_append]; rfl
  have hlast : S[pre.length]? = some .P := by
    have heq' : S = pre ++ [.P] ++ [] := by simpa only [List.append_nil] using heq
    simpa only [Nat.add_zero, List.getElem?_cons_zero] using
      word_factor_getElem S pre [.P] [] heq' 0 (by decide)
  have hright : i.val + 1 < S.length := by
    by_contra hbad
    have hind : i.val = pre.length := by omega
    have hHi : S[i.val]? = some .H := List.getElem?_eq_some_iff.mpr ⟨i.isLt, hH⟩
    rw [hind] at hHi
    have hbad := hlast.symm.trans hHi
    cases hbad
  let l : Fin S.length := ⟨i.val - 1, by omega⟩
  let r : Fin S.length := ⟨i.val + 1, hright⟩
  have hl : S.get l = .P := by
    cases he : S.get l with
    | H => exact ((hnoH l he).2 (by dsimp [l]; omega)).elim
    | P => rfl
  have hr : S.get r = .P := by
    cases he : S.get r with
    | H => exact ((hnoH r he).1 rfl).elim
    | P => rfl
  exact hnotPHP ⟨hH, l, r, by dsimp [l]; omega, rfl, hl, hr⟩

theorem assembleCappedBodies_ends_P (gaps : ℕ → ℕ) (i : ℕ) (u : Sequence) (us : List Sequence) :
    ∃ pre, assembleCappedBodies gaps i (u :: us) = pre ++ [.P] := by
  induction us generalizing i u with
  | nil =>
    exact ⟨List.replicate (gaps i) .P ++ .P :: u,
      by simp only [assembleCappedBodies, capWord, List.append_nil, List.cons_append, List.append_assoc]⟩
  | cons v vs ih =>
    obtain ⟨pre, heq⟩ := ih (i + 1) v
    exact ⟨List.replicate (gaps i) .P ++ capWord u ++ pre,
      by rw [assembleCappedBodies, heq]; simp only [List.append_assoc]⟩

namespace ConstructionParameters

theorem reductionWord_ends_P (p : ConstructionParameters) (items bulkLengths : List ℕ) (gaps : ℕ → ℕ) :
    ∃ pre, p.reductionWord items bulkLengths gaps = pre ++ [.P] := by
  obtain ⟨u, us, hbodies⟩ : ∃ u us, p.reductionUnitBodies items bulkLengths = u :: us := by
    exact ⟨[.H], _, rfl⟩
  obtain ⟨pre, heq⟩ := assembleCappedBodies_ends_P gaps 0 u us
  refine ⟨[.H, .P] ++ pre, ?_⟩
  rw [reductionWord, assembleReductionWord, hbodies, heq]
  exact (List.append_assoc _ _ _).symm

end ConstructionParameters

end ProteinFolding.Tetrahedral
