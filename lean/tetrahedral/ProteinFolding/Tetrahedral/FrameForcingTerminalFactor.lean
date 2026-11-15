import ProteinFolding.Tetrahedral.FrameForcingTerminalWord
import ProteinFolding.Tetrahedral.FrameForcingFrameVertices

/-! A nonframe H whose geometric H-neighbours lie strictly inside one
actual frame factor has no H chain-neighbour. -/

namespace ProteinFolding.Tetrahedral

theorem oct_neighbours_of_lower_bound (m : ℕ) (d : Fin 4) (c : Site)
    (word : Sequence) (site : ℕ → Site)
    (h : ∀ q, -octRadius m - 1 ≤ tetraCoordinate m q.val d → tetrahedralLattice.Adj c q →
      ∃ r, 1 ≤ r ∧ r + 1 < word.length ∧ q = site r) :
    ∀ q ∈ octahedron m, tetrahedralLattice.Adj c q →
      ∃ r, 1 ≤ r ∧ r + 1 < word.length ∧ q = site r := by
  intro q hq hadj
  apply h q _ hadj
  have hbound := ((mem_octahedron m q).mp hq d).1
  have heq : -octRadius m - 1 = -(2 * (m : ℤ) - 1) := by dsimp [octRadius]; omega
  rw [heq]
  exact hbound

theorem H_in_factor_support_of_index (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m) (pre word post : Sequence)
    (heq : S = pre ++ word ++ post) (i : Fin S.length) (hH : S.get i = .H)
    (hlo : pre.length ≤ i.val) (hhi : i.val < pre.length + word.length) :
    f.pos i ∈ hSupport word (OctWordPath.ofFoldOccurrence f m hsupport pre word post heq).toFold := by
  let P := OctWordPath.ofFoldOccurrence f m hsupport pre word post heq
  let r := i.val - pre.length
  have hr : r < word.length := by dsimp [r]; omega
  have hind : pre.length + r = i.val := by dsimp [r]; omega
  have hget := word_factor_getElem S pre word post heq r hr
  rw [hind] at hget
  have hHi : S[i.val]? = some .H := List.getElem?_eq_some_iff.mpr ⟨i.isLt, hH⟩
  have hlocal : word[r]? = some .H := hget.symm.trans hHi
  have hmem := P.site_mem_Hsupport r hlocal
  have hsite : P.site r = f.pos i := by
    change foldSiteAt f (pre.length + r) = f.pos i
    rw [hind, foldSiteAt_eq f i.val i.isLt]
  rw [hsite] at hmem
  exact hmem

theorem H_no_chain_neighbour_of_factor_neighbours (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m) (pre word post : Sequence)
    (heq : S = pre ++ word ++ post) (c : Site)
    (hnotFrame : c ∉ hSupport word (OctWordPath.ofFoldOccurrence f m hsupport pre word post heq).toFold)
    (hneighbours : ∀ q ∈ octahedron m, tetrahedralLattice.Adj c q →
      ∃ r, 1 ≤ r ∧ r + 1 < word.length ∧ q = (OctWordPath.ofFoldOccurrence f m hsupport pre word post heq).site r)
    (i : Fin S.length) (hH : S.get i = .H) (hic : f.pos i = c) :
    ∀ j : Fin S.length, S.get j = .H → i.val + 1 ≠ j.val ∧ j.val + 1 ≠ i.val := by
  have hlen : pre.length + word.length ≤ S.length := by
    rw [heq, List.length_append, List.length_append]
    omega
  have hbad (j : Fin S.length) (hj : S.get j = .H)
      (hnear : i.val + 1 = j.val ∨ j.val + 1 = i.val) : False := by
    have hq : f.pos j ∈ octahedron m := by
      rw [← hsupport]
      exact H_position_in_hSupport S f j hj
    have hadj : tetrahedralLattice.Adj c (f.pos j) := by
      rw [← hic]
      rcases hnear with h | h
      · exact f.consecutive i j h
      · exact (f.consecutive j i h).symm
    obtain ⟨r, hrlo, hrhi, hsite⟩ := hneighbours (f.pos j) hq hadj
    change f.pos j = foldSiteAt f (pre.length + r) at hsite
    rw [foldSiteAt_eq f _ (by omega)] at hsite
    have hjIndex := congrArg Fin.val (f.injective_pos hsite)
    change j.val = pre.length + r at hjIndex
    have hmem := H_in_factor_support_of_index S f m hsupport pre word post heq i hH (by omega) (by omega)
    rw [hic] at hmem
    exact hnotFrame hmem
  intro j hj
  exact ⟨fun h => hbad j hj (Or.inl h), fun h => hbad j hj (Or.inr h)⟩

theorem first_of_factor_corner (S lastPre : Sequence) (hlast : S = lastPre ++ [.P])
    (f : Fold tetrahedralLattice S.length) (m : ℕ) (hsupport : hSupport S f = octahedron m)
    (hvertices : (phpIndices S).image f.pos = octVertices m)
    (pre word post : Sequence) (heq : S = pre ++ word ++ post) (c : Site)
    (hcOct : c ∈ octahedron m) (hcNotVertex : c ∉ octVertices m)
    (hcNotFrame : c ∉ hSupport word (OctWordPath.ofFoldOccurrence f m hsupport pre word post heq).toFold)
    (hneighbours : ∀ q ∈ octahedron m, tetrahedralLattice.Adj c q →
      ∃ r, 1 ≤ r ∧ r + 1 < word.length ∧ q = (OctWordPath.ofFoldOccurrence f m hsupport pre word post heq).site r) :
    foldSiteAt f 0 = c := by
  have hcH : c ∈ hSupport S f := by rw [hsupport]; exact hcOct
  obtain ⟨i, hi, hic⟩ := (mem_hSupport S f c).mp hcH
  have hnotPHP : ¬ IsPHPMonomer S i := by
    intro hphp
    have hidx : i ∈ phpIndices S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hphp⟩
    have hcVertex : c ∈ octVertices m := by
      rw [← hvertices]
      exact Finset.mem_image.mpr ⟨i, hidx, hic⟩
    exact hcNotVertex hcVertex
  have hnoH := H_no_chain_neighbour_of_factor_neighbours S f m hsupport pre word post heq c
    hcNotFrame hneighbours i hi hic
  have hiZero := H_first_of_no_H_neighbours S lastPre hlast i hi hnotPHP hnoH
  have hzero : 0 < S.length := by have hib := i.isLt; omega
  rw [foldSiteAt_eq f 0 hzero]
  have heqIndex : (⟨0, hzero⟩ : Fin S.length) = i := Fin.ext hiZero.symm
  rw [heqIndex]
  exact hic

end ProteinFolding.Tetrahedral
