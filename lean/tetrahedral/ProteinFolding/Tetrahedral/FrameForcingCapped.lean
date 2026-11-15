import ProteinFolding.Tetrahedral.FrameForcingOccurrences
import ProteinFolding.Tetrahedral.FrameForcingVertices
import ProteinFolding.Tetrahedral.FrameWordCounts

/-! Capped full-budget frame parts force their actual hydrophobic positions. -/

namespace ProteinFolding.Tetrahedral

theorem capWord_length (word : Sequence) : (capWord word).length = word.length + 2 := by
  simp [capWord]

theorem capWord_get_inner (word : Sequence) (i : ℕ) (hi : i < word.length) :
    (capWord word)[i + 1]? = word[i]? := by
  rw [capWord, List.getElem?_cons_succ, List.getElem?_append_left hi]

theorem capWord_get_final_P (word : Sequence) :
    (capWord word)[word.length + 1]? = some .P := by
  rw [capWord, List.getElem?_cons_succ, List.getElem?_append_right le_rfl]
  simp

theorem capped_frame_endpoints_vertices (m : ℕ) (gaps : List ℕ)
    (P : OctWordPath m (capWord (frameGapWord gaps))) (hgaps : 0 < gaps.length)
    (hfirst : 0 < gaps[0]'(by omega))
    (hlast : 0 < gaps[gaps.length - 1]'(by omega)) :
    P.site 1 ∈ octVertices m ∧
      P.site (1 + frameHOffset gaps gaps.length) ∈ octVertices m := by
  let word := frameGapWord gaps
  have hlen : word.length = 1 + frameHOffset gaps gaps.length := frameGapWord_length gaps
  have hpos : 0 < frameHOffset gaps gaps.length := frameHOffset_pos_of_nonempty gaps (by intro h; simp [h] at hgaps)
  have hcaplen := capWord_length word
  have hstartH : word[0]? = some .H := by rfl
  have hstartP : word[1]? = some .P := by
    simpa only [frameHOffset_zero, Nat.zero_add] using
      frameGapWord_P_at_gap gaps 0 hgaps 1 (by decide) (by omega)
  have hstartPbound : 1 < word.length := (List.getElem?_eq_some_iff.mp hstartP).choose
  dsimp only [word] at hcaplen hlen hstartPbound
  have hstartVertex : P.site 1 ∈ octVertices m := by
    apply P.PHP_vertex 1 (by decide) (by omega)
    · rfl
    · exact (capWord_get_inner word 0 (by dsimp only [word]; omega)).trans hstartH
    · exact (capWord_get_inner word 1 hstartPbound).trans hstartP
  have hj : gaps.length - 1 < gaps.length := by omega
  have hnext := frameHOffset_next gaps (gaps.length - 1) hj
  have hjnext : gaps.length - 1 + 1 = gaps.length := by omega
  rw [hjnext] at hnext
  have hendP : word[frameHOffset gaps gaps.length - 1]? = some .P := by
    have h := frameGapWord_P_at_gap gaps (gaps.length - 1) hj
      gaps[gaps.length - 1] hlast (by omega)
    have heq : frameHOffset gaps (gaps.length - 1) + gaps[gaps.length - 1] =
        frameHOffset gaps gaps.length - 1 := by omega
    simpa only [heq] using h
  have hendPbound : frameHOffset gaps gaps.length - 1 < word.length :=
    (List.getElem?_eq_some_iff.mp hendP).choose
  have hendH := frameGapWord_H_at_offset gaps gaps.length le_rfl
  refine ⟨hstartVertex, ?_⟩
  apply P.PHP_vertex (1 + frameHOffset gaps gaps.length) (by omega) (by omega)
  · rw [show 1 + frameHOffset gaps gaps.length - 1 = (frameHOffset gaps gaps.length - 1) + 1 by omega]
    exact (capWord_get_inner word _ hendPbound).trans hendP
  · rw [show 1 + frameHOffset gaps gaps.length = frameHOffset gaps gaps.length + 1 by omega]
    exact (capWord_get_inner word _ (by dsimp only [word]; omega)).trans hendH
  · rw [show 1 + frameHOffset gaps gaps.length + 1 = word.length + 1 by dsimp only [word]; omega]
    exact capWord_get_final_P word

theorem capped_frame_forced_edge (m : ℕ) (hm : 2 ≤ m) (gaps : List ℕ)
    (P : OctWordPath m (capWord (frameGapWord gaps))) (hgaps : 0 < gaps.length)
    (hfirst : 0 < gaps[0]'(by omega))
    (hlast : 0 < gaps[gaps.length - 1]'(by omega))
    (hallow : ∀ k ∈ gaps, FrameGapAllowed k)
    (hbudget : (gaps.map frameGapAdvance).sum = 2 * m - 2) :
    ∃ F : OctEdgeFrame, P.site 1 = octEdgeStart m F ∧
      (∀ j ≤ gaps.length, P.site (1 + frameHOffset gaps j) =
        octEdgeZigzag m F (((gaps.take j).map frameGapAdvance).sum)) ∧
      P.site (frameGapWord gaps).length = octEdgeZigzag m F (2 * m - 2) := by
  have hfactor : capWord (frameGapWord gaps) = [.P] ++ frameGapWord gaps ++ [.P] := by
    simp only [capWord, List.cons_append, List.nil_append]
  let Q := P.factor [.P] (frameGapWord gaps) [.P] hfactor
  have hchain := Q.frameChain
  obtain ⟨hp, hq⟩ := capped_frame_endpoints_vertices m gaps P hgaps hfirst hlast
  have hlen := frameGapWord_length gaps
  have hcaplen := capWord_length (frameGapWord gaps)
  have hpos := frameHOffset_pos_of_nonempty gaps (by intro h; simp [h] at hgaps)
  have hp' : Q.site (frameHOffset gaps 0) ∈ octVertices m := by
    simpa only [Q, OctWordPath.factor, List.length_singleton, frameHOffset_zero, Nat.add_zero] using hp
  have hq' : Q.site (frameHOffset gaps gaps.length) ∈ octVertices m := hq
  have hne : Q.site (frameHOffset gaps 0) ≠ Q.site (frameHOffset gaps gaps.length) := by
    intro heq
    have heq' : P.site 1 = P.site (1 + frameHOffset gaps gaps.length) := by
      simpa only [Q, OctWordPath.factor, List.length_singleton, frameHOffset_zero, Nat.add_zero] using heq
    have h := P.injective 1 (by omega) _ (by omega) heq'
    omega
  obtain ⟨F, hs, hforced, hend⟩ := frameChain_between_vertices m hm gaps
    (fun j => Q.site (frameHOffset gaps j)) hallow hchain hp' hq' hne hbudget
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [Q, OctWordPath.factor, List.length_singleton, frameHOffset_zero, Nat.add_zero] using hs
  · intro j hj
    exact hforced j hj
  · simpa only [Q, OctWordPath.factor, List.length_singleton, hlen] using hend

end ProteinFolding.Tetrahedral
