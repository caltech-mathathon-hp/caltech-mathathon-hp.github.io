import ProteinFolding.Tetrahedral.FrameForcingGaps
import ProteinFolding.Tetrahedral.FoldRigidity

/-! Extracting the frame's local paths from an actual fold and literal word.
All intermediate P sites are outside the octahedron because its H support is full. -/

namespace ProteinFolding.Tetrahedral

structure OctWordPath (m : ℕ) (word : Sequence) where
  site : ℕ → Site
  adjacent : ∀ i, i + 1 < word.length → tetrahedralLattice.Adj (site i) (site (i + 1))
  injective : ∀ i, i < word.length → ∀ j, j < word.length → site i = site j → i = j
  H_mem : ∀ i, i < word.length → word[i]? = some .H → site i ∈ octahedron m
  P_out : ∀ i, i < word.length → word[i]? = some .P → site i ∉ octahedron m

theorem word_factor_getElem (whole pre word suffix : Sequence)
    (heq : whole = pre ++ word ++ suffix) (i : ℕ) (hi : i < word.length) :
    whole[pre.length + i]? = word[i]? := by
  rw [heq, List.append_assoc, List.getElem?_append_right (by omega)]
  rw [show pre.length + i - pre.length = i by omega]
  exact List.getElem?_append_left hi

noncomputable def foldSiteAt {S : Sequence} (f : Fold tetrahedralLattice S.length) (i : ℕ) : Site :=
  if hi : i < S.length then f.pos ⟨i, hi⟩ else origin

theorem foldSiteAt_eq {S : Sequence} (f : Fold tetrahedralLattice S.length) (i : ℕ)
    (hi : i < S.length) : foldSiteAt f i = f.pos ⟨i, hi⟩ := by
  rw [foldSiteAt, dif_pos hi]

noncomputable def OctWordPath.ofFoldOccurrence {S : Sequence}
    (f : Fold tetrahedralLattice S.length) (m : ℕ)
    (hsupport : hSupport S f = octahedron m) (pre word suffix : Sequence)
    (heq : S = pre ++ word ++ suffix) : OctWordPath m word where
  site := fun i => foldSiteAt f (pre.length + i)
  adjacent := by
    intro i hi
    have hlen : pre.length + word.length ≤ S.length := by rw [heq, List.length_append, List.length_append]; omega
    rw [foldSiteAt_eq f _ (by omega), foldSiteAt_eq f _ (by omega)]
    exact f.consecutive _ _ (by change pre.length + i + 1 = pre.length + (i + 1); omega)
  injective := by
    intro i hi j hj hsite
    have hlen : pre.length + word.length ≤ S.length := by rw [heq, List.length_append, List.length_append]; omega
    rw [foldSiteAt_eq f _ (by omega), foldSiteAt_eq f _ (by omega)] at hsite
    have h := congrArg Fin.val (f.injective_pos hsite)
    change pre.length + i = pre.length + j at h
    omega
  H_mem := by
    intro i hi hH
    have hlen : pre.length + word.length ≤ S.length := by rw [heq, List.length_append, List.length_append]; omega
    have hletter : S[pre.length + i]? = some .H := (word_factor_getElem S pre word suffix heq i hi).trans hH
    obtain ⟨hbound, hletter⟩ := List.getElem?_eq_some_iff.mp hletter
    rw [foldSiteAt_eq f _ hbound, ← hsupport]
    exact H_position_in_hSupport S f _ hletter
  P_out := by
    intro i hi hP
    have hletter : S[pre.length + i]? = some .P := (word_factor_getElem S pre word suffix heq i hi).trans hP
    obtain ⟨hbound, hletter⟩ := List.getElem?_eq_some_iff.mp hletter
    rw [foldSiteAt_eq f _ hbound, ← hsupport]
    exact P_position_not_in_hSupport S f _ hletter

def OctWordPath.factor {m : ℕ} {whole : Sequence} (P : OctWordPath m whole)
    (pre word suffix : Sequence) (heq : whole = pre ++ word ++ suffix) : OctWordPath m word where
  site := fun i => P.site (pre.length + i)
  adjacent := by
    intro i hi
    have hlen : pre.length + word.length ≤ whole.length := by rw [heq, List.length_append, List.length_append]; omega
    have h := P.adjacent (pre.length + i) (by omega)
    simpa only [Nat.add_assoc] using h
  injective := by
    intro i hi j hj hsite
    have hlen : pre.length + word.length ≤ whole.length := by rw [heq, List.length_append, List.length_append]; omega
    have h := P.injective _ (by omega) _ (by omega) hsite
    omega
  H_mem := by
    intro i hi hH
    have hletter := (word_factor_getElem whole pre word suffix heq i hi).trans hH
    obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hletter
    exact P.H_mem _ hbound hletter
  P_out := by
    intro i hi hP
    have hletter := (word_factor_getElem whole pre word suffix heq i hi).trans hP
    obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hletter
    exact P.P_out _ hbound hletter

theorem OctWordPath.PHP_vertex {m : ℕ} {word : Sequence} (P : OctWordPath m word)
    (i : ℕ) (hi : 0 < i) (hir : i + 1 < word.length)
    (hleft : word[i - 1]? = some .P) (hH : word[i]? = some .H)
    (hright : word[i + 1]? = some .P) : P.site i ∈ octVertices m := by
  have hHmem := P.H_mem i (by omega) hH
  have hLout := P.P_out (i - 1) (by omega) hleft
  have hRout := P.P_out (i + 1) hir hright
  have hLadj : tetrahedralLattice.Adj (P.site i) (P.site (i - 1)) := by
    have h := P.adjacent (i - 1) (by omega)
    have heq : i - 1 + 1 = i := by omega
    rw [heq] at h
    exact h.symm
  have hRadj := P.adjacent i hir
  apply two_dangling_implies_vertex m hHmem
  rw [octDanglingDirections_card_eq_external]
  apply Finset.one_lt_card.mpr
  refine ⟨P.site (i - 1), Finset.mem_filter.mpr ⟨(mem_neighbours _ _).mpr hLadj, hLout⟩,
    P.site (i + 1), Finset.mem_filter.mpr ⟨(mem_neighbours _ _).mpr hRadj, hRout⟩, ?_⟩
  intro heq
  have h := P.injective (i - 1) (by omega) (i + 1) hir heq
  omega

def frameHOffset (gaps : List ℕ) (j : ℕ) : ℕ :=
  ((gaps.take j).map (fun k => k + 1)).sum

theorem frameHOffset_zero (gaps : List ℕ) : frameHOffset gaps 0 = 0 := by simp [frameHOffset]

theorem frameHOffset_cons_succ (k : ℕ) (gaps : List ℕ) (j : ℕ) :
    frameHOffset (k :: gaps) (j + 1) = k + 1 + frameHOffset gaps j := by
  simp only [frameHOffset, List.take_succ_cons, List.map_cons, List.sum_cons]

theorem frameHOffset_next (gaps : List ℕ) (j : ℕ) (hj : j < gaps.length) :
    frameHOffset gaps (j + 1) = frameHOffset gaps j + gaps[j] + 1 := by
  induction gaps generalizing j with
  | nil => simp at hj
  | cons k gaps ih =>
    cases j with
    | zero => simp [frameHOffset]
    | succ j =>
      have hj' : j < gaps.length := by simp only [List.length_cons] at hj; omega
      simp only [frameHOffset_cons_succ, List.getElem_cons_succ]
      rw [ih j hj']
      omega

theorem frameGapWord_cons (k : ℕ) (gaps : List ℕ) :
    frameGapWord (k :: gaps) = .H :: (List.replicate k .P ++ frameGapWord gaps) := by
  simp only [frameGapWord, frameGapTail, List.flatMap_cons, List.append_assoc, List.singleton_append]

theorem frameGapWord_H_at_offset (gaps : List ℕ) (j : ℕ) (hj : j ≤ gaps.length) :
    (frameGapWord gaps)[frameHOffset gaps j]? = some .H := by
  induction gaps generalizing j with
  | nil =>
    have hjzero : j = 0 := by simpa using hj
    subst j
    rfl
  | cons k gaps ih =>
    cases j with
    | zero => simp [frameHOffset_zero, frameGapWord]
    | succ j =>
      have hj' : j ≤ gaps.length := by simp only [List.length_cons] at hj; omega
      rw [frameHOffset_cons_succ, frameGapWord_cons]
      rw [show k + 1 + frameHOffset gaps j = (k + frameHOffset gaps j) + 1 by omega]
      rw [List.getElem?_cons_succ, List.getElem?_append_right (by simp)]
      simpa using ih j hj'

theorem frameGapWord_P_at_gap (gaps : List ℕ) (j : ℕ) (hj : j < gaps.length)
    (r : ℕ) (hr : 0 < r) (hrk : r < gaps[j] + 1) :
    (frameGapWord gaps)[frameHOffset gaps j + r]? = some .P := by
  induction gaps generalizing j with
  | nil => simp at hj
  | cons k gaps ih =>
    cases j with
    | zero =>
      have hrk' : r ≤ k := by simpa only [List.getElem_cons_zero] using (show r ≤ (k :: gaps)[0] by omega)
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      rw [frameHOffset_zero, Nat.zero_add, frameGapWord_cons, List.getElem?_cons_succ,
        List.getElem?_append_left (by simp only [List.length_replicate]; omega)]
      exact List.getElem?_replicate_of_lt (by omega)
    | succ j =>
      have hj' : j < gaps.length := by simp only [List.length_cons] at hj; omega
      have hrk' : r < gaps[j] + 1 := by simpa only [List.getElem_cons_succ] using hrk
      rw [frameHOffset_cons_succ, frameGapWord_cons]
      rw [show k + 1 + frameHOffset gaps j + r = (k + (frameHOffset gaps j + r)) + 1 by omega]
      rw [List.getElem?_cons_succ, List.getElem?_append_right (by simp)]
      simpa using ih j hj' hrk'

theorem OctWordPath.frameHop {m k : ℕ} {word : Sequence} (P : OctWordPath m word)
    (a : ℕ) (hstart : word[a]? = some .H) (hend : word[a + k + 1]? = some .H)
    (hout : ∀ r, 0 < r → r < k + 1 → word[a + r]? = some .P) :
    OctFrameHop m k (P.site a) (P.site (a + k + 1)) := by
  have ha : a < word.length := (List.getElem?_eq_some_iff.mp hstart).choose
  have he : a + k + 1 < word.length := (List.getElem?_eq_some_iff.mp hend).choose
  refine ⟨P.H_mem a ha hstart, P.H_mem _ he hend, ?_⟩
  by_cases hk : k = 0
  · rw [if_pos hk]
    simpa only [hk, Nat.add_zero] using P.adjacent a (by omega)
  · rw [if_neg hk]
    let L := OctExteriorLink.ofPath (m := m) (n := k + 1) (fun r => P.site (a + r)) (by omega)
      (by intro r hr; simpa only [Nat.add_assoc] using P.adjacent (a + r) (by omega))
      (by simpa using P.H_mem a ha hstart)
      (by simpa only [Nat.add_assoc] using P.H_mem _ he hend)
      (by intro r hr hrk; exact P.P_out _ (by omega) (hout r hr hrk))
    exact ⟨L, by rfl, by change P.site (a + (k + 1)) = P.site (a + k + 1); rw [Nat.add_assoc]⟩

theorem OctWordPath.frameChain {m : ℕ} {gaps : List ℕ} (P : OctWordPath m (frameGapWord gaps)) :
    OctFrameChain m gaps (fun j => P.site (frameHOffset gaps j)) := by
  intro j hj
  have hnext := frameHOffset_next gaps j hj
  have hstart := frameGapWord_H_at_offset gaps j (by omega)
  have hend : (frameGapWord gaps)[frameHOffset gaps j + gaps[j] + 1]? = some .H := by
    rw [← hnext]
    exact frameGapWord_H_at_offset gaps (j + 1) (by omega)
  have hhop := P.frameHop (k := gaps[j]) (frameHOffset gaps j) hstart hend
    (fun r hr hrk => frameGapWord_P_at_gap gaps j hj r hr hrk)
  simpa only [hnext] using hhop

theorem frameGapWord_length (gaps : List ℕ) :
    (frameGapWord gaps).length = 1 + frameHOffset gaps gaps.length := by
  induction gaps with
  | nil => rfl
  | cons k gaps ih =>
    rw [frameGapWord_cons]
    simp only [List.length_cons, List.length_append, List.length_replicate,
      frameHOffset_cons_succ, ih]
    omega

theorem frameHOffset_pos_of_nonempty (gaps : List ℕ) (hne : gaps ≠ []) :
    0 < frameHOffset gaps gaps.length := by
  cases gaps with
  | nil => contradiction
  | cons k gaps =>
    simp only [List.length_cons, frameHOffset_cons_succ]
    omega

end ProteinFolding.Tetrahedral

