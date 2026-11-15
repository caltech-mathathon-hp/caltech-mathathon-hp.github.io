import ProteinFolding.Tetrahedral.OctahedralLinkAdvance
import Mathlib.Tactic.NormNum

/-! Local frame hops and the equality propagation used to force a frame edge.
Hop data consists only of H endpoints and the actual intervening exterior path. -/

namespace ProteinFolding.Tetrahedral

def FrameGapAllowed (k : ℕ) : Prop := k = 0 ∨ k = 3 ∨ k = 6 ∨ k = 10

def frameGapAdvance (k : ℕ) : ℕ :=
  if k = 0 then 1 else if k % 2 = 0 then k - 3 else k - 1

def OctFrameHop (m k : ℕ) (p q : Site) : Prop :=
  p ∈ octahedron m ∧ q ∈ octahedron m ∧
    if k = 0 then tetrahedralLattice.Adj p q else
      ∃ L : OctExteriorLink m (k + 1), L.site 0 = p ∧ L.site (k + 1) = q

theorem frameHop_advance_bound {m k : ℕ} {p q : Site}
    (hallow : FrameGapAllowed k) (hop : OctFrameHop m k p q)
    {a b : Fin 4} (hab : a ≠ b) :
    octEdgeHeight4 m a b q - octEdgeHeight4 m a b p ≤ 4 * (frameGapAdvance k : ℤ) := by
  rcases hallow with rfl | rfl | rfl | rfl
  · have hadj : tetrahedralLattice.Adj p q := by simpa only [OctFrameHop, if_pos rfl] using hop.2.2
    simpa only [frameGapAdvance, if_pos rfl, Nat.cast_one, mul_one] using
      (octEdgeHeight4_adj_bounds m a b hadj).2
  · obtain ⟨L, hs, he⟩ := hop.2.2
    have h := exterior_link_advance_bound L hab
    simpa only [hs, he, frameGapAdvance] using h
  · obtain ⟨L, hs, he⟩ := hop.2.2
    have h := exterior_even_P_link_advance_bound L hab (by decide)
    simpa only [hs, he, frameGapAdvance] using h
  · obtain ⟨L, hs, he⟩ := hop.2.2
    have h := exterior_even_P_link_advance_bound L hab (by decide)
    simpa only [hs, he, frameGapAdvance] using h

theorem frameHop_maximizer_index {m k i : ℕ} (hm : 1 ≤ m) {p q : Site}
    (hallow : FrameGapAllowed k) (hop : OctFrameHop m k p q) (F : OctEdgeFrame)
    (hi : i < 2 * m - 1) (hstart : p = octEdgeZigzag m F i)
    (hmax : octEdgeHeight4 m F.a F.b q - octEdgeHeight4 m F.a F.b p =
      4 * (frameGapAdvance k : ℤ)) :
    i + frameGapAdvance k < 2 * m - 1 ∧
      q = octEdgeZigzag m F (i + frameGapAdvance k) := by
  rcases hallow with rfl | rfl | rfl | rfl
  · have hadj : tetrahedralLattice.Adj p q := hop.2.2
    have hheight : octEdgeHeight4 m F.a F.b q = octEdgeHeight4 m F.a F.b p + 4 := by
      norm_num [frameGapAdvance] at hmax
      omega
    have hq := height_up_step_unique m F.a F.b hadj hheight
    rw [hstart, ← octEdgeZigzag_succ] at hq
    have hb := (octEdgeHeight4_bounds m F.a F.b hop.2.1).2
    rw [hq, octEdgeZigzag_height hm F] at hb
    dsimp [octRadius] at hb
    exact ⟨by simpa only [frameGapAdvance, if_pos rfl] using (show i + 1 < 2 * m - 1 by omega),
      by simpa only [frameGapAdvance, if_pos rfl] using hq⟩
  · obtain ⟨L, hs, he⟩ := hop.2.2
    have hstartL : L.site 0 = octEdgeZigzag m F i := hs.trans hstart
    have hmaxL : octEdgeHeight4 m F.a F.b (L.site (3 + 1)) -
        octEdgeHeight4 m F.a F.b (L.site 0) = 4 * ((3 : ℤ) - 1) := by
      simpa only [hs, he, frameGapAdvance] using hmax
    obtain ⟨r, hr, hend, hindex⟩ := exterior_odd_P_link_maximiser_index hm L F (by decide) hi hstartL hmaxL
    have hrEq : r = i + frameGapAdvance 3 := by norm_num [frameGapAdvance]; omega
    rw [hrEq] at hr hend
    exact ⟨hr, he.symm.trans hend⟩
  · obtain ⟨L, hs, he⟩ := hop.2.2
    have hstartL : L.site 0 = octEdgeZigzag m F i := hs.trans hstart
    have hmaxL : octEdgeHeight4 m F.a F.b (L.site (6 + 1)) -
        octEdgeHeight4 m F.a F.b (L.site 0) = 4 * ((6 : ℤ) - 3) := by
      simpa only [hs, he, frameGapAdvance] using hmax
    obtain ⟨r, hr, hend, hindex⟩ := exterior_even_P_link_maximiser_index hm L F (by decide) hi hstartL hmaxL
    have hrEq : r = i + frameGapAdvance 6 := by norm_num [frameGapAdvance]; omega
    rw [hrEq] at hr hend
    exact ⟨hr, he.symm.trans hend⟩
  · obtain ⟨L, hs, he⟩ := hop.2.2
    have hstartL : L.site 0 = octEdgeZigzag m F i := hs.trans hstart
    have hmaxL : octEdgeHeight4 m F.a F.b (L.site (10 + 1)) -
        octEdgeHeight4 m F.a F.b (L.site 0) = 4 * ((10 : ℤ) - 3) := by
      simpa only [hs, he, frameGapAdvance] using hmax
    obtain ⟨r, hr, hend, hindex⟩ := exterior_even_P_link_maximiser_index hm L F (by decide) hi hstartL hmaxL
    have hrEq : r = i + frameGapAdvance 10 := by norm_num [frameGapAdvance]; omega
    rw [hrEq] at hr hend
    exact ⟨hr, he.symm.trans hend⟩

def OctFrameChain (m : ℕ) (gaps : List ℕ) (site : ℕ → Site) : Prop :=
  ∀ i (hi : i < gaps.length), OctFrameHop m gaps[i] (site i) (site (i + 1))

theorem frameChain_advance_bound (m : ℕ) (gaps : List ℕ) (site : ℕ → Site)
    (hallow : ∀ k ∈ gaps, FrameGapAllowed k) (hchain : OctFrameChain m gaps site)
    {a b : Fin 4} (hab : a ≠ b) :
    octEdgeHeight4 m a b (site gaps.length) - octEdgeHeight4 m a b (site 0) ≤
      4 * (((gaps.map frameGapAdvance).sum : ℕ) : ℤ) := by
  induction gaps generalizing site with
  | nil => simp
  | cons k gaps ih =>
    have hhead := frameHop_advance_bound (hallow k (by simp)) (hchain 0 (by simp)) hab
    have htail : OctFrameChain m gaps (fun i => site (i + 1)) := by
      intro i hi
      simpa only [List.getElem_cons_succ] using hchain (i + 1) (by simp only [List.length_cons]; omega)
    have hrest := ih (fun i => site (i + 1)) (fun j hj => hallow j (by simp [hj])) htail
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add]
    dsimp only at hhead hrest
    omega

/-- Equality in the total advance forces every H site to its unique edge
index. This conclusion is derived from the intervening actual paths. -/
theorem frameChain_saturated_on_edge (m : ℕ) (hm : 1 ≤ m) (gaps : List ℕ)
    (site : ℕ → Site) (hallow : ∀ k ∈ gaps, FrameGapAllowed k)
    (hchain : OctFrameChain m gaps site) (F : OctEdgeFrame) (i : ℕ)
    (hi : i < 2 * m - 1) (hstart : site 0 = octEdgeZigzag m F i)
    (hheight : octEdgeHeight4 m F.a F.b (site gaps.length) -
      octEdgeHeight4 m F.a F.b (site 0) = 4 * (((gaps.map frameGapAdvance).sum : ℕ) : ℤ)) :
    ∀ j ≤ gaps.length, i + ((gaps.take j).map frameGapAdvance).sum < 2 * m - 1 ∧
      site j = octEdgeZigzag m F (i + ((gaps.take j).map frameGapAdvance).sum) := by
  induction gaps generalizing site i with
  | nil =>
    intro j hj
    have hjzero : j = 0 := by simpa using hj
    subst j
    simpa using And.intro hi hstart
  | cons k gaps ih =>
    have hheadhop : OctFrameHop m k (site 0) (site 1) := hchain 0 (by simp)
    have hheadbound := frameHop_advance_bound (hallow k (by simp)) hheadhop F.ab
    have hallowtail : ∀ k ∈ gaps, FrameGapAllowed k := fun k hk => hallow k (by simp [hk])
    have htail : OctFrameChain m gaps (fun r => site (r + 1)) := by
      intro r hr
      simpa only [List.getElem_cons_succ] using hchain (r + 1) (by simp only [List.length_cons]; omega)
    have htailbound := frameChain_advance_bound m gaps (fun r => site (r + 1)) hallowtail htail F.ab
    dsimp only at htailbound
    simp only [Nat.zero_add] at htailbound
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add] at hheight
    have hheadmax : octEdgeHeight4 m F.a F.b (site 1) - octEdgeHeight4 m F.a F.b (site 0) =
        4 * (frameGapAdvance k : ℤ) := by omega
    obtain ⟨hinext, hnext⟩ := frameHop_maximizer_index hm (hallow k (by simp)) hheadhop F hi hstart hheadmax
    have htailmax : octEdgeHeight4 m F.a F.b (site (gaps.length + 1)) -
        octEdgeHeight4 m F.a F.b (site 1) = 4 * (((gaps.map frameGapAdvance).sum : ℕ) : ℤ) := by omega
    have hrec := ih (site := fun r => site (r + 1)) (i := i + frameGapAdvance k)
      hallowtail htail hinext hnext htailmax
    intro j hj
    cases j with
    | zero => simpa using And.intro hi hstart
    | succ j =>
      have hjtail : j ≤ gaps.length := by simp only [List.length_cons] at hj; omega
      simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, Nat.add_assoc] using hrec j hjtail

end ProteinFolding.Tetrahedral
