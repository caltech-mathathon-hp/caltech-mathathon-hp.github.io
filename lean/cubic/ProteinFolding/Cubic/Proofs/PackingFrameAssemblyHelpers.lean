import ProteinFolding.Cubic.Proofs.PackingFrameRoutingDisjoint
import ProteinFolding.Cubic.Proofs.PackingStripAttachments
import ProteinFolding.Cubic.Proofs.PackingItemChain
import ProteinFolding.Cubic.Proofs.PackingCountCompleteness

/-! Final assembly lemmas for the literal prefix, wall and item words. -/

namespace ProteinFolding.CubicPackingFrameAssemblyHelpers

open CubicPacking CubicPackingLift CubicCertificates CubicPackingRouting
open CubicPackingItems CubicPackingFrameRoutingDisjoint

theorem appendWord_exists_pos {S T : Sequence} (f : Fold cubicLattice S.length)
    (g : Fold cubicLattice T.length) hdisjoint hseam (p : Site) :
    (∃ i, (Fold.appendWord f g hdisjoint hseam).pos i = p) ↔
      (∃ i, f.pos i = p) ∨ ∃ j, g.pos j = p := by
  constructor
  · rintro ⟨i, hi⟩
    by_cases hil : i.val < S.length
    · let j : Fin S.length := ⟨i.val, hil⟩
      have he : i = Fold.leftWordIndex S T j := Fin.ext rfl
      exact Or.inl ⟨j, by simpa only [he, Fold.appendWord_pos_left] using hi⟩
    · have hil' := i.isLt
      simp only [List.length_append] at hil'
      let j : Fin T.length := ⟨i.val - S.length, by omega⟩
      have he : i = Fold.rightWordIndex S T j := by
        apply Fin.ext
        change i.val = S.length + (i.val - S.length)
        omega
      exact Or.inr ⟨j, by simpa only [he, Fold.appendWord_pos_right] using hi⟩
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact ⟨Fold.leftWordIndex S T i, by simpa only [Fold.appendWord_pos_left] using hi⟩
    · exact ⟨Fold.rightWordIndex S T j, by simpa only [Fold.appendWord_pos_right] using hj⟩

theorem appendWord_disjoint_from_third {S T U : Sequence}
    (f : Fold cubicLattice S.length) (g : Fold cubicLattice T.length)
    (h : Fold cubicLattice U.length) hdisjoint hseam
    (hfh : ∀ i j, f.pos i ≠ h.pos j) (hgh : ∀ i j, g.pos i ≠ h.pos j) :
    ∀ i j, (Fold.appendWord f g hdisjoint hseam).pos i ≠ h.pos j := by
  intro i j he
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ :=
    (appendWord_exists_pos f g hdisjoint hseam _).mp ⟨i, rfl⟩
  · exact hfh k j (hk.trans he)
  · exact hgh k j (hk.trans he)

theorem appendWord_last {S T : Sequence}
    (f : Fold cubicLattice S.length) (g : Fold cubicLattice T.length) hdisjoint hseam
    (hT : 0 < T.length) (i : Fin (S ++ T).length) (hi : i.val + 1 = (S ++ T).length) :
    ∃ j : Fin T.length, j.val + 1 = T.length ∧
      (Fold.appendWord f g hdisjoint hseam).pos i = g.pos j := by
  have hv : i.val + 1 = S.length + T.length := by simpa only [List.length_append] using hi
  let j : Fin T.length := ⟨i.val - S.length, by omega⟩
  have he : i = Fold.rightWordIndex S T j := by
    apply Fin.ext
    change i.val = S.length + (i.val - S.length)
    omega
  refine ⟨j, ?_, ?_⟩
  · change i.val - S.length + 1 = T.length
    omega
  · rw [he, Fold.appendWord_pos_right]

theorem appendWord_H_inside {S T : Sequence}
    (f : Fold cubicLattice S.length) (g : Fold cubicLattice T.length) hdisjoint hseam
    (a : Site) (n : ℕ)
    (hf : ∀ i, S.get i = .H → f.pos i ∈ cube a n)
    (hg : ∀ i, T.get i = .H → g.pos i ∈ cube a n) :
    ∀ i, (S ++ T).get i = .H → (Fold.appendWord f g hdisjoint hseam).pos i ∈ cube a n := by
  intro i hi
  have hp : (Fold.appendWord f g hdisjoint hseam).pos i ∈
      hydrophobicSites (S ++ T) (Fold.appendWord f g hdisjoint hseam) := ⟨i, hi, rfl⟩
  rw [appendWord_hydrophobicSites] at hp
  rcases hp with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · rw [← he]
    exact hf j hj
  · rw [← he]
    exact hg j hj

/-- Pairwise full-site separation and the two backbone seams suffice for
the complete frozen frame word. -/
theorem frameWord_perfect_of_three_folds (q Q : ℕ) (items : List ℕ)
    (hq : 0 < q) (hsum : items.sum = q * (4 * Q))
    (prefixFold : Fold cubicLattice (prefixWord q Q).length)
    (wall : Fold cubicLattice (walls q Q).length)
    (item : Fold cubicLattice (itemWords q Q items).length)
    (hwall : 0 < (walls q Q).length)
    (hpw : ∀ i j, prefixFold.pos i ≠ wall.pos j)
    (hpi : ∀ i j, prefixFold.pos i ≠ item.pos j)
    (hwi : ∀ i j, wall.pos i ≠ item.pos j)
    (hspw : ∀ i j, i.val + 1 = (prefixWord q Q).length → j.val = 0 →
      cubicLattice.Adj (prefixFold.pos i) (wall.pos j))
    (hswi : ∀ i j, i.val + 1 = (walls q Q).length → j.val = 0 →
      cubicLattice.Adj (wall.pos i) (item.pos j))
    (hpH : ∀ i, (prefixWord q Q).get i = .H →
      prefixFold.pos i ∈ cube (fun _ => 0) (side q Q))
    (hwH : ∀ i, (walls q Q).get i = .H →
      wall.pos i ∈ cube (fun _ => 0) (side q Q))
    (hiH : ∀ i, (itemWords q Q items).get i = .H →
      item.pos i ∈ cube (fun _ => 0) (side q Q)) :
    PerfectHPStringFold (frameWord q Q items) (side q Q) := by
  let pw := Fold.appendWord prefixFold wall hpw hspw
  have hpwi : ∀ i j, pw.pos i ≠ item.pos j :=
    appendWord_disjoint_from_third prefixFold wall item hpw hspw hpi hwi
  have hspwi : ∀ i j, i.val + 1 = (prefixWord q Q ++ walls q Q).length → j.val = 0 →
      cubicLattice.Adj (pw.pos i) (item.pos j) := by
    intro i j hi hj
    obtain ⟨k, hk, he⟩ := appendWord_last prefixFold wall hpw hspw hwall i hi
    change cubicLattice.Adj ((Fold.appendWord prefixFold wall hpw hspw).pos i) (item.pos j)
    rw [he]
    exact hswi k j hk hj
  let f := Fold.appendWord pw item hpwi hspwi
  have hin : ∀ i, ((prefixWord q Q ++ walls q Q) ++ itemWords q Q items).get i = .H →
      f.pos i ∈ cube (fun _ => 0) (side q Q) :=
    appendWord_H_inside pw item hpwi hspwi _ _
      (appendWord_H_inside prefixFold wall hpw hspw _ _ hpH hwH) hiH
  have heq : frameWord q Q items = (prefixWord q Q ++ walls q Q) ++ itemWords q Q items := by
    simp only [frameWord, List.append_assoc]
  let finalFold := f.onLength (congrArg List.length heq)
  apply frameWord_perfect_of_inside q Q items hq hsum finalFold
  change hydrophobicSites _ (f.onLength _) ⊆ _
  rw [CubicPackingPrefixFold.onWord_hsites f heq]
  rintro p ⟨i, hi, rfl⟩
  exact hin i hi

theorem prefixFold_routingConnector_disjoint {q Q Y : ℕ} {items : List ℕ}
    {hd : 2 ≤ depth q Q} {heven : depth q Q % 2 = 0}
    (w : CubicPackingPrefixFold.Witness q Q hd heven)
    (L : Layout (depth q Q) items) (R : L.Routing Y)
    (hY : (Y : ℤ) ≤ (depth q Q : ℤ) - alpha Q)
    (j : Fin items.length) : ∀ i k, w.fold.pos i ≠ (R.connector j).pos k := by
  unfold Layout.Routing.connector
  split_ifs with hj
  · exact witness_initialConnector_disjoint w 5 R.initialRadius Y (L.startPort j)
      (depth q Q + 2) (by decide) R.initialPositive
      (by have := L.startPort_bounds j; omega) (L.startPort_bounds j).2 hY (R.initialLength j hj)
  · exact witness_portConnector_disjoint w (L.endPort (L.previous j (by omega)))
      (L.startPort j) (5 + j.val) (R.radius j (by omega)) (depth q Q + 2)
      (by omega) (R.radiusPositive j (by omega)) (L.endPort_ne_startPort _ _)
      (L.endPort_bounds _).2 (L.startPort_bounds j).2 (R.radiusLength j (by omega))

theorem itemChain_disjoint_of_parts {d q Q Y N : ℕ} {items : List ℕ} {hd : 0 < d}
    (front : Fold cubicLattice N) (L : Layout d items) (chain : L.ChainWitness q Q Y hd)
    (hc : ∀ b i k, front.pos i ≠ (chain.routes.connector b).pos k)
    (hs : ∀ b i k, front.pos i ≠ (L.strip hd b).pos k) :
    ∀ i j, front.pos i ≠ chain.fold.pos j := by
  intro i j he
  obtain ⟨b, ⟨k, hk⟩ | ⟨k, hk⟩⟩ := (chain.sites (chain.fold.pos j)).mp ⟨j, rfl⟩
  · exact hc b i k (he.trans hk.symm)
  · exact hs b i k (he.trans hk.symm)

/-- The exact sites formula transports the local collision matrix to the
entire item chain in its original occurrence order. -/
theorem prefixFold_itemChain_disjoint {q Q Y : ℕ} {items : List ℕ}
    {hd : 2 ≤ depth q Q} {heven : depth q Q % 2 = 0}
    (w : CubicPackingPrefixFold.Witness q Q hd heven)
    (L : Layout (depth q Q) items) (chain : L.ChainWitness q Q Y (by omega))
    (hY : (Y : ℤ) ≤ (depth q Q : ℤ) - alpha Q) :
    ∀ i j, w.fold.pos i ≠ chain.fold.pos j := by
  apply itemChain_disjoint_of_parts w.fold L chain
  · exact fun b => prefixFold_routingConnector_disjoint w L chain.routes hY b
  · intro b i k
    have hb := L.bounds b
    exact prefixFold_strip_disjoint w (L.placement b).width (L.placement b).upper (L.stripEven b)
      (by omega) (by omega) i k

end ProteinFolding.CubicPackingFrameAssemblyHelpers

