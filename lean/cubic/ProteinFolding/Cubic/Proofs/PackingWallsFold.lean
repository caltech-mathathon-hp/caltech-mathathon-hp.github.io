import ProteinFolding.Cubic.Proofs.PackingGapFold
import ProteinFolding.Cubic.Proofs.PackingPrefixWallsDisjoint
import ProteinFolding.Cubic.Proofs.PackingWallGapBridgeDisjoint
import ProteinFolding.Cubic.Proofs.PackingWallGapDisjoint

/-! Literal complete wall folding, including every fixed P bridge. -/

namespace ProteinFolding.CubicPackingWalls

open CubicCertificates CubicPacking CubicPackingLift CubicPackingRouting
open CubicPackingPrefixWallsDisjoint

noncomputable def wallFold (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q) (j : Fin q) :=
  (wallUnit_fold_exists q Q hq hQ j).choose

theorem wallFold_spec (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q) (j : Fin q) :
    AttachedTo (fun _ => 0) (side q Q) (wallFold q Q hq hQ j)
      (unitOwners (depth q Q) (alpha Q) (wallTop q Q j)) ∧
    hydrophobicSites (wallUnit q Q) (wallFold q Q hq hQ j) =
      Set.range (unitOwners (depth q Q) (alpha Q) (wallTop q Q j)) ∧
    HasEnds (wallFold q Q hq hQ j)
      (point (depth q Q + 1) (wallTop q Q j - alpha Q + 1) (-1))
      (point (depth q Q + 1) (wallTop q Q j - alpha Q - 2) (-1)) :=
  (wallUnit_fold_exists q Q hq hQ j).choose_spec

theorem unitOwners_interval (d A : ℕ) (top : ℤ)
    (i : Fin (A + (d + ((2 * A + 2) + (d + A))))) :
    top - (2 * A + 2) + 1 ≤ unitOwners d A top i 1 ∧
      unitOwners d A top i 1 ≤ top := by
  cases i using Fin.addCases with
  | left i =>
    have hi := i.isLt
    simp only [unitOwners, Fin.append_left]
    dsimp [verticalFold, verticalPos, point, lineRow]
    omega
  | right i =>
    simp only [unitOwners, Fin.append_right]
    cases i using Fin.addCases with
    | left i => simp [horizontalFold, horizontalPos, point]; omega
    | right i =>
      simp only [Fin.append_right]
      cases i using Fin.addCases with
      | left i =>
        have hi := i.isLt
        simp only [Fin.append_left]
        dsimp [verticalFold, verticalPos, point, lineRow]
        omega
      | right i =>
        simp only [Fin.append_right]
        cases i using Fin.addCases with
        | left i => simp [horizontalFold, horizontalPos, point]; omega
        | right i =>
          have hi := i.isLt
          simp only [Fin.append_right]
          dsimp [verticalFold, verticalPos, point, lineRow]
          omega

theorem wallOwners_disjoint (q Q : ℕ) (j k : Fin q) (hjk : j.val < k.val) :
    ∀ i l, unitOwners (depth q Q) (alpha Q) (wallTop q Q j) i ≠
      unitOwners (depth q Q) (alpha Q) (wallTop q Q k) l := by
  intro i l he
  have hj := unitOwners_interval (depth q Q) (alpha Q) (wallTop q Q j) i
  have hk := unitOwners_interval (depth q Q) (alpha Q) (wallTop q Q k) l
  have hy := congrFun he 1
  have hdiff : ((j.val : ℤ) + 1) * beta Q ≤ (k.val : ℤ) * beta Q := by
    have h := Nat.mul_le_mul_right (beta Q) (show j.val + 1 ≤ k.val by omega)
    exact_mod_cast h
  have hb : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by dsimp [beta, alpha]; omega
  dsimp [wallTop] at hj hk hy
  rw [add_mul] at hdiff
  omega

theorem wallFolds_disjoint (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (j k : Fin q) (hjk : j.val < k.val) :
    ∀ i l, (wallFold q Q hq hQ j).pos i ≠ (wallFold q Q hq hQ k).pos l :=
  attached_folds_disjoint (fun _ => 0) (side q Q) _ _ _ _
    (wallFold_spec q Q hq hQ j).1 (wallFold_spec q Q hq hQ k).1
    (wallOwners_disjoint q Q j k hjk)

theorem wallFold_height (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (j : Fin q) (i : Fin (wallUnit q Q).length) :
    -1 ≤ (wallFold q Q hq hQ j).pos i 2 := by
  have h := attached_height_lower (fun _ => 0) (side q Q) (wallFold q Q hq hQ j) _
    (wallFold_spec q Q hq hQ j).1 0 (fun k => by rw [unitOwners_plane]) i
  omega

theorem wall_bridge_disjoint (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (j k : Fin q) : ∀ i l, (wallFold q Q hq hQ j).pos i ≠
      (unitPBridge (depth q Q) (alpha Q) (wallTop q Q k)).pos l := by
  intro i l he
  have h := wallFold_height q Q hq hQ j i
  have hz := congrFun he 2
  change _ = -2 at hz
  omega

theorem unitBridges_disjoint (q Q : ℕ) (j k : Fin q) (hjk : j.val < k.val) :
    ∀ i l, (unitPBridge (depth q Q) (alpha Q) (wallTop q Q j)).pos i ≠
      (unitPBridge (depth q Q) (alpha Q) (wallTop q Q k)).pos l := by
  intro i l he
  have hi := i.isLt
  have hl := l.isLt
  simp only [List.length_replicate] at hi hl
  have hy := congrFun he 1
  change wallTop q Q j - alpha Q - 2 - i.val = wallTop q Q k - alpha Q - 2 - l.val at hy
  have hdiff : ((j.val : ℤ) + 1) * beta Q ≤ (k.val : ℤ) * beta Q := by
    have h := Nat.mul_le_mul_right (beta Q) (show j.val + 1 ≤ k.val by omega)
    exact_mod_cast h
  have hb : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by dsimp [beta, alpha]; omega
  dsimp [wallTop] at hy
  rw [add_mul] at hdiff
  omega

def wallUnitsChainWord (q Q : ℕ) : ℕ → Sequence
  | 0 => wallUnit q Q
  | k + 1 => (wallUnitsChainWord q Q k ++ List.replicate (2 * alpha Q) .P) ++ wallUnit q Q

def UnitChainSites (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q) (k : ℕ) (p : Site) : Prop :=
  (∃ j : Fin q, j.val ≤ k ∧ ∃ i, (wallFold q Q hq hQ j).pos i = p) ∨
  (∃ j : Fin q, j.val < k ∧ ∃ i,
    (unitPBridge (depth q Q) (alpha Q) (wallTop q Q j)).pos i = p)

theorem wallFold_H_inside (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q) (j : Fin q) :
    hydrophobicSites (wallUnit q Q) (wallFold q Q hq hQ j) ⊆ cube (fun _ => 0) (side q Q) := by
  intro p hp
  rw [(wallFold_spec q Q hq hQ j).2.1] at hp
  obtain ⟨i, rfl⟩ := hp
  exact (wallFold_spec q Q hq hQ j).1.1 i

theorem wallUnitsChainWord_positive (q Q k : ℕ) (hq : 0 < q) :
    0 < (wallUnitsChainWord q Q k).length := by
  have hunit : 0 < (wallUnit q Q).length := by
    rw [wallUnit_length]
    have hd := depth_two_le q Q hq
    omega
  induction k with
  | zero => exact hunit
  | succ k ih => simp only [wallUnitsChainWord, List.length_append]; omega

theorem wallUnitsChainFold_exists (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (k : ℕ) (hk : k < q) :
    ∃ f : Fold cubicLattice (wallUnitsChainWord q Q k).length,
      HasEnds f (point (depth q Q + 1) (depth q Q - alpha Q + 1) (-1))
        (point (depth q Q + 1) (wallTop q Q ⟨k, hk⟩ - alpha Q - 2) (-1)) ∧
      (∀ i, UnitChainSites q Q hq hQ k (f.pos i)) ∧
      hydrophobicSites (wallUnitsChainWord q Q k) f ⊆ cube (fun _ => 0) (side q Q) := by
  induction k with
  | zero =>
    let j : Fin q := ⟨0, hk⟩
    refine ⟨wallFold q Q hq hQ j, ?_, ?_, wallFold_H_inside q Q hq hQ j⟩
    · simpa [j, wallTop] using (wallFold_spec q Q hq hQ j).2.2
    · intro i
      exact Or.inl ⟨j, by simp [j], i, rfl⟩
  | succ k ih =>
    obtain ⟨old, heOld, hOld, hOldH⟩ := ih (by omega)
    let j : Fin q := ⟨k, by omega⟩
    let l : Fin q := ⟨k + 1, hk⟩
    let bridge := unitPBridge (depth q Q) (alpha Q) (wallTop q Q j)
    let next := wallFold q Q hq hQ l
    have hA : 0 < alpha Q := by dsimp [alpha]; omega
    have heBridge := unitPBridge_ends (depth q Q) (alpha Q) (wallTop q Q j) hA
    have heNext := (wallFold_spec q Q hq hQ l).2.2
    have hdisOldBridge : ∀ i t, old.pos i ≠ bridge.pos t := by
      intro i t he
      rcases hOld i with ⟨a, ha, b, hb⟩ | ⟨a, ha, b, hb⟩
      · exact wall_bridge_disjoint q Q hq hQ a j b t (hb.trans he)
      · exact unitBridges_disjoint q Q a j ha b t (hb.trans he)
    have seam₁ : cubicLattice.Adj
        (point (depth q Q + 1) (wallTop q Q j - alpha Q - 2) (-1))
        (point (depth q Q + 1) (wallTop q Q j - alpha Q - 2) (-2)) := by
      change latticeDistance _ _ = 1
      rw [distance_eq]
      simp [point]
    let mid := Fold.appendWord old bridge hdisOldBridge (hasEnds_seam old bridge heOld heBridge seam₁)
    have heMid := appendWord_hasEnds old bridge hdisOldBridge
      (hasEnds_seam old bridge heOld heBridge seam₁)
      (wallUnitsChainWord_positive q Q k hq) (by simp; omega) heOld heBridge
    have hdisOldNext : ∀ i t, old.pos i ≠ next.pos t := by
      intro i t he
      rcases hOld i with ⟨a, ha, b, hb⟩ | ⟨a, ha, b, hb⟩
      · exact wallFolds_disjoint q Q hq hQ a l (by dsimp [l]; omega) b t (hb.trans he)
      · exact wall_bridge_disjoint q Q hq hQ l a t b (hb.trans he).symm
    have hdisBridgeNext : ∀ i t, bridge.pos i ≠ next.pos t :=
      fun i t => Ne.symm (wall_bridge_disjoint q Q hq hQ l j t i)
    have hdisMidNext : ∀ i t, mid.pos i ≠ next.pos t := by
      intro i t
      exact appendWord_property old bridge hdisOldBridge (hasEnds_seam old bridge heOld heBridge seam₁)
        (fun p => p ≠ next.pos t) (fun a => hdisOldNext a t) (fun a => hdisBridgeNext a t) i
    have hrow : wallTop q Q j - 3 * alpha Q - 1 = wallTop q Q l - alpha Q + 1 := by
      dsimp [wallTop, j, l]
      have hb : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by dsimp [beta, alpha]; omega
      push_cast
      rw [add_mul]
      omega
    have seam₂ : cubicLattice.Adj
        (point (depth q Q + 1) (wallTop q Q j - 3 * alpha Q - 1) (-2))
        (point (depth q Q + 1) (wallTop q Q l - alpha Q + 1) (-1)) := by
      rw [hrow]
      change latticeDistance _ _ = 1
      rw [distance_eq]
      simp [point]
    let f := Fold.appendWord mid next hdisMidNext (hasEnds_seam mid next heMid heNext seam₂)
    refine ⟨f, ?_, ?_, ?_⟩
    · exact appendWord_hasEnds mid next hdisMidNext (hasEnds_seam mid next heMid heNext seam₂)
        (by simp only [List.length_append]; have h := wallUnitsChainWord_positive q Q k hq; omega)
        (wallUnitsChainWord_positive q Q 0 hq) heMid heNext
    · apply appendWord_property mid next hdisMidNext (hasEnds_seam mid next heMid heNext seam₂)
        (UnitChainSites q Q hq hQ (k + 1))
      · apply appendWord_property old bridge hdisOldBridge (hasEnds_seam old bridge heOld heBridge seam₁)
          (UnitChainSites q Q hq hQ (k + 1))
        · intro i
          rcases hOld i with ⟨a, ha, b, hb⟩ | ⟨a, ha, b, hb⟩
          · exact Or.inl ⟨a, by omega, b, hb⟩
          · exact Or.inr ⟨a, by omega, b, hb⟩
        · intro i
          exact Or.inr ⟨j, by dsimp [j]; omega, i, rfl⟩
      · intro i
        exact Or.inl ⟨l, by dsimp [l]; omega, i, rfl⟩
    · intro p hp
      change p ∈ hydrophobicSites ((wallUnitsChainWord q Q k ++ _) ++ _) f at hp
      rw [appendWord_hydrophobicSites, appendWord_hydrophobicSites] at hp
      rcases hp with (hp | hp) | hp
      · exact hOldH hp
      · rw [replicateP_H_sites (2 * alpha Q) bridge] at hp
        exact False.elim hp
      · exact wallFold_H_inside q Q hq hQ l hp

theorem repeatWord_snoc (w : Sequence) (k : ℕ) :
    repeatWord w (k + 1) = repeatWord w k ++ w := by
  induction k with
  | zero => simp [repeatWord]
  | succ k ih =>
    change w ++ repeatWord w (k + 1) = (w ++ repeatWord w k) ++ w
    rw [ih]
    simp only [List.append_assoc]

theorem wallUnitsChainWord_eq (q Q k : ℕ) :
    wallUnitsChainWord q Q k = repeatWord (wallUnit q Q ++ List.replicate (2 * alpha Q) .P) k ++ wallUnit q Q := by
  induction k with
  | zero => simp [wallUnitsChainWord, repeatWord]
  | succ k ih => rw [wallUnitsChainWord, ih, repeatWord_snoc]; simp only [List.append_assoc]

theorem gapChainWord_eq (A k : ℕ) :
    gapChainWord A k = edgeWord 2 ++ repeatWord (List.replicate (2 * A + 4) .P ++ edgeWord 2) k := by
  induction k with
  | zero => simp [gapChainWord, repeatWord]
  | succ k ih => rw [gapChainWord, ih, repeatWord_snoc]; simp only [List.append_assoc]

theorem gap_last_literal (q Q : ℕ) (hq : 0 < q) :
    gapLast (alpha Q) (alpha Q + 1) (q - 1) = (depth q Q : ℤ) - alpha Q := by
  have he : (((q - 1 : ℕ) : ℤ) + 1) = q := by exact_mod_cast (show q - 1 + 1 = q by omega)
  have hb : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by dsimp [beta, alpha]; omega
  have hm := congrArg (fun z : ℤ => z * beta Q) he
  dsimp [gapLast, depth]
  rw [hb] at hm ⊢
  nlinarith

def GapHSupport (q Q : ℕ) (p : Site) : Prop :=
  ∃ j : Fin q, ∃ e : Fin 2,
    p = point (depth q Q + 1) (alpha Q + 1 + (j.val : ℤ) * beta Q + e.val) 0

theorem gapWordFold_exists (q Q : ℕ) (hq : 0 < q) :
    ∃ f : Fold cubicLattice (gapWord q Q).length,
      HasEnds f (point (depth q Q + 1) (alpha Q + 1) (-1))
        (point (depth q Q + 1) (depth q Q - alpha Q) (-1)) ∧
      (∀ i, GapRegion (depth q Q) (alpha Q) (alpha Q + 1) (q - 1) (f.pos i) ∧
        GapSites (depth q Q) (alpha Q) (alpha Q + 1) (q - 1) (f.pos i)) ∧
      (hydrophobicSites (gapWord q Q) f ⊆ {p | GapHSupport q Q p}) ∧
      hydrophobicSites (gapWord q Q) f ⊆ cube (fun _ => 0) (side q Q) := by
  have hw : gapWord q Q = gapChainWord (alpha Q) (q - 1) := by
    rw [gapChainWord_eq]
    rfl
  rw [hw]
  obtain ⟨f, he, hp, hH⟩ := gapChainFold_full_exists (depth q Q) (alpha Q) (alpha Q + 1) (q - 1)
  refine ⟨f, ?_, hp, ?_, ?_⟩
  · rwa [gap_last_literal q Q hq] at he
  · intro p hmem
    obtain ⟨j, hj, he | he⟩ := hH hmem
    all_goals
      have hjq : j < q := by omega
      have hb : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by dsimp [beta, alpha]; omega
    · exact ⟨⟨j, hjq⟩, ⟨0, by decide⟩, by simpa [hb] using he⟩
    · exact ⟨⟨j, hjq⟩, ⟨1, by decide⟩, by simpa [hb] using he⟩
  · intro p hmem
    obtain ⟨i, hi, rfl⟩ := hmem
    have hr := (hp i).1
    obtain ⟨j, hj, he | he⟩ := hH ⟨i, hi, rfl⟩
    all_goals
      have hylo := hr.1
      have hyhi := hr.2.1
      rw [gap_last_literal q Q hq] at hyhi
      rw [he] at hylo hyhi ⊢
      intro c
      fin_cases c <;> dsimp [point, side] at hylo hyhi ⊢ <;> omega

def WallSites (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q) (p : Site) : Prop :=
  UnitChainSites q Q hq hQ (q - 1) p ∨
    (GapRegion (depth q Q) (alpha Q) (alpha Q + 1) (q - 1) p ∧
      GapSites (depth q Q) (alpha Q) (alpha Q + 1) (q - 1) p)

theorem wallTop_last (q Q : ℕ) (hq : 0 < q) :
    wallTop q Q ⟨q - 1, by omega⟩ = beta Q := by
  have he : (((q - 1 : ℕ) : ℤ) + 1) = q := by exact_mod_cast (show q - 1 + 1 = q by omega)
  have hm := congrArg (fun z : ℤ => z * beta Q) he
  dsimp [wallTop, depth]
  nlinarith

theorem walls_fold_of_unit_gap_separation (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (hUE : ∀ a b : Fin q, ∀ i t,
      (wallFold q Q hq hQ a).pos i ≠
        (gapEdgeFold (depth q Q) (alpha Q + 1 + (b.val : ℤ) * beta Q)).pos t) :
    ∃ f : Fold cubicLattice (walls q Q).length,
      HasEnds f (point (depth q Q + 1) (depth q Q + 1 - alpha Q) (-1))
        (point (depth q Q + 1) (depth q Q - alpha Q) (-1)) ∧
      (∀ i, WallSites q Q hq hQ (f.pos i)) ∧
      hydrophobicSites (walls q Q) f ⊆ cube (fun _ => 0) (side q Q) := by
  have hw : walls q Q = wallUnitsChainWord q Q (q - 1) ++ gapWord q Q := by
    rw [wallUnitsChainWord_eq]
    rfl
  rw [hw]
  obtain ⟨units, heU, hU, hUH⟩ := wallUnitsChainFold_exists q Q hq hQ (q - 1) (by omega)
  obtain ⟨gap, heG, hG, hGH, hGin⟩ := gapWordFold_exists q Q hq
  have hdis : ∀ i t, units.pos i ≠ gap.pos t := by
    intro i t he
    have hbeta : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by dsimp [beta, alpha]; omega
    rcases hU i with ⟨a, ha, b, hb⟩ | ⟨a, ha, b, hb⟩
    · rcases (hG t).2 with ⟨v, hv, c, hc⟩ | ⟨v, hv, c, hc⟩
      · let vf : Fin q := ⟨v, by omega⟩
        have hcs : (gapEdgeFold (depth q Q) (alpha Q + 1 + (vf.val : ℤ) * beta Q)).pos c = gap.pos t := by
          dsimp [vf, gapEdgeFold]
          rw [hbeta]
          exact hc
        exact hUE a vf b c ((hb.trans he).trans hcs.symm)
      · have hz := congrFun ((hb.trans he).trans hc.symm) 2
        have hlo := wallFold_height q Q hq hQ a b
        have hg := (gapPBridge_location (depth q Q) (alpha Q)
          (gapLast (alpha Q) (alpha Q + 1) v) c).2.2.2
        rcases hg with hg | hg <;> omega
    · rcases (hG t).2 with ⟨v, hv, c, hc⟩ | ⟨v, hv, c, hc⟩
      · have hz := congrFun ((hb.trans he).trans hc.symm) 2
        have hlo := (gapEdgeFold_location (depth q Q)
          (alpha Q + 1 + (v : ℤ) * (2 * alpha Q + 2)) c).2.2.1
        change (-2 : ℤ) = (gapEdgeFold (depth q Q)
          (alpha Q + 1 + (v : ℤ) * (2 * alpha Q + 2))).pos c 2 at hz
        omega
      · exact unitPBridge_gapPBridge_disjoint q Q a ⟨v, by omega⟩ b c
          ((hb.trans he).trans hc.symm)
  have hlast : wallTop q Q ⟨q - 1, by omega⟩ - alpha Q - 2 = (alpha Q : ℤ) := by
    rw [wallTop_last q Q hq]
    dsimp [beta, alpha]
    omega
  have seam : cubicLattice.Adj
      (point (depth q Q + 1) (wallTop q Q ⟨q - 1, by omega⟩ - alpha Q - 2) (-1))
      (point (depth q Q + 1) (alpha Q + 1) (-1)) := by
    rw [hlast]
    change latticeDistance _ _ = 1
    rw [distance_eq]
    simp [point]
  let f := Fold.appendWord units gap hdis (hasEnds_seam units gap heU heG seam)
  refine ⟨f, ?_, ?_, ?_⟩
  · have he := appendWord_hasEnds units gap hdis (hasEnds_seam units gap heU heG seam)
      (wallUnitsChainWord_positive q Q (q - 1) hq)
      (by rw [gapWord_length]; omega) heU heG
    have hy : (depth q Q : ℤ) - alpha Q + 1 = depth q Q + 1 - alpha Q := by ring
    simpa only [hy] using he
  · apply appendWord_property units gap hdis (hasEnds_seam units gap heU heG seam) (WallSites q Q hq hQ)
    · exact fun i => Or.inl (hU i)
    · exact fun i => Or.inr (hG i)
  · intro p hp
    rw [appendWord_hydrophobicSites] at hp
    exact hp.elim (fun h => hUH h) (fun h => hGin h)

/-- The entire literal walls word has a self-avoiding fold with the prescribed
front ports and with every H inside the packing cube. All geometric separation
premises are discharged by the coordinate constructions. -/
theorem walls_fold_exists (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q) :
    ∃ f : Fold cubicLattice (walls q Q).length,
      HasEnds f (point (depth q Q + 1) (depth q Q + 1 - alpha Q) (-1))
        (point (depth q Q + 1) (depth q Q - alpha Q) (-1)) ∧
      (∀ i, WallSites q Q hq hQ (f.pos i)) ∧
      hydrophobicSites (walls q Q) f ⊆ cube (fun _ => 0) (side q Q) := by
  apply walls_fold_of_unit_gap_separation q Q hq hQ
  intro a b
  exact wallUnit_gapEdge_disjoint q Q a b (wallFold q Q hq hQ a)
    (wallFold_spec q Q hq hQ a).1

end ProteinFolding.CubicPackingWalls
