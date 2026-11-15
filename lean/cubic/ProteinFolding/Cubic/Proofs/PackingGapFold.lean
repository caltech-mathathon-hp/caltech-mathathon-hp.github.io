import ProteinFolding.Cubic.Proofs.PackingWallBridges
import Mathlib.Tactic.FinCases

/-! The literal gap word J, with its E₂ blocks ascending the right rail
and its fixed P connections at depths two and three. -/

namespace ProteinFolding.CubicPackingWalls

open CubicCertificates CubicPacking CubicPackingLift CubicPackingRouting

def gapEdgePos (d : ℕ) (y : ℤ) (i : Fin 6) : Site :=
  point (if i.val = 2 ∨ i.val = 3 then (d : ℤ) + 2 else d + 1)
    (if i.val < 3 then y else y + 1) (if i.val = 0 ∨ i.val = 5 then -1 else 0)

/-- The complete six-residue PHP-PHP block, with prescribed front-facing
endpoint P sites. The middle P pair points out of the right rail. -/
def gapEdgeFold (d : ℕ) (y : ℤ) : Fold cubicLattice (edgeWord 2).length where
  pos := gapEdgePos d y
  injective_pos := by
    intro i j he
    have hx := congrFun he 0
    have hy := congrFun he 1
    have hz := congrFun he 2
    fin_cases i <;> fin_cases j <;>
      dsimp only [gapEdgePos, point] at hx hy hz <;> apply Fin.ext <;> dsimp <;> omega
  consecutive i j hij := by
    change latticeDistance (gapEdgePos d y i) (gapEdgePos d y j) = 1
    fin_cases i <;> fin_cases j <;> norm_num [edgeWord, repeatWord] at hij
    all_goals rw [distance_eq]; norm_num [gapEdgePos, point] <;> omega

theorem gapEdgeFold_ends (d : ℕ) (y : ℤ) :
    HasEnds (gapEdgeFold d y) (point (d + 1) y (-1)) (point (d + 1) (y + 1) (-1)) :=
  hasEnds_of_indices _ (by decide) _ _ rfl rfl

theorem gapEdgeFold_location (d : ℕ) (y : ℤ) (i : Fin (edgeWord 2).length) :
    y ≤ (gapEdgeFold d y).pos i 1 ∧ (gapEdgeFold d y).pos i 1 ≤ y + 1 ∧
    -1 ≤ (gapEdgeFold d y).pos i 2 ∧
    ((gapEdgeFold d y).pos i 0 = d + 1 ∨ (gapEdgeFold d y).pos i 0 = d + 2) := by
  fin_cases i <;> dsimp only [gapEdgeFold, gapEdgePos, point] <;> omega

def gapChainWord (A : ℕ) : ℕ → Sequence
  | 0 => edgeWord 2
  | k + 1 => (gapChainWord A k ++ List.replicate (2 * A + 4) .P) ++ edgeWord 2

def gapLast (A : ℕ) (start : ℤ) (k : ℕ) : ℤ := start + (k : ℤ) * (2 * A + 2) + 1

theorem gapLast_ge_start (A : ℕ) (start : ℤ) (k : ℕ) : start ≤ gapLast A start k := by
  have hnon : 0 ≤ (k : ℤ) * (2 * A + 2) := by positivity
  unfold gapLast
  omega

/-- Bounds used to separate each new bridge and gap block from everything
already constructed. Only the final E₂ block can attain the maximal row. -/
def GapRegion (d A : ℕ) (start : ℤ) (k : ℕ) (p : Site) : Prop :=
  start ≤ p 1 ∧ p 1 ≤ gapLast A start k ∧
  (p 1 = gapLast A start k → -1 ≤ p 2) ∧
  (p 0 = d + 1 ∨ p 0 = d + 2) ∧ -3 ≤ p 2 ∧ p 2 ≤ 0

theorem gapChainWord_nonempty (A k : ℕ) : 0 < (gapChainWord A k).length := by
  induction k with
  | zero => change 0 < 6; decide
  | succ k ih => simp only [gapChainWord, List.length_append]; omega

def GapSites (d A : ℕ) (start : ℤ) (k : ℕ) (p : Site) : Prop :=
  (∃ j ≤ k, ∃ i : Fin 6,
    gapEdgePos d (start + (j : ℤ) * (2 * A + 2)) i = p) ∨
  (∃ j < k, ∃ i, (gapPBridge d A (gapLast A start j)).pos i = p)

theorem gapChainFold_full_exists (d A : ℕ) (start : ℤ) (k : ℕ) :
    ∃ f : Fold cubicLattice (gapChainWord A k).length,
      HasEnds f (point (d + 1) start (-1)) (point (d + 1) (gapLast A start k) (-1)) ∧
      (∀ i, GapRegion d A start k (f.pos i) ∧ GapSites d A start k (f.pos i)) ∧
      hydrophobicSites (gapChainWord A k) f ⊆
        {p | ∃ j ≤ k, p = point (d + 1) (start + (j : ℤ) * (2 * A + 2)) 0 ∨
          p = point (d + 1) (start + (j : ℤ) * (2 * A + 2) + 1) 0} := by
  induction k with
  | zero =>
    refine ⟨gapEdgeFold d start, ?_, ?_, ?_⟩
    · simpa only [gapLast, Nat.cast_zero, zero_mul, add_zero] using gapEdgeFold_ends d start
    · intro i
      constructor
      swap
      ·
        exact Or.inl ⟨0, by omega, i, by simp [gapEdgeFold]⟩
      have hi := gapEdgeFold_location d start i
      have hz : (gapEdgeFold d start).pos i 2 ≤ 0 := by
        fin_cases i <;> simp [gapEdgeFold, gapEdgePos, point]
      change start ≤ _ ∧ _ ≤ start + (0 : ℤ) * _ + 1 ∧ _
      simp only [zero_mul, add_zero]
      exact ⟨hi.1, hi.2.1, fun _ => hi.2.2.1, hi.2.2.2, by omega, hz⟩
    · rintro p ⟨i, hi, rfl⟩
      refine ⟨0, by omega, ?_⟩
      fin_cases i <;> simp [gapChainWord, edgeWord, repeatWord] at hi
      all_goals simp [gapEdgeFold, gapEdgePos, point]
  | succ k ih =>
    obtain ⟨old, heOld, hOldFull, hOldH⟩ := ih
    have hOld := fun i => (hOldFull i).1
    let y := gapLast A start k
    let newStart := y + 2 * A + 1
    let bridge := gapPBridge d A y
    let next := gapEdgeFold d newStart
    have hydef : y = gapLast A start k := rfl
    have hnew : newStart = y + 2 * A + 1 := rfl
    have heBridge := gapPBridge_ends d A y
    have heNext := gapEdgeFold_ends d newStart
    have hBridge : ∀ i, bridge.pos i 0 = d + 1 ∧ y ≤ bridge.pos i 1 ∧
        bridge.pos i 1 ≤ y + 2 * A + 1 ∧ (bridge.pos i 2 = -2 ∨ bridge.pos i 2 = -3) :=
      gapPBridge_location d A y
    have hNext : ∀ i, newStart ≤ next.pos i 1 ∧ next.pos i 1 ≤ newStart + 1 ∧
        -1 ≤ next.pos i 2 ∧ (next.pos i 0 = d + 1 ∨ next.pos i 0 = d + 2) :=
      gapEdgeFold_location d newStart
    have hdisOldBridge : ∀ i j, old.pos i ≠ bridge.pos j := by
      intro i j he
      have ho := hOld i
      have hb := hBridge j
      have hy := congrFun he 1
      have hz := congrFun he 2
      have hytop : old.pos i 1 = gapLast A start k := by
        have hbl := hb.2.1
        have hyhi := ho.2.1
        omega
      have hzold := ho.2.2.1 hytop
      rcases hb.2.2.2 with hb | hb <;> omega
    have seam₁ : cubicLattice.Adj (point (d + 1) y (-1)) (point (d + 1) y (-2)) := by
      change latticeDistance _ _ = 1
      rw [distance_eq]
      simp [point]
    let fmid := Fold.appendWord old bridge hdisOldBridge (hasEnds_seam old bridge heOld heBridge seam₁)
    have hdisOldNext : ∀ i j, old.pos i ≠ next.pos j := by
      intro i j he
      have ho := (hOld i).2.1
      have hn := (hNext j).1
      have hy := congrFun he 1
      omega
    have hdisBridgeNext : ∀ i j, bridge.pos i ≠ next.pos j := by
      intro i j he
      have hb := hBridge i
      have hn := hNext j
      have hz := congrFun he 2
      rcases hb.2.2.2 with hb | hb <;> omega
    have hdisMidNext : ∀ i j, fmid.pos i ≠ next.pos j := by
      intro i j
      have hp := appendWord_property old bridge hdisOldBridge
        (hasEnds_seam old bridge heOld heBridge seam₁) (fun p => p ≠ next.pos j)
        (fun i => hdisOldNext i j) (fun i => hdisBridgeNext i j) i
      exact hp
    have hBridgeLen : 0 < (List.replicate (2 * A + 4) Residue.P).length := by simp
    have heMid := appendWord_hasEnds old bridge hdisOldBridge
      (hasEnds_seam old bridge heOld heBridge seam₁) (gapChainWord_nonempty A k) hBridgeLen heOld heBridge
    have seam₂ : cubicLattice.Adj (point (d + 1) newStart (-2)) (point (d + 1) newStart (-1)) := by
      change latticeDistance _ _ = 1
      rw [distance_eq]
      simp [point]
    let f := Fold.appendWord fmid next hdisMidNext (hasEnds_seam fmid next heMid heNext seam₂)
    have he := appendWord_hasEnds fmid next hdisMidNext
      (hasEnds_seam fmid next heMid heNext seam₂)
      (by simp only [List.length_append]; have h := gapChainWord_nonempty A k; omega)
      (by decide) heMid heNext
    have hlast : newStart + 1 = gapLast A start (k + 1) := by
      dsimp [newStart, y, gapLast]
      simp only [add_mul, one_mul]
      ring
    have he' : HasEnds f (point (d + 1) start (-1))
        (point (d + 1) (gapLast A start (k + 1)) (-1)) := by
      refine ⟨he.1, ?_⟩
      intro i hi
      exact (he.2 i hi).trans (congrArg (fun z => point (d + 1) z (-1)) hlast)
    refine ⟨f, he', ?_, ?_⟩
    · apply appendWord_property fmid next hdisMidNext (hasEnds_seam fmid next heMid heNext seam₂)
        (fun p => GapRegion d A start (k + 1) p ∧ GapSites d A start (k + 1) p)
      · apply appendWord_property old bridge hdisOldBridge (hasEnds_seam old bridge heOld heBridge seam₁)
          (fun p => GapRegion d A start (k + 1) p ∧ GapSites d A start (k + 1) p)
        · intro i
          constructor
          swap
          ·
            rcases (hOldFull i).2 with ⟨j, hj, a, ha⟩ | ⟨j, hj, a, ha⟩
            · exact Or.inl ⟨j, by omega, a, ha⟩
            · exact Or.inr ⟨j, by omega, a, ha⟩
          have ho := hOld i
          dsimp only [GapRegion] at ho ⊢
          have hlt : gapLast A start k < gapLast A start (k + 1) := by
            rw [← hlast]
            omega
          exact ⟨ho.1, by omega, by omega, ho.2.2.2.1, ho.2.2.2.2⟩
        · intro i
          constructor
          swap
          ·
            exact Or.inr ⟨k, by omega, i, rfl⟩
          have hb := hBridge i
          dsimp only [GapRegion]
          rw [← hlast]
          have hstart := gapLast_ge_start A start k
          rcases hb.2.2.2 with hz | hz <;> omega
      · intro i
        constructor
        swap
        ·
          refine Or.inl ⟨k + 1, by omega, i, ?_⟩
          change gapEdgePos d _ i = gapEdgePos d newStart i
          congr 1
          dsimp [newStart, y, gapLast]
          push_cast
          ring
        have hn := hNext i
        dsimp only [GapRegion]
        rw [← hlast]
        have hz : next.pos i 2 ≤ 0 := by fin_cases i <;> simp [next, gapEdgeFold, gapEdgePos, point]
        exact ⟨by
          have ho := hOld ⟨0, gapChainWord_nonempty A k⟩
          have hbound := ho.1.trans ho.2.1
          omega, hn.2.1, by omega, hn.2.2.2, by omega, hz⟩
    · intro p hp
      rw [show hydrophobicSites (gapChainWord A (k + 1)) f =
          hydrophobicSites (gapChainWord A k) old ∪
          hydrophobicSites (List.replicate (2 * A + 4) .P) bridge ∪
          hydrophobicSites (edgeWord 2) next by
        change hydrophobicSites ((gapChainWord A k ++ _) ++ _) _ = _
        rw [appendWord_hydrophobicSites, appendWord_hydrophobicSites]] at hp
      rcases hp with (hp | hp) | hp
      · obtain ⟨j, hj, hp⟩ := hOldH hp
        exact ⟨j, by omega, hp⟩
      · have he := replicateP_H_sites (2 * A + 4) bridge
        rw [he] at hp
        exact False.elim hp
      · obtain ⟨i, hi, rfl⟩ := hp
        refine ⟨k + 1, by omega, ?_⟩
        have hy : start + ((k + 1 : ℕ) : ℤ) * (2 * A + 2) = newStart := by
          dsimp [newStart, y, gapLast]
          push_cast
          ring
        rw [hy]
        fin_cases i <;> simp [edgeWord, repeatWord] at hi
        all_goals simp [next, gapEdgeFold, gapEdgePos, point]

theorem gapChainFold_exists (d A : ℕ) (start : ℤ) (k : ℕ) :
    ∃ f : Fold cubicLattice (gapChainWord A k).length,
      HasEnds f (point (d + 1) start (-1)) (point (d + 1) (gapLast A start k) (-1)) ∧
      ∀ i, GapRegion d A start k (f.pos i) := by
  obtain ⟨f, he, hp, _⟩ := gapChainFold_full_exists d A start k
  exact ⟨f, he, fun i => (hp i).1⟩

end ProteinFolding.CubicPackingWalls

