import ProteinFolding.Tetrahedral.NearFieldEntryTetherBounds

/-! Entry columns cannot cross another entry corner. Earlier prefixes stop
below its private skin; later prefixes lie beyond its starting row. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem borrowedPoint_ne_laterRowC (m a b A B j n r : ℕ)
    (hs : a + b + 0 + 2 = m) (ht : A + B + 0 + 2 = m)
    (ha : 1 ≤ a) (hA : 1 ≤ A) (hb : b < B) :
    borrowedPoint m A B 0 ht hA n ≠
      faceRowPoint 2 m j (a - 1 + j) (b + j) 1 (by omega) r := by
  intro heq
  have hy := congrArg (fun q : Site => q.val 1) heq
  have hz := congrArg (fun q : Site => q.val 2) heq
  cases n with
  | zero =>
    dsimp only [borrowedPoint] at hy hz
    rw [faceDanglingColumn_seed] at hy hz
    dsimp [faceSubSite, faceSubCoordinates, faceRowPoint, faceRowCoordinates] at hy hz
    omega
  | succ n =>
    dsimp only [borrowedPoint] at hy hz
    rw [faceDanglingColumn_point_coordinates] at hy hz
    dsimp [faceRowPoint, faceRowCoordinates] at hy hz
    omega

theorem entryUp_ne_earlier_row (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hkl : k < l)
    (i : Fin (2 * p.entrySkin l - 1)) (j : Fin (entryRowCount p k)) :
    (entryUp p l hl).pos i ≠ (entryRowFold p k hk).pos j := by
  have hj := p.tether_skin_bounds k hk
  have ht := p.entry_column_triangle_room k hk
  have ha := entryAnchor_positive p k hk
  unfold entryRowFold rowCBFold
  apply glue_property _ _ _ _ _ _ (fun q => (entryUp p l hl).pos i ≠ q) ?_ ?_ j
  · intro r
    have heq : p.side - 3 - 3 * (k + 1) + p.entrySkin k =
        entryAnchorA p k - 1 + p.entrySkin k := by unfold entryAnchorA; omega
    change borrowedPoint p.side (entryAnchorA p l) (3 * (l + 1)) 0
      (entryAnchor_equation p l hl) (entryAnchor_positive p l hl) i.val ≠
      faceRowPoint 2 p.side (p.entrySkin k)
        (p.side - 3 - 3 * (k + 1) + p.entrySkin k) (3 * (k + 1) + p.entrySkin k) 1
        (entryRow_faceEquation p k hk) r.val
    simpa only [heq] using borrowedPoint_ne_laterRowC p.side
      (entryAnchorA p k) (3 * (k + 1)) (entryAnchorA p l) (3 * (l + 1))
      (p.entrySkin k) i.val r.val (entryAnchor_equation p k hk) (entryAnchor_equation p l hl)
      ha (entryAnchor_positive p l hl) (by omega)
  · intro r heq
    dsimp only [rowFold] at heq
    have hfree := faceRowB_avoids_columns p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k + (3 * (k + 1) + 1))
      (3 * (k + 1) + p.entrySkin k - (3 * (k + 1) + 1)) 1
      (by have h := entryRow_faceEquation p k hk; omega) (by omega) (by omega) (by omega)
      r.val (by have h := r.isLt; have hr := p.separator_room k hk; omega)
    apply hfree
    rw [← heq]
    exact borrowedPoint_on_column p.side (entryAnchorA p l) (3 * (l + 1)) 0
      (entryAnchor_equation p l hl) (entryAnchor_positive p l hl) i.val

theorem entryUp_ne_other_row (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (2 * p.entrySkin l - 1)) (j : Fin (entryRowCount p k)) :
    (entryUp p l hl).pos i ≠ (entryRowFold p k hk).pos j := by
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · exact entryUp_ne_earlier_row p k l hk hl hkl i j
  · intro heq
    have hu := entryUp_mem_solid p l hl i
    have hrank : p.entrySkin l ≤ p.entrySkin k - 1 := by unfold ConstructionParameters.entrySkin; omega
    have hsmall := skinSolid_mono p.side hrank hu
    rw [heq] at hsmall
    exact (Finset.mem_sdiff.mp (entryRow_mem_skin p k hk j)).2 hsmall

theorem entryRows_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (entryRowCount p k)) (j : Fin (entryRowCount p l)) :
    (entryRowFold p k hk).pos i ≠ (entryRowFold p l hl).pos j := by
  intro heq
  have hskin : p.entrySkin k ≠ p.entrySkin l := fun h => hne (p.entrySkins_injective h)
  have hdis : Disjoint (skin p.side (p.entrySkin k)) (skin p.side (p.entrySkin l)) := by
    rcases lt_or_gt_of_ne hskin with h | h
    · exact skins_disjoint _ _ _ h
    · exact (skins_disjoint _ _ _ h).symm
  exact Finset.disjoint_left.mp hdis (entryRow_mem_skin p k hk i)
    (heq ▸ entryRow_mem_skin p l hl j)

end ProteinFolding.Tetrahedral.NearField
