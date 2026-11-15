import ProteinFolding.Tetrahedral.NearFieldColumnSeparation

/-! Simultaneous disjointness of the actual entry tethers. No pairwise
route-disjointness hypothesis is used. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem entryRow_ne_far_column (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (a b c : ℕ) (hs : a + b + c + 2 = p.side) (hc : 2 ≤ c)
    (i : Fin (entryRowCount p k)) (n : ℕ) :
    (entryRowFold p k hk).pos i ≠ (faceDanglingColumn p.side a b c hs).point n := by
  have hj := p.tether_skin_bounds k hk
  have ht := p.entry_column_triangle_room k hk
  unfold entryRowFold rowCBFold
  apply glue_property _ _ _ _ _ _ (fun q => q ≠ (faceDanglingColumn p.side a b c hs).point n) ?_ ?_ i
  · intro r
    exact entryRowC_ne_farColumn p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k) (3 * (k + 1) + p.entrySkin k)
      a b c r.val n (entryRow_faceEquation p k hk) hs hc
  · intro r heq
    have hfree := faceRowB_avoids_columns p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k + (3 * (k + 1) + 1))
      (3 * (k + 1) + p.entrySkin k - (3 * (k + 1) + 1)) 1
      (by have h := entryRow_faceEquation p k hk; omega) (by omega) (by omega) (by omega)
      r.val (by have h := r.isLt; have hr := p.separator_room k hk; omega)
    exact hfree ⟨faceDanglingColumn p.side a b c hs, n, heq.symm⟩

theorem entryRows_downs_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (i : Fin (entryRowCount p k)) (j : Fin (2 * p.entrySkin l - 1)) :
    (entryRowFold p k hk).pos i ≠ (entryDown p l hl).pos j :=
  entryRow_ne_far_column p k hk (p.side - 2 - p.separatorIndex l) 0 (p.separatorIndex l)
    (by have h := p.separator_room l hl; omega) (separatorIndex_ge_two p l) i j.rev.val

theorem entryTethers_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (p.entryTether k)) (j : Fin (p.entryTether l)) :
    (entryTetherFold p k hk).pos i ≠ (entryTetherFold p l hl).pos j := by
  apply entryTetherFold_property p k hk (fun q => q ≠ (entryTetherFold p l hl).pos j) _ _ _ i
  · intro r
    exact entryTetherFold_property p l hl (fun q => (entryUp p k hk).pos r ≠ q)
      (entryUps_disjoint p k l hk hl hne r)
      (entryUp_ne_other_row p l k hl hk hne.symm r)
      (entryUps_downs_disjoint p k l hk hl r) j
  · intro r
    exact entryTetherFold_property p l hl (fun q => (entryRowFold p k hk).pos r ≠ q)
      (fun s => (entryUp_ne_other_row p k l hk hl hne s r).symm)
      (entryRows_disjoint p k l hk hl hne r)
      (entryRows_downs_disjoint p k l hk hl r) j
  · intro r
    exact entryTetherFold_property p l hl (fun q => (entryDown p k hk).pos r ≠ q)
      (fun s => (entryUps_downs_disjoint p l k hl hk s r).symm)
      (fun s => (entryRows_downs_disjoint p l k hl hk s r).symm)
      (entryDowns_disjoint p k l hk hl hne r) j

end ProteinFolding.Tetrahedral.NearField
