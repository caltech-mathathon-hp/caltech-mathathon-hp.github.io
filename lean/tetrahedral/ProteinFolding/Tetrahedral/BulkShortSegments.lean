import ProteinFolding.Tetrahedral.BulkRungPathBounds
import ProteinFolding.Tetrahedral.BulkLineInjectivity

/-! Exact cardinal bounds for transverse-bounded pieces of rung lines. -/

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 2000000

theorem bulkRung_positive_finite_card_le_Z_interval (m : ℕ) (p : Site)
    (S : Finset Site) (B : ℤ) (hp : 0 < bulkAlpha m p)
    (hline : ∀ q ∈ S, (bulkRungGraph m).Reachable p q)
    (hbound : ∀ q ∈ S, |bulkZ q| ≤ B) :
    S.card ≤ (Finset.Icc (-B) B).card := by
  classical
  apply Finset.card_le_card_of_injOn bulkZ
  · intro q hq
    exact Finset.mem_Icc.mpr (abs_le.mp (hbound q hq))
  · intro q hq r hr heq
    obtain ⟨wq⟩ := hline q hq
    have hα := bulkWalk_alpha m wq
    have hqr : (bulkRungGraph m).Reachable q r :=
      (show (bulkRungGraph m).Reachable p q from ⟨wq⟩).symm.trans (hline r hr)
    exact (bulkRung_positive_Z_injective m hqr (by omega) heq.symm).symm

theorem bulkRung_negative_finite_card_le_Y_interval (m : ℕ) (p : Site)
    (S : Finset Site) (B : ℤ) (hp : bulkAlpha m p < 0)
    (hline : ∀ q ∈ S, (bulkRungGraph m).Reachable p q)
    (hbound : ∀ q ∈ S, |bulkY m q| ≤ B) :
    S.card ≤ (Finset.Icc (-B) B).card := by
  classical
  apply Finset.card_le_card_of_injOn (bulkY m)
  · intro q hq
    exact Finset.mem_Icc.mpr (abs_le.mp (hbound q hq))
  · intro q hq r hr heq
    obtain ⟨wq⟩ := hline q hq
    have hα := bulkWalk_alpha m wq
    have hqr : (bulkRungGraph m).Reachable q r :=
      (show (bulkRungGraph m).Reachable p q from ⟨wq⟩).symm.trans (hline r hr)
    exact (bulkRung_negative_Y_injective m hqr (by omega) heq.symm).symm

theorem bulkRung_positive_path_card_le_nine (m : ℕ) {p q : Site}
    (w : (bulkRungGraph m).Walk p q) (hw : w.IsPath)
    (hp : 0 < bulkAlpha m p) (hpZ : |bulkZ p| ≤ 4) (hqZ : |bulkZ q| ≤ 4) :
    w.support.toFinset.card ≤ 9 := by
  classical
  have hc := bulkRung_positive_finite_card_le_Z_interval m p w.support.toFinset 4 hp
    (by
      intro r hr
      obtain ⟨i, hi, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hr)
      exact ⟨hi ▸ w.take i⟩)
    (by
      intro r hr
      exact bulkRung_path_Z_bound m w hw 4 hpZ hqZ (List.mem_toFinset.mp hr))
  have hcard : (Finset.Icc (-4 : ℤ) 4).card = 9 := by decide
  rwa [hcard] at hc

theorem bulkSegment_positive_card_le_nine_of_Z_bound (m : ℕ) (p : BulkVertex m)
    (hp : 0 < bulkAlpha m p.val)
    (hbound : ∀ q : BulkVertex m, (bulkSegmentGraph m).Reachable p q → |bulkZ q.val| ≤ 4) :
    (bulkSegmentSites m p).card ≤ 9 := by
  classical
  have hcard : (Finset.Icc (-4 : ℤ) 4).card = 9 := by decide
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun q : BulkVertex m => bulkZ q.val)
  · intro q hq
    exact Finset.mem_Icc.mpr (abs_le.mp (hbound q ((mem_bulkSegmentSites m p q).mp hq)))
  · intro q hq r hr heq
    have hpq := (mem_bulkSegmentSites m p q).mp hq
    have hpr := (mem_bulkSegmentSites m p r).mp hr
    have hα := bulkSegment_alpha m hpq
    apply Subtype.ext
    exact (bulkRung_positive_Z_injective m
      (bulkSegment_reachable_rung m (hpq.symm.trans hpr)) (by omega) heq.symm).symm

theorem bulkSegment_positive_card_le_nine_of_spanning_path (m : ℕ) {p q : BulkVertex m}
    (w : (bulkSegmentGraph m).Walk p q) (hw : w.IsPath)
    (hspan : ∀ r : BulkVertex m, (bulkSegmentGraph m).Reachable p r → r ∈ w.support)
    (hp : 0 < bulkAlpha m p.val) (hpZ : |bulkZ p.val| ≤ 4) (hqZ : |bulkZ q.val| ≤ 4) :
    (bulkSegmentSites m p).card ≤ 9 := by
  apply bulkSegment_positive_card_le_nine_of_Z_bound m p hp
  intro r hr
  have hmapPath := SimpleGraph.Walk.map_isPath_of_injective (f := bulkSegmentRungHom m)
    Subtype.val_injective hw
  apply bulkRung_path_Z_bound m (w.map (bulkSegmentRungHom m)) hmapPath 4 hpZ hqZ
  rw [SimpleGraph.Walk.support_map]
  exact List.mem_map.mpr ⟨r, hspan r hr, rfl⟩

end ProteinFolding.Tetrahedral
