import ProteinFolding.Tetrahedral.BulkSegmentExtrema
import ProteinFolding.Tetrahedral.BulkRungPathBounds

/-! Local rung facts used to identify the bend of a spanning component path. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulk_nonbend_lower_rung (m : ℕ) (p : Site)
    (hy : bulkY m p ≠ 0) (hz : bulkZ p ≠ 0) :
    ∃ q : Site, (bulkRungGraph m).Adj p q ∧ bulkRho m q < bulkRho m p := by
  have hypos : 0 < |bulkY m p| := abs_pos.mpr hy
  have hzpos : 0 < |bulkZ p| := abs_pos.mpr hz
  have hdist := bulkBendDistance_eq m p
  have hn : 1 ≤ bulkBendDistance m p := by omega
  refine ⟨bulkInwardPoint m p 1, bulkInwardPoint_adj m p 0 (by omega), ?_⟩
  have h := (bulkInwardPoint_rho_alpha m p 1 hn).1
  simp only [Nat.cast_one, mul_one] at h
  omega

theorem bulk_two_upper_rungs_bend (m : ℕ) (p q r : Site)
    (hq : (bulkRungGraph m).Adj p q) (hr : (bulkRungGraph m).Adj p r)
    (hne : q ≠ r) (hqle : bulkRho m p ≤ bulkRho m q)
    (hrle : bulkRho m p ≤ bulkRho m r) : bulkY m p = 0 ∨ bulkZ p = 0 := by
  classical
  by_contra hb
  have hy : bulkY m p ≠ 0 := fun h => hb (Or.inl h)
  have hz : bulkZ p ≠ 0 := fun h => hb (Or.inr h)
  obtain ⟨s, hs, hslow⟩ := bulk_nonbend_lower_rung m p hy hz
  have hqs : q ≠ s := by intro h; rw [h] at hqle; omega
  have hrs : r ≠ s := by intro h; rw [h] at hrle; omega
  have hsub : ({q, r, s} : Finset Site) ⊆ bulkRungNeighbours m p := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact (bulkRungGraph_adj_iff m _ _).mp hq
    · exact (bulkRungGraph_adj_iff m _ _).mp hr
    · exact (bulkRungGraph_adj_iff m _ _).mp hs
  have hcard := Finset.card_le_card hsub
  have hthree : ({q, r, s} : Finset Site).card = 3 := by simp [hne, hqs, hrs]
  rw [hthree, bulkRungNeighbours_card] at hcard
  omega

private theorem distinct_pair_cases {a b q r : Site}
    (hq : q ∈ ({a, b} : Finset Site)) (hr : r ∈ ({a, b} : Finset Site))
    (hne : q ≠ r) : (q = a ∧ r = b) ∨ (q = b ∧ r = a) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq hr
  rcases hq with rfl | rfl <;> rcases hr with rfl | rfl
  · exact (hne rfl).elim
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact (hne rfl).elim

theorem bulk_bend_rung_x_pair (m : ℕ) (p q r : Site)
    (hb : bulkY m p = 0 ∨ bulkZ p = 0)
    (hq : (bulkRungGraph m).Adj p q) (hr : (bulkRungGraph m).Adj p r) (hne : q ≠ r) :
    (q.val 0 = p.val 0 - 1 ∧ r.val 0 = p.val 0 + 1) ∨
      (q.val 0 = p.val 0 + 1 ∧ r.val 0 = p.val 0 - 1) := by
  have hqmem := (bulkRungGraph_adj_iff m p q).mp hq
  have hrmem := (bulkRungGraph_adj_iff m p r).mp hr
  have hnz := bulk_coordinates_not_both_zero m p
  rcases hb with hy | hz
  · have hz : bulkZ p ≠ 0 := hnz.resolve_left (fun h => h hy)
    let sz : ℤ := if 0 < bulkZ p then 1 else -1
    have hsz : sz = 1 ∨ sz = -1 := by dsimp [sz]; split_ifs <;> omega
    have hzp : 0 < sz * bulkZ p := by dsimp [sz]; split_ifs <;> omega
    rw [bulkRungNeighbours_bendY m p sz hsz hy hzp] at hqmem hrmem
    have hxa := (bulkArmNext_coordinates 1 sz (Or.inl rfl) hsz p).2.2
    have hxb := (bulkArmNext_coordinates (-1) sz (Or.inr rfl) hsz p).2.2
    rcases distinct_pair_cases hqmem hrmem hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hsz with hsz | hsz <;> rw [hsz] at hxa hxb ⊢ <;>
      by_cases hA : InASublattice p.val <;> simp [hA] at hxa hxb <;> omega
  · have hy : bulkY m p ≠ 0 := hnz.resolve_right (fun h => h hz)
    let sy : ℤ := if 0 < bulkY m p then 1 else -1
    have hsy : sy = 1 ∨ sy = -1 := by dsimp [sy]; split_ifs <;> omega
    have hyp : 0 < sy * bulkY m p := by dsimp [sy]; split_ifs <;> omega
    rw [bulkRungNeighbours_bendZ m p sy hsy hz hyp] at hqmem hrmem
    have hxa := (bulkArmNext_coordinates sy 1 hsy (Or.inl rfl) p).2.2
    have hxb := (bulkArmNext_coordinates sy (-1) hsy (Or.inr rfl) p).2.2
    rcases distinct_pair_cases hqmem hrmem hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hsy with hsy | hsy <;> rw [hsy] at hxa hxb ⊢ <;>
      by_cases hA : InASublattice p.val <;> simp [hA] at hxa hxb <;> omega

end ProteinFolding.Tetrahedral
