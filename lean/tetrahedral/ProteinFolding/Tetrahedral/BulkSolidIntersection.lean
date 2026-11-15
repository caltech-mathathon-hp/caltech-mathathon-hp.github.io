import ProteinFolding.Tetrahedral.BulkBendUniqueness

/-! A foliation line meeting the solid contains its bend inside the solid. -/

namespace ProteinFolding.Tetrahedral

theorem bulkQuadrant_face_difference (m : ℕ) (p : Site) (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) :
    tetraCoordinate m p.val (bulkQuadrantDirection sy sz) -
      tetraCoordinate m p.val (bulkQuadrantDirection (-sy) (-sz)) =
        2 * (sy * bulkY m p + sz * bulkZ p + sz) := by
  rcases hsy with rfl | rfl <;> rcases hsz with rfl | rfl
  all_goals dsimp [bulkQuadrantDirection, tetraCoordinate, bulkY, bulkZ]
  all_goals ring

theorem bulk_inward_next_mem_octahedron (m : ℕ) (p : Site) (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1)
    (hy : 0 < sy * bulkY m p) (hz : 0 < sz * bulkZ p)
    (hp : p ∈ octahedron m) : bulkArmNext (-sy) (-sz) p ∈ octahedron m := by
  have hdiff := bulkQuadrant_face_difference m p sy sz hsy hsz
  have hpositive : 0 < sy * bulkY m p + sz * bulkZ p + sz := by
    rcases hsz with hs | hs <;> rw [hs] at hz ⊢ <;> omega
  rcases p.property with hpA | hpB
  · simp only [bulkArmNext, if_pos hpA]
    apply (step_mem_octahedron_A m hpA hp _).mpr
    have hbound := ((inOctahedron_iff_A m hpA).mp ((mem_octahedron m _).mp hp)
      (bulkQuadrantDirection sy sz)).2
    omega
  · have hpnotA := (inB_iff_not_inA p).mp hpB
    simp only [bulkArmNext, if_neg hpnotA, neg_neg]
    apply (step_mem_octahedron_B m hpB hp _).mpr
    have hbound := ((inOctahedron_iff_B m hpB).mp ((mem_octahedron m _).mp hp)
      (bulkQuadrantDirection (-sy) (-sz))).1
    omega

theorem bulkInwardPoint_signed_coordinates (m : ℕ) (p : Site) (n : ℕ) :
    bulkYSign m p * bulkY m (bulkInwardPoint m p n) = |bulkY m p| - n ∧
      bulkZSign p * bulkZ (bulkInwardPoint m p n) = |bulkZ p| - n := by
  have hsy := bulkYSign_unit m p
  have hsz := bulkZSign_unit p
  have hy0 := abs_eq_unit_mul (bulkYSign m p) (bulkY m p) hsy (bulkYSign_nonneg m p)
  have hz0 := abs_eq_unit_mul (bulkZSign p) (bulkZ p) hsz (bulkZSign_nonneg p)
  have hy := bulkArmPoint_y m (-bulkYSign m p) (-bulkZSign p) (by omega) (by omega) p n
  have hz := bulkArmPoint_z (-bulkYSign m p) (-bulkZSign p) (by omega) (by omega) p n
  change bulkY m (bulkInwardPoint m p n) = _ at hy
  change bulkZ (bulkInwardPoint m p n) = _ at hz
  constructor
  · rw [hy, hy0]
    rcases hsy with hs | hs <;> rw [hs] <;> ring
  · rw [hz, hz0]
    rcases hsz with hs | hs <;> rw [hs] <;> ring

theorem bulkInwardPoint_mem_octahedron (m : ℕ) (p : Site) (hp : p ∈ octahedron m)
    (n : ℕ) (hn : n ≤ bulkBendDistance m p) : bulkInwardPoint m p n ∈ octahedron m := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    have hn' : n ≤ bulkBendDistance m p := by omega
    have hprev := ih hn'
    have hdist := bulkBendDistance_eq m p
    have hsigned := bulkInwardPoint_signed_coordinates m p n
    have hny : (n : ℤ) < |bulkY m p| := by
      have h := min_le_left |bulkY m p| |bulkZ p|
      omega
    have hnz : (n : ℤ) < |bulkZ p| := by
      have h := min_le_right |bulkY m p| |bulkZ p|
      omega
    exact bulk_inward_next_mem_octahedron m (bulkInwardPoint m p n)
      (bulkYSign m p) (bulkZSign p) (bulkYSign_unit m p) (bulkZSign_unit p)
      (by omega) (by omega) hprev

theorem bulkBendPoint_mem_octahedron (m : ℕ) (p : Site) (hp : p ∈ octahedron m) :
    bulkBendPoint m p ∈ octahedron m :=
  bulkInwardPoint_mem_octahedron m p hp (bulkBendDistance m p) (le_refl _)

theorem bulkInwardWalk_support_mem_octahedron (m : ℕ) (p : Site)
    (hp : p ∈ octahedron m) (n : ℕ) (hn : n ≤ bulkBendDistance m p) :
    ∀ r ∈ (bulkInwardWalk m p n hn).support, r ∈ octahedron m := by
  induction n with
  | zero =>
    intro r hr
    change r ∈ ([p] : List Site) at hr
    have heq : r = p := by simpa only [List.mem_singleton] using hr
    rwa [heq]
  | succ n ih =>
    intro r hr
    change r ∈ ((bulkInwardWalk m p n (by omega)).concat
      (bulkInwardPoint_adj m p n (by omega))).support at hr
    rw [SimpleGraph.Walk.support_concat] at hr
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | hr
    · exact ih (by omega) r hr
    · rw [hr]
      exact bulkInwardPoint_mem_octahedron m p hp (n + 1) hn

/-- Intersecting any foliation line with the solid gives a connected set.
The witness is an actual simple path all of whose sites remain in the solid. -/
theorem bulk_solid_line_intersection_connected (m : ℕ) (p q : Site)
    (hp : p ∈ octahedron m) (hq : q ∈ octahedron m)
    (hline : (bulkRungGraph m).Reachable p q) :
    ∃ w : (bulkRungGraph m).Walk p q, w.IsPath ∧ ∀ r ∈ w.support, r ∈ octahedron m := by
  have hb : bulkBendPoint m p = bulkBendPoint m q :=
    bulk_bend_unique_of_reachable m (bulkBendPoint_is_bend m p) (bulkBendPoint_is_bend m q)
      ((bulkBendPoint_reachable m p).symm.trans (hline.trans (bulkBendPoint_reachable m q)))
  let wp := bulkInwardWalk m p (bulkBendDistance m p) (le_refl _)
  have hpInside : ∀ r ∈ wp.support, r ∈ octahedron m :=
    bulkInwardWalk_support_mem_octahedron m p hp _ _
  have hqWalk : ∃ wq : (bulkRungGraph m).Walk q (bulkBendPoint m p),
      ∀ r ∈ wq.support, r ∈ octahedron m := by
    rw [hb]
    exact ⟨bulkInwardWalk m q (bulkBendDistance m q) (le_refl _),
      bulkInwardWalk_support_mem_octahedron m q hq _ _⟩
  obtain ⟨wq, hqInside⟩ := hqWalk
  let w := wp.append wq.reverse
  refine ⟨w.toPath.val, w.toPath.property, ?_⟩
  intro r hr
  have hrw := w.support_toPath_subset hr
  change r ∈ (wp.append wq.reverse).support at hrw
  rw [SimpleGraph.Walk.mem_support_append_iff] at hrw
  rcases hrw with h | h
  · exact hpInside r h
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h
    exact hqInside r h

end ProteinFolding.Tetrahedral
