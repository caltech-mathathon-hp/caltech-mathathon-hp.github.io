import ProteinFolding.Tetrahedral.BulkJointPlanes

/-! A class-X joint with both edge parameters outside the near range has
|alpha| <= R-37. Odd candidates require the odd reversal margin. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192

theorem bulk_int_abs_ite (x : ℤ) : |x| = if 0 ≤ x then x else -x := by
  split_ifs with h
  · exact abs_of_nonneg h
  · exact abs_of_neg (by omega)

def bulkXEdgeAlphaSign (F : OctEdgeFrame) : ℤ :=
  if (F.k = 0 ∧ F.a = 3) ∨ (F.k = 1 ∧ F.a = 2) ∨
      (F.k = 2 ∧ F.a = 1) ∨ (F.k = 3 ∧ F.a = 0) then 1 else -1

theorem bulkXEdgeAlphaSign_unit (F : OctEdgeFrame) :
    bulkXEdgeAlphaSign F = 1 ∨ bulkXEdgeAlphaSign F = -1 := by
  unfold bulkXEdgeAlphaSign
  split_ifs <;> simp

local instance bulkFarXAlphaFrameFintype : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bulkFarX_reference_source_alpha (F : OctEdgeFrame) (odd : Bool) (d : Fin 4) :
    BulkXEdgeFrame F → bulkFastDamaged 21 (bulkEdgeCandidate 21 F 10 odd d (by decide)) →
      match odd with
      | false => -1 ≤ bulkXEdgeAlphaSign F * bulkAlpha 21 (bulkEdgeCandidate 21 F 10 odd d (by decide)) ∧
          bulkXEdgeAlphaSign F * bulkAlpha 21 (bulkEdgeCandidate 21 F 10 odd d (by decide)) ≤ 1
      | true => -3 ≤ bulkXEdgeAlphaSign F * bulkAlpha 21 (bulkEdgeCandidate 21 F 10 odd d (by decide)) ∧
          bulkXEdgeAlphaSign F * bulkAlpha 21 (bulkEdgeCandidate 21 F 10 odd d (by decide)) ≤ -1 := by
  cases odd <;> revert F d <;> decide

set_option maxHeartbeats 2000000 in
theorem bulkXEdgeAnchor_alpha_shift (m : ℕ) (F : OctEdgeFrame) (t : ℕ)
    (hm : 1 ≤ m) (ht : 10 ≤ t) (htm : t + 11 ≤ m) (hX : BulkXEdgeFrame F) :
    bulkAlpha m (bulkEdgeAnchor m F t) - bulkAlpha 21 (bulkEdgeAnchor 21 F 10) =
      bulkXEdgeAlphaSign F * (octRadius m - 4 * (t : ℤ)) := by
  unfold bulkAlpha bulkY bulkZ
  rw [bulkEdgeAnchor_closedCoordinates hm F t, bulkEdgeAnchor_closedCoordinates (by decide : 1 ≤ 21) F 10]
  rcases F with ⟨k, j, a, b, hkj, hka, hkb, hja, hjb, hab⟩
  fin_cases k <;> fin_cases j <;> fin_cases a <;> fin_cases b
  all_goals simp_all [BulkXEdgeFrame, bulkXEdgeAlphaSign, bulkEdgeClosedCoordinates, bulkEdgeFaceValue, octRadius]
  all_goals simp only [bulk_int_abs_ite]
  all_goals split_ifs <;> omega

set_option maxHeartbeats 1200000 in
theorem bulkFarX_candidate_source_alpha_bound (m : ℕ) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hm : 1 ≤ m) (ht : 10 ≤ t)
    (htm : t + (if odd then 12 else 11) ≤ m)
    (hX : BulkXEdgeFrame F) (hd : bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m) :
    |bulkAlpha m (bulkEdgeCandidate m F t odd d hm)| ≤ octRadius m - 39 := by
  have hfar : t + 11 ≤ m := by
    cases odd
    · change t + 11 ≤ m at htm
      exact htm
    · change t + 12 ≤ m at htm
      omega
  have hbox := bulkEdgeCandidate_in_box m F t odd d hm
  have hDm := (bulkEdgeReanchor_damaged_iff m 21 t 10 F 2 (bulkEdgeCandidate m F t odd d hm)
    (by omega) (by omega) (by decide) (by decide) hbox).mpr hd
  rw [bulkEdgeReanchor_candidate m 21 t 10 F odd d hm (by decide)] at hDm
  have href := bulkFarX_reference_source_alpha F odd d hX ((bulkDamaged_fast_iff 21 _).mp hDm)
  have hα := (bulkEdgeReanchor_relative_rho_alpha m 21 t 10 F 2
    (bulkEdgeCandidate m F t odd d hm) (by omega) (by omega) (by decide) (by decide) hbox).2
  rw [bulkEdgeReanchor_candidate m 21 t 10 F odd d hm (by decide)] at hα
  have hshift := bulkXEdgeAnchor_alpha_shift m F t hm ht hfar hX
  rcases bulkXEdgeAlphaSign_unit F with hs | hs
  · rw [hs] at href hshift
    simp only [one_mul] at href hshift
    cases odd <;> dsimp only at href <;> simp at htm
    all_goals rw [abs_le]
    all_goals unfold octRadius at hshift ⊢
    all_goals constructor <;> omega
  · rw [hs] at href hshift
    simp only [neg_one_mul] at href hshift
    cases odd <;> dsimp only at href <;> simp at htm
    all_goals rw [abs_le]
    all_goals unfold octRadius at hshift ⊢
    all_goals constructor <;> omega

theorem bulk_adj_alpha_abs_bound (m : ℕ) {p q : Site} (h : tetrahedralLattice.Adj p q) :
    |bulkAlpha m q| ≤ |bulkAlpha m p| + 2 := by
  have hd := bulk_adj_deltas m h
  have hy : bulkY m q = bulkY m p + 1 ∨ bulkY m q = bulkY m p - 1 := by omega
  have hz : bulkZ q = bulkZ p + 1 ∨ bulkZ q = bulkZ p - 1 := by omega
  have hay := abs_unit_adjacent (bulkY m p) (bulkY m q) hy
  have haz := abs_unit_adjacent (bulkZ p) (bulkZ q) hz
  have hp := abs_le.mp (le_refl |bulkAlpha m p|)
  rw [abs_le]
  unfold bulkAlpha at hp ⊢
  constructor <;> omega

theorem bulkFarX_joint_alpha_bound (m : ℕ) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hm : 1 ≤ m) (ht : 10 ≤ t)
    (htm : t + (if odd then 12 else 11) ≤ m)
    (hX : BulkXEdgeFrame F) (hd : bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m)
    (p : Site) (hp : p = bulkEdgeCandidate m F t odd d hm ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p) :
    |bulkAlpha m p| ≤ octRadius m - 37 := by
  have hsource := bulkFarX_candidate_source_alpha_bound m F t odd d hm ht htm hX hd
  rcases hp with rfl | hp
  · omega
  · exact (bulk_adj_alpha_abs_bound m hp).trans (by omega)

end ProteinFolding.Tetrahedral
