import ProteinFolding.Tetrahedral.BulkLineCoordinates
import ProteinFolding.Tetrahedral.BulkBendUniqueness

/-! Along a simple rung path, rho and each absolute transverse coordinate
are bounded by their endpoint values. -/

namespace ProteinFolding.Tetrahedral

open SimpleGraph

theorem bulkRung_path_rho_bound (m : ℕ) {p q : Site} (w : (bulkRungGraph m).Walk p q)
    (hw : w.IsPath) {r : Site} (hr : r ∈ w.support) :
    bulkRho m r ≤ max (bulkRho m p) (bulkRho m q) := by
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hr
  have hne : (Finset.range (w.length + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (w.length + 1))
    (fun j => bulkRho m (w.getVert j)) hne
  have hjlen : j ≤ w.length := by have h := Finset.mem_range.mp hj; omega
  have hri := hmax i (Finset.mem_range.mpr (by omega))
  rw [hi] at hri
  by_cases hj0 : j = 0
  · rw [hj0, Walk.getVert_zero] at hri
    exact hri.trans (le_max_left _ _)
  by_cases hjend : j = w.length
  · rw [hjend, Walk.getVert_length] at hri
    exact hri.trans (le_max_right _ _)
  have hjpos : 0 < j := by omega
  have hjlt : j < w.length := by omega
  have hl := w.adj_getVert_succ (show j - 1 < w.length by omega)
  rw [show j - 1 + 1 = j by omega] at hl
  have hr' := w.adj_getVert_succ hjlt
  have heq := bulk_lower_rung_unique m (w.getVert j)
    ((bulkRungGraph_adj_iff m _ _).mp hl.symm)
    ((bulkRungGraph_adj_iff m _ _).mp hr')
    (hmax (j - 1) (Finset.mem_range.mpr (by omega)))
    (hmax (j + 1) (Finset.mem_range.mpr (by omega)))
  have hbad := hw.getVert_injOn (show j - 1 ≤ w.length by omega)
    (show j + 1 ≤ w.length by omega) heq
  omega

theorem bulkRung_path_Z_bound (m : ℕ) {p q : Site} (w : (bulkRungGraph m).Walk p q)
    (hw : w.IsPath) (B : ℤ) (hp : |bulkZ p| ≤ B) (hq : |bulkZ q| ≤ B)
    {r : Site} (hr : r ∈ w.support) : |bulkZ r| ≤ B := by
  have hρ := bulkRung_path_rho_bound m w hw hr
  have hαq := bulkWalk_alpha m w
  obtain ⟨i, hi, _⟩ := Walk.mem_support_iff_exists_getVert.mp hr
  have hαr := bulkWalk_alpha m (w.take i)
  rw [hi] at hαr
  have hpρ : bulkRho m p = bulkAlpha m p + 2 * |bulkZ p| := by unfold bulkRho bulkAlpha; omega
  have hqρ : bulkRho m q = bulkAlpha m q + 2 * |bulkZ q| := by unfold bulkRho bulkAlpha; omega
  have hrρ : bulkRho m r = bulkAlpha m r + 2 * |bulkZ r| := by unfold bulkRho bulkAlpha; omega
  have hmax : max (bulkRho m p) (bulkRho m q) ≤ bulkAlpha m p + 2 * B := max_le (by omega) (by omega)
  omega

theorem bulkRung_path_Y_bound (m : ℕ) {p q : Site} (w : (bulkRungGraph m).Walk p q)
    (hw : w.IsPath) (B : ℤ) (hp : |bulkY m p| ≤ B) (hq : |bulkY m q| ≤ B)
    {r : Site} (hr : r ∈ w.support) : |bulkY m r| ≤ B := by
  have hρ := bulkRung_path_rho_bound m w hw hr
  have hαq := bulkWalk_alpha m w
  obtain ⟨i, hi, _⟩ := Walk.mem_support_iff_exists_getVert.mp hr
  have hαr := bulkWalk_alpha m (w.take i)
  rw [hi] at hαr
  have hpρ : bulkRho m p = -bulkAlpha m p + 2 * |bulkY m p| := by unfold bulkRho bulkAlpha; omega
  have hqρ : bulkRho m q = -bulkAlpha m q + 2 * |bulkY m q| := by unfold bulkRho bulkAlpha; omega
  have hrρ : bulkRho m r = -bulkAlpha m r + 2 * |bulkY m r| := by unfold bulkRho bulkAlpha; omega
  have hmax : max (bulkRho m p) (bulkRho m q) ≤ -bulkAlpha m p + 2 * B := max_le (by omega) (by omega)
  omega

end ProteinFolding.Tetrahedral
