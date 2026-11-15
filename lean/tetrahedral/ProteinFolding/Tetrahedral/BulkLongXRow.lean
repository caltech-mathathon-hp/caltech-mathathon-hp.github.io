import ProteinFolding.Tetrahedral.BulkSegments
import ProteinFolding.Tetrahedral.BulkFastLocal
import ProteinFolding.Tetrahedral.BulkFoliationParity

/-! A damaged row site lies near the octahedral boundary. This excludes row
status for moderate-alpha segments in a bounded X slab. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem tetraCoordinate_le_coordinate_abs_sum (m : ℕ) (p : Site) (k : Fin 4) :
    tetraCoordinate m p.val k ≤ |p.val 0| + |bulkY m p| + |p.val 2| := by
  have hxp := le_abs_self (p.val 0)
  have hxn := neg_le_abs (p.val 0)
  have hyp := le_abs_self (bulkY m p)
  have hyn := neg_le_abs (bulkY m p)
  have hzp := le_abs_self (p.val 2)
  have hzn := neg_le_abs (p.val 2)
  dsimp only [bulkY] at hyp hyn ⊢
  fin_cases k <;> dsimp [tetraCoordinate] <;> omega

theorem bulkDamaged_row_lower (m : ℕ) (p : Site) (hd : p ∈ bulkDamaged m)
    (hz : bulkZ p = 0) : octRadius m - 4 ≤ |p.val 0| + |bulkY m p| := by
  obtain ⟨_, d, hdeleted, _⟩ := (bulkDamaged_fast_iff m p).mp hd
  have hpB := bulkZ_zero_inB p hz
  have hadj := step_adj p d
  have heA : InASublattice (step p d).val := by
    rcases adj_sublattices hadj with ⟨hpA, _⟩ | ⟨_, heA⟩
    · exact (sublattices_disjoint p.val hpA hpB).elim
    · exact heA
  obtain ⟨_, k, j, _, hedge⟩ := hdeleted
  have hk : tetraCoordinate m (step p d).val k = octRadius m := by
    rcases hedge with hA | hB
    · exact hA.2.1
    · exact (sublattices_disjoint (step p d).val heA hB.1).elim
  have hface := tetraCoordinate_le_coordinate_abs_sum m (step p d) k
  rw [hk] at hface
  have hdx := adj_coordinate hadj 0
  have hdy := (bulk_adj_deltas m hadj).1
  have hdz := adj_coordinate hadj 2
  have hxp := le_abs_self (p.val 0)
  have hxn := neg_le_abs (p.val 0)
  have hyp := le_abs_self (bulkY m p)
  have hyn := neg_le_abs (bulkY m p)
  have hx : |(step p d).val 0| ≤ |p.val 0| + 1 := by
    rw [abs_le]
    constructor <;> omega
  have hy : |bulkY m (step p d)| ≤ |bulkY m p| + 1 := by
    rw [abs_le]
    constructor <;> omega
  have hez : |(step p d).val 2| ≤ 2 := by
    rw [abs_le]
    dsimp only [bulkZ] at hz
    constructor <;> omega
  omega

theorem bulkRowSegment_alpha_positive (m : ℕ) (p : BulkVertex m) (hrow : BulkRowSegment m p) :
    0 < bulkAlpha m p.val := by
  obtain ⟨q, hq, _, hZ⟩ := hrow
  have hα := bulkSegment_alpha m ((mem_bulkSegmentSites m p q).mp hq)
  have hnonzero := (bulk_coordinates_not_both_zero m q.val).resolve_right
    (fun h => h hZ)
  have hypos : 0 < |bulkY m q.val| := abs_pos.mpr hnonzero
  have hqα : bulkAlpha m q.val = |bulkY m q.val| := by
    simp only [bulkAlpha, hZ, abs_zero, sub_zero]
  omega

theorem bulkSegment_not_row_of_slab_alpha (m : ℕ) (p : BulkVertex m) (B : ℤ)
    (hslab : ∀ q : BulkVertex m, (bulkSegmentGraph m).Reachable p q → |q.val.val 0| ≤ B)
    (hα : bulkAlpha m p.val < octRadius m - B - 4) : ¬BulkRowSegment m p := by
  rintro ⟨q, hq, hd, hZ⟩
  have hreach := (mem_bulkSegmentSites m p q).mp hq
  have hbound := bulkDamaged_row_lower m q.val hd hZ
  have hx := hslab q hreach
  have ha := bulkSegment_alpha m hreach
  have hqα : bulkAlpha m q.val = |bulkY m q.val| := by
    simp only [bulkAlpha, hZ, abs_zero, sub_zero]
  omega

end ProteinFolding.Tetrahedral
