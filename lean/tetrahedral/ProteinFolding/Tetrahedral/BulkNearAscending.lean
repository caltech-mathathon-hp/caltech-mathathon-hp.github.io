import ProteinFolding.Tetrahedral.BulkNearAscendingData
import ProteinFolding.Tetrahedral.BulkSegmentValueTransfer

/-! The two exceptional near-y-vertex escapes end at a strictly larger
lexicographic segment potential, uniformly over the infinite size family. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def bulkNearAscendingReferenceVertex (j : Fin 4) : BulkVertex 50 :=
  ⟨bulkNearAscendingRoot j, (bulkInterior_fast_iff 50 _).mpr
    ((bulkNearAscending_reference_certificate j).2.1 _
      (bulkNearAscending_reference_certificate j).1)⟩

def bulkNearAscendingView (m : ℕ) (hm : 18 ≤ m) (j : Fin 4) : BulkVertex m :=
  ⟨bulkReanchorSite 50 m (bulkNearAscendingVertex j) (bulkNearAscendingRoot j),
    (bulkReanchor_interior_iff 50 m (bulkNearAscendingVertex j) 11 _
      (by decide) (by omega)
      (bulkNearAscending_reference_box j _ (bulkNearAscending_reference_certificate j).1)).mpr
        (bulkNearAscendingReferenceVertex j).property⟩

theorem bulkNearAscending_reference_not_row (j : Fin 4) :
    ¬BulkRowSegment 50 (bulkNearAscendingReferenceVertex j) := by
  rw [bulkSegmentFiniteCheck_row 50 (bulkNearAscendingReferenceVertex j)
    (bulkNearAscendingSupport j) (bulkNearAscendingRank j) (bulkNearAscending_reference_certificate j)]
  rintro ⟨p, hp, hd, hz⟩
  exact bulkNearAscending_reference_no_row j p hp ⟨(bulkDamaged_fast_iff 50 p).mp hd, hz⟩

theorem bulkNearAscending_reference_xhat (j : Fin 4) :
    bulkSegmentXhat 50 (bulkNearAscendingReferenceVertex j) = bulkNearAscendingXhat j := by
  unfold bulkSegmentXhat
  simp only [bulkSegmentFiniteCheck_xValues 50 (bulkNearAscendingReferenceVertex j)
    (bulkNearAscendingSupport j) (bulkNearAscendingRank j) (bulkNearAscending_reference_certificate j)]
  fin_cases j <;> decide

theorem bulkNearAscending_uniform_not_row (m : ℕ) (hm : 18 ≤ m) (j : Fin 4) :
    ¬BulkRowSegment m (bulkNearAscendingView m hm j) := by
  rw [bulkSegment_vertex_row 50 m (bulkNearAscendingVertex j) 11 (bulkNearAscendingSupport j)
    (bulkNearAscendingReferenceVertex j) (bulkNearAscendingView m hm j)
    (bulkNearAscendingRank j) (by decide) hm (bulkNearAscending_reference_box j)
    (bulkNearAscending_reference_certificate j) rfl]
  exact bulkNearAscending_reference_not_row j

theorem bulkNearAscending_uniform_xhat (m : ℕ) (hm : 18 ≤ m) (j : Fin 4) :
    bulkSegmentXhat m (bulkNearAscendingView m hm j) = bulkNearAscendingXhat j := by
  have hv : bulkNearAscendingVertex j = 1 ∨ bulkNearAscendingVertex j = 4 := by
    unfold bulkNearAscendingVertex
    split_ifs <;> simp only [true_or, or_true]
  rw [bulkSegment_vertex_y_xhat 50 m (bulkNearAscendingVertex j) 11 hv (bulkNearAscendingSupport j)
    (bulkNearAscendingReferenceVertex j) (bulkNearAscendingView m hm j)
    (bulkNearAscendingRank j) (by decide) hm (bulkNearAscending_reference_box j)
    (bulkNearAscending_reference_certificate j) rfl]
  exact bulkNearAscending_reference_xhat j

theorem bulkNearAscending_uniform_alpha (m : ℕ) (hm : 18 ≤ m) (j : Fin 4) :
    bulkAlpha m (bulkNearAscendingView m hm j).val =
      if j.val < 2 then 2 * (m : ℤ) - 9 else 2 * (m : ℤ) - 7 := by
  have h := (bulkReanchor_rho_alpha 50 m (bulkNearAscendingVertex j) 11
    (bulkNearAscendingRoot j) (by decide) (by omega)
    (bulkNearAscending_reference_box j _ (bulkNearAscending_reference_certificate j).1)).2
  change bulkAlpha m (bulkReanchorSite 50 m (bulkNearAscendingVertex j) (bulkNearAscendingRoot j)) = _
  rw [h, bulkNearAscending_reference_alpha]
  by_cases hj : j.val < 2 <;>
    simp only [bulkNearAscendingVertex, hj, ↓reduceIte, bulkVertexYExpansion,
      bulkVertexZExpansion, Fin.isValue] <;> omega

theorem bulkNearAscending_uniform_potential (m : ℕ) (hm : 18 ≤ m) (j : Fin 4) :
    bulkSegmentPotential m (bulkNearAscendingView m hm j) =
      toLex (1, toLex ((if j.val < 2 then 2 * (m : ℤ) - 9 else 2 * (m : ℤ) - 7),
        bulkNearAscendingXhat j)) := by
  have hpos : 0 < bulkAlpha m (bulkNearAscendingView m hm j).val := by
    rw [bulkNearAscending_uniform_alpha]
    split_ifs <;> omega
  unfold bulkSegmentPotential
  rw [if_neg (bulkNearAscending_uniform_not_row m hm j), if_pos hpos,
    bulkNearAscending_uniform_alpha, bulkNearAscending_uniform_xhat]

theorem bulkNearAscending_pair_strict (m : ℕ) (hm : 18 ≤ m) (i : Fin 2) :
    bulkSegmentPotential m (bulkNearAscendingView m hm ⟨2 * i.val, by omega⟩) <
      bulkSegmentPotential m (bulkNearAscendingView m hm ⟨2 * i.val + 1, by omega⟩) := by
  rw [bulkNearAscending_uniform_potential, bulkNearAscending_uniform_potential]
  fin_cases i <;>
    simp [bulkNearAscendingXhat, Prod.Lex.lt_iff]

end ProteinFolding.Tetrahedral
