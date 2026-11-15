import ProteinFolding.Tetrahedral.Normalization
import ProteinFolding.Tetrahedral.OctahedralVertices
import Mathlib.Algebra.BigOperators.Fin

/-! The 32 added and 19 removed bonds of Appendix B, frozen in canon_patches.py.
The six vertices are in lexicographic coordinate order. -/

namespace ProteinFolding.Tetrahedral

def bulkPatchVertex (m : ℕ) (v : Fin 6) : Site :=
  match v.val with
  | 0 => octVertexSite m 0 false
  | 1 => octVertexSite m 1 false
  | 2 => octVertexSite m 2 false
  | 3 => octVertexSite m 2 true
  | 4 => octVertexSite m 1 true
  | _ => octVertexSite m 0 true

def bulkPatchAdds (v : Fin 6) : Finset (Coordinates × Coordinates) :=
  match v.val with
  | 0 => {(![3, -1, 1], ![4, 0, 0]),
      (![4, 2, -2], ![5, 1, -3]),
      (![5, -1, -1], ![6, 0, -2])}
  | 1 => {(![-5, 7, -3], ![-4, 6, -2]),
      (![-4, 8, 4], ![-3, 7, 3]),
      (![-3, 5, -3], ![-2, 4, -2]),
      (![-2, 8, 2], ![-1, 7, 1]),
      (![-1, 3, 1], ![0, 4, 0]),
      (![0, 6, 2], ![1, 5, 1]),
      (![1, 3, -1], ![2, 4, -2]),
      (![3, 5, -1], ![4, 6, -2])}
  | 2 => {(![-4, 2, 6], ![-3, 3, 7]),
      (![-2, 2, 4], ![-1, 1, 3]),
      (![-2, 4, 6], ![-1, 3, 5]),
      (![2, 2, 4], ![3, 3, 5]),
      (![4, 2, 6], ![5, 3, 7])}
  | 3 => {(![-4, -2, -6], ![-3, -3, -7]),
      (![-2, -4, -6], ![-1, -3, -5]),
      (![-2, -2, -4], ![-1, -1, -3]),
      (![2, -2, -4], ![3, -3, -5]),
      (![4, -2, -6], ![5, -3, -7])}
  | 4 => {(![-5, -7, 3], ![-4, -6, 2]),
      (![-4, -6, -2], ![-3, -5, -1]),
      (![-3, -5, 3], ![-2, -4, 2]),
      (![-2, -6, 0], ![-1, -5, 1]),
      (![0, -4, 0], ![1, -3, 1]),
      (![1, -5, 3], ![2, -6, 4]),
      (![1, -3, 1], ![2, -4, 2]),
      (![3, -7, 3], ![4, -8, 4])}
  | _ => {(![-6, 0, -2], ![-5, 1, -1]),
      (![-5, -1, -3], ![-4, -2, -2]),
      (![-4, 0, 0], ![-3, 1, 1])}

def bulkPatchRemoves (v : Fin 6) : Finset (Coordinates × Coordinates) :=
  match v.val with
  | 0 => {(![4, 0, 0], ![5, -1, -1]),
      (![5, 1, -3], ![6, 0, -2])}
  | 1 => {(![-4, 6, -2], ![-3, 5, -3]),
      (![-3, 7, 3], ![-2, 8, 2]),
      (![-1, 7, 1], ![0, 6, 2]),
      (![0, 4, 0], ![1, 5, 1]),
      (![2, 4, -2], ![3, 5, -1])}
  | 2 => {(![-3, 3, 7], ![-2, 4, 6]),
      (![-2, 2, 4], ![-1, 3, 5]),
      (![3, 3, 5], ![4, 2, 6])}
  | 3 => {(![-3, -3, -7], ![-2, -4, -6]),
      (![-2, -2, -4], ![-1, -3, -5]),
      (![3, -3, -5], ![4, -2, -6])}
  | 4 => {(![-4, -6, 2], ![-3, -5, 3]),
      (![-3, -5, -1], ![-2, -6, 0]),
      (![-1, -5, 1], ![0, -4, 0]),
      (![2, -6, 4], ![3, -7, 3])}
  | _ => {(![-6, 0, -2], ![-5, -1, -3]),
      (![-5, 1, -1], ![-4, 0, 0])}

def ValidBulkPatchPair (e : Coordinates × Coordinates) : Prop :=
  IsLatticeSite e.1 ∧ IsLatticeSite e.2 ∧
    ((InASublattice e.1 ∧ InBSublattice e.2 ∧
      ∃ d : Fin 4, ∀ k : Fin 3, e.2 k = e.1 k + bondVector d k) ∨
     (InASublattice e.2 ∧ InBSublattice e.1 ∧
      ∃ d : Fin 4, ∀ k : Fin 3, e.1 k = e.2 k + bondVector d k))

instance (e : Coordinates × Coordinates) : Decidable (ValidBulkPatchPair e) :=
  by unfold ValidBulkPatchPair; infer_instance

theorem bulkPatchAdds_valid (v : Fin 6) : ∀ e ∈ bulkPatchAdds v, ValidBulkPatchPair e := by
  fin_cases v <;> decide

theorem bulkPatchRemoves_valid (v : Fin 6) : ∀ e ∈ bulkPatchRemoves v, ValidBulkPatchPair e := by
  fin_cases v <;> decide

theorem bulkPatchAdds_count : (∑ v : Fin 6, (bulkPatchAdds v).card) = 32 := by decide

theorem bulkPatchRemoves_count : (∑ v : Fin 6, (bulkPatchRemoves v).card) = 19 := by decide

theorem bulkPatchAdds_disjoint_removes (v : Fin 6) :
    Disjoint (bulkPatchAdds v) (bulkPatchRemoves v) := by fin_cases v <;> decide

theorem bulkPatch_vertex_inA (m : ℕ) (v : Fin 6) : InASublattice (bulkPatchVertex m v).val := by
  fin_cases v <;> exact octVertexCoordinates_inA _ _ _

theorem bulkPatchAdds_within_eight (v : Fin 6) :
    ∀ e ∈ bulkPatchAdds v, ∀ k : Fin 3, |e.1 k| ≤ 8 ∧ |e.2 k| ≤ 8 := by
  fin_cases v <;> decide

theorem bulkPatchRemoves_within_eight (v : Fin 6) :
    ∀ e ∈ bulkPatchRemoves v, ∀ k : Fin 3, |e.1 k| ≤ 8 ∧ |e.2 k| ≤ 8 := by
  fin_cases v <;> decide

def bulkPatchRelativePair (m : ℕ) (v : Fin 6) (p q : Site) : Coordinates × Coordinates :=
  ((shiftSite (bulkPatchVertex m v) (bulkPatch_vertex_inA m v) p).val,
    (shiftSite (bulkPatchVertex m v) (bulkPatch_vertex_inA m v) q).val)

theorem bulkPatchAdds_translated_adj (m : ℕ) (v : Fin 6) (p q : Site)
    (h : bulkPatchRelativePair m v p q ∈ bulkPatchAdds v) : tetrahedralLattice.Adj p q := by
  have hv := bulkPatchAdds_valid v _ h
  apply (adj_shift_iff (bulkPatchVertex m v) (bulkPatch_vertex_inA m v) p q).mp
  exact hv.2.2

theorem bulkPatchRemoves_translated_adj (m : ℕ) (v : Fin 6) (p q : Site)
    (h : bulkPatchRelativePair m v p q ∈ bulkPatchRemoves v) : tetrahedralLattice.Adj p q := by
  have hv := bulkPatchRemoves_valid v _ h
  apply (adj_shift_iff (bulkPatchVertex m v) (bulkPatch_vertex_inA m v) p q).mp
  exact hv.2.2

def bulkPatchAdded (m : ℕ) (p q : Site) : Prop :=
  ∃ v : Fin 6, bulkPatchRelativePair m v p q ∈ bulkPatchAdds v ∨
    bulkPatchRelativePair m v q p ∈ bulkPatchAdds v

def bulkPatchRemoved (m : ℕ) (p q : Site) : Prop :=
  ∃ v : Fin 6, bulkPatchRelativePair m v p q ∈ bulkPatchRemoves v ∨
    bulkPatchRelativePair m v q p ∈ bulkPatchRemoves v

theorem bulkPatchAdded_adj (m : ℕ) {p q : Site} (h : bulkPatchAdded m p q) :
    tetrahedralLattice.Adj p q := by
  obtain ⟨v, h | h⟩ := h
  · exact bulkPatchAdds_translated_adj m v p q h
  · exact (bulkPatchAdds_translated_adj m v q p h).symm

theorem bulkPatchRemoved_adj (m : ℕ) {p q : Site} (h : bulkPatchRemoved m p q) :
    tetrahedralLattice.Adj p q := by
  obtain ⟨v, h | h⟩ := h
  · exact bulkPatchRemoves_translated_adj m v p q h
  · exact (bulkPatchRemoves_translated_adj m v q p h).symm

end ProteinFolding.Tetrahedral
