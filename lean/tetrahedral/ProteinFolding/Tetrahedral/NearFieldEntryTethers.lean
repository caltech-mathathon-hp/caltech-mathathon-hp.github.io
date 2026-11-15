import ProteinFolding.Tetrahedral.NearFieldEntryAvoidance

/-! The complete entry tether, with its original anchor cap, borrowed
column, private two-row corner, and reversed separator column. -/

namespace ProteinFolding.Tetrahedral.NearField

def entryDown (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (2 * p.entrySkin k - 1) :=
  (columnPrefix (entryTargetColumn p k hk) (2 * p.entrySkin k - 1)).reverse

theorem entryRow_down_disjoint (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (entryRowCount p k)) (j : Fin (2 * p.entrySkin k - 1)) :
    (entryRowFold p k hk).pos i ≠ (entryDown p k hk).pos j :=
  entryRow_ne_targetColumn p k hk i j.rev.val

theorem entryUp_down_disjoint (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i j : Fin (2 * p.entrySkin k - 1)) : (entryUp p k hk).pos i ≠ (entryDown p k hk).pos j :=
  entryUp_ne_targetColumn p k hk i j.rev.val

theorem entryUp_row_seam (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) (j : Fin (entryRowCount p k))
    (hi : i.val + 1 = 2 * p.entrySkin k - 1) (hj : j.val = 0) :
    tetrahedralLattice.Adj ((entryUp p k hk).pos i) ((entryRowFold p k hk).pos j) := by
  have hskin := p.tether_skin_bounds k hk
  have ht := p.entry_column_triangle_room k hk
  unfold entryUp
  rw [borrowedPrefix_last _ _ _ _ _ _ _ hskin.1 i hi, entryRow_first p k hk j hj]
  have hstep : step (faceSubSite p.side (p.entrySkin k)
      (entryAnchorA p k - 1 + p.entrySkin k) (3 * (k + 1) + p.entrySkin k) (0 + 2)
      (by have h := entryAnchor_equation p k hk; have ha := entryAnchor_positive p k hk; omega)) 2 =
      faceSurfaceSite p.side (p.entrySkin k)
        (p.side - 3 - 3 * (k + 1) + p.entrySkin k) (3 * (k + 1) + p.entrySkin k) 1
        (entryRow_faceEquation p k hk) := by
    rw [faceSub_step_two _ _ _ _ _ _ (by omega)]
    congr 1
    unfold entryAnchorA
    omega
  rw [← hstep]
  exact step_adj _ _

theorem entryRow_down_seam (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (entryRowCount p k)) (j : Fin (2 * p.entrySkin k - 1))
    (hi : i.val + 1 = entryRowCount p k) (hj : j.val = 0) :
    tetrahedralLattice.Adj ((entryRowFold p k hk).pos i) ((entryDown p k hk).pos j) := by
  have hskin := p.tether_skin_bounds k hk
  have hr := p.separator_room k hk
  have hrev : j.rev.val + 1 = 2 * p.entrySkin k - 1 := by simp only [Fin.val_rev]; omega
  change tetrahedralLattice.Adj _ ((columnPrefix (entryTargetColumn p k hk) _).pos j.rev)
  unfold entryTargetColumn
  rw [columnPrefix_last _ _ _ _ _ _ (by omega) j.rev hrev, entryRow_last p k hk i hi]
  have hstep : step (faceSubSite p.side (p.entrySkin k)
      (p.side - 2 - p.separatorIndex k + p.entrySkin k) (0 + p.entrySkin k)
      (p.separatorIndex k + 1) (by omega)) 1 =
      faceSurfaceSite p.side (p.entrySkin k)
        (p.side - 2 - p.separatorIndex k + p.entrySkin k) (p.entrySkin k - 1)
        (p.separatorIndex k + 1) (by omega) := by
    rw [faceSub_step_one _ _ _ _ _ _ (by omega)]
    congr 1 <;> omega
  rw [← hstep]
  exact (step_adj _ _).symm

def entryUpRows (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice ((2 * p.entrySkin k - 1) + entryRowCount p k) :=
  Fold.append (entryUp p k hk) (entryRowFold p k hk)
    (entryUp_row_disjoint p k hk) (entryUp_row_seam p k hk)

theorem entryUpRows_down_disjoint (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin ((2 * p.entrySkin k - 1) + entryRowCount p k)) (j : Fin (2 * p.entrySkin k - 1)) :
    (entryUpRows p k hk).pos i ≠ (entryDown p k hk).pos j := by
  intro heq
  rcases (Fold.append_exists_pos _ _ _ _ _).mp ⟨i, heq⟩ with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact entryUp_down_disjoint p k hk r j hr
  · exact entryRow_down_disjoint p k hk r j hr

theorem entryUpRows_down_seam (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin ((2 * p.entrySkin k - 1) + entryRowCount p k)) (j : Fin (2 * p.entrySkin k - 1))
    (hi : i.val + 1 = (2 * p.entrySkin k - 1) + entryRowCount p k) (hj : j.val = 0) :
    tetrahedralLattice.Adj ((entryUpRows p k hk).pos i) ((entryDown p k hk).pos j) := by
  unfold entryUpRows
  rw [append_last _ _ _ _ (by unfold entryRowCount; omega) i hi]
  exact entryRow_down_seam p k hk _ j
    (by change entryRowCount p k - 1 + 1 = entryRowCount p k; unfold entryRowCount; omega) hj

def entryTetherRaw (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (((2 * p.entrySkin k - 1) + entryRowCount p k) + (2 * p.entrySkin k - 1)) :=
  Fold.append (entryUpRows p k hk) (entryDown p k hk)
    (entryUpRows_down_disjoint p k hk) (entryUpRows_down_seam p k hk)

theorem entryTetherRaw_count (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    ((2 * p.entrySkin k - 1) + entryRowCount p k) + (2 * p.entrySkin k - 1) = p.entryTether k := by
  have h := entryRowCount_add_columnCounts p k
  have hj := p.tether_skin_bounds k hk
  omega

def entryTetherFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (p.entryTether k) :=
  (entryTetherRaw p k hk).onLength (entryTetherRaw_count p k hk).symm

end ProteinFolding.Tetrahedral.NearField
