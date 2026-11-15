import ProteinFolding.Tetrahedral.NearFieldExitRowAvoidance

/-! The complete exit tether: up the separator column, around the two
column-free rows, and down the prescribed 6-slot column. Its site count
is exactly the literal P-run length in the reduction word. -/

namespace ProteinFolding.Tetrahedral.NearField

def exitSourceColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    DanglingColumn p.side :=
  faceDanglingColumn p.side (p.side - 3 - p.separatorIndex k) 0 (p.separatorIndex k + 1)
    (by have h := p.separator_room k hk; omega)

def exitTargetColumn (p : ConstructionParameters) (k : ℕ) : DanglingColumn p.side :=
  faceDanglingColumn p.side 0 (5 * p.exitSlot k + 3) (p.side - 5 - 5 * p.exitSlot k)
    (by have h := p.exit_column_triangle_room k; omega)

def exitColumnCount (p : ConstructionParameters) (k : ℕ) : ℕ := 2 * p.exitSkin k - 1

def exitUp (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (exitColumnCount p k) :=
  columnPrefix (exitSourceColumn p k hk) (exitColumnCount p k)

def exitDown (p : ConstructionParameters) (k : ℕ) :
    Fold tetrahedralLattice (exitColumnCount p k) :=
  (columnPrefix (exitTargetColumn p k) (exitColumnCount p k)).reverse

theorem exitColumn_seeds_ne (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (exitSourceColumn p k hk).seed ≠ (exitTargetColumn p k).seed := by
  intro heq
  have hy := congrArg (fun q : Site => q.val 1) heq
  dsimp only [exitSourceColumn, exitTargetColumn] at hy
  rw [faceDanglingColumn_seed, faceDanglingColumn_seed] at hy
  dsimp [faceSubSite, faceSubCoordinates] at hy
  omega

theorem exitUp_row_disjoint (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (exitColumnCount p k)) (j : Fin (exitRowCount p k)) :
    (exitUp p k hk).pos i ≠ (exitRowFold p k hk).pos j := by
  intro heq
  exact exitRow_avoids_columns p k hk j ⟨exitSourceColumn p k hk, i.val, heq⟩

theorem exitRow_down_disjoint (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (exitRowCount p k)) (j : Fin (exitColumnCount p k)) :
    (exitRowFold p k hk).pos i ≠ (exitDown p k).pos j := by
  exact exitRow_ne_column p k hk (exitTargetColumn p k) i j.rev.val

theorem exitUp_down_disjoint (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i j : Fin (exitColumnCount p k)) : (exitUp p k hk).pos i ≠ (exitDown p k).pos j :=
  DanglingColumn.points_ne_of_seed_ne (exitColumn_seeds_ne p k hk) i.val j.rev.val

theorem exitUp_row_seam (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (exitColumnCount p k)) (j : Fin (exitRowCount p k))
    (hi : i.val + 1 = exitColumnCount p k) (hj : j.val = 0) :
    tetrahedralLattice.Adj ((exitUp p k hk).pos i) ((exitRowFold p k hk).pos j) := by
  have hskin := p.tether_skin_bounds k hk
  unfold exitUp exitSourceColumn exitColumnCount
  rw [columnPrefix_last _ _ _ _ _ _ (by omega) i hi, exitRow_first p k hk j hj]
  have hstep : step (faceSubSite p.side (p.exitSkin k)
      (p.side - 3 - p.separatorIndex k + p.exitSkin k) (0 + p.exitSkin k)
      (p.separatorIndex k + 1 + 1) (by have h := p.separator_room k hk; omega)) 1 =
      faceSurfaceSite p.side (p.exitSkin k)
        (p.side - 3 - p.separatorIndex k + p.exitSkin k) (p.exitSkin k - 1)
        (p.separatorIndex k + 2) (exitRow_faceEquation p k hk) := by
    rw [faceSub_step_one _ _ _ _ _ _ (by omega)]
    congr 1 <;> omega
  rw [← hstep]
  exact step_adj _ _

theorem exitRow_down_seam (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (exitRowCount p k)) (j : Fin (exitColumnCount p k))
    (hi : i.val + 1 = exitRowCount p k) (hj : j.val = 0) :
    tetrahedralLattice.Adj ((exitRowFold p k hk).pos i) ((exitDown p k).pos j) := by
  have hskin := p.tether_skin_bounds k hk
  have ht := p.exit_column_triangle_room k
  have hrev : j.rev.val + 1 = 2 * p.exitSkin k - 1 := by
    simp only [Fin.val_rev]
    change exitColumnCount p k - (j.val + 1) + 1 = _
    unfold exitColumnCount
    omega
  change tetrahedralLattice.Adj _ ((columnPrefix (exitTargetColumn p k) _).pos j.rev)
  unfold exitTargetColumn exitColumnCount
  rw [columnPrefix_last _ _ _ _ _ _ (by omega) j.rev hrev, exitRow_last p k hk i hi]
  have hstep : step (faceSubSite p.side (p.exitSkin k) (0 + p.exitSkin k)
      (5 * p.exitSlot k + 3 + p.exitSkin k) (p.side - 5 - 5 * p.exitSlot k + 1) (by omega)) 0 =
      faceSurfaceSite p.side (p.exitSkin k) (p.exitSkin k - 1)
        (5 * p.exitSlot k + 3 + p.exitSkin k) (p.side - 4 - 5 * p.exitSlot k) (by omega) := by
    rw [faceSub_step_zero _ _ _ _ _ _ (by omega)]
    congr 1 <;> omega
  rw [← hstep]
  exact (step_adj _ _).symm

def exitUpRows (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (exitColumnCount p k + exitRowCount p k) :=
  Fold.append (exitUp p k hk) (exitRowFold p k hk)
    (exitUp_row_disjoint p k hk) (exitUp_row_seam p k hk)

theorem exitUpRows_down_disjoint (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (exitColumnCount p k + exitRowCount p k)) (j : Fin (exitColumnCount p k)) :
    (exitUpRows p k hk).pos i ≠ (exitDown p k).pos j := by
  intro heq
  rcases (Fold.append_exists_pos _ _ _ _ _).mp ⟨i, heq⟩ with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact exitUp_down_disjoint p k hk r j hr
  · exact exitRow_down_disjoint p k hk r j hr

theorem exitUpRows_down_seam (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (exitColumnCount p k + exitRowCount p k)) (j : Fin (exitColumnCount p k))
    (hi : i.val + 1 = exitColumnCount p k + exitRowCount p k) (hj : j.val = 0) :
    tetrahedralLattice.Adj ((exitUpRows p k hk).pos i) ((exitDown p k).pos j) := by
  unfold exitUpRows
  rw [append_last _ _ _ _ (by unfold exitRowCount; omega) i hi]
  exact exitRow_down_seam p k hk _ j
    (by change exitRowCount p k - 1 + 1 = exitRowCount p k; unfold exitRowCount; omega) hj

def exitTetherRaw (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice ((exitColumnCount p k + exitRowCount p k) + exitColumnCount p k) :=
  Fold.append (exitUpRows p k hk) (exitDown p k)
    (exitUpRows_down_disjoint p k hk) (exitUpRows_down_seam p k hk)

theorem exitTetherRaw_count (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (exitColumnCount p k + exitRowCount p k) + exitColumnCount p k = p.exitTether k := by
  have h := exitRowCount_add_columnCounts p k hk
  have hj := p.tether_skin_bounds k hk
  unfold exitColumnCount
  omega

def exitTetherFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (p.exitTether k) :=
  (exitTetherRaw p k hk).onLength (exitTetherRaw_count p k hk).symm

end ProteinFolding.Tetrahedral.NearField
