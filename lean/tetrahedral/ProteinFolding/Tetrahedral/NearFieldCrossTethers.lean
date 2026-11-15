import ProteinFolding.Tetrahedral.NearFieldEntryFamily
import ProteinFolding.Tetrahedral.NearFieldExitFamily

/-! Entry and exit tethers are disjoint for every pair of indices. The row
skins are ordered, both exit rows avoid all columns, and the separator and
exit columns have explicitly distinct owners. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem entryUp_exitUp_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) (j : Fin (exitColumnCount p l)) :
    (entryUp p k hk).pos i ≠ (exitUp p l hl).pos j :=
  borrowedPoint_ne_farColumn p.side (entryAnchorA p k) (3 * (k + 1))
    (p.side - 3 - p.separatorIndex l) 0 (p.separatorIndex l + 1) i.val j.val
    (entryAnchor_equation p k hk) (by have h := p.separator_room l hl; omega)
    (entryAnchor_positive p k hk) (by have h := separatorIndex_ge_two p l; omega)

theorem entryUp_exitDown_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) (j : Fin (exitColumnCount p l)) :
    (entryUp p k hk).pos i ≠ (exitDown p l).pos j :=
  borrowedPoint_ne_farColumn p.side (entryAnchorA p k) (3 * (k + 1))
    0 (5 * p.exitSlot l + 3) (p.side - 5 - 5 * p.exitSlot l) i.val j.rev.val
    (entryAnchor_equation p k hk) (by have h := p.exit_column_triangle_room l; omega)
    (entryAnchor_positive p k hk) (by have h := p.exit_column_triangle_room l; omega)

theorem entryUp_exitRow_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) (j : Fin (exitRowCount p l)) :
    (entryUp p k hk).pos i ≠ (exitRowFold p l hl).pos j := by
  intro heq
  have hon := borrowedPoint_on_column p.side (entryAnchorA p k) (3 * (k + 1)) 0
    (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) i.val
  change OnDanglingColumn p.side ((entryUp p k hk).pos i) at hon
  rw [heq] at hon
  exact exitRow_avoids_columns p l hl j hon

theorem entryRow_exitUp_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (i : Fin (entryRowCount p k)) (j : Fin (exitColumnCount p l)) :
    (entryRowFold p k hk).pos i ≠ (exitUp p l hl).pos j :=
  entryRow_ne_far_column p k hk (p.side - 3 - p.separatorIndex l) 0 (p.separatorIndex l + 1)
    (by have h := p.separator_room l hl; omega) (by have h := separatorIndex_ge_two p l; omega) i j.val

theorem entryRow_exitDown_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins)
    (i : Fin (entryRowCount p k)) (j : Fin (exitColumnCount p l)) :
    (entryRowFold p k hk).pos i ≠ (exitDown p l).pos j :=
  entryRow_ne_far_column p k hk 0 (5 * p.exitSlot l + 3) (p.side - 5 - 5 * p.exitSlot l)
    (by have h := p.exit_column_triangle_room l; omega)
    (by have h := p.exit_column_triangle_room l; omega) i j.rev.val

theorem entryRow_exitRow_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (i : Fin (entryRowCount p k)) (j : Fin (exitRowCount p l)) :
    (entryRowFold p k hk).pos i ≠ (exitRowFold p l hl).pos j := by
  intro heq
  have hdis := skins_disjoint p.side (p.entrySkin k) (p.exitSkin l) (p.entrySkin_lt_exitSkin k l hk)
  exact Finset.disjoint_left.mp hdis (entryRow_mem_skin p k hk i)
    (heq ▸ exitRow_mem_skin p l hl j)

theorem entryDown_exitUp_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) (j : Fin (exitColumnCount p l)) :
    (entryDown p k hk).pos i ≠ (exitUp p l hl).pos j := by
  apply DanglingColumn.points_ne_of_seed_ne
  apply faceColumn_seed_ne_of_c_ne p.side
  intro heq
  have hkmod := p.separatorIndex_even k
  have hlmod := p.separatorIndex_even l
  omega

theorem entryDown_exitDown_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) (j : Fin (exitColumnCount p l)) :
    (entryDown p k hk).pos i ≠ (exitDown p l).pos j := by
  apply DanglingColumn.points_ne_of_seed_ne
  exact faceColumn_seed_ne_of_b_ne p.side _ _ _ _ _ _ _ _ (by omega)

theorem entryDown_exitRow_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) (j : Fin (exitRowCount p l)) :
    (entryDown p k hk).pos i ≠ (exitRowFold p l hl).pos j :=
  (exitRow_ne_column p l hl (entryTargetColumn p k hk) j i.rev.val).symm

theorem entry_exit_tethers_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (i : Fin (p.entryTether k)) (j : Fin (p.exitTether l)) :
    (entryTetherFold p k hk).pos i ≠ (exitTetherFold p l hl).pos j := by
  apply entryTetherFold_property p k hk (fun q => q ≠ (exitTetherFold p l hl).pos j) _ _ _ i
  · intro r
    exact exitTetherFold_property p l hl (fun q => (entryUp p k hk).pos r ≠ q)
      (entryUp_exitUp_disjoint p k l hk hl r)
      (entryUp_exitRow_disjoint p k l hk hl r)
      (entryUp_exitDown_disjoint p k l hk r) j
  · intro r
    exact exitTetherFold_property p l hl (fun q => (entryRowFold p k hk).pos r ≠ q)
      (entryRow_exitUp_disjoint p k l hk hl r)
      (entryRow_exitRow_disjoint p k l hk hl r)
      (entryRow_exitDown_disjoint p k l hk r) j
  · intro r
    exact exitTetherFold_property p l hl (fun q => (entryDown p k hk).pos r ≠ q)
      (entryDown_exitUp_disjoint p k l hk hl r)
      (entryDown_exitRow_disjoint p k l hk hl r)
      (entryDown_exitDown_disjoint p k l hk r) j

end ProteinFolding.Tetrahedral.NearField
