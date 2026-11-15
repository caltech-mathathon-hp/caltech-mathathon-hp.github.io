import ProteinFolding.Tetrahedral.NearFieldColumnSeparation
import ProteinFolding.Tetrahedral.NearFieldExitTetherBounds

/-! All exit tethers are simultaneously disjoint: their canonical columns
have distinct seeds, while their private row margins avoid every column. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem exitUps_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (exitColumnCount p k)) (j : Fin (exitColumnCount p l)) :
    (exitUp p k hk).pos i ≠ (exitUp p l hl).pos j := by
  apply DanglingColumn.points_ne_of_seed_ne
  exact faceColumn_seed_ne_of_c_ne p.side _ _ _ _ _ _ _ _
    (fun h => hne (separatorIndex_injective p (by omega)))

theorem exitUps_downs_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins)
    (i : Fin (exitColumnCount p k)) (j : Fin (exitColumnCount p l)) :
    (exitUp p k hk).pos i ≠ (exitDown p l).pos j := by
  apply DanglingColumn.points_ne_of_seed_ne
  exact faceColumn_seed_ne_of_b_ne p.side _ _ _ _ _ _ _ _ (by omega)

theorem exitDowns_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (exitColumnCount p k)) (j : Fin (exitColumnCount p l)) :
    (exitDown p k).pos i ≠ (exitDown p l).pos j := by
  apply DanglingColumn.points_ne_of_seed_ne
  apply faceColumn_seed_ne_of_b_ne p.side
  intro heq
  apply hne
  unfold ConstructionParameters.exitSlot at heq
  omega

theorem exitRows_ups_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (i : Fin (exitRowCount p k)) (j : Fin (exitColumnCount p l)) :
    (exitRowFold p k hk).pos i ≠ (exitUp p l hl).pos j :=
  exitRow_ne_column p k hk (exitSourceColumn p l hl) i j.val

theorem exitRows_downs_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins)
    (i : Fin (exitRowCount p k)) (j : Fin (exitColumnCount p l)) :
    (exitRowFold p k hk).pos i ≠ (exitDown p l).pos j :=
  exitRow_ne_column p k hk (exitTargetColumn p l) i j.rev.val

theorem exitRows_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (exitRowCount p k)) (j : Fin (exitRowCount p l)) :
    (exitRowFold p k hk).pos i ≠ (exitRowFold p l hl).pos j := by
  intro heq
  have hskin : p.exitSkin k ≠ p.exitSkin l := fun h => hne (p.exitSkins_injective h)
  have hdis : Disjoint (skin p.side (p.exitSkin k)) (skin p.side (p.exitSkin l)) := by
    rcases lt_or_gt_of_ne hskin with h | h
    · exact skins_disjoint _ _ _ h
    · exact (skins_disjoint _ _ _ h).symm
  exact Finset.disjoint_left.mp hdis (exitRow_mem_skin p k hk i)
    (heq ▸ exitRow_mem_skin p l hl j)

theorem exitTethers_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (p.exitTether k)) (j : Fin (p.exitTether l)) :
    (exitTetherFold p k hk).pos i ≠ (exitTetherFold p l hl).pos j := by
  apply exitTetherFold_property p k hk (fun q => q ≠ (exitTetherFold p l hl).pos j) _ _ _ i
  · intro r
    exact exitTetherFold_property p l hl (fun q => (exitUp p k hk).pos r ≠ q)
      (exitUps_disjoint p k l hk hl hne r)
      (fun s => (exitRows_ups_disjoint p l k hl hk s r).symm)
      (exitUps_downs_disjoint p k l hk r) j
  · intro r
    exact exitTetherFold_property p l hl (fun q => (exitRowFold p k hk).pos r ≠ q)
      (exitRows_ups_disjoint p k l hk hl r)
      (exitRows_disjoint p k l hk hl hne r)
      (exitRows_downs_disjoint p k l hk r) j
  · intro r
    exact exitTetherFold_property p l hl (fun q => (exitDown p k).pos r ≠ q)
      (fun s => (exitUps_downs_disjoint p l k hl s r).symm)
      (fun s => (exitRows_downs_disjoint p l k hl s r).symm)
      (exitDowns_disjoint p k l hk hl hne r) j

end ProteinFolding.Tetrahedral.NearField
