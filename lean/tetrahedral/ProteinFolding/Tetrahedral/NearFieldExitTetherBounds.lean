import ProteinFolding.Tetrahedral.NearFieldTetherSupport

/-! Exact caps and near-field solid bounds of the assembled exit tether. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem exitUp_mem_solid (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (exitColumnCount p k)) : (exitUp p k hk).pos i ∈ skinSolid p.side (p.exitSkin k) :=
  columnPrefix_mem_solid (exitSourceColumn p k hk) _ (by have h := p.tether_skin_bounds k hk; omega) i

theorem exitDown_mem_solid (p : ConstructionParameters) (k : ℕ)
    (i : Fin (exitColumnCount p k)) : (exitDown p k).pos i ∈ skinSolid p.side (p.exitSkin k) := by
  apply columnPrefix_mem_solid (exitTargetColumn p k) _ _ i.rev
  unfold ConstructionParameters.exitSkin
  omega

theorem exitTetherRaw_mem_solid (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin ((exitColumnCount p k + exitRowCount p k) + exitColumnCount p k)) :
    (exitTetherRaw p k hk).pos i ∈ skinSolid p.side (p.exitSkin k) := by
  apply exitTetherRaw_property p k hk (fun q => q ∈ skinSolid p.side (p.exitSkin k))
    (exitUp_mem_solid p k hk) _ (exitDown_mem_solid p k) i
  intro s
  exact skin_subset_solid _ _ (exitRow_mem_skin p k hk s)

theorem exitTetherFold_mem_solid (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.exitTether k)) : (exitTetherFold p k hk).pos i ∈ skinSolid p.side (2 * p.bins + 3) := by
  apply skinSolid_mono _ (p.tether_skin_bounds k hk).2.2.2
  exact exitTetherRaw_mem_solid p k hk _

theorem exitTetherRaw_outside (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin ((exitColumnCount p k + exitRowCount p k) + exitColumnCount p k)) :
    (exitTetherRaw p k hk).pos i ∉ octahedron p.side := by
  apply exitTetherRaw_property p k hk (fun q => q ∉ octahedron p.side) _ _ _ i
  · exact columnPrefix_outside _ _
  · intro s
    exact positiveSkin_outside _ _ (by have h := p.tether_skin_bounds k hk; omega)
      (exitRow_mem_skin p k hk s)
  · intro r
    exact (exitTargetColumn p k).point_outside r.rev.val

theorem exitTetherFold_outside (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.exitTether k)) : (exitTetherFold p k hk).pos i ∉ octahedron p.side :=
  exitTetherRaw_outside p k hk _

theorem exitTetherRaw_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin ((exitColumnCount p k + exitRowCount p k) + exitColumnCount p k)) (hi : i.val = 0) :
    (exitTetherRaw p k hk).pos i = (exitSourceColumn p k hk).seed := by
  have hj := p.tether_skin_bounds k hk
  unfold exitTetherRaw
  rw [append_first _ _ _ _ (by unfold exitColumnCount; omega) i hi]
  unfold exitUpRows
  rw [append_first _ _ _ _ (by unfold exitColumnCount; omega) _ rfl]
  exact columnPrefix_first _ _ _ rfl

theorem exitTetherRaw_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin ((exitColumnCount p k + exitRowCount p k) + exitColumnCount p k))
    (hi : i.val + 1 = (exitColumnCount p k + exitRowCount p k) + exitColumnCount p k) :
    (exitTetherRaw p k hk).pos i = (exitTargetColumn p k).seed := by
  have hj := p.tether_skin_bounds k hk
  unfold exitTetherRaw
  rw [append_last _ _ _ _ (by unfold exitColumnCount; omega) i hi]
  apply columnPrefix_first _ _ _ _
  simp only [Fin.val_rev]
  change exitColumnCount p k - (exitColumnCount p k - 1 + 1) = 0
  omega

theorem exitTetherFold_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.exitTether k)) (hi : i.val = 0) :
    (exitTetherFold p k hk).pos i = (exitSourceColumn p k hk).seed :=
  exitTetherRaw_first p k hk _ hi

theorem exitTetherFold_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.exitTether k)) (hi : i.val + 1 = p.exitTether k) :
    (exitTetherFold p k hk).pos i = (exitTargetColumn p k).seed := by
  exact exitTetherRaw_last p k hk _ (by simpa only [exitTetherRaw_count p k hk] using hi)

end ProteinFolding.Tetrahedral.NearField
