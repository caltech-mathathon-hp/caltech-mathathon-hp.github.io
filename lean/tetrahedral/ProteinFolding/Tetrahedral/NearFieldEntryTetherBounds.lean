import ProteinFolding.Tetrahedral.NearFieldTetherSupport

/-! Exact caps, externality, and the uniform near-field solid bound of all
entry tethers. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem entryUp_mem_solid (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) : (entryUp p k hk).pos i ∈ skinSolid p.side (p.entrySkin k) :=
  borrowedPrefix_mem_solid p.side (entryAnchorA p k) (3 * (k + 1)) 0
    (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) (p.entrySkin k)
    (by have h := p.tether_skin_bounds k hk; omega) i

theorem entryDown_mem_solid (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) : (entryDown p k hk).pos i ∈ skinSolid p.side (p.entrySkin k) :=
  columnPrefix_mem_solid (entryTargetColumn p k hk) _ (by have h := p.tether_skin_bounds k hk; omega) i.rev

theorem entryTetherFold_mem_solid (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.entryTether k)) : (entryTetherFold p k hk).pos i ∈ skinSolid p.side (2 * p.bins + 3) := by
  apply skinSolid_mono _ (show p.entrySkin k ≤ 2 * p.bins + 3 by have h := p.tether_skin_bounds k hk; omega)
  apply entryTetherFold_property p k hk (fun q => q ∈ skinSolid p.side (p.entrySkin k))
    (entryUp_mem_solid p k hk) _ (entryDown_mem_solid p k hk) i
  intro r
  exact skin_subset_solid _ _ (entryRow_mem_skin p k hk r)

theorem entryTetherFold_outside (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.entryTether k)) : (entryTetherFold p k hk).pos i ∉ octahedron p.side := by
  apply entryTetherFold_property p k hk (fun q => q ∉ octahedron p.side) _ _ _ i
  · intro r
    exact borrowedPoint_outside p.side (entryAnchorA p k) (3 * (k + 1)) 0
      (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) r.val
  · intro r
    exact positiveSkin_outside _ _ (by have h := p.tether_skin_bounds k hk; omega)
      (entryRow_mem_skin p k hk r)
  · intro r
    exact (entryTargetColumn p k hk).point_outside r.rev.val

theorem entryTetherRaw_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (((2 * p.entrySkin k - 1) + entryRowCount p k) + (2 * p.entrySkin k - 1)))
    (hi : i.val = 0) : (entryTetherRaw p k hk).pos i =
      (faceDanglingColumn p.side (entryAnchorA p k) (3 * (k + 1)) 0 (entryAnchor_equation p k hk)).seed := by
  have hj := p.tether_skin_bounds k hk
  unfold entryTetherRaw
  rw [append_first _ _ _ _ (by omega) i hi]
  unfold entryUpRows
  rw [append_first _ _ _ _ (by omega) _ rfl]
  exact borrowedPrefix_first p.side (entryAnchorA p k) (3 * (k + 1)) 0
    (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) (p.entrySkin k) _ rfl

theorem entryTetherRaw_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (((2 * p.entrySkin k - 1) + entryRowCount p k) + (2 * p.entrySkin k - 1)))
    (hi : i.val + 1 = ((2 * p.entrySkin k - 1) + entryRowCount p k) + (2 * p.entrySkin k - 1)) :
    (entryTetherRaw p k hk).pos i = (entryTargetColumn p k hk).seed := by
  have hj := p.tether_skin_bounds k hk
  unfold entryTetherRaw
  rw [append_last _ _ _ _ (by omega) i hi]
  apply columnPrefix_first _ _ _ _
  simp only [Fin.val_rev]
  omega

theorem entryTetherFold_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.entryTether k)) (hi : i.val = 0) : (entryTetherFold p k hk).pos i =
      (faceDanglingColumn p.side (entryAnchorA p k) (3 * (k + 1)) 0 (entryAnchor_equation p k hk)).seed :=
  entryTetherRaw_first p k hk _ hi

theorem entryTetherFold_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.entryTether k)) (hi : i.val + 1 = p.entryTether k) :
    (entryTetherFold p k hk).pos i = (entryTargetColumn p k hk).seed := by
  exact entryTetherRaw_last p k hk _ (by simpa only [entryTetherRaw_count p k hk] using hi)

end ProteinFolding.Tetrahedral.NearField
