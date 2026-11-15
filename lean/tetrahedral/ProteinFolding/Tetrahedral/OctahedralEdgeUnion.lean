import ProteinFolding.Tetrahedral.BulkMerges
import ProteinFolding.Tetrahedral.OctahedralCount

/-! The twelve edge zigzags in the explicit layer coordinates. -/

namespace ProteinFolding.Tetrahedral

theorem bulkOnDeletedEdge_A_iff (m : ℕ) {p : Site} (hpA : InASublattice p.val)
    (hp : p ∈ octahedron m) : bulkOnDeletedEdge m p ↔
      ∃ k j : Fin 4, k ≠ j ∧ tetraCoordinate m p.val k = octRadius m ∧
        tetraCoordinate m p.val j = -octRadius m := by
  constructor
  · rintro ⟨k, j, hkj, h | h⟩
    · exact ⟨k, j, hkj, h.1.2.2, h.2⟩
    · exact (sublattices_disjoint _ hpA h.1.2.1).elim
  · rintro ⟨k, j, hkj, hk, hj⟩
    exact ⟨k, j, hkj, Or.inl ⟨⟨hp, hpA, hk⟩, hj⟩⟩

theorem bulkOnDeletedEdge_B_iff (m : ℕ) {p : Site} (hpB : InBSublattice p.val)
    (hp : p ∈ octahedron m) : bulkOnDeletedEdge m p ↔
      ∃ k j : Fin 4, k ≠ j ∧ tetraCoordinate m p.val k = 2 * (m : ℤ) - 3 ∧
        tetraCoordinate m p.val j = -(2 * (m : ℤ) - 1) := by
  constructor
  · rintro ⟨k, j, hkj, h | h⟩
    · exact (sublattices_disjoint _ h.1.2.1 hpB).elim
    · exact ⟨k, j, hkj, h.2, h.1.2.2⟩
  · rintro ⟨k, j, hkj, hk, hj⟩
    exact ⟨k, j, hkj, Or.inr ⟨⟨hp, hpB, hj⟩, hk⟩⟩

theorem deleted_even_central_iff {m u v : ℕ} (hu : u < m) (hv : v < m) :
    bulkOnDeletedEdge m (evenLayerPoint 0 u v) ↔
      u = 0 ∨ u + 1 = m ∨ v = 0 ∨ v + 1 = m := by
  rw [bulkOnDeletedEdge_A_iff m (evenLayerCoordinates_inA 0 u v)
    (evenLayerPoint_mem m 0 u v (by omega) (by omega))]
  constructor
  · rintro ⟨k, j, hkj, hk, hj⟩
    fin_cases k <;> fin_cases j <;>
      dsimp [tetraCoordinate, evenLayerPoint, evenLayerCoordinates, octRadius] at hk hj
    all_goals first | exact (hkj rfl).elim | omega
  · rintro (h | h | h | h)
    · refine ⟨1, 0, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, evenLayerPoint, evenLayerCoordinates] <;> omega
    · refine ⟨0, 1, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, evenLayerPoint, evenLayerCoordinates, octRadius] <;> omega
    · refine ⟨3, 2, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, evenLayerPoint, evenLayerCoordinates] <;> omega
    · refine ⟨2, 3, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, evenLayerPoint, evenLayerCoordinates, octRadius] <;> omega

theorem deleted_even_positive_iff {m j u v : ℕ} (hj : 1 ≤ j)
    (hu : u < m - j) (hv : v < m - j) :
    bulkOnDeletedEdge m (evenLayerPoint j u v) ↔
      (u = 0 ∨ u + 1 = m - j) ∧ (v = 0 ∨ v + 1 = m - j) := by
  rw [bulkOnDeletedEdge_A_iff m (evenLayerCoordinates_inA j u v) (evenLayerPoint_mem m j u v hu hv)]
  constructor
  · rintro ⟨k, l, hkl, hk, hl⟩
    fin_cases k <;> fin_cases l <;>
      dsimp [tetraCoordinate, evenLayerPoint, evenLayerCoordinates, octRadius] at hk hl
    all_goals first | exact (hkl rfl).elim | omega
  · rintro ⟨h | h, h' | h'⟩
    · refine ⟨1, 2, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, evenLayerPoint, evenLayerCoordinates] <;> omega
    · refine ⟨1, 3, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, evenLayerPoint, evenLayerCoordinates, octRadius] <;> omega
    · refine ⟨0, 2, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, evenLayerPoint, evenLayerCoordinates, octRadius] <;> omega
    · refine ⟨0, 3, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, evenLayerPoint, evenLayerCoordinates, octRadius] <;> omega

theorem deleted_odd_central_iff {m u v : ℕ} (hu : u < m - 1) (hv : v < m) :
    bulkOnDeletedEdge m (oddLayerPoint 0 u v) ↔ v = 0 ∨ v + 1 = m := by
  rw [bulkOnDeletedEdge_B_iff m (oddLayerCoordinates_inB 0 u v)
    (oddLayerPoint_mem m 0 u v (by omega) (by omega))]
  constructor
  · rintro ⟨k, j, hkj, hk, hj⟩
    fin_cases k <;> fin_cases j <;>
      dsimp [tetraCoordinate, oddLayerPoint, oddLayerCoordinates, octRadius] at hk hj
    all_goals first | exact (hkj rfl).elim | omega
  · rintro (h | h)
    · refine ⟨3, 2, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, oddLayerPoint, oddLayerCoordinates, octRadius] <;> omega
    · refine ⟨2, 3, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, oddLayerPoint, oddLayerCoordinates, octRadius] <;> omega

theorem deleted_odd_positive_iff {m j u v : ℕ} (hj : 1 ≤ j)
    (hu : u < m - j - 1) (hv : v < m - j) :
    bulkOnDeletedEdge m (oddLayerPoint j u v) ↔
      (u = 0 ∨ u + 1 = m - j - 1) ∧ (v = 0 ∨ v + 1 = m - j) := by
  rw [bulkOnDeletedEdge_B_iff m (oddLayerCoordinates_inB j u v) (oddLayerPoint_mem m j u v hu hv)]
  constructor
  · rintro ⟨k, l, hkl, hk, hl⟩
    fin_cases k <;> fin_cases l <;>
      dsimp [tetraCoordinate, oddLayerPoint, oddLayerCoordinates, octRadius] at hk hl
    all_goals first | exact (hkl rfl).elim | omega
  · rintro ⟨h | h, h' | h'⟩
    · refine ⟨1, 2, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, oddLayerPoint, oddLayerCoordinates, octRadius] <;> omega
    · refine ⟨1, 3, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, oddLayerPoint, oddLayerCoordinates, octRadius] <;> omega
    · refine ⟨0, 2, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, oddLayerPoint, oddLayerCoordinates, octRadius] <;> omega
    · refine ⟨0, 3, by decide, ?_, ?_⟩ <;>
        dsimp [tetraCoordinate, oddLayerPoint, oddLayerCoordinates, octRadius] <;> omega

theorem octMirrorFace_involutive (i : Fin 4) : octMirrorFace (octMirrorFace i) = i := by
  revert i
  decide

theorem octMirrorFace_injective : Function.Injective octMirrorFace :=
  Function.LeftInverse.injective octMirrorFace_involutive

theorem deletedEdge_octMirror (m : ℕ) {p : Site} (hp : bulkOnDeletedEdge m p) :
    bulkOnDeletedEdge m (octMirror p) := by
  obtain ⟨k, j, hkj, hp | hp⟩ := hp
  · refine ⟨octMirrorFace k, octMirrorFace j, fun he => hkj (octMirrorFace_injective he),
      Or.inl ⟨⟨(octMirror_mem_octahedron m p).mpr hp.1.1,
        octMirrorCoordinates_inA hp.1.2.1, ?_⟩, ?_⟩⟩
    · rw [tetraCoordinate_octMirror, octMirrorFace_involutive]
      exact hp.1.2.2
    · rw [tetraCoordinate_octMirror, octMirrorFace_involutive]
      exact hp.2
  · refine ⟨octMirrorFace k, octMirrorFace j, fun he => hkj (octMirrorFace_injective he),
      Or.inr ⟨⟨(octMirror_mem_octahedron m p).mpr hp.1.1,
        octMirrorCoordinates_inB hp.1.2.1, ?_⟩, ?_⟩⟩
    · rw [tetraCoordinate_octMirror, octMirrorFace_involutive]
      exact hp.1.2.2
    · rw [tetraCoordinate_octMirror, octMirrorFace_involutive]
      exact hp.2

theorem deletedEdge_octMirror_iff (m : ℕ) (p : Site) :
    bulkOnDeletedEdge m (octMirror p) ↔ bulkOnDeletedEdge m p := by
  constructor
  · intro hp
    simpa only [octMirror_involutive] using deletedEdge_octMirror m hp
  · exact deletedEdge_octMirror m

end ProteinFolding.Tetrahedral
