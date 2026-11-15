import ProteinFolding.Tetrahedral.NearFieldSeparatorCaps

/-! The actual separator caps have exact endpoints, colours, bounds, and bulk clearance. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

theorem separatorFirstH_mem_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)) ∈ hSupport (p.separatorWord k) (separatorFold p k hk) := by
  rw [separatorFold_hSupport]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact dimerHIndex_mem_Hsites p.side entryEdgeFrame (6 * (k + 1)) 0 false 0 le_rfl 0

theorem separatorLastH_mem_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10) ∈ hSupport (p.separatorWord k) (separatorFold p k hk) := by
  rw [separatorFold_hSupport]
  apply Finset.mem_union_right
  exact dimerHIndex_mem_Hsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 true 2 le_rfl 1

theorem cappedSeparatorFold_sites (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side) (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10)) :
    foldSites (cappedSeparatorFold p k hk C D hC hD) =
      ({C.seed} ∪ foldSites (separatorFold p k hk)) ∪ {D.seed} := cappedWordFold_sites _ _ _ _ _ _ _ _ _

theorem cappedSeparatorFold_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side) (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (i : Fin (capWord (p.separatorWord k)).length) (hi : i.val = 0) :
    (cappedSeparatorFold p k hk C D hC hD).pos i = C.seed := cappedWordFold_first _ _ _ _ _ _ _ _ _ i hi

theorem cappedSeparatorFold_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side) (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (i : Fin (capWord (p.separatorWord k)).length) (hi : i.val + 1 = (capWord (p.separatorWord k)).length) :
    (cappedSeparatorFold p k hk C D hC hD).pos i = D.seed := cappedWordFold_last _ _ _ _ _ _ _ _ _ i hi

theorem cappedSeparatorFold_mem_solid (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side) (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (i : Fin (capWord (p.separatorWord k)).length) :
    (cappedSeparatorFold p k hk C D hC hD).pos i ∈ skinSolid p.side (2 * p.bins + 3) := by
  have hmem := (mem_foldSites (cappedSeparatorFold p k hk C D hC hD) _).mpr ⟨i, rfl⟩
  rw [cappedSeparatorFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]
    exact skinSolid_mono p.side (by omega : 1 ≤ 2 * p.bins + 3) C.point_zero_mem_solid_one
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    rw [← hj]
    exact separatorFold_mem_solid p k hk j
  · rw [h]
    exact skinSolid_mono p.side (by omega : 1 ≤ 2 * p.bins + 3) D.point_zero_mem_solid_one

theorem cappedSeparatorFold_ne_bulkEndColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side) (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (E : DanglingColumn p.side) (hE : E.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side E.owner).card = 1)
    (i : Fin (capWord (p.separatorWord k)).length) (n : ℕ) :
    (cappedSeparatorFold p k hk C D hC hD).pos i ≠ E.point n := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hCm : C.owner ∈ edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0 := by
    rw [hC]; exact dimerHIndex_mem_Hsites p.side entryEdgeFrame _ _ false 0 le_rfl 0
  have hDm : D.owner ∈ edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 := by
    rw [hD]; exact dimerHIndex_mem_Hsites p.side exitEdgeFrame _ _ true 2 le_rfl 1
  intro heq
  have hmem := (mem_foldSites (cappedSeparatorFold p k hk C D hC hD) _).mpr ⟨i, heq⟩
  rw [cappedSeparatorFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact edgeDimerCap_ne_bulkColumn hm entryEdgeFrame _ _ (separatorEntry_room p k hk) C hCm E hE n h.symm
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    exact separatorFold_ne_bulkEndColumn p k hk E hE hend j n hj
  · exact edgeDimerCap_ne_bulkColumn hm exitEdgeFrame _ _ (separatorExit_room p k) D hDm E hE n h.symm

end ProteinFolding.Tetrahedral.NearField
