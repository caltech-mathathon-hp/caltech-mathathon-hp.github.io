import ProteinFolding.Tetrahedral.NearFieldSeparatorEndpoints
import ProteinFolding.Tetrahedral.NearFieldSeparatorSupport

/-! The two exterior P caps are included in a single fold of the whole separator unit. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

theorem danglingCap_ne_tether_of_owner_inA (p : ConstructionParameters) (t : TetherIndex p)
    (C : DanglingColumn p.side) (hA : InASublattice C.owner.val) (i : Fin (tetherCount p t)) :
    C.seed ≠ (tetherFold p t).pos i := by
  apply danglingCap_ne_tetherFold p t C _ _ i
  · intro heq
    rw [heq] at hA
    exact sublattices_disjoint _ hA (tetherSource_owner_inB p t)
  · intro heq
    rw [heq] at hA
    exact sublattices_disjoint _ hA (tetherTarget_owner_inB p t)

theorem separatorFold_ne_first_cap (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C : DanglingColumn p.side) (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (i : Fin (p.separatorWord k).length) : (separatorFold p k hk).pos i ≠ C.seed := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hCm : C.owner ∈ edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0 := by
    rw [hC]
    exact dimerHIndex_mem_Hsites p.side entryEdgeFrame (6 * (k + 1)) 0 false 0 le_rfl 0
  have hA : InASublattice C.owner.val := by rw [hC]; exact separatorFirstH_inA p k
  apply separatorFold_property p k hk (fun x => x ≠ C.seed) _ _ _ _ _ i
  · exact edgeDimerFold_ne_first_cap hm entryEdgeFrame (6 * (k + 1)) 0 false (separatorEntry_room p k hk) C hC
  · intro j
    rw [entryTetherWordFold_pos]
    simpa only [tetherFold] using (danglingCap_ne_tether_of_owner_inA p (false, ⟨k, by omega⟩) C hA ⟨j.val, by simpa using j.isLt⟩).symm
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm trackEdgeFrame (2 * p.separatorIndex k) 1 true
      (separatorCenter_room p k hk) C
      (fun hx => Finset.disjoint_left.mp (separatorEntry_center_Hdisjoint p k k hk hk) hCm hx)
  · intro j
    rw [exitTetherWordFold_pos]
    simpa only [tetherFold] using (danglingCap_ne_tether_of_owner_inA p (true, ⟨k, by omega⟩) C hA ⟨j.val, by simpa using j.isLt⟩).symm
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm exitEdgeFrame (10 * p.exitSlot k + 6) 2 true
      (separatorExit_room p k) C
      (fun hx => Finset.disjoint_left.mp (separatorEntry_exit_Hdisjoint p k k hk) hCm hx)

theorem separatorFold_ne_last_cap (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (D : DanglingColumn p.side) (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (i : Fin (p.separatorWord k).length) : (separatorFold p k hk).pos i ≠ D.seed := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hDm : D.owner ∈ edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 := by
    rw [hD]
    exact dimerHIndex_mem_Hsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 true 2 le_rfl 1
  have hA : InASublattice D.owner.val := by rw [hD]; exact separatorLastH_inA p k
  apply separatorFold_property p k hk (fun x => x ≠ D.seed) _ _ _ _ _ i
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm entryEdgeFrame (6 * (k + 1)) 0 false
      (separatorEntry_room p k hk) D
      (fun hx => Finset.disjoint_left.mp (separatorEntry_exit_Hdisjoint p k k hk) hx hDm)
  · intro j
    rw [entryTetherWordFold_pos]
    simpa only [tetherFold] using (danglingCap_ne_tether_of_owner_inA p (false, ⟨k, by omega⟩) D hA ⟨j.val, by simpa using j.isLt⟩).symm
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm trackEdgeFrame (2 * p.separatorIndex k) 1 true
      (separatorCenter_room p k hk) D
      (fun hx => Finset.disjoint_left.mp (separatorCenter_exit_Hdisjoint p k k hk) hx hDm)
  · intro j
    rw [exitTetherWordFold_pos]
    simpa only [tetherFold] using (danglingCap_ne_tether_of_owner_inA p (true, ⟨k, by omega⟩) D hA ⟨j.val, by simpa using j.isLt⟩).symm
  · exact edgeDimerFold_ne_last_cap hm exitEdgeFrame (10 * p.exitSlot k + 6) 2 true (separatorExit_room p k) D hD

theorem separatorCaps_ne (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side) (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10)) : C.seed ≠ D.seed := by
  apply dangling_caps_ne_of_owner_ne p.side C.owner D.owner C.dir D.dir C.owner_mem D.owner_mem C.seed_outside
  intro heq
  have hc := dimerHIndex_mem_Hsites p.side entryEdgeFrame (6 * (k + 1)) 0 false 0 le_rfl 0
  have hd := dimerHIndex_mem_Hsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 true 2 le_rfl 1
  change octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)) ∈ _ at hc
  change octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10) ∈ _ at hd
  rw [← hC, heq] at hc
  rw [← hD] at hd
  exact Finset.disjoint_left.mp (separatorEntry_exit_Hdisjoint p k k hk) hc hd

def cappedSeparatorFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side) (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10)) :
    Fold tetrahedralLattice (capWord (p.separatorWord k)).length :=
  cappedWordFold (separatorFold p k hk) C.seed D.seed (separatorWord_length_pos p k)
    (fun i => (separatorFold_ne_first_cap p k hk C hC i).symm) (separatorFold_ne_last_cap p k hk D hD)
    (separatorCaps_ne p k hk C D hC hD)
    (fun i hi => by rw [separatorFold_first p k hk i hi, ← hC]; exact (step_adj _ _).symm)
    (fun i hi => by rw [separatorFold_last p k hk i hi, ← hD]; exact step_adj _ _)

theorem cappedSeparatorFold_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side) (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10)) :
    hSupport (capWord (p.separatorWord k)) (cappedSeparatorFold p k hk C D hC hD) =
      hSupport (p.separatorWord k) (separatorFold p k hk) :=
  cappedWordFold_hSupport _ _ _ _ _ _ _ _ _

end ProteinFolding.Tetrahedral.NearField
