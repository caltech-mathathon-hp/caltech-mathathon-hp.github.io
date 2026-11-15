import ProteinFolding.Tetrahedral.NearFieldSeparatorObstacleOwners
import ProteinFolding.Tetrahedral.NearFieldCanonicalSeparatorPieces

/-! Disjoint physical H supports separate every complete track interval
from a complete separator, including both sides' local caps and tethers. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 500000
set_option maxRecDepth 4096

theorem edgeDimerFold_ne_separatorFold_of_Hdis (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * p.side - 1) (hpair : F.k ≠ 2 ∨ F.j ≠ 3)
    (hdis : Disjoint (hSupport (p.separatorWord k) (separatorFold p k hk))
      (edgeDimerHsites p.side F base q))
    (i : Fin (dimerChain (q + 1)).length) (j : Fin (p.separatorWord k).length) :
    (edgeDimerFold (m := p.side) (by have h := p.side_ge; omega) F base q reverse hroom).pos i ≠
      (separatorFold p k hk).pos j := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hE : Disjoint (edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0)
      (edgeDimerHsites p.side F base q) := Finset.disjoint_left.mpr
    (fun x hx hy => Finset.disjoint_left.mp hdis (separatorEntryHsites_subset_hSupport p k hk hx) hy)
  have hM : Disjoint (edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k) 1)
      (edgeDimerHsites p.side F base q) := Finset.disjoint_left.mpr
    (fun x hx hy => Finset.disjoint_left.mp hdis (separatorCenterHsites_subset_hSupport p k hk hx) hy)
  have hX : Disjoint (edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2)
      (edgeDimerHsites p.side F base q) := Finset.disjoint_left.mpr
    (fun x hx hy => Finset.disjoint_left.mp hdis (separatorExitHsites_subset_hSupport p k hk hx) hy)
  have hs (b : Bool) : DimerLinkOwnerExcluded p.side F base q reverse
      (tetherSourceColumn p (b, ⟨k, by omega⟩)).owner :=
    dimerLinkOwnerExcluded_of_not_mem p.side F base q reverse _
      (fun h => Finset.disjoint_left.mp hdis (separator_tetherSource_mem_hSupport p k hk b) h)
  have ht (b : Bool) : DimerLinkOwnerExcluded p.side F base q reverse
      (tetherTargetColumn p (b, ⟨k, by omega⟩)).owner :=
    dimerLinkOwnerExcluded_of_not_mem p.side F base q reverse _
      (fun h => Finset.disjoint_left.mp hdis (separator_tetherTarget_mem_hSupport p k hk b) h)
  apply separatorFold_property p k hk (fun x => (edgeDimerFold hm F base q reverse hroom).pos i ≠ x) _ _ _ _ _ j
  · intro s
    exact edgeDimerFolds_disjoint hm F entryEdgeFrame base q (6 * (k + 1)) 0 reverse false
      hroom (separatorEntry_room p k hk) hE.symm i s
  · intro s
    rw [entryTetherWordFold_pos]
    simpa only [tetherFold] using edgeDimerFold_ne_tetherFold p (false, ⟨k, by omega⟩)
      F base q reverse hroom (fun _ => hpair) (hs false) (ht false) i
      ⟨s.val, by simpa only [List.length_replicate] using s.isLt⟩
  · intro s
    exact edgeDimerFolds_disjoint hm F trackEdgeFrame base q (2 * p.separatorIndex k) 1 reverse true
      hroom (separatorCenter_room p k hk) hM.symm i s
  · intro s
    rw [exitTetherWordFold_pos]
    simpa only [tetherFold] using edgeDimerFold_ne_tetherFold p (true, ⟨k, by omega⟩)
      F base q reverse hroom (fun _ => hpair) (hs true) (ht true) i
      ⟨s.val, by simpa only [List.length_replicate] using s.isLt⟩
  · intro s
    exact edgeDimerFolds_disjoint hm F exitEdgeFrame base q (10 * p.exitSlot k + 6) 2 reverse true
      hroom (separatorExit_room p k) hX.symm i s

theorem edgeDimerFold_ne_cappedSeparator_of_Hdis (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * p.side - 1) (hpair : F.k ≠ 2 ∨ F.j ≠ 3)
    (hdis : Disjoint (hSupport (p.separatorWord k) (separatorFold p k hk))
      (edgeDimerHsites p.side F base q))
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (i : Fin (dimerChain (q + 1)).length) (j : Fin (capWord (p.separatorWord k)).length) :
    (edgeDimerFold (m := p.side) (by have h := p.side_ge; omega) F base q reverse hroom).pos i ≠
      (cappedSeparatorFold p k hk C D hC hD).pos j := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hCnot : C.owner ∉ edgeDimerHsites p.side F base q := by
    intro h
    apply Finset.disjoint_left.mp hdis _ h
    rw [hC]
    exact separatorFirstH_mem_hSupport p k hk
  have hDnot : D.owner ∉ edgeDimerHsites p.side F base q := by
    intro h
    apply Finset.disjoint_left.mp hdis _ h
    rw [hD]
    exact separatorLastH_mem_hSupport p k hk
  exact frameTrack_property_of_capped_sites (cappedSeparatorFold p k hk C D hC hD) (separatorFold p k hk)
    C.seed D.seed (cappedSeparatorFold_sites p k hk C D hC hD)
    (fun x => (edgeDimerFold hm F base q reverse hroom).pos i ≠ x)
    (edgeDimerFold_ne_cap_of_owner_not_mem hm F base q reverse hroom C hCnot i)
    (edgeDimerFold_ne_separatorFold_of_Hdis p k hk F base q reverse hroom hpair hdis i)
    (edgeDimerFold_ne_cap_of_owner_not_mem hm F base q reverse hroom D hDnot i) j

theorem cappedInterval_ne_cappedSeparator_of_Hdis (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F : OctEdgeFrame) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * p.side - 1) (hpair : F.k ≠ 2 ∨ F.j ≠ 3)
    (hdis : Disjoint (hSupport (p.separatorWord k) (separatorFold p k hk))
      (edgeDimerHsites p.side F base (n - 1)))
    (A B : DanglingColumn p.side)
    (hA : A.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hB : B.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (n - 1) 1))
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (i : Fin (capWord (dimerChain n)).length) (j : Fin (capWord (p.separatorWord k)).length) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      F base n hn reverse hroom A B hA hB).pos i ≠ (cappedSeparatorFold p k hk C D hC hD).pos j := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hAm : A.owner ∈ edgeDimerHsites p.side F base (n - 1) := by
    rw [hA]
    exact dimerHIndex_mem_Hsites p.side F base (n - 1) reverse 0 (by omega) 0
  have hBm : B.owner ∈ edgeDimerHsites p.side F base (n - 1) := by
    rw [hB]
    exact dimerHIndex_mem_Hsites p.side F base (n - 1) reverse (n - 1) le_rfl 1
  have hAnot : A.owner ∉ hSupport (p.separatorWord k) (separatorFold p k hk) :=
    fun h => Finset.disjoint_left.mp hdis h hAm
  have hBnot : B.owner ∉ hSupport (p.separatorWord k) (separatorFold p k hk) :=
    fun h => Finset.disjoint_left.mp hdis h hBm
  unfold cappedIntervalDimerFold
  refine transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold hm F base (n - 1) reverse (by omega) A B hA hB)
    (fun x => x ≠ (cappedSeparatorFold p k hk C D hC hD).pos j) ?_ i
  intro r
  exact cappedEdgeDimerFold_property hm F base (n - 1) reverse (by omega) A B hA hB
    (fun x => x ≠ (cappedSeparatorFold p k hk C D hC hD).pos j)
    (cappedSeparatorFold_ne_cap_of_owner_not_mem_all p k hk C D hC hD A hAnot j).symm
    (fun s => edgeDimerFold_ne_cappedSeparator_of_Hdis p k hk F base (n - 1) reverse
      (by omega) hpair hdis C D hC hD s j)
    (cappedSeparatorFold_ne_cap_of_owner_not_mem_all p k hk C D hC hD B hBnot j).symm r

end ProteinFolding.Tetrahedral.NearField
