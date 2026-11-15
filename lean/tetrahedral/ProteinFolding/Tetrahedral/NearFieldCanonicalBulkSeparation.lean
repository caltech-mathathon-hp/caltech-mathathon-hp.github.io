import ProteinFolding.Tetrahedral.NearFieldCanonicalTerminalSeparation

/-! Whole capped bulk units avoid every actual nonbulk local family. Bulk
bodies lie in bulkInterior; the two exterior caps use its actual leaf columns. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Keep the construction size symbolic during elaboration of finite-set facts.
-- The two scalar identities below unfold its defining equation explicitly.
attribute [local irreducible] ConstructionParameters.side

private theorem outside_not_mem_bulk {m : ℕ} {x : Site} (hx : x ∉ octahedron m) :
    x ∉ bulkInterior m := fun h => hx (Finset.mem_sdiff.mp h).1

private theorem deleted_not_mem_bulk {m : ℕ} {x : Site} (hx : x ∈ bulkDeletedEdges m) :
    x ∉ bulkInterior m := fun h => (Finset.mem_sdiff.mp h).2 hx

theorem edgeDimerFold_not_mem_bulkInterior {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (i : Fin (dimerChain (q + 1)).length) :
    (edgeDimerFold hm F base q reverse hroom).pos i ∉ bulkInterior m := by
  rcases edgeDimerFold_pos_cases hm F base q reverse hroom i with
      ⟨j, hj, s, hs⟩ | ⟨j, hj, s, hs⟩
  · rw [hs]
    exact deleted_not_mem_bulk (edgeDimerHsites_subset_deleted hm F base q hroom
      (dimerHIndex_mem_Hsites m F base q reverse j hj s))
  · rw [hs]
    have hb := dimerLinkIndex_bounds base reverse j
    exact outside_not_mem_bulk (edgePPPFold_outside hm F _ (by omega) s)

theorem cappedInterval_not_mem_bulkInterior {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (base n : ℕ) (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1))
    (i : Fin (capWord (dimerChain n)).length) :
    (cappedIntervalDimerFold hm F base n hn reverse hroom C D hC hD).pos i ∉ bulkInterior m := by
  apply transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold hm F base (n - 1) reverse (by omega) C D hC hD)
    (fun x => x ∉ bulkInterior m) _ i
  exact cappedEdgeDimerFold_property hm F base (n - 1) reverse (by omega) C D hC hD
    (fun x => x ∉ bulkInterior m) (outside_not_mem_bulk C.seed_outside)
    (edgeDimerFold_not_mem_bulkInterior hm F base (n - 1) reverse (by omega))
    (outside_not_mem_bulk D.seed_outside)

theorem canonicalSingletonPiece_not_mem_bulkInterior (p : ConstructionParameters) (r : Fin 3)
    (i : Fin (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).word.length) :
    (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).fold.pos i ∉ bulkInterior p.side := by
  have hmem := (mem_foldSites
    (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).fold _).mpr ⟨i, rfl⟩
  rw [canonicalSingletonPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]
    exact outside_not_mem_bulk
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r false).seed_outside
  · rw [h]
    exact deleted_not_mem_bulk (canonicalSingletonColumn_owner_deleted p.side
      (by have h := p.side_ge; omega) r false)
  · rw [h]
    exact outside_not_mem_bulk
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r true).seed_outside

theorem canonicalItemPiece_not_mem_bulkInterior (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ∉ bulkInterior p.side :=
  cappedInterval_not_mem_bulkInterior (m := p.side) (by have h := p.side_ge; omega)
    trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s)
    (by have h := p.itemDimers_ge s hs; omega) false (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload) i

theorem canonicalRightPiece_not_mem_bulkInterior (p : ConstructionParameters)
    (i : Fin (canonicalRightPiece p).word.length) :
    (canonicalRightPiece p).fold.pos i ∉ bulkInterior p.side :=
  cappedInterval_not_mem_bulkInterior (m := p.side) (by have h := p.side_ge; omega)
    trackEdgeFrame (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega)
    false (rightFillerTrackBase_room p) (rightFirstColumn p) (rightFinalColumn p) rfl
    (by
      rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
      have he : rightFillerTrackBase p + 2 * p.rightFiller - 1 = 2 * p.side - 3 := by
        have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := by
          simp only [ConstructionParameters.side]
        dsimp [rightFillerTrackBase]
        omega
      rw [he]
      exact rightFinalColumn_track_owner p) i

theorem leftFillerFold_not_mem_bulkInterior (p : ConstructionParameters)
    (i : Fin (dimerChain p.leftFiller).length) : (leftFillerFold p).pos i ∉ bulkInterior p.side := by
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hi
  · exact deleted_not_mem_bulk (edgeZigzag_mem_deleted (by have h := p.side_ge; omega)
      entryEdgeFrame 2 (by have h := p.side_ge; omega))
  · let j : Fin (dimerChain (p.leftFiller - 1 + 1)).length :=
      ⟨i.val, by
        have hlen := dimerChain_succ_length (p.leftFiller - 1)
        have hword := leftFiller_word_length p
        have hi := i.isLt
        omega⟩
    have h := edgeDimerFold_not_mem_bulkInterior (by have h := p.side_ge; omega : 1 ≤ p.side)
      trackEdgeFrame 0 (p.leftFiller - 1) false (leftFiller_room p) j
    rw [edgeDimerFold_pos] at h
    exact h

theorem canonicalLeftPiece_not_mem_bulkInterior (p : ConstructionParameters)
    (i : Fin (canonicalLeftPiece p).word.length) :
    (canonicalLeftPiece p).fold.pos i ∉ bulkInterior p.side :=
  frameTrack_property_of_capped_sites _ _ _ _
    (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p))
    (fun x => x ∉ bulkInterior p.side)
    (outside_not_mem_bulk (entryLocalColumn p none).seed_outside)
    (leftFillerFold_not_mem_bulkInterior p)
    (outside_not_mem_bulk (leftLastColumn p).seed_outside) i

theorem separatorFold_not_mem_bulkInterior (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.separatorWord k).length) : (separatorFold p k hk).pos i ∉ bulkInterior p.side := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply separatorFold_property p k hk (fun x => x ∉ bulkInterior p.side) _ _ _ _ _ i
  · exact edgeDimerFold_not_mem_bulkInterior hm entryEdgeFrame (6 * (k + 1)) 0 false
      (separatorEntry_room p k hk)
  · intro j
    rw [entryTetherWordFold_pos]
    exact outside_not_mem_bulk (entryTetherFold_outside p k hk ⟨j.val, by simpa using j.isLt⟩)
  · exact edgeDimerFold_not_mem_bulkInterior hm trackEdgeFrame (2 * p.separatorIndex k) 1 true
      (separatorCenter_room p k hk)
  · intro j
    rw [exitTetherWordFold_pos]
    exact outside_not_mem_bulk (exitTetherFold_outside p k hk ⟨j.val, by simpa using j.isLt⟩)
  · exact edgeDimerFold_not_mem_bulkInterior hm exitEdgeFrame (10 * p.exitSlot k + 6) 2 true
      (separatorExit_room p k)

theorem canonicalSeparatorPiece_not_mem_bulkInterior (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (i : Fin (canonicalSeparatorPiece p k).word.length) :
    (canonicalSeparatorPiece p k).fold.pos i ∉ bulkInterior p.side :=
  frameTrack_property_of_capped_sites _ _ _ _
    (cappedSeparatorFold_sites p k.val (by have h := k.isLt; omega) _ _ rfl
      (exitCapColumn_owner p k.val (by have h := k.isLt; omega)))
    (fun x => x ∉ bulkInterior p.side)
    (outside_not_mem_bulk (entryLocalColumn p (some k)).seed_outside)
    (separatorFold_not_mem_bulkInterior p k.val (by have h := k.isLt; omega))
    (outside_not_mem_bulk (exitCapColumn p k.val (by have h := k.isLt; omega)).seed_outside) i

theorem frameHRunFold_not_mem_bulkInterior (p : ConstructionParameters) (j : FrameHRunIndex p)
    (i : Fin (frameHRunWord p j).length) : (frameHRunFold p j).pos i ∉ bulkInterior p.side := by
  have hmem := (mem_foldSites (frameHRunFold p j) _).mpr ⟨i, rfl⟩
  rw [frameHRunFold_sites] at hmem
  obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hmem
  have ht' := Finset.mem_range.mp ht
  have hr := frameHRun_room p j
  have hd := edgeZigzag_mem_deleted (by have h := p.side_ge; omega : 1 ≤ p.side)
    (frameHRunData p j).frame ((frameHRunData p j).base + t) (by omega)
  rw [heq] at hd
  exact deleted_not_mem_bulk hd

theorem frameCoreFold_not_mem_bulkInterior (p : ConstructionParameters)
    (i : Fin (p.framePart1 ++ p.framePart2).length) : (frameCoreFold p).pos i ∉ bulkInterior p.side := by
  apply frameCoreFold_property p (fun x => x ∉ bulkInterior p.side) _ i
  intro j s
  rcases j with j | j
  · exact frameHRunFold_not_mem_bulkInterior p j s
  · dsimp only [frameCorePiece, frameLinkPiece] at s ⊢
    rw [frameLinkWordFold_pos]
    exact outside_not_mem_bulk (positiveSkin_outside p.side 1 (by decide) (frameLinkFold_mem_skin_one p j _))

theorem frameFold_not_mem_bulkInterior (p : ConstructionParameters) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ∉ bulkInterior p.side :=
  frameTrack_property_of_capped_sites _ _ _ _ (frameFold_sites p)
    (fun x => x ∉ bulkInterior p.side)
    (outside_not_mem_bulk (frameFirstColumn p).seed_outside)
    (frameCoreFold_not_mem_bulkInterior p)
    (outside_not_mem_bulk (frameLastColumn p).seed_outside) i

theorem canonicalSingletonPiece_ne_bulkEndColumn (p : ConstructionParameters) (r : Fin 3)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (i : Fin (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).word.length) (n : ℕ) :
    (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).fold.pos i ≠ C.point n := by
  have hmem := (mem_foldSites
    (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).fold _).mpr ⟨i, rfl⟩
  rw [canonicalSingletonPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]
    exact canonicalSingletonColumn_ne_bulkColumn p.side (by have h := p.side_ge; omega) r false C hC 0 n
  · rw [h]
    intro heq
    exact C.point_outside n (heq ▸ canonicalSingletonOwner_mem p.side (by have h := p.side_ge; omega) r)
  · rw [h]
    exact canonicalSingletonColumn_ne_bulkColumn p.side (by have h := p.side_ge; omega) r true C hC 0 n

theorem canonicalLeftPiece_ne_bulkEndColumn (p : ConstructionParameters)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1)
    (i : Fin (canonicalLeftPiece p).word.length) (n : ℕ) :
    (canonicalLeftPiece p).fold.pos i ≠ C.point n := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply frameTrack_property_of_capped_sites _ _ _ _
    (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p))
    (fun x => x ≠ C.point n) _ (fun j => leftFillerFold_ne_bulkEndColumn p C hC hend j n) _ i
  · exact (bulkColumn_ne_edgeColumn C (entryLocalColumn p none) hC
      (edgeZigzag_mem_deleted hm entryEdgeFrame 2 (by have h := p.side_ge; omega)) n 0).symm
  · apply Ne.symm
    apply bulkColumn_ne_edgeColumn C (leftLastColumn p) hC _ n 0
    rw [leftLastColumn_owner]
    have hroom := leftFiller_room p
    have hpos := p.leftFiller_ge
    exact edgeZigzag_mem_deleted hm trackEdgeFrame _ (by omega)

theorem frameEndpointColumn_owner_deleted (p : ConstructionParameters) (b : Bool) :
    (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).owner ∈ bulkDeletedEdges p.side := by
  change frameEndpointVertex p.side b ∈ _
  rw [frameEndpointVertex_eq_edge]
  cases b <;> exact edgeZigzag_mem_deleted (by have h := p.side_ge; omega) _ 0
    (by have h := p.side_ge; omega)

theorem frameFold_ne_bulkEndColumn (p : ConstructionParameters)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (i : Fin p.frameWord.length) (n : ℕ) : (frameFold p).pos i ≠ C.point n := by
  apply frameTrack_property_of_capped_sites _ _ _ _ (frameFold_sites p)
    (fun x => x ≠ C.point n) _ _ _ i
  · exact (bulkColumn_ne_edgeColumn C (frameFirstColumn p) hC (frameEndpointColumn_owner_deleted p true) n 0).symm
  · intro k
    apply frameCoreFold_ne_column_of_links p C n _ k
    intro j s
    rw [frameLinkFold_pos_eq_framePoint]
    exact bulkColumn_ne_frameP C hC (frameLinkKind j) (frameLinkParameter_odd p j)
      (frameLinkParameter_ge p j) (frameLinkParameter_room p j) n (frameLinkInteriorIndex p j s)
      (frameLinkInteriorIndex_pos p j s) (frameLinkInteriorIndex_before_last p j s)
  · exact (bulkColumn_ne_edgeColumn C (frameLastColumn p) hC (frameEndpointColumn_owner_deleted p false) n 0).symm

theorem canonicalSeparatorPiece_ne_bulkEndColumn (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1)
    (i : Fin (canonicalSeparatorPiece p k).word.length) (n : ℕ) :
    (canonicalSeparatorPiece p k).fold.pos i ≠ C.point n :=
  cappedSeparatorFold_ne_bulkEndColumn p k.val (by have h := k.isLt; omega) _ _ rfl
    (exitCapColumn_owner p k.val (by have h := k.isLt; omega)) C hC hend i n

theorem canonicalItemPiece_ne_bulkEndColumn (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) (n : ℕ) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ≠ C.point n :=
  cappedIntervalDimerFold_ne_bulkEndColumn p.side (by have h := p.side_ge; omega)
    trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s) (by have h := p.itemDimers_ge s hs; omega)
    false (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload) C hC hend i n

theorem canonicalRightPiece_ne_bulkEndColumn (p : ConstructionParameters)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1)
    (i : Fin (canonicalRightPiece p).word.length) (n : ℕ) :
    (canonicalRightPiece p).fold.pos i ≠ C.point n :=
  cappedIntervalDimerFold_ne_bulkEndColumn p.side (by have h := p.side_ge; omega)
    trackEdgeFrame (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega)
    false (rightFillerTrackBase_room p) (rightFirstColumn p) (rightFinalColumn p) rfl
    (by
      rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
      have he : rightFillerTrackBase p + 2 * p.rightFiller - 1 = 2 * p.side - 3 := by
        have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := by
          simp only [ConstructionParameters.side]
        dsimp [rightFillerTrackBase]
        omega
      rw [he]
      exact rightFinalColumn_track_owner p) C hC hend i n

theorem canonicalBulkPiece_sites (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) :
    foldSites (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).fold =
      ({(ReductionTM2.BulkScan.firstColumn p.side (by have h := p.side_ge; omega) ha j).seed} ∪
        foldSites (ReductionTM2.BulkScan.runtimePiece p.side (by have h := p.side_ge; omega) ha j).fold) ∪
      {(ReductionTM2.BulkScan.lastColumn p.side (by have h := p.side_ge; omega) ha j).seed} :=
  ReductionTM2.BulkScan.cappedRuntimeFoldWithColumns_sites p.side (by have h := p.side_ge; omega) ha j
    (ReductionTM2.BulkScan.firstColumn p.side (by have h := p.side_ge; omega) ha j)
    (ReductionTM2.BulkScan.lastColumn p.side (by have h := p.side_ge; omega) ha j) rfl rfl

theorem canonicalBulkPiece_disjoint_of_exclusion (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) (q : PositionedWord)
    (hout : ∀ i, q.fold.pos i ∉ bulkInterior p.side)
    (hcol : ∀ C : DanglingColumn p.side, C.owner ∈ bulkInterior p.side →
      (bulkCoverNeighbours p.side C.owner).card = 1 → ∀ i n, q.fold.pos i ≠ C.point n) :
    WordsDisjoint
      (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j) q := by
  apply (foldSites_disjoint_iff _ _).mpr
  intro i k heq
  have hmem := (mem_foldSites
    (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).fold _).mpr ⟨i, heq⟩
  rw [canonicalBulkPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact hcol (ReductionTM2.BulkScan.firstColumn p.side (by have h := p.side_ge; omega) ha j)
      (ReductionTM2.BulkScan.runtimeFirst_inside p.side (by have h := p.side_ge; omega) ha j)
      (ReductionTM2.BulkScan.runtimeFirst_degree p.side (by have h := p.side_ge; omega) ha j) k 0 h
  · exact hout k (ReductionTM2.BulkScan.runtimePiece_inside p.side (by have h := p.side_ge; omega) ha j _ h)
  · exact hcol (ReductionTM2.BulkScan.lastColumn p.side (by have h := p.side_ge; omega) ha j)
      (ReductionTM2.BulkScan.runtimeLast_inside p.side (by have h := p.side_ge; omega) ha j)
      (ReductionTM2.BulkScan.runtimeLast_degree p.side (by have h := p.side_ge; omega) ha j) k 0 h

theorem canonicalBulkPiece_singletonPiece_disjoint (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) (r : Fin 3) :
    WordsDisjoint (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j)
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r) :=
  canonicalBulkPiece_disjoint_of_exclusion p ha j _ (canonicalSingletonPiece_not_mem_bulkInterior p r)
    (fun C hC _ i n => canonicalSingletonPiece_ne_bulkEndColumn p r C hC i n)

theorem canonicalBulkPiece_frameWordPiece_disjoint (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) :
    WordsDisjoint (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j)
      (frameWordPiece p) :=
  canonicalBulkPiece_disjoint_of_exclusion p ha j _ (frameFold_not_mem_bulkInterior p)
    (fun C hC _ i n => frameFold_ne_bulkEndColumn p C hC i n)

theorem canonicalBulkPiece_separatorPiece_disjoint (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) (k : Fin (p.bins + 1)) :
    WordsDisjoint (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j)
      (canonicalSeparatorPiece p k) :=
  canonicalBulkPiece_disjoint_of_exclusion p ha j _ (canonicalSeparatorPiece_not_mem_bulkInterior p k)
    (canonicalSeparatorPiece_ne_bulkEndColumn p k)

theorem canonicalBulkPiece_leftPiece_disjoint (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) :
    WordsDisjoint (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j)
      (canonicalLeftPiece p) :=
  canonicalBulkPiece_disjoint_of_exclusion p ha j _ (canonicalLeftPiece_not_mem_bulkInterior p)
    (canonicalLeftPiece_ne_bulkEndColumn p)

theorem canonicalBulkPiece_itemPiece_disjoint (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    WordsDisjoint (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j)
      (canonicalItemPiece p k before s hk hs hload) :=
  canonicalBulkPiece_disjoint_of_exclusion p ha j _ (canonicalItemPiece_not_mem_bulkInterior p k before s hk hs hload)
    (canonicalItemPiece_ne_bulkEndColumn p k before s hk hs hload)

theorem canonicalBulkPiece_rightPiece_disjoint (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) :
    WordsDisjoint (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j)
      (canonicalRightPiece p) :=
  canonicalBulkPiece_disjoint_of_exclusion p ha j _ (canonicalRightPiece_not_mem_bulkInterior p)
    (canonicalRightPiece_ne_bulkEndColumn p)

theorem canonicalBulkPiece_ringPiece_disjoint (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) (r : Fin 3) :
    WordsDisjoint (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j)
      (canonicalRingWordPiece p r) :=
  canonicalBulkPiece_disjoint_of_exclusion p ha j _ (canonicalRingWordPiece_not_mem_bulkInterior p r)
    (canonicalRingWordPiece_ne_bulkEndColumn p r)

theorem canonicalBulkPiece_terminalWordPiece_disjoint (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) :
    WordsDisjoint (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j)
      (terminalWordPiece p) :=
  (terminalWordPiece_bulkPiece_disjoint p ha j).symm

theorem canonicalBulkPieces_disjoint (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j k : Fin (ReductionTM2.BulkScan.lengths p.side).length) (hne : j ≠ k) :
    WordsDisjoint (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j)
      (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha k) :=
  ReductionTM2.BulkScan.cappedRuntimePiecesWithColumns_disjoint p.side
    (by have h := p.side_ge; omega) ha
    (ReductionTM2.BulkScan.runtimeColumns p.side (by have h := p.side_ge; omega) ha)
    (ReductionTM2.BulkScan.runtimeColumns_owner p.side (by have h := p.side_ge; omega) ha) j k hne

theorem canonicalBulkPieces_mem_iff (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) (q : PositionedWord) :
    q ∈ ReductionTM2.BulkScan.cappedRuntimePieces p.side (by have h := p.side_ge; omega) ha ↔
      ∃ j : Fin (ReductionTM2.BulkScan.lengths p.side).length,
        ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j = q := by
  change q ∈ List.ofFn (ReductionTM2.BulkScan.cappedRuntimePiece p.side
    (by have h := p.side_ge; omega) ha) ↔ _
  exact List.mem_ofFn

theorem canonicalBulkPieces_property (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) (P : PositionedWord → Prop)
    (h : ∀ j : Fin (ReductionTM2.BulkScan.lengths p.side).length,
      P (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j))
    (q : PositionedWord)
    (hq : q ∈ ReductionTM2.BulkScan.cappedRuntimePieces p.side (by have h := p.side_ge; omega) ha) : P q := by
  obtain ⟨j, rfl⟩ := (canonicalBulkPieces_mem_iff p ha q).mp hq
  exact h j

end ProteinFolding.Tetrahedral.NearField
