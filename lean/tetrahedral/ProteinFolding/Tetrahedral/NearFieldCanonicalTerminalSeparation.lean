import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonFamily
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingTrackSeparation
import ProteinFolding.Tetrahedral.NearFieldFrameColumnFamily
import ProteinFolding.Tetrahedral.NearFieldFrameTrackCoreSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalEndpointColours
import ProteinFolding.Tetrahedral.NearFieldCanonicalBasePieces
import ProteinFolding.Tetrahedral.NearFieldCanonicalUnits
import ProteinFolding.Tetrahedral.ReductionTM2BulkEndpointFacts

/-! The initial two-residue terminal unit avoids the actual local families.
Both its omitted corner H and its height-zero P cap are covered explicitly. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem terminalColumn_owner_inB (p : ConstructionParameters) :
    InBSublattice (terminalColumn p).owner.val := by
  rw [terminalColumn_owner]
  exact initialTerminal_inB p

theorem terminalColumn_owner_deleted (p : ConstructionParameters) :
    (terminalColumn p).owner ∈ bulkDeletedEdges p.side := by
  rw [terminalColumn_owner]
  exact edgeZigzag_mem_deleted (by have h := p.side_ge; omega) entryEdgeFrame _
    (by have h := p.side_ge; omega)

theorem terminalColumn_owner_reserved_coordinate (p : ConstructionParameters) :
    tetraCoordinate p.side (terminalColumn p).owner.val 3 ≤ -octRadius p.side := by
  rw [terminalColumn_owner, entryEdgeZigzag_coordinates (by have h := p.side_ge; omega)]
  dsimp [entryEdgeCoordinates, tetraCoordinate, octRadius]
  omega

theorem terminalWordPiece_disjoint_of_avoids (p : ConstructionParameters) (q : PositionedWord)
    (howner : ∀ j, q.fold.pos j ≠ (terminalColumn p).owner)
    (hcap : ∀ j, q.fold.pos j ≠ (terminalColumn p).seed) :
    WordsDisjoint (terminalWordPiece p) q := by
  apply (foldSites_disjoint_iff _ _).mpr
  intro i j
  change (if i.val = 0 then (terminalColumn p).owner else (terminalColumn p).seed) ≠ q.fold.pos j
  split_ifs
  · exact (howner j).symm
  · exact (hcap j).symm

private theorem terminal_capped_sites_property {a b : ℕ}
    (f : Fold tetrahedralLattice a) (g : Fold tetrahedralLattice b) (c d : Site)
    (hsites : foldSites f = ({c} ∪ foldSites g) ∪ {d}) (P : Site → Prop)
    (hc : P c) (hg : ∀ i, P (g.pos i)) (hd : P d) (i : Fin a) : P (f.pos i) := by
  have h := (mem_foldSites f _).mpr ⟨i, rfl⟩
  rw [hsites] at h
  simp only [Finset.mem_union, Finset.mem_singleton] at h
  rcases h with (h | h) | h
  · rw [h]
    exact hc
  · obtain ⟨j, hj⟩ := (mem_foldSites g _).mp h
    rw [← hj]
    exact hg j
  · rw [h]
    exact hd

private theorem outside_ne_terminalOwner (p : ConstructionParameters) (x : Site)
    (hx : x ∉ octahedron p.side) : x ≠ (terminalColumn p).owner := by
  intro heq
  exact hx (heq.symm ▸ (terminalColumn p).owner_mem)

private theorem inside_ne_column_seed {m : ℕ} (C : DanglingColumn m) (x : Site)
    (hx : x ∈ octahedron m) : x ≠ C.seed := by
  intro heq
  apply C.seed_outside
  change C.seed ∈ octahedron m
  rw [← heq]
  exact hx

private theorem inside_ne_terminalCap (p : ConstructionParameters) (x : Site)
    (hx : x ∈ octahedron p.side) : x ≠ (terminalColumn p).seed := by
  with_reducible exact inside_ne_column_seed (terminalColumn p) x hx

theorem canonicalSingletonPiece_ne_terminalOwner (p : ConstructionParameters) (r : Fin 3)
    (i : Fin (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).word.length) :
    (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).fold.pos i ≠
      (terminalColumn p).owner := by
  have hmem := (mem_foldSites
    (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).fold _).mpr ⟨i, rfl⟩
  rw [canonicalSingletonPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]
    exact outside_ne_terminalOwner p _
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r false).seed_outside
  · rw [h]
    intro heq
    have hA := canonicalSingletonOwner_inA p.side r
    rw [heq] at hA
    exact sublattices_disjoint _ hA (terminalColumn_owner_inB p)
  · rw [h]
    exact outside_ne_terminalOwner p _
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r true).seed_outside

theorem canonicalSingletonPiece_ne_terminalCap (p : ConstructionParameters) (r : Fin 3)
    (i : Fin (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).word.length) :
    (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).fold.pos i ≠
      (terminalColumn p).seed := by
  have hmem := (mem_foldSites
    (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r).fold _).mpr ⟨i, rfl⟩
  rw [canonicalSingletonPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]
    exact DanglingColumn.seed_ne_of_owner_colours _ _ (canonicalSingletonOwner_inA p.side r)
      (terminalColumn_owner_inB p)
  · rw [h]
    exact inside_ne_terminalCap p _ (canonicalSingletonOwner_mem p.side (by have h := p.side_ge; omega) r)
  · rw [h]
    exact DanglingColumn.seed_ne_of_owner_colours _ _ (canonicalSingletonOwner_inA p.side r)
      (terminalColumn_owner_inB p)

theorem terminalWordPiece_singletonPiece_disjoint (p : ConstructionParameters) (r : Fin 3) :
    WordsDisjoint (terminalWordPiece p)
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r) :=
  terminalWordPiece_disjoint_of_avoids p _ (canonicalSingletonPiece_ne_terminalOwner p r)
    (canonicalSingletonPiece_ne_terminalCap p r)

theorem canonicalRingWordPiece_ne_terminalOwner (p : ConstructionParameters) (r : Fin 3)
    (i : Fin (canonicalRingWordPiece p r).word.length) :
    (canonicalRingWordPiece p r).fold.pos i ≠ (terminalColumn p).owner :=
  cappedRingFold_ne_reserved_oct_site p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame r) (canonicalRingFrame_small_ne_reserved r)
    (canonicalRingColumn p r 0) (canonicalRingColumn p r 1)
    (canonicalRingColumn_first_owner p r) (canonicalRingColumn_last_owner p r)
    (terminalColumn p).owner (terminalColumn p).owner_mem (terminalColumn_owner_reserved_coordinate p) i

theorem canonicalRingWordPiece_ne_terminalCap (p : ConstructionParameters) (r : Fin 3)
    (i : Fin (canonicalRingWordPiece p r).word.length) :
    (canonicalRingWordPiece p r).fold.pos i ≠ (terminalColumn p).seed :=
  canonicalRingWordPiece_ne_reserved_edge_cap p r entryEdgeFrame rfl
    (terminalColumn p) _ (terminalColumn_owner p) i

theorem terminalWordPiece_ringPiece_disjoint (p : ConstructionParameters) (r : Fin 3) :
    WordsDisjoint (terminalWordPiece p) (canonicalRingWordPiece p r) :=
  terminalWordPiece_disjoint_of_avoids p _ (canonicalRingWordPiece_ne_terminalOwner p r)
    (canonicalRingWordPiece_ne_terminalCap p r)

private theorem bulkPiece_ne_terminalOwner (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length)
    (i : Fin (ReductionTM2.BulkScan.runtimePiece p.side (by have h := p.side_ge; omega) ha j).word.length) :
    (ReductionTM2.BulkScan.runtimePiece p.side (by have h := p.side_ge; omega) ha j).fold.pos i ≠
      (terminalColumn p).owner := by
  intro heq
  have hmem := ReductionTM2.BulkScan.runtimePiece_inside p.side (by have h := p.side_ge; omega) ha j _
    ((mem_foldSites _ _).mpr ⟨i, rfl⟩)
  rw [heq] at hmem
  exact (Finset.mem_sdiff.mp hmem).2 (terminalColumn_owner_deleted p)

theorem canonicalBulkPiece_ne_terminalOwner (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length)
    (i : Fin (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).word.length) :
    (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).fold.pos i ≠
      (terminalColumn p).owner := by
  apply terminal_capped_sites_property _ _ _ _
    (ReductionTM2.BulkScan.cappedRuntimeFoldWithColumns_sites p.side
      (by have h := p.side_ge; omega) ha j _ _ rfl rfl)
    (fun x => x ≠ (terminalColumn p).owner) _ (bulkPiece_ne_terminalOwner p ha j) _ i
  · exact outside_ne_terminalOwner p _
      (ReductionTM2.BulkScan.firstColumn p.side (by have h := p.side_ge; omega) ha j).seed_outside
  · exact outside_ne_terminalOwner p _
      (ReductionTM2.BulkScan.lastColumn p.side (by have h := p.side_ge; omega) ha j).seed_outside

private theorem bulkColumn_seed_ne_deletedColumn {m : ℕ} (C D : DanglingColumn m)
    (hC : C.owner ∈ bulkInterior m) (hD : D.owner ∈ bulkDeletedEdges m) : C.seed ≠ D.seed := by
  intro heq
  have ho := column_owner_eq_of_seed_eq C D heq
  exact (Finset.mem_sdiff.mp hC).2 (ho.symm ▸ hD)

private theorem cappedRuntimePiece_ne_deletedColumn_seed (m : ℕ) (hm : 27 ≤ m)
    (ha : (bulkFiniteGraph m).IsAcyclic) (j : Fin (ReductionTM2.BulkScan.lengths m).length)
    (E : DanglingColumn m) (hE : E.owner ∈ bulkDeletedEdges m)
    (i : Fin (ReductionTM2.BulkScan.cappedRuntimePiece m hm ha j).word.length) :
    (ReductionTM2.BulkScan.cappedRuntimePiece m hm ha j).fold.pos i ≠ E.seed := by
  have hfirst : (ReductionTM2.BulkScan.firstColumn m hm ha j).owner ∈ bulkInterior m := by
    rw [ReductionTM2.BulkScan.firstColumn_owner]
    exact ReductionTM2.BulkScan.runtimeFirst_inside m hm ha j
  have hlast : (ReductionTM2.BulkScan.lastColumn m hm ha j).owner ∈ bulkInterior m := by
    rw [ReductionTM2.BulkScan.lastColumn_owner]
    exact ReductionTM2.BulkScan.runtimeLast_inside m hm ha j
  apply terminal_capped_sites_property _ _ _ _
    (ReductionTM2.BulkScan.cappedRuntimeFoldWithColumns_sites m hm ha j
      (ReductionTM2.BulkScan.firstColumn m hm ha j) (ReductionTM2.BulkScan.lastColumn m hm ha j)
      (ReductionTM2.BulkScan.firstColumn_owner m hm ha j) (ReductionTM2.BulkScan.lastColumn_owner m hm ha j))
    (fun x => x ≠ E.seed) _ _ _ i
  · exact bulkColumn_seed_ne_deletedColumn (ReductionTM2.BulkScan.firstColumn m hm ha j) E hfirst hE
  · intro k
    apply inside_ne_column_seed E
    exact (Finset.mem_sdiff.mp (ReductionTM2.BulkScan.runtimePiece_inside m hm ha j _
      ((mem_foldSites _ _).mpr ⟨k, rfl⟩))).1
  · exact bulkColumn_seed_ne_deletedColumn (ReductionTM2.BulkScan.lastColumn m hm ha j) E hlast hE

theorem canonicalBulkPiece_ne_terminalCap (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length)
    (i : Fin (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).word.length) :
    (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).fold.pos i ≠
      (terminalColumn p).seed := by
  with_reducible
    exact cappedRuntimePiece_ne_deletedColumn_seed p.side (by have h := p.side_ge; omega)
      ha j (terminalColumn p) (terminalColumn_owner_deleted p) i

theorem terminalWordPiece_bulkPiece_disjoint (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) :
    WordsDisjoint (terminalWordPiece p)
      (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j) :=
  terminalWordPiece_disjoint_of_avoids p _ (canonicalBulkPiece_ne_terminalOwner p ha j)
    (canonicalBulkPiece_ne_terminalCap p ha j)

theorem frameHRun_entry_index_ne_terminal (p : ConstructionParameters) (j : FrameHRunIndex p)
    (hj : frameHRunOnExit j = false) (t : ℕ) (ht : t < (frameHRunData p j).count) :
    (frameHRunData p j).base + t ≠ 2 * p.side - 3 := by
  have hm := p.side_ge
  have hf := p.family_side_bound
  have htail := p.frameTail1_add
  rcases j with c | ⟨b, k⟩
  · fin_cases c <;> dsimp [frameHRunData] at ht ⊢ <;>
      dsimp [frameHRunOnExit] at hj <;>
      simp only [Bool.true_eq_false, Bool.false_eq_true] at hj <;> omega
  · have hk := k.isLt
    cases b <;> dsimp [frameHRunOnExit] at hj
    · dsimp [frameHRunData] at ht ⊢
      split_ifs at ht <;> omega
    · cases hj

theorem frameHRunFold_ne_terminalOwner (p : ConstructionParameters) (j : FrameHRunIndex p)
    (i : Fin (frameHRunWord p j).length) :
    (frameHRunFold p j).pos i ≠ (terminalColumn p).owner := by
  have hmem := (mem_foldSites (frameHRunFold p j) _).mpr ⟨i, rfl⟩
  rw [frameHRunFold_sites] at hmem
  obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hmem
  have ht' := Finset.mem_range.mp ht
  rw [← heq, terminalColumn_owner, frameHRun_frame]
  cases hj : frameHRunOnExit j
  · simp only [hj, Bool.false_eq_true, if_false]
    intro h
    exact frameHRun_entry_index_ne_terminal p j hj t ht'
      (octEdgeZigzag_injective (by have h := p.side_ge; omega) entryEdgeFrame h)
  · simp only [hj, ite_true]
    have hroom := frameHRun_exit_room p j hj
    exact (entryEdge_ne_exitEdge_before_corner (by have h := p.side_ge; omega)
      _ _ (by omega)).symm

theorem frameCoreFold_ne_terminalOwner (p : ConstructionParameters)
    (i : Fin (p.framePart1 ++ p.framePart2).length) :
    (frameCoreFold p).pos i ≠ (terminalColumn p).owner := by
  apply frameCoreFold_property p (fun x => x ≠ (terminalColumn p).owner) _ i
  intro j s
  rcases j with j | j
  · exact frameHRunFold_ne_terminalOwner p j s
  · dsimp only [frameCorePiece, frameLinkPiece] at s ⊢
    rw [frameLinkWordFold_pos]
    apply outside_ne_terminalOwner p
    exact positiveSkin_outside p.side 1 (by decide) (frameLinkFold_mem_skin_one p j _)

theorem frameFold_ne_terminalOwner (p : ConstructionParameters) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠ (terminalColumn p).owner := by
  apply terminal_capped_sites_property _ _ _ _ (frameFold_sites p)
    (fun x => x ≠ (terminalColumn p).owner) _ (frameCoreFold_ne_terminalOwner p) _ i
  · exact outside_ne_terminalOwner p _ (frameFirstColumn p).seed_outside
  · exact outside_ne_terminalOwner p _ (frameLastColumn p).seed_outside

theorem frameFold_ne_terminalCap (p : ConstructionParameters) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠ (terminalColumn p).seed := by
  apply terminal_capped_sites_property _ _ _ _ (frameFold_sites p)
    (fun x => x ≠ (terminalColumn p).seed) _ _ _ i
  · exact DanglingColumn.seed_ne_of_owner_colours _ _ (frameEndpointVertex_inA p.side true)
      (terminalColumn_owner_inB p)
  · intro k
    apply frameCoreFold_ne_column_of_links p (terminalColumn p) 0 _ k
    intro j s
    rw [frameLinkFold_pos_eq_framePoint]
    exact terminalColumn_ne_frameP p (frameLinkParameter j) (frameLinkKind j)
      (frameLinkParameter_odd p j) (frameLinkParameter_room p j) 0 (frameLinkInteriorIndex p j s)
      (frameLinkInteriorIndex_pos p j s) (frameLinkInteriorIndex_before_last p j s)
  · exact DanglingColumn.seed_ne_of_owner_colours _ _ (frameEndpointVertex_inA p.side false)
      (terminalColumn_owner_inB p)

theorem terminalWordPiece_frameWordPiece_disjoint (p : ConstructionParameters) :
    WordsDisjoint (terminalWordPiece p) (frameWordPiece p) :=
  terminalWordPiece_disjoint_of_avoids p _ (frameFold_ne_terminalOwner p) (frameFold_ne_terminalCap p)

theorem terminalOwner_not_mem_trackHsites (p : ConstructionParameters) (base q : ℕ) :
    (terminalColumn p).owner ∉ edgeDimerHsites p.side trackEdgeFrame base q := by
  intro hmem
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hmem
  have hy := congrArg (fun x : Site => x.val 1) ht
  change (octEdgeZigzag p.side trackEdgeFrame (base + t.val)).val 1 =
    (terminalColumn p).owner.val 1 at hy
  rw [terminalColumn_owner,
    trackEdgeZigzag_coordinates (by have h := p.side_ge; omega),
    entryEdgeZigzag_coordinates (by have h := p.side_ge; omega)] at hy
  have hmod := Nat.mod_lt (base + t.val) (by decide : 0 < 2)
  have hm := p.side_ge
  dsimp [trackEdgeCoordinates, entryEdgeCoordinates, octRadius] at hy
  omega

theorem cappedInterval_ne_terminalOwner_of_not_mem (p : ConstructionParameters)
    (F : OctEdgeFrame) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * p.side - 1) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (n - 1) 1))
    (hnot : (terminalColumn p).owner ∉ edgeDimerHsites p.side F base (n - 1))
    (i : Fin (capWord (dimerChain n)).length) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      F base n hn reverse hroom C D hC hD).pos i ≠ (terminalColumn p).owner :=
  transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold (by have h := p.side_ge; omega : 1 ≤ p.side)
      F base (n - 1) reverse (by omega) C D hC hD)
    (fun x => x ≠ (terminalColumn p).owner)
    (cappedEdgeDimerFold_ne_octSite_of_not_mem_Hsites (by have h := p.side_ge; omega : 1 ≤ p.side)
      F base (n - 1) reverse (by omega) C D hC hD
      (terminalColumn p).owner (terminalColumn p).owner_mem hnot) i

theorem cappedInterval_ne_terminalCap_of_not_mem (p : ConstructionParameters)
    (F : OctEdgeFrame) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * p.side - 1) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (n - 1) 1))
    (hnot : (terminalColumn p).owner ∉ edgeDimerHsites p.side F base (n - 1))
    (i : Fin (capWord (dimerChain n)).length) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      F base n hn reverse hroom C D hC hD).pos i ≠ (terminalColumn p).seed :=
  transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold (by have h := p.side_ge; omega : 1 ≤ p.side)
      F base (n - 1) reverse (by omega) C D hC hD)
    (fun x => x ≠ (terminalColumn p).seed)
    (cappedEdgeDimerFold_ne_cap_of_owner_not_mem (by have h := p.side_ge; omega : 1 ≤ p.side)
      F base (n - 1) reverse (by omega) C D hC hD (terminalColumn p) hnot) i

theorem terminalWordPiece_intervalPiece_disjoint (p : ConstructionParameters)
    (F : OctEdgeFrame) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * p.side - 1) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (n - 1) 1))
    (hnot : (terminalColumn p).owner ∉ edgeDimerHsites p.side F base (n - 1)) :
    WordsDisjoint (terminalWordPiece p)
      (cappedIntervalDimerPiece (m := p.side) (by have h := p.side_ge; omega)
        F base n hn reverse hroom C D hC hD) :=
  terminalWordPiece_disjoint_of_avoids p _
    (cappedInterval_ne_terminalOwner_of_not_mem p F base n hn reverse hroom C D hC hD hnot)
    (cappedInterval_ne_terminalCap_of_not_mem p F base n hn reverse hroom C D hC hD hnot)

theorem terminalWordPiece_itemPiece_disjoint (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    WordsDisjoint (terminalWordPiece p) (canonicalItemPiece p k before s hk hs hload) :=
  terminalWordPiece_intervalPiece_disjoint p trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s)
    (by have h := p.itemDimers_ge s hs; omega) false (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload)
    (terminalOwner_not_mem_trackHsites p _ _)

theorem terminalWordPiece_rightPiece_disjoint (p : ConstructionParameters) :
    WordsDisjoint (terminalWordPiece p) (canonicalRightPiece p) :=
  terminalWordPiece_intervalPiece_disjoint p trackEdgeFrame (rightFillerTrackBase p) p.rightFiller
    (by have h := p.rightFiller_ge; omega) false (rightFillerTrackBase_room p)
    (rightFirstColumn p) (rightFinalColumn p) rfl
    (by
      rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
      have he : rightFillerTrackBase p + 2 * p.rightFiller - 1 = 2 * p.side - 3 := by
        have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
        dsimp [rightFillerTrackBase]
        omega
      rw [he]
      exact rightFinalColumn_track_owner p)
    (terminalOwner_not_mem_trackHsites p _ _)

private def terminal_left_dimer_index (p : ConstructionParameters)
    (i : Fin (dimerChain p.leftFiller).length) : Fin (dimerChain (p.leftFiller - 1 + 1)).length :=
  ⟨i.val, by
    have hlen := dimerChain_succ_length (p.leftFiller - 1)
    have hword := leftFiller_word_length p
    have hi := i.isLt
    omega⟩

theorem leftFillerFold_ne_terminalOwner (p : ConstructionParameters)
    (i : Fin (dimerChain p.leftFiller).length) : (leftFillerFold p).pos i ≠ (terminalColumn p).owner := by
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hi
  · rw [terminalColumn_owner]
    intro h
    have he := octEdgeZigzag_injective (by have h := p.side_ge; omega) entryEdgeFrame h
    have hm := p.side_ge
    omega
  · have h := edgeDimerFold_ne_octSite_of_not_mem_Hsites (by have h := p.side_ge; omega : 1 ≤ p.side)
      trackEdgeFrame 0 (p.leftFiller - 1) false (leftFiller_room p)
      (terminalColumn p).owner (terminalColumn p).owner_mem (terminalOwner_not_mem_trackHsites p _ _)
      (terminal_left_dimer_index p i)
    rw [edgeDimerFold_pos] at h
    exact h

theorem leftFillerFold_ne_terminalCap (p : ConstructionParameters)
    (i : Fin (dimerChain p.leftFiller).length) : (leftFillerFold p).pos i ≠ (terminalColumn p).seed := by
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hi
  · exact inside_ne_terminalCap p _ (leftFillerStart_mem_oct p)
  · have h := edgeDimerFold_ne_cap_of_owner_not_mem (by have h := p.side_ge; omega : 1 ≤ p.side)
      trackEdgeFrame 0 (p.leftFiller - 1) false (leftFiller_room p) (terminalColumn p)
      (terminalOwner_not_mem_trackHsites p _ _) (terminal_left_dimer_index p i)
    rw [edgeDimerFold_pos] at h
    exact h

theorem canonicalLeftPiece_ne_terminalOwner (p : ConstructionParameters)
    (i : Fin (canonicalLeftPiece p).word.length) :
    (canonicalLeftPiece p).fold.pos i ≠ (terminalColumn p).owner := by
  apply terminal_capped_sites_property _ _ _ _ (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p))
    (fun x => x ≠ (terminalColumn p).owner) _ (leftFillerFold_ne_terminalOwner p) _ i
  · exact outside_ne_terminalOwner p _ (entryLocalColumn p none).seed_outside
  · exact outside_ne_terminalOwner p _ (leftLastColumn p).seed_outside

theorem canonicalLeftPiece_ne_terminalCap (p : ConstructionParameters)
    (i : Fin (canonicalLeftPiece p).word.length) :
    (canonicalLeftPiece p).fold.pos i ≠ (terminalColumn p).seed := by
  apply terminal_capped_sites_property _ _ _ _ (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p))
    (fun x => x ≠ (terminalColumn p).seed) _ (leftFillerFold_ne_terminalCap p) _ i
  · exact DanglingColumn.seed_ne_of_owner_colours _ _ (leftFillerFirstH_inA p) (terminalColumn_owner_inB p)
  · exact DanglingColumn.seed_ne_of_owner_colours _ _
      (by rw [leftLastColumn_owner]; exact leftFillerLastH_inA p) (terminalColumn_owner_inB p)

theorem terminalWordPiece_leftPiece_disjoint (p : ConstructionParameters) :
    WordsDisjoint (terminalWordPiece p) (canonicalLeftPiece p) :=
  terminalWordPiece_disjoint_of_avoids p _ (canonicalLeftPiece_ne_terminalOwner p) (canonicalLeftPiece_ne_terminalCap p)

theorem terminalOwner_ne_trackEdge (p : ConstructionParameters) (r : ℕ) :
    (terminalColumn p).owner ≠ octEdgeZigzag p.side trackEdgeFrame r := by
  intro heq
  apply terminalOwner_not_mem_trackHsites p r 0
  rw [heq]
  exact dimerHIndex_mem_Hsites p.side trackEdgeFrame r 0 false 0 le_rfl 0

theorem terminalOwner_ne_entryEdge_of_lt (p : ConstructionParameters) (r : ℕ)
    (hr : r < 2 * p.side - 3) : (terminalColumn p).owner ≠ octEdgeZigzag p.side entryEdgeFrame r := by
  rw [terminalColumn_owner]
  intro heq
  have h := octEdgeZigzag_injective (by have h := p.side_ge; omega) entryEdgeFrame heq
  omega

theorem terminalOwner_ne_exitEdge_before_corner (p : ConstructionParameters) (r : ℕ)
    (hr : r + 2 ≤ 2 * p.side - 2) :
    (terminalColumn p).owner ≠ octEdgeZigzag p.side exitEdgeFrame r := by
  rw [terminalColumn_owner]
  exact entryEdge_ne_exitEdge_before_corner (by have h := p.side_ge; omega) _ _ hr

theorem terminalCap_ne_tetherFold (p : ConstructionParameters) (t : TetherIndex p)
    (i : Fin (tetherCount p t)) : (terminalColumn p).seed ≠ (tetherFold p t).pos i := by
  apply danglingCap_ne_tetherFold p t (terminalColumn p) _ _ i
  · rcases t with ⟨b, k⟩
    cases b
    · change (terminalColumn p).owner ≠
        (faceDanglingColumn p.side (entryAnchorA p k.val) (3 * (k.val + 1)) 0
          (entryAnchor_equation p k.val (Nat.le_of_lt_succ k.isLt))).owner
      rw [entrySource_owner p k.val (Nat.le_of_lt_succ k.isLt)]
      apply terminalOwner_ne_entryEdge_of_lt
      have h := p.entry_column_triangle_room k.val (Nat.le_of_lt_succ k.isLt)
      omega
    · change (terminalColumn p).owner ≠ (exitSourceColumn p k.val (Nat.le_of_lt_succ k.isLt)).owner
      rw [exitSource_owner p k.val (Nat.le_of_lt_succ k.isLt)]
      exact terminalOwner_ne_trackEdge p _
  · rcases t with ⟨b, k⟩
    cases b
    · change (terminalColumn p).owner ≠ (entryTargetColumn p k.val (Nat.le_of_lt_succ k.isLt)).owner
      rw [entryTarget_owner p k.val (Nat.le_of_lt_succ k.isLt)]
      exact terminalOwner_ne_trackEdge p _
    · change (terminalColumn p).owner ≠ (exitTargetColumn p k.val).owner
      rw [exitTarget_owner]
      apply terminalOwner_ne_exitEdge_before_corner
      have h := p.exit_column_triangle_room k.val
      omega

theorem terminalOwner_not_mem_entryHsites (p : ConstructionParameters) (base q : ℕ)
    (hhi : base + 2 * (q + 1) ≤ 2 * p.side - 3) :
    (terminalColumn p).owner ∉ edgeDimerHsites p.side entryEdgeFrame base q := by
  intro hmem
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hmem
  have hb := t.isLt
  exact terminalOwner_ne_entryEdge_of_lt p _ (by omega) ht.symm

theorem terminalOwner_not_mem_exitHsites (p : ConstructionParameters) (base q : ℕ)
    (hhi : base + 2 * (q + 1) ≤ 2 * p.side - 3) :
    (terminalColumn p).owner ∉ edgeDimerHsites p.side exitEdgeFrame base q := by
  intro hmem
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hmem
  have hb := t.isLt
  exact terminalOwner_ne_exitEdge_before_corner p _ (by omega) ht.symm

private theorem terminalOwner_not_mem_separatorEntry (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (terminalColumn p).owner ∉ edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0 := by
  apply terminalOwner_not_mem_entryHsites
  have h := p.entry_column_triangle_room k hk
  omega

private theorem terminalOwner_not_mem_separatorExit (p : ConstructionParameters) (k : ℕ) :
    (terminalColumn p).owner ∉ edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 := by
  apply terminalOwner_not_mem_exitHsites
  have h := p.exit_column_triangle_room k
  omega

theorem separatorFold_ne_terminalOwner (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.separatorWord k).length) : (separatorFold p k hk).pos i ≠ (terminalColumn p).owner := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply separatorFold_property p k hk (fun x => x ≠ (terminalColumn p).owner) _ _ _ _ _ i
  · exact edgeDimerFold_ne_octSite_of_not_mem_Hsites hm entryEdgeFrame (6 * (k + 1)) 0 false
      (separatorEntry_room p k hk) _ (terminalColumn p).owner_mem (terminalOwner_not_mem_separatorEntry p k hk)
  · intro j
    rw [entryTetherWordFold_pos]
    exact outside_ne_terminalOwner p _ (entryTetherFold_outside p k hk ⟨j.val, by simpa using j.isLt⟩)
  · exact edgeDimerFold_ne_octSite_of_not_mem_Hsites hm trackEdgeFrame (2 * p.separatorIndex k) 1 true
      (separatorCenter_room p k hk) _ (terminalColumn p).owner_mem (terminalOwner_not_mem_trackHsites p _ _)
  · intro j
    rw [exitTetherWordFold_pos]
    exact outside_ne_terminalOwner p _ (exitTetherFold_outside p k hk ⟨j.val, by simpa using j.isLt⟩)
  · exact edgeDimerFold_ne_octSite_of_not_mem_Hsites hm exitEdgeFrame (10 * p.exitSlot k + 6) 2 true
      (separatorExit_room p k) _ (terminalColumn p).owner_mem (terminalOwner_not_mem_separatorExit p k)

theorem separatorFold_ne_terminalCap (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.separatorWord k).length) : (separatorFold p k hk).pos i ≠ (terminalColumn p).seed := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply separatorFold_property p k hk (fun x => x ≠ (terminalColumn p).seed) _ _ _ _ _ i
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm entryEdgeFrame (6 * (k + 1)) 0 false
      (separatorEntry_room p k hk) (terminalColumn p) (terminalOwner_not_mem_separatorEntry p k hk)
  · intro j
    rw [entryTetherWordFold_pos]
    simpa only [tetherFold] using
      (terminalCap_ne_tetherFold p (false, ⟨k, by omega⟩) ⟨j.val, by simpa using j.isLt⟩).symm
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm trackEdgeFrame (2 * p.separatorIndex k) 1 true
      (separatorCenter_room p k hk) (terminalColumn p) (terminalOwner_not_mem_trackHsites p _ _)
  · intro j
    rw [exitTetherWordFold_pos]
    simpa only [tetherFold] using
      (terminalCap_ne_tetherFold p (true, ⟨k, by omega⟩) ⟨j.val, by simpa using j.isLt⟩).symm
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm exitEdgeFrame (10 * p.exitSlot k + 6) 2 true
      (separatorExit_room p k) (terminalColumn p) (terminalOwner_not_mem_separatorExit p k)

theorem canonicalSeparatorPiece_ne_terminalOwner (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (i : Fin (canonicalSeparatorPiece p k).word.length) :
    (canonicalSeparatorPiece p k).fold.pos i ≠ (terminalColumn p).owner := by
  apply terminal_capped_sites_property _ _ _ _
    (cappedSeparatorFold_sites p k.val (by have h := k.isLt; omega) _ _ rfl
      (exitCapColumn_owner p k.val (by have h := k.isLt; omega)))
    (fun x => x ≠ (terminalColumn p).owner) _
    (separatorFold_ne_terminalOwner p k.val (by have h := k.isLt; omega)) _ i
  · exact outside_ne_terminalOwner p _ (entryLocalColumn p (some k)).seed_outside
  · exact outside_ne_terminalOwner p _ (exitCapColumn p k.val (by have h := k.isLt; omega)).seed_outside

theorem canonicalSeparatorPiece_ne_terminalCap (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (i : Fin (canonicalSeparatorPiece p k).word.length) :
    (canonicalSeparatorPiece p k).fold.pos i ≠ (terminalColumn p).seed := by
  apply terminal_capped_sites_property _ _ _ _
    (cappedSeparatorFold_sites p k.val (by have h := k.isLt; omega) _ _ rfl
      (exitCapColumn_owner p k.val (by have h := k.isLt; omega)))
    (fun x => x ≠ (terminalColumn p).seed) _
    (separatorFold_ne_terminalCap p k.val (by have h := k.isLt; omega)) _ i
  · exact DanglingColumn.seed_ne_of_owner_colours _ _ (separatorFirstH_inA p k.val) (terminalColumn_owner_inB p)
  · exact DanglingColumn.seed_ne_of_owner_colours _ _
      (by rw [exitCapColumn_owner]; exact separatorLastH_inA p k.val) (terminalColumn_owner_inB p)

theorem terminalWordPiece_separatorPiece_disjoint (p : ConstructionParameters) (k : Fin (p.bins + 1)) :
    WordsDisjoint (terminalWordPiece p) (canonicalSeparatorPiece p k) :=
  terminalWordPiece_disjoint_of_avoids p _ (canonicalSeparatorPiece_ne_terminalOwner p k)
    (canonicalSeparatorPiece_ne_terminalCap p k)

theorem canonicalLocal_terminal_disjoint (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    CanonicalLocalProperty p ha (WordsDisjoint (terminalWordPiece p)) := {
  singleton := terminalWordPiece_singletonPiece_disjoint p
  frame := terminalWordPiece_frameWordPiece_disjoint p
  separator := terminalWordPiece_separatorPiece_disjoint p
  left := terminalWordPiece_leftPiece_disjoint p
  item := terminalWordPiece_itemPiece_disjoint p
  right := terminalWordPiece_rightPiece_disjoint p
  ring := terminalWordPiece_ringPiece_disjoint p
  bulk := terminalWordPiece_bulkPiece_disjoint p ha }

theorem terminalWordPiece_taggedBody_disjoint (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (u : CappedUnit p.side) (hu : u ∈ canonicalTaggedBodies p items d ha) :
    WordsDisjoint (terminalWordPiece p) u.piece :=
  canonicalTaggedBodies_property p items d ha _ (canonicalLocal_terminal_disjoint p ha) u hu

end ProteinFolding.Tetrahedral.NearField
