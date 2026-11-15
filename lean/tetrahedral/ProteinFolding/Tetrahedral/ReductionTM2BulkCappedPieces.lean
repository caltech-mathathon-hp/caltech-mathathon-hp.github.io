import ProteinFolding.Tetrahedral.ReductionTM2BulkRuntimePieces
import ProteinFolding.Tetrahedral.NearFieldCapFoldSites
import ProteinFolding.Tetrahedral.NearFieldPPPPairwiseFacts
import ProteinFolding.Tetrahedral.ColumnsSkins

/-! Actual capped bulk words. Endpoint columns are chosen from the proved
surface endpoints; the closed reduction machine receives none of this data. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

open NearField

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable def surfaceColumn (m : ℕ) (p : Site) (hp : OctSurfaceSite m p) : DanglingColumn m where
  owner := p
  dir := (octDanglingDirections m p).min' (Finset.card_pos.mp hp.2)
  owner_mem := hp.1
  seed_outside := (Finset.mem_filter.mp (Finset.min'_mem _ (Finset.card_pos.mp hp.2))).2

noncomputable def firstColumn (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : DanglingColumn m :=
  surfaceColumn m (runtimeFirst m hm ha j) (runtimeFirst_surface m hm ha j)

noncomputable def lastColumn (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : DanglingColumn m :=
  surfaceColumn m (runtimeLast m hm ha j) (runtimeLast_surface m hm ha j)

theorem firstColumn_owner (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : (firstColumn m hm ha j).owner = runtimeFirst m hm ha j := rfl

theorem lastColumn_owner (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : (lastColumn m hm ha j).owner = runtimeLast m hm ha j := rfl

theorem runtimeFirst_ne_last (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : runtimeFirst m hm ha j ≠ runtimeLast m hm ha j := by
  intro he
  have hidx := (runtimeFold m hm ha j).injective_pos he
  have hv := congrArg (fun i : Fin ((lengths m).get j) => i.val) hidx
  change 0 = (lengths m).get j - 1 at hv
  have hn := runtimeFold_length_ge_three m hm ha j
  omega

theorem column_seed_not_mem_body (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (C : DanglingColumn m) :
    C.seed ∉ foldSites (runtimePiece m hm ha j).fold := by
  intro h
  exact C.seed_outside (Finset.mem_sdiff.mp (runtimePiece_inside m hm ha j C.seed h)).1

theorem body_caps_ne (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (C D : DanglingColumn m)
    (hC : C.owner = runtimeFirst m hm ha j) (hD : D.owner = runtimeLast m hm ha j) : C.seed ≠ D.seed := by
  apply dangling_caps_ne_of_owner_ne m C.owner D.owner C.dir D.dir C.owner_mem D.owner_mem C.seed_outside
  rw [hC, hD]
  exact runtimeFirst_ne_last m hm ha j

noncomputable def cappedRuntimeFoldWithColumns (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (C D : DanglingColumn m)
    (hC : C.owner = runtimeFirst m hm ha j) (hD : D.owner = runtimeLast m hm ha j) :
    Fold tetrahedralLattice (capWord (List.replicate ((lengths m).get j) Residue.H)).length :=
  cappedWordFold (runtimePiece m hm ha j).fold C.seed D.seed (runtimePiece m hm ha j).length_pos
    (fun i he => column_seed_not_mem_body m hm ha j C ((mem_foldSites _ _).2 ⟨i, he.symm⟩))
    (fun i he => column_seed_not_mem_body m hm ha j D ((mem_foldSites _ _).2 ⟨i, he⟩))
    (body_caps_ne m hm ha j C D hC hD)
    (by
      intro i hi
      rw [(runtimePiece m hm ha j).first_eq i hi]
      change tetrahedralLattice.Adj C.seed (runtimeFirst m hm ha j)
      rw [← hC]
      exact (step_adj _ _).symm)
    (by
      intro i hi
      rw [(runtimePiece m hm ha j).last_eq i hi]
      change tetrahedralLattice.Adj (runtimeLast m hm ha j) D.seed
      rw [← hD]
      exact step_adj _ _)

theorem cappedRuntimeFoldWithColumns_sites (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (C D : DanglingColumn m)
    (hC : C.owner = runtimeFirst m hm ha j) (hD : D.owner = runtimeLast m hm ha j) :
    foldSites (cappedRuntimeFoldWithColumns m hm ha j C D hC hD) =
      ({C.seed} ∪ foldSites (runtimePiece m hm ha j).fold) ∪ {D.seed} :=
  cappedWordFold_sites _ _ _ _ _ _ _ _ _

theorem cappedRuntimeFoldWithColumns_hSupport (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (C D : DanglingColumn m)
    (hC : C.owner = runtimeFirst m hm ha j) (hD : D.owner = runtimeLast m hm ha j) :
    hSupport (capWord (List.replicate ((lengths m).get j) Residue.H))
      (cappedRuntimeFoldWithColumns m hm ha j C D hC hD) = foldSites (runtimePiece m hm ha j).fold := by
  rw [cappedRuntimeFoldWithColumns, cappedWordFold_hSupport]
  exact runtimePiece_hSupport m hm ha j

noncomputable def cappedRuntimePieceWithColumns (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (C D : DanglingColumn m)
    (hC : C.owner = runtimeFirst m hm ha j) (hD : D.owner = runtimeLast m hm ha j) : PositionedWord where
  word := capWord (List.replicate ((lengths m).get j) Residue.H)
  fold := cappedRuntimeFoldWithColumns m hm ha j C D hC hD
  length_pos := by simp [capWord]
  first := C.seed
  last := D.seed
  first_eq := cappedWordFold_first _ _ _ _ _ _ _ _ _
  last_eq := cappedWordFold_last _ _ _ _ _ _ _ _ _

theorem cappedRuntimePieceWithColumns_hSupport_inside (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (C D : DanglingColumn m)
    (hC : C.owner = runtimeFirst m hm ha j) (hD : D.owner = runtimeLast m hm ha j) :
    hSupport (cappedRuntimePieceWithColumns m hm ha j C D hC hD).word
      (cappedRuntimePieceWithColumns m hm ha j C D hC hD).fold ⊆ bulkInterior m := by
  change hSupport (capWord (List.replicate ((lengths m).get j) Residue.H))
    (cappedRuntimeFoldWithColumns m hm ha j C D hC hD) ⊆ bulkInterior m
  rw [cappedRuntimeFoldWithColumns_hSupport]
  exact fun p hp => runtimePiece_inside m hm ha j p hp

theorem cappedRuntimePieceWithColumns_mem_solid_one (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (C D : DanglingColumn m)
    (hC : C.owner = runtimeFirst m hm ha j) (hD : D.owner = runtimeLast m hm ha j)
    (i : Fin (cappedRuntimePieceWithColumns m hm ha j C D hC hD).word.length) :
    (cappedRuntimePieceWithColumns m hm ha j C D hC hD).fold.pos i ∈ skinSolid m 1 := by
  change (cappedRuntimeFoldWithColumns m hm ha j C D hC hD).pos i ∈ skinSolid m 1
  have hmem := (mem_foldSites (cappedRuntimePieceWithColumns m hm ha j C D hC hD).fold _).2 ⟨i, rfl⟩
  change (cappedRuntimeFoldWithColumns m hm ha j C D hC hD).pos i ∈
    foldSites (cappedRuntimeFoldWithColumns m hm ha j C D hC hD) at hmem
  rw [cappedRuntimeFoldWithColumns_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]; exact C.point_zero_mem_solid_one
  · have hp := (Finset.mem_sdiff.mp (runtimePiece_inside m hm ha j _ h)).1
    exact skinSolid_mono m (by omega : 0 ≤ 1) (by simpa only [skinSolid_zero] using hp)
  · rw [h]; exact D.point_zero_mem_solid_one

theorem cappedRuntimePieceWithColumns_colours (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (C D : DanglingColumn m)
    (hC : C.owner = runtimeFirst m hm ha j) (hD : D.owner = runtimeLast m hm ha j) :
    (FarField.colour (cappedRuntimePieceWithColumns m hm ha j C D hC hD).first,
      FarField.colour (cappedRuntimePieceWithColumns m hm ha j C D hC hD).last) =
      (!(((colours m).get (colourIndex m j)).1), !(((colours m).get (colourIndex m j)).2)) := by
  change (FarField.colour (step C.owner C.dir), FarField.colour (step D.owner D.dir)) = _
  rw [FarField.adj_colour (step_adj C.owner C.dir), FarField.adj_colour (step_adj D.owner D.dir), hC, hD]
  exact congrArg (fun c : Bool × Bool => (!c.1, !c.2)) (runtimeFold_colours m hm ha j)

noncomputable def cappedRuntimePiece (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : PositionedWord :=
  cappedRuntimePieceWithColumns m hm ha j (firstColumn m hm ha j) (lastColumn m hm ha j) rfl rfl

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan
