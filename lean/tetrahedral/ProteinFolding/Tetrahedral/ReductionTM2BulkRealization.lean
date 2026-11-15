import ProteinFolding.Tetrahedral.ReductionTM2BulkRecordComponents
import ProteinFolding.Tetrahedral.ReductionTM2BulkColour

/-! The physical bulk-fold family in the exact emitted occurrence order.
This is existence data for the completeness proof, independent of the closed
source-only word-generating machine. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

set_option maxHeartbeats 2000000

noncomputable def physicalFold (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) : Fold tetrahedralLattice ((taggedRecords m).get j).2.1 :=
  (bulkLiftFold m _ (BulkOrientedPath.fold m hm ha (recordComponent m hm ha j))).onLength
    (recordComponent_length m hm ha j)

theorem physicalFold_inside (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) (i : Fin ((taggedRecords m).get j).2.1) :
    (physicalFold m hm ha j).pos i ∈ bulkInterior m :=
  ((BulkOrientedPath.fold m hm ha (recordComponent m hm ha j)).pos
    (Fin.cast (recordComponent_length m hm ha j) i)).property

theorem physicalFold_component (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) (i : Fin ((taggedRecords m).get j).2.1) :
    ∃ hp : (physicalFold m hm ha j).pos i ∈ bulkInterior m,
      (bulkFiniteGraph m).connectedComponentMk ⟨(physicalFold m hm ha j).pos i, hp⟩ = recordComponent m hm ha j := by
  refine ⟨physicalFold_inside m hm ha j i, ?_⟩
  let c := recordComponent m hm ha j
  let k := Fin.cast (recordComponent_length m hm ha j) i
  exact (BulkOrientedPath.sites m hm ha c ((BulkOrientedPath.fold m hm ha c).pos k)).1 ⟨k, rfl⟩

theorem physicalFold_disjoint (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j k : Fin (taggedRecords m).length) (hne : j ≠ k) :
    Disjoint (Set.range (physicalFold m hm ha j).pos) (Set.range (physicalFold m hm ha k).pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨i, hi⟩ ⟨l, hl⟩
  obtain ⟨hpi, hci⟩ := physicalFold_component m hm ha j i
  obtain ⟨hpl, hcl⟩ := physicalFold_component m hm ha k l
  have hv : (⟨(physicalFold m hm ha j).pos i, hpi⟩ : BulkVertex m) =
      ⟨(physicalFold m hm ha k).pos l, hpl⟩ := Subtype.ext (hi.trans hl.symm)
  have hc : recordComponent m hm ha j = recordComponent m hm ha k :=
    hci.symm.trans ((congrArg (bulkFiniteGraph m).connectedComponentMk hv).trans hcl)
  exact hne (recordComponent_injective m hm ha hc)

theorem physicalFold_covers (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (p : Site) (hp : p ∈ bulkInterior m) :
    ∃ j : Fin (taggedRecords m).length, ∃ i, (physicalFold m hm ha j).pos i = p := by
  let u : BulkVertex m := ⟨p, hp⟩
  let c := (bulkFiniteGraph m).connectedComponentMk u
  obtain ⟨j, hj⟩ := recordComponent_surjective m hm ha c
  obtain ⟨k, hk⟩ := (BulkOrientedPath.sites m hm ha (recordComponent m hm ha j) u).2 (by rw [hj])
  let i : Fin ((taggedRecords m).get j).2.1 :=
    ⟨k.val, by rw [recordComponent_length m hm ha j]; exact k.isLt⟩
  have hcast : Fin.cast (recordComponent_length m hm ha j) i = k := Fin.ext rfl
  refine ⟨j, i, ?_⟩
  change ((BulkOrientedPath.fold m hm ha (recordComponent m hm ha j)).pos
    (Fin.cast (recordComponent_length m hm ha j) i)).val = p
  rw [hcast, hk]

theorem physicalFold_length_ge_three (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) : 3 ≤ ((taggedRecords m).get j).2.1 := by
  rw [recordComponent_length m hm ha j]
  exact BulkComponentPath.length_ge_three m hm ha _

noncomputable def physicalFirst (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) : Site :=
  (physicalFold m hm ha j).pos ⟨0, by have h := physicalFold_length_ge_three m hm ha j; omega⟩

noncomputable def physicalLast (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) : Site :=
  (physicalFold m hm ha j).pos ⟨((taggedRecords m).get j).2.1 - 1,
    by have h := physicalFold_length_ge_three m hm ha j; omega⟩

theorem physicalFirst_eq (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) :
    physicalFirst m hm ha j = ((BulkOrientedPath.fold m hm ha (recordComponent m hm ha j)).pos
      (PathOrientation.first (by have h := BulkComponentPath.length_ge_three m hm ha (recordComponent m hm ha j); omega))).val := rfl

theorem physicalLast_eq (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) :
    physicalLast m hm ha j = ((BulkOrientedPath.fold m hm ha (recordComponent m hm ha j)).pos
      (PathOrientation.last (by have h := BulkComponentPath.length_ge_three m hm ha (recordComponent m hm ha j); omega))).val := by
  have he := recordComponent_length m hm ha j
  have hcast : Fin.cast he (⟨((taggedRecords m).get j).2.1 - 1,
      by have h := physicalFold_length_ge_three m hm ha j; omega⟩ : Fin ((taggedRecords m).get j).2.1) =
      PathOrientation.last (by have h := BulkComponentPath.length_ge_three m hm ha (recordComponent m hm ha j); omega) := by
    apply Fin.ext
    change ((taggedRecords m).get j).2.1 - 1 = bulkComponentLength m (recordComponent m hm ha j) - 1
    rw [he]
  change ((BulkOrientedPath.fold m hm ha (recordComponent m hm ha j)).pos
    (Fin.cast he _)).val = _
  rw [hcast]

theorem physicalFold_colours (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) :
    (FarField.colour (physicalFirst m hm ha j), FarField.colour (physicalLast m hm ha j)) =
      ((taggedRecords m).get j).2.2 := by
  have hrec := congrArg Prod.snd (recordComponent_record m hm ha j)
  rw [hrec]
  apply Prod.ext
  · rw [physicalFirst_eq, BulkOrientedPath.points_first]
    exact (BulkIndexModel.colour_index m _).symm
  · rw [physicalLast_eq, BulkOrientedPath.points_last]
    exact (BulkIndexModel.colour_index m _).symm

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan
