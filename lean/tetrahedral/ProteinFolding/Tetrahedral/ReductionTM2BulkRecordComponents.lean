import ProteinFolding.Tetrahedral.ReductionTM2BulkAnnotated

/-! Proof-only identification of each emitted record occurrence with one
physical graph component. Equal record values remain separate occurrences.
None of these choices is used by the reduction machine. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

set_option maxHeartbeats 2000000

theorem entry_component_exists (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) :
    ∃ c : (bulkFiniteGraph m).ConnectedComponent,
      ((taggedRecords m).get j).1 = BulkOrientedPath.points m hm ha c 0 ∧
      ((taggedRecords m).get j).2 = (bulkComponentLength m c,
        (BulkPredicate.colour (m, (BulkOrientedPath.points m hm ha c 0, 0)),
          BulkPredicate.colour (m, (BulkOrientedPath.points m hm ha c (bulkComponentLength m c - 1), 0)))) := by
  apply tagged_component m hm ha
  change (taggedRecords m).get j ∈ taggedRecords m
  exact List.get_mem _ _

noncomputable def recordComponent (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) : (bulkFiniteGraph m).ConnectedComponent :=
  Classical.choose (entry_component_exists m hm ha j)

theorem recordComponent_start (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) :
    ((taggedRecords m).get j).1 = BulkOrientedPath.points m hm ha (recordComponent m hm ha j) 0 :=
  (Classical.choose_spec (entry_component_exists m hm ha j)).1

theorem recordComponent_record (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) :
    ((taggedRecords m).get j).2 = (bulkComponentLength m (recordComponent m hm ha j),
      (BulkPredicate.colour (m, (BulkOrientedPath.points m hm ha (recordComponent m hm ha j) 0, 0)),
        BulkPredicate.colour (m, (BulkOrientedPath.points m hm ha (recordComponent m hm ha j)
          (bulkComponentLength m (recordComponent m hm ha j) - 1), 0)))) :=
  (Classical.choose_spec (entry_component_exists m hm ha j)).2

theorem recordComponent_length (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) :
    ((taggedRecords m).get j).2.1 = bulkComponentLength m (recordComponent m hm ha j) :=
  congrArg Prod.fst (recordComponent_record m hm ha j)

theorem recordComponent_injective (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    Function.Injective (recordComponent m hm ha) := by
  intro i j he
  apply tagged_start_injective m i j
  rw [recordComponent_start m hm ha i, recordComponent_start m hm ha j, he]

theorem recordComponent_surjective (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    Function.Surjective (recordComponent m hm ha) := by
  intro c
  let k := BulkOrientedPath.points m hm ha c 0
  let r : Record := (bulkComponentLength m c,
    (BulkPredicate.colour (m, (k, 0)),
      BulkPredicate.colour (m, (BulkOrientedPath.points m hm ha c (bulkComponentLength m c - 1), 0))))
  have hemit : emit (m, k) = [r] := BulkOrientedPath.emitted m hm ha c
  have htag : (k, r) ∈ taggedRecords m := by
    apply List.mem_flatMap.mpr
    refine ⟨k, List.mem_range.mpr (BulkOrientedPath.first_bound m hm ha c), ?_⟩
    apply List.mem_map.mpr
    refine ⟨r, ?_, rfl⟩
    rw [hemit]
    simp
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp htag
  refine ⟨j, ?_⟩
  apply BulkOrientedPath.first_injective m hm ha
  have hs := recordComponent_start m hm ha j
  exact hs.symm.trans (congrArg Prod.fst hj)

noncomputable def recordComponentEquiv (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    Fin (taggedRecords m).length ≃ (bulkFiniteGraph m).ConnectedComponent :=
  Equiv.ofBijective (recordComponent m hm ha)
    ⟨recordComponent_injective m hm ha, recordComponent_surjective m hm ha⟩

theorem tagged_length (m : ℕ) : (taggedRecords m).length = (records m).length := by
  have h := congrArg List.length (map_snd_taggedRecords m)
  simpa only [List.length_map] using h

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan
