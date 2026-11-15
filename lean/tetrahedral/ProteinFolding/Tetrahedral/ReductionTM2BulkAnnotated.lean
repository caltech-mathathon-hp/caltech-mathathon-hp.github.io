import ProteinFolding.Tetrahedral.ReductionTM2BulkScanComponents

/-! Occurrence-preserving proof metadata for the computed record list.
The source index is retained only here to identify components even when
several emitted length/colour records have the same value. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

noncomputable def taggedEmit (m k : ℕ) : List (ℕ × Record) := (emit (m, k)).map (fun r => (k, r))
noncomputable def taggedRecords (m : ℕ) : List (ℕ × Record) :=
  (List.range (Grid.count m)).flatMap (taggedEmit m)

theorem map_snd_tagged_list (m : ℕ) (xs : List ℕ) :
    (xs.flatMap (taggedEmit m)).map Prod.snd = xs.flatMap (fun k => emit (m, k)) := by
  induction xs with
  | nil => rfl
  | cons k xs ih =>
    rw [List.flatMap_cons, List.map_append, ih, List.flatMap_cons]
    congr 1
    simp only [taggedEmit, List.map_map, Function.comp_def, List.map_id']

theorem map_snd_taggedRecords (m : ℕ) : (taggedRecords m).map Prod.snd = records m :=
  map_snd_tagged_list m _

theorem map_fst_tagged_list (m : ℕ) (xs : List ℕ) :
    (xs.flatMap (taggedEmit m)).map Prod.fst = xs.filter (fun k => canonical (m, k)) := by
  induction xs with
  | nil => rfl
  | cons k xs ih =>
    rw [List.flatMap_cons, List.map_append, ih]
    cases hc : canonical (m, k) <;> simp [taggedEmit, emit, hc]

theorem map_fst_taggedRecords (m : ℕ) :
    (taggedRecords m).map Prod.fst = (List.range (Grid.count m)).filter (fun k => canonical (m, k)) :=
  map_fst_tagged_list m _

theorem tagged_starts_nodup (m : ℕ) : ((taggedRecords m).map Prod.fst).Nodup := by
  rw [map_fst_taggedRecords]
  exact List.Nodup.filter _ (List.nodup_range (n := Grid.count m))

theorem tagged_start_injective (m : ℕ) (i j : Fin (taggedRecords m).length)
    (h : ((taggedRecords m).get i).1 = ((taggedRecords m).get j).1) : i = j := by
  have hi : i.val < ((taggedRecords m).map Prod.fst).length := by simpa only [List.length_map] using i.isLt
  have hj : j.val < ((taggedRecords m).map Prod.fst).length := by simpa only [List.length_map] using j.isLt
  have he : ((taggedRecords m).map Prod.fst)[i.val]'hi = ((taggedRecords m).map Prod.fst)[j.val]'hj := by
    simp only [List.getElem_map]
    exact h
  exact Fin.ext ((tagged_starts_nodup m).getElem_inj_iff.mp he)

theorem tagged_membership (m k : ℕ) (r : Record) (h : (k, r) ∈ taggedRecords m) :
    k < Grid.count m ∧ r ∈ emit (m, k) := by
  obtain ⟨i, hi, hir⟩ := List.mem_flatMap.mp h
  obtain ⟨r', hr', he⟩ := List.mem_map.mp hir
  have hik : i = k := congrArg Prod.fst he
  have hrr : r' = r := congrArg Prod.snd he
  exact ⟨hik ▸ List.mem_range.mp hi, by simpa only [hik, hrr] using hr'⟩

theorem tagged_component (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (k : ℕ) (r : Record) (h : (k, r) ∈ taggedRecords m) :
    ∃ c : (bulkFiniteGraph m).ConnectedComponent,
      k = BulkOrientedPath.points m hm ha c 0 ∧
      r = (bulkComponentLength m c, (BulkPredicate.colour (m, (BulkOrientedPath.points m hm ha c 0, 0)),
        BulkPredicate.colour (m, (BulkOrientedPath.points m hm ha c (bulkComponentLength m c - 1), 0)))) := by
  have hr := (tagged_membership m k r h).2
  have hne : emit (m, k) ≠ [] := by intro he; rw [he] at hr; cases hr
  obtain ⟨c, hc⟩ := (BulkOrientedPath.emit_nonempty_iff m hm ha k).1 hne
  rw [hc, BulkOrientedPath.emitted m hm ha c] at hr
  exact ⟨c, hc, List.mem_singleton.mp hr⟩

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan
