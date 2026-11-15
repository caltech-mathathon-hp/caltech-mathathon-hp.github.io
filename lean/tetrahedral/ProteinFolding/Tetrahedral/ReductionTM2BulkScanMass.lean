import ProteinFolding.Tetrahedral.ReductionTM2BulkScanComponents
import ProteinFolding.Tetrahedral.ReductionTM2BulkOutput
import ProteinFolding.Tetrahedral.PathCoverMass

/-! Exact mass and minimum lengths for the actually computed canonical scan.
The only remaining geometric hypothesis is acyclicity of the fixed graph. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

open scoped BigOperators

set_option maxHeartbeats 2000000

local instance (m : ℕ) : Finite (bulkFiniteGraph m).ConnectedComponent :=
  Finite.of_surjective (bulkFiniteGraph m).connectedComponentMk (fun c => c.exists_rep)
noncomputable local instance (m : ℕ) : Fintype (bulkFiniteGraph m).ConnectedComponent := Fintype.ofFinite _

noncomputable def activeStarts (m : ℕ) : Finset ℕ :=
  (Finset.range (Grid.count m)).filter (fun k => emit (m, k) ≠ [])

noncomputable def weight (m k : ℕ) : ℕ := ((emit (m, k)).map Prod.fst).sum

theorem flatMap_sum (m : ℕ) (xs : List ℕ) :
    ((xs.flatMap (fun k => emit (m, k))).map Prod.fst).sum = (xs.map (weight m)).sum := by
  induction xs with
  | nil => rfl
  | cons k xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih, weight]

theorem lengths_sum_range (m : ℕ) :
    (lengths m).sum = ∑ k ∈ Finset.range (Grid.count m), weight m k := by
  rw [lengths, records, flatMap_sum]
  simpa only [List.toFinset_range] using
    (List.sum_toFinset (weight m) (List.nodup_range (n := Grid.count m))).symm

theorem range_sum_active (m : ℕ) :
    (∑ k ∈ Finset.range (Grid.count m), weight m k) = ∑ k ∈ activeStarts m, weight m k := by
  symm
  rw [activeStarts, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases he : emit (m, k) = []
  · simp [weight, he]
  · simp [he]

theorem sum_components_eq_active (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    (∑ c : (bulkFiniteGraph m).ConnectedComponent, bulkComponentLength m c) =
      ∑ k ∈ activeStarts m, weight m k := by
  classical
  apply Finset.sum_bij (fun c _ => BulkOrientedPath.points m hm ha c 0)
  · intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (BulkOrientedPath.first_bound m hm ha c),
      (BulkOrientedPath.emit_nonempty_iff m hm ha _).2 ⟨c, rfl⟩⟩
  · intro c hc d hd he
    exact BulkOrientedPath.first_injective m hm ha he
  · intro k hk
    have hne := (Finset.mem_filter.mp hk).2
    obtain ⟨c, hc⟩ := (BulkOrientedPath.emit_nonempty_iff m hm ha k).1 hne
    exact ⟨c, Finset.mem_univ _, hc.symm⟩
  · intro c hc
    rw [weight, BulkOrientedPath.emitted m hm ha c]
    simp

theorem lengths_sum_components (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    (lengths m).sum = ∑ c : (bulkFiniteGraph m).ConnectedComponent, bulkComponentLength m c := by
  rw [lengths_sum_range, range_sum_active, ← sum_components_eq_active m hm ha]

theorem lengths_ge_three (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (n : ℕ) (hn : n ∈ lengths m) : 3 ≤ n := by
  obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hn
  obtain ⟨k, hk, hkr⟩ := List.mem_flatMap.mp hr
  have hne : emit (m, k) ≠ [] := by
    intro he
    rw [he] at hkr
    cases hkr
  obtain ⟨c, hc⟩ := (BulkOrientedPath.emit_nonempty_iff m hm ha k).1 hne
  rw [hc, BulkOrientedPath.emitted m hm ha c] at hkr
  have he := List.mem_singleton.mp hkr
  subst r
  exact hrn ▸ BulkComponentPath.length_ge_three m hm ha c

theorem lengths_mass (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    (lengths m).sum + 24 * m = octahedralNumber m + 42 := by
  rw [lengths_sum_components m hm ha]
  exact sum_bulkComponentLength_mass m (by omega)
    (fun p hp => bulkCoverNeighbours_card_le_two m (by omega) p)

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan
