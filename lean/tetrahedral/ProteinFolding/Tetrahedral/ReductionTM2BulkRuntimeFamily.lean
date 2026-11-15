import ProteinFolding.Tetrahedral.ReductionTM2BulkRealizationEnds
import ProteinFolding.Tetrahedral.ReductionTM2BulkOutput

/-! The physical witness family is indexed by the actual computed length
list, with the exact computed endpoint-colour list in the same order. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

set_option maxHeartbeats 2000000

theorem lengths_eq_tagged (m : ℕ) :
    lengths m = (taggedRecords m).map (fun e => e.2.1) := by
  rw [lengths, ← map_snd_taggedRecords, List.map_map]
  rfl

theorem colours_eq_tagged (m : ℕ) :
    colours m = (taggedRecords m).map (fun e => e.2.2) := by
  rw [colours, ← map_snd_taggedRecords, List.map_map]
  rfl

theorem lengths_length_tagged (m : ℕ) : (lengths m).length = (taggedRecords m).length := by
  rw [lengths_eq_tagged, List.length_map]

theorem colours_length_lengths (m : ℕ) : (colours m).length = (lengths m).length := by
  rw [colours_eq_tagged, lengths_eq_tagged, List.length_map, List.length_map]

def outputIndex (m : ℕ) (j : Fin (lengths m).length) : Fin (taggedRecords m).length :=
  ⟨j.val, by rw [← lengths_length_tagged]; exact j.isLt⟩

def colourIndex (m : ℕ) (j : Fin (lengths m).length) : Fin (colours m).length :=
  ⟨j.val, by rw [colours_length_lengths]; exact j.isLt⟩

theorem outputIndex_injective (m : ℕ) : Function.Injective (outputIndex m) := by
  intro i j he
  have hv := congrArg (fun k : Fin (taggedRecords m).length => k.val) he
  exact Fin.ext hv

theorem outputIndex_surjective (m : ℕ) : Function.Surjective (outputIndex m) := by
  intro k
  refine ⟨⟨k.val, by rw [lengths_length_tagged]; exact k.isLt⟩, ?_⟩
  exact Fin.ext rfl

theorem output_length (m : ℕ) (j : Fin (lengths m).length) :
    (lengths m).get j = ((taggedRecords m).get (outputIndex m j)).2.1 := by
  change (lengths m)[j.val]'j.isLt = ((taggedRecords m)[j.val]'(outputIndex m j).isLt).2.1
  simp only [lengths_eq_tagged, List.getElem_map]

theorem output_colours (m : ℕ) (j : Fin (lengths m).length) :
    (colours m).get (colourIndex m j) = ((taggedRecords m).get (outputIndex m j)).2.2 := by
  change (colours m)[j.val]'(colourIndex m j).isLt = ((taggedRecords m)[j.val]'(outputIndex m j).isLt).2.2
  simp only [colours_eq_tagged, List.getElem_map]

noncomputable def runtimeFold (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : Fold tetrahedralLattice ((lengths m).get j) :=
  (physicalFold m hm ha (outputIndex m j)).onLength (output_length m j)

theorem runtimeFold_length_ge_three (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : 3 ≤ (lengths m).get j := by
  rw [output_length]
  exact physicalFold_length_ge_three m hm ha _

theorem runtimeFold_inside (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (i : Fin ((lengths m).get j)) :
    (runtimeFold m hm ha j).pos i ∈ bulkInterior m :=
  physicalFold_inside m hm ha (outputIndex m j) _

theorem runtimeFold_disjoint (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j k : Fin (lengths m).length) (hne : j ≠ k) :
    Disjoint (Set.range (runtimeFold m hm ha j).pos) (Set.range (runtimeFold m hm ha k).pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨i, hi⟩ ⟨l, hl⟩
  have hd := physicalFold_disjoint m hm ha (outputIndex m j) (outputIndex m k)
    (fun he => hne (outputIndex_injective m he))
  exact Set.disjoint_left.mp hd ⟨Fin.cast (output_length m j) i, hi⟩
    ⟨Fin.cast (output_length m k) l, hl⟩

theorem runtimeFold_covers (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (p : Site) (hp : p ∈ bulkInterior m) :
    ∃ j : Fin (lengths m).length, ∃ i, (runtimeFold m hm ha j).pos i = p := by
  obtain ⟨k, i, hi⟩ := physicalFold_covers m hm ha p hp
  obtain ⟨j, rfl⟩ := outputIndex_surjective m k
  let l : Fin ((lengths m).get j) := Fin.cast (output_length m j).symm i
  refine ⟨j, l, ?_⟩
  have hcast : Fin.cast (output_length m j) l = i := Fin.ext rfl
  change (physicalFold m hm ha (outputIndex m j)).pos (Fin.cast (output_length m j) l) = p
  rw [hcast]
  exact hi

noncomputable def runtimeFirst (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : Site :=
  (runtimeFold m hm ha j).pos ⟨0, by have h := runtimeFold_length_ge_three m hm ha j; omega⟩

noncomputable def runtimeLast (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : Site :=
  (runtimeFold m hm ha j).pos ⟨(lengths m).get j - 1,
    by have h := runtimeFold_length_ge_three m hm ha j; omega⟩

theorem runtimeFirst_eq (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : runtimeFirst m hm ha j = physicalFirst m hm ha (outputIndex m j) := rfl

theorem runtimeLast_eq (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : runtimeLast m hm ha j = physicalLast m hm ha (outputIndex m j) := by
  have he := output_length m j
  have hcast : Fin.cast he (⟨(lengths m).get j - 1,
      by have h := runtimeFold_length_ge_three m hm ha j; omega⟩ : Fin ((lengths m).get j)) =
      (⟨((taggedRecords m).get (outputIndex m j)).2.1 - 1,
        by have h := physicalFold_length_ge_three m hm ha (outputIndex m j); omega⟩ :
        Fin ((taggedRecords m).get (outputIndex m j)).2.1) := by
    apply Fin.ext
    change (lengths m).get j - 1 = ((taggedRecords m).get (outputIndex m j)).2.1 - 1
    rw [he]
  change (physicalFold m hm ha (outputIndex m j)).pos (Fin.cast he _) = _
  rw [hcast]
  rfl

theorem runtimeFold_colours (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) :
    (FarField.colour (runtimeFirst m hm ha j), FarField.colour (runtimeLast m hm ha j)) =
      (colours m).get (colourIndex m j) := by
  rw [runtimeFirst_eq, runtimeLast_eq, output_colours]
  exact physicalFold_colours m hm ha _

theorem runtimeFirst_surface (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : OctSurfaceSite m (runtimeFirst m hm ha j) := by
  rw [runtimeFirst_eq]
  exact physicalFirst_surface m hm ha _

theorem runtimeLast_surface (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : OctSurfaceSite m (runtimeLast m hm ha j) := by
  rw [runtimeLast_eq]
  exact physicalLast_surface m hm ha _

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan
