import ProteinFolding.Tetrahedral.BulkEdgeLayerCount

/-! The actual deleted-edge union has 24m−42 sites for m≥3. -/

namespace ProteinFolding.Tetrahedral

def nonnegativeDeletedEdges (m : ℕ) : Finset Site :=
  (bulkDeletedEdges m).filter (fun p => 0 ≤ p.val 0)

theorem nonnegativeDeletedEdges_eq_layers (m : ℕ) : nonnegativeDeletedEdges m =
    (Finset.range m).biUnion (evenDeletedLayer m) ∪
      (Finset.range m).biUnion (oddDeletedLayer m) := by
  have heq : nonnegativeDeletedEdges m = (nonnegativeOctahedron m).filter (bulkOnDeletedEdge m) := by
    ext p
    simp only [nonnegativeDeletedEdges, bulkDeletedEdges, nonnegativeOctahedron, Finset.mem_filter]
    exact and_right_comm
  rw [heq, nonnegativeOctahedron_eq_layers, Finset.filter_union, Finset.filter_biUnion,
    Finset.filter_biUnion]
  rfl

theorem nonnegativeDeletedEdges_card (m : ℕ) :
    (nonnegativeDeletedEdges m).card =
      (∑ j ∈ Finset.range m, (evenDeletedLayer m j).card) +
      (∑ j ∈ Finset.range m, (oddDeletedLayer m j).card) := by
  have he : (Finset.range m).toSet.PairwiseDisjoint (evenDeletedLayer m) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hi := ((mem_evenLayerImage m i p).mp (Finset.mem_filter.mp hp).1).2
    have hj := ((mem_evenLayerImage m j p).mp (Finset.mem_filter.mp hq).1).2
    exact hij (by omega)
  have ho : (Finset.range m).toSet.PairwiseDisjoint (oddDeletedLayer m) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hi := ((mem_oddLayerImage m i p).mp (Finset.mem_filter.mp hp).1).2
    have hj := ((mem_oddLayerImage m j p).mp (Finset.mem_filter.mp hq).1).2
    exact hij (by omega)
  have hdis : Disjoint ((Finset.range m).biUnion (evenDeletedLayer m))
      ((Finset.range m).biUnion (oddDeletedLayer m)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hq
    have hix := ((mem_evenLayerImage m i p).mp (Finset.mem_filter.mp hi).1).2
    have hjx := ((mem_oddLayerImage m j p).mp (Finset.mem_filter.mp hj).1).2
    omega
  rw [nonnegativeDeletedEdges_eq_layers, Finset.card_union_of_disjoint hdis,
    Finset.card_biUnion he, Finset.card_biUnion ho]

theorem sum_evenDeletedLayer_card {m : ℕ} (hm : 3 ≤ m) :
    (∑ j ∈ Finset.range m, (evenDeletedLayer m j).card) = 8 * m - 11 := by
  have hsplit := Finset.sum_range_succ' (f := fun j => (evenDeletedLayer m j).card) (m - 1)
  rw [show m - 1 + 1 = m by omega] at hsplit
  have hlastSplit := Finset.sum_range_succ (f := fun j => (evenDeletedLayer m (j + 1)).card) (m - 2)
  rw [show m - 2 + 1 = m - 1 by omega] at hlastSplit
  have hconstant : (∑ j ∈ Finset.range (m - 2), (evenDeletedLayer m (j + 1)).card) = 4 * (m - 2) := by
    calc
      _ = ∑ _j ∈ Finset.range (m - 2), 4 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [evenDeletedLayer_card_positive (by omega : 1 ≤ j + 1) (by omega : j + 1 < m),
          if_neg (by omega : j + 1 + 1 ≠ m)]
      _ = _ := by simp [Nat.mul_comm]
  have hlast : (evenDeletedLayer m (m - 1)).card = 1 := by
    rw [evenDeletedLayer_card_positive (by omega : 1 ≤ m - 1) (by omega : m - 1 < m),
      if_pos (by omega : m - 1 + 1 = m)]
  have hzero := evenDeletedLayer_card_central (by omega : 2 ≤ m)
  omega

theorem sum_oddDeletedLayer_card {m : ℕ} (hm : 3 ≤ m) :
    (∑ j ∈ Finset.range m, (oddDeletedLayer m j).card) = 6 * m - 12 := by
  have hsplit := Finset.sum_range_succ' (f := fun j => (oddDeletedLayer m j).card) (m - 1)
  rw [show m - 1 + 1 = m by omega] at hsplit
  have hlastSplit := Finset.sum_range_succ (f := fun j => (oddDeletedLayer m (j + 1)).card) (m - 2)
  rw [show m - 2 + 1 = m - 1 by omega] at hlastSplit
  have hpenSplit := Finset.sum_range_succ (f := fun j => (oddDeletedLayer m (j + 1)).card) (m - 3)
  rw [show m - 3 + 1 = m - 2 by omega] at hpenSplit
  have hconstant : (∑ j ∈ Finset.range (m - 3), (oddDeletedLayer m (j + 1)).card) = 4 * (m - 3) := by
    calc
      _ = ∑ _j ∈ Finset.range (m - 3), 4 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [oddDeletedLayer_card_positive (by omega : 1 ≤ j + 1) (by omega : j + 1 < m),
          if_neg (by omega : j + 1 + 2 ≠ m), if_neg (by omega : j + 1 + 1 ≠ m)]
      _ = _ := by simp [Nat.mul_comm]
  have hlast : (oddDeletedLayer m (m - 1)).card = 0 := by
    rw [oddDeletedLayer_card_positive (by omega : 1 ≤ m - 1) (by omega : m - 1 < m),
      if_neg (by omega : m - 1 + 2 ≠ m), if_pos (by omega : m - 1 + 1 = m)]
  have hpen : (oddDeletedLayer m (m - 2)).card = 2 := by
    rw [oddDeletedLayer_card_positive (by omega : 1 ≤ m - 2) (by omega : m - 2 < m),
      if_pos (by omega : m - 2 + 2 = m)]
  have hzero := oddDeletedLayer_card_central (by omega : 2 ≤ m)
  omega

theorem nonnegativeDeletedEdges_card_formula {m : ℕ} (hm : 3 ≤ m) :
    (nonnegativeDeletedEdges m).card = 14 * m - 23 := by
  rw [nonnegativeDeletedEdges_card, sum_evenDeletedLayer_card hm, sum_oddDeletedLayer_card hm]
  omega

theorem bulkDeletedEdges_central_layer (m : ℕ) :
    finiteLayer (bulkDeletedEdges m) 0 = evenDeletedLayer m 0 := by
  ext p
  simp only [finiteLayer, bulkDeletedEdges, evenDeletedLayer, Finset.mem_filter]
  rw [mem_evenLayerImage]
  constructor
  · rintro ⟨⟨hp, he⟩, hx⟩
    exact ⟨⟨hp, by omega⟩, he⟩
  · rintro ⟨⟨hp, hx⟩, he⟩
    exact ⟨⟨hp, he⟩, by omega⟩

theorem octMirror_mem_bulkDeletedEdges (m : ℕ) (p : Site) :
    octMirror p ∈ bulkDeletedEdges m ↔ p ∈ bulkDeletedEdges m := by
  simp only [bulkDeletedEdges, Finset.mem_filter, octMirror_mem_octahedron, deletedEdge_octMirror_iff]

theorem bulkDeletedEdges_card_add_central (m : ℕ) :
    (bulkDeletedEdges m).card + (finiteLayer (bulkDeletedEdges m) 0).card =
      2 * (nonnegativeDeletedEdges m).card := by
  let P := (bulkDeletedEdges m).filter (fun p => 0 < p.val 0)
  let N := (bulkDeletedEdges m).filter (fun p => p.val 0 < 0)
  have hmirror : N.image octMirror = P := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      have h := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨(octMirror_mem_bulkDeletedEdges m q).mpr h.1, by
        change 0 < -q.val 0; omega⟩
    · intro hp
      have h := Finset.mem_filter.mp hp
      refine Finset.mem_image.mpr ⟨octMirror p, ?_, octMirror_involutive p⟩
      exact Finset.mem_filter.mpr ⟨(octMirror_mem_bulkDeletedEdges m p).mpr h.1, by
        change -p.val 0 < 0; omega⟩
  have hncard : N.card = P.card := by
    rw [← hmirror, Finset.card_image_of_injective _ octMirror_injective]
  have htotal : (nonnegativeDeletedEdges m).card + N.card = (bulkDeletedEdges m).card := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := bulkDeletedEdges m) (p := fun p => 0 ≤ p.val 0)
    simpa only [nonnegativeDeletedEdges, not_le] using h
  have hcentral : (finiteLayer (bulkDeletedEdges m) 0).card + P.card =
      (nonnegativeDeletedEdges m).card := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := nonnegativeDeletedEdges m) (p := fun p => p.val 0 = 0)
    have hzero : (nonnegativeDeletedEdges m).filter (fun p => p.val 0 = 0) =
        finiteLayer (bulkDeletedEdges m) 0 := by
      ext p
      simp only [nonnegativeDeletedEdges, finiteLayer, Finset.mem_filter]
      constructor
      · exact fun hp => ⟨hp.1.1, hp.2⟩
      · exact fun hp => ⟨⟨hp.1, by omega⟩, hp.2⟩
    have hpos : (nonnegativeDeletedEdges m).filter (fun p => ¬ p.val 0 = 0) = P := by
      ext p
      simp only [nonnegativeDeletedEdges, P, Finset.mem_filter]
      constructor
      · exact fun hp => ⟨hp.1.1, by omega⟩
      · exact fun hp => ⟨⟨hp.1, by omega⟩, by omega⟩
    rw [hzero, hpos] at h
    exact h
  omega

theorem bulkDeletedEdges_card_add {m : ℕ} (hm : 3 ≤ m) :
    (bulkDeletedEdges m).card + 42 = 24 * m := by
  have h := bulkDeletedEdges_card_add_central m
  rw [bulkDeletedEdges_central_layer, evenDeletedLayer_card_central (by omega : 2 ≤ m),
    nonnegativeDeletedEdges_card_formula hm] at h
  omega

theorem bulkDeletedEdges_card {m : ℕ} (hm : 3 ≤ m) :
    (bulkDeletedEdges m).card = 24 * m - 42 := by
  have h := bulkDeletedEdges_card_add hm
  omega

theorem bulkInterior_card_add_edges (m : ℕ) :
    (bulkInterior m).card + (bulkDeletedEdges m).card = octahedralNumber m := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (bulkOnDeletedEdge m) (octahedron m))
  change (bulkInterior m).card + (bulkDeletedEdges m).card = (octahedron m).card at h
  simpa only [octahedron_card] using h

theorem bulkInterior_card_add {m : ℕ} (hm : 3 ≤ m) :
    (bulkInterior m).card + 24 * m = octahedralNumber m + 42 := by
  have he := bulkDeletedEdges_card_add hm
  have hi := bulkInterior_card_add_edges m
  omega

end ProteinFolding.Tetrahedral
