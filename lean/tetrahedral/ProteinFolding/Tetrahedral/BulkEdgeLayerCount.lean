import ProteinFolding.Tetrahedral.OctahedralEdgeUnion

/-! Exact edge-site counts in each nonnegative layer. -/

namespace ProteinFolding.Tetrahedral

def edgeEndIndices (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u => u.val = 0 ∨ u.val + 1 = n)

theorem edgeEndIndices_card_one : (edgeEndIndices 1).card = 1 := by decide
theorem edgeEndIndices_card_zero : (edgeEndIndices 0).card = 0 := by decide

theorem edgeEndIndices_card {n : ℕ} (hn : 2 ≤ n) : (edgeEndIndices n).card = 2 := by
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have heq : edgeEndIndices n = {first, last} := by
    ext u
    simp only [edgeEndIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hu | hu)
      · exact Or.inl (Fin.ext hu)
      · exact Or.inr (Fin.ext (by dsimp [last]; omega))
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · right
        dsimp [last]
        omega
  have hne : first ≠ last := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [first, last] at hv
    omega
  rw [heq]
  simp [hne]

def edgeSquareBoundary (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun uv => uv.1 ∈ edgeEndIndices n ∨ uv.2 ∈ edgeEndIndices n)

theorem edgeSquareBoundary_card {n : ℕ} (hn : 2 ≤ n) :
    (edgeSquareBoundary n).card = 4 * n - 4 := by
  have heq : edgeSquareBoundary n =
      (edgeEndIndices n ×ˢ Finset.univ) ∪ ((Finset.univ \ edgeEndIndices n) ×ˢ edgeEndIndices n) := by
    ext uv
    simp only [edgeSquareBoundary, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_product, Finset.mem_sdiff, and_true]
    by_cases h : uv.1 ∈ edgeEndIndices n <;> simp [h]
  have hdis : Disjoint (edgeEndIndices n ×ˢ (Finset.univ : Finset (Fin n)))
      ((Finset.univ \ edgeEndIndices n) ×ˢ edgeEndIndices n) := by
    apply Finset.disjoint_left.mpr
    intro uv hu hv
    exact (Finset.mem_sdiff.mp (Finset.mem_product.mp hv).1).2 (Finset.mem_product.mp hu).1
  rw [heq, Finset.card_union_of_disjoint hdis, Finset.card_product, Finset.card_product,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), edgeEndIndices_card hn]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

def evenDeletedLayer (m j : ℕ) : Finset Site := (evenLayerImage m j).filter (bulkOnDeletedEdge m)
def oddDeletedLayer (m j : ℕ) : Finset Site := (oddLayerImage m j).filter (bulkOnDeletedEdge m)

theorem evenLayerPoint_pair_injective (j a b : ℕ) :
    Function.Injective (fun uv : Fin a × Fin b => evenLayerPoint j uv.1.val uv.2.val) := by
  intro uv wz heq
  have hy := congrArg (fun p : Site => p.val 1) heq
  have hz := congrArg (fun p : Site => p.val 2) heq
  dsimp [evenLayerPoint, evenLayerCoordinates] at hy hz
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem oddLayerPoint_pair_injective (j a b : ℕ) :
    Function.Injective (fun uv : Fin a × Fin b => oddLayerPoint j uv.1.val uv.2.val) := by
  intro uv wz heq
  have hy := congrArg (fun p : Site => p.val 1) heq
  have hz := congrArg (fun p : Site => p.val 2) heq
  dsimp [oddLayerPoint, oddLayerCoordinates] at hy hz
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem evenDeletedLayer_central_eq (m : ℕ) : evenDeletedLayer m 0 =
    (edgeSquareBoundary m).image (fun uv => evenLayerPoint 0 uv.1.val uv.2.val) := by
  have hfilter : (Finset.univ.filter (fun uv : Fin m × Fin m =>
      bulkOnDeletedEdge m (evenLayerPoint 0 uv.1.val uv.2.val))) = edgeSquareBoundary m := by
    ext uv
    simp only [edgeSquareBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [deleted_even_central_iff (m := m) uv.1.isLt uv.2.isLt]
    simp only [edgeEndIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact or_assoc.symm
  unfold evenDeletedLayer evenLayerImage
  simp only [Nat.sub_zero]
  rw [Finset.filter_image, hfilter]

theorem evenDeletedLayer_positive_eq (m j : ℕ) (hj : 1 ≤ j) : evenDeletedLayer m j =
    (edgeEndIndices (m - j) ×ˢ edgeEndIndices (m - j)).image
      (fun uv => evenLayerPoint j uv.1.val uv.2.val) := by
  unfold evenDeletedLayer evenLayerImage
  rw [Finset.filter_image]
  congr 1
  ext uv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [deleted_even_positive_iff hj uv.1.isLt uv.2.isLt]
  simp only [edgeEndIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem oddDeletedLayer_central_eq (m : ℕ) : oddDeletedLayer m 0 =
    ((Finset.univ : Finset (Fin (m - 1))) ×ˢ edgeEndIndices m).image
      (fun uv => oddLayerPoint 0 uv.1.val uv.2.val) := by
  unfold oddDeletedLayer oddLayerImage
  simp only [Nat.sub_zero]
  rw [Finset.filter_image]
  congr 1
  ext uv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [deleted_odd_central_iff (m := m) uv.1.isLt uv.2.isLt]
  simp only [edgeEndIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem oddDeletedLayer_positive_eq (m j : ℕ) (hj : 1 ≤ j) : oddDeletedLayer m j =
    (edgeEndIndices (m - j - 1) ×ˢ edgeEndIndices (m - j)).image
      (fun uv => oddLayerPoint j uv.1.val uv.2.val) := by
  unfold oddDeletedLayer oddLayerImage
  rw [Finset.filter_image]
  congr 1
  ext uv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [deleted_odd_positive_iff hj uv.1.isLt uv.2.isLt]
  simp only [edgeEndIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem evenDeletedLayer_card_central {m : ℕ} (hm : 2 ≤ m) :
    (evenDeletedLayer m 0).card = 4 * m - 4 := by
  rw [evenDeletedLayer_central_eq, Finset.card_image_of_injective _ (evenLayerPoint_pair_injective 0 m m)]
  exact edgeSquareBoundary_card hm

theorem evenDeletedLayer_card_positive {m j : ℕ} (hj : 1 ≤ j) (hjm : j < m) :
    (evenDeletedLayer m j).card = if j + 1 = m then 1 else 4 := by
  rw [evenDeletedLayer_positive_eq m j hj,
    Finset.card_image_of_injective _ (evenLayerPoint_pair_injective j (m - j) (m - j)),
    Finset.card_product]
  by_cases hlast : j + 1 = m
  · rw [if_pos hlast, show m - j = 1 by omega, edgeEndIndices_card_one]
  · rw [if_neg hlast, edgeEndIndices_card (by omega : 2 ≤ m - j)]

theorem oddDeletedLayer_card_central {m : ℕ} (hm : 2 ≤ m) :
    (oddDeletedLayer m 0).card = 2 * (m - 1) := by
  rw [oddDeletedLayer_central_eq,
    Finset.card_image_of_injective _ (oddLayerPoint_pair_injective 0 (m - 1) m),
    Finset.card_product, edgeEndIndices_card hm]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

theorem oddDeletedLayer_card_positive {m j : ℕ} (hj : 1 ≤ j) (hjm : j < m) :
    (oddDeletedLayer m j).card = if j + 2 = m then 2 else if j + 1 = m then 0 else 4 := by
  rw [oddDeletedLayer_positive_eq m j hj,
    Finset.card_image_of_injective _ (oddLayerPoint_pair_injective j (m - j - 1) (m - j)),
    Finset.card_product]
  by_cases hpen : j + 2 = m
  · rw [if_pos hpen, show m - j - 1 = 1 by omega, show m - j = 2 by omega,
      edgeEndIndices_card_one, edgeEndIndices_card (by decide : 2 ≤ 2)]
  · rw [if_neg hpen]
    by_cases hlast : j + 1 = m
    · rw [if_pos hlast, show m - j - 1 = 0 by omega, edgeEndIndices_card_zero]
      omega
    · rw [if_neg hlast, edgeEndIndices_card (by omega : 2 ≤ m - j - 1),
        edgeEndIndices_card (by omega : 2 ≤ m - j)]

end ProteinFolding.Tetrahedral
