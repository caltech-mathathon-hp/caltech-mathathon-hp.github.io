import ProteinFolding.Tetrahedral.OctahedralLayers
import ProteinFolding.Tetrahedral.OctahedralReflection

/-! The total number of sites in the octahedron, Section 5.1. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

theorem octahedron_x_bounds {m : ℕ} {p : Site} (hp : p ∈ octahedron m) :
    -octRadius m ≤ p.val 0 ∧ p.val 0 ≤ octRadius m := by
  have hi := (mem_octahedron m p).mp hp
  have h0 := (hi 0).2
  have h1 := (hi 1).2
  have h2 := (hi 2).2
  have h3 := (hi 3).2
  have hx := tetraCoordinate_pair_x m p.val
  have hs := tetraCoordinate_sum m p.val
  omega

def nonnegativeOctahedron (m : ℕ) : Finset Site :=
  (octahedron m).filter (fun p => 0 ≤ p.val 0)

theorem nonnegativeOctahedron_eq_layers (m : ℕ) :
    nonnegativeOctahedron m =
      (Finset.range m).biUnion (evenLayerImage m) ∪
        (Finset.range m).biUnion (oddLayerImage m) := by
  ext p
  constructor
  · intro hp
    have h := Finset.mem_filter.mp hp
    have hx := (octahedron_x_bounds h.1).2
    let n := p.val 0 |>.toNat
    have hn : (n : ℤ) = p.val 0 := Int.toNat_of_nonneg h.2
    let j := n / 2
    have hj : j < m := by dsimp [j]; dsimp [octRadius] at hx; omega
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hmod with he | ho
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_range.mpr hj, (mem_evenLayerImage m j p).mpr ⟨h.1, ?_⟩⟩
      dsimp [j]
      omega
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_range.mpr hj, (mem_oddLayerImage m j p).mpr ⟨h.1, ?_⟩⟩
      dsimp [j]
      omega
  · intro hp
    rcases Finset.mem_union.mp hp with he | ho
    · obtain ⟨j, _, hp⟩ := Finset.mem_biUnion.mp he
      have h := (mem_evenLayerImage m j p).mp hp
      exact Finset.mem_filter.mpr ⟨h.1, by omega⟩
    · obtain ⟨j, _, hp⟩ := Finset.mem_biUnion.mp ho
      have h := (mem_oddLayerImage m j p).mp hp
      exact Finset.mem_filter.mpr ⟨h.1, by omega⟩

def nonnegativeProfileSum (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m, ((m - j) ^ 2 + (m - j - 1) * (m - j))

theorem nonnegativeOctahedron_card (m : ℕ) :
    (nonnegativeOctahedron m).card = nonnegativeProfileSum m := by
  have he : (Finset.range m).toSet.PairwiseDisjoint (evenLayerImage m) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have hi := ((mem_evenLayerImage m i p).mp hp).2
    have hj := ((mem_evenLayerImage m j p).mp hp').2
    exact hij (by omega)
  have ho : (Finset.range m).toSet.PairwiseDisjoint (oddLayerImage m) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have hi := ((mem_oddLayerImage m i p).mp hp).2
    have hj := ((mem_oddLayerImage m j p).mp hp').2
    exact hij (by omega)
  have hdis : Disjoint ((Finset.range m).biUnion (evenLayerImage m))
      ((Finset.range m).biUnion (oddLayerImage m)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp'
    have hi' := ((mem_evenLayerImage m i p).mp hi).2
    have hj' := ((mem_oddLayerImage m j p).mp hj).2
    omega
  rw [nonnegativeOctahedron_eq_layers, Finset.card_union_of_disjoint hdis,
    Finset.card_biUnion he, Finset.card_biUnion ho]
  simp_rw [evenLayerImage_card, oddLayerImage_card]
  exact (Finset.sum_add_distrib).symm

theorem nonnegativeProfileSum_succ (m : ℕ) :
    nonnegativeProfileSum (m + 1) =
      nonnegativeProfileSum m + (m + 1) ^ 2 + m * (m + 1) := by
  unfold nonnegativeProfileSum
  rw [Finset.sum_range_succ']
  simp only [Nat.sub_zero, Nat.add_sub_cancel]
  have heq : ∀ j : ℕ, m + 1 - (j + 1) = m - j := by intro j; omega
  simp_rw [heq]
  omega

theorem nonnegativeProfileSum_eq (m : ℕ) :
    nonnegativeProfileSum m = m ^ 2 + rootSum (m ^ 2) := by
  induction m with
  | zero => simp [nonnegativeProfileSum]
  | succ m ih =>
    rw [nonnegativeProfileSum_succ, ih, rootSum_square_succ]
    ring

theorem octahedron_card_add_central (m : ℕ) :
    (octahedron m).card + (finiteLayer (octahedron m) 0).card =
      2 * (nonnegativeOctahedron m).card := by
  let P := (octahedron m).filter (fun p => 0 < p.val 0)
  let N := (octahedron m).filter (fun p => p.val 0 < 0)
  have hmirror : N.image octMirror = P := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      have h := Finset.mem_filter.mp hq
      apply Finset.mem_filter.mpr
      exact ⟨(octMirror_mem_octahedron m q).mpr h.1, by
        change 0 < -q.val 0; omega⟩
    · intro hp
      have h := Finset.mem_filter.mp hp
      apply Finset.mem_image.mpr
      refine ⟨octMirror p, ?_, octMirror_involutive p⟩
      apply Finset.mem_filter.mpr
      exact ⟨(octMirror_mem_octahedron m p).mpr h.1, by
        change -p.val 0 < 0; omega⟩
  have hncard : N.card = P.card := by
    rw [← hmirror, Finset.card_image_of_injective _ octMirror_injective]
  have htotal : (nonnegativeOctahedron m).card + N.card = (octahedron m).card := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := octahedron m) (p := fun p => 0 ≤ p.val 0)
    simpa only [nonnegativeOctahedron, not_le] using h
  have hcentral : (finiteLayer (octahedron m) 0).card + P.card =
      (nonnegativeOctahedron m).card := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := nonnegativeOctahedron m) (p := fun p => p.val 0 = 0)
    have hzero : (nonnegativeOctahedron m).filter (fun p => p.val 0 = 0) =
        finiteLayer (octahedron m) 0 := by
      ext p
      simp only [nonnegativeOctahedron, finiteLayer, Finset.mem_filter]
      constructor
      · exact fun hp => ⟨hp.1.1, hp.2⟩
      · exact fun hp => ⟨⟨hp.1, by omega⟩, hp.2⟩
    have hpos : (nonnegativeOctahedron m).filter (fun p => ¬ p.val 0 = 0) = P := by
      ext p
      simp only [nonnegativeOctahedron, P, Finset.mem_filter]
      constructor
      · exact fun hp => ⟨hp.1.1, by omega⟩
      · exact fun hp => ⟨⟨hp.1, by omega⟩, by omega⟩
    rw [hzero, hpos] at h
    exact h
  omega

/-- The site count N_m in Section 5.1, for every natural m including 0. -/
theorem octahedron_card (m : ℕ) : (octahedron m).card = octahedralNumber m := by
  have h := octahedron_card_add_central m
  rw [card_octahedron_central_layer, nonnegativeOctahedron_card, nonnegativeProfileSum_eq] at h
  unfold octahedralNumber
  omega

theorem octahedron_card_formula (m : ℕ) :
    (octahedron m).card = m * (4 * m ^ 2 - 1) / 3 := by
  rw [octahedron_card, octahedralNumber_formula]

end ProteinFolding.Tetrahedral
