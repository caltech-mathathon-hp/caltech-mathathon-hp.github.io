import ProteinFolding.Tetrahedral.OctahedralCount
import ProteinFolding.Tetrahedral.OctahedralBoundary
import ProteinFolding.Tetrahedral.Layers

/-! Internal-edge and boundary counts of the octahedron (Section 5.1). -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

theorem step_mem_octahedron_of_x_decreases (m : ℕ) {p : Site} (hp : p ∈ octahedron m)
    (hxpos : 0 < p.val 0) (d : Fin 4)
    (hx : (step p d).val 0 = p.val 0 - 1) : step p d ∈ octahedron m := by
  have hsum := tetraCoordinate_sum m p.val
  have hpair := tetraCoordinate_pair_x m p.val
  rcases p.property with hpA | hpB
  · have hi := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m p).mp hp)
    have h2 := hi 2
    have h3 := hi 3
    have hs := congrFun (step_val_of_A p hpA d) 0
    rw [bondVector_eq_bondComponent] at hs
    fin_cases d
    · change (step p 0).val 0 = p.val 0 + 1 at hs
      change (step p 0).val 0 = p.val 0 - 1 at hx
      omega
    · change (step p 1).val 0 = p.val 0 + 1 at hs
      change (step p 1).val 0 = p.val 0 - 1 at hx
      omega
    · rw [step_mem_octahedron_A m hpA hp]
      change tetraCoordinate m p.val 2 < octRadius m
      omega
    · rw [step_mem_octahedron_A m hpA hp]
      change tetraCoordinate m p.val 3 < octRadius m
      omega
  · have hi := (inOctahedron_iff_B m hpB).mp ((mem_octahedron m p).mp hp)
    have h0 := hi 0
    have h1 := hi 1
    have hs := congrFun (step_val_of_B p hpB d) 0
    rw [bondVector_eq_bondComponent] at hs
    fin_cases d
    · rw [step_mem_octahedron_B m hpB hp]
      change -(2 * (m : ℤ) - 1) < tetraCoordinate m p.val 0
      omega
    · rw [step_mem_octahedron_B m hpB hp]
      change -(2 * (m : ℤ) - 1) < tetraCoordinate m p.val 1
      omega
    · change (step p 2).val 0 = p.val 0 + 1 at hs
      change (step p 2).val 0 = p.val 0 - 1 at hx
      omega
    · change (step p 3).val 0 = p.val 0 + 1 at hs
      change (step p 3).val 0 = p.val 0 - 1 at hx
      omega

theorem neighbour_mem_octahedron_of_positive_below (m : ℕ) {p q : Site}
    (hp : p ∈ octahedron m) (hxpos : 0 < p.val 0)
    (hadj : tetrahedralLattice.Adj p q) (hx : q.val 0 = p.val 0 - 1) :
    q ∈ octahedron m := by
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp hadj
  exact step_mem_octahedron_of_x_decreases m hp hxpos d hx

theorem neighbour_mem_octahedron_of_negative_above (m : ℕ) {p q : Site}
    (hp : p ∈ octahedron m) (hxneg : p.val 0 < 0)
    (hadj : tetrahedralLattice.Adj p q) (hx : q.val 0 = p.val 0 + 1) :
    q ∈ octahedron m := by
  have hp' := (octMirror_mem_octahedron m p).mpr hp
  have hpos : 0 < (octMirror p).val 0 := by change 0 < -p.val 0; omega
  have hx' : (octMirror q).val 0 = (octMirror p).val 0 - 1 := by
    change -q.val 0 = -p.val 0 - 1
    omega
  exact (octMirror_mem_octahedron m q).mp
    (neighbour_mem_octahedron_of_positive_below m hp' hpos (octMirror_adj hadj) hx')

/-- Each edge is directed from the endpoint farther from the central layer. -/
def InwardBond (p q : Site) : Prop := tetrahedralLattice.Adj p q ∧
  ((0 < p.val 0 ∧ q.val 0 = p.val 0 - 1) ∨
    (p.val 0 < 0 ∧ q.val 0 = p.val 0 + 1))

instance decidableInwardBond : DecidableRel InwardBond := fun p q =>
  inferInstanceAs (Decidable (tetrahedralLattice.Adj p q ∧
    ((0 < p.val 0 ∧ q.val 0 = p.val 0 - 1) ∨
      (p.val 0 < 0 ∧ q.val 0 = p.val 0 + 1))))

theorem adj_iff_inward_or_reverse (p q : Site) :
    tetrahedralLattice.Adj p q ↔ InwardBond p q ∨ InwardBond q p := by
  constructor
  · intro h
    have hx := adj_coordinate h 0
    have hd : ((0 < p.val 0 ∧ q.val 0 = p.val 0 - 1) ∨
        (p.val 0 < 0 ∧ q.val 0 = p.val 0 + 1)) ∨
      ((0 < q.val 0 ∧ p.val 0 = q.val 0 - 1) ∨
        (q.val 0 < 0 ∧ p.val 0 = q.val 0 + 1)) := by omega
    exact hd.elim (fun hd => Or.inl ⟨h, hd⟩) (fun hd => Or.inr ⟨h.symm, hd⟩)
  · intro h
    exact h.elim (fun h => h.1) (fun h => h.1.symm)

theorem inwardBond_asymm {p q : Site} (hpq : InwardBond p q) : ¬ InwardBond q p := by
  intro hqp
  have hp := hpq.2
  have hq := hqp.2
  omega

def inwardEdgeCount (S : Finset Site) : ℕ :=
  ((S ×ˢ S).filter (fun pq => InwardBond pq.1 pq.2)).card

theorem inwardEdgeCount_eq_sum (S : Finset Site) :
    inwardEdgeCount S = ∑ p ∈ S, (S.filter (fun q => InwardBond p q)).card := by
  simp only [inwardEdgeCount, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

theorem inwardNeighbour_card (S : Finset Site) (p : Site) :
    (internalNeighbours S p).card = (S.filter (fun q => InwardBond p q)).card +
      (S.filter (fun q => InwardBond q p)).card := by
  rw [internalNeighbours_eq_filter]
  have heq : S.filter (fun q => tetrahedralLattice.Adj p q) =
      S.filter (fun q => InwardBond p q) ∪ S.filter (fun q => InwardBond q p) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_union, adj_iff_inward_or_reverse]
    exact and_or_left
  rw [heq, Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (by
    intro q h h'
    exact inwardBond_asymm (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp h').2)

theorem internalEdgeCount_eq_inwardEdgeCount (S : Finset Site) :
    internalEdgeCount S = inwardEdgeCount S := by
  have hsum : (∑ p ∈ S, (internalNeighbours S p).card) = 2 * inwardEdgeCount S := by
    simp_rw [inwardNeighbour_card]
    rw [Finset.sum_add_distrib]
    have hswap : (∑ p ∈ S, (S.filter (fun q => InwardBond q p)).card) =
        ∑ p ∈ S, (S.filter (fun q => InwardBond p q)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    rw [hswap, ← inwardEdgeCount_eq_sum]
    omega
  have h := sum_internalNeighbours S
  omega

theorem inwardNeighbours_octahedron_card (m : ℕ) {p : Site} (hp : p ∈ octahedron m) :
    ((octahedron m).filter (fun q => InwardBond p q)).card =
      if p.val 0 = 0 then 0 else 2 := by
  by_cases hzero : p.val 0 = 0
  · rw [if_pos hzero]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have h := (Finset.mem_filter.mp hq).2.2
    omega
  · rw [if_neg hzero]
    by_cases hpos : 0 < p.val 0
    · have heq : (octahedron m).filter (fun q => InwardBond p q) = neighboursBelow p := by
        ext q
        simp only [Finset.mem_filter, neighboursBelow, mem_neighbours]
        constructor
        · rintro ⟨_, hadj, hdir⟩
          exact ⟨hadj, by omega⟩
        · rintro ⟨hadj, hx⟩
          exact ⟨neighbour_mem_octahedron_of_positive_below m hp hpos hadj hx,
            hadj, Or.inl ⟨hpos, hx⟩⟩
      rw [heq, card_neighboursBelow]
    · have hneg : p.val 0 < 0 := by omega
      have heq : (octahedron m).filter (fun q => InwardBond p q) = neighboursAbove p := by
        ext q
        simp only [Finset.mem_filter, neighboursAbove, mem_neighbours]
        constructor
        · rintro ⟨_, hadj, hdir⟩
          exact ⟨hadj, by omega⟩
        · rintro ⟨hadj, hx⟩
          exact ⟨neighbour_mem_octahedron_of_negative_above m hp hneg hadj hx,
            hadj, Or.inr ⟨hneg, hx⟩⟩
      rw [heq, card_neighboursAbove]

theorem octahedron_internalEdgeCount_add (m : ℕ) :
    internalEdgeCount (octahedron m) + 2 * m ^ 2 = 2 * octahedralNumber m := by
  rw [internalEdgeCount_eq_inwardEdgeCount, inwardEdgeCount_eq_sum]
  have hc := Finset.sum_congr (s₁ := octahedron m) rfl
    (fun p hp => inwardNeighbours_octahedron_card m hp)
  rw [hc]
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := octahedron m) (p := fun p => p.val 0 = 0)
  change (finiteLayer (octahedron m) 0).card +
    ((octahedron m).filter (fun p => ¬ p.val 0 = 0)).card = (octahedron m).card at hpart
  rw [card_octahedron_central_layer, octahedron_card] at hpart
  have hsum : (∑ p ∈ octahedron m, if p.val 0 = 0 then 0 else 2) =
      2 * ((octahedron m).filter (fun p => ¬ p.val 0 = 0)).card := by
    rw [Finset.card_eq_sum_ones]
    simp only [Finset.sum_filter]
    simp_rw [Nat.two_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hz : p.val 0 = 0 <;> simp [hz]
  rw [hsum]
  omega

theorem octahedron_internalEdgeCount (m : ℕ) :
    internalEdgeCount (octahedron m) = 2 * (octahedralNumber m - m ^ 2) := by
  have h := octahedron_internalEdgeCount_add m
  have hn : m ^ 2 ≤ octahedralNumber m := by unfold octahedralNumber; omega
  omega

theorem octahedron_boundaryCount (m : ℕ) : boundaryCount (octahedron m) = 4 * m ^ 2 := by
  have hd := degree_boundary_identity (octahedron m)
  have he := octahedron_internalEdgeCount_add m
  rw [octahedron_card] at hd
  omega

end ProteinFolding.Tetrahedral
