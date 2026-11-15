import Shelf.Cube

namespace ProteinFolding.Shelf

open ProteinFolding ProteinFolding.CubicPackingGeometry

/-- Nodes of different edges are different points. -/
theorem openEdgePoint_eq_iff (d : ℕ) (e e' : CubeEdge) (r s : Fin d) :
    openEdgePoint 0 d e r = openEdgePoint 0 d e' s ↔ e = e' ∧ r = s := by
  constructor
  · intro h
    have := openEdgePoint_injective 0 d (a₁ := (e, r)) (a₂ := (e', s)) h
    simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

theorem mem_openEdgeFinset_iff (d : ℕ) (e : CubeEdge) (p : Site) :
    p ∈ openEdgeFinset 0 d e ↔ ∃ r : Fin d, p = openEdgePoint 0 d e r := by
  simp [openEdgeFinset, eq_comm]

/-- Every point of the skeleton is a corner or a node of exactly one edge. -/
theorem skeleton_cases (d : ℕ) {p : Site} (hp : EdgeSkeleton 0 (d + 2) p) :
    p ∈ cornerFinset 0 d ∨ ∃ e : CubeEdge, ∃ r : Fin d, p = openEdgePoint 0 d e r := by
  rw [← mem_skeletonFinset, ← skeleton_decomposition, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact Or.inl hp
  · right
    obtain ⟨⟨e, r⟩, _, he⟩ := Finset.mem_image.mp hp
    exact ⟨e, r, he.symm⟩

/-- Lemma 10: nodes of two edges that do not touch are at distance at least `n - 1 = d + 1`. -/
theorem far_edges (d : ℕ) {e e' : CubeEdge} (h : NoCommonCorner e e') (r s : Fin d) :
    d + 1 ≤ latticeDistance (openEdgePoint 0 d e r) (openEdgePoint 0 d e' s) :=
  nonincident_edges_distance 0 d e e' r s h

private theorem two_coords (p q : Site) {i j : Fin 3} (hij : i ≠ j) :
    (p i - q i).natAbs + (p j - q j).natAbs ≤ latticeDistance p q := by
  rw [CubicCertificates.distance_eq]
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega

private theorem three_coords (p q : Site) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    (p i - q i).natAbs + (p j - q j).natAbs + (p k - q k).natAbs ≤ latticeDistance p q := by
  rw [CubicCertificates.distance_eq]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hik hjk ⊢ <;> omega

private theorem endValue_zero_cases (d : ℕ) (side : Fin 2) :
    endValue 0 d side = 0 ∨ endValue 0 d side = (d : ℤ) + 1 := by
  fin_cases side <;> simp [endValue]

/-- A node and a point with a coordinate in `{0, N}` in the edge's direction differ by at least
`1` in that coordinate. -/
private theorem axis_gap (d : ℕ) (e f : CubeEdge) (r s : Fin d) (hk : e.axis ≠ f.axis) :
    1 ≤ (openEdgePoint 0 d e r e.axis - openEdgePoint 0 d f s e.axis).natAbs := by
  rw [openEdgePoint_axis, openEdgePoint_fixed 0 d f s e.axis hk]
  simp only [Pi.zero_apply]
  have := r.isLt
  rcases endValue_zero_cases d (fixedSide f e.axis) with h | h <;> rw [h] <;> simp <;> omega

/-- Lemma 10, the case of equality: the two nodes have the same number on their edges. -/
theorem far_edges_eq (d : ℕ) {e e' : CubeEdge} (h : NoCommonCorner e e') (r s : Fin d)
    (heq : latticeDistance (openEdgePoint 0 d e r) (openEdgePoint 0 d e' s) = d + 1) : r = s := by
  obtain ⟨k, hke, hkf, hside⟩ := nonincident_separating_coordinate e e' h
  have hk : (openEdgePoint 0 d e r k - openEdgePoint 0 d e' s k).natAbs = d + 1 := by
    rw [openEdgePoint_fixed 0 d e r k hke, openEdgePoint_fixed 0 d e' s k hkf,
      endValue_distance_of_ne _ d _ _ hside]
  by_cases hax : e.axis = e'.axis
  · have h2 := two_coords (openEdgePoint 0 d e r) (openEdgePoint 0 d e' s) hke
    rw [openEdgePoint_axis, hax, openEdgePoint_axis] at h2
    apply Fin.ext
    omega
  · have h3 := three_coords (openEdgePoint 0 d e r) (openEdgePoint 0 d e' s) hke hkf hax
    have g1 := axis_gap d e e' r s hax
    have g2 := axis_gap d e' e s r (Ne.symm hax)
    rw [← Int.natAbs_neg, neg_sub] at g2
    omega

/-- Lemma 10, as used in Step 4: if equality holds and one node is an end node, so is the other. -/
theorem far_edges_end (d : ℕ) {e e' : CubeEdge} (h : NoCommonCorner e e') (r s : Fin d)
    (heq : latticeDistance (openEdgePoint 0 d e r) (openEdgePoint 0 d e' s) = d + 1)
    (hr : IsEnd r) : IsEnd s := by
  rwa [← far_edges_eq d h r s heq]

/-- A path that runs through all `d` nodes of an edge is the edge, in one of its two directions.
In particular it starts and ends at the two end nodes. -/
theorem fills_edge_direction (d : ℕ) (e : CubeEdge) (p : Fin d → Site)
    (hinj : Function.Injective p)
    (hstep : ∀ i j : Fin d, i.val + 1 = j.val → cubicLattice.Adj (p i) (p j))
    (hedge : ∀ i, p i ∈ openEdgeFinset 0 d e) :
    (∀ i : Fin d, p i = openEdgePoint 0 d e i) ∨ (∀ i : Fin d, p i = openEdgePoint 0 d e i.rev) := by
  rcases Nat.eq_zero_or_pos d with rfl | ht
  · exact Or.inl (fun i => i.elim0)
  have hex : ∀ i, ∃ r : Fin d, openEdgePoint 0 d e r = p i := by
    intro i
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp (hedge i)
    exact ⟨r, hr⟩
  let r : Fin d → Fin d := fun i => Classical.choose (hex i)
  have hr : ∀ i, openEdgePoint 0 d e (r i) = p i := fun i => Classical.choose_spec (hex i)
  let x : Fin d → ℤ := fun i => (r i).val
  have hx : Function.Injective x := by
    intro i j he
    have he' : r i = r j := by apply Fin.ext; dsimp [x] at he; omega
    apply hinj
    rw [← hr i, ← hr j, he']
  have hxs : ∀ i j : Fin d, i.val + 1 = j.val → (x j - x i).natAbs = 1 := by
    intro i j hij
    have h := (hstep i j hij).symm
    change latticeDistance (p j) (p i) = 1 at h
    rw [← hr j, ← hr i, openEdgePoint_distance] at h
    exact h
  have h0 := (r ⟨0, ht⟩).isLt
  have hl := (r ⟨d - 1, by omega⟩).isLt
  rcases line_path_interval ht x hx hxs with hxint | hxint
  · left
    have hx0 := hxint ⟨d - 1, by omega⟩
    dsimp only [x] at hx0
    intro i
    have hi := hxint i
    dsimp only [x] at hi
    have : r i = i := by apply Fin.ext; omega
    rw [← hr i, this]
  · right
    have hx0 := hxint ⟨d - 1, by omega⟩
    dsimp only [x] at hx0
    intro i
    have hi := hxint i
    dsimp only [x] at hi
    have : r i = i.rev := by apply Fin.ext; simp only [Fin.val_rev] at hx0 ⊢; omega
    rw [← hr i, this]

end ProteinFolding.Shelf
