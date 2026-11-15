import ProteinFolding.Tetrahedral.OctahedralVertices

/-!
# Surface edges of the octahedron, Section 5.6(O3)

The face saturation predicates specify the two alternating colours of an
edge. Bonded surface sites lie on a common such edge. The integer height is
four times the manuscript's edge coordinate, so all calculations stay in ℤ.
-/

namespace ProteinFolding.Tetrahedral

def OctBigFace (m : ℕ) (k : Fin 4) (p : Site) : Prop :=
  p ∈ octahedron m ∧ InASublattice p.val ∧ tetraCoordinate m p.val k = octRadius m

def OctSmallFace (m : ℕ) (j : Fin 4) (p : Site) : Prop :=
  p ∈ octahedron m ∧ InBSublattice p.val ∧
    tetraCoordinate m p.val j = -(2 * (m : ℤ) - 1)

def OctAEdgeSite (m : ℕ) (k j : Fin 4) (p : Site) : Prop :=
  OctBigFace m k p ∧ tetraCoordinate m p.val j = -octRadius m

def OctBEdgeSite (m : ℕ) (k j : Fin 4) (p : Site) : Prop :=
  OctSmallFace m j p ∧ tetraCoordinate m p.val k = 2 * (m : ℤ) - 3

def OctEdgeSite (m : ℕ) (k j : Fin 4) (p : Site) : Prop :=
  OctAEdgeSite m k j p ∨ OctBEdgeSite m k j p

def OctSurfaceSite (m : ℕ) (p : Site) : Prop :=
  p ∈ octahedron m ∧ 0 < (octDanglingDirections m p).card

theorem octSurfaceSite_iff_faces (m : ℕ) (p : Site) :
    OctSurfaceSite m p ↔ (∃ k, OctBigFace m k p) ∨ ∃ j, OctSmallFace m j p := by
  constructor
  · rintro ⟨hp, hs⟩
    obtain ⟨d, hd⟩ := Finset.card_pos.mp hs
    have hout := (Finset.mem_filter.mp hd).2
    rcases p.property with hpA | hpB
    · exact Or.inl ⟨d, hp, hpA, (step_not_mem_octahedron_A m hpA hp d).mp hout⟩
    · exact Or.inr ⟨d, hp, hpB, (step_not_mem_octahedron_B m hpB hp d).mp hout⟩
  · rintro (⟨k, hp, hpA, hk⟩ | ⟨j, hp, hpB, hj⟩)
    · refine ⟨hp, Finset.card_pos.mpr ⟨k, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (step_not_mem_octahedron_A m hpA hp k).mpr hk⟩
    · refine ⟨hp, Finset.card_pos.mpr ⟨j, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (step_not_mem_octahedron_B m hpB hp j).mpr hj⟩

theorem octEdgeSite_surface (m : ℕ) {k j : Fin 4} {p : Site}
    (hp : OctEdgeSite m k j p) : OctSurfaceSite m p := by
  apply (octSurfaceSite_iff_faces m p).mpr
  rcases hp with hp | hp
  · exact Or.inl ⟨k, hp.1⟩
  · exact Or.inr ⟨j, hp.1⟩

/-- The face inequalities force all four incidence conclusions in (O3). -/
theorem bonded_big_small_faces (m : ℕ) {p : Site} {k j d : Fin 4}
    (hp : OctBigFace m k p) (hq : OctSmallFace m j (step p d)) :
    d ≠ k ∧ d ≠ j ∧ k ≠ j ∧
      OctAEdgeSite m k j p ∧ OctBEdgeSite m k j (step p d) := by
  obtain ⟨hp, hpA, hk⟩ := hp
  obtain ⟨hq, hqB, hj⟩ := hq
  have hpbound := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m p).mp hp)
  have hqbound := (inOctahedron_iff_B m hqB).mp ((mem_octahedron m _).mp hq)
  have hpk := hpbound k
  have hpj := hpbound j
  have hqk := hqbound k
  have hqj := hqbound j
  have hqm : 2 ≤ m := by
    have h0 := (hqbound 0).2
    have h1 := (hqbound 1).2
    have h2 := (hqbound 2).2
    have h3 := (hqbound 3).2
    have hs := tetraCoordinate_sum m (step p d).val
    omega
  have hstepk := tetraCoordinate_step_A m hpA d k
  have hstepj := tetraCoordinate_step_A m hpA d j
  have hdk : d ≠ k := by
    intro heq
    have hkd : k = d := heq.symm
    rw [if_pos hkd] at hstepk
    dsimp [octRadius] at *
    omega
  have hdj : d ≠ j := by
    intro heq
    have hjd : j = d := heq.symm
    rw [if_pos hjd] at hstepj
    dsimp [octRadius] at *
    omega
  rw [if_neg (Ne.symm hdk)] at hstepk
  rw [if_neg (Ne.symm hdj)] at hstepj
  have hfj : tetraCoordinate m p.val j = -octRadius m := by
    dsimp [octRadius] at *
    omega
  have hfk : tetraCoordinate m (step p d).val k = 2 * (m : ℤ) - 3 := by
    dsimp [octRadius] at *
    omega
  have hkj : k ≠ j := by
    intro heq
    subst j
    dsimp [octRadius] at *
    omega
  exact ⟨hdk, hdj, hkj, ⟨⟨hp, hpA, hk⟩, hfj⟩, ⟨⟨hq, hqB, hj⟩, hfk⟩⟩

theorem bonded_surface_sites_on_edge (m : ℕ) {p q : Site}
    (hpA : InASublattice p.val) (hp : OctSurfaceSite m p) (hq : OctSurfaceSite m q)
    (hadj : tetrahedralLattice.Adj p q) :
    ∃ k j, k ≠ j ∧ OctAEdgeSite m k j p ∧ OctBEdgeSite m k j q := by
  have hqB : InBSublattice q.val := by
    rcases adj_sublattices hadj with h | h
    · exact h.2
    · exact (sublattices_disjoint p.val hpA h.1).elim
  have hpf := (octSurfaceSite_iff_faces m p).mp hp
  have hqf := (octSurfaceSite_iff_faces m q).mp hq
  obtain ⟨k, hk⟩ : ∃ k, OctBigFace m k p := by
    rcases hpf with h | ⟨j, hj⟩
    · exact h
    · exact (sublattices_disjoint p.val hpA hj.2.1).elim
  obtain ⟨j, hj⟩ : ∃ j, OctSmallFace m j q := by
    rcases hqf with ⟨k, hk⟩ | h
    · exact (sublattices_disjoint q.val hk.2.1 hqB).elim
    · exact h
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp hadj
  have h := bonded_big_small_faces m hk hj
  exact ⟨k, j, h.2.2.1, h.2.2.2⟩

/-- The edge definition accounts for every bonded pair of surface sites. -/
theorem bonded_surface_sites_iff_common_edge (m : ℕ) {p q : Site}
    (hpA : InASublattice p.val) (hadj : tetrahedralLattice.Adj p q) :
    OctSurfaceSite m p ∧ OctSurfaceSite m q ↔
      ∃ k j, k ≠ j ∧ OctAEdgeSite m k j p ∧ OctBEdgeSite m k j q := by
  constructor
  · rintro ⟨hp, hq⟩
    exact bonded_surface_sites_on_edge m hpA hp hq hadj
  · rintro ⟨k, j, _, hp, hq⟩
    exact ⟨octEdgeSite_surface m (Or.inl hp), octEdgeSite_surface m (Or.inr hq)⟩

def octEdgeHeight4 (m : ℕ) (a b : Fin 4) (p : Site) : ℤ :=
  tetraCoordinate m p.val a - tetraCoordinate m p.val b

theorem octEdgeHeight4_bounds (m : ℕ) (a b : Fin 4) {p : Site}
    (hp : p ∈ octahedron m) :
    -2 * octRadius m ≤ octEdgeHeight4 m a b p ∧
      octEdgeHeight4 m a b p ≤ 2 * octRadius m := by
  rcases p.property with hpA | hpB
  · have h := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m p).mp hp)
    have ha := h a
    have hb := h b
    dsimp [octEdgeHeight4]
    omega
  · have h := (inOctahedron_iff_B m hpB).mp ((mem_octahedron m p).mp hp)
    have ha := h a
    have hb := h b
    dsimp [octEdgeHeight4, octRadius]
    omega

theorem octEdgeHeight4_max_iff (m : ℕ) (a b : Fin 4) {p : Site}
    (hp : p ∈ octahedron m) :
    octEdgeHeight4 m a b p = 2 * octRadius m ↔ OctEdgeSite m a b p := by
  rcases p.property with hpA | hpB
  · have h := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m p).mp hp)
    have ha := h a
    have hb := h b
    constructor
    · intro heq
      dsimp [octEdgeHeight4] at heq
      exact Or.inl ⟨⟨hp, hpA, by omega⟩, by omega⟩
    · rintro (⟨⟨_, _, ha⟩, hb⟩ | ⟨⟨_, hpB, _⟩, _⟩)
      · dsimp [octEdgeHeight4]
        omega
      · exact (sublattices_disjoint p.val hpA hpB).elim
  · have h := (inOctahedron_iff_B m hpB).mp ((mem_octahedron m p).mp hp)
    have ha := h a
    have hb := h b
    constructor
    · intro heq
      dsimp [octEdgeHeight4, octRadius] at heq
      exact Or.inr ⟨⟨hp, hpB, by omega⟩, by omega⟩
    · rintro (⟨⟨_, hpA, _⟩, _⟩ | ⟨⟨_, _, hb⟩, ha⟩)
      · exact (sublattices_disjoint p.val hpA hpB).elim
      · dsimp [octEdgeHeight4, octRadius]
        omega

theorem octEdgeHeight4_min_iff (m : ℕ) (a b : Fin 4) {p : Site}
    (hp : p ∈ octahedron m) :
    octEdgeHeight4 m a b p = -2 * octRadius m ↔ OctEdgeSite m b a p := by
  have h := octEdgeHeight4_max_iff m b a hp
  have heq : octEdgeHeight4 m a b p = -octEdgeHeight4 m b a p := by
    dsimp [octEdgeHeight4]
    omega
  rw [heq]
  convert h using 1
  omega

theorem octEdgeHeight4_step_A (m : ℕ) (a b d : Fin 4) {p : Site}
    (hpA : InASublattice p.val) :
    octEdgeHeight4 m a b (step p d) = octEdgeHeight4 m a b p +
      (if a = d then 4 else 0) - (if b = d then 4 else 0) := by
  unfold octEdgeHeight4
  rw [tetraCoordinate_step_A m hpA, tetraCoordinate_step_A m hpA]
  split_ifs <;> omega

theorem octEdgeHeight4_step_B (m : ℕ) (a b d : Fin 4) {p : Site}
    (hpB : InBSublattice p.val) :
    octEdgeHeight4 m a b (step p d) = octEdgeHeight4 m a b p -
      (if a = d then 4 else 0) + (if b = d then 4 else 0) := by
  unfold octEdgeHeight4
  rw [tetraCoordinate_step_B m hpB, tetraCoordinate_step_B m hpB]
  split_ifs <;> omega

theorem octEdgeHeight4_adj_bounds (m : ℕ) (a b : Fin 4) {p q : Site}
    (hadj : tetrahedralLattice.Adj p q) :
    -4 ≤ octEdgeHeight4 m a b q - octEdgeHeight4 m a b p ∧
      octEdgeHeight4 m a b q - octEdgeHeight4 m a b p ≤ 4 := by
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp hadj
  rcases p.property with hpA | hpB
  · rw [octEdgeHeight4_step_A m a b d hpA]
    split_ifs <;> omega
  · rw [octEdgeHeight4_step_B m a b d hpB]
    split_ifs <;> omega

end ProteinFolding.Tetrahedral
