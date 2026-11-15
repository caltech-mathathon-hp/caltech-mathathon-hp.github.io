import ProteinFolding.Tetrahedral.OctahedralZigzags

/-! Any two distinct octahedral vertices attain the full height range
in some edge direction. The endpoint need not be assumed adjacent. -/

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 1000000 in
theorem distinct_vertices_extreme_direction (m : ℕ) {p q : Site}
    (hp : p ∈ octVertices m) (hq : q ∈ octVertices m) (hne : p ≠ q) :
    ∃ a b : Fin 4, a ≠ b ∧ octEdgeHeight4 m a b p = -2 * octRadius m ∧
      octEdgeHeight4 m a b q = 2 * octRadius m := by
  obtain ⟨⟨ap, sp⟩, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨⟨aq, sq⟩, _, rfl⟩ := Finset.mem_image.mp hq
  fin_cases ap <;> cases sp <;> fin_cases aq <;> cases sq
  all_goals first
    | exact (hne rfl).elim
    | (refine ⟨0, 1, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)
    | (refine ⟨0, 2, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)
    | (refine ⟨0, 3, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)
    | (refine ⟨1, 0, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)
    | (refine ⟨1, 2, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)
    | (refine ⟨1, 3, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)
    | (refine ⟨2, 0, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)
    | (refine ⟨2, 1, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)
    | (refine ⟨2, 3, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)
    | (refine ⟨3, 0, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)
    | (refine ⟨3, 1, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)
    | (refine ⟨3, 2, by decide, ?_, ?_⟩ <;>
        dsimp [octEdgeHeight4, tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre] <;> omega)

theorem distinct_vertices_full_advance (m : ℕ) {p q : Site}
    (hp : p ∈ octVertices m) (hq : q ∈ octVertices m) (hne : p ≠ q) :
    ∃ a b : Fin 4, a ≠ b ∧
      octEdgeHeight4 m a b q = octEdgeHeight4 m a b p + 4 * octRadius m := by
  obtain ⟨a, b, hab, hp', hq'⟩ := distinct_vertices_extreme_direction m hp hq hne
  refine ⟨a, b, hab, ?_⟩
  omega

theorem vertex_minimum_has_edge_frame (m : ℕ) (hm : 2 ≤ m) {p : Site}
    (hp : p ∈ octVertices m) (a b : Fin 4) (hab : a ≠ b)
    (hmin : octEdgeHeight4 m a b p = -2 * octRadius m) :
    ∃ F : OctEdgeFrame, F.a = a ∧ F.b = b ∧ p = octEdgeStart m F := by
  have hpA := octVertices_inA hp
  have hpOct := octVertices_subset_octahedron (show 1 ≤ m by omega) hp
  have hbound := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m p).mp hpOct)
  have ha := hbound a
  have hb := hbound b
  have hR : 0 < octRadius m := by unfold octRadius; omega
  have hpa : tetraCoordinate m p.val a = -octRadius m := by
    unfold octEdgeHeight4 at hmin
    omega
  have hpb : tetraCoordinate m p.val b = octRadius m := by
    unfold octEdgeHeight4 at hmin
    omega
  let highs := Finset.univ.filter (fun d : Fin 4 => tetraCoordinate m p.val d = octRadius m)
  have hhighs : highs.card = 2 := by
    have h := (two_dangling_iff_vertex hm hpOct).mpr hp
    rw [octDanglingDirections_A m hpA hpOct] at h
    exact h
  obtain ⟨k, hk, hkb⟩ := Finset.exists_mem_ne (show 1 < highs.card by omega) b
  have hpk : tetraCoordinate m p.val k = octRadius m := (Finset.mem_filter.mp hk).2
  have hka : k ≠ a := by intro h; subst k; omega
  have hsmall : ({k, a, b} : Finset (Fin 4)).card < (Finset.univ : Finset (Fin 4)).card := by
    simp [hka, hkb, hab]
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hjne : j ≠ k ∧ j ≠ a ∧ j ≠ b := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hj
  let F : OctEdgeFrame := ⟨k, j, a, b, Ne.symm hjne.1, hka, hkb, hjne.2.1, hjne.2.2, hab⟩
  have hsum := tetraCoordinate_sum_frame m F p.val
  change tetraCoordinate m p.val k + tetraCoordinate m p.val j +
    tetraCoordinate m p.val a + tetraCoordinate m p.val b = 0 at hsum
  have hpj : tetraCoordinate m p.val j = -octRadius m := by omega
  refine ⟨F, rfl, rfl, ?_⟩
  have hs := octEdgeStart_spec (show 1 ≤ m by omega) F
  apply Subtype.ext
  apply tetraCoordinate_injective m
  funext i
  rcases F.index_cases i with hi | hi | hi | hi
  · rw [hi]
    exact hpk.trans hs.2.1.symm
  · rw [hi]
    exact hpj.trans hs.2.2.1.symm
  · rw [hi]
    exact hpa.trans hs.2.2.2.1.symm
  · rw [hi]
    exact hpb.trans hs.2.2.2.2.symm

/-- The direction and starting edge frame needed to force a frame chain
between any distinct vertices, including initially antipodal candidates. -/
theorem distinct_vertices_edge_frame (m : ℕ) (hm : 2 ≤ m) {p q : Site}
    (hp : p ∈ octVertices m) (hq : q ∈ octVertices m) (hne : p ≠ q) :
    ∃ F : OctEdgeFrame, p = octEdgeStart m F ∧
      octEdgeHeight4 m F.a F.b q = 2 * octRadius m := by
  obtain ⟨a, b, hab, hmin, hmax⟩ := distinct_vertices_extreme_direction m hp hq hne
  obtain ⟨F, hFa, hFb, hpF⟩ := vertex_minimum_has_edge_frame m hm hp a b hab hmin
  exact ⟨F, hpF, by simpa only [hFa, hFb] using hmax⟩

end ProteinFolding.Tetrahedral
