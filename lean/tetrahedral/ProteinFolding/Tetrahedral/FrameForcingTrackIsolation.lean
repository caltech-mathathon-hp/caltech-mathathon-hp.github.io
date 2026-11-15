import ProteinFolding.Tetrahedral.FrameForcingTrackSupport
import ProteinFolding.Tetrahedral.BulkEdgeReversal

/-! The complete track, including its two B-corners, is isolated among
ordinary edge sites once four explicit frame guards are removed. -/

namespace ProteinFolding.Tetrahedral

theorem reverse_edge_end_eq_start (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    octEdgeZigzag m (bulkReverseEdgeFrame F) (2 * m - 2) = octEdgeStart m F := by
  have h := bulkEdgeAnchor_reverse (by omega : 1 ≤ m) F 0 (by omega)
  simp only [bulkEdgeAnchor, Nat.sub_zero] at h
  rw [show 2 * (m - 1) = 2 * m - 2 by omega] at h
  exact h.symm

theorem reverse_edge_inner_eq_two (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    octEdgeZigzag m (bulkReverseEdgeFrame F) (2 * m - 4) = octEdgeZigzag m F 2 := by
  have h := bulkEdgeAnchor_reverse (by omega : 1 ≤ m) F 1 (by omega)
  simp only [bulkEdgeAnchor] at h
  rw [show m - 1 - 1 = m - 2 by omega, show 2 * (m - 2) = 2 * m - 4 by omega] at h
  exact h.symm

theorem reverse_edge_two_eq_inner (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    octEdgeZigzag m (bulkReverseEdgeFrame F) 2 = octEdgeZigzag m F (2 * m - 4) := by
  simpa only [bulkReverseEdgeFrame] using
    (reverse_edge_inner_eq_two m hm (bulkReverseEdgeFrame F)).symm

theorem track_start_corner_neighbours (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (q : Site) (hq : q ∈ octahedron m)
    (hadj : tetrahedralLattice.Adj (octEdgeZigzag m F 1) q) :
    q = octEdgeStart m F ∨ q = octEdgeZigzag m F 2 ∨ q = octEdgeZigzag m F.smallOtherSide 2 := by
  have hc := shared_middle_corner_eq m hm (bulkReverseEdgeFrame F) F.smallOtherSide rfl rfl rfl rfl
  rw [← start_corner_shared m (by omega) F] at hc
  rw [← hc] at hadj
  rcases shared_middle_corner_neighbours m hm (bulkReverseEdgeFrame F) F.smallOtherSide
    rfl rfl rfl rfl q hq hadj with h | h | h
  · exact Or.inl (h.trans (reverse_edge_end_eq_start m hm F))
  · exact Or.inr (Or.inl (h.trans (reverse_edge_inner_eq_two m hm F)))
  · exact Or.inr (Or.inr h)

theorem track_end_vertex_eq_exit_end_vertex (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hk : G.k = F.a) (hj : G.j = F.j) (ha : G.a = F.b) (hb : G.b = F.k) :
    octEdgeZigzag m F.smallOtherSide (2 * m - 2) = octEdgeZigzag m G (2 * m - 2) := by
  have ht := octEdgeEnd_faces m (by omega : 1 ≤ m) F.smallOtherSide
  have hg := octEdgeEnd_faces m (by omega : 1 ≤ m) G
  have htk : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * m - 2)).val F.k = -octRadius m := ht.2.2.2
  have htj : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * m - 2)).val F.j = -octRadius m := ht.2.1
  have hta : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * m - 2)).val F.a = octRadius m := ht.2.2.1
  have htb : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * m - 2)).val F.b = octRadius m := ht.1
  have hgk : tetraCoordinate m (octEdgeZigzag m G (2 * m - 2)).val F.k = -octRadius m := by rw [← hb]; exact hg.2.2.2
  have hgj : tetraCoordinate m (octEdgeZigzag m G (2 * m - 2)).val F.j = -octRadius m := by rw [← hj]; exact hg.2.1
  have hga : tetraCoordinate m (octEdgeZigzag m G (2 * m - 2)).val F.a = octRadius m := by rw [← hk]; exact hg.1
  have hgb : tetraCoordinate m (octEdgeZigzag m G (2 * m - 2)).val F.b = octRadius m := by rw [← ha]; exact hg.2.2.1
  apply Subtype.ext
  apply tetraCoordinate_injective m
  funext d
  rcases F.index_cases d with rfl | rfl | rfl | rfl
  · exact htk.trans hgk.symm
  · exact htj.trans hgj.symm
  · exact hta.trans hga.symm
  · exact htb.trans hgb.symm

theorem track_end_corner_neighbours (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hk : G.k = F.a) (hj : G.j = F.j) (ha : G.a = F.b) (hb : G.b = F.k)
    (q : Site) (hq : q ∈ octahedron m)
    (hadj : tetrahedralLattice.Adj (octEdgeZigzag m F.smallOtherSide (2 * m - 3)) q) :
    q = octEdgeZigzag m G (2 * m - 2) ∨ q = octEdgeZigzag m F.smallOtherSide (2 * m - 4) ∨
      q = octEdgeZigzag m G (2 * m - 4) := by
  rcases shared_middle_corner_neighbours m hm F.smallOtherSide (bulkReverseEdgeFrame G)
    hk hj hb ha q hq hadj with h | h | h
  · exact Or.inl (h.trans (track_end_vertex_eq_exit_end_vertex m hm F G hk hj ha hb))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.trans (reverse_edge_two_eq_inner m hm G)))

theorem frameTrackSites_isolated (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hk : G.k = F.a) (hj : G.j = F.j) (ha : G.a = F.b) (hb : G.b = F.k)
    (V : Finset Site) (hV : V ⊆ bulkDeletedEdges m)
    (hVa : octEdgeStart m F ∉ V) (hVc : octEdgeZigzag m G (2 * m - 2) ∉ V)
    (hEntry : octEdgeZigzag m F 3 ∉ V) (hExit : octEdgeZigzag m G (2 * m - 4) ∉ V) :
    ∀ x ∈ frameTrackSites m F, ∀ y ∈ V, tetrahedralLattice.Adj x y → y ∈ frameTrackSites m F := by
  intro x hx y hy hadj
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  have hr' := Finset.mem_range.mp hr
  have hyEdge := (Finset.mem_filter.mp (hV hy)).2
  obtain ⟨k, j, _, hyOn⟩ := hyEdge
  have hySurface := octEdgeSite_surface m hyOn
  have hm1 : 1 ≤ m := by omega
  by_cases hzero : r = 0
  · rw [hzero, frameTrackPoint, if_pos rfl] at hadj
    obtain ⟨s, _, heq, hstep⟩ := inner_edge_surface_neighbour_index m hm F 2 (by decide) (by omega) y hySurface hadj
    have hs : s = 1 ∨ s = 3 := by omega
    rcases hs with rfl | rfl
    · refine Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
      change octEdgeZigzag m F.smallOtherSide 1 = y
      rw [← start_corner_shared m hm1 F]
      exact heq.symm
    · exact False.elim (hEntry (heq ▸ hy))
  rw [frameTrackPoint, if_neg hzero] at hadj
  by_cases hone : r = 1
  · rw [hone, ← start_corner_shared m hm1 F] at hadj
    rcases track_start_corner_neighbours m hm F y hySurface.1 hadj with h | h | h
    · exact False.elim (hVa (h ▸ hy))
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), h.symm⟩
    · refine Finset.mem_image.mpr ⟨2, Finset.mem_range.mpr (by omega), ?_⟩
      change octEdgeZigzag m F.smallOtherSide 2 = y
      exact h.symm
  by_cases hlast : r = 2 * m - 3
  · rw [hlast] at hadj
    rcases track_end_corner_neighbours m hm F G hk hj ha hb y hySurface.1 hadj with h | h | h
    · exact False.elim (hVc (h ▸ hy))
    · refine Finset.mem_image.mpr ⟨2 * m - 4, Finset.mem_range.mpr (by omega), ?_⟩
      rw [frameTrackPoint, if_neg (by omega)]
      exact h.symm
    · exact False.elim (hExit (h ▸ hy))
  · obtain ⟨s, _, heq, hstep⟩ := inner_edge_surface_neighbour_index m hm F.smallOtherSide r
      (by omega) (by omega) y hySurface hadj
    have hspos : 0 < s := by omega
    refine Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr (by omega), ?_⟩
    rw [frameTrackPoint, if_neg (by omega)]
    exact heq.symm

end ProteinFolding.Tetrahedral
