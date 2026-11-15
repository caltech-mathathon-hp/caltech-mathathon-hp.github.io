import ProteinFolding.Tetrahedral.FrameForcingTrackPath
import ProteinFolding.Tetrahedral.FrameForcingMiddleCorner
import ProteinFolding.Tetrahedral.FrameForcingFrameVertices

/-! Exact support facts for the soundness track, including its two corners
and the omitted terminal corner of the actual frame. -/

namespace ProteinFolding.Tetrahedral

theorem frameTrackSites_card (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) :
    (frameTrackSites m F).card = 2 * m - 2 := by
  rw [frameTrackSites, Finset.card_image_of_injective _ (frameTrackPoint_injective m hm F), Finset.card_range]

theorem frameTrackPoint_mem_deleted (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r < 2 * m - 2) : frameTrackPoint m F r ∈ bulkDeletedEdges m := by
  have hm1 : 1 ≤ m := by omega
  by_cases hzero : r = 0
  · rw [hzero, frameTrackPoint, if_pos rfl]
    have he := octEdgeZigzag_mem hm1 F (by omega : 2 < 2 * m - 1)
    exact Finset.mem_filter.mpr ⟨(octEdgeSite_surface m he).1, F.k, F.j, F.kj, he⟩
  · rw [frameTrackPoint, if_neg hzero]
    have he := octEdgeZigzag_mem hm1 F.smallOtherSide (by omega : r < 2 * m - 1)
    exact Finset.mem_filter.mpr ⟨(octEdgeSite_surface m he).1,
      F.smallOtherSide.k, F.smallOtherSide.j, F.smallOtherSide.kj, he⟩

theorem frameTrackPoint_not_vertex (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r < 2 * m - 2) : frameTrackPoint m F r ∉ octVertices m := by
  have hm1 : 1 ≤ m := by omega
  intro hv
  by_cases hzero : r = 0
  · rw [hzero, frameTrackPoint, if_pos rfl] at hv
    rcases octEdgeZigzag_vertex_endpoints m (by omega) F 2 hv with h | h
    · change octEdgeZigzag m F 2 = octEdgeZigzag m F 0 at h
      have hi := octEdgeZigzag_injective hm1 F h
      omega
    · have hi := octEdgeZigzag_injective hm1 F h
      omega
  · rw [frameTrackPoint, if_neg hzero] at hv
    rcases octEdgeZigzag_vertex_endpoints m (by omega) F.smallOtherSide r hv with h | h
    · change octEdgeZigzag m F.smallOtherSide r = octEdgeZigzag m F.smallOtherSide 0 at h
      exact hzero (octEdgeZigzag_injective hm1 F.smallOtherSide h)
    · have hi := octEdgeZigzag_injective hm1 F.smallOtherSide h
      omega

theorem frameTrackPoint_ne_terminal_corner (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (r : ℕ) :
    frameTrackPoint m F r ≠ octEdgeZigzag m F (2 * m - 3) := by
  have hm1 : 1 ≤ m := by omega
  have hc := end_corner_faces m hm F
  have hH : frameH2 m F (octEdgeZigzag m F (2 * m - 3)) = 2 := by
    dsimp only [frameH2]
    rw [hc.2.2.2.1, hc.2.2.2.2]
    omega
  have hK : frameK2 m F (octEdgeZigzag m F (2 * m - 3)) = -2 := by
    dsimp only [frameK2]
    rw [hc.2.2.2.1, hc.2.2.1]
    omega
  intro heq
  have h := congrArg (frameH2 m F) heq
  rw [frameTrackPoint_H2 m hm1 F r, hH] at h
  have hr : r = 1 := by omega
  subst r
  have h' := congrArg (frameK2 m F) heq
  change frameK2 m F (octEdgeZigzag m F.smallOtherSide 1) = _ at h'
  rw [(track_edge_height_data m hm1 F 1).2, hK] at h'
  dsimp [octRadius] at h'
  omega

theorem track_end_corner_eq_exit_end_corner (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hk : G.k = F.a) (hj : G.j = F.j) (ha : G.a = F.b) (hb : G.b = F.k) :
    octEdgeZigzag m F.smallOtherSide (2 * m - 3) = octEdgeZigzag m G (2 * m - 3) := by
  have ht := end_corner_faces m hm F.smallOtherSide
  have hg := end_corner_faces m hm G
  have htk : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * m - 3)).val F.k = -octRadius m + 3 := ht.2.2.2.2
  have htj : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * m - 3)).val F.j = -octRadius m - 1 := ht.2.2.1
  have hta : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * m - 3)).val F.a = octRadius m - 1 := ht.2.2.2.1
  have htb : tetraCoordinate m (octEdgeZigzag m F.smallOtherSide (2 * m - 3)).val F.b = octRadius m - 1 := ht.2.1
  have hgk : tetraCoordinate m (octEdgeZigzag m G (2 * m - 3)).val F.k = -octRadius m + 3 := by rw [← hb]; exact hg.2.2.2.2
  have hgj : tetraCoordinate m (octEdgeZigzag m G (2 * m - 3)).val F.j = -octRadius m - 1 := by rw [← hj]; exact hg.2.2.1
  have hga : tetraCoordinate m (octEdgeZigzag m G (2 * m - 3)).val F.a = octRadius m - 1 := by rw [← hk]; exact hg.2.1
  have hgb : tetraCoordinate m (octEdgeZigzag m G (2 * m - 3)).val F.b = octRadius m - 1 := by rw [← ha]; exact hg.2.2.2.1
  apply Subtype.ext
  apply tetraCoordinate_injective m
  funext d
  rcases F.index_cases d with rfl | rfl | rfl | rfl
  · exact htk.trans hgk.symm
  · exact htj.trans hgj.symm
  · exact hta.trans hga.symm
  · exact htb.trans hgb.symm

end ProteinFolding.Tetrahedral
