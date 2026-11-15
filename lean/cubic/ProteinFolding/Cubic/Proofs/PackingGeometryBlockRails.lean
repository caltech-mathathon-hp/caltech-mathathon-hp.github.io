import ProteinFolding.Cubic.Proofs.PackingGeometryFrameBlocks

/-! Every literal E block in the walls lies on one of the two rails left by
the prefix. This uses injectivity of the full fold to exclude occupied prefix
sites, rather than assuming a preferred orientation of the cube. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

theorem corner_free_skeleton_path_in_one_edge (a : Site) (d : ℕ)
    (qs : List Site) (hnd : qs.Nodup) (hchain : qs.IsChain cubicLattice.Adj)
    (hsk : ∀ p ∈ qs, EdgeSkeleton a (d + 2) p)
    (hcorner : ∀ p ∈ qs, p ∉ cornerFinset a d) (hne : qs ≠ []) :
    ∃ e, qs.toFinset ⊆ openEdgeFinset a d e := by
  have hc : visitedCorners a d qs = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpq, hpc⟩ := Finset.mem_filter.mp hp
    exact hcorner p (List.mem_toFinset.mp hpq) hpc
  have hk := visitedEdges_card_le a d qs hnd hchain hsk
  rw [hc, Finset.card_empty, Nat.zero_add] at hk
  have hnonempty : (visitedEdges a d qs).Nonempty := by
    obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    cases hl : edgeLabel a d p with
    | none => exact False.elim (hcorner p (by simp)
        ((edgeLabel_eq_none_iff a d p (hsk p (by simp))).mp hl))
    | some e => exact ⟨e, mem_visitedEdges_of_label a d (p :: rest) p e (by simp) hl⟩
  have hk1 : (visitedEdges a d qs).card = 1 := Nat.le_antisymm hk
    (Finset.card_pos.mpr hnonempty)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hk1
  refine ⟨e, ?_⟩
  have hsub := path_subset_edge_cover a d qs hsk
  rw [hc, he] at hsub
  simpa only [Finset.empty_union, Finset.singleton_biUnion] using hsub

theorem prefix_initial_end_le (q Q : ℕ) :
    3 * (9 * depth q Q + 8) ≤ (prefixWord q Q).length := by
  simp only [prefixWord, List.length_append, edgeWord_length]
  omega

theorem prefix_second_end_le (q Q : ℕ) :
    (beforeSecondEdge q Q).length + 3 * depth q Q ≤ (prefixWord q Q).length := by
  simp only [beforeSecondEdge, prefixWord, List.length_append, edgeWord_length]
  omega

theorem after_prefix_edge_disjoint_initial (q Q : ℕ) (items : List ℕ) (t : ℕ)
    (o : EdgeOccurrence (frameWord q Q items) t)
    (hafter : (prefixWord q Q).length ≤ o.pre.length)
    (f : Fold cubicLattice (frameWord q Q items).length) :
    Disjoint (o.sites f) (initialEdgePath q Q items f).toFinset := by
  rw [o.sites_eq_pathList]
  apply separated_edge_paths_disjoint f [] (afterInitialEdge q Q items) o.pre o.post
    (9 * depth q Q + 8) t (frameWord_initial_decomposition q Q items) o.word_eq
  simpa only [List.length_nil, Nat.zero_add] using (prefix_initial_end_le q Q).trans hafter

theorem after_prefix_edge_disjoint_second (q Q : ℕ) (items : List ℕ) (t : ℕ)
    (o : EdgeOccurrence (frameWord q Q items) t)
    (hafter : (prefixWord q Q).length ≤ o.pre.length)
    (f : Fold cubicLattice (frameWord q Q items).length) :
    Disjoint (o.sites f) (secondEdgePath q Q items f).toFinset := by
  rw [o.sites_eq_pathList]
  exact separated_edge_paths_disjoint f (beforeSecondEdge q Q) (afterSecondEdge q Q items)
    o.pre o.post (depth q Q) t (frameWord_second_decomposition q Q items) o.word_eq
    ((prefix_second_end_le q Q).trans hafter)

/-- A nonempty E block after the literal prefix has its whole compressed path
on one of the two unoccupied open edges. -/
theorem after_prefix_edge_on_remaining_rail (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (t : ℕ) (ht : 0 < t) (o : EdgeOccurrence (frameWord q Q items) t)
    (hafter : (prefixWord q Q).length ≤ o.pre.length)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q))
    (second : CubeEdge) (hsecond : (secondEdgePath q Q items f).toFinset =
      openEdgeFinset a (depth q Q) second) :
    ∃ e ∈ ((Finset.univ \ visitedEdges a (depth q Q) (initialEdgePath q Q items f)) \ {second}),
      ∀ i, o.path f i ∈ openEdgeFinset a (depth q Q) e := by
  let ps := initialEdgePath q Q items f
  let qs := edgeHPathList o.pre o.post t (foldOnWord o.word_eq f)
  let fp := foldOnWord (frameWord_initial_decomposition q Q items) f
  have hpnd := edgeHPathList_nodup [] (afterInitialEdge q Q items) (9 * depth q Q + 8) fp
  have hpchain := edgeHPathList_chain [] (afterInitialEdge q Q items) (9 * depth q Q + 8)
    fp a _ (frame_initial_pack q Q items f a hpack)
  have hpsk := edgeHPathList_skeleton [] (afterInitialEdge q Q items) (9 * depth q Q + 8)
    fp a _ (frame_initial_pack q Q items f a hpack)
  have hplen := initialEdgePath_length q Q items f
  have hd : 0 < depth q Q := by have := depth_two_le q Q hq; omega
  have hdisj := after_prefix_edge_disjoint_initial q Q items t o hafter f
  have hsk : ∀ p ∈ qs, EdgeSkeleton a (depth q Q + 2) p := by
    apply edgeHPathList_skeleton
    rw [foldOnWord_hydrophobicSites]
    exact hpack
  have hcorner : ∀ p ∈ qs, p ∉ cornerFinset a (depth q Q) := by
    intro p hp hc
    have hm : p ∈ visitedCorners a (depth q Q) ps := by
      rw [maximal_skeleton_path_covers_corners a (depth q Q) hd ps hpnd hpchain hpsk hplen]
      exact hc
    apply Finset.disjoint_left.mp hdisj
    · rw [o.sites_eq_pathList]
      exact List.mem_toFinset.mpr hp
    · exact (Finset.mem_filter.mp hm).1
  obtain ⟨e, he⟩ := corner_free_skeleton_path_in_one_edge a (depth q Q) qs
    (edgeHPathList_nodup o.pre o.post t (foldOnWord o.word_eq f))
    (edgeHPathList_chain o.pre o.post t (foldOnWord o.word_eq f) a _
      (by rw [foldOnWord_hydrophobicSites]; exact hpack)) hsk hcorner
    (by intro h; have hl := congrArg List.length h; simp only [qs, edgeHPathList, List.length_ofFn, List.length_nil] at hl; omega)
  have hmem : ∀ i, o.path f i ∈ openEdgeFinset a (depth q Q) e := by
    intro i
    apply he
    rw [← o.sites_eq_pathList]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let i : Fin t := ⟨0, ht⟩
  have hpoint := hmem i
  have hpointSites : o.path f i ∈ o.sites f := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hnotvisited : e ∉ visitedEdges a (depth q Q) ps := by
    intro hev
    have hp : o.path f i ∈ ps.toFinset := by
      rw [maximal_skeleton_path_fills_edges a (depth q Q) hd ps hpnd hpchain hpsk hplen]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, hev, hpoint⟩)
    exact Finset.disjoint_left.mp hdisj hpointSites hp
  have hnotsecond : e ≠ second := by
    intro heq
    have hp : o.path f i ∈ (secondEdgePath q Q items f).toFinset := by rw [hsecond, ← heq]; exact hpoint
    exact Finset.disjoint_left.mp (after_prefix_edge_disjoint_second q Q items t o hafter f) hpointSites hp
  refine ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotvisited⟩,
    by simpa only [Finset.mem_singleton] using hnotsecond⟩, hmem⟩

theorem frameBlock_length_pos (q Q : ℕ) (hQ : 0 < Q) (b : FrameBlock q) :
    0 < anchorLength Q (frameBlockKind b) := by
  unfold frameBlockKind
  split_ifs <;> simp only [anchorLength, alpha, beta] <;> omega

theorem frameBlock_on_remaining_rail (q Q : ℕ) (items : List ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q))
    (second : CubeEdge) (hsecond : (secondEdgePath q Q items f).toFinset =
      openEdgeFinset a (depth q Q) second) (b : FrameBlock q) :
    ∃ e ∈ ((Finset.univ \ visitedEdges a (depth q Q) (initialEdgePath q Q items f)) \ {second}),
      ∀ i, (frameBlockOccurrence q Q items b).path f i ∈ openEdgeFinset a (depth q Q) e := by
  apply after_prefix_edge_on_remaining_rail q Q items hq _ (frameBlock_length_pos q Q hQ b)
    _ _ f a hpack second hsecond
  rw [frameBlockOccurrence_offset]
  exact frameBlockOffset_after_prefix q Q b

end ProteinFolding.CubicPackingGeometry
