import Shelf.Cube

namespace ProteinFolding.Shelf

open ProteinFolding ProteinFolding.CubicPackingGeometry

/-- Lemma 9, first sentence: a simple path on the skeleton has at most `9n - 10` vertices (`n = d + 2`). -/
theorem longPath_length_le (d : ℕ) (ps : List Site) (hnd : ps.Nodup)
    (hchain : ps.IsChain cubicLattice.Adj) (hsk : ∀ p ∈ ps, EdgeSkeleton 0 (d + 2) p) :
    ps.length ≤ 9 * (d + 2) - 10 := by
  have := skeleton_path_length_le 0 d ps hnd hchain hsk
  omega

/-- The points of a longest path are its corners and the nodes of its visited edges. -/
private theorem mem_longPath_iff (d : ℕ) (hd : 0 < d) (ps : List Site) (hnd : ps.Nodup)
    (hchain : ps.IsChain cubicLattice.Adj) (hsk : ∀ p ∈ ps, EdgeSkeleton 0 (d + 2) p)
    (hlen : ps.length = 9 * (d + 2) - 10) (p : Site) :
    p ∈ ps ↔ p ∈ cornerFinset 0 d ∨ ∃ e ∈ visitedEdges 0 d ps, p ∈ openEdgeFinset 0 d e := by
  have h := maximal_skeleton_path_fills_edges 0 d hd ps hnd hchain hsk (by omega)
  rw [← List.mem_toFinset, h, Finset.mem_union, Finset.mem_biUnion]

/-- A point is a node of at most one edge. -/
private theorem node_edge_unique (d : ℕ) {e e' : CubeEdge} {p : Site}
    (he : p ∈ openEdgeFinset 0 d e) (he' : p ∈ openEdgeFinset 0 d e') : e = e' := by
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp he'
  have := openEdgePoint_injective 0 d (a₁ := (e', s)) (a₂ := (e, r)) hs
  exact (congrArg Prod.fst this).symm

/-- A node is not a corner. -/
private theorem node_not_corner (d : ℕ) {e : CubeEdge} {p : Site}
    (he : p ∈ openEdgeFinset 0 d e) : p ∉ cornerFinset 0 d := by
  intro hc
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp he
  exact Finset.disjoint_left.mp (cornerFinset_disjoint_open 0 d) hc
    (Finset.mem_image.mpr ⟨(e, r), Finset.mem_univ _, rfl⟩)

/-- On a longest path, an edge that the path does not visit has no node on the path. -/
theorem unvisited_edge_avoids (d : ℕ) (hd : 0 < d) (ps : List Site) (hnd : ps.Nodup)
    (hchain : ps.IsChain cubicLattice.Adj) (hsk : ∀ p ∈ ps, EdgeSkeleton 0 (d + 2) p)
    (hlen : ps.length = 9 * (d + 2) - 10) {e : CubeEdge} (he : e ∉ visitedEdges 0 d ps) :
    ∀ p ∈ openEdgeFinset 0 d e, p ∉ ps := by
  intro p hp hps
  rcases (mem_longPath_iff d hd ps hnd hchain hsk hlen p).mp hps with hc | ⟨e', he', hp'⟩
  · exact node_not_corner d hp hc
  · exact he (node_edge_unique d hp' hp ▸ he')

/-- Lemma 9, second sentence: a simple path with exactly `9n - 10` vertices contains all corners and
all nodes of nine edges, and no two of the three remaining ("free") edges touch. -/
theorem longPath_free_edges (d : ℕ) (hd : 0 < d) (ps : List Site) (hnd : ps.Nodup)
    (hchain : ps.IsChain cubicLattice.Adj) (hsk : ∀ p ∈ ps, EdgeSkeleton 0 (d + 2) p)
    (hlen : ps.length = 9 * (d + 2) - 10) :
    ∃ free : Finset CubeEdge, free.card = 3 ∧
      (∀ e ∈ free, ∀ e' ∈ free, e ≠ e' → NoCommonCorner e e') ∧
      (∀ p, p ∈ ps ↔ p ∈ cornerFinset 0 d ∨ ∃ e, e ∉ free ∧ p ∈ openEdgeFinset 0 d e) := by
  have hlen' : ps.length = 9 * d + 8 := by omega
  refine ⟨Finset.univ \ visitedEdges 0 d ps,
    maximal_skeleton_path_unused_edges 0 d hd ps hnd hchain hsk hlen', ?_, ?_⟩
  · intro e he e' he' hne
    exact noCommonCorner_of_matching _
      (maximal_unused_edges_matching 0 d hd ps hnd hchain hsk hlen') e e' he he' hne
  · intro p
    rw [mem_longPath_iff d hd ps hnd hchain hsk hlen p]
    simp [Finset.mem_sdiff]

/-- A simple skeleton path with `n - 2` vertices that avoids a longest path fills one of its free edges.
(Step 3 of the proof of Theorem 12, for the fillers.) -/
theorem filler_fills_free_edge (d : ℕ) (hd : 0 < d) (ps qs : List Site)
    (hpnd : ps.Nodup) (hpchain : ps.IsChain cubicLattice.Adj)
    (hpsk : ∀ p ∈ ps, EdgeSkeleton 0 (d + 2) p) (hplen : ps.length = 9 * (d + 2) - 10)
    (hqnd : qs.Nodup) (hqchain : qs.IsChain cubicLattice.Adj)
    (hqsk : ∀ p ∈ qs, EdgeSkeleton 0 (d + 2) p) (hqlen : qs.length = d)
    (hdisj : ∀ p ∈ qs, p ∉ ps) :
    ∃ e : CubeEdge, (∀ p, p ∈ qs ↔ p ∈ openEdgeFinset 0 d e) ∧
      ∀ p ∈ openEdgeFinset 0 d e, p ∉ ps := by
  have hdisj' : Disjoint qs.toFinset ps.toFinset := by
    rw [Finset.disjoint_left]
    intro p hq hp
    exact hdisj p (List.mem_toFinset.mp hq) (List.mem_toFinset.mp hp)
  obtain ⟨e, he, hqe⟩ := disjoint_edge_path_fills_unused_edge 0 d hd ps qs hpnd hpchain hpsk
    (by omega) hqnd hqchain hqsk hqlen hdisj'
  refine ⟨e, fun p => ?_, unvisited_edge_avoids d hd ps hpnd hpchain hpsk hplen he⟩
  rw [← List.mem_toFinset, hqe]

/-- A nonempty simple skeleton path that avoids a longest path lies in one edge, and that edge is
disjoint from the longest path. (Step 3, for the items and the separators.) -/
theorem path_in_free_edge (d : ℕ) (hd : 0 < d) (ps qs : List Site)
    (hpnd : ps.Nodup) (hpchain : ps.IsChain cubicLattice.Adj)
    (hpsk : ∀ p ∈ ps, EdgeSkeleton 0 (d + 2) p) (hplen : ps.length = 9 * (d + 2) - 10)
    (hqnd : qs.Nodup) (hqchain : qs.IsChain cubicLattice.Adj)
    (hqsk : ∀ p ∈ qs, EdgeSkeleton 0 (d + 2) p) (hqne : qs ≠ [])
    (hdisj : ∀ p ∈ qs, p ∉ ps) :
    ∃ e : CubeEdge, (∀ p ∈ qs, p ∈ openEdgeFinset 0 d e) ∧
      ∀ p ∈ openEdgeFinset 0 d e, p ∉ ps := by
  have hmem := mem_longPath_iff d hd ps hpnd hpchain hpsk hplen
  have hcorner : ∀ p ∈ qs, p ∉ cornerFinset 0 d := fun p hq hc =>
    hdisj p hq ((hmem p).mpr (Or.inl hc))
  obtain ⟨e, he⟩ := corner_free_skeleton_path_in_one_edge 0 d qs hqnd hqchain hqsk hcorner hqne
  have hqe : ∀ p ∈ qs, p ∈ openEdgeFinset 0 d e := fun p hp => he (List.mem_toFinset.mpr hp)
  refine ⟨e, hqe, unvisited_edge_avoids d hd ps hpnd hpchain hpsk hplen ?_⟩
  intro hv
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil qs hqne
  exact hdisj q hq ((hmem q).mpr (Or.inr ⟨e, hv, hqe q hq⟩))

end ProteinFolding.Shelf
