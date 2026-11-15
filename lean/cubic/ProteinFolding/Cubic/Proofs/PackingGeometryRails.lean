import ProteinFolding.Cubic.Proofs.PackingGeometryMatching

/-! A further E_d path, disjoint from the maximal edge prefix, fills exactly
one of the three unused open edges. The two remaining rails are nonincident. -/

namespace ProteinFolding.CubicPackingGeometry

theorem corner_free_skeleton_path_one_edge (a : Site) (d : ℕ) (hd : 0 < d)
    (qs : List Site) (hnd : qs.Nodup) (hchain : qs.IsChain cubicLattice.Adj)
    (hsk : ∀ p ∈ qs, EdgeSkeleton a (d + 2) p)
    (hcorner : ∀ p ∈ qs, p ∉ cornerFinset a d) (hlen : qs.length = d) :
    ∃ e, qs.toFinset = openEdgeFinset a d e := by
  have hc : visitedCorners a d qs = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpq, hpc⟩ := Finset.mem_filter.mp hp
    exact hcorner p (List.mem_toFinset.mp hpq) hpc
  have hk := visitedEdges_card_le a d qs hnd hchain hsk
  rw [hc, Finset.card_empty, Nat.zero_add] at hk
  have hnonempty : (visitedEdges a d qs).Nonempty := by
    have hq : qs ≠ [] := by intro he; simp only [he, List.length_nil] at hlen; omega
    obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil hq
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
  simp only [Finset.empty_union, Finset.singleton_biUnion] at hsub
  apply Finset.eq_of_subset_of_card_le hsub
  rw [openEdgeFinset_card, List.toFinset_card_of_nodup hnd, hlen]

theorem disjoint_edge_path_fills_unused_edge (a : Site) (d : ℕ) (hd : 0 < d)
    (ps qs : List Site) (hpnd : ps.Nodup) (hpchain : ps.IsChain cubicLattice.Adj)
    (hpsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) (hplen : ps.length = 9 * d + 8)
    (hqnd : qs.Nodup) (hqchain : qs.IsChain cubicLattice.Adj)
    (hqsk : ∀ p ∈ qs, EdgeSkeleton a (d + 2) p) (hqlen : qs.length = d)
    (hdisj : Disjoint qs.toFinset ps.toFinset) :
    ∃ e, e ∉ visitedEdges a d ps ∧ qs.toFinset = openEdgeFinset a d e := by
  have hcorner : ∀ p ∈ qs, p ∉ cornerFinset a d := by
    intro p hp hc
    have hm : p ∈ visitedCorners a d ps := by
      rw [maximal_skeleton_path_covers_corners a d hd ps hpnd hpchain hpsk hplen]
      exact hc
    exact Finset.disjoint_left.mp hdisj (List.mem_toFinset.mpr hp) (Finset.mem_filter.mp hm).1
  obtain ⟨e, he⟩ := corner_free_skeleton_path_one_edge a d hd qs hqnd hqchain hqsk hcorner hqlen
  refine ⟨e, ?_, he⟩
  intro hev
  let r : Fin d := ⟨0, hd⟩
  have hq : openEdgePoint a d e r ∈ qs.toFinset := by
    rw [he]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  have hp : openEdgePoint a d e r ∈ ps.toFinset := by
    rw [maximal_skeleton_path_fills_edges a d hd ps hpnd hpchain hpsk hplen]
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨e, hev, Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩⟩
  exact Finset.disjoint_left.mp hdisj hq hp

theorem two_remaining_rails (a : Site) (d : ℕ) (hd : 0 < d)
    (ps qs : List Site) (hpnd : ps.Nodup) (hpchain : ps.IsChain cubicLattice.Adj)
    (hpsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) (hplen : ps.length = 9 * d + 8)
    (hqnd : qs.Nodup) (hqchain : qs.IsChain cubicLattice.Adj)
    (hqsk : ∀ p ∈ qs, EdgeSkeleton a (d + 2) p) (hqlen : qs.length = d)
    (hdisj : Disjoint qs.toFinset ps.toFinset) :
    ∃ e, qs.toFinset = openEdgeFinset a d e ∧
      ((Finset.univ \ visitedEdges a d ps) \ {e}).card = 2 ∧
      ∀ bits, (incidentEdges bits ∩ ((Finset.univ \ visitedEdges a d ps) \ {e})).card ≤ 1 := by
  obtain ⟨e, he, hqe⟩ := disjoint_edge_path_fills_unused_edge a d hd ps qs hpnd hpchain
    hpsk hplen hqnd hqchain hqsk hqlen hdisj
  refine ⟨e, hqe, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset (by simpa using he : {e} ⊆ Finset.univ \ visitedEdges a d ps),
      maximal_skeleton_path_unused_edges a d hd ps hpnd hpchain hpsk hplen, Finset.card_singleton]
  · intro bits
    apply (Finset.card_le_card ?_).trans
      (maximal_unused_edges_matching a d hd ps hpnd hpchain hpsk hplen bits)
    intro x hx
    obtain ⟨hi, he⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨hi, (Finset.mem_sdiff.mp he).1⟩

end ProteinFolding.CubicPackingGeometry
