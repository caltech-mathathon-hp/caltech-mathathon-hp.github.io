import ProteinFolding.Cubic.Proofs.PackingGeometryEdges
import ProteinFolding.Cubic.Proofs.PackingGeometryPaths
import ProteinFolding.Common.GapLabels
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.ChainOfFn

/-! The maximal edge-prefix argument. Cube corners separate paths through
the twelve open edge interiors. This file connects the finite geometric
decomposition to the generic marked-path counting lemma. -/

namespace ProteinFolding.CubicPackingGeometry

open scoped BigOperators

noncomputable def edgeLabel (a : Site) (d : ℕ) (p : Site) : Option CubeEdge :=
  if h : ∃ q : CubeEdge × Fin d, openEdgePoint a d q.1 q.2 = p then
    some (Classical.choose h).1
  else none

theorem edgeLabel_openEdgePoint (a : Site) (d : ℕ) (e : CubeEdge) (r : Fin d) :
    edgeLabel a d (openEdgePoint a d e r) = some e := by
  have hex : ∃ q : CubeEdge × Fin d,
      openEdgePoint a d q.1 q.2 = openEdgePoint a d e r := ⟨(e, r), rfl⟩
  rw [edgeLabel, dif_pos hex]
  have hpoint := Classical.choose_spec hex
  have he : Classical.choose hex = (e, r) := openEdgePoint_injective a d hpoint
  exact congrArg (fun q : CubeEdge × Fin d => some q.1) he

theorem edgeLabel_eq_some_iff (a : Site) (d : ℕ) (p : Site) (e : CubeEdge) :
    edgeLabel a d p = some e ↔ ∃ r : Fin d, openEdgePoint a d e r = p := by
  constructor
  · intro h
    unfold edgeLabel at h
    split at h
    · rename_i hex
      have he := Option.some.inj h
      have hp := Classical.choose_spec hex
      refine ⟨(Classical.choose hex).2, ?_⟩
      simpa only [he] using hp
    · cases h
  · rintro ⟨r, rfl⟩
    exact edgeLabel_openEdgePoint a d e r

theorem edgeLabel_eq_none_iff (a : Site) (d : ℕ) (p : Site)
    (hp : EdgeSkeleton a (d + 2) p) : edgeLabel a d p = none ↔ p ∈ cornerFinset a d := by
  constructor
  · intro hn
    have hm := (mem_skeletonFinset a (d + 2) p).mpr hp
    rw [← skeleton_decomposition] at hm
    rcases Finset.mem_union.mp hm with hc | he
    · exact hc
    · obtain ⟨⟨e, r⟩, _, rfl⟩ := Finset.mem_image.mp he
      rw [edgeLabel_openEdgePoint] at hn
      cases hn
  · intro hc
    have hn : ¬ ∃ q : CubeEdge × Fin d, openEdgePoint a d q.1 q.2 = p := by
      rintro ⟨⟨e, r⟩, rfl⟩
      exact openEdgePoint_not_corner a d e r ((corner_iff_mem a d _).mpr hc)
    simp only [edgeLabel, dif_neg hn]

theorem edgeLabel_adjacent (a : Site) (d : ℕ) {p q : Site}
    (h : cubicLattice.Adj p q) : GapLabels.SameOrGap (edgeLabel a d p) (edgeLabel a d q) := by
  intro e f he hf
  obtain ⟨r, rfl⟩ := (edgeLabel_eq_some_iff a d p e).mp he
  obtain ⟨s, rfl⟩ := (edgeLabel_eq_some_iff a d q f).mp hf
  exact openEdgePoint_adjacent_key h

theorem edgeLabels_chain (a : Site) (d : ℕ) (ps : List Site)
    (hchain : ps.IsChain cubicLattice.Adj) :
    (ps.map (edgeLabel a d)).IsChain GapLabels.SameOrGap :=
  List.isChain_map_of_isChain (edgeLabel a d) (fun _ _ h => edgeLabel_adjacent a d h) hchain

def visitedCorners (a : Site) (d : ℕ) (ps : List Site) : Finset Site :=
  ps.toFinset.filter fun p => p ∈ cornerFinset a d

noncomputable def visitedEdges (a : Site) (d : ℕ) (ps : List Site) : Finset CubeEdge :=
  GapLabels.labels (ps.map (edgeLabel a d))

theorem visitedCorners_card_le (a : Site) (d : ℕ) (ps : List Site) :
    (visitedCorners a d ps).card ≤ 8 := by
  rw [← cornerFinset_card a d]
  apply Finset.card_le_card
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem gaps_eq_visitedCorners (a : Site) (d : ℕ) (ps : List Site) (hnd : ps.Nodup)
    (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) :
    GapLabels.gaps (ps.map (edgeLabel a d)) = (visitedCorners a d ps).card := by
  have he : GapLabels.gaps (ps.map (edgeLabel a d)) =
      (ps.filter fun p => decide (p ∈ cornerFinset a d)).length := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      have hp := hsk p (by simp)
      have hs : ∀ q ∈ ps, EdgeSkeleton a (d + 2) q := by intro q hq; exact hsk q (by simp [hq])
      have hbool : (edgeLabel a d p).isNone = decide (p ∈ cornerFinset a d) := by
        cases hl : edgeLabel a d p with
        | none =>
          have hc := (edgeLabel_eq_none_iff a d p hp).mp hl
          simp [hc]
        | some e =>
          have hc : p ∉ cornerFinset a d := by
            intro hc
            have hf := (edgeLabel_eq_none_iff a d p hp).mpr hc
            rw [hl] at hf
            cases hf
          simp [hc]
      simp only [GapLabels.gaps, List.map_cons, List.filter_cons, hbool]
      split_ifs <;> (try simp only [List.length_cons]) <;>
        rw [show (List.filter Option.isNone (ps.map (edgeLabel a d))).length =
          (ps.filter fun p => decide (p ∈ cornerFinset a d)).length from ih hnd.of_cons hs]
  rw [he]
  have hn := hnd.filter (fun p => decide (p ∈ cornerFinset a d))
  have hc := List.toFinset_card_of_nodup hn
  rw [List.toFinset_filter] at hc
  simpa only [visitedCorners, decide_eq_true_eq] using hc.symm

theorem visitedEdges_card_le (a : Site) (d : ℕ) (ps : List Site) (hnd : ps.Nodup)
    (hchain : ps.IsChain cubicLattice.Adj) (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) :
    (visitedEdges a d ps).card ≤ (visitedCorners a d ps).card + 1 := by
  have h := GapLabels.card_labels_le_gaps_add_one (ps.map (edgeLabel a d))
    (edgeLabels_chain a d ps hchain)
  rw [gaps_eq_visitedCorners a d ps hnd hsk] at h
  exact h

theorem path_subset_edge_cover (a : Site) (d : ℕ) (ps : List Site)
    (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) :
    ps.toFinset ⊆ visitedCorners a d ps ∪
      (visitedEdges a d ps).biUnion (openEdgeFinset a d) := by
  intro p hp
  have hpm : p ∈ ps := List.mem_toFinset.mp hp
  cases hl : edgeLabel a d p with
  | none =>
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hp, (edgeLabel_eq_none_iff a d p (hsk p hpm)).mp hl⟩
  | some e =>
    obtain ⟨r, hr⟩ := (edgeLabel_eq_some_iff a d p e).mp hl
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨e, ?_, Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hr⟩⟩
    simp only [visitedEdges, GapLabels.labels, List.mem_toFinset, List.mem_filterMap]
    exact ⟨some e, List.mem_map.mpr ⟨p, hpm, hl⟩, rfl⟩

theorem edge_cover_card_le (a : Site) (d : ℕ) (ps : List Site) :
    (visitedCorners a d ps ∪ (visitedEdges a d ps).biUnion (openEdgeFinset a d)).card ≤
      (visitedCorners a d ps).card + (visitedEdges a d ps).card * d := by
  have hu := Finset.card_union_le (visitedCorners a d ps)
    ((visitedEdges a d ps).biUnion (openEdgeFinset a d))
  have he := Finset.card_biUnion_le_card_mul (visitedEdges a d ps) (openEdgeFinset a d) d
    (fun e _ => (openEdgeFinset_card a d e).le)
  omega

theorem skeleton_path_length_bound (a : Site) (d : ℕ) (ps : List Site) (hnd : ps.Nodup)
    (hchain : ps.IsChain cubicLattice.Adj) (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) :
    ps.length ≤ (visitedCorners a d ps).card + ((visitedCorners a d ps).card + 1) * d := by
  have hsub := Finset.card_le_card (path_subset_edge_cover a d ps hsk)
  rw [List.toFinset_card_of_nodup hnd] at hsub
  have hcard := edge_cover_card_le a d ps
  have he := Nat.mul_le_mul_right d (visitedEdges_card_le a d ps hnd hchain hsk)
  omega

theorem skeleton_path_length_le (a : Site) (d : ℕ) (ps : List Site) (hnd : ps.Nodup)
    (hchain : ps.IsChain cubicLattice.Adj) (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) :
    ps.length ≤ 9 * d + 8 := by
  have hlen := skeleton_path_length_bound a d ps hnd hchain hsk
  have hc := visitedCorners_card_le a d ps
  have hm := Nat.mul_le_mul_right d (by omega : (visitedCorners a d ps).card + 1 ≤ 9)
  omega

/-- Equality in the prefix length bound forces all eight corners and exactly
nine distinct geometric open edges. -/
theorem maximal_skeleton_path_counts (a : Site) (d : ℕ) (hd : 0 < d) (ps : List Site)
    (hnd : ps.Nodup) (hchain : ps.IsChain cubicLattice.Adj)
    (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) (hlen : ps.length = 9 * d + 8) :
    (visitedCorners a d ps).card = 8 ∧ (visitedEdges a d ps).card = 9 := by
  have hsub := Finset.card_le_card (path_subset_edge_cover a d ps hsk)
  rw [List.toFinset_card_of_nodup hnd] at hsub
  have hcover := edge_cover_card_le a d ps
  have hc := visitedCorners_card_le a d ps
  have hk := visitedEdges_card_le a d ps hnd hchain hsk
  have hk9 : (visitedEdges a d ps).card ≤ 9 := by omega
  have hm := Nat.mul_le_mul_right d hk9
  have hc8 : (visitedCorners a d ps).card = 8 := by omega
  have heq : (visitedEdges a d ps).card * d = 9 * d := by omega
  exact ⟨hc8, Nat.eq_of_mul_eq_mul_right hd heq⟩

theorem maximal_skeleton_path_covers_corners (a : Site) (d : ℕ) (hd : 0 < d) (ps : List Site)
    (hnd : ps.Nodup) (hchain : ps.IsChain cubicLattice.Adj)
    (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) (hlen : ps.length = 9 * d + 8) :
    visitedCorners a d ps = cornerFinset a d := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · rw [cornerFinset_card, (maximal_skeleton_path_counts a d hd ps hnd hchain hsk hlen).1]

/-- A maximal prefix fills every vertex of each of its nine open edge
interiors. It cannot use partial edge interiors instead. -/
theorem maximal_skeleton_path_fills_edges (a : Site) (d : ℕ) (hd : 0 < d) (ps : List Site)
    (hnd : ps.Nodup) (hchain : ps.IsChain cubicLattice.Adj)
    (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) (hlen : ps.length = 9 * d + 8) :
    ps.toFinset = cornerFinset a d ∪
      (visitedEdges a d ps).biUnion (openEdgeFinset a d) := by
  have hc := maximal_skeleton_path_counts a d hd ps hnd hchain hsk hlen
  have hcorners := maximal_skeleton_path_covers_corners a d hd ps hnd hchain hsk hlen
  have hsub := path_subset_edge_cover a d ps hsk
  rw [hcorners] at hsub
  apply Finset.eq_of_subset_of_card_le hsub
  have hcover := edge_cover_card_le a d ps
  rw [hcorners, cornerFinset_card, hc.2] at hcover
  rw [List.toFinset_card_of_nodup hnd, hlen]
  omega

theorem maximal_skeleton_path_unused_edges (a : Site) (d : ℕ) (hd : 0 < d) (ps : List Site)
    (hnd : ps.Nodup) (hchain : ps.IsChain cubicLattice.Adj)
    (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) (hlen : ps.length = 9 * d + 8) :
    (Finset.univ \ visitedEdges a d ps).card = 3 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, cubeEdge_card,
    (maximal_skeleton_path_counts a d hd ps hnd hchain hsk hlen).2]

theorem maximal_skeleton_path_start (a : Site) (d : ℕ) (hd : 0 < d) (ps : List Site)
    (hnd : ps.Nodup) (hchain : ps.IsChain cubicLattice.Adj)
    (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) (hlen : ps.length = 9 * d + 8) :
    GapLabels.start (ps.map (edgeLabel a d)) = 1 := by
  have hc := maximal_skeleton_path_counts a d hd ps hnd hchain hsk hlen
  have h := GapLabels.card_labels_le (ps.map (edgeLabel a d)) (edgeLabels_chain a d ps hchain)
  rw [gaps_eq_visitedCorners a d ps hnd hsk, hc.1] at h
  change (visitedEdges a d ps).card ≤ 8 + GapLabels.start (ps.map (edgeLabel a d)) at h
  rw [hc.2] at h
  have hs := GapLabels.start_le_one (ps.map (edgeLabel a d))
  omega

theorem maximal_skeleton_path_head_not_corner (a : Site) (d : ℕ) (hd : 0 < d)
    (p : Site) (ps : List Site) (hnd : (p :: ps).Nodup)
    (hchain : (p :: ps).IsChain cubicLattice.Adj)
    (hsk : ∀ q ∈ p :: ps, EdgeSkeleton a (d + 2) q) (hlen : (p :: ps).length = 9 * d + 8) :
    p ∉ cornerFinset a d := by
  intro hc
  have hn := (edgeLabel_eq_none_iff a d p (hsk p (by simp))).mpr hc
  have hstart := maximal_skeleton_path_start a d hd (p :: ps) hnd hchain hsk hlen
  simp only [List.map_cons, hn, GapLabels.start] at hstart
  exact (by decide : (0 : ℕ) ≠ 1) hstart

def edgeHPathList (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ CubicPacking.edgeWord t ++ post).length) : List Site :=
  List.ofFn (edgeHPath pre post t f)

theorem edgeHPathList_nodup (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ CubicPacking.edgeWord t ++ post).length) :
    (edgeHPathList pre post t f).Nodup :=
  List.nodup_ofFn.mpr (edgeHPath_injective pre post t f)

theorem edgeHPathList_chain (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ CubicPacking.edgeWord t ++ post).length)
    (a : Site) (n : ℕ) (hpack : hydrophobicSites (pre ++ CubicPacking.edgeWord t ++ post) f = cube a n) :
    (edgeHPathList pre post t f).IsChain cubicLattice.Adj := by
  apply List.isChain_ofFn.mpr
  intro i hi
  exact edgeHPath_adjacent pre post t f a n hpack _ _ rfl

theorem edgeHPathList_skeleton (pre post : Sequence) (t : ℕ)
    (f : Fold cubicLattice (pre ++ CubicPacking.edgeWord t ++ post).length)
    (a : Site) (n : ℕ) (hpack : hydrophobicSites (pre ++ CubicPacking.edgeWord t ++ post) f = cube a n) :
    ∀ p ∈ edgeHPathList pre post t f, EdgeSkeleton a n p := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact edgeHPath_on_skeleton pre post t f a n hpack i

/-- The literal E-prefix in an arbitrary perfect fold uses all eight corners,
exactly nine full edge interiors, and leaves exactly three geometric edges. -/
theorem maximal_edgeWord_classification (pre post : Sequence) (d : ℕ) (hd : 0 < d)
    (f : Fold cubicLattice (pre ++ CubicPacking.edgeWord (9 * d + 8) ++ post).length)
    (a : Site)
    (hpack : hydrophobicSites (pre ++ CubicPacking.edgeWord (9 * d + 8) ++ post) f = cube a (d + 2)) :
    let ps := edgeHPathList pre post (9 * d + 8) f
    (visitedEdges a d ps).card = 9 ∧
      ps.toFinset = cornerFinset a d ∪
        (visitedEdges a d ps).biUnion (openEdgeFinset a d) ∧
      (Finset.univ \ visitedEdges a d ps).card = 3 := by
  let ps := edgeHPathList pre post (9 * d + 8) f
  have hn := edgeHPathList_nodup pre post (9 * d + 8) f
  have hc := edgeHPathList_chain pre post (9 * d + 8) f a (d + 2) hpack
  have hs := edgeHPathList_skeleton pre post (9 * d + 8) f a (d + 2) hpack
  have hl : ps.length = 9 * d + 8 := List.length_ofFn
  exact ⟨(maximal_skeleton_path_counts a d hd ps hn hc hs hl).2,
    maximal_skeleton_path_fills_edges a d hd ps hn hc hs hl,
    maximal_skeleton_path_unused_edges a d hd ps hn hc hs hl⟩

end ProteinFolding.CubicPackingGeometry
