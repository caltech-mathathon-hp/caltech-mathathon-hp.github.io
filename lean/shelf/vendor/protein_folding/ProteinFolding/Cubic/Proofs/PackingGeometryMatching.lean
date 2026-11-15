import ProteinFolding.Cubic.Proofs.PackingGeometryPrefix

/-! The three cube edges not used by a maximal skeleton prefix have no
common endpoints. Each corner is internal to the prefix and uses two of its
three incident geometric edges. -/

namespace ProteinFolding.CubicPackingGeometry

def cornerEdge (bits : Fin 3 → Fin 2) : Fin 3 → CubeEdge
  | 0 => ⟨0, bits 1, bits 2⟩
  | 1 => ⟨1, bits 0, bits 2⟩
  | 2 => ⟨2, bits 0, bits 1⟩

theorem cornerEdge_axis (bits : Fin 3 → Fin 2) (axis : Fin 3) :
    (cornerEdge bits axis).axis = axis := by fin_cases axis <;> rfl

theorem cornerEdge_injective (bits : Fin 3 → Fin 2) : Function.Injective (cornerEdge bits) := by
  intro i j h
  simpa only [cornerEdge_axis] using congrArg CubeEdge.axis h

def incidentEdges (bits : Fin 3 → Fin 2) : Finset CubeEdge := Finset.univ.image (cornerEdge bits)

theorem incidentEdges_card (bits : Fin 3 → Fin 2) : (incidentEdges bits).card = 3 := by
  rw [incidentEdges, Finset.card_image_of_injective _ (cornerEdge_injective bits)]
  simp

theorem openEdge_adjacent_corner_incident (a : Site) (d : ℕ) (hd : 0 < d)
    (bits : Fin 3 → Fin 2) (e : CubeEdge) (r : Fin d)
    (h : cubicLattice.Adj (cornerPoint a d bits) (openEdgePoint a d e r)) :
    e ∈ incidentEdges bits := by
  have h0 := adjacent_coordinate_bounds h 0
  have h1 := adjacent_coordinate_bounds h 1
  have h2 := adjacent_coordinate_bounds h 2
  obtain ⟨axis, b, c⟩ := e
  have he : (⟨axis, b, c⟩ : CubeEdge) = cornerEdge bits axis := by
    fin_cases axis
    · have hb := endValue_close_injective (a 1) d (bits 1) b hd
        (by simpa [cornerPoint, openEdgePoint] using h1)
      have hc := endValue_close_injective (a 2) d (bits 2) c hd
        (by simpa [cornerPoint, openEdgePoint] using h2)
      subst b; subst c; rfl
    · have hb := endValue_close_injective (a 0) d (bits 0) b hd
        (by simpa [cornerPoint, openEdgePoint] using h0)
      have hc := endValue_close_injective (a 2) d (bits 2) c hd
        (by simpa [cornerPoint, openEdgePoint] using h2)
      subst b; subst c; rfl
    · have hb := endValue_close_injective (a 0) d (bits 0) b hd
        (by simpa [cornerPoint, openEdgePoint] using h0)
      have hc := endValue_close_injective (a 1) d (bits 1) c hd
        (by simpa [cornerPoint, openEdgePoint] using h1)
      subst b; subst c; rfl
  exact Finset.mem_image.mpr ⟨axis, Finset.mem_univ _, he.symm⟩

theorem corners_not_adjacent (a : Site) (d : ℕ) (hd : 0 < d)
    (bits bits' : Fin 3 → Fin 2) :
    ¬ cubicLattice.Adj (cornerPoint a d bits) (cornerPoint a d bits') := by
  intro h
  have he : bits = bits' := by
    funext k
    exact endValue_close_injective (a k) d (bits k) (bits' k) hd
      (adjacent_coordinate_bounds h k)
  subst bits'
  exact cubicLattice.loopless _ h

theorem corner_neighbour_not_corner (a : Site) (d : ℕ) (hd : 0 < d)
    (bits : Fin 3 → Fin 2) (p : Site)
    (h : cubicLattice.Adj (cornerPoint a d bits) p) : p ∉ cornerFinset a d := by
  intro hp
  obtain ⟨bits', _, rfl⟩ := Finset.mem_image.mp hp
  exact corners_not_adjacent a d hd bits bits' h

theorem openEdge_adjacent_corner_unique (a : Site) (d : ℕ)
    (bits : Fin 3 → Fin 2) (e : CubeEdge) (r s : Fin d)
    (hr : cubicLattice.Adj (cornerPoint a d bits) (openEdgePoint a d e r))
    (hs : cubicLattice.Adj (cornerPoint a d bits) (openEdgePoint a d e s)) : r = s := by
  have h1 := adjacent_coordinate_bounds hr e.axis
  have h2 := adjacent_coordinate_bounds hs e.axis
  rw [openEdgePoint_axis] at h1 h2
  change endValue (a e.axis) d (bits e.axis) - 1 ≤ a e.axis + 1 + (r.val : ℤ) ∧
    a e.axis + 1 + (r.val : ℤ) ≤ endValue (a e.axis) d (bits e.axis) + 1 at h1
  change endValue (a e.axis) d (bits e.axis) - 1 ≤ a e.axis + 1 + (s.val : ℤ) ∧
    a e.axis + 1 + (s.val : ℤ) ≤ endValue (a e.axis) d (bits e.axis) + 1 at h2
  generalize hb : bits e.axis = b at h1 h2
  apply Fin.ext
  have hr' := r.isLt
  have hs' := s.isLt
  fin_cases b <;> simp only [endValue, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul] at h1 h2 <;> omega

theorem maximal_corner_two_neighbours (a : Site) (d : ℕ) (hd : 0 < d)
    (ps : List Site) (hnd : ps.Nodup) (hchain : ps.IsChain cubicLattice.Adj)
    (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) (hlen : ps.length = 9 * d + 8)
    (bits : Fin 3 → Fin 2) (hmem : cornerPoint a d bits ∈ ps) :
    ∃ u v, u ∈ ps ∧ v ∈ ps ∧ u ≠ v ∧
      cubicLattice.Adj (cornerPoint a d bits) u ∧ cubicLattice.Adj (cornerPoint a d bits) v := by
  let c := cornerPoint a d bits
  have hc : c ∈ cornerFinset a d := Finset.mem_image.mpr ⟨bits, Finset.mem_univ _, rfl⟩
  obtain ⟨left, right, rfl⟩ := List.append_of_mem hmem
  have hleft : left ≠ [] := by
    intro he
    subst left
    exact maximal_skeleton_path_head_not_corner a d hd c right hnd hchain hsk hlen hc
  have hright : right ≠ [] := by
    intro he
    subst right
    have hn : (c :: left.reverse).Nodup := by
      simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append] using List.nodup_reverse.mpr hnd
    have hch : (c :: left.reverse).IsChain cubicLattice.Adj := by
      have hr := List.isChain_reverse.mpr (hchain.imp (fun _ _ h => h.symm))
      simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append] using hr
    have hsk' : ∀ p ∈ c :: left.reverse, EdgeSkeleton a (d + 2) p := by
      intro p hp
      apply hsk p
      simpa only [List.mem_cons, List.mem_reverse, List.mem_append, List.mem_singleton,
        List.mem_nil_iff, or_false, false_or, or_comm, c] using hp
    have hl : (c :: left.reverse).length = 9 * d + 8 := by
      simpa only [List.length_append, List.length_cons, List.length_nil, List.length_reverse,
        Nat.add_comm] using hlen
    exact maximal_skeleton_path_head_not_corner a d hd c left.reverse hn hch hsk' hl hc
  obtain ⟨v, right, rfl⟩ := List.exists_cons_of_ne_nil hright
  have hrev : left.reverse ≠ [] := by simpa using hleft
  obtain ⟨u, left', he⟩ := List.exists_cons_of_ne_nil hrev
  have hl : left = left'.reverse ++ [u] := by
    have hr := congrArg List.reverse he
    simpa only [List.reverse_reverse, List.reverse_cons] using hr
  simp only [hl, List.append_assoc, List.singleton_append] at hnd hchain hsk hlen ⊢
  have hn : (u :: c :: v :: right).Nodup := List.Nodup.of_append_right hnd
  have hch : (u :: c :: v :: right).IsChain cubicLattice.Adj := hchain.right_of_append
  have huv : u ≠ v := by
    intro he
    exact (List.nodup_cons.mp hn).1 (by simp [he])
  obtain ⟨huc, hcv⟩ := List.isChain_cons_cons.mp hch
  refine ⟨u, v, by simp, by simp, huv, huc.symm, ?_⟩
  exact (List.isChain_cons_cons.mp hcv).1

theorem corner_neighbour_edge (a : Site) (d : ℕ) (hd : 0 < d)
    (bits : Fin 3 → Fin 2) (p : Site) (hsk : EdgeSkeleton a (d + 2) p)
    (hadj : cubicLattice.Adj (cornerPoint a d bits) p) :
    ∃ e r, edgeLabel a d p = some e ∧ openEdgePoint a d e r = p ∧ e ∈ incidentEdges bits := by
  cases hl : edgeLabel a d p with
  | none =>
    exact False.elim (corner_neighbour_not_corner a d hd bits p hadj
      ((edgeLabel_eq_none_iff a d p hsk).mp hl))
  | some e =>
    obtain ⟨r, hr⟩ := (edgeLabel_eq_some_iff a d p e).mp hl
    refine ⟨e, r, rfl, hr, ?_⟩
    apply openEdge_adjacent_corner_incident a d hd bits e r
    simpa only [hr] using hadj

theorem mem_visitedEdges_of_label (a : Site) (d : ℕ) (ps : List Site) (p : Site) (e : CubeEdge)
    (hp : p ∈ ps) (he : edgeLabel a d p = some e) : e ∈ visitedEdges a d ps := by
  simp only [visitedEdges, GapLabels.labels, List.mem_toFinset, List.mem_filterMap]
  exact ⟨some e, List.mem_map.mpr ⟨p, hp, he⟩, rfl⟩

theorem maximal_corner_two_visited_edges (a : Site) (d : ℕ) (hd : 0 < d)
    (ps : List Site) (hnd : ps.Nodup) (hchain : ps.IsChain cubicLattice.Adj)
    (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) (hlen : ps.length = 9 * d + 8)
    (bits : Fin 3 → Fin 2) :
    ∃ e f, e ≠ f ∧ e ∈ incidentEdges bits ∧ f ∈ incidentEdges bits ∧
      e ∈ visitedEdges a d ps ∧ f ∈ visitedEdges a d ps := by
  have hc : cornerPoint a d bits ∈ visitedCorners a d ps := by
    rw [maximal_skeleton_path_covers_corners a d hd ps hnd hchain hsk hlen]
    exact Finset.mem_image.mpr ⟨bits, Finset.mem_univ _, rfl⟩
  have hcm : cornerPoint a d bits ∈ ps := List.mem_toFinset.mp (Finset.mem_filter.mp hc).1
  obtain ⟨u, v, hu, hv, huv, hau, hav⟩ :=
    maximal_corner_two_neighbours a d hd ps hnd hchain hsk hlen bits hcm
  obtain ⟨e, r, her, hru, hei⟩ := corner_neighbour_edge a d hd bits u (hsk u hu) hau
  obtain ⟨f, s, hfs, hsv, hfi⟩ := corner_neighbour_edge a d hd bits v (hsk v hv) hav
  have hne : e ≠ f := by
    intro hef
    subst f
    have h1 : cubicLattice.Adj (cornerPoint a d bits) (openEdgePoint a d e r) := by
      simpa only [hru] using hau
    have h2 : cubicLattice.Adj (cornerPoint a d bits) (openEdgePoint a d e s) := by
      simpa only [hsv] using hav
    have hrs := openEdge_adjacent_corner_unique a d bits e r s h1 h2
    subst s
    exact huv (hru.symm.trans hsv)
  exact ⟨e, f, hne, hei, hfi, mem_visitedEdges_of_label a d ps u e hu her,
    mem_visitedEdges_of_label a d ps v f hv hfs⟩

/-- No cube corner is incident to two of the three unused edges. Thus the
unused geometric edges form a matching on the cube's eight corners. -/
theorem maximal_unused_edges_matching (a : Site) (d : ℕ) (hd : 0 < d)
    (ps : List Site) (hnd : ps.Nodup) (hchain : ps.IsChain cubicLattice.Adj)
    (hsk : ∀ p ∈ ps, EdgeSkeleton a (d + 2) p) (hlen : ps.length = 9 * d + 8)
    (bits : Fin 3 → Fin 2) :
    (incidentEdges bits ∩ (Finset.univ \ visitedEdges a d ps)).card ≤ 1 := by
  obtain ⟨e, f, hef, hei, hfi, hev, hfv⟩ :=
    maximal_corner_two_visited_edges a d hd ps hnd hchain hsk hlen bits
  have hp : {e, f} ⊆ incidentEdges bits := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hei
    · exact hfi
  have hc : (incidentEdges bits \ {e, f}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hp, incidentEdges_card, Finset.card_pair hef]
  rw [← hc]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxi, hxv⟩ := Finset.mem_inter.mp hx
  have hxnv := (Finset.mem_sdiff.mp hxv).2
  apply Finset.mem_sdiff.mpr
  refine ⟨hxi, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨fun hxe => hxnv (hxe.symm ▸ hev), fun hxf => hxnv (hxf.symm ▸ hfv)⟩

theorem maximal_edgeWord_unused_matching (pre post : Sequence) (d : ℕ) (hd : 0 < d)
    (f : Fold cubicLattice (pre ++ CubicPacking.edgeWord (9 * d + 8) ++ post).length)
    (a : Site)
    (hpack : hydrophobicSites (pre ++ CubicPacking.edgeWord (9 * d + 8) ++ post) f = cube a (d + 2))
    (bits : Fin 3 → Fin 2) :
    (incidentEdges bits ∩ (Finset.univ \ visitedEdges a d
      (edgeHPathList pre post (9 * d + 8) f))).card ≤ 1 := by
  apply maximal_unused_edges_matching a d hd
    (edgeHPathList pre post (9 * d + 8) f)
  · exact edgeHPathList_nodup pre post (9 * d + 8) f
  · exact edgeHPathList_chain pre post (9 * d + 8) f a (d + 2) hpack
  · exact edgeHPathList_skeleton pre post (9 * d + 8) f a (d + 2) hpack
  · exact List.length_ofFn

end ProteinFolding.CubicPackingGeometry
