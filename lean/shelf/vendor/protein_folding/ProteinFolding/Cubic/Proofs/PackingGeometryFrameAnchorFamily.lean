import ProteinFolding.Cubic.Proofs.PackingGeometryFrameAnchorVolume

/-! Discharging the finite-family rail and interval premises for an actual
perfect fold of the literal frame. In particular, J fixes the short-anchor
rail, while all long anchors tile the other rail at the prescribed starts. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

theorem railCoordinate_injective_on_edge (a : Site) (d : ℕ) (e : CubeEdge)
    (p r : Site) (hp : p ∈ openEdgeFinset a d e) (hr : r ∈ openEdgeFinset a d e)
    (he : railCoordinate a e.axis p = railCoordinate a e.axis r) : p = r := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr
  rw [← hi, ← hj, railCoordinate_openEdgePoint, railCoordinate_openEdgePoint] at he
  have hij : i = j := by apply Fin.ext; omega
  rw [← hi, ← hj, hij]

theorem two_element_finset_named {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.card = 2) (x : α) (hx : x ∈ s) :
    ∃ y, x ≠ y ∧ s = {x, y} := by
  obtain ⟨u, v, huv, hs⟩ := Finset.card_eq_two.mp hs
  rw [hs] at hx
  rcases Finset.mem_insert.mp hx with hxu | hxv
  · subst x
    exact ⟨v, huv, hs⟩
  · have hxv := Finset.mem_singleton.mp hxv
    subst x
    exact ⟨u, huv.symm, by simpa only [Finset.pair_comm] using hs⟩

theorem frameBlockKind_gap_iff {q : ℕ} (b : FrameBlock q) :
    frameBlockKind b = .gap ↔ b.2 = 3 := by
  rcases b with ⟨j, k⟩
  fin_cases k <;> simp [frameBlockKind]

theorem frameBlockKind_long_iff {q : ℕ} (b : FrameBlock q) :
    frameBlockKind b = .long ↔ b.2 = 1 := by
  rcases b with ⟨j, k⟩
  fin_cases k <;> simp [frameBlockKind]

/-- Geometric data obtained from an actual perfect fold. All fields refer to
the literal E blocks; neither rail assignment nor interval coverage is assumed. -/
structure FrameAnchorFamily (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site) where
  railEdge : Fin 2 → CubeEdge
  railEdge_injective : Function.Injective railEdge
  rail : FrameBlock q → Fin 2
  start : FrameBlock q → ℕ
  on_edge : ∀ b i, (frameBlockOccurrence q Q items b).path f i ∈
    openEdgeFinset a (depth q Q) (railEdge (rail b))
  coordinate_image : ∀ b,
    Finset.univ.image (fun i => railCoordinate a (railEdge (rail b)).axis
      ((frameBlockOccurrence q Q items b).path f i)) =
      anchorSites Q frameBlockKind start b
  bound : ∀ b, 1 ≤ start b ∧ start b + anchorLength Q (frameBlockKind b) ≤ depth q Q + 1
  gap_rail : ∀ b, frameBlockKind b = .gap → rail b = 0
  disjoint : ∀ b c, b ≠ c → rail b = rail c →
    Disjoint (anchorSites Q frameBlockKind start b) (anchorSites Q frameBlockKind start c)
  fill : ∀ r, (railBlocks Finset.univ rail r).biUnion (anchorSites Q frameBlockKind start) =
    Finset.Ico 1 (depth q Q + 1)
  matching : ∀ bits, (incidentEdges bits ∩ Finset.univ.image railEdge).card ≤ 1

theorem frame_anchor_family_exists (q Q : ℕ) (items : List ℕ) (hq : 2 ≤ q) (hQ : q < Q)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    Nonempty (FrameAnchorFamily q Q items f a) := by
  have hq0 : 0 < q := by omega
  have hQ0 : 0 < Q := by omega
  obtain ⟨second, hsecond, hcard, hmatching⟩ := frame_two_remaining_rails q Q items hq0 f a hpack
  let R := (Finset.univ \ visitedEdges a (depth q Q) (initialEdgePath q Q items f)) \ {second}
  have hex := fun b => frameBlock_on_remaining_rail q Q items hq0 hQ0 f a hpack second hsecond b
  let edge : FrameBlock q → CubeEdge := fun b => Classical.choose (hex b)
  have hemem : ∀ b, edge b ∈ R := fun b => (Classical.choose_spec (hex b)).1
  have hepath : ∀ b i, (frameBlockOccurrence q Q items b).path f i ∈
      openEdgeFinset a (depth q Q) (edge b) := fun b => (Classical.choose_spec (hex b)).2
  let zero : Fin q := ⟨0, by omega⟩
  let e₀ := edge (zero, 3)
  obtain ⟨e₁, hene, hR⟩ := two_element_finset_named R hcard e₀ (hemem (zero, 3))
  let re : Fin 2 → CubeEdge := fun r => if r = 0 then e₀ else e₁
  have hrein : Function.Injective re := by
    intro r s he
    fin_cases r <;> fin_cases s <;> simp_all [re]
  let rail : FrameBlock q → Fin 2 := fun b => if edge b = e₀ then 0 else 1
  have heq : ∀ b, re (rail b) = edge b := by
    intro b
    have hm := hemem b
    rw [hR] at hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · simp [rail, re, hm]
    · have hm := Finset.mem_singleton.mp hm
      simp [rail, re, hm, hene.symm]
  have honto : ∀ r, re r ∈ R := by intro r; fin_cases r <;> simp [re, hR]
  have hstart : ∀ b, ∃ s, 1 ≤ s ∧ s + anchorLength Q (frameBlockKind b) ≤ depth q Q + 1 ∧
      Finset.univ.image (fun i => railCoordinate a (edge b).axis
        ((frameBlockOccurrence q Q items b).path f i)) = Finset.Ico s (s + anchorLength Q (frameBlockKind b)) := by
    intro b
    apply openEdge_path_coordinate_image a (depth q Q) _ (frameBlock_length_pos q Q hQ0 b) (edge b)
      ((frameBlockOccurrence q Q items b).path f)
      ((frameBlockOccurrence q Q items b).path_injective f)
    · intro i j hij
      exact (frameBlockOccurrence q Q items b).path_adjacent f a (side q Q) hpack i j hij
    · exact hepath b
  let start : FrameBlock q → ℕ := fun b => Classical.choose (hstart b)
  have hbounds : ∀ b, 1 ≤ start b ∧ start b + anchorLength Q (frameBlockKind b) ≤ depth q Q + 1 :=
    fun b => ⟨(Classical.choose_spec (hstart b)).1, (Classical.choose_spec (hstart b)).2.1⟩
  have himage : ∀ b, Finset.univ.image (fun i => railCoordinate a (edge b).axis
      ((frameBlockOccurrence q Q items b).path f i)) = anchorSites Q frameBlockKind start b :=
    fun b => (Classical.choose_spec (hstart b)).2.2
  have hgaps : ∀ b, frameBlockKind b = .gap → rail b = 0 := by
    intro b hb
    have hb3 := (frameBlockKind_gap_iff b).mp hb
    have he : edge b = e₀ := by
      have h := frame_gap_blocks_one_edge q Q items hq hQ f a R hmatching edge hemem hepath b.1
      exact (congrArg edge (show b = (b.1, 3) from Prod.ext rfl hb3)).trans h
    simp [rail, he]
  have hdisjoint : ∀ b c, b ≠ c → rail b = rail c →
      Disjoint (anchorSites Q frameBlockKind start b) (anchorSites Q frameBlockKind start c) := by
    intro b c hbc hrail
    have he : edge b = edge c := (heq b).symm.trans ((congrArg re hrail).trans (heq c))
    rw [Finset.disjoint_left]
    intro y hyb hyc
    rw [← himage b] at hyb
    rw [← himage c] at hyc
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hyb
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hyc
    have hp : (frameBlockOccurrence q Q items b).path f i =
        (frameBlockOccurrence q Q items c).path f j := by
      apply railCoordinate_injective_on_edge a (depth q Q) (edge b) _ _ (hepath b i)
        (by rw [he]; exact hepath c j)
      rw [hi, he, hj]
    exact Finset.disjoint_left.mp (frameBlock_sites_disjoint q Q items f b c hbc)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hp.symm⟩)
  have hsaturation := frameBlock_sites_fill_rails q Q items f a R hcard edge hemem hepath
  have hfill : ∀ r, (railBlocks Finset.univ rail r).biUnion (anchorSites Q frameBlockKind start) =
      Finset.Ico 1 (depth q Q + 1) := by
    intro r
    ext y
    constructor
    · intro hy
      obtain ⟨b, _, hy⟩ := Finset.mem_biUnion.mp hy
      have hb := hbounds b
      exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hy).1.trans' hb.1,
        lt_of_lt_of_le (Finset.mem_Ico.mp hy).2 hb.2⟩
    · intro hy
      obtain ⟨hy0, hy1⟩ := Finset.mem_Ico.mp hy
      let k : Fin (depth q Q) := ⟨y - 1, by omega⟩
      let p := openEdgePoint a (depth q Q) (re r) k
      have hp : p ∈ R.biUnion (openEdgeFinset a (depth q Q)) :=
        Finset.mem_biUnion.mpr ⟨re r, honto r, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩
      rw [← hsaturation] at hp
      obtain ⟨b, _, hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
      have he : edge b = re r := by
        by_contra hne
        exact Finset.disjoint_left.mp (openEdgeFinsets_disjoint a (depth q Q) (edge b) (re r) hne)
          (hepath b i) (by rw [hi]; exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
      have hr : rail b = r := hrein ((heq b).trans he)
      refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, ?_⟩
      rw [← himage b]
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
      rw [hi, he]
      change railCoordinate a (re r).axis (openEdgePoint a (depth q Q) (re r) k) = y
      rw [railCoordinate_openEdgePoint]
      change y - 1 + 1 = y
      omega
  refine ⟨⟨re, hrein, rail, start, ?_, ?_, hbounds, hgaps, hdisjoint, hfill, ?_⟩⟩
  · intro b i
    rw [heq]
    exact hepath b i
  · intro b
    rw [heq]
    exact himage b
  · have he : Finset.univ.image re = R := by
      have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
      rw [hu]
      simp [re, hR]
    simpa only [he] using hmatching

theorem FrameAnchorFamily.rails_no_common_corner {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) : NoCommonCorner (F.railEdge 0) (F.railEdge 1) := by
  apply noCommonCorner_of_matching (Finset.univ.image F.railEdge) F.matching
    (F.railEdge 0) (F.railEdge 1)
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩)
  intro he
  exact (by decide : (0 : Fin 2) ≠ 1) (F.railEdge_injective he)

theorem FrameAnchorFamily.long_rail {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hQ : 0 < Q) (hq : q < Q) :
    ∀ b, F.rail b = 1 ↔ frameBlockKind b = .long := by
  intro b
  exact anchor_family_rail_forcing q Q hQ hq Finset.univ frameBlockKind F.rail F.start
    (frameBlock_long_count q) (fun b _ => F.gap_rail b)
    (fun b _ c _ => F.disjoint b c) F.fill b (Finset.mem_univ _)

theorem FrameAnchorFamily.long_starts {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hQ : 0 < Q) (hq : q < Q) :
    (Finset.univ.filter fun b : FrameBlock q => frameBlockKind b = .long).image F.start =
      (Finset.range q).image (fun j => j * beta Q + 1) := by
  exact anchor_family_long_starts q Q hQ hq Finset.univ frameBlockKind F.rail F.start
    (frameBlock_long_count q) (fun b _ => F.gap_rail b)
    (fun b _ c _ => F.disjoint b c) F.fill (fun b _ => F.bound b)

theorem FrameAnchorFamily.long_starts_by_wall {q Q : ℕ} {items : List ℕ}
    {f : Fold cubicLattice (frameWord q Q items).length} {a : Site}
    (F : FrameAnchorFamily q Q items f a) (hQ : 0 < Q) (hq : q < Q) :
    Finset.univ.image (fun j : Fin q => F.start (j, 1)) =
      (Finset.range q).image (fun j => j * beta Q + 1) := by
  rw [← F.long_starts hQ hq]
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter,
    frameBlockKind_long_iff]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨(j, 1), rfl, hj⟩
  · rintro ⟨b, hb, hy⟩
    refine ⟨b.1, ?_⟩
    have he : b = (b.1, 1) := Prod.ext rfl hb
    simpa only [← he] using hy

/-- The actual long E_β blocks of every perfect frame fold tile one common
rail, with starts exactly 1, β+1, ..., (q−1)β+1, in an arbitrary chain order.
This is a consequence of the perfect fold alone, not a supplied rail layout. -/
theorem frame_long_anchor_geometry (q Q : ℕ) (items : List ℕ) (hq : 2 ≤ q) (hQ : q < Q)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    ∃ (e : CubeEdge) (start : Fin q → ℕ),
      Finset.univ.image start = (Finset.range q).image (fun j => j * beta Q + 1) ∧
      ∀ j : Fin q,
        (∀ i, (frameBlockOccurrence q Q items (j, 1)).path f i ∈
          openEdgeFinset a (depth q Q) e) ∧
        Finset.univ.image (fun i => railCoordinate a e.axis
          ((frameBlockOccurrence q Q items (j, 1)).path f i)) =
            Finset.Ico (start j) (start j + beta Q) := by
  obtain ⟨F⟩ := frame_anchor_family_exists q Q items hq hQ f a hpack
  have hQ0 : 0 < Q := by omega
  refine ⟨F.railEdge 1, fun j => F.start (j, 1), F.long_starts_by_wall hQ0 hQ, ?_⟩
  intro j
  have hr : F.rail (j, 1) = 1 := (F.long_rail hQ0 hQ (j, 1)).mpr (by simp [frameBlockKind])
  constructor
  · intro i
    simpa only [hr] using F.on_edge (j, 1) i
  · simpa [hr, anchorSites, frameBlockKind, anchorLength] using F.coordinate_image (j, 1)

end ProteinFolding.CubicPackingGeometry
