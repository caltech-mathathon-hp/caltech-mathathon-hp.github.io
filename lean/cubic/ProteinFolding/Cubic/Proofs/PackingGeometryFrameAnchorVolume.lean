import ProteinFolding.Cubic.Proofs.PackingGeometryBlockRails

/-! Exact occupation of the two remaining rails by the literal frame anchors.
The capacity argument counts actual, pairwise distinct fold sites. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking
open scoped BigOperators

theorem frameBlock_total_length (q Q : ℕ) :
    (∑ b : FrameBlock q, anchorLength Q (frameBlockKind b)) = 2 * depth q Q := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ j : Fin q,
      (∑ k : Fin 4, anchorLength Q (frameBlockKind (j, k))) = 2 * alpha Q + beta Q + 2 := by
    intro j
    simp [Fin.sum_univ_succ, frameBlockKind, anchorLength]
    omega
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  dsimp [alpha, beta, depth]
  ring

theorem frameBlock_long_count (q : ℕ) :
    (Finset.univ.filter fun b : FrameBlock q => frameBlockKind b = .long).card = q := by
  have he : (Finset.univ.filter fun b : FrameBlock q => frameBlockKind b = .long) =
      Finset.univ.image (fun j : Fin q => (j, (1 : Fin 4))) := by
    ext b
    rcases b with ⟨j, k⟩
    fin_cases k <;> simp [frameBlockKind]
  rw [he, Finset.card_image_of_injective _ (by intro i j h; exact (Prod.mk.inj h).1)]
  simp

theorem frameBlock_sites_union_card (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) :
    (Finset.univ.biUnion fun b : FrameBlock q => (frameBlockOccurrence q Q items b).sites f).card =
      2 * depth q Q := by
  rw [Finset.card_biUnion]
  · simp only [EdgeOccurrence.sites_card]
    exact frameBlock_total_length q Q
  · intro b _ c _ hbc
    exact frameBlock_sites_disjoint q Q items f b c hbc

theorem openEdgeFinsets_disjoint (a : Site) (d : ℕ) (e g : CubeEdge) (heg : e ≠ g) :
    Disjoint (openEdgeFinset a d e) (openEdgeFinset a d g) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hp
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hq
  have he : (e, r) = (g, s) := openEdgePoint_injective a d (hr.trans hs.symm)
  exact heg (congrArg Prod.fst he)

theorem openEdgeFinsets_union_card (a : Site) (d : ℕ) (rails : Finset CubeEdge) :
    (rails.biUnion (openEdgeFinset a d)).card = rails.card * d := by
  rw [Finset.card_biUnion]
  · simp only [openEdgeFinset_card, Finset.sum_const, smul_eq_mul]
  · intro e _ g _ heg
    exact openEdgeFinsets_disjoint a d e g heg

theorem frameBlock_sites_fill_rails (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (rails : Finset CubeEdge) (hcard : rails.card = 2)
    (edge : FrameBlock q → CubeEdge) (hmem : ∀ b, edge b ∈ rails)
    (honedge : ∀ b i, (frameBlockOccurrence q Q items b).path f i ∈
      openEdgeFinset a (depth q Q) (edge b)) :
    (Finset.univ.biUnion fun b : FrameBlock q => (frameBlockOccurrence q Q items b).sites f) =
      rails.biUnion (openEdgeFinset a (depth q Q)) := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨b, _, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr ⟨edge b, hmem b, honedge b i⟩
  · rw [frameBlock_sites_union_card, openEdgeFinsets_union_card, hcard]

theorem gap_link_short (q Q : ℕ) (hq : 2 ≤ q) (hQ : q < Q) :
    2 * alpha Q + 10 < depth q Q + 1 := by
  have hmul := Nat.mul_le_mul_right (beta Q) hq
  dsimp [alpha, beta, depth] at *
  omega

noncomputable def frameGapFirstIndex (q Q : ℕ) (items : List ℕ) (j : Fin q) : Fin (frameWord q Q items).length :=
  (frameBlockOccurrence q Q items (j, 3)).index
    ⟨0, by simp [frameBlockKind, anchorLength]⟩

theorem frameGapFirstIndex_val (q Q : ℕ) (items : List ℕ) (j : Fin q) :
    (frameGapFirstIndex q Q items j).val = (prefixWord q Q).length + (wallUnits q Q).length +
      j.val * (2 * alpha Q + 10) + 1 := by
  rw [frameGapFirstIndex, EdgeOccurrence.index_val, frameBlockOccurrence_offset]
  simp [frameBlockOffset, Nat.add_assoc]

/-- J's successive E₂ blocks cannot change between the two matching rails:
the distance between their first H sites is smaller than the rail separation. -/
theorem frame_gap_blocks_same_edge (q Q : ℕ) (items : List ℕ) (hq : 2 ≤ q) (hQ : q < Q)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (rails : Finset CubeEdge) (hmatching : ∀ bits, (incidentEdges bits ∩ rails).card ≤ 1)
    (edge : FrameBlock q → CubeEdge) (hmem : ∀ b, edge b ∈ rails)
    (honedge : ∀ b i, (frameBlockOccurrence q Q items b).path f i ∈
      openEdgeFinset a (depth q Q) (edge b)) (j k : Fin q) (hjk : j.val + 1 = k.val) :
    edge (j, 3) = edge (k, 3) := by
  let ij := frameGapFirstIndex q Q items j
  let ik := frameGapFirstIndex q Q items k
  have hj := frameGapFirstIndex_val q Q items j
  have hk := frameGapFirstIndex_val q Q items k
  have hjp : f.pos ij ∈ openEdgeFinset a (depth q Q) (edge (j, 3)) := honedge (j, 3) _
  have hkp : f.pos ik ∈ openEdgeFinset a (depth q Q) (edge (k, 3)) := honedge (k, 3) _
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hjp
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hkp
  have he : ik.val - ij.val = 2 * alpha Q + 10 := by
    change _ = _ at hj hk
    change (frameGapFirstIndex q Q items k).val - (frameGapFirstIndex q Q items j).val = _
    rw [hj, hk, ← hjk, Nat.add_mul, Nat.one_mul]
    omega
  apply short_fold_link_same_rail a (depth q Q) rails hmatching (edge (j, 3)) (edge (k, 3))
    (hmem _) (hmem _) r s f ij ik (by omega) hr.symm hs.symm
  rw [he]
  exact gap_link_short q Q hq hQ

theorem frame_gap_blocks_one_edge (q Q : ℕ) (items : List ℕ) (hq : 2 ≤ q) (hQ : q < Q)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (rails : Finset CubeEdge) (hmatching : ∀ bits, (incidentEdges bits ∩ rails).card ≤ 1)
    (edge : FrameBlock q → CubeEdge) (hmem : ∀ b, edge b ∈ rails)
    (honedge : ∀ b i, (frameBlockOccurrence q Q items b).path f i ∈
      openEdgeFinset a (depth q Q) (edge b)) :
    ∀ j : Fin q, edge (j, 3) = edge (⟨0, by omega⟩, 3) := by
  have hnat : ∀ n (hn : n < q), edge (⟨n, hn⟩, 3) = edge (⟨0, by omega⟩, 3) := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have hn' : n < q := by omega
      exact (frame_gap_blocks_same_edge q Q items hq hQ f a rails hmatching edge hmem honedge
        ⟨n, hn'⟩ ⟨n + 1, hn⟩ rfl).symm.trans (ih hn')
  intro j
  exact hnat j.val j.isLt

end ProteinFolding.CubicPackingGeometry
