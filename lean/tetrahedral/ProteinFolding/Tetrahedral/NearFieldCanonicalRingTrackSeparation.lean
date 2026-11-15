import ProteinFolding.Tetrahedral.NearFieldCanonicalRings
import ProteinFolding.Tetrahedral.NearFieldCanonicalRightPiece

/-! Complete rings avoid every actual capped track interval and both fillers.
The interval statements retain the physical cap columns. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem ringSideHsites_disjoint_edgeHsites (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hj : F.j ≠ G.j) (s : Fin 3) (base q : ℕ) :
    Disjoint (edgeDimerHsites m (ringSideFrame F s) 1 (m - 3)) (edgeDimerHsites m G base q) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hy
  have hr := r.isLt
  exact ringEdgePoint_ne_other_small_face m hm (ringSideFrame F s) G _ _ (by omega) (by omega)
    (by rw [ringSideFrame_small]; exact hj) ht.symm

theorem ringTerminalSite_ne_other_edge (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hj : F.j ≠ G.j) (s : Fin 3) (e : Fin 2) (r : ℕ) :
    ringTerminalSite m F s e ≠ octEdgeZigzag m G r := by
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (ringTerminalSite_mem m hm F s e)
  rw [← ht]
  have ht' := t.isLt
  exact ringEdgePoint_ne_other_small_face m hm (ringSideFrame F s) G _ r (by omega) (by omega)
    (by rw [ringSideFrame_small]; exact hj)

theorem ringTerminalSite_not_mem_other_edgeHsites (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hj : F.j ≠ G.j) (s : Fin 3) (e : Fin 2) (base q : ℕ) :
    ringTerminalSite m F s e ∉ edgeDimerHsites m G base q := by
  intro hx
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hx
  exact ringTerminalSite_ne_other_edge m hm F G hj s e _ ht.symm

theorem ringFold_ne_other_edgeDimerFold (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (i : Fin (dimerChain (3 * (m - 2))).length) (j : Fin (dimerChain (q + 1)).length) :
    (ringFold m hm heven F).pos i ≠ (edgeDimerFold (by omega : 1 ≤ m) G base q reverse hroom).pos j := by
  apply ringFold_property m hm heven F (fun x => x ≠ (edgeDimerFold (by omega : 1 ≤ m) G base q reverse hroom).pos j) _ _ i
  · intro s r
    let r' : Fin (dimerChain (m - 3 + 1)).length :=
      ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
    exact edgeDimerFolds_disjoint (by omega : 1 ≤ m) (ringSideFrame F s) G
      1 (m - 3) base q false reverse (by omega) hroom
      (ringSideHsites_disjoint_edgeHsites m hm F G hj s base q) r' j
  · intro c r
    have hs := dimerLinkOwnerExcluded_of_not_mem m G base q reverse (ringTerminalSite m F c.succ 0)
      (ringTerminalSite_not_mem_other_edgeHsites m hm F G hj c.succ 0 base q)
    have ht := dimerLinkOwnerExcluded_of_not_mem m G base q reverse (ringTerminalSite m F c.castSucc 1)
      (ringTerminalSite_not_mem_other_edgeHsites m hm F G hj c.castSucc 1 base q)
    rw [← ringCorner_start_owner m hm F c] at hs
    rw [← ringCorner_end_owner m hm F c] at ht
    exact (edgeDimerFold_ne_edgePPPFold (by omega : 1 ≤ m) G
      (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) base q reverse hroom
      1 (by omega) hs ht j r.rev).symm

theorem ringFold_ne_other_edge_cap (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j) (E : DanglingColumn m) (a : ℕ)
    (hE : E.owner = octEdgeZigzag m G a) (i : Fin (dimerChain (3 * (m - 2))).length) :
    (ringFold m hm heven F).pos i ≠ E.seed := by
  apply ringFold_property m hm heven F (fun x => x ≠ E.seed) _ _ i
  · intro s r
    let r' : Fin (dimerChain (m - 3 + 1)).length :=
      ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
    apply edgeDimerFold_ne_cap_of_owner_not_mem (by omega : 1 ≤ m) (ringSideFrame F s)
      1 (m - 3) false (by omega) E _ r'
    intro hmem
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hmem
    rw [hE] at ht
    have ht' := t.isLt
    exact ringEdgePoint_ne_other_small_face m hm (ringSideFrame F s) G _ a (by omega) (by omega)
      (by rw [ringSideFrame_small]; exact hj) ht
  · intro c r
    let K := bulkReverseEdgeFrame (ringSideFrame F c.castSucc)
    change (edgePPPFold m K 1).pos r.rev ≠ E.seed
    apply facePPPFold_ne_cap_of_owner_ne m _ _ _ _ (edgePPPLateral_ne K _)
      (edgePPP_back_ne_normal K _) (edgePPP_normal_face (by omega : 1 ≤ m) K 1 (by omega)) _ E _ _ r.rev
    · rw [edgePPP_endpoint]
      rcases octEdgeZigzag_mem (by omega : 1 ≤ m) K (show 1 + 2 < 2 * m - 1 by omega) with h | h <;>
        exact h.1.1
    · rw [hE]
      change octEdgeZigzag m G a ≠ octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 1
      rw [ringCorner_start_owner m hm F c]
      exact (ringTerminalSite_ne_other_edge m hm F G hj c.succ 0 a).symm
    · rw [edgePPP_endpoint, hE]
      change octEdgeZigzag m G a ≠ octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 3
      rw [ringCorner_end_owner m hm F c]
      exact (ringTerminalSite_ne_other_edge m hm F G hj c.castSucc 1 a).symm

private theorem cappedRing_positions (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (P : Site → Prop) (hfirst : P C.seed)
    (hbody : ∀ i, P ((ringFold m (by omega) heven F).pos i)) (hlast : P D.seed)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) :
    P ((cappedRingFold m hm heven F C D hC hD).pos i) := by
  have hmem := (mem_foldSites (cappedRingFold m hm heven F C D hC hD) _).mpr ⟨i, rfl⟩
  rw [cappedRingFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]
    exact hfirst
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    rw [← hj]
    exact hbody j
  · rw [h]
    exact hlast

theorem cappedRingFold_ne_other_edgeDimerFold (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) (j : Fin (dimerChain (q + 1)).length) :
    (cappedRingFold m hm heven F C D hC hD).pos i ≠
      (edgeDimerFold (by omega : 1 ≤ m) G base q reverse hroom).pos j := by
  apply cappedRing_positions m hm heven F C D hC hD
    (fun x => x ≠ (edgeDimerFold (by omega : 1 ≤ m) G base q reverse hroom).pos j) _ _ _ i
  · apply Ne.symm
    apply edgeDimerFold_ne_cap_of_owner_not_mem (by omega : 1 ≤ m) G base q reverse hroom C _ j
    rw [hC]
    exact ringTerminalSite_not_mem_other_edgeHsites m (by omega) F G hj 0 0 base q
  · intro r
    exact ringFold_ne_other_edgeDimerFold m (by omega) heven F G hj base q reverse hroom r j
  · apply Ne.symm
    apply edgeDimerFold_ne_cap_of_owner_not_mem (by omega : 1 ≤ m) G base q reverse hroom D _ j
    rw [hD]
    exact ringTerminalSite_not_mem_other_edgeHsites m (by omega) F G hj 2 1 base q

theorem cappedRingFold_ne_other_edge_cap (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (E : DanglingColumn m) (a : ℕ) (hE : E.owner = octEdgeZigzag m G a)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) :
    (cappedRingFold m hm heven F C D hC hD).pos i ≠ E.seed := by
  apply cappedRing_positions m hm heven F C D hC hD (fun x => x ≠ E.seed) _ _ _ i
  · apply dangling_caps_ne_of_owner_ne m C.owner E.owner C.dir E.dir C.owner_mem E.owner_mem C.seed_outside
    rw [hC, hE]
    exact ringTerminalSite_ne_other_edge m (by omega) F G hj 0 0 a
  · exact ringFold_ne_other_edge_cap m (by omega) heven F G hj E a hE
  · apply dangling_caps_ne_of_owner_ne m D.owner E.owner D.dir E.dir D.owner_mem E.owner_mem D.seed_outside
    rw [hD, hE]
    exact ringTerminalSite_ne_other_edge m (by omega) F G hj 2 1 a

theorem cappedRingFold_ne_other_cappedEdgeDimerFold (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j) (C D E H : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (hE : E.owner = octEdgeZigzag m G (dimerHIndex base reverse 0 0))
    (hH : H.owner = octEdgeZigzag m G (dimerHIndex base reverse q 1))
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length)
    (j : Fin (capWord (dimerChain (q + 1))).length) :
    (cappedRingFold m hm heven F C D hC hD).pos i ≠
      (cappedEdgeDimerFold (by omega : 1 ≤ m) G base q reverse hroom E H hE hH).pos j := by
  intro heq
  have hmem := (mem_foldSites (cappedEdgeDimerFold (by omega : 1 ≤ m) G base q reverse hroom E H hE hH) _).mpr
    ⟨j, heq.symm⟩
  rw [cappedEdgeDimerFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact cappedRingFold_ne_other_edge_cap m hm heven F G hj C D hC hD E _ hE i h
  · obtain ⟨r, hr⟩ := (mem_foldSites _ _).mp h
    exact cappedRingFold_ne_other_edgeDimerFold m hm heven F G hj C D hC hD base q reverse hroom i r hr.symm
  · exact cappedRingFold_ne_other_edge_cap m hm heven F G hj C D hC hD H _ hH i h

theorem cappedRingFold_ne_other_cappedInterval (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j) (C D E H : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (base n : ℕ) (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (hE : E.owner = octEdgeZigzag m G (dimerHIndex base reverse 0 0))
    (hH : H.owner = octEdgeZigzag m G (dimerHIndex base reverse (n - 1) 1))
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) (j : Fin (capWord (dimerChain n)).length) :
    (cappedRingFold m hm heven F C D hC hD).pos i ≠
      (cappedIntervalDimerFold (by omega : 1 ≤ m) G base n hn reverse hroom E H hE hH).pos j := by
  have hm1 : 1 ≤ m := by omega
  have hroom' : base + 2 * (n - 1 + 1) ≤ 2 * m - 1 := by omega
  exact transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold hm1 G base (n - 1) reverse hroom' E H hE hH)
    (fun x => (cappedRingFold m hm heven F C D hC hD).pos i ≠ x)
    (cappedRingFold_ne_other_cappedEdgeDimerFold m hm heven F G hj C D E H hC hD
      base (n - 1) reverse hroom' hE hH i) j

theorem edgeDimerFold_ne_other_ringTerminalColumn (m : ℕ) (hm : 30 ≤ m)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (C : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0 ∨ C.owner = ringTerminalSite m F 2 1)
    (i : Fin (dimerChain (q + 1)).length) (n : ℕ) :
    (edgeDimerFold (by omega : 1 ≤ m) G base q reverse hroom).pos i ≠ C.point n := by
  apply edgeDimerFold_ne_column_of_PPP_ne (by omega : 1 ≤ m) G base q reverse hroom C _ i n
  intro j hj' s r
  have hb := dimerLinkIndex_bounds base reverse j
  exact edgePPP_ne_ring_terminal_column m hm G F _ (by omega) C hC
    (ringTerminalSite_ne_other_edge m (by omega) F G hj 0 0 _)
    (ringTerminalSite_ne_other_edge m (by omega) F G hj 0 0 _)
    (ringTerminalSite_ne_other_edge m (by omega) F G hj 2 1 _)
    (ringTerminalSite_ne_other_edge m (by omega) F G hj 2 1 _) s r

theorem ringTerminalColumn_ne_other_edge_column (m : ℕ) (hm : 3 ≤ m)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j) (C E : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0 ∨ C.owner = ringTerminalSite m F 2 1)
    (a : ℕ) (hE : E.owner = octEdgeZigzag m G a) (n r : ℕ) : C.point n ≠ E.point r := by
  apply DanglingColumn.points_ne_of_seed_ne _ n r
  apply dangling_caps_ne_of_owner_ne m C.owner E.owner C.dir E.dir C.owner_mem E.owner_mem C.seed_outside
  rw [hE]
  rcases hC with hC | hC
  · rw [hC]
    exact ringTerminalSite_ne_other_edge m hm F G hj 0 0 a
  · rw [hC]
    exact ringTerminalSite_ne_other_edge m hm F G hj 2 1 a

private theorem positions_of_capped_sites {a b : ℕ} (f : Fold tetrahedralLattice a)
    (g : Fold tetrahedralLattice b) (c d : Site)
    (hsites : foldSites f = ({c} ∪ foldSites g) ∪ {d}) (P : Site → Prop)
    (hc : P c) (hg : ∀ i, P (g.pos i)) (hd : P d) (i : Fin a) : P (f.pos i) := by
  have hmem := (mem_foldSites f _).mpr ⟨i, rfl⟩
  rw [hsites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]
    exact hc
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    rw [← hj]
    exact hg j
  · rw [h]
    exact hd

theorem cappedInterval_ne_other_ringTerminalColumn (m : ℕ) (hm : 30 ≤ m)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * m - 1) (E H C : DanglingColumn m)
    (hE : E.owner = octEdgeZigzag m G (dimerHIndex base reverse 0 0))
    (hH : H.owner = octEdgeZigzag m G (dimerHIndex base reverse (n - 1) 1))
    (hC : C.owner = ringTerminalSite m F 0 0 ∨ C.owner = ringTerminalSite m F 2 1)
    (i : Fin (capWord (dimerChain n)).length) (r : ℕ) :
    (cappedIntervalDimerFold (by omega : 1 ≤ m) G base n hn reverse hroom E H hE hH).pos i ≠ C.point r := by
  have hm1 : 1 ≤ m := by omega
  have hroom' : base + 2 * (n - 1 + 1) ≤ 2 * m - 1 := by omega
  apply transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold hm1 G base (n - 1) reverse hroom' E H hE hH) (fun x => x ≠ C.point r) _ i
  intro j
  apply positions_of_capped_sites _ _ E.seed H.seed (cappedEdgeDimerFold_sites hm1 G base (n - 1) reverse hroom' E H hE hH)
    (fun x => x ≠ C.point r) _ _ _ j
  · exact (ringTerminalColumn_ne_other_edge_column m (by omega) F G hj C E hC _ hE r 0).symm
  · intro t
    exact edgeDimerFold_ne_other_ringTerminalColumn m hm F G hj base (n - 1) reverse hroom' C hC t r
  · exact (ringTerminalColumn_ne_other_edge_column m (by omega) F G hj C H hC _ hH r 0).symm

theorem canonicalRingWordPiece_ne_reserved_edge_cap (p : ConstructionParameters) (i : Fin 3)
    (G : OctEdgeFrame) (hG : G.j = 3) (E : DanglingColumn p.side) (a : ℕ)
    (hE : E.owner = octEdgeZigzag p.side G a) (r : Fin (canonicalRingWordPiece p i).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ E.seed :=
  cappedRingFold_ne_other_edge_cap p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) G (by rw [hG]; exact canonicalRingFrame_small_ne_reserved i)
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i) E a hE r

theorem canonicalRingWordPiece_ne_reserved_interval (p : ConstructionParameters) (i : Fin 3)
    (G : OctEdgeFrame) (hG : G.j = 3) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * p.side - 1) (E H : DanglingColumn p.side)
    (hE : E.owner = octEdgeZigzag p.side G (dimerHIndex base reverse 0 0))
    (hH : H.owner = octEdgeZigzag p.side G (dimerHIndex base reverse (n - 1) 1))
    (r : Fin (canonicalRingWordPiece p i).word.length)
    (s : Fin (cappedIntervalDimerPiece (m := p.side) (by have h := p.side_ge; omega) G base n hn reverse hroom E H hE hH).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠
      (cappedIntervalDimerPiece (m := p.side) (by have h := p.side_ge; omega) G base n hn reverse hroom E H hE hH).fold.pos s :=
  cappedRingFold_ne_other_cappedInterval p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) G (by rw [hG]; exact canonicalRingFrame_small_ne_reserved i)
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1) E H
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i) base n hn reverse hroom hE hH r s

theorem reserved_interval_ne_canonicalRingColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (G : OctEdgeFrame) (hG : G.j = 3) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * p.side - 1) (E H : DanglingColumn p.side)
    (hE : E.owner = octEdgeZigzag p.side G (dimerHIndex base reverse 0 0))
    (hH : H.owner = octEdgeZigzag p.side G (dimerHIndex base reverse (n - 1) 1))
    (s : Fin (cappedIntervalDimerPiece (m := p.side) (by have h := p.side_ge; omega) G base n hn reverse hroom E H hE hH).word.length)
    (r : ℕ) : (cappedIntervalDimerPiece (m := p.side) (by have h := p.side_ge; omega) G base n hn reverse hroom E H hE hH).fold.pos s ≠
      (canonicalRingColumn p i e).point r :=
  cappedInterval_ne_other_ringTerminalColumn p.side (by have h := p.side_ge; omega) (canonicalRingFrame i) G
    (by rw [hG]; exact canonicalRingFrame_small_ne_reserved i) base n hn reverse hroom E H
    (canonicalRingColumn p i e) hE hH (canonicalRingColumn_owner_alternative p i e) s r

theorem canonicalRingWordPiece_ne_itemPiece (p : ConstructionParameters) (i : Fin 3) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (r : Fin (canonicalRingWordPiece p i).word.length)
    (t : Fin (canonicalItemPiece p k before s hk hs hload).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (canonicalItemPiece p k before s hk hs hload).fold.pos t := by
  exact canonicalRingWordPiece_ne_reserved_interval p i trackEdgeFrame rfl
    (itemTrackBase p k before) (p.itemDimers s) (by have h := p.itemDimers_ge s hs; omega) false
    (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload) r t

theorem canonicalItemPiece_ne_ringColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (k before s : ℕ) (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (t : Fin (canonicalItemPiece p k before s hk hs hload).word.length) (r : ℕ) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos t ≠ (canonicalRingColumn p i e).point r := by
  exact reserved_interval_ne_canonicalRingColumn p i e trackEdgeFrame rfl
    (itemTrackBase p k before) (p.itemDimers s) (by have h := p.itemDimers_ge s hs; omega) false
    (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload) t r

private theorem rightFillerLastIndex (p : ConstructionParameters) :
    dimerHIndex (rightFillerTrackBase p) false (p.rightFiller - 1) 1 = 2 * p.side - 3 := by
  rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
  have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
  dsimp [rightFillerTrackBase]
  omega

theorem canonicalRingWordPiece_ne_rightPiece (p : ConstructionParameters) (i : Fin 3)
    (r : Fin (canonicalRingWordPiece p i).word.length) (s : Fin (canonicalRightPiece p).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (canonicalRightPiece p).fold.pos s := by
  exact canonicalRingWordPiece_ne_reserved_interval p i trackEdgeFrame rfl
    (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega) false
    (rightFillerTrackBase_room p) (rightFirstColumn p) (rightFinalColumn p)
    (by rfl) (by rw [rightFillerLastIndex]; exact rightFinalColumn_track_owner p) r s

theorem canonicalRightPiece_ne_ringColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (s : Fin (canonicalRightPiece p).word.length) (r : ℕ) :
    (canonicalRightPiece p).fold.pos s ≠ (canonicalRingColumn p i e).point r := by
  exact reserved_interval_ne_canonicalRingColumn p i e trackEdgeFrame rfl
    (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega) false
    (rightFillerTrackBase_room p) (rightFirstColumn p) (rightFinalColumn p)
    (by rfl) (by rw [rightFillerLastIndex]; exact rightFinalColumn_track_owner p) s r

private theorem cappedRingFold_ne_reserved_edgePoint (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (hj : F.j ≠ 3) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (G : OctEdgeFrame) (hG : G.j = 3) (a : ℕ) (ha : a < 2 * m - 1)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) :
    (cappedRingFold m hm heven F C D hC hD).pos i ≠ octEdgeZigzag m G a := by
  have hin : octEdgeZigzag m G a ∈ octahedron m := by
    rcases octEdgeZigzag_mem (by omega : 1 ≤ m) G ha with h | h
    · exact h.1.1
    · exact h.1.1
  have hface := ringEdgePoint_small_coordinate m (by omega) G a
  rw [hG] at hface
  exact cappedRingFold_ne_reserved_oct_site m hm heven F hj C D hC hD
    (octEdgeZigzag m G a) hin hface i

theorem canonicalRingWordPiece_ne_leftFillerFold (p : ConstructionParameters) (i : Fin 3)
    (r : Fin (canonicalRingWordPiece p i).word.length) (s : Fin (dimerChain p.leftFiller).length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (leftFillerFold p).pos s := by
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hs
  · exact cappedRingFold_ne_reserved_edgePoint p.side (by have h := p.side_ge; omega) p.side_even
      (canonicalRingFrame i) (canonicalRingFrame_small_ne_reserved i)
      (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
      (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)
      entryEdgeFrame rfl 2 (by have h := p.side_ge; omega) r
  · let t : Fin (dimerChain (p.leftFiller - 1 + 1)).length :=
      ⟨s.val, by
        have hl := dimerChain_succ_length (p.leftFiller - 1)
        have hn := leftFiller_word_length p
        have hs' := s.isLt
        omega⟩
    have h := cappedRingFold_ne_other_edgeDimerFold p.side (by have h := p.side_ge; omega) p.side_even
      (canonicalRingFrame i) trackEdgeFrame (canonicalRingFrame_small_ne_reserved i)
      (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
      (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)
      0 (p.leftFiller - 1) false (leftFiller_room p) r t
    rw [edgeDimerFold_pos] at h
    exact h

private theorem entryLocal_none_owner (p : ConstructionParameters) :
    (entryLocalColumn p none).owner = octEdgeZigzag p.side entryEdgeFrame 2 := by
  dsimp only [entryLocalColumn, entryAColumn, entryCapIndex]

theorem canonicalRingWordPiece_ne_leftPiece (p : ConstructionParameters) (i : Fin 3)
    (r : Fin (canonicalRingWordPiece p i).word.length) (s : Fin (canonicalLeftPiece p).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (canonicalLeftPiece p).fold.pos s := by
  dsimp only [canonicalLeftPiece, leftFillerWordPiece] at s ⊢
  apply positions_of_capped_sites
    (cappedLeftFillerFold p (entryLocalColumn p none) (leftLastColumn p) (entryLocal_none_owner p) (leftLastColumn_owner p))
    (leftFillerFold p) (entryLocalColumn p none).seed (leftLastColumn p).seed
    (cappedLeftFillerFold_sites p _ _ (entryLocal_none_owner p) (leftLastColumn_owner p))
    (fun x => (canonicalRingWordPiece p i).fold.pos r ≠ x) _ _ _ s
  · exact canonicalRingWordPiece_ne_reserved_edge_cap p i entryEdgeFrame rfl _ 2 (entryLocal_none_owner p) r
  · exact canonicalRingWordPiece_ne_leftFillerFold p i r
  · exact canonicalRingWordPiece_ne_reserved_edge_cap p i trackEdgeFrame rfl _ _ (leftLastColumn_owner p) r

private theorem inside_ne_column {m : ℕ} {x : Site} (hx : x ∈ octahedron m)
    (C : DanglingColumn m) (n : ℕ) : x ≠ C.point n := by
  intro heq
  rw [heq] at hx
  exact C.point_outside n hx

theorem leftFillerFold_ne_canonicalRingColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (s : Fin (dimerChain p.leftFiller).length) (r : ℕ) :
    (leftFillerFold p).pos s ≠ (canonicalRingColumn p i e).point r := by
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hs
  · exact inside_ne_column (leftFillerStart_mem_oct p) (canonicalRingColumn p i e) r
  · let t : Fin (dimerChain (p.leftFiller - 1 + 1)).length :=
      ⟨s.val, by
        have hl := dimerChain_succ_length (p.leftFiller - 1)
        have hn := leftFiller_word_length p
        have hs' := s.isLt
        omega⟩
    have h := edgeDimerFold_ne_other_ringTerminalColumn p.side (by have h := p.side_ge; omega)
      (canonicalRingFrame i) trackEdgeFrame (canonicalRingFrame_small_ne_reserved i)
      0 (p.leftFiller - 1) false (leftFiller_room p) (canonicalRingColumn p i e)
      (canonicalRingColumn_owner_alternative p i e) t r
    rw [edgeDimerFold_pos] at h
    exact h

theorem canonicalLeftPiece_ne_ringColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (s : Fin (canonicalLeftPiece p).word.length) (r : ℕ) :
    (canonicalLeftPiece p).fold.pos s ≠ (canonicalRingColumn p i e).point r := by
  dsimp only [canonicalLeftPiece, leftFillerWordPiece] at s ⊢
  apply positions_of_capped_sites
    (cappedLeftFillerFold p (entryLocalColumn p none) (leftLastColumn p) (entryLocal_none_owner p) (leftLastColumn_owner p))
    (leftFillerFold p) (entryLocalColumn p none).seed (leftLastColumn p).seed
    (cappedLeftFillerFold_sites p _ _ (entryLocal_none_owner p) (leftLastColumn_owner p))
    (fun x => x ≠ (canonicalRingColumn p i e).point r) _ _ _ s
  · exact (ringTerminalColumn_ne_other_edge_column p.side (by have h := p.side_ge; omega)
      (canonicalRingFrame i) entryEdgeFrame (canonicalRingFrame_small_ne_reserved i)
      (canonicalRingColumn p i e) (entryLocalColumn p none) (canonicalRingColumn_owner_alternative p i e)
      2 (entryLocal_none_owner p) r 0).symm
  · intro t
    exact leftFillerFold_ne_canonicalRingColumn p i e t r
  · exact (ringTerminalColumn_ne_other_edge_column p.side (by have h := p.side_ge; omega)
      (canonicalRingFrame i) trackEdgeFrame (canonicalRingFrame_small_ne_reserved i)
      (canonicalRingColumn p i e) (leftLastColumn p) (canonicalRingColumn_owner_alternative p i e)
      _ (leftLastColumn_owner p) r 0).symm

theorem canonicalRingWordPiece_leftPiece_disjoint (p : ConstructionParameters) (i : Fin 3) :
    Disjoint (foldSites (canonicalRingWordPiece p i).fold) (foldSites (canonicalLeftPiece p).fold) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalRingWordPiece_ne_leftPiece p i)

theorem canonicalRingWordPiece_itemPiece_disjoint (p : ConstructionParameters) (i : Fin 3)
    (k before s : ℕ) (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    Disjoint (foldSites (canonicalRingWordPiece p i).fold)
      (foldSites (canonicalItemPiece p k before s hk hs hload).fold) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalRingWordPiece_ne_itemPiece p i k before s hk hs hload)

theorem canonicalRingWordPiece_rightPiece_disjoint (p : ConstructionParameters) (i : Fin 3) :
    Disjoint (foldSites (canonicalRingWordPiece p i).fold) (foldSites (canonicalRightPiece p).fold) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalRingWordPiece_ne_rightPiece p i)

end ProteinFolding.Tetrahedral.NearField
