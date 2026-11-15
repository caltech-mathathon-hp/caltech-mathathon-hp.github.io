import ProteinFolding.Tetrahedral.NearFieldDimerChainFrame
import ProteinFolding.Tetrahedral.NearFieldDimerHsiteIndices
import ProteinFolding.Tetrahedral.NearFieldFrameCoreEndpoints
import ProteinFolding.Tetrahedral.NearFieldIntervalPieces

/-! Inner track intervals avoid all frame H-runs and P-links, including
both local caps. These interfaces use only the checked uncapped frame. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem frameTrack_property_of_capped_sites {a b : ℕ} (f : Fold tetrahedralLattice a)
    (g : Fold tetrahedralLattice b) (p q : Site)
    (hsites : foldSites f = ({p} ∪ foldSites g) ∪ {q}) (P : Site → Prop)
    (hp : P p) (hg : ∀ i, P (g.pos i)) (hq : P q) (i : Fin a) : P (f.pos i) := by
  have h := (mem_foldSites f _).mpr ⟨i, rfl⟩
  rw [hsites] at h
  simp only [Finset.mem_union, Finset.mem_singleton] at h
  rcases h with (h | h) | h
  · rw [h]
    exact hp
  · obtain ⟨j, hj⟩ := (mem_foldSites g _).mp h
    rw [← hj]
    exact hg j
  · rw [h]
    exact hq

theorem cappedEdgeDimerFold_property {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1))
    (P : Site → Prop) (hfirst : P C.seed)
    (hbody : ∀ i, P ((edgeDimerFold hm F base q reverse hroom).pos i)) (hlast : P D.seed)
    (i : Fin (capWord (dimerChain (q + 1))).length) :
    P ((cappedEdgeDimerFold hm F base q reverse hroom C D hC hD).pos i) :=
  frameTrack_property_of_capped_sites _ _ C.seed D.seed
    (cappedEdgeDimerFold_sites hm F base q reverse hroom C D hC hD)
    P hfirst hbody hlast i

theorem edgeDimerFold_ne_octSite_of_not_mem_Hsites {m : ℕ} (hm : 1 ≤ m)
    (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (x : Site) (hx : x ∈ octahedron m)
    (hnot : x ∉ edgeDimerHsites m F base q) (i : Fin (dimerChain (q + 1)).length) :
    (edgeDimerFold hm F base q reverse hroom).pos i ≠ x := by
  rcases edgeDimerFold_pos_cases hm F base q reverse hroom i with
      ⟨j, hj, s, hs⟩ | ⟨j, hj, s, hs⟩
  · rw [hs]
    intro heq
    apply hnot
    rw [← heq]
    exact dimerHIndex_mem_Hsites m F base q reverse j hj s
  · rw [hs]
    intro heq
    have hb := dimerLinkIndex_bounds base reverse j
    have hinside := hx
    rw [← heq] at hinside
    exact edgePPPFold_outside hm F _ (by omega) s hinside

theorem cappedEdgeDimerFold_ne_octSite_of_not_mem_Hsites {m : ℕ} (hm : 1 ≤ m)
    (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1))
    (x : Site) (hx : x ∈ octahedron m) (hnot : x ∉ edgeDimerHsites m F base q)
    (i : Fin (capWord (dimerChain (q + 1))).length) :
    (cappedEdgeDimerFold hm F base q reverse hroom C D hC hD).pos i ≠ x := by
  apply cappedEdgeDimerFold_property hm F base q reverse hroom C D hC hD (fun y => y ≠ x) _ _ _ i
  · intro heq
    apply C.seed_outside
    change C.seed ∈ octahedron m
    rw [heq]
    exact hx
  · exact edgeDimerFold_ne_octSite_of_not_mem_Hsites hm F base q reverse hroom x hx hnot
  · intro heq
    apply D.seed_outside
    change D.seed ∈ octahedron m
    rw [heq]
    exact hx

theorem cappedEdgeDimerFold_ne_cap_of_owner_not_mem {m : ℕ} (hm : 1 ≤ m)
    (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1))
    (E : DanglingColumn m) (hE : E.owner ∉ edgeDimerHsites m F base q)
    (i : Fin (capWord (dimerChain (q + 1))).length) :
    (cappedEdgeDimerFold hm F base q reverse hroom C D hC hD).pos i ≠ E.seed := by
  have hCm : C.owner ∈ edgeDimerHsites m F base q := by
    rw [hC]
    exact dimerHIndex_mem_Hsites m F base q reverse 0 (by omega) 0
  have hDm : D.owner ∈ edgeDimerHsites m F base q := by
    rw [hD]
    exact dimerHIndex_mem_Hsites m F base q reverse q le_rfl 1
  have hcap (X : DanglingColumn m) (hX : X.owner ∈ edgeDimerHsites m F base q) : X.seed ≠ E.seed := by
    apply dangling_caps_ne_of_owner_ne m X.owner E.owner X.dir E.dir X.owner_mem E.owner_mem X.seed_outside
    intro heq
    apply hE
    rw [← heq]
    exact hX
  exact cappedEdgeDimerFold_property hm F base q reverse hroom C D hC hD (fun y => y ≠ E.seed)
    (hcap C hCm) (edgeDimerFold_ne_cap_of_owner_not_mem hm F base q reverse hroom E hE) (hcap D hDm) i

theorem cappedEdgeDimerFold_ne_framePFold {m : ℕ} (hm : 1 ≤ m)
    (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1))
    (f : ℕ) (kind : Fin 6) (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius m)
    (hstart : frameStartH m f kind ∉ edgeDimerHsites m F base q)
    (hend : frameEndH m f kind ∉ edgeDimerHsites m F base q)
    (i : Fin (capWord (dimerChain (q + 1))).length) (t : Fin (nearFrameLength kind - 2)) :
    (cappedEdgeDimerFold hm F base q reverse hroom C D hC hD).pos i ≠ (framePFold m f kind hf).pos t := by
  have hCm : C.owner ∈ edgeDimerHsites m F base q := by
    rw [hC]
    exact dimerHIndex_mem_Hsites m F base q reverse 0 (by omega) 0
  have hDm : D.owner ∈ edgeDimerHsites m F base q := by
    rw [hD]
    exact dimerHIndex_mem_Hsites m F base q reverse q le_rfl 1
  exact cappedEdgeDimerFold_property hm F base q reverse hroom C D hC hD
    (fun x => x ≠ (framePFold m f kind hf).pos t)
    (edgeDimerCap_ne_framePFold m F base q C hCm f kind hf hflo hfhi hstart hend t)
    (fun j => edgeDimerFold_ne_framePFold hm F base q reverse hroom
      f kind hf hflo hfhi hstart hend j t)
    (edgeDimerCap_ne_framePFold m F base q D hDm f kind hf hflo hfhi hstart hend t) i

theorem nearFrameRouteFrame_ne_track (kind : Fin 6) :
    (nearFrameRouteFrame kind).k ≠ trackEdgeFrame.k := by
  unfold nearFrameRouteFrame
  split_ifs <;> decide

theorem innerTrack_frameStart_not_mem {m : ℕ} (hm : 3 ≤ m) (base q : ℕ)
    (hlo : 2 ≤ base) (hhi : base + 2 * (q + 1) + 1 ≤ 2 * m - 2)
    (f : ℕ) (kind : Fin 6) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius m) :
    frameStartH m f kind ∉ edgeDimerHsites m trackEdgeFrame base q :=
  edgeDimerHsites_not_mem_other_pair hm trackEdgeFrame base q hlo hhi
    (nearFrameRouteFrame kind) (nearFrameStartIndex m f kind)
    (nearFrame_endpoint_indices m f kind hflo hfhi).1 (Or.inl (nearFrameRouteFrame_ne_track kind))

theorem innerTrack_frameEnd_not_mem {m : ℕ} (hm : 3 ≤ m) (base q : ℕ)
    (hlo : 2 ≤ base) (hhi : base + 2 * (q + 1) + 1 ≤ 2 * m - 2)
    (f : ℕ) (kind : Fin 6) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius m) :
    frameEndH m f kind ∉ edgeDimerHsites m trackEdgeFrame base q :=
  edgeDimerHsites_not_mem_other_pair hm trackEdgeFrame base q hlo hhi
    (nearFrameRouteFrame kind) (nearFrameEndIndex m f kind)
    (nearFrame_endpoint_indices m f kind hflo hfhi).2 (Or.inl (nearFrameRouteFrame_ne_track kind))

theorem cappedInnerTrack_ne_framePFold {m : ℕ} (hm : 3 ≤ m) (base n : ℕ) (hn : 0 < n)
    (hlo : 2 ≤ base) (hhi : base + 2 * n + 1 ≤ 2 * m - 2) (reverse : Bool)
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m trackEdgeFrame (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m trackEdgeFrame (dimerHIndex base reverse (n - 1) 1))
    (f : ℕ) (kind : Fin 6) (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius m)
    (i : Fin (capWord (dimerChain n)).length) (t : Fin (nearFrameLength kind - 2)) :
    (cappedIntervalDimerFold (m := m) (by omega) trackEdgeFrame base n hn reverse (by omega) C D hC hD).pos i ≠
      (framePFold m f kind hf).pos t := by
  exact transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold (by omega : 1 ≤ m) trackEdgeFrame base (n - 1) reverse (by omega) C D hC hD)
    (fun x => x ≠ (framePFold m f kind hf).pos t)
    (fun j => cappedEdgeDimerFold_ne_framePFold (by omega : 1 ≤ m) trackEdgeFrame
      base (n - 1) reverse (by omega) C D hC hD f kind hf hflo hfhi
      (innerTrack_frameStart_not_mem hm base (n - 1) hlo (by omega) f kind hflo hfhi)
      (innerTrack_frameEnd_not_mem hm base (n - 1) hlo (by omega) f kind hflo hfhi) j t) i

theorem frameHRun_frame_ne_track (p : ConstructionParameters) (j : FrameHRunIndex p) :
    (frameHRunData p j).frame.k ≠ trackEdgeFrame.k := by
  rw [frameHRun_frame]
  cases frameHRunOnExit j <;> decide

theorem innerTrack_frameHRun_pos_not_mem (p : ConstructionParameters) (base q : ℕ)
    (hlo : 2 ≤ base) (hhi : base + 2 * (q + 1) + 1 ≤ 2 * p.side - 2)
    (j : FrameHRunIndex p) (s : Fin (frameHRunWord p j).length) :
    (frameHRunFold p j).pos s ∉ edgeDimerHsites p.side trackEdgeFrame base q := by
  have hmem := (mem_foldSites (frameHRunFold p j) _).mpr ⟨s, rfl⟩
  rw [frameHRunFold_sites] at hmem
  obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hmem
  have ht' := Finset.mem_range.mp ht
  have hr := frameHRun_room p j
  have hnot := edgeDimerHsites_not_mem_other_pair (by have h := p.side_ge; omega : 3 ≤ p.side)
    trackEdgeFrame base q hlo hhi (frameHRunData p j).frame ((frameHRunData p j).base + t)
    (by omega) (Or.inl (frameHRun_frame_ne_track p j))
  exact heq ▸ hnot

theorem cappedInterval_ne_frameCoreFold_of_exclusions (p : ConstructionParameters)
    (F : OctEdgeFrame) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * p.side - 1) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (n - 1) 1))
    (hH : ∀ j : FrameHRunIndex p, ∀ s : Fin (frameHRunWord p j).length,
      (frameHRunFold p j).pos s ∉ edgeDimerHsites p.side F base (n - 1))
    (hstart : ∀ j : FrameLinkIndex p,
      frameStartH p.side (frameLinkParameter j) (frameLinkKind j) ∉ edgeDimerHsites p.side F base (n - 1))
    (hend : ∀ j : FrameLinkIndex p,
      frameEndH p.side (frameLinkParameter j) (frameLinkKind j) ∉ edgeDimerHsites p.side F base (n - 1))
    (i : Fin (capWord (dimerChain n)).length) (t : Fin (p.framePart1 ++ p.framePart2).length) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      F base n hn reverse hroom C D hC hD).pos i ≠ (frameCoreFold p).pos t := by
  let f := cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
    F base n hn reverse hroom C D hC hD
  apply frameCoreFold_property p (fun x => f.pos i ≠ x) _ t
  intro j s
  rcases j with j | j
  · dsimp only [frameCorePiece, frameHRunPiece] at s ⊢
    exact transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
      (cappedEdgeDimerFold (by have h := p.side_ge; omega : 1 ≤ p.side)
        F base (n - 1) reverse (by omega) C D hC hD)
      (fun x => x ≠ (frameHRunFold p j).pos s)
      (fun r => cappedEdgeDimerFold_ne_octSite_of_not_mem_Hsites
        (by have h := p.side_ge; omega : 1 ≤ p.side) F base (n - 1)
        reverse (by omega) C D hC hD _ (frameHRunFold_mem_oct p j s) (hH j s) r) i
  · dsimp only [frameCorePiece, frameLinkPiece] at s ⊢
    rw [frameLinkWordFold_pos]
    let s' : Fin (nearFrameLength (frameLinkKind j) - 2) :=
      ⟨s.val, by simpa only [frameLinkWord, List.length_replicate] using s.isLt⟩
    change f.pos i ≠ (frameLinkFold p j).pos s'
    exact transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
      (cappedEdgeDimerFold (by have h := p.side_ge; omega : 1 ≤ p.side)
        F base (n - 1) reverse (by omega) C D hC hD)
      (fun x => x ≠ (frameLinkFold p j).pos s')
      (fun r => cappedEdgeDimerFold_ne_framePFold (by have h := p.side_ge; omega : 1 ≤ p.side)
        F base (n - 1) reverse (by omega) C D hC hD (frameLinkParameter j) (frameLinkKind j)
        (frameLinkParameter_odd p j) (frameLinkParameter_ge p j) (frameLinkParameter_room p j)
        (hstart j) (hend j) r s') i

theorem cappedInnerTrack_ne_frameCoreFold (p : ConstructionParameters) (base n : ℕ) (hn : 0 < n)
    (hlo : 2 ≤ base) (hhi : base + 2 * n + 1 ≤ 2 * p.side - 2) (reverse : Bool)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side trackEdgeFrame (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (dimerHIndex base reverse (n - 1) 1))
    (i : Fin (capWord (dimerChain n)).length) (t : Fin (p.framePart1 ++ p.framePart2).length) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      trackEdgeFrame base n hn reverse (by omega) C D hC hD).pos i ≠ (frameCoreFold p).pos t :=
  cappedInterval_ne_frameCoreFold_of_exclusions p trackEdgeFrame base n hn reverse (by omega) C D hC hD
    (innerTrack_frameHRun_pos_not_mem p base (n - 1) hlo (by omega))
    (fun j => innerTrack_frameStart_not_mem (by have h := p.side_ge; omega : 3 ≤ p.side)
      base (n - 1) hlo (by omega) (frameLinkParameter j) (frameLinkKind j)
      (frameLinkParameter_ge p j) (frameLinkParameter_room p j))
    (fun j => innerTrack_frameEnd_not_mem (by have h := p.side_ge; omega : 3 ≤ p.side)
      base (n - 1) hlo (by omega) (frameLinkParameter j) (frameLinkKind j)
      (frameLinkParameter_ge p j) (frameLinkParameter_room p j)) i t

theorem innerTrack_frameEndpoint_owner_not_mem (p : ConstructionParameters) (base q : ℕ)
    (hlo : 2 ≤ base) (hhi : base + 2 * (q + 1) + 1 ≤ 2 * p.side - 2) (b : Bool) :
    (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).owner ∉
      edgeDimerHsites p.side trackEdgeFrame base q := by
  change frameEndpointVertex p.side b ∉ _
  rw [frameEndpointVertex_eq_edge]
  cases b
  · exact edgeDimerHsites_not_mem_other_pair (by have h := p.side_ge; omega : 3 ≤ p.side)
      trackEdgeFrame base q hlo hhi exitEdgeFrame 0 (by have h := p.side_ge; omega) (Or.inl (by decide))
  · exact edgeDimerHsites_not_mem_other_pair (by have h := p.side_ge; omega : 3 ≤ p.side)
      trackEdgeFrame base q hlo hhi entryEdgeFrame 0 (by have h := p.side_ge; omega) (Or.inl (by decide))

end ProteinFolding.Tetrahedral.NearField

