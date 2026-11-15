import ProteinFolding.Tetrahedral.NearFieldRingFold
import ProteinFolding.Tetrahedral.NearFieldDimerBounds

/-! Exact H support and solid bounds for the complete three-side ring.
The assembly identities preserve residue labels as well as occupied sites. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem ringSideFold_hSupport (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    hSupport (dimerChain (m - 2)) (ringSideFold m hm F) =
      edgeDimerHsites m F 1 (m - 3) := by
  have hw : dimerChain (m - 3 + 1) = dimerChain (m - 2) := by
    rw [show m - 3 + 1 = m - 2 by omega]
  change hSupport _ (transportWordFold hw
    (edgeDimerFold (by omega : 1 ≤ m) F 1 (m - 3) false (by omega))) = _
  rw [transportWordFold_hSupport, edgeDimerFold_hSupport]

theorem ringSideFold_mem_solid_one (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (i : Fin (dimerChain (m - 2)).length) :
    (ringSideFold m hm F).pos i ∈ skinSolid m 1 := by
  let j : Fin (dimerChain (m - 3 + 1)).length :=
    ⟨i.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact i.isLt⟩
  exact edgeDimerFold_mem_solid_one (by omega : 1 ≤ m) F 1 (m - 3) false (by omega) j

def ringHsites (m : ℕ) (F : OctEdgeFrame) : Finset Site :=
  edgeDimerHsites m (ringSideFrame F 0) 1 (m - 3) ∪
    (edgeDimerHsites m (ringSideFrame F 1) 1 (m - 3) ∪
      edgeDimerHsites m (ringSideFrame F 2) 1 (m - 3))

theorem ringFold_hSupport (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame) :
    hSupport (dimerChain (3 * (m - 2))) (ringFold m hm heven F) = ringHsites m F := by
  change hSupport _ (transportWordFold _ (ringAssembly m hm heven F).piece.fold) = _
  rw [transportWordFold_hSupport, (ringAssembly m hm heven F).hSupport_eq]
  simp only [ringPieces, pieceHsupport, ringSidePiece, ringCornerPiece,
    ringSideFold_hSupport, hSupport_allP_empty, Finset.empty_union, Finset.union_empty,
    ringHsites]

theorem ringHsites_subset_oct (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    ringHsites m F ⊆ octahedron m := by
  intro x hx
  simp only [ringHsites, Finset.mem_union] at hx
  rcases hx with hx | hx | hx
  all_goals exact edgeDimerHsites_subset_oct (by omega : 1 ≤ m) _ 1 (m - 3) (by omega) hx

theorem ringFold_hSupport_subset_oct (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) :
    hSupport (dimerChain (3 * (m - 2))) (ringFold m hm heven F) ⊆ octahedron m := by
  rw [ringFold_hSupport]
  exact ringHsites_subset_oct m hm F

theorem ringFold_sites (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame) :
    foldSites (ringFold m hm heven F) = pieceSites (ringPieces m hm heven F) := by
  change foldSites (transportWordFold _ (ringAssembly m hm heven F).piece.fold) = _
  rw [transportWordFold_sites, (ringAssembly m hm heven F).sites_eq]

theorem ringPieces_sites_solid_one (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (a : PositionedWord) (ha : a ∈ ringPieces m hm heven F) :
    foldSites a.fold ⊆ skinSolid m 1 := by
  intro x hx
  simp only [ringPieces, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  all_goals obtain ⟨i, rfl⟩ := (mem_foldSites _ x).mp hx
  all_goals first
    | exact ringSideFold_mem_solid_one m hm _ i
    | exact skin_subset_solid m 1 (ringCornerFold_skin m hm _ i)

theorem ringFold_mem_solid_one (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (i : Fin (dimerChain (3 * (m - 2))).length) :
    (ringFold m hm heven F).pos i ∈ skinSolid m 1 := by
  have hmem := (mem_foldSites (ringFold m hm heven F) _).mpr ⟨i, rfl⟩
  rw [ringFold_sites] at hmem
  obtain ⟨a, ha, hi⟩ := (mem_pieceSites _ _).mp hmem
  exact ringPieces_sites_solid_one m hm heven F a ha hi

theorem ringFold_property (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (P : Site → Prop)
    (hsides : ∀ (j : Fin 3) (r : Fin (dimerChain (m - 2)).length),
      P ((ringSideFold m hm (ringSideFrame F j)).pos r))
    (hcorners : ∀ (c : Fin 2) (r : Fin 3), P ((ringCornerFold m (ringSideFrame F c.castSucc)).pos r))
    (i : Fin (dimerChain (3 * (m - 2))).length) : P ((ringFold m hm heven F).pos i) := by
  have hmem := (mem_foldSites (ringFold m hm heven F) _).mpr ⟨i, rfl⟩
  rw [ringFold_sites] at hmem
  obtain ⟨a, ha, hi⟩ := (mem_pieceSites _ _).mp hmem
  simp only [ringPieces, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  all_goals obtain ⟨r, hr⟩ := (mem_foldSites _ _).mp hi
  all_goals rw [← hr]
  all_goals first | exact hsides _ r | exact hcorners _ r

theorem ringFold_first_inB (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (i : Fin (dimerChain (3 * (m - 2))).length) (hi : i.val = 0) :
    InBSublattice ((ringFold m hm heven F).pos i).val := by
  rw [ringFold_first m hm heven F i hi]
  exact (octEdgeZigzag_odd (by omega : 1 ≤ m) (ringSideFrame F 0) 0).1

theorem ringFold_last_inB (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (i : Fin (dimerChain (3 * (m - 2))).length)
    (hi : i.val + 1 = (dimerChain (3 * (m - 2))).length) :
    InBSublattice ((ringFold m hm heven F).pos i).val := by
  rw [ringFold_last m hm heven F i hi]
  change InBSublattice (octEdgeZigzag m (ringSideFrame F 2) (2 * m - 5)).val
  rw [ringSide_last_eq_reverse_three m hm]
  exact (octEdgeZigzag_odd (by omega : 1 ≤ m)
    (bulkReverseEdgeFrame (ringSideFrame F 2)) 1).1

end ProteinFolding.Tetrahedral.NearField
