import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonColumns
import ProteinFolding.Tetrahedral.BulkSurfaceDegree
import ProteinFolding.Tetrahedral.FarFieldMixedCaps

/-! Pairwise and bulk interfaces for the actual standalone vertex columns.
Positive-height columns also miss all three complete PHP words. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem canonicalSingletonColumn_seed_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (fun a : Fin 3 × Bool =>
      (canonicalSingletonColumn m (by omega) a.1 a.2).seed) := by
  rintro ⟨r, a⟩ ⟨s, b⟩ heq
  have hrs : r = s := by
    by_contra hne
    exact dangling_caps_ne_of_owner_ne m _ _ _ _
      (canonicalSingletonColumn m (by omega) r a).owner_mem
      (canonicalSingletonColumn m (by omega) s b).owner_mem
      (canonicalSingletonColumn m (by omega) r a).seed_outside
      (fun h => hne (canonicalSingletonOwner_injective m hm h)) heq
  subst s
  have hab : a = b := by
    cases a <;> cases b
    · rfl
    · exact False.elim (canonicalSingletonCaps_ne m (by omega) r heq)
    · exact False.elim (canonicalSingletonCaps_ne m (by omega) r heq.symm)
    · rfl
  exact Prod.ext rfl hab

theorem canonicalSingletonColumns_points_ne (m : ℕ) (hm : 2 ≤ m)
    (a b : Fin 3 × Bool) (hne : a ≠ b) (n s : ℕ) :
    (canonicalSingletonColumn m (by omega) a.1 a.2).point n ≠
      (canonicalSingletonColumn m (by omega) b.1 b.2).point s :=
  DanglingColumn.points_ne_of_seed_ne
    (fun h => hne (canonicalSingletonColumn_seed_injective m hm h)) n s

theorem canonicalSingletonColumn_owner_deleted (m : ℕ) (hm : 1 ≤ m)
    (r : Fin 3) (last : Bool) :
    (canonicalSingletonColumn m hm r last).owner ∈ bulkDeletedEdges m :=
  octVertices_subset_bulkDeleted hm (octVertexForFaces_mem m r.castSucc 3)

theorem canonicalSingletonColumn_ne_bulkColumn (m : ℕ) (hm : 1 ≤ m)
    (r : Fin 3) (last : Bool) (C : DanglingColumn m) (hC : C.owner ∈ bulkInterior m)
    (n s : ℕ) :
    (canonicalSingletonColumn m hm r last).point n ≠ C.point s :=
  (bulkColumn_ne_edgeColumn C (canonicalSingletonColumn m hm r last) hC
    (canonicalSingletonColumn_owner_deleted m hm r last) s n).symm

theorem canonicalSingletonColumn_ne_BColumn (m : ℕ) (hm : 1 ≤ m)
    (r : Fin 3) (last : Bool) (C : DanglingColumn m) (hC : InBSublattice C.owner.val)
    (n s : ℕ) :
    (canonicalSingletonColumn m hm r last).point n ≠ C.point s :=
  DanglingColumn.points_ne_of_owner_colours _ _ (canonicalSingletonOwner_inA m r) hC n s

theorem canonicalSingletonOwner_ne_frameBorrowOwner (m : ℕ) (hm : 3 ≤ m)
    (r : Fin 3) (i : ℕ) (hi : i % 2 = 0) (mode : Bool) :
    canonicalSingletonOwner m r ≠ frameBorrowOwner (m := m) (by omega) i hi mode := by
  intro heq
  have hx := congrArg (fun x : Site => x.val 0) heq
  change (canonicalSingletonOwner m r).val 0 =
    (octEdgeZigzag m entryEdgeFrame i).val 0 + frameBorrowOffset mode 0 at hx
  rw [entryEdgeZigzag_coordinates (by omega : 1 ≤ m)] at hx
  fin_cases r
  all_goals dsimp [canonicalSingletonOwner, octVertexForFaces, octVertexSite,
    octVertexCoordinates, octCentre, frameBorrowOffset, entryEdgeCoordinates, octRadius] at hx
  all_goals omega

theorem canonicalSingletonColumn_ne_frameBorrowColumn (m : ℕ) (hm : 3 ≤ m)
    (r : Fin 3) (last : Bool) (i : ℕ) (hi : i % 2 = 0) (hilo : 2 ≤ i)
    (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) (n s : ℕ) :
    (canonicalSingletonColumn m (by omega) r last).point n ≠
      (frameBorrowColumn (m := m) (by omega) i hi hilo hihi mode).point s := by
  apply DanglingColumn.points_ne_of_seed_ne _ n s
  exact dangling_caps_ne_of_owner_ne m _ _ _ _
    (canonicalSingletonColumn m (by omega) r last).owner_mem
    (frameBorrowColumn (m := m) (by omega) i hi hilo hihi mode).owner_mem
    (canonicalSingletonColumn m (by omega) r last).seed_outside
    (canonicalSingletonOwner_ne_frameBorrowOwner m hm r i hi mode)

theorem canonicalSingletonOwner_ne_of_reserved_coordinate (m : ℕ) (hm : 2 ≤ m)
    (r : Fin 3) (x : Site) (hx : tetraCoordinate m x.val 3 ≤ -octRadius m) :
    canonicalSingletonOwner m r ≠ x := by
  intro heq
  have h := (canonicalSingletonOwner_faces m r).2
  rw [heq] at h
  dsimp [octRadius] at hx h
  omega

theorem frameEndpointVertex_reserved_coordinate (m : ℕ) (atStart : Bool) :
    tetraCoordinate m (frameEndpointVertex m atStart).val 3 = -octRadius m := by
  cases atStart <;> dsimp [frameEndpointVertex, octVertexSite, octVertexCoordinates,
    octCentre, tetraCoordinate] <;> omega

theorem canonicalSingletonColumn_ne_frameEndpointColumn (m : ℕ) (hm : 2 ≤ m)
    (r : Fin 3) (last atStart : Bool) (n s : ℕ) :
    (canonicalSingletonColumn m (by omega) r last).point n ≠
      (frameEndpointColumn (m := m) (by omega) atStart).point s := by
  apply DanglingColumn.points_ne_of_seed_ne _ n s
  exact dangling_caps_ne_of_owner_ne m _ _ _ _
    (canonicalSingletonColumn m (by omega) r last).owner_mem
    (frameEndpointColumn (m := m) (by omega) atStart).owner_mem
    (canonicalSingletonColumn m (by omega) r last).seed_outside
    (canonicalSingletonOwner_ne_of_reserved_coordinate m hm r _
      (le_of_eq (frameEndpointVertex_reserved_coordinate m atStart)))

theorem canonicalSingletonPiece_ne_positiveColumn (m : ℕ) (hm : 1 ≤ m)
    (r : Fin 3) (C : DanglingColumn m) (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (canonicalSingletonPiece m hm r).word.length) :
    (canonicalSingletonPiece m hm r).fold.pos i ≠ C.point n := by
  intro heq
  have hmem := (mem_foldSites (canonicalSingletonPiece m hm r).fold _).mpr ⟨i, heq⟩
  rw [canonicalSingletonPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact FarField.dangling_ne_positive_column
      (canonicalSingletonColumn m hm r false).seed_dangling C n hn h.symm
  · have hinside := canonicalSingletonOwner_mem m hm r
    rw [← h] at hinside
    exact C.point_outside n hinside
  · exact FarField.dangling_ne_positive_column
      (canonicalSingletonColumn m hm r true).seed_dangling C n hn h.symm

end ProteinFolding.Tetrahedral.NearField
