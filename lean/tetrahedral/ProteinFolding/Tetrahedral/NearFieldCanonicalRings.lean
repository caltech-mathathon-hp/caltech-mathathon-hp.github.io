import ProteinFolding.Tetrahedral.NearFieldCappedRingSeparation
import ProteinFolding.Tetrahedral.NearFieldRingFrameSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingVertices
import ProteinFolding.Tetrahedral.NearFieldFramePieces

/-! The three actual ring words, their six B-owned columns, and the checked
geometric interfaces used by the source-only forward assembly. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private def canonicalRingFrameZero : OctEdgeFrame :=
  ⟨1, 0, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩

private def canonicalRingFrameOne : OctEdgeFrame :=
  ⟨0, 1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩

private def canonicalRingFrameTwo : OctEdgeFrame :=
  ⟨0, 2, 1, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩

def canonicalRingFrame (i : Fin 3) : OctEdgeFrame :=
  if i = 0 then canonicalRingFrameZero
  else if i = 1 then canonicalRingFrameOne else canonicalRingFrameTwo

theorem canonicalRingFrame_small (i : Fin 3) : (canonicalRingFrame i).j = i.castSucc := by
  fin_cases i <;> rfl

theorem canonicalRingFrame_small_ne_reserved (i : Fin 3) : (canonicalRingFrame i).j ≠ 3 := by
  rw [canonicalRingFrame_small]
  intro h
  have hv := congrArg Fin.val h
  change i.val = 3 at hv
  have hi := i.isLt
  omega

theorem canonicalRingFrame_small_injective :
    Function.Injective (fun i : Fin 3 => (canonicalRingFrame i).j) := by
  intro i j h
  change (canonicalRingFrame i).j = (canonicalRingFrame j).j at h
  rw [canonicalRingFrame_small, canonicalRingFrame_small] at h
  exact Fin.castSucc_injective 3 h

theorem ringTerminalSite_mem_oct (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (s : Fin 3) (e : Fin 2) : ringTerminalSite m F s e ∈ octahedron m :=
  edgeDimerHsites_subset_oct (by omega : 1 ≤ m) (ringSideFrame F s) 1 (m - 3)
    (by omega) (ringTerminalSite_mem m hm F s e)

theorem ringTerminalSite_small_coordinate (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (s : Fin 3) (e : Fin 2) :
    tetraCoordinate m (ringTerminalSite m F s e).val F.j = -(2 * (m : ℤ) - 1) := by
  fin_cases e
  · change tetraCoordinate m (octEdgeZigzag m (ringSideFrame F s) 1).val F.j = _
    have h := (octEdgeZigzag_odd (by omega : 1 ≤ m) (ringSideFrame F s) 0).2.2.1
    change tetraCoordinate m (octEdgeZigzag m (ringSideFrame F s) 1).val
      (ringSideFrame F s).j = -octRadius m - 1 at h
    rw [ringSideFrame_small] at h
    dsimp [octRadius] at h
    omega
  · change tetraCoordinate m (octEdgeZigzag m (ringSideFrame F s) (2 * m - 5)).val F.j = _
    rw [ringSide_last_eq_reverse_three m hm]
    have h := (octEdgeZigzag_odd (by omega : 1 ≤ m)
      (bulkReverseEdgeFrame (ringSideFrame F s)) 1).2.2.1
    change tetraCoordinate m (octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F s)) 3).val
      (ringSideFrame F s).j = -octRadius m - 1 at h
    rw [ringSideFrame_small] at h
    dsimp [octRadius] at h
    omega

def ringTerminalColumn (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (s : Fin 3) (e : Fin 2) : DanglingColumn m where
  owner := ringTerminalSite m F s e
  dir := F.j
  owner_mem := ringTerminalSite_mem_oct m hm F s e
  seed_outside := (step_not_mem_octahedron_B m (ringTerminalSite_inB m hm F s e)
    (ringTerminalSite_mem_oct m hm F s e) F.j).mpr (ringTerminalSite_small_coordinate m hm F s e)

def canonicalRingColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2) :
    DanglingColumn p.side :=
  ringTerminalColumn p.side (by have h := p.side_ge; omega) (canonicalRingFrame i)
    (if e = 0 then 0 else 2) e

theorem canonicalRingColumn_first_owner (p : ConstructionParameters) (i : Fin 3) :
    (canonicalRingColumn p i 0).owner = ringTerminalSite p.side (canonicalRingFrame i) 0 0 := rfl

theorem canonicalRingColumn_last_eq (p : ConstructionParameters) (i : Fin 3) :
    canonicalRingColumn p i 1 =
      ringTerminalColumn p.side (by have h := p.side_ge; omega) (canonicalRingFrame i) 2 1 := by
  unfold canonicalRingColumn
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

theorem canonicalRingColumn_last_owner (p : ConstructionParameters) (i : Fin 3) :
    (canonicalRingColumn p i 1).owner = ringTerminalSite p.side (canonicalRingFrame i) 2 1 :=
  congrArg (fun C : DanglingColumn p.side => C.owner) (canonicalRingColumn_last_eq p i)

theorem canonicalRingColumn_dir (p : ConstructionParameters) (i : Fin 3) (e : Fin 2) :
    (canonicalRingColumn p i e).dir = (canonicalRingFrame i).j := rfl

theorem canonicalRingColumn_dir_index (p : ConstructionParameters) (i : Fin 3) (e : Fin 2) :
    (canonicalRingColumn p i e).dir = i.castSucc :=
  (canonicalRingColumn_dir p i e).trans (canonicalRingFrame_small i)

theorem canonicalRingColumn_owner_inB (p : ConstructionParameters) (i : Fin 3) (e : Fin 2) :
    InBSublattice (canonicalRingColumn p i e).owner.val :=
  ringTerminalSite_inB p.side (by have h := p.side_ge; omega) (canonicalRingFrame i)
    (if e = 0 then 0 else 2) e

theorem canonicalRingColumn_seed_inA (p : ConstructionParameters) (i : Fin 3) (e : Fin 2) :
    InASublattice (canonicalRingColumn p i e).seed.val :=
  step_in_A (canonicalRingColumn_owner_inB p i e) (canonicalRingColumn p i e).dir

theorem canonicalRingColumn_owner_deleted (p : ConstructionParameters) (i : Fin 3) (e : Fin 2) :
    (canonicalRingColumn p i e).owner ∈ bulkDeletedEdges p.side :=
  ringTerminalSite_deleted p.side (by have h := p.side_ge; omega) (canonicalRingFrame i)
    (if e = 0 then 0 else 2) e

theorem canonicalRingColumn_owner_alternative (p : ConstructionParameters) (i : Fin 3) (e : Fin 2) :
    (canonicalRingColumn p i e).owner = ringTerminalSite p.side (canonicalRingFrame i) 0 0 ∨
      (canonicalRingColumn p i e).owner = ringTerminalSite p.side (canonicalRingFrame i) 2 1 := by
  fin_cases e
  · exact Or.inl (canonicalRingColumn_first_owner p i)
  · exact Or.inr (canonicalRingColumn_last_owner p i)

theorem canonicalRingColumn_owner_injective (p : ConstructionParameters) :
    Function.Injective (fun ie : Fin 3 × Fin 2 => (canonicalRingColumn p ie.1 ie.2).owner) := by
  rintro ⟨i, e⟩ ⟨j, e'⟩ heq
  change ringTerminalSite p.side (canonicalRingFrame i) (if e = 0 then 0 else 2) e =
    ringTerminalSite p.side (canonicalRingFrame j) (if e' = 0 then 0 else 2) e' at heq
  have hij : i = j := by
    by_contra hne
    have hj : (canonicalRingFrame i).j ≠ (canonicalRingFrame j).j :=
      fun h => hne (canonicalRingFrame_small_injective h)
    exact ringTerminalSite_ne_small_faces p.side (by have h := p.side_ge; omega)
      (canonicalRingFrame i) (canonicalRingFrame j) hj _ _ e e' heq
  subst j
  have hp := ringTerminalSite_injective p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i)
    (a₁ := ((if e = 0 then 0 else 2), e))
    (a₂ := ((if e' = 0 then 0 else 2), e')) heq
  have hsnd := congrArg (fun a : Fin 3 × Fin 2 => a.2) hp
  exact Prod.ext rfl hsnd

theorem canonicalRingColumn_seed_injective (p : ConstructionParameters) :
    Function.Injective (fun ie : Fin 3 × Fin 2 => (canonicalRingColumn p ie.1 ie.2).seed) := by
  intro ie je hseed
  apply canonicalRingColumn_owner_injective p
  by_contra howner
  exact dangling_caps_ne_of_owner_ne p.side
    (canonicalRingColumn p ie.1 ie.2).owner (canonicalRingColumn p je.1 je.2).owner
    (canonicalRingColumn p ie.1 ie.2).dir (canonicalRingColumn p je.1 je.2).dir
    (canonicalRingColumn p ie.1 ie.2).owner_mem (canonicalRingColumn p je.1 je.2).owner_mem
    (canonicalRingColumn p ie.1 ie.2).seed_outside howner hseed

noncomputable def canonicalRingWordPiece (p : ConstructionParameters) (i : Fin 3) : PositionedWord :=
  ringWordPiece p.side (by have h := p.side_ge; omega) p.side_even (canonicalRingFrame i)
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)

noncomputable def canonicalRingPieces (p : ConstructionParameters) : List PositionedWord :=
  [canonicalRingWordPiece p 0, canonicalRingWordPiece p 1, canonicalRingWordPiece p 2]

theorem canonicalRingWordPiece_word (p : ConstructionParameters) (i : Fin 3) :
    (canonicalRingWordPiece p i).word = capWord (dimerChain (3 * (p.side - 2))) := rfl

private theorem ringWordPiece_first_projection (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1) :
    (ringWordPiece m hm heven F C D hC hD).first = C.seed := rfl

private theorem ringWordPiece_last_projection (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1) :
    (ringWordPiece m hm heven F C D hC hD).last = D.seed := rfl

theorem canonicalRingWordPiece_first (p : ConstructionParameters) (i : Fin 3) :
    (canonicalRingWordPiece p i).first = (canonicalRingColumn p i 0).seed :=
  ringWordPiece_first_projection p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)

theorem canonicalRingWordPiece_last (p : ConstructionParameters) (i : Fin 3) :
    (canonicalRingWordPiece p i).last = (canonicalRingColumn p i 1).seed :=
  ringWordPiece_last_projection p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)

theorem canonicalRingPieces_words (p : ConstructionParameters) :
    (canonicalRingPieces p).map PositionedWord.word =
      List.replicate 3 (capWord (dimerChain (3 * (p.side - 2)))) := rfl

theorem canonicalRingPieces_length (p : ConstructionParameters) : (canonicalRingPieces p).length = 3 := rfl

theorem canonicalRingWordPiece_hSupport (p : ConstructionParameters) (i : Fin 3) :
    hSupport (canonicalRingWordPiece p i).word (canonicalRingWordPiece p i).fold =
      ringHsites p.side (canonicalRingFrame i) :=
  cappedRingFold_hSupport p.side (by have h := p.side_ge; omega) p.side_even (canonicalRingFrame i)
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)

theorem canonicalRingWordPiece_hSupport_subset_oct (p : ConstructionParameters) (i : Fin 3) :
    hSupport (canonicalRingWordPiece p i).word (canonicalRingWordPiece p i).fold ⊆ octahedron p.side :=
  ringWordPiece_hSupport_subset p.side (by have h := p.side_ge; omega) p.side_even (canonicalRingFrame i)
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)

theorem canonicalRingWordPiece_mem_solid_one (p : ConstructionParameters) (i : Fin 3)
    (r : Fin (canonicalRingWordPiece p i).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ∈ skinSolid p.side 1 :=
  ringWordPiece_mem_solid_one p.side (by have h := p.side_ge; omega) p.side_even (canonicalRingFrame i)
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i) r

theorem canonicalRingWordPieces_disjoint (p : ConstructionParameters) (i j : Fin 3) (hne : i ≠ j) :
    Disjoint (foldSites (canonicalRingWordPiece p i).fold) (foldSites (canonicalRingWordPiece p j).fold) :=
  cappedRingFolds_disjoint_small_faces p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) (canonicalRingFrame j)
    (fun h => hne (canonicalRingFrame_small_injective h))
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn p j 0) (canonicalRingColumn p j 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)
    (canonicalRingColumn_first_owner p j) (canonicalRingColumn_last_owner p j)

theorem canonicalRingPieces_pairwise (p : ConstructionParameters) :
    (canonicalRingPieces p).Pairwise (fun a b => Disjoint (foldSites a.fold) (foldSites b.fold)) := by
  refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact canonicalRingWordPieces_disjoint p 0 1 (by decide)
    · exact canonicalRingWordPieces_disjoint p 0 2 (by decide)
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    exact canonicalRingWordPieces_disjoint p 1 2 (by decide)
  · intro a ha
    cases ha

theorem canonicalRingColumns_points_ne (p : ConstructionParameters) (i j : Fin 3) (e f : Fin 2)
    (hne : (i, e) ≠ (j, f)) (n r : ℕ) :
    (canonicalRingColumn p i e).point n ≠ (canonicalRingColumn p j f).point r := by
  have hseed : (canonicalRingColumn p i e).seed ≠ (canonicalRingColumn p j f).seed := by
    intro h
    exact hne (canonicalRingColumn_seed_injective p (a₁ := (i, e)) (a₂ := (j, f)) h)
  exact DanglingColumn.points_ne_of_seed_ne hseed n r

theorem canonicalRingColumn_point_ne_seed (p : ConstructionParameters) (i j : Fin 3) (e f : Fin 2)
    (n : ℕ) (hn : 0 < n) :
    (canonicalRingColumn p i e).point n ≠ (canonicalRingColumn p j f).seed := by
  by_cases hij : (i, e) = (j, f)
  · have hcol : canonicalRingColumn p i e = canonicalRingColumn p j f :=
      congrArg (fun ie : Fin 3 × Fin 2 => canonicalRingColumn p ie.1 ie.2) hij
    intro h
    rw [hcol] at h
    change (canonicalRingColumn p j f).point n = (canonicalRingColumn p j f).point 0 at h
    have hz := (canonicalRingColumn p j f).point_injective h
    omega
  · exact canonicalRingColumns_points_ne p i j e f hij n 0

theorem canonicalRingBody_ne_column (p : ConstructionParameters) (i j : Fin 3) (e : Fin 2)
    (r : Fin (dimerChain (3 * (p.side - 2))).length) (n : ℕ) :
    (ringFold p.side (by have h := p.side_ge; omega) p.side_even (canonicalRingFrame i)).pos r ≠
      (canonicalRingColumn p j e).point n := by
  by_cases hij : i = j
  · subst j
    fin_cases e
    · exact ringFold_ne_first_column p.side (by have h := p.side_ge; omega) p.side_even
        (canonicalRingFrame i) (canonicalRingColumn p i 0) (canonicalRingColumn_first_owner p i) r n
    · exact ringFold_ne_last_column p.side (by have h := p.side_ge; omega) p.side_even
        (canonicalRingFrame i) (canonicalRingColumn p i 1) (canonicalRingColumn_last_owner p i) r n
  · exact ringFold_ne_foreign_terminal_column p.side (by have h := p.side_ge; omega) p.side_even
      (canonicalRingFrame i) (canonicalRingFrame j)
      (fun h => hij (canonicalRingFrame_small_injective h)) (canonicalRingColumn p j e)
      (canonicalRingColumn_owner_alternative p j e) r n

private theorem canonicalRingWordPiece_ne_column_aux (p : ConstructionParameters) (i j : Fin 3)
    (e : Fin 2) (r : Fin (canonicalRingWordPiece p i).word.length) (n : ℕ)
    (hfirst : (canonicalRingColumn p j e).point n ≠ (canonicalRingColumn p i 0).seed)
    (hlast : (canonicalRingColumn p j e).point n ≠ (canonicalRingColumn p i 1).seed) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (canonicalRingColumn p j e).point n := by
  change (cappedRingFold p.side (by have h := p.side_ge; omega) p.side_even (canonicalRingFrame i)
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)).pos r ≠ _
  intro heq
  have hmem := (mem_foldSites (cappedRingFold p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)) _).mpr ⟨r, heq⟩
  rw [cappedRingFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact hfirst h
  · obtain ⟨s, hs⟩ := (mem_foldSites _ _).mp h
    exact canonicalRingBody_ne_column p i j e s n hs
  · exact hlast h

theorem canonicalRingWordPiece_ne_column_pos (p : ConstructionParameters) (i j : Fin 3) (e : Fin 2)
    (r : Fin (canonicalRingWordPiece p i).word.length) (n : ℕ) (hn : 0 < n) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (canonicalRingColumn p j e).point n :=
  canonicalRingWordPiece_ne_column_aux p i j e r n
    (canonicalRingColumn_point_ne_seed p j i e 0 n hn)
    (canonicalRingColumn_point_ne_seed p j i e 1 n hn)

theorem canonicalRingWordPiece_ne_foreign_column (p : ConstructionParameters) (i j : Fin 3)
    (hij : i ≠ j) (e : Fin 2) (r : Fin (canonicalRingWordPiece p i).word.length) (n : ℕ) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (canonicalRingColumn p j e).point n := by
  have hpair (f : Fin 2) : (j, e) ≠ (i, f) := by
    intro h
    exact hij (congrArg Prod.fst h).symm
  exact canonicalRingWordPiece_ne_column_aux p i j e r n
    (canonicalRingColumns_points_ne p j i e 0 (hpair 0) n 0)
    (canonicalRingColumns_points_ne p j i e 1 (hpair 1) n 0)

theorem canonicalRingWordPiece_not_mem_bulkInterior (p : ConstructionParameters) (i : Fin 3)
    (r : Fin (canonicalRingWordPiece p i).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ∉ bulkInterior p.side :=
  cappedRingFold_not_mem_bulkInterior p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i) r

theorem canonicalRingWordPiece_ne_bulkEndColumn (p : ConstructionParameters) (i : Fin 3)
    (E : DanglingColumn p.side) (hE : E.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side E.owner).card = 1)
    (r : Fin (canonicalRingWordPiece p i).word.length) (n : ℕ) :
    (canonicalRingWordPiece p i).fold.pos r ≠ E.point n :=
  cappedRingFold_ne_bulkEndColumn p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i) E hE hend r n

theorem canonicalRingWordPiece_ne_vertexColumn (p : ConstructionParameters) (i : Fin 3)
    (E : DanglingColumn p.side) (a : Fin 3) (positive : Bool)
    (hE : E.owner = octVertexSite p.side a positive)
    (r : Fin (canonicalRingWordPiece p i).word.length) (n : ℕ) :
    (canonicalRingWordPiece p i).fold.pos r ≠ E.point n :=
  cappedRingFold_ne_vertexColumn p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i) E a positive hE r n

theorem canonicalRingWordPiece_ne_vertexSite (p : ConstructionParameters) (i : Fin 3)
    (a : Fin 3) (positive : Bool) (r : Fin (canonicalRingWordPiece p i).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ octVertexSite p.side a positive :=
  cappedRingFold_ne_vertexSite p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i) a positive r

theorem canonicalRingWordPiece_ne_vertexForFaces (p : ConstructionParameters) (i : Fin 3)
    (k b : Fin 4) (r : Fin (canonicalRingWordPiece p i).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ octVertexForFaces p.side k b := by
  obtain ⟨ap, _, hap⟩ := Finset.mem_image.mp (octVertexForFaces_mem p.side k b)
  rw [← hap]
  exact canonicalRingWordPiece_ne_vertexSite p i ap.1 ap.2 r

theorem canonicalRingWordPiece_ne_vertexForFacesColumn (p : ConstructionParameters) (i : Fin 3)
    (E : DanglingColumn p.side) (k b : Fin 4) (hE : E.owner = octVertexForFaces p.side k b)
    (r : Fin (canonicalRingWordPiece p i).word.length) (n : ℕ) :
    (canonicalRingWordPiece p i).fold.pos r ≠ E.point n := by
  obtain ⟨ap, _, hap⟩ := Finset.mem_image.mp (octVertexForFaces_mem p.side k b)
  exact canonicalRingWordPiece_ne_vertexColumn p i E ap.1 ap.2 (hE.trans hap.symm) r n

theorem canonicalRingWordPiece_ne_frameBorrowPoint (p : ConstructionParameters) (i : Fin 3)
    (a : ℕ) (ha : a % 2 = 0) (hlo : 2 ≤ a) (hhi : (a : ℤ) + 2 ≤ octRadius p.side)
    (mode : Bool) (hnear : mode = true ∨ 4 ≤ a)
    (hfar : mode = false ∨ (a : ℤ) + 4 ≤ octRadius p.side)
    (r : Fin (canonicalRingWordPiece p i).word.length) (n : ℕ) :
    (canonicalRingWordPiece p i).fold.pos r ≠
      frameBorrowPoint (m := p.side) (by have h := p.side_ge; omega) a ha hlo hhi mode n :=
  cappedRingFold_ne_frameBorrowPoint p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) (canonicalRingFrame_small_ne_reserved i)
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)
    a ha hlo hhi mode hnear hfar r n

theorem canonicalRingColumn_ne_AColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (E : DanglingColumn p.side) (hEA : InASublattice E.owner.val) (n r : ℕ) :
    (canonicalRingColumn p i e).point n ≠ E.point r :=
  (DanglingColumn.points_ne_of_owner_colours E (canonicalRingColumn p i e) hEA
    (canonicalRingColumn_owner_inB p i e) r n).symm

theorem canonicalRingColumn_ne_bulkColumn (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (E : DanglingColumn p.side) (hE : E.owner ∈ bulkInterior p.side) (n r : ℕ) :
    (canonicalRingColumn p i e).point n ≠ E.point r :=
  (bulkColumn_ne_edgeColumn E (canonicalRingColumn p i e) hE
    (canonicalRingColumn_owner_deleted p i e) r n).symm

theorem canonicalRingWordPiece_ne_frameLink (p : ConstructionParameters) (i : Fin 3)
    (j : FrameLinkIndex p) (r : Fin (canonicalRingWordPiece p i).word.length)
    (s : Fin (nearFrameLength (frameLinkKind j) - 2)) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (frameLinkFold p j).pos s :=
  cappedRingFold_ne_framePFold p.side (frameLinkParameter j) (by have h := p.side_ge; omega)
    p.side_even (canonicalRingFrame i) (canonicalRingFrame_small_ne_reserved i)
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)
    (frameLinkKind j) (frameLinkParameter_odd p j) (frameLinkParameter_ge p j)
    (frameLinkParameter_room p j) r s

private theorem frameHRunFold_reserved_small_coordinate (p : ConstructionParameters) (j : FrameHRunIndex p)
    (s : Fin (frameHRunWord p j).length) :
    tetraCoordinate p.side ((frameHRunFold p j).pos s).val 3 ≤ -octRadius p.side := by
  have hmem := (mem_foldSites (frameHRunFold p j) _).mpr ⟨s, rfl⟩
  rw [frameHRunFold_sites] at hmem
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hmem
  have hj : (frameHRunData p j).frame.j = 3 := by
    rw [frameHRun_frame]
    split_ifs <;> rfl
  have h := ringEdgePoint_small_coordinate p.side (by have h := p.side_ge; omega)
    (frameHRunData p j).frame ((frameHRunData p j).base + t)
  rw [hj, ht] at h
  exact h

theorem canonicalRingWordPiece_ne_frameHRun (p : ConstructionParameters) (i : Fin 3)
    (j : FrameHRunIndex p) (r : Fin (canonicalRingWordPiece p i).word.length)
    (s : Fin (frameHRunWord p j).length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (frameHRunFold p j).pos s :=
  cappedRingFold_ne_reserved_oct_site p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame i) (canonicalRingFrame_small_ne_reserved i)
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)
    ((frameHRunFold p j).pos s) (frameHRunFold_mem_oct p j s)
    (frameHRunFold_reserved_small_coordinate p j s) r

theorem canonicalRingWordPiece_ne_frameCorePiece (p : ConstructionParameters) (i : Fin 3)
    (j : FrameCoreIndex p) (r : Fin (canonicalRingWordPiece p i).word.length)
    (s : Fin (frameCorePiece p j).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (frameCorePiece p j).fold.pos s := by
  rcases j with j | j
  · exact canonicalRingWordPiece_ne_frameHRun p i j r s
  · change (canonicalRingWordPiece p i).fold.pos r ≠ (frameLinkWordFold p j).pos s
    rw [frameLinkWordFold_pos]
    exact canonicalRingWordPiece_ne_frameLink p i j r _

theorem canonicalRingWordPiece_frameCorePiece_disjoint (p : ConstructionParameters) (i : Fin 3)
    (j : FrameCoreIndex p) :
    Disjoint (foldSites (canonicalRingWordPiece p i).fold) (foldSites (frameCorePiece p j).fold) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalRingWordPiece_ne_frameCorePiece p i j)

theorem canonicalRingColumn_ne_frameLink (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (j : FrameLinkIndex p) (n : ℕ) (s : Fin (nearFrameLength (frameLinkKind j) - 2)) :
    (canonicalRingColumn p i e).point n ≠ (frameLinkFold p j).pos s :=
  ringTerminalColumn_ne_framePFold p.side (frameLinkParameter j) (by have h := p.side_ge; omega)
    (canonicalRingFrame i) (canonicalRingFrame_small_ne_reserved i) (if e = 0 then 0 else 2) e
    (canonicalRingColumn p i e) rfl (frameLinkKind j) (frameLinkParameter_odd p j)
    (frameLinkParameter_ge p j) (frameLinkParameter_room p j) n s

theorem canonicalRingColumn_ne_frameCorePiece (p : ConstructionParameters) (i : Fin 3) (e : Fin 2)
    (j : FrameCoreIndex p) (n : ℕ) (s : Fin (frameCorePiece p j).word.length) :
    (canonicalRingColumn p i e).point n ≠ (frameCorePiece p j).fold.pos s := by
  rcases j with j | j
  · intro heq
    dsimp only [frameCorePiece, frameHRunPiece] at s heq
    have hmem := frameHRunFold_mem_oct p j s
    rw [← heq] at hmem
    exact (canonicalRingColumn p i e).point_outside n hmem
  · change (canonicalRingColumn p i e).point n ≠ (frameLinkWordFold p j).pos s
    rw [frameLinkWordFold_pos]
    exact canonicalRingColumn_ne_frameLink p i e j n _

end ProteinFolding.Tetrahedral.NearField
