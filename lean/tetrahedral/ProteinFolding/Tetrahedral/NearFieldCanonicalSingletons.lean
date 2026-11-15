import ProteinFolding.Tetrahedral.NearFieldUnitSupport
import ProteinFolding.Tetrahedral.OctahedralZigzags

/-! The three actual standalone PHP units at the vertices opposite the
reserved small face. Their two caps use the two outward big-face directions. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def canonicalSingletonOwner (m : ℕ) (r : Fin 3) : Site :=
  octVertexForFaces m r.castSucc 3

theorem canonicalSingletonIndex_ne (r : Fin 3) : r.castSucc ≠ (3 : Fin 4) := by
  intro h
  have hv := congrArg Fin.val h
  change r.val = 3 at hv
  have hr := r.isLt
  omega

theorem canonicalSingletonOwner_inA (m : ℕ) (r : Fin 3) :
    InASublattice (canonicalSingletonOwner m r).val :=
  octVertices_inA (octVertexForFaces_mem m r.castSucc 3)

theorem canonicalSingletonOwner_mem (m : ℕ) (hm : 1 ≤ m) (r : Fin 3) :
    canonicalSingletonOwner m r ∈ octahedron m :=
  octVertices_subset_octahedron hm (octVertexForFaces_mem m r.castSucc 3)

theorem canonicalSingletonOwner_faces (m : ℕ) (r : Fin 3) :
    tetraCoordinate m (canonicalSingletonOwner m r).val r.castSucc = octRadius m ∧
      tetraCoordinate m (canonicalSingletonOwner m r).val 3 = octRadius m :=
  octVertexForFaces_faces m (canonicalSingletonIndex_ne r)

theorem canonicalSingletonOwner_other_coordinate (m : ℕ) (r d : Fin 3) :
    tetraCoordinate m (canonicalSingletonOwner m r).val d.castSucc =
      if d = r then octRadius m else -octRadius m := by
  fin_cases r <;> fin_cases d
  all_goals dsimp [canonicalSingletonOwner, octVertexForFaces, octVertexSite,
    octVertexCoordinates, octCentre, tetraCoordinate, octRadius]
  all_goals omega

theorem canonicalSingletonOwner_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (canonicalSingletonOwner m) := by
  intro r s heq
  by_contra hne
  have hr := (canonicalSingletonOwner_faces m r).1
  have hs := canonicalSingletonOwner_other_coordinate m s r
  rw [if_neg hne] at hs
  rw [heq] at hr
  dsimp [octRadius] at hr hs
  omega

def canonicalSingletonColumn (m : ℕ) (hm : 1 ≤ m) (r : Fin 3) (last : Bool) : DanglingColumn m where
  owner := canonicalSingletonOwner m r
  dir := if last then 3 else r.castSucc
  owner_mem := canonicalSingletonOwner_mem m hm r
  seed_outside := by
    apply (step_not_mem_octahedron_A m (canonicalSingletonOwner_inA m r)
      (canonicalSingletonOwner_mem m hm r) _).mpr
    cases last
    · exact (canonicalSingletonOwner_faces m r).1
    · exact (canonicalSingletonOwner_faces m r).2

theorem canonicalSingletonColumn_owner (m : ℕ) (hm : 1 ≤ m) (r : Fin 3) (last : Bool) :
    (canonicalSingletonColumn m hm r last).owner = canonicalSingletonOwner m r := rfl

theorem canonicalSingletonCaps_ne (m : ℕ) (hm : 1 ≤ m) (r : Fin 3) :
    (canonicalSingletonColumn m hm r false).seed ≠ (canonicalSingletonColumn m hm r true).seed := by
  intro heq
  change step (canonicalSingletonOwner m r) r.castSucc = step (canonicalSingletonOwner m r) 3 at heq
  have hleft := tetraCoordinate_step_A m (canonicalSingletonOwner_inA m r) r.castSucc 3
  have hright := tetraCoordinate_step_A m (canonicalSingletonOwner_inA m r) 3 3
  simp only [if_neg (canonicalSingletonIndex_ne r).symm] at hleft
  simp only [ite_true] at hright
  rw [heq] at hleft
  omega

def canonicalSingletonPiece (m : ℕ) (hm : 1 ≤ m) (r : Fin 3) : PositionedWord :=
  singletonWordPiece (canonicalSingletonColumn m hm r false) (canonicalSingletonColumn m hm r true)
    rfl (canonicalSingletonCaps_ne m hm r)

theorem canonicalSingletonPiece_word (m : ℕ) (hm : 1 ≤ m) (r : Fin 3) :
    (canonicalSingletonPiece m hm r).word = capWord [Residue.H] := rfl

theorem canonicalSingletonPiece_hSupport (m : ℕ) (hm : 1 ≤ m) (r : Fin 3) :
    hSupport (canonicalSingletonPiece m hm r).word (canonicalSingletonPiece m hm r).fold =
      {canonicalSingletonOwner m r} :=
  cappedSingletonFold_hSupport (canonicalSingletonColumn m hm r false)
    (canonicalSingletonColumn m hm r true) rfl (canonicalSingletonCaps_ne m hm r)

theorem canonicalSingletonPiece_hSupport_subset (m : ℕ) (hm : 1 ≤ m) (r : Fin 3) :
    hSupport (canonicalSingletonPiece m hm r).word (canonicalSingletonPiece m hm r).fold ⊆ octahedron m :=
  singletonWordPiece_hSupport_subset_oct (canonicalSingletonColumn m hm r false)
    (canonicalSingletonColumn m hm r true) rfl (canonicalSingletonCaps_ne m hm r)

theorem canonicalSingletonPiece_sites (m : ℕ) (hm : 1 ≤ m) (r : Fin 3) :
    foldSites (canonicalSingletonPiece m hm r).fold =
      ({(canonicalSingletonColumn m hm r false).seed} ∪ {canonicalSingletonOwner m r}) ∪
        {(canonicalSingletonColumn m hm r true).seed} := by
  change foldSites (cappedSingletonFold (canonicalSingletonColumn m hm r false)
    (canonicalSingletonColumn m hm r true) rfl (canonicalSingletonCaps_ne m hm r)) = _
  rw [cappedSingletonFold, cappedWordFold_sites]
  have hb : foldSites (oneHFold (canonicalSingletonOwner m r)) = {canonicalSingletonOwner m r} := by
    ext x
    simp [foldSites, oneHFold]
  rw [canonicalSingletonColumn_owner, hb]

theorem canonicalSingletonPiece_mem_solid_one (m : ℕ) (hm : 1 ≤ m) (r : Fin 3)
    (i : Fin (canonicalSingletonPiece m hm r).word.length) :
    (canonicalSingletonPiece m hm r).fold.pos i ∈ skinSolid m 1 := by
  have hmem := (mem_foldSites (canonicalSingletonPiece m hm r).fold _).mpr ⟨i, rfl⟩
  rw [canonicalSingletonPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]; exact (canonicalSingletonColumn m hm r false).point_zero_mem_solid_one
  · rw [h]
    have hz : canonicalSingletonOwner m r ∈ skinSolid m 0 := by
      rw [skinSolid_zero]
      exact canonicalSingletonOwner_mem m hm r
    exact skinSolid_mono m (by omega : 0 ≤ 1) hz
  · rw [h]; exact (canonicalSingletonColumn m hm r true).point_zero_mem_solid_one

theorem canonicalSingletonPieces_disjoint (m : ℕ) (hm : 2 ≤ m) (r s : Fin 3) (hne : r ≠ s) :
    Disjoint (foldSites (canonicalSingletonPiece m (by omega) r).fold)
      (foldSites (canonicalSingletonPiece m (by omega) s).fold) := by
  have howner : canonicalSingletonOwner m r ≠ canonicalSingletonOwner m s :=
    fun he => hne (canonicalSingletonOwner_injective m hm he)
  have hcap (a b : Bool) : (canonicalSingletonColumn m (by omega) r a).seed ≠
      (canonicalSingletonColumn m (by omega) s b).seed := by
    apply dangling_caps_ne_of_owner_ne m _ _ _ _
      (canonicalSingletonColumn m (by omega) r a).owner_mem
      (canonicalSingletonColumn m (by omega) s b).owner_mem
      (canonicalSingletonColumn m (by omega) r a).seed_outside
    exact howner
  rw [canonicalSingletonPiece_sites, canonicalSingletonPiece_sites]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [Finset.mem_union, Finset.mem_singleton] at hx hy
  rcases hx with (rfl | rfl) | rfl
  · rcases hy with (h | h) | h
    · exact hcap false false h
    · apply (canonicalSingletonColumn m (by omega) r false).seed_outside
      change (canonicalSingletonColumn m (by omega) r false).seed ∈ octahedron m
      rw [h]; exact canonicalSingletonOwner_mem m (by omega) s
    · exact hcap false true h
  · rcases hy with (h | h) | h
    · apply (canonicalSingletonColumn m (by omega) s false).seed_outside
      change (canonicalSingletonColumn m (by omega) s false).seed ∈ octahedron m
      rw [← h]; exact canonicalSingletonOwner_mem m (by omega) r
    · exact howner h
    · apply (canonicalSingletonColumn m (by omega) s true).seed_outside
      change (canonicalSingletonColumn m (by omega) s true).seed ∈ octahedron m
      rw [← h]; exact canonicalSingletonOwner_mem m (by omega) r
  · rcases hy with (h | h) | h
    · exact hcap true false h
    · apply (canonicalSingletonColumn m (by omega) r true).seed_outside
      change (canonicalSingletonColumn m (by omega) r true).seed ∈ octahedron m
      rw [h]; exact canonicalSingletonOwner_mem m (by omega) s
    · exact hcap true true h

end ProteinFolding.Tetrahedral.NearField
