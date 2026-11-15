import ProteinFolding.Cubic.Proofs.PackingGeometryFrameIndices
import ProteinFolding.Cubic.Proofs.PackingGeometryWallsWord

/-! Literal E/F joins contain H-P-P-H across their two P endpoints. In an
arbitrary perfect fold those endpoint H residues are adjacent by the proved
compression lemma. The surrounding words and their embedding are unrestricted.
Both walls in the actual wall unit admit these literal decompositions. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

theorem get_cast_word {S T : Sequence} (h : S = T) (i : Fin T.length) :
    S.get (Fin.cast (congrArg List.length h).symm i) = T.get i := by
  cases h
  rfl

def wallSegment (pre post : Sequence) (s d t : ℕ) : Sequence :=
  pre ++ edgeWord s ++ faceWord d ++ edgeWord t ++ post

def wallLeftPost (post : Sequence) (d t : ℕ) : Sequence := faceWord d ++ edgeWord t ++ post
def wallMiddlePre (pre : Sequence) (s : ℕ) : Sequence := pre ++ edgeWord s
def wallMiddlePost (post : Sequence) (t : ℕ) : Sequence := edgeWord t ++ post
def wallRightPre (pre : Sequence) (s d : ℕ) : Sequence := pre ++ edgeWord s ++ faceWord d

theorem wallSegment_left (pre post : Sequence) (s d t : ℕ) :
    wallSegment pre post s d t = pre ++ edgeWord s ++ wallLeftPost post d t := by
  simp [wallSegment, wallLeftPost, List.append_assoc]

theorem wallSegment_middle (pre post : Sequence) (s d t : ℕ) :
    wallSegment pre post s d t = wallMiddlePre pre s ++ faceWord d ++ wallMiddlePost post t := by
  simp [wallSegment, wallMiddlePre, wallMiddlePost, List.append_assoc]

theorem wallSegment_right (pre post : Sequence) (s d t : ℕ) :
    wallSegment pre post s d t = wallRightPre pre s d ++ edgeWord t ++ post := rfl

def wallLeftAnchor (pre post : Sequence) (s d t : ℕ) (hs : 0 < s)
    (f : Fold cubicLattice (wallSegment pre post s d t).length) : Site :=
  edgeHPath pre (wallLeftPost post d t) s (foldOnWord (wallSegment_left pre post s d t) f)
    ⟨s - 1, by omega⟩

def wallRightAnchor (pre post : Sequence) (s d t : ℕ) (ht : 0 < t)
    (f : Fold cubicLattice (wallSegment pre post s d t).length) : Site :=
  edgeHPath (wallRightPre pre s d) post t (foldOnWord (wallSegment_right pre post s d t) f) ⟨0, ht⟩

def wallMiddlePath (pre post : Sequence) (s d t : ℕ) (heven : 2 ∣ d)
    (f : Fold cubicLattice (wallSegment pre post s d t).length) : Fin d → Site :=
  faceWallPath (wallMiddlePre pre s) (wallMiddlePost post t) d heven
    (foldOnWord (wallSegment_middle pre post s d t) f)

theorem wallLeftJoin_adjacent (pre post : Sequence) (s d t : ℕ) (hs : 0 < s)
    (hd : 0 < d) (heven : 2 ∣ d)
    (f : Fold cubicLattice (wallSegment pre post s d t).length) (a : Site) (n : ℕ)
    (hpack : hydrophobicSites (wallSegment pre post s d t) f = cube a n) :
    cubicLattice.Adj (wallLeftAnchor pre post s d t hs f)
      (wallMiddlePath pre post s d t heven f ⟨0, hd⟩) := by
  have hhalf : 0 < d / 2 := by have he := Nat.mul_div_cancel' heven; omega
  let last : Fin s := ⟨s - 1, by omega⟩
  let first : Fin (d / 2) := ⟨0, hhalf⟩
  let i := Fin.cast (congrArg List.length (wallSegment_left pre post s d t)).symm
    (edgeIndex pre (wallLeftPost post d t) s last 1)
  let j := Fin.cast (congrArg List.length (wallSegment_left pre post s d t)).symm
    (edgeIndex pre (wallLeftPost post d t) s last 2)
  let k := Fin.cast (congrArg List.length (wallSegment_middle pre post s d t)).symm
    (faceIndex (wallMiddlePre pre s) (wallMiddlePost post t) d first 0)
  let l := Fin.cast (congrArg List.length (wallSegment_middle pre post s d t)).symm
    (faceIndex (wallMiddlePre pre s) (wallMiddlePost post t) d first 1)
  have ha := hpph_adjacent f a n hpack i j k l
    (by dsimp [i, j, edgeIndex])
    (by dsimp [j, k, edgeIndex, faceIndex, last, first, wallMiddlePre]
        simp only [List.length_append, edgeWord_length]; omega)
    (by dsimp [k, l, faceIndex])
    (by exact (get_cast_word (wallSegment_left pre post s d t)
        (edgeIndex pre (wallLeftPost post d t) s last 1)).trans (by rw [edgeIndex_residue]; rfl))
    (by exact (get_cast_word (wallSegment_left pre post s d t)
        (edgeIndex pre (wallLeftPost post d t) s last 2)).trans (by rw [edgeIndex_residue]; rfl))
    (by exact (get_cast_word (wallSegment_middle pre post s d t)
        (faceIndex (wallMiddlePre pre s) (wallMiddlePost post t) d first 0)).trans (by rw [faceIndex_residue]; rfl))
    (by exact (get_cast_word (wallSegment_middle pre post s d t)
        (faceIndex (wallMiddlePre pre s) (wallMiddlePost post t) d first 1)).trans (by rw [faceIndex_residue]; rfl))
  simpa only [wallLeftAnchor, wallMiddlePath, faceWallPath, edgeHPath, faceHPath,
    foldOnWord_pos, faceBlock, faceHOffset, Nat.zero_div, Nat.zero_mod, Nat.zero_add,
    i, l, last, first] using ha

theorem wallRightJoin_adjacent (pre post : Sequence) (s d t : ℕ) (ht : 0 < t)
    (hd : 0 < d) (heven : 2 ∣ d)
    (f : Fold cubicLattice (wallSegment pre post s d t).length) (a : Site) (n : ℕ)
    (hpack : hydrophobicSites (wallSegment pre post s d t) f = cube a n) :
    cubicLattice.Adj (wallMiddlePath pre post s d t heven f ⟨d - 1, by omega⟩)
      (wallRightAnchor pre post s d t ht f) := by
  have he := Nat.mul_div_cancel' heven
  have hhalf : 0 < d / 2 := by omega
  have hlastDiv : (d - 1) / 2 = d / 2 - 1 := by omega
  have hlastMod : (d - 1) % 2 = 1 := by omega
  let last : Fin (d / 2) := ⟨d / 2 - 1, by omega⟩
  let first : Fin t := ⟨0, ht⟩
  let i := Fin.cast (congrArg List.length (wallSegment_middle pre post s d t)).symm
    (faceIndex (wallMiddlePre pre s) (wallMiddlePost post t) d last 2)
  let j := Fin.cast (congrArg List.length (wallSegment_middle pre post s d t)).symm
    (faceIndex (wallMiddlePre pre s) (wallMiddlePost post t) d last 3)
  let k := Fin.cast (congrArg List.length (wallSegment_right pre post s d t)).symm
    (edgeIndex (wallRightPre pre s d) post t first 0)
  let l := Fin.cast (congrArg List.length (wallSegment_right pre post s d t)).symm
    (edgeIndex (wallRightPre pre s d) post t first 1)
  have ha := hpph_adjacent f a n hpack i j k l
    (by dsimp [i, j, faceIndex])
    (by dsimp [j, k, faceIndex, edgeIndex, last, first, wallRightPre, wallMiddlePre]
        simp only [List.length_append, faceWord_length d heven]
        omega)
    (by dsimp [k, l, edgeIndex])
    (by exact (get_cast_word (wallSegment_middle pre post s d t)
        (faceIndex (wallMiddlePre pre s) (wallMiddlePost post t) d last 2)).trans (by rw [faceIndex_residue]; rfl))
    (by exact (get_cast_word (wallSegment_middle pre post s d t)
        (faceIndex (wallMiddlePre pre s) (wallMiddlePost post t) d last 3)).trans (by rw [faceIndex_residue]; rfl))
    (by exact (get_cast_word (wallSegment_right pre post s d t)
        (edgeIndex (wallRightPre pre s d) post t first 0)).trans (by rw [edgeIndex_residue]; rfl))
    (by exact (get_cast_word (wallSegment_right pre post s d t)
        (edgeIndex (wallRightPre pre s d) post t first 1)).trans (by rw [edgeIndex_residue]; rfl))
  simpa only [wallRightAnchor, wallMiddlePath, faceWallPath, edgeHPath, faceHPath,
    foldOnWord_pos, faceBlock, faceHOffset, hlastDiv, hlastMod, Nat.reduceAdd,
    i, l, last, first] using ha

theorem wallUnit_first_segment (pre post : Sequence) (q Q : ℕ) :
    pre ++ wallUnit q Q ++ post =
      wallSegment pre (faceWord (depth q Q) ++ edgeWord (alpha Q) ++ post)
        (alpha Q) (depth q Q) (beta Q) := by
  simp [wallUnit, wallSegment, List.append_assoc]

theorem wallUnit_second_segment (pre post : Sequence) (q Q : ℕ) :
    pre ++ wallUnit q Q ++ post =
      wallSegment (pre ++ edgeWord (alpha Q) ++ faceWord (depth q Q)) post
        (beta Q) (depth q Q) (alpha Q) := by
  simp [wallUnit, wallSegment, List.append_assoc]

/-- The literal three-block wall has the generic straight-row conclusion;
the boundary-adjacency hypotheses have been discharged by its H-P-P-H joins. -/
theorem wallSegment_straight (pre post : Sequence) (s d t : ℕ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 < t) (heven : 2 ∣ d)
    (f : Fold cubicLattice (wallSegment pre post s d t).length) (a : Site)
    (hpack : hydrophobicSites (wallSegment pre post s d t) f = cube a (d + 2))
    (e g : CubeEdge) (r u : Fin d) (hnc : NoCommonCorner e g)
    (hleft : wallLeftAnchor pre post s d t hs f = openEdgePoint a d e r)
    (hright : wallRightAnchor pre post s d t ht f = openEdgePoint a d g u) :
    ∃ axis : Fin 3, axis ≠ e.axis ∧ axis ≠ g.axis ∧
      ((∀ i : Fin d, wallMiddlePath pre post s d t heven f i =
        Function.update (openEdgePoint a d e r) axis
          (openEdgePoint a d e r axis + ((i.val + 1 : ℕ) : ℤ))) ∨
       (∀ i : Fin d, wallMiddlePath pre post s d t heven f i =
        Function.update (openEdgePoint a d e r) axis
          (openEdgePoint a d e r axis - ((i.val + 1 : ℕ) : ℤ)))) := by
  have hfirst := wallLeftJoin_adjacent pre post s d t hs hd heven f a (d + 2) hpack
  have hlast := wallRightJoin_adjacent pre post s d t ht hd heven f a (d + 2) hpack
  rw [hleft] at hfirst
  rw [hright] at hlast
  have hpack' : hydrophobicSites (wallMiddlePre pre s ++ faceWord d ++ wallMiddlePost post t)
      (foldOnWord (wallSegment_middle pre post s d t) f) = cube a (d + 2) := by
    rw [foldOnWord_hydrophobicSites]
    exact hpack
  exact faceWord_wall_straight (wallMiddlePre pre s) (wallMiddlePost post t) d hd heven
    (foldOnWord (wallSegment_middle pre post s d t) f) a hpack' e g r u hnc hfirst hlast

theorem wallSegment_rails_parallel (pre post : Sequence) (s d t : ℕ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 < t) (heven : 2 ∣ d)
    (f : Fold cubicLattice (wallSegment pre post s d t).length) (a : Site)
    (hpack : hydrophobicSites (wallSegment pre post s d t) f = cube a (d + 2))
    (e g : CubeEdge) (r u : Fin d) (hnc : NoCommonCorner e g)
    (hleft : wallLeftAnchor pre post s d t hs f = openEdgePoint a d e r)
    (hright : wallRightAnchor pre post s d t ht f = openEdgePoint a d g u)
    (hnoedge : ∀ i, ¬ EdgeSkeleton a (d + 2) (wallMiddlePath pre post s d t heven f i)) :
    e.axis = g.axis := by
  have hfirst := wallLeftJoin_adjacent pre post s d t hs hd heven f a (d + 2) hpack
  have hlast := wallRightJoin_adjacent pre post s d t ht hd heven f a (d + 2) hpack
  rw [hleft] at hfirst
  rw [hright] at hlast
  have hpack' : hydrophobicSites (wallMiddlePre pre s ++ faceWord d ++ wallMiddlePost post t)
      (foldOnWord (wallSegment_middle pre post s d t) f) = cube a (d + 2) := by
    rw [foldOnWord_hydrophobicSites]
    exact hpack
  exact faceWord_rails_parallel (wallMiddlePre pre s) (wallMiddlePost post t) d hd heven
    (foldOnWord (wallSegment_middle pre post s d t) f) a hpack' e g r u hnc hnoedge hfirst hlast

end ProteinFolding.CubicPackingGeometry
