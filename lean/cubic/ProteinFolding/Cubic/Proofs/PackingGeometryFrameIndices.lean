import ProteinFolding.Cubic.Proofs.PackingGeometryRails
import ProteinFolding.Cubic.Proofs.PackingWords

/-! The two literal edge blocks in the frame prefix have disjoint sequence
indices. Injectivity of the unchanged fold therefore makes their compressed
H paths disjoint in space. This connects the generic unused-edge classification
to the actual reduction word, without fixing a preferred cube orientation. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

def foldOnWord {S T : Sequence} (h : S = T) (f : Fold cubicLattice S.length) :
    Fold cubicLattice T.length := h ▸ f

theorem foldOnWord_pos {S T : Sequence} (h : S = T) (f : Fold cubicLattice S.length)
    (i : Fin T.length) :
    (foldOnWord h f).pos i = f.pos (Fin.cast (congrArg List.length h).symm i) := by
  cases h
  rfl

theorem foldOnWord_hydrophobicSites {S T : Sequence} (h : S = T) (f : Fold cubicLattice S.length) :
    hydrophobicSites T (foldOnWord h f) = hydrophobicSites S f := by
  cases h
  rfl

def afterSecondEdge (q Q : ℕ) (items : List ℕ) : Sequence :=
  let d := depth q Q
  List.replicate 4 .P ++ repeatWord (faceWord (d ^ 2) ++ List.replicate (d + 9) .P) 3 ++
    faceWord (d ^ 2 - 2) ++ [.P] ++ List.replicate (d ^ 3 + 2) .H ++
    List.replicate (alpha Q + 8) .P ++ walls q Q ++ itemWords q Q items

def beforeSecondEdge (q Q : ℕ) : Sequence :=
  edgeWord (9 * depth q Q + 8) ++ faceWord (depth q Q ^ 2)

def afterInitialEdge (q Q : ℕ) (items : List ℕ) : Sequence :=
  faceWord (depth q Q ^ 2) ++ edgeWord (depth q Q) ++ afterSecondEdge q Q items

theorem frameWord_initial_decomposition (q Q : ℕ) (items : List ℕ) :
    frameWord q Q items = [] ++ edgeWord (9 * depth q Q + 8) ++ afterInitialEdge q Q items := by
  simp [frameWord, prefixWord, afterInitialEdge, afterSecondEdge, List.append_assoc]

theorem frameWord_second_decomposition (q Q : ℕ) (items : List ℕ) :
    frameWord q Q items = beforeSecondEdge q Q ++ edgeWord (depth q Q) ++ afterSecondEdge q Q items := by
  simp [frameWord, prefixWord, beforeSecondEdge, afterSecondEdge, List.append_assoc]

def initialEdgePath (q Q : ℕ) (items : List ℕ) (f : Fold cubicLattice (frameWord q Q items).length) :
    List Site :=
  edgeHPathList [] (afterInitialEdge q Q items) (9 * depth q Q + 8)
    (foldOnWord (frameWord_initial_decomposition q Q items) f)

def secondEdgePath (q Q : ℕ) (items : List ℕ) (f : Fold cubicLattice (frameWord q Q items).length) :
    List Site :=
  edgeHPathList (beforeSecondEdge q Q) (afterSecondEdge q Q items) (depth q Q)
    (foldOnWord (frameWord_second_decomposition q Q items) f)

theorem initialEdgePath_length (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) :
    (initialEdgePath q Q items f).length = 9 * depth q Q + 8 := List.length_ofFn

theorem secondEdgePath_length (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) :
    (secondEdgePath q Q items f).length = depth q Q := List.length_ofFn

theorem separated_edge_paths_disjoint {S : Sequence} (f : Fold cubicLattice S.length)
    (pre₁ post₁ pre₂ post₂ : Sequence) (t₁ t₂ : ℕ)
    (h₁ : S = pre₁ ++ edgeWord t₁ ++ post₁) (h₂ : S = pre₂ ++ edgeWord t₂ ++ post₂)
    (hbefore : pre₁.length + 3 * t₁ ≤ pre₂.length) :
    Disjoint (edgeHPathList pre₂ post₂ t₂ (foldOnWord h₂ f)).toFinset
      (edgeHPathList pre₁ post₁ t₁ (foldOnWord h₁ f)).toFinset := by
  rw [Finset.disjoint_left]
  intro p hp₂ hp₁
  have hm₂ : p ∈ List.ofFn (edgeHPath pre₂ post₂ t₂ (foldOnWord h₂ f)) := List.mem_toFinset.mp hp₂
  have hm₁ : p ∈ List.ofFn (edgeHPath pre₁ post₁ t₁ (foldOnWord h₁ f)) := List.mem_toFinset.mp hp₁
  obtain ⟨i, hi⟩ := (List.mem_ofFn (f := edgeHPath pre₂ post₂ t₂ (foldOnWord h₂ f))).mp hm₂
  obtain ⟨j, hj⟩ := (List.mem_ofFn (f := edgeHPath pre₁ post₁ t₁ (foldOnWord h₁ f))).mp hm₁
  change (foldOnWord h₂ f).pos (edgeIndex pre₂ post₂ t₂ i 1) = p at hi
  change (foldOnWord h₁ f).pos (edgeIndex pre₁ post₁ t₁ j 1) = p at hj
  rw [foldOnWord_pos] at hi hj
  have he := congrArg Fin.val (f.injective_pos (hi.trans hj.symm))
  change pre₂.length + 3 * i.val + 1 = pre₁.length + 3 * j.val + 1 at he
  have hjlt := j.isLt
  omega

/-- The second E block begins after every residue of the first E block.
The two paths cannot share a site because the complete chain is injective. -/
theorem frameEdgePaths_disjoint (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) :
    Disjoint (secondEdgePath q Q items f).toFinset (initialEdgePath q Q items f).toFinset := by
  apply separated_edge_paths_disjoint f [] (afterInitialEdge q Q items)
    (beforeSecondEdge q Q) (afterSecondEdge q Q items) (9 * depth q Q + 8) (depth q Q)
    (frameWord_initial_decomposition q Q items) (frameWord_second_decomposition q Q items)
  simp [beforeSecondEdge, edgeWord_length]

theorem frame_initial_pack (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    hydrophobicSites ([] ++ edgeWord (9 * depth q Q + 8) ++ afterInitialEdge q Q items)
      (foldOnWord (frameWord_initial_decomposition q Q items) f) = cube a (depth q Q + 2) := by
  rw [foldOnWord_hydrophobicSites]
  exact hpack

theorem frame_second_pack (q Q : ℕ) (items : List ℕ)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    hydrophobicSites (beforeSecondEdge q Q ++ edgeWord (depth q Q) ++ afterSecondEdge q Q items)
      (foldOnWord (frameWord_second_decomposition q Q items) f) = cube a (depth q Q + 2) := by
  rw [foldOnWord_hydrophobicSites]
  exact hpack

/-- In every perfect fold of the actual frame word, the second E_d fills one
unused open edge. Exactly two mutually nonincident rails remain for the walls. -/
theorem frame_two_remaining_rails (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    ∃ e, (secondEdgePath q Q items f).toFinset = openEdgeFinset a (depth q Q) e ∧
      ((Finset.univ \ visitedEdges a (depth q Q) (initialEdgePath q Q items f)) \ {e}).card = 2 ∧
      ∀ bits, (incidentEdges bits ∩
        ((Finset.univ \ visitedEdges a (depth q Q) (initialEdgePath q Q items f)) \ {e})).card ≤ 1 := by
  let fp := foldOnWord (frameWord_initial_decomposition q Q items) f
  let fq := foldOnWord (frameWord_second_decomposition q Q items) f
  have hp := frame_initial_pack q Q items f a hpack
  have hqpack := frame_second_pack q Q items f a hpack
  exact two_remaining_rails a (depth q Q) (by have := depth_two_le q Q hq; omega)
    (initialEdgePath q Q items f) (secondEdgePath q Q items f)
    (edgeHPathList_nodup [] (afterInitialEdge q Q items) (9 * depth q Q + 8) fp)
    (edgeHPathList_chain [] (afterInitialEdge q Q items) (9 * depth q Q + 8) fp a _ hp)
    (edgeHPathList_skeleton [] (afterInitialEdge q Q items) (9 * depth q Q + 8) fp a _ hp)
    (initialEdgePath_length q Q items f)
    (edgeHPathList_nodup (beforeSecondEdge q Q) (afterSecondEdge q Q items) (depth q Q) fq)
    (edgeHPathList_chain (beforeSecondEdge q Q) (afterSecondEdge q Q items) (depth q Q) fq a _ hqpack)
    (edgeHPathList_skeleton (beforeSecondEdge q Q) (afterSecondEdge q Q items) (depth q Q) fq a _ hqpack)
    (secondEdgePath_length q Q items f) (frameEdgePaths_disjoint q Q items f)

end ProteinFolding.CubicPackingGeometry
