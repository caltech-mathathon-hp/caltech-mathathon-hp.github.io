import ProteinFolding.Tetrahedral.ReductionTM2BulkRuntimeFamily
import ProteinFolding.Tetrahedral.NearFieldWordPieceAssembly

/-! Actual computed bulk H-runs as positioned word pieces for the final
finite concatenation. All lengths and their occurrence order are computed. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

open NearField

set_option maxHeartbeats 2000000

noncomputable def runtimePiece (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : PositionedWord where
  word := List.replicate ((lengths m).get j) .H
  fold := (runtimeFold m hm ha j).onLength (by simp only [List.length_replicate])
  length_pos := by
    simp only [List.length_replicate]
    have h := runtimeFold_length_ge_three m hm ha j
    omega
  first := runtimeFirst m hm ha j
  last := runtimeLast m hm ha j
  first_eq i hi := by
    change (runtimeFold m hm ha j).pos (Fin.cast _ i) = (runtimeFold m hm ha j).pos _
    congr 1
    apply Fin.ext
    exact hi
  last_eq i hi := by
    change (runtimeFold m hm ha j).pos (Fin.cast _ i) = (runtimeFold m hm ha j).pos _
    congr 1
    apply Fin.ext
    have hn : i.val + 1 = (lengths m).get j := by simpa only [List.length_replicate] using hi
    change i.val = (lengths m).get j - 1
    omega

theorem runtimePiece_inside (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (p : Site) (hp : p ∈ foldSites (runtimePiece m hm ha j).fold) :
    p ∈ bulkInterior m := by
  obtain ⟨i, hi⟩ := (mem_foldSites _ _).1 hp
  rw [← hi]
  exact runtimeFold_inside m hm ha j _

theorem runtimePiece_hSupport (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) :
    hSupport (runtimePiece m hm ha j).word (runtimePiece m hm ha j).fold =
      foldSites (runtimePiece m hm ha j).fold :=
  hSupport_allH_eq_foldSites _ _

theorem runtimePiece_disjoint (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j k : Fin (lengths m).length) (hne : j ≠ k) :
    Disjoint (foldSites (runtimePiece m hm ha j).fold) (foldSites (runtimePiece m hm ha k).fold) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨i, hi⟩ := (mem_foldSites _ _).1 hp
  obtain ⟨l, hl⟩ := (mem_foldSites _ _).1 hq
  have hd := runtimeFold_disjoint m hm ha j k hne
  exact Set.disjoint_left.mp hd ⟨Fin.cast (by simp only [runtimePiece, List.length_replicate]) i, hi⟩
    ⟨Fin.cast (by simp only [runtimePiece, List.length_replicate]) l, hl⟩

theorem runtimePiece_colours (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) :
    (FarField.colour (runtimePiece m hm ha j).first, FarField.colour (runtimePiece m hm ha j).last) =
      (colours m).get (colourIndex m j) :=
  runtimeFold_colours m hm ha j

theorem runtimePiece_sites (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) :
    foldSites (runtimePiece m hm ha j).fold = foldSites (runtimeFold m hm ha j) := by
  ext p
  rw [mem_foldSites, mem_foldSites]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨Fin.cast (by simp only [runtimePiece, List.length_replicate]) i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨i.val, by simpa only [runtimePiece, List.length_replicate] using i.isLt⟩, hi⟩

noncomputable def runtimePieces (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    List PositionedWord := List.ofFn (runtimePiece m hm ha)

theorem runtimePieces_pairwise (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    (runtimePieces m hm ha).Pairwise (fun a b => Disjoint (foldSites a.fold) (foldSites b.fold)) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact runtimePiece_disjoint m hm ha i j (ne_of_lt hij)

theorem runtimePieces_sites (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    pieceSites (runtimePieces m hm ha) = bulkInterior m := by
  ext p
  rw [mem_pieceSites]
  constructor
  · rintro ⟨piece, hpiece, hp⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hpiece
    exact runtimePiece_inside m hm ha j p hp
  · intro hp
    obtain ⟨j, i, hi⟩ := runtimeFold_covers m hm ha p hp
    refine ⟨runtimePiece m hm ha j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
    rw [runtimePiece_sites, mem_foldSites]
    exact ⟨i, hi⟩

theorem runtimePieces_words (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    (runtimePieces m hm ha).map PositionedWord.word =
      (lengths m).map (fun n => List.replicate n Residue.H) := by
  rw [runtimePieces, List.map_ofFn]
  exact List.ofFn_getElem_eq_map (lengths m) (fun n => List.replicate n Residue.H)

theorem runtimePieces_hSupport (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    pieceHsupport (runtimePieces m hm ha) = bulkInterior m := by
  rw [← runtimePieces_sites m hm ha]
  have h : ∀ piece ∈ runtimePieces m hm ha,
      hSupport piece.word piece.fold = foldSites piece.fold := by
    intro piece hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact runtimePiece_hSupport m hm ha j
  generalize runtimePieces m hm ha = ps at *
  induction ps with
  | nil => rfl
  | cons piece ps ih =>
    change hSupport piece.word piece.fold ∪ pieceHsupport ps = foldSites piece.fold ∪ pieceSites ps
    rw [h piece (by simp), ih (fun q hq => h q (by simp [hq]))]

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan
