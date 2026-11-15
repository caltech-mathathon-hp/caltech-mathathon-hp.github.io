import ProteinFolding.Tetrahedral.NearFieldAssemblySupport
import ProteinFolding.Tetrahedral.BulkEdgeCount

/-! Residue labels and bulk separation pass through the same actual assembled
fold, using its checked word, occupied-site and hydrophobic-support equalities. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem residue_H_of_pos_mem_hSupport {S : Sequence} (f : Fold tetrahedralLattice S.length)
    (i : Fin S.length) (h : f.pos i ∈ hSupport S f) : S.get i = .H := by
  obtain ⟨j, hj, heq⟩ := (mem_hSupport _ _ _).mp h
  have hij := f.injective_pos heq
  simpa only [hij] using hj

theorem site_mem_hSupport_of_mem_oct {S : Sequence} (f : Fold tetrahedralLattice S.length) (m : ℕ)
    (hP : ∀ i, S.get i = .P → f.pos i ∉ octahedron m)
    (x : Site) (hx : x ∈ foldSites f) (ho : x ∈ octahedron m) : x ∈ hSupport S f := by
  obtain ⟨i, rfl⟩ := (mem_foldSites _ _).mp hx
  cases hres : S.get i with
  | H => exact (mem_hSupport _ _ _).mpr ⟨i, hres, rfl⟩
  | P => exact False.elim (hP i hres ho)

theorem hSupport_subset_pieceHsupport (ps : List PositionedWord) (p : PositionedWord) (hp : p ∈ ps) :
    hSupport p.word p.fold ⊆ pieceHsupport ps := by
  revert hp
  induction ps with
  | nil => intro hp; simp at hp
  | cons q qs ih =>
    intro hp x hx
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (ih hp hx)

theorem PieceAssembly.P_outside_oct {ps : List PositionedWord} (a : PieceAssembly ps) (m : ℕ)
    (hpieces : ∀ p ∈ ps, ∀ i, p.word.get i = .P → p.fold.pos i ∉ octahedron m)
    (i : Fin a.piece.word.length) (hP : a.piece.word.get i = .P) :
    a.piece.fold.pos i ∉ octahedron m := by
  intro ho
  have hs := (mem_foldSites a.piece.fold _).mpr ⟨i, rfl⟩
  rw [a.sites_eq] at hs
  obtain ⟨p, hp, hpos⟩ := (mem_pieceSites _ _).mp hs
  have hH := site_mem_hSupport_of_mem_oct p.fold m (hpieces p hp) _ hpos ho
  have hwhole : a.piece.fold.pos i ∈ hSupport a.piece.word a.piece.fold := by
    rw [a.hSupport_eq]
    exact hSupport_subset_pieceHsupport ps p hp hH
  have hh := residue_H_of_pos_mem_hSupport a.piece.fold i hwhole
  rw [hP] at hh
  cases hh

theorem foldSites_disjoint_bulkInterior_of_residues {S : Sequence}
    (f : Fold tetrahedralLattice S.length) (m : ℕ)
    (hH : hSupport S f ⊆ bulkDeletedEdges m)
    (hP : ∀ i, S.get i = .P → f.pos i ∉ octahedron m) :
    Disjoint (foldSites f) (bulkInterior m) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hmem := Finset.mem_sdiff.mp hy
  have hhyd := site_mem_hSupport_of_mem_oct f m hP x hx hmem.1
  exact hmem.2 (hH hhyd)

end ProteinFolding.Tetrahedral.NearField
