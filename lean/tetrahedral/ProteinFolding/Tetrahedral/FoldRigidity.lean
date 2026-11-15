import ProteinFolding.Tetrahedral.SiteRigidityInvariance
import ProteinFolding.Tetrahedral.OctahedralVertices

/-! The first soundness step: the sharp score forces the entire hydrophobic
support to be an octahedron after a score-preserving lattice symmetry. -/

namespace ProteinFolding.Tetrahedral

theorem hSupport_normalize (S : Sequence) (f : Fold tetrahedralLattice S.length) (c : Site) :
    hSupport S (normalizeFold f c) = (hSupport S f).image (normalizeSite c) := by
  simp only [hSupport, normalizeFold, Finset.image_image, Function.comp_def]

theorem fold_threshold_normalizes (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hm : 0 < m) (hcount : hydrophobicCount S = octahedralNumber m)
    (hscore : 2 * octahedralNumber m - 2 * m ^ 2 ≤ bondCount S f) :
    ∃ c ∈ hSupport S f, hSupport S (normalizeFold f c) = octahedron m ∧
      bondCount S (normalizeFold f c) = 2 * octahedralNumber m - 2 * m ^ 2 := by
  have hbound := bondCount_octahedral_bound S f m hm hcount
  have heq : bondCount S f = 2 * octahedralNumber m - 2 * m ^ 2 := by omega
  have hcard : (hSupport S f).card = octahedralNumber m := by rw [hSupport_card, hcount]
  have hedges : internalEdgeCount (hSupport S f) = 2 * octahedralNumber m - 2 * m ^ 2 := by
    rw [← bondCount_eq_internalEdgeCount, heq]
  obtain ⟨c, hc, hshape⟩ := contact_maximizer_normalizes_to_octahedron _ m hm hcard hedges
  refine ⟨c, hc, ?_, ?_⟩
  · rw [hSupport_normalize, hshape]
  · rw [bondCount_normalize, heq]

theorem fold_octahedral_support_score (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m) :
    bondCount S f = 2 * octahedralNumber m - 2 * m ^ 2 := by
  rw [bondCount_eq_internalEdgeCount, hsupport, octahedron_edge_threshold]

/-- Existence at the sharp threshold is exactly existence of a fold whose
H-sites fill the fixed octahedron. The normalization moves every residue. -/
theorem octahedral_threshold_iff_oct_support (S : Sequence) (m : ℕ) (hm : 0 < m)
    (hcount : hydrophobicCount S = octahedralNumber m) :
    HPStringFold S (2 * (octahedralNumber m : ℤ) - 2 * (m ^ 2 : ℕ)) ↔
      ∃ f : Fold tetrahedralLattice S.length, hSupport S f = octahedron m := by
  have hN : m ^ 2 ≤ octahedralNumber m := by unfold octahedralNumber; omega
  constructor
  · rintro ⟨f, hf⟩
    have hf' : 2 * octahedralNumber m - 2 * m ^ 2 ≤ bondCount S f := by omega
    obtain ⟨c, _, hsupport, _⟩ := fold_threshold_normalizes S f m hm hcount hf'
    exact ⟨normalizeFold f c, hsupport⟩
  · rintro ⟨f, hsupport⟩
    refine ⟨f, ?_⟩
    have hscore := fold_octahedral_support_score S f m hsupport
    omega

theorem P_position_not_in_hSupport (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (i : Fin S.length) (hi : S.get i = .P) : f.pos i ∉ hSupport S f := by
  intro hmem
  obtain ⟨j, hj, hpos⟩ := (mem_hSupport S f (f.pos i)).mp hmem
  have hji := f.injective_pos hpos
  subst j
  rw [hi] at hj
  cases hj

theorem H_position_in_hSupport (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (i : Fin S.length) (hi : S.get i = .H) : f.pos i ∈ hSupport S f :=
  (mem_hSupport S f _).mpr ⟨i, hi, rfl⟩

/-- Every H-P chain bond in an octahedral-support fold exits that support. -/
theorem HP_chain_bond_external (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m)
    (i j : Fin S.length) (hi : S.get i = .H) (hj : S.get j = .P)
    (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    f.pos i ∈ octahedron m ∧
      f.pos j ∈ externalNeighbours (octahedron m) (f.pos i) := by
  have hH := H_position_in_hSupport S f i hi
  have hP := P_position_not_in_hSupport S f j hj
  rw [hsupport] at hH hP
  refine ⟨hH, ?_⟩
  unfold externalNeighbours
  apply Finset.mem_filter.mpr
  refine ⟨?_, hP⟩
  rw [mem_neighbours]
  rcases hij with hij | hij
  · exact f.consecutive i j hij
  · exact (f.consecutive j i hij).symm

/-- An interior H flanked by P's must occupy an octahedral vertex. -/
theorem PHP_monomer_is_vertex (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m)
    (l i r : Fin S.length) (hi : S.get i = .H)
    (hl : S.get l = .P) (hr : S.get r = .P)
    (hli : l.val + 1 = i.val) (hir : i.val + 1 = r.val) :
    f.pos i ∈ octVertices m := by
  obtain ⟨hH, hL⟩ := HP_chain_bond_external S f m hsupport i l hi hl (Or.inr hli)
  obtain ⟨_, hR⟩ := HP_chain_bond_external S f m hsupport i r hi hr (Or.inl hir)
  apply two_dangling_implies_vertex m hH
  rw [octDanglingDirections_card_eq_external]
  apply Finset.one_lt_card.mpr
  refine ⟨f.pos l, hL, f.pos r, hR, ?_⟩
  intro hpos
  have heq := congrArg Fin.val (f.injective_pos hpos)
  omega

def IsPHPMonomer (S : Sequence) (i : Fin S.length) : Prop :=
  S.get i = .H ∧ ∃ l r : Fin S.length,
    l.val + 1 = i.val ∧ i.val + 1 = r.val ∧ S.get l = .P ∧ S.get r = .P

instance decidableIsPHPMonomer (S : Sequence) (i : Fin S.length) :
    Decidable (IsPHPMonomer S i) := by
  unfold IsPHPMonomer
  infer_instance

def phpIndices (S : Sequence) : Finset (Fin S.length) :=
  Finset.univ.filter (IsPHPMonomer S)

theorem phpIndices_image_subset_vertices (S : Sequence)
    (f : Fold tetrahedralLattice S.length) (m : ℕ)
    (hsupport : hSupport S f = octahedron m) :
    (phpIndices S).image f.pos ⊆ octVertices m := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hH, l, r, hli, hir, hl, hr⟩ := (Finset.mem_filter.mp hi).2
  exact PHP_monomer_is_vertex S f m hsupport l i r hH hl hr hli hir

theorem phpIndices_card_le_six (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hm : 2 ≤ m) (hsupport : hSupport S f = octahedron m) :
    (phpIndices S).card ≤ 6 := by
  have h := Finset.card_le_card (phpIndices_image_subset_vertices S f m hsupport)
  rw [Finset.card_image_of_injective _ f.injective_pos, octVertices_card hm] at h
  exact h

/-- If the word has six PHP monomers, all six vertices are used by them. -/
theorem six_phpIndices_fill_vertices (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hm : 2 ≤ m) (hsupport : hSupport S f = octahedron m)
    (hphp : (phpIndices S).card = 6) :
    (phpIndices S).image f.pos = octVertices m := by
  apply Finset.eq_of_subset_of_card_le (phpIndices_image_subset_vertices S f m hsupport)
  rw [Finset.card_image_of_injective _ f.injective_pos, octVertices_card hm, hphp]

end ProteinFolding.Tetrahedral
