import ProteinFolding.Tetrahedral.FiniteSets

/-!
# Relating sequence bonds to occupied-site edges

Injectivity of a fold identifies its hydrophobic residues with a finite set
of lattice sites. The sequence-index bond count agrees with the geometric
internal-edge count. Thus the boundary identity applies to every HP fold.
-/

namespace ProteinFolding.Tetrahedral

/-- The finite set of sites occupied by hydrophobic residues. -/
def hSupport (S : Sequence) (f : Fold tetrahedralLattice S.length) : Finset Site :=
  (hydrophobicIndices S).image f.pos

@[simp] theorem mem_hSupport (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (p : Site) : p ∈ hSupport S f ↔ ∃ i, S.get i = Residue.H ∧ f.pos i = p := by
  simp [hSupport, hydrophobicIndices]

theorem hSupport_card (S : Sequence) (f : Fold tetrahedralLattice S.length) :
    (hSupport S f).card = hydrophobicCount S :=
  Finset.card_image_of_injective _ f.injective_pos

theorem mem_hhBonds_iff (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (ij : Fin S.length × Fin S.length) : ij ∈ hhBonds S f ↔
      ij.1 < ij.2 ∧ S.get ij.1 = Residue.H ∧ S.get ij.2 = Residue.H ∧
        tetrahedralLattice.Adj (f.pos ij.1) (f.pos ij.2) := by
  simp [hhBonds]

/-- Canonical edge orientation from A to B. -/
def orientEdge (p q : Site) : Site × Site :=
  if InASublattice p.val then (p, q) else (q, p)

theorem orientEdge_mem_internalEdges (T : Finset Site) {p q : Site}
    (hp : p ∈ T) (hq : q ∈ T) (hadj : tetrahedralLattice.Adj p q) :
    orientEdge p q ∈ internalEdges T := by
  rcases hadj with h | h
  · simp only [orientEdge, if_pos h.1]
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, h⟩
  · simp only [orientEdge, if_neg ((inB_iff_not_inA p).mp h.2.1)]
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq, hp⟩, h⟩

theorem orientEdge_injective_on_ordered_indices (S : Sequence)
    (f : Fold tetrahedralLattice S.length) {ij kl : Fin S.length × Fin S.length}
    (hij : ij.1 < ij.2) (hkl : kl.1 < kl.2)
    (heq : orientEdge (f.pos ij.1) (f.pos ij.2) =
      orientEdge (f.pos kl.1) (f.pos kl.2)) : ij = kl := by
  by_cases hi : InASublattice (f.pos ij.1).val <;>
    by_cases hk : InASublattice (f.pos kl.1).val
  · simp only [orientEdge, if_pos hi, if_pos hk] at heq
    exact Prod.ext (f.injective_pos (congrArg Prod.fst heq))
      (f.injective_pos (congrArg Prod.snd heq))
  · simp only [orientEdge, if_pos hi, if_neg hk] at heq
    have h₁ := f.injective_pos (congrArg Prod.fst heq)
    have h₂ := f.injective_pos (congrArg Prod.snd heq)
    have hbad : kl.2 < kl.1 := h₁ ▸ h₂ ▸ hij
    exact False.elim (lt_asymm hkl hbad)
  · simp only [orientEdge, if_neg hi, if_pos hk] at heq
    have h₁ := f.injective_pos (congrArg Prod.snd heq)
    have h₂ := f.injective_pos (congrArg Prod.fst heq)
    have hbad : kl.2 < kl.1 := h₁ ▸ h₂ ▸ hij
    exact False.elim (lt_asymm hkl hbad)
  · simp only [orientEdge, if_neg hi, if_neg hk] at heq
    exact Prod.ext (f.injective_pos (congrArg Prod.snd heq))
      (f.injective_pos (congrArg Prod.fst heq))

/-- The manuscript's identification of H-H bonds with edges inside the H-set. -/
theorem bondCount_eq_internalEdgeCount (S : Sequence)
    (f : Fold tetrahedralLattice S.length) :
    bondCount S f = internalEdgeCount (hSupport S f) := by
  unfold bondCount internalEdgeCount
  apply Finset.card_bij (fun ij _ => orientEdge (f.pos ij.1) (f.pos ij.2))
  · intro ij hij
    have h := (mem_hhBonds_iff S f ij).mp hij
    apply orientEdge_mem_internalEdges
    · exact (mem_hSupport S f _).mpr ⟨ij.1, h.2.1, rfl⟩
    · exact (mem_hSupport S f _).mpr ⟨ij.2, h.2.2.1, rfl⟩
    · exact h.2.2.2
  · intro ij hij kl hkl heq
    exact orientEdge_injective_on_ordered_indices S f
      ((mem_hhBonds_iff S f ij).mp hij).1 ((mem_hhBonds_iff S f kl).mp hkl).1 heq
  · rintro ⟨p, q⟩ hpq
    have he := Finset.mem_filter.mp hpq
    have hp := (Finset.mem_product.mp he.1).1
    have hq := (Finset.mem_product.mp he.1).2
    have hd : DirectedBond p q := he.2
    obtain ⟨i, hi, hpi⟩ := (mem_hSupport S f p).mp hp
    obtain ⟨j, hj, hpj⟩ := (mem_hSupport S f q).mp hq
    have hne : i ≠ j := by
      intro hij
      have hpq : p = q := hpi.symm.trans (hij ▸ hpj)
      exact sublattices_disjoint q.val (hpq ▸ hd.1) hd.2.1
    rcases lt_or_gt_of_ne hne with hij | hji
    · refine ⟨(i, j), ?_, ?_⟩
      · apply (mem_hhBonds_iff S f _).mpr
        refine ⟨hij, hi, hj, ?_⟩
        rw [hpi, hpj]
        exact Or.inl hd
      · simp only [orientEdge, hpi, hpj, if_pos hd.1]
    · refine ⟨(j, i), ?_, ?_⟩
      · apply (mem_hhBonds_iff S f _).mpr
        refine ⟨hji, hj, hi, ?_⟩
        rw [hpj, hpi]
        exact Or.inr hd
      · simp only [orientEdge, hpi, hpj, if_neg ((inB_iff_not_inA q).mp hd.2.1)]

/-- Every fold satisfies the degree/boundary identity for its H-sites. -/
theorem fold_boundary_identity (S : Sequence) (f : Fold tetrahedralLattice S.length) :
    4 * hydrophobicCount S = 2 * bondCount S f + boundaryCount (hSupport S f) := by
  rw [bondCount_eq_internalEdgeCount, ← hSupport_card S f]
  exact degree_boundary_identity (hSupport S f)

theorem bondCount_le_twice_hydrophobicCount (S : Sequence)
    (f : Fold tetrahedralLattice S.length) : bondCount S f ≤ 2 * hydrophobicCount S := by
  rw [bondCount_eq_internalEdgeCount, ← hSupport_card S f]
  exact internalEdgeCount_le_twice_card _

end ProteinFolding.Tetrahedral
