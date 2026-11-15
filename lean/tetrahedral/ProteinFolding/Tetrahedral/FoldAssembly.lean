import ProteinFolding.Common.FoldConcatenation
import ProteinFolding.Tetrahedral.FoldRigidity

/-! Concatenating concrete disjoint pieces preserves their exact occupied
and hydrophobic sets. All H and P sites use the same injective Fold. -/

namespace ProteinFolding.Tetrahedral

def foldSites {n : ℕ} (f : Fold tetrahedralLattice n) : Finset Site :=
  Finset.univ.image f.pos

@[simp] theorem mem_foldSites {n : ℕ} (f : Fold tetrahedralLattice n) (p : Site) :
    p ∈ foldSites f ↔ ∃ i, f.pos i = p := by simp [foldSites]

theorem foldSites_disjoint_iff {n m : ℕ} (f : Fold tetrahedralLattice n)
    (g : Fold tetrahedralLattice m) :
    Disjoint (foldSites f) (foldSites g) ↔ ∀ i j, f.pos i ≠ g.pos j := by
  rw [Finset.disjoint_left]
  constructor
  · intro h i j heq
    exact h ((mem_foldSites f _).mpr ⟨i, rfl⟩) ((mem_foldSites g _).mpr ⟨j, heq.symm⟩)
  · intro h p hp hq
    obtain ⟨i, rfl⟩ := (mem_foldSites f p).mp hp
    obtain ⟨j, hj⟩ := (mem_foldSites g _).mp hq
    exact h i j hj.symm

theorem foldSites_appendWord {S T : Sequence} (f : Fold tetrahedralLattice S.length)
    (g : Fold tetrahedralLattice T.length) hdisjoint hseam :
    foldSites (Fold.appendWord f g hdisjoint hseam) = foldSites f ∪ foldSites g := by
  ext p
  simp only [mem_foldSites, Finset.mem_union]
  change (∃ i, (Fold.append f g hdisjoint hseam).pos (Fin.cast List.length_append i) = p) ↔ _
  constructor
  · rintro ⟨i, hi⟩
    exact (Fold.append_exists_pos f g hdisjoint hseam p).mp ⟨_, hi⟩
  · intro hp
    obtain ⟨i, hi⟩ := (Fold.append_exists_pos f g hdisjoint hseam p).mpr hp
    refine ⟨Fin.cast List.length_append.symm i, ?_⟩
    simpa only [Fin.cast_cast, Fin.cast_refl] using hi

theorem hSupport_appendWord {S T : Sequence} (f : Fold tetrahedralLattice S.length)
    (g : Fold tetrahedralLattice T.length) hdisjoint hseam :
    hSupport (S ++ T) (Fold.appendWord f g hdisjoint hseam) = hSupport S f ∪ hSupport T g := by
  ext p
  simp only [mem_hSupport, Finset.mem_union]
  exact Fold.appendWord_exists_residue f g hdisjoint hseam .H p

theorem hSupport_allP_empty (n : ℕ) (f : Fold tetrahedralLattice (List.replicate n Residue.P).length) :
    hSupport (List.replicate n .P) f = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨i, hi, _⟩ := (mem_hSupport _ f p).mp hp
  have hget : (List.replicate n Residue.P).get i = .P := by simp
  rw [hget] at hi
  cases hi

theorem hSupport_allH_eq_foldSites (n : ℕ)
    (f : Fold tetrahedralLattice (List.replicate n Residue.H).length) :
    hSupport (List.replicate n .H) f = foldSites f := by
  ext p
  simp [mem_hSupport]

theorem hSupport_append_allP {S : Sequence} (f : Fold tetrahedralLattice S.length)
    (n : ℕ) (g : Fold tetrahedralLattice (List.replicate n Residue.P).length)
    hdisjoint hseam :
    hSupport (S ++ List.replicate n .P) (Fold.appendWord f g hdisjoint hseam) = hSupport S f := by
  rw [hSupport_appendWord, hSupport_allP_empty, Finset.union_empty]

end ProteinFolding.Tetrahedral
