import ProteinFolding.Tetrahedral.NearFieldWordFoldAppend

/-! Exact word equalities transport folds together with their H labels. -/

namespace ProteinFolding.Tetrahedral.NearField

def transportWordFold {S T : Sequence} (h : S = T) (f : Fold tetrahedralLattice S.length) :
    Fold tetrahedralLattice T.length :=
  f.onLength (congrArg List.length h.symm)

theorem transportWordFold_hSupport {S T : Sequence} (h : S = T)
    (f : Fold tetrahedralLattice S.length) :
    hSupport T (transportWordFold h f) = hSupport S f := by
  cases h
  rfl

theorem transportWordFold_sites {S T : Sequence} (h : S = T)
    (f : Fold tetrahedralLattice S.length) :
    foldSites (transportWordFold h f) = foldSites f := by
  cases h
  rfl

theorem transportWordFold_property {S T : Sequence} (h : S = T)
    (f : Fold tetrahedralLattice S.length) (P : Site → Prop)
    (hf : ∀ i, P (f.pos i)) (i : Fin T.length) : P ((transportWordFold h f).pos i) :=
  hf (Fin.cast (congrArg List.length h.symm) i)

theorem transportWordFold_first {S T : Sequence} (h : S = T)
    (f : Fold tetrahedralLattice S.length) (p : Site)
    (hf : ∀ i, i.val = 0 → f.pos i = p) (i : Fin T.length) (hi : i.val = 0) :
    (transportWordFold h f).pos i = p := hf _ hi

theorem transportWordFold_last {S T : Sequence} (h : S = T)
    (f : Fold tetrahedralLattice S.length) (p : Site)
    (hf : ∀ i, i.val + 1 = S.length → f.pos i = p)
    (i : Fin T.length) (hi : i.val + 1 = T.length) :
    (transportWordFold h f).pos i = p := by
  apply hf
  have hlen := congrArg List.length h
  change i.val + 1 = S.length
  omega

end ProteinFolding.Tetrahedral.NearField
