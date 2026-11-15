import ProteinFolding.Tetrahedral.NearFieldWordPieceAssembly

/-! Changing only the first H site preserves the exact remaining support. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem hSupport_repoint {S : Sequence} (f g : Fold tetrahedralLattice S.length)
    (i₀ : Fin S.length) (a : Site) (hH : S.get i₀ = .H) (hfirst : f.pos i₀ = a)
    (hother : ∀ i, i ≠ i₀ → f.pos i = g.pos i) :
    hSupport S f = insert a ((hSupport S g).erase (g.pos i₀)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := (mem_hSupport S f x).mp hx
    by_cases he : i = i₀
    · subst i
      exact Finset.mem_insert.mpr (Or.inl (hix.symm.trans hfirst))
    · apply Finset.mem_insert.mpr
      right
      refine Finset.mem_erase.mpr ⟨?_, (mem_hSupport S g x).mpr ⟨i, hi, (hother i he).symm.trans hix⟩⟩
      intro hx0
      have hp : g.pos i = g.pos i₀ := (hother i he).symm.trans (hix.trans hx0)
      exact he (g.injective_pos hp)
  · intro hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact (mem_hSupport S f x).mpr ⟨i₀, hH, hfirst.trans hx.symm⟩
    · obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hx
      obtain ⟨i, hi, hix⟩ := (mem_hSupport S g x).mp hm
      have he : i ≠ i₀ := by
        intro he
        subst i
        exact hne hix.symm
      exact (mem_hSupport S f x).mpr ⟨i, hi, (hother i he).trans hix⟩

end ProteinFolding.Tetrahedral.NearField
