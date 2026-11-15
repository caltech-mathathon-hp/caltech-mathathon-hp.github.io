import ProteinFolding.Tetrahedral.FrameForcingBandChains
import ProteinFolding.Tetrahedral.FrameForcingBinArithmetic
import ProteinFolding.Tetrahedral.FrameForcingCatalogueGeometry
import ProteinFolding.Tetrahedral.FrameForcingAmbient

/-! Two actual size-two separator blocks confine every other declared
chain that meets the intervening bin. -/

namespace ProteinFolding.Tetrahedral

def twoTrackPairs (m : ℕ) (F : OctEdgeFrame) (u v : ℕ) : Finset Site :=
  {frameTrackPoint m F (2 * u), frameTrackPoint m F (2 * u + 1),
    frameTrackPoint m F (2 * v), frameTrackPoint m F (2 * v + 1)}

theorem twoTrackPairs_mem (m : ℕ) (F : OctEdgeFrame) (u v s : ℕ)
    (hconsecutive : u + 1 = v ∨ v + 1 = u)
    (hs : 2 * min u v ≤ s ∧ s < 2 * min u v + 4) :
    frameTrackPoint m F s ∈ twoTrackPairs m F u v := by
  have hs' : s = 2 * u ∨ s = 2 * u + 1 ∨ s = 2 * v ∨ s = 2 * v + 1 := by omega
  rcases hs' with rfl | rfl | rfl | rfl <;> simp [twoTrackPairs]

theorem DimerCatalogue.bin_chain_all {α : Type} {S : Sequence}
    (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hm : 3 ≤ m) (hsupport : hSupport S f = octahedron m)
    (F : OctEdgeFrame) (u v u' v' : ℕ)
    (hleft : u + 1 = v ∨ v + 1 = u) (hright : u' + 1 = v' ∨ v' + 1 = u')
    (hlo : 5 ≤ 2 * min u v + 4) (hhi : 2 * min u' v' + 6 ≤ 2 * m)
    (havoidL : ∀ t, c.q t ≠ 2 → Disjoint (c.chainSites f t) (twoTrackPairs m F u v))
    (havoidR : ∀ t, c.q t ≠ 2 → Disjoint (c.chainSites f t) (twoTrackPairs m F u' v'))
    (t : c.Index) (ht : c.q t ≠ 2)
    (hmeet : (c.chainSites f t ∩ frameTrackBand m F (2 * min u v + 4) (2 * min u' v')).Nonempty) :
    c.chainSites f t ⊆ frameTrackBand m F (2 * min u v + 4) (2 * min u' v') := by
  classical
  let V := bulkDeletedEdges m \ (twoTrackPairs m F u v ∪ twoTrackPairs m F u' v')
  have hV : V ⊆ bulkDeletedEdges m := Finset.sdiff_subset
  have hsub : c.chainSites f t ⊆ V := by
    intro x hx
    apply Finset.mem_sdiff.mpr
    refine ⟨foldDimerPairs_subset_edges S f m hsupport (c.chainSites_subset f t hx), ?_⟩
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.disjoint_left.mp (havoidL t ht) hx h
    · exact Finset.disjoint_left.mp (havoidR t ht) hx h
  have hguard : ∀ s ∈ Finset.Ico (2 * min u v + 4 - 2) (2 * min u v + 4) ∪
      Finset.Ico (2 * min u' v') (2 * min u' v' + 2), frameTrackPoint m F s ∉ V := by
    intro s hs hmem
    have hnot := (Finset.mem_sdiff.mp hmem).2
    apply hnot
    rcases Finset.mem_union.mp hs with hs | hs
    · apply Finset.mem_union_left
      apply twoTrackPairs_mem m F u v s hleft
      have hb := Finset.mem_Ico.mp hs
      constructor <;> omega
    · apply Finset.mem_union_right
      apply twoTrackPairs_mem m F u' v' s hright
      have hb := Finset.mem_Ico.mp hs
      constructor <;> omega
  obtain ⟨x, hx⟩ := hmeet
  obtain ⟨hxC, hxW⟩ := Finset.mem_inter.mp hx
  obtain ⟨⟨i, b⟩, _, rfl⟩ := Finset.mem_image.mp hxC
  exact factorDimerPairs_band_all S f m hm hsupport (c.pre t) (c.post t) (c.q t) (c.factor t)
    F _ _ hlo hhi V hV hsub hguard ⟨i, b, hxW⟩

end ProteinFolding.Tetrahedral
