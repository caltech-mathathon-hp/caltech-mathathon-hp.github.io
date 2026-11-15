import ProteinFolding.Tetrahedral.FrameForcingCatalogueGeometry
import ProteinFolding.Tetrahedral.FrameForcingTrackBands

/-! Entry and exit anchor chains cannot meet an interior bin: their
respective H and K heights are separated from every bin site. -/

namespace ProteinFolding.Tetrahedral

theorem frameTrackBand_interior_heights (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame)
    (lo hi : ℕ) (hlo : 5 ≤ lo) (hhi : hi + 6 ≤ 2 * m) :
    ∀ x ∈ frameTrackBand m F lo hi, 10 ≤ frameH2 m F x ∧ frameK2 m F x ≤ -10 := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  have hr' := Finset.mem_Ico.mp hr
  rw [frameTrackPoint_H2 m hm F r, frameTrackPoint_K2 m hm F r (by omega)]
  dsimp only [octRadius]
  constructor <;> omega

namespace DimerCatalogue

theorem singleton_height_bound {α : Type} {S : Sequence}
    (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (K : ℕ)
    (hsites : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 1)).biUnion (c.chainSites f) =
      Finset.univ.biUnion (fun k : Fin (K + 1) => edgeBlock m F (6 * (k.val + 1)) 2))
    (i : c.Index) (hi : c.q i = 1) (x : Site) (hx : x ∈ c.chainSites f i) :
    frameH2 m F x ≤ 2 := by
  letI := c.finiteIndex
  have hmem : x ∈ (Finset.univ.filter (fun i => c.q i = 1)).biUnion (c.chainSites f) :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hx⟩
  rw [hsites] at hmem
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hk
  exact (entry_edge_height_data m hm F _).2.1

theorem exit_height_bound {α : Type} {S : Sequence}
    (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hm : 1 ≤ m) (F G : OctEdgeFrame) (K : ℕ)
    (hGk : G.k = F.a) (hGj : G.j = F.j) (hGa : G.a = F.b)
    (hsites : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 3)).biUnion (c.chainSites f) =
      Finset.univ.biUnion (fun k : Fin (K + 1) => edgeBlock m G (2 * m - (10 * k.val + 13)) 6))
    (i : c.Index) (hi : c.q i = 3) (x : Site) (hx : x ∈ c.chainSites f i) :
    -2 ≤ frameK2 m F x := by
  letI := c.finiteIndex
  have hmem : x ∈ (Finset.univ.filter (fun i => c.q i = 3)).biUnion (c.chainSites f) :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hx⟩
  rw [hsites] at hmem
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hk
  exact (intended_exit_height_data m hm F G hGk hGj hGa _).2.1

end DimerCatalogue

end ProteinFolding.Tetrahedral
