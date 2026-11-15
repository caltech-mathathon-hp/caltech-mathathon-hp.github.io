import Shelf.MainTheorem
import Shelf.Core
import Shelf.Tiling
import Shelf.ATokens
import Shelf.Regroup
import Shelf.Linkers
import Shelf.LayoutChain
import Shelf.LayoutFits
import Shelf.LayoutNodup

/-!
# Theorem 16: an exact packing gives a perfect fold

The packing tells us where the items go on the shelf. The Core Lemma gives the
core, the Routing Lemma the linkers, and the rest of the fold is Table 1. The
list of sites is a walk without repeated sites that spells the string, with the
`H`'s in the cube; since the string has `n³` letters `H`, they fill the cube.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue Layout

/-- The parts of the fold that Table 1 leaves open exist. -/
theorem exists_good_parts {J : Packing.Instance} (hJ : Normalised J)
    (h : ∃ parts, Packing.Exact J parts) : ∃ P : Parts J, P.Good := by
  obtain ⟨lo, hbin, hdis⟩ := exists_tiling J h
  have hlo : Placed J lo := ⟨hbin, hdis⟩
  obtain ⟨core, hlen, hnd, hchain, hmem, hlast⟩ :=
    corePath (side J) (by have := ten_le_side hJ; omega) (side_even hJ)
  obtain ⟨mid, h0, hsucc, hc0, hcsucc, hmnd, hmdis, hmout⟩ := exists_linkers hJ hlo
  refine ⟨⟨core, aTokens J, lo, mid⟩, ?_⟩
  exact
    { core_length := hlen
      core_nodup := hnd
      core_chain := hchain
      core_mem := hmem
      core_last := by
        rw [hlast]; simp [coreEnd, N]; ring_nf
      a_length := aTokens_length J
      a_valid := aTokens_valid J
      a_linked := aTokens_linked hJ
      a_nodup := aTokens_nodup J
      a_centres := aTokens_centres J
      a_head := aTokens_head? J
      a_last := aTokens_getLast? hJ
      placed := hlo
      mid_zero_length := h0
      mid_succ_length := hsucc
      mid_zero_chain := hc0
      mid_succ_chain := hcsucc
      mid_nodup := hmnd
      mid_disjoint := hmdis
      mid_out := hmout }

/-- **Theorem 16.** If the instance has an exact packing, the string has a perfect fold. -/
theorem packingGivesFold : PackingGivesFold := by
  intro J hJ h
  obtain ⟨P, hP⟩ := exists_good_parts hJ h
  have hfit := layout_fits hJ hP
  rw [← shelfWord_eq_layoutWord hJ] at hfit
  exact perfect_of_walk (layout P) hfit (layout_nodup hJ hP) (layout_isChain hJ hP)
    (hydrophobicCount_shelfWord J hJ)

end ProteinFolding.Shelf
