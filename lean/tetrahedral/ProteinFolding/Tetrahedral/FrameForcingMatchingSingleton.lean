import ProteinFolding.Tetrahedral.FrameForcingDimerPairs
import ProteinFolding.Tetrahedral.FrameForcingOccurrences

/-! Removing the first monomer from a 2D+1 ambient set leaves exactly the
actual D pairs, once that first monomer is known to lie in the ambient set. -/

namespace ProteinFolding.Tetrahedral

theorem FinitePairFamily.covered_eq_erase_one {ι α : Type*} [Fintype ι] [DecidableEq α]
    (F : FinitePairFamily ι α) (V : Finset α) (x : α)
    (hsub : F.covered ⊆ V) (hcard : V.card = 2 * Fintype.card ι + 1)
    (hx : x ∈ V) (hnot : x ∉ F.covered) : F.covered = V.erase x := by
  have hsub' : F.covered ⊆ V.erase x := by
    intro y hy
    apply Finset.mem_erase.mpr
    refine ⟨?_, hsub hy⟩
    intro heq
    exact hnot (heq ▸ hy)
  apply Finset.eq_of_subset_of_card_le hsub'
  rw [F.covered_card, Finset.card_erase_of_mem hx, hcard]
  omega

theorem foldDimerPairs_first_not_covered (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (hzero : 0 < S.length) : foldSiteAt f 0 ∉ (foldDimerPairs S f).covered := by
  rw [foldSiteAt_eq f 0 hzero]
  intro hx
  obtain ⟨⟨a, b⟩, _, heq⟩ := Finset.mem_image.mp hx
  have hindex := congrArg Fin.val (f.injective_pos heq)
  cases b with
  | false => change a.val + 1 = 0 at hindex; omega
  | true => change a.val + 2 = 0 at hindex; omega

end ProteinFolding.Tetrahedral
