import ProteinFolding.Tetrahedral.FoldAssembly
import ProteinFolding.Tetrahedral.FrameForcingSlotBlocks

/-! Literal all-H runs along the retained frame edge intervals. -/

namespace ProteinFolding.Tetrahedral.NearField

def edgeHRunFold {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ) :
    Fold tetrahedralLattice (List.replicate n Residue.H).length where
  pos i := octEdgeZigzag m F (a + i.val)
  injective_pos i j hij := by
    apply Fin.ext
    have h := octEdgeZigzag_injective hm F hij
    omega
  consecutive i j hij := by
    have he : a + j.val = (a + i.val) + 1 := by omega
    simpa only [he] using octEdgeZigzag_adj m F (a + i.val)

theorem edgeHRunFold_first {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ)
    (i : Fin (List.replicate n Residue.H).length) (hi : i.val = 0) :
    (edgeHRunFold hm F a n).pos i = octEdgeZigzag m F a := by
  change octEdgeZigzag m F (a + i.val) = _
  rw [hi, Nat.add_zero]

theorem edgeHRunFold_last {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ)
    (i : Fin (List.replicate n Residue.H).length) (hi : i.val + 1 = (List.replicate n Residue.H).length) :
    (edgeHRunFold hm F a n).pos i = octEdgeZigzag m F (a + (n - 1)) := by
  have hn : i.val + 1 = n := by simpa only [List.length_replicate] using hi
  change octEdgeZigzag m F (a + i.val) = _
  congr 1
  omega

theorem edgeHRunFold_mem_oct {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ)
    (hroom : a + n ≤ 2 * m - 1) (i : Fin (List.replicate n Residue.H).length) :
    (edgeHRunFold hm F a n).pos i ∈ octahedron m := by
  have hi : i.val < n := by simpa only [List.length_replicate] using i.isLt
  rcases octEdgeZigzag_mem hm F (show a + i.val < 2 * m - 1 by omega) with h | h
  · exact h.1.1
  · exact h.1.1

theorem edgeHRunFold_sites {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ) :
    foldSites (edgeHRunFold hm F a n) = edgeBlock m F a n := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (mem_foldSites _ _).mp hx
    refine Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr ?_, hi⟩
    simpa only [List.length_replicate] using i.isLt
  · intro hx
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hx
    refine (mem_foldSites _ _).mpr ⟨⟨t, ?_⟩, heq⟩
    simpa only [List.length_replicate] using Finset.mem_range.mp ht

theorem edgeHRunFold_hSupport {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ) :
    hSupport (List.replicate n .H) (edgeHRunFold hm F a n) = edgeBlock m F a n := by
  rw [hSupport_allH_eq_foldSites, edgeHRunFold_sites]

end ProteinFolding.Tetrahedral.NearField
