import ProteinFolding.Tetrahedral.FrameForcingPairMatching
import ProteinFolding.Tetrahedral.FrameForcingSlotBlocks

/-! Ordinary-edge blocks inherit the unique path matching from the actual
HH pairs once slot occupancy and isolation have been proved. -/

namespace ProteinFolding.Tetrahedral

noncomputable def edgeBlockEquiv (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ) :
    Fin n ≃ {x : Site // x ∈ edgeBlock m F a n} :=
  Equiv.ofBijective (fun i => ⟨octEdgeZigzag m F (a + i.val),
    Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩⟩) (by
    constructor
    · intro i j heq
      have h := octEdgeZigzag_injective hm F (congrArg Subtype.val heq)
      apply Fin.ext
      omega
    · intro x
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp x.property
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, Subtype.ext heq⟩)

noncomputable def FinitePairFamily.edgePathMatching {ι : Type*} [Fintype ι]
    (P : FinitePairFamily ι Site) (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ)
    (hW : edgeBlock m F a n ⊆ P.covered)
    (hclosed : ∀ i, P.point (i, false) ∈ edgeBlock m F a n ↔ P.point (i, true) ∈ edgeBlock m F a n)
    (hadj : ∀ i, tetrahedralLattice.Adj (P.point (i, false)) (P.point (i, true))) :
    PathMatching n := by
  apply P.pathMatching (edgeBlock m F a n) hW hclosed hadj n (edgeBlockEquiv m hm F a n)
  intro i j hbond
  change tetrahedralLattice.Adj (octEdgeZigzag m F (a + i.val)) (octEdgeZigzag m F (a + j.val)) at hbond
  have h := (octEdgeZigzag_adj_iff hm F _ _).mp hbond
  omega

end ProteinFolding.Tetrahedral
