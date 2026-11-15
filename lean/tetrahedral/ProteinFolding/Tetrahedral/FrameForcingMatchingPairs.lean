import ProteinFolding.Tetrahedral.FrameForcingEdgeMatching

/-! The path matching is the actual HH matching: every even/odd consecutive
pair in a filled isolated edge block is one physical dimer. -/

namespace ProteinFolding.Tetrahedral.FinitePairFamily

variable {ι : Type*} [Fintype ι]

theorem pathMatching_mate_pair (F : FinitePairFamily ι Site) (W : Finset Site)
    (hW : W ⊆ F.covered)
    (hclosed : ∀ i, F.point (i, false) ∈ W ↔ F.point (i, true) ∈ W)
    (hadj : ∀ i, tetrahedralLattice.Adj (F.point (i, false)) (F.point (i, true)))
    (n : ℕ) (e : Fin n ≃ {x : Site // x ∈ W})
    (hpath : ∀ i j, tetrahedralLattice.Adj (e i).val (e j).val → i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (i : Fin n) :
    ∃ a b, (e i).val = F.point (a, b) ∧
      (e ((F.pathMatching W hW hclosed hadj n e hpath).mate i)).val = F.point (a, !b) := by
  let t := e.trans (F.pairsInEquiv W hW).symm
  have hpoint (j : Fin n) : F.point (t j).val = (e j).val := by
    exact congrArg Subtype.val ((F.pairsInEquiv W hW).apply_symm_apply (e j))
  let M := F.pathMatching W hW hclosed hadj n e hpath
  have hmate : t (M.mate i) = F.flipIn W hclosed (t i) := by
    change t (t.symm (F.flipIn W hclosed (t i))) = _
    exact t.apply_symm_apply _
  refine ⟨(t i).val.1, (t i).val.2, (hpoint i).symm, ?_⟩
  calc
    (e (M.mate i)).val = F.point (t (M.mate i)).val := (hpoint _).symm
    _ = F.point (F.flipIn W hclosed (t i)).val := congrArg (fun p : F.PairsIn W => F.point p.val) hmate
    _ = F.point ((t i).val.1, !(t i).val.2) := rfl

theorem edgeBlock_even_pair (P : FinitePairFamily ι Site)
    (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ)
    (hW : edgeBlock m F a n ⊆ P.covered)
    (hclosed : ∀ i, P.point (i, false) ∈ edgeBlock m F a n ↔ P.point (i, true) ∈ edgeBlock m F a n)
    (hadj : ∀ i, tetrahedralLattice.Adj (P.point (i, false)) (P.point (i, true)))
    (k : ℕ) (hk : 2 * k < n) :
    ∃ i b, octEdgeZigzag m F (a + 2 * k) = P.point (i, b) ∧
      octEdgeZigzag m F (a + 2 * k + 1) = P.point (i, !b) := by
  let e := edgeBlockEquiv m hm F a n
  have hpath : ∀ i j, tetrahedralLattice.Adj (e i).val (e j).val →
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
    intro i j hbond
    change tetrahedralLattice.Adj (octEdgeZigzag m F (a + i.val)) (octEdgeZigzag m F (a + j.val)) at hbond
    have h := (octEdgeZigzag_adj_iff hm F _ _).mp hbond
    omega
  let M := P.pathMatching (edgeBlock m F a n) hW hclosed hadj n e hpath
  have hmate := M.mate_even k hk
  obtain ⟨i, b, hfirst, hsecond⟩ := P.pathMatching_mate_pair _ hW hclosed hadj n e hpath ⟨2 * k, hk⟩
  change octEdgeZigzag m F (a + 2 * k) = P.point (i, b) at hfirst
  change octEdgeZigzag m F (a + (M.mate ⟨2 * k, hk⟩).val) = P.point (i, !b) at hsecond
  rw [hmate] at hsecond
  exact ⟨i, b, hfirst, by simpa only [Nat.add_assoc] using hsecond⟩

end ProteinFolding.Tetrahedral.FinitePairFamily
