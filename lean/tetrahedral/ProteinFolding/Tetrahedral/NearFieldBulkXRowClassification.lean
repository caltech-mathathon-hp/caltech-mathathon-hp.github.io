import ProteinFolding.Tetrahedral.NearFieldBulkXRows

/-! Exhaustiveness of the finite X-plane row family and the colour parity
of every ambient edge zigzag. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgeFrame_eq_of_fields (F G : OctEdgeFrame)
    (hk : F.k = G.k) (hj : F.j = G.j) (ha : F.a = G.a) (hb : F.b = G.b) : F = G := by
  cases F
  cases G
  cases hk
  cases hj
  cases ha
  cases hb
  rfl

theorem xRowFrames_exhaustive (F : OctEdgeFrame) (hx : columnOpposite F.k = F.j) :
    ∃ k : Fin 4, ∃ reverse : Bool, F = xRowFrame k reverse := by
  have hall : ∀ k j a b : Fin 4,
      k ≠ j → k ≠ a → k ≠ b → j ≠ a → j ≠ b → a ≠ b → columnOpposite k = j →
      ∃ reverse : Bool, j = (xRowFrame k reverse).j ∧
        a = (xRowFrame k reverse).a ∧ b = (xRowFrame k reverse).b := by decide
  obtain ⟨reverse, hj, ha, hb⟩ := hall F.k F.j F.a F.b F.kj F.ka F.kb F.ja F.jb F.ab hx
  exact ⟨F.k, reverse, edgeFrame_eq_of_fields F (xRowFrame F.k reverse) rfl hj ha hb⟩

theorem xRowOpposite_symmetric (k j : Fin 4) (hx : columnOpposite j = k) : columnOpposite k = j := by
  revert k j
  decide

theorem edgeZigzag_A_even {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hp : InASublattice (octEdgeZigzag m F r).val) : r % 2 = 0 := by
  by_contra h
  have hr : r = 2 * (r / 2) + 1 := by omega
  have hB := (octEdgeZigzag_odd hm F (r / 2)).1
  rw [← hr] at hB
  exact sublattices_disjoint _ hp hB

theorem edgeZigzag_B_odd {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hp : InBSublattice (octEdgeZigzag m F r).val) : r % 2 = 1 := by
  by_contra h
  have hr : r = 2 * (r / 2) := by omega
  have hA := (octEdgeZigzag_even hm F (r / 2)).1
  rw [← hr] at hA
  exact sublattices_disjoint _ hA hp

end ProteinFolding.Tetrahedral.NearField
