import ProteinFolding.Tetrahedral.FarFieldMixedCaps

namespace ProteinFolding.Tetrahedral.FarField

/-- Complete Lemma F routing for an actual finite mixture of ordinary and
borrowed dangling caps, at every large length of the required parity. -/
theorem mixed_cap_routes_avoiding {m w k : ℕ} (C : Fin w → DanglingColumn m)
    (hseed : Function.Injective (fun i => (C i).seed)) (caps : Fin w → Site)
    (hdangling : ∀ i, IsDangling m (caps i)) (hcaps : Function.Injective caps)
    (hadj : ∀ i, tetrahedralLattice.Adj (caps i) ((C i).point 1)) (e : Pairing w k)
    (O : Set Site) (hlow : ∀ s ∈ O, rho (octRadius m) s < 20 * (m : ℤ) + 21)
    (hclear : ∀ i n, 1 ≤ n → (C i).point n ∈ O → False)
    (L : Fin k → ℕ) (hL : ∀ r, uniformLinkerLength m w ≤ L r)
    (hparity : ∀ r, CapParity (caps (e.first r)) (caps (e.second r)) (L r)) :
    ∃ f : ∀ r : Fin k, Fold tetrahedralLattice (L r),
      (∀ r a, a.val = 0 → (f r).pos a = caps (e.first r)) ∧
      (∀ r a, a.val + 1 = L r → (f r).pos a = caps (e.second r)) ∧
      (∀ r s, r ≠ s → Disjoint (Set.range (f r).pos) (Set.range (f s).pos)) ∧
      (∀ r s, s ∈ Set.range (f r).pos → s ∈ O → s = caps (e.first r) ∨ s = caps (e.second r)) := by
  exact paired_cap_routes_ordered (columnsWireData C hseed) (mixedCapEntryData C hseed caps hdangling hcaps hadj)
    e O (mixedLocalObstacleData C hseed caps hdangling hcaps hadj O hlow hclear) m rfl
    (columnsWireData.x_lower C hseed) L hL hparity

end ProteinFolding.Tetrahedral.FarField
