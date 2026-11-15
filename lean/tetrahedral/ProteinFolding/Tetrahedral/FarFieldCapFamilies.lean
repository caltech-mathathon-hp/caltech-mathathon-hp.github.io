import ProteinFolding.Tetrahedral.FarFieldCapRouteBounds
import ProteinFolding.Tetrahedral.FarFieldFamilies

namespace ProteinFolding.Tetrahedral.FarField

theorem Pairing.ordered_capParity_for {w k : ℕ} (e : Pairing w k) (d : WireData w)
    (caps : Fin w → Site) (r : Fin k) (L : ℕ)
    (hL : CapParity (caps (e.first r)) (caps (e.second r)) L) :
    CapParity (caps (e.lower d r)) (caps (e.upper d r)) L := by
  by_cases h : d.slabs (e.first r) < d.slabs (e.second r)
  · simpa only [Pairing.lower, Pairing.upper, if_pos h] using hL
  · simpa only [Pairing.lower, Pairing.upper, if_neg h] using (capParity_swap _ _ L).1 hL

/-- Lemma F for original caps, including a borrowed entry bond when needed.
The hypotheses describe only the near-field arm and entry geometry. The entire
far-field routing, its padding and simultaneous avoidance are constructed. -/
theorem paired_cap_routes {w k : ℕ} (d : WireData w) (c : CapEntryData d) (e : Pairing w k)
    (m : ℕ) (hH : d.H = 20 * m + 21)
    (hxlow : ∀ i, -d.H ≤ wireBaseXs d.quadrants d.bases i)
    (L : Fin k → ℕ) (hL : ∀ r, uniformLinkerLength m w ≤ L r)
    (hparity : ∀ r, CapParity (c.caps (e.first r)) (c.caps (e.second r)) (L r)) :
    ∃ f : ∀ r : Fin k, Fold tetrahedralLattice (L r),
      (∀ r i, i.val = 0 → (f r).pos i = c.caps (e.lower d r)) ∧
      (∀ r i, i.val + 1 = L r → (f r).pos i = c.caps (e.upper d r)) ∧
      (∀ r s, r ≠ s → Disjoint (Set.range (f r).pos) (Set.range (f s).pos)) := by
  let p := d.defaultPlan e.pairIndex
  have hex (r : Fin k) : Nonempty (ExactCapPairRoute c p (e.lower d r) (e.upper d r) (L r)) := by
    apply c.uniform_exactCapPairRoute_exists e.pairIndex e.card_eq m hH _ _
      (e.lower_ne_upper d r) (e.slab_order d r) _ hxlow (L r) (hL r)
      (e.ordered_capParity_for d c.caps r (L r) (hparity r))
    simp only [Pairing.pairIndex_lower, Pairing.pairIndex_upper]
  let routes (r : Fin k) := Classical.choice (hex r)
  let f (r : Fin k) := (routes r).fold (e.lower_ne_upper d r)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro r i hi
    exact (routes r).first (e.lower_ne_upper d r) i hi
  · intro r i hi
    exact (routes r).last (e.lower_ne_upper d r) i hi
  · intro r s hrs
    have he := e.endpoints_ne d r s hrs
    exact (routes r).disjoint (routes s) (e.lower_ne_upper d r) (e.lower_ne_upper d s)
      he.1 he.2.1 he.2.2.1 he.2.2.2 (e.same_height d r) (e.same_height d s) (e.height_gap d r s hrs)

end ProteinFolding.Tetrahedral.FarField
