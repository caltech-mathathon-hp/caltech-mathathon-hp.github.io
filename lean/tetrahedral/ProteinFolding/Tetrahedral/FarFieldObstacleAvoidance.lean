import ProteinFolding.Tetrahedral.FarFieldCapFamilies

namespace ProteinFolding.Tetrahedral.FarField

/-- Local near-field clearance. Only the short cap entries and outward columns
need a separate geometric check; every later routing stage is above the solid. -/
structure LocalObstacleData {w : ℕ} {d : WireData w} (c : CapEntryData d) (O : Set Site) : Prop where
  low : ∀ s ∈ O, rho d.R s < d.H
  entries : ∀ i a, (c.paths i).pos a ∈ O → (c.paths i).pos a = c.caps i
  columns : ∀ i a, (d.columns i).pos a ∈ O → (d.columns i).pos a = c.caps i

namespace LocalObstacleData

variable {w : ℕ} {d : WireData w} {c : CapEntryData d} {O : Set Site} (o : LocalObstacleData c O)

include o

theorem wire_contacts (p : RoutingPlan d) (i : Fin w) (s : Site)
    (hs : s ∈ Set.range (p.wirePath i).pos) (hO : s ∈ O) : s = c.caps i := by
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, hb⟩ := p.wire_below_H_is_column i a (o.low _ hO)
  have hmem : (d.columns i).pos b ∈ O := by rwa [hb]
  exact hb.symm.trans (o.columns i b hmem)

theorem middle_disjoint {p : RoutingPlan d} {i j : Fin w} {Δ : ℕ} (m : MiddleData p i j Δ) :
    Disjoint (Set.range m.path.pos) O := by
  apply Set.disjoint_left.mpr
  rintro s ⟨a, rfl⟩ hs
  have hlow := o.low _ hs
  have hprofile := m.profile a
  have hheight := p.height_above_H i
  omega

theorem pair_contacts {p : RoutingPlan d} {i j : Fin w} {Δ : ℕ} (m : MiddleData p i j Δ)
    (hne : i ≠ j) (s : Site) (hs : s ∈ Set.range (m.pairPath hne).pos) (hO : s ∈ O) :
    s = c.caps i ∨ s = c.caps j := by
  rcases m.pairPath_range hne hs with (hi | hm) | hj
  · exact Or.inl (o.wire_contacts p i s hi hO)
  · exact False.elim (Set.disjoint_left.mp (o.middle_disjoint m) hm hO)
  · exact Or.inr (o.wire_contacts p j s hj hO)

theorem capPair_contacts {p : RoutingPlan d} {i j : Fin w} {Δ : ℕ} (m : MiddleData p i j Δ)
    (hne : i ≠ j) (s : Site) (hs : s ∈ Set.range (c.capPairPath m hne).pos) (hO : s ∈ O) :
    s = c.caps i ∨ s = c.caps j := by
  rcases c.capPair_range m hne hs with (⟨a, ha⟩ | hm) | ⟨a, ha⟩
  · have hmem : (c.paths i).pos a ∈ O := by rwa [ha]
    exact Or.inl (ha.symm.trans (o.entries i a hmem))
  · exact o.pair_contacts m hne s hm hO
  · have hmem : (c.paths j).pos a ∈ O := by rwa [ha]
    exact Or.inr (ha.symm.trans (o.entries j a hmem))

theorem exactRoute_contacts {p : RoutingPlan d} {i j : Fin w} {L : ℕ}
    (e : ExactCapPairRoute c p i j L) (hne : i ≠ j) (s : Site)
    (hs : s ∈ Set.range (e.fold hne).pos) (hO : s ∈ O) : s = c.caps i ∨ s = c.caps j :=
  o.capPair_contacts e.middle hne s (e.range_subset hne hs) hO

end LocalObstacleData

/-- Simultaneous, length-exact original-cap routes. Their only contacts with
the near field are their own two caps. All clearance assumptions are local to
the entry segments and columns; the far-field paths are constructed here. -/
theorem paired_cap_routes_avoiding {w k : ℕ} (d : WireData w) (c : CapEntryData d)
    (e : Pairing w k) (O : Set Site) (o : LocalObstacleData c O)
    (m : ℕ) (hH : d.H = 20 * m + 21)
    (hxlow : ∀ i, -d.H ≤ wireBaseXs d.quadrants d.bases i)
    (L : Fin k → ℕ) (hL : ∀ r, uniformLinkerLength m w ≤ L r)
    (hparity : ∀ r, CapParity (c.caps (e.first r)) (c.caps (e.second r)) (L r)) :
    ∃ f : ∀ r : Fin k, Fold tetrahedralLattice (L r),
      (∀ r i, i.val = 0 → (f r).pos i = c.caps (e.lower d r)) ∧
      (∀ r i, i.val + 1 = L r → (f r).pos i = c.caps (e.upper d r)) ∧
      (∀ r s, r ≠ s → Disjoint (Set.range (f r).pos) (Set.range (f s).pos)) ∧
      (∀ r s, s ∈ Set.range (f r).pos → s ∈ O → s = c.caps (e.lower d r) ∨ s = c.caps (e.upper d r)) := by
  let p := d.defaultPlan e.pairIndex
  have hex (r : Fin k) : Nonempty (ExactCapPairRoute c p (e.lower d r) (e.upper d r) (L r)) := by
    apply c.uniform_exactCapPairRoute_exists e.pairIndex e.card_eq m hH _ _
      (e.lower_ne_upper d r) (e.slab_order d r) _ hxlow (L r) (hL r)
      (e.ordered_capParity_for d c.caps r (L r) (hparity r))
    simp only [Pairing.pairIndex_lower, Pairing.pairIndex_upper]
  let routes (r : Fin k) := Classical.choice (hex r)
  let f (r : Fin k) := (routes r).fold (e.lower_ne_upper d r)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro r i hi
    exact (routes r).first (e.lower_ne_upper d r) i hi
  · intro r i hi
    exact (routes r).last (e.lower_ne_upper d r) i hi
  · intro r s hrs
    have he := e.endpoints_ne d r s hrs
    exact (routes r).disjoint (routes s) (e.lower_ne_upper d r) (e.lower_ne_upper d s)
      he.1 he.2.1 he.2.2.1 he.2.2.2 (e.same_height d r) (e.same_height d s) (e.height_gap d r s hrs)
  · intro r s hs hO
    exact o.exactRoute_contacts (routes r) (e.lower_ne_upper d r) s hs hO

end ProteinFolding.Tetrahedral.FarField
