import ProteinFolding.Tetrahedral.FarFieldExactLengths

namespace ProteinFolding.Tetrahedral.FarField

structure CapEntryData {w : ℕ} (d : WireData w) where
  caps : Fin w → Site
  sites : Fin w → ℕ
  paths : ∀ i, Fold tetrahedralLattice (sites i)
  sites_pos : ∀ i, 0 < sites i
  sites_le_two : ∀ i, sites i ≤ 2
  first : ∀ i k, k.val = 0 → (paths i).pos k = caps i
  last : ∀ i k, k.val + 1 = sites i → (paths i).pos k = d.armCaps i
  low : ∀ i k, rho d.R ((paths i).pos k) < d.H
  disjoint : ∀ i j, i ≠ j → Disjoint (Set.range (paths i).pos) (Set.range (paths j).pos)
  columns : ∀ i j a b, (paths i).pos a = (d.columns j).pos b →
    i = j ∧ a.val + 1 = sites i ∧ b.val = 0

namespace RoutingPlan

variable {w : ℕ} {d : WireData w} (p : RoutingPlan d)

theorem height_above_H (i : Fin w) : d.H + 4 ≤ p.heights i := by
  have hl := (assignedLevel_bounds d.H (wireBaseXs d.quadrants d.bases) i).1
  change d.H ≤ d.levels i at hl
  have hu := p.heights_above i i
  omega

theorem wire_below_H_is_column (i : Fin w) (k : Fin (p.wireSites i))
    (hk : rho d.R ((p.wirePath i).pos k) < d.H) :
    ∃ a, (d.columns i).pos a = (p.wirePath i).pos k := by
  have hl := (assignedLevel_bounds d.H (wireBaseXs d.quadrants d.bases) i).1
  change d.H ≤ d.levels i at hl
  have hm := p.wirePath_range i ⟨k, rfl⟩
  rcases hm with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hm' := d.prefixPath_range i (p.heights i) (p.heights_odd i) (p.own_height i) ⟨a, ha⟩
    rcases hm' with ⟨b, hb⟩ | ⟨b, hb⟩
    · have hm'' := d.columnAvenuePath_range i ⟨b, hb⟩
      rcases hm'' with hc | ⟨c, hc⟩
      · exact hc
      · have hp := d.avenue_paths_profile i c
        rw [hc] at hp
        omega
    · have hp := d.radial_paths_profile i (p.heights i) (p.heights_odd i) (p.own_height i) b
      rw [hb] at hp
      omega
  · have hp := (p.approaches i).level a
    rw [ha] at hp
    have hu := p.height_above_H i
    omega

end RoutingPlan

namespace CapEntryData

variable {w : ℕ} {d : WireData w} (c : CapEntryData d)

theorem wire_intersection (p : RoutingPlan d) (i j : Fin w) (a : Fin (c.sites i)) (b : Fin (p.wireSites j))
    (heq : (c.paths i).pos a = (p.wirePath j).pos b) : i = j ∧ a.val + 1 = c.sites i ∧ b.val = 0 := by
  have hlo := c.low i a
  have hlow : rho d.R ((p.wirePath j).pos b) < d.H := by rwa [heq] at hlo
  obtain ⟨k, hk⟩ := p.wire_below_H_is_column j b hlow
  have hcol := c.columns i j a k (heq.trans hk.symm)
  have hfirst := d.column_first j k hcol.2.2
  have hwire : (p.wirePath j).pos b = d.armCaps j := hk.symm.trans hfirst
  have hb := (p.wirePath j).injective_pos (hwire.trans (p.wirePath_first j ⟨0, p.wireSites_pos j⟩ rfl).symm)
  have hbval : b.val = 0 := congrArg (fun k : Fin (p.wireSites j) => k.val) hb
  exact ⟨hcol.1, hcol.2.1, hbval⟩

theorem disjoint_other_wire (p : RoutingPlan d) (i j : Fin w) (hne : i ≠ j) :
    Disjoint (Set.range (c.paths i).pos) (Set.range (p.wirePath j).pos) := by
  apply Set.disjoint_left.mpr
  rintro s ⟨a, rfl⟩ ⟨b, heq⟩
  exact hne (c.wire_intersection p i j a b heq.symm).1

theorem disjoint_middle {p : RoutingPlan d} {i j : Fin w} {Δ : ℕ}
    (m : MiddleData p i j Δ) (k : Fin w) : Disjoint (Set.range (c.paths k).pos) (Set.range m.path.pos) := by
  apply Set.disjoint_left.mpr
  rintro s ⟨a, rfl⟩ ⟨b, heq⟩
  have ha := c.low k a
  have hb := m.profile b
  rw [heq] at hb
  have hu := p.height_above_H i
  omega

theorem pair_intersection {p : RoutingPlan d} {i j : Fin w} {Δ : ℕ} (m : MiddleData p i j Δ)
    (hne : i ≠ j) (k : Fin w) (a : Fin (c.sites k)) (b : Fin m.pairSites)
    (heq : (c.paths k).pos a = (m.pairPath hne).pos b) :
    (k = i ∧ a.val + 1 = c.sites k ∧ (c.paths k).pos a = d.armCaps i) ∨
      (k = j ∧ a.val + 1 = c.sites k ∧ (c.paths k).pos a = d.armCaps j) := by
  have hm := m.pairPath_range hne ⟨b, rfl⟩
  rcases hm with (⟨s, hs⟩ | ⟨s, hs⟩) | ⟨s, hs⟩
  · have hi := c.wire_intersection p k i a s (heq.trans hs.symm)
    exact Or.inl ⟨hi.1, hi.2.1, (heq.trans hs.symm).trans (p.wirePath_first i s hi.2.2)⟩
  · exact False.elim (Set.disjoint_left.mp (c.disjoint_middle m k) ⟨a, rfl⟩ ⟨s, hs.trans heq.symm⟩)
  · have hj := c.wire_intersection p k j a s (heq.trans hs.symm)
    exact Or.inr ⟨hj.1, hj.2.1, (heq.trans hs.symm).trans (p.wirePath_first j s hj.2.2)⟩

end CapEntryData

end ProteinFolding.Tetrahedral.FarField
