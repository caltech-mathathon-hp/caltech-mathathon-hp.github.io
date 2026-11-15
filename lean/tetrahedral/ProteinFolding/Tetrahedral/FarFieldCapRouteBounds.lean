import ProteinFolding.Tetrahedral.FarFieldCapExactLengths
import ProteinFolding.Tetrahedral.FarFieldRouteBounds

namespace ProteinFolding.Tetrahedral.FarField.CapEntryData

variable {w : ℕ} {d : WireData w} (c : CapEntryData d)

theorem column_radial_entry_bound (p : RoutingPlan d) (i : Fin w) :
    (columnHeight d.R d.H d.quadrants d.bases i : ℤ) +
      radialHeight d.R (p.heights i) (d.entries i).point + c.sites i - 1 ≤ p.heights i + 2 := by
  have hc := columnHeight_exact d.R d.R_even d.H d.H_odd d.quadrants d.bases i (d.positive i) (d.below i)
  have hE := d.entries_profile i
  have hr := radialHeight_exact d.R d.R_even (d.quadrants i) (d.entries i).point hE.1
    (p.heights i) (p.heights_odd i) (by have h := p.own_height i; omega)
  have hs := c.sites_le_two i
  have hpos : 0 < rho d.R (d.bases i) := by
    have hp := d.positive i
    have hy := hp.1
    have hz := hp.2
    simp only [rho, abs_of_pos hp.1, abs_of_pos hp.2]
    omega
  change rho d.R (d.bases i) + 2 * (columnHeight d.R d.H d.quadrants d.bases i : ℤ) = d.levels i at hc
  omega

theorem wireSites_entry_bound (p : RoutingPlan d) (i : Fin w)
    (hxlow : -d.H ≤ wireBaseXs d.quadrants d.bases i) :
    (p.wireSites i : ℤ) + c.sites i - 1 ≤ 2 * d.H + 5 * p.heights i + 60 * w + 10 := by
  have hc := p.wireSites_count i
  have hcr := c.column_radial_entry_bound p i
  have ha := RoutingPlan.avenueEdges_bound (d := d) i hxlow
  have hA := (p.approaches i).length_bound
  omega

theorem baseCapPairCount_bound (p : RoutingPlan d) (i j : Fin w) (U : ℤ)
    (hui : p.heights i ≤ U) (huj : p.heights j ≤ U)
    (hxlow : ∀ k, -d.H ≤ wireBaseXs d.quadrants d.bases k) :
    c.baseCapPairCount p i j ≤ 4 * d.H + 10 * U + 180 * w + 32 := by
  have hi := c.wireSites_entry_bound p i (hxlow i)
  have hj := c.wireSites_entry_bound p j (hxlow j)
  have hgap := p.target_gap_bound i j
  unfold baseCapPairCount RoutingPlan.basePairCount
  omega

theorem default_baseCapPairCount_bound {k : ℕ} (pairIndex : Fin w → Fin k) (hw : w = 2 * k)
    (m : ℕ) (hH : d.H = 20 * m + 21) (i j : Fin w)
    (hxlow : ∀ s, -d.H ≤ wireBaseXs d.quadrants d.bases s) :
    c.baseCapPairCount (d.defaultPlan pairIndex) i j ≤ 280 * m + 240 * w + 406 := by
  have hi := d.pairedHeight_bound pairIndex hw i
  have hj := d.pairedHeight_bound pairIndex hw j
  have h := c.baseCapPairCount_bound (d.defaultPlan pairIndex) i j (d.H + 6 * w + 8) hi hj hxlow
  rw [hH] at h
  omega

theorem uniform_exactCapPairRoute_exists {k : ℕ} (pairIndex : Fin w → Fin k) (hw : w = 2 * k)
    (m : ℕ) (hH : d.H = 20 * m + 21) (i j : Fin w) (hne : i ≠ j)
    (horder : d.slabs i < d.slabs j) (hpair : pairIndex i = pairIndex j)
    (hxlow : ∀ s, -d.H ≤ wireBaseXs d.quadrants d.bases s)
    (L : ℕ) (hL : uniformLinkerLength m w ≤ L) (hparity : CapParity (c.caps i) (c.caps j) L) :
    Nonempty (ExactCapPairRoute c (d.defaultPlan pairIndex) i j L) := by
  have hb := c.default_baseCapPairCount_bound pairIndex hw m hH i j hxlow
  have hstrict := baseRouteBound_lt m w
  unfold baseRouteBound uniformLinkerLength at *
  apply exactCapPairRoute_exists c (d.defaultPlan pairIndex) i j hne horder
  · simp only [WireData.defaultPlan, WireData.pairedHeight, hpair]
  · omega
  · exact hparity

end ProteinFolding.Tetrahedral.FarField.CapEntryData
