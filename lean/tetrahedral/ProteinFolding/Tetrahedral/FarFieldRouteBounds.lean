import ProteinFolding.Tetrahedral.FarFieldExactLengths
import ProteinFolding.Tetrahedral.FarFieldPrescribedLength

namespace ProteinFolding.Tetrahedral.FarField.RoutingPlan

variable {w : ℕ} {d : WireData w} (p : RoutingPlan d)

theorem wireSites_count (i : Fin w) :
    (p.wireSites i : ℤ) = (columnHeight d.R d.H d.quadrants d.bases i : ℤ) +
      (d.entries i).avenueEdges + radialHeight d.R (p.heights i) (d.entries i).point + (p.approaches i).sites := by
  have hca := d.columnAvenueSites_pos i
  have hp := d.prefixSites_pos i (p.heights i)
  have ha := (p.approaches i).sites_pos
  unfold wireSites WireData.prefixSites WireData.columnAvenueSites at *
  omega

theorem column_radial_bound (i : Fin w) :
    (columnHeight d.R d.H d.quadrants d.bases i : ℤ) +
      radialHeight d.R (p.heights i) (d.entries i).point ≤ p.heights i + 2 := by
  have hc := columnHeight_exact d.R d.R_even d.H d.H_odd d.quadrants d.bases i (d.positive i) (d.below i)
  have hE := d.entries_profile i
  have hr := radialHeight_exact d.R d.R_even (d.quadrants i) (d.entries i).point hE.1
    (p.heights i) (p.heights_odd i) (by have h := p.own_height i; omega)
  have hpos : 0 < rho d.R (d.bases i) := by
    have hp := d.positive i
    have hy := hp.1
    have hz := hp.2
    simp only [rho, abs_of_pos hp.1, abs_of_pos hp.2]
    omega
  change rho d.R (d.bases i) + 2 * (columnHeight d.R d.H d.quadrants d.bases i : ℤ) = d.levels i at hc
  omega

theorem avenueEdges_bound (i : Fin w) (hxlow : -d.H ≤ wireBaseXs d.quadrants d.bases i) :
    ((d.entries i).avenueEdges : ℤ) ≤ 2 * d.H + 60 * w + 3 := by
  have he := (d.entries i).avenueEdges_exact (le_of_lt (d.tops_before_slab i))
  have ht := d.tops_profile i
  have hs := (slabValue_bounds d.H d.levels i).2
  change d.slabs i ≤ d.H + 60 * w at hs
  have hx := (d.entries i).upper
  omega

theorem wireSites_bound (i : Fin w) (hxlow : -d.H ≤ wireBaseXs d.quadrants d.bases i) :
    (p.wireSites i : ℤ) ≤ 2 * d.H + 5 * p.heights i + 60 * w + 10 := by
  have hc := p.wireSites_count i
  have hcr := p.column_radial_bound i
  have ha := avenueEdges_bound (d := d) i hxlow
  have hA := (p.approaches i).length_bound
  omega

theorem target_gap_bound (i j : Fin w) :
    X (p.approaches j).target - X (p.approaches i).target ≤ 60 * w + 13 := by
  have hi := p.target_profile i
  have hj := p.target_profile j
  have hs0 := (slabValue_bounds d.H d.levels i).1
  have hs1 := (slabValue_bounds d.H d.levels j).2
  change d.H + 60 ≤ d.slabs i at hs0
  change d.slabs j ≤ d.H + 60 * w at hs1
  omega

theorem basePairCount_bound (i j : Fin w) (U : ℤ) (hui : p.heights i ≤ U) (huj : p.heights j ≤ U)
    (hxlow : ∀ k, -d.H ≤ wireBaseXs d.quadrants d.bases k) :
    p.basePairCount i j ≤ 4 * d.H + 10 * U + 180 * w + 32 := by
  have hi := p.wireSites_bound i (hxlow i)
  have hj := p.wireSites_bound j (hxlow j)
  have hgap := p.target_gap_bound i j
  unfold basePairCount
  omega

end ProteinFolding.Tetrahedral.FarField.RoutingPlan

namespace ProteinFolding.Tetrahedral.FarField.WireData

variable {w : ℕ} (d : WireData w)

theorem default_basePairCount_bound {k : ℕ} (pairIndex : Fin w → Fin k) (hw : w = 2 * k)
    (m : ℕ) (hH : d.H = 20 * m + 21) (i j : Fin w)
    (hxlow : ∀ s, -d.H ≤ wireBaseXs d.quadrants d.bases s) :
    (d.defaultPlan pairIndex).basePairCount i j ≤ 280 * m + 240 * w + 406 := by
  have hi := d.pairedHeight_bound pairIndex hw i
  have hj := d.pairedHeight_bound pairIndex hw j
  have h := (d.defaultPlan pairIndex).basePairCount_bound i j (d.H + 6 * w + 8) hi hj hxlow
  rw [hH] at h
  omega

theorem uniform_exactPairRoute_exists {k : ℕ} (pairIndex : Fin w → Fin k) (hw : w = 2 * k)
    (m : ℕ) (hH : d.H = 20 * m + 21) (i j : Fin w) (hne : i ≠ j)
    (horder : d.slabs i < d.slabs j) (hpair : pairIndex i = pairIndex j)
    (hxlow : ∀ s, -d.H ≤ wireBaseXs d.quadrants d.bases s)
    (L : ℕ) (hL : uniformLinkerLength m w ≤ L) (hparity : CapParity (d.armCaps i) (d.armCaps j) L) :
    Nonempty (ExactPairRoute (d.defaultPlan pairIndex) i j L) := by
  have hb := d.default_basePairCount_bound pairIndex hw m hH i j hxlow
  have hstrict := baseRouteBound_lt m w
  unfold baseRouteBound uniformLinkerLength at *
  apply exactPairRoute_exists (d.defaultPlan pairIndex) i j hne horder
  · simp only [defaultPlan, pairedHeight, hpair]
  · omega
  · exact hparity

end ProteinFolding.Tetrahedral.FarField.WireData
