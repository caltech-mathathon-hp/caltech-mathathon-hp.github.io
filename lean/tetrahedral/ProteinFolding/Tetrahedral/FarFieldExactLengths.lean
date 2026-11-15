import ProteinFolding.Tetrahedral.FarFieldPairSeparation

namespace ProteinFolding.Tetrahedral.FarField

def WireData.armCaps {w : ℕ} (d : WireData w) (i : Fin w) : Site :=
  quadrantMap d.R d.R_even (d.quadrants i) (d.bases i)

theorem MiddleData.pair_capParity {w : ℕ} {d : WireData w} {p : RoutingPlan d}
    {i j : Fin w} {Δ : ℕ} (m : MiddleData p i j Δ) (hne : i ≠ j) :
    CapParity (d.armCaps i) (d.armCaps j) m.pairSites := by
  have h := fold_capParity (m.pairPath hne) m.pairSites_pos
  have hf := m.pairPath_first hne ⟨0, m.pairSites_pos⟩ rfl
  have hl := m.pairPath_last hne ⟨m.pairSites - 1, by have h := m.pairSites_pos; omega⟩
    (by change m.pairSites - 1 + 1 = m.pairSites; have h := m.pairSites_pos; omega)
  simpa only [hf, hl, WireData.armCaps] using h

namespace RoutingPlan

variable {w : ℕ} {d : WireData w} (p : RoutingPlan d)

theorem lengthDelta (i j : Fin w) (hne : i ≠ j) (horder : d.slabs i < d.slabs j)
    (hsame : p.heights i = p.heights j) (L : ℕ) (hL : p.basePairCount i j + 6 ≤ (L : ℤ))
    (hparity : CapParity (d.armCaps i) (d.armCaps j) L) :
    ∃ Δ : ℕ, 6 ≤ Δ ∧ Δ % 2 = 0 ∧ p.basePairCount i j + Δ = (L : ℤ) := by
  obtain ⟨m⟩ := middleData_exists p i j hne horder hsame 6 (by decide) (by decide)
  have hmod := capParity_mod_eq (d.armCaps i) (d.armCaps j) m.pairSites L (m.pair_capParity hne) hparity
  have hcount := m.pairSites_count
  let Δ := ((L : ℤ) - p.basePairCount i j).toNat
  have hcast : (Δ : ℤ) = (L : ℤ) - p.basePairCount i j := Int.toNat_of_nonneg (by omega)
  refine ⟨Δ, ?_, ?_, ?_⟩ <;> omega

end RoutingPlan

structure ExactPairRoute {w : ℕ} {d : WireData w} (p : RoutingPlan d) (i j : Fin w) (L : ℕ) where
  extra : ℕ
  extra_ge : 6 ≤ extra
  extra_even : extra % 2 = 0
  middle : MiddleData p i j extra
  sites_eq : middle.pairSites = L

theorem exactPairRoute_exists {w : ℕ} {d : WireData w} (p : RoutingPlan d) (i j : Fin w)
    (hne : i ≠ j) (horder : d.slabs i < d.slabs j) (hsame : p.heights i = p.heights j)
    (L : ℕ) (hL : p.basePairCount i j + 6 ≤ (L : ℤ))
    (hparity : CapParity (d.armCaps i) (d.armCaps j) L) : Nonempty (ExactPairRoute p i j L) := by
  obtain ⟨Δ, hΔ, heven, hcount⟩ := p.lengthDelta i j hne horder hsame L hL hparity
  obtain ⟨m⟩ := middleData_exists p i j hne horder hsame Δ hΔ heven
  have hn := m.pairSites_count
  exact ⟨⟨Δ, hΔ, heven, m, by omega⟩⟩

namespace ExactPairRoute

variable {w : ℕ} {d : WireData w} {p : RoutingPlan d} {i j : Fin w} {L : ℕ} (e : ExactPairRoute p i j L)

noncomputable def fold (hne : i ≠ j) : Fold tetrahedralLattice L :=
  (e.middle.pairPath hne).onLength e.sites_eq.symm

theorem first (hne : i ≠ j) (k : Fin L) (hk : k.val = 0) : (e.fold hne).pos k = d.armCaps i := by
  change (e.middle.pairPath hne).pos (Fin.cast e.sites_eq.symm k) = _
  apply e.middle.pairPath_first
  exact hk

theorem last (hne : i ≠ j) (k : Fin L) (hk : k.val + 1 = L) : (e.fold hne).pos k = d.armCaps j := by
  change (e.middle.pairPath hne).pos (Fin.cast e.sites_eq.symm k) = _
  apply e.middle.pairPath_last
  change k.val + 1 = e.middle.pairSites
  have h := e.sites_eq
  omega

theorem range_subset (hne : i ≠ j) : Set.range (e.fold hne).pos ⊆ Set.range (e.middle.pairPath hne).pos := by
  rintro s ⟨k, rfl⟩
  exact ⟨Fin.cast e.sites_eq.symm k, rfl⟩

theorem disjoint {r s : Fin w} {M : ℕ} (f : ExactPairRoute p r s M)
    (hij : i ≠ j) (hrs : r ≠ s)
    (hir : i ≠ r) (his : i ≠ s) (hjr : j ≠ r) (hjs : j ≠ s)
    (hm : p.heights i = p.heights j) (hn : p.heights r = p.heights s)
    (hgap : p.heights i + 4 ≤ p.heights r ∨ p.heights r + 4 ≤ p.heights i) :
    Disjoint (Set.range (e.fold hij).pos) (Set.range (f.fold hrs).pos) :=
  (e.middle.pairPaths_disjoint f.middle hij hrs hir his hjr hjs hm hn hgap).mono
    (e.range_subset hij) (f.range_subset hrs)

end ExactPairRoute

end ProteinFolding.Tetrahedral.FarField
