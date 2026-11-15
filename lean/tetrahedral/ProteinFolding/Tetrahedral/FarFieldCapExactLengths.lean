import ProteinFolding.Tetrahedral.FarFieldCapPairSeparation

namespace ProteinFolding.Tetrahedral.FarField

namespace CapEntryData

variable {w : ℕ} {d : WireData w} (c : CapEntryData d)

theorem capPair_capParity {p : RoutingPlan d} {i j : Fin w} {Δ : ℕ}
    (m : MiddleData p i j Δ) (hne : i ≠ j) : CapParity (c.caps i) (c.caps j) (c.capPairSites m) := by
  have h := fold_capParity (c.capPairPath m hne) (c.capPairSites_pos m)
  have hf := c.capPair_first m hne ⟨0, c.capPairSites_pos m⟩ rfl
  have hl := c.capPair_last m hne ⟨c.capPairSites m - 1, by have h := c.capPairSites_pos m; omega⟩
    (by change c.capPairSites m - 1 + 1 = c.capPairSites m; have h := c.capPairSites_pos m; omega)
  simpa only [hf, hl] using h

theorem lengthDelta (p : RoutingPlan d) (i j : Fin w) (hne : i ≠ j)
    (horder : d.slabs i < d.slabs j) (hsame : p.heights i = p.heights j)
    (L : ℕ) (hL : c.baseCapPairCount p i j + 6 ≤ (L : ℤ))
    (hparity : CapParity (c.caps i) (c.caps j) L) :
    ∃ Δ : ℕ, 6 ≤ Δ ∧ Δ % 2 = 0 ∧ c.baseCapPairCount p i j + Δ = (L : ℤ) := by
  obtain ⟨m⟩ := middleData_exists p i j hne horder hsame 6 (by decide) (by decide)
  have hmod := capParity_mod_eq (c.caps i) (c.caps j) (c.capPairSites m) L (c.capPair_capParity m hne) hparity
  have hcount := c.capPair_count m
  let Δ := ((L : ℤ) - c.baseCapPairCount p i j).toNat
  have hcast : (Δ : ℤ) = (L : ℤ) - c.baseCapPairCount p i j := Int.toNat_of_nonneg (by omega)
  refine ⟨Δ, ?_, ?_, ?_⟩ <;> omega

end CapEntryData

structure ExactCapPairRoute {w : ℕ} {d : WireData w} (c : CapEntryData d)
    (p : RoutingPlan d) (i j : Fin w) (L : ℕ) where
  extra : ℕ
  extra_ge : 6 ≤ extra
  extra_even : extra % 2 = 0
  middle : MiddleData p i j extra
  sites_eq : c.capPairSites middle = L

theorem exactCapPairRoute_exists {w : ℕ} {d : WireData w} (c : CapEntryData d)
    (p : RoutingPlan d) (i j : Fin w) (hne : i ≠ j)
    (horder : d.slabs i < d.slabs j) (hsame : p.heights i = p.heights j)
    (L : ℕ) (hL : c.baseCapPairCount p i j + 6 ≤ (L : ℤ))
    (hparity : CapParity (c.caps i) (c.caps j) L) : Nonempty (ExactCapPairRoute c p i j L) := by
  obtain ⟨Δ, hΔ, heven, hcount⟩ := c.lengthDelta p i j hne horder hsame L hL hparity
  obtain ⟨m⟩ := middleData_exists p i j hne horder hsame Δ hΔ heven
  have hn := c.capPair_count m
  exact ⟨⟨Δ, hΔ, heven, m, by omega⟩⟩

namespace ExactCapPairRoute

variable {w : ℕ} {d : WireData w} {c : CapEntryData d} {p : RoutingPlan d}
  {i j : Fin w} {L : ℕ} (e : ExactCapPairRoute c p i j L)

noncomputable def fold (hne : i ≠ j) : Fold tetrahedralLattice L :=
  (c.capPairPath e.middle hne).onLength e.sites_eq.symm

theorem first (hne : i ≠ j) (k : Fin L) (hk : k.val = 0) : (e.fold hne).pos k = c.caps i := by
  change (c.capPairPath e.middle hne).pos (Fin.cast e.sites_eq.symm k) = _
  exact c.capPair_first e.middle hne _ hk

theorem last (hne : i ≠ j) (k : Fin L) (hk : k.val + 1 = L) : (e.fold hne).pos k = c.caps j := by
  change (c.capPairPath e.middle hne).pos (Fin.cast e.sites_eq.symm k) = _
  apply c.capPair_last
  change k.val + 1 = c.capPairSites e.middle
  have h := e.sites_eq
  omega

theorem range_subset (hne : i ≠ j) : Set.range (e.fold hne).pos ⊆ Set.range (c.capPairPath e.middle hne).pos := by
  rintro s ⟨k, rfl⟩
  exact ⟨Fin.cast e.sites_eq.symm k, rfl⟩

theorem disjoint {r s : Fin w} {M : ℕ} (f : ExactCapPairRoute c p r s M)
    (hij : i ≠ j) (hrs : r ≠ s)
    (hir : i ≠ r) (his : i ≠ s) (hjr : j ≠ r) (hjs : j ≠ s)
    (hm : p.heights i = p.heights j) (hn : p.heights r = p.heights s)
    (hgap : p.heights i + 4 ≤ p.heights r ∨ p.heights r + 4 ≤ p.heights i) :
    Disjoint (Set.range (e.fold hij).pos) (Set.range (f.fold hrs).pos) :=
  (c.capPairPaths_disjoint e.middle f.middle hij hrs hir his hjr hjs hm hn hgap).mono
    (e.range_subset hij) (f.range_subset hrs)

end ExactCapPairRoute

end ProteinFolding.Tetrahedral.FarField
