import ProteinFolding.Tetrahedral.FarFieldMiddlePaths
import ProteinFolding.Tetrahedral.FarFieldAvoidance

namespace ProteinFolding.Tetrahedral.FarField

namespace WireData

variable {w : ℕ} (d : WireData w)

theorem prefix_alpha_strip (i : Fin w) (u : ℤ) (hu : u % 2 = 1) (hui : d.levels i + 2 ≤ u)
    (k : Fin (d.prefixSites i u)) :
    alpha d.R ((d.prefixPath i u hu hui).pos k) = alpha d.R (d.bases i) ∨
      alpha d.R ((d.prefixPath i u hu hui).pos k) = alpha d.R (d.bases i) + 2 := by
  have hm := d.prefixPath_range i u hu hui ⟨k, rfl⟩
  rcases hm with ⟨c, hc⟩ | ⟨c, hc⟩
  · have hm' := d.columnAvenuePath_range i ⟨c, hc⟩
    rcases hm' with ⟨a, ha⟩ | ⟨a, ha⟩
    · have hp := (columnFold_profile d.R d.R_even d.H d.H_odd d.quadrants d.bases i (d.positive i) (d.below i) a).2.2.1
      change alpha d.R ((d.columns i).pos a) = _ at hp
      rw [ha] at hp
      exact Or.inl hp
    · have hp := (d.avenue_paths_profile i a).2.2.1
      rw [ha] at hp
      exact hp
  · have hp := (d.radial_paths_profile i u hu hui c).2.2.1
    rw [hc] at hp
    exact hp

end WireData

namespace RoutingPlan

variable {w : ℕ} {d : WireData w} (p : RoutingPlan d)

theorem prefix_alpha_bound (i : Fin w) (k : Fin (d.prefixSites i (p.heights i))) :
    alpha d.R ((d.prefixPath i (p.heights i) (p.heights_odd i) (p.own_height i)).pos k) ≤ p.a - 4 := by
  have hs := d.prefix_alpha_strip i (p.heights i) (p.heights_odd i) (p.own_height i) k
  have ha := p.a_above i
  have habs := le_abs_self (alpha d.R (d.bases i))
  omega

end RoutingPlan

structure MiddleData {w : ℕ} {d : WireData w} (p : RoutingPlan d) (i j : Fin w) (Δ : ℕ) where
  sites : ℕ
  path : Fold tetrahedralLattice sites
  sites_pos : 0 < sites
  count : (sites : ℤ) = X (p.approaches j).target - X (p.approaches i).target + 1 + Δ
  first : ∀ k, k.val = 0 → path.pos k = (p.approaches i).target
  last : ∀ k, k.val + 1 = sites → path.pos k = (p.approaches j).target
  profile : ∀ k, PositiveQuadrant d.R (path.pos k) ∧
    (rho d.R (path.pos k) = p.heights i ∨ rho d.R (path.pos k) = p.heights i + 2) ∧
    (alpha d.R (path.pos k) = p.a ∨ alpha d.R (path.pos k) = p.a + 2 ∨
      alpha d.R (path.pos k) = p.a + 4 ∨ alpha d.R (path.pos k) = p.a + 6)

theorem middleData_exists {w : ℕ} {d : WireData w} (p : RoutingPlan d) (i j : Fin w)
    (hne : i ≠ j) (horder : d.slabs i < d.slabs j) (hsame : p.heights i = p.heights j)
    (Δ : ℕ) (hΔ : 6 ≤ Δ) (heven : Δ % 2 = 0) : Nonempty (MiddleData p i j Δ) := by
  obtain ⟨n, f, hn, hfirst, hlast, hprofile⟩ := p.middle_path_exists i j hne horder hsame Δ hΔ heven
  have hgap := p.target_gap i j hne horder
  exact ⟨⟨n, f, by omega, hn, hfirst, hlast, hprofile⟩⟩

namespace MiddleData

variable {w : ℕ} {d : WireData w} {p : RoutingPlan d} {i j : Fin w} {Δ : ℕ} (m : MiddleData p i j Δ)

theorem wire_intersection (k : Fin w) (a : Fin m.sites) (b : Fin (p.wireSites k))
    (heq : m.path.pos a = (p.wirePath k).pos b) : m.path.pos a = (p.approaches k).target := by
  have hm := m.profile a
  have hw := p.wirePath_range k ⟨b, rfl⟩
  rcases hw with ⟨c, hc⟩ | ⟨c, hc⟩
  · have hα := p.prefix_alpha_bound k c
    rw [hc, ← heq] at hα
    omega
  · have hpos : PositiveQuadrant d.R ((p.approaches k).path.pos c) := by rw [hc, ← heq]; exact hm.1
    have hlim := (p.approaches k).alpha_limit c hpos
    have hα : alpha d.R ((p.approaches k).path.pos c) = p.a := by rw [hc, ← heq] at hlim ⊢; omega
    have htarget := (p.approaches k).hits_target c hpos hα
    exact heq.trans (hc.symm.trans htarget)

theorem avoids_wire_of_level_gap (k : Fin w)
    (hgap : p.heights i + 4 ≤ p.heights k ∨ p.heights k + 4 ≤ p.heights i) :
    Disjoint (Set.range m.path.pos) (Set.range (p.wirePath k).pos) := by
  apply Set.disjoint_left.mpr
  rintro s ⟨a, rfl⟩ ⟨b, heq⟩
  have ht := m.wire_intersection k a b heq.symm
  have hρ := m.profile a
  have hk := (p.approaches k).target_level
  rw [← ht] at hk
  omega

theorem disjoint_other_middle {r s : Fin w} {Δ' : ℕ} (n : MiddleData p r s Δ')
    (hgap : p.heights i + 4 ≤ p.heights r ∨ p.heights r + 4 ≤ p.heights i) :
    Disjoint (Set.range m.path.pos) (Set.range n.path.pos) := by
  apply paths_disjoint_of_levels d.R (p.heights i) (p.heights r) m.path n.path
    (fun a => (m.profile a).2.1) (fun b => (n.profile b).2.1) hgap

end MiddleData

end ProteinFolding.Tetrahedral.FarField
