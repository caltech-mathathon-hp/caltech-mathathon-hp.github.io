import ProteinFolding.Tetrahedral.FarFieldWirePaths
import ProteinFolding.Tetrahedral.FarFieldPadding

namespace ProteinFolding.Tetrahedral.FarField

theorem ApproachData.target_window {R u a : ℤ} {T : Site} (h : ApproachData R u a T) :
    X T - 4 ≤ X h.target ∧ X h.target ≤ X T + 1 := by
  let k : Fin h.sites := ⟨h.sites - 1, by have hpos := h.sites_pos; omega⟩
  have hk := h.last k (by change h.sites - 1 + 1 = h.sites; have hpos := h.sites_pos; omega)
  have hx := h.window k
  rwa [hk] at hx

def middleStartIndex (S : Site) : ℕ := if InASublattice S.val then 2 else 3

theorem middleStartIndex_spec (S : Site) :
    (middleStartIndex S = 2 ∨ middleStartIndex S = 3) ∧
      (middleStartIndex S : ℤ) = throughOffset S ∧
      X S - X (throughAnchor S) = middleStartIndex S := by
  by_cases h : InASublattice S.val <;>
    simp [middleStartIndex, throughOffset, X, throughAnchor, throughAnchorCoordinates, h] <;> omega

namespace RoutingPlan

variable {w : ℕ} {d : WireData w} (p : RoutingPlan d)

theorem target_profile (i : Fin w) :
    PositiveQuadrant d.R (p.approaches i).target ∧
      rho d.R (p.approaches i).target = p.heights i ∧
      alpha d.R (p.approaches i).target = p.a ∧
      (d.slabs i - 5 ≤ X (p.approaches i).target ∧ X (p.approaches i).target ≤ d.slabs i + 5) := by
  have ht := p.radialTops_profile i
  have hs := (p.approaches i).target_window
  exact ⟨(p.approaches i).target_positive, (p.approaches i).target_level,
    (p.approaches i).target_alpha, by omega⟩

theorem target_gap (i j : Fin w) (hne : i ≠ j) (horder : d.slabs i < d.slabs j) :
    X (p.approaches i).target + 50 ≤ X (p.approaches j).target := by
  have hi := p.target_profile i
  have hj := p.target_profile j
  have hs := slabValue_separated d.H d.levels i j hne
  change d.slabs i + 60 ≤ d.slabs j ∨ d.slabs j + 60 ≤ d.slabs i at hs
  omega

/-- The middle of a paired linker, after the exact two-avenue padding. Its
site count is the original X-gap plus one and the requested even increase. -/
theorem middle_path_exists (i j : Fin w) (hne : i ≠ j) (horder : d.slabs i < d.slabs j)
    (hsame : p.heights i = p.heights j) (Δ : ℕ) (hΔ : 6 ≤ Δ) (heven : Δ % 2 = 0) :
    ∃ (n : ℕ) (f : Fold tetrahedralLattice n),
      (n : ℤ) = X (p.approaches j).target - X (p.approaches i).target + 1 + Δ ∧
      (∀ k, k.val = 0 → f.pos k = (p.approaches i).target) ∧
      (∀ k, k.val + 1 = n → f.pos k = (p.approaches j).target) ∧
      (∀ k, PositiveQuadrant d.R (f.pos k) ∧
        (rho d.R (f.pos k) = p.heights i ∨ rho d.R (f.pos k) = p.heights i + 2) ∧
        (alpha d.R (f.pos k) = p.a ∨ alpha d.R (f.pos k) = p.a + 2 ∨
          alpha d.R (f.pos k) = p.a + 4 ∨ alpha d.R (f.pos k) = p.a + 6)) := by
  let S := (p.approaches i).target
  let T := (p.approaches j).target
  let c := throughAnchor S
  let r := middleStartIndex S
  let b := (X T - X c).toNat
  have hi := p.target_profile i
  have hj := p.target_profile j
  have hgap := p.target_gap i j hne horder
  have hrs := middleStartIndex_spec S
  have hroom : |alpha d.R S| + 8 < rho d.R S := by
    change |alpha d.R (p.approaches i).target| + 8 < rho d.R (p.approaches i).target
    rw [hi.2.1, hi.2.2.1]
    exact p.heights_room i
  have hm := margins_of_level d.R S hi.1 hroom
  have hc := throughAnchor_margins d.R S (by omega) hm.2
  have hprivate := throughAnchor_private d.R S (by omega) hm.2
  have hbc : (b : ℤ) = X T - X c := by
    dsimp only [b]
    apply Int.toNat_of_nonneg
    dsimp only [S, T, c] at *
    omega
  have hr : r = 2 ∨ r = 3 := hrs.1
  have hb : r + 47 ≤ b := by dsimp only [S, T, c, r] at *; omega
  have hstart : avenue c (throughAnchor_A S) (throughUp S) r = S := by
    simpa only [r, hrs.2.1, c] using avenue_through_site S
  have hend : avenue c (throughAnchor_A S) (throughUp S) b = T := by
    rw [hbc]
    change avenueThrough S (X T) = T
    apply avenueThrough_hits d.R S T (by omega) hm.2 hj.1
    · change rho d.R (p.approaches j).target = rho d.R (p.approaches i).target
      rw [hj.2.1, hi.2.1, hsame]
    · change alpha d.R (p.approaches j).target = alpha d.R (p.approaches i).target
      rw [hj.2.2.1, hi.2.2.1]
  obtain ⟨n, f, hn, hfirst, hlast, hprofile⟩ :=
    exists_even_padding_path d.R c (throughAnchor_A S) (throughUp S) r b Δ hr hb hΔ heven hc.1 hc.2
  refine ⟨n, f, ?_, ?_, ?_, ?_⟩
  · dsimp only [S, T, c, r] at *
    omega
  · intro k hk
    exact (hfirst k hk).trans hstart
  · intro k hk
    exact (hlast k hk).trans hend
  · intro k
    have hk := hprofile k
    have hu : privateLevel d.R c (throughUp S) = p.heights i := hprivate.1.trans hi.2.1
    have ha : privateStrip d.R c = p.a := hprivate.2.trans hi.2.2.1
    simpa only [hu, ha] using hk

end RoutingPlan

end ProteinFolding.Tetrahedral.FarField
