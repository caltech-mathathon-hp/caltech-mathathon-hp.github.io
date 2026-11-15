import ProteinFolding.Tetrahedral.NearFieldTetherFamily
import ProteinFolding.Tetrahedral.NearFieldTetherSupport

/-! The only dangling sites occupied by an N4 tether are its two intended caps. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem higherSkin_not_dangling (m j : ℕ) (hj : 2 ≤ j) {s : Site} (hs : s ∈ skin m j) :
    ¬ IsDangling m s := by
  rintro ⟨hout, owner, ho, hadj⟩
  have hone := dangling_mem_skin_one m ho hadj hout
  exact Finset.disjoint_left.mp (skins_disjoint m 1 j (by omega)) hone hs

theorem entryTetherFold_dangling_eq_endpoint (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.entryTether k)) (hdang : IsDangling p.side ((entryTetherFold p k hk).pos i)) :
    (entryTetherFold p k hk).pos i =
      (faceDanglingColumn p.side (entryAnchorA p k) (3 * (k + 1)) 0 (entryAnchor_equation p k hk)).seed ∨
    (entryTetherFold p k hk).pos i = (entryTargetColumn p k hk).seed := by
  apply entryTetherFold_property p k hk (fun s => IsDangling p.side s →
    s = (faceDanglingColumn p.side (entryAnchorA p k) (3 * (k + 1)) 0 (entryAnchor_equation p k hk)).seed ∨
    s = (entryTargetColumn p k hk).seed) _ _ _ i hdang
  · intro r hr
    change IsDangling p.side (borrowedPoint p.side (entryAnchorA p k) (3 * (k + 1)) 0
      (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) r.val) at hr
    cases hn : r.val with
    | zero =>
      left
      change borrowedPoint p.side (entryAnchorA p k) (3 * (k + 1)) 0
        (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) r.val = _
      rw [hn]
      rfl
    | succ n =>
      rw [hn] at hr
      have hz := ((faceDanglingColumn p.side (entryAnchorA p k - 1) (3 * (k + 1)) (0 + 1)
        (by have h := entryAnchor_equation p k hk; have ha := entryAnchor_positive p k hk; omega)).point_dangling_iff_zero (n + 1)).mp hr
      omega
  · intro r hr
    exact (higherSkin_not_dangling _ _ (p.tether_skin_bounds k hk).1 (entryRow_mem_skin p k hk r) hr).elim
  · intro r hr
    have hz := ((entryTargetColumn p k hk).point_dangling_iff_zero r.rev.val).mp hr
    right
    change (entryTargetColumn p k hk).point r.rev.val = _
    rw [hz]
    rfl

theorem exitTetherFold_dangling_eq_endpoint (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.exitTether k)) (hdang : IsDangling p.side ((exitTetherFold p k hk).pos i)) :
    (exitTetherFold p k hk).pos i = (exitSourceColumn p k hk).seed ∨
    (exitTetherFold p k hk).pos i = (exitTargetColumn p k).seed := by
  apply exitTetherFold_property p k hk (fun s => IsDangling p.side s →
    s = (exitSourceColumn p k hk).seed ∨ s = (exitTargetColumn p k).seed) _ _ _ i hdang
  · intro r hr
    have hz := ((exitSourceColumn p k hk).point_dangling_iff_zero r.val).mp hr
    left
    change (exitSourceColumn p k hk).point r.val = _
    rw [hz]
    rfl
  · intro r hr
    exact (higherSkin_not_dangling _ _ (by have h := p.tether_skin_bounds k hk; omega)
      (exitRow_mem_skin p k hk r) hr).elim
  · intro r hr
    have hz := ((exitTargetColumn p k).point_dangling_iff_zero r.rev.val).mp hr
    right
    change (exitTargetColumn p k).point r.rev.val = _
    rw [hz]
    rfl

theorem tetherFold_dangling_eq_endpoint (p : ConstructionParameters) (t : TetherIndex p)
    (i : Fin (tetherCount p t)) (hdang : IsDangling p.side ((tetherFold p t).pos i)) :
    (tetherFold p t).pos i = tetherSource p t ∨ (tetherFold p t).pos i = tetherTarget p t := by
  rcases t with ⟨b, k⟩
  cases b
  · exact entryTetherFold_dangling_eq_endpoint p k.val (Nat.le_of_lt_succ k.isLt) i hdang
  · exact exitTetherFold_dangling_eq_endpoint p k.val (Nat.le_of_lt_succ k.isLt) i hdang

theorem tetherFold_ne_other_dangling (p : ConstructionParameters) (t : TetherIndex p)
    (i : Fin (tetherCount p t)) {q : Site} (hq : IsDangling p.side q)
    (hsource : q ≠ tetherSource p t) (htarget : q ≠ tetherTarget p t) : (tetherFold p t).pos i ≠ q := by
  intro heq
  have hdang : IsDangling p.side ((tetherFold p t).pos i) := by rw [heq]; exact hq
  rcases tetherFold_dangling_eq_endpoint p t i hdang with h | h
  · exact hsource (heq.symm.trans h)
  · exact htarget (heq.symm.trans h)

end ProteinFolding.Tetrahedral.NearField
