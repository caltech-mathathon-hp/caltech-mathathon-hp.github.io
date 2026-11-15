import ProteinFolding.Cubic.Proofs.GeometryEqualityIntervals
import ProteinFolding.Cubic.Proofs.GeometryBound

/-! Tight line counts and Cartesian support force gapless coordinate sets. -/

namespace ProteinFolding.CubicGeometry

open scoped BigOperators

theorem axis_tight_of_maximal_edges (s : Finset Site) (n : ℕ)
    (hc : s.card = n ^ 3) (he : positiveEdgeCount s ≥ 3 * n ^ 2 * (n - 1)) (k : Fin 3) :
    (positiveEdges s k).card + (s.image (lineKey k)).card = s.card := by
  have hcards := lineKey_cards_of_maximal_edges s n hc he
  have hlines : (∑ k : Fin 3, (s.image (lineKey k)).card) = 3 * n ^ 2 := by
    have hsum : (∑ k : Fin 3, (s.image (lineKey k)).card) =
        (s.image (lineKey 0)).card + (s.image (lineKey 1)).card +
          (s.image (lineKey 2)).card := by simp [Fin.sum_univ_succ, Nat.add_assoc]
    rw [hsum, hcards.1, hcards.2.1, hcards.2.2]
    omega
  have htotal : positiveEdgeCount s + (∑ k : Fin 3, (s.image (lineKey k)).card) =
      3 * s.card := by
    have hupper := positiveEdgeCount_add_lines_le s
    rw [hlines, hc] at hupper ⊢
    by_cases hn : n = 0
    · simp_all
    · have hn' : n - 1 + 1 = n := by omega
      have harith : 3 * n ^ 3 = 3 * n ^ 2 * (n - 1) + 3 * n ^ 2 := by nlinarith
      omega
  have hsum : (∑ k : Fin 3, ((positiveEdges s k).card + (s.image (lineKey k)).card)) =
      ∑ _ : Fin 3, s.card := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Nat.nsmul_eq_mul, positiveEdgeCount] using htotal
  exact (Finset.sum_eq_sum_iff_of_le
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => positiveEdges_add_lineKeys_le s k)).mp
      hsum k (Finset.mem_univ k)

theorem upperBoundary_lineKey_injective_of_tight (s : Finset Site) (k : Fin 3)
    (htight : (positiveEdges s k).card + (s.image (lineKey k)).card = s.card) :
    Set.InjOn (lineKey k) (upperBoundary s k) := by
  classical
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := s) (fun p => stepPlus k p ∈ s)
  change (positiveEdges s k).card + (upperBoundary s k).card = s.card at hpart
  have hcard : (s.image (lineKey k)).card = (upperBoundary s k).card := by omega
  apply Finset.card_image_iff.mp
  rw [lineKeys_upperBoundary, hcard]

theorem coordinate_boundary_card_one_of_tight (s : Finset Site) (hne : s.Nonempty)
    (hcart : ∀ p : Site, p ∈ s ↔ ∀ j : Fin 3, p j ∈ s.image (fun q => q j))
    (k : Fin 3)
    (htight : (positiveEdges s k).card + (s.image (lineKey k)).card = s.card) :
    ((s.image (fun p => p k)).filter (fun x => x + 1 ∉ s.image (fun p => p k))).card = 1 := by
  classical
  obtain ⟨p, hp⟩ := hne
  let X := s.image (fun p => p k)
  have hX : X.Nonempty := ⟨p k, Finset.mem_image_of_mem _ hp⟩
  have hpoint : ∀ x ∈ X, Function.update p k x ∈ s := by
    intro x hx
    apply (hcart _).mpr
    intro j
    by_cases hj : j = k
    · subst j; simpa [X] using hx
    · simpa [Function.update_of_ne hj] using Finset.mem_image_of_mem (fun q => q j) hp
  have hupper : ∀ x ∈ X, x + 1 ∉ X → Function.update p k x ∈ upperBoundary s k := by
    intro x hx hout
    apply Finset.mem_filter.mpr
    refine ⟨hpoint x hx, ?_⟩
    intro hsucc
    apply hout
    have himage := Finset.mem_image_of_mem (fun q => q k) hsucc
    simpa [X, stepPlus] using himage
  have hle : (X.filter (fun x => x + 1 ∉ X)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have heq : Function.update p k x = Function.update p k y :=
      upperBoundary_lineKey_injective_of_tight s k htight
        (hupper x hx'.1 hx'.2) (hupper y hy'.1 hy'.2)
        (by simp [lineKey, Function.update_idem])
    have hvalue := congrFun heq k
    simpa using hvalue
  have hmax : X.max' hX ∈ X := X.max'_mem hX
  have hout : X.max' hX + 1 ∉ X := by
    intro hsucc
    have hbound := X.le_max' _ hsucc
    omega
  have hpos : 0 < (X.filter (fun x => x + 1 ∉ X)).card :=
    Finset.card_pos.mpr ⟨X.max' hX, Finset.mem_filter.mpr ⟨hmax, hout⟩⟩
  exact Nat.le_antisymm hle hpos

theorem coordinate_eq_interval_of_tight (s : Finset Site) (hne : s.Nonempty)
    (hcart : ∀ p : Site, p ∈ s ↔ ∀ j : Fin 3, p j ∈ s.image (fun q => q j))
    (k : Fin 3)
    (htight : (positiveEdges s k).card + (s.image (lineKey k)).card = s.card) :
    let X := s.image (fun p => p k)
    ∃ a b : ℤ, X = Finset.Icc a b := by
  classical
  let X := s.image (fun p => p k)
  have hX : X.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p k, Finset.mem_image_of_mem _ hp⟩
  exact ⟨X.min' hX, X.max' hX,
    eq_Icc_of_one_upper_boundary X hX (coordinate_boundary_card_one_of_tight s hne hcart k htight)⟩

end ProteinFolding.CubicGeometry
