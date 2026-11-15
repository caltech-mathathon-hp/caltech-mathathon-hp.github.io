import ProteinFolding.Tetrahedral.SiteProfileTelescoping
import ProteinFolding.Tetrahedral.LayerRigidityErosion
import ProteinFolding.Tetrahedral.OctahedralBoundary
import ProteinFolding.Tetrahedral.OctahedralCount

/-! Global geometric rigidity from a normalized central layer.
Two inward neighbours suffice for inclusion; equality follows from cardinality. -/

namespace ProteinFolding.Tetrahedral

theorem mem_octahedron_of_two_neighbours (m : ℕ) {p q r : Site}
    (hpq : tetrahedralLattice.Adj p q) (hpr : tetrahedralLattice.Adj p r)
    (hqr : q ≠ r) (hq : q ∈ octahedron m) (hr : r ∈ octahedron m) :
    p ∈ octahedron m := by
  by_contra hout
  have hdang : IsDangling m p := ⟨hout, q, hq, hpq.symm⟩
  have hu := dangling_unique_inside m hdang
  exact hqr (hu.unique ⟨hq, hpq.symm⟩ ⟨hr, hpr.symm⟩)

theorem site_layer_containment_propagates (S : Finset Site) (f : Site → Site)
    (hf : Function.Injective f)
    (hadj : ∀ p q, tetrahedralLattice.Adj p q → tetrahedralLattice.Adj (f p) (f q))
    (m : ℕ) (k a b : ℤ)
    (hab : (a = k ∧ b = k + 1) ∨ (a = k + 1 ∧ b = k))
    (htight : (finiteLayer S a).card = (finiteLayer S b).card + gapRunCount S k)
    (hinner : ∀ p ∈ finiteLayer S a, f p ∈ octahedron m) :
    ∀ p ∈ finiteLayer S b, f p ∈ octahedron m := by
  intro p hp
  have hn := tight_imbalance_smaller_neighbours S k a b hab htight p hp
  have hx := gap_steps_other_layer k a b p hab (Finset.mem_filter.mp hp).2
  apply mem_octahedron_of_two_neighbours m
    (hadj p (gapPrev k p) (gapPrev_adj k p))
    (hadj p (gapNext k p) (gapNext_adj k p))
  · exact fun heq => gapPrev_ne_next k p (hf heq)
  · exact hinner _ (Finset.mem_filter.mpr ⟨hn.1, hx.1⟩)
  · exact hinner _ (Finset.mem_filter.mpr ⟨hn.2, hx.2⟩)

/-- A graph embedding sending the central layer into the octahedron sends all
occupied layers there when every outward imbalance is tight. -/
theorem site_image_subset_octahedron_of_signed_imbalances (S : Finset Site)
    (f : Site → Site) (hf : Function.Injective f)
    (hadj : ∀ p q, tetrahedralLattice.Adj p q → tetrahedralLattice.Adj (f p) (f q))
    (m : ℕ) (center : ℤ)
    (hcentral : ∀ p ∈ finiteLayer S center, f p ∈ octahedron m)
    (hleft : ∀ k < center, (finiteLayer S (k + 1)).card =
      (finiteLayer S k).card + gapRunCount S k)
    (hright : ∀ k, center ≤ k → (finiteLayer S k).card =
      (finiteLayer S (k + 1)).card + gapRunCount S k) :
    S.image f ⊆ octahedron m := by
  have hdown : ∀ n : ℕ, ∀ p ∈ finiteLayer S (center - n), f p ∈ octahedron m := by
    intro n
    induction n with
    | zero => simpa using hcentral
    | succ n ih =>
      let k : ℤ := center - ((n + 1 : ℕ) : ℤ)
      have hk : k < center := by dsimp [k]; omega
      have heq : k + 1 = center - n := by dsimp [k]; omega
      apply site_layer_containment_propagates S f hf hadj m k (k + 1) k
        (Or.inr ⟨rfl, rfl⟩) (hleft k hk)
      simpa only [heq] using ih
  have hup : ∀ n : ℕ, ∀ p ∈ finiteLayer S (center + n), f p ∈ octahedron m := by
    intro n
    induction n with
    | zero => simpa using hcentral
    | succ n ih =>
      have heq : center + ((n + 1 : ℕ) : ℤ) = center + n + 1 := by omega
      rw [heq]
      apply site_layer_containment_propagates S f hf hadj m (center + n)
        (center + n) (center + n + 1) (Or.inl ⟨rfl, rfl⟩) (hright _ (by omega)) ih
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  by_cases hside : p.val 0 ≤ center
  · have heq : center - ((center - p.val 0).toNat : ℤ) = p.val 0 := by omega
    apply hdown (center - p.val 0).toNat p
    apply Finset.mem_filter.mpr
    exact ⟨hp, by omega⟩
  · have heq : center + ((p.val 0 - center).toNat : ℤ) = p.val 0 := by omega
    apply hup (p.val 0 - center).toNat p
    apply Finset.mem_filter.mpr
    exact ⟨hp, by omega⟩

/-- The inclusion becomes the full octahedron when the occupied cardinality
is the octahedral number. -/
theorem site_image_eq_octahedron_of_signed_imbalances (S : Finset Site)
    (f : Site → Site) (hf : Function.Injective f)
    (hadj : ∀ p q, tetrahedralLattice.Adj p q → tetrahedralLattice.Adj (f p) (f q))
    (m : ℕ) (center : ℤ) (hcard : S.card = octahedralNumber m)
    (hcentral : ∀ p ∈ finiteLayer S center, f p ∈ octahedron m)
    (hleft : ∀ k < center, (finiteLayer S (k + 1)).card =
      (finiteLayer S k).card + gapRunCount S k)
    (hright : ∀ k, center ≤ k → (finiteLayer S k).card =
      (finiteLayer S (k + 1)).card + gapRunCount S k) :
    S.image f = octahedron m := by
  apply Finset.eq_of_subset_of_card_le
    (site_image_subset_octahedron_of_signed_imbalances S f hf hadj m center hcentral hleft hright)
  rw [Finset.card_image_of_injective _ hf, octahedron_card, hcard]

end ProteinFolding.Tetrahedral
