import ProteinFolding.Tetrahedral.OctahedralExteriorLinks

/-!
# Link advances and equality, Section 5.6(O4)

The proof counts cancelled bond pairs. It establishes the stated bounds
and preservation of the edge for every length, without a size cutoff.
-/

namespace ProteinFolding.Tetrahedral
namespace OctExteriorLink

variable {m n : ℕ} (L : OctExteriorLink m n)

def loss (a b : Fin 4) : ℤ :=
  (n : ℤ) - (((L.positive a : ℤ) - (L.negative a : ℤ)) -
    ((L.positive b : ℤ) - (L.negative b : ℤ)))

theorem loss_eq_sum (a b : Fin 4) :
    L.loss a b = ∑ r : Fin 4, directionLoss a b L.positive L.negative r := by
  have ht := pathCount_total L.site L.dir n
  change (∑ r : Fin 4, L.positive r) + (∑ r : Fin 4, L.negative r) = n at ht
  have htZ := congrArg (fun z : ℕ => (z : ℤ)) ht
  push_cast at htZ
  rw [sum_directionLoss]
  dsimp [loss]
  omega

theorem cancellations_cast : (L.cancellations : ℤ) =
    ∑ r : Fin 4, ((min (L.positive r) (L.negative r) : ℕ) : ℤ) := by
  simp only [cancellations, Nat.cast_sum]

theorem height_difference_eq_loss (a b : Fin 4) :
    octEdgeHeight4 m a b (L.site n) - octEdgeHeight4 m a b (L.site 0) =
      4 * ((n : ℤ) - L.loss a b) := by
  have ha := L.coordinate_difference a
  have hb := L.coordinate_difference b
  dsimp [octEdgeHeight4, loss]
  omega

theorem loss_ge_twice_cancellations {a b : Fin 4} (hab : a ≠ b) :
    2 * (L.cancellations : ℤ) ≤ L.loss a b := by
  rw [L.loss_eq_sum, L.cancellations_cast]
  exact sum_directionLoss_ge_cancellation hab L.positive L.negative

theorem loss_ge_two {a b : Fin 4} (hab : a ≠ b) : 2 ≤ L.loss a b := by
  have h := L.loss_ge_twice_cancellations hab
  have hc := L.cancellations_ge_one
  omega

theorem loss_ge_four_odd_length {a b : Fin 4} (hab : a ≠ b) (hn : n % 2 = 1) :
    4 ≤ L.loss a b := by
  have h := L.loss_ge_twice_cancellations hab
  have hc := L.cancellations_ge_two_odd_length hn
  omega

theorem neutral_counts_eq_of_minimal_loss {a b : Fin 4} (hab : a ≠ b) (t : ℕ)
    (hc : t ≤ L.cancellations) (hloss : L.loss a b = 2 * (t : ℤ))
    {r : Fin 4} (hra : r ≠ a) (hrb : r ≠ b) : L.positive r = L.negative r := by
  have hb := L.loss_ge_twice_cancellations hab
  have heq : L.loss a b = 2 * (L.cancellations : ℤ) := by omega
  apply neutral_counts_eq_of_loss_eq hab L.positive L.negative _ hra hrb
  rw [← L.loss_eq_sum, ← L.cancellations_cast]
  exact heq

/-- Equality preserves both transverse face coordinates, with precisely the
one-unit shift required when the endpoint changes sublattice. -/
theorem minimal_loss_preserves_edge (F : OctEdgeFrame) (t : ℕ)
    (hc : t ≤ L.cancellations) (hloss : L.loss F.a F.b = 2 * (t : ℤ))
    (hstart : OctEdgeSite m F.k F.j (L.site 0)) : OctEdgeSite m F.k F.j (L.site n) := by
  have hk := L.coordinate_difference F.k
  have hj := L.coordinate_difference F.j
  have hck := L.neutral_counts_eq_of_minimal_loss F.ab t hc hloss F.ka F.kb
  have hcj := L.neutral_counts_eq_of_minimal_loss F.ab t hc hloss F.ja F.jb
  rw [hck] at hk
  rw [hcj] at hj
  rcases hstart with ⟨⟨_, hpA, hpk⟩, hpj⟩ | ⟨⟨_, hpB, hpj⟩, hpk⟩
  · rw [siteCharge_A hpA] at hk hj
    rcases (L.site n).property with hqA | hqB
    · rw [siteCharge_A hqA] at hk hj
      exact Or.inl ⟨⟨L.end_mem, hqA, by omega⟩, by omega⟩
    · rw [siteCharge_B hqB] at hk hj
      exact Or.inr ⟨⟨L.end_mem, hqB, by dsimp [octRadius] at *; omega⟩,
        by dsimp [octRadius] at *; omega⟩
  · rw [siteCharge_B hpB] at hk hj
    rcases (L.site n).property with hqA | hqB
    · rw [siteCharge_A hqA] at hk hj
      exact Or.inl ⟨⟨L.end_mem, hqA, by dsimp [octRadius] at *; omega⟩,
        by dsimp [octRadius] at *; omega⟩
    · rw [siteCharge_B hqB] at hk hj
      exact Or.inr ⟨⟨L.end_mem, hqB, by omega⟩, by omega⟩

end OctExteriorLink

/-- Four times the advance of a P^k link is at most 4(k−1). -/
theorem exterior_link_advance_bound {m k : ℕ} (L : OctExteriorLink m (k + 1))
    {a b : Fin 4} (hab : a ≠ b) :
    octEdgeHeight4 m a b (L.site (k + 1)) - octEdgeHeight4 m a b (L.site 0) ≤
      4 * ((k : ℤ) - 1) := by
  have h := L.height_difference_eq_loss a b
  have hl := L.loss_ge_two hab
  push_cast at h
  omega

/-- For even k the sharper bound is 4(k−3). -/
theorem exterior_even_P_link_advance_bound {m k : ℕ} (L : OctExteriorLink m (k + 1))
    {a b : Fin 4} (hab : a ≠ b) (hk : k % 2 = 0) :
    octEdgeHeight4 m a b (L.site (k + 1)) - octEdgeHeight4 m a b (L.site 0) ≤
      4 * ((k : ℤ) - 3) := by
  have h := L.height_difference_eq_loss a b
  have hl := L.loss_ge_four_odd_length hab (by omega)
  push_cast at h
  omega

theorem exterior_odd_P_link_maximiser_on_edge {m k : ℕ} (L : OctExteriorLink m (k + 1))
    (F : OctEdgeFrame) (_hk : k % 2 = 1) (hstart : OctEdgeSite m F.k F.j (L.site 0))
    (hmax : octEdgeHeight4 m F.a F.b (L.site (k + 1)) -
      octEdgeHeight4 m F.a F.b (L.site 0) = 4 * ((k : ℤ) - 1)) :
    OctEdgeSite m F.k F.j (L.site (k + 1)) := by
  apply L.minimal_loss_preserves_edge F 1 L.cancellations_ge_one _ hstart
  have h := L.height_difference_eq_loss F.a F.b
  push_cast at h
  omega

theorem exterior_even_P_link_maximiser_on_edge {m k : ℕ} (L : OctExteriorLink m (k + 1))
    (F : OctEdgeFrame) (hk : k % 2 = 0) (hstart : OctEdgeSite m F.k F.j (L.site 0))
    (hmax : octEdgeHeight4 m F.a F.b (L.site (k + 1)) -
      octEdgeHeight4 m F.a F.b (L.site 0) = 4 * ((k : ℤ) - 3)) :
    OctEdgeSite m F.k F.j (L.site (k + 1)) := by
  apply L.minimal_loss_preserves_edge F 2 (L.cancellations_ge_two_odd_length (by omega)) _ hstart
  have h := L.height_difference_eq_loss F.a F.b
  push_cast at h
  omega

theorem exterior_odd_P_link_maximiser_index {m k i : ℕ} (hm : 1 ≤ m)
    (L : OctExteriorLink m (k + 1)) (F : OctEdgeFrame) (hk : k % 2 = 1)
    (hi : i < 2 * m - 1) (hstart : L.site 0 = octEdgeZigzag m F i)
    (hmax : octEdgeHeight4 m F.a F.b (L.site (k + 1)) -
      octEdgeHeight4 m F.a F.b (L.site 0) = 4 * ((k : ℤ) - 1)) :
    ∃ r < 2 * m - 1, L.site (k + 1) = octEdgeZigzag m F r ∧ r + 1 = i + k := by
  have hs : OctEdgeSite m F.k F.j (L.site 0) := by
    rw [hstart]
    exact octEdgeZigzag_mem hm F hi
  have he := exterior_odd_P_link_maximiser_on_edge L F hk hs hmax
  obtain ⟨r, hr, hend⟩ := (octEdgeSite_iff_param hm F _).mp he
  refine ⟨r, hr, hend, ?_⟩
  rw [hstart, hend, octEdgeZigzag_height hm F, octEdgeZigzag_height hm F] at hmax
  omega

theorem exterior_even_P_link_maximiser_index {m k i : ℕ} (hm : 1 ≤ m)
    (L : OctExteriorLink m (k + 1)) (F : OctEdgeFrame) (hk : k % 2 = 0)
    (hi : i < 2 * m - 1) (hstart : L.site 0 = octEdgeZigzag m F i)
    (hmax : octEdgeHeight4 m F.a F.b (L.site (k + 1)) -
      octEdgeHeight4 m F.a F.b (L.site 0) = 4 * ((k : ℤ) - 3)) :
    ∃ r < 2 * m - 1, L.site (k + 1) = octEdgeZigzag m F r ∧ r + 3 = i + k := by
  have hs : OctEdgeSite m F.k F.j (L.site 0) := by
    rw [hstart]
    exact octEdgeZigzag_mem hm F hi
  have he := exterior_even_P_link_maximiser_on_edge L F hk hs hmax
  obtain ⟨r, hr, hend⟩ := (octEdgeSite_iff_param hm F _).mp he
  refine ⟨r, hr, hend, ?_⟩
  rw [hstart, hend, octEdgeZigzag_height hm F, octEdgeZigzag_height hm F] at hmax
  omega

end ProteinFolding.Tetrahedral
