import ProteinFolding.Tetrahedral.FrameForcingSlots
import ProteinFolding.Tetrahedral.SeparatorArithmetic
import ProteinFolding.Tetrahedral.TetherDistance

/-! Opposite frame endpoints have coefficient distance 4m−4. Entry and exit
anchors are too close to those endpoints for a separator bridge to join them. -/

namespace ProteinFolding.Tetrahedral

theorem octEdgeZigzag_fixed_height (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) :
    octEdgeHeight4 m F.k F.j (octEdgeZigzag m F r) = 2 * octRadius m := by
  have hmod := Nat.mod_lt r (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div r 2
  by_cases heven : r % 2 = 0
  · have hr : r = 2 * (r / 2) := by omega
    rw [hr]
    have h := octEdgeZigzag_even hm F (r / 2)
    unfold octEdgeHeight4
    rw [h.2.1, h.2.2.1]
    omega
  · have hr : r = 2 * (r / 2) + 1 := by omega
    rw [hr]
    have h := octEdgeZigzag_odd hm F (r / 2)
    unfold octEdgeHeight4
    rw [h.2.1, h.2.2.1]
    omega

theorem tetraLift_difference_A (m : ℕ) (p q : Site)
    (hp : InASublattice p.val) (hq : InASublattice q.val) (d : Fin 4) :
    4 * (tetraLift q d - tetraLift p d) = tetraCoordinate m q.val d - tetraCoordinate m p.val d := by
  have hp' := tetraLift_spec p d
  have hq' := tetraLift_spec q d
  rw [siteCharge_A hp] at hp'
  rw [siteCharge_A hq] at hq'
  rw [tetraCoordinate_difference_independent m p.val q.val d]
  omega

theorem opposite_frame_vertex_distance (m : ℕ) (hm : 1 ≤ m) (F₁ F₂ : OctEdgeFrame)
    (hbig : F₂.k = F₁.a) (hsmall : F₂.j = F₁.b)
    (ha : F₂.a = F₁.j) (hb : F₂.b = F₁.k) :
    tetraCoefficientDistance (octEdgeStart m F₁) (octEdgeZigzag m F₂ (2 * m - 2)) = 4 * (m : ℤ) - 4 := by
  have hstart := octEdgeStart_spec hm F₁
  have hend := octEdgeEnd_faces m hm F₂
  have hindex : 2 * (m - 1) = 2 * m - 2 := by omega
  have hendA : InASublattice (octEdgeZigzag m F₂ (2 * m - 2)).val := by
    simpa only [hindex] using (octEdgeZigzag_even hm F₂ (m - 1)).1
  have hk : tetraCoordinate m (octEdgeZigzag m F₂ (2 * m - 2)).val F₁.k = -octRadius m := by
    rw [← hb]; exact hend.2.2.2
  have hj : tetraCoordinate m (octEdgeZigzag m F₂ (2 * m - 2)).val F₁.j = octRadius m := by
    rw [← ha]; exact hend.2.2.1
  have hfa : tetraCoordinate m (octEdgeZigzag m F₂ (2 * m - 2)).val F₁.a = octRadius m := by
    rw [← hbig]; exact hend.1
  have hfb : tetraCoordinate m (octEdgeZigzag m F₂ (2 * m - 2)).val F₁.b = -octRadius m := by
    rw [← hsmall]; exact hend.2.1
  have habs (d : Fin 4) : |tetraLift (octEdgeZigzag m F₂ (2 * m - 2)) d - tetraLift (octEdgeStart m F₁) d| = (m : ℤ) - 1 := by
    have h := tetraLift_difference_A m _ _ hstart.1 hendA d
    rcases F₁.index_cases d with hd | hd | hd | hd
    · rw [hd, hk, hstart.2.1] at h
      dsimp [octRadius] at h
      have hv : tetraLift (octEdgeZigzag m F₂ (2 * m - 2)) d - tetraLift (octEdgeStart m F₁) d = 1 - (m : ℤ) := by rw [hd]; omega
      rw [hv, abs_of_nonpos (by omega)]
      omega
    · rw [hd, hj, hstart.2.2.1] at h
      dsimp [octRadius] at h
      have hv : tetraLift (octEdgeZigzag m F₂ (2 * m - 2)) d - tetraLift (octEdgeStart m F₁) d = (m : ℤ) - 1 := by rw [hd]; omega
      rw [hv, abs_of_nonneg (by omega)]
    · rw [hd, hfa, hstart.2.2.2.1] at h
      dsimp [octRadius] at h
      have hv : tetraLift (octEdgeZigzag m F₂ (2 * m - 2)) d - tetraLift (octEdgeStart m F₁) d = (m : ℤ) - 1 := by rw [hd]; omega
      rw [hv, abs_of_nonneg (by omega)]
    · rw [hd, hfb, hstart.2.2.2.2] at h
      dsimp [octRadius] at h
      have hv : tetraLift (octEdgeZigzag m F₂ (2 * m - 2)) d - tetraLift (octEdgeStart m F₁) d = 1 - (m : ℤ) := by rw [hd]; omega
      rw [hv, abs_of_nonpos (by omega)]
      omega
  simp only [tetraCoefficientDistance, habs, Fin.sum_univ_succ, Fin.sum_univ_zero]
  omega

namespace ConstructionParameters

theorem opposite_frame_anchor_path_impossible (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F₁ F₂ : OctEdgeFrame) (hbig : F₂.k = F₁.a) (hsmall : F₂.j = F₁.b)
    (ha : F₂.a = F₁.j) (hb : F₂.b = F₁.k)
    (r s : ℕ) (hr : r ≤ 6 * p.bins + 7) (hs : s ≤ 2 * p.side - 2)
    (hfarEnd : 2 * p.side - 2 - s ≤ 10 * p.bins + 11) (f : ℕ → Site) (n : ℕ)
    (hstep : ∀ i < n, tetrahedralLattice.Adj (f i) (f (i + 1)))
    (hstart : tetrahedralLattice.Adj (octEdgeZigzag p.side F₁ r) (f 0))
    (hend : tetrahedralLattice.Adj (f n) (octEdgeZigzag p.side F₂ s))
    (hnear : n ≤ (p.separatorBridge k).length - 1) : False := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hpath := path_coefficient_distance_bound f n hstep
  have hleft := tetraCoefficientDistance_adj hstart
  have hright := tetraCoefficientDistance_adj hend
  have hentry := path_coefficient_distance_bound (octEdgeZigzag p.side F₁) r
    (fun i _ => octEdgeZigzag_adj p.side F₁ i)
  change tetraCoefficientDistance (octEdgeStart p.side F₁) (octEdgeZigzag p.side F₁ r) ≤ (r : ℤ) at hentry
  have hexit := path_coefficient_distance_bound (fun i => octEdgeZigzag p.side F₂ (s + i))
    (2 * p.side - 2 - s) (fun i _ => by simpa only [Nat.add_assoc] using octEdgeZigzag_adj p.side F₂ (s + i))
  have hsum : s + (2 * p.side - 2 - s) = 2 * p.side - 2 := by omega
  simp only [Nat.add_zero, hsum] at hexit
  have htri₁ := tetraCoefficientDistance_triangle (octEdgeStart p.side F₁) (octEdgeZigzag p.side F₁ r) (f 0)
  have htri₂ := tetraCoefficientDistance_triangle (octEdgeStart p.side F₁) (f 0) (f n)
  have htri₃ := tetraCoefficientDistance_triangle (octEdgeStart p.side F₁) (f n) (octEdgeZigzag p.side F₂ s)
  have htri₄ := tetraCoefficientDistance_triangle (octEdgeStart p.side F₁) (octEdgeZigzag p.side F₂ s)
    (octEdgeZigzag p.side F₂ (2 * p.side - 2))
  rw [opposite_frame_vertex_distance p.side hm F₁ F₂ hbig hsmall ha hb] at htri₄
  have hfar : 4 * p.side - 16 * p.bins - 28 ≤ n := by omega
  exact p.opposite_frame_separatorBridge_impossible k hk n hnear hfar

end ConstructionParameters

end ProteinFolding.Tetrahedral
